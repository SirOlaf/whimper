use std::ops::Range;

const DOS_SIGNATURE: &[u8] = b"MZ";
const PE_SIGNATURE: &[u8] = b"PE\0\0";
const AMD64: u16 = 0x8664;
const PE32_PLUS: u16 = 0x20b;
const EXECUTE: u32 = 0x2000_0000;

#[derive(Debug)]
pub struct Section {
    pub name: String,
    pub virtual_address: u32,
    pub virtual_size: u32,
    pub raw_size: u32,
    pub characteristics: u32,
}

impl Section {
    pub fn is_executable(&self) -> bool {
        self.characteristics & EXECUTE != 0
    }

    fn range(&self) -> Range<usize> {
        let start = self.virtual_address as usize;
        start..start + self.virtual_size as usize
    }
}

/// An image laid out at the PE preferred image base, with virtual tails zero-filled.
pub struct PeImage {
    image_base: u64,
    entry_rva: u32,
    memory: Vec<u8>,
    header_size: usize,
    sections: Vec<Section>,
}

fn bytes_at(data: &[u8], offset: usize, size: usize) -> Result<&[u8], String> {
    data.get(offset..offset.checked_add(size).ok_or("PE offset overflow")?)
        .ok_or_else(|| format!("truncated PE at file offset 0x{offset:x}"))
}

fn u16_at(data: &[u8], offset: usize) -> Result<u16, String> {
    Ok(u16::from_le_bytes(
        bytes_at(data, offset, 2)?.try_into().unwrap(),
    ))
}

fn u32_at(data: &[u8], offset: usize) -> Result<u32, String> {
    Ok(u32::from_le_bytes(
        bytes_at(data, offset, 4)?.try_into().unwrap(),
    ))
}

fn u64_at(data: &[u8], offset: usize) -> Result<u64, String> {
    Ok(u64::from_le_bytes(
        bytes_at(data, offset, 8)?.try_into().unwrap(),
    ))
}

impl PeImage {
    pub fn parse(file: &[u8]) -> Result<Self, String> {
        if bytes_at(file, 0, 2)? != DOS_SIGNATURE {
            return Err("missing DOS signature".into());
        }
        let pe = u32_at(file, 0x3c)? as usize;
        if bytes_at(file, pe, 4)? != PE_SIGNATURE {
            return Err("missing PE signature".into());
        }
        let coff = pe.checked_add(4).ok_or("PE offset overflow")?;
        if u16_at(file, coff)? != AMD64 {
            return Err("only x86_64 PE images are supported".into());
        }
        let section_count = u16_at(file, coff + 2)? as usize;
        let optional_size = u16_at(file, coff + 16)? as usize;
        let optional = coff.checked_add(20).ok_or("PE offset overflow")?;
        let optional_bytes = bytes_at(file, optional, optional_size)?;
        if optional_bytes.len() < 64 || u16_at(optional_bytes, 0)? != PE32_PLUS {
            return Err("expected a PE32+ optional header".into());
        }

        let entry_rva = u32_at(optional_bytes, 16)?;
        let image_base = u64_at(optional_bytes, 24)?;
        let image_size = u32_at(optional_bytes, 56)? as usize;
        let header_size = u32_at(optional_bytes, 60)? as usize;
        if image_size == 0 || header_size > image_size {
            return Err("invalid PE image or header size".into());
        }
        if entry_rva as usize >= image_size {
            return Err("entry point is outside the PE image".into());
        }
        image_base
            .checked_add(image_size as u64)
            .ok_or("PE virtual address overflow")?;

        let section_table = optional
            .checked_add(optional_size)
            .ok_or("PE offset overflow")?;
        let table_size = section_count
            .checked_mul(40)
            .ok_or("PE section table overflow")?;
        if section_table
            .checked_add(table_size)
            .ok_or("PE section table overflow")?
            > header_size
        {
            return Err("PE section table extends beyond mapped headers".into());
        }
        bytes_at(file, section_table, table_size)?;
        let mut sections = Vec::with_capacity(section_count);
        let mut spans = vec![0..header_size];
        let mut memory = vec![0; image_size];
        memory[..header_size].copy_from_slice(bytes_at(file, 0, header_size)?);

        for index in 0..section_count {
            let header = section_table + index * 40;
            let name_bytes = bytes_at(file, header, 8)?;
            let name_len = name_bytes.iter().position(|&byte| byte == 0).unwrap_or(8);
            let name = String::from_utf8_lossy(&name_bytes[..name_len]).into_owned();
            let raw_size = u32_at(file, header + 16)?;
            let raw_offset = u32_at(file, header + 20)? as usize;
            let mut section = Section {
                name,
                virtual_size: u32_at(file, header + 8)?,
                virtual_address: u32_at(file, header + 12)?,
                raw_size,
                characteristics: u32_at(file, header + 36)?,
            };
            // Some linkers leave VirtualSize zero; the raw extent is then the
            // only usable section size. Raw alignment padding is otherwise not
            // part of the mapped virtual section.
            if section.virtual_size == 0 {
                section.virtual_size = raw_size;
            }
            let range = section.range();
            if range.end > image_size
                || spans
                    .iter()
                    .any(|span| range.start < span.end && span.start < range.end)
            {
                return Err(format!("invalid or overlapping section {}", section.name));
            }
            if !range.is_empty() {
                spans.push(range.clone());
            }
            if raw_size != 0 {
                let raw = bytes_at(file, raw_offset, raw_size as usize)?;
                let copied = raw.len().min(range.len());
                memory[range.start..range.start + copied].copy_from_slice(&raw[..copied]);
            }
            sections.push(section);
        }

        let image = Self {
            image_base,
            entry_rva,
            memory,
            header_size,
            sections,
        };
        if image.executable_bytes_at(image.entry_point()).is_none() {
            return Err("entry point is outside executable sections".into());
        }
        Ok(image)
    }

    pub fn image_base(&self) -> u64 {
        self.image_base
    }

    pub fn entry_point(&self) -> u64 {
        self.image_base + self.entry_rva as u64
    }

    pub fn sections(&self) -> &[Section] {
        &self.sections
    }

    fn rva(&self, address: u64) -> Option<usize> {
        usize::try_from(address.checked_sub(self.image_base)?).ok()
    }

    pub fn section_at(&self, address: u64) -> Option<&Section> {
        let rva = self.rva(address)?;
        self.sections
            .iter()
            .find(|section| section.range().contains(&rva))
    }

    /// Read mapped bytes at a virtual address. Adjacent sections can be read
    /// across their boundary, but gaps and file-alignment padding are absent.
    pub fn read(&self, address: u64, size: usize) -> Option<&[u8]> {
        let rva = self.rva(address)?;
        let end = rva.checked_add(size)?;
        if end > self.memory.len() {
            return None;
        }
        if size == 0 && !(rva < self.header_size || self.section_at(address).is_some()) {
            return None;
        }
        let mut covered = rva;
        while covered < end {
            let region_end = if covered < self.header_size {
                self.header_size
            } else {
                self.sections
                    .iter()
                    .find(|section| section.range().contains(&covered))?
                    .range()
                    .end
            };
            covered = region_end.min(end);
        }
        self.memory.get(rva..end)
    }

    pub fn executable_bytes_at(&self, address: u64) -> Option<&[u8]> {
        let section = self.section_at(address)?;
        if !section.is_executable() {
            return None;
        }
        let start = self.rva(address)?;
        self.memory.get(start..section.range().end)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> Vec<u8> {
        let mut file = vec![0; 0x800];
        file[..2].copy_from_slice(b"MZ");
        file[0x3c..0x40].copy_from_slice(&0x80u32.to_le_bytes());
        file[0x80..0x84].copy_from_slice(PE_SIGNATURE);
        file[0x84..0x86].copy_from_slice(&AMD64.to_le_bytes());
        file[0x86..0x88].copy_from_slice(&2u16.to_le_bytes());
        file[0x94..0x96].copy_from_slice(&0xf0u16.to_le_bytes());
        let opt = 0x98;
        file[opt..opt + 2].copy_from_slice(&PE32_PLUS.to_le_bytes());
        file[opt + 16..opt + 20].copy_from_slice(&0x1000u32.to_le_bytes());
        file[opt + 24..opt + 32].copy_from_slice(&0x140000000u64.to_le_bytes());
        file[opt + 56..opt + 60].copy_from_slice(&0x3000u32.to_le_bytes());
        file[opt + 60..opt + 64].copy_from_slice(&0x200u32.to_le_bytes());
        let text = opt + 0xf0;
        file[text..text + 5].copy_from_slice(b".text");
        file[text + 8..text + 12].copy_from_slice(&0x20u32.to_le_bytes());
        file[text + 12..text + 16].copy_from_slice(&0x1000u32.to_le_bytes());
        file[text + 16..text + 20].copy_from_slice(&0x10u32.to_le_bytes());
        file[text + 20..text + 24].copy_from_slice(&0x400u32.to_le_bytes());
        file[text + 36..text + 40].copy_from_slice(&0x60000020u32.to_le_bytes());
        let data = text + 40;
        file[data..data + 5].copy_from_slice(b".data");
        file[data + 8..data + 12].copy_from_slice(&0x30u32.to_le_bytes());
        file[data + 12..data + 16].copy_from_slice(&0x2000u32.to_le_bytes());
        file[data + 16..data + 20].copy_from_slice(&0x10u32.to_le_bytes());
        file[data + 20..data + 24].copy_from_slice(&0x600u32.to_le_bytes());
        file[data + 36..data + 40].copy_from_slice(&0xc0000040u32.to_le_bytes());
        file[0x400..0x410].fill(0x90);
        file[0x600..0x610].fill(0x42);
        file
    }

    #[test]
    fn maps_code_data_and_zero_filled_tails() {
        let image = PeImage::parse(&fixture()).unwrap();
        assert_eq!(image.image_base(), 0x140000000);
        assert_eq!(image.entry_point(), 0x140001000);
        assert_eq!(image.read(0x140001000, 1), Some(&[0x90][..]));
        assert_eq!(image.read(0x140002000, 1), Some(&[0x42][..]));
        assert_eq!(image.read(0x140002010, 1), Some(&[0][..]));
        assert_eq!(image.read(0x14000101f, 1), Some(&[0][..]));
        assert!(image.read(0x140001020, 1).is_none());
        assert!(image.read(0x140001000, 0x1001).is_none());
        assert!(image.executable_bytes_at(0x140002000).is_none());
        assert_eq!(image.executable_bytes_at(0x140001000).unwrap().len(), 0x20);
    }

    #[test]
    fn rejects_truncated_and_overlapping_sections() {
        let mut file = fixture();
        file.truncate(0x608);
        assert!(PeImage::parse(&file).is_err());
        let mut file = fixture();
        let data_va = 0x98 + 0xf0 + 40 + 12;
        file[data_va..data_va + 4].copy_from_slice(&0x1010u32.to_le_bytes());
        assert!(PeImage::parse(&file).is_err());
    }

    #[test]
    fn excludes_file_alignment_padding_from_virtual_section() {
        let mut file = fixture();
        let text_virtual_size = 0x98 + 0xf0 + 8;
        file[text_virtual_size..text_virtual_size + 4].copy_from_slice(&8u32.to_le_bytes());
        let image = PeImage::parse(&file).unwrap();
        assert_eq!(
            image
                .executable_bytes_at(image.entry_point())
                .unwrap()
                .len(),
            8
        );
        assert!(image.read(image.entry_point() + 8, 1).is_none());
    }

    #[test]
    fn reads_across_adjacent_mapped_sections() {
        let mut file = fixture();
        let data_va = 0x98 + 0xf0 + 40 + 12;
        file[data_va..data_va + 4].copy_from_slice(&0x1020u32.to_le_bytes());
        let image = PeImage::parse(&file).unwrap();
        assert_eq!(image.read(0x14000101f, 2), Some(&[0, 0x42][..]));
    }
}
