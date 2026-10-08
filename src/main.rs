mod irt0;
mod pe;

use std::{
    error::Error,
    fs, io,
    path::{Path, PathBuf},
};

use iced_x86::{Decoder, DecoderOptions, Mnemonic};

// The byte-string hash function is the default decompilation target.
// --address (or --entry) selects another function in the loaded image.
const EXAMPLE_ADDRESS: u64 = 0x14008d690;

fn has_pe_signature(bytes: &[u8]) -> bool {
    if !bytes.starts_with(b"MZ") {
        return false;
    }
    let Some(offset) = bytes.get(0x3c..0x40) else {
        return false;
    };
    let offset = u32::from_le_bytes(offset.try_into().unwrap()) as usize;
    bytes.get(offset..offset.saturating_add(4)) == Some(b"PE\0\0".as_slice())
}

fn first_pe_file(directory: &Path) -> io::Result<(PathBuf, Vec<u8>)> {
    let mut paths = fs::read_dir(directory)?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<io::Result<Vec<_>>>()?;
    paths.sort();
    for path in paths {
        if path.is_file() {
            let bytes = fs::read(&path)?;
            if has_pe_signature(&bytes) {
                return Ok((path, bytes));
            }
        }
    }
    Err(io::Error::new(
        io::ErrorKind::NotFound,
        format!("no PE binary found in {}", directory.display()),
    ))
}

fn number(text: &str) -> Result<u64, Box<dyn Error>> {
    Ok(if let Some(hex) = text.strip_prefix("0x") {
        u64::from_str_radix(hex, 16)?
    } else {
        text.parse()?
    })
}

fn function_bytes<'a>(
    image: &'a pe::PeImage,
    address: u64,
    length: Option<usize>,
) -> Result<&'a [u8], Box<dyn Error>> {
    let bytes = image
        .executable_bytes_at(address)
        .ok_or_else(|| format!("address 0x{address:x} is outside an executable PE section"))?;
    if let Some(length) = length {
        return bytes
            .get(..length)
            .ok_or_else(|| "function length exceeds executable section".into());
    }

    // Leaf functions may not appear in .pdata. Compiler-generated INT3
    // padding gives the current example an instruction-aligned endpoint.
    // Callers can provide --length for a function without this padding.
    let mut decoder = Decoder::with_ip(64, bytes, address, DecoderOptions::NONE);
    while decoder.can_decode() {
        let instruction = decoder.decode();
        if instruction.mnemonic() == Mnemonic::Int3 {
            let length = usize::try_from(instruction.ip() - address)?;
            return Ok(&bytes[..length]);
        }
    }
    Err("no INT3 function boundary found; supply --length".into())
}

fn run() -> Result<(), Box<dyn Error>> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let mut address = None;
    let mut length = None;
    let mut use_entry = false;
    let mut list_sections = false;
    let mut read_request = None;
    let mut tier = 6;
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "--address" | "--length" => {
                let option = &args[index];
                let value = args
                    .get(index + 1)
                    .ok_or_else(|| format!("missing value for {option}"))?;
                let parsed = number(value)?;
                if option == "--address" {
                    address = Some(parsed);
                } else {
                    length = Some(usize::try_from(parsed)?);
                }
                index += 2;
            }
            "--tier" => {
                tier = number(args.get(index + 1).ok_or("missing value for --tier")?)?;
                if !(1..=6).contains(&tier) {
                    return Err("--tier must be between 1 and 6".into());
                }
                index += 2;
            }
            "--entry" => {
                use_entry = true;
                index += 1;
            }
            "--list-sections" => {
                list_sections = true;
                index += 1;
            }
            "--read" => {
                let address = number(args.get(index + 1).ok_or("missing address for --read")?)?;
                let size = usize::try_from(number(
                    args.get(index + 2).ok_or("missing size for --read")?,
                )?)?;
                read_request = Some((address, size));
                index += 3;
            }
            other => return Err(format!("unknown option: {other}").into()),
        }
    }
    if use_entry && address.is_some() {
        return Err("--entry and --address cannot be used together".into());
    }

    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("samplebinary");
    let (path, file) = first_pe_file(&directory)?;
    let image =
        pe::PeImage::parse(&file).map_err(|error| format!("{}: {error}", path.display()))?;
    if list_sections {
        println!(
            "{}: image base 0x{:x}, entry 0x{:x}",
            path.display(),
            image.image_base(),
            image.entry_point()
        );
        for section in image.sections() {
            println!(
                "{:<8} 0x{:x}..0x{:x} raw 0x{:x} {}",
                section.name,
                image.image_base() + section.virtual_address as u64,
                image.image_base() + section.virtual_address as u64 + section.virtual_size as u64,
                section.raw_size,
                if section.is_executable() {
                    "code"
                } else {
                    "data"
                },
            );
        }
        return Ok(());
    }
    if let Some((address, size)) = read_request {
        let bytes = image.read(address, size).ok_or_else(|| {
            format!(
                "0x{address:x}..0x{:x} crosses unmapped image bytes",
                address.saturating_add(size as u64)
            )
        })?;
        for byte in bytes {
            print!("{byte:02x}");
        }
        println!();
        return Ok(());
    }

    let address = address.unwrap_or(if use_entry {
        image.entry_point()
    } else {
        EXAMPLE_ADDRESS
    });
    let code = function_bytes(&image, address, length)?;
    if code.is_empty() {
        return Err("selected function is empty".into());
    }
    let irt0program = irt0::lift(code, usize::try_from(address)?);

    for instr in irt0program.instructions {
        println!("{:?}", instr.1);
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
