use super::Report;
use std::fmt::Write;

impl Report {
    pub fn render(&self) -> String {
        let mut output = String::from("// Tier 6 arithmetic analysis (bit-vector sums)\n");
        for (heading, loops) in [("input", &self.before), ("remaining", &self.remaining)] {
            for analysis in loops {
                writeln!(
                    output,
                    "// {heading} loop 0x{:x}: {}",
                    analysis.offset, analysis.check
                )
                .unwrap();
                for (variable, value) in &analysis.updates {
                    writeln!(output, "//   v{}' = {}", variable.id, value).unwrap();
                }
                if let Some(shape) = &analysis.subtraction {
                    writeln!(
                        output,
                        "//   repeated subtraction: v{}, stride {}, u{}",
                        shape.accumulator.id, shape.stride, shape.bits
                    )
                    .unwrap();
                    for blocker in &shape.blockers {
                        writeln!(output, "//   blocked: {blocker}").unwrap();
                    }
                    if shape.blockers.is_empty() {
                        writeln!(output, "//   unknown strides require allow_assumptions").unwrap();
                    }
                } else {
                    writeln!(output, "//   no registered arithmetic shape").unwrap();
                }
            }
        }
        for rewrite in &self.rewrites {
            writeln!(
                output,
                "// rewrite at 0x{:x}: {}",
                rewrite.offset, rewrite.rule
            )
            .unwrap();
        }
        if self.budget_exhausted {
            writeln!(
                output,
                "// rewrite budget exhausted; unmatched code retained"
            )
            .unwrap();
        }
        output
    }
}
