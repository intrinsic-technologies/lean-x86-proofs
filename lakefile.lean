import Lake
open Lake DSL

package x86proofs

require x86 from git
  "https://github.com/intrinsic-technologies/lean-x86.git" @ "v0.0.2"

@[default_target]
lean_lib X86Proofs
