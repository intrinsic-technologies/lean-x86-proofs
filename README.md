# lean-x86-proofs

Lemmas about [lean-x86](https://github.com/intrinsic-technologies/lean-x86). For each instruction
form it covers, the library proves what one `step` of lean-x86's machine does and states the
result as a Hoare triple with a single effect.

The library works at the level of single instructions: decoding, single steps, per-instruction
triples, and the rules that compose triples over straight-line code.

## Build

Build with the Lean toolchain named in `lean-toolchain`:

```sh
lake build
```

## Layout

| Path | Contents |
|---|---|
| `X86Proofs/Core/` | Facts about lean-x86's state and helpers that involve no stepping: its spec monads and the `spec_run` tactic, registers, flags, operands, the oracle, and the SSE and x87 value models |
| `X86Proofs/Step/` | lean-x86's `step`, taken apart: fetch, prefixes, decoding (one file per opcode byte, in `Step/Decode/`), addresses, paging and memory, and `ReadyToStep`, the machine facts every step lemma assumes |
| `X86Proofs/Program/` | Hoare triples over `step`; effects, which give every instruction the same postcondition shape; composing effects over a block; runs of lean-x86's return-boundary runner; and the write-back facts the instruction folders share (`Program/ReadWrite/`) |
| `X86Proofs/Instructions/` | One folder per instruction, holding its operation and, for each form, a decode, form, step and triple theorem |
| `X86Proofs.lean` | The library root, which imports every module |
