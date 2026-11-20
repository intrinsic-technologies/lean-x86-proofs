import Lean

/-!
# Simp sets for composing blocks

Registered here because a simp attribute cannot be used in the file that registers it.

- `x86_compose`: what `x86_norm` unfolds and rewrites to put a composed effect in normal form
  (the effect definitions of the instruction triples, the canonical-state reads, address and
  flag arithmetic). `Program/Compose.lean` fills it with the generic facts, and each
  instruction's `Triple.lean` with its effect definitions.
- `x86_local`: the `Effect.Local` fact of each instruction effect (at the end of the instruction's
  `Triple.lean`), which `x86_local` closes goals with.

For carrying an instruction's precondition over to the state after a block (`x86_mid`,
`Program/Compose.lean`):

- `x86_pre` (a label): the carry-over lemmas, one per precondition shape, `X.of_holds`: from the
  block so far holding (`h : e.Holds s s'`) and the canonical state (`ho : Obs (e.after s true)
  s'`), `X … s'` follows from facts about the start state `s` and the canonical state. Tried in
  order by the head of their conclusion.
- `x86_obs` (a label): `Obs t t' → f t' = f t` for the reads an instruction makes (`Obs.back_reg`,
  …), applied to `ho` to rewrite reads of the state after the block into the canonical state.
- `x86_inv` (a label): `e.Holds s s' → f s' = f s` (or `↔`) for what every effect keeps (control
  registers, CPUID, segment registers, …), applied to `h`.
- `x86_pre_simp`: the normal form both the goals and the block's precondition are brought to
  (state fields as operand reads, `MxcsrPre` and `DirectionFlagClear` as reads, …).
- `x86_addr`: the address functions (`storeAddrAt`, `stackPtr`, …) to unfold when showing that
  an address reads only what `Obs` sees (`AddrObs`).
-/

register_simp_attr x86_compose
register_simp_attr x86_local
register_label_attr x86_pre
register_label_attr x86_obs
register_label_attr x86_inv
register_simp_attr x86_pre_simp
register_simp_attr x86_addr
