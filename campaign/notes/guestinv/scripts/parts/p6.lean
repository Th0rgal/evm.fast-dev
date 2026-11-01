
/-! ## 8. `K_pan` and the budget -/

/-- The proposed total source budget: the generated bound of `main` plus the entry tick. -/
def K_pan : Nat := K.«main» + 1

/-- Kernel-checked target budget after the concrete stage transfer. -/
def K_target : Nat := 118223496 * K_pan + 119233963

theorem K_target_budget : 118223496 * K_pan + 119233963 ≤ 10 ^ 122 - 1 := by decide

theorem K_pan_budget : K_target ≤ 10 ^ 122 - 1 := K_target_budget

/-- The conditional assembly (round-3 assembly ruling), PROVED and `sorry`-free: the primitive
obligations imply the campaign target. `#print axioms assembly` lists no `sorryAx`. -/
theorem assembly (P : Primitives) : CoveredSourceTicksConsumedBounded K_pan :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnEntry (assembly_main P)

/-- End-to-end target of the campaign under this proposal: the assembly applied to the leaves. Its
`sorry` dependencies are exactly the primitive leaves (`primitives`). -/
theorem coveredSourceTicksConsumedBounded_K_pan : CoveredSourceTicksConsumedBounded K_pan :=
  assembly primitives

/-! ### Round-1 counterexamples, pinned (each is the tick count of the counterexample run) -/

/-- Item 2, `sort_elems` with `esz = 0`, `n = 2^62`: at least `n` merge iterations. -/
example : 2 ^ 62 ≤ K.«sort_elems» := by decide

/-- Item 2, `htr_payload` / `htr_new_payload_request` with `ntx = 2^59`: ≈ 2.9·10^16 ticks. -/
example : 29000000000000000 ≤ K.«htr_payload» := by decide
example : 29000000000000000 ≤ K.«htr_new_payload_request» := by decide

/-- Item 2, self-looping extension node: `6·W` resp. `5.25·W` ticks. -/
example : 6 * domainBytes ≤ K.«_mpt_insert_node» := by decide
example : 6 * domainBytes ≤ K.«trie_walk» := by decide

/-- Item 2, `rlp_list_count` over `W − 10` bytes of `0xc0` (9 ticks per byte). -/
example : 9 * domainBytes ≤ K.«tx_scalar_word» := by decide
example : 9 * domainBytes ≤ K.«hdr_word_field» := by decide

/-- Item 2, 16 000 lookups with `W/2`-byte keys: ≈ 7.7·10^12 ticks. -/
example : 7700000000000 ≤ K.«_decode_witness_node_body» := by decide

/-- Item 3, `htab_union_into` with `src.count = 2^62` aliasing `dst` (2^62 `htab_item` calls),
and `finish_child` reaching it. -/
example : 2 ^ 62 * (K.«htab_item» + 1) ≤ K.«htab_union_into» := by decide
example : 2 ^ 62 ≤ K.«finish_child» := by decide

/-- Item 5, `incorporate_child_on_error` after a `2^62` mint: ≈ 2^58 `run_frames` iterations. -/
example : 2 ^ 58 ≤ evmPotMax := by decide

-- The revision-9 check records the trusted-axiom boundary in the same single-file Lean run.
#print axioms assembly
#print axioms assembly_main
#print axioms K_pan_budget
#print axioms K_target_budget
#print axioms bufferRegion_disj
#print axioms bufferRegion_disj_le
#print axioms AllocatorGrows.allocated
#print axioms FreshBlock.disj_allocated

end InitECandidate.Solver.Wave8GuestInv
