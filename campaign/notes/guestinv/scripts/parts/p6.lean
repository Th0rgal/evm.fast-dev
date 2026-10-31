
/-! ## 8. `K_pan` and the budget -/

/-- The proposed total source budget: the generated bound of `main` plus the entry tick. -/
def K_pan : Nat := K.«main» + 1

/-- Kernel-checked budget inequality (target side `32·K + 23077`, `ConcreteStage1To5Transfer`). -/
theorem K_pan_budget : 32 * K_pan + 23077 ≤ (10 ^ 299 - 1) / 10 ^ 4 := by decide

/-- End-to-end target of the campaign under this proposal. Its only `sorry` dependencies are the
leaves below `main` (through `gb_main`). -/
theorem coveredSourceTicksConsumedBounded_K_pan : CoveredSourceTicksConsumedBounded K_pan :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnEntry «gb_main»

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

end InitECandidate.Solver.Wave8GuestInv
