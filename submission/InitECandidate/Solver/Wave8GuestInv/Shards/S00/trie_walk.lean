import InitECandidate.Solver.Wave8GuestInv.Shards.S00.TrieLoop

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

/-- The trie descent is read-only; its two mutable loop-head words give a 2^128 key space. -/
theorem fb_trie_walk
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (h_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail») :
    TerminatingFunBoundedOn GuestInv (ofString "trie_walk") K.«trie_walk» := by
  fb_unfold 266 Guest.Software.guestFn_trie_walk
  refine TerminatingProgBoundedOn.weaken'
    (K := (71723149827058354885847154688 + 1) * (Trie.bodyK + 1) + 0) ?_ ?_
  · refine Trie.dec_on' (Q := Trie.Pinv) _ _
      (fun s v hP hv => ⟨guestInv_setVar _ _ _ hP, Trie.setVar_word s _ v hv⟩) ?_
    exact Trie.seq_on' (Trie.loop_bound h_memeq h_mpt_fail)
      (fun s _ hP _ => guestInv_evaluate s _ hP.1) (straightOn _ rfl)
  · unfold K.«trie_walk» Trie.bodyK
    simp only [nat_max_eq]
    omega


end InitECandidate.Solver.Wave8Leaves.S00
