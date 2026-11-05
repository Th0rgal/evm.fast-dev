import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmStepLemmas

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.PanSemStateFiniteExact

 theorem evmChainFrom_stable {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fuel e c : Nat) (h : (evmChainFrom s fuel e c).length < fuel) :
    evmChainFrom s (fuel + 1) e c = evmChainFrom s fuel e c := by
  induction fuel generalizing e c with
  | zero => simp at h
  | succ fuel ih =>
    by_cases hk : memW s (c + 16) = 0
    · simp [evmChainFrom, hk]
    · have ht : (evmChainFrom s fuel (memW s c) (memW s (c + 8))).length < fuel := by
        simpa only [evmChainFrom, if_neg hk, List.length_cons, Nat.add_lt_add_iff_right] using h
      have he := congrArg (List.cons (e, c))
        (ih (memW s c) (memW s (c + 8)) ht)
      simpa only [evmChainFrom, if_neg hk] using he

 theorem evmChain_parent {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hkind : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hlen : (evmChain s).length ≤ maxChain) :
    evmChainFrom s (maxChain + 1)
        (memW s (globN s "cur_cont")) (memW s (globN s "cur_cont" + 8)) =
      (evmChain s).tail := by
  have hcons : evmChain s = (globN s "ev", globN s "cur_cont") ::
      evmChainFrom s maxChain (memW s (globN s "cur_cont"))
        (memW s (globN s "cur_cont" + 8)) := by
    simp only [evmChain, evmChainFrom, if_neg hkind]
  rw [hcons] at hlen ⊢
  simp only [List.tail_cons]
  exact evmChainFrom_stable s _ _ _ (by simp only [List.length_cons] at hlen; omega)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
