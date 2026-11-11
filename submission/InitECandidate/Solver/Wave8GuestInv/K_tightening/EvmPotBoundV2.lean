import InitECandidate.Solver.Wave8GuestInv.K_tightening.V23Prewarm

/-!
# v2 potential bound: `EvmInv s → evmPot s < evmPotMaxV2`

This is the genuine cutover obligation left open by `V23Prewarm.lean`.  The
argument only uses the two conjuncts of `EvmInv` that bound the chain:

* `(evmChain s).length ≤ maxChain` (here `maxChain = 16384`);
* the regular-gas sum `R = Σ (gas + spilled)` satisfies `R + 1 < 2^64`.

Every memory word is a `BitVec 64`, so the state-gas sum `S` is at most
`chain.length * (2^64 - 1)`, and the frame component `F` is at most
`2 * chain.length + 1`.  With those three linear bounds the potential

`R * (evmPotF * evmPotS) + F * evmPotS + S`

is below `2^160 = evmPotMaxV2`.  No new assumption is introduced: the proof is
a consequence of `EvmInv` alone.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open K

/-- Every memory read is a `BitVec 64`, hence below `2^64`. -/
theorem memW_lt_two_pow_64 {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    memW s a < 2 ^ 64 := by
  unfold memW
  split
  rename_i w _
  exact w.isLt

/-- A sum of `n` memory words is at most `n * (2^64 - 1)`. -/
theorem sum_map_memW_le {F : Type} (s : PanSemStateFiniteExact 64 F) (off : Nat) :
    ∀ l : List Ivl, (l.map fun ec => memW s (ec.1 + off)).sum ≤ l.length * (2 ^ 64 - 1)
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := memW_lt_two_pow_64 s (x.1 + off)
    have h2 := sum_map_memW_le s off xs
    omega

/-- The chain-length conjunct of `EvmInv`. -/
theorem evmInv_chain_len {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    (evmChain s).length ≤ maxChain := by
  obtain ⟨-, S, -, hrest⟩ := h
  exact hrest.2.1

/-- The regular-gas conjunct of `EvmInv`. -/
theorem evmInv_gas_sum {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum + 1 < 2 ^ 64 := by
  obtain ⟨-, S, -, hrest⟩ := h
  exact hrest.2.2.2.2.2.2.2.2.2.2.2

/-- Unfolding of the lexicographic potential into its three components. -/
theorem evmPot_unfold {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evmPot s =
      ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum *
          (evmPotF * evmPotS) +
        (2 * (evmChain s).length + (if EvmDone s then 0 else 1)) * evmPotS +
        ((evmChain s).map fun ec => memW s (ec.1 + 72)).sum := rfl

/-- The v2 potential bound: `EvmInv` bounds `evmPot` by `2^160`. -/
theorem evmPot_lt_evmPotMaxV2 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : EvmInv s) : evmPot s < evmPotMaxV2 := by
  have hlen := evmInv_chain_len s h
  have hR := evmInv_gas_sum s h
  have hSle := sum_map_memW_le s 72 (evmChain s)
  have hlen' : (evmChain s).length ≤ 16384 := hlen
  have hF : evmPotF = 2 * 16384 + 2 := rfl
  have hS : evmPotS = 16384 * 2 ^ 64 := rfl
  rw [evmPot_unfold, evmPotMaxV2, hF, hS]
  set n := (evmChain s).length with hn
  set R := ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum with hRdef
  set Sg := ((evmChain s).map fun ec => memW s (ec.1 + 72)).sum with hSdef
  have hRlt : R < 2 ^ 64 := by omega
  have hSbound : Sg ≤ n * (2 ^ 64 - 1) := hSle
  have hFple : 2 * n + (if EvmDone s then 0 else 1) ≤ 2 * 16384 + 1 := by
    split <;> omega
  by_cases hd : EvmDone s <;>
    simp only [hd, if_true, if_false] at hFple ⊢ <;>
    omega

end InitECandidate.Solver.Wave8GuestInv
