import InitECandidate.Solver.Wave8GuestInv.R11Shards.EvmBase
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M21.ek_charge_gas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.ek_stack_pop

/-! # Base definitions and `DispatchSpecWalk` combinators for `op_dispatch_spec` (R11) -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. Self-contained EVM potential and `FunSpec` vocabulary (pre-`C00`) -/

def evmR {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum

def evmFp {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  2 * (evmChain s).length + (if EvmDone s then 0 else 1)

def evmS {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  ((evmChain s).map fun ec => memW s (ec.1 + 72)).sum

def IsEvmErr (r : Option (PanSemResultExact 64)) : Prop :=
  ∃ v, r = some (.exception (ofString "EvmErr") v)

def EvmRun : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ ¬ EvmDone s

theorem evmPot_eq {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evmPot s = evmR s * (evmPotF * evmPotS) + evmFp s * evmPotS + evmS s := rfl

theorem evmFp_done {F : Type} {t : PanSemStateFiniteExact 64 F} (h : EvmDone t) :
    evmFp t = 2 * (evmChain t).length := by
  simp [evmFp, h]

theorem evmFp_notDone {F : Type} {t : PanSemStateFiniteExact 64 F} (h : ¬ EvmDone t) :
    evmFp t = 2 * (evmChain t).length + 1 := by
  simp [evmFp, h]

theorem evmFp_le {F : Type} (t : PanSemStateFiniteExact 64 F) :
    evmFp t ≤ 2 * (evmChain t).length + 1 := by
  unfold evmFp; split <;> omega

theorem localsFree_evmInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : EvmInv s) :
    EvmInv { s with locals := locals, clock := k } := by
  have hGp : GuestInv { s with locals := locals, clock := k } :=
    guestInv_with_locals_clock s locals k h.1.1
  exact (evmInv_of_head_status_gas_update h hGp rfl rfl (fun _ _ => rfl) (le_refl _)).1

theorem memW_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : t.memory = s.memory) :
    memW t = memW s := by
  funext a; simp [memW, h]

theorem globN_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : t.globals = s.globals) :
    globN t = globN s := by
  funext a; simp [globN, h]

theorem evmChainFrom_congr {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : t.memory = s.memory) :
    ∀ (fuel e c : Nat), evmChainFrom t fuel e c = evmChainFrom s fuel e c
  | 0, _, _ => rfl
  | fuel + 1, e, c => by
    simp only [evmChainFrom, memW_congr h, evmChainFrom_congr h fuel]

theorem evmChain_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) : evmChain t = evmChain s := by
  simp only [evmChain, evmChainFrom_congr hm, globN_congr hg]

theorem evmDone_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) : EvmDone t ↔ EvmDone s := by
  simp only [EvmDone, memW_congr hm, globN_congr hg]

theorem evm_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) :
    evmPot t = evmPot s ∧ evmR t = evmR s ∧ (evmChain t).length = (evmChain s).length ∧
      evmFp t = evmFp s := by
  have hc := evmChain_congr hm hg
  have hd := evmDone_congr hm hg
  refine ⟨?_, ?_, by rw [hc], ?_⟩
  · simp only [evmPot, hc, memW_congr hm, hd]
  · simp only [evmR, hc, memW_congr hm]
  · simp only [evmFp, hc, hd]

theorem memW_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : memW s a < 2 ^ 64 := by
  unfold memW; split; rename_i w _; exact w.isLt

theorem sum_map_memW_le {F : Type} (s : PanSemStateFiniteExact 64 F) (off : Nat) :
    ∀ l : List Ivl, (l.map fun ec => memW s (ec.1 + off)).sum ≤ l.length * (2 ^ 64 - 1)
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := memW_lt s (x.1 + off)
    have h2 := sum_map_memW_le s off xs
    omega

theorem evmInv_len {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    (evmChain s).length ≤ maxChain := by
  obtain ⟨_, S, hS⟩ := h; exact hS.2.2.1

theorem evmS_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) : evmS s < evmPotS := by
  have hlen := evmInv_len s h
  have hle := sum_map_memW_le s 72 (evmChain s)
  have hm : (evmChain s).length * (2 ^ 64 - 1) < maxChain * 2 ^ 64 := by
    have : (evmChain s).length * (2 ^ 64 - 1) ≤ maxChain * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_right _ hlen
    simp only [maxChain] at this ⊢; omega
  show ((evmChain s).map fun ec => memW s (ec.1 + 72)).sum < maxChain * 2 ^ 64
  omega

theorem evmFp_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    evmFp s < evmPotF := by
  have hlen := evmInv_len s h
  unfold evmFp evmPotF
  simp only [maxChain] at hlen ⊢
  split <;> omega

theorem evmPot_lt_bound {F : Type} (t : PanSemStateFiniteExact 64 F) (h : EvmInv t) {R0 F0 : Nat}
    (hR : evmR t ≤ R0) (hF : evmFp t < F0) :
    evmPot t < R0 * (evmPotF * evmPotS) + F0 * evmPotS := by
  have hS := evmS_lt t h
  have hFp := evmFp_lt t h
  rw [evmPot_eq]
  rcases Nat.lt_or_ge (evmR t) R0 with hlt | hge
  · have h1 : evmFp t * evmPotS + evmS t < evmPotF * evmPotS := by
      have : (evmFp t + 1) * evmPotS ≤ evmPotF * evmPotS := Nat.mul_le_mul_right _ hFp
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    have h2 : (evmR t + 1) * (evmPotF * evmPotS) ≤ R0 * (evmPotF * evmPotS) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  · have hReq : evmR t = R0 := le_antisymm hR hge
    have h2 : (evmFp t + 1) * evmPotS ≤ F0 * evmPotS := Nat.mul_le_mul_right _ hF
    rw [Nat.add_mul, Nat.one_mul] at h2; rw [hReq]; omega

theorem evmPot_ge {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evmR s * (evmPotF * evmPotS) + evmFp s * evmPotS ≤ evmPot s := by
  rw [evmPot_eq]; omega

/-! ## 2. Postcondition of `op_dispatch` and `op_*` handlers -/

def OpDispatchPost {F : Type} (s : PanSemStateFiniteExact 64 F)
    (r : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F) : Prop :=
  ((∃ v, r = some (.returned v)) → EvmInv post ∧ evmPot post < evmPot s) ∧
  (IsEvmErr r → EvmInv post ∧ (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)

def OpHandlerSpec (fname : MlS) : Prop :=
  FunSpec EvmRun OpDispatchPost fname

theorem opDispatchPost_congr_lc {F : Type}
    {s s' post post' : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hs_m : s'.memory = s.memory) (hs_g : s'.globals = s.globals)
    (hp_lc : post' = { post with locals := post'.locals, clock := post'.clock })
    (h : OpDispatchPost s' r post) :
    OpDispatchPost s r post' := by
  have hs := evm_congr hs_m hs_g
  have hp_m : post'.memory = post.memory := by rw [hp_lc]
  have hp_g : post'.globals = post.globals := by rw [hp_lc]
  have hp := evm_congr hp_m hp_g
  have hinv : EvmInv post → EvmInv post' := fun h0 => by
    rw [hp_lc]; exact localsFree_evmInv post post'.locals post'.clock h0
  refine ⟨fun hret => ?_, fun herr => ?_⟩
  · obtain ⟨hi, hlt⟩ := h.1 hret
    exact ⟨hinv hi, by rw [hp.1, ← hs.1]; exact hlt⟩
  · obtain ⟨hi, hlen, hR⟩ := h.2 herr
    exact ⟨hinv hi, by rw [hp.2.2.1, ← hs.2.2.1]; exact hlen,
      by rw [hp.2.1, ← hs.2.1]; exact hR⟩

theorem opDispatchPost_error {F : Type} (s t : PanSemStateFiniteExact 64 F) :
    OpDispatchPost s (some .error) t := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, h⟩
    cases h
  · rintro ⟨_, h⟩
    cases h

theorem opDispatchPost_other {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hnret : ∀ v, r ≠ some (.returned v)) (hnerr : ¬ IsEvmErr r) :
    OpDispatchPost s r t :=
  ⟨fun ⟨v, hv⟩ => (hnret v hv).elim, fun he => (hnerr he).elim⟩

/-! ## 3. Potential decrease lemmas for `op_*` handlers -/

theorem evmPot_lt_of_done {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hRun : EvmRun s) (hInv : EvmInv post) (hDone : EvmDone post)
    (hlen : (evmChain post).length ≤ (evmChain s).length)
    (hR : evmR post ≤ evmR s) :
    evmPot post < evmPot s := by
  have hFp_s : evmFp s = 2 * (evmChain s).length + 1 := evmFp_notDone hRun.2
  have hFp_p : evmFp post = 2 * (evmChain post).length := evmFp_done hDone
  have hF_lt : evmFp post < evmFp s := by omega
  have hlt := evmPot_lt_bound post hInv hR hF_lt
  have hge := evmPot_ge s
  omega

theorem evmPot_lt_of_chain_shorter {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hRun : EvmRun s) (hInv : EvmInv post)
    (hlen : (evmChain post).length < (evmChain s).length)
    (hR : evmR post ≤ evmR s) :
    evmPot post < evmPot s := by
  have hFp_s : evmFp s = 2 * (evmChain s).length + 1 := evmFp_notDone hRun.2
  have hFp_p : evmFp post ≤ 2 * (evmChain post).length + 1 := evmFp_le post
  have hF_lt : evmFp post < evmFp s := by omega
  have hlt := evmPot_lt_bound post hInv hR hF_lt
  have hge := evmPot_ge s
  omega

theorem evmPot_lt_of_evmR_lt {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv post) (hR_lt : evmR post < evmR s) :
    evmPot post < evmPot s := by
  have hS := evmS_lt post hInv
  have hFp := evmFp_lt post hInv
  rw [evmPot_eq post]
  have h1 : evmFp post * evmPotS + evmS post < evmPotF * evmPotS := by
    have : (evmFp post + 1) * evmPotS ≤ evmPotF * evmPotS := Nat.mul_le_mul_right _ hFp
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have h2 : (evmR post + 1) * (evmPotF * evmPotS) ≤ evmR s * (evmPotF * evmPotS) :=
    Nat.mul_le_mul_right _ hR_lt
  rw [Nat.add_mul, Nat.one_mul] at h2
  have hge := evmPot_ge s
  omega

theorem evmPot_lt_of_evmS_lt {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv post) (hR : evmR post ≤ evmR s)
    (hF : evmFp post ≤ evmFp s) (hS_lt : evmS post < evmS s) :
    evmPot post < evmPot s := by
  rcases Nat.lt_or_ge (evmR post) (evmR s) with hR_lt | hR_ge
  · exact evmPot_lt_of_evmR_lt hInv hR_lt
  · have hR_eq : evmR post = evmR s := le_antisymm hR hR_ge
    rcases Nat.lt_or_ge (evmFp post) (evmFp s) with hF_lt | hF_ge
    · have hlt := evmPot_lt_bound post hInv hR hF_lt
      have hge := evmPot_ge s
      omega
    · have hF_eq : evmFp post = evmFp s := le_antisymm hF hF_ge
      rw [evmPot_eq post, evmPot_eq s, hR_eq, hF_eq]
      omega

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
