import InitECandidate.Solver.GuestGasAndHtabBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.SourceWitnessClockBound`

Minimal source clock witness `k_min = Nat.find h` for `sourceBehaviour input = .terminate …`.

`sourceBehaviour` is `semanticsDecls` (an `∃ k, evaluate … k ≠ timeOut` choice).
Here:
* `NotTO s k` : running `"main"` from `s` at clock `k` does not time out.
* `k_min` is the least such clock; `NotTO` is upward closed (add-clock lemma), so
  `NotTO s K ↔ k_min ≤ K`. Hence discharging `k_min ≤ maxGuestSourceClock`
  is *exactly* exhibiting one non-timeout run at a budget `≤ maxGuestSourceClock`
  (e.g. `guestSourceClockBudget gasSteps d probe init` from `GuestGasAndHtabBound`).
* Hash-table capacity: from `htab_new(_,16)`, after `n ≤ 105,263` gas-paid fresh keys
  the capacity is a power of two `≤ 262,144`, and exactly `262,144` at `n = 105,263`.

Not proved here: that the Guest program's actual `PanSem` run fits the
`guestSourceClockBudget` shape (per-gas-step tick accounting of the 825 functions).
That remains the open semantic obligation (`hbudget` hypotheses below).
-/

namespace InitECandidate.Solver.SourceWitnessClockBound

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.HtabLoadFactorBound
open InitECandidate.Solver.GuestGasAndHtabBound
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang

/-- Running `"main"` from `s` at clock `k` does not time out. -/
def NotTO (s : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat) : Prop :=
  (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
    (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut

/-- 1. Upward closure of non-timeout in the clock. -/
theorem notTO_mono (s : PanSemStateFiniteExact 64 Guest.HostMemory) {k K : Nat}
    (hk : NotTO s k) (hle : k ≤ K) : NotTO s K := by
  unfold NotTO at *
  rcases hrun : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
      (.call none (ofString "main") [] : ProgHOL 64) with ⟨res, s'⟩
  rw [hrun] at hk
  have hadd := panPropsEvaluateAddClockEq (.call none (ofString "main") [] : ProgHOL 64)
    { s with clock := k } res s' (K - k) ⟨hrun, hk⟩
  have hst_eq : ({ { s with clock := k } with clock := k + (K - k) } :
      PanSemStateFiniteExact 64 Guest.HostMemory) = { s with clock := K } := by
    simp only [Nat.add_sub_of_le hle]
  rw [hst_eq] at hadd
  rw [hadd]
  exact hk

/-- 2. Terminating source ⇒ a declaration state with some non-timeout clock. -/
theorem exists_notTO_of_terminate (input : Guest.InputBlob) (outcome : HolOutcome)
    (events : List HolIoEvent) (hsource : sourceBehaviour input = .terminate outcome events) :
    ∃ stCtxt s_decls,
      decsStcnamesHOLExact [] sourceDeclarations = some stCtxt ∧
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
        { sourceInitialState input with structs := stCtxt }
        (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
        sourceDeclarations = some s_decls ∧
      ∃ k, NotTO s_decls k := by
  obtain ⟨stCtxt, s_decls, k, res, post, hst, hdec, hev, hnt, _, _, _⟩ :=
    sourceBehaviour_terminate_clock_stabilizes input outcome events hsource
  refine ⟨stCtxt, s_decls, hst, hdec, k, ?_⟩
  unfold NotTO; rw [hev]; exact hnt

/-- The minimal witness `k_min = Nat.find h`. -/
noncomputable def kMin (s : PanSemStateFiniteExact 64 Guest.HostMemory) (h : ∃ k, NotTO s k) : Nat :=
  Nat.find h

/-- 3. `k_min` is itself a non-timeout clock. -/
theorem kMin_spec (s : PanSemStateFiniteExact 64 Guest.HostMemory) (h : ∃ k, NotTO s k) :
    NotTO s (kMin s h) := Nat.find_spec h

/-- 4. Every clock strictly below `k_min` times out (minimality). -/
theorem lt_kMin_timeOut (s : PanSemStateFiniteExact 64 Guest.HostMemory) (h : ∃ k, NotTO s k)
    (k : Nat) (hk : k < kMin s h) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
      (.call none (ofString "main") [] : ProgHOL 64)).1 = some .timeOut := by
  have := Nat.find_min h hk
  unfold NotTO at this
  exact Classical.not_not.mp this

/-- 5. Exact characterisation: non-timeout at `K` iff `k_min ≤ K`. -/
theorem notTO_iff_kMin_le (s : PanSemStateFiniteExact 64 Guest.HostMemory) (h : ∃ k, NotTO s k)
    (K : Nat) : NotTO s K ↔ kMin s h ≤ K :=
  ⟨fun hK => Nat.find_min' h hK, fun hle => notTO_mono s (kMin_spec s h) hle⟩

/-- 6. Discharge rule: one non-timeout run at a budget `B ≤ maxGuestSourceClock`
gives `k_min ≤ maxGuestSourceClock` (and conversely, via 5). -/
theorem kMin_le_max_iff (s : PanSemStateFiniteExact 64 Guest.HostMemory) (h : ∃ k, NotTO s k) :
    kMin s h ≤ maxGuestSourceClock ↔ ∃ B, B ≤ maxGuestSourceClock ∧ NotTO s B := by
  constructor
  · intro hle; exact ⟨kMin s h, hle, kMin_spec s h⟩
  · rintro ⟨B, hB, hnt⟩; exact Nat.le_trans (Nat.find_min' h hnt) hB

/-- 7. Gas/call-graph/probe budget form: a non-timeout run at
`guestSourceClockBudget gasSteps d probe init` (gas ≤ 200M, depth ≤ 18,
probe ≤ 200, init ≤ maxInputBytes) bounds `k_min ≤ 43,934,217,712`. -/
theorem kMin_le_maxGuestSourceClock_of_budget
    (s : PanSemStateFiniteExact 64 Guest.HostMemory) (h : ∃ k, NotTO s k)
    (gasSteps d probeBudget initTicks : Nat)
    (hgas : gasSteps ≤ maxBlockGasLimit) (hd : d ≤ guestCallGraphMaxDepth)
    (hprobe : probeBudget ≤ 200) (hinit : initTicks ≤ Guest.maxInputBytes)
    (hbudget : NotTO s (guestSourceClockBudget gasSteps d probeBudget initTicks)) :
    kMin s h ≤ guestSourceClockBudget gasSteps d probeBudget initTicks ∧
      kMin s h ≤ maxGuestSourceClock := by
  have h1 := Nat.find_min' h hbudget
  have h2 := (guestSourceClockBudget_le_max gasSteps d probeBudget initTicks hgas hd hprobe hinit).1
  exact ⟨h1, Nat.le_trans h1 h2⟩

/-- 8. At `k_min` (and every `K ≥ k_min`) the source completes with `outcome` and `events`. -/
theorem complete_at_ge_kMin (input : Guest.InputBlob) (outcome : HolOutcome)
    (events : List HolIoEvent) (hsource : sourceBehaviour input = .terminate outcome events)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (h : ∃ k, NotTO s_decls k) (K : Nat) (hK : kMin s_decls h ≤ K) :
    panEntryClass (PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := K }
      (.call none (ofString "main") [] : ProgHOL 64)).1 = .CompleteResult outcome ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := K }
      (.call none (ofString "main") [] : ProgHOL 64)).2.ffi.ioEvents = events := by
  have hnt := notTO_mono s_decls (kMin_spec s_decls h) hK
  rcases hrun : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := K }
      (.call none (ofString "main") [] : ProgHOL 64) with ⟨res, post⟩
  unfold NotTO at hnt; rw [hrun] at hnt
  exact sourceBehaviour_not_timeOut_at_budget_complete input outcome events hsource stCtxt
    s_decls hst hev_decls K res post hrun hnt

/-! ## Hash-table capacity under the gas bound -/

/-- Capacity invariant: power of two `16·2^j`, and either initial or `cap < 4·count`. -/
def CapInv (t : Tab) : Prop := (∃ j, t.cap = 16 * 2 ^ j) ∧ (t.cap = 16 ∨ t.cap < 4 * t.count)

theorem capInv_setFresh (t : Tab) (h : CapInv t) : CapInv (setFresh t) := by
  obtain ⟨⟨j, hj⟩, hc⟩ := h
  unfold setFresh
  split
  · rename_i hg
    refine ⟨⟨j + 1, by simp only; rw [hj, Nat.pow_succ, Nat.mul_assoc]⟩, Or.inr ?_⟩
    simp only; omega
  · refine ⟨⟨j, hj⟩, ?_⟩
    simp only; omega

theorem capInv_applyN (n : Nat) (t : Tab) (h : CapInv t) : CapInv (applyN n t) := by
  induction n generalizing t with
  | zero => exact h
  | succ n ih => exact ih (setFresh t) (capInv_setFresh t h)

/-- 9. From `htab_new(_,16)`, `n ≤ 105,263` gas-paid fresh keys keep `cap ≤ 262,144`. -/
theorem guest_htab_cap_le_of_gas (n : Nat) (hgas : minGasPerKey * n ≤ blockGasLimit) :
    (applyN n guestInitialTab).cap ≤ 262144 ∧
      2 * n ≤ (applyN n guestInitialTab).cap := by
  have hn := keys_le_200M n hgas
  have hinv := iterate_inv guestInitialTab ⟨by decide, by decide⟩ n
  have hcnt := applyN_count n guestInitialTab
  have hc := capInv_applyN n guestInitialTab ⟨⟨0, rfl⟩, Or.inl rfl⟩
  obtain ⟨⟨j, hj⟩, hor⟩ := hc
  have hc0 : guestInitialTab.count = 0 := rfl
  rw [hc0, Nat.zero_add] at hcnt
  have hlt : 16 * 2 ^ j < 421053 := by rw [← hj]; rcases hor with h | h <;> omega
  have hj14 : j ≤ 14 := by
    by_contra hcon
    have : 2 ^ 15 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have : 2 ^ j ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) hj14
  refine ⟨by omega, ?_⟩
  have := hinv.2; rw [hcnt] at this; exact this

/-- 10. Tightness: at the extremal `n = 105,263` the capacity is exactly `262,144 = 2^18`. -/
theorem guest_htab_cap_eq_at_max :
    (applyN 105263 guestInitialTab).cap = 262144 := by
  have hb := guest_htab_cap_le_of_gas 105263 (by decide)
  obtain ⟨⟨j, hj⟩, _⟩ := capInv_applyN 105263 guestInitialTab ⟨⟨0, rfl⟩, Or.inl rfl⟩
  have hge : 210526 ≤ 16 * 2 ^ j := by rw [← hj]; exact hb.2
  have hle : 16 * 2 ^ j ≤ 262144 := by rw [← hj]; exact hb.1
  have hj14 : 14 ≤ j := by
    by_contra hcon
    have : 2 ^ j ≤ 2 ^ 13 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hj14' : j ≤ 14 := by
    by_contra hcon
    have : 2 ^ 15 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have : j = 14 := by omega
  rw [hj, this]; decide

/-- 11. Linear-probe count for any lookup is `< 262,144` under the gas bound. -/
theorem guest_probe_lt_262144_of_gas (n : Nat) (hgas : minGasPerKey * n ≤ blockGasLimit)
    (used : Nat → Bool) (home : Nat)
    (hfree : ∃ j, j < (applyN n guestInitialTab).cap ∧ used j = false) :
    ∃ r, r < 262144 ∧
      probe used (applyN n guestInitialTab).cap home (applyN n guestInitialTab).cap = some r := by
  obtain ⟨_, _, _, r, hr, hp⟩ :=
    htab_probe_bound_of_gas_limit guestInitialTab ⟨by decide, by decide⟩ n hgas used home hfree
  exact ⟨r, Nat.lt_of_lt_of_le hr (guest_htab_cap_le_of_gas n hgas).1, hp⟩

end InitECandidate.Solver.SourceWitnessClockBound
