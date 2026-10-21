import InitECandidate.Solver.HtabLoadFactorBound
import InitECandidate.Solver.SourceTerminationBound
import InitECandidate.Solver.SourceCallGraphBound
import InitECandidate.Solver.YukonPipelineBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.GuestGasAndHtabBound` — Verrou B: Guest Hash-Table Load Factor, Acyclic Call Graph, and EVM Gas Step Bounds Below Yukon Ceiling

This module integrates:
1. **Hash-Table Load-Factor & Probe Bound (`HtabLoadFactorBound`)**:
   Starting from any table satisfying `Inv t0` (`2 ≤ t0.cap ∧ 2 * t0.count ≤ t0.cap`),
   under `Guest.GasLimit.declaredGasLimit input ≤ 200_000_000` and EIP-2929/2930
   `minGasPerKey = 1900`, the number of fresh table insertions is bounded by
   `n ≤ 105_263`, the invariant `2 * count ≤ cap` (`count < cap`) is preserved across
   all `n` insertions (`applyN n t0`), and every linear probe terminates in `< cap` steps.
   Moreover, after `n` fresh insertions, `(applyN n t0).count = t0.count + n`.
2. **Acyclic Call Graph & EVM Gas Step-Decrement Bound (`SourceCallGraphBound`, `SourceTerminationBound`)**:
   Combines the acyclic call-graph depth (`d ≤ 18`, `guestMaxFrameBound = 348`),
   `loopClockBudget`, `callClockBudget`, and the strict EVM gas decrement (`charge_gas`)
   to bound the total `PanSem` source clock budget `K_pan` (`guestSourceClockBudget`)
   and stabilize any terminating source execution `sourceBehaviour input = .terminate outcome events`.
3. **End-to-End Total Target Budget Below the Yukon Float64 Ceiling (`K_total < 900_719_925_474`)**:
   Combines `bootstrapSteps` (`23_132`) with `linearPipelineTargetBudget` over `K_pan`
   to prove formally (`0 sorryAx`) that `K_total < 900_719_925_474` (`yukonFloat64Ceiling`).
-/

namespace InitECandidate.Solver.GuestGasAndHtabBound

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.HtabLoadFactorBound
open InitECandidate.Solver.GuestStepBound
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang

/-! ## 1. Constants & Ceiling Definitions -/

/-- The IEEE-754 float64 exact-integer Yukon ceiling `900,719,925,474` (`⌊(2^53 - 1) / 10000⌋ + 1`). -/
def yukonFloat64Ceiling : Nat := 900719925474

/-- Maximum number of fresh hash-table keys creatable under `blockGasLimit = 200,000,000`
at `minGasPerKey = 1900` gas per fresh key (`200,000,000 / 1900 = 105,263`). -/
def maxFreshHtabKeys : Nat := 105263

/-- Initial guest hash-table configuration `htab_new(20, 16)` (`count = 0, cap = 16`). -/
def guestInitialTab : Tab := ⟨0, 16⟩

/-- Exact value of `InitE.bootstrapSteps = 23,132`. -/
theorem bootstrapSteps_eq : bootstrapSteps = 23132 := by decide

/-! ## 2. Hash-Table Load Factor & Probe Bound Under `declaredGasLimit input ≤ 200,000,000` -/

/-- Exact count after `n` fresh insertions: `(applyN n t).count = t.count + n`. -/
theorem applyN_count (n : Nat) (t : Tab) :
    (applyN n t).count = t.count + n := by
  induction n generalizing t with
  | zero => simp [applyN]
  | succ n ih =>
    simp only [applyN, ih]
    unfold setFresh
    split <;> simp <;> omega

/-- Capacity monotonicity: `(applyN n t).cap ≥ t.cap` and `2 * (t.count + n) ≤ (applyN n t).cap`
whenever `Inv t` holds. -/
theorem applyN_count_and_cap_inv (n : Nat) (t : Tab) (h : Inv t) :
    (applyN n t).count = t.count + n ∧
      2 ≤ (applyN n t).cap ∧
      2 * (t.count + n) ≤ (applyN n t).cap := by
  have hinv := iterate_inv t h n
  have hcnt := applyN_count n t
  refine ⟨hcnt, hinv.1, ?_⟩
  rw [← hcnt]
  exact hinv.2

/-- Under `Guest.GasLimit.declaredGasLimit input ≤ 200,000,000` (with decoded `StatelessInput`)
and `minGasPerKey * n ≤ decoded.payload.gasLimit`, the fresh-key count `n` satisfies
`n ≤ maxFreshHtabKeys` (`105,263`), the load-factor invariant `Inv (applyN n t0)`
(`2 * count ≤ cap` and `count < cap`) holds, `(applyN n t0).count = t0.count + n`,
and every probe from `home` terminates in `< (applyN n t0).cap` steps. -/
theorem guest_htab_bound_of_declared_gas_limit
    {input : Guest.InputBlob} {decoded : Guest.InputDecode.StatelessInput}
    (hdecode : Guest.InputDecode.decodeStatelessInput input = some decoded)
    (hdeclared : Guest.GasLimit.declaredGasLimit input ≤ maxBlockGasLimit)
    (t0 : Tab) (h0 : Inv t0)
    (n : Nat) (hgas : minGasPerKey * n ≤ decoded.payload.gasLimit)
    (used : Nat → Bool) (home : Nat)
    (hfree : ∃ j, j < (applyN n t0).cap ∧ used j = false) :
    n ≤ maxFreshHtabKeys ∧
      Inv (applyN n t0) ∧
      (applyN n t0).count = t0.count + n ∧
      2 * (applyN n t0).count ≤ (applyN n t0).cap ∧
      (applyN n t0).count < (applyN n t0).cap ∧
      ∃ r, r < (applyN n t0).cap ∧
        probe used (applyN n t0).cap home (applyN n t0).cap = some r := by
  have hdec_gas := (GuestStepBound.declaredGasLimit_le_of_decode hdecode hdeclared).2
  have hgas_block : minGasPerKey * n ≤ blockGasLimit := by
    unfold blockGasLimit
    omega
  obtain ⟨hn, hinv, hlt, hprobe⟩ :=
    htab_probe_bound_of_gas_limit t0 h0 n hgas_block used home hfree
  exact ⟨hn, hinv, applyN_count n t0, hinv.2, hlt, hprobe⟩

/-! ## 3. Source `PanSem` Clock Budget `K_pan` Combining Gas Steps, Htab Probes, and Call Graph -/

/-- Composite source `PanSem` clock budget `K_pan` parameterized by:
- `gasSteps`: number of EVM gas-consuming steps (`≤ maxBlockGasLimit = 200,000,000`),
- `stepCallDepth`: acyclic call-graph depth per step (`≤ guestCallGraphMaxDepth = 18`),
- `probeBudget`: bounded hash-table / inner-loop ticks per step,
- `initTicks`: static declaration and input-cursor initialization ticks (`≤ Guest.maxInputBytes`). -/
def guestSourceClockBudget (gasSteps stepCallDepth probeBudget initTicks : Nat) : Nat :=
  initTicks + loopClockBudget gasSteps (stepCallDepth + probeBudget)

/-- Monotonicity of `guestSourceClockBudget` in all four parameters, together with
strict gas-decrement step accounting (`(gl - amount).toNat < gl.toNat`). -/
theorem guestSourceClockBudget_mono_and_gas_step
    {g1 g2 d1 d2 p1 p2 i1 i2 : Nat}
    (hg : g1 ≤ g2) (hd : d1 ≤ d2) (hp : p1 ≤ p2) (hi : i1 ≤ i2)
    (gl amount : Guest.Word) (hamt : amount.toNat ≤ gl.toNat) (hpos : 1 ≤ amount.toNat) :
    guestSourceClockBudget g1 d1 p1 i1 ≤ guestSourceClockBudget g2 d2 p2 i2 ∧
      (gl - amount : BitVec 64).toNat < gl.toNat ∧
      guestSourceClockBudget (g1 + 1) d1 p1 i1 =
        (d1 + p1 + 1) + guestSourceClockBudget g1 d1 p1 i1 := by
  unfold guestSourceClockBudget
  have hloop := (loopClockBudget_step_and_mono g1 g2 (d1 + p1) (d2 + p2) hg (by omega)).2.2
  have hstep := (loopClockBudget_step_and_mono g1 g2 (d1 + p1) (d2 + p2) hg (by omega)).2.1
  have hgas := gas_strictly_decreases gl amount hamt hpos
  refine ⟨Nat.add_le_add hi hloop, hgas, ?_⟩
  omega

/-- Concrete worst-case `PanSem` source clock ceiling `K_pan_max` for a block with
`gasSteps ≤ 200,000,000`, acyclic call depth `d ≤ 18`, per-step inner budget `≤ 200`,
and input-cursor initialization `initTicks ≤ Guest.maxInputBytes` (`134,217,712`):
`guestSourceClockBudget gasSteps d probeBudget initTicks ≤ 43,934,217,712`. -/
def maxGuestSourceClock : Nat := 43934217712

theorem guestSourceClockBudget_le_max
    (gasSteps d probeBudget initTicks : Nat)
    (hgas : gasSteps ≤ maxBlockGasLimit)
    (hd : d ≤ guestCallGraphMaxDepth)
    (hprobe : probeBudget ≤ 200)
    (hinit : initTicks ≤ Guest.maxInputBytes) :
    guestSourceClockBudget gasSteps d probeBudget initTicks ≤ maxGuestSourceClock ∧
      d * guestMaxFrameBound ≤ 6264 := by
  have hcg := (guestCallGraph_frame_and_tick_bound d hd).2.2.1
  have hmono : guestSourceClockBudget gasSteps d probeBudget initTicks ≤
      guestSourceClockBudget maxBlockGasLimit guestCallGraphMaxDepth 200 Guest.maxInputBytes := by
    unfold guestSourceClockBudget
    have hl := (loopClockBudget_step_and_mono gasSteps maxBlockGasLimit
      (d + probeBudget) (guestCallGraphMaxDepth + 200) hgas (by omega)).2.2
    exact Nat.add_le_add hinit hl
  have hval : guestSourceClockBudget maxBlockGasLimit guestCallGraphMaxDepth 200 Guest.maxInputBytes =
      maxGuestSourceClock := by decide
  exact ⟨hval ▸ hmono, hcg⟩

/-! ## 4. Total Target Budget `K_total < 900,719,925,474` and Source Clock Stabilization -/

/-- Total target machine budget `K_total` combining `InitE.bootstrapSteps` (`23,132`)
and `linearPipelineTargetBudget K_pan C_front D_front C_back D_back C_target`. -/
def guestTotalTargetBudget
    (K_pan C_front D_front C_back D_back C_target : Nat) : Nat :=
  bootstrapSteps + linearPipelineTargetBudget K_pan C_front D_front C_back D_back C_target

/-- Monotonicity of `guestTotalTargetBudget` in `K_pan`. -/
theorem guestTotalTargetBudget_mono_k_pan
    {k1 k2 : Nat} (C_front D_front C_back D_back C_target : Nat)
    (hle : k1 ≤ k2) :
    guestTotalTargetBudget k1 C_front D_front C_back D_back C_target ≤
      guestTotalTargetBudget k2 C_front D_front C_back D_back C_target := by
  unfold guestTotalTargetBudget
  exact Nat.add_le_add_left
    (linearPipelineTargetBudget_mono_k_pan C_front D_front C_back D_back C_target hle)
    bootstrapSteps

/-- Explicit arithmetic bound proving that for any `K_pan ≤ maxGuestSourceClock` (`43,934,217,712`)
and pipeline factors `(C_front ≤ 2, D_front ≤ 1000, C_back ≤ 5, D_back ≤ 10000, C_target ≤ 2)`,
`guestTotalTargetBudget K_pan C_front D_front C_back D_back C_target < yukonFloat64Ceiling`
(`878,684,407,372 < 900,719,925,474`). -/
theorem guestTotalTargetBudget_lt_yukon_ceiling_of_le_max
    (K_pan C_front D_front C_back D_back C_target : Nat)
    (hk_pan : K_pan ≤ maxGuestSourceClock)
    (hCf : C_front ≤ 2) (hDf : D_front ≤ 1000)
    (hCb : C_back ≤ 5) (hDb : D_back ≤ 10000) (hCt : C_target ≤ 2) :
    guestTotalTargetBudget K_pan C_front D_front C_back D_back C_target < yukonFloat64Ceiling := by
  have hmono := guestTotalTargetBudget_mono_k_pan C_front D_front C_back D_back C_target hk_pan
  have hbs : bootstrapSteps = 23132 := bootstrapSteps_eq
  unfold guestTotalTargetBudget linearPipelineTargetBudget maxGuestSourceClock yukonFloat64Ceiling at *
  rw [hbs] at hmono ⊢
  have h1 : C_front * 43934217712 + D_front ≤ 2 * 43934217712 + 1000 := by omega
  have h2 : C_back * (C_front * 43934217712 + D_front) + D_back ≤
      5 * (2 * 43934217712 + 1000) + 10000 := by
    have hm := Nat.mul_le_mul hCb h1
    omega
  have h3 : C_target * (C_back * (C_front * 43934217712 + D_front) + D_back) ≤
      2 * (5 * (2 * 43934217712 + 1000) + 10000) :=
    Nat.mul_le_mul hCt h2
  omega

/-- Master theorem: combining
1. the `HtabLoadFactorBound` invariant (`2 * count ≤ cap`, `n ≤ 105,263` fresh keys under
   `declaredGasLimit input ≤ 200,000,000`),
2. the acyclic call-graph and EVM gas step bound `K_pan ≤ maxGuestSourceClock`
   (`43,934,217,712`), and
3. the total target step budget `K_total` across `bootstrapSteps + linearPipelineTargetBudget`,
proves that `K_total` is strictly below the Yukon float64 ceiling `900,719,925,474`
(`K_total < yukonFloat64Ceiling`). -/
theorem guest_gas_and_htab_total_budget_lt_yukon_ceiling
    {input : Guest.InputBlob} {decoded : Guest.InputDecode.StatelessInput}
    (hdecode : Guest.InputDecode.decodeStatelessInput input = some decoded)
    (hdeclared : Guest.GasLimit.declaredGasLimit input ≤ maxBlockGasLimit)
    (n : Nat) (hgas_keys : minGasPerKey * n ≤ decoded.payload.gasLimit)
    (used : Nat → Bool) (home : Nat)
    (hfree : ∃ j, j < (applyN n guestInitialTab).cap ∧ used j = false)
    (gasSteps d probeBudget initTicks : Nat)
    (hgas_steps : gasSteps ≤ decoded.payload.gasLimit)
    (hd : d ≤ guestCallGraphMaxDepth)
    (hprobe : probeBudget ≤ 200)
    (hinit : initTicks ≤ Guest.maxInputBytes)
    (C_front D_front C_back D_back C_target : Nat)
    (hCf : C_front ≤ 2) (hDf : D_front ≤ 1000)
    (hCb : C_back ≤ 5) (hDb : D_back ≤ 10000) (hCt : C_target ≤ 2) :
    let K_pan := guestSourceClockBudget gasSteps d probeBudget initTicks
    let K_total := guestTotalTargetBudget K_pan C_front D_front C_back D_back C_target
    n ≤ maxFreshHtabKeys ∧
      (applyN n guestInitialTab).count = n ∧
      2 * (applyN n guestInitialTab).count ≤ (applyN n guestInitialTab).cap ∧
      (applyN n guestInitialTab).count < (applyN n guestInitialTab).cap ∧
      (∃ r, r < (applyN n guestInitialTab).cap ∧
        probe used (applyN n guestInitialTab).cap home (applyN n guestInitialTab).cap = some r) ∧
      d * guestMaxFrameBound ≤ 6264 ∧
      K_pan ≤ maxGuestSourceClock ∧
      K_total < yukonFloat64Ceiling := by
  dsimp only
  have hinit_inv : Inv guestInitialTab := ⟨by decide, by decide⟩
  have hhtab := guest_htab_bound_of_declared_gas_limit hdecode hdeclared
    guestInitialTab hinit_inv n hgas_keys used home hfree
  have hcnt : (applyN n guestInitialTab).count = n := by
    have hc := hhtab.2.2.1
    simpa [guestInitialTab] using hc
  have hdec_gas := (GuestStepBound.declaredGasLimit_le_of_decode hdecode hdeclared).2
  have hsteps_max : gasSteps ≤ maxBlockGasLimit := by
    unfold maxBlockGasLimit InitE.gasLimit
    omega
  obtain ⟨hk_pan, hframe⟩ :=
    guestSourceClockBudget_le_max gasSteps d probeBudget initTicks hsteps_max hd hprobe hinit
  have htot_lt :=
    guestTotalTargetBudget_lt_yukon_ceiling_of_le_max
      (guestSourceClockBudget gasSteps d probeBudget initTicks)
      C_front D_front C_back D_back C_target hk_pan hCf hDf hCb hDb hCt
  exact ⟨hhtab.1, hcnt, hhtab.2.2.2.1, hhtab.2.2.2.2.1,
    hhtab.2.2.2.2.2, hframe, hk_pan, htot_lt⟩

/-- End-to-end source stabilization corollary at `K_pan`: whenever
`sourceBehaviour input = .terminate outcome events` and its witness clock `k_pan`
fits within `K_pan = guestSourceClockBudget gasSteps d probeBudget initTicks`,
evaluating `"main"` at clock `K_pan` completes without `.timeOut`, produces
`.CompleteResult outcome` and `events`, and the induced total target budget
`K_total` is strictly below `yukonFloat64Ceiling` (`900,719,925,474`). -/
theorem source_terminate_at_guest_budget_lt_yukon_ceiling
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (hsource : sourceBehaviour input = .terminate outcome events)
    (gasSteps d probeBudget initTicks : Nat)
    (hgas_steps : gasSteps ≤ maxBlockGasLimit)
    (hd : d ≤ guestCallGraphMaxDepth)
    (hprobe : probeBudget ≤ 200)
    (hinit : initTicks ≤ Guest.maxInputBytes)
    (C_front D_front C_back D_back C_target : Nat)
    (hCf : C_front ≤ 2) (hDf : D_front ≤ 1000)
    (hCb : C_back ≤ 5) (hDb : D_back ≤ 10000) (hCt : C_target ≤ 2) :
    let K_pan := guestSourceClockBudget gasSteps d probeBudget initTicks
    let K_total := guestTotalTargetBudget K_pan C_front D_front C_back D_back C_target
    K_total < yukonFloat64Ceiling ∧
      ∃ stCtxt s_decls k_pan res_src s_src_post,
        decsStcnamesHOLExact [] sourceDeclarations = some stCtxt ∧
        @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
          { sourceInitialState input with structs := stCtxt }
          (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
          sourceDeclarations = some s_decls ∧
        PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
          (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post) ∧
        res_src ≠ some .timeOut ∧
        panEntryClass res_src = .CompleteResult outcome ∧
        s_src_post.ffi.ioEvents = events ∧
        (k_pan ≤ K_pan →
          panEntryClass (PanSemStateFiniteExact.evaluateHOLFiniteState
            { s_decls with clock := K_pan }
            (.call none (ofString "main") [] : ProgHOL 64)).1 = .CompleteResult outcome ∧
          (PanSemStateFiniteExact.evaluateHOLFiniteState
            { s_decls with clock := K_pan }
            (.call none (ofString "main") [] : ProgHOL 64)).2.ffi.ioEvents = events) := by
  dsimp only
  obtain ⟨hk_pan, _⟩ :=
    guestSourceClockBudget_le_max gasSteps d probeBudget initTicks hgas_steps hd hprobe hinit
  have htot_lt :=
    guestTotalTargetBudget_lt_yukon_ceiling_of_le_max
      (guestSourceClockBudget gasSteps d probeBudget initTicks)
      C_front D_front C_back D_back C_target hk_pan hCf hDf hCb hDb hCt
  obtain ⟨stCtxt, s_decls, k_pan, res_src, s_src_post, hst, hev_decls, hev_call, hnt, hclass, hio, hstab⟩ :=
    sourceBehaviour_terminate_clock_stabilizes input outcome events hsource
  refine ⟨htot_lt, stCtxt, s_decls, k_pan, res_src, s_src_post, hst, hev_decls, hev_call, hnt, hclass, hio, ?_⟩
  intro hle
  have hs := hstab (guestSourceClockBudget gasSteps d probeBudget initTicks) hle
  exact ⟨hs.2.2.1, hs.2.2.2⟩


end InitECandidate.Solver.GuestGasAndHtabBound
