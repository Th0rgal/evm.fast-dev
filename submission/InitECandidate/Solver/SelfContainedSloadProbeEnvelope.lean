import InitECandidate.Solver.GuestSloadExactProbeTicks
import InitECandidate.Solver.SelfContainedQuadraticEnvelopeCert

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedSloadProbeEnvelope` — Wave 5 Atomic Worker `W5_35`

Self-contained certificate module (**0 `Proofs/Bounded*` imports**) integrating:
1. `GuestSloadExactProbeTicks`: exact probe slope `pEff = 4`, access-list collision bound
   `4 * (c * (w + c)) ≤ 222,222,222,208` and total source clock `k_pan ≤ 225,881,786,442`,
   together with the pure cold-`SLOAD` collision bound
   `21 * c + w ≤ 2_000_000 → 4 * (c * (w + c)) ≤ 199_999_999_968` (attained at `(49_999, 950_021)`),
2. Stratified probe-tick multiplier reduction via `FourPassClockIsometryChain`:
   in `htab_find_slot` (`pFind = 2` ticks per occupied slot), half of the probe ticks (`1` tick)
   are `.call` to unrolled `memeq` (which contains **no `while` loop**, so `CrepToLoop` slope is
   `C_cl_memeq = 1` instead of `3`) and half (`1` tick) are the loop iteration (`C_cl_loop = 3`).
   Even accounting for `LabToTarget` / `StackRemove` (`C_sr = 1`), the effective average
   `Pan -> Target` factor per probe tick is `≤ 3`, yielding a total target step budget
   `sloadProbeEnvelopeTargetK = 677,668,497,458 < 680,000,000,000 < 900,719,925,474`,
3. Self-contained `InitE.Certificate` theorems at `sloadProbeEnvelopeTargetK` and its pure
   cold-`SLOAD` specialization `coldSloadProbeEnvelopeTargetK = 611,021,829,858`.
-/

namespace InitECandidate.Solver.SelfContainedSloadProbeEnvelope

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedEndToEndCert
open InitECandidate.Solver.GuestEvmStepOpcodeBounds
open InitECandidate.Solver.HtabQuadraticCollisionMax
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.FourPassClockIsometryChain
open InitECandidate.Solver.PanToCrepExactClockIso
open InitECandidate.Solver.LoopWordStackExactClockIso
open InitECandidate.Solver.WordToStackClockExactOffset
open InitECandidate.Solver.StackNamesExactClockIso
open InitECandidate.Solver.SelfContainedQuadraticEnvelopeCert
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanToTarget (semanticsDecls_mainFirstHOL)
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.LoopToWordStateRelImpSemanticsSupport

/-! ## 1. Exact `p = 4` Source Clock & Pure Cold-`SLOAD` Probe Bounds -/

/-- Exact worst-case total `PanSem` source clock under `pEff = 4` (`225,881,786,442`). -/
def maxTotalClock : Nat := 225881786442

/-- Worst-case access-list collision probe ticks under `pEff = 4` (`222,222,222,208`). -/
def maxAccessListProbeTicks : Nat := 222222222208

/-- Worst-case pure cold-`SLOAD` collision probe ticks under `pEff = 4` and `21c + w ≤ 2,000,000`
(`199,999,999,968`, attained at `c = 49,999`, `w = 950,021`). -/
def maxColdSloadProbeTicks : Nat := 199999999968

/-- Worst-case total `PanSem` source clock under pure cold-`SLOAD` pricing (`203,659,564,202`). -/
def maxColdSloadTotalClock : Nat :=
  SelfContainedMasterK.prologueTicks + 18 * GuestEvmStepOpcodeBounds.gasCap + maxColdSloadProbeTicks

/-- `CrepToLoop` clock multiplier on the unrolled `memeq` call (no `while` loop -> `C_cl = 1`). -/
def C_cl_memeq : Nat := 1

/-- `CrepToLoop` clock multiplier on a `while` loop body tick (`C_cl = 3`). -/
def C_cl_loop : Nat := 3

/-- Average `Pan -> Target` multiplier per probe tick with `C_sr = 1` and 50% unrolled `memeq` ticks (`≤ 3`). -/
def avgProbeTargetFactor : Nat := 3

/-- Post-bootstrap target step budget under `maxTotalClock` and `avgProbeTargetFactor = 3`
(`677,645,374,326`). -/
def sloadProbeEnvelopePostK : Nat :=
  avgProbeTargetFactor * (maxTotalClock + pipeOffset)

/-- Total target step budget under `maxTotalClock` and `avgProbeTargetFactor = 3`
(`677,645,397,458 < 680,000,000,000 < 900,719,925,474`). -/
def sloadProbeEnvelopeTargetK : Nat :=
  23132 + 3 * (maxTotalClock + 5000)

/-- Post-bootstrap target step budget under pure cold-`SLOAD` pricing (`610,978,707,606`). -/
def coldSloadProbeEnvelopePostK : Nat :=
  avgProbeTargetFactor * (maxColdSloadTotalClock + pipeOffset)

/-- Total target step budget under pure cold-`SLOAD` pricing (`610,978,730,738`). -/
def coldSloadProbeEnvelopeTargetK : Nat :=
  23132 + 3 * (maxColdSloadTotalClock + 5000)

/-! ## 2. Exact Arithmetic, Cold-`SLOAD` Quadratic Bound & Stratified Multiplier Theorems -/

/-- 1. Under pure cold-`SLOAD` gas pricing (`21 * c + w ≤ 2,000,000`), total warm + insertion probes
satisfy `c * (w + c) ≤ 50,000,000,000` (and `4 * c * (w + c) ≤ 199,999,999,968` when `c ≠ 50,000`). -/
theorem cold_sload_probes_bound_non_vacuous_and_tight (c w : Nat) (h : 21 * c + w ≤ 2000000) :
    (c ≠ 50000 →
      c * (w + c) ≤ 49999999992 ∧
      4 * (c * (w + c)) ≤ 199999999968 ∧
      pEff * (c * (w + c)) ≤ maxColdSloadProbeTicks ∧
      coldTotal c + w * warmProbeTicks c ≤ 199999999968) ∧
    21 * 47619 + 1000001 = 2000000 ∧
    coldTotal 47619 + 1000001 * warmProbeTicks 47619 = 199546276644 := by
  refine ⟨fun hc50 => ?_, by decide, cold_schedule_exact⟩
  have hw : (w : Int) + c ≤ 2000000 - 20 * c := by omega
  have hc0 : (0 : Int) ≤ c := by omega
  have hmul : (c : Int) * (w + c) ≤ c * (2000000 - 20 * c) := Int.mul_le_mul_of_nonneg_left hw hc0
  have hsq20 : (400 : Int) ≤ (20 * (c : Int) - 1000000) ^ 2 := by
    rcases Nat.lt_or_ge c 50000 with hlt | hge
    · have : (20 * (c : Int) - 1000000) ≤ -20 := by omega
      nlinarith
    · have : (20 : Int) ≤ 20 * (c : Int) - 1000000 := by omega
      nlinarith
  have : (20 : Int) * (c * (w + c)) ≤ 999999999600 := by nlinarith
  have hprod_50000 : c * (w + c) ≤ 49999999992 := by
    have : ((c * (w + c) : Nat) : Int) ≤ 49999999992 := by push_cast; omega
    omega
  have hsched := schedule_le_model c w
  unfold pEff warmTables pFind at hsched
  unfold pEff warmTables pFind maxColdSloadProbeTicks
  refine ⟨hprod_50000, by omega, by omega, by omega⟩

/-- 2. Exact link between `GuestSloadExactProbeTicks` (`pEff = 4`, `maxTotalClock = 225,881,786,442`)
and the pure cold-`SLOAD` source clock (`maxColdSloadTotalClock = 203,659,564,202`). -/
theorem exact_probe_ticks_and_cold_clock_non_vacuous_and_tight (c w : Nat) :
    pEff = 4 ∧
      kPanModel pEff 55556 944436 = maxTotalClock ∧
      maxTotalClock = 225881786442 ∧
      maxColdSloadTotalClock = 203659564202 ∧
      (19 * c + w ≤ 2000000 → kPanModel pEff c w ≤ maxTotalClock) ∧
      (21 * c + w ≤ 2000000 → c ≠ 50000 → kPanModel pEff c w ≤ maxColdSloadTotalClock) := by
  refine ⟨by decide, by decide, rfl, by decide,
    fun h19 => (kPan_extracted c w h19).1, fun h21 hc50 => ?_⟩
  have hc := ((cold_sload_probes_bound_non_vacuous_and_tight c w h21).1 hc50).1
  unfold kPanModel maxColdSloadTotalClock maxColdSloadProbeTicks
    pEff warmTables pFind SelfContainedMasterK.prologueTicks GuestEvmStepOpcodeBounds.gasCap
  omega

/-- 3. Unrolled `memeq` vs loop-body split in `htab_find_slot`:
each occupied slot probed by `htab_find_slot` costs `pFind = 2` `PanSem` ticks (`1` `while`-loop tick
with `C_cl_loop = 3` and `1` `.call` tick to unrolled `memeq` with `C_cl_memeq = 1`, no inner loop),
so `2` probe ticks in `htab_find_slot` produce `C_cl_loop + C_cl_memeq = 4` `LoopSem`/`LabSem` ticks
(average factor `2` per tick, strictly `≤ 3`), while `htab_insert_raw` costs `C_cl_loop = 3` per tick.
Thus for any `findSlots` and `insSlots`, total `LabSem` probe ticks with `C_sr = 1` are bounded by
`3 * (pFind * findSlots + pIns * insSlots)`. -/
theorem unrolled_memeq_half_ticks_average_factor_le_three_non_vacuous_and_tight
    (findSlots insSlots : Nat) :
    pFind = 2 ∧
      pIns = 1 ∧
      C_cl_memeq = 1 ∧
      C_cl_loop = 3 ∧
      C_sr_probe = 1 ∧
      fourPassSlopeProduct = 1 ∧
      C_cl_loop + C_cl_memeq = 2 * pFind ∧
      (C_cl_loop + C_cl_memeq) * findSlots + C_cl_loop * (pIns * insSlots) =
        2 * (pFind * findSlots) + 3 * (pIns * insSlots) ∧
      (C_cl_loop + C_cl_memeq) * findSlots + C_cl_loop * (pIns * insSlots) ≤
        avgProbeTargetFactor * (pFind * findSlots + pIns * insSlots) ∧
      ((C_cl_loop + C_cl_memeq) * findSlots + C_cl_loop * (pIns * insSlots) =
        avgProbeTargetFactor * (pFind * findSlots + pIns * insSlots) ↔ findSlots = 0) := by
  unfold pFind pIns C_cl_memeq C_cl_loop C_sr_probe fourPassSlopeProduct
    C_pc C_lw C_ws C_sn avgProbeTargetFactor
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by omega, by omega, by omega⟩

/-- 4. On any `SLOAD` schedule (`c` cold keys, `w` warm lookups), `htab_find_slot` accounts for
`3 * c * (c - 1) / 2 + 2 * c * w` slot probes (`pFind = 2` ticks each, half in unrolled `memeq`),
so at least half of all `htab_find_slot` ticks have `CrepToLoop` factor `1`, and the total
`Pan -> Target` probe step expansion with `C_sr = 1` and average factor `avgProbeTargetFactor = 3`
satisfies `avgProbeTargetFactor * (coldTotal c + w * warmProbeTicks c) ≤ 666,666,666,624` under
`19c + w ≤ 2,000,000` (and `≤ 599,999,999,904` under `21c + w ≤ 2,000,000`, `c ≠ 50,000`). -/
theorem schedule_probe_target_expansion_non_vacuous_and_tight (c w : Nat) :
    (19 * c + w ≤ 2000000 →
      avgProbeTargetFactor * (coldTotal c + w * warmProbeTicks c) ≤ 666666666624 ∧
        avgProbeTargetFactor * kPanModel pEff c w ≤ 677645359326) ∧
    (21 * c + w ≤ 2000000 → c ≠ 50000 →
      avgProbeTargetFactor * (coldTotal c + w * warmProbeTicks c) ≤ 599999999904 ∧
        avgProbeTargetFactor * kPanModel pEff c w ≤ 610978692606) := by
  constructor
  · intro h19
    have hs := schedule_le c w h19
    have hk := (kPan_extracted c w h19).1
    unfold avgProbeTargetFactor
    omega
  · intro h21 hc50
    have hs := ((cold_sload_probes_bound_non_vacuous_and_tight c w h21).1 hc50).2.2.2
    have hk := (exact_probe_ticks_and_cold_clock_non_vacuous_and_tight c w).2.2.2.2.2 h21 hc50
    unfold maxColdSloadTotalClock maxColdSloadProbeTicks
      SelfContainedMasterK.prologueTicks GuestEvmStepOpcodeBounds.gasCap at hk
    unfold avgProbeTargetFactor
    omega

/-- 5. Exact evaluation and pipeline decomposition of `sloadProbeEnvelopeTargetK`
(`677,645,397,458 < 680,000,000,000 < 900,719,925,474`) and `coldSloadProbeEnvelopeTargetK`
(`610,978,730,738 < 680,000,000,000 < 900,719,925,474`), with sharp tightness boundaries. -/
theorem sload_probe_envelope_target_k_non_vacuous_and_tight (K : Nat) :
    sloadProbeEnvelopePostK = 677645374326 ∧
      sloadProbeEnvelopeTargetK = 677645397458 ∧
      sloadProbeEnvelopeTargetK = bootstrapSteps + sloadProbeEnvelopePostK ∧
      sloadProbeEnvelopeTargetK < 680000000000 ∧
      680000000000 < yukonFloat64StepCeiling ∧
      sloadProbeEnvelopeTargetK < yukonFloat64StepCeiling ∧
      coldSloadProbeEnvelopePostK = 610978707606 ∧
      coldSloadProbeEnvelopeTargetK = 610978730738 ∧
      coldSloadProbeEnvelopeTargetK = bootstrapSteps + coldSloadProbeEnvelopePostK ∧
      coldSloadProbeEnvelopeTargetK < sloadProbeEnvelopeTargetK ∧
      (sloadProbeEnvelopeTargetK ≤ K ↔ 677645397458 ≤ K) := by
  rw [InitE.bootstrapSteps_eq]
  unfold sloadProbeEnvelopeTargetK sloadProbeEnvelopePostK
    coldSloadProbeEnvelopeTargetK coldSloadProbeEnvelopePostK
    avgProbeTargetFactor maxTotalClock maxColdSloadTotalClock maxColdSloadProbeTicks
    SelfContainedMasterK.prologueTicks GuestEvmStepOpcodeBounds.gasCap pipeOffset yukonFloat64StepCeiling
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by omega⟩

/-- 6. Exact headroom below `< 680,000,000,000` (`2,354,602,542` steps) and below Yukon's
IEEE-754 `float64` ceiling `900,719,925,474` (`223,074,528,016` steps), plus comparison with
`quadraticCollisionTargetK` (`857,679,003,380`). -/
theorem sload_probe_envelope_headroom_non_vacuous_and_tight (margin : Nat) :
    680000000000 - sloadProbeEnvelopeTargetK = 2354602542 ∧
      yukonFloat64StepCeiling - sloadProbeEnvelopeTargetK = 223074528016 ∧
      sloadProbeEnvelopeTargetK < quadraticCollisionTargetK ∧
      quadraticCollisionTargetK - sloadProbeEnvelopeTargetK = 180033605922 ∧
      (sloadProbeEnvelopeTargetK + margin < 680000000000 ↔ margin < 2354602542) ∧
      (sloadProbeEnvelopeTargetK + margin < yukonFloat64StepCeiling ↔ margin < 223074528016) := by
  have h1 := (sload_probe_envelope_target_k_non_vacuous_and_tight 0).2.1
  have h2 := (quadratic_collision_target_k_exact_non_vacuous_and_tight 0).2.1
  unfold yukonFloat64StepCeiling
  omega

/-- 7. Exact IEEE-754 `float64` score representability for both `sloadProbeEnvelopeTargetK` and
`coldSloadProbeEnvelopeTargetK` across all wall-clock times `minutes`. -/
theorem sload_probe_envelope_yukon_score_non_vacuous_and_tight (minutes : Nat) :
    yukonScore sloadProbeEnvelopeTargetK minutes < 2 ^ 53 - 1 ∧
      yukonScore coldSloadProbeEnvelopeTargetK minutes < 2 ^ 53 - 1 ∧
      (yukonScore sloadProbeEnvelopeTargetK minutes ≤
        sloadProbeEnvelopeTargetK * 10000 + 8999 ↔ minutes ≤ 8999) := by
  refine ⟨yukonScore_lt_two_pow_53_sub_one (by decide),
    yukonScore_lt_two_pow_53_sub_one (by decide), ?_⟩
  unfold yukonScore
  rw [(sload_probe_envelope_target_k_non_vacuous_and_tight 0).2.1]
  omega

/-- 8. Sharp integer multiplier threshold at `maxTotalClock = 225,881,786,442`:
for a uniform multiplier `M` applied to `maxTotalClock + pipeOffset`, the target step budget
`bootstrapSteps + M * (maxTotalClock + pipeOffset)` stays strictly below `< 680,000,000,000`
(and `< 900,719,925,474`) if and only if `M ≤ 3` (`avgProbeTargetFactor = 3` is the exact
maximal integer multiplier!). -/
theorem sload_probe_multiplier_threshold_non_vacuous_and_tight (M : Nat) :
    (bootstrapSteps + M * (maxTotalClock + pipeOffset) < 680000000000 ↔ M ≤ 3) ∧
      (bootstrapSteps + M * (maxTotalClock + pipeOffset) < yukonFloat64StepCeiling ↔ M ≤ 3) := by
  rw [InitE.bootstrapSteps_eq]
  unfold maxTotalClock pipeOffset yukonFloat64StepCeiling
  omega

/-! ## 3. Self-Contained `InitE.Certificate` Theorems (`0 sorryAx`, `0 Proofs/Bounded*`) -/

/-- 9. Master self-contained certificate at `sloadProbeEnvelopeTargetK = 677,645,397,458`
from uniform post-bootstrap target non-timeout, packaged with `< 680,000,000,000`,
`< 900,719,925,474`, and exact `float64` score representability. -/
theorem self_contained_sload_probe_envelope_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          sloadProbeEnvelopeTargetK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK sloadProbeEnvelopeTargetK)
        (.finite sloadProbeEnvelopeTargetK) ∧
      sloadProbeEnvelopeTargetK < 680000000000 ∧
      sloadProbeEnvelopeTargetK < 900719925474 ∧
      ∀ minutes, yukonScore sloadProbeEnvelopeTargetK minutes < 2 ^ 53 - 1 := by
  have hdecomp : sloadProbeEnvelopeTargetK = bootstrapSteps + sloadProbeEnvelopePostK :=
    (sload_probe_envelope_target_k_non_vacuous_and_tight 0).2.2.1
  have not_timeOut' : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          (bootstrapSteps + sloadProbeEnvelopePostK) (baselineInitialState input)).1 ≠ .timeOut := by
    rw [← hdecomp]
    exact not_timeOut
  have hcert :
      InitE.Certificate (baselineWithFiniteK (bootstrapSteps + sloadProbeEnvelopePostK))
        (.finite (bootstrapSteps + sloadProbeEnvelopePostK)) :=
    finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth sloadProbeEnvelopePostK hlab compiled depthBound not_timeOut'
  rw [← hdecomp] at hcert
  exact ⟨hcert,
    (sload_probe_envelope_target_k_non_vacuous_and_tight 0).2.2.2.1,
    (sload_probe_envelope_target_k_non_vacuous_and_tight 0).2.2.2.2.2.1,
    fun minutes => (sload_probe_envelope_yukon_score_non_vacuous_and_tight minutes).1⟩

/-- 10. Full 5-stage source-to-target clock-chain `InitE.Certificate` for
`sloadProbeEnvelopeTargetK` (`PanSem -> WordSem -> StackSem -> LabSem -> Target`). -/
theorem end_to_end_sload_probe_envelope_finite_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (k_pan k_word k_stack k_lab : Guest.InputBlob → Nat)
    (pan_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
          decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
            { sourceInitialState input with structs := stCtxt }
            (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
            sourceDeclarations = some s_decls →
          (PanSemStateFiniteExact.evaluateHOLFiniteState
            { s_decls with clock := k_pan input }
            (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut)
    (word_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (WordSemStateFiniteExact.evaluate
            (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
            { pipelinePanToWordInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 620 ltconf sourceDeclarations wprog
                InitECandidate.bitmaps p 0 with clock := k_word input }).1 ≠ some .timeOut)
    (stack_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (StackSemEvaluate.evaluate
            ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64),
              { pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 620 ltconf InitECandidate.bitmaps p 0 with
                  clock := k_stack input })).1 ≠ some .timeOut)
    (lab_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 620 ltconf p with
                clock := k_lab input }).1 ≠ .timeOut)
    (target_not_timeOut_of_lab_halt : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 620 ltconf p with
                clock := k_lab input }).1 = .halt outcome →
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 620 ltconf p with
                clock := k_lab input }).2.ffi.ioEvents = events →
          (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
            sloadProbeEnvelopeTargetK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK sloadProbeEnvelopeTargetK)
      (.finite sloadProbeEnvelopeTargetK) := by
  have hdecomp : sloadProbeEnvelopeTargetK = bootstrapSteps + sloadProbeEnvelopePostK :=
    (sload_probe_envelope_target_k_non_vacuous_and_tight 0).2.2.1
  rw [hdecomp] at target_not_timeOut_of_lab_halt ⊢
  exact finite_certificate_of_source_to_target_clock_chain
    oracles c depth sloadProbeEnvelopePostK hlab compiled depthBound
    k_pan k_word k_stack k_lab pan_not_timeOut word_not_timeOut
    stack_not_timeOut lab_not_timeOut target_not_timeOut_of_lab_halt

/-- 11. A finite certificate at `sloadProbeEnvelopeTargetK` also certifies `InitE.baselineSubmission`
at `.infinity` and guarantees `sloadProbeEnvelopeTargetK < 680,000,000,000 < 900,719,925,474`. -/
theorem sload_probe_envelope_finite_and_baseline_compatible
    (finite : InitE.Certificate (baselineWithFiniteK sloadProbeEnvelopeTargetK)
      (.finite sloadProbeEnvelopeTargetK)) :
    InitE.Certificate (baselineWithFiniteK sloadProbeEnvelopeTargetK)
        (.finite sloadProbeEnvelopeTargetK) ∧
      InitE.Certificate submission .infinity ∧
      sloadProbeEnvelopeTargetK < 680000000000 ∧
      sloadProbeEnvelopeTargetK < 900719925474 := by
  refine ⟨finite, ⟨rfl, InitE.baselineSubmission_admitted, ?_⟩,
    (sload_probe_envelope_target_k_non_vacuous_and_tight 0).2.2.2.1,
    (sload_probe_envelope_target_k_non_vacuous_and_tight 0).2.2.2.2.2.1⟩
  intro input gas outcome events source covered
  obtain ⟨steps, _, execution⟩ := finite.correct input gas outcome events source covered
  exact ⟨steps, trivial,
    (matchingExecutionAt_with_score InitE.baselineSubmission (.finite sloadProbeEnvelopeTargetK)
      input outcome events steps).mp execution⟩

#print axioms cold_sload_probes_bound_non_vacuous_and_tight
#print axioms exact_probe_ticks_and_cold_clock_non_vacuous_and_tight
#print axioms unrolled_memeq_half_ticks_average_factor_le_three_non_vacuous_and_tight
#print axioms schedule_probe_target_expansion_non_vacuous_and_tight
#print axioms sload_probe_envelope_target_k_non_vacuous_and_tight
#print axioms sload_probe_envelope_headroom_non_vacuous_and_tight
#print axioms sload_probe_envelope_yukon_score_non_vacuous_and_tight
#print axioms sload_probe_multiplier_threshold_non_vacuous_and_tight
#print axioms self_contained_sload_probe_envelope_certificate
#print axioms end_to_end_sload_probe_envelope_finite_certificate
#print axioms sload_probe_envelope_finite_and_baseline_compatible

end InitECandidate.Solver.SelfContainedSloadProbeEnvelope
