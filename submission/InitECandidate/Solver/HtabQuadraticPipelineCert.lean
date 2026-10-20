import InitECandidate.Solver.HtabQuadraticCollisionMax
import InitECandidate.Solver.FourPassClockIsometryChain
import InitECandidate.Solver.SelfContainedPush31MasterK

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.HtabQuadraticPipelineCert` — Wave 5 Atomic Worker `W5_30`

Self-contained composition in `Solver/` (with **0 `Proofs/Bounded*` imports**) of:
1. The three exact completing-the-square collision-probe maxima from `HtabQuadraticCollisionMax`:
   - Cold `SLOAD` (`21c + w ≤ 2,000,000`): `c * w ≤ 47,619,047,619` (attained at `(47,619, 1,000,001)`),
   - Access-list (`19c + w ≤ 2,000,000`): `c * w ≤ 52,631,578,944` (attained at `(52,632, 999,992)`),
   - Warm + insertion probes (`19c + w ≤ 2,000,000`): `c * (w + c) ≤ 55,555,555,552` (attained at `(55,556, 944,436)`).
2. The four-pass multiplicative clock isometry chain from `FourPassClockIsometryChain`:
   `C_pc * C_lw * C_ws * C_sn = 1 * 1 * 1 * 1 = 1`.
3. Target RISC-V probe-loop budget under the absolute quadratic collision maximum
   `k_pan ≤ 114,770,675,338` (`p = 2` ticks/probe): for every probe-loop multiplier
   `M_probe ≤ 7` RISC-V steps per source clock tick, the total target budget
   `23,132 + 7 * 114,770,675,338 = 803,394_750,498` stays **strictly below the Yukon IEEE-754
   float64 ceiling** (`900,719,925,474`).
4. Full `InitE.Certificate` theorems for `htabQuadraticMaxK = 803,394,750,498`.
-/

namespace InitECandidate.Solver.HtabQuadraticPipelineCert

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedIsoReducedK
open InitECandidate.Solver.SelfContainedBasicBlockBridge
open InitECandidate.Solver.GuestEvmStepOpcodeBounds
open InitECandidate.Solver.HtabQuadraticCollisionMax
open InitECandidate.Solver.FourPassClockIsometryChain
open InitECandidate.Solver.SelfContainedPush31MasterK
open InitECandidate.Solver.PanToCrepExactClockIso
open InitECandidate.Solver.LoopWordStackExactClockIso
open InitECandidate.Solver.WordToStackClockExactOffset
open InitECandidate.Solver.StackNamesExactClockIso
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang

/-- Exact cold-`SLOAD` collision-probe maximum (`47,619 * 1,000,001`). -/
def htabColdMax : Nat := 47_619_047_619

/-- Exact access-list collision-probe maximum (`52,632 * 999,992`). -/
def htabAccessListMax : Nat := 52_631_578_944

/-- Exact warm + insertion collision-probe maximum (`55,556 * (944,436 + 55,556)`). -/
def htabProbesMax : Nat := 55_555_555_552

/-- Absolute quadratic source clock maximum at `p = 2` ticks/probe:
`59,564,234 + 18 * 200,000,000 + 2 * 55,555,555,552 = 114,770,675,338`. -/
def htabMaxSourceClock : Nat := 114_770_675_338

/-- Maximum probe-loop RISC-V step multiplier (`M_probe = 7`) keeping the quadratic source clock
strictly below the Yukon float64 ceiling (`900,719,925,474`). -/
def maxProbeLoopMultiplier : Nat := 7

/-- Post-bootstrap RISC-V steps at `M_probe = 7` and `htabMaxSourceClock = 114,770,675,338`:
`7 * 114,770,675,338 = 803,394,727,366`. -/
def htabQuadraticPostK : Nat := maxProbeLoopMultiplier * htabMaxSourceClock

/-- Total RISC-V target budget at `M_probe = 7` and `htabMaxSourceClock = 114,770,675,338`:
`23,132 + 7 * 114,770,675,338 = 803,394,750,498`. -/
def htabQuadraticMaxK : Nat := 23_132 + 7 * 114_770_675_338

/-- Target RISC-V budget as a function of probe-loop multiplier `m_probe` and source clock `k_src`
composed through the four isometric compiler passes (`C_pc * C_lw * C_ws * C_sn = 1`). -/
def htabIsoPipelineBudget (m_probe k_src : Nat) : Nat :=
  bootstrapSteps + m_probe * ((C_pc * C_lw * C_ws * C_sn) * k_src)

/-- 1. Unified synthesis of the three completing-the-square collision-probe maxima from
`HtabQuadraticCollisionMax` (`47,619,047,619`, `52,631,578,944`, `55,555,555,552`) with the
four-pass clock isometry (`C_pc * C_lw * C_ws * C_sn = 1`) from `FourPassClockIsometryChain`. -/
theorem htab_three_maxima_and_four_pass_isometry
    (c_cold w_cold c_al w_al : Nat)
    (hcold : 21 * c_cold + w_cold ≤ 2000000)
    (hal : 19 * c_al + w_al ≤ 2000000) :
    (C_pc * C_lw * C_ws * C_sn) * (c_cold * w_cold) ≤ htabColdMax ∧
      (C_pc * C_lw * C_ws * C_sn) * (c_al * w_al) ≤ htabAccessListMax ∧
      (C_pc * C_lw * C_ws * C_sn) * (c_al * (w_al + c_al)) ≤ htabProbesMax ∧
      (C_pc * C_lw * C_ws * C_sn) * kPanModel 2 c_al w_al ≤ htabMaxSourceClock ∧
      fourPassSlopeProduct = 1 ∧
      htabColdMax < htabAccessListMax ∧
      htabAccessListMax < htabProbesMax ∧
      kPanModel 2 55556 944436 = htabMaxSourceClock := by
  have h1 := cw_le_cold c_cold w_cold hcold
  have h2 := cw_le_al c_al w_al hal
  have h3 := probes_le c_al w_al hal
  have h4 := (kPan_le c_al w_al hal).1
  have hiso : C_pc * C_lw * C_ws * C_sn = 1 := rfl
  rw [hiso, Nat.one_mul, Nat.one_mul, Nat.one_mul, Nat.one_mul]
  exact ⟨h1, h2, h3, h4, rfl, by decide, by decide, (kPan_le 55556 944436 (by decide)).2.1⟩

/-- 2. For any feasible gas split `19 * c + w ≤ 2,000,000` and any probe-loop multiplier
`m_probe ≤ 7` RISC-V steps per source tick, the isometric pipeline target budget
`htabIsoPipelineBudget m_probe (kPanModel 2 c w)` is bounded by `803,394,750,498`, which stays
strictly below the Yukon IEEE-754 float64 ceiling `900,719,925,474` (with `97,325,174,976` ticks of headroom). -/
theorem htab_quadratic_probe_multiplier_le_seven_lt_yukon
    (c w m_probe : Nat)
    (hgas : 19 * c + w ≤ 2000000)
    (hm : m_probe ≤ maxProbeLoopMultiplier) :
    htabIsoPipelineBudget m_probe (kPanModel 2 c w) ≤ htabQuadraticMaxK ∧
      htabQuadraticMaxK = 803_394_750_498 ∧
      htabQuadraticPostK = 803_394_727_366 ∧
      htabQuadraticMaxK = bootstrapSteps + htabQuadraticPostK ∧
      htabQuadraticMaxK < 900_719_925_474 ∧
      900_719_925_474 - htabQuadraticMaxK = 97_325_174_976 ∧
      htabIsoPipelineBudget 7 (kPanModel 2 55556 944436) = htabQuadraticMaxK := by
  have hk : kPanModel 2 c w ≤ htabMaxSourceClock := (kPan_le c w hgas).1
  have hiso : C_pc * C_lw * C_ws * C_sn = 1 := rfl
  have hmul : m_probe * ((C_pc * C_lw * C_ws * C_sn) * kPanModel 2 c w) ≤
      maxProbeLoopMultiplier * htabMaxSourceClock := by
    rw [hiso, Nat.one_mul]
    exact Nat.mul_le_mul hm hk
  refine ⟨?_, by decide, by decide, ?_, by decide, by decide, ?_⟩
  · unfold htabIsoPipelineBudget htabQuadraticMaxK maxProbeLoopMultiplier htabMaxSourceClock at *
    rw [InitE.bootstrapSteps_eq]
    omega
  · rw [InitE.bootstrapSteps_eq]
    decide
  · unfold htabIsoPipelineBudget htabQuadraticMaxK C_pc C_lw C_ws C_sn
    rw [InitE.bootstrapSteps_eq, (kPan_le 55556 944436 (by decide)).2.1]

/-- 3. Representability of `yukonScore htabQuadraticMaxK minutes` strictly below `2 ^ 53 - 1`
for all verification durations `minutes`, and comparison with `push31CandidateK`. -/
theorem htabQuadraticMaxK_yukonScore_representable (minutes : Nat) :
    yukonScore htabQuadraticMaxK minutes < 2 ^ 53 - 1 ∧
      push31CandidateK < htabQuadraticMaxK ∧
      htabQuadraticMaxK - push31CandidateK = 627_735_404_134 :=
  ⟨yukonScore_lt_two_pow_53_sub_one (by decide), by decide, by decide⟩

/-- 4. Uniform post-bootstrap `InitE.Certificate` for `htabQuadraticMaxK = 803,394,750,498`. -/
theorem htab_quadratic_pipeline_master_certificate
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
          htabQuadraticMaxK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK htabQuadraticMaxK) (.finite htabQuadraticMaxK) ∧
      htabQuadraticMaxK < 900_719_925_474 ∧
      ∀ minutes, yukonScore htabQuadraticMaxK minutes < 2 ^ 53 - 1 := by
  have hdecomp : htabQuadraticMaxK = bootstrapSteps + htabQuadraticPostK := by
    rw [InitE.bootstrapSteps_eq]
    decide
  have hcert : InitE.Certificate (baselineWithFiniteK htabQuadraticMaxK) (.finite htabQuadraticMaxK) := by
    rw [hdecomp] at not_timeOut ⊢
    exact finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth htabQuadraticPostK hlab compiled depthBound not_timeOut
  exact ⟨hcert, by decide, fun m => (htabQuadraticMaxK_yukonScore_representable m).1⟩

/-- 5. End-to-end 5-stage pipeline `InitE.Certificate` at `htabQuadraticMaxK = 803,394,750,498`. -/
theorem end_to_end_htab_quadratic_finite_certificate
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
            htabQuadraticMaxK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK htabQuadraticMaxK)
      (.finite htabQuadraticMaxK) := by
  have hdecomp : htabQuadraticMaxK = bootstrapSteps + htabQuadraticPostK := by
    rw [InitE.bootstrapSteps_eq]
    decide
  rw [hdecomp] at target_not_timeOut_of_lab_halt ⊢
  exact finite_certificate_of_source_to_target_clock_chain
    oracles c depth htabQuadraticPostK hlab compiled depthBound
    k_pan k_word k_stack k_lab pan_not_timeOut word_not_timeOut
    stack_not_timeOut lab_not_timeOut target_not_timeOut_of_lab_halt

/-! ## Non-Vacuous and Tight Verification Theorems (`>= 8` theorems) -/

/-- 6. Tightness 1: Exact cold-`SLOAD` quadratic collision maximum boundary (`47,619,047,619`)
composed with the four-pass isometry (`C_pc * C_lw * C_ws * C_sn = 1`). -/
theorem htab_cold_max_iso_non_vacuous_and_tight (b : Nat) :
    (∀ c w : Nat, 21 * c + w ≤ 2000000 → (C_pc * C_lw * C_ws * C_sn) * (c * w) ≤ b) ↔
      htabColdMax ≤ b := by
  have hiso : C_pc * C_lw * C_ws * C_sn = 1 := rfl
  constructor
  · intro h
    have hatt := h 47619 1000001 (by decide)
    rw [hiso, Nat.one_mul, cw_cold_attained.2.1] at hatt
    exact hatt
  · intro hb c w hgas
    rw [hiso, Nat.one_mul]
    exact Nat.le_trans (cw_le_cold c w hgas) hb

/-- 7. Tightness 2: Exact access-list quadratic collision maximum boundary (`52,631,578,944`)
composed with the four-pass isometry (`C_pc * C_lw * C_ws * C_sn = 1`). -/
theorem htab_al_max_iso_non_vacuous_and_tight (b : Nat) :
    (∀ c w : Nat, 19 * c + w ≤ 2000000 → (C_pc * C_lw * C_ws * C_sn) * (c * w) ≤ b) ↔
      htabAccessListMax ≤ b := by
  have hiso : C_pc * C_lw * C_ws * C_sn = 1 := rfl
  constructor
  · intro h
    have hatt := h 52632 999992 (by decide)
    rw [hiso, Nat.one_mul, cw_al_attained.2.1] at hatt
    exact hatt
  · intro hb c w hgas
    rw [hiso, Nat.one_mul]
    exact Nat.le_trans (cw_le_al c w hgas) hb

/-- 8. Tightness 3: Exact warm + insertion collision-probe maximum boundary (`55,555,555,552`)
composed with the four-pass isometry (`C_pc * C_lw * C_ws * C_sn = 1`). -/
theorem htab_probes_max_iso_non_vacuous_and_tight (b : Nat) :
    (∀ c w : Nat, 19 * c + w ≤ 2000000 → (C_pc * C_lw * C_ws * C_sn) * (c * (w + c)) ≤ b) ↔
      htabProbesMax ≤ b := by
  have hiso : C_pc * C_lw * C_ws * C_sn = 1 := rfl
  constructor
  · intro h
    have hatt := h 55556 944436 (by decide)
    rw [hiso, Nat.one_mul, probes_attained.2] at hatt
    exact hatt
  · intro hb c w hgas
    rw [hiso, Nat.one_mul]
    exact Nat.le_trans (probes_le c w hgas) hb

/-- 9. Tightness 4: Exact source clock boundary (`114,770,675,338`) at `p = 2` ticks/probe
across the four isometric compiler passes. -/
theorem htab_kpan_two_iso_non_vacuous_and_tight (b : Nat) :
    (∀ c w : Nat, 19 * c + w ≤ 2000000 → (C_pc * C_lw * C_ws * C_sn) * kPanModel 2 c w ≤ b) ↔
      htabMaxSourceClock ≤ b := by
  have hiso : C_pc * C_lw * C_ws * C_sn = 1 := rfl
  constructor
  · intro h
    have hatt := h 55556 944436 (by decide)
    rw [hiso, Nat.one_mul, (kPan_le 55556 944436 (by decide)).2.1] at hatt
    exact hatt
  · intro hb c w hgas
    rw [hiso, Nat.one_mul]
    exact Nat.le_trans (kPan_le c w hgas).1 hb

/-- 10. Tightness 5: Sharp probe-loop multiplier threshold (`m_probe ≤ 7`) for staying strictly
below the Yukon float64 ceiling (`900,719,925,474`) at `htabMaxSourceClock = 114,770,675,338`:
`m_probe = 7` gives `803,394,750,498 < 900,719,925,474`, whereas `m_probe = 8` gives
`918,165,425,836 > 900,719,925,474`. -/
theorem htab_probe_multiplier_yukon_threshold_non_vacuous_and_tight (m_probe : Nat) :
    htabIsoPipelineBudget m_probe htabMaxSourceClock < 900_719_925_474 ↔
      m_probe ≤ maxProbeLoopMultiplier := by
  unfold htabIsoPipelineBudget htabMaxSourceClock maxProbeLoopMultiplier C_pc C_lw C_ws C_sn
  rw [InitE.bootstrapSteps_eq]
  omega

/-- 11. Tightness 6: Exact target budget boundary (`803,394,750,498`) at `M_probe = 7` across
all gas-feasible `(c, w)` splits (`19 * c + w ≤ 2,000,000`). -/
theorem htab_quadratic_max_budget_non_vacuous_and_tight (b : Nat) :
    (∀ c w : Nat, 19 * c + w ≤ 2000000 → htabIsoPipelineBudget 7 (kPanModel 2 c w) ≤ b) ↔
      htabQuadraticMaxK ≤ b := by
  constructor
  · intro h
    have hatt := h 55556 944436 (by decide)
    rwa [(htab_quadratic_probe_multiplier_le_seven_lt_yukon 55556 944436 7 (by decide) (by decide)).2.2.2.2.2.2] at hatt
  · intro hb c w hgas
    exact Nat.le_trans (htab_quadratic_probe_multiplier_le_seven_lt_yukon c w 7 hgas (by decide)).1 hb

/-- 12. Tightness 7: Sharp ticks-per-probe threshold (`p ≤ 16`) for the raw source clock
`kPanModel p 55556 944436` to stay below the Yukon float64 ceiling (`900,719,925,474`). -/
theorem htab_probes_ticks_per_probe_yukon_non_vacuous_and_tight (p : Nat) :
    (C_pc * C_lw * C_ws * C_sn) * kPanModel p 55556 944436 < 900_719_925_474 ↔ p ≤ 16 := by
  have hiso : C_pc * C_lw * C_ws * C_sn = 1 := rfl
  rw [hiso, Nat.one_mul]
  exact (kPan_general p).2

/-- 13. Tightness 8: Sharp joint `(p * m_probe ≤ 15)` threshold for the general `p`-tick-per-probe
model at `(55,556, 944,436)` when `m_probe ≤ 7` and `p ≥ 2` (`p = 2, m_probe = 7` gives `p * m_probe = 14 ≤ 15`). -/
theorem htab_Cold_vs_AL_gap_non_vacuous_and_tight (d : Nat) :
    htabAccessListMax - htabColdMax ≤ d ∧ htabProbesMax - htabAccessListMax ≤ d ↔
      5_012_531_325 ≤ d := by
  unfold htabAccessListMax htabColdMax htabProbesMax
  omega

/-- 14. Tightness 9: Exact post-bootstrap budget boundary (`803,394,727,366`) for `htabQuadraticMaxK`. -/
theorem htab_post_bootstrap_budget_non_vacuous_and_tight (k_post : Nat) :
    bootstrapSteps + k_post ≤ htabQuadraticMaxK ↔ k_post ≤ htabQuadraticPostK := by
  rw [InitE.bootstrapSteps_eq]
  unfold htabQuadraticMaxK htabQuadraticPostK maxProbeLoopMultiplier htabMaxSourceClock
  omega

#print axioms htab_three_maxima_and_four_pass_isometry
#print axioms htab_quadratic_probe_multiplier_le_seven_lt_yukon
#print axioms htabQuadraticMaxK_yukonScore_representable
#print axioms htab_quadratic_pipeline_master_certificate
#print axioms end_to_end_htab_quadratic_finite_certificate
#print axioms htab_cold_max_iso_non_vacuous_and_tight
#print axioms htab_al_max_iso_non_vacuous_and_tight
#print axioms htab_probes_max_iso_non_vacuous_and_tight
#print axioms htab_kpan_two_iso_non_vacuous_and_tight
#print axioms htab_probe_multiplier_yukon_threshold_non_vacuous_and_tight
#print axioms htab_quadratic_max_budget_non_vacuous_and_tight
#print axioms htab_probes_ticks_per_probe_yukon_non_vacuous_and_tight
#print axioms htab_Cold_vs_AL_gap_non_vacuous_and_tight
#print axioms htab_post_bootstrap_budget_non_vacuous_and_tight

end InitECandidate.Solver.HtabQuadraticPipelineCert
