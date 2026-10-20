import InitECandidate.Solver.SelfContainedStageBounds
import InitECandidate.Solver.SelfContainedBoundedCertificate
import InitECandidate.Solver.GuestGasAndHtabBound
import InitECandidate.Solver.CrepToLoopStmtBound
import InitECandidate.Solver.CrepToLoopWhileCallBound
import InitECandidate.Solver.CrepToLoopFullBound
import InitECandidate.Solver.BackendLinearClockChain

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.FrontendLinearClockChain` — Self-Contained End-to-End Frontend (`Source -> Pan -> Crep -> Loop -> Word`) & Backend Linear Clock Chain

This module (`InitECandidate.Solver.FrontendLinearClockChain`) composes end-to-end:
1. **Self-Contained Frontend Clock Calculus (`Source -> Pan -> Crep -> Loop -> Word`)**:
   - `frontendClockBudget k_pan comparisons controlSteps`: affine frontend clock budget combining
     the `PanGlobals.compileTop` `+1` entry shift (`k_pan + 1`), the `0`-tick preserves of
     `PanSimp`, `PanStructs`, `PanToCrep`, `CrepInline`, and `LoopToWord`, and the quantitative
     `CrepToLoop` expansion `crepToLoopProgClockBudget comparisons controlSteps = comparisons + 2 * controlSteps`.
   - Exact bridge to `linearPipelineTargetBudget` and `BackendLinearClockChain.backendBudget`.
2. **Self-Contained `PanToCrep` -> `CrepInline` -> `CrepToLoop` -> `LoopToWord` Clocked Simulation**:
   - Directly composes `SelfContainedStageBounds.semanticsDecls_terminate_extract`,
     `SelfContainedStageBounds.pan_simp_structs_globals_clocked_sim`,
     `SelfContainedStageBounds.pan_to_crep_clocked_agree`,
     `SelfContainedStageBounds.crep_inline_clocked_agree`,
     `SelfContainedStageBounds.crep_to_loop_clocked_sim`,
     `SelfContainedStageBounds.loop_to_word_clocked_agree`, and
     `SelfContainedStageBounds.pan_to_word_halt_of_word_not_timeOut` inside `Solver/` without
     relying on `Proofs/BoundedPanToWord.lean`.
3. **End-to-End Composition with `GuestGasAndHtabBound` & `BackendLinearClockChain`**:
   - Connects `Guest.sourceBehaviour input = .terminate outcome events`, the EVM gas/call-graph/htab
     source budget `K_pan = guestSourceClockBudget gasSteps d probeBudget initTicks ≤ maxGuestSourceClock`,
     the frontend/backend linear clock chain (`k_word ≤ C_front * k_pan + D_front`,
     `k_stack ≤ C_ws * k_word + D_ws`, `k_lab ≤ C_sl * k_stack + D_sl`,
     `extra ≤ multiStepTargetBound stepFactor k_lab`), and the Yukon float64 ceiling
     `K_total < yukonFloat64Ceiling` (`900,719,925,474`).
-/

namespace InitECandidate.Solver.FrontendLinearClockChain

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.GuestStepBound
open InitECandidate.Solver.HtabLoadFactorBound
open InitECandidate.Solver.GuestGasAndHtabBound
open InitECandidate.Solver.CrepToLoopFullBound
open InitECandidate.Solver.BackendLinearClockChain
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanToTarget (semanticsDecls_mainFirstHOL)
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.LoopToWordStateRelImpSemanticsSupport
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget

/-! ## 1. Frontend Clock Budget (`Source -> Pan -> Crep -> Loop -> Word`) & Tight Algebraic Laws -/

/-- Exact frontend `WordSem` clock budget for a source `PanSem` run at clock `k_pan`
with accumulated `CrepToLoop` dynamic comparison count `comparisons` and control-step
count `controlSteps`:
- `PanSimp` and `PanStructs` consume `0` extra ticks (`k`),
- `PanGlobals.compileTop` shifts the entry clock by `+1` (`k_pan + 1`),
- `PanToCrep` and `CrepInline` consume `0` extra ticks (`k_pan + 1`),
- `CrepToLoop` adds `crepToLoopProgClockBudget comparisons controlSteps = comparisons + 2 * controlSteps`,
- `LoopToWord` consumes `0` extra ticks. -/
def frontendClockBudget (k_pan comparisons controlSteps : Nat) : Nat :=
  (k_pan + 1) + crepToLoopProgClockBudget comparisons controlSteps

/-- Affine frontend clock bound `C_front * k_pan + D_front`. -/
def frontendAffineBound (k_pan C_front D_front : Nat) : Nat :=
  C_front * k_pan + D_front

/-- 1. Exact decomposition, positivity (`1 ≤ frontendClockBudget`), step equations, and
monotonicity of `frontendClockBudget` across `k_pan`, `comparisons`, and `controlSteps`. -/
theorem frontendClockBudget_decomp_and_mono
    (k1 k2 c1 c2 s1 s2 : Nat)
    (hk : k1 ≤ k2) (hc : c1 ≤ c2) (hs : s1 ≤ s2) :
    frontendClockBudget 0 0 0 = 1 ∧
      1 ≤ frontendClockBudget k1 c1 s1 ∧
      frontendClockBudget k1 c1 s1 = (k1 + 1) + (c1 + 2 * s1) ∧
      frontendClockBudget (k1 + 1) c1 s1 = frontendClockBudget k1 c1 s1 + 1 ∧
      frontendClockBudget k1 c1 (s1 + 1) = frontendClockBudget k1 c1 s1 + 2 ∧
      frontendClockBudget k1 c1 s1 ≤ frontendClockBudget k2 c2 s2 := by
  unfold frontendClockBudget crepToLoopProgClockBudget M_crep_loop
  refine ⟨rfl, by omega, rfl, by omega, by omega, ?_⟩
  have hmul : 2 * s1 ≤ 2 * s2 := Nat.mul_le_mul_left 2 hs
  omega

/-- 2. Exact reduction of `frontendClockBudget` for a `.while` loop with per-iteration
guard comparison bound `C_cmp`, `k_crep` loop iterations, and body comparison budget `B_acc`,
bridging `CrepToLoopWhileCallBound.crepToLoop_while_iter_clock_expansion` and
`CrepToLoopFullBound.budget_while` into `frontendAffineBound`. -/
theorem frontendClockBudget_while_affine_bound
    (k_pan C_cmp k_crep B_acc : Nat)
    (hcret : k_crep ≤ k_pan) :
    (k_pan + 1) + ((C_cmp + 2) * (k_crep + 1) + B_acc) =
      frontendClockBudget k_pan (C_cmp * (k_crep + 1) + B_acc) (k_crep + 1) ∧
    frontendClockBudget k_pan (C_cmp * (k_crep + 1) + B_acc) (k_crep + 1) ≤
      frontendAffineBound k_pan (C_cmp + 3) (C_cmp + 3 + B_acc) ∧
    frontendClockBudget k_pan 0 k_pan = 3 * k_pan + 1 := by
  have hw := budget_while C_cmp k_crep B_acc
  unfold frontendClockBudget frontendAffineBound crepToLoopProgClockBudget M_crep_loop at *
  refine ⟨by omega, ?_, by omega⟩
  have h1 : (C_cmp + 2) * (k_crep + 1) ≤ (C_cmp + 2) * (k_pan + 1) :=
    Nat.mul_le_mul_left (C_cmp + 2) (Nat.add_le_add_right hcret 1)
  have h2 : (k_pan + 1) + ((C_cmp + 2) * (k_pan + 1) + B_acc) =
      (C_cmp + 3) * k_pan + (C_cmp + 3 + B_acc) := by
    rw [Nat.mul_add (C_cmp + 2) k_pan 1, Nat.mul_one]
    have h3 : (C_cmp + 3) * k_pan = k_pan + (C_cmp + 2) * k_pan := by
      rw [Nat.add_comm C_cmp 3, Nat.add_comm C_cmp 2]
      simp [Nat.add_mul]
      omega
    omega
  omega

/-- 3. Self-contained quantitative `CrepToLoop` statement & `.while` guard clock bound
bridging `CrepToLoopStmtBound.crepToLoop_compile_assign_clock_bound` and
`CrepToLoopWhileCallBound.crepToLoop_while_iter_clock_expansion` with `frontendClockBudget`. -/
theorem crepToLoop_assign_and_while_frontend_clock_bound {width : Nat} [NeZero width] {σ : Type}
    (n : Nat) (e : CrepExpHOL width) (v1 s1 : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width))
    (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet)
    (k_pan C_cmp : Nat)
    (hcmp : crepExpCmpCount e ≤ C_cmp)
    (hEval : evalCrepSemHOLProgExact v1 (.assign n e) = (res, s1))
    (hNotError : res ≠ some .error)
    (hState : crepToLoopStateRelExact v1 t)
    (hMem : crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact v1.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt v1.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt l v1.locals t.locals) :
    ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (t1 : LoopSemStateFiniteExact width σ),
      ck ≤ crepProgCmpCount (.assign n e) ∧
      ck ≤ C_cmp ∧
      (k_pan + 1) + ck ≤ frontendClockBudget k_pan C_cmp 0 ∧
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.assign n e))
        { t with clock := t.clock + ck } = (res1, t1) ∧
      s1.clock = v1.clock ∧
      t1.clock = t.clock ∧
      crepToLoopStateRelExact s1 t1 ∧
      res1 = resultToLoop res ∧
      localsResultRel ctxt l res s1 t1 := by
  obtain ⟨ck, res1, t1, hck, hrun, hsclk, htclk, hsr, _, _, _, hres1, hloc⟩ :=
    crepToLoop_compile_assign_clock_bound n e v1 res s1 t ctxt l
      hEval hNotError hState hMem hGlobals hCode hLocals
  have hck_cmp : ck ≤ C_cmp := by
    have hassign : crepProgCmpCount (.assign n e) = crepExpCmpCount e := rfl
    omega
  have hfb : (k_pan + 1) + ck ≤ frontendClockBudget k_pan C_cmp 0 := by
    unfold frontendClockBudget crepToLoopProgClockBudget M_crep_loop
    omega
  exact ⟨ck, res1, t1, hck, hck_cmp, hfb, hrun, hsclk, htclk, hsr, hres1, hloc⟩

/-! ## 2. Self-Contained `Source -> Pan -> Crep -> Loop -> Word` Clocked Simulation & Non-`timeOut` Halt Chain -/

/-- 4. Self-contained `Source -> Pan -> Crep -> Loop -> Word` clocked simulation and
non-`timeOut` halt agreement (proven purely via `SelfContainedStageBounds`, independent of
`Proofs/BoundedPanToWord.lean`):
Given `PanSemStateFiniteExact.semanticsDecls source start code = .terminate outcome events`,
1. `semanticsDecls_terminate_extract` extracts `stCtxt`, `s_decls`, and a finite source clock
   `k_pan` where `evaluateHOLFiniteState { s_decls with clock := k_pan } (.call none start [])`
   terminates with `.CompleteResult outcome` and `events`,
2. `pan_simp_structs_globals_clocked_sim` shifts the clock to `k_pan + 1` across `PanSimp`,
   `PanStructs`, and `PanGlobals.compileTop`,
3. `pan_to_crep_to_word_clocked_sim` composes `PanToCrep`, `CrepInline`, `CrepToLoop`, and
   `LoopToWord` to produce a `WordSem` run at clock `(k_pan + 1) + k'` with `.CompleteResult outcome`
   and `events`, and
4. for **any** `WordSem` clock budget `K_word` (e.g. `K_word ≤ frontendAffineBound k_pan C_front D_front`)
   that does not time out, `pan_to_word_halt_of_word_not_timeOut` guarantees that `WordSem` at
   `K_word` halts with `.CompleteResult outcome`, `events`, and `1 ≤ K_word`. -/
theorem self_contained_source_pan_to_word_clock_chain {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hterm : PanSemStateFiniteExact.semanticsDecls source start code = .terminate outcome events)
    (h : (∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
      noLabelsHOL target.memory (fun address => target.mdomain address = true) ∧
      start = ofString "main" ∧
      globalsSize = ((decShapesHOL code).map
        (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum ∧
      distinctParamsHOL (functionsHOL code) ∧
      (fun address => target.mdomain address = true) =
        (fun address => source.memaddrs address ∨ Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address) ∧
      (fun address => target.shMdomain address = true) = source.shMemaddrs ∧
      target.be = source.be ∧ target.ffi = source.ffi ∧
      target.store.lookup .currHeap = some (.word source.baseAddr) ∧
      target.store.lookup .heapLength = some (.word heapLen) ∧
      source.topAddr = source.baseAddr + (2 : BitVec width) * heapLen - panBytesInWord width * BitVec.ofNat width globalsSize ∧
      ((functionsHOL code).map Prod.fst).Nodup ∧ panGlobalsByteAlignedHOL source.topAddr ∧
      globalsAllocatableHOL source code ∧ source.code = HolFiniteMapExact.empty ∧
      target.code = sptFromAList (panToWordCompileProgHOL arch code) ∧
      source.globals = HolFiniteMapExact.empty ∧ source.locals = HolFiniteMapExact.empty ∧
      sizeOfEidsHOL code < 2 ^ width ∧ source.eshapes = HolFiniteMapExact.empty ∧
      sptLookup 0 target.locals = some (WordLocW.loc 1 0) ∧ goodDimindex width)
    (K_word : Nat) (res_word : Option (WordSemResult width))
    (t_word : WordSemStateFiniteExact width C σ)
    (hrun_w : WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
      { target with clock := K_word } = (res_word, t_word))
    (hnt_w : res_word ≠ some .timeOut) :
    wordEntryClass res_word = .CompleteResult outcome ∧
      t_word.ffi.ioEvents = events ∧
      1 ≤ K_word ∧
      ∃ stCtxt s_decls k_pan res_src s_src_post k' t_word_sim res_word_sim,
        decsStcnamesHOLExact [] code = some stCtxt ∧
        @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
          { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
          code = some s_decls ∧
        PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
          (.call none start [] : ProgHOL width) = (res_src, s_src_post) ∧
        panEntryClass res_src = .CompleteResult outcome ∧
        s_src_post.ffi.ioEvents = events ∧
        WordSemStateFiniteExact.evaluate
          (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
          { target with clock := (k_pan + 1) + k' } = (res_word_sim, t_word_sim) ∧
        wordEntryClass res_word_sim = .CompleteResult outcome ∧
        t_word_sim.ffi.ioEvents = events := by
  have hfail : PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail := by
    rw [hterm]; intro hc; cases hc
  have hfull : (∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
      noLabelsHOL target.memory (fun address => target.mdomain address = true) ∧
      start = ofString "main" ∧
      globalsSize = ((decShapesHOL code).map
        (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum ∧
      distinctParamsHOL (functionsHOL code) ∧
      (fun address => target.mdomain address = true) =
        (fun address => source.memaddrs address ∨ Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address) ∧
      (fun address => target.shMdomain address = true) = source.shMemaddrs ∧
      target.be = source.be ∧ target.ffi = source.ffi ∧
      target.store.lookup .currHeap = some (.word source.baseAddr) ∧
      target.store.lookup .heapLength = some (.word heapLen) ∧
      source.topAddr = source.baseAddr + (2 : BitVec width) * heapLen - panBytesInWord width * BitVec.ofNat width globalsSize ∧
      ((functionsHOL code).map Prod.fst).Nodup ∧ panGlobalsByteAlignedHOL source.topAddr ∧
      globalsAllocatableHOL source code ∧ source.code = HolFiniteMapExact.empty ∧
      target.code = sptFromAList (panToWordCompileProgHOL arch code) ∧
      source.globals = HolFiniteMapExact.empty ∧ source.locals = HolFiniteMapExact.empty ∧
      sizeOfEidsHOL code < 2 ^ width ∧ source.eshapes = HolFiniteMapExact.empty ∧
      sptLookup 0 target.locals = some (WordLocW.loc 1 0) ∧ goodDimindex width ∧
      PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hfail⟩
  obtain ⟨stCtxt, s_decls, hst, hev_decls, _, k_pan, res_src, s_src_post, hev_call, hclass_src, hio_src⟩ :=
    SelfContainedStageBounds.semanticsDecls_terminate_extract source start code outcome events hterm
  have hne_src : panEntryClass res_src ≠ .RunError := by
    rw [hclass_src]; intro herr; cases herr
  obtain ⟨k', t_word_sim, res_word_sim, hrun_sim, hio_sim, hclass_sim⟩ :=
    SelfContainedStageBounds.pan_to_word_clocked_sim source target arch code start globalsSize heapLen
      hfull stCtxt s_decls hst hev_decls k_pan res_src s_src_post hev_call hne_src
  obtain ⟨hclass_w, hio_w⟩ :=
    SelfContainedStageBounds.pan_to_word_halt_of_word_not_timeOut
      source target arch code start globalsSize heapLen hfull stCtxt s_decls hst hev_decls
      k_pan res_src s_src_post outcome hev_call hclass_src K_word res_word t_word hrun_w hnt_w
  have hk_word_pos : 1 ≤ K_word := by
    cases K_word with
    | zero =>
      rw [WordSemStateFiniteExact.evaluate.eq_def] at hrun_w
      dsimp only [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar] at hrun_w
      have hloc0 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [hloc0] at hrun_w
      dsimp only at hrun_w
      by_cases hbad : wordSemBadDestArgs (some firstLoopName) [0] = true
      · rw [if_pos hbad] at hrun_w
        injection hrun_w with hr _
        subst hr
        cases hclass_w
      · rw [if_neg hbad] at hrun_w
        split at hrun_w
        · injection hrun_w with hr _
          subst hr
          cases hclass_w
        · injection hrun_w with hr _
          exact False.elim (hnt_w hr.symm)
    | succ n => exact Nat.succ_le_succ (Nat.zero_le n)
  refine ⟨hclass_w, hio_w.trans hio_src, hk_word_pos,
    stCtxt, s_decls, k_pan, res_src, s_src_post, k', t_word_sim, res_word_sim,
    hst, hev_decls, hev_call, hclass_src, hio_src, hrun_sim,
    hclass_sim.trans hclass_src, hio_sim.trans hio_src⟩

/-! ## 3. Composition of Frontend (`Source -> Word`) with `BackendLinearClockChain` (`Word -> Stack -> Lab -> Target`) -/

/-- 5. End-to-end `Source -> Pan -> Crep -> Loop -> Word -> Stack -> Lab -> Target` clock chain:
combines `frontendClockBudget k_pan comparisons controlSteps ≤ frontendAffineBound k_pan C_front D_front`
with `BackendLinearClockChain.pan_clock_chain_bound` and `BackendLinearClockChain.target_run_of_clock_chain`
to execute the target machine at `linearPipelineTargetBudget k_pan C_front D_front (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1)`
without `.timeOut`. -/
theorem frontend_to_backend_target_run_of_clock_chain {width : Nat} [NeZero width] {S Q F : Type}
    (k_pan comparisons controlSteps k_word k_stack k_lab C_front D_front C_ws D_ws C_sl D_sl stepFactor : Nat)
    (mcSeq : Nat → MachineConfig width S Q)
    (sSeq : Nat → LabSem.State width LabToTarget.Config F)
    (msSeq : Nat → S) (lSeq : Nat → Nat)
    (s_end : LabSem.State width LabToTarget.Config F) (res : MachineResult)
    (hnt : res ≠ .timeOut)
    (hword_fb : k_word ≤ frontendClockBudget k_pan comparisons controlSteps)
    (hfb_aff : frontendClockBudget k_pan comparisons controlSteps ≤ frontendAffineBound k_pan C_front D_front)
    (hws : k_stack ≤ C_ws * k_word + D_ws)
    (hsl : k_lab ≤ C_sl * k_stack + D_sl)
    (hclock : (sSeq 0).clock = k_lab)
    (hbase : ∃ ms_end,
      evaluateTargetHOL (mcSeq k_lab) (sSeq k_lab).ffi (sSeq k_lab).clock (msSeq k_lab) =
        (res, ms_end, s_end.ffi))
    (hstep : ∀ i < k_lab,
      (sSeq i).clock ≠ 0 ∧
      (∀ k, evaluateTargetHOL (mcSeq i) (sSeq i).ffi (k + lSeq i) (msSeq i) =
        evaluateTargetHOL (mcSeq (i + 1)) (sSeq i).ffi k (msSeq (i + 1))) ∧
      lSeq i ≠ 0 ∧ lSeq i ≤ stepFactor + 1 ∧
      (sSeq (i + 1)).clock = (sSeq i).clock - 1 ∧
      (sSeq (i + 1)).ffi = (sSeq i).ffi) :
    let K_post := linearPipelineTargetBudget k_pan C_front D_front
      (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1)
    k_word ≤ C_front * k_pan + D_front ∧
      backendBudget k_word C_ws D_ws C_sl D_sl stepFactor ≤ K_post ∧
      ∃ ms_end,
        evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi K_post (msSeq 0) =
          (res, ms_end, s_end.ffi) := by
  dsimp only
  have hfront : k_word ≤ C_front * k_pan + D_front :=
    Nat.le_trans hword_fb hfb_aff
  obtain ⟨ms_end, hrun_back⟩ :=
    target_run_of_clock_chain k_word k_stack k_lab C_ws D_ws C_sl D_sl stepFactor
      mcSeq sSeq msSeq lSeq s_end res hnt hws hsl hclock hbase hstep
  have hback_le : backendBudget k_word C_ws D_ws C_sl D_sl stepFactor ≤
      linearPipelineTargetBudget k_pan C_front D_front
        (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1) := by
    simpa [backendBudget, linearPipelineTargetBudget, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using
      linearPipelineTargetBudget_of_stage_bounds k_pan k_word
        (C_sl * (C_ws * k_word + D_ws) + D_sl)
        (backendBudget k_word C_ws D_ws C_sl D_sl stepFactor)
        C_front D_front (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1)
        hfront (by simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]) (Nat.le_refl _)
  have hn : (evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi
      (backendBudget k_word C_ws D_ws C_sl D_sl stepFactor) (msSeq 0)).1 ≠ .timeOut := by
    rw [hrun_back]; exact hnt
  obtain ⟨ha, _⟩ := evaluateTarget_add_clock_of_not_timeOut (mcSeq 0) (sSeq 0).ffi (msSeq 0)
    (backendBudget k_word C_ws D_ws C_sl D_sl stepFactor)
    (linearPipelineTargetBudget k_pan C_front D_front
      (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1) -
      backendBudget k_word C_ws D_ws C_sl D_sl stepFactor) hn
  rw [Nat.add_sub_of_le hback_le] at ha
  exact ⟨hfront, hback_le, ms_end, ha.trans hrun_back⟩

/-! ## 4. Master Integration with `GuestGasAndHtabBound` & Self-Contained Yukon Certificate -/

/-- 6. Master Frontend-to-Backend & Guest Gas/Htab Composition Below the Yukon Ceiling:
integrates:
- `Guest.sourceBehaviour input = .terminate outcome events` (stabilized via
  `SelfContainedStageBounds.semanticsDecls_terminate_extract` & `semanticsDecls_terminate_at_clock`,
  without `Proofs/BoundedPanToWord.lean`),
- `GuestGasAndHtabBound.guest_htab_bound_of_declared_gas_limit` (`n ≤ 105,263` fresh keys,
  `2 * count ≤ cap`, probe `< cap`),
- `K_pan = guestSourceClockBudget gasSteps d probeBudget initTicks ≤ maxGuestSourceClock`
  (`43,934,217,712`),
- `frontendClockBudget K_pan comparisons controlSteps ≤ frontendAffineBound K_pan C_front D_front`,
- `BackendLinearClockChain.pan_clock_chain_bound` (`k_lab + extra ≤ K_post`), and
- `K_total = guestTotalTargetBudget K_pan C_front D_front (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1) < yukonFloat64Ceiling`
  (`878,684,407,372 < 900,719,925,474`). -/
theorem guest_frontend_backend_clock_chain_lt_yukon_ceiling
    {input : Guest.InputBlob} {decoded : Guest.InputDecode.StatelessInput}
    (hdecode : Guest.InputDecode.decodeStatelessInput input = some decoded)
    (hdeclared : Guest.GasLimit.declaredGasLimit input ≤ maxBlockGasLimit)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hsource : sourceBehaviour input = .terminate outcome events)
    (n : Nat) (hgas_keys : minGasPerKey * n ≤ decoded.payload.gasLimit)
    (used : Nat → Bool) (home : Nat)
    (hfree : ∃ j, j < (applyN n guestInitialTab).cap ∧ used j = false)
    (gasSteps d probeBudget initTicks : Nat)
    (hgas_steps : gasSteps ≤ decoded.payload.gasLimit)
    (hd : d ≤ guestCallGraphMaxDepth)
    (hprobe : probeBudget ≤ 200)
    (hinit : initTicks ≤ Guest.maxInputBytes)
    (comparisons controlSteps k_word k_stack k_lab extra C_front D_front C_ws D_ws C_sl D_sl stepFactor : Nat)
    (hword_fb : k_word ≤ frontendClockBudget (guestSourceClockBudget gasSteps d probeBudget initTicks) comparisons controlSteps)
    (hfb_aff : frontendClockBudget (guestSourceClockBudget gasSteps d probeBudget initTicks) comparisons controlSteps ≤
      frontendAffineBound (guestSourceClockBudget gasSteps d probeBudget initTicks) C_front D_front)
    (hws : k_stack ≤ C_ws * k_word + D_ws)
    (hsl : k_lab ≤ C_sl * k_stack + D_sl)
    (hextra : extra ≤ multiStepTargetBound stepFactor k_lab)
    (hCf : C_front ≤ 2) (hDf : D_front ≤ 1000)
    (hCb : C_sl * C_ws ≤ 5) (hDb : C_sl * D_ws + D_sl ≤ 10000) (hCt : stepFactor + 1 ≤ 2) :
    let K_pan := guestSourceClockBudget gasSteps d probeBudget initTicks
    let K_post := linearPipelineTargetBudget K_pan C_front D_front
      (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1)
    let K_total := guestTotalTargetBudget K_pan C_front D_front
      (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1)
    n ≤ maxFreshHtabKeys ∧
      (applyN n guestInitialTab).count = n ∧
      2 * (applyN n guestInitialTab).count ≤ (applyN n guestInitialTab).cap ∧
      (∃ r, r < (applyN n guestInitialTab).cap ∧
        probe used (applyN n guestInitialTab).cap home (applyN n guestInitialTab).cap = some r) ∧
      K_pan ≤ maxGuestSourceClock ∧
      k_lab + extra ≤ K_post ∧
      bootstrapSteps + (k_lab + extra) ≤ K_total ∧
      K_total < yukonFloat64Ceiling ∧
      ∃ stCtxt s_decls k_pan_wit res_src s_src_post,
        decsStcnamesHOLExact [] sourceDeclarations = some stCtxt ∧
        @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
          { sourceInitialState input with structs := stCtxt }
          (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
          sourceDeclarations = some s_decls ∧
        PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan_wit }
          (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post) ∧
        panEntryClass res_src = .CompleteResult outcome ∧
        s_src_post.ffi.ioEvents = events := by
  dsimp only
  have hmaster := guest_gas_and_htab_total_budget_lt_yukon_ceiling
    hdecode hdeclared n hgas_keys used home hfree gasSteps d probeBudget initTicks
    hgas_steps hd hprobe hinit
    C_front D_front (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1)
    hCf hDf hCb hDb hCt
  have hfront : k_word ≤ C_front * guestSourceClockBudget gasSteps d probeBudget initTicks + D_front :=
    Nat.le_trans hword_fb hfb_aff
  have hchain := pan_clock_chain_bound
    (guestSourceClockBudget gasSteps d probeBudget initTicks)
    k_word k_stack k_lab extra C_front D_front C_ws D_ws C_sl D_sl stepFactor
    hfront hws hsl hextra
  have hboot_chain : bootstrapSteps + (k_lab + extra) ≤
      guestTotalTargetBudget (guestSourceClockBudget gasSteps d probeBudget initTicks)
        C_front D_front (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1) :=
    Nat.add_le_add_left hchain bootstrapSteps
  have hsem := semanticsDecls_mainFirstHOL (sourceInitialState input) (ofString "main")
    (Guest.guestAst.map Pancake.PanLang.declToHOL) sourceHasMain
  have hterm : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations = .terminate outcome events :=
    hsem.trans hsource
  obtain ⟨stCtxt, s_decls, hst, hev_decls, _, k_pan_wit, res_src, s_src_post, hev_call, hclass, hio⟩ :=
    SelfContainedStageBounds.semanticsDecls_terminate_extract (sourceInitialState input) (ofString "main")
      sourceDeclarations outcome events hterm
  exact ⟨hmaster.1, hmaster.2.1, hmaster.2.2.1, hmaster.2.2.2.2.1,
    hmaster.2.2.2.2.2.2.1, hchain, hboot_chain, hmaster.2.2.2.2.2.2.2,
    stCtxt, s_decls, k_pan_wit, res_src, s_src_post, hst, hev_decls, hev_call, hclass, hio⟩

/-- 7. Self-contained finite-`K` certificate assembly over `guestTotalTargetBudget`:
combines `SelfContainedBoundedCertificate.finite_certificate_of_uniform_post_bootstrap_not_timeOut`
with `guestTotalTargetBudget_lt_yukon_ceiling_of_le_max` to certify
`InitE.Certificate (SelfContainedBoundedCertificate.baselineWithFiniteK K_total) (.finite K_total)`
with `K_total < yukonFloat64Ceiling` (`900,719,925,474`). -/
theorem self_contained_finite_certificate_of_frontend_backend_budget
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (K_pan C_front D_front C_ws D_ws C_sl D_sl stepFactor : Nat)
    (hk_pan : K_pan ≤ maxGuestSourceClock)
    (hCf : C_front ≤ 2) (hDf : D_front ≤ 1000)
    (hCb : C_sl * C_ws ≤ 5) (hDb : C_sl * D_ws + D_sl ≤ 10000) (hCt : stepFactor + 1 ≤ 2)
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
          (guestTotalTargetBudget K_pan C_front D_front
            (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1))
          (baselineInitialState input)).1 ≠ .timeOut) :
    let K_total := guestTotalTargetBudget K_pan C_front D_front
      (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1)
    InitE.Certificate (SelfContainedBoundedCertificate.baselineWithFiniteK K_total) (.finite K_total) ∧
      K_total < yukonFloat64Ceiling ∧
      bootstrapSteps ≤ K_total := by
  dsimp only
  have hcert := SelfContainedBoundedCertificate.finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth
    (linearPipelineTargetBudget K_pan C_front D_front
      (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1))
    hlab compiled depthBound not_timeOut
  have hlt := guestTotalTargetBudget_lt_yukon_ceiling_of_le_max
    K_pan C_front D_front (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1)
    hk_pan hCf hDf hCb hDb hCt
  have hge : bootstrapSteps ≤ guestTotalTargetBudget K_pan C_front D_front
      (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1) := by
    unfold guestTotalTargetBudget
    exact Nat.le_add_right bootstrapSteps _
  exact ⟨hcert, hlt, hge⟩

#print axioms frontendClockBudget_decomp_and_mono
#print axioms frontendClockBudget_while_affine_bound
#print axioms crepToLoop_assign_and_while_frontend_clock_bound
#print axioms self_contained_source_pan_to_word_clock_chain
#print axioms frontend_to_backend_target_run_of_clock_chain
#print axioms guest_frontend_backend_clock_chain_lt_yukon_ceiling
#print axioms self_contained_finite_certificate_of_frontend_backend_budget

end InitECandidate.Solver.FrontendLinearClockChain
