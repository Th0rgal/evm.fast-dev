import InitECandidate.Solver.PanToCrepExactClockIso
import InitECandidate.Solver.LoopWordStackExactClockIso
import InitECandidate.Solver.WordToStackClockExactOffset
import InitECandidate.Solver.StackNamesExactClockIso

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.FourPassClockIsometryChain` — Wave 5 Atomic Worker `W5_21`

Self-contained composition of the four isometric compiler passes (`PanToCrep`, `LoopToWord`,
`WordToStack`, `StackNames`) in `Solver/`, with **0 `Proofs/Bounded*` imports**:

1. **Four-Pass Multiplicative Isometry (`1 * 1 * 1 * 1 = 1`)**:
   - `PanToCrep`: `C_pc = 1, D_pc = 0` (`PanToCrepExactClockIso`)
   - `LoopToWord`: `C_lw = 1, D_lw = 0` (`LoopWordStackExactClockIso`)
   - `WordToStack`: `C_ws = 1, D_ws = ck` (`WordToStackClockExactOffset`)
   - `StackNames`: `C_sn = 1, D_sn = 0` + `StackRemove.initCode = 0` ticks (`StackNamesExactClockIso`)
   - Product of multiplicative slopes: `C_pc * C_lw * C_ws * C_sn = 1 * 1 * 1 * 1 = 1`
     (`four_pass_multiplicative_isometry`).

2. **Front-to-Lab Multiplicative Reduction to `CrepToLoop` (`C_cl`) & `StackRemove` (`C_sr`)**:
   - In the 6-pass front-to-lab pipeline (`PanToCrep -> CrepToLoop -> LoopToWord -> WordToStack -> StackRemove -> StackNames`),
     composing the 6 affine clock maps collapses the total multiplicative factor from
     `C_sn * C_sr * C_ws * C_lw * C_cl * C_pc` to `C_sr * C_cl`.

3. **Semantic Composition Theorems**:
   - Composes `PanToCrep -> CrepToLoop -> LoopToWord` (`pan_to_crep_to_loop_to_word_clock_comp`),
   - Composes `WordToStack -> StackRemove.initCode -> StackNames` (`word_to_stack_to_names_entry_clock_comp`).
-/

namespace InitECandidate.Solver.FourPassClockIsometryChain

open InitE
open InitECandidate.Solver.PanToCrepExactClockIso
open InitECandidate.Solver.LoopWordStackExactClockIso
open InitECandidate.Solver.WordToStackClockExactOffset
open InitECandidate.Solver.StackNamesExactClockIso
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.PanToCrepStateRelImpSemanticsTop
open Flapjack.LoopToWord
open Flapjack.LoopToWord.CompileCorrect
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm

/-- Multiplicative clock factor for `LoopToWord` (`1`). -/
def C_lw : Nat := 1

/-- Additive clock offset for `LoopToWord` (`0`). -/
def D_lw : Nat := 0

/-- Multiplicative clock factor for `WordToStack` (`1`). -/
def C_ws : Nat := 1

/-- Product of the four isometric pass slopes (`PanToCrep`, `LoopToWord`, `WordToStack`, `StackNames`). -/
def fourPassSlopeProduct : Nat :=
  C_pc * C_lw * C_ws * C_sn

/-- Six-pass front-to-lab affine clock composition:
`PanToCrep (C_pc, D_pc) -> CrepToLoop (c_cl, d_cl) -> LoopToWord (C_lw, D_lw) -> WordToStack (C_ws, d_ws) -> StackRemove (c_sr, d_sr) -> StackNames (C_sn, D_sn)`. -/
def frontToLabAffine (c_cl d_cl d_ws c_sr d_sr k : Nat) : Nat :=
  affine C_sn D_sn
    (affine c_sr d_sr
      (affine C_ws d_ws
        (affine C_lw D_lw
          (affine c_cl d_cl
            (affine C_pc D_pc k)))))

/-- 1. Exact multiplicative clock isometry of the four passes (`1 * 1 * 1 * 1 = 1`) and
collapse of the 6-pass front-to-lab multiplicative expansion to `c_sr * c_cl` alone. -/
theorem four_pass_multiplicative_isometry (c_cl d_cl d_ws c_sr d_sr k : Nat) :
    C_pc = 1 ∧
      D_pc = 0 ∧
      C_lw = 1 ∧
      D_lw = 0 ∧
      C_ws = 1 ∧
      C_sn = 1 ∧
      D_sn = 0 ∧
      C_pc * C_lw * C_ws * C_sn = 1 ∧
      fourPassSlopeProduct = 1 ∧
      (C_sn * (c_sr * (C_ws * (C_lw * (c_cl * C_pc))))) = c_sr * c_cl ∧
      frontToLabAffine c_cl d_cl d_ws c_sr d_sr k =
        affine (c_sr * c_cl) (c_sr * (d_cl + d_ws) + d_sr) k ∧
      (frontToLabAffine c_cl d_cl d_ws c_sr d_sr k ≤
        affine (c_sr * c_cl) (c_sr * (d_cl + d_ws) + d_sr) k) := by
  unfold frontToLabAffine fourPassSlopeProduct affine C_pc D_pc C_lw D_lw C_ws C_sn D_sn
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ring, by ring, ?_⟩
  ring_nf; omega

/-- 2. Pure 4-pass affine chain (`PanToCrep -> LoopToWord -> WordToStack -> StackNames` with
`CrepToLoop` and `StackRemove` set to identity `(1, 0)`): exact unit slope and additive offset `d_ws`. -/
theorem four_pass_chain_affine_exact (d_ws k1 k2 : Nat) :
    affine C_sn D_sn (affine C_ws d_ws (affine C_lw D_lw (affine C_pc D_pc k1))) = k1 + d_ws ∧
      (affine C_sn D_sn (affine C_ws d_ws (affine C_lw D_lw (affine C_pc D_pc k1))) ≤
        affine C_sn D_sn (affine C_ws d_ws (affine C_lw D_lw (affine C_pc D_pc k2))) ↔ k1 ≤ k2) := by
  unfold affine C_pc D_pc C_lw D_lw C_ws C_sn D_sn
  omega

/-- 3. Reduction of the `budgetAt` front factor to `c_sr * c_cl` alone:
because `fourPassSlopeProduct = 1`, any bound `c_sr * c_cl ≤ M` immediately bounds the
full 6-pass front-to-lab budget `budgetAt (C_sn * c_sr * C_ws * C_lw * c_cl * C_pc)` by `budgetAt M`. -/
theorem front_to_lab_budget_reduces_to_cl_sr (c_cl c_sr M : Nat) :
    budgetAt (C_sn * (c_sr * (C_ws * (C_lw * (c_cl * C_pc))))) = budgetAt (c_sr * c_cl) ∧
      (c_sr * c_cl ≤ M →
        budgetAt (C_sn * (c_sr * (C_ws * (C_lw * (c_cl * C_pc))))) ≤ budgetAt M) := by
  have hmul : C_sn * (c_sr * (C_ws * (C_lw * (c_cl * C_pc)))) = c_sr * c_cl := by
    unfold C_sn C_ws C_lw C_pc
    ring
  rw [hmul]
  exact ⟨rfl, fun h => budgetAt_mono h⟩

/-- 4. Concrete `400B` and `M = 6` (`22,059,344,444`) threshold theorems for `c_sr * c_cl`:
when `c_sr * c_cl ≤ 6`, the 6-pass front-to-lab budget is at most `22,059,344,444 < 400,000,000,000`. -/
theorem front_to_lab_cl_sr_six_lt_400B (c_cl c_sr : Nat) (h : c_sr * c_cl ≤ 6) :
    budgetAt (C_sn * (c_sr * (C_ws * (C_lw * (c_cl * C_pc))))) ≤ 22059344444 ∧
      bootstrapSteps + SelfContainedMasterK.bMax *
        ((c_sr * c_cl) * (SelfContainedMasterK.refinedSourceClock +
          SelfContainedMasterK.pipeOffset)) < 400000000000 := by
  have hred := (front_to_lab_budget_reduces_to_cl_sr c_cl c_sr 6).2 h
  rw [budgetAt_6] at hred
  have h108 : c_sr * (c_cl * 1) ≤ 108 := by rw [Nat.mul_one]; omega
  have hlt := iso_front_budget_lt_400B 1 c_cl c_sr h108
  rw [Nat.mul_one] at hlt
  exact ⟨hred, hlt⟩

/-- 5. Semantic composition of `PanToCrep` (`C_pc = 1, D_pc = 0`), `CrepToLoop` (`ck` additive ticks),
and `LoopToWord` (`C_lw = 1, D_lw = 0`):
for any `ProgHOL width` program `prog`, the three-stage `PanSem -> CrepSem -> LoopSem -> WordSem`
chain executes at clock `s.clock + ck` (`0` ticks from `PanToCrep` and `LoopToWord`), preserves
FFI state across all three passes, and preserves non-`timeOut` execution with exact end-clock
equality `w1.clock = s1.clock` on all non-`timeOut`, non-`finalFfi` runs. -/
theorem pan_to_crep_to_loop_to_word_clock_comp {width : Nat} [NeZero width] {C σ : Type}
    (prog : ProgHOL width) (s s1 : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width))
    (t : CrepSemHOLState width σ) (ctxt_pc : PanToCrepContextExact width)
    (u : LoopSemStateFiniteExact width σ) (ctxt_loop : CrepToLoopContextExact) (l : NumSet)
    (w : WordSemStateFiniteExact width C σ) (ctxt_lw : Spt Nat)
    (retv : WordLocW width) (l_lw : Nat × Nat)
    (hev : s.evaluateHOLFiniteState prog = (res, s1))
    (hne : res ≠ some .error)
    (hsr_pc : panToCrepStateRelFiniteExact s t)
    (hcode_pc : codeRelExactHOLW ctxt_pc s.code t.code)
    (hexcp_pc : panToCrepExcpRelFiniteExact ctxt_pc.eids s.eshapes)
    (hlocals_pc : panToCrepLocalsRelFiniteExact ctxt_pc s.locals t.locals)
    (hloc_pc : localisedProgHOL prog = true)
    (hsr_cl : crepToLoopStateRelExact t u)
    (hmem_cl : crepToLoopMemRelHOLExact t.memory u.memory t.memaddrs)
    (hglob_cl : crepToLoopGlobalsRelHOLExact t.globals u.globals)
    (hcode_cl : crepToLoopCodeRelExact ctxt_loop t.code u.code)
    (hlocals_cl : crepToLoopLocalsRelExact ctxt_loop l t.locals u.locals)
    (hsr_lw : ∀ ck, loopToWordStateRelHOLExact
      { u with clock := panToCrepClockBudget s.clock + ck }
      { w with clock := panToCrepClockBudget s.clock + ck })
    (hlocals_lw : LoopToWord.localsRelHOL ctxt_lw u.locals w.locals)
    (hretv : sptLookup 0 w.locals = some retv)
    (hdim : goodDimindex width)
    (hnwloc : ¬ wordSemIsWordLoc retv = true)
    (hacc : ∀ k, sptMem k (accVarsHOL
      (compileHOLExact ctxt_loop l (compileProgExactHOLW ctxt_pc prog)) .ln) → sptMem k ctxt_lw) :
    ∃ (res_crep : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ)
      (ck : Nat) (res_loop : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (u1 : LoopSemStateFiniteExact width σ)
      (w1 : WordSemStateFiniteExact width C σ) (res_word : Option (WordSemResult width)),
      evalCrepSemHOLProgExact { t with clock := panToCrepClockBudget s.clock }
          (compileProgExactHOLW ctxt_pc prog) = (res_crep, t1) ∧
        LoopSemStateFiniteExact.evaluate
          (compileHOLExact ctxt_loop l (compileProgExactHOLW ctxt_pc prog))
          { u with clock := panToCrepClockBudget s.clock + ck } = (res_loop, u1) ∧
        WordSemStateFiniteExact.evaluate
          (LoopToWord.compHOL ctxt_lw
            (compileHOLExact ctxt_loop l (compileProgExactHOLW ctxt_pc prog)) l_lw).1
          { w with clock := C_lw * (panToCrepClockBudget s.clock + ck) + D_lw } = (res_word, w1) ∧
        t1.clock = s1.clock ∧
        u1.clock = s1.clock ∧
        w1.ffi = s1.ffi ∧
        (res ≠ some .timeOut → res_loop ≠ some .timeOut) ∧
        (res ≠ some .timeOut → (∀ f, res ≠ some (.finalFfi f)) →
          w1.clock = s1.clock ∧
          (C_lw * (panToCrepClockBudget s.clock + ck) + D_lw) - w1.clock =
            (s.clock + ck) - s1.clock) := by
  obtain ⟨res_crep, t1, ck, res_loop, u1, hrun_pc, hrun_cl, hclk_t1, hclk_u1, hffi_u1,
      _, _, hres_pc, hres_cl, hnt_loop⟩ :=
    pan_to_crep_to_loop_clock_comp prog s s1 res t ctxt_pc u ctxt_loop l
      hev hne hsr_pc hcode_pc hexcp_pc hlocals_pc hloc_pc
      hsr_cl hmem_cl hglob_cl hcode_cl hlocals_cl
  have hiff_pc := pcCompileCorrectResultRel_not_timeOut_iff ctxt_pc s1 t1 res res_crep hres_pc
  have hne_loop : res_loop ≠ some .error := by
    rw [hres_cl]
    have hne_crep := hiff_pc.1
    rcases res_crep with _ | (_ | _ | _ | _ | _ | _) <;>
      simp [resultToLoop] at hne_crep ⊢
  have hlw_clk : C_lw * (panToCrepClockBudget s.clock + ck) + D_lw =
      panToCrepClockBudget s.clock + ck := by
    unfold C_lw D_lw; omega
  obtain ⟨w1, res_word, hrun_lw, _, hffi_w1, _, hpost_lw⟩ :=
    loop_to_word_clock_iso
      (compileHOLExact ctxt_loop l (compileProgExactHOLW ctxt_pc prog))
      { u with clock := panToCrepClockBudget s.clock + ck }
      res_loop u1
      { w with clock := panToCrepClockBudget s.clock + ck }
      ctxt_lw retv l_lw
      ⟨hrun_cl, hne_loop, hsr_lw ck, hlocals_lw, hretv, hdim, hnwloc, hacc⟩
  rw [← hlw_clk] at hrun_lw
  refine ⟨res_crep, t1, ck, res_loop, u1, w1, res_word, hrun_pc, hrun_cl, hrun_lw,
    hclk_t1, hclk_u1, hffi_w1.trans hffi_u1, hnt_loop, ?_⟩
  intro hnt hff
  have hnt_l : res_loop ≠ some .timeOut := hnt_loop hnt
  have hff_l : ∀ f, res_loop ≠ some (.finalFfi f) := by
    intro f hfl
    rw [hres_cl] at hfl
    have hff_c : res_crep ≠ some (.finalFfi f) := fun hc => hff f ((hiff_pc.2.2.2 f).mp hc)
    rcases res_crep with _ | (_ | _ | _ | _ | _ | _) <;>
      simp_all [resultToLoop]
  obtain ⟨hw1_clk, _⟩ := hpost_lw hnt_l hff_l
  have hw1_s1 : w1.clock = s1.clock := hw1_clk.trans hclk_u1
  refine ⟨hw1_s1, ?_⟩
  have hbud : panToCrepClockBudget s.clock = s.clock := (pan_to_crep_budget_iso s.clock 0).2.2.1
  rw [hlw_clk, hbud, hw1_s1]

/-- 6. Semantic composition of `WordToStack` (`C_ws = 1, D_ws = ck`), `StackRemove.initCode`
(`0` ticks), and `StackNames` (`C_sn = 1, D_sn = 0`):
given a `WordSem` entry call `.call none (some start) [0] none` from `s_word` to `(res_word, s1_word)`,
the `WordToStack` target call runs at `t_stack.clock + ck` with `0` multiplicative expansion,
and wrapping with `StackRemove.initCode` (`0` ticks) plus `StackNames` (`C_sn = 1, D_sn = 0`)
executes entry `0` at `C_sn * (t_stack.clock + ck + 1) + D_sn = t_stack.clock + ck + 1`. -/
theorem word_to_stack_to_names_entry_clock_comp {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (start : Nat)
    (s_word s1_word : WordSemStateFiniteExact width (Nat × C) F) (k : Nat)
    (res_word : Option (WordSemResult width))
    (t_stack s2_stack : StackSemStateFiniteExact width C F) (lens : List Nat)
    (generateGc : Bool) (maxHeap pointer : Nat)
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat)
    (hrun_word : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) s_word =
      (res_word, s1_word))
    (hne_word : res_word ≠ some .error)
    (hrel_ws : WordToStackProofs.stateRel ac k 0 0 s_word t_stack lens 0)
    (hentry : sptLookup 0 s2_stack.code =
      some (.seq (StackRemove.initCode generateGc maxHeap pointer)
        (.call none (.inl start) none)))
    (hrun_init : StackSemEvaluate.evaluate (StackRemove.initCode generateGc maxHeap pointer, s2_stack) =
      (none, t_stack))
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s2_stack.useAlloc) (hs : ¬s2_stack.useStore) (hk : ¬s2_stack.useStack)
    (hc : s2_stack.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    ∃ (ck : Nat) (t1_stack : StackSemStateFiniteExact width C F)
      (res_stack : Option (StackSemResult width)),
      clockNeutralHOL (StackRemove.initCode (width := width) generateGc maxHeap pointer) ∧
        t_stack.clock = s2_stack.clock ∧
        s_word.clock = t_stack.clock ∧
        StackSemEvaluate.evaluate (.call none (.inl start) none,
          { t_stack with clock := C_ws * t_stack.clock + ck }) = (res_stack, t1_stack) ∧
        (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
          { StackNamesExactClockIso.stateRel c f s2_stack with
            clock := C_sn * (C_ws * t_stack.clock + ck + 1) + D_sn })).1 = res_stack ∧
        (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
          { StackNamesExactClockIso.stateRel c f s2_stack with
            clock := C_sn * (C_ws * t_stack.clock + ck + 1) + D_sn })).2.ffi = t1_stack.ffi ∧
        (res_word.map compileResult = res_stack →
          s1_word.ffi = t1_stack.ffi ∧
          t1_stack.clock = s1_word.clock ∧
          s1_word.clock ≤ t_stack.clock ∧
          (C_ws * t_stack.clock + ck) - t1_stack.clock =
            (s_word.clock - s1_word.clock) + ck) := by
  obtain ⟨ck, t1_stack, res_stack, hrun_ws, hpost_ws⟩ :=
    word_to_stack_exact_offset ac start s_word k res_word s1_word t_stack lens
      hrun_word hne_word hrel_ws
  have hcws : C_ws * t_stack.clock + ck = t_stack.clock + ck := by
    unfold C_ws; omega
  have hsn := stack_names_compose_init_code_neutral generateGc maxHeap pointer start c f
    s2_stack t_stack (C_ws * t_stack.clock + ck) hentry hrun_init hf ha hs hk hc
  have hrun_ws' : StackSemEvaluate.evaluate (.call none (.inl start) none,
      { t_stack with clock := C_ws * t_stack.clock + ck }) = (res_stack, t1_stack) := by
    rwa [hcws]
  have hr_eq : (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { StackNamesExactClockIso.stateRel c f s2_stack with
        clock := C_sn * (C_ws * t_stack.clock + ck + 1) + D_sn })).1 = res_stack := by
    rw [hsn.2.2.1, hrun_ws']
  have hffi_eq : (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { StackNamesExactClockIso.stateRel c f s2_stack with
        clock := C_sn * (C_ws * t_stack.clock + ck + 1) + D_sn })).2.ffi = t1_stack.ffi := by
    rw [hsn.2.2.2.1, hrun_ws']
  refine ⟨ck, t1_stack, res_stack, hsn.1, hsn.2.1, stateRel_clock_eq ac k hrel_ws,
    hrun_ws', hr_eq, hffi_eq, ?_⟩
  intro hsame
  rw [hcws]
  exact hpost_ws hsame

/-! ## Non-Vacuous and Tight Verification Theorems (`>= 8` theorems) -/

/-- 7. Tightness 1: Exact four-pass slope product boundary (`C_pc * C_lw * C_ws * C_sn ≤ m ↔ 1 ≤ m`). -/
theorem four_pass_slope_product_non_vacuous_and_tight (m : Nat) :
    C_pc * C_lw * C_ws * C_sn ≤ m ↔ 1 ≤ m := by
  unfold C_pc C_lw C_ws C_sn
  omega

/-- 8. Tightness 2: Exact `PanToCrep` + `LoopToWord` composite clock budget boundary
(`affine C_lw D_lw (panToCrepClockBudget k) ≤ b ↔ k ≤ b`). -/
theorem pan_crep_loop_word_budget_non_vacuous_and_tight (k b : Nat) :
    affine C_lw D_lw (panToCrepClockBudget k) ≤ b ↔ k ≤ b := by
  unfold affine C_lw D_lw panToCrepClockBudget C_pc D_pc
  omega

/-- 9. Tightness 3: Exact `LoopToWord` + `WordToStack` composite affine clock boundary
(`affine C_ws ck (affine C_lw D_lw k) ≤ b ↔ k + ck ≤ b`). -/
theorem loop_word_stack_offset_non_vacuous_and_tight (k ck b : Nat) :
    affine C_ws ck (affine C_lw D_lw k) ≤ b ↔ k + ck ≤ b := by
  unfold affine C_ws C_lw D_lw
  omega

/-- 10. Tightness 4: Exact `WordToStack` + `StackRemove.initCode` + `StackNames` entry clock boundary
(`C_sn * (C_ws * k + ck + 1) + D_sn ≤ b ↔ k + ck < b`). -/
theorem word_stack_names_init_entry_non_vacuous_and_tight (k ck b : Nat) :
    C_sn * (C_ws * k + ck + 1) + D_sn ≤ b ↔ k + ck < b := by
  unfold C_sn D_sn C_ws
  omega

/-- 11. Tightness 5: Exact 4-pass pure chain (`PanToCrep -> LoopToWord -> WordToStack -> StackNames`)
clock budget boundary (`affine C_sn D_sn (affine C_ws ck (affine C_lw D_lw (panToCrepClockBudget k))) ≤ b ↔ k + ck ≤ b`). -/
theorem four_pass_pure_chain_budget_non_vacuous_and_tight (k ck b : Nat) :
    affine C_sn D_sn (affine C_ws ck (affine C_lw D_lw (panToCrepClockBudget k))) ≤ b ↔
      k + ck ≤ b := by
  unfold affine C_sn D_sn C_ws C_lw D_lw panToCrepClockBudget C_pc D_pc
  omega

/-- 12. Tightness 6: Exact 6-pass `frontToLabAffine` clock boundary
(`frontToLabAffine c_cl d_cl d_ws c_sr d_sr k ≤ b ↔ (c_sr * c_cl) * k + (c_sr * (d_cl + d_ws) + d_sr) ≤ b`). -/
theorem front_to_lab_affine_non_vacuous_and_tight (c_cl d_cl d_ws c_sr d_sr k b : Nat) :
    frontToLabAffine c_cl d_cl d_ws c_sr d_sr k ≤ b ↔
      (c_sr * c_cl) * k + (c_sr * (d_cl + d_ws) + d_sr) ≤ b := by
  rw [(four_pass_multiplicative_isometry c_cl d_cl d_ws c_sr d_sr k).2.2.2.2.2.2.2.2.2.2.1]
  unfold affine
  exact Iff.rfl

/-- 13. Tightness 7: Sharp 6-pass front-to-lab `400B` threshold reduction to `c_sr * c_cl ≤ 108`. -/
theorem front_to_lab_400B_threshold_non_vacuous_and_tight (c_cl c_sr : Nat) :
    bootstrapSteps + SelfContainedMasterK.bMax *
      ((C_sn * (c_sr * (C_ws * (C_lw * (c_cl * C_pc))))) *
        (SelfContainedMasterK.refinedSourceClock + SelfContainedMasterK.pipeOffset)) <
      400000000000 ↔ c_sr * c_cl ≤ 108 := by
  have hmul : C_sn * (c_sr * (C_ws * (C_lw * (c_cl * C_pc)))) = c_sr * c_cl := by
    unfold C_sn C_ws C_lw C_pc; ring
  rw [hmul]
  exact SelfContainedMasterK.front_factor_threshold (c_sr * c_cl)

/-- 14. Tightness 8: Sharp 6-pass front-to-lab `M = 6` (`22,059,344,444`) threshold reduction
to `c_sr * c_cl ≤ 6`. -/
theorem front_to_lab_factor_six_threshold_non_vacuous_and_tight (c_cl c_sr : Nat) :
    budgetAt (C_sn * (c_sr * (C_ws * (C_lw * (c_cl * C_pc))))) ≤ 22059344444 ↔
      c_sr * c_cl ≤ 6 := by
  have hmul : C_sn * (c_sr * (C_ws * (C_lw * (c_cl * C_pc)))) = c_sr * c_cl := by
    unfold C_sn C_ws C_lw C_pc; ring
  rw [hmul, ← budgetAt_6]
  unfold budgetAt
  rw [InitE.bootstrapSteps_eq, SelfContainedMasterK.refinedSourceClock_eq.1]
  unfold SelfContainedMasterK.bMax SelfContainedMasterK.pipeOffset
  omega

/-- 15. Tightness 9: Exact consumed-ticks conservation across the 4 isometric passes
(`(k + ck) - k1 ≤ d ↔ (k - k1) + ck ≤ d` when `k1 ≤ k`). -/
theorem four_pass_consumed_ticks_non_vacuous_and_tight (k k1 ck d : Nat) (hle : k1 ≤ k) :
    (C_sn * (C_ws * (C_lw * (C_pc * k + D_pc) + D_lw) + ck) + D_sn) - k1 ≤ d ↔
      (k - k1) + ck ≤ d := by
  unfold C_sn D_sn C_ws C_lw D_lw C_pc D_pc
  omega

#print axioms four_pass_multiplicative_isometry
#print axioms four_pass_chain_affine_exact
#print axioms front_to_lab_budget_reduces_to_cl_sr
#print axioms front_to_lab_cl_sr_six_lt_400B
#print axioms pan_to_crep_to_loop_to_word_clock_comp
#print axioms word_to_stack_to_names_entry_clock_comp
#print axioms four_pass_slope_product_non_vacuous_and_tight
#print axioms pan_crep_loop_word_budget_non_vacuous_and_tight
#print axioms loop_word_stack_offset_non_vacuous_and_tight
#print axioms word_stack_names_init_entry_non_vacuous_and_tight
#print axioms four_pass_pure_chain_budget_non_vacuous_and_tight
#print axioms front_to_lab_affine_non_vacuous_and_tight
#print axioms front_to_lab_400B_threshold_non_vacuous_and_tight
#print axioms front_to_lab_factor_six_threshold_non_vacuous_and_tight
#print axioms four_pass_consumed_ticks_non_vacuous_and_tight

end InitECandidate.Solver.FourPassClockIsometryChain
