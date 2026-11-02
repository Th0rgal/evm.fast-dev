import InitECandidate.Solver.Wave8Stage.StackToLabClock
import InitECandidate.Solver.Wave8Stage.Stage4LabGlue
import InitECandidate.Solver.Wave8Stage.Stage4InitGlue
import InitECandidate.Solver.Wave8Stage.Stage4RawCallGlue
import InitECandidate.Solver.Wave8Stage.Stage4NamesGlue

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.Stage4

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage.StackToLabClock

variable {width : Nat} [NeZero width]

/-- The first four instructions alone exclude the proposed code-cost bound 3. -/
theorem initCode_stepCost_ge_four (generateGc : Bool) (maxHeap pointer : Nat) :
    4 ≤ stepCost (StackRemove.initCode (width := width) generateGc maxHeap pointer) := by
  change 4 ≤ 1 + (1 + (1 + (1 + _)))
  omega

/-- The full fixed initializer prefix costs at least 51 Lab extra steps,
without counting the generated store-list initialization instructions. -/
theorem initCode_stepCost_ge_fiftyOne (generateGc : Bool) (maxHeap pointer : Nat) :
    51 ≤ stepCost (StackRemove.initCode (width := width) generateGc maxHeap pointer) := by
  simp only [StackRemove.initCode, StackRemove.initMemory, listSeqHOL,
    moveHOL, subInst, addInst, StackRemove.rightShiftInst, StackRemove.leftShiftInst,
    StackRemove.constInst, StackRemove.loadInst, StackRemove.storeInst,
    addBytesInWordInst, stepCost]
  omega

/-- Every post-StackRemove table includes the initializer, even when the source
program is empty. This obstruction is independent of all source-code facts. -/
theorem compiled_table_not_codeStepBounded_three {C F : Type}
    (s : StackSemStateFiniteExact width C F)
    (jump generateGc : Bool) (bounds : BitVec width × BitVec width)
    (maxHeap pointer start : Nat) (program : List (Nat × HolProg width))
    (hc : s.code = sptFromAList
      (StackRemove.compileHOL jump bounds generateGc maxHeap pointer start program)) :
    ¬ CodeStepBounded 3 s := by
  intro hb
  have hl : sptLookup 0 s.code = some
      (.seq (StackRemove.initCode generateGc maxHeap pointer) (.call none (.inl start) none)) := by
    rw [hc, sptLookup_sptFromAList]
    simp [StackRemove.compileHOL, StackRemove.initStubs, sptAListLookup]
  have hu := hb.1 _ _ hl
  have hlower := initCode_stepCost_ge_four (width := width) generateGc maxHeap pointer
  simp only [stepCost, Nat.add_zero] at hu
  omega

/-- In particular, the actual intermediate state supplied by fullMakeInit
cannot meet the proposed bound 3, for any source code or machine state. -/
theorem fullMakeInit_s2_not_codeStepBounded_three {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (code : List (Nat × HolProg width))
    (t : LabSem.State width C F) (saveRegs : Nat → Bool)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :
    ¬ CodeStepBounded 3
      (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle) := by
  exact compiled_table_not_codeStepBounded_three _ sc.jump (StackToLab.isGenGc dc.gcKind)
    offset maxHeap sp BvlToBvi.initGlobalsLocation
    (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code) rfl

/-- A finite, program-dependent replacement for the unsupported constant 3. -/
def codeStepBudget (code : List (Nat × HolProg width)) : Nat :=
  (code.map (fun e => stepCost e.2)).foldr max 0

theorem stepCost_le_codeStepBudget {code : List (Nat × HolProg width)}
    {entry : Nat × HolProg width} (h : entry ∈ code) :
    stepCost entry.2 ≤ codeStepBudget code := by
  induction code with
  | nil => simp at h
  | cons e es ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- Finite installed code and an empty compilation oracle discharge the code
invariant with the explicit maximum of actual procedure costs. -/
theorem codeStepBounded_of_empty_oracle {C F : Type}
    (s : StackSemStateFiniteExact width C F) (code : List (Nat × HolProg width))
    (hc : s.code = sptFromAList code)
    (ho : ∀ i, (s.compileOracle i).2.1 = []) :
    CodeStepBounded (codeStepBudget code) s := by
  constructor
  · intro k p hp
    rw [hc, sptLookup_sptFromAList] at hp
    exact stepCost_le_codeStepBudget (sptAListLookup_mem _ _ _ hp)
  · intro i e he
    rw [ho i] at he
    exact False.elim (List.not_mem_nil he)

/-- Register renaming does not change the explicit finite code budget. -/
theorem codeStepBudget_names (names : Spt Nat) (code : List (Nat × HolProg width)) :
    codeStepBudget (StackNames.compileHOL names code) = codeStepBudget code := by
  simp [codeStepBudget, StackNames.compileHOL, List.map_map,
    StackNames.progCompEntryHOL, Function.comp_def, stepCost_progCompHOL]

/-- The actual post-StackNames initial state has a finite code bound without
any assumption about the syntactic size of the compiled guest procedures. -/
theorem fullMakeInit_s3_codeStepBounded {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (code : List (Nat × HolProg width))
    (t : LabSem.State width C F) (saveRegs : Nat → Bool)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (ho : ∀ i, (oracle i).2.1 = []) :
    CodeStepBounded
      (codeStepBudget (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code))
      (StackToLab.Proofs.FullMakeInitSemantics.s3 sc dc maxHeap sp offset code t saveRegs oracle) := by
  rw [← codeStepBudget_names sc.regNames]
  apply codeStepBounded_of_empty_oracle
  · rfl
  · intro i
    simp [StackToLab.Proofs.FullMakeInitSemantics.s3,
      StackToLab.Proofs.MakeInit.makeInit,
      StackToLab.Proofs.FullMakeInitSemantics.coracle3,
      StackToLab.Proofs.FullMakeInitSemantics.coracle2,
      StackToLab.Proofs.FullMakeInitSemantics.coracle1,
      Function.comp_def, ho, StackNames.compileHOL]

/-- The bound-3 obstruction persists at the actual StackToLab input, after
register renaming. Any whole-procedure bound there must be at least 51. -/
theorem fullMakeInit_s3_codeStepBounded_ge_fiftyOne {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (code : List (Nat × HolProg width))
    (t : LabSem.State width C F) (saveRegs : Nat → Bool)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (M : Nat)
    (hb : CodeStepBounded M
      (StackToLab.Proofs.FullMakeInitSemantics.s3 sc dc maxHeap sp offset code t saveRegs oracle)) :
    51 ≤ M := by
  have hl : sptLookup 0
      (StackToLab.Proofs.FullMakeInitSemantics.s3 sc dc maxHeap sp offset code t saveRegs oracle).code =
      some (StackNames.progCompHOL sc.regNames
        (.seq (StackRemove.initCode (StackToLab.isGenGc dc.gcKind) maxHeap sp)
          (.call none (.inl BvlToBvi.initGlobalsLocation) none))) := by
    change sptLookup 0 (sptFromAList (StackNames.compileHOL sc.regNames
      (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code))) = _
    rw [sptLookup_sptFromAList, StackNames.sptAListLookup_compileHOL]
    simp [StackToLab.Proofs.FullMakeInitSemantics.code2,
      StackRemove.compileHOL, StackRemove.initStubs, sptAListLookup]
  have hu := hb.1 _ _ hl
  rw [stepCost_progCompHOL] at hu
  have hlo := initCode_stepCost_ge_fiftyOne (width := width) (StackToLab.isGenGc dc.gcKind) maxHeap sp
  simp only [stepCost, Nat.add_zero] at hu
  omega

/-- FullMakeInit's standard assumptions already force successful execution of
the initializer; no separate successful-initializer premise is needed. -/
theorem fullMakeInit_init_result_none {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hA : StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle) :
    (StackSemEvaluate.evaluate
      (StackRemove.initCode (StackToLab.isGenGc dc.gcKind) maxHeap sp,
        StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)).1 = none := by
  obtain ⟨s1, hopt, _⟩ := StackRemove.Proofs.InitSemantics.makeInitSemantics sc.jump
    offset (StackToLab.isGenGc dc.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
    (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle)
    (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code)
    (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)
    bitmaps dataSp
    ⟨StackToLab.Proofs.FullMakeInitSemantics.dischargeThese_s2 hA,
      StackToLab.Proofs.FullMakeInitSemantics.propagateThese_s2 hA⟩
  unfold StackRemove.Proofs.InitMake.makeInitOpt at hopt
  split at hopt
  · cases hopt
  · rename_i post he
    exact congrArg Prod.fst he

/-- The real reduced initialization state is related to the state obtained by
executing initCode. This discharges the initial StackRemove relation from the
standard fullMakeInit assumptions. -/
theorem fullMakeInit_postInit_stateRel {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hA : StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle) :
    ∃ post, StackSemEvaluate.evaluate
      (StackRemove.initCode (StackToLab.isGenGc dc.gcKind) maxHeap sp,
        StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle) =
        (none, post) ∧
      StackRemove.stateRelHOL sc.jump offset sp
        (StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dc.gcKind) maxHeap
          bitmaps dataSp (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle) sc.jump offset sp
          (sptFromAList (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code))
          (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)) post := by
  obtain ⟨post, w2, w3, w4, run, _, _, _, _, _, _, _, _, _, rel, _⟩ :=
    Flapjack.Pancake.Proofs.PanToTarget.panToTargetInitCodeRun hA
  obtain ⟨s1, hopt, _⟩ := StackRemove.Proofs.InitSemantics.makeInitSemantics sc.jump
    offset (StackToLab.isGenGc dc.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
    (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle)
    (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code)
    (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)
    bitmaps dataSp
    ⟨StackToLab.Proofs.FullMakeInitSemantics.dischargeThese_s2 hA,
      StackToLab.Proofs.FullMakeInitSemantics.propagateThese_s2 hA⟩
  refine ⟨post, run, ?_⟩
  unfold StackRemove.Proofs.InitMake.makeInitAny
  rw [hopt]
  unfold StackRemove.Proofs.InitMake.makeInitOpt at hopt
  rw [run] at hopt
  simp only at hopt
  split at hopt
  · cases hopt
    exact rel
  · cases hopt

/-- Quantitative entry-call transfer with the actual procedure-cost bound.
This is the StackToLab part of Stage 4, before substituting the concrete
StackRawCall/StackRemove initial states. -/
theorem stackToLab_call_affine_not_timeOut {C F : Type}
    (M start : Nat) (s post : StackSemStateFiniteExact width C F)
    (res : Option (StackSemResult width)) (t : LabSem.State width C F)
    (hcode : CodeStepBounded M s)
    (run : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width), s) =
      (res, post))
    (rel : StackToLab.Proofs.StateRel.stateRel s t)
    (hpc : LabSem.locToPc start 0 t.code = some t.pc)
    (halt : StackToLab.Proofs.FlattenCallCorrect.haltAssum C F s.code)
    (hne : StackToLab.Proofs.FlattenSemantics.stackEntryClass res ≠ .RunError)
    (hnt : res ≠ some .timeOut) :
    (LabSem.evaluate { t with clock := (M + 1) * s.clock + M }).1 ≠ .timeOut := by
  have nerr : res ≠ some .error := by
    rintro rfl
    simp [StackToLab.Proofs.FlattenSemantics.stackEntryClass] at hne
  have hres : res ≠ some .timeOut →
      (∃ w : BitVec width, res = some (.halt (.word w))) ∨
      (∃ f, res = some (.finalFFI f)) ∨
      (∃ n, res = some (.result (.loc n 0)) ∧
        ∀ u : StackSemStateFiniteExact width C F, sptSubspt s.code u.code ∧ u.clock ≠ 0 →
          ∃ v, StackSemEvaluate.evaluate ((.call none (.inl n) none : HolProg width), u) =
              (some (.halt (.word 0)), v) ∧ v.ffi = u.ffi ∧ v.clock = u.clock - 1) := by
    intro hto
    rcases res with _ | x
    · simp [StackToLab.Proofs.FlattenSemantics.stackEntryClass] at hne
    rcases x with v | v | _ | _ | v | _ | e | _
    · rcases v with w | ⟨a, b⟩
      · simp [StackToLab.Proofs.FlattenSemantics.stackEntryClass] at hne
      · by_cases hab : a = 1 ∧ b = 0
        · obtain ⟨rfl, rfl⟩ := hab
          exact .inr (.inr ⟨1, rfl, halt⟩)
        · simp [StackToLab.Proofs.FlattenSemantics.stackEntryClass] at hne
          omega
    · simp [StackToLab.Proofs.FlattenSemantics.stackEntryClass] at hne
    · simp [StackToLab.Proofs.FlattenSemantics.stackEntryClass] at hne
    · simp [StackToLab.Proofs.FlattenSemantics.stackEntryClass] at hne
    · rcases v with w | ⟨a, b⟩
      · exact .inl ⟨w, rfl⟩
      · simp [StackToLab.Proofs.FlattenSemantics.stackEntryClass] at hne
    · exact absurd rfl hto
    · exact .inr (.inl ⟨e, rfl⟩)
    · simp [StackToLab.Proofs.FlattenSemantics.stackEntryClass] at hne
  obtain ⟨ck, r, final, _, hb, he, hf, hh, hr, _, _, _⟩ :=
    stackToLab_call_clock_simulation M start s post res t hcode run rel hpc nerr hres
  have hrnt : r ≠ .timeOut := by
    rcases hres hnt with ⟨w, hw⟩ | ⟨f, hf'⟩ | ⟨n, hn, _⟩
    · rw [hh _ hw]
      simp only
      split <;> simp
    · rw [hf _ hf']
      simp
    · rw [hr _ hn]
      simp
  have hmul := Nat.mul_le_mul_right M (Nat.sub_le s.clock post.clock)
  have hbudget : t.clock - 1 + ck ≤ (M + 1) * s.clock + M := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm M s.clock]
    omega
  have lifted := LabProps.evaluateAddClock
    { t with clock := t.clock - 1 + ck } r final
    ((M + 1) * s.clock + M - (t.clock - 1 + ck)) ⟨he, hrnt⟩
  have hsum : t.clock - 1 + ck + ((M + 1) * s.clock + M - (t.clock - 1 + ck)) =
      (M + 1) * s.clock + M := Nat.add_sub_of_le hbudget
  simp only [hsum] at lifted
  rw [lifted]
  exact hrnt

/-- Discharge the code, state relation, entry location, and halt-procedure
premises of the quantitative StackToLab transfer on the actual fullMakeInit
post-StackNames state. The remaining source-run premises are the Stage 4
StackRawCall/StackAlloc/StackRemove bridge obligations. -/
theorem fullMakeInit_lab_affine_not_timeOut {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hA : StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle)
    (ho : ∀ i, (oracle i).2.1 = []) (k : Nat)
    (hne : StackToLab.Proofs.FlattenSemantics.stackEntryClass
      (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
        { StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle
            with clock := k })).1 ≠ .RunError)
    (hnt : (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle
          with clock := k })).1 ≠ some .timeOut) :
    (LabSem.evaluate { t with clock := ((codeStepBudget (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code) + 1)
        * k + codeStepBudget (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code))
    }).1 ≠ .timeOut := by
  have hf : Function.Bijective (StackNames.findNameSpt sc.regNames) := by
    rcases hA with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hf⟩
    exact hf
  have namesEq := fullMakeInit_s2_s3_entry_result sc dc maxHeap sp offset code t saveRegs oracle hf 0 k
  rw [← namesEq] at hne hnt
  let s := StackToLab.Proofs.FullMakeInitSemantics.s3 sc dc maxHeap sp offset code t saveRegs oracle
  let M := codeStepBudget (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code)
  have hc : CodeStepBounded M { s with clock := k } :=
    fullMakeInit_s3_codeStepBounded sc dc maxHeap sp offset code t saveRegs oracle ho
  have hrel : StackToLab.Proofs.StateRel.stateRel { s with clock := k } { t with clock := k } :=
    StackToLab.Proofs.StateRel.stateRelWithClock
      (StackToLab.Proofs.FullMakeInitSemantics.stateRel_s3 hA)
  have hp := StackToLab.Proofs.FullMakeInitSemantics.locToPc_start hA
  have hh : StackToLab.Proofs.FlattenCallCorrect.haltAssum C F s.code :=
    StackToLab.Proofs.MakeInit.haltAssumLemma
  exact stackToLab_call_affine_not_timeOut M 0 { s with clock := k } _ _ { t with clock := k }
    hc rfl hrel hp hh hne hnt

/-- Compose the actual initializer, StackNames state boundary, and quantitative
StackToLab transfer. Only the post-initialization StackRemove run remains as a
source premise; the code-cost invariant is discharged from the compiled table. -/
theorem fullMakeInit_lab_affine_of_postInit_run {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hA : StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle)
    (ho : ∀ i, (oracle i).2.1 = [])
    (post : StackSemStateFiniteExact width C F)
    (hinit : StackSemEvaluate.evaluate
      (StackRemove.initCode (StackToLab.isGenGc dc.gcKind) maxHeap sp,
        StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle) =
      (none, post)) (k : Nat)
    (hne : StackToLab.Proofs.FlattenSemantics.stackEntryClass
      (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
          { post with clock := k })).1 ≠ .RunError)
    (hnt : (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { post with clock := k })).1 ≠ some .timeOut) :
    let M := codeStepBudget (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code)
    (LabSem.evaluate { t with clock := (M + 1) * k + (2 * M + 1) }).1 ≠ .timeOut := by
  let s2 := StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle
  have hentry : sptLookup 0 s2.code = some
      (.seq (StackRemove.initCode (StackToLab.isGenGc dc.gcKind) maxHeap sp)
        (.call none (.inl BvlToBvi.initGlobalsLocation) none)) := by
    change sptLookup 0 (sptFromAList
      (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code)) = _
    rw [sptLookup_sptFromAList]
    simp [StackToLab.Proofs.FullMakeInitSemantics.code2,
      StackRemove.compileHOL, StackRemove.initStubs, sptAListLookup]
  have he := stack_init_entry_result (StackToLab.isGenGc dc.gcKind) maxHeap sp
    BvlToBvi.initGlobalsLocation s2 post k hentry hinit
  have hn : StackToLab.Proofs.FlattenSemantics.stackEntryClass
      (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
        { s2 with clock := k + 1 })).1 ≠ .RunError := by
    rw [he]
    exact hne
  have ht : (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { s2 with clock := k + 1 })).1 ≠ some .timeOut := by
    rw [he]
    exact hnt
  have hlab := fullMakeInit_lab_affine_not_timeOut sc dc maxHeap sp offset bitmaps code t
    saveRegs dataSp oracle hA ho (k + 1) hn ht
  let M := codeStepBudget (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code)
  have budget : (M + 1) * (k + 1) + M = (M + 1) * k + (2 * M + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  change (LabSem.evaluate { t with clock := (M + 1) * (k + 1) + M }).1 ≠ .timeOut at hlab
  rwa [budget] at hlab

/-- Assembly interface for the remaining quantitative StackRemove step.
The callback is required only for the actual reduced state and its related
post-initializer target; initializer success and that relation are discharged. -/
theorem fullMakeInit_lab_affine_of_remove_bridge {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (t : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hA : StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle)
    (ho : ∀ i, (oracle i).2.1 = []) (k : Nat)
    (bridge : ∀ post : StackSemStateFiniteExact width C F,
      StackRemove.stateRelHOL sc.jump offset sp
        (StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dc.gcKind) maxHeap
          bitmaps dataSp (StackToLab.Proofs.FullMakeInitSemantics.coracle1 oracle) sc.jump offset sp
          (sptFromAList (StackToLab.Proofs.FullMakeInitSemantics.code1 dc code))
          (StackToLab.Proofs.FullMakeInitSemantics.s2 sc dc maxHeap sp offset code t saveRegs oracle)) post →
      let res := (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
          { post with clock := k })).1
      StackToLab.Proofs.FlattenSemantics.stackEntryClass res ≠ .RunError ∧ res ≠ some .timeOut) :
    let M := codeStepBudget (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset code)
    (LabSem.evaluate { t with clock := (M + 1) * k + (2 * M + 1) }).1 ≠ .timeOut := by
  obtain ⟨post, run, rel⟩ := fullMakeInit_postInit_stateRel
    sc dc maxHeap sp offset bitmaps code t saveRegs dataSp oracle hA
  obtain ⟨hne, hnt⟩ := bridge post rel
  exact fullMakeInit_lab_affine_of_postInit_run sc dc maxHeap sp offset bitmaps code t
    saveRegs dataSp oracle hA ho post run k hne hnt


end InitECandidate.Solver.Wave8Stage.Stage4
