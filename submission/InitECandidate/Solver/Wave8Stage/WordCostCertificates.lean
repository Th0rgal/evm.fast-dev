import InitECandidate.Solver.Wave8Stage.WordCostEffectPrimitives
import InitECandidate.Solver.Wave8Stage.WordCostEffectIO
import InitECandidate.Solver.Wave8Stage.WordCostEffectCalls
import InitECandidate.Solver.Wave8Stage.WordCostEffectLoops
import InitECandidate.Solver.Wave8Stage.WordOracleInvariant
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate
import Flapjack.Pancake.Semantics.LoopSem

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8Stage.WordCostCertificates
open Flapjack WordSemStateFiniteExact WordToStackSourceCost WordCostControl WordCostEffects

abbrev Subeffects (first second : Effects) : Prop :=
  ∀ exit cost, Covers (first exit) cost → Covers (second exit) cost

theorem at_mono {width : Nat} [NeZero width] {C F : Type}
    {first second : Effects} {p : WordLangProgHOL (BitVec width)}
    {s : WordSemStateFiniteExact width C F}
    (le : Subeffects first second) (h : At first p s) : At second p s :=
  fun ne nt => le _ _ (h ne nt)

/-- Syntactic certificates for outcome-sensitive costs. Code summaries are
checked separately at each actual lookup. Invalid primitives have no rule. -/
inductive Derives {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool) :
    WordLangProgHOL (BitVec width) → Effects → Prop where
  | normal (p : WordLangProgHOL (BitVec width)) (h : erase p = .skip) :
      Derives defs terminal p (atom .fall 0)
  | tick : Derives defs terminal .tick (atom .fall (-1))
  | share (op : WordMemOp) (reg : Nat) (exp : WordLangExpHOL (BitVec width)) :
      Derives defs terminal (.shareInst op reg exp) (merge (atom .fall 1) (atom .final 1))
  | raise (reg : Nat) : Derives defs terminal (.raise reg) (atom .raised 1)
  | result (reg : Nat) (regs : List Nat) :
      Derives defs terminal (.return reg regs) (atom .returned 0)
  | breakTo (label : Nat) : Derives defs terminal (.break label) (atom (.breakTo label) 0)
  | continueTo (label : Nat) : Derives defs terminal (.continue label) (atom (.continueTo label) 0)
  | ffi (name : Basis.Pure.MlString.MlString) (p1 l1 p2 l2 : Nat) (names : WordLangCutsetsHOL) :
      Derives defs terminal (.ffi name p1 l1 p2 l2 names) (ffiEffects (terminal name))
  | seq {first second : WordLangProgHOL (BitVec width)} {a b : Effects}
      (left : Derives defs terminal first a) (right : Derives defs terminal second b) :
      Derives defs terminal (.seq first second) (WordCostEffects.seq a b)
  | branch (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec width))
      {first second : WordLangProgHOL (BitVec width)} {a b : Effects}
      (left : Derives defs terminal first a) (right : Derives defs terminal second b) :
      Derives defs terminal (.ite cmp reg operand first second) (merge a b)
  | loop (names exits : WordLangNumSetHOL) {body : WordLangProgHOL (BitVec width)} {effects : Effects}
      (bodyRule : Derives defs terminal body effects)
      (cycle : AtMost (join (effects .fall) (effects (.continueTo 0))) 1) :
      Derives defs terminal (.loop names body exits) (loopEffects effects)
  | tail (dest : Option Nat) (args : List Nat) :
      Derives defs terminal (.call none dest args none) (shift (some (-1)) (defs dest))
  | returning (names : List Nat) (live : WordLangCutsetsHOL)
      (next : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
      (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
      (contEffects handlerEffects : Effects)
      (cont : Derives defs terminal next contEffects)
      (handlers : ∀ name body h1 h2, handler = some (name,body,h1,h2) →
        Derives defs terminal body handlerEffects) :
      Derives defs terminal (.call (some (names,live,next,l1,l2)) dest args handler)
        (returningEffects (defs dest) contEffects (handler.map (fun _ => handlerEffects)))

private theorem call_positive {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F)
    (ne : (evaluate (.call ret dest args handler) s).1 ≠ some .error)
    (nt : (evaluate (.call ret dest args handler) s).1 ≠ some .timeOut) : s.clock ≠ 0 := by
  intro zero
  rw [Compiler.Backend.WordToWord.evaluate_call_eq] at ne nt
  simp only [zero,if_true] at ne nt
  rcases ret with _ | ⟨_,_,_,_,_⟩ <;> rcases handler with _ | ⟨_,_,_,_⟩ <;>
    (repeat' split at ne) <;> simp_all


private theorem world_after {width : Nat} [NeZero width] {C F : Type}
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (oracle : HolOracle F)
    (codeNoInstall : WordProps.noInstallCode code)
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (ni : noInstallSubprogsHOL p = true)
    (world : s.code = code ∧ s.ffi.oracle = oracle) :
    (evaluate p s).2.code = code ∧ (evaluate p s).2.ffi.oracle = oracle := by
  have hc := code_evaluate p s ni (world.1 ▸ codeNoInstall)
  exact ⟨hc.trans world.1,(WordOracleInvariant.evaluate_oracle_eq p s).symm.trans world.2⟩

private theorem world_entry {width : Nat} [NeZero width] {C F : Type}
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (oracle : HolOracle F)
    (s : WordSemStateFiniteExact width C F) (values : List (WordLocW width)) (frame : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (world : s.code = code ∧ s.ffi.oracle = oracle) :
    let entry := WordSemStateFiniteExact.callEnv values frame (pushEnv envs handler (decClock s))
    entry.code = code ∧ entry.ffi.oracle = oracle := by
  rcases handler with _ | ⟨_,_,_,_⟩ <;> exact world

private theorem world_pop {width : Nat} [NeZero width] {C F : Type}
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (oracle : HolOracle F)
    (s popped : WordSemStateFiniteExact width C F) (pop : popEnv s = some popped)
    (world : s.code = code ∧ s.ffi.oracle = oracle) :
    popped.code = code ∧ popped.ffi.oracle = oracle := by
  unfold popEnv at pop
  repeat' split at pop
  all_goals cases pop <;> exact world

/-- Global soundness of syntactic signed-cost certificates, over the actual
Word evaluator. The certificate for each found body is checked against the
summary for the requested destination, including indirect calls. The only
oracle assumption concerns which primitive FFI calls are terminal. -/
theorem sound {width : Nat} [NeZero width] {C F : Type}
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (oracle : HolOracle F)
    (codeNoInstall : WordProps.noInstallCode code)
    (codeCertificates : ∀ (dest : Option Nat) (xs : List (WordLocW width)) (sizes : Spt Nat)
      (values : List (WordLocW width)) (body : WordLangProgHOL (BitVec width)) (frame : Option Nat),
      wordSemFindCode dest xs code sizes = some (values,body,frame) →
      ∃ effects, Derives defs terminal body effects ∧ Subeffects effects (defs dest))
    (terminalCalls : ∀ (ffi : HolFfiState F) name, ffi.oracle = oracle → terminal name = true →
      ∀ config bytes, ∃ event, callFFIHOL ffi (.extCall name) config bytes = .final event)
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (effects : Effects) (certificate : Derives defs terminal p effects)
    (ni : noInstallSubprogsHOL p = true)
    (world : s.code = code ∧ s.ffi.oracle = oracle) : At effects p s := by
  cases certificate with
  | normal p erased => exact skip_at p s erased
  | tick => exact tick_at s
  | share op reg exp => exact share_at op reg exp s
  | raise reg => exact raise_at reg s
  | result reg regs => exact return_at reg regs s
  | breakTo label => exact break_at label s
  | continueTo label => exact continue_at label s
  | ffi name p1 l1 p2 l2 names =>
    exact ffi_at name p1 l1 p2 l2 names (terminal name) s
      (terminalCalls s.ffi name world.2)
  | @seq first second a b left right =>
    have parts : noInstallSubprogsHOL first = true ∧ noInstallSubprogsHOL second = true := by
      simpa only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] using ni
    apply seq_at a b first second s
    · exact sound defs terminal code oracle codeNoInstall codeCertificates terminalCalls
        first s a left parts.1 world
    · intro post run
      have mono := evaluate_clock first s none post run
      have postWorld := world_after code oracle codeNoInstall first s parts.1 world
      rw [run] at postWorld
      exact sound defs terminal code oracle codeNoInstall codeCertificates terminalCalls
        second post b right parts.2 postWorld
  | @branch cmp reg operand first second a b left right =>
    have parts : noInstallSubprogsHOL first = true ∧ noInstallSubprogsHOL second = true := by
      simpa only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] using ni
    exact branch_at a b cmp reg operand first second s
      (sound defs terminal code oracle codeNoInstall codeCertificates terminalCalls first s a left parts.1 world)
      (sound defs terminal code oracle codeNoInstall codeCertificates terminalCalls second s b right parts.2 world)
  | @loop names exits body a bodyRule cycle =>
    have bodyNi : noInstallSubprogsHOL body = true := by
      simpa only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp] using ni
    apply loop_at a names exits body s cycle
    · intro cut cutRun
      have cutClock := cutState_clock_termdep _ _ _ cutRun
      obtain ⟨locals,stateEq⟩ := cutStateConst _ _ _ cutRun
      have cutWorld : cut.code = code ∧ cut.ffi.oracle = oracle := by rw [stateEq]; exact world
      exact sound defs terminal code oracle codeNoInstall codeCertificates terminalCalls
        body cut a bodyRule bodyNi cutWorld
    · intro cut r post cutRun run cont positive
      have cutClock := cutState_clock_termdep _ _ _ cutRun
      have mono := evaluate_clock body cut r post run
      obtain ⟨locals,stateEq⟩ := cutStateConst _ _ _ cutRun
      have cutWorld : cut.code = code ∧ cut.ffi.oracle = oracle := by rw [stateEq]; exact world
      have postWorld := world_after code oracle codeNoInstall body cut bodyNi cutWorld
      rw [run] at postWorld
      exact sound defs terminal code oracle codeNoInstall codeCertificates terminalCalls
        (wordSemSTOP (.loop names body exits)) (decClock post) (loopEffects a)
        (by simpa only [wordSemSTOP] using Derives.loop names exits bodyRule cycle)
        (by simpa only [wordSemSTOP] using ni) postWorld
  | tail dest args =>
    intro ne nt
    have positive := call_positive none dest args none s ne nt
    apply tailCall_at (defs dest) dest args s ?_ ne nt
    intro xs values body frame hg hf
    have found : wordSemFindCode dest xs code s.stackSize = some (values,body,frame) := by
      simpa only [world.1] using hf
    obtain ⟨a,proof,le⟩ := codeCertificates dest xs s.stackSize values body frame found
    have bodyNi := WordProps.noInstallFindCode s.code dest xs s.stackSize values body frame
      ⟨world.1 ▸ codeNoInstall,hf⟩
    apply at_mono le
    exact sound defs terminal code oracle codeNoInstall codeCertificates terminalCalls
      body (WordSemStateFiniteExact.callEnv values frame (decClock s)) a proof bodyNi world
  | returning names live next l1 l2 dest args handler contEffects handlerEffects cont handlers =>
    intro ne nt
    have positive := call_positive (some (names,live,next,l1,l2)) dest args handler s ne nt
    apply returningCall_at (defs dest) contEffects handlerEffects names live next l1 l2 dest args handler s
      ?_ ?_ ?_ ne nt
    · intro xs values body frame envs hg hf hc
      have found : wordSemFindCode dest (wordSemAddRetLoc (some (names,live,next,l1,l2)) xs)
          code s.stackSize = some (values,body,frame) := by simpa only [world.1] using hf
      obtain ⟨a,proof,le⟩ := codeCertificates dest _ s.stackSize values body frame found
      have bodyNi := WordProps.noInstallFindCode s.code dest _ s.stackSize values body frame
        ⟨world.1 ▸ codeNoInstall,hf⟩
      have entryWorld := world_entry code oracle s values frame envs handler world
      apply at_mono le
      exact sound defs terminal code oracle codeNoInstall codeCertificates terminalCalls
        body (WordSemStateFiniteExact.callEnv values frame (pushEnv envs handler (decClock s)))
        a proof bodyNi entryWorld
    · intro xs values body frame envs address ys post popped hg hf hc run pop
      let entry := WordSemStateFiniteExact.callEnv values frame (pushEnv envs handler (decClock s))
      have mono := evaluate_clock body entry (some (.result address ys)) post run
      have entryWorld := world_entry code oracle s values frame envs handler world
      have bodyNi := WordProps.noInstallFindCode s.code dest _ s.stackSize values body frame
        ⟨world.1 ▸ codeNoInstall,hf⟩
      have postWorld := world_after code oracle codeNoInstall body entry bodyNi entryWorld
      rw [run] at postWorld
      have poppedWorld := world_pop code oracle post popped pop postWorld
      have popClock := popEnv_clock post popped pop
      exact sound defs terminal code oracle codeNoInstall codeCertificates terminalCalls
        next (setVars names ys popped) contEffects cont (noInstall_call_ret ni) poppedWorld
    · intro xs values body frame envs address value post name hbody h1 h2 hg hf hc run hh
      let entry := WordSemStateFiniteExact.callEnv values frame (pushEnv envs handler (decClock s))
      have mono := evaluate_clock body entry (some (.exception address value)) post run
      have entryWorld := world_entry code oracle s values frame envs handler world
      have bodyNi := WordProps.noInstallFindCode s.code dest _ s.stackSize values body frame
        ⟨world.1 ▸ codeNoInstall,hf⟩
      have postWorld := world_after code oracle codeNoInstall body entry bodyNi entryWorld
      rw [run] at postWorld
      have handlerNi : noInstallSubprogsHOL hbody = true := by
        subst handler
        exact noInstall_call_handler ni
      exact sound defs terminal code oracle codeNoInstall codeCertificates terminalCalls
        hbody (setVar name value post) handlerEffects (handlers name hbody h1 h2 hh) handlerNi postWorld
termination_by (s.clock,sizeOf p)
decreasing_by
  all_goals subst p
  all_goals simp_wf
  all_goals try dsimp only [entry] at *
  all_goals try dsimp only [WordSemStateFiniteExact.callEnv,decClock,setVars,setVar] at *
  all_goals try simp only [pushEnv_clock,wordSemSTOP] at *
  all_goals first
    | exact Prod.Lex.right _ (by simp +arith)
    | exact Prod.Lex.left _ _ (by omega)
    | apply LoopSemStateFiniteExact.lexLt <;> first | omega | simp +arith

#print axioms sound
end InitECandidate.Solver.Wave8Stage.WordCostCertificates
