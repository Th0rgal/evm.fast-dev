import InitECandidate.Proofs.BoundedPanToWord
import InitECandidate.Solver.CompilerClockBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.CrepToLoopStmtBound` — Wave 3 Atomic Worker `W3_1`

Quantitative clock bound for `CrepToLoop` statement compilation:
1. `crepProgCmpCount : CrepProgHOL width → Nat` counting `.cmp` comparisons across
   all expressions of a `CrepProgHOL width` program.
2. Structural equations `crepProgCmpCount_seq`, `crepProgCmpCount_if`,
   `crepProgCmpCount_dec`, and `crepProgCmpCount_assign`.
3. `crepToLoop_compile_assign_clock_bound`: quantitative clock-bounded simulation
   for `.assign n e` in `CrepToLoop.compileHOLExact`, combining
   `crepToLoop_comp_exp_preserves_eval_clock_bound` (`BoundedPanToWord.lean`) with
   `loop_evaluate_leaf_clock_eq` and `crep_evaluate_leaf_clock_eq`
   (`CompilerClockBound.lean`) to establish `ck ≤ crepProgCmpCount (.assign n e)`.
-/

namespace InitECandidate.Solver

open Classical
open InitE
open Flapjack
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Structural count of `.cmp` nodes across all expressions of a `CrepProgHOL width`
program. Each `.cmp` node in an expression compiles to a single `.ite` in `HolLoopProg`,
whose `cutRes` exit consumes at most 1 clock tick in `LoopSemStateFiniteExact.evaluate`. -/
def crepProgCmpCount {width : Nat} [NeZero width] : CrepProgHOL width → Nat
  | .skip => 0
  | .assign _ src => crepExpCmpCount src
  | .dec _ value body => crepExpCmpCount value + crepProgCmpCount body
  | .seq first second => crepProgCmpCount first + crepProgCmpCount second
  | .ite cond thenBranch elseBranch =>
      crepExpCmpCount cond + crepProgCmpCount thenBranch + crepProgCmpCount elseBranch
  | .while cond body => crepExpCmpCount cond + crepProgCmpCount body
  | .store dst src => crepExpCmpCount dst + crepExpCmpCount src
  | .storeByte dst src => crepExpCmpCount dst + crepExpCmpCount src
  | .store32 dst src => crepExpCmpCount dst + crepExpCmpCount src
  | .storeGlob _ src => crepExpCmpCount src
  | .shMem _ _ addr => crepExpCmpCount addr
  | .return es => crepExpsCmpCount es
  | .call (some (_, some (_, hprog))) _ args =>
      crepExpsCmpCount args + crepProgCmpCount hprog
  | .call _ _ args => crepExpsCmpCount args
  | .raise _ => 0
  | .break _ => 0
  | .continue _ => 0
  | .tick => 0
  | .primitive _ _ _ => 0
  | .extCall _ _ _ _ _ => 0

@[simp] theorem crepProgCmpCount_skip {width : Nat} [NeZero width] :
    crepProgCmpCount (.skip : CrepProgHOL width) = 0 := rfl

@[simp] theorem crepProgCmpCount_assign {width : Nat} [NeZero width]
    (name : Nat) (src : CrepExpHOL width) :
    crepProgCmpCount (.assign name src : CrepProgHOL width) = crepExpCmpCount src := rfl

@[simp] theorem crepProgCmpCount_dec {width : Nat} [NeZero width]
    (name : Nat) (value : CrepExpHOL width) (body : CrepProgHOL width) :
    crepProgCmpCount (.dec name value body : CrepProgHOL width) =
      crepExpCmpCount value + crepProgCmpCount body := rfl

@[simp] theorem crepProgCmpCount_seq {width : Nat} [NeZero width]
    (first second : CrepProgHOL width) :
    crepProgCmpCount (.seq first second : CrepProgHOL width) =
      crepProgCmpCount first + crepProgCmpCount second := rfl

@[simp] theorem crepProgCmpCount_if {width : Nat} [NeZero width]
    (cond : CrepExpHOL width) (thenBranch elseBranch : CrepProgHOL width) :
    crepProgCmpCount (.ite cond thenBranch elseBranch : CrepProgHOL width) =
      crepExpCmpCount cond + crepProgCmpCount thenBranch + crepProgCmpCount elseBranch := rfl

@[simp] theorem crepProgCmpCount_store {width : Nat} [NeZero width]
    (dst src : CrepExpHOL width) :
    crepProgCmpCount (.store dst src : CrepProgHOL width) =
      crepExpCmpCount dst + crepExpCmpCount src := rfl

@[simp] theorem crepProgCmpCount_storeByte {width : Nat} [NeZero width]
    (dst src : CrepExpHOL width) :
    crepProgCmpCount (.storeByte dst src : CrepProgHOL width) =
      crepExpCmpCount dst + crepExpCmpCount src := rfl

@[simp] theorem crepProgCmpCount_store32 {width : Nat} [NeZero width]
    (dst src : CrepExpHOL width) :
    crepProgCmpCount (.store32 dst src : CrepProgHOL width) =
      crepExpCmpCount dst + crepExpCmpCount src := rfl

@[simp] theorem crepProgCmpCount_storeGlob {width : Nat} [NeZero width]
    (dst : BitVec 5) (src : CrepExpHOL width) :
    crepProgCmpCount (.storeGlob dst src : CrepProgHOL width) =
      crepExpCmpCount src := rfl

@[simp] theorem crepProgCmpCount_return {width : Nat} [NeZero width]
    (es : List (CrepExpHOL width)) :
    crepProgCmpCount (.return es : CrepProgHOL width) = crepExpsCmpCount es := rfl

/-- Quantitative clock-bounded `CrepToLoop` simulation for `.assign n e`:
combining `crepToLoop_comp_exp_preserves_eval_clock_bound` (for the compiled
expression prefix `p`, which consumes `ck ≤ crepExpCmpCount e` ticks) with
`loop_evaluate_leaf_clock_eq` (showing the trailing `.assign mapped le` leaf
in `HolLoopProg` consumes `0` clock ticks) and `crep_evaluate_leaf_clock_eq`,
the compiled assignment executes at clock `t.clock + ck` with
`ck ≤ crepProgCmpCount (.assign n e)` and preserves all five `CrepToLoop`
state/memory/globals/code/locals invariants. -/
theorem crepToLoop_compile_assign_clock_bound {width : Nat} [NeZero width] {σ : Type}
    (n : Nat) (e : CrepExpHOL width) (v1 : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet)
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
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.assign n e))
          { t with clock := t.clock + ck } = (res1, t1) ∧
      s1.clock = v1.clock ∧
      t1.clock = t.clock ∧
      crepToLoopStateRelExact s1 t1 ∧
      crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
      crepToLoopCodeRelExact ctxt s1.code t1.code ∧
      res1 = resultToLoop res ∧
      localsResultRel ctxt l res s1 t1 := by
  have hCrepLeafClock : s1.clock = v1.clock := by
    have hleaf := crep_evaluate_leaf_clock_eq v1 (.assign n e) rfl
    rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, hEval] at hleaf
    exact hleaf
  have he := hEval
  rw [evalCrepSemHOLProgExact_assign] at he
  cases hev : crepExactEvalExp v1 (fun a => Classical.propDecidable (v1.memaddrs a)) e with
  | none =>
      simp only [hev, Prod.mk.injEq] at he
      exact absurd he.1.symm hNotError
  | some value =>
      cases hlocal : v1.locals.lookup n with
      | none =>
          simp only [hev, hlocal, Prod.mk.injEq] at he
          exact absurd he.1.symm hNotError
      | some old =>
          simp only [hev, hlocal, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hev' : evalCrepSemHOLExp v1 e = some value := by
            simpa [crepExactEvalExp_eq_eval] using hev
          obtain ⟨mapped, hmap, hlive, _⟩ := hLocals.2.2.2 n old hlocal
          rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with
            ⟨p, le, ntmp, nl⟩
          obtain ⟨ck, st, hck, hp, heval, hst, hm', hg', hc', hl'⟩ :=
            crepToLoop_comp_exp_preserves_eval_clock_bound v1 e value t ctxt (ctxt.vmax + 1) l
              p le ntmp nl ⟨hev', hState, hMem, hGlobals, hCode, hLocals, hC, Nat.lt_succ_self _⟩
          obtain ⟨hok, _, hnl⟩ := compile_exp_out_rel ctxt (ctxt.vmax + 1) l e
            p le ntmp nl hC
          have hliveIncl : ∀ k, sptMem k l → sptMem k nl := by
            intro k hk
            rw [hnl]
            exact cut_sets_union_domain_subset _ l hok k hk
          have hcompile : compileHOLExact ctxt l (.assign n e) =
              loopNestedSeqHOL (p ++ [.assign mapped le]) := by
            simp [compileHOLExact, hmap, hC]
          have hLoopLeafClock :
              (HolLoopState.evaluate (.assign mapped le : HolLoopProg width) st).2.clock =
                st.clock :=
            loop_evaluate_leaf_clock_eq st (.assign mapped le) rfl
          have hAssignStep :
              LoopSemStateFiniteExact.evaluate (.assign mapped le : HolLoopProg width) st =
                (none, LoopSemStateFiniteExact.setVar mapped (wlabWlocExact value) st) := by
            rw [LoopSemStateFiniteExact.evaluate.eq_3]
            simp [LoopSemStateFiniteExact.setVar, heval]
          have hTargetClock :
              (LoopSemStateFiniteExact.setVar mapped (wlabWlocExact value) st).clock = t.clock := by
            have h1 : (LoopSemStateFiniteExact.setVar mapped (wlabWlocExact value) st).clock = st.clock := by
              simpa [HolLoopState.evaluate, hAssignStep] using hLoopLeafClock
            rw [h1, ← hst.2.2.1, hState.2.2.1]
          have hrun : LoopSemStateFiniteExact.evaluate
              (loopNestedSeqHOL (p ++ [.assign mapped le]))
              { t with clock := t.clock + ck } =
                (none, LoopSemStateFiniteExact.setVar mapped (wlabWlocExact value) st) := by
            rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none _ _ _ _ hp]
            simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq,
              hAssignStep, LoopSemStateFiniteExact.evaluate]
          have hlocals : crepToLoopLocalsRelExact ctxt l
              (CrepSemHOLState.setVar n value v1).locals
              (LoopSemStateFiniteExact.setVar mapped (wlabWlocExact value) st).locals := by
            simp only [LoopSemStateFiniteExact.setVar]
            refine ⟨hl'.1, hl'.2.1, ?_, ?_⟩
            · intro k hk
              exact (sptMem_sptInsert k mapped (wlabWlocExact value) st.locals).mpr
                (Or.inr (hl'.2.2.1 k (hliveIncl k hk)))
            · intro key val hval
              have hlookup : (CrepSemHOLState.setVar n value v1).locals.lookup key =
                  (FUPDATE_HOL v1.locals.lookup (n, value)) key := by
                simp [CrepSemHOLState.setVar, HolFiniteMapExact.lookup_updateEq]
              rw [hlookup] at hval
              by_cases hkey : key = n
              · subst key
                simp [FUPDATE_HOL] at hval
                have hval' : val = value := hval.symm
                subst val
                exact ⟨mapped, hmap, hlive, by
                  simpa [wlabWlocExact, wlabWlocHOL] using
                    sptLookup_sptInsert_same mapped (wlabWlocHOL value) st.locals⟩
              · have hbase : v1.locals.lookup key = some val := by
                  simpa [FUPDATE_HOL, hkey] using hval
                obtain ⟨mappedKey, hkeyMap, hkeyLive, _⟩ :=
                  hLocals.2.2.2 key val hbase
                obtain ⟨mappedKey', hkeyMap', _, hkeyValue⟩ :=
                  hl'.2.2.2 key val hbase
                have hkeysEq : mappedKey' = mappedKey :=
                  Option.some.inj (hkeyMap'.symm.trans hkeyMap)
                subst mappedKey'
                have hneq : mappedKey ≠ mapped := by
                  intro heq
                  exact hkey (hLocals.1 key n mappedKey mapped hkeyMap hmap heq)
                refine ⟨mappedKey, hkeyMap, hkeyLive, ?_⟩
                rw [sptLookup_sptInsert_ne mapped mappedKey _ st.locals hneq]
                exact hkeyValue
          refine ⟨ck, none, LoopSemStateFiniteExact.setVar mapped (wlabWlocExact value) st,
            by simpa [crepProgCmpCount] using hck,
            by rw [hcompile]; exact hrun,
            hCrepLeafClock, hTargetClock,
            by simpa only [crepToLoopStateRelExact, CrepSemHOLState.setVar,
                LoopSemStateFiniteExact.setVar] using hst,
            by simpa only [CrepSemHOLState.setVar, LoopSemStateFiniteExact.setVar] using hm',
            by simpa only [CrepSemHOLState.setVar, LoopSemStateFiniteExact.setVar] using hg',
            by simpa only [CrepSemHOLState.setVar, LoopSemStateFiniteExact.setVar] using hc',
            rfl, hlocals⟩

#print axioms crepProgCmpCount_seq
#print axioms crepProgCmpCount_if
#print axioms crepProgCmpCount_dec
#print axioms crepToLoop_compile_assign_clock_bound

end InitECandidate.Solver
