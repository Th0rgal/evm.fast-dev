import InitECandidate.Solver.Wave8Stage.WordToStackSourceCost
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8Stage.WordToStackCostBound
open Classical Flapjack WordSemStateFiniteExact WordToStackSourceCost

/-- Extra-tick potential in a fragment between source clock decrements. -/
def programCost {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Nat
  | .raise _ | .shareInst .. => 1
  | .seq first second | .ite _ _ _ first second => programCost first + programCost second
  | .loop _ body _ => programCost body
  | .call ret _ _ handler =>
      (match ret with | none => 0 | some (_,_,body,_,_) => programCost body) +
      (match handler with | none => 0 | some (_,body,_,_) => programCost body)
  | _ => 0
termination_by p => sizeOf p

@[simp] theorem programCost_call {width : Nat} [NeZero width]
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    programCost (.call ret dest args handler) =
      (match ret with | none => 0 | some (_,_,body,_,_) => programCost body) +
      (match handler with | none => 0 | some (_,body,_,_) => programCost body) := by
  cases ret with
  | none =>
    cases handler with
    | none => simp [programCost]
    | some h => rcases h with ⟨n,body,l1,l2⟩; simp [programCost]
  | some r =>
    rcases r with ⟨names,live,body,l1,l2⟩
    cases handler with
    | none => simp [programCost]
    | some h => rcases h with ⟨n,hbody,h1,h2⟩; simp [programCost]

def codeCostBound {width : Nat} [NeZero width]
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (bound : Nat) : Prop :=
  ∀ name arity body, sptLookup name code = some (arity,body) → programCost body ≤ bound

private theorem callee_bound {width : Nat} [NeZero width]
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (bound : Nat)
    (hc : codeCostBound code bound) (dest : Option Nat) (args : List (WordLocW width))
    (sizes : Spt Nat) (values : List (WordLocW width))
    (body : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (found : wordSemFindCode dest args code sizes = some (values,body,ss)) :
    programCost body ≤ bound := by
  obtain ⟨name,arity,hl⟩ := WordProps.findCode_lookup code dest args sizes values body ss found
  exact hc name arity body hl

/-- All additional Stack ticks are paid by the initial fragment potential or
by a source call/loop tick. This retains the actual post-clock in the bound. -/
theorem sourceCost_bound {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (bound : Nat) (hp : programCost p ≤ bound) (hc : codeCostBound s.code bound)
    (hni : noInstallSubprogsHOL p = true) (hcode : WordProps.noInstallCode s.code)
    (hne : (evaluate p s).1 ≠ some .error) :
    sourceCost p s + bound * (evaluate p s).2.clock ≤ bound * s.clock + programCost p := by
  have mono := Nat.mul_le_mul_left bound (evaluate_clock_proj p s).1
  revert hp hni hne
  cases heq : p <;> intro hp hni hne
  case seq first second =>
    simp only [programCost] at hp
    have parts := hp
    have ni : noInstallSubprogsHOL first = true ∧ noInstallSubprogsHOL second = true := by
      simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] using hni
    rw [sourceCost]
    split
    rename_i r t hrun
    dsimp only
    rw [evaluate, fix_clock_evaluate]
    simp only [hrun]
    rw [evaluate, fix_clock_evaluate, hrun] at hne
    have hmono := evaluate_clock first s r t hrun
    have hct := code_evaluate first s ni.1 hcode
    rw [hrun] at hct
    have hn : r ≠ some .error := by
      intro bad
      subst r
      exact hne rfl
    have hi := sourceCost_bound first s bound (by omega) hc ni.1 hcode (by rw [hrun]; exact hn)
    rw [hrun] at hi
    cases r with
    | some r => simp only [programCost]; dsimp only at hi ⊢; omega
    | none =>
      have hn2 : (evaluate second t).1 ≠ some .error := hne
      have hj := sourceCost_bound second t bound (by omega) (hct ▸ hc) ni.2 (hct ▸ hcode) hn2
      simp only [programCost]
      dsimp only at hi ⊢
      omega
  case ite cmp reg operand first second =>
    have ni : noInstallSubprogsHOL first = true ∧ noInstallSubprogsHOL second = true := by
      simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] using hni
    simp only [programCost] at hp ⊢
    rw [sourceCost, evaluate]
    rw [evaluate] at hne
    cases hl : getVar reg s <;> cases hr : getVarImm operand s <;> simp only [hl,hr] at hne ⊢
    all_goals try exact (hne rfl).elim
    rename_i left right
    cases hcmp : wordSemWordCmp cmp left right with
    | none => simp only [hcmp] at hne; exact (hne rfl).elim
    | some value =>
      cases value with
      | false =>
        simp only [hcmp] at hne ⊢
        have hi := sourceCost_bound second s bound (by omega) hc ni.2 hcode hne
        omega
      | true =>
        simp only [hcmp] at hne ⊢
        have hi := sourceCost_bound first s bound (by omega) hc ni.1 hcode hne
        omega
  case loop names body exitNames =>
    have hbody : programCost body ≤ bound := by simpa only [programCost] using hp
    have hniBody : noInstallSubprogsHOL body = true := by
      simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using hni
    rw [sourceCost]
    split
    · rename_i hcut
      rw [evaluate, hcut] at hne
      exact (hne rfl).elim
    · rename_i cutSource hcut
      have hcs := cutState_clock_termdep _ _ _ hcut
      have cutClock := congrArg (bound * ·) hcs.1
      obtain ⟨locals, hstate⟩ := cutStateConst _ _ _ hcut
      have cutCode : cutSource.code = s.code := by rw [hstate]
      split
      rename_i r t hrun
      dsimp only
      rw [evaluate, hcut]
      dsimp only
      rw [fix_clock_evaluate]
      simp only [hrun]
      rw [evaluate, hcut] at hne
      dsimp only at hne
      rw [fix_clock_evaluate, hrun] at hne
      have hn : r ≠ some .error := by
        intro bad
        subst r
        exact hne rfl
      have hi := sourceCost_bound body cutSource bound hbody (cutCode ▸ hc)
        hniBody (cutCode ▸ hcode) (by rw [hrun]; exact hn)
      rw [hrun] at hi
      have codePost := code_evaluate body cutSource hniBody (cutCode ▸ hcode)
      rw [hrun] at codePost
      have postMono := evaluate_clock body cutSource r t hrun
      have pay : bound * t.clock = bound * (t.clock - 1) + bound ∨ t.clock = 0 := by
        by_cases hz : t.clock = 0
        · exact .inr hz
        · left
          calc
            bound * t.clock = bound * (t.clock - 1 + 1) := congrArg (bound * ·) (by omega)
            _ = _ := by simp [Nat.mul_add]
      by_cases cont : wordSemContLoop r = true
      · simp only [cont, if_true]
        by_cases hz : t.clock = 0
        · simp only [hz, ne_eq, not_true_eq_false, and_false, if_false, dite_true, dite_false, flushState]
          simp only [programCost]
          dsimp only at hi ⊢
          omega
        · simp only [hz, ne_eq, not_false_eq_true, and_self, if_true, dite_false, dite_true]
          have hnTail : (evaluate (wordSemSTOP (.loop names body exitNames)) (decClock t)).1 ≠ some .error := by
            simpa only [cont, if_true, hz, dite_false] using hne
          have hj := sourceCost_bound (wordSemSTOP (.loop names body exitNames)) (decClock t) bound
            (by simpa only [wordSemSTOP, programCost] using hbody)
            (show codeCostBound (decClock t).code bound from codePost ▸ cutCode ▸ hc)
            (by simpa only [wordSemSTOP] using hni)
            (show WordProps.noInstallCode (decClock t).code from codePost ▸ cutCode ▸ hcode) hnTail
          simp only [wordSemSTOP, programCost] at hj ⊢
          dsimp only [decClock] at hi hj ⊢
          rcases pay with pay | zero
          · omega
          · exact (hz zero).elim
      · simp only [cont, false_and, if_false, dite_false, Bool.false_eq_true] at hne ⊢
        split
        · split
          · rename_i hcutOut
            simp only at hne
            rw [hcutOut] at hne
            exact (hne rfl).elim
          · rename_i out hcutOut
            have ho := cutState_clock_termdep _ _ _ hcutOut
            simp only [programCost]
            dsimp only at hi ⊢
            have heqClock := congrArg (bound * ·) ho.1
            omega
        · simp only [programCost]
          dsimp only at hi ⊢
          have heqClock := congrArg (bound * ·) hcs.1
          omega
  case call ret dest args handler =>
    rw [evaluate] at hne ⊢
    cases hg : getVars args s with
    | none => simp only [hg] at hne; exact (hne rfl).elim
    | some xs =>
      simp only [hg] at hne ⊢
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true] at hne; exact (hne rfl).elim
      simp only [hbad, Bool.false_eq_true, if_false] at hne ⊢
      cases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
      | none => simp only [hf] at hne; exact (hne rfl).elim
      | some value =>
        rcases value with ⟨values,body,ss⟩
        simp only [hf] at hne ⊢
        have bodyCost := callee_bound s.code bound hc dest _ s.stackSize values body ss hf
        have bodyNi := WordProps.noInstallFindCode s.code dest _ _ values body ss ⟨hcode,hf⟩
        cases ret with
        | none =>
          cases handler with
          | some _ => exact (hne rfl).elim
          | none =>
            simp only at hne ⊢
            by_cases hz : s.clock = 0
            · simp only [hz, dite_true] at hne ⊢
              rw [sourceCost]
              simp only [hg,hf,hz,dite_true, Nat.zero_add, programCost, flushState]
              simp
            · simp only [hz,dite_false] at hne ⊢
              rcases hrun : evaluate body (WordSemStateFiniteExact.callEnv values ss (decClock s)) with ⟨r,t⟩
              simp only [hrun] at hne ⊢
              have hn : r ≠ some .error := by
                intro bad
                subst r
                exact hne rfl
              have hi := sourceCost_bound body (WordSemStateFiniteExact.callEnv values ss (decClock s)) bound bodyCost hc
                bodyNi hcode (by rw [hrun]; exact hn)
              rw [hrun] at hi
              have pay : bound * s.clock = bound * (s.clock - 1) + bound := by
                calc
                  bound * s.clock = bound * (s.clock - 1 + 1) := congrArg (bound * ·) (by omega)
                  _ = _ := by simp [Nat.mul_add]
              rw [sourceCost]
              simp only [hg,hf,hz,dite_false,programCost]
              dsimp only [WordSemStateFiniteExact.callEnv] at hi
              change sourceCost body (WordSemStateFiniteExact.callEnv values ss (decClock s)) + bound * t.clock ≤ bound * (s.clock - 1) + programCost body at hi
              split <;> dsimp only <;> omega
        | some ret =>
          rcases ret with ⟨names,live,continuation,l1,l2⟩
          simp only at hne ⊢
          by_cases invalid : sptDomainEmpty live.1 ∨ ¬ names.Nodup
          · simp only [invalid,if_true] at hne; exact (hne rfl).elim
          simp only [invalid,if_false] at hne ⊢
          cases hcut : wordSemCutEnvs live s.locals with
          | none => simp only [hcut] at hne; exact (hne rfl).elim
          | some envs =>
            simp only [hcut] at hne ⊢
            by_cases hz : s.clock = 0
            · simp only [hz,dite_true] at hne ⊢
              rw [sourceCost]
              simp only [hg,hf,hz,dite_true, Nat.zero_add, flushState]
              omega
            · simp only [hz,dite_false] at hne ⊢
              let entry := WordSemStateFiniteExact.callEnv values ss (pushEnv envs handler (decClock s))
              have entryCode : entry.code = s.code := code_pushEnv envs handler _
              have entryClock : entry.clock = s.clock - 1 := by simp [entry,WordSemStateFiniteExact.callEnv,decClock,pushEnv_clock]
              rcases hrun : evaluate body entry with ⟨r,t⟩
              have hm := evaluate_clock body entry r t hrun
              rw [show WordSemStateFiniteExact.callEnv values ss (pushEnv envs handler (decClock s)) = entry from rfl] at hne ⊢
              have hfix : fixClock entry (r,t) = (r,t) := by rw [← hrun, fix_clock_evaluate]
              rw [hfix]
              rw [fix_clock_evaluate, hrun] at hne
              have hn : r ≠ some .error := by intro bad; subst r; exact hne rfl
              have hi := sourceCost_bound body entry bound bodyCost (entryCode ▸ hc) bodyNi
                (entryCode ▸ hcode) (by rw [hrun]; exact hn)
              rw [hrun] at hi
              have ct := code_evaluate body entry bodyNi (entryCode ▸ hcode)
              rw [hrun] at ct
              have ct' : t.code = s.code := ct.trans entryCode
              have pay : bound * s.clock = bound * (s.clock - 1) + bound := by
                calc
                  bound * s.clock = bound * (s.clock - 1 + 1) := congrArg (bound * ·) (by omega)
                  _ = _ := by simp [Nat.mul_add]
              rw [entryClock] at hi
              rw [sourceCost]
              simp only [hg,hf,hz,dite_false,hcut]
              have hrunExpanded := hrun
              dsimp only [entry] at hrunExpanded
              have hr1 := congrArg Prod.fst hrunExpanded
              have hr2 := congrArg Prod.snd hrunExpanded
              simp only [hr1,hr2]
              cases r with
              | none => exact (hne rfl).elim
              | some r =>
                cases r with
                | result address valuesOut =>
                  by_cases invalidReturn : address ≠ .loc l1 l2 ∨ valuesOut.length ≠ names.length
                  · simp only [invalidReturn,if_true] at hne; exact (hne rfl).elim
                  simp only [invalidReturn,if_false] at hne ⊢
                  generalize hpop : WordSemStateFiniteExact.popEnv t = poppedOption at hne
                  cases poppedOption with
                  | none => exact (hne rfl).elim
                  | some popped =>
                    simp only [Nat.max_zero]
                    split
                    · rename_i missing
                      have missing' : popEnv t = none := by simpa only [hr2] using missing
                      rw [hpop] at missing'
                      cases missing'
                    · rename_i poppedAgain foundPop
                      have found' : popEnv t = some poppedAgain := by simpa only [hr2] using foundPop
                      have same := Option.some.inj (found'.symm.trans hpop)
                      subst poppedAgain
                      by_cases domain : sptDomainEqUnion popped.locals envs.1 envs.2
                      · try simp only [domain,if_true] at hne ⊢
                        have pc := popEnv_clock t popped hpop
                        have pcode : popped.code = s.code :=
                          ((popEnvConst _ _ hpop).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).trans ct'
                        have contCost : programCost continuation ≤ bound := by
                          simp only [programCost_call] at hp
                          omega
                        have hj := sourceCost_bound continuation (setVars names valuesOut popped) bound
                          contCost (show codeCostBound (setVars names valuesOut popped).code bound from pcode ▸ hc)
                          (noInstall_call_ret hni)
                          (show WordProps.noInstallCode (setVars names valuesOut popped).code from pcode ▸ hcode) hne
                        change _ ≤ bound * popped.clock + programCost continuation at hj
                        simp only [programCost_call]
                        dsimp only [entry] at hi
                        have pcMul := congrArg (bound * ·) pc
                        omega
                      · try simp only [domain,if_false] at hne
                        exact (hne rfl).elim
                | exception address valueOut =>
                  cases handler with
                  | none => simp only [programCost]; dsimp only [entry] at hi; omega
                  | some handler =>
                    rcases handler with ⟨name,hbody,h1,h2⟩
                    try simp only at hne ⊢
                    by_cases wrong : address ≠ .loc h1 h2
                    · rw [if_pos wrong] at hne
                      exact (hne rfl).elim
                    try simp only [wrong,if_false] at hne ⊢
                    split at hne
                    · rename_i domain
                      rw [if_pos domain]
                      have handlerCost : programCost hbody ≤ bound := by
                        simp only [programCost_call] at hp
                        omega
                      have hj := sourceCost_bound hbody (setVar name valueOut t) bound handlerCost
                        (show codeCostBound (setVar name valueOut t).code bound from ct' ▸ hc)
                        (noInstall_call_handler hni)
                        (show WordProps.noInstallCode (setVar name valueOut t).code from ct' ▸ hcode) hne
                      change _ ≤ bound * t.clock + programCost hbody at hj
                      simp only [programCost]
                      dsimp only [entry] at hi
                      omega
                    · exact (hne rfl).elim
                | «break» n | «continue» n | error => exact (hne rfl).elim
                | _ => simp only [programCost]; dsimp only [entry] at hi; omega
  all_goals
    have he : sourceCost p s = programCost p := by
      subst p; simp only [sourceCost, programCost]
    rw [← heq] at *
    rw [he]
    omega
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals subst p
  all_goals simp_wf
  all_goals try dsimp only [entry] at *
  all_goals try dsimp only [WordSemStateFiniteExact.callEnv,decClock,setVars,setVar] at *
  all_goals try simp only [pushEnv_clock, wordSemSTOP] at *
  all_goals first
    | exact Prod.Lex.right _ (by simp +arith)
    | exact Prod.Lex.left _ _ (by omega)
    | exact LoopSemStateFiniteExact.lexLt (by omega) (by simp +arith)

end InitECandidate.Solver.Wave8Stage.WordToStackCostBound
