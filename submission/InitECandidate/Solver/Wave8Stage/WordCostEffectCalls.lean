import InitECandidate.Solver.Wave8Stage.WordCostEffectRules
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Call

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostEffects
open Flapjack WordSemStateFiniteExact WordToStackSourceCost

/-- Call entry pays one tick. Only a return reaches the continuation; only an
exception reaches the handler. A final FFI cannot spend either later credit. -/
def returningEffects (callee continuation : Effects) (handler : Option Effects) : Effects :=
  fun exit => join
    (if exit = .final ∨ exit = .invalid then add (some (-1)) (callee exit) else none)
    (join (add (add (some (-1)) (callee .returned)) (continuation exit))
      (match (generalizing := false) handler with
       | none => if exit = .raised then add (some (-1)) (callee .raised) else none
       | some effects => add (add (some (-1)) (callee .raised)) (effects exit)))

private theorem paid {bound : Budget} {cost : Int} (h : Covers bound cost) :
    Covers (add (some (-1)) bound) (cost-1) := by
  have credit : Covers (some (-1)) (-1) := by simp
  have result := covers_add _ _ _ _ credit h
  exact covers_mono result (by omega)

/-- Returning-call rule with the actual argument lookup, saved environment,
callee result, popped frame, and handler state. The recursive premises retain
those equations so code/FFI invariants can be carried by a global induction. -/
theorem returningCall_at {width : Nat} [NeZero width] {C F : Type}
    (callee continuation : Effects) (handlerEffects : Effects)
    (names : List Nat) (live : WordLangCutsetsHOL)
    (next : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F)
    (calleeRule : ∀ xs values body frame envs,
      getVars args s = some xs →
      wordSemFindCode dest (wordSemAddRetLoc (some (names,live,next,l1,l2)) xs)
        s.code s.stackSize = some (values,body,frame) →
      wordSemCutEnvs live s.locals = some envs →
      At callee body (WordSemStateFiniteExact.callEnv values frame
        (pushEnv envs handler (decClock s))))
    (returnRule : ∀ xs values body frame envs address ys post popped,
      getVars args s = some xs →
      wordSemFindCode dest (wordSemAddRetLoc (some (names,live,next,l1,l2)) xs)
        s.code s.stackSize = some (values,body,frame) →
      wordSemCutEnvs live s.locals = some envs →
      evaluate body (WordSemStateFiniteExact.callEnv values frame
        (pushEnv envs handler (decClock s))) = (some (.result address ys),post) →
      popEnv post = some popped → At continuation next (setVars names ys popped))
    (handlerRule : ∀ xs values body frame envs address value post name hbody h1 h2,
      getVars args s = some xs →
      wordSemFindCode dest (wordSemAddRetLoc (some (names,live,next,l1,l2)) xs)
        s.code s.stackSize = some (values,body,frame) →
      wordSemCutEnvs live s.locals = some envs →
      evaluate body (WordSemStateFiniteExact.callEnv values frame
        (pushEnv envs handler (decClock s))) = (some (.exception address value),post) →
      handler = some (name,hbody,h1,h2) → At handlerEffects hbody (setVar name value post)) :
    At (returningEffects callee continuation (handler.map (fun _ => handlerEffects)))
      (.call (some (names,live,next,l1,l2)) dest args handler) s := by
  intro ne nt
  rw [Compiler.Backend.WordToWord.evaluate_call_eq] at ne nt
  cases hg : getVars args s with
  | none => simp only [hg] at ne; exact (ne rfl).elim
  | some xs =>
    simp only [hg] at ne nt
    by_cases bad : wordSemBadDestArgs dest args = true
    · simp only [bad,if_true] at ne; exact (ne rfl).elim
    simp only [bad,Bool.false_eq_true,if_false] at ne nt
    cases hf : wordSemFindCode dest (wordSemAddRetLoc (some (names,live,next,l1,l2)) xs)
        s.code s.stackSize with
    | none => simp only [hf] at ne; exact (ne rfl).elim
    | some found =>
      rcases found with ⟨values,body,frame⟩
      simp only [hf] at ne nt
      by_cases invalid : sptDomainEmpty live.1 ∨ ¬ names.Nodup
      · simp only [invalid,if_true] at ne; exact (ne rfl).elim
      simp only [invalid,if_false] at ne nt
      cases hc : wordSemCutEnvs live s.locals with
      | none => simp only [hc] at ne; exact (ne rfl).elim
      | some envs =>
        simp only [hc] at ne nt
        by_cases zero : s.clock = 0
        · simp only [zero,dite_true] at nt; exact (nt rfl).elim
        simp only [zero,dite_false] at ne nt
        let entry := WordSemStateFiniteExact.callEnv values frame
          (pushEnv envs handler (decClock s))
        have entryClock : entry.clock = s.clock-1 := by
          simp [entry,WordSemStateFiniteExact.callEnv,decClock,pushEnv_clock]
        rcases run : evaluate body entry with ⟨r,t⟩
        rw [run] at ne nt
        have bodyNe : r ≠ some .error := by intro bad; subst r; exact ne rfl
        have bodyNt : r ≠ some .timeOut := by intro bad; subst r; exact nt rfl
        have bodyFits := calleeRule xs values body frame envs hg hf hc
          (by rw [run]; exact bodyNe) (by rw [run]; exact bodyNt)
        have expandedRun := run
        dsimp only [entry] at expandedRun
        simp only [Fits,netCost,expandedRun] at bodyFits
        change Covers (callee (classify r))
          ((sourceCost body entry : Int) + t.clock - entry.clock) at bodyFits
        rw [entryClock] at bodyFits
        have bodyPaid := paid bodyFits
        have whole : evaluate (.call (some (names,live,next,l1,l2)) dest args handler) s =
            (match (generalizing := false) r with
          | some (.result address ys) =>
            if address ≠ .loc l1 l2 ∨ ys.length ≠ names.length then (some .error,t)
            else match popEnv t with
            | none => (some .error,t)
            | some popped => if sptDomainEqUnion popped.locals envs.1 envs.2 then
                evaluate next (setVars names ys popped) else (some .error,popped)
          | some (.exception address value) => match (generalizing := false) handler with
            | none => (some (.exception address value),t)
            | some (name,hbody,h1,h2) => if address ≠ .loc h1 h2 then (some .error,t)
                else if sptDomainEqUnion t.locals envs.1 envs.2 then
                  evaluate hbody (setVar name value t) else (some .error,t)
          | none | some (.break _) | some (.continue _) => (some .error,t)
          | _ => (r,t)) := by
          rw [Compiler.Backend.WordToWord.evaluate_call_eq]
          simp only [hg,bad,Bool.false_eq_true,if_false,hf,invalid,hc,zero,expandedRun]
          cases r with
          | none => rfl
          | some r => cases r <;> rfl
        have cost : sourceCost (.call (some (names,live,next,l1,l2)) dest args handler) s =
          sourceCost body entry + max
            (match (generalizing := false) r with
             | some (.result _ ys) => match popEnv t with
               | none => 0 | some popped => sourceCost next (setVars names ys popped)
             | _ => 0)
            (match (generalizing := false) handler,r with
             | some (name,hbody,_,_),some (.exception _ value) => sourceCost hbody (setVar name value t)
             | _,_ => 0) := by
          rw [sourceCost]
          have hr1 := congrArg Prod.fst expandedRun
          have hr2 := congrArg Prod.snd expandedRun
          simp only [hg,hf,hc,zero,dite_false,hr1,hr2]
          cases r with
          | none => rfl
          | some r =>
            cases r <;> try rfl
            dsimp only
            split
            · rename_i missing
              have missing' : popEnv t = none := by simpa only [hr2] using missing
              rw [missing']
              rfl
            · rename_i popped found
              have found' : popEnv t = some popped := by simpa only [hr2] using found
              rw [found']
              rfl
        cases r with
        | none => exact (ne rfl).elim
        | some r =>
          cases r with
          | result address ys =>
            by_cases badReturn : address ≠ .loc l1 l2 ∨ ys.length ≠ names.length
            · simp only [badReturn,if_true] at ne; exact (ne rfl).elim
            simp only [badReturn,if_false] at ne nt
            cases hp : popEnv t with
            | none => simp only [hp] at ne; exact (ne rfl).elim
            | some popped =>
              try simp only [hp] at ne nt
              by_cases domain : sptDomainEqUnion popped.locals envs.1 envs.2
              · try simp only [domain,if_true] at ne nt
                have contFits := returnRule xs values body frame envs address ys t popped
                  hg hf hc expandedRun hp ne nt
                simp only [Fits,netCost] at contFits
                have combined := covers_add _ _ _ _ bodyPaid contFits
                have popClock := popEnv_clock t popped hp
                have cost' : sourceCost (.call (some (names,live,next,l1,l2)) dest args handler) s =
                    sourceCost body entry + sourceCost next (setVars names ys popped) := by
                  rw [cost]
                  cases handler <;> simp only [hp,Nat.max_zero]
                dsimp only at whole
                simp only [Fits,netCost,whole,badReturn,if_false,hp,domain,if_true,cost',
                  Nat.max_zero,Int.natCast_add]
                unfold returningEffects
                apply covers_join_right
                apply covers_join_left
                apply covers_mono combined
                simp only [classify,WordSemStateFiniteExact.setVars] at combined bodyPaid contFits ⊢
                dsimp only [entry] at *
                simp only [WordSemStateFiniteExact.callEnv,pushEnv_clock,decClock] at *
                omega
              · simp only [domain,if_false] at ne; exact (ne rfl).elim
          | exception address value =>
            cases hh : handler with
            | none =>
              try rw [hh] at whole cost
              dsimp only at whole cost
              simp only [Fits,netCost,whole,cost,Nat.max_self,Nat.add_zero,
                returningEffects,hh,Option.map_none,classify,if_false,if_true]
              apply covers_join_right
              apply covers_join_right
              apply covers_mono bodyPaid
              simp only [classify] at bodyPaid
              omega
            | some h =>
              rcases h with ⟨name,hbody,h1,h2⟩
              try rw [hh] at whole cost
              dsimp only at whole cost
              try simp only [hh] at ne nt
              try dsimp only at ne nt
              by_cases wrong : address ≠ .loc h1 h2
              · try simp only [wrong,if_true] at ne
                exact (ne (by simp [hh,wrong])).elim
              simp only [wrong,if_false] at ne nt
              by_cases domain : sptDomainEqUnion t.locals envs.1 envs.2
              · try simp only [domain,if_true] at ne nt
                have handlerFits := handlerRule xs values body frame envs address value t
                  name hbody h1 h2 hg hf hc expandedRun hh ne nt
                simp only [Fits,netCost] at handlerFits
                have combined := covers_add _ _ _ _ bodyPaid handlerFits
                simp only [Fits,netCost,whole,hh,wrong,if_false,domain,if_true,cost,
                  Nat.zero_max,Int.natCast_add,returningEffects,Option.map_some]
                apply covers_join_right
                apply covers_join_right
                apply covers_mono combined
                simp only [classify,WordSemStateFiniteExact.setVar] at bodyPaid handlerFits ⊢
                omega
              · simp only [domain,if_false] at ne; exact (ne rfl).elim
          | finalFfi event | notEnoughSpace =>
            have cost' : sourceCost (.call (some (names,live,next,l1,l2)) dest args handler) s =
                sourceCost body entry := by
              rw [cost]
              cases handler <;> rfl
            dsimp only at whole
            simp only [Fits,netCost,whole,cost',Nat.max_self,Nat.add_zero,returningEffects,classify,or_true,true_or,if_true]
            apply covers_join_left
            apply covers_mono bodyPaid
            omega
          | error => exact (bodyNe rfl).elim
          | timeOut => exact (bodyNt rfl).elim
          | «break» label | «continue» label => exact (ne rfl).elim

#print axioms returningCall_at
end InitECandidate.Solver.Wave8Stage.WordCostEffects
