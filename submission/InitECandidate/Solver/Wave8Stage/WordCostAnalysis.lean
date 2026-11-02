import InitECandidate.Solver.Wave8Stage.WordCostCertificates

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostAnalysis
open Flapjack WordCostEffects WordCostCertificates WordCostControl

def one : Budget → Bool
  | none => true
  | some value => decide (value ≤ 1)

theorem one_sound (bound : Budget) (h : one bound = true) : AtMost bound 1 := by
  cases bound with
  | none => intro cost covered; exact (covers_none cost covered).elim
  | some value =>
    have le : value ≤ 1 := by simpa only [one,decide_eq_true_eq] using h
    intro cost covered
    have := (covers_some _ _).mp covered
    omega

/-- Executable certificate synthesis. Fuel exhaustion and unsupported
instructions return none. Later credits remain separated by actual exit. -/
def analyze {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool) :
    Nat → WordLangProgHOL (BitVec width) → Option Effects
  | 0,_ => none
  | _+1,.alloc .. | _+1,.mustTerminate .. | _+1,.install .. => none
  | _+1,.tick => some (atom .fall (-1))
  | _+1,.shareInst .. => some (merge (atom .fall 1) (atom .final 1))
  | _+1,.raise _ => some (atom .raised 1)
  | _+1,.return .. => some (atom .returned 0)
  | _+1,.break label => some (atom (.breakTo label) 0)
  | _+1,.continue label => some (atom (.continueTo label) 0)
  | _+1,.ffi name .. => some (ffiEffects (terminal name))
  | n+1,.seq first second => do
      let a ← analyze defs terminal n first
      let b ← analyze defs terminal n second
      pure (WordCostEffects.seq a b)
  | n+1,.ite _ _ _ first second => do
      let a ← analyze defs terminal n first
      let b ← analyze defs terminal n second
      pure (merge a b)
  | n+1,.loop _ body _ => do
      let a ← analyze defs terminal n body
      if one (join (a .fall) (a (.continueTo 0))) then some (loopEffects a) else none
  | _+1,.call none dest _ none => some (shift (some (-1)) (defs dest))
  | _+1,.call none _ _ (some _) => none
  | n+1,.call (some (_,_,next,_,_)) dest _ none => do
      let c ← analyze defs terminal n next
      pure (returningEffects (defs dest) c none)
  | n+1,.call (some (_,_,next,_,_)) dest _ (some (_,handler,_,_)) => do
      let c ← analyze defs terminal n next
      let h ← analyze defs terminal n handler
      pure (returningEffects (defs dest) c (some h))
  | _+1,_ => some (atom .fall 0)

/-- Every successful checker result is a syntactic certificate consumed by
`WordCostCertificates.sound`; computation is never used as an axiom. -/
theorem analyze_derives {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (fuel : Nat) (p : WordLangProgHOL (BitVec width)) (effects : Effects)
    (checked : analyze defs terminal fuel p = some effects) :
    Derives defs terminal p effects := by
  induction fuel generalizing p effects with
  | zero => simp only [analyze,reduceCtorEq] at checked
  | succ fuel ih =>
    cases p with
    | alloc _ _ | mustTerminate _ | install _ _ _ _ _ => cases checked
    | tick => cases checked; exact Derives.tick
    | shareInst op reg exp => cases checked; exact Derives.share op reg exp
    | raise reg => cases checked; exact Derives.raise reg
    | «return» reg regs => cases checked; exact Derives.result reg regs
    | «break» label => cases checked; exact Derives.breakTo label
    | «continue» label => cases checked; exact Derives.continueTo label
    | ffi name p1 l1 p2 l2 names => cases checked; exact Derives.ffi name p1 l1 p2 l2 names
    | seq first second =>
      simp only [analyze] at checked
      cases ha : analyze defs terminal fuel first with
      | none => simp [ha] at checked
      | some a =>
        cases hb : analyze defs terminal fuel second with
        | none => simp [ha,hb] at checked
        | some b =>
          simp only [ha,hb,bind,pure,Option.bind,Option.pure_def,Option.some.injEq] at checked
          subst effects
          exact Derives.seq (ih first a ha) (ih second b hb)
    | ite cmp reg operand first second =>
      simp only [analyze] at checked
      cases ha : analyze defs terminal fuel first with
      | none => simp [ha] at checked
      | some a =>
        cases hb : analyze defs terminal fuel second with
        | none => simp [ha,hb] at checked
        | some b =>
          simp only [ha,hb,bind,pure,Option.bind,Option.pure_def,Option.some.injEq] at checked
          subst effects
          exact Derives.branch cmp reg operand (ih first a ha) (ih second b hb)
    | loop names body exits =>
      simp only [analyze] at checked
      cases ha : analyze defs terminal fuel body with
      | none => simp [ha] at checked
      | some a =>
        simp only [ha,bind,Option.bind] at checked
        split at checked
        · rename_i bounded
          cases checked
          exact Derives.loop names exits (ih body a ha) (one_sound _ bounded)
        · cases checked
    | call ret dest args handler =>
      rcases ret with _ | ⟨names,live,next,l1,l2⟩
      · cases handler with
        | none => cases checked; exact Derives.tail dest args
        | some _ => cases checked
      · cases handler with
        | none =>
          simp only [analyze] at checked
          cases hc : analyze defs terminal fuel next with
          | none => simp [hc] at checked
          | some c =>
            simp only [hc,bind,pure,Option.bind,Option.pure_def,Option.some.injEq] at checked
            subst effects
            exact Derives.returning names live next l1 l2 dest args none c (fun _ => none)
              (ih next c hc) (by intro name body h1 h2 equal; cases equal)
        | some h =>
          rcases h with ⟨name,hbody,h1,h2⟩
          simp only [analyze] at checked
          cases hc : analyze defs terminal fuel next with
          | none => simp [hc] at checked
          | some c =>
            cases hh : analyze defs terminal fuel hbody with
            | none => simp [hc,hh] at checked
            | some h =>
              simp only [hc,hh,bind,pure,Option.bind,Option.pure_def,Option.some.injEq] at checked
              subst effects
              apply Derives.returning names live next l1 l2 dest args (some (name,hbody,h1,h2)) c h
                (ih next c hc)
              intro actual body a1 a2 equal
              simp only [Option.some.injEq,Prod.mk.injEq] at equal
              obtain ⟨rfl,rfl,rfl,rfl⟩ := equal
              exact ih hbody h hh
    | skip | move _ _ | inst _ | assign _ _ | get _ _ | set _ _ | store _ _ | storeConsts _ _ _ _ _ | opCurrHeap _ _ _ | locValue _ _ | codeBufferWrite _ _ | dataBufferWrite _ _ =>
      cases checked
      apply Derives.normal
      simp only [erase]

end InitECandidate.Solver.Wave8Stage.WordCostAnalysis
