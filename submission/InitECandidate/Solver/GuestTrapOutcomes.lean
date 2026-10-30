import InitECandidate.Solver.GuestTrapAndLookup

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.GuestTrapAndLookup

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestExceptionShapes
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestFrameMemKeep

theorem lookup_trap_with :
    originalRuntimeCode.lookup (ofString "trap_with") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_trap_with, .one) :=
  lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_trap_with) rfl

theorem lookup_memzero :
    originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)], sourceFnBody Guest.Software.guestFn_memzero, .one) :=
  lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memzero) rfl

theorem lookup_alloc :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem lookup_fork_init :
    originalRuntimeCode.lookup (ofString "fork_init") =
      some ([], sourceFnBody Guest.Software.guestFn_fork_init, .one) :=
  lookup_of_guestAst_getElem 861 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_fork_init) rfl

/-- Zero-parameter lookup helper. -/
theorem pan_zero_arg_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name : MlS) (body : ProgHOL width) (rs : ShapeHOL)
    (lookup : code name = some ([], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [] =
      some (body, HolFiniteMapExact.empty, rs) := by
  have raw : lookupCodeHOLExact code name [] =
      some (body, (fun _ => none), rs) := by
    simp [lookupCodeHOLExact, lookup]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    rfl

/-- One-word-parameter lookup helper. -/
theorem pan_one_word_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name parameter : MlS) (body : ProgHOL width) (amount : BitVec width)
    (lookup : code name = some ([(parameter, .one)], body, .one)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [.val (.word amount)] =
      some (body, HolFiniteMapExact.empty.update (parameter, .val (.word amount)), .one) := by
  have raw : lookupCodeHOLExact code name [.val (.word amount)] =
      some (body, (fun key => if key = parameter then some (.val (.word amount)) else none), .one) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, ShapeHOL.one))
    apply HolFiniteMapExact.ext
    funext key
    by_cases same : key = parameter
    · subst same
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
    · have different : parameter ≠ key := Ne.symm same
      simp [same, different, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

/-- Two-word-parameter lookup helper. -/
theorem pan_two_word_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (body : ProgHOL width) (left right : BitVec width)
    (different : first ≠ second)
    (lookup : code name = some ([(first, .one), (second, .one)], body, .one)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [.val (.word left), .val (.word right)] =
      some (body, (HolFiniteMapExact.empty.update (first, .val (.word left))).update (second, .val (.word right)), .one) := by
  have raw : lookupCodeHOLExact code name [.val (.word left), .val (.word right)] =
      some (body, (fun key => if key = second then some (.val (.word right)) else if key = first then some (.val (.word left)) else none), .one) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL, different]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, ShapeHOL.one))
    apply HolFiniteMapExact.ext
    funext key
    by_cases one : key = first
    · subst key
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, different, Ne.symm different]
    · have backOne : first ≠ key := Ne.symm one
      by_cases two : key = second
      · subst key
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
      · have backTwo : second ≠ key := Ne.symm two
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, one, two, backOne, backTwo]

/-- Three-word-parameter lookup helper. -/
theorem pan_three_word_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second third : MlS) (body : ProgHOL width) (left right last : BitVec width)
    (different : first ≠ second) (firstThird : first ≠ third) (secondThird : second ≠ third)
    (lookup : code name = some ([(first, .one), (second, .one), (third, .one)], body, .one)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [.val (.word left), .val (.word right), .val (.word last)] =
      some (body, ((HolFiniteMapExact.empty.update (first, .val (.word left))).update (second, .val (.word right))).update (third, .val (.word last)), .one) := by
  have raw : lookupCodeHOLExact code name [.val (.word left), .val (.word right), .val (.word last)] =
      some (body, (fun key => if key = third then some (.val (.word last)) else if key = second then some (.val (.word right)) else if key = first then some (.val (.word left)) else none), .one) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL, different, firstThird, secondThird]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, ShapeHOL.one))
    apply HolFiniteMapExact.ext
    funext key
    by_cases three : key = third
    · subst key
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
    · have backThree := Ne.symm three
      by_cases two : key = second
      · subst key
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, secondThird, Ne.symm secondThird]
      · have backTwo := Ne.symm two
        by_cases one : key = first
        · subst key
          simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
            different, Ne.symm different, firstThird, Ne.symm firstThird]
        · have backOne := Ne.symm one
          simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
            one, two, three, backOne, backTwo, backThree]

/-- `trap_with` body never returns `none` and never returns `some (.returned v)` and never raises anything except `TrapErr`. -/
theorem evaluate_trap_with_body_outcomes {F : Type} (state : PanSemStateFiniteExact 64 F) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_trap_with)
    out.1 ≠ none ∧
    (∀ v, out.1 ≠ some (.returned v)) ∧
    (∀ eid v, eid ≠ ofString "TrapErr" → out.1 ≠ some (.exception eid v)) := by
  have hbody : sourceFnBody Guest.Software.guestFn_trap_with =
      .seq (.shMemStore .op8 (.op .add [.const 2688614400, .const 33]) (.var .local (ofString "code")))
        (.seq (.shMemStore .opW (.op .add [.const 2688614400, .const 40]) (.var .global (ofString "heap_ptr")))
          (.seq (.shMemStore .opW (.op .add [.const 2688614400, .const 48]) (.var .global (ofString "journal_n")))
            (.seq (.extCall (ofString "trap") .baseAddr (.var .local (ofString "code")) .baseAddr (.const 0))
              (.raise (ofString "TrapErr") (.var .local (ofString "code")))))) := rfl
  have hsh (s : PanSemStateFiniteExact 64 F) (op : OpSize) (a e : ExpHOL 64) :
      let r := (evaluateHOLFiniteState s (.shMemStore op a e)).1
      r = none ∨ r = some .error ∨ ∃ ev, r = some (.finalFfi ev) := by
    classical
    dsimp only
    rw [evaluateHOLFiniteState_shMemStore_total]
    dsimp only
    split
    · unfold shMemStoreHOLExact
      split <;> split
      all_goals simp [ofExact, toExact]
      all_goals split <;> simp
    · simp
  have hext (s : PanSemStateFiniteExact 64 F) (fn : MlS) (a b c d : ExpHOL 64) :
      let r := (evaluateHOLFiniteState s (.extCall fn a b c d)).1
      r = none ∨ r = some .error ∨ ∃ ev, r = some (.finalFfi ev) := by
    classical
    dsimp only
    rw [evaluateHOLFiniteState_extCall_source]
    split
    · split
      · split <;> simp
      · simp
    · simp
  have hraise (s : PanSemStateFiniteExact 64 F) :
      let r := (evaluateHOLFiniteState s (.raise (ofString "TrapErr") (.var .local (ofString "code")))).1
      r = some .error ∨ ∃ v, r = some (.exception (ofString "TrapErr") v) := by
    classical
    dsimp only
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split <;> simp
    · simp
  have hseq (s : PanSemStateFiniteExact 64 F) (p1 p2 : ProgHOL 64)
      (hp1 : let r := (evaluateHOLFiniteState s p1).1; r = none ∨ r = some .error ∨ ∃ ev, r = some (.finalFfi ev))
      (hp2 : ∀ s' : PanSemStateFiniteExact 64 F, let r := (evaluateHOLFiniteState s' p2).1
        r ≠ none ∧ (∀ v, r ≠ some (.returned v)) ∧ (∀ eid v, eid ≠ ofString "TrapErr" → r ≠ some (.exception eid v))) :
      let r := (evaluateHOLFiniteState s (.seq p1 p2)).1
      r ≠ none ∧ (∀ v, r ≠ some (.returned v)) ∧ (∀ eid v, eid ≠ ofString "TrapErr" → r ≠ some (.exception eid v)) := by
    dsimp only at hp1 ⊢
    rw [evaluateHOLFiniteState_seq_line780]
    cases h1 : evaluateHOLFiniteState s p1 with
    | mk res1 st1 =>
      rw [h1] at hp1
      rcases hp1 with rfl | rfl | ⟨ev, rfl⟩
      · exact hp2 st1
      · refine ⟨by simp, fun _ => by simp, fun _ _ _ => by simp⟩
      · refine ⟨by simp, fun _ => by simp, fun _ _ _ => by simp⟩
  dsimp only
  rw [hbody]
  apply hseq _ _ _ (hsh _ _ _ _)
  intro s1
  apply hseq _ _ _ (hsh _ _ _ _)
  intro s2
  apply hseq _ _ _ (hsh _ _ _ _)
  intro s3
  apply hseq _ _ _ (hext _ _ _ _ _ _)
  intro s4
  rcases hraise s4 with herr | ⟨v, hexn⟩
  · dsimp only at herr ⊢
    rw [herr]
    exact ⟨by simp, fun _ => by simp, fun _ _ _ => by simp⟩
  · dsimp only at hexn ⊢
    rw [hexn]
    refine ⟨by simp, fun _ => by simp, fun eid w hne h => ?_⟩
    injection h with h'
    cases h'
    exact hne rfl

end InitECandidate.Solver.GuestTrapAndLookup
