import InitECandidate.Solver.Wave8GuestInv.Expressions

/-! RLP family: flowing runs keep word locals words (assignments are shape-checked; `dec` /
`decCall` restore shadowed names). Same induction as `evaluate_ro`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.Wave8Leaves.Rlp

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup

/-- Programs whose constructs are all covered by `evaluate_wordLocal`. -/
def wsafe : ProgHOL 64 → Bool
  | .dec _ _ _ body => wsafe body
  | .seq first second => wsafe first && wsafe second
  | .ite _ yes no => wsafe yes && wsafe no
  | .while _ body => wsafe body
  | .assign _ _ _ => true
  | .store _ _ | .storeByte _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .decCall _ _ _ _ continuation => wsafe continuation
  | .call none _ _ => true
  | .call (some (_, none)) _ _ => true
  | .call (some (_, some (_, _, handler))) _ _ => wsafe handler
  | _ => false

def WordLocal {F : Type} (x : MlS) (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w : BitVec 64, s.locals.lookup x = some (.val (.word w))

theorem shape_one_word (v : ValueHOL 64) (h : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ w, v = .val (.word w) := by
  rcases v with ⟨⟨w⟩⟩ | fs | ⟨n, fs⟩
  · exact ⟨w, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL] at h
  · simp [shapeOfHOLExact, shapeEqHOL] at h

theorem evaluate_wordLocal {F : Type} (x : MlS)
    (program : ProgHOL 64) (supported : wsafe program = true)
    (state : PanSemStateFiniteExact 64 F) (hx : WordLocal x state)
    (hflow : Flowing (evaluateHOLFiniteState state program).1) :
    WordLocal x (evaluateHOLFiniteState state program).2 := by
  cases shape : program with
  | skip => subst shape; rw [evaluateHOLFiniteState_skip]; exact hx
  | «break» => subst shape; rw [evaluateHOLFiniteState_break]; exact hx
  | «continue» => subst shape; rw [evaluateHOLFiniteState_continue]; exact hx
  | annot tag text => subst shape; rw [evaluateHOLFiniteState_annot]; exact hx
  | raise name value =>
    subst shape
    revert hflow
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp [Flowing]
    · simp [Flowing]
  | «return» value =>
    subst shape
    revert hflow
    rw [evaluateHOLFiniteState_return]
    split
    · simp [Flowing]
    · split <;> simp [Flowing]
  | store destination value =>
    subst shape
    revert hflow
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · intro _; exact hx
        · simp [Flowing]
      · simp [Flowing]
    · simp [Flowing]
  | storeByte destination value =>
    subst shape
    revert hflow
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · intro _; exact hx
        · simp [Flowing]
      · simp [Flowing]
    · simp [Flowing]
  | assign kind name value =>
    subst shape
    revert hflow
    rw [evaluateHOLFiniteState_assign]
    split
    · simp [Flowing]
    · rename_i v _
      split
      · rename_i hvalid
        intro _
        obtain ⟨w, hw⟩ := hx
        cases kind with
        | global => exact ⟨w, by simpa [setKvarHOLFinite, setGlobalHOLFinite] using hw⟩
        | «local» =>
          by_cases hxn : x = name
          · subst hxn
            have hsh : shapeEqHOL (shapeOfHOLExact v) .one = true := by
              simpa [isValidValueHOLFinite, lookupKvarHOLFinite, hw, shapeOfHOLExact] using hvalid
            obtain ⟨w', rfl⟩ := shape_one_word v hsh
            exact ⟨w', by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
          · exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              Ne.symm hxn, hw]⟩
      · simp [Flowing]
  | dec name kind initializer body =>
    have child : wsafe body = true := by simpa only [shape, wsafe] using supported
    subst shape
    revert hflow
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp [Flowing]
    · split
      · rename_i v _ _
        intro hflow
        obtain ⟨w, hw⟩ := hx
        by_cases hxn : x = name
        · subst hxn
          exact ⟨w, by rw [PanRunBounded.resVarEq_lookup, if_pos rfl]; exact hw⟩
        · have hx' : WordLocal x (setVarHOLFinite name v state) :=
            ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn, hw]⟩
          obtain ⟨w', hw'⟩ := evaluate_wordLocal x body child (setVarHOLFinite name v state) hx' hflow
          exact ⟨w', by rw [PanRunBounded.resVarEq_lookup, if_neg hxn]; exact hw'⟩
      · simp [Flowing]
  | seq first second =>
    have children : wsafe first = true ∧ wsafe second = true := by
      simpa only [shape, wsafe, Bool.and_eq_true] using supported
    subst shape
    have remaining := evaluateHOLFiniteState_clock_le state first
    revert hflow
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at remaining
      dsimp only at remaining
      cases result with
      | none =>
        intro hflow
        have mclock : middle.clock ≤ state.clock := remaining
        have hm : WordLocal x middle := by
          have := evaluate_wordLocal x first children.1 state hx (by rw [firstRun]; exact Or.inl rfl)
          rw [firstRun] at this; exact this
        exact evaluate_wordLocal x second children.2 middle hm hflow
      | some result =>
        intro hflow
        have := evaluate_wordLocal x first children.1 state hx (by rw [firstRun]; exact hflow)
        rw [firstRun] at this; exact this
  | ite condition yes no =>
    have children : wsafe yes = true ∧ wsafe no = true := by
      simpa only [shape, wsafe, Bool.and_eq_true] using supported
    subst shape
    revert hflow
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_wordLocal x no children.2 state hx
      · exact evaluate_wordLocal x yes children.1 state hx
    · simp [Flowing]
  | «while» condition body =>
    have child : wsafe body = true := by simpa only [shape, wsafe] using supported
    subst shape
    revert hflow
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp [Flowing]
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at remaining
            dsimp only at remaining
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            have hxd : WordLocal x (decClockHOLFinite state) := hx
            have hmid (hf : Flowing result) : WordLocal x middle := by
              have := evaluate_wordLocal x body child (decClockHOLFinite state) hxd (by rw [bodyRun]; exact hf)
              rw [bodyRun] at this; exact this
            cases result with
            | none =>
              intro hflow
              exact evaluate_wordLocal x (.while condition body) (by simpa [wsafe] using child) middle
                (hmid (Or.inl rfl)) hflow
            | some result =>
              cases result with
              | «continue» =>
                intro hflow
                exact evaluate_wordLocal x (.while condition body) (by simpa [wsafe] using child) middle
                  (hmid (Or.inr (Or.inr rfl))) hflow
              | «break» => intro _; exact hmid (Or.inr (Or.inl rfl))
              | _ => simp [Flowing]
      · intro _; exact hx
    · simp [Flowing]
  | decCall name kind function arguments continuation =>
    have child : wsafe continuation = true := by simpa only [shape, wsafe] using supported
    subst shape
    revert hflow
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · simp [Flowing]
    · split
      · simp [Flowing]
      · rename_i body callee rs found
        split
        · simp [Flowing]
        · rename_i nonzero
          dsimp only
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at cl ⊢
          obtain ⟨r, st⟩ := out
          dsimp only at cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try simp [Flowing])
          split
          · intro hflow
            have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            obtain ⟨w, hw⟩ := hx
            by_cases hxn : x = name
            · subst hxn
              exact ⟨w, by rw [PanRunBounded.resVarEq_lookup, if_pos rfl]; exact hw⟩
            · obtain ⟨w', hw'⟩ := evaluate_wordLocal x continuation child _
                ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn, hw]⟩ hflow
              exact ⟨w', by rw [PanRunBounded.resVarEq_lookup, if_neg hxn]; exact hw'⟩
          · intro h; rcases h with h | h | h <;> simp at h
  | call info function arguments =>
    subst shape
    revert hflow
    rw [evaluateHOLFiniteState_call]
    split
    · simp [Flowing]
    · split
      · simp [Flowing]
      · rename_i body callee rs found
        split
        · simp [Flowing]
        · rename_i nonzero
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at cl ⊢
          obtain ⟨r, st⟩ := out
          dsimp only at cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stc : st.clock < state.clock := by omega
          obtain ⟨w, hw⟩ := hx
          have hnf : ∀ (o : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
              o ≠ none → o ≠ some .break → o ≠ some .continue → Flowing (o, t).1 → WordLocal x (o, t).2 := by
            intro o t h1 h2 h3 hf
            rcases hf with hf | hf | hf
            · exact absurd hf h1
            · exact absurd hf h2
            · exact absurd hf h3
          cases r with
          | none => exact hnf _ _ (by simp) (by simp) (by simp)
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · rcases info with _ | ⟨_ | ⟨kind, nm⟩, handler⟩
                · exact hnf _ _ (by simp) (by simp) (by simp)
                · intro _; exact ⟨w, hw⟩
                · dsimp only
                  split
                  · rename_i hvalid
                    intro _
                    cases kind with
                    | global => exact ⟨w, by simpa [setKvarHOLFinite, setGlobalHOLFinite] using hw⟩
                    | «local» =>
                      by_cases hxn : x = nm
                      · subst hxn
                        have hsh : shapeEqHOL (shapeOfHOLExact v) .one = true := by
                          simpa [isValidValueHOLExact, lookupKvarHOLExact, toExact, hw, shapeOfHOLExact]
                            using hvalid
                        obtain ⟨w', rfl⟩ := shape_one_word v hsh
                        exact ⟨w', by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update,
                          FUPDATE]⟩
                      · exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update,
                          FUPDATE, Ne.symm hxn, hw]⟩
                  · exact hnf _ _ (by simp) (by simp) (by simp)
              · exact hnf _ _ (by simp) (by simp) (by simp)
            | exception e v =>
              dsimp only
              rcases info with _ | ⟨dest, _ | ⟨hid, hv, hp⟩⟩
              · exact hnf _ _ (by simp) (by simp) (by simp)
              · exact hnf _ _ (by simp) (by simp) (by simp)
              · have hhp : wsafe hp = true := by
                  rcases dest with _ | ⟨_, _⟩ <;> simpa [wsafe] using supported
                dsimp only
                split
                · split
                  · split
                    · rename_i hc
                      intro hflow
                      simp only [Bool.and_eq_true] at hc
                      refine evaluate_wordLocal x hp hhp _ ?_ hflow
                      by_cases hxn : x = hv
                      · subst hxn
                        have hsh : shapeEqHOL (shapeOfHOLExact v) .one = true := by
                          simpa [isValidValueHOLExact, lookupKvarHOLExact, toExact, hw, shapeOfHOLExact]
                            using hc.2
                        obtain ⟨w', rfl⟩ := shape_one_word v hsh
                        exact ⟨w', by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
                      · exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          Ne.symm hxn, hw]⟩
                    · exact hnf _ _ (by simp) (by simp) (by simp)
                  · exact hnf _ _ (by simp) (by simp) (by simp)
                · exact hnf _ _ (by simp) (by simp) (by simp)
            | _ => exact hnf _ _ (by simp) (by simp) (by simp)
  | _ => simp [shape, wsafe] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | (simp only [callEntryStateHOLFinite] at small; exact Or.inl small)
      | omega
      | (by_cases hc : state.clock = 0
         · right; refine ⟨by omega, ?_⟩; simp +arith
         · left; omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · right; refine ⟨h, ?_⟩; simp +arith)
      | (right; refine ⟨rfl, ?_⟩; simp +arith)

end InitECandidate.Solver.Wave8Leaves.Rlp
