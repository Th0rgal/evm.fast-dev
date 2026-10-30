import InitE.OracleReplay
import InitECandidate.Solver.GuestGlobalKeep

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.B2Oracle

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep

theorem shMemStoreHOLExact_consistent {F : Type} (oracle : HolOracle F) (initial : F)
    (state : PanSemStateExact 64 F) [DecidablePred state.shMemaddrs]
    (word address : BitVec 64) (nb : Nat) (h : OracleConsistent oracle initial state.ffi) :
    OracleConsistent oracle initial (shMemStoreHOLExact state word address nb).2.ffi := by
  unfold shMemStoreHOLExact
  split
  · split
    · cases hc : callFFIHOL state.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL word false ++ panWordToBytesHOL address false) with
      | final ev => exact h
      | ret next r => exact call_oracle_consistent oracle initial _ _ _ _ _ _ h hc
    · exact h
  · split
    · cases hc : callFFIHOL state.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
          ((panWordToBytesHOL word false).take nb ++ panWordToBytesHOL address false) with
      | final ev => exact h
      | ret next r => exact call_oracle_consistent oracle initial _ _ _ _ _ _ h hc
    · exact h

theorem shMemLoadHOLFiniteExact_consistent {F : Type} (oracle : HolOracle F) (initial : F)
    (state : PanSemStateFiniteExact 64 F) [DecidablePred state.shMemaddrs]
    (kind : VarKind) (name : MlS) (address : BitVec 64) (nb : Nat)
    (h : OracleConsistent oracle initial state.ffi) :
    OracleConsistent oracle initial (shMemLoadHOLFiniteExact state kind name address nb).2.ffi := by
  unfold shMemLoadHOLFiniteExact
  split
  · split
    · cases hc : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) with
      | final ev => exact h
      | ret next r =>
          simp only [setKvarFfiHOLFinite]
          cases kind <;> exact call_oracle_consistent oracle initial _ _ _ _ _ _ h hc
    · exact h
  · split
    · cases hc : callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) with
      | final ev => exact h
      | ret next r =>
          simp only [setKvarFfiHOLFinite]
          cases kind <;> exact call_oracle_consistent oracle initial _ _ _ _ _ _ h hc
    · exact h

theorem evaluate_consistent {F : Type} (oracle : HolOracle F) (initial : F)
    (program : ProgHOL 64) (state : PanSemStateFiniteExact 64 F)
    (h : OracleConsistent oracle initial state.ffi) :
    OracleConsistent oracle initial (evaluateHOLFiniteState state program).2.ffi := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; exact h
  | dec name kind initializer body =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact h
    · split
      · exact evaluate_consistent oracle initial body _ h
      · exact h
  | decCall name kind function arguments continuation =>
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · exact h
    · rename_i values _
      split
      · exact h
      · rename_i body callee rs found
        split
        · exact h
        · rename_i nonzero
          dsimp only
          have ih := evaluate_consistent oracle initial body (callEntryStateHOLFinite state callee) h
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih cl
          obtain ⟨r, st⟩ := out
          dsimp only at ih cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          rcases r with _ | (_ | _ | _ | _ | v | _ | ev)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try exact ih)
          split
          · have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            exact evaluate_consistent oracle initial continuation (setVarHOLFinite name v _) ih
          · exact ih
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · exact h
    · split
      · cases kind <;> exact h
      · exact h
  | seq first second =>
    have firstOk := evaluate_consistent oracle initial first state h
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at firstOk remaining
      dsimp only at firstOk remaining
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        exact evaluate_consistent oracle initial second middle firstOk
      | some result => exact firstOk
  | ite condition yes no =>
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_consistent oracle initial no state h
      · exact evaluate_consistent oracle initial yes state h
    · exact h
  | «while» condition body =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact h
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have bodyOk := evaluate_consistent oracle initial body (decClockHOLFinite state) h
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at bodyOk remaining
            dsimp only at bodyOk remaining
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            cases result with
            | none => exact evaluate_consistent oracle initial (.while condition body) middle bodyOk
            | some result =>
              cases result with
              | «continue» => exact evaluate_consistent oracle initial (.while condition body) middle bodyOk
              | «break» => exact bodyOk
              | returned value => exact bodyOk
              | exception exception value => exact bodyOk
              | finalFfi ffi => exact bodyOk
              | error => exact bodyOk
              | timeOut => exact bodyOk
      · exact h
    · exact h
  | «break» => rw [evaluateHOLFiniteState_break]; exact h
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact h
  | annot tag text => rw [evaluateHOLFiniteState_annot]; exact h
  | tick => rw [evaluateHOLFiniteState_tick]; split <;> exact h
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> exact h
    · exact h
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact h
    · split <;> exact h
  | store destination value =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> exact h
      · exact h
    · exact h
  | store32 destination value =>
    rw [evaluateHOLFiniteState_store32]
    repeat' split
    all_goals exact h
  | storeByte destination value =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> exact h
      · exact h
    · exact h
  | extCall name a b c d =>
    rw [evaluateHOLFiniteState_extCall_source]
    split
    · split
      · split
        · exact h
        · rename_i hc
          exact call_oracle_consistent oracle initial _ _ _ _ _ _ h hc
      · exact h
    · exact h
  | primitive name op args =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · exact h
    · split
      · exact h
      · split
        · exact h
        · exact h
  | shMemStore op a v =>
    classical
    rw [evaluateHOLFiniteState_shMemStore_total]
    dsimp only
    split
    · exact shMemStoreHOLExact_consistent oracle initial _ _ _ _ h
    · exact h
  | shMemLoad op kind name a =>
    classical
    rw [evaluateHOLFiniteState_shMemLoad_source]
    split
    · split
      · exact shMemLoadHOLFiniteExact_consistent oracle initial _ _ _ _ _ h
      · exact h
    · exact h
  | call info function arguments =>
    rw [evaluateHOLFiniteState_call]
    split
    · exact h
    · rename_i values _
      split
      · exact h
      · rename_i body callee rs found
        split
        · exact h
        · rename_i nonzero
          have ih := evaluate_consistent oracle initial body (callEntryStateHOLFinite state callee) h
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih cl
          obtain ⟨r, st⟩ := out
          dsimp only at ih cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stc : st.clock < state.clock := by omega
          rcases r with _ | (_ | _ | _ | _ | v | ⟨eid, ev⟩ | fe)
          · exact ih
          · exact ih
          · exact ih
          · exact ih
          · exact ih
          · dsimp only
            split
            · rcases info with _ | ⟨_ | ⟨kind, nm⟩, _⟩
              · exact ih
              · exact ih
              · dsimp only
                split
                · cases kind <;> exact ih
                · exact ih
            · exact ih
          · dsimp only
            rcases info with _ | ⟨dest, _ | ⟨hid, hv, hp⟩⟩
            · exact ih
            · exact ih
            · dsimp only
              split
              · split
                · split
                  · exact evaluate_consistent oracle initial hp
                      (setVarHOLFinite hv ev { st with locals := state.locals }) ih
                  · exact ih
                · exact ih
              · exact ih
          · exact ih
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | (simp only [callEntryStateHOLFinite] at small; exact Or.inl small)
      | exact Or.inl stc
      | omega
      | (by_cases hc : state.clock = 0
         · right; refine ⟨by omega, ?_⟩; simp +arith
         · left; omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · right; refine ⟨h, ?_⟩; simp +arith)
      | (right; refine ⟨rfl, ?_⟩; simp +arith)

end InitECandidate.Solver.B2Oracle
