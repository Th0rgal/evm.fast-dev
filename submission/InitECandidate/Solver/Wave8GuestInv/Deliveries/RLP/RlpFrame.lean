import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpHandle

/-! RLP family, part 7: frame lemma for read-only programs (memory, globals and ffi preserved),
adapted from `GuestGlobalKeep.evaluate_keepsG` (same induction on `(clock, sizeOf program)`). -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.Wave8Leaves.Rlp

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingCombinators

/-- Read-only programs: no stores, no global writes, no FFI/shared memory, calls (with local or no
destination) only to `good` functions, whose bodies must themselves be read-only. -/
def roProg (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => roProg good body
  | .seq first second => roProg good first && roProg good second
  | .ite _ yes no => roProg good yes && roProg good no
  | .while _ body => roProg good body
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .decCall _ _ function _ continuation => good function && roProg good continuation
  | .call none function _ => good function
  | .call (some (none, none)) function _ => good function
  | .call (some (some (.local, _), none)) function _ => good function
  | .call (some (none, some (_, _, handler))) function _ => good function && roProg good handler
  | .call (some (some (.local, _), some (_, _, handler))) function _ =>
      good function && roProg good handler
  | _ => false

/-- `t` agrees with `s` on memory, globals, FFI state and `topAddr`. -/
def Frame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t.memory = s.memory ∧ t.globals = s.globals ∧ t.ffi = s.ffi ∧ t.topAddr = s.topAddr

theorem Frame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : Frame s s := ⟨rfl, rfl, rfl, rfl⟩

theorem Frame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F} (h1 : Frame s t)
    (h2 : Frame t u) : Frame s u :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

theorem frame_via {F : Type} {s t : PanSemStateFiniteExact 64 F} (y : PanSemStateFiniteExact 64 F)
    (h : Frame y t) (hy : y.memory = s.memory ∧ y.globals = s.globals ∧ y.ffi = s.ffi ∧
      y.topAddr = s.topAddr) :
    Frame s t :=
  ⟨h.1.trans hy.1, h.2.1.trans hy.2.1, h.2.2.1.trans hy.2.2.1, h.2.2.2.trans hy.2.2.2⟩

theorem evaluate_ro {F : Type} (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) → roProg good body = true)
    (program : ProgHOL 64) (supported : roProg good program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    Frame state (evaluateHOLFiniteState state program).2 := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; exact Frame.refl _
  | dec name kind initializer body =>
    have child : roProg good body = true := by simpa only [shape, roProg] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact Frame.refl _
    · split
      · rename_i v _ _
        have h := evaluate_ro good hgood body child (setVarHOLFinite name v state) code
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
      · exact Frame.refl _
  | decCall name kind function arguments continuation =>
    have children : good function = true ∧ roProg good continuation = true := by
      simpa only [shape, roProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · exact Frame.refl _
    · rename_i values _
      split
      · exact Frame.refl _
      · rename_i body callee rs found
        rw [code] at found
        have bodyOk := hgood function children.1 values body callee rs found
        split
        · exact Frame.refl _
        · rename_i nonzero
          dsimp only
          have ih := evaluate_ro good hgood body bodyOk (callEntryStateHOLFinite state callee) code
          have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at ih meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          have ih' : Frame state st := ⟨ih.1, ih.2.1, ih.2.2.1, ih.2.2.2⟩
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try exact ⟨ih'.1, ih'.2.1, ih'.2.2.1, ih'.2.2.2⟩)
          all_goals (try exact ih')
          split
          · have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            have hc := evaluate_ro good hgood continuation children.2 (setVarHOLFinite name v
              { st with locals := state.locals, clock := if state.clock - 1 < st.clock then state.clock - 1 else st.clock })
              (by exact stCode)
            exact Frame.trans ih' ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
          · exact ih'
  | assign kind name value =>
    cases kind with
    | global => simp [shape, roProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact Frame.refl _
      · split
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · exact Frame.refl _
  | seq first second =>
    have children : roProg good first = true ∧ roProg good second = true := by
      simpa only [shape, roProg, Bool.and_eq_true] using supported
    have memory := evaluate_ro good hgood first children.1 state code
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at memory remaining meta'
      dsimp only at memory remaining meta'
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        exact Frame.trans memory (evaluate_ro good hgood second children.2 middle (meta'.1.trans code))
      | some result => exact memory
  | ite condition yes no =>
    have children : roProg good yes = true ∧ roProg good no = true := by
      simpa only [shape, roProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_ro good hgood no children.2 state code
      · exact evaluate_ro good hgood yes children.1 state code
    · exact Frame.refl _
  | «while» condition body =>
    have child : roProg good body = true := by simpa only [shape, roProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact Frame.refl _
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have memory := evaluate_ro good hgood body child (decClockHOLFinite state) code
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at memory remaining meta'
            dsimp only at memory remaining meta'
            have memory' : Frame state middle := ⟨memory.1, memory.2.1, memory.2.2.1, memory.2.2.2⟩
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none => exact Frame.trans memory' (evaluate_ro good hgood (.while condition body) (by simpa [roProg] using child) middle mCode)
            | some result =>
              cases result with
              | «continue» => exact Frame.trans memory' (evaluate_ro good hgood (.while condition body) (by simpa [roProg] using child) middle mCode)
              | «break» => exact memory'
              | returned value => exact memory'
              | exception exception value => exact memory'
              | finalFfi ffi => exact memory'
              | error => exact memory'
              | timeOut => exact memory'
      · exact Frame.refl _
    · exact Frame.refl _
  | «break» => rw [evaluateHOLFiniteState_break]; exact Frame.refl _
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact Frame.refl _
  | annot tag text => rw [evaluateHOLFiniteState_annot]; exact Frame.refl _
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    · exact Frame.refl _
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact Frame.refl _
    · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | call info function arguments =>
    have hk : good function = true ∧ (info = none ∨ ∃ handler, info = some (none, handler) ∨
        ∃ nm, info = some (some (.local, nm), handler)) ∧
        ∀ dest hid hv hp, info = some (dest, some (hid, hv, hp)) → roProg good hp = true := by
      rcases info with _ | ⟨_ | ⟨kind, nm⟩, _ | ⟨hid, hv, hp⟩⟩
      · simpa [shape, roProg] using supported
      · simp [shape, roProg] at supported
        exact ⟨supported, Or.inr ⟨none, Or.inl rfl⟩, fun _ _ _ _ h => by cases h⟩
      · simp [shape, roProg] at supported
        exact ⟨supported.1, Or.inr ⟨_, Or.inl rfl⟩, fun _ _ _ _ h => by cases h; exact supported.2⟩
      · cases kind
        · simp [shape, roProg] at supported
          exact ⟨supported, Or.inr ⟨none, Or.inr ⟨nm, rfl⟩⟩, fun _ _ _ _ h => by cases h⟩
        · simp [shape, roProg] at supported
      · cases kind
        · simp [shape, roProg] at supported
          exact ⟨supported.1, Or.inr ⟨_, Or.inr ⟨nm, rfl⟩⟩, fun _ _ _ _ h => by cases h; exact supported.2⟩
        · simp [shape, roProg] at supported
    rw [evaluateHOLFiniteState_call]
    split
    · exact Frame.refl _
    · rename_i values _
      split
      · exact Frame.refl _
      · rename_i body callee rs found
        split
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · rename_i nonzero
          have found' := found
          rw [code] at found'
          have ih := evaluate_ro good hgood body (hgood function hk.1 values body callee rs found')
            (callEntryStateHOLFinite state callee) code
          have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at ih meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stc : st.clock < state.clock := by omega
          have ih' : Frame state st := ⟨ih.1, ih.2.1, ih.2.2.1, ih.2.2.2⟩
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          rcases hk.2.1 with rfl | ⟨handler, rfl | ⟨nm, rfl⟩⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              first
                | exact ih'
                | exact ⟨ih'.1, ih'.2.1, ih'.2.2.1, ih'.2.2.2⟩
          · rcases handler with _ | ⟨hid, hv, hp⟩ <;>
              rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              first
                | exact ih'
                | exact ⟨ih'.1, ih'.2.1, ih'.2.2.1, ih'.2.2.2⟩
                | exact Frame.trans ih' (frame_via _ (evaluate_ro good hgood hp (hk.2.2 _ hid hv hp rfl) _
                    (by exact stCode)) ⟨rfl, rfl, rfl, rfl⟩)
          · rcases handler with _ | ⟨hid, hv, hp⟩ <;>
              rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              first
                | exact ih'
                | exact ⟨ih'.1, ih'.2.1, ih'.2.2.1, ih'.2.2.2⟩
                | (simp only [setKvarHOLFinite, setVarHOLFinite]; exact ⟨ih'.1, ih'.2.1, ih'.2.2.1, ih'.2.2.2⟩)
                | exact Frame.trans ih' (frame_via _ (evaluate_ro good hgood hp (hk.2.2 _ hid hv hp rfl) _
                    (by exact stCode)) ⟨rfl, rfl, rfl, rfl⟩)
  | _ => simp [shape, roProg] at supported
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
