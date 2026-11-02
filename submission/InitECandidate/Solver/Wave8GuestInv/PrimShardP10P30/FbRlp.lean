import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbHtab

/-!
# PrimShardP10P30.FbRlp

Proves `TerminatingFunBoundedOn GuestInv` for the RLP validation and list-decoding callees of
`fb_set_storage` on `wave8/spec-r11`:
- `fb__rlp_validate_items_body` (`62209915858 = 2 * domainBytes + 2`)
- `fb_rlp_validate_items`
- `fb_rlp_item_total`
- `fb_rlp_list_count` (`domainBytes + 1`)
- `fb_rlp_item`
- `fb_rlp_decode_fully`
- `fb_rlp_list_to_slices`
- `fb_decode_account_from_leaf`
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound

/-! ### Read-only program frame (`evaluate_ro`) and word-local preservation (`evaluate_wordLocal`) -/

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

def MemFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t.memory = s.memory ∧ t.globals = s.globals ∧ t.ffi = s.ffi ∧ t.topAddr = s.topAddr

theorem MemFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : MemFrame s s :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem MemFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : MemFrame s t) (h2 : MemFrame t u) : MemFrame s u :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

theorem memFrame_via {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (y : PanSemStateFiniteExact 64 F) (h : MemFrame y t)
    (hy : y.memory = s.memory ∧ y.globals = s.globals ∧ y.ffi = s.ffi ∧ y.topAddr = s.topAddr) :
    MemFrame s t :=
  ⟨h.1.trans hy.1, h.2.1.trans hy.2.1, h.2.2.1.trans hy.2.2.1, h.2.2.2.trans hy.2.2.2⟩

theorem evaluate_ro {F : Type} (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) → roProg good body = true)
    (program : ProgHOL 64) (supported : roProg good program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    MemFrame state (evaluateHOLFiniteState state program).2 := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; exact MemFrame.refl _
  | dec name kind initializer body =>
    have child : roProg good body = true := by simpa only [shape, roProg] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact MemFrame.refl _
    · split
      · rename_i v _ _
        have h := evaluate_ro good hgood body child (setVarHOLFinite name v state) code
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
      · exact MemFrame.refl _
  | decCall name kind function arguments continuation =>
    have children : good function = true ∧ roProg good continuation = true := by
      simpa only [shape, roProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · exact MemFrame.refl _
    · rename_i values _
      split
      · exact MemFrame.refl _
      · rename_i body callee rs found
        rw [code] at found
        have bodyOk := hgood function children.1 values body callee rs found
        split
        · exact MemFrame.refl _
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
          have ih' : MemFrame state st := ⟨ih.1, ih.2.1, ih.2.2.1, ih.2.2.2⟩
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
            exact MemFrame.trans ih' ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
          · exact ih'
  | assign kind name value =>
    cases kind with
    | global => simp [shape, roProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact MemFrame.refl _
      · split
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · exact MemFrame.refl _
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
        exact MemFrame.trans memory (evaluate_ro good hgood second children.2 middle (meta'.1.trans code))
      | some result => exact memory
  | ite condition yes no =>
    have children : roProg good yes = true ∧ roProg good no = true := by
      simpa only [shape, roProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_ro good hgood no children.2 state code
      · exact evaluate_ro good hgood yes children.1 state code
    · exact MemFrame.refl _
  | «while» condition body =>
    have child : roProg good body = true := by simpa only [shape, roProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact MemFrame.refl _
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
            have memory' : MemFrame state middle := ⟨memory.1, memory.2.1, memory.2.2.1, memory.2.2.2⟩
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none => exact MemFrame.trans memory' (evaluate_ro good hgood (.while condition body) (by simpa [roProg] using child) middle mCode)
            | some result =>
              cases result with
              | «continue» => exact MemFrame.trans memory' (evaluate_ro good hgood (.while condition body) (by simpa [roProg] using child) middle mCode)
              | «break» => exact memory'
              | returned value => exact memory'
              | exception exception value => exact memory'
              | finalFfi ffi => exact memory'
              | error => exact memory'
              | timeOut => exact memory'
      · exact MemFrame.refl _
    · exact MemFrame.refl _
  | «break» => rw [evaluateHOLFiniteState_break]; exact MemFrame.refl _
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact MemFrame.refl _
  | annot tag text => rw [evaluateHOLFiniteState_annot]; exact MemFrame.refl _
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    · exact MemFrame.refl _
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact MemFrame.refl _
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
    · exact MemFrame.refl _
    · rename_i values _
      split
      · exact MemFrame.refl _
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
          have ih' : MemFrame state st := ⟨ih.1, ih.2.1, ih.2.2.1, ih.2.2.2⟩
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
                | exact MemFrame.trans ih' (memFrame_via _ (evaluate_ro good hgood hp (hk.2.2 _ hid hv hp rfl) _
                    (by exact stCode)) ⟨rfl, rfl, rfl, rfl⟩)
          · rcases handler with _ | ⟨hid, hv, hp⟩ <;>
              rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              first
                | exact ih'
                | exact ⟨ih'.1, ih'.2.1, ih'.2.2.1, ih'.2.2.2⟩
                | (simp only [setKvarHOLFinite, setVarHOLFinite]; exact ⟨ih'.1, ih'.2.1, ih'.2.2.1, ih'.2.2.2⟩)
                | exact MemFrame.trans ih' (memFrame_via _ (evaluate_ro good hgood hp (hk.2.2 _ hid hv hp rfl) _
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

theorem evalMeta {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) :
    (evaluateHOLFiniteState s p).2.code = s.code ∧
    (evaluateHOLFiniteState s p).2.memaddrs = s.memaddrs ∧
    (evaluateHOLFiniteState s p).2.shMemaddrs = s.shMemaddrs ∧
    (evaluateHOLFiniteState s p).2.be = s.be ∧
    (evaluateHOLFiniteState s p).2.eshapes = s.eshapes ∧
    (evaluateHOLFiniteState s p).2.baseAddr = s.baseAddr ∧
    (evaluateHOLFiniteState s p).2.structs = s.structs := by
  have hm := evaluateHOLFiniteState_metadata s p
  have invariant := evaluateInvariantsHOLFinite p
    (PanPropsEvalStateFiniteExact.ofPanSemFinite s)
    (evaluateHOLFiniteState s p).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState s p).2) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact ⟨hm.1, hm.2.1, hm.2.2.2.1, hm.2.2.1, hm.2.2.2.2, invariant.2.2.2.2.1, invariant.2.2.2.2.2.1⟩

theorem dec_on' {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (name : MlS)
    (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hQ : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      shapeEqHOL .one (shapeOfHOLExact v) = true → Q (setVarHOLFinite name v s))
    (hbody : TerminatingProgBoundedOn Q body K) :
    TerminatingProgBoundedOn P (.dec name .one init body) K := by
  intro F state hcode hPs hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i val _ hsh
      have hb := hbody (setVarHOLFinite name val state) hcode (hQ state val hPs hsh) hnt
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem seq_on' {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64}
    {a b : Nat} (h1 : TerminatingProgBoundedOn P first a) (hp : PreservesOn P Q first)
    (h2 : TerminatingProgBoundedOn Q second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP hnt
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := hp state hcode hP
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨s1, k1⟩ := h1 state hcode hP (by simp [hr1])
    rw [hr1] at s1 k1; dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid (by simp)) hnt
    exact ⟨by omega, by omega⟩
  | some _ =>
    dsimp only at hnt ⊢
    obtain ⟨s1, k1⟩ := h1 state hcode hP (by simpa [hr1] using hnt)
    rw [hr1] at s1 k1; dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem setVar_word {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (v : ValueHOL 64)
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) : WordLocal name (setVarHOLFinite name v s) := by
  obtain ⟨w, rfl⟩ := shape_one_word v (by
    rcases v with ⟨⟨w⟩⟩ | fs | ⟨n, fs⟩ <;> simp_all [shapeEqHOL, shapeOfHOLExact])
  exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩

theorem setVar_keep {F : Type} (s : PanSemStateFiniteExact 64 F) (name x : MlS) (v : ValueHOL 64)
    (hne : name ≠ x) (h : WordLocal x s) : WordLocal x (setVarHOLFinite name v s) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hw]⟩

/-! ### `RetOK` combinators and `hdr_post` (`rlp_item_header` returns `1 ≤ h0 + h1 ≤ len` AND reads `[p, p+8]`) -/

def RetOK (Q : ValueHOL 64 → Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) :
    Prop :=
  ∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) → Q v

theorem R_seq {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (ha : RetOK Q s a) (hb : ∀ mid, evaluateHOLFiniteState s a = (none, mid) → RetOK Q mid b) :
    RetOK Q s (.seq a b) := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780] at hv
  rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
  rw [hr] at hv
  cases r with
  | none => exact hb mid hr v hv
  | some _ => apply ha v; rw [hr]; simpa using hv

theorem R_ite {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {yes no : ProgHOL 64}
    (h : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → (w ≠ 0 → RetOK Q s yes) ∧ (w = 0 → RetOK Q s no)) :
    RetOK Q s (.ite c yes no) := by
  intro v hv
  rw [evaluateHOLFiniteState_ite] at hv
  split at hv
  · rename_i w hw
    split at hv
    · exact (h w hw).2 (by assumption) v hv
    · exact (h w hw).1 (by assumption) v hv
  · simp at hv

theorem R_dec {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (h : ∀ v, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) init =
      some v → shapeEqHOL sh (shapeOfHOLExact v) = true → RetOK Q (setVarHOLFinite n v s) body) :
    RetOK Q s (.dec n sh init body) := by
  intro v hv
  rw [evaluateHOLFiniteState_dec_total] at hv
  dsimp only at hv
  split at hv
  · simp at hv
  · rename_i val hval
    split at hv
    · rename_i hsh; exact h val hval hsh v hv
    · simp at hv

theorem R_ret {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    (h : ∀ v, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
      some v → Q v) :
    RetOK Q s (.return e) := by
  intro v hv
  rw [evaluateHOLFiniteState_return] at hv
  split at hv
  · simp at hv
  · rename_i val hval
    split at hv
    · simp at hv; subst hv; exact h val hval
    · simp at hv

theorem R_skip {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} :
    RetOK Q s .skip := by
  intro v hv; rw [evaluateHOLFiniteState_skip] at hv; simp at hv

theorem rlp_fail_noret {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_fail)).1 ≠ some (.returned v) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_fail =
      .seq (.raise (ofString "RlpErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
  have hraise : ∀ w, (evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ some (.returned w) ∧
      (evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ none := by
    intro w
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  rw [hb, evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
    ProgHOL 64) with ⟨r, mid⟩
  rw [hr] at hraise
  cases r with
  | none => exact absurd rfl (hraise v).2
  | some _ => dsimp only; exact (hraise v).1

theorem lookup_rlp_fail' : originalRuntimeCode.lookup (ofString "rlp_fail") =
    some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_rlp_fail, .one) :=
  lookup_of_guestAst_getElem 105 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_fail) rfl

theorem call_noret {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64))
    (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) f args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, st⟩
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> simp

theorem call_fail_nonone {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "rlp_fail") args)).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · rename_i values _
    split
    · simp
    · rename_i body callee rs hl
      have hb := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ rs values callee
        (by rw [hcode]; exact lookup_rlp_fail') hl
      subst hb
      split
      · simp
      · have hnr := fun w => rlp_fail_noret (callEntryStateHOLFinite s callee) w
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_rlp_fail) with ⟨r, st⟩
        rw [hrun] at hnr
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> try simp
        exact absurd rfl (hnr w)

theorem R_guard {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {c : ExpHOL 64} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (h : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w = 0 → RetOK Q s rest) :
    RetOK Q s (.seq (.ite c (.call (some (none, none)) (ofString "rlp_fail") args) .skip) rest) := by
  apply R_seq
  · apply R_ite
    intro w _
    exact ⟨fun _ v hv => absurd hv (call_noret s _ args v), fun _ => R_skip⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · rename_i w hw
      split at hmid
      · rename_i hw0
        rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact h w hw hw0
      · exact absurd (by rw [hmid]) (call_fail_nonone s hcode args)
    · simp at hmid

theorem R_decCall {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {f : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : ∀ (u : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), shapeEqHOL (shapeOfHOLExact v) sh = true →
      u.code = s.code → (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) →
      u.locals.lookup n = some v → RetOK Q u cont) :
    RetOK Q s (.decCall n sh f args cont) := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv
  split at hv
  · simp at hv
  · split at hv
    · simp at hv
    · rename_i body callee rs _
      split at hv
      · simp at hv
      · have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
        rw [hrun] at hmeta
        change st.code = s.code at hmeta
        simp only [hrun] at hv
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only at hv <;> try simp at hv
        split at hv
        · rename_i hsh
          try simp only [Bool.and_eq_true] at hsh
          refine h _ w hsh.1 (by simp [setVarHOLFinite, fixClockHOLFinite, hmeta]) ?_ ?_ v hv
          · intro k hk
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp at hv

def abrupt : ProgHOL 64 → Bool
  | .return _ => true
  | .raise _ _ => true
  | .seq _ b => abrupt b
  | .dec _ _ _ b => abrupt b
  | .decCall _ _ _ _ c => abrupt c
  | .ite _ y n => abrupt y && abrupt n
  | _ => false

theorem abrupt_nonone {F : Type} (p : ProgHOL 64) (h : abrupt p = true) (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ none := by
  match p, h with
  | .return e, _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | .raise n e, _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | .seq a b, h =>
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
    cases r with
    | none => exact abrupt_nonone b (by simpa [abrupt] using h) mid
    | some _ => simp
  | .dec n sh e b, h =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact abrupt_nonone b (by simpa [abrupt] using h) _
      · simp
  | .decCall n sh f args c, h =>
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · simp
    · split
      · simp
      · rename_i body callee rs _
        split
        · simp
        · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
          simp only [hrun]
          rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
          split
          · exact abrupt_nonone c (by simpa [abrupt] using h) _
          · simp
  | .ite c y n, h =>
    have hh : abrupt y = true ∧ abrupt n = true := by simpa [abrupt] using h
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact abrupt_nonone n hh.2 s
      · exact abrupt_nonone y hh.1 s
    · simp

theorem R_branch {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {yes rest : ProgHOL 64} (hab : abrupt yes = true)
    (hy : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w ≠ 0 → RetOK Q s yes)
    (hr : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w = 0 → RetOK Q s rest) :
    RetOK Q s (.seq (.ite c yes .skip) rest) := by
  apply R_seq
  · apply R_ite
    intro w hw
    exact ⟨hy w hw, fun _ => R_skip⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · rename_i w hw
      split at hmid
      · rename_i hw0
        rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact hr w hw hw0
      · exact absurd (by rw [hmid]) (abrupt_nonone yes hab s)
    · simp at hmid

theorem R_check2 {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {c c' : ExpHOL 64} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (hr : RetOK Q s rest) :
    RetOK Q s (.seq (.ite c (.ite c' (.call (some (none, none)) (ofString "rlp_fail") args) .skip) .skip)
      rest) := by
  apply R_seq
  · apply R_ite
    intro w _
    refine ⟨fun _ => ?_, fun _ => R_skip⟩
    apply R_ite
    intro w' _
    exact ⟨fun _ v hv => absurd hv (call_noret s _ args v), fun _ => R_skip⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · split at hmid
      · rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact hr
      · rw [evaluateHOLFiniteState_ite] at hmid
        split at hmid
        · split at hmid
          · rw [evaluateHOLFiniteState_skip] at hmid
            simp only [Prod.mk.injEq] at hmid
            obtain ⟨-, rfl⟩ := hmid
            exact hr
          · exact absurd (by rw [hmid]) (call_fail_nonone s hcode args)
        · simp at hmid
    · simp at hmid

def hdrShape : ShapeHOL :=
  .comb (InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural
    [Shape.one, Shape.one, Shape.one])

def hval (a b c : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word a), .val (.word b), .val (.word c)]

def HdrQ (L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ a b c : BitVec 64, v = hval a b c ∧ 1 ≤ a.toNat + b.toNat ∧ a.toNat + b.toNat ≤ L.toNat ∧
    (c ≠ 0 → 1 ≤ a.toNat)

theorem loadByte_word_dom {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.loadByte e) =
      some v) :
    ∃ a B : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
        some (.val (.word a)) ∧
      s.memaddrs (panByteAlignHOL (width := 64) a) ∧
      v = .val (.word B) ∧ B.toNat < 256 := by
  simp only [evalHOLExact] at hv
  split at hv
  · rename_i a ha
    dsimp only [panMemLoadByteHOL] at hv
    split at hv
    · rename_i hdom
      simp only [Option.map_some, Option.some.injEq] at hv
      refine ⟨a, _, ha, hdom, hv.symm, ?_⟩
      have := (panGetByteHOL a (s.memory (panByteAlignHOL a)).1 s.be).toNat_lt
      simp; omega
    · simp at hv
  · simp at hv

private theorem lk_set {F : Type} (st : PanSemStateFiniteExact 64 F) (k : MlS) (x : ValueHOL 64) (k' : MlS)
    (hk : k ≠ k') : (setVarHOLFinite k x st).locals.lookup k' = st.locals.lookup k' := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk]

private theorem lk_set' {F : Type} (st : PanSemStateFiniteExact 64 F) (k : MlS) (x : ValueHOL 64) :
    (setVarHOLFinite k x st).locals.lookup k = some x := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem toNat_sub_one (L : BitVec 64) (hL : L ≠ 0) : (L - 1#64).toNat = L.toNat - 1 := by
  have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [BitVec.toNat_sub]; simp; omega

private theorem short_branch {F : Type} (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (L B off flag : BitVec 64) (hL : L ≠ 0)
    (hl : st.locals.lookup (ofString "len") = some (.val (.word L)))
    (hb : st.locals.lookup (ofString "b") = some (.val (.word B))) :
    RetOK (HdrQ L) st
      (.dec (ofString "n") .one (.op .sub [.var .local (ofString "b"), .const off])
        (.seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"), .const 1#64])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
          (.return (.rstruct [.const 1#64, .var .local (ofString "n"), .const flag])))) := by
  refine R_dec (fun v hv _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  refine R_guard (by exact hcode) (fun w hw hw0 => R_ret (fun v hv => ?_))
  have hL1 := toNat_sub_one L hL
  have hne_nb : ofString "n" ≠ ofString "b" := by decide
  have hne_nlen : ofString "n" ≠ ofString "len" := by decide
  have hN : (B - off).toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, lk_set, lk_set', hne_nlen, hl, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 < B - off := by rw [BitVec.lt_def, hL1]; omega
    simp [this] at hw
  simp [evalHOLExact, evalListHOLExact, lk_set, lk_set'] at hv
  subst hv
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  refine ⟨1, B - off, flag, rfl, by simp, ?_, fun _ => by rw [h1]⟩
  rw [h1]
  have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

private theorem long_branch {F : Type} (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (L B off flag : BitVec 64) (hL : L ≠ 0)
    (hl : st.locals.lookup (ofString "len") = some (.val (.word L)))
    (hb : st.locals.lookup (ofString "b") = some (.val (.word B))) :
    RetOK (HdrQ L) st
      (.dec (ofString "ll") .one (.op .sub [.var .local (ofString "b"), .const off])
        (.seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"), .const 1#64])
              (.var .local (ofString "ll")))
            (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
          (.decCall (ofString "n") .one (ofString "rlp_read_length")
            [.op .add [.var .local (ofString "p"), .const 1#64], .var .local (ofString "ll")]
            (.seq (.ite (.cmp .notLower (.const 55#64) (.var .local (ofString "n")))
                (.call (some (none, none)) (ofString "rlp_fail") [.const 5#64]) .skip)
              (.seq (.ite (.cmp .lower (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64],
                    .var .local (ofString "ll")]) (.var .local (ofString "n")))
                  (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
                (.return (.rstruct [.op .add [.const 1#64, .var .local (ofString "ll")],
                  .var .local (ofString "n"), .const flag]))))))) := by
  refine R_dec (fun v hv _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have hL1 := toNat_sub_one L hL
  have hne_ll_len : ofString "ll" ≠ ofString "len" := by decide
  refine R_guard (by exact hcode) (fun w hw hw0 => ?_)
  have hLL : (B - off).toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, lk_set, lk_set', hne_ll_len, hl, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 < B - off := by rw [BitVec.lt_def, hL1]; omega
    simp [this] at hw
  refine R_decCall (fun u v hsh hcu hloc hn => ?_)
  obtain ⟨N, rfl⟩ := shape_one_word v (by
    rcases v with ⟨⟨w⟩⟩ | fs | ⟨n, fs⟩ <;> simp_all [shapeEqHOL, shapeOfHOLExact])
  have hul : u.locals.lookup (ofString "len") = some (.val (.word L)) := by
    rw [hloc _ (by decide), lk_set _ _ _ _ (by decide)]; exact hl
  have hull : u.locals.lookup (ofString "ll") = some (.val (.word (B - off))) := by
    rw [hloc _ (by decide), lk_set']
  have hcu' : u.code = originalRuntimeCode := hcu.trans hcode
  refine R_guard hcu' (fun w _ _ => ?_)
  refine R_guard hcu' (fun w hw hw0 => R_ret (fun v hv => ?_))
  have hsub : (L - 1#64 - (B - off)).toNat = L.toNat - 1 - (B - off).toNat := by
    rw [BitVec.toNat_sub, hL1]; have := (B - off).isLt; omega
  have hNle : N.toNat ≤ L.toNat - 1 - (B - off).toNat := by
    simp [evalHOLExact, evalListHOLExact, hul, hull, hn, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 - (B - off) < N := by rw [BitVec.lt_def, hsub]; omega
    simp [this] at hw
  simp [evalHOLExact, evalListHOLExact, hull, hn, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hadd : (1#64 + (B - off)).toNat = 1 + (B - off).toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [h1]; have := L.isLt; omega), h1]
  refine ⟨1#64 + (B - off), N, flag, rfl, ?_, ?_, fun _ => by rw [hadd]; omega⟩
  · rw [hadd]; omega
  · rw [hadd]
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    omega

/-- `rlp_item_header` returns `1 ≤ h0 + h1 ≤ len` AND guarantees `p` was read from `ordinaryDomain`! -/
theorem hdr_post_dom {F : Type} (e : PanSemStateFiniteExact 64 F)
    (hcode : e.code = originalRuntimeCode) (hP : GuestInv e)
    (P L : BitVec 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState e (sourceFnBody Guest.Software.guestFn_rlp_item_header)).1 =
      some (.returned v)) :
    HdrQ L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd := by
  revert v hret
  change RetOK (fun v => HdrQ L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd) e
    (sourceFnBody Guest.Software.guestFn_rlp_item_header)
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_guard hcode (fun w hw hw0 => ?_)
  have hL : L ≠ 0 := by
    intro h; subst h; simp [evalHOLExact, hl, Compiler.Encoders.Asm.wordCmpHOL] at hw; subst hw0
    simp at hw
  refine R_dec (fun v hv _ => ?_)
  obtain ⟨P', B, ha, hdom, rfl, _⟩ := loadByte_word_dom e _ v hv
  simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq] at ha
  subst ha
  rw [hP.memaddrs] at hdom
  have hbnd := ordinaryDomain_bounds _ hdom
  have hal := byteAlign_bounds P
  have hp_in : sourceBase ≤ P.toNat ∧ P.toNat < heapEnd := ⟨by omega, by omega⟩
  have liftQ : ∀ {st : PanSemStateFiniteExact 64 F} {pr : ProgHOL 64},
      RetOK (HdrQ L) st pr →
      RetOK (fun v => HdrQ L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd) st pr :=
    fun h v hv => ⟨h v hv, hp_in⟩
  apply liftQ
  set e1 := setVarHOLFinite (ofString "b") (.val (.word B)) e with he1
  have hb1 : e1.locals.lookup (ofString "b") = some (.val (.word B)) := by
    simp [he1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hl1 : e1.locals.lookup (ofString "len") = some (.val (.word L)) := by
    simp [he1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "len" by decide, hl]
  have hc1 : e1.code = originalRuntimeCode := hcode
  refine R_branch (by rfl) (fun w hw hw0 => R_ret (fun v hv => ?_)) (fun w hw hw0 => ?_)
  · simp [evalHOLExact, evalListHOLExact] at hv
    subst hv
    refine ⟨0, 1, 0, rfl, by simp, ?_, fun hc => absurd rfl hc⟩
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    simp; omega
  have hL1 := toNat_sub_one L hL
  refine R_branch (by rfl) (fun w _ _ => R_dec (fun v hv _ => ?_)) (fun w _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact, hb1, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    set e2 := setVarHOLFinite (ofString "n") (.val (.word (B - 128#64))) e1 with he2
    have hc2 : e2.code = originalRuntimeCode := hcode
    refine R_guard hc2 (fun w hw hw0 => ?_)
    have hN : (B - 128#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, he2, lk_set, lk_set',
        show ofString "n" ≠ ofString "len" by decide, hl1, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
      subst hw0
      by_contra hc
      have : L - 1#64 < B - 128#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hw
    refine R_check2 hc2 (R_ret (fun v hv => ?_))
    simp [evalHOLExact, evalListHOLExact, he2, lk_set, lk_set'] at hv
    subst hv
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    refine ⟨1, B - 128#64, 0, rfl, by simp, ?_, fun _ => by rw [h1]⟩
    rw [h1]
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  refine R_branch (by rfl) (fun w _ _ => long_branch e1 hc1 L B 183#64 0#64 hL hl1 hb1) (fun w _ _ => ?_)
  refine R_branch (by rfl) (fun w _ _ => short_branch e1 hc1 L B 192#64 1#64 hL hl1 hb1) (fun w _ _ => ?_)
  exact long_branch e1 hc1 L B 247#64 1#64 hL hl1 hb1

theorem lookup_hdr' : originalRuntimeCode.lookup (ofString "rlp_item_header") =
    some ([(ofString "p", .one), (ofString "len", .one)],
      sourceFnBody Guest.Software.guestFn_rlp_item_header, hdrShape) :=
  lookup_of_guestAst_getElem 109 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_header) rfl

theorem callee_p_len {fname : MlS} {body0 : ProgHOL 64} {rs0 : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname =
      some ([(ofString "p", .one), (ofString "len", .one)], body0, rs0))
    (v1 v2 : ValueHOL 64) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup fname [v1, v2] =
      some (body, callee, rs)) :
    body = body0 ∧ callee.lookup (ofString "p") = some v1 ∧ callee.lookup (ofString "len") = some v2 := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · simp at hl
  · rename_i b cl r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    simp only [lookupCodeHOLExact, hlook] at heq
    split at heq
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine ⟨rfl, ?_, by simp⟩
      simp [List.zip, List.foldl, show ofString "p" ≠ ofString "len" by decide]
    · simp at heq

/-! ### `fb__rlp_validate_items_body` (`62209915858 = 2 * domainBytes + 2`) -/

namespace VibR10

def pop : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
    (.assign .local (ofString "go") (.const 0))
    (.seq (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
      (.seq (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
        (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16])))))

def pushTail : ProgHOL 64 :=
  .seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
    (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
      (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
        (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
          (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
            (.assign .local (ofString "end") (.var .local (ofString "after")))))))

def push : ProgHOL 64 :=
  .decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24] pushTail

def cont : ProgHOL 64 :=
  .dec (ofString "payload") .one
    (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
    (.dec (ofString "after") .one
      (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))])
      (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
        push
        (.assign .local (ofString "pos") (.var .local (ofString "after")))))

def item : ProgHOL 64 :=
  .decCall (ofString "h") hdrShape (ofString "rlp_item_header")
    [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]]
    cont

def body : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end"))) pop item

def cond : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "go")) (.const 0)

def bodyK : Nat := Nat.max 0 ((K.«rlp_item_header» + 1) + Nat.max (K.«scratch_alloc» + 1) 0)

theorem body_bound : TerminatingProgBoundedOn GuestInv body bodyK := by
  apply TerminatingProgBoundedOn.weaken'
  · unfold body pop item cont push pushTail hdrShape
    dsimp only [InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map]
    fb_auto
  · unfold bodyK
    simp only [Nat.max_def, max_def]
    split_ifs <;> omega

/-- Scratch-stack representation: `StackAt mem sp top stk` holds when `stk` is a linked list of
24-byte records `[after, end_, prev]` in `[sp, heapEnd)` with each record strictly below its `prev`. -/
inductive StackAt (mem : BitVec 64 → HolWordLab 64) :
    Nat → BitVec 64 → List (BitVec 64 × BitVec 64) → Prop where
  | nil (sp : Nat) : StackAt mem sp 0 []
  | cons {sp : Nat} {top prev a e : BitVec 64} {rest : List (BitVec 64 × BitVec 64)}
      (hnz : top ≠ 0)
      (hsp : sp ≤ top.toNat)
      (hhi : top.toNat + 24 ≤ heapEnd)
      (hm0 : mem top = .word a)
      (hm8 : mem (top + 8#64) = .word e)
      (hm16 : mem (top + 16#64) = .word prev)
      (htail : StackAt mem (top.toNat + 24) prev rest) :
      StackAt mem sp top ((a, e) :: rest)

theorem stackAt_mono {mem : BitVec 64 → HolWordLab 64} {sp1 sp2 : Nat}
    {top : BitVec 64} {stk : List (BitVec 64 × BitVec 64)}
    (hle : sp1 ≤ sp2) (h : StackAt mem sp2 top stk) : StackAt mem sp1 top stk := by
  cases h with
  | nil _ => exact .nil sp1
  | cons hnz hsp hhi hm0 hm8 hm16 htail =>
    exact .cons hnz (Nat.le_trans hle hsp) hhi hm0 hm8 hm16 htail

theorem stackAt_congr {mem1 mem2 : BitVec 64 → HolWordLab 64} {sp : Nat}
    {top : BitVec 64} {stk : List (BitVec 64 × BitVec 64)}
    (h : StackAt mem1 sp top stk)
    (heq : ∀ w : BitVec 64, sp ≤ w.toNat → mem2 w = mem1 w) :
    StackAt mem2 sp top stk := by
  induction h with
  | nil sp => exact .nil sp
  | @cons sp top prev a e rest hnz hsp hhi hm0 hm8 hm16 _ ih =>
    have heH : heapEnd = 2701131776 + 8 * 3888119741 := by decide
    have h8 : (top + 8#64).toNat = top.toNat + 8 :=
      BitVec.toNat_add_of_lt (by simp; omega)
    have h16 : (top + 16#64).toNat = top.toNat + 16 :=
      BitVec.toNat_add_of_lt (by simp; omega)
    refine .cons hnz hsp hhi
      ((heq top hsp).trans hm0)
      ((heq (top + 8#64) (by omega)).trans hm8)
      ((heq (top + 16#64) (by omega)).trans hm16)
      (ih fun w hw => heq w (by omega))

theorem stackAt_unique {mem : BitVec 64 → HolWordLab 64} {top : BitVec 64}
    {sp1 sp2 : Nat} {stk1 stk2 : List (BitVec 64 × BitVec 64)}
    (h1 : StackAt mem sp1 top stk1) (h2 : StackAt mem sp2 top stk2) : stk1 = stk2 := by
  induction h1 generalizing sp2 stk2 with
  | nil _ =>
    cases h2 with
    | nil _ => rfl
    | cons hnz _ _ _ _ _ _ => exact absurd rfl hnz
  | cons hnz _ _ hm0 hm8 hm16 _ ih =>
    cases h2 with
    | nil _ => exact absurd rfl hnz
    | cons _ _ _ hm0' hm8' hm16' htail' =>
      have ha : _ = _ := hm0.symm.trans hm0'; injection ha with ha
      have he : _ = _ := hm8.symm.trans hm8'; injection he with he
      have hp : _ = _ := hm16.symm.trans hm16'; injection hp with hp
      subst ha; subst he; subst hp
      exact congrArg _ (ih htail')

theorem hdrGood_ro : ∀ function, (function == ofString "rlp_fail" || function == ofString "rlp_read_length") = true →
    ∀ values body callee rs,
    PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
      some (body, callee, rs) →
    roProg (fun f => f == ofString "rlp_fail" || f == ofString "rlp_read_length") body = true := by
  intro function hf values body callee rs hl
  simp only [Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 105 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_fail) rfl) hl
    subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 106 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_read_length) rfl) hl
    subst hb; rfl

theorem hdr_body_ro : ∀ values body callee rs,
    PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_item_header")
      values = some (body, callee, rs) →
    roProg (fun f => f == ofString "rlp_fail" || f == ofString "rlp_read_length") body = true := by
  intro values body callee rs hl
  have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
    (lookup_of_guestAst_getElem 109 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_rlp_item_header) rfl) hl
  subst hb; rfl

theorem evaluate_scratch_alloc_24 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (hcode : state.code = originalRuntimeCode)
    (hn : state.locals.lookup (ofString "n") = some (.val (.word 24)))
    (retVal : ValueHOL 64)
    (hret : (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)).1 =
      some (.returned retVal)) :
    ∃ p f q : BitVec 64,
      retVal = .val (.word q) ∧
      state.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)) ∧
      state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) ∧
      (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)).2.globals.lookup
        (ofString "scratch_ptr") = some (.val (.word q)) ∧
      (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)).2.memory = state.memory ∧
      f.toNat ≤ q.toNat ∧ ¬ ((p - f).toNat < 24) ∧ q = (p - 24) &&& ((0 : BitVec 64) - 8) := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_scratch_alloc =
      .dec (ofString "p") .one (.var .global (ofString "scratch_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const 7])
                .skip)
              (.seq
                (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q"))))))) := rfl
  have hret0 := hret
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  rcases hsp : state.globals.lookup (ofString "scratch_ptr") with _ | ⟨⟨p⟩⟩ | _ | _ <;>
    try (simp [evalHOLExact, hsp, shapeEqHOL, shapeOfHOLExact] at hret; done)
  have hpe : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "scratch_ptr")) = some (.val (.word p)) := hsp
  rw [hpe] at hret; simp only [shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hret
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word 24)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "n" by decide, hn]
  rcases hfmp : state.globals.lookup (ofString "frame_mem_ptr") with _ | ⟨⟨f⟩⟩ | fs | ⟨nm, fs⟩
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
    simp [evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, fixClockHOLFinite, hfmp] at hret
  swap
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
    simp [evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, fixClockHOLFinite, hfmp, valueIsWord] at hret
  swap
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
    simp [evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, fixClockHOLFinite, hfmp, valueIsWord] at hret
  -- Now both `p` and `f` are words!
  have hf_g : pState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) := hfmp
  have hev1 : @evalHOLExact 64 F _ pState.toExact (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (p - f).toNat < 24 then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc, hf_g,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  have proj_eq :
      let inner := evaluateHOLFiniteState pState
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const 7])
                .skip)
              (.seq
                (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q")))))))
      (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)).1 = inner.1 ∧
      (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)).2.globals = inner.2.globals ∧
      (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)).2.memory = inner.2.memory := by
    dsimp only [pState]
    refine ⟨?_, ?_, ?_⟩
    · conv_lhs => rw [hbody_eq, evaluateHOLFiniteState_dec_total]
      dsimp only; rw [hpe]; simp [shapeEqHOL, shapeOfHOLExact]
    · conv_lhs => rw [hbody_eq, evaluateHOLFiniteState_dec_total]
      dsimp only; rw [hpe]; simp [shapeEqHOL, shapeOfHOLExact]
    · conv_lhs => rw [hbody_eq, evaluateHOLFiniteState_dec_total]
      dsimp only; rw [hpe]; simp [shapeEqHOL, shapeOfHOLExact]
  obtain ⟨hp1, hpg, hpm⟩ := proj_eq
  rw [hp1] at hret0
  rw [hpg, hpm]
  rw [evaluateHOLFiniteState_seq_line780] at hret0 ⊢
  by_cases hcmp1 : (p - f).toNat < 24
  · rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1] at hret0
    dsimp only at hret0
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0)] at hret0
    have hno_none := evaluate_call_trap_with_no_none pState 7 hcode
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 7 w hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret hret0
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => exact absurd hret0 (hno_ret retVal)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 7])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1] at hret0 ⊢; dsimp only at hret0 ⊢
    let q : BitVec 64 := (p - 24) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
        ↓reduceIte, List.foldr]
      simp [q]
      rw [show AndOp.and (18446744073709551608#64) (18446744073709551615#64) = (18446744073709551608#64)
        by decide]
      rfl
    rw [evaluateHOLFiniteState_dec_total] at hret0 ⊢; dsimp only at hret0 ⊢
    rw [hq_eval] at hret0 ⊢; simp only [shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hret0 ⊢
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hf_q : qState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) := hfmp
    have hev2 : @evalHOLExact 64 F _ qState.toExact (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr"))) =
        some (.val (.word (if q.toNat < f.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, hf_q, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
        decide_eq_true_eq]
    rw [evaluateHOLFiniteState_seq_line780] at hret0 ⊢
    by_cases hcmp2 : q.toNat < f.toNat
    · rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2] at hret0
      dsimp only at hret0
      rw [if_neg (by decide : (1 : BitVec 64) ≠ 0)] at hret0
      have hno_none := evaluate_call_trap_with_no_none qState 7 hcode
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 7 w hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret hret0
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => exact absurd hret0 (hno_ret retVal)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2] at hret0 ⊢; dsimp only at hret0 ⊢
      have hp_gq : qState.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)) := hsp
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "q")))) =
          (some (.returned (.val (.word q))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, isValidValueHOLExact, lookupKvarHOLExact, hp_gq,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return]
      rw [heval_end] at hret0 ⊢; dsimp only at hret0 ⊢
      injection hret0 with hr; injection hr with hr'
      refine ⟨p, f, q, hr'.symm, rfl, rfl, ?_, rfl, by omega, hcmp1, rfl⟩
      simp [emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem lookup_scratch_alloc : originalRuntimeCode.lookup (ofString "scratch_alloc") =
    some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_scratch_alloc, .one) :=
  lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_alloc) rfl

theorem sa_callee (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "scratch_alloc")
      [.val (.word 24)] = some (body, callee, rs)) :
    body = sourceFnBody Guest.Software.guestFn_scratch_alloc ∧
      callee.lookup (ofString "n") = some (.val (.word 24)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · simp at hl
  · rename_i b cl r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    simp [lookupCodeHOLExact, lookup_scratch_alloc, shapeEqHOL, shapeOfHOLExact] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp

theorem store_word_eval {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : GuestInv s)
    (dst val : ExpHOL 64) (addr w : BitVec 64)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dst =
      some (.val (.word addr)))
    (hval : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) val =
      some (.val (.word w)))
    (hnone : (evaluateHOLFiniteState s (.store dst val)).1 = none) :
    sourceBase ≤ addr.toNat ∧ addr.toNat + 8 ≤ heapEnd ∧
    (evaluateHOLFiniteState s (.store dst val)).2.locals = s.locals ∧
    (evaluateHOLFiniteState s (.store dst val)).2.globals = s.globals ∧
    (evaluateHOLFiniteState s (.store dst val)).2.memory addr = .word w ∧
    (∀ x : BitVec 64, x ≠ addr →
      (evaluateHOLFiniteState s (.store dst val)).2.memory x = s.memory x) := by
  revert hnone
  rw [evaluateHOLFiniteState_store, hdst]
  dsimp only
  rw [hval]
  dsimp only
  split
  · rename_i mem hmem
    intro _
    dsimp only
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
    by_cases hdom : s.memaddrs addr
    · simp only [hdom, ↓reduceIte, Option.some.injEq] at hmem
      subst hmem
      have hmad : s.memaddrs = ordinaryDomain := hP.memaddrs
      have hbnd := ordinaryDomain_bounds addr (hmad ▸ hdom)
      refine ⟨hbnd.1, hbnd.2, rfl, rfl, ?_, fun x hx => ?_⟩
      · simp [FUPDATE]
      · simp [FUPDATE, hx]
    · simp [hdom] at hmem
  · simp

theorem pushTail_eval {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : GuestInv s)
    (q aft end_ top pay : BitVec 64)
    (hrec : s.locals.lookup (ofString "rec") = some (.val (.word q)))
    (haft : s.locals.lookup (ofString "after") = some (.val (.word aft)))
    (hend : s.locals.lookup (ofString "end") = some (.val (.word end_)))
    (htop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (hpay : s.locals.lookup (ofString "payload") = some (.val (.word pay)))
    (hnone : (evaluateHOLFiniteState s pushTail).1 = none) :
    let out := (evaluateHOLFiniteState s pushTail).2
    sourceBase ≤ q.toNat ∧ q.toNat + 24 ≤ heapEnd ∧ q ≠ 0 ∧
    out.globals = s.globals ∧
    out.locals.lookup (ofString "top") = some (.val (.word q)) ∧
    out.locals.lookup (ofString "pos") = some (.val (.word pay)) ∧
    out.locals.lookup (ofString "end") = some (.val (.word aft)) ∧
    out.locals.lookup (ofString "go") = s.locals.lookup (ofString "go") ∧
    out.memory q = .word aft ∧
    out.memory (q + 8#64) = .word end_ ∧
    out.memory (q + 16#64) = .word top ∧
    (∀ w : BitVec 64, q.toNat + 24 ≤ w.toNat → out.memory w = s.memory w) := by
  dsimp only
  unfold pushTail at hnone ⊢
  -- Step 1: `store rec after`
  rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
  rcases hr1 : evaluateHOLFiniteState s (.store (.var .local (ofString "rec")) (.var .local (ofString "after"))) with ⟨r1, s1⟩
  simp only [hr1] at hnone ⊢
  cases r1 with | some _ => simp at hnone | none =>
  dsimp only at hnone ⊢
  have hs1_inv : GuestInv s1 := by
    have h := guestInv_evaluate s (.store (.var .local (ofString "rec")) (.var .local (ofString "after"))) hP
    rwa [hr1] at h
  obtain ⟨hq_lo, hq8_hi, hs1_loc, hs1_glob, hs1_mq, hs1_moth⟩ := store_word_eval s hP
    (.var .local (ofString "rec")) (.var .local (ofString "after")) q aft
    hrec haft (by rw [hr1])
  rw [hr1] at hs1_loc hs1_glob hs1_mq hs1_moth; dsimp only at hs1_loc hs1_glob hs1_mq hs1_moth
  -- Step 2: `store (rec + 8) end`
  rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
  rcases hr2 : evaluateHOLFiniteState s1 (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end"))) with ⟨r2, s2⟩
  simp only [hr2] at hnone ⊢
  cases r2 with | some _ => simp at hnone | none =>
  dsimp only at hnone ⊢
  have hs2_inv : GuestInv s2 := by
    have h := guestInv_evaluate s1 (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end"))) hs1_inv
    rwa [hr2] at h
  have hd2 : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.op .add [.var .local (ofString "rec"), .const 8]) = some (.val (.word (q + 8#64))) := by
    simp [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hs1_loc, hrec,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  have hv2 : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.var .local (ofString "end")) = some (.val (.word end_)) := by
    simp [evalHOLExact, PanSemStateFiniteExact.toExact, hs1_loc, hend]
  obtain ⟨_, hq16_hi, hs2_loc, hs2_glob, hs2_mq8, hs2_moth⟩ := store_word_eval s1 hs1_inv
    (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")) (q + 8#64) end_
    hd2 hv2 (by rw [hr2])
  rw [hr2] at hs2_loc hs2_glob hs2_mq8 hs2_moth; dsimp only at hs2_loc hs2_glob hs2_mq8 hs2_moth
  -- Step 3: `store (rec + 16) top`
  rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
  rcases hr3 : evaluateHOLFiniteState s2 (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top"))) with ⟨r3, s3⟩
  simp only [hr3] at hnone ⊢
  cases r3 with | some _ => simp at hnone | none =>
  dsimp only at hnone ⊢
  have hd3 : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
      (.op .add [.var .local (ofString "rec"), .const 16]) = some (.val (.word (q + 16#64))) := by
    simp [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hs2_loc, hs1_loc, hrec,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  have hv3 : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
      (.var .local (ofString "top")) = some (.val (.word top)) := by
    simp [evalHOLExact, PanSemStateFiniteExact.toExact, hs2_loc, hs1_loc, htop]
  obtain ⟨_, hq24_hi, hs3_loc, hs3_glob, hs3_mq16, hs3_moth⟩ := store_word_eval s2 hs2_inv
    (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")) (q + 16#64) top
    hd3 hv3 (by rw [hr3])
  rw [hr3] at hs3_loc hs3_glob hs3_mq16 hs3_moth; dsimp only at hs3_loc hs3_glob hs3_mq16 hs3_moth
  -- Step 4-6: three local assignments `top := rec; pos := payload; end := after` (read-only!)
  let asg3 : ProgHOL 64 :=
    .seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
      (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
        (.assign .local (ofString "end") (.var .local (ofString "after"))))
  -- Evaluate `asg3` on `s3`:
  have hasg3 : ∃ s6 : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s3 asg3 = (none, s6) ∧
      s6.globals = s3.globals ∧ s6.memory = s3.memory ∧
      s6.locals.lookup (ofString "top") = some (.val (.word q)) ∧
      s6.locals.lookup (ofString "pos") = some (.val (.word pay)) ∧
      s6.locals.lookup (ofString "end") = some (.val (.word aft)) ∧
      s6.locals.lookup (ofString "go") = s3.locals.lookup (ofString "go") := by
    change (evaluateHOLFiniteState s3 asg3).1 = none at hnone
    dsimp only [asg3] at hnone ⊢
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnone ⊢
    have he1 : @evalHOLExact 64 F _ s3.toExact (fun x => Classical.propDecidable (s3.memaddrs x))
        (.var .local (ofString "rec")) = some (.val (.word q)) := by
      simp [evalHOLExact, PanSemStateFiniteExact.toExact, hs3_loc, hs2_loc, hs1_loc, hrec]
    have hvld1 : isValidValueHOLFinite s3 .local (ofString "top") (.val (.word q)) = true := by
      simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact,
        PanSemStateFiniteExact.toExact, hs3_loc, hs2_loc, hs1_loc, htop, shapeOfHOLExact, shapeEqHOL]
    rw [he1] at hnone ⊢; dsimp only at hnone ⊢
    rw [if_pos hvld1] at hnone ⊢; dsimp only at hnone ⊢
    set s4 := setKvarHOLFinite .local (ofString "top") (.val (.word q)) s3
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnone ⊢
    have he2 : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
        (.var .local (ofString "payload")) = some (.val (.word pay)) := by
      simp [evalHOLExact, PanSemStateFiniteExact.toExact, s4, setKvarHOLFinite, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, show ofString "top" ≠ ofString "payload" by decide,
        hs3_loc, hs2_loc, hs1_loc, hpay]
    rw [he2] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hvld2 : isValidValueHOLFinite s4 .local (ofString "pos") (.val (.word pay)) = true
    swap; · rw [if_neg hvld2] at hnone; simp at hnone
    rw [if_pos hvld2] at hnone ⊢; dsimp only at hnone ⊢
    set s5 := setKvarHOLFinite .local (ofString "pos") (.val (.word pay)) s4
    rw [evaluateHOLFiniteState_assign] at hnone ⊢
    have he3 : @evalHOLExact 64 F _ s5.toExact (fun x => Classical.propDecidable (s5.memaddrs x))
        (.var .local (ofString "after")) = some (.val (.word aft)) := by
      simp [evalHOLExact, PanSemStateFiniteExact.toExact, s5, s4, setKvarHOLFinite, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, show ofString "pos" ≠ ofString "after" by decide,
        show ofString "top" ≠ ofString "after" by decide, hs3_loc, hs2_loc, hs1_loc, haft]
    rw [he3] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hvld3 : isValidValueHOLFinite s5 .local (ofString "end") (.val (.word aft)) = true
    swap; · rw [if_neg hvld3] at hnone; simp at hnone
    rw [if_pos hvld3]
    refine ⟨_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [s5, s4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "end" ≠ ofString "top" by decide, show ofString "pos" ≠ ofString "top" by decide]
    · simp [s5, s4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "end" ≠ ofString "pos" by decide]
    · simp [s5, s4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [s5, s4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "end" ≠ ofString "go" by decide, show ofString "pos" ≠ ofString "go" by decide,
        show ofString "top" ≠ ofString "go" by decide]
  obtain ⟨s6, hs6, hs6_glob, hs6_mem, hs6_top, hs6_pos, hs6_end, hs6_go⟩ := hasg3
  dsimp only [asg3] at hs6
  rw [hs6]
  dsimp only
  have heS : sourceBase = 2701131776 := by decide
  have heH : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  have hq8_nat : (q + 8#64).toNat = q.toNat + 8 := BitVec.toNat_add_of_lt (by simp; omega)
  have hq16_nat : (q + 16#64).toNat = q.toNat + 16 := BitVec.toNat_add_of_lt (by simp; omega)
  have hq_nz : q ≠ 0 := by intro h0; subst h0; simp at hq_lo; omega
  have hne_0_8 : q ≠ q + 8#64 := fun h => by have := congrArg BitVec.toNat h; omega
  have hne_0_16 : q ≠ q + 16#64 := fun h => by have := congrArg BitVec.toNat h; omega
  have hne_8_16 : q + 8#64 ≠ q + 16#64 := fun h => by have := congrArg BitVec.toNat h; omega
  refine ⟨hq_lo, by omega, hq_nz,
    hs6_glob.trans (hs3_glob.trans (hs2_glob.trans hs1_glob)),
    hs6_top, hs6_pos, hs6_end,
    hs6_go.trans (by rw [hs3_loc, hs2_loc, hs1_loc]),
    by rw [hs6_mem, hs3_moth _ hne_0_16, hs2_moth _ hne_0_8, hs1_mq],
    by rw [hs6_mem, hs3_moth _ hne_8_16, hs2_mq8],
    by rw [hs6_mem, hs3_mq16],
    fun w hw => ?_⟩
  have hw0 : w ≠ q := fun h => by subst h; omega
  have hw8 : w ≠ q + 8#64 := fun h => by subst h; omega
  have hw16 : w ≠ q + 16#64 := fun h => by subst h; omega
  rw [hs6_mem, hs3_moth w hw16, hs2_moth w hw8, hs1_moth w hw0]

/-- `push` calls `scratch_alloc(24)` and then runs `pushTail`: allocates `q < p` with `q + 24 ≤ p`
(since `store rec after` proves `q >= sourceBase >= 24`, ruling out unsigned underflow of `p - 24`!)
and pushes `(aft, end_)` onto the scratch stack! -/
theorem push_eval {F : Type} (u : PanSemStateFiniteExact 64 F)
    (hcode : u.code = originalRuntimeCode) (hP : GuestInv u)
    (aft end_ top pay : BitVec 64)
    (haft : u.locals.lookup (ofString "after") = some (.val (.word aft)))
    (hend : u.locals.lookup (ofString "end") = some (.val (.word end_)))
    (htop : u.locals.lookup (ofString "top") = some (.val (.word top)))
    (hpay : u.locals.lookup (ofString "payload") = some (.val (.word pay)))
    (hnone : (evaluateHOLFiniteState u push).1 = none) :
    let out := (evaluateHOLFiniteState u push).2
    ∃ p q : BitVec 64,
      u.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)) ∧
      out.globals.lookup (ofString "scratch_ptr") = some (.val (.word q)) ∧
      q.toNat + 24 ≤ p.toNat ∧ q.toNat + 24 ≤ heapEnd ∧ q ≠ 0 ∧
      out.locals.lookup (ofString "top") = some (.val (.word q)) ∧
      out.locals.lookup (ofString "pos") = some (.val (.word pay)) ∧
      out.locals.lookup (ofString "end") = some (.val (.word aft)) ∧
      out.locals.lookup (ofString "go") = u.locals.lookup (ofString "go") ∧
      out.memory q = .word aft ∧
      out.memory (q + 8#64) = .word end_ ∧
      out.memory (q + 16#64) = .word top ∧
      (∀ w : BitVec 64, q.toNat + 24 ≤ w.toNat → out.memory w = u.memory w) := by
  dsimp only
  unfold push at hnone ⊢
  revert hnone
  rw [evaluateHOLFiniteState_decCall_total]
  have hargs : evalListHOLFinite u (h := fun address => Classical.propDecidable (u.memaddrs address))
      [ExpHOL.const (24 : BitVec 64)] = some [.val (.word 24#64)] := by
    simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact]
  simp only [hargs]
  rcases hl : lookupCodeHOLFinite u.code.lookup (ofString "scratch_alloc") [.val (.word 24#64)] with
    _ | ⟨body, callee, rs⟩
  · simp
  dsimp only
  have hl' := hl; rw [hcode] at hl'
  obtain ⟨rfl, hn⟩ := sa_callee body callee rs hl'
  split
  · simp
  have hst_inv : GuestInv (evaluateHOLFiniteState (callEntryStateHOLFinite u callee)
      (sourceFnBody Guest.Software.guestFn_scratch_alloc)).2 :=
    guestInv_evaluate _ _ (guestInv_callEntry u callee hP)
  rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite u callee)
      (sourceFnBody Guest.Software.guestFn_scratch_alloc) with ⟨r, st⟩
  rw [hrun] at hst_inv
  simp only [hrun]
  cases r with
  | none => simp
  | some rr =>
    cases rr with
    | returned v =>
      dsimp only
      split
      · intro hnone_tail
        obtain ⟨p, f, q, rfl, hp, hf, hq_sp, hst_mem, hfq, hcmp1, hq_def⟩ :=
          evaluate_scratch_alloc_24 (callEntryStateHOLFinite u callee) hcode hn v (by rw [hrun])
        rw [hrun] at hq_sp hst_mem; dsimp only at hq_sp hst_mem
        set cState := setVarHOLFinite (ofString "rec") (.val (.word q))
          { (fixClockHOLFinite (callEntryStateHOLFinite u callee)
              (some (PanSemResultExact.returned (.val (.word q))), st)).2 with locals := u.locals }
        have hc_inv : GuestInv cState :=
          guestInv_setVar _ _ _ (guestInv_with_locals_clock st u.locals _ hst_inv)
        have hc_rec : cState.locals.lookup (ofString "rec") = some (.val (.word q)) := by
          simp [cState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hc_aft : cState.locals.lookup (ofString "after") = some (.val (.word aft)) := by
          simp [cState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rec" ≠ ofString "after" by decide, haft]
        have hc_end : cState.locals.lookup (ofString "end") = some (.val (.word end_)) := by
          simp [cState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rec" ≠ ofString "end" by decide, hend]
        have hc_top : cState.locals.lookup (ofString "top") = some (.val (.word top)) := by
          simp [cState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rec" ≠ ofString "top" by decide, htop]
        have hc_pay : cState.locals.lookup (ofString "payload") = some (.val (.word pay)) := by
          simp [cState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rec" ≠ ofString "payload" by decide, hpay]
        obtain ⟨hq_lo, hq24_hi, hq_nz, hout_glob, hout_top, hout_pos, hout_end, hout_go,
            hout_m0, hout_m8, hout_m16, hout_moth⟩ :=
          pushTail_eval cState hc_inv q aft end_ top pay hc_rec hc_aft hc_end hc_top hc_pay hnone_tail
        -- Prove `q.toNat + 24 ≤ p.toNat` WITHOUT wrapping!
        have hq_le_p : q.toNat + 24 ≤ p.toNat := by
          have hand := and_neg8_toNat (p - 24)
          rw [← hq_def] at hand
          by_cases hp24 : 24 ≤ p.toNat
          · have hsub : (p - 24).toNat = p.toNat - 24 := by
              rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
              simp
            omega
          · -- Impossible! If `p.toNat < 24`, then `(p - 24).toNat = 2^64 + p.toNat - 24 >= 2^64 - 24`,
            -- so `q.toNat >= 2^64 - 31 > heapEnd`, contradicting `hq24_hi`!
            have hsub : (p - 24).toNat = 2 ^ 64 + p.toNat - 24 := by
              have := p.isLt; rw [BitVec.toNat_sub]; simp; omega
            have heH : heapEnd = 2701131776 + 8 * 3888119741 := by decide
            have hdiv : (2 ^ 64 + p.toNat - 24) / 8 * 8 ≥ 2 ^ 64 - 32 := by omega
            omega
        dsimp only
        refine ⟨p, q, hp, ?_, hq_le_p, hq24_hi, hq_nz, ?_, ?_, ?_, ?_, hout_m0, hout_m8, hout_m16, ?_⟩
        · change (evaluateHOLFiniteState cState pushTail).2.globals.lookup (ofString "scratch_ptr") = _
          rw [hout_glob]; simpa [cState, setVarHOLFinite, fixClockHOLFinite] using hq_sp
        · change ((evaluateHOLFiniteState cState pushTail).2.locals.resVarEq
            (ofString "rec", u.locals.lookup (ofString "rec"))).lookup (ofString "top") = _
          rw [PanRunBounded.resVarEq_lookup, if_neg (by decide : ofString "top" ≠ ofString "rec"), hout_top]
        · change ((evaluateHOLFiniteState cState pushTail).2.locals.resVarEq
            (ofString "rec", u.locals.lookup (ofString "rec"))).lookup (ofString "pos") = _
          rw [PanRunBounded.resVarEq_lookup, if_neg (by decide : ofString "pos" ≠ ofString "rec"), hout_pos]
        · change ((evaluateHOLFiniteState cState pushTail).2.locals.resVarEq
            (ofString "rec", u.locals.lookup (ofString "rec"))).lookup (ofString "end") = _
          rw [PanRunBounded.resVarEq_lookup, if_neg (by decide : ofString "end" ≠ ofString "rec"), hout_end]
        · change ((evaluateHOLFiniteState cState pushTail).2.locals.resVarEq
            (ofString "rec", u.locals.lookup (ofString "rec"))).lookup (ofString "go") = _
          rw [PanRunBounded.resVarEq_lookup, if_neg (by decide : ofString "go" ≠ ofString "rec"), hout_go]
          simp [cState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rec" ≠ ofString "go" by decide]
        · intro w hw
          change (evaluateHOLFiniteState cState pushTail).2.memory w = u.memory w
          rw [hout_moth w hw]
          have hm : cState.memory = st.memory := rfl
          rw [hm, hst_mem]; rfl
      · simp
    | _ => simp

theorem pop_eval {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : GuestInv s)
    (top pos end_ : BitVec 64)
    (htop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (hpos : s.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (hend : s.locals.lookup (ofString "end") = some (.val (.word end_)))
    (hnone : (evaluateHOLFiniteState s pop).1 = none) :
    let out := (evaluateHOLFiniteState s pop).2
    if top = 0 then
      out.globals = s.globals ∧ out.memory = s.memory ∧
      out.locals.lookup (ofString "go") = some (.val (.word 0)) ∧
      out.locals.lookup (ofString "pos") = some (.val (.word pos)) ∧
      out.locals.lookup (ofString "end") = some (.val (.word end_)) ∧
      out.locals.lookup (ofString "top") = some (.val (.word 0))
    else
      ∀ a e prev : BitVec 64,
        top.toNat + 24 ≤ heapEnd →
        s.memory top = .word a →
        s.memory (top + 8#64) = .word e →
        s.memory (top + 16#64) = .word prev →
        out.globals = s.globals ∧ out.memory = s.memory ∧
        out.locals.lookup (ofString "go") = s.locals.lookup (ofString "go") ∧
        out.locals.lookup (ofString "pos") = some (.val (.word a)) ∧
        out.locals.lookup (ofString "end") = some (.val (.word e)) ∧
        out.locals.lookup (ofString "top") = some (.val (.word prev)) := by
  dsimp only
  unfold pop at hnone ⊢
  rw [evaluateHOLFiniteState_ite] at hnone ⊢
  have hcmp : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.cmp .equal (.var .local (ofString "top")) (.const 0)) =
      some (.val (.word (if top = 0 then 1 else 0))) := by
    by_cases h0 : top = 0 <;> simp [evalHOLExact, htop, Compiler.Encoders.Asm.wordCmpHOL, h0]
  rw [hcmp] at hnone ⊢; dsimp only at hnone ⊢
  by_cases h0 : top = 0
  · subst h0
    simp only [↓reduceIte, show (1 : BitVec 64) ≠ 0 by decide] at hnone ⊢
    rw [evaluateHOLFiniteState_assign] at hnone ⊢
    have he0 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
        (.const 0) = some (.val (.word 0)) := rfl
    rw [he0] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hv : isValidValueHOLFinite s .local (ofString "go") (.val (.word 0)) = true
    swap; · rw [if_neg hv] at hnone; simp at hnone
    rw [if_pos hv]
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "pos" by decide, hpos]
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "end" by decide, hend]
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "top" by decide, htop]
  · simp only [if_neg h0, ↓reduceIte] at hnone ⊢
    intro a e prev hhi hm0 hm8 hm16
    -- Step 1: `pos := load .one (top + 0)`
    rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
    rcases hr1 : evaluateHOLFiniteState s (.assign .local (ofString "pos")
        (.load .one (.op .add [.var .local (ofString "top"), .const 0]))) with ⟨r1, s1⟩
    simp only [hr1] at hnone ⊢
    cases r1 with | some _ => simp at hnone | none =>
    dsimp only at hnone ⊢
    have hload_val : ∀ (st : PanSemStateFiniteExact 64 F) (off w : BitVec 64),
        st.structs = s.structs → st.memaddrs = s.memaddrs → st.memory = s.memory →
        st.locals.lookup (ofString "top") = some (.val (.word top)) →
        s.memory (top + off) = .word w →
        ∀ v, @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x))
            (.load .one (.op .add [.var .local (ofString "top"), .const off])) = some v →
          v = .val (.word w) := by
      intro st off w hst hma hme htl hmw v hev
      have had : @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x))
          (.op .add [.var .local (ofString "top"), .const off]) = some (.val (.word (top + off))) := by
        simp [evalHOLExact, evalListHOLExact, htl, wordOpHOL, wordOp, valueIsWord, valueWord]
      rw [evalHOLExact, had] at hev; dsimp only at hev
      split at hev
      · simp only [memLoadHOLExact, PanSemStateFiniteExact.toExact, hme, hmw] at hev
        split at hev
        · exact (Option.some.inj hev).symm
        · simp at hev
      · simp at hev
    have hs1_eq : s1 = setKvarHOLFinite .local (ofString "pos") (.val (.word a)) s := by
      rw [evaluateHOLFiniteState_assign] at hr1
      rcases he1 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
          (.load .one (.op .add [.var .local (ofString "top"), .const 0])) with _ | v1
      · rw [he1] at hr1; simp at hr1
      · have hv1 := hload_val s 0 a rfl rfl rfl htop (by simpa using hm0) v1 he1
        subst hv1
        rw [he1] at hr1; dsimp only at hr1
        by_cases hv : isValidValueHOLFinite s .local (ofString "pos") (.val (.word a)) = true
        · rw [if_pos hv] at hr1; exact (Prod.mk.inj hr1).2.symm
        · rw [if_neg hv] at hr1; simp at hr1
    subst hs1_eq
    -- Step 2: `end := load .one (top + 8)`
    rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
    set s1 := setKvarHOLFinite .local (ofString "pos") (.val (.word a)) s
    rcases hr2 : evaluateHOLFiniteState s1 (.assign .local (ofString "end")
        (.load .one (.op .add [.var .local (ofString "top"), .const 8]))) with ⟨r2, s2⟩
    simp only [hr2] at hnone ⊢
    cases r2 with | some _ => simp at hnone | none =>
    dsimp only at hnone ⊢
    have hs1_top : s1.locals.lookup (ofString "top") = some (.val (.word top)) := by
      simp [s1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "pos" ≠ ofString "top" by decide, htop]
    have hs2_eq : s2 = setKvarHOLFinite .local (ofString "end") (.val (.word e)) s1 := by
      rw [evaluateHOLFiniteState_assign] at hr2
      rcases he2 : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
          (.load .one (.op .add [.var .local (ofString "top"), .const 8])) with _ | v2
      · rw [he2] at hr2; simp at hr2
      · have hv2 := hload_val s1 8#64 e rfl rfl rfl hs1_top hm8 v2 he2
        subst hv2
        rw [he2] at hr2; dsimp only at hr2
        by_cases hv : isValidValueHOLFinite s1 .local (ofString "end") (.val (.word e)) = true
        · rw [if_pos hv] at hr2; exact (Prod.mk.inj hr2).2.symm
        · rw [if_neg hv] at hr2; simp at hr2
    subst hs2_eq
    -- Step 3: `top := load .one (top + 16)`
    set s2 := setKvarHOLFinite .local (ofString "end") (.val (.word e)) s1
    rcases hr3 : evaluateHOLFiniteState s2 (.assign .local (ofString "top")
        (.load .one (.op .add [.var .local (ofString "top"), .const 16]))) with ⟨r3, s3⟩
    simp only [s2, hr3] at hnone ⊢
    cases r3 with | some _ => simp at hnone | none =>
    have hs2_top : s2.locals.lookup (ofString "top") = some (.val (.word top)) := by
      simp [s2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "end" ≠ ofString "top" by decide, hs1_top]
    have hs3_eq : s3 = setKvarHOLFinite .local (ofString "top") (.val (.word prev)) s2 := by
      rw [evaluateHOLFiniteState_assign] at hr3
      rcases he3 : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
          (.load .one (.op .add [.var .local (ofString "top"), .const 16])) with _ | v3
      · rw [he3] at hr3; simp at hr3
      · have hv3 := hload_val s2 16#64 prev rfl rfl rfl hs2_top hm16 v3 he3
        subst hv3
        rw [he3] at hr3; dsimp only at hr3
        by_cases hv : isValidValueHOLFinite s2 .local (ofString "top") (.val (.word prev)) = true
        · rw [if_pos hv] at hr3; exact (Prod.mk.inj hr3).2.symm
        · rw [if_neg hv] at hr3; simp at hr3
    subst hs3_eq
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [s2, s1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "top" ≠ ofString "go" by decide, show ofString "end" ≠ ofString "go" by decide,
        show ofString "pos" ≠ ofString "go" by decide]
    · simp [s2, s1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "top" ≠ ofString "pos" by decide, show ofString "end" ≠ ofString "pos" by decide]
    · simp [s2, s1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "top" ≠ ofString "end" by decide]
    · simp [s2, s1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem hdr_value (v : ValueHOL 64) (h : shapeEqHOL (shapeOfHOLExact v) hdrShape = true) :
    ∃ a b c, v = hval a b c := by
  rcases v with ⟨⟨w⟩⟩ | fs | ⟨n, fs⟩
  · simp [shapeOfHOLExact, shapeEqHOL, hdrShape,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural] at h
  · rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, fs⟩⟩⟩⟩ <;>
      simp [shapeOfHOLExact, shapeEqHOL, hdrShape, shapeEqHOL.shapeEqListHOL,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural] at h
    obtain ⟨h0, h1, h2⟩ := h
    obtain ⟨a, rfl⟩ := shape_one_word f0 (by simpa [shapeEqHOL] using h0)
    obtain ⟨b, rfl⟩ := shape_one_word f1 (by simpa [shapeEqHOL] using h1)
    obtain ⟨c, rfl⟩ := shape_one_word f2 (by simpa [shapeEqHOL] using h2)
    exact ⟨a, b, c, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL, hdrShape,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural] at h

theorem item_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hP : GuestInv s)
    (pos end_ top : BitVec 64)
    (hpos : s.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (hend : s.locals.lookup (ofString "end") = some (.val (.word end_)))
    (htop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (hnone : (evaluateHOLFiniteState s item).1 = none) :
    let out := (evaluateHOLFiniteState s item).2
    ∃ a b c : BitVec 64,
      1 ≤ a.toNat + b.toNat ∧ a.toNat + b.toNat ≤ (end_ - pos).toNat ∧
      (c ≠ 0 → 1 ≤ a.toNat) ∧
      sourceBase ≤ pos.toNat ∧ pos.toNat < heapEnd ∧
      out.locals.lookup (ofString "go") = s.locals.lookup (ofString "go") ∧
      (c = 0 ∧ out.globals = s.globals ∧ out.memory = s.memory ∧
        out.locals.lookup (ofString "top") = some (.val (.word top)) ∧
        out.locals.lookup (ofString "pos") = some (.val (.word (pos + a + b))) ∧
        out.locals.lookup (ofString "end") = some (.val (.word end_)) ∨
       c ≠ 0 ∧ ∃ p q : BitVec 64,
        s.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)) ∧
        out.globals.lookup (ofString "scratch_ptr") = some (.val (.word q)) ∧
        q.toNat + 24 ≤ p.toNat ∧ q.toNat + 24 ≤ heapEnd ∧ q ≠ 0 ∧
        out.locals.lookup (ofString "top") = some (.val (.word q)) ∧
        out.locals.lookup (ofString "pos") = some (.val (.word (pos + a))) ∧
        out.locals.lookup (ofString "end") = some (.val (.word (pos + a + b))) ∧
        out.memory q = .word (pos + a + b) ∧
        out.memory (q + 8#64) = .word end_ ∧
        out.memory (q + 16#64) = .word top ∧
        (∀ w : BitVec 64, q.toNat + 24 ≤ w.toNat → out.memory w = s.memory w)) := by
  dsimp only
  unfold item at hnone ⊢
  revert hnone
  rw [evaluateHOLFiniteState_decCall_total]
  have hargs : evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address))
      [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]] =
      some [.val (.word pos), .val (.word (end_ - pos))] := by
    simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hpos, hend,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  simp only [hargs]
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "rlp_item_header")
      [.val (.word pos), .val (.word (end_ - pos))] with _ | ⟨fb, callee, rs⟩
  · simp
  dsimp only
  have hl' := hl; rw [hcode] at hl'
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len lookup_hdr' _ _ fb callee rs hl'
  have hro := hdr_body_ro _ _ callee rs hl'
  split
  · simp
  have hfr := evaluate_ro _ hdrGood_ro _ hro (callEntryStateHOLFinite s callee) hcode
  have hst_inv : GuestInv (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_rlp_item_header)).2 :=
    guestInv_evaluate _ _ (guestInv_callEntry s callee hP)
  have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_rlp_item_header)).1
  rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_rlp_item_header) with ⟨r, st⟩
  rw [hrun] at hfr hst_inv hmeta
  change st.code = s.code at hmeta
  simp only [hrun]
  cases r with
  | none => simp
  | some rr =>
    cases rr with
    | returned v =>
      dsimp only
      split
      · rename_i hsh
        intro hnone_cont
        simp only [Bool.and_eq_true] at hsh
        obtain ⟨⟨a, b, c, rfl, hab1, hab2, hca⟩, hpos_lo, hpos_hi⟩ :=
          hdr_post_dom (callEntryStateHOLFinite s callee) hcode (guestInv_callEntry s callee hP)
            pos (end_ - pos) hcp hcl v (by rw [hrun])
        set u := setVarHOLFinite (ofString "h") (hval a b c)
          { (fixClockHOLFinite (callEntryStateHOLFinite s callee)
              (some (PanSemResultExact.returned (hval a b c)), st)).2 with locals := s.locals }
        have hu_inv : GuestInv u :=
          guestInv_setVar _ _ _ (guestInv_with_locals_clock st s.locals _ hst_inv)
        have hu_code : u.code = originalRuntimeCode := hmeta.trans hcode
        have hu_mem : u.memory = s.memory := hfr.1
        have hu_glob : u.globals = s.globals := hfr.2.1
        -- Unfold `cont` = `dec payload (pos + h.0) (dec after (payload + h.1) (ite (h.2 != 0) push (pos := after)))`:
        unfold cont at hnone_cont ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnone_cont ⊢; dsimp only at hnone_cont ⊢
        have he_pay : @evalHOLExact 64 F _ u.toExact (fun x => Classical.propDecidable (u.memaddrs x))
            (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))]) =
            some (.val (.word (pos + a))) := by
          simp [evalHOLExact, evalListHOLExact, u, setVarHOLFinite, HolFiniteMapExact.lookup_update,
            FUPDATE, show ofString "h" ≠ ofString "pos" by decide, hpos, hval,
            wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [he_pay] at hnone_cont ⊢
        simp only [shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hnone_cont ⊢
        set u1 := setVarHOLFinite (ofString "payload") (.val (.word (pos + a))) u
        rw [evaluateHOLFiniteState_dec_total] at hnone_cont ⊢; dsimp only at hnone_cont ⊢
        have he_aft : @evalHOLExact 64 F _ u1.toExact (fun x => Classical.propDecidable (u1.memaddrs x))
            (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))]) =
            some (.val (.word (pos + a + b))) := by
          simp [evalHOLExact, evalListHOLExact, u1, u, setVarHOLFinite, HolFiniteMapExact.lookup_update,
            FUPDATE, show ofString "payload" ≠ ofString "h" by decide, hval,
            wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [he_aft] at hnone_cont ⊢
        simp only [shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hnone_cont ⊢
        set u2 := setVarHOLFinite (ofString "after") (.val (.word (pos + a + b))) u1
        have hu2_inv : GuestInv u2 := guestInv_setVar _ _ _ (guestInv_setVar _ _ _ hu_inv)
        have hu2_code : u2.code = originalRuntimeCode := hu_code
        have hu2_mem : u2.memory = s.memory := hu_mem
        have hu2_glob : u2.globals = s.globals := hu_glob
        have hu2_aft : u2.locals.lookup (ofString "after") = some (.val (.word (pos + a + b))) := by
          simp [u2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hu2_pay : u2.locals.lookup (ofString "payload") = some (.val (.word (pos + a))) := by
          simp [u2, u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "after" ≠ ofString "payload" by decide]
        have hu2_pos : u2.locals.lookup (ofString "pos") = some (.val (.word pos)) := by
          simp [u2, u1, u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "after" ≠ ofString "pos" by decide,
            show ofString "payload" ≠ ofString "pos" by decide,
            show ofString "h" ≠ ofString "pos" by decide, hpos]
        have hu2_end : u2.locals.lookup (ofString "end") = some (.val (.word end_)) := by
          simp [u2, u1, u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "after" ≠ ofString "end" by decide,
            show ofString "payload" ≠ ofString "end" by decide,
            show ofString "h" ≠ ofString "end" by decide, hend]
        have hu2_top : u2.locals.lookup (ofString "top") = some (.val (.word top)) := by
          simp [u2, u1, u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "after" ≠ ofString "top" by decide,
            show ofString "payload" ≠ ofString "top" by decide,
            show ofString "h" ≠ ofString "top" by decide, htop]
        have hu2_go : u2.locals.lookup (ofString "go") = s.locals.lookup (ofString "go") := by
          simp [u2, u1, u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "after" ≠ ofString "go" by decide,
            show ofString "payload" ≠ ofString "go" by decide,
            show ofString "h" ≠ ofString "go" by decide]
        have he_c : @evalHOLExact 64 F _ u2.toExact (fun x => Classical.propDecidable (u2.memaddrs x))
            (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0)) =
            some (.val (.word (if c = 0 then 0 else 1))) := by
          by_cases hc0 : c = 0 <;>
            simp [evalHOLExact, u2, u1, u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "after" ≠ ofString "h" by decide,
              show ofString "payload" ≠ ofString "h" by decide,
              hval, Compiler.Encoders.Asm.wordCmpHOL, hc0]
        rw [evaluateHOLFiniteState_ite, he_c] at hnone_cont ⊢; dsimp only at hnone_cont ⊢
        -- Helper to unwind `resVarEq` across `after`, `payload`, `h` for any local `x ∉ {after, payload, h}`:
        have unwind_loc : ∀ (m : HolFiniteMapExact MlS (ValueHOL 64)) (x : MlS),
            x ≠ ofString "after" → x ≠ ofString "payload" → x ≠ ofString "h" →
            (((m.resVarEq (ofString "after", u1.locals.lookup (ofString "after"))).resVarEq
              (ofString "payload", u.locals.lookup (ofString "payload"))).resVarEq
              (ofString "h", s.locals.lookup (ofString "h"))).lookup x = m.lookup x := by
          intro m x h1 h2 h3
          simp [PanRunBounded.resVarEq_lookup, h1, h2, h3]
        by_cases hc0 : c = 0
        · simp only [if_pos hc0, ↓reduceIte] at hnone_cont ⊢
          rw [evaluateHOLFiniteState_assign] at hnone_cont ⊢
          have he_a2 : @evalHOLExact 64 F _ u2.toExact (fun x => Classical.propDecidable (u2.memaddrs x))
              (.var .local (ofString "after")) = some (.val (.word (pos + a + b))) := hu2_aft
          have hvld_p : isValidValueHOLFinite u2 .local (ofString "pos") (.val (.word (pos + a + b))) = true := by
            simp [isValidValueHOLFinite, lookupKvarHOLExact, hu2_pos, shapeOfHOLExact, shapeEqHOL]
          rw [he_a2] at hnone_cont ⊢; dsimp only at hnone_cont ⊢
          rw [if_pos hvld_p]
          dsimp only
          refine ⟨a, b, c, hab1, hab2, hca, hpos_lo, hpos_hi, ?_, Or.inl ⟨hc0, hu2_glob, hu2_mem, ?_, ?_, ?_⟩⟩
          · rw [unwind_loc _ _ (by decide) (by decide) (by decide)]
            simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "pos" ≠ ofString "go" by decide, hu2_go]
          · rw [unwind_loc _ _ (by decide) (by decide) (by decide)]
            simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "pos" ≠ ofString "top" by decide, hu2_top]
          · rw [unwind_loc _ _ (by decide) (by decide) (by decide)]
            simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          · rw [unwind_loc _ _ (by decide) (by decide) (by decide)]
            simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "pos" ≠ ofString "end" by decide, hu2_end]
        · simp only [if_neg hc0, show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hnone_cont ⊢
          obtain ⟨p, q, hp_sp, hq_sp, hq_le_p, hq24_hi, hq_nz, hout_top, hout_pos, hout_end,
              hout_go, hout_m0, hout_m8, hout_m16, hout_moth⟩ :=
            push_eval u2 hu2_code hu2_inv (pos + a + b) end_ top (pos + a)
              hu2_aft hu2_end hu2_top hu2_pay hnone_cont
          rw [hu2_glob] at hp_sp
          refine ⟨a, b, c, hab1, hab2, hca, hpos_lo, hpos_hi, ?_,
            Or.inr ⟨hc0, p, q, hp_sp, hq_sp, hq_le_p, hq24_hi, hq_nz, ?_, ?_, ?_,
              hout_m0, hout_m8, hout_m16, fun w hw => (hout_moth w hw).trans (congrFun hu2_mem w)⟩⟩
          · rw [unwind_loc _ _ (by decide) (by decide) (by decide), hout_go, hu2_go]
          · rw [unwind_loc _ _ (by decide) (by decide) (by decide), hout_top]
          · rw [unwind_loc _ _ (by decide) (by decide) (by decide), hout_pos]
          · rw [unwind_loc _ _ (by decide) (by decide) (by decide), hout_end]
      · simp
    | _ => simp

/-- Chain invariant on `(pos, end_) :: stk`: adjacent frames share endpoints (`e = a_next`). -/
def ChainAdj : BitVec 64 → List (BitVec 64 × BitVec 64) → Prop
  | _, [] => True
  | end_, (a, e) :: rest => end_ = a ∧ ChainAdj e rest

/-- Sum of `(e - a : BitVec 64).toNat` across `(pos, end_) :: stk`. -/
def remBytes : List (BitVec 64 × BitVec 64) → Nat
  | [] => 0
  | (a, e) :: rest => (e - a).toNat + remBytes rest

/-- State invariant for `_rlp_validate_items_body`'s `while (go != 0)` loop, parameterized by the
history `(vis : Finset (Fin domainBytes))` of `item` read positions in `[sourceBase, heapEnd)` and
the cumulative step sum `spent : Nat` from the first `item` read (`P_base`). -/
def LoopInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (P_base : Option (BitVec 64)) (spent : Nat)
    (vis : Finset (Fin domainBytes))
    (stk : List (BitVec 64 × BitVec 64)) : Prop :=
  GuestInv s ∧
  ∃ go pos end_ top : BitVec 64,
    s.locals.lookup (ofString "go") = some (.val (.word go)) ∧
    s.locals.lookup (ofString "pos") = some (.val (.word pos)) ∧
    s.locals.lookup (ofString "end") = some (.val (.word end_)) ∧
    s.locals.lookup (ofString "top") = some (.val (.word top)) ∧
    ChainAdj end_ stk ∧
    stk.length ≤ vis.card ∧
    (top = 0 ∧ stk = [] ∨
     ∃ sp : BitVec 64,
       s.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) ∧
       StackAt s.memory sp.toNat top stk) ∧
    match P_base with
    | none => vis = ∅ ∧ spent = 0 ∧ stk = [] ∧ top = 0
    | some P0 =>
        pos = P0 + BitVec.ofNat 64 spent ∧
        spent + remBytes ((pos, end_) :: stk) < 2 ^ 64 ∧
        ∀ k ∈ vis, ∃ d : Nat, d < spent ∧
          sourceBase ≤ (P0 + BitVec.ofNat 64 d).toNat ∧
          (P0 + BitVec.ofNat 64 d).toNat < heapEnd ∧
          k.val = (P0 + BitVec.ofNat 64 d).toNat - sourceBase

theorem vib_while_aux :
    ∀ (fuel : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F)
      (P_base : Option (BitVec 64)) (spent : Nat)
      (vis : Finset (Fin domainBytes))
      (stk : List (BitVec 64 × BitVec 64)),
      s.code = originalRuntimeCode →
      LoopInv s P_base spent vis stk →
      (match s.locals.lookup (ofString "go") with
       | some (.val (.word w)) => if w = 0 then 0 else 1 + 2 * (domainBytes - vis.card) + stk.length
       | _ => 0) ≤ fuel →
      TerminatingRunBounded s (.while cond body) (fuel * (bodyK + 1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro F s P_base spent vis stk hcode hinv hfuel hnt
    obtain ⟨_, go, pos, end_, top, hgo, _, _, _, _, _, _, _⟩ := hinv
    rw [hgo] at hfuel
    dsimp only at hfuel
    have hgo0 : go = 0 := by
      by_cases hz : go = 0
      · exact hz
      · rw [if_neg hz] at hfuel; omega
    subst hgo0
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    have hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word 0)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [cond, evalHOLExact, hgo, Compiler.Encoders.Asm.wordCmpHOL]
    split
    · rename_i word hword
      rw [hc] at hword; injection hword with h; injection h with h; injection h with h
      subst h
      rw [if_neg (by simp)]
      exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | succ n ih =>
    intro F s P_base spent vis stk hcode hinv hfuel hnt
    have hnt0 := hnt
    obtain ⟨hG, go, pos, end_, top, hgo, hpos, hend, htop, hchain, hstk_le, hstack, hbase⟩ := hinv
    rw [hgo] at hfuel; dsimp only at hfuel
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    by_cases hgo0 : go = 0
    · subst hgo0
      have hc0_ev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond =
          some (.val (.word 0)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [cond, evalHOLExact, hgo, Compiler.Encoders.Asm.wordCmpHOL]
      split
      · rename_i word hword
        rw [hc0_ev] at hword; injection hword with h; injection h with h; injection h with h
        subst h
        rw [if_neg (by simp)]
        exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · rw [if_neg hgo0] at hfuel
      have hc1_ev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond =
          some (.val (.word 1)) := by
        rw [evalHOLFinite_eq_toExact]
        have hz : go ≠ 0#64 := hgo0
        simp [cond, evalHOLExact, hgo, Compiler.Encoders.Asm.wordCmpHOL, hz]
      split
      · rename_i word hword
        have hw1 : word = 1 := by
          rw [hc1_ev] at hword; injection hword with h; injection h with h; injection h with h; exact h.symm
        subst hw1
        simp only [hword] at hnt
        rw [if_pos (by decide : (1 : BitVec 64) ≠ 0)] at hnt ⊢
        by_cases hclk : s.clock = 0
        · rw [if_pos hclk] at hnt; exact absurd rfl hnt
        · rw [if_neg hclk] at hnt ⊢
          set sd := decClockHOLFinite s
          have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
          have hb := body_bound sd hcode hGd
          have hunfold := while_unfold_continue cond body s 1 hword (by decide) hclk
          have hmeta := (evaluateHOLFiniteState_metadata sd body).1
          have hnc := evaluate_noTopContinue body rfl sd
          unfold TerminatingRunBounded at hb
          rcases hrun : evaluateHOLFiniteState sd body with ⟨res, post⟩
          simp only [sd, hrun] at hnt hb hunfold hmeta hnc ⊢
          refine (?_ : s.clock ≤ _ ∧ _ ≤ s.clock)
          change post.code = s.code at hmeta
          have hge1 : bodyK + 1 ≤ (n + 1) * (bodyK + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
          cases res with
          | some r =>
            cases r with
            | «continue» => exact absurd rfl hnc
            | timeOut => exact absurd rfl hnt
            | _ =>
              obtain ⟨hspent, hkept⟩ := hb (by simp)
              change s.clock - 1 ≤ post.clock + bodyK at hspent
              change post.clock ≤ s.clock - 1 at hkept
              dsimp only
              exact ⟨by omega, by omega⟩
          | none =>
            dsimp only
            obtain ⟨hspent, hkept⟩ := hb (by simp)
            change s.clock - 1 ≤ post.clock + bodyK at hspent
            change post.clock ≤ s.clock - 1 at hkept
            have hsame := hunfold (Or.inl rfl)
            have hnt_post : (evaluateHOLFiniteState post (.while cond body)).1 ≠ some .timeOut := by
              rw [← hsame]; exact hnt0
            have hG_post : GuestInv post := by
              have h := guestInv_evaluate sd body hGd
              rwa [hrun] at h
            -- Split `body` on `pos == end_`:
            have hbody_split : evaluateHOLFiniteState sd body =
                if pos = end_ then evaluateHOLFiniteState sd pop else evaluateHOLFiniteState sd item := by
              unfold body
              rw [evaluateHOLFiniteState_ite]
              have hpe : @evalHOLExact 64 F _ sd.toExact (fun x => Classical.propDecidable (sd.memaddrs x))
                  (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end"))) =
                  some (.val (.word (if pos = end_ then 1 else 0))) := by
                have hp_sd : sd.locals.lookup (ofString "pos") = some (.val (.word pos)) := hpos
                have he_sd : sd.locals.lookup (ofString "end") = some (.val (.word end_)) := hend
                by_cases h : pos = end_ <;>
                  simp [evalHOLExact, hp_sd, he_sd, Compiler.Encoders.Asm.wordCmpHOL, h]
              rw [hpe]; by_cases h : pos = end_ <;> simp [h]
            by_cases hpe : pos = end_
            · -- `pop` branch (`pos = end_`)!
              rw [if_pos hpe] at hbody_split
              have hpop_eq : evaluateHOLFiniteState sd pop = (none, post) := hbody_split.symm.trans hrun
              have hpop := pop_eval sd hGd top pos end_ htop hpos hend (by rw [hpop_eq])
              rw [hpop_eq] at hpop; dsimp only at hpop
              by_cases htop0 : top = 0
              · -- `pop` with `top = 0`: sets `go := 0`!
                rw [if_pos htop0] at hpop
                obtain ⟨hpg, hpm, hp_go, hp_pos, hp_end, hp_top⟩ := hpop
                have hstk_nil : stk = [] := by
                  rcases hstack with ⟨_, hs⟩ | ⟨sp, _, hs⟩
                  · exact hs
                  · subst htop0; cases hs with
                    | nil _ => rfl
                    | cons hnz _ _ _ _ _ _ => exact absurd rfl hnz
                subst hstk_nil
                have hinv_post : LoopInv post P_base spent vis [] := by
                  refine ⟨hG_post, 0, pos, end_, 0, hp_go, hp_pos, hp_end, hp_top, trivial,
                    Nat.zero_le _, Or.inl ⟨rfl, rfl⟩, ?_⟩
                  cases P_base with
                  | none => exact ⟨hbase.1, hbase.2.1, rfl, rfl⟩
                  | some P0 => exact hbase
                obtain ⟨htail, htailKept⟩ := ih post P_base spent vis []
                  (hmeta.trans hcode) hinv_post (by rw [hp_go]; simp) hnt_post
                have hmul : n * (bodyK + 1) + (bodyK + 1) = (n + 1) * (bodyK + 1) := by rw [Nat.succ_mul]
                exact ⟨by omega, by omega⟩
              · -- `pop` with `top ≠ 0`: pops `(a, e)` from `stk = (a, e) :: rest`!
                rw [if_neg htop0] at hpop
                rcases hstack with ⟨ht0, _⟩ | ⟨sp, hsp_lk, hstk_at⟩
                · exact absurd ht0 htop0
                cases hstk_at with
                | nil _ => exact absurd rfl htop0
                | @cons _ _ prev a e rest _ hsp_le hhi hm0 hm8 hm16 htail_at =>
                  obtain ⟨hpg, hpm, hp_go, hp_pos, hp_end, hp_top⟩ :=
                    hpop a e prev hhi hm0 hm8 hm16
                  have hp_go' : post.locals.lookup (ofString "go") = some (.val (.word go)) :=
                    hp_go.trans hgo
                  obtain ⟨hend_eq_a, hchain_rest⟩ := hchain
                  have hpos_eq_a : pos = a := hpe.trans hend_eq_a
                  have hinv_post : LoopInv post P_base spent vis rest := by
                    refine ⟨hG_post, go, a, e, prev, hp_go', hp_pos, hp_end, hp_top,
                      hchain_rest, by simp at hstk_le; omega,
                      Or.inr ⟨sp, by rw [hpg]; exact hsp_lk, by
                        rw [hpm]; exact stackAt_mono (by omega) htail_at⟩, ?_⟩
                    cases P_base with
                    | none => simp at hbase
                    | some P0 =>
                      obtain ⟨hpos_P0, hrem_lt, hvis_ok⟩ := hbase
                      refine ⟨hpos_eq_a ▸ hpos_P0, ?_, hvis_ok⟩
                      simpa [remBytes, hpe] using hrem_lt
                  have hfuel_post :
                      (match post.locals.lookup (ofString "go") with
                       | some (.val (.word w)) => if w = 0 then 0 else 1 + 2 * (domainBytes - vis.card) + rest.length
                       | _ => 0) ≤ n := by
                    rw [hp_go']; dsimp only; rw [if_neg hgo0]
                    simp only [List.length_cons] at hfuel; omega
                  obtain ⟨htail, htailKept⟩ := ih post P_base spent vis rest
                    (hmeta.trans hcode) hinv_post hfuel_post hnt_post
                  have hmul : n * (bodyK + 1) + (bodyK + 1) = (n + 1) * (bodyK + 1) := by rw [Nat.succ_mul]
                  exact ⟨by omega, by omega⟩
            · -- `item` branch (`pos ≠ end_`)!
              rw [if_neg hpe] at hbody_split
              have hitem_eq : evaluateHOLFiniteState sd item = (none, post) := hbody_split.symm.trans hrun
              have hitem := item_eval sd hcode hGd pos end_ top hpos hend htop (by rw [hitem_eq])
              rw [hitem_eq] at hitem; dsimp only at hitem
              obtain ⟨a, b, c, hab1, hab2, hca, hpos_lo, hpos_hi, hp_go, hbranch⟩ := hitem
              have hp_go' : post.locals.lookup (ofString "go") = some (.val (.word go)) :=
                hp_go.trans hgo
              -- Establish `(P0, spent0)` for `P_base.getD pos`:
              let P0 : BitVec 64 := P_base.getD pos
              have hP0_state :
                  pos = P0 + BitVec.ofNat 64 spent ∧
                  spent + remBytes ((pos, end_) :: stk) < 2 ^ 64 ∧
                  (∀ k ∈ vis, ∃ d : Nat, d < spent ∧
                    sourceBase ≤ (P0 + BitVec.ofNat 64 d).toNat ∧
                    (P0 + BitVec.ofNat 64 d).toNat < heapEnd ∧
                    k.val = (P0 + BitVec.ofNat 64 d).toNat - sourceBase) := by
                cases P_base with
                | none =>
                  obtain ⟨rfl, rfl, rfl, _⟩ := hbase
                  refine ⟨by simp [P0], ?_, by simp⟩
                  simp only [remBytes, Nat.zero_add]
                  exact (end_ - pos).isLt
                | some P0' => exact hbase
              obtain ⟨hpos_P0, hrem_lt, hvis_ok⟩ := hP0_state
              -- Construct the fresh key `k_now : Fin domainBytes` for `pos`!
              have hk_lt_dom : pos.toNat - sourceBase < domainBytes := by
                have eD : domainBytes = heapEnd - sourceBase := rfl
                omega
              let k_now : Fin domainBytes := ⟨pos.toNat - sourceBase, hk_lt_dom⟩
              have hk_fresh : k_now ∉ vis := by
                intro hmem
                obtain ⟨d, hd_lt, _, _, hk_eq⟩ := hvis_ok k_now hmem
                have hval_eq : (P0 + BitVec.ofNat 64 d).toNat = pos.toNat := by
                  change pos.toNat - sourceBase = _ at hk_eq
                  omega
                have hbv_eq : P0 + BitVec.ofNat 64 d = P0 + BitVec.ofNat 64 spent :=
                  (BitVec.eq_of_toNat_eq hval_eq).trans hpos_P0
                have hdiff : BitVec.ofNat 64 (spent - d) = (0 : BitVec 64) := by
                  have h1 : BitVec.ofNat 64 d + BitVec.ofNat 64 (spent - d) = BitVec.ofNat 64 spent := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
                    have hd1 : d < 2 ^ 64 := by omega
                    have hd2 : spent - d < 2 ^ 64 := by omega
                    have hd3 : spent < 2 ^ 64 := by omega
                    rw [Nat.mod_eq_of_lt hd1, Nat.mod_eq_of_lt hd2, Nat.mod_eq_of_lt hd3]
                    have : d + (spent - d) = spent := by omega
                    rw [this, Nat.mod_eq_of_lt hd3]
                  have h2 : (P0 + BitVec.ofNat 64 d) + BitVec.ofNat 64 (spent - d) = P0 + BitVec.ofNat 64 d + 0 := by
                    rw [BitVec.add_assoc, h1, ← hbv_eq, add_zero]
                  have h3 := congrArg (fun x => -(P0 + BitVec.ofNat 64 d) + x) h2
                  simpa [← BitVec.add_assoc] using h3
                have hsd_lt : spent - d < 2 ^ 64 := by omega
                have hsd0 : (BitVec.ofNat 64 (spent - d)).toNat = 0 := by rw [hdiff]; rfl
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsd_lt] at hsd0
                omega
              have hcard_lt : vis.card < domainBytes := by
                have hle : (insert k_now vis).card ≤ domainBytes := by
                  simpa using Finset.card_le_univ (insert k_now vis)
                rw [Finset.card_insert_of_notMem hk_fresh] at hle
                omega
              have hcard_ins : (insert k_now vis).card = vis.card + 1 :=
                Finset.card_insert_of_notMem hk_fresh
              -- Helper for `BitVec.ofNat 64 (spent + δ) = BitVec.ofNat 64 spent + δ_bv`:
              have add_spent : ∀ (δ : BitVec 64), spent + δ.toNat < 2 ^ 64 →
                  P0 + BitVec.ofNat 64 (spent + δ.toNat) = pos + δ := by
                intro δ hlt64
                rw [hpos_P0, BitVec.add_assoc]
                congr 1
                apply BitVec.eq_of_toNat_eq
                have hs_lt : spent < 2 ^ 64 := by omega
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
                    BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs_lt,
                    Nat.mod_eq_of_lt hlt64]
              have hsub_add : ∀ (x y z : BitVec 64), x - (y + z) = (x - y) - z := by
                intro x y z
                have h : ((x - y) - z) + (y + z) = x := by
                  calc ((x - y) - z) + (y + z)
                      = (((x - y) - z) + z) + y := by
                        rw [BitVec.add_comm y z, ← BitVec.add_assoc]
                    _ = (x - y) + y := by rw [BitVec.sub_add_cancel]
                    _ = x := BitVec.sub_add_cancel x y
                exact (BitVec.sub_eq_iff_eq_add.mpr h.symm)
              rcases hbranch with ⟨hc0, hpg, hpm, hp_top, hp_pos, hp_end⟩ |
                  ⟨hc_nz, p_sp, q_sp, hp_sp, hq_sp, hq_le_p, hq24_hi, hq_nz,
                   hp_top, hp_pos, hp_end, hm0, hm8, hm16, hmoth⟩
              · -- `c = 0`: `pos' = pos + a + b`, `end' = end_`, `stk' = stk`!
                have hab_bv : pos + a + b = pos + BitVec.ofNat 64 (a.toNat + b.toNat) := by
                  rw [BitVec.add_assoc]
                  have hlt : a.toNat + b.toNat < 2 ^ 64 := by
                    have := (end_ - pos).isLt; omega
                  have ha_b : a + b = BitVec.ofNat 64 (a.toNat + b.toNat) := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_add_of_lt hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
                  rw [ha_b]
                have hrem_sub : (end_ - (pos + a + b)).toNat = (end_ - pos).toNat - (a.toNat + b.toNat) := by
                  have hlt : a.toNat + b.toNat < 2 ^ 64 := by have := (end_ - pos).isLt; omega
                  have hbv : end_ - (pos + a + b) = (end_ - pos) - BitVec.ofNat 64 (a.toNat + b.toNat) := by
                    rw [hab_bv, hsub_add]
                  rw [hbv, BitVec.toNat_sub_of_le]
                  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
                  · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact hab2
                have hinv_post : LoopInv post (some P0) (spent + (a.toNat + b.toNat))
                    (insert k_now vis) stk := by
                  refine ⟨hG_post, go, pos + a + b, end_, top, hp_go', hp_pos, hp_end, hp_top,
                    hchain, by rw [hcard_ins]; omega, ?_, ?_⟩
                  · rcases hstack with ⟨ht0, hs0⟩ | ⟨sp, hsp_lk, hstk_at⟩
                    · exact Or.inl ⟨ht0, hs0⟩
                    · exact Or.inr ⟨sp, by rw [hpg]; exact hsp_lk, by rw [hpm]; exact hstk_at⟩
                  · refine ⟨?_, ?_, ?_⟩
                    · have hlt64 : spent + (a.toNat + b.toNat) < 2 ^ 64 := by
                        simp only [remBytes] at hrem_lt; omega
                      rw [hab_bv, ← add_spent (BitVec.ofNat 64 (a.toNat + b.toNat))]
                      · congr 2
                        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hlt64
                    · simp only [remBytes, hrem_sub] at hrem_lt ⊢; omega
                    · intro k hk
                      rcases Finset.mem_insert.mp hk with rfl | hk
                      · exact ⟨spent, by omega, hpos_P0 ▸ hpos_lo, hpos_P0 ▸ hpos_hi, by rw [← hpos_P0]⟩
                      · obtain ⟨d, hd, h1, h2, h3⟩ := hvis_ok k hk
                        exact ⟨d, by omega, h1, h2, h3⟩
                have hfuel_post :
                    (match post.locals.lookup (ofString "go") with
                     | some (.val (.word w)) => if w = 0 then 0 else 1 + 2 * (domainBytes - (insert k_now vis).card) + stk.length
                     | _ => 0) ≤ n := by
                  rw [hp_go', hcard_ins]; dsimp only; rw [if_neg hgo0]; omega
                obtain ⟨htail, htailKept⟩ := ih post (some P0) (spent + (a.toNat + b.toNat))
                  (insert k_now vis) stk (hmeta.trans hcode) hinv_post hfuel_post hnt_post
                have hmul : n * (bodyK + 1) + (bodyK + 1) = (n + 1) * (bodyK + 1) := by rw [Nat.succ_mul]
                exact ⟨by omega, by omega⟩
              · -- `c ≠ 0` (`push`): `pos' = pos + a`, `end' = pos + a + b`, `stk' = (pos + a + b, end_) :: stk`!
                have ha1 : 1 ≤ a.toNat := hca hc_nz
                have hlt_ab : a.toNat + b.toNat < 2 ^ 64 := by have := (end_ - pos).isLt; omega
                have hab_bv : pos + a + b = pos + BitVec.ofNat 64 (a.toNat + b.toNat) := by
                  rw [BitVec.add_assoc]
                  have ha_b : a + b = BitVec.ofNat 64 (a.toNat + b.toNat) := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_add_of_lt hlt_ab, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_ab]
                  rw [ha_b]
                have hrem_b : ((pos + a + b) - (pos + a)).toNat = b.toNat := by
                  have hbv : (pos + a + b) - (pos + a) = b := by
                    rw [BitVec.add_comm (pos + a) b, BitVec.add_sub_cancel]
                  rw [hbv]
                have hrem_push : (end_ - (pos + a + b)).toNat = (end_ - pos).toNat - (a.toNat + b.toNat) := by
                  have hbv : end_ - (pos + a + b) = (end_ - pos) - BitVec.ofNat 64 (a.toNat + b.toNat) := by
                    rw [hab_bv, hsub_add]
                  rw [hbv, BitVec.toNat_sub_of_le]
                  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_ab]
                  · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_ab]; exact hab2
                -- Build `StackAt post.memory q_sp.toNat q_sp ((pos + a + b, end_) :: stk)`:
                have hstk_new : StackAt post.memory q_sp.toNat q_sp ((pos + a + b, end_) :: stk) := by
                  have htail_at : StackAt post.memory (q_sp.toNat + 24) top stk := by
                    rcases hstack with ⟨ht0, hs0⟩ | ⟨sp_old, hsp_old, hold_at⟩
                    · subst ht0; subst hs0; exact .nil _
                    · have hsp_eq : sp_old = p_sp := by
                        have h := hsp_old.symm.trans hp_sp
                        injection h with h; injection h with h; injection h
                      subst hsp_eq
                      exact stackAt_congr (stackAt_mono hq_le_p hold_at) hmoth
                  exact .cons hq_nz (Nat.le_refl _) hq24_hi hm0 hm8 hm16 htail_at
                have hinv_post : LoopInv post (some P0) (spent + a.toNat)
                    (insert k_now vis) ((pos + a + b, end_) :: stk) := by
                  refine ⟨hG_post, go, pos + a, pos + a + b, q_sp, hp_go', hp_pos, hp_end, hp_top,
                    ⟨rfl, hchain⟩, by simp [hcard_ins]; omega,
                    Or.inr ⟨q_sp, hq_sp, hstk_new⟩, ?_⟩
                  refine ⟨?_, ?_, ?_⟩
                  · have hlt64 : spent + a.toNat < 2 ^ 64 := by
                      simp only [remBytes] at hrem_lt; omega
                    exact (add_spent a hlt64).symm
                  · simp only [remBytes, hrem_b, hrem_push] at hrem_lt ⊢
                    omega
                  · intro k hk
                    rcases Finset.mem_insert.mp hk with rfl | hk
                    · exact ⟨spent, by omega, hpos_P0 ▸ hpos_lo, hpos_P0 ▸ hpos_hi, by rw [← hpos_P0]⟩
                    · obtain ⟨d, hd, h1, h2, h3⟩ := hvis_ok k hk
                      exact ⟨d, by omega, h1, h2, h3⟩
                have hfuel_post :
                    (match post.locals.lookup (ofString "go") with
                     | some (.val (.word w)) => if w = 0 then 0 else 1 + 2 * (domainBytes - (insert k_now vis).card) + ((pos + a + b, end_) :: stk).length
                     | _ => 0) ≤ n := by
                  rw [hp_go', hcard_ins, List.length_cons]; dsimp only; rw [if_neg hgo0]; omega
                obtain ⟨htail, htailKept⟩ := ih post (some P0) (spent + a.toNat)
                  (insert k_now vis) ((pos + a + b, end_) :: stk)
                  (hmeta.trans hcode) hinv_post hfuel_post hnt_post
                have hmul : n * (bodyK + 1) + (bodyK + 1) = (n + 1) * (bodyK + 1) := by rw [Nat.succ_mul]
                exact ⟨by omega, by omega⟩
      · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

def EntryInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => LoopInv s none 0 ∅ []

theorem loop_bound : TerminatingProgBoundedOn EntryInv (.while cond body)
    ((62209915858 + 1) * (bodyK + 1)) := by
  intro F s hcode hinv
  have h1 := vib_while_aux (1 + 2 * domainBytes) s none 0 ∅ [] hcode hinv (by
    obtain ⟨_, go, _, _, _, hgo, _, _, _, _, _, _, _⟩ := hinv
    rw [hgo]; dsimp only
    by_cases hz : go = 0
    · rw [if_pos hz]; exact Nat.zero_le _
    · rw [if_neg hz]; simp)
  refine h1.weaken (Nat.mul_le_mul_right _ ?_)
  have hd : domainBytes = 31104957928 := by rw [domainBytes_eq]
  omega

end VibR10

theorem dec_val_on {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (name : MlS)
    (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hQ : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) init = some v →
      shapeEqHOL .one (shapeOfHOLExact v) = true → Q (setVarHOLFinite name v s))
    (hbody : TerminatingProgBoundedOn Q body K) :
    TerminatingProgBoundedOn P (.dec name .one init body) K := by
  intro F state hcode hPs hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rename_i val hval
    revert hnt
    split <;> intro hnt
    · rename_i hsh
      have hb := hbody (setVarHOLFinite name val state) hcode (hQ state val hPs hval hsh) hnt
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem fb__rlp_validate_items_body :
    TerminatingFunBoundedOn GuestInv (ofString "_rlp_validate_items_body") K.«_rlp_validate_items_body» := by
  fb_unfold 110 Guest.Software.guestFn__rlp_validate_items_body
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_val_on (Q := fun s => GuestInv s ∧ s.locals.lookup (ofString "top") = some (.val (.word 0)))
    · intro F s v hP hv _
      simp only [evalHOLExact, Option.some.injEq] at hv; subst hv
      exact ⟨guestInv_setVar _ _ _ hP,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
    · apply dec_on' (Q := fun s => GuestInv s ∧ s.locals.lookup (ofString "top") = some (.val (.word 0)) ∧
          WordLocal (ofString "pos") s)
      · intro F s v hP hsh
        exact ⟨guestInv_setVar _ _ _ hP.1,
          by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "pos" ≠ ofString "top" by decide, hP.2],
          setVar_word s _ v hsh⟩
      · apply dec_on' (Q := fun s => GuestInv s ∧ s.locals.lookup (ofString "top") = some (.val (.word 0)) ∧
            WordLocal (ofString "pos") s ∧ WordLocal (ofString "end") s)
        · intro F s v hP hsh
          exact ⟨guestInv_setVar _ _ _ hP.1,
            by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "end" ≠ ofString "top" by decide, hP.2.1],
            setVar_keep s _ _ v (by decide) hP.2.2,
            setVar_word s _ v hsh⟩
        · apply dec_val_on (Q := VibR10.EntryInv)
          · intro F s v hP hv _
            simp only [evalHOLExact, Option.some.injEq] at hv; subst hv
            obtain ⟨pos, hpos⟩ := hP.2.2.1
            obtain ⟨end_, hend⟩ := hP.2.2.2
            refine ⟨guestInv_setVar _ _ _ hP.1, 1, pos, end_, 0, ?_, ?_, ?_, ?_,
              trivial, Nat.zero_le _, Or.inl ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
            · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "go" ≠ ofString "pos" by decide, hpos]
            · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "go" ≠ ofString "end" by decide, hend]
            · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "go" ≠ ofString "top" by decide, hP.2.1]
          · exact seq_on' VibR10.loop_bound
              (fun s _ hP _ => guestInv_evaluate s _ hP.1)
              (straightOn _ rfl)
  · unfold K.«_rlp_validate_items_body» VibR10.bodyK
    generalize_K
    simp only [Nat.add_zero, Nat.zero_add, max_def]
    split_ifs <;> omega

theorem fb_rlp_validate_items :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_validate_items") K.«rlp_validate_items» := by
  fb_prove 111 Guest.Software.guestFn_rlp_validate_items K.«rlp_validate_items»

theorem fb_rlp_item_total :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_item_total") K.«rlp_item_total» := by
  fb_prove 112 Guest.Software.guestFn_rlp_item_total K.«rlp_item_total»

end InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30
