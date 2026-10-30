import InitE.SourceSemantics
import InitE.SourceDeclarationsCore
import InitE.SourceNameFacts
import InitE.SourceMainFacts
import InitECandidate.Solver.CompactComputation
import InitECandidate.Solver.FrontendCodecComputation
import InitECandidate.Solver.GuestCodeLookup
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.PanToTarget.MainFirstSemantics
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.GuestGlobalKeep

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup

theorem list_lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, List.lookup a l = some b → (a, b) ∈ l
  | [], h => by simp at h
  | (k, v) :: t, h => by
    by_cases e : a = k
    · subst e; simp [List.lookup] at h; subst h; simp
    · have : (a == k) = false := by simpa using e
      simp [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (list_lookup_mem h)

theorem originalRuntimeCode_mem {f : MlS} {x : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (h : originalRuntimeCode.lookup f = some x) : (f, x) ∈ functionsHOL sourceDeclarations := by
  rw [originalRuntimeCode_lookup_eq_reverse_lookup] at h
  exact List.mem_reverse.mp (list_lookup_mem h)

theorem lookupCode_installed {code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {f : MlS} {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite code f values = some (body, callee, rs)) :
    ∃ params rs', code f = some (params, body, rs') := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i fb fl fs found
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _, _⟩ := h
    unfold lookupCodeHOLExact at found
    split at found
    · cases found
    · rename_i params b r hc
      split at found
      · simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, _, _⟩ := found
        exact ⟨params, r, hc⟩
      · cases found

theorem evaluateHOLFiniteState_metadata {F : Type}
    (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64) :
    (evaluateHOLFiniteState state program).2.code = state.code ∧
      (evaluateHOLFiniteState state program).2.memaddrs = state.memaddrs ∧
      (evaluateHOLFiniteState state program).2.be = state.be ∧
      (evaluateHOLFiniteState state program).2.shMemaddrs = state.shMemaddrs ∧
      (evaluateHOLFiniteState state program).2.eshapes = state.eshapes := by
  have invariant := evaluateInvariantsHOLFinite program
    (PanPropsEvalStateFiniteExact.ofPanSemFinite state)
    (evaluateHOLFiniteState state program).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState state program).2) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact ⟨invariant.2.2.2.2.2.2.1, invariant.1, invariant.2.2.1, invariant.2.1, invariant.2.2.2.1⟩

def keepsG (watched : MlS) (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => keepsG watched good body
  | .seq first second => keepsG watched good first && keepsG watched good second
  | .ite _ yes no => keepsG watched good yes && keepsG watched good no
  | .while _ body => keepsG watched good body
  | .assign .global name _ => !(name == watched)
  | .assign .local _ _ => true
  | .store _ _ | .storeByte _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .extCall _ _ _ _ _ => true
  | .decCall _ _ function _ continuation => good function && keepsG watched good continuation
  | .call none function _ => good function
  | .call (some (none, none)) function _ => good function
  | .call (some (some (.local, _), none)) function _ => good function
  | .call (some (some (.global, name), none)) function _ => good function && !(name == watched)
  | .call (some (none, some (_, _, handler))) function _ => good function && keepsG watched good handler
  | .call (some (some (.local, _), some (_, _, handler))) function _ => good function && keepsG watched good handler
  | .call (some (some (.global, name), some (_, _, handler))) function _ =>
      good function && !(name == watched) && keepsG watched good handler
  | .primitive _ _ _ => true
  | .shMemLoad _ .local _ _ => true
  | .shMemLoad _ .global name _ => !(name == watched)
  | .shMemStore _ _ _ => true
  | _ => false

def DestOK (watched : MlS) (dest : Option (VarKind × MlS)) : Prop :=
  dest = none ∨ (∃ name, dest = some (.local, name)) ∨ (∃ name, dest = some (.global, name) ∧ name ≠ watched)

theorem call_keeps {F : Type} (watched : MlS)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (function : MlS) (arguments : List (ExpHOL 64)) (state : PanSemStateFiniteExact 64 F)
    (hinfo : info = none ∨ ∃ dest handler, info = some (dest, handler) ∧ DestOK watched dest)
    (ihBody : ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup function values = some (body, callee, rs) →
      state.clock ≠ 0 →
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.globals.lookup watched =
        state.globals.lookup watched)
    (ihHandler : ∀ dest hid hv hp, info = some (dest, some (hid, hv, hp)) →
      ∀ (t : PanSemStateFiniteExact 64 F),
        t.clock < state.clock → t.code = state.code →
        (evaluateHOLFiniteState t hp).2.globals.lookup watched = t.globals.lookup watched) :
    (evaluateHOLFiniteState state (.call info function arguments)).2.globals.lookup watched =
      state.globals.lookup watched := by
  rw [evaluateHOLFiniteState_call]
  split
  · rfl
  · rename_i values _
    split
    · rfl
    · rename_i body callee rs found
      split
      · rfl
      · rename_i nonzero
        have ih := ihBody values body callee rs found nonzero
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
        have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
        generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
        obtain ⟨r, st⟩ := out
        dsimp only at ih meta' cl ⊢
        change st.clock ≤ state.clock - 1 at cl
        have stc : st.clock < state.clock := by omega
        rcases hinfo with rfl | ⟨dest, handler, rfl, hdest⟩
        · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
            simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite,
              HolFiniteMapExact.lookup_update, FUPDATE, emptyLocalsHOLFinite, ih] <;> simp_all
        · rcases hdest with rfl | ⟨nm, rfl⟩ | ⟨nm, rfl, ne⟩ <;> rcases handler with _ | ⟨hid, hv, hp⟩ <;>
            rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
            first
              | (refine (ihHandler _ hid hv hp rfl _ (by exact stc) (by exact meta'.1)).trans ih)
              | (simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite,
                  HolFiniteMapExact.lookup_update, FUPDATE, emptyLocalsHOLFinite, ih] <;> simp_all)

theorem shMemStore_globals {F : Type} (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (address value : ExpHOL 64) (key : MlS) :
    (evaluateHOLFiniteState state (.shMemStore operator address value)).2.globals.lookup key =
      state.globals.lookup key := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · unfold shMemStoreHOLExact
    split <;> split
    all_goals simp [ofExact, toExact]
    all_goals split <;> simp
  · simp

theorem shMemLoad_local_globals {F : Type} (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (name : MlS) (address : ExpHOL 64) (key : MlS) :
    (evaluateHOLFiniteState state (.shMemLoad operator .local name address)).2.globals.lookup key =
      state.globals.lookup key := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source]
  split
  · split
    · unfold shMemLoadHOLFiniteExact
      dsimp only
      split <;> split <;> (try split) <;>
        simp [emptyLocalsHOLFinite, setKvarFfiHOLFinite, setKvarHOLFinite, setVarHOLFinite]
    · rfl
  · rfl

theorem shMemLoad_global_globals {F : Type} (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (name : MlS) (address : ExpHOL 64) (key : MlS) (hne : name ≠ key) :
    (evaluateHOLFiniteState state (.shMemLoad operator .global name address)).2.globals.lookup key =
      state.globals.lookup key := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source]
  split
  · split
    · unfold shMemLoadHOLFiniteExact
      dsimp only
      split <;> split <;> (try split) <;>
        simp [emptyLocalsHOLFinite, setKvarFfiHOLFinite, setKvarHOLFinite, setGlobalHOLFinite,
          HolFiniteMapExact.lookup_update, FUPDATE, hne]
    · rfl
  · rfl

theorem lex_of {a b c d : Nat} (h : a < c ∨ (a = c ∧ b < d)) :
    Prod.Lex (· < ·) (· < ·) (a, b) (c, d) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

theorem evaluate_keepsG {F : Type} (watched : MlS) (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body, callee, rs) →
      keepsG watched good body = true)
    (program : ProgHOL 64) (supported : keepsG watched good program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals.lookup watched = state.globals.lookup watched := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : keepsG watched good body = true := by simpa only [shape, keepsG] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · split
      · exact evaluate_keepsG watched good hgood body child _ code
      · rfl
  | decCall name kind function arguments continuation =>
    have children : good function = true ∧ keepsG watched good continuation = true := by
      simpa only [shape, keepsG, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        rw [code] at found
        have bodyOk := hgood function children.1 values body callee rs found
        split
        · rfl
        · rename_i nonzero
          dsimp only
          have ih := evaluate_keepsG watched good hgood body bodyOk (callEntryStateHOLFinite state callee) code
          have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at ih meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try exact ih)
          split
          · have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            exact (evaluate_keepsG watched good hgood continuation children.2 (setVarHOLFinite name v _) (by exact stCode)).trans ih
          · exact ih
  | assign kind name value =>
    cases kind with
    | global =>
      have different : name ≠ watched := by simpa [shape, keepsG] using supported
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split
        · simp [setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, different]
        · rfl
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split <;> rfl
  | seq first second =>
    have children : keepsG watched good first = true ∧ keepsG watched good second = true := by
      simpa only [shape, keepsG, Bool.and_eq_true] using supported
    have memory := evaluate_keepsG watched good hgood first children.1 state code
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
        exact (evaluate_keepsG watched good hgood second children.2 middle (meta'.1.trans code)).trans memory
      | some result => exact memory
  | ite condition yes no =>
    have children : keepsG watched good yes = true ∧ keepsG watched good no = true := by
      simpa only [shape, keepsG, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_keepsG watched good hgood no children.2 state code
      · exact evaluate_keepsG watched good hgood yes children.1 state code
    · rfl
  | «while» condition body =>
    have child : keepsG watched good body = true := by simpa only [shape, keepsG] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have memory := evaluate_keepsG watched good hgood body child (decClockHOLFinite state) code
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at memory remaining meta'
            dsimp only at memory remaining meta'
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none => exact (evaluate_keepsG watched good hgood (.while condition body) (by simpa [keepsG] using child) middle mCode).trans memory
            | some result =>
              cases result with
              | «continue» => exact (evaluate_keepsG watched good hgood (.while condition body) (by simpa [keepsG] using child) middle mCode).trans memory
              | «break» => exact memory
              | returned value => exact memory
              | exception exception value => exact memory
              | finalFfi ffi => exact memory
              | error => exact memory
              | timeOut => exact memory
      · rfl
    · rfl
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot tag text => rw [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> rfl
    · rfl
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  | store destination value =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte destination value =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | extCall name a b c d =>
    rw [evaluateHOLFiniteState_extCall_source]
    split
    · split
      · split <;> simp [emptyLocalsHOLFinite, ofExact, toExact]
      · simp
    · simp
  | primitive name op args =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | shMemStore op a v => exact shMemStore_globals state op a v watched
  | shMemLoad op kind name a =>
    cases kind with
    | «local» => exact shMemLoad_local_globals state op name a watched
    | global =>
      have hne : name ≠ watched := by simpa [shape, keepsG] using supported
      exact shMemLoad_global_globals state op name a watched hne
  | call info function arguments =>
    have hk : good function = true ∧ (info = none ∨ ∃ dest handler, info = some (dest, handler) ∧ DestOK watched dest) ∧
        ∀ dest hid hv hp, info = some (dest, some (hid, hv, hp)) → keepsG watched good hp = true := by
      rcases info with _ | ⟨_ | ⟨kind, nm⟩, _ | ⟨hid, hv, hp⟩⟩
      · simpa [shape, keepsG] using supported
      · simp [shape, keepsG] at supported
        exact ⟨supported, Or.inr ⟨none, none, rfl, Or.inl rfl⟩, fun _ _ _ _ h => by cases h⟩
      · simp [shape, keepsG] at supported
        exact ⟨supported.1, Or.inr ⟨none, _, rfl, Or.inl rfl⟩, fun _ _ _ _ h => by cases h; exact supported.2⟩
      · cases kind
        · simp [shape, keepsG] at supported
          exact ⟨supported, Or.inr ⟨_, none, rfl, Or.inr (Or.inl ⟨nm, rfl⟩)⟩, fun _ _ _ _ h => by cases h⟩
        · simp [shape, keepsG] at supported
          exact ⟨supported.1, Or.inr ⟨_, none, rfl, Or.inr (Or.inr ⟨nm, rfl, supported.2⟩)⟩, fun _ _ _ _ h => by cases h⟩
      · cases kind
        · simp [shape, keepsG] at supported
          exact ⟨supported.1, Or.inr ⟨_, _, rfl, Or.inr (Or.inl ⟨nm, rfl⟩)⟩, fun _ _ _ _ h => by cases h; exact supported.2⟩
        · simp [shape, keepsG] at supported
          exact ⟨supported.1.1, Or.inr ⟨_, _, rfl, Or.inr (Or.inr ⟨nm, rfl, supported.1.2⟩)⟩,
            fun _ _ _ _ h => by cases h; exact supported.2⟩
    refine call_keeps watched info function arguments state hk.2.1 (fun values body callee rs found nonzero => ?_)
      (fun dest hid hv hp hi t tlt tcode => ?_)
    · rw [code] at found
      exact evaluate_keepsG watched good hgood body (hgood function hk.1 values body callee rs found)
        (callEntryStateHOLFinite state callee) code
    · exact evaluate_keepsG watched good hgood hp (hk.2.2 dest hid hv hp hi) t (tcode.trans code)
  | _ => simp [shape, keepsG] at supported
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
      | omega
      | (by_cases hc : state.clock = 0
         · right; refine ⟨by omega, ?_⟩; simp +arith
         · left; omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · right; refine ⟨h, ?_⟩; simp +arith)
      | (right; refine ⟨rfl, ?_⟩; simp +arith)

end InitECandidate.Solver.GuestGlobalKeep
