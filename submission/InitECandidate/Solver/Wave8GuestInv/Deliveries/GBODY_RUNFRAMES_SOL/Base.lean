import InitECandidate.Solver.Wave8GuestInv.Bounds
/-! Light bootstrap: definitions and proved Hoare/run-frames glue copied verbatim from
Contracts.lean at integration 6109dbfbe (frozen rev9 8a79d9f28). The unrelated
covered-entry bridge is deliberately absent. Final Axioms.lean checks definitional
statement equality against the full frozen spec. No contract leaf is supplied here. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.RunFramesRace
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

theorem lookupCodeHOLFinite_installed_return {F : Type}
    (state : PanSemStateFiniteExact 64 F) (fname : MlS)
    (params : List (MlS × ShapeHOL)) (body body' : ProgHOL 64) (ret ret' : ShapeHOL)
    (values : List (ValueHOL 64)) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hc : state.code.lookup fname = some (params, body, ret))
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ret' = ret := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    state.code.lookup fname values body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, hc] at hx
  split at hx
  · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
  · cases hx

/-- `Q` on normal return only. -/
def OnReturn (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → Q s post


def evmR {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum

def IsEvmErr (r : Option (PanSemResultExact 64)) : Prop :=
  ∃ v, r = some (.exception (ofString "EvmErr") v)


def EvmRun : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ ¬ EvmDone s

/-- `finish_child` entry (inside `run_frames`). -/
def FinishReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0


theorem freeChain_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k nodes : Nat) :
    ∀ (Fr : List Nat) (head : Nat),
      FreeChain { s with locals := locals, clock := k } nodes head Fr ↔ FreeChain s nodes head Fr
  | [], _ => Iff.rfl
  | f :: rest, head => by
    simp only [FreeChain]
    exact and_congr Iff.rfl (freeChain_with_locals s locals k nodes rest _)

theorem htabWF_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k t : Nat) :
    HtabWF { s with locals := locals, clock := k } t ↔ HtabWF s t := by
  simp only [HtabWF, freeChain_with_locals]
  exact Iff.rfl

theorem tablesTyped_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    TablesTyped { s with locals := locals, clock := k } S ↔ TablesTyped s S := by
  simp only [TablesTyped, htabWF_with_locals]
  exact Iff.rfl

theorem worldTyped_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    WorldTyped { s with locals := locals, clock := k } S ↔ WorldTyped s S := by
  simp only [WorldTyped, tablesTyped_with_locals]
  exact Iff.rfl

theorem locN_congr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (n : String)
    (h : locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    locN { s with locals := locals, clock := k } n = locN s n := by
  simp only [locN, h]

theorem arenaReady_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ArenaReady { s with locals := locals, clock := k } ↔ ArenaReady s :=
  ⟨fun h => ⟨guestInv_congr (s := { s with locals := locals, clock := k }) rfl rfl rfl rfl h.1, h.2⟩,
   fun h => ⟨guestInv_with_locals_clock s locals k h.1, h.2⟩⟩

theorem evmChainFrom_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ∀ (fuel e c : Nat),
      evmChainFrom { s with locals := locals, clock := k } fuel e c = evmChainFrom s fuel e c
  | 0, _, _ => rfl
  | fuel + 1, e, c => by
    simp only [evmChainFrom, evmChainFrom_with_locals s locals k fuel]
    rfl

theorem evmChain_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmChain { s with locals := locals, clock := k } = evmChain s :=
  evmChainFrom_with_locals s locals k _ _ _

theorem localsFree_arenaReady : LocalsFree ArenaReady :=
  fun s locals k h => (arenaReady_with_locals s locals k).2 h

theorem localsFree_worldOK : LocalsFree WorldOK := by
  intro F s locals k h
  simp only [WorldOK, worldTyped_with_locals, arenaReady_with_locals] at h ⊢
  exact h

theorem localsFree_evmInv : LocalsFree EvmInv := by
  intro F s locals k h
  simp only [EvmInv, FrameWF, MsgOwned, worldTyped_with_locals, arenaReady_with_locals, evmChain_with_locals] at h ⊢
  exact h


theorem evmInv_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    GuestInv s := h.1.1


structure Hoare (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (prog : ProgHOL 64)
    (Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) :
    Prop where
  run : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    Q (evaluateHOLFiniteState s prog).1 (evaluateHOLFiniteState s prog).2

section HoareRules

variable {P P' R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
  {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}

theorem Hoare.of_false {prog : ProgHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → False) : Hoare P prog Q :=
  ⟨fun s _ hP _ => (h s hP).elim⟩

theorem Hoare.mono {prog : ProgHOL 64} (h : Hoare P' prog Q)
    (hPP : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P' s) : Hoare P prog Q :=
  ⟨fun s hcode hP hnt => h.run s hcode (hPP s hP) hnt⟩

theorem Hoare.skip
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q none s) :
    Hoare P .skip Q := by
  refine ⟨fun {F} s _ hP _ => ?_⟩
  rw [evaluateHOLFiniteState_skip]
  exact h s hP

theorem Hoare.seq {first second : ProgHOL 64}
    (h1 : Hoare P first fun r t => (r = none → R t) ∧ (r ≠ none → Q r t))
    (h2 : Hoare R second Q) : Hoare P (.seq first second) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s first).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr : evaluateHOLFiniteState s first with ⟨r1, m⟩
  simp only [hr] at hnt hmeta ⊢
  change m.code = s.code at hmeta
  cases r1 with
  | none =>
    have h := h1.run s hcode hP (by rw [hr]; simp)
    rw [hr] at h
    exact h2.run m (hmeta.trans hcode) (h.1 rfl) hnt
  | some r =>
    have h := h1.run s hcode hP (by rw [hr]; exact hnt)
    rw [hr] at h
    exact h.2 (by simp)

theorem Hoare.ite {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : Hoare (fun s => P s ∧ CondTrue cond s) yes Q)
    (hno : Hoare (fun s => P s ∧ CondFalse cond s) no Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    Hoare P (.ite cond yes no) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · rename_i w hw
    revert hnt
    split <;> intro hnt
    · rename_i hz
      subst hz
      exact hno.run s hcode ⟨hP, hw⟩ hnt
    · rename_i hz
      exact hyes.run s hcode ⟨hP, w, hw, hz⟩ hnt
  · exact herr s hP

theorem resVarEq_lookup_ne (m : HolFiniteMapExact MlS (ValueHOL 64)) (name n : MlS)
    (o : Option (ValueHOL 64)) (h : n ≠ name) :
    (HolFiniteMapExact.resVarEq m (name, o)).lookup n = m.lookup n := by
  rcases o with _ | v
  · simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, h]
  · simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq, FUPDATE_HOL]
    split
    · rename_i heq; exact absurd heq h
    · rfl

/-- `Q` does not read the locals outside `names`. -/
def PostLocalsOnly (names : List String)
    (Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) :
    Prop :=
  ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)),
    (∀ n ∈ names, locals.lookup (ofString n) = t.locals.lookup (ofString n)) →
    Q r t → Q r { t with locals := locals }

theorem Hoare.dec {names : List String} {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64}
    {body : ProgHOL 64} (hname : ∀ n ∈ names, ofString n ≠ name)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some v → P' (setVarHOLFinite name v s))
    (hbody : Hoare P' body Q) (hQ : PostLocalsOnly names Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    Hoare P (.dec name shape init body) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact herr s hP
  · rename_i v hv
    revert hnt
    split <;> intro hnt
    · have hb := hbody.run (setVarHOLFinite name v s) hcode (hinit s v hP hv) hnt
      exact hQ _ _ _ (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hb
    · exact herr s hP

theorem Hoare.assign {kind : VarKind} {name : MlS} {source : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) source =
        some v → Q none (setKvarHOLFinite kind name v s))
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    Hoare P (.assign kind name source) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_assign] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact herr s hP
  · rename_i v hv
    revert hnt
    split <;> intro hnt
    · exact h s v hP hv
    · exact herr s hP

/-- The installed body of a `FunSpec` function, at a successful lookup. -/
theorem FunSpec.at_lookup {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS}
    (hf : FunSpec Pc Qc fname) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (hcode : state.code = originalRuntimeCode) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret'))
    (hPc : Pc (callEntryStateHOLFinite state callee))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1 ≠
      some .timeOut) :
    Qc (callEntryStateHOLFinite state callee)
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').2 := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  have hret := lookupCodeHOLFinite_installed_return state fname params body' body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hret
  exact hspec _ hcode hPc ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩ hnt

/-- Handler-free call with no destination, callee described by a `FunSpec`. Results other than
a normal return are covered by `hother` (a call never yields `continue`). -/
theorem Hoare.call0 {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {arguments : List (ExpHOL 64)}
    (hf : FunSpec Pc Qc fname) (hentry : CallEntryOn P Pc fname arguments)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      Q none { post with locals := s.locals })
    (hother : ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
      r ≠ none → r ≠ some .continue → Q r t) :
    Hoare P (.call (some (none, none)) fname arguments) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
    _ | values
  · exact hother _ _ (by simp) (by simp)
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact hother _ _ (by simp) (by simp)
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hPc := hentry s values body' callee ret' hcode hP hargs hl
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt ⊢
        have hQc (hsafe : res ≠ some .timeOut) : Qc (callEntryStateHOLFinite s callee) res post := by
          have := FunSpec.at_lookup hf s hcode values body' callee ret' hl hPc (by rw [hrun]; exact hsafe)
          rw [hrun] at this
          exact this
        cases res with
        | none => exact hother _ _ (by simp) (by simp)
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · exact hret s callee post v hcode hP (hQc (by simp))
            · exact hother _ _ (by simp) (by simp)
          | timeOut => simp at hnt
          | _ => exact hother _ _ (by simp) (by simp)

/-- Call with an exception handler and no destination: the handler runs on
`setVar var v {post with locals := caller locals}` after the callee raised `exn`. -/
theorem Hoare.callH {Pc Ph : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {arguments : List (ExpHOL 64)}
    {exn var : MlS} {handler : ProgHOL 64}
    (hf : FunSpec Pc Qc fname) (hentry : CallEntryOn P Pc fname arguments)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      Q none { post with locals := s.locals })
    (hexn : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.exception exn v)) post →
      Ph (setVarHOLFinite var v { post with locals := s.locals }))
    (hh : Hoare Ph handler Q)
    (hother : ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
      r ≠ none → r ≠ some .continue → Q r t) :
    Hoare P (.call (some (none, some (exn, var, handler))) fname arguments) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
    _ | values
  · exact hother _ _ (by simp) (by simp)
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact hother _ _ (by simp) (by simp)
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hPc := hentry s values body' callee ret' hcode hP hargs hl
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite s callee) body').1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta ⊢
        change post.code = s.code at hmeta
        have hQc (hsafe : res ≠ some .timeOut) : Qc (callEntryStateHOLFinite s callee) res post := by
          have := FunSpec.at_lookup hf s hcode values body' callee ret' hl hPc (by rw [hrun]; exact hsafe)
          rw [hrun] at this
          exact this
        cases res with
        | none => exact hother _ _ (by simp) (by simp)
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · exact hret s callee post v hcode hP (hQc (by simp))
            · exact hother _ _ (by simp) (by simp)
          | timeOut => simp at hnt
          | exception eid v =>
            dsimp only at hnt ⊢
            by_cases hid : eid = exn
            · subst hid
              simp only [↓reduceIte] at hnt ⊢
              rcases hsh : s.eshapes.lookup eid with _ | shape
              · exact hother _ _ (by simp) (by simp)
              · simp only [hsh] at hnt ⊢
                by_cases hv : (shapeEqHOL (shapeOfHOLExact v) shape &&
                    isValidValueHOLExact s.toExact .local var v) = true
                · simp only [hv, ↓reduceIte] at hnt ⊢
                  exact hh.run _ (by simp [setVarHOLFinite]; exact hmeta.trans hcode)
                    (hexn s callee post v hcode hP (hQc (by simp))) hnt
                · simp only [hv, Bool.false_eq_true, ↓reduceIte]
                  exact hother _ _ (by simp) (by simp)
            · simp only [hid, ↓reduceIte]
              exact hother _ _ (by simp) (by simp)
          | _ => exact hother _ _ (by simp) (by simp)

end HoareRules

/-! ### Evaluating the `run_frames` loop tests -/

/-- Evaluation of an expression at a state (the decider every rewrite lemma uses). -/
noncomputable abbrev evalAt {F : Type} (t : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e

theorem evalAt_cmp {F : Type} (t : PanSemStateFiniteExact 64 F) (op : Cmp) (l r : ExpHOL 64)
    (w : BitVec 64) (h : evalAt t (.cmp op l r) = some (.val (.word w))) :
    ∃ a b : BitVec 64, evalAt t l = some (.val (.word a)) ∧ evalAt t r = some (.val (.word b)) ∧
      w = if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b then 1 else 0 := by
  simp only [evalAt, evalHOLExact] at h ⊢
  split at h
  · rename_i a b ha hb
    exact ⟨a, b, ha, hb, (by simpa using h.symm)⟩
  · cases h

theorem evalAt_const {F : Type} (t : PanSemStateFiniteExact 64 F) (k : BitVec 64)
    (v : ValueHOL 64) (h : evalAt t (.const k) = some v) : v = .val (.word k) := by
  simp only [evalAt, evalHOLExact] at h
  cases h; rfl

theorem evalAt_local {F : Type} (t : PanSemStateFiniteExact 64 F) (n : String) (a : BitVec 64)
    (h : evalAt t (.var .local (ofString n)) = some (.val (.word a))) : a.toNat = locN t n := by
  simp only [evalAt, evalHOLExact] at h
  simp [locN] at h ⊢
  rw [h]

theorem evalAt_loadG' {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .global (ofString g), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (globN t g + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hg : t.globals.lookup (ofString g) with _ | v
  · simp [hg] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [globN, memW, hg, hadd, h.2]
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

/-- A one-word load from `global + k` that succeeds yields the word `memW t (globN t g + k)`. -/
theorem evalAt_loadG {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .global (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (globN t g + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hg : t.globals.lookup (ofString g) with _ | w
    · simp [hg] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hg, valueIsWord] at h
      · simp [hg, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  exact ⟨a, rfl, evalAt_loadG' t g k a h⟩

theorem locN_setVar_same {F : Type} (t : PanSemStateFiniteExact 64 F) (n : String)
    (w : BitVec 64) : locN (setVarHOLFinite (ofString n) (.val (.word w)) t) n = w.toNat := by
  simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem locN_setVar_ne {F : Type} (t : PanSemStateFiniteExact 64 F) (n : String) (m : MlS)
    (v : ValueHOL 64) (h : ofString n ≠ m) : locN (setVarHOLFinite m v t) n = locN t n := by
  have hl : (t.locals.update (m, v)).lookup (ofString n) = t.locals.lookup (ofString n) := by
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm h]
  simp only [locN, setVarHOLFinite, hl]

/-! ### The EVM potential reads only memory and globals -/

def evmFp {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  2 * (evmChain s).length + (if EvmDone s then 0 else 1)

def evmS {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  ((evmChain s).map fun ec => memW s (ec.1 + 72)).sum

theorem evmPot_eq {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evmPot s = evmR s * (evmPotF * evmPotS) + evmFp s * evmPotS + evmS s := rfl

theorem memW_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : t.memory = s.memory) :
    memW t = memW s := by
  funext a; simp [memW, h]

theorem globN_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : t.globals = s.globals) :
    globN t = globN s := by
  funext a; simp [globN, h]

theorem evmChainFrom_congr {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : t.memory = s.memory) :
    ∀ (fuel e c : Nat), evmChainFrom t fuel e c = evmChainFrom s fuel e c
  | 0, _, _ => rfl
  | fuel + 1, e, c => by
    simp only [evmChainFrom, memW_congr h, evmChainFrom_congr h fuel]

theorem evmChain_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) : evmChain t = evmChain s := by
  simp only [evmChain, evmChainFrom_congr hm, globN_congr hg]

theorem evmDone_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) : EvmDone t ↔ EvmDone s := by
  simp only [EvmDone, memW_congr hm, globN_congr hg]

theorem evm_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) :
    evmPot t = evmPot s ∧ evmR t = evmR s ∧ (evmChain t).length = (evmChain s).length ∧
      evmFp t = evmFp s := by
  have hc := evmChain_congr hm hg
  have hd := evmDone_congr hm hg
  refine ⟨?_, ?_, by rw [hc], ?_⟩
  · simp only [evmPot, hc, memW_congr hm, hd]
  · simp only [evmR, hc, memW_congr hm]
  · simp only [evmFp, hc, hd]

theorem memW_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : memW s a < 2 ^ 64 := by
  unfold memW
  split
  rename_i w _
  exact w.isLt

theorem sum_map_memW_le {F : Type} (s : PanSemStateFiniteExact 64 F) (off : Nat) :
    ∀ l : List Ivl, (l.map fun ec => memW s (ec.1 + off)).sum ≤ l.length * (2 ^ 64 - 1)
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := memW_lt s (x.1 + off)
    have h2 := sum_map_memW_le s off xs
    omega

theorem evmInv_len {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    (evmChain s).length ≤ maxChain := by
  obtain ⟨_, S, hS⟩ := h
  exact hS.2.2.1

theorem evmS_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) : evmS s < evmPotS := by
  have hlen := evmInv_len s h
  have hle := sum_map_memW_le s 72 (evmChain s)
  have hm : (evmChain s).length * (2 ^ 64 - 1) < maxChain * 2 ^ 64 := by
    have : (evmChain s).length * (2 ^ 64 - 1) ≤ maxChain * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_right _ hlen
    simp only [maxChain] at this ⊢
    omega
  show ((evmChain s).map fun ec => memW s (ec.1 + 72)).sum < maxChain * 2 ^ 64
  omega

theorem evmFp_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    evmFp s < evmPotF := by
  have hlen := evmInv_len s h
  unfold evmFp evmPotF
  simp only [maxChain] at hlen ⊢
  split <;> omega

/-- The decrease argument of `run_frames`: under `EvmInv`, `R` not larger and `F` strictly
smaller is below any potential with those `R`, `F` components. -/
theorem evmPot_lt_bound {F : Type} (t : PanSemStateFiniteExact 64 F) (h : EvmInv t) {R0 F0 : Nat}
    (hR : evmR t ≤ R0) (hF : evmFp t < F0) :
    evmPot t < R0 * (evmPotF * evmPotS) + F0 * evmPotS := by
  have hS := evmS_lt t h
  have hFp := evmFp_lt t h
  rw [evmPot_eq]
  rcases Nat.lt_or_ge (evmR t) R0 with hlt | hge
  · have h1 : evmFp t * evmPotS + evmS t < evmPotF * evmPotS := by
      have : (evmFp t + 1) * evmPotS ≤ evmPotF * evmPotS := Nat.mul_le_mul_right _ hFp
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    have h2 : (evmR t + 1) * (evmPotF * evmPotS) ≤ R0 * (evmPotF * evmPotS) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at h2
    have h3 : 0 ≤ F0 * evmPotS := Nat.zero_le _
    omega
  · have hReq : evmR t = R0 := le_antisymm hR hge
    have h2 : (evmFp t + 1) * evmPotS ≤ F0 * evmPotS := Nat.mul_le_mul_right _ hF
    rw [Nat.add_mul, Nat.one_mul] at h2
    rw [hReq]
    omega

theorem evmPot_ge {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evmR s * (evmPotF * evmPotS) + evmFp s * evmPotS ≤ evmPot s := by
  rw [evmPot_eq]; omega

/-! ### Loop tests of `run_frames` -/

theorem cond_loadG {F : Type} (t : PanSemStateFiniteExact 64 F) (op : Cmp) (g : String)
    (k w : BitVec 64)
    (h : evalAt t (.cmp op (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) = some (.val (.word w))) :
    ∃ a : BitVec 64, a.toNat = memW t (globN t g + k.toNat) ∧
      w = if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a 0 then 1 else 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := evalAt_cmp t op _ _ w h
  obtain ⟨a', ha', hm⟩ := evalAt_loadG t g k _ ha
  cases ha'
  have hb' := evalAt_const t 0 _ hb
  cases hb'
  exact ⟨a, hm, rfl⟩

theorem condTrue_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondTrue (.cmp .notEqual (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) ≠ 0 := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, ha, rfl⟩ := cond_loadG t _ g k w hw
  rw [← ha]
  intro h0
  apply hne
  have : a = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst this
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem condFalse_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondFalse (.cmp .notEqual (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) = 0 := by
  obtain ⟨a, ha, h0⟩ := cond_loadG t _ g k 0 h
  rw [← ha]
  by_cases hz : a = 0
  · subst hz; rfl
  · exfalso
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at h0
    exact hz h0

theorem condTrue_eq0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondTrue (.cmp .equal (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) = 0 := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, ha, rfl⟩ := cond_loadG t _ g k w hw
  rw [← ha]
  by_cases hz : a = 0
  · subst hz; rfl
  · exfalso; apply hne
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    exact hz

theorem condFalse_eq0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondFalse (.cmp .equal (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) ≠ 0 := by
  obtain ⟨a, ha, h0⟩ := cond_loadG t _ g k 0 h
  rw [← ha]
  intro hz
  have : a = 0 := BitVec.eq_of_toNat_eq (by simpa using hz)
  subst this
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at h0

theorem cond_local {F : Type} (t : PanSemStateFiniteExact 64 F) (op : Cmp) (n : String)
    (r : ExpHOL 64) (w : BitVec 64)
    (h : evalAt t (.cmp op (.var .local (ofString n)) r) = some (.val (.word w))) :
    ∃ a b : BitVec 64, a.toNat = locN t n ∧ evalAt t r = some (.val (.word b)) ∧
      w = if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b then 1 else 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := evalAt_cmp t op _ _ w h
  exact ⟨a, b, evalAt_local t n a ha, hb, rfl⟩

theorem condTrue_local_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {n : String}
    (h : CondTrue (.cmp .notEqual (.var .local (ofString n)) (.const 0)) t) : locN t n ≠ 0 := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, b, ha, hb, rfl⟩ := cond_local t _ n _ w hw
  cases evalAt_const t 0 _ hb
  rw [← ha]
  intro h0
  apply hne
  have : a = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst this
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem condFalse_local_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {n : String}
    (h : CondFalse (.cmp .notEqual (.var .local (ofString n)) (.const 0)) t) : locN t n = 0 := by
  obtain ⟨a, b, ha, hb, h0⟩ := cond_local t _ n _ 0 h
  cases evalAt_const t 0 _ hb
  rw [← ha]
  by_cases hz : a = 0
  · subst hz; rfl
  · exfalso
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at h0
    exact hz h0

theorem cond_notLower {F : Type} {t : PanSemStateFiniteExact 64 F} {n g : String} {k w : BitVec 64}
    (h : evalAt t (.cmp .notLower (.var .local (ofString n))
      (.load .one (.op .add [.var .global (ofString g), .const k]))) = some (.val (.word w))) :
    (w ≠ 0 → memW t (globN t g + k.toNat) ≤ locN t n) ∧
      (w = 0 → locN t n < memW t (globN t g + k.toNat)) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := cond_local t _ n _ w h
  obtain ⟨b', hb', hm⟩ := evalAt_loadG t g k _ hb
  cases hb'
  rw [← ha, ← hm]
  constructor
  · intro hw
    by_cases hlt : a < b
    · exfalso; apply hw; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt]
    · exact Nat.le_of_not_lt (fun hc => hlt (BitVec.lt_def.mpr hc))
  · intro hw
    by_cases hlt : a < b
    · exact BitVec.lt_def.mp hlt
    · exfalso; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt] at hw

/-! ### The glue, proved -/

section RunFramesGlue

variable (p0 R0 L0 F0 : Nat)

/-- Loop-head facts carried through the body: the potential components of the head. -/
def GPre : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ evmPot t = p0 ∧ evmR t = R0 ∧ (evmChain t).length = L0 ∧ evmFp t = F0

def GQ : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none ∨ r = some .continue) → (EvmInv t ∧ evmPot t < p0) ∨ locN t "go" = 0

def GMid : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => (GPre p0 R0 L0 F0 t ∧ EvmDone t ∧ locN t "done" ≠ 0) ∨
    (EvmInv t ∧ evmPot t < p0 ∧ locN t "done" = 0)

def GA : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none → GMid p0 R0 L0 F0 t) ∧ (r ≠ none → GQ p0 r t)

theorem gq_other {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (h1 : r ≠ none) (h2 : r ≠ some .continue) : GQ p0 r t := by
  intro h; rcases h with h | h <;> contradiction

theorem ga_other {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (h1 : r ≠ none) (h2 : r ≠ some .continue) : GA p0 R0 L0 F0 r t :=
  ⟨fun h => absurd h h1, fun _ => gq_other p0 r t h1 h2⟩

theorem gpre_congr {F : Type} {t u : PanSemStateFiniteExact 64 F} (hm : u.memory = t.memory)
    (hg : u.globals = t.globals) (hinv : EvmInv u) (h : GPre p0 R0 L0 F0 t) :
    GPre p0 R0 L0 F0 u := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  obtain ⟨e1, e2, e3, e4⟩ := evm_congr hm hg
  exact ⟨hinv, e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4⟩

theorem evmInv_locals {F : Type} {t : PanSemStateFiniteExact 64 F}
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (h : EvmInv t) :
    EvmInv { t with locals := locals } :=
  localsFree_evmInv t locals t.clock h

theorem evmInv_setVar {F : Type} {t : PanSemStateFiniteExact 64 F} (n : MlS) (v : ValueHOL 64)
    (h : EvmInv t) : EvmInv (setVarHOLFinite n v t) :=
  localsFree_evmInv t _ t.clock h

theorem evmInv_entry {F : Type} {t : PanSemStateFiniteExact 64 F}
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : EvmInv t) :
    EvmInv (callEntryStateHOLFinite t callee) :=
  localsFree_evmInv t _ _ h

theorem gq_postLocals : PostLocalsOnly ["go"] (GQ p0) := by
  intro F r t locals hl h hr
  rcases h hr with ⟨hi, hp⟩ | hgo
  · left
    exact ⟨evmInv_locals locals hi, by rw [(evm_congr (s := t) (t := { t with locals := locals }) rfl rfl).1]; exact hp⟩
  · right
    rw [locN_congr t locals t.clock "go" (hl "go" (by simp))]
    exact hgo

theorem ga_postLocals : PostLocalsOnly ["go", "done"] (GA p0 R0 L0 F0) := by
  intro F r t locals hl h
  have hgo := hl "go" (by simp)
  have hdone := locN_congr t locals t.clock "done" (hl "done" (by simp))
  refine ⟨fun hr => ?_, fun hr => gq_postLocals p0 r t locals (fun n hn => by
    simp at hn; subst hn; exact hgo) (h.2 hr)⟩
  rcases h.1 hr with ⟨hp, hd, hn⟩ | ⟨hi, hp, hn⟩
  · left
    refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := { t with locals := locals }) rfl rfl
      (evmInv_locals locals hp.1) hp, ?_, ?_⟩
    · exact (evmDone_congr (s := t) (t := { t with locals := locals }) rfl rfl).2 hd
    · change locN { t with locals := locals, clock := t.clock } "done" ≠ 0
      rw [hdone]; exact hn
  · right
    refine ⟨evmInv_locals locals hi, ?_, ?_⟩
    · rw [(evm_congr (s := t) (t := { t with locals := locals }) rfl rfl).1]; exact hp
    · change locN { t with locals := locals, clock := t.clock } "done" = 0
      rw [hdone]; exact hn

end RunFramesGlue

/-- `run_frames` is the 585th declaration of the AST. -/
theorem lookup_run_frames :
    originalRuntimeCode.lookup (ofString "run_frames") =
      some ((sourceFunctionEntry Guest.Software.guestFn_run_frames).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 584 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_run_frames) rfl

section RunFramesGlue2

variable (p0 R0 L0 F0 : Nat)

/-- After `dec done 0`. -/
def GP1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ locN t "done" = 0

/-- After `dec pc (load ev)` on the not-yet-done path. -/
def GPpc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ locN t "done" = 0 ∧
    memW t (globN t "cur_cont" + 32) = 0 ∧ memW t (globN t "ev" + 104) ≠ 0 ∧
    locN t "pc" = memW t (globN t "ev")

/-- At the `op_dispatch` call: a running frame. -/
def GPdisp : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ locN t "done" = 0 ∧ ¬ EvmDone t ∧ F0 = 2 * L0 + 1

/-- In the `EvmErr` handler of `op_dispatch`. -/
def GPh : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ (evmChain t).length = L0 ∧ evmR t ≤ R0 ∧ locN t "done" = 0 ∧
    F0 = 2 * L0 + 1

/-- The done branch, before `frame_epilogue`. -/
def GPdone : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ EvmDone t

/-- After `frame_epilogue`. -/
def GPepi : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ EvmDone t ∧ (evmChain t).length = L0 ∧ evmR t ≤ R0 ∧ 2 * L0 ≤ F0

/-- At the `finish_child` call. -/
def GPfin : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPepi R0 L0 F0 t ∧ memW t (globN t "cur_cont" + 16) ≠ 0

/-- In the `EvmErr` handler of `finish_child`. -/
def GPh4 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ (evmChain t).length + 1 = L0 ∧ evmR t ≤ R0 ∧ 2 * L0 ≤ F0

end RunFramesGlue2

theorem evmFp_done {F : Type} {t : PanSemStateFiniteExact 64 F} (h : EvmDone t) :
    evmFp t = 2 * (evmChain t).length := by
  simp [evmFp, h]

theorem evmFp_notDone {F : Type} {t : PanSemStateFiniteExact 64 F} (h : ¬ EvmDone t) :
    evmFp t = 2 * (evmChain t).length + 1 := by
  simp [evmFp, h]

theorem evmFp_le {F : Type} (t : PanSemStateFiniteExact 64 F) :
    evmFp t ≤ 2 * (evmChain t).length + 1 := by
  unfold evmFp; split <;> omega


theorem TerminatingProgBoundedOn.mono_bound {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {a b : Nat} (h : TerminatingProgBoundedOn P prog a) (hle : a ≤ b) :
    TerminatingProgBoundedOn P prog b :=
  fun s hc hP => (h s hc hP).weaken hle

/-- A program that never changes the clock costs nothing. -/
theorem TerminatingProgBoundedOn.of_clock {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s prog).2.clock = s.clock) :
    TerminatingProgBoundedOn P prog 0 :=
  fun s _ _ _ => ⟨by have := h s; omega, by have := h s; omega⟩

theorem clock_return {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_return]
  repeat' split
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals (try rfl)

theorem clock_raise {F : Type} (s : PanSemStateFiniteExact 64 F) (n : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.raise n e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_raise]
  repeat' split
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals (try rfl)

theorem clock_shMemStore {F : Type} (s : PanSemStateFiniteExact 64 F) (op : OpSize) (a v : ExpHOL 64) :
    (evaluateHOLFiniteState s (.shMemStore op a v)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_shMemStore]
  show (shMemStoreClauseHOLFiniteExact s op a v).2.clock = s.clock
  simp only [shMemStoreClauseHOLFiniteExact, shMemStoreClauseHOLExact, shMemStoreHOLExact]
  repeat' split
  all_goals rfl

/-- A guard that ignores locals and clock holds at every callee entry. -/
theorem callEntryOn_of_localsFree {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (h : LocalsFree P) (fname : MlS) (arguments : List (ExpHOL 64)) :
    CallEntryOn P P fname arguments :=
  fun state _ _ _ _ _ hP _ _ => h state _ _ hP

/-- `seq` whose second part needs only `GuestInv` (which every evaluation keeps). -/
theorem TerminatingProgBoundedOn.seq_guestInv_after
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (h2 : TerminatingProgBoundedOn GuestInv second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := guestInv_evaluate state first (hPG state hP)
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) hmid hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem seq_clock {first second : ProgHOL 64}
    (h1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s first).2.clock = s.clock)
    (h2 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s second).2.clock = s.clock) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s (.seq first second)).2.clock = s.clock := by
  intro F s
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s first with ⟨r, mid⟩
  have := h1 s
  rw [hr] at this
  cases r with
  | none => dsimp only; rw [h2 mid]; exact this
  | some _ => exact this

theorem clock_assign {F : Type} (s : PanSemStateFiniteExact 64 F) (k : VarKind) (n : MlS)
    (e : ExpHOL 64) : (evaluateHOLFiniteState s (.assign k n e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_assign]
  repeat' split
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals (try rfl)
  all_goals (cases k <;> rfl)


theorem clock_skip {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s .skip).2.clock = s.clock := by simp

end InitECandidate.Solver.Wave8GuestInv.RunFramesRace
