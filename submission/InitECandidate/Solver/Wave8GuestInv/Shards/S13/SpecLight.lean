import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.GuestUniformClockBound
import Guest.SoftwareAst

/-! Light-cone infrastructure and counter-loop lemmas for shard s13 (adapted from s01 at 9bd58bb2e).

Imports ONLY the light cone (`InitECandidate.Solver.PanTerminatingBounded`,
`InitECandidate.Solver.GuestUniformClockBound`, `Guest.SoftwareAst`).
Restates the needed definitions (`TerminatingFunBoundedOn`, `K.*`, etc.) verbatim from
`campaign/specs-proposed/GuestInv.lean` (rev 7) and parameterizes over `GuestInv` via
`IsGuestInv` so declarations can be checked in the light cone via `turbo-lean check` and
verified for `type_of%` equality and `#print axioms` against the full spec in `Axioms.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S13.Spec

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open Flapjack.Compiler.Encoders.Asm

/-! ## 1. Restated definitions and combinators from `GuestInv.lean` -/

def domainBytes : Nat := heapEnd - sourceBase

/-- Abstract interface satisfied by `Wave8GuestInv.GuestInv`: preserved by evaluation and
invariant under changes to fields other than `(code, memaddrs, shMemaddrs, baseAddr)`. -/
class IsGuestInv (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop where
  eval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (prog : ProgHOL 64),
    P s → P (evaluateHOLFiniteState s prog).2
  congr : ∀ {F : Type} {s t : PanSemStateFiniteExact 64 F},
    t.code = s.code → t.memaddrs = s.memaddrs → t.shMemaddrs = s.shMemaddrs →
    t.baseAddr = s.baseAddr → P s → P t

/-- Light-cone witness of `IsGuestInv`. -/
def GuestInvLight {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧
  s.memaddrs = ordinaryDomain ∧
  s.shMemaddrs = sharedDomain ∧
  s.baseAddr = BitVec.ofNat 64 sourceBase

theorem evaluate_baseAddr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program : ProgHOL 64) :
    (evaluateHOLFiniteState state program).2.baseAddr = state.baseAddr := by
  have invariant := evaluateInvariantsHOLFinite program
    (PanPropsEvalStateFiniteExact.ofPanSemFinite state)
    (evaluateHOLFiniteState state program).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState state program).2) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact invariant.2.2.2.2.1

instance : IsGuestInv GuestInvLight where
  eval s prog h := by
    obtain ⟨c, m, sh, b⟩ := h
    have hm := PanRunBounded.evaluateHOLFiniteState_metadata s prog
    exact ⟨hm.1.trans c, hm.2.1.trans m, hm.2.2.2.1.trans sh, (evaluate_baseAddr s prog).trans b⟩
  congr hcode hmem hsh hbase h := by
    obtain ⟨c, m, sh, b⟩ := h
    exact ⟨hcode.trans c, hmem.trans m, hsh.trans sh, hbase.trans b⟩

theorem guestInv_evaluate {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    [IsGuestInv GuestInv] {F : Type} (s : PanSemStateFiniteExact 64 F) (prog : ProgHOL 64)
    (h : GuestInv s) : GuestInv (evaluateHOLFiniteState s prog).2 :=
  IsGuestInv.eval s prog h

theorem guestInv_congr {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    [IsGuestInv GuestInv] {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hcode : t.code = s.code) (hmem : t.memaddrs = s.memaddrs) (hsh : t.shMemaddrs = s.shMemaddrs)
    (hbase : t.baseAddr = s.baseAddr) (h : GuestInv s) : GuestInv t :=
  IsGuestInv.congr hcode hmem hsh hbase h

theorem guestInv_callEntry {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    [IsGuestInv GuestInv] {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : GuestInv s) :
    GuestInv (callEntryStateHOLFinite s callee) :=
  guestInv_congr (s := s) rfl rfl rfl rfl h

theorem guestInv_with_locals_clock {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    [IsGuestInv GuestInv] {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : GuestInv s) :
    GuestInv { s with locals := locals, clock := k } :=
  guestInv_congr (s := s) rfl rfl rfl rfl h

theorem guestInv_setVar {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    [IsGuestInv GuestInv] {F : Type} (name : MlS) (v : ValueHOL 64)
    (s : PanSemStateFiniteExact 64 F) (h : GuestInv s) : GuestInv (setVarHOLFinite name v s) :=
  guestInv_congr (s := s) rfl rfl rfl rfl h

theorem guestInv_decClock {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    [IsGuestInv GuestInv] {F : Type} (s : PanSemStateFiniteExact 64 F) (hs : GuestInv s) :
    GuestInv (decClockHOLFinite s) :=
  guestInv_with_locals_clock s s.locals _ hs

/-- `fname` is installed and its body is bounded by `K` from every `P` entry state. -/
def TerminatingFunBoundedOn (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) (K : Nat) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    TerminatingProgBoundedOn P body K

def PreservesOn (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
    state.code = originalRuntimeCode → P state →
    (evaluateHOLFiniteState state prog).1 ≠ some .timeOut →
    Q (evaluateHOLFiniteState state prog).2

theorem preservesOn_guestInv {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    [IsGuestInv GuestInv] (prog : ProgHOL 64) : PreservesOn GuestInv GuestInv prog :=
  fun state _ h _ => guestInv_evaluate state prog h

def CallEntryOn (P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (fname : MlS)
    (arguments : List (ExpHOL 64)) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL),
    state.code = originalRuntimeCode → P state →
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values →
    lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, returnShape) →
    Pc (callEntryStateHOLFinite state callee)

theorem callEntryOn_guestInv {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    [IsGuestInv GuestInv] (fname : MlS) (arguments : List (ExpHOL 64)) :
    CallEntryOn GuestInv GuestInv fname arguments := by
  intro F state values body callee ret _ hP _ _
  exact guestInv_callEntry state callee hP

theorem TerminatingFunBoundedOn.weaken {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {K K' : Nat} (h : TerminatingFunBoundedOn P fname K) (hle : K ≤ K') :
    TerminatingFunBoundedOn P fname K' := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  exact ⟨params, body, ret, hlook, fun state hcode hP => (hb state hcode hP).weaken hle⟩

theorem TerminatingFunBoundedOn.of_unconditional
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {K : Nat}
    (h : TerminatingFunBounded fname K) : TerminatingFunBoundedOn P fname K := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  exact ⟨params, body, ret, hlook, fun state hcode _ => hb state hcode⟩

def LocalsFree (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (k : Nat), P s → P { s with locals := locals, clock := k }

theorem localsFree_guestInv {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    [IsGuestInv GuestInv] : LocalsFree GuestInv :=
  fun s locals k h => guestInv_with_locals_clock s locals k h

theorem callee_body_bound {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {ret : ShapeHOL} {B : Nat}
    (hlook : originalRuntimeCode.lookup fname = some (params, body, ret))
    (hbody : TerminatingProgBoundedOn Pc body B) {arguments : List (ExpHOL 64)}
    (hentry : CallEntryOn P Pc fname arguments)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (hcode : state.code = originalRuntimeCode)
    (hP : P state) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    body' = body ∧ TerminatingRunBounded (callEntryStateHOLFinite state callee) body' B := by
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  exact ⟨rfl, hbody (callEntryStateHOLFinite state callee) hcode
    (hentry state values body' callee ret' hcode hP hargs hl)⟩

theorem TerminatingProgBoundedOn.call_on
    {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (hentry : CallEntryOn P Pc fname arguments) :
    TerminatingProgBoundedOn P (.call (some (destination, none)) fname arguments) (B + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  intro F state hcode hP hnt
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · have hout : evaluateHOLFiniteState state (.call (some (destination, none)) fname arguments) =
        (some .error, state) := by
      rw [evaluateHOLFiniteState_call, hargs]
    rw [hout]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · have hout : evaluateHOLFiniteState state (.call (some (destination, none)) fname arguments) =
          (some .error, state) := by
        rw [evaluateHOLFiniteState_call, hargs]
        simp only [hl]
      rw [hout]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · obtain ⟨_, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      by_cases hz : state.clock = 0
      · exfalso; apply hnt
        rw [evaluateHOLFiniteState_call, hargs]
        simp [hl, hz]
      · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        have hntb : res ≠ some .timeOut := by
          intro h; subst h; apply hnt
          rw [evaluateHOLFiniteState_call, hargs]
          simp [hl, hz, hrun]
        have hb := hrunBound (by rw [hrun]; exact hntb)
        rw [hrun] at hb
        obtain ⟨hspent, hkept⟩ := hb
        change state.clock - 1 ≤ post.clock + B at hspent
        change post.clock ≤ state.clock - 1 at hkept
        have hpair := evaluate_call_body_clock_no_timeout state post fname destination arguments
          values body' callee ret' res hargs hl hz hrun hntb
        dsimp only at hpair
        rw [hpair.2]
        exact ⟨by omega, by omega⟩

theorem TerminatingProgBoundedOn.call_guestInv
    {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} [IsGuestInv GuestInv]
    {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    TerminatingProgBoundedOn GuestInv (.call (some (destination, none)) fname arguments)
      (B + 1) :=
  TerminatingProgBoundedOn.call_on hf destination arguments (callEntryOn_guestInv fname arguments)

theorem TerminatingProgBoundedOn.tailCall_on
    {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B) (arguments : List (ExpHOL 64))
    (hentry : CallEntryOn P Pc fname arguments) :
    TerminatingProgBoundedOn P (.call none fname arguments) (B + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨_, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt ⊢
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | timeOut => simp at hnt
          | returned value =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            dsimp only
            split
            · exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
            · exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩

theorem TerminatingProgBoundedOn.tailCall_guestInv
    {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} [IsGuestInv GuestInv]
    {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B) (arguments : List (ExpHOL 64)) :
    TerminatingProgBoundedOn GuestInv (.call none fname arguments) (B + 1) :=
  TerminatingProgBoundedOn.tailCall_on hf arguments (callEntryOn_guestInv fname arguments)

theorem TerminatingProgBoundedOn.decCall_guestInv
    {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} [IsGuestInv GuestInv]
    {fname : MlS} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (hcont : TerminatingProgBoundedOn GuestInv continuation Bc) :
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname arguments continuation)
      (B + Bc + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  have hentry : CallEntryOn GuestInv GuestInv fname arguments := callEntryOn_guestInv fname arguments
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨hbb, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      subst hbb
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee)
          body').1
        have hpost := guestInv_evaluate (callEntryStateHOLFinite state callee) body'
          (guestInv_callEntry state callee hP)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta hpost ⊢
        change post.code = state.code at hmeta
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | returned value =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              set resumed := setVarHOLFinite name value { post with locals := state.locals } with hres
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              have hresInv : GuestInv resumed :=
                guestInv_setVar name value _
                  (guestInv_with_locals_clock post state.locals post.clock hpost)
              have hcb := hcont resumed hresCode hresInv hnt
              obtain ⟨hsc, hkc⟩ := hcb
              change post.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + Bc
                at hsc
              change (evaluateHOLFiniteState resumed continuation).2.clock ≤ post.clock at hkc
              exact ⟨by omega, by omega⟩
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact ⟨by omega, by omega⟩
          | timeOut => simp at hnt
          | «break» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | «continue» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | error =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
          | exception _ _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
          | finalFfi _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩

theorem TerminatingProgBoundedOn.seq_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a) (hp : PreservesOn P P first)
    (h2 : TerminatingProgBoundedOn P second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := hp state hcode hP
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
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid (by simp)) hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem TerminatingProgBoundedOn.ite_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {cond : ExpHOL 64}
    {yes no : ProgHOL 64} {a b : Nat}
    (hyes : TerminatingProgBoundedOn P yes a) (hno : TerminatingProgBoundedOn P no b) :
    TerminatingProgBoundedOn P (.ite cond yes no) (max a b) := by
  intro F state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · revert hnt
    split <;> intro hnt
    · exact TerminatingRunBounded.weaken (hno state hcode hP) (Nat.le_max_right a b) hnt
    · exact TerminatingRunBounded.weaken (hyes state hcode hP) (Nat.le_max_left a b) hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem TerminatingProgBoundedOn.dec_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : LocalsFree P)
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn P body K) :
    TerminatingProgBoundedOn P (.dec name shape init body) K := by
  intro F state hcode hPs
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i val _ _
      have hb := hbody (setVarHOLFinite name val state) hcode
        (hP state (state.locals.update (name, val)) state.clock hPs) hnt
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem TerminatingProgBoundedOn.seq_guestInv
    {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} [IsGuestInv GuestInv]
    {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn GuestInv first a)
    (h2 : TerminatingProgBoundedOn GuestInv second b) :
    TerminatingProgBoundedOn GuestInv (.seq first second) (a + b) :=
  TerminatingProgBoundedOn.seq_on h1 (preservesOn_guestInv first) h2

def LoopActive (condition : ExpHOL 64) {F : Type} (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ word : BitVec 64,
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) ∧ word ≠ 0

theorem evaluate_clock_irrelevant {F : Type} (prog : ProgHOL 64)
    (state post : PanSemStateFiniteExact 64 F) (res : Option (PanSemResultExact 64)) (d : Nat)
    (hrun : evaluateHOLFiniteState state prog = (res, post)) (hnt : res ≠ some .timeOut) :
    evaluateHOLFiniteState { state with clock := state.clock + d } prog =
      (res, { post with clock := post.clock + d }) :=
  panPropsEvaluateAddClockEq prog state res post d ⟨hrun, hnt⟩

theorem evaluate_ne_of_clock_lt {F : Type} (prog : ProgHOL 64)
    (state upper : PanSemStateFiniteExact 64 F)
    (hupper : upper = { state with clock := upper.clock }) (hlt : state.clock < upper.clock)
    (hsame : evaluateHOLFiniteState upper prog = evaluateHOLFiniteState state prog)
    (hnt : (evaluateHOLFiniteState state prog).1 ≠ some .timeOut) : False := by
  rcases hrun : evaluateHOLFiniteState state prog with ⟨res, post⟩
  rw [hrun] at hsame hnt
  have hadd := evaluate_clock_irrelevant prog state post res (upper.clock - state.clock) hrun hnt
  have hshift : ({ state with clock := state.clock + (upper.clock - state.clock) } :
      PanSemStateFiniteExact 64 F) = upper := by
    have hsum : state.clock + (upper.clock - state.clock) = upper.clock := by omega
    rw [hsum]
    exact hupper.symm
  rw [hshift, hsame] at hadd
  have hclk := congrArg (fun out => out.2.clock) hadd
  dsimp only at hclk
  omega

theorem while_unfold_continue {F : Type} (condition : ExpHOL 64) (body : ProgHOL 64)
    (state : PanSemStateFiniteExact 64 F) (word : BitVec 64)
    (hcond : evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)))
    (hword : word ≠ 0) (hclock : state.clock ≠ 0)
    (hflow : (evaluateHOLFiniteState (decClockHOLFinite state) body).1 = none ∨
      (evaluateHOLFiniteState (decClockHOLFinite state) body).1 = some .continue) :
    evaluateHOLFiniteState state (.while condition body) =
      evaluateHOLFiniteState (evaluateHOLFiniteState (decClockHOLFinite state) body).2
        (.while condition body) := by
  rw [evaluateHOLFiniteState_while_fixClockRewrite]
  simp only [hcond, if_pos hword, if_neg hclock]
  rcases hb : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨r, post⟩
  rw [hb] at hflow
  rcases hflow with h | h <;> (dsimp only at h; subst h; rfl)

def SameHead {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with clock := t.clock }

def WhileTimesOut (condition : ExpHOL 64) (body : ProgHOL 64) {F : Type}
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  (evaluateHOLFiniteState t (.while condition body)).1 = some .timeOut

def Stationary (condition : ExpHOL 64) (body : ProgHOL 64) {F : Type}
    (s t : PanSemStateFiniteExact 64 F) : Prop :=
  SameHead s t ∨ WhileTimesOut condition body t

theorem while_rank_stationary_aux
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hbody : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → TerminatingRunBounded (decClockHOLFinite s) body B)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        (μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s ∨
          Stationary condition body s (evaluateHOLFiniteState (decClockHOLFinite s) body).2)) :
    ∀ (n : Nat) {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → P state →
      (LoopActive condition state → μ state + 1 ≤ n) →
      TerminatingRunBounded state (.while condition body) (n * (B + 1)) := by
  intro n
  induction n with
  | zero =>
    intro F state hcode hP hle hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · have := hle ⟨word, hword, hzero⟩
        omega
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | succ n ih =>
    intro F state hcode hP hle hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · rw [if_pos hzero] at hnt ⊢
        by_cases hclock : state.clock = 0
        · rw [if_pos hclock] at hnt; exact absurd rfl hnt
        · rw [if_neg hclock] at hnt ⊢
          have hact : LoopActive condition state := ⟨word, hword, hzero⟩
          have hμ := hle hact
          have hb := hbody state hcode hP hact
          have hstep' := hstep state hcode hP hact
          have hunfold := while_unfold_continue condition body state word hword hzero hclock
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite state) body).1
          unfold TerminatingRunBounded at hb
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
          simp only [hrun] at hnt hb hstep' hunfold hmeta
          dsimp only at hb hstep' hunfold hmeta hnt ⊢
          change post.code = state.code at hmeta
          have hcont (hflow : result = none ∨ result = some .continue) :
              state.clock ≤ (evaluateHOLFiniteState post (.while condition body)).2.clock +
                (n + 1) * (B + 1) ∧
              (evaluateHOLFiniteState post (.while condition body)).2.clock ≤ state.clock := by
            have hsafe : result ≠ some .timeOut := by
              rcases hflow with h | h <;> simp [h]
            obtain ⟨hspent, hkept⟩ := hb hsafe
            change state.clock - 1 ≤ post.clock + B at hspent
            change post.clock ≤ state.clock - 1 at hkept
            obtain ⟨hPpost, hdown⟩ := hstep' hflow
            have hsame := hunfold hflow
            have hntPost : (evaluateHOLFiniteState post (.while condition body)).1 ≠
                some .timeOut := by
              rw [← hsame]; exact hnt0
            rcases hdown with hlt | hrep
            · obtain ⟨htail, htailKept⟩ := ih post (hmeta.trans hcode) hPpost
                (fun _ => by omega) hntPost
              have hmul : n * (B + 1) + (B + 1) = (n + 1) * (B + 1) := by
                rw [Nat.succ_mul]
              exact ⟨by omega, by omega⟩
            · exfalso
              rcases hrep with hrep | hto
              · refine evaluate_ne_of_clock_lt (.while condition body) post state ?_
                  (by omega) hsame hntPost
                rw [hrep]
              · exact hntPost hto
          cases result with
          | none => exact hcont (Or.inl rfl)
          | some r =>
            cases r with
            | «continue» => exact hcont (Or.inr rfl)
            | timeOut => exact absurd rfl hnt
            | _ =>
              obtain ⟨hspent, hkept⟩ := hb (by simp)
              change state.clock - 1 ≤ post.clock + B at hspent
              change post.clock ≤ state.clock - 1 at hkept
              simp only
              have hone : B + 1 ≤ (n + 1) * (B + 1) := Nat.le_mul_of_pos_left _ (by omega)
              exact ⟨by omega, by omega⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem TerminatingProgBoundedOn.while_rank_stationary
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B N : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : TerminatingProgBoundedOn P body B)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → μ s ≤ N)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        (μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s ∨
          Stationary condition body s (evaluateHOLFiniteState (decClockHOLFinite s) body).2)) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  fun state hcode hP =>
    while_rank_stationary_aux μ (fun s hc hPs _ => hbody (decClockHOLFinite s) hc (hdec s hPs))
      hstep (N + 1) state hcode hP (fun hact => by have := hle state hcode hP hact; omega)

theorem TerminatingProgBoundedOn.while_rank
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B N : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : TerminatingProgBoundedOn P body B)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → μ s ≤ N)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  TerminatingProgBoundedOn.while_rank_stationary μ hdec hbody hle
    fun s hcode hP hact hflow =>
      let h := hstep s hcode hP hact hflow
      ⟨h.1, Or.inl h.2⟩

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


/-- Ordinary-domain fact needed by the input-blob walk. -/
class HasOrdinaryDomain (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop where
  memaddrs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → s.memaddrs = ordinaryDomain

namespace K

def «trap_with» : Nat := 0

def «alloc» : Nat := Nat.max ((«trap_with» + 1)) (0) + Nat.max ((«trap_with» + 1)) (0)

def «memcpy» : Nat := Nat.max (((domainBytes + 1) + 1) * (0 + 1) + ((domainBytes + 1) + 1) * (0 + 1)) (0) + ((domainBytes + 1) + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)

def «memzero» : Nat := Nat.max (((domainBytes + 1) + 1) * (0 + 1) + ((domainBytes + 1) + 1) * (0 + 1)) (0) + ((domainBytes + 1) + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)

def «rlp_fail» : Nat := 0

def «rlp_read_length» : Nat := Nat.max ((«rlp_fail» + 1)) (0) + ((domainBytes + 1) + 1) * (0 + 1)

def «rlp_item_header» : Nat := Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0)) (0) + Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0)

def «scratch_alloc» : Nat := Nat.max ((«trap_with» + 1)) (0) + Nat.max ((«trap_with» + 1)) (0)

def «_rlp_validate_items_body» : Nat := (62209915858 + 1) * (Nat.max (0) ((«rlp_item_header» + 1) + Nat.max ((«scratch_alloc» + 1)) (0)) + 1)

def «scratch_mark» : Nat := 0

def «scratch_release» : Nat := 0

def «rlp_validate_items» : Nat := («scratch_mark» + 1) + («_rlp_validate_items_body» + 1) + («scratch_release» + 1) + («scratch_release» + 1)

def «rlp_item_total» : Nat := («rlp_item_header» + 1) + Nat.max ((«rlp_validate_items» + 1)) (0)

def «rlp_list_count» : Nat := ((domainBytes + 1) + 1) * ((«rlp_item_total» + 1) + 1)

def «rlp_item» : Nat := Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + («rlp_list_count» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0) + («rlp_list_count» + 1)

def «rlp_decode_fully» : Nat := («rlp_item» + 1) + Nat.max ((«rlp_fail» + 1)) (0)

def «rlp_item_total_unchecked» : Nat := Nat.max ((«rlp_read_length» + 1)) (0) + («rlp_read_length» + 1)

def «rlp_list_to_slices» : Nat := («rlp_list_count» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«rlp_item_total_unchecked» + 1) + 1)

def «htab_find_leaf» : Nat := (2 ^ 64 + 1) * (0 + 1)

def «memeq» : Nat := Nat.max ((2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)) (0) + (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)

def «rlp_be_len» : Nat := (8 + 1) * (0 + 1)

def «rlp_header_len» : Nat := («rlp_be_len» + 1)

def «rlp_bytes_encoded_len» : Nat := («rlp_header_len» + 1)

def «keccak_f1600» : Nat := (2 ^ 64 + 1) * (0 + 1)

def «keccak_absorb_block» : Nat := (2 ^ 64 + 1) * (0 + 1) + («keccak_f1600» + 1)

def «keccak256» : Nat := («memzero» + 1) + ((domainBytes + 1) + 1) * ((«keccak_absorb_block» + 1) + 1) + («memzero» + 1) + («memcpy» + 1) + («keccak_absorb_block» + 1) + Nat.max (0) ((«memcpy» + 1))

def «rlp_put_be» : Nat := (2 ^ 64 + 1) * (0 + 1)

def «rlp_write_header» : Nat := («rlp_be_len» + 1) + («rlp_put_be» + 1)

def «rlp_encode_bytes» : Nat := («rlp_write_header» + 1) + («memcpy» + 1)

def «rlp_encode_list_header» : Nat := («rlp_write_header» + 1)

def «rlp_list_header_len» : Nat := («rlp_header_len» + 1)

def «htab_has» : Nat := («htab_find_leaf» + 1) + («memeq» + 1)

def «htab_first_diff» : Nat := ((domainBytes + 1) + 1) * (Nat.max ((8 + 1) * (0 + 1)) (0) + 1)

def «htab_grow» : Nat := («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1)

def «htab_new_node» : Nat := Nat.max ((«htab_grow» + 1)) (0)

def «htab_new_internal» : Nat := («htab_new_node» + 1)

def «htab_new_leaf» : Nat := («htab_new_node» + 1) + («memcpy» + 1)

def «htab_set» : Nat := («htab_find_leaf» + 1) + Nat.max ((«htab_new_leaf» + 1)) (0) + («memeq» + 1) + («htab_first_diff» + 1) + (7776239486 + 1) * (0 + 1) + («htab_new_leaf» + 1) + («htab_new_internal» + 1)

def «heap_mark» : Nat := 0

def «heap_release» : Nat := 0

def «u256_is_zero» : Nat := 0

def «htab_new» : Nat := («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1)

def «bswap64» : Nat := 0

def «u256_from_be» : Nat := Nat.max ((«bswap64» + 1) + («bswap64» + 1) + («bswap64» + 1) + («bswap64» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1)

def «udivmod» : Nat := Nat.max ((«trap_with» + 1)) (0) + (64 + 1) * (0 + 1)

def «udiv» : Nat := («udivmod» + 1)

def «check_gas_limit» : Nat := («udiv» + 1)

def «rlp_encode_word» : Nat := («rlp_be_len» + 1) + («rlp_put_be» + 1)

def «bit_length64» : Nat := 0

def «u256_bit_length» : Nat := Nat.max ((«bit_length64» + 1)) (0) + Nat.max ((«bit_length64» + 1)) (0) + Nat.max ((«bit_length64» + 1)) (0) + («bit_length64» + 1)

def «u256_byte_length» : Nat := («u256_bit_length» + 1)

def «u256_limb» : Nat := 0

def «u256_to_be_min» : Nat := («u256_byte_length» + 1) + (2 ^ 64 + 1) * ((«u256_limb» + 1) + 1)

def «rlp_put_u256» : Nat := («heap_mark» + 1) + («alloc» + 1) + («u256_to_be_min» + 1) + («rlp_encode_bytes» + 1) + («heap_release» + 1)

def «htab_item» : Nat := 0

def «tx_fixed_bytes» : Nat := («rlp_item» + 1)

def «tx_list_item» : Nat := («rlp_item» + 1)

def «decode_access_list» : Nat := («rlp_list_to_slices» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«rlp_item» + 1) + («rlp_list_to_slices» + 1) + («tx_fixed_bytes» + 1) + («tx_list_item» + 1) + («rlp_list_to_slices» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«tx_fixed_bytes» + 1) + («memcpy» + 1) + 1) + 1)

def «tx_scalar_item» : Nat := («rlp_item» + 1)

def «tx_scalar_u256» : Nat := («tx_scalar_item» + 1) + («u256_from_be» + 1)

def «tx_scalar_word» : Nat := («tx_scalar_item» + 1) + (2 ^ 64 + 1) * (0 + 1)

def «decode_authorizations» : Nat := («rlp_list_to_slices» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«rlp_item» + 1) + («rlp_list_to_slices» + 1) + («tx_scalar_u256» + 1) + («tx_fixed_bytes» + 1) + («tx_scalar_word» + 1) + («tx_scalar_word» + 1) + («tx_scalar_u256» + 1) + («tx_scalar_u256» + 1) + 1)

def «decode_blob_hashes» : Nat := («rlp_list_to_slices» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«tx_fixed_bytes» + 1) + («memcpy» + 1) + 1)

def «tx_bytes_item» : Nat := («rlp_item» + 1)

def «tx_to_item» : Nat := («rlp_item» + 1)

def «decode_transaction_rlp» : Nat := («alloc» + 1) + («memzero» + 1) + Nat.max ((«rlp_decode_fully» + 1)) (Nat.max ((«rlp_decode_fully» + 1)) (0)) + («rlp_list_to_slices» + 1) + Nat.max ((«tx_scalar_word» + 1)) (0) + Nat.max ((«tx_scalar_word» + 1)) ((«tx_scalar_u256» + 1)) + Nat.max ((«tx_scalar_u256» + 1)) ((«tx_scalar_u256» + 1) + («tx_scalar_u256» + 1)) + («tx_scalar_word» + 1) + Nat.max ((«tx_fixed_bytes» + 1)) ((«tx_to_item» + 1)) + («tx_scalar_u256» + 1) + («tx_bytes_item» + 1) + Nat.max ((«tx_list_item» + 1) + («decode_access_list» + 1)) (0) + Nat.max ((«tx_scalar_u256» + 1) + («tx_list_item» + 1) + («decode_blob_hashes» + 1)) (0) + Nat.max ((«tx_list_item» + 1) + («decode_authorizations» + 1)) (0) + («tx_scalar_u256» + 1) + («tx_scalar_u256» + 1) + («tx_scalar_u256» + 1)

def «decode_transaction» : Nat := («decode_transaction_rlp» + 1)

def «u256_eq» : Nat := 0

def «u256_lt» : Nat := 0

def «u256_sub» : Nat := 0

def «u256_add» : Nat := 0

def «digits_len» : Nat := (2 ^ 64 + 1) * (0 + 1)

def «digits_to_u256» : Nat := 0

def «div64by32» : Nat := (32 + 1) * (0 + 1)

def «nlz32» : Nat := 0

def «divmnu» : Nat := Nat.max ((31104957944 + 1) * ((«div64by32» + 1) + 1)) (0) + («nlz32» + 1) + (31104957944 + 1) * (0 + 1) + (31104957944 + 1) * (0 + 1) + (31104957944 + 1) * (Nat.max (0) ((«div64by32» + 1)) + (3 + 1) * (0 + 1) + (31104957944 + 1) * (0 + 1) + Nat.max ((31104957944 + 1) * (0 + 1)) (0) + 1) + (31104957944 + 1) * (0 + 1) + (31104957944 + 1) * (0 + 1)

def «u256_to_digits» : Nat := 0

def «digits_divmod» : Nat := («u256_to_digits» + 1) + («digits_len» + 1) + («digits_len» + 1) + (16 + 1) * (0 + 1) + Nat.max ((«digits_to_u256» + 1)) (0) + (8 + 1) * (0 + 1) + («divmnu» + 1) + («digits_to_u256» + 1)

def «mul64x64» : Nat := 0

def «u256_divmod» : Nat := («u256_lt» + 1) + Nat.max ((«udivmod» + 1)) (0) + («u256_to_digits» + 1) + («digits_divmod» + 1) + («digits_to_u256» + 1)

def «u256_mul_full» : Nat := («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1)

def «u256_gt» : Nat := («u256_lt» + 1)

def «u256_fits_word» : Nat := 0

def «u256_div» : Nat := («u256_divmod» + 1)

def «u256_from_word» : Nat := 0

def «u256_mul» : Nat := Nat.max ((«mul64x64» + 1)) (0) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1)

def «taylor_exponential» : Nat := («u256_from_word» + 1) + («u256_from_word» + 1) + («u256_from_word» + 1) + («u256_mul» + 1) + («u256_is_zero» + 1) + ((2 ^ 64 + 1) + 1) * ((«u256_add» + 1) + («u256_mul_full» + 1) + Nat.max ((«trap_with» + 1)) (0) + («u256_from_word» + 1) + («u256_mul» + 1) + («u256_div» + 1) + («u256_is_zero» + 1) + 1) + («u256_div» + 1)

def «calculate_blob_gas_price» : Nat := («taylor_exponential» + 1)

def «rlp_word_encoded_len» : Nat := («rlp_be_len» + 1)

def «tx_is_blob» : Nat := 0

def «count_tokens_in_data» : Nat := (2 ^ 64 + 1) * (0 + 1)

def «calculate_intrinsic_cost» : Nat := («count_tokens_in_data» + 1) + («u256_is_zero» + 1) + Nat.max (0) ((«memeq» + 1)) + Nat.max ((2 ^ 64 + 1) * (0 + 1)) (0)

def «validate_transaction» : Nat := («calculate_intrinsic_cost» + 1) + («u256_fits_word» + 1)

def «validate_block_access_list_gas_limit» : Nat := (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«htab_has» + 1)) (0) + 1)) (0) + 1) + («udiv» + 1)

def «encode_header» : Nat := («alloc» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_put_u256» + 1) + («rlp_encode_word» + 1) + («rlp_encode_word» + 1) + («rlp_encode_word» + 1) + («rlp_encode_word» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_put_u256» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_word» + 1) + («rlp_encode_word» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + Nat.max ((«rlp_encode_bytes» + 1) + («rlp_encode_word» + 1)) (0) + («rlp_list_header_len» + 1) + («rlp_encode_list_header» + 1)

def «header_hash» : Nat := («heap_mark» + 1) + («encode_header» + 1) + («keccak256» + 1) + («heap_release» + 1)

def «is_valid_versioned_hashes» : Nat := (2 ^ 64 + 1) * ((«decode_transaction» + 1) + («tx_is_blob» + 1) + Nat.max ((2 ^ 64 + 1) * ((«memeq» + 1) + 1)) (0) + 1)

def «nodedb_build» : Nat := (2 ^ 64 + 1) * (0 + 1) + («htab_new» + 1) + (2 ^ 64 + 1) * ((«keccak256» + 1) + («htab_set» + 1) + 1)

def «withdrawal_rlp_len» : Nat := («rlp_word_encoded_len» + 1) + («rlp_word_encoded_len» + 1) + («rlp_word_encoded_len» + 1) + («rlp_list_header_len» + 1)

def «block_rlp_length» : Nat := («heap_mark» + 1) + («encode_header» + 1) + («heap_release» + 1) + (2 ^ 64 + 1) * (Nat.max ((«rlp_bytes_encoded_len» + 1)) (0) + 1) + («rlp_list_header_len» + 1) + (2 ^ 64 + 1) * ((«withdrawal_rlp_len» + 1) + 1) + («rlp_list_header_len» + 1) + («rlp_list_header_len» + 1)

def «encode_execution_requests» : Nat := («alloc» + 1) + (2 ^ 64 + 1) * (Nat.max ((«alloc» + 1) + («memcpy» + 1)) (0) + 1)

def «calculate_base_fee_per_gas» : Nat := («check_gas_limit» + 1) + («u256_from_word» + 1) + («u256_from_word» + 1) + Nat.max ((«u256_from_word» + 1) + («u256_mul» + 1) + («u256_div» + 1) + («u256_div» + 1) + («u256_is_zero» + 1) + Nat.max ((«u256_from_word» + 1)) (0) + («u256_add» + 1)) (0) + («u256_from_word» + 1) + («u256_mul» + 1) + («u256_div» + 1) + («u256_div» + 1) + («u256_sub» + 1)

def «calculate_excess_blob_gas» : Nat := («calculate_blob_gas_price» + 1) + («u256_from_word» + 1) + («u256_mul» + 1) + («u256_from_word» + 1) + («u256_mul» + 1) + («u256_gt» + 1) + Nat.max ((«udiv» + 1)) (0)

def «validate_header» : Nat := («calculate_excess_blob_gas» + 1) + («calculate_base_fee_per_gas» + 1) + («u256_eq» + 1) + («u256_is_zero» + 1) + («memeq» + 1) + («heap_mark» + 1) + («alloc» + 1) + («keccak256» + 1) + («memeq» + 1) + Nat.max ((«heap_release» + 1)) (0) + («header_hash» + 1) + («memeq» + 1) + («heap_release» + 1)

def «hdr_bytes_field» : Nat := («rlp_item» + 1)

def «hdr_raw_field» : Nat := («rlp_item» + 1)

def «hdr_uint_field» : Nat := («rlp_item» + 1)

def «hdr_u256_field» : Nat := («hdr_uint_field» + 1) + («u256_from_be» + 1)

def «hdr_word_field» : Nat := («hdr_uint_field» + 1) + (2 ^ 64 + 1) * (0 + 1)

def «decode_header» : Nat := («rlp_decode_fully» + 1) + («rlp_list_to_slices» + 1) + («alloc» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_u256_field» + 1) + («hdr_word_field» + 1) + («hdr_word_field» + 1) + («hdr_word_field» + 1) + («hdr_uint_field» + 1) + («hdr_word_field» + 1) + («hdr_raw_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_u256_field» + 1) + («hdr_bytes_field» + 1) + («hdr_uint_field» + 1) + («hdr_word_field» + 1) + («hdr_uint_field» + 1) + («hdr_word_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + Nat.max ((«hdr_bytes_field» + 1) + («hdr_uint_field» + 1) + («hdr_word_field» + 1)) (0)

def «validate_headers» : Nat := («alloc» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«decode_header» + 1) + («keccak256» + 1) + 1) + (2 ^ 64 + 1) * ((«memeq» + 1) + 1)

def «ceil_log2» : Nat := (2 ^ 64 + 1) * (0 + 1)

def «ssz_fail» : Nat := 0

def «ssz_split_var_list» : Nat := Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0) + («alloc» + 1) + (2 ^ 64 + 1) * (Nat.max ((«ssz_fail» + 1)) (0) + 1)

def «decode_bytes_list» : Nat := («ssz_split_var_list» + 1) + (2 ^ 64 + 1) * (Nat.max ((«ssz_fail» + 1)) (0) + 1)

def «ssz_check_offsets» : Nat := (2 ^ 64 + 1) * (Nat.max ((«ssz_fail» + 1)) (0) + Nat.max (Nat.max ((«ssz_fail» + 1)) (0)) (0) + 1) + Nat.max ((«ssz_fail» + 1)) (0)

def «ssz_fixed_list_count» : Nat := («udivmod» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0)

def «decode_payload» : Nat := Nat.max ((«ssz_fail» + 1)) (0) + («alloc» + 1) + («ssz_check_offsets» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + («ssz_split_var_list» + 1) + («ssz_fixed_list_count» + 1)

def «decode_requests» : Nat := Nat.max ((«ssz_fail» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1) + («ssz_check_offsets» + 1) + («alloc» + 1) + («ssz_fixed_list_count» + 1) + («ssz_fixed_list_count» + 1) + («ssz_fixed_list_count» + 1) + («ssz_fixed_list_count» + 1) + («ssz_fixed_list_count» + 1)

def «decode_stateless_input» : Nat := Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0) + («ssz_check_offsets» + 1) + («alloc» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + («ssz_check_offsets» + 1) + («decode_payload» + 1) + («ssz_fixed_list_count» + 1) + («decode_requests» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1) + («ssz_check_offsets» + 1) + («decode_bytes_list» + 1) + («decode_bytes_list» + 1) + («decode_bytes_list» + 1)

def «input_blob» : Nat := Nat.max ((«trap_with» + 1)) (0) + («alloc» + 1) + ((domainBytes + 1) + 1) * (0 + 1)

def «host_input_byte» : Nat := 0

def «host_input_le32» : Nat := («host_input_byte» + 1) + («host_input_byte» + 1) + («host_input_byte» + 1) + («host_input_byte» + 1)

def «precheck_host_ssz_header» : Nat := Nat.max ((«ssz_fail» + 1)) (0) + («host_input_byte» + 1) + («host_input_byte» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0) + («host_input_le32» + 1) + («host_input_le32» + 1) + («ssz_check_offsets» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + («host_input_le32» + 1) + («host_input_le32» + 1) + («host_input_le32» + 1) + («ssz_check_offsets» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + («host_input_le32» + 1) + («host_input_le32» + 1) + («host_input_le32» + 1) + («host_input_le32» + 1) + («ssz_check_offsets» + 1)

def «decode_host_input» : Nat := («precheck_host_ssz_header» + 1) + («input_blob» + 1) + («decode_stateless_input» + 1)

end K

end InitECandidate.Solver.Wave8Leaves.S13.Spec
