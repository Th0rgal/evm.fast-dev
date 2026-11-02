import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.GuestUniformClockBound
import Guest.SoftwareAst

/-! Light-cone infrastructure and counter-loop lemmas for shard s01 (`wave8/leaves-s01`).

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

namespace InitECandidate.Solver.Wave8GuestInv.S01

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

/-! ## 2. Restated `K.*` bounds for shard s01 and its callees (from `GuestInv.lean` §6) -/

namespace K

def «trap_with» : Nat := 0
def «alloc» : Nat := Nat.max ((«trap_with» + 1)) (0) + Nat.max ((«trap_with» + 1)) (0)
def «mpt_fail» : Nat := 0
def «memcpy» : Nat := Nat.max (((domainBytes + 1) + 1) * (0 + 1) + ((domainBytes + 1) + 1) * (0 + 1)) (0) + ((domainBytes + 1) + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)
def «memzero» : Nat := Nat.max (((domainBytes + 1) + 1) * (0 + 1) + ((domainBytes + 1) + 1) * (0 + 1)) (0) + ((domainBytes + 1) + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)
def «key_to_nibbles» : Nat := ((domainBytes + 1) + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)
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
def «htab_get» : Nat := («htab_find_leaf» + 1) + («memeq» + 1)
def «keccak_f1600» : Nat := (2 ^ 64 + 1) * (0 + 1)
def «keccak_absorb_block» : Nat := (2 ^ 64 + 1) * (0 + 1) + («keccak_f1600» + 1)
def «keccak256» : Nat := («memzero» + 1) + ((domainBytes + 1) + 1) * ((«keccak_absorb_block» + 1) + 1) + («memzero» + 1) + («memcpy» + 1) + («keccak_absorb_block» + 1) + Nat.max (0) ((«memcpy» + 1))
def «htab_first_diff» : Nat := ((domainBytes + 1) + 1) * (Nat.max ((8 + 1) * (0 + 1)) (0) + 1)
def «htab_grow» : Nat := («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1)
def «htab_new_node» : Nat := Nat.max ((«htab_grow» + 1)) (0)
def «htab_new_internal» : Nat := («htab_new_node» + 1)
def «htab_new_leaf» : Nat := («htab_new_node» + 1) + («memcpy» + 1)
def «htab_set» : Nat := («htab_find_leaf» + 1) + Nat.max ((«htab_new_leaf» + 1)) (0) + («memeq» + 1) + («htab_first_diff» + 1) + (7776239486 + 1) * (0 + 1) + («htab_new_leaf» + 1) + («htab_new_internal» + 1)
def «record_pre_state_read» : Nat := («htab_set» + 1)
def «decode_account_from_leaf» : Nat := («rlp_decode_fully» + 1) + («mpt_fail» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («rlp_list_to_slices» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («rlp_item» + 1) + («rlp_item» + 1) + («rlp_item» + 1) + («rlp_item» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + Nat.max ((«mpt_fail» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («memzero» + 1) + (2 ^ 64 + 1) * (0 + 1) + Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0)) + Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0))
def «heap_mark» : Nat := 0
def «heap_release» : Nat := 0
def «trie_walk» : Nat := (71723149827058354885847154688 + 1) * (Nat.max ((«mpt_fail» + 1)) (0) + Nat.max (Nat.max ((«memeq» + 1)) (0)) (0) + Nat.max ((«memeq» + 1)) (0) + 1)
def «trie_lookup» : Nat := («key_to_nibbles» + 1) + («trie_walk» + 1)
def «ws_account_leaf» : Nat := («heap_mark» + 1) + («alloc» + 1) + («keccak256» + 1) + («trie_lookup» + 1) + («heap_release» + 1)
def «ws_get_account_optional» : Nat := («ws_account_leaf» + 1) + («alloc» + 1) + («decode_account_from_leaf» + 1)
def «ws_storage_root_of» : Nat := («ws_get_account_optional» + 1)
def «ws_account_has_storage» : Nat := («ws_storage_root_of» + 1) + («memeq» + 1)
def «account_has_storage» : Nat := («htab_get» + 1) + («htab_get» + 1) + («record_pre_state_read» + 1) + («ws_account_has_storage» + 1)
def «acct_new» : Nat := («alloc» + 1)
def «acct_empty» : Nat := («acct_new» + 1)
def «get_pre_state_account_optional» : Nat := («htab_set» + 1) + («htab_get» + 1) + («record_pre_state_read» + 1) + («ws_get_account_optional» + 1)
def «get_account_optional» : Nat := («htab_set» + 1) + («htab_get» + 1) + («get_pre_state_account_optional» + 1)
def «get_account» : Nat := («get_account_optional» + 1) + Nat.max ((«acct_empty» + 1)) (0)
def «account_deployable» : Nat := («get_account» + 1) + («memeq» + 1) + («account_has_storage» + 1)
def «account_exists» : Nat := («get_account_optional» + 1)
def «acct_copy» : Nat := («alloc» + 1) + («memcpy» + 1)
def «u256_is_zero» : Nat := 0
def «acct_is_empty» : Nat := («memeq» + 1) + («u256_is_zero» + 1)
def «htab_new» : Nat := («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1)
def «lst_new» : Nat := («alloc» + 1) + («alloc» + 1)
def «bal_ensure_account» : Nat := («htab_get» + 1) + («alloc» + 1) + («htab_new» + 1) + («htab_new» + 1) + («lst_new» + 1) + («lst_new» + 1) + («lst_new» + 1) + («htab_set» + 1)
def «lst_push» : Nat := Nat.max ((«alloc» + 1) + («memcpy» + 1)) (0)
def «lst_upsert_idx» : Nat := (2 ^ 64 + 1) * (0 + 1) + («lst_push» + 1)
def «add_balance_change» : Nat := («bal_ensure_account» + 1) + («lst_upsert_idx» + 1)
def «add_code_change» : Nat := («bal_ensure_account» + 1) + («lst_upsert_idx» + 1)
def «add_nonce_change» : Nat := («bal_ensure_account» + 1) + (2 ^ 64 + 1) * (0 + 1) + («lst_push» + 1)
def «add_sat» : Nat := 0
def «add_storage_read» : Nat := («bal_ensure_account» + 1) + («htab_set» + 1)
def «add_storage_write» : Nat := («bal_ensure_account» + 1) + («htab_get» + 1) + Nat.max ((«lst_new» + 1) + («htab_set» + 1)) (0) + («lst_upsert_idx» + 1)
def «add_to_bloom» : Nat := («heap_mark» + 1) + («alloc» + 1) + («keccak256» + 1) + (2 ^ 64 + 1) * (0 + 1) + («heap_release» + 1)
def «add_touched_account» : Nat := («bal_ensure_account» + 1)
def «st_be32» : Nat := 0
def «bswap64» : Nat := 0
def «st_be64» : Nat := Nat.max ((«bswap64» + 1)) (0) + («st_be32» + 1) + («st_be32» + 1)
def «addr_from_words» : Nat := («st_be32» + 1) + («st_be64» + 1) + («st_be64» + 1)

end K

/-! ## 3. Unconditional bounds & function lookup helpers -/

theorem onOf {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {p : ProgHOL 64} {K : Nat}
    (h : TerminatingProgBounded p K) : TerminatingProgBoundedOn P p K :=
  fun s hcode _ => h s hcode

theorem straightOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (p : ProgHOL 64)
    (hs : extStraightLine p = true) : TerminatingProgBoundedOn P p 0 :=
  onOf (TerminatingProgBounded.straight p hs)

theorem funOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {f : MlS} {K K' : Nat}
    (h : FunBounded f K) (hle : K ≤ K') : TerminatingFunBoundedOn P f K' :=
  (TerminatingFunBoundedOn.of_unconditional (terminatingFunBounded_of_funBounded h)).weaken hle

theorem TerminatingProgBoundedOn.weakenK {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {K K' : Nat} (h : TerminatingProgBoundedOn P p K) (hle : K ≤ K') :
    TerminatingProgBoundedOn P p K' :=
  fun s hcode hP => (h s hcode hP).weaken hle

theorem onFun_of_guestAst {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (K : Nat)
    (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hprog : TerminatingProgBoundedOn P
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) K) :
    TerminatingFunBoundedOn P (ofString (extractFn d).name) K :=
  ⟨_, _, _, InitECandidate.Solver.GuestTrapAndLookup.lookup_of_guestAst_getElem i hi (extractFn d) hd,
    hprog⟩

theorem onFun_le {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (K : Nat)
    (hd : Guest.Software.guestAst[i] = .function (extractFn d)) {K' : Nat}
    (hprog : TerminatingProgBoundedOn P
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) K')
    (hle : K' ≤ K) :
    TerminatingFunBoundedOn P (ofString (extractFn d).name) K :=
  (onFun_of_guestAst i hi d K' hd hprog).weaken hle

/-! ## 4. Tactics for walking loop-free subprograms -/

open Lean Elab Tactic Meta in
elab "callee_hyp" : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  unless g.isAppOfArity ``TerminatingFunBoundedOn 3 do throwError "callee_hyp: bad goal"
  let fn := g.getAppArgs[1]!
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``TerminatingFunBoundedOn 3 && t.getAppArgs[1]! == fn then
      if ← isDefEq t g then
        (← getMainGoal).assign d.toExpr
        replaceMainGoal []
        return
  throwError "callee_hyp: no hypothesis for {fn}"

macro "htab_walk" : tactic => `(tactic| repeat (first
  | exact straightOn _ rfl
  | apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
  | apply TerminatingProgBoundedOn.seq_guestInv
  | apply TerminatingProgBoundedOn.ite_on
  | (apply TerminatingProgBoundedOn.decCall_guestInv; case hf => callee_hyp)
  | (apply TerminatingProgBoundedOn.call_guestInv; case hf => callee_hyp)
  | (apply TerminatingProgBoundedOn.tailCall_guestInv; case hf => callee_hyp)))

macro "htab_bound" k:ident : tactic => `(tactic| (simp only [$k:ident, Nat.max_def]; (try split_ifs) <;> omega))

macro "htab_unfold" d:ident : tactic => `(tactic| dsimp only [extractFn, $d:ident,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map])

/-! ## 5. Counted loops `while i < X` with step 1 -/

inductive IncrBody (c : MlS) : ProgHOL 64 → Prop
  | incr : IncrBody c (.assign .local c (.op .add [.var .local c, .const 1]))
  | seq (first : ProgHOL 64) {tail : ProgHOL 64}
      (avoid : avoidsLocal c first = true) (noCont : noTopContinue first = true)
      (rest : IncrBody c tail) : IncrBody c (.seq first tail)
  | dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
      (distinct : c ≠ name) (rest : IncrBody c body) : IncrBody c (.dec name shape init body)
  | decCall (name : MlS) (shape : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64))
      {cont : ProgHOL 64} (distinct : c ≠ name) (rest : IncrBody c cont) :
      IncrBody c (.decCall name shape fn args cont)

theorem IncrBody.run {c : MlS} {body : ProgHOL 64} (hb : IncrBody c body) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      state.locals.lookup c = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup c = some (.val (.word (w + 1)))) := by
  induction hb with
  | incr =>
    intro F state w atC
    have run : evaluateHOLFiniteState state
        (.assign .local c (.op .add [.var .local c, .const 1])) =
        (none, setVarHOLFinite c (.val (.word (w + 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atC, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [run]
    refine ⟨by simp, fun _ => ?_⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | seq first avoid noCont rest ih =>
    intro F state w atC
    have frame := evaluate_avoidsLocal_flowing c first avoid state
    have noContinue := evaluate_noTopContinue first noCont state
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at frame noContinue
      dsimp only at frame noContinue
      cases result with
      | none =>
        dsimp only
        have kept := frame (Or.inl rfl)
        exact ih middle w (by rw [kept]; exact atC)
      | some r =>
        dsimp only
        exact ⟨noContinue, fun h => by simp at h⟩
  | dec name shape init distinct rest ih =>
    intro F state w atC
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact ⟨by simp, by simp⟩
    · rename_i val _
      split
      · have atInner : (setVarHOLFinite name val state).locals.lookup c =
            some (.val (.word w)) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, atC]
        obtain ⟨t1, t2⟩ := ih (setVarHOLFinite name val state) w atInner
        cases run : evaluateHOLFiniteState (setVarHOLFinite name val state) _ with
        | mk res post =>
          rw [run] at t1 t2
          dsimp only at t1 t2 ⊢
          refine ⟨t1, fun normal => ?_⟩
          rw [PanRunBounded.resVarEq_lookup, if_neg distinct]
          exact t2 normal
      · exact ⟨by simp, by simp⟩
  | @decCall name shape fn args cont distinct rest ih =>
    intro F state w atC
    have hcont : (evaluateHOLFiniteState state (.decCall name shape fn args cont)).1 ≠
        some .continue := by
      intro hc
      rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
      rw [hrun] at hc
      dsimp only at hc
      subst hc
      obtain ⟨_, resumed, inner, hloc, _, hcr, _⟩ :=
        decCall_flowing (Or.inr (Or.inr rfl)) hrun
      have atR : resumed.locals.lookup c = some (.val (.word w)) := (hloc c distinct).trans atC
      have := (ih resumed w atR).1
      rw [hcr] at this
      exact this rfl
    refine ⟨hcont, fun hnone => ?_⟩
    rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
    rw [hrun] at hnone
    dsimp only at hnone
    subst hnone
    obtain ⟨_, resumed, inner, hloc, _, hcr, hpost⟩ := decCall_flowing (Or.inl rfl) hrun
    have atR : resumed.locals.lookup c = some (.val (.word w)) := (hloc c distinct).trans atC
    have := (ih resumed w atR).2
    rw [hcr] at this
    rw [hpost, PanRunBounded.resVarEq_lookup, if_neg distinct]
    exact this rfl

def cmpRank (op : Cmp) (a : BitVec 64) : Nat :=
  match op with
  | .less => (a.toNat + 2 ^ 63) % 2 ^ 64
  | _ => a.toNat

theorem cmpRank_lt (op : Cmp) (hop : op = .less ∨ op = .lower) (a b : BitVec 64)
    (h : Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b = true) : cmpRank op a < cmpRank op b := by
  have ha := a.isLt
  have hb := b.isLt
  rcases hop with rfl | rfl
  · simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      Flapjack.Compiler.Encoders.Asm.holAsmSignedLess] at h
    simp only [cmpRank]
    split_ifs at h <;> simp_all <;> omega
  · simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, decide_eq_true_eq, BitVec.lt_def] at h
    simp only [cmpRank]
    omega

theorem cmpRank_succ (op : Cmp) (a b : BitVec 64) (h : cmpRank op a < cmpRank op b) :
    cmpRank op (a + 1) = cmpRank op a + 1 := by
  have ha := a.isLt
  have hb := b.isLt
  have hs : (a + 1).toNat = (a.toNat + 1) % 2 ^ 64 := by simp [BitVec.toNat_add]
  cases op <;> simp only [cmpRank] at h ⊢ <;> omega

theorem cmpRank_le (op : Cmp) (a : BitVec 64) : cmpRank op a < 2 ^ 64 := by
  have := a.isLt
  cases op <;> simp only [cmpRank] <;> omega

def counterGap (op : Cmp) (i X : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup i, s.locals.lookup X with
  | some (.val (.word a)), some (.val (.word b)) => cmpRank op b - cmpRank op a
  | _, _ => 0

theorem while_counter_guestInv {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    [IsGuestInv GuestInv] (op : Cmp) (hop : op = .less ∨ op = .lower) (i X : MlS)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B) (hinc : IncrBody i body)
    (hX : avoidsLocal X body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp op (.var .local i) (.var .local X)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (counterGap op i X)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [counterGap]
    split
    · rename_i a b _ _
      have := cmpRank_le op b
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, b, ha, hb, hword⟩ := evalAt_cmp s op _ _ word hw
    simp only [evalAt, evalHOLExact] at ha hb
    have hia : s.locals.lookup i = some (.val (.word a)) := by simpa using ha
    have hXb : s.locals.lookup X = some (.val (.word b)) := by simpa using hb
    have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt := cmpRank_lt op hop a b hcmp
    obtain ⟨hnc, hinc'⟩ := hinc.run (decClockHOLFinite s) a hia
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc
    have hi' := hinc' hnone
    have hX' := evaluate_avoidsLocal_flowing X body hX (decClockHOLFinite s)
      (Or.inl hnone)
    have hX'' : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup X =
        some (.val (.word b)) := hX'.trans hXb
    have hsucc := cmpRank_succ op a b hlt
    simp only [counterGap, hi', hX'', hia, hXb]
    omega

macro "incr_body" : tactic => `(tactic| repeat (first
  | exact IncrBody.incr
  | apply IncrBody.dec _ _ _ (by decide)
  | apply IncrBody.decCall _ _ _ _ (by decide)
  | apply IncrBody.seq _ rfl rfl))

macro "counted_while" : tactic => `(tactic|
  (apply while_counter_guestInv .less (Or.inl rfl)
   · htab_walk
   · incr_body
   · rfl))

/-! ## 6. Signed counter loops with general step -/

def CounterAdd (counter : MlS) (step : BitVec 64) (body : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
    s.locals.lookup counter = some (.val (.word w)) →
    let out := evaluateHOLFiniteState s body
    (out.1 = none ∨ out.1 = some .continue) →
    out.2.locals.lookup counter = some (.val (.word (w + step)))

theorem CounterAdd.assign (counter : MlS) (step : BitVec 64) :
    CounterAdd counter step (.assign .local counter (.op .add [.var .local counter, .const step])) := by
  intro F s w hlocal
  have run : evaluateHOLFiniteState s
      (.assign .local counter (.op .add [.var .local counter, .const step])) =
      (none, setVarHOLFinite counter (.val (.word (w + step))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
      hlocal, wordOpHOL, wordOp, valueIsWord, valueWord,
      lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [run]
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem CounterAdd.seq (counter : MlS) (step : BitVec 64) (first : ProgHOL 64)
    {rest : ProgHOL 64} (havoid : avoidsLocal counter first = true)
    (hnocont : noTopContinue first = true) (hrest : CounterAdd counter step rest) :
    CounterAdd counter step (.seq first rest) := by
  intro F s w hlocal
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780]
  cases hrun : evaluateHOLFiniteState s first with
  | mk r mid =>
    have hkeep := evaluate_avoidsLocal_flowing counter first havoid s
    have hnc := evaluate_noTopContinue first hnocont s
    rw [hrun] at hkeep hnc
    cases r with
    | none =>
      dsimp only at hkeep ⊢
      exact hrest mid w ((hkeep (Or.inl rfl)).trans hlocal)
    | some result =>
      dsimp only at hnc ⊢
      intro hflow
      rcases hflow with h | h
      · cases h
      · exact False.elim (hnc h)

theorem CounterAdd.dec (counter : MlS) (step : BitVec 64) (name : MlS)
    (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (hne : counter ≠ name) (hbody : CounterAdd counter step body) :
    CounterAdd counter step (.dec name shape init body) := by
  intro F s w hlocal
  dsimp only
  intro hflow
  cases hrun : evaluateHOLFiniteState s (.dec name shape init body) with
  | mk result post =>
    rw [hrun] at hflow
    dsimp only at hflow ⊢
    obtain ⟨value, inner, hinner, hrestore⟩ :=
      dec_flowing (hflow.elim Or.inl (fun h => Or.inr (Or.inr h))) hrun
    have hentry : (setVarHOLFinite name value s).locals.lookup counter = some (.val (.word w)) := by
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne] using hlocal
    have h := hbody (setVarHOLFinite name value s) w hentry
    dsimp only at h
    rw [hinner] at h
    dsimp only at h
    rw [hrestore, InitECandidate.Solver.PanRunBounded.resVarEq_lookup]
    simpa [hne] using h hflow

private theorem signed_less_eq (left right : BitVec 64) :
    holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

theorem cmp_counter_active {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (op : Cmp) (bound : ExpHOL 64) (result : BitVec 64)
    (hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp op (.var .local counter) bound) = some (.val (.word result)))
    (hnz : result ≠ 0) :
    ∃ w v : BitVec 64, s.locals.lookup counter = some (.val (.word w)) ∧
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) bound = some (.val (.word v)) ∧
      wordCmpHOL op w v = true := by
  change evalAt s _ = _ at hc
  obtain ⟨w, v, hw, hv, hword⟩ := evalAt_cmp s op _ _ result hc
  simp only [evalAt, evalHOLExact] at hw
  have hwl : s.locals.lookup counter = some (.val (.word w)) := by simpa using hw
  have hcmp : wordCmpHOL op w v = true := by
    by_contra h
    simp [h] at hword
    exact hnz hword
  exact ⟨w, v, hwl, hv, hcmp⟩

private def signedUpRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => (9223372036854775807 - w.toInt).toNat
  | _ => 0

private theorem signedUpRank_le (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    signedUpRank counter s ≤ 2 ^ 64 := by
  unfold signedUpRank
  split
  · rename_i w h
    have := BitVec.le_toInt w
    omega
  · omega

theorem while_up_signed_guestInv {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    [IsGuestInv GuestInv] (counter : MlS) (step : BitVec 64) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat} (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hadd : CounterAdd counter step body) (hstep : 0 < step.toInt)
    (hbound : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : BitVec 64),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) bound = some (.val (.word v)) →
      v.toInt + step.toInt ≤ 9223372036854775808) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp .less (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (signedUpRank counter)
    (fun s hs => guestInv_decClock s hs) hbody
    (fun s _ _ _ => signedUpRank_le counter s) ?_
  intro F s _ hs ⟨result, hcond, hnz⟩ hflow
  refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
  obtain ⟨w, v, hl, hv, hcmp⟩ := cmp_counter_active s counter .less bound result hcond hnz
  have hlt : w.toInt < v.toInt := by
    simpa only [wordCmpHOL, signed_less_eq, BitVec.slt_iff_toInt_lt] using hcmp
  have hlim := hbound s v hv
  have hwmin := BitVec.le_toInt w
  have hwmax := BitVec.toInt_le (x := w)
  have hnext : (w + step).toInt = w.toInt + step.toInt := by
    rw [BitVec.toInt_add]
    apply Int.bmod_eq_of_le <;> omega
  have hl' : (decClockHOLFinite s).locals.lookup counter = some (.val (.word w)) := hl
  have heffect := hadd (decClockHOLFinite s) w hl' hflow
  simp only [signedUpRank, heffect, hl, hnext]
  omega

macro "counter_add" : tactic => `(tactic| repeat (first
  | exact CounterAdd.assign _ _
  | apply CounterAdd.dec _ _ _ _ _ (by decide)
  | apply CounterAdd.seq _ _ _ (by decide) (by decide)))

end InitECandidate.Solver.Wave8GuestInv.S01
