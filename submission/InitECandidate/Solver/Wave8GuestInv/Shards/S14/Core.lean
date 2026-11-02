import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.GuestUniformClockBound
import Guest.SoftwareAst

/-! Light-cone core helpers and tactics for Wave 8 shard s14 (`wave8/leaves-s14`).
Imports only the light cone (`PanTerminatingBounded`, `GuestUniformClockBound`, `Guest.SoftwareAst`).
Adapted from:
* `wave8/leaves-s11` (`campaign/leaves/s11/Core.lean`): metadata-invariant combinators and tactics.
* `campaign/specs-proposed/GuestInv.lean` (rev7 `7640c93ae` / rev9 `8a79d9f28`): combinators.
* `wave8/leaves-rlp-opus55` (`RlpWalk.lean` / `RlpCore.lean`): structural tactics.
* `wave8/leaves-htab-opus55` (`Base.lean` / `Counter.lean`): `callee_hyp`, `IncrBody`,
  `cmpRank`, `counterGap`, `while_counter`.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S14

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound

/-- Abstract metadata-only invariant property satisfied by `GuestInv`. -/
def MetadataInv (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ {F : Type} {s t : PanSemStateFiniteExact 64 F},
    t.code = s.code → t.memaddrs = s.memaddrs → t.shMemaddrs = s.shMemaddrs →
    t.baseAddr = s.baseAddr → P s → P t

/-- Restated verbatim from `GuestInv.lean`: `fname` is installed and its body is bounded by `K`
from every `P` entry state. -/
def TerminatingFunBoundedOn (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) (K : Nat) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    TerminatingProgBoundedOn P body K

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

theorem metadataInv_evaluate {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P) {F : Type} (s : PanSemStateFiniteExact 64 F) (prog : ProgHOL 64)
    (h : P s) : P (evaluateHOLFiniteState s prog).2 := by
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata s prog
  exact hP hm.1 hm.2.1 hm.2.2.2.1 (evaluate_baseAddr s prog) h

theorem metadataInv_callEntry {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : P s) :
    P (callEntryStateHOLFinite s callee) :=
  hP (s := s) rfl rfl rfl rfl h

theorem metadataInv_with_locals_clock {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : P s) :
    P { s with locals := locals, clock := k } :=
  hP (s := s) rfl rfl rfl rfl h

theorem metadataInv_setVar {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P) {F : Type} (name : MlS) (v : ValueHOL 64)
    (s : PanSemStateFiniteExact 64 F) (h : P s) : P (setVarHOLFinite name v s) :=
  hP (s := s) rfl rfl rfl rfl h

theorem metadataInv_decClock {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P) {F : Type} (s : PanSemStateFiniteExact 64 F) (hs : P s) :
    P (decClockHOLFinite s) :=
  metadataInv_with_locals_clock hP s s.locals _ hs

theorem TerminatingProgBoundedOn.weaken' {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {K K' : Nat} (h : TerminatingProgBoundedOn P prog K) (hle : K ≤ K') :
    TerminatingProgBoundedOn P prog K' :=
  fun s hc hP => (h s hc hP).weaken hle

theorem straightOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (prog : ProgHOL 64) (hs : extStraightLine prog = true) :
    TerminatingProgBoundedOn P prog 0 :=
  fun s hc _ => TerminatingProgBounded.straight prog hs s hc

theorem dec_meta {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    {K : Nat} (hbody : TerminatingProgBoundedOn P body K) :
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
        (metadataInv_with_locals_clock hP state (state.locals.update (name, val)) state.clock hPs) hnt
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem seq_meta {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a)
    (h2 : TerminatingProgBoundedOn P second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hPs
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := metadataInv_evaluate hP state first hPs
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
    obtain ⟨s1, k1⟩ := h1 state hcode hPs hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) hmid hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hPs hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem ite_meta {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {cond : ExpHOL 64}
    {yes no : ProgHOL 64} {a b : Nat}
    (hyes : TerminatingProgBoundedOn P yes a) (hno : TerminatingProgBoundedOn P no b) :
    TerminatingProgBoundedOn P (.ite cond yes no) (max a b) := by
  intro F state hcode hPs
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · revert hnt
    split <;> intro hnt
    · exact TerminatingRunBounded.weaken (hno state hcode hPs) (Nat.le_max_right a b) hnt
    · exact TerminatingRunBounded.weaken (hyes state hcode hPs) (Nat.le_max_left a b) hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem callee_body_bound_meta {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P)
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {ret : ShapeHOL} {B : Nat}
    (hlook : originalRuntimeCode.lookup fname = some (params, body, ret))
    (hbody : TerminatingProgBoundedOn P body B)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (hcode : state.code = originalRuntimeCode)
    (hPs : P state) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    body' = body ∧ TerminatingRunBounded (callEntryStateHOLFinite state callee) body' B := by
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  exact ⟨rfl, hbody (callEntryStateHOLFinite state callee) hcode
    (metadataInv_callEntry hP state callee hPs)⟩

theorem call_meta {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {fname : MlS} {B : Nat} {destination : Option (VarKind × MlS)}
    {arguments : List (ExpHOL 64)} (hf : TerminatingFunBoundedOn P fname B) :
    TerminatingProgBoundedOn P (.call (some (destination, none)) fname arguments) (B + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  intro F state hcode hPs hnt
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
    · obtain ⟨_, hrunBound⟩ := callee_body_bound_meta hP hlook hbody state hcode hPs values body'
        callee ret' hl
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

theorem decCall_meta {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {fname : MlS} {B Bc : Nat} {name : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    (hf : TerminatingFunBoundedOn P fname B)
    (hcont : TerminatingProgBoundedOn P continuation Bc) :
    TerminatingProgBoundedOn P (.decCall name shape fname arguments continuation)
      (B + Bc + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  intro F state hcode hPs hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨hbb, hrunBound⟩ := callee_body_bound_meta hP hlook hbody state hcode hPs values body'
        callee ret' hl
      subst hbb
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee)
          body').1
        have hpost := metadataInv_evaluate hP (callEntryStateHOLFinite state callee) body'
          (metadataInv_callEntry hP state callee hPs)
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
              have hresInv : P resumed :=
                metadataInv_setVar hP name value _
                  (metadataInv_with_locals_clock hP post state.locals post.clock hpost)
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

/-! ### `while` ranking and counted loops -/

def LoopActive (condition : ExpHOL 64) {F : Type} (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ word : BitVec 64,
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) ∧ word ≠ 0

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

theorem while_rank_aux
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
        μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s) :
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
            obtain ⟨hPpost, hlt⟩ := hstep' hflow
            have hsame := hunfold hflow
            have hntPost : (evaluateHOLFiniteState post (.while condition body)).1 ≠
                some .timeOut := by
              rw [← hsame]; exact hnt0
            obtain ⟨htail, htailKept⟩ := ih post (hmeta.trans hcode) hPpost
              (fun _ => by omega) hntPost
            have hmul : n * (B + 1) + (B + 1) = (n + 1) * (B + 1) := by
              rw [Nat.succ_mul]
            exact ⟨by omega, by omega⟩
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
  fun state hcode hP =>
    while_rank_aux μ (fun s hc hPs _ => hbody (decClockHOLFinite s) hc (hdec s hPs))
      hstep (N + 1) state hcode hP (fun hact => by have := hle state hcode hP hact; omega)

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

/-- Bodies whose normal completion runs `c = c + 1` last, and which never yield `continue`. -/
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
    refine ⟨hcont, fun hn => ?_⟩
    rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
    rw [hrun] at hn
    dsimp only at hn ⊢
    subst hn
    obtain ⟨_, resumed, inner, hloc, _, hcr, hpost⟩ :=
      decCall_flowing (Or.inl rfl) hrun
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

theorem while_counter_meta {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P) (op : Cmp) (hop : op = .less ∨ op = .lower) (i X : MlS)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn P body B) (hinc : IncrBody i body)
    (hX : avoidsLocal X body = true) :
    TerminatingProgBoundedOn P (.while (.cmp op (.var .local i) (.var .local X)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (counterGap op i X)
    (fun s hs => metadataInv_decClock hP s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [counterGap]
    split
    · rename_i a b _ _
      have := cmpRank_le op b
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨metadataInv_evaluate hP _ _ (metadataInv_decClock hP s hs), ?_⟩
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

def counterGapConst (op : Cmp) (i : MlS) (b : BitVec 64) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup i with
  | some (.val (.word a)) => cmpRank op b - cmpRank op a
  | _ => 0

theorem while_counter_const_meta {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P) (op : Cmp) (hop : op = .less ∨ op = .lower) (i : MlS) (b : BitVec 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn P body B) (hinc : IncrBody i body) :
    TerminatingProgBoundedOn P (.while (.cmp op (.var .local i) (.const b)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (counterGapConst op i b)
    (fun s hs => metadataInv_decClock hP s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [counterGapConst]
    split
    · have := cmpRank_le op b
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨metadataInv_evaluate hP _ _ (metadataInv_decClock hP s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, b', ha, hb, hword⟩ := evalAt_cmp s op _ _ word hw
    simp only [evalAt, evalHOLExact] at ha hb
    have hia : s.locals.lookup i = some (.val (.word a)) := by simpa using ha
    have hbb : b' = b := by
      injection hb with h1
      injection h1 with h2
      injection h2 with h3
      exact h3.symm
    subst b'
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
    have hsucc := cmpRank_succ op a b hlt
    simp only [counterGapConst, hi', hia]
    omega

open Lean Elab Tactic Meta in
/-- Close `TerminatingFunBoundedOn P (ofString "f") ?B` by the local hypothesis about the
syntactically same function name. -/
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

macro "incr_body" : tactic => `(tactic| repeat (first
  | exact IncrBody.incr
  | apply IncrBody.dec _ _ _ (by decide)
  | apply IncrBody.decCall _ _ _ _ (by decide)
  | apply IncrBody.seq _ rfl rfl))

syntax "fb_auto " ident : tactic
macro_rules
  | `(tactic| fb_auto $hP) => `(tactic| first
      | exact straightOn _ rfl
      | (apply seq_meta $hP
         · fb_auto $hP
         · fb_auto $hP)
      | (apply ite_meta
         · fb_auto $hP
         · fb_auto $hP)
      | (apply dec_meta $hP; fb_auto $hP)
      | (apply call_meta $hP; callee_hyp)
      | (apply decCall_meta $hP
         · callee_hyp
         · fb_auto $hP)
      | (apply while_counter_meta $hP .less (Or.inl rfl)
         · fb_auto $hP
         · incr_body
         · rfl)
      | (apply while_counter_meta $hP .lower (Or.inr rfl)
         · fb_auto $hP
         · incr_body
         · rfl)
      | (apply while_counter_const_meta $hP .less (Or.inl rfl)
         · fb_auto $hP
         · incr_body)
      | (apply while_counter_const_meta $hP .lower (Or.inr rfl)
         · fb_auto $hP
         · incr_body))

syntax "fb_unfold " num ident : tactic
macro_rules
  | `(tactic| fb_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expFieldListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expFieldToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
         List.map, Option.map]))

syntax "fb_arith" : tactic
macro_rules
  | `(tactic| fb_arith) => `(tactic|
      first
      | omega
      | (simp only [Nat.max_def, max_def]; (try split_ifs) <;> omega))

syntax "fb_prove " ident num ident : tactic
macro_rules
  | `(tactic| fb_prove $hP $idx $fn) => `(tactic|
      (fb_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fb_auto $hP
       · fb_arith))

end InitECandidate.Solver.Wave8Leaves.S14
