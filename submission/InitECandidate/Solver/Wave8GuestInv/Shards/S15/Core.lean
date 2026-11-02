import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.GuestUniformClockBound
import Guest.SoftwareAst

/-! Light-cone core helpers and tactics for Wave 8 shard s15 (`wave8/leaves-s15`).
Imports only the light cone (`PanTerminatingBounded`, `GuestUniformClockBound`, `Guest.SoftwareAst`).
Adapted from `campaign/leaves/s14/Core.lean` and `campaign/specs-proposed/GuestInv.lean`, extended
with `shMemStore_locals_flowing` so `output_write`'s shared-memory store loop is handled uniformly.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S15

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

/-! ### `while` ranking and shared-memory counter loop -/

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

private theorem shMemStoreHOLExact_locals {F : Type}
    (state : PanSemStateExact 64 F) [DecidablePred state.shMemaddrs]
    (word address : BitVec 64) (nb : Nat) :
    (shMemStoreHOLExact state word address nb).2.locals = state.locals := by
  unfold shMemStoreHOLExact
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · split <;> rfl
    · rfl

theorem evaluate_shMemStore_locals {F : Type}
    (state : PanSemStateFiniteExact 64 F) (operator : OpSize) (address value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemStore operator address value)).2.locals = state.locals := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · apply HolFiniteMapExact.ext
    change (shMemStoreHOLExact state.toExact _ _ (nbOpHOL operator)).2.locals = state.locals.lookup
    exact shMemStoreHOLExact_locals state.toExact _ _ (nbOpHOL operator)
  · rfl

def lowerGap (i X : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup i, s.locals.lookup X with
  | some (.val (.word a)), some (.val (.word b)) => b.toNat - a.toNat
  | _, _ => 0

theorem while_shMemStore_lower {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P) (i X : MlS) (hdist : i ≠ X)
    (op : OpSize) (addr val : ExpHOL 64) :
    TerminatingProgBoundedOn P
      (.while (.cmp .lower (.var .local i) (.var .local X))
        (.seq (.shMemStore op addr val)
          (.assign .local i (.op .add [.var .local i, .const 1#64]))))
      ((2 ^ 64 + 1) * (0 + 1)) := by
  let body : ProgHOL 64 :=
    .seq (.shMemStore op addr val) (.assign .local i (.op .add [.var .local i, .const 1#64]))
  have hbody : TerminatingProgBoundedOn P body 0 := straightOn body rfl
  apply TerminatingProgBoundedOn.while_rank (lowerGap i X)
    (fun s hs => metadataInv_decClock hP s hs) hbody
  · intro F s _ _ _
    simp only [lowerGap]
    split
    · rename_i a b _ _
      have := b.isLt
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨metadataInv_evaluate hP _ _ (metadataInv_decClock hP s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, b, ha, hb, hword⟩ := evalAt_cmp s .lower _ _ word hw
    simp only [evalAt, evalHOLExact] at ha hb
    have hia : s.locals.lookup i = some (.val (.word a)) := by simpa using ha
    have hXb : s.locals.lookup X = some (.val (.word b)) := by simpa using hb
    have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower a b = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt : a.toNat < b.toNat := by
      simpa [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, decide_eq_true_eq, BitVec.lt_def] using hcmp
    have hnc : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 ≠ some .continue :=
      evaluate_noTopContinue body rfl (decClockHOLFinite s)
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc
    dsimp only [body] at hnone ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
    have hloc1 := evaluate_shMemStore_locals (decClockHOLFinite s) op addr val
    rcases hst : evaluateHOLFiniteState (decClockHOLFinite s) (.shMemStore op addr val) with ⟨r1, mid⟩
    rw [hst] at hnone hloc1
    cases r1 with
    | some _ => simp at hnone
    | none =>
      dsimp only at hnone hloc1 ⊢
      have hmid_loc : mid.locals = s.locals := hloc1
      have hmid_i : mid.locals.lookup i = some (.val (.word a)) := by rw [hmid_loc]; exact hia
      have hrun2 : evaluateHOLFiniteState mid
          (.assign .local i (.op .add [.var .local i, .const 1#64])) =
          (none, setVarHOLFinite i (.val (.word (a + 1#64))) mid) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hmid_i, wordOpHOL,
          wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
          setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      rw [hrun2]
      dsimp only
      have hpost_i : (setVarHOLFinite i (.val (.word (a + 1#64))) mid).locals.lookup i =
          some (.val (.word (a + 1#64))) := by
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hpost_X : (setVarHOLFinite i (.val (.word (a + 1#64))) mid).locals.lookup X =
          some (.val (.word b)) := by
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdist, hmid_loc, hXb]
      have ha1 : (a + 1#64).toNat = a.toNat + 1 := by
        have hb_lt := b.isLt
        rw [BitVec.toNat_add_of_lt]
        · simp
        · simp; omega
      simp only [lowerGap, hpost_i, hpost_X, hia, hXb, ha1]
      omega

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
      | exact while_shMemStore_lower $hP _ _ (by decide) _ _ _)

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

end InitECandidate.Solver.Wave8Leaves.S15
