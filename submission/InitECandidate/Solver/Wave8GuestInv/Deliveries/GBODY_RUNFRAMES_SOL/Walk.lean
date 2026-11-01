import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.Base

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.RunFramesRace
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- Costs of the four direct callees; no callee implementation is inspected. -/
def charge (f : MlS) : Nat :=
  if f = ofString "op_dispatch" then K.op_dispatch else
  if f = ofString "finish_child" then K.finish_child else
  if f = ofString "frame_epilogue" then K.frame_epilogue else
  if f = ofString "frame_exception" then K.frame_exception else 0

theorem charge_op_dispatch : charge (ofString "op_dispatch") = K.op_dispatch := by
  simp only [charge, if_pos rfl, ite_true]

theorem charge_finish_child : charge (ofString "finish_child") = K.finish_child := by
  simp only [charge, if_neg (show ofString "finish_child" ≠ ofString "op_dispatch" from by decide), if_pos rfl, ite_true]

theorem charge_frame_epilogue : charge (ofString "frame_epilogue") = K.frame_epilogue := by
  simp only [charge, if_neg (show ofString "frame_epilogue" ≠ ofString "op_dispatch" from by decide), if_neg (show ofString "frame_epilogue" ≠ ofString "finish_child" from by decide), if_pos rfl, ite_true]

theorem charge_frame_exception : charge (ofString "frame_exception") = K.frame_exception := by
  simp only [charge, if_neg (show ofString "frame_exception" ≠ ofString "op_dispatch" from by decide), if_neg (show ofString "frame_exception" ≠ ofString "finish_child" from by decide), if_neg (show ofString "frame_exception" ≠ ofString "frame_epilogue" from by decide), if_pos rfl, ite_true]

/-- The frozen spec's structural clock accounting, restricted to the loop-free body. -/
def walkCost : ProgHOL 64 → Nat
  | .seq a b => walkCost a + walkCost b
  | .ite _ a b => max (walkCost a) (walkCost b)
  | .dec _ _ _ b => walkCost b
  | .call (some (_, some (_, _, h))) f _ => (charge f + 1) + walkCost h
  | .call _ f _ => charge f + 1
  | _ => 0

/-- A guard-carrying Hoare derivation with its structural clock bound. -/
structure BHoare (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (prog : ProgHOL 64)
    (Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) : Prop where
  hoare : Hoare P prog Q
  bounded : TerminatingProgBoundedOn P prog (walkCost prog)

section Rules
variable {P P' R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
  {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}

theorem BHoare.of_bound {prog : ProgHOL 64}
    (hb : TerminatingProgBoundedOn P prog (walkCost prog)) (h : Hoare P prog Q) :
    BHoare P prog Q := ⟨h, hb⟩

theorem BHoare.skip
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q none s) :
    BHoare P .skip Q := by
  exact ⟨Hoare.skip h, TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)⟩

theorem BHoare.seq {first second : ProgHOL 64}
    (h1 : BHoare P first fun r t => (r = none → R t) ∧ (r ≠ none → Q r t))
    (h2 : BHoare R second Q) : BHoare P (.seq first second) Q := by
  refine ⟨Hoare.seq h1.hoare h2.hoare, ?_⟩
  intro F state hcode hP hnt
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    have hp := h1.hoare.run state hcode hP hnt1
    rw [hr1] at hp
    obtain ⟨s1, k1⟩ := h1.bounded state hcode hP hnt1
    rw [hr1] at s1 k1
    obtain ⟨s2, k2⟩ := h2.bounded mid (hmeta.1.trans hcode) (hp.1 rfl) hnt
    exact ⟨by change state.clock ≤ _ + (walkCost first + walkCost second); dsimp only at s1 k1; omega,
      by dsimp only at k1; omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1.bounded state hcode hP hnt1
    rw [hr1] at s1 k1
    exact ⟨by change state.clock ≤ _ + (walkCost first + walkCost second); dsimp only at s1; omega, k1⟩

theorem BHoare.ite {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : BHoare (fun s => P s ∧ CondTrue cond s) yes Q)
    (hno : BHoare (fun s => P s ∧ CondFalse cond s) no Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    BHoare P (.ite cond yes no) Q := by
  exact ⟨Hoare.ite hyes.hoare hno.hoare herr,
    TerminatingProgBoundedOn.ite_cond_on hyes.bounded hno.bounded⟩

theorem BHoare.dec {names : List String} {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64}
    {body : ProgHOL 64} (hname : ∀ n ∈ names, ofString n ≠ name)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some v → P' (setVarHOLFinite name v s))
    (hbody : BHoare P' body Q) (hQ : PostLocalsOnly names Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    BHoare P (.dec name shape init body) Q := by
  refine ⟨Hoare.dec hname hinit hbody.hoare hQ herr, ?_⟩
  intro F state hcode hPs hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i val hv _
      have hb := hbody.bounded (setVarHOLFinite name val state) hcode (hinit state val hPs hv) hnt
      simpa only [setVarHOLFinite, walkCost] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem BHoare.assign {kind : VarKind} {name : MlS} {source : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) source =
        some v → Q none (setKvarHOLFinite kind name v s))
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    BHoare P (.assign kind name source) Q := by
  exact ⟨Hoare.assign h herr, TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)⟩


end Rules
end InitECandidate.Solver.Wave8GuestInv.RunFramesRace
