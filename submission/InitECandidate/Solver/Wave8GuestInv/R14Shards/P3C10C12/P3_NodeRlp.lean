import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.P3C10C12

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

def GBody.«node_rlp» : Prop :=
  (TerminatingFunBoundedOn NodeRlpReady (ofString "_node_rlp_fill") K.«_node_rlp_fill») →
  (TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail») →
  (ReadOnlyFn (ofString "mpt_fail")) →
  TerminatingFunBoundedOn NodeRlpReady (ofString "node_rlp") K.«node_rlp»

namespace P3NodeRlp

private theorem localsOnly : LocalsOnly ["node"] NodeRlpReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "node" (hl "node" (by simp))
  simp only [NodeRlpReady, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

private theorem entry {fname : MlS} {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e)
    (hp : e.1 = [(ofString "node", .one)]) :
    CallEntryOn NodeRlpReady NodeRlpReady fname [.var .local (ofString "node")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "node") .one b r
    (by rw [hcode]; exact hl) values body' callee ret' hargs hlook
  exact localsOnly state callee (state.clock - 1) (by simpa using hc) hP

private theorem straight (p : ProgHOL 64) (h : extStraightLine p = true) :
    TerminatingProgBoundedOn GuestInv p 0 :=
  fun s hc _ => TerminatingProgBounded.straight p h s hc

private theorem weakenGuard {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {k : Nat} (h : TerminatingProgBoundedOn Q p k)
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s) :
    TerminatingProgBoundedOn P p k := fun s hc hP => h s hc (hp s hP)

private theorem call_ro {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} (hP : LocalsOnly names P)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    {f : MlS} (h : ReadOnlyFn f) (args : List (ExpHOL 64)) :
    Hoare P (.call (some (none, none)) f args) (fun r t => r = none → P t) := by
  apply Hoare.call0 h (callEntryOn_of_imp localsFree_guestInv hPG _ _)
  · intro F s callee post v hc hPs hq _
    rw [hq (Or.inl ⟨v, rfl⟩)]
    exact hP s s.locals post.clock (fun _ _ => rfl) hPs
  · intro F r t hr _ he
    exact False.elim (hr he)

private theorem lookup_fill : originalRuntimeCode.lookup (ofString "_node_rlp_fill") =
    some ((sourceFunctionEntry Guest.Software.guestFn__node_rlp_fill).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 284 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_fill) rfl

private theorem lookup_rlp : originalRuntimeCode.lookup (ofString "node_rlp") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_rlp).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 285 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_rlp) rfl

end P3NodeRlp

theorem «gbody_node_rlp» : GBody.«node_rlp» := by
  intro hf hm hr
  refine ⟨_, _, _, P3NodeRlp.lookup_rlp, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_rlp,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals P3NodeRlp.localsOnly _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (P3NodeRlp.weakenGuard (P3NodeRlp.straight _ rfl) (fun s h => h.1.1))
        (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.seq_hoare
          (TerminatingProgBoundedOn.ite_on
            (TerminatingProgBoundedOn.call_on hm _ _
              (callEntryOn_of_imp localsFree_guestInv (fun s h => h.1.1) _ _))
            (P3NodeRlp.weakenGuard (P3NodeRlp.straight _ rfl) (fun s h => h.1.1)))
          (Hoare.ite
            (Hoare.mono (P3NodeRlp.call_ro P3NodeRlp.localsOnly (fun s h => h.1.1) hr _) (fun s h => h.1))
            (Hoare.skip (fun s h _ => h.1)) (fun _ _ h => absurd h (by simp)))
          (TerminatingProgBoundedOn.seq_guestInv_after
            (TerminatingProgBoundedOn.call_on hf _ _ (P3NodeRlp.entry P3NodeRlp.lookup_fill (by rfl)))
            (fun s h => h.1.1)
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«node_rlp»
  simp only [Nat.max_def]
  split <;> omega

end InitECandidate.Solver.Wave8GuestInv.P3C10C12
