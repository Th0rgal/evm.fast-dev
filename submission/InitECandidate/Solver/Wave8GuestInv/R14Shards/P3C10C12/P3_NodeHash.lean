import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def GBody.«node_hash» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») →
  (TerminatingFunBoundedOn NodeRlpReady (ofString "node_rlp") K.«node_rlp») →
  TerminatingFunBoundedOn NodeRlpReady (ofString "node_hash") K.«node_hash»

namespace P3NodeHash

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

private theorem lookup_rlp : originalRuntimeCode.lookup (ofString "node_rlp") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_rlp).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 285 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_rlp) rfl

private theorem lookup_hash : originalRuntimeCode.lookup (ofString "node_hash") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_hash).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 290 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_hash) rfl

end P3NodeHash

theorem «gbody_node_hash» : GBody.«node_hash» := by
  intro ha hk hn
  refine ⟨_, _, _, P3NodeHash.lookup_hash, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_hash,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals P3NodeHash.localsOnly _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (P3NodeHash.weakenGuard (P3NodeHash.straight _ rfl) (fun s h => h.1.1))
        (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.decCall_on hn _ _ _ (P3NodeHash.entry P3NodeHash.lookup_rlp (by rfl))
          (decCallResumeOn_guestInv (fun s h => h.1.1) _ _ _)
          (TerminatingProgBoundedOn.decCall_guestInv ha _ _ _
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.call_guestInv hk _ _)
              (TerminatingProgBoundedOn.seq_guestInv (P3NodeHash.straight _ rfl)
                (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))) ?_
  unfold K.«node_hash»
  omega

end InitECandidate.Solver.Wave8GuestInv
