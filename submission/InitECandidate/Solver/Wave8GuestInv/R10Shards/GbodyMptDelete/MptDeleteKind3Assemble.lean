import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Descend

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
def mptElse : ProgHOL 64 → ProgHOL 64
  | .ite _ _ no => no
  | _ => .skip

def mptDeleteAfterKind : ProgHOL 64 :=
  mptDecBody (mptElse (mptRight mptDeleteBody))

def mptBranchCode : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "level")) (.var .local (ofString "klen")))
    mptDeleteValueCode mptBranchDescend

def MptDeleteDone (sp : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => MptDeleteHead t ∧ (locN t "go" = 0 ∨ globN t "scratch_ptr" + 40 ≤ sp)

theorem mptBranch_hoare (h : MptDeleteCallees) (sp : Nat) :
    Hoare (fun s => MptDeleteBranchReady s ∧ globN s "scratch_ptr" ≤ sp)
      mptBranchCode (fun r t => r = none → MptDeleteDone sp t) := by
  apply Hoare.ite
  · refine ⟨fun s hc hp _ hr => ?_⟩
    have hv := (mptDeleteBranch_value h).run s hc hp.1.1 (by rw [hr]; simp)
    rw [hr] at hv
    exact ⟨(hv rfl).1, Or.inl (hv rfl).2⟩
  · refine ⟨fun s hc hp _ hr => ?_⟩
    have hne := mptCondFalse_eqLoc hp.2
    have hle : locN s "level" ≤ locN s "klen" := by
      obtain ⟨_, _, _, Nd, fs, _, _, _, hle, _⟩ := hp.1.1
      exact hle
    have hd := mptBranchDescend_run h hc hp.1.1 (by omega) (by
      exact (Prod.ext hr rfl : evaluateHOLFiniteState s mptBranchDescend =
        (none, (evaluateHOLFiniteState s mptBranchDescend).2)))
    exact ⟨hd.1, Or.inr (Nat.le_trans hd.2 hp.1.2)⟩
  · intro F s _ hr
    cases hr

theorem mptDeleteAfterKind_hoare (h : MptDeleteCallees) (sp : Nat) :
    Hoare (fun s => MptDeleteBranchReady s ∧ globN s "scratch_ptr" ≤ sp)
      mptDeleteAfterKind (fun r t => r = none → MptDeleteDone sp t) := by
  apply mptHoare_seq (R := fun s => MptDeleteBranchReady s ∧ globN s "scratch_ptr" ≤ sp)
  · apply Hoare.ite
    · apply Hoare.of_false
      intro F s hp
      have hh := mptCondTrue_eq hp.2
      have hk := hp.1.1.2.2.1
      change locN s "k" = 0 at hh
      omega
    · apply Hoare.skip
      intro F s hp _
      exact hp.1
    · intro F s _ hr
      cases hr
  · apply mptHoare_seq (mptDeleteBranch_invalidate h sp)
    apply Hoare.ite
    · apply Hoare.of_false
      intro F s hp
      have hh := mptCondTrue_eq hp.2
      have hk := hp.1.1.2.2.1
      change locN s "k" = 1 at hh
      omega
    · apply Hoare.ite
      · apply Hoare.of_false
        intro F s hp
        have hh := mptCondTrue_eq hp.2
        have hk := hp.1.1.1.2.2.1
        change locN s "k" = 2 at hh
        omega
      · exact Hoare.mono (mptBranch_hoare h sp) (fun _ hp => hp.1.1)
      · intro F s _ hr
        cases hr
    · intro F s _ hr
      cases hr

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
