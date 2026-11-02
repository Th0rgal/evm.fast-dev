import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxCuts

/-! Kernel-checked diagnosis of the phase-one interface at ead8ebe88649ba81.

`ProgHOL.decCall` is a constructor, not an abbreviation for `dec` and `seq`.
The original spine operations stopped at the first such constructor, which is
the declaration of `enc`. Consequently the phase-one cut retains the complete
transaction body and discards its purported continuation.

This module imports only the definition/cut interface, never the admitted leaf.
-/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.LegacySpine
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded

/-! Historical definitions from ead8ebe88649ba81. The current `R10` operations
traverse `decCall`; the mismatch results below apply only to this snapshot. -/
def spineAt : Nat → ProgHOL 64 → ProgHOL 64
  | 0, p => p
  | n+1, .seq _ b => spineAt n b
  | n+1, .dec _ _ _ b => spineAt n b
  | _, p => p

def spinePlug : Nat → ProgHOL 64 → ProgHOL 64 → ProgHOL 64
  | 0, _, tail => tail
  | n+1, .seq a b, tail => .seq a (spinePlug n b tail)
  | n+1, .dec x sh e b, tail => .dec x sh e (spinePlug n b tail)
  | _, p, _ => p

def ptxPhase1 (tail : ProgHOL 64) : ProgHOL 64 := spinePlug 43 ptxCode tail

theorem ptx_first_decCall :
    ∃ body : ProgHOL 64,
      spineAt 2 ptxCode = .decCall (ofString "enc") (.comb [.one, .one])
        (ofString "encode_transaction") [.var .local (ofString "tx")] body := by
  unfold ptxCode
  exact ⟨_, rfl⟩

theorem spineAt_decCall (n : Nat) (x : MlS) (sh : ShapeHOL) (fn : MlS)
    (args : List (ExpHOL 64)) (body : ProgHOL 64) :
    spineAt n (.decCall x sh fn args body) = .decCall x sh fn args body := by
  cases n <;> rfl

theorem spinePlug_decCall (n : Nat) (x : MlS) (sh : ShapeHOL) (fn : MlS)
    (args : List (ExpHOL 64)) (body tail : ProgHOL 64) :
    spinePlug (n + 1) (.decCall x sh fn args body) tail = .decCall x sh fn args body := rfl

/-- The advertised first checkpoint is actually the first callee declaration. -/
theorem ptx_checkpoint43_eq_checkpoint2 : spineAt 43 ptxCode = spineAt 2 ptxCode := by
  unfold ptxCode
  rfl

/-- In the published interface, phase one is the whole transaction. -/
theorem ptxPhase1_eq_whole_body (tail : ProgHOL 64) : ptxPhase1 tail = ptxCode := by
  unfold ptxPhase1 ptxCode
  rfl

/-- In particular, no supplied continuation is installed by this cut. -/
theorem ptxPhase1_ignores_tail (tail₁ tail₂ : ProgHOL 64) :
    ptxPhase1 tail₁ = ptxPhase1 tail₂ := by
  rw [ptxPhase1_eq_whole_body, ptxPhase1_eq_whole_body]

/-- All the subsequent advertised checkpoints stop at the same declaration. -/
theorem ptx_later_checkpoints_stuck :
    spineAt 118 ptxCode = spineAt 2 ptxCode ∧
    spineAt 120 ptxCode = spineAt 2 ptxCode ∧
    spineAt 170 ptxCode = spineAt 2 ptxCode := by
  unfold ptxCode
  exact ⟨rfl, rfl, rfl⟩

/-- With a zero-cost continuation, the requested conclusion is exactly a bound
on the entire transaction at the phase-one-only budget. -/
theorem ptxPhase1_skip_target_iff :
    TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 .skip) (ptxCost1 + 0) ↔
      TerminatingProgBoundedOn TxReadyStrong ptxCode ptxCost1 := by
  rw [ptxPhase1_eq_whole_body, Nat.add_zero]

theorem ptxValidated_skip_zero : TerminatingProgBoundedOn PtxValidated .skip 0 := by
  intro F s _ _ _
  simp only [evaluateHOLFiniteState_skip, Nat.add_zero]
  exact ⟨le_rfl, le_rfl⟩

/-- The complete requested interface is equivalent to a whole-body bound;
its checkpoint assumption contributes nothing to that obligation. -/
theorem ptxPhase1_interface_iff_whole_body :
    (∀ (_ : PtxCallees) {tail : ProgHOL 64} {b : Nat},
      TerminatingProgBoundedOn PtxValidated tail b →
        TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 tail) (ptxCost1 + b)) ↔
      (PtxCallees → TerminatingProgBoundedOn TxReadyStrong ptxCode ptxCost1) := by
  constructor
  · intro hcut h
    exact ptxPhase1_skip_target_iff.mp (hcut h ptxValidated_skip_zero)
  · intro hbody h tail b _
    rw [ptxPhase1_eq_whole_body]
    intro F s hcode hready
    exact (hbody h s hcode hready).weaken (Nat.le_add_right _ _)


end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.LegacySpine
