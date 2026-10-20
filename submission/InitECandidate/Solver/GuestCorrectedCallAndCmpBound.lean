import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Assembly
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCall
import InitECandidate.Solver.SelfContainedMasterK

set_option autoImplicit false

/-!
Corrected arithmetic layer for the Guest candidate budget.
The audited manifest in GuestAstStaticBounds is restated here to avoid its
BoundedPanToWord dependency: 255 simple and two compound nonconstant guards,
39 call vertices / 38 edges. Extraction from Guest.guestAst remains external.
The affine composition follows LoopWordStackExactClockIso.front_factor_after_iso;
WordToStack's entry offset is additive, and is not numerically bounded here.
This module proves budget arithmetic, not uniform target non-timeOut.
-/
namespace InitECandidate.Solver.GuestCorrectedCallAndCmpBound

abbrev Master := InitECandidate.Solver.SelfContainedMasterK.refinedSourceClock

def maxWhileGuardCmpCount : Nat := 4
def maxWhileLoopMultiplier : Nat := maxWhileGuardCmpCount + 2
def callGraphDepthFuncs : Nat := 39
def callGraphMaxEdges : Nat := callGraphDepthFuncs - 1
def simpleGuardCount : Nat := 255
def compoundGuardCount : Nat := 2

def frontFactor (cmp : Nat) : Nat := 1 * (cmp + 2) * 1 * 1 * 2
def correctedFrontFactor : Nat := frontFactor maxWhileGuardCmpCount
def simpleFrontFactor : Nat := frontFactor 1

def correctedCandidateK : Nat := InitE.bootstrapSteps +
  InitECandidate.Solver.SelfContainedMasterK.bMax * correctedFrontFactor *
    (Master + InitECandidate.Solver.SelfContainedMasterK.pipeOffset)

def yukonFiniteCeiling : Nat := 900719925474

def affine (c d k : Nat) : Nat := c * k + d

/-- The exact corrected constants, with the compound guard's two coercion comparisons. -/
theorem corrected_constants :
    maxWhileGuardCmpCount = 4 ∧ maxWhileLoopMultiplier = 6 ∧
      callGraphDepthFuncs = 39 ∧ callGraphMaxEdges = 38 := by decide

theorem correctedFrontFactor_eq :
    correctedFrontFactor = 1 * 6 * 1 * 1 * 2 ∧ correctedFrontFactor = 12 := by decide

theorem simpleFrontFactor_eq : simpleFrontFactor = 6 ∧ frontFactor 1 = 1 * 3 * 1 * 1 * 2 := by
  decide

theorem nonconstant_guard_population :
    simpleGuardCount + compoundGuardCount = 257 ∧ simpleGuardCount = 255 := by decide

/-- A count-weighted manifest statistic, not a dynamic execution average. -/
theorem stratified_manifest_factor_sum :
    simpleGuardCount * simpleFrontFactor + compoundGuardCount * correctedFrontFactor = 1554 := by
  decide

/-- Stratification can be applied to separately bounded dynamic clock contributions. -/
theorem stratified_clock_le_global (simpleTicks compoundTicks : Nat) :
    simpleFrontFactor * simpleTicks + correctedFrontFactor * compoundTicks ≤
      correctedFrontFactor * (simpleTicks + compoundTicks) := by
  unfold simpleFrontFactor correctedFrontFactor frontFactor maxWhileGuardCmpCount
  omega

/-- Corrected multiplicative factor, with every additive pass cost visible.
No bound of 5000 on these costs is inferred from the clock isometries. -/
theorem corrected_affine_composition (d_pc d_cl d_ws d_sl k : Nat) :
    affine 2 d_sl (affine 1 d_ws (affine 1 0 (affine 6 d_cl (affine 1 d_pc k)))) =
      correctedFrontFactor * k + (2 * (6 * d_pc + d_cl + d_ws) + d_sl) := by
  unfold affine correctedFrontFactor frontFactor maxWhileGuardCmpCount
  omega

/-- Direct connection to the semantic LoopToWord relation; the pass costs no clock ticks. -/
theorem loopToWord_clock_eq {width : Nat} [NeZero width] {C F : Type}
    {s : Flapjack.LoopSemStateFiniteExact width F}
    {t : Flapjack.WordSemStateFiniteExact width C F}
    (h : Flapjack.loopToWordStateRelHOLExact s t) :
    t.clock = s.clock := by
  obtain ⟨_, _, _, _, hc, _⟩ := h
  exact hc

/-- On the agreeing-results branch of WordToStack, an entry offset changes only the
additive consumed clock. The finishing-clock equality is an explicit premise. -/
theorem wordToStack_consumed_clock (start finish stackFinish ck : Nat)
    (hfinish : stackFinish = finish) (hle : finish ≤ start) :
    (start + ck) - stackFinish = (start - finish) + ck := by omega

/-- A descending rank certificate is needed to turn the extracted depth into a chain bound. -/
def RankedChain : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: tail => b < a ∧ RankedChain (b :: tail)

theorem ranked_chain_length (a : Nat) (tail : List Nat)
    (h : RankedChain (a :: tail)) : (a :: tail).length ≤ a + 1 := by
  induction tail generalizing a with
  | nil => simp
  | cons b tail ih =>
    obtain ⟨hlt, hrest⟩ := h
    have hb := ih b hrest
    simp only [List.length_cons] at hb ⊢
    omega

theorem corrected_call_depth (a : Nat) (tail : List Nat)
    (h : RankedChain (a :: tail)) (hroot : a < callGraphDepthFuncs) :
    (a :: tail).length ≤ 39 ∧ (a :: tail).length - 1 ≤ 38 := by
  have hb := ranked_chain_length a tail h
  unfold callGraphDepthFuncs at hroot
  omega

theorem correctedCandidateK_eq : correctedCandidateK = 44118665756 := by
  unfold correctedCandidateK Master
  rw [InitE.bootstrapSteps_eq, InitECandidate.Solver.SelfContainedMasterK.refinedSourceClock_eq.1]
  decide

theorem correctedCandidateK_formula :
    correctedCandidateK = 23132 + 8 * 12 * (459564194 + 5000) := by
  rw [correctedCandidateK_eq]

theorem correctedCandidateK_lt_ceiling : correctedCandidateK < yukonFiniteCeiling := by
  rw [correctedCandidateK_eq]; decide

/-- Stronger than merely fitting below the ceiling: a full factor twenty of headroom. -/
theorem correctedCandidateK_twentyfold_headroom :
    20 * correctedCandidateK < yukonFiniteCeiling := by
  rw [correctedCandidateK_eq]; decide

theorem corrected_yukon_score (minutes : Nat) :
    InitECandidate.Solver.yukonScore correctedCandidateK minutes < 2 ^ 53 - 1 :=
  InitECandidate.Solver.yukonScore_lt_two_pow_53_sub_one
    (by rw [correctedCandidateK_eq]; decide)

#print axioms corrected_constants
#print axioms correctedFrontFactor_eq
#print axioms simpleFrontFactor_eq
#print axioms nonconstant_guard_population
#print axioms stratified_manifest_factor_sum
#print axioms stratified_clock_le_global
#print axioms corrected_affine_composition
#print axioms loopToWord_clock_eq
#print axioms wordToStack_consumed_clock
#print axioms ranked_chain_length
#print axioms corrected_call_depth
#print axioms correctedCandidateK_eq
#print axioms correctedCandidateK_formula
#print axioms correctedCandidateK_lt_ceiling
#print axioms correctedCandidateK_twentyfold_headroom
#print axioms corrected_yukon_score

end InitECandidate.Solver.GuestCorrectedCallAndCmpBound
