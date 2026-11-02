import InitECandidate.Solver.GuestBoundBlockTxBal
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Callees
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13DivMod
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_BitOps
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_SmodSar
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_Sha256
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_U256Core
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_StateHostLeaves
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_U256MulExp

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.FastGen

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestBoundBlockTxBal
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees
open InitECandidate.Solver.Wave8GuestInv.P13.DivMod
open InitECandidate.Solver.Wave8GuestInv.FastBitOps
open InitECandidate.Solver.Wave8GuestInv.FastSmodSar
open InitECandidate.Solver.Wave8GuestInv.FastSha256
open InitECandidate.Solver.Wave8GuestInv.FastU256Core
open InitECandidate.Solver.Wave8GuestInv.FastStateHostLeaves
open InitECandidate.Solver.Wave8GuestInv.FastU256MulExp

def expCounterGap (op : Cmp) (i : MlS) (limitExp : ExpHOL 64) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup i,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) limitExp with
  | some (.val (.word a)), some (.val (.word b)) => cmpRank op b - cmpRank op a
  | _, _ => 0

theorem while_up_exp_guestInv (op : Cmp) (hop : op = .less ∨ op = .lower)
    (i : MlS) (limitExp : ExpHOL 64) {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep i 1 body)
    (hlim : expLocalsAvoided limitExp body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp op (.var .local i) limitExp) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp op (.var .local i) limitExp) body B (2 ^ 64)
    (expCounterGap op i limitExp)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [expCounterGap]
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
    have hia : s.locals.lookup i = some (.val (.word a)) := by
      simpa [evalAt, evalHOLExact] using ha
    have hlim_s : @evalHOLExact 64 F _ s.toExact
        (fun addr => Classical.propDecidable (s.memaddrs addr)) limitExp =
        some (.val (.word b)) := by
      simpa [evalAt] using hb
    have hcmp : wordCmpHOL op a b = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt := cmpRank_lt op hop a b hcmp
    have hi' := hstep (decClockHOLFinite s) a hia hflow
    have hflow' : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue :=
      hflow.elim Or.inl (fun h => Or.inr (Or.inr h))
    have hkeep : ∀ k, avoidsLocal k body = true →
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup k =
        s.locals.lookup k :=
      fun k hk => evaluate_avoidsLocal_flowing k body hk (decClockHOLFinite s) hflow'
    have hlim_eq : @evalHOLExact 64 F _
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.toExact
        (fun addr => Classical.propDecidable
          ((evaluateHOLFiniteState (decClockHOLFinite s) body).2.memaddrs addr)) limitExp =
        @evalHOLExact 64 F _ s.toExact
          (fun addr => Classical.propDecidable (s.memaddrs addr)) limitExp := by
      rw [← evalHOLFinite_eq_toExact, ← evalHOLFinite_eq_toExact]
      exact evalHOLFinite_eq_of_expLocalsAvoided _ s body hkeep limitExp hlim
    have hlim' : @evalHOLExact 64 F _
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.toExact
        (fun addr => Classical.propDecidable
          ((evaluateHOLFiniteState (decClockHOLFinite s) body).2.memaddrs addr)) limitExp =
        some (.val (.word b)) := hlim_eq.trans hlim_s
    have hsucc := cmpRank_succ op a b hlt
    simp only [expCounterGap, hi', hlim', hia, hlim_s]
    omega

def signedDownRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => w.toInt.toNat
  | _ => 0

theorem while_down_signed_guestInv (counter : MlS) {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hsub : CounterStep counter (-1) body) :
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .less (.const 0) (.var .local counter)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp .less (.const 0) (.var .local counter)) body B (2 ^ 64)
    (signedDownRank counter)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    unfold signedDownRank
    split
    · rename_i w _
      have := BitVec.toInt_le (x := w)
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨z, w, hz, hlw, hword⟩ := evalAt_cmp s .less _ _ word hw
    have hz0 : z = 0#64 := by simpa [evalAt, evalHOLExact] using hz.symm
    subst z
    have hlookup : s.locals.lookup counter = some (.val (.word w)) := by
      simpa [evalAt, evalHOLExact] using hlw
    have hcmp : wordCmpHOL .less 0#64 w = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt : (0 : Int) < w.toInt := by
      have hlt0 := cmpRank_lt .less (Or.inl rfl) 0#64 w hcmp
      have hwlt := w.isLt
      simp only [cmpRank, BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide] at hlt0 ⊢
      split_ifs <;> omega
    have hwmax := BitVec.toInt_le (x := w)
    have hnext : (w + (-1 : BitVec 64)).toInt = w.toInt - 1 := by
      have hm1 : (-1 : BitVec 64).toInt = -1 := by decide
      rw [BitVec.toInt_add, hm1]
      apply Int.bmod_eq_of_le <;> omega
    have heff := hsub (decClockHOLFinite s) w hlookup hflow
    simp only [signedDownRank, heff, hlookup, hnext]
    omega

theorem tailCall_guestInv' {fname : MlS} {B : Nat} {arguments : List (ExpHOL 64)}
    (hf : TerminatingFunBoundedOn GuestInv fname B) :
    TerminatingProgBoundedOn GuestInv (.call none fname arguments) (B + 1) :=
  TerminatingProgBoundedOn.tailCall_guestInv hf arguments

theorem while_counter_guestInv_step (op : Cmp) (hop : op = .less ∨ op = .lower) (i X : MlS)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep i 1 body)
    (hnc : noTopContinue body = true)
    (hX : avoidsLocal X body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp op (.var .local i) (.var .local X)) body)
      ((2 ^ 64 + 1) * (B + 1)) :=
  while_up_exp_guestInv op hop i (.var .local X) hbody hstep hX

syntax "fg_unfold " num ident : tactic
macro_rules
  | `(tactic| fg_unfold $idx $fn) => `(tactic|
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

syntax "fg_arith " ident : tactic
macro_rules
  | `(tactic| fg_arith $k) => `(tactic|
      (have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
       unfold $k:ident
       generalize_K
       generalize domainBytes = D at hD ⊢
       try simp only [nat_max_eq]
       first | omega | (simp only [Nat.max_def, max_def]; (try split_ifs) <;> omega)))

end InitECandidate.Solver.Wave8GuestInv.FastGen
