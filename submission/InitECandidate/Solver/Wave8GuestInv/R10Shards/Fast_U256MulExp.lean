import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Callees

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.FastU256MulExp

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees

private theorem while_counter_guestInv_step (op : Cmp) (hop : op = .less ∨ op = .lower) (i X : MlS)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep i 1 body)
    (hnc : noTopContinue body = true)
    (hX : avoidsLocal X body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp op (.var .local i) (.var .local X)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp op (.var .local i) (.var .local X)) body B (2 ^ 64)
    (counterGap op i X)
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
    have hcmp : wordCmpHOL op a b = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt := cmpRank_lt op hop a b hcmp
    have hnc' := evaluate_noTopContinue body hnc (decClockHOLFinite s)
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc'
    have hi' := hstep (decClockHOLFinite s) a hia (Or.inl hnone)
    have hX' := evaluate_avoidsLocal_flowing X body hX (decClockHOLFinite s) (Or.inl hnone)
    have hX'' : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup X =
        some (.val (.word b)) := hX'.trans hXb
    have hsucc := cmpRank_succ op a b hlt
    simp only [counterGap, hi', hX'', hia, hXb]
    omega

theorem fb_u256_limb : TerminatingFunBoundedOn GuestInv (ofString "u256_limb") K.«u256_limb» := by
  fb_prove 43 Guest.Software.guestFn_u256_limb K.«u256_limb»

theorem fb_u256_bit : TerminatingFunBoundedOn GuestInv (ofString "u256_bit") K.«u256_bit» := by
  have _ := fb_u256_limb
  fb_prove 44 Guest.Software.guestFn_u256_bit K.«u256_bit»

theorem fb_u256_byte : TerminatingFunBoundedOn GuestInv (ofString "u256_byte") K.«u256_byte» := by
  have _ := fb_u256_limb
  fb_prove 85 Guest.Software.guestFn_u256_byte K.«u256_byte»

theorem fb_u256_byte_length : TerminatingFunBoundedOn GuestInv (ofString "u256_byte_length") K.«u256_byte_length» := by
  have _ := fb_u256_bit_length
  fb_prove 79 Guest.Software.guestFn_u256_byte_length K.«u256_byte_length»

theorem fb_u256_add : TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add» := by
  fb_prove 56 Guest.Software.guestFn_u256_add K.«u256_add»

theorem fb_u256_sub : TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub» := by
  fb_prove 57 Guest.Software.guestFn_u256_sub K.«u256_sub»

theorem fb_u256_mul : TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul» := by
  have _ := fb_mul64x64
  fb_prove 60 Guest.Software.guestFn_u256_mul K.«u256_mul»

theorem fb_u256_mul_full : TerminatingFunBoundedOn GuestInv (ofString "u256_mul_full") K.«u256_mul_full» := by
  have _ := fb_mul64x64
  fb_prove 61 Guest.Software.guestFn_u256_mul_full K.«u256_mul_full»

theorem fb_u256_to_be_min : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min» := by
  have _ := fb_u256_byte_length
  have _ := fb_u256_limb
  fb_prove 88 Guest.Software.guestFn_u256_to_be_min K.«u256_to_be_min»

theorem fb_u256_exp : TerminatingFunBoundedOn GuestInv (ofString "u256_exp") K.«u256_exp» := by
  have _ := fb_u256_bit_length
  have _ := fb_u256_bit
  have _ := fb_u256_mul
  refine ⟨_, _, _, lookup_of_guestAst_getElem 80 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_u256_exp) rfl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_u256_exp,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expFieldListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expFieldToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    List.map, Option.map]
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply dec_guestInv
    apply decCall_guestInv'
    · exact_fb_hyp
    · apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · apply while_counter_guestInv_step .lower (Or.inr rfl)
        · fb_auto
        · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          exact CounterStep.suffix _ _ _ (CounterStep.assign _ _) rfl
        · rfl
        · rfl
      · exact straightOn _ rfl
  · fb_arith K.«u256_exp»

end InitECandidate.Solver.Wave8GuestInv.FastU256MulExp
