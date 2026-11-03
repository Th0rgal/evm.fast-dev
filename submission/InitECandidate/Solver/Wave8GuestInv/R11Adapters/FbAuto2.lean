import InitECandidate.Solver.Wave8GuestInv.R10Shards.P12_P15Common

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R11Adapters

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P12_P15.Common

def rFieldCounterGap (op : Cmp) (i X : MlS) (idx : Nat) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup i, s.locals.lookup X with
  | some (.val (.word a)), some (.rStruct fields) =>
      match fields[idx]? with
      | some (.val (.word b)) => cmpRank op b - cmpRank op a
      | _ => 0
  | _, _ => 0

theorem while_counter_rfield_guestInv (op : Cmp) (hop : op = .less ∨ op = .lower)
    (i X : MlS) (idx : Nat)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B) (hinc : IncrBody i body)
    (hX : avoidsLocal X body = true) :
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp op (.var .local i) (.rfield idx (.var .local X))) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp op (.var .local i) (.rfield idx (.var .local X))) body B (2 ^ 64)
    (rFieldCounterGap op i X idx)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [rFieldCounterGap]
    split
    · split
      · rename_i b _
        have := cmpRank_le op b
        omega
      · omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, b, ha, hb, hword⟩ := evalAt_cmp s op _ _ word hw
    simp only [evalAt, evalHOLExact] at ha hb
    have hia : s.locals.lookup i = some (.val (.word a)) := by simpa using ha
    have hcmp : wordCmpHOL op a b = true := by
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
    have hX' := evaluate_avoidsLocal_flowing X body hX (decClockHOLFinite s) (Or.inl hnone)
    have hXdc : (decClockHOLFinite s).locals.lookup X = s.locals.lookup X := rfl
    cases hXval : s.locals.lookup X with
    | none => simp [hXval] at hb
    | some cell =>
      cases cell with
      | val _ => simp [hXval] at hb
      | nStruct _ _ => simp [hXval] at hb
      | rStruct fields =>
        simp only [hXval] at hb
        cases hfidx : fields[idx]? with
        | none => simp [hfidx] at hb
        | some fv =>
          cases fv with
          | rStruct _ => simp [hfidx] at hb
          | nStruct _ _ => simp [hfidx] at hb
          | val wl =>
            cases wl with
            | word b' =>
              have hb_eq : b' = b := by simpa [hfidx] using hb
              subst hb_eq
              have hX'' : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup X =
                  some (.rStruct fields) := hX'.trans (hXdc.trans hXval)
              have hsucc := cmpRank_succ op a b' hlt
              simp only [rFieldCounterGap, hi', hX'', hia, hXval, hfidx]
              omega

syntax "fb_auto2" : tactic
macro_rules
  | `(tactic| fb_auto2) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · fb_auto2
         · fb_auto2)
      | (apply TerminatingProgBoundedOn.ite_on
         · fb_auto2
         · fb_auto2)
      | (apply dec_guestInv; fb_auto2)
      | (apply call_guestInv'; exact_fb_hyp)
      | (apply decCall_guestInv'
         · exact_fb_hyp
         · fb_auto2)
      | (apply callHandle_guestInv'
         · exact_fb_hyp
         · fb_auto2)
      | (apply TerminatingProgBoundedOn.tailCall_guestInv; exact_fb_hyp)
      | (apply while_counter_guestInv .less (Or.inl rfl)
         · fb_auto2
         · incr_body
         · rfl)
      | (apply while_counter_guestInv .lower (Or.inr rfl)
         · fb_auto2
         · incr_body
         · rfl)
      | (apply while_counter_rfield_guestInv .less (Or.inl rfl)
         · fb_auto2
         · incr_body
         · rfl)
      | (apply while_counter_rfield_guestInv .lower (Or.inr rfl)
         · fb_auto2
         · incr_body
         · rfl)
      | (apply while_up_unsigned_const_guestInv
         · fb_auto2
         · counter_step)
      | (apply while_up_signed_const_guestInv _ 1 _
         · fb_auto2
         · counter_step
         · decide
         · decide)
      | (apply while_down_unsigned_guestInv
         · fb_auto2
         · counter_step))

syntax "fb_prove2 " num ident ident : tactic
macro_rules
  | `(tactic| fb_prove2 $idx $fn $k) => `(tactic|
      (fb_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fb_auto2
       · (have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
          unfold $k:ident
          generalize_K
          generalize domainBytes = D at hD ⊢
          try simp only [nat_max_eq]
          try simp only [BitVec.toNat_ofNat]
          omega)))

end InitECandidate.Solver.Wave8GuestInv.R11Adapters
