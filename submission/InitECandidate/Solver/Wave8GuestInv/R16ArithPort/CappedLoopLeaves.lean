import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_30

/-! R11-tightened capped-counter leaf proofs for:
`fb_fp_pow`, `fb_fp12_pow_absx`, `fb_pair_miller_loop`, `fb_fq12_reduce`, `fb_fq12_mul`,
`fb_fq12_sqr`, and `fb_ecp_mul`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16ArithPort.Capped

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees
open InitECandidate.Solver.Wave8GuestInv.P13.DivMod
open InitECandidate.Solver.Wave8GuestInv.FastU256MulExp
open InitECandidate.Solver.Wave8GuestInv.FastGen

/-- 1. `fb_fp_pow` (`i` initialized to `256 = 2^8`, decremented first) -/
theorem fb_fp_pow : TerminatingFunBoundedOn GuestInv (ofString "fp_pow") K.«fp_pow» := by
  have _ := fb_fp_sqr
  have _ := fb_u256_bit
  have _ := fb_fp_mul
  fg_unfold 155 Guest.Software.guestFn_fp_pow
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply dec_guestInv
    apply dec_const_cap_guestInv "i" (BitVec.ofNat 64 256)
    exact seq_to_guestInv (fun _ h => h.1)
      (while_down_first_capped_on .lower (Or.inr rfl) "i"
        (TerminatingProgBoundedOn.seq_guestInv
          (TerminatingProgBoundedOn.ite_on (call_guestInv' fb_fp_sqr) (straightOn _ rfl))
          (decCall_guestInv' fb_u256_bit
            (TerminatingProgBoundedOn.ite_on
              (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp_mul) (straightOn _ rfl))
              (straightOn _ rfl))))
        rfl)
      (straightOn _ rfl)
  · rw [show (BitVec.ofNat 64 256).toNat = 2 ^ 8 by decide]
    fg_arith K.«fp_pow»

/-- 2. `fb_fp12_pow_absx` (`i` initialized to `64`, decremented first) -/
theorem fb_fp12_pow_absx :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_pow_absx") K.«fp12_pow_absx» := by
  fg_unfold 755 Guest.Software.guestFn_fp12_pow_absx
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv' fb_heap_mark
    apply decCall_guestInv' fb_alloc
    apply decCall_guestInv' fb_alloc
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_copy)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_set_one)
    apply dec_guestInv
    apply dec_guestInv
    apply dec_const_cap_guestInv "i" (BitVec.ofNat 64 64)
    apply seq_to_guestInv (fun _ h => h.1)
    · exact while_down_first_capped_on .lower (Or.inr rfl) "i"
        (TerminatingProgBoundedOn.seq_guestInv
          (TerminatingProgBoundedOn.ite_on (call_guestInv' fb_fp12_mul) (straightOn _ rfl))
          (TerminatingProgBoundedOn.ite_on
            (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_mul) (straightOn _ rfl))
            (straightOn _ rfl)))
        rfl
    · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_copy)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_heap_release)
      exact straightOn _ rfl
  · rw [show (BitVec.ofNat 64 64).toNat = 64 by decide]
    fg_arith K.«fp12_pow_absx»

/-- 3. `fb_pair_miller_loop` (`i` initialized to `63`, decremented first) -/
theorem fb_pair_miller_loop :
    TerminatingFunBoundedOn GuestInv (ofString "pair_miller_loop") K.«pair_miller_loop» := by
  fg_unfold 785 Guest.Software.guestFn_pair_miller_loop
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv' fb_heap_mark
    apply decCall_guestInv' fb_alloc
    apply decCall_guestInv' fb_alloc
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp2_copy)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp2_copy)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp2_set_one)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_set_one)
    apply dec_guestInv
    apply dec_const_cap_guestInv "i" (BitVec.ofNat 64 63)
    apply seq_to_guestInv (fun _ h => h.1)
    · exact while_down_first_capped_on .lower (Or.inr rfl) "i"
        (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_mul)
          (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_pair_doubling_step)
            (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_pair_ell)
              (TerminatingProgBoundedOn.ite_on
                (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_pair_addition_step)
                  (call_guestInv' fb_pair_ell))
                (straightOn _ rfl)))))
        rfl
    · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_conj)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_heap_release)
      exact straightOn _ rfl
  · rw [show (BitVec.ofNat 64 63).toNat = 63 by decide]
    fg_arith K.«pair_miller_loop»

/-- 4. `fb_fq12_reduce` (`e` initialized to `11`, decremented first) -/
theorem fb_fq12_reduce :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_reduce") K.«fq12_reduce» := by
  have h_fq_mul_small := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fq_mul_small
  fg_unfold 658 Guest.Software.guestFn_fq12_reduce
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_const_cap_guestInv "e" (BitVec.ofNat 64 11)
    apply seq_to_guestInv (fun _ h => h.1)
    · exact while_down_first_capped_on .lower (Or.inr rfl) "e"
        (dec_guestInv _ _ _
          (decCall_guestInv' h_fq_mul_small
            (decCall_guestInv' h_fq_mul_small
              (dec_guestInv _ _ _
                (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq_sub)
                  (TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
                    (dec_guestInv _ _ _
                      (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq_add)
                        (straightOn _ rfl)))))))))
        rfl
    · exact straightOn _ rfl
  · rw [show (BitVec.ofNat 64 11).toNat = 11 by decide]
    fg_arith K.«fq12_reduce»

/-- Inner-loop helper for `fq12_mul`: `while (iend >=u i)` where `iend ≤ 11`. -/
private def fq12MulInnerMu {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "iend") with
  | some (.val (.word wi)), some (.val (.word we)) =>
    if we.toNat ≤ 11 then we.toNat + 1 - wi.toNat else 0
  | _, _ => 0

private theorem fq12MulInnerMu_le {F : Type} (s : PanSemStateFiniteExact 64 F) :
    fq12MulInnerMu s ≤ 12 := by
  unfold fq12MulInnerMu
  split
  · split_ifs <;> omega
  · omega

private def fq12MulGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ we : BitVec 64,
    s.locals.lookup (ofString "iend") = some (.val (.word we)) ∧ we.toNat ≤ 11

private theorem while_fq12_mul_inner {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep (ofString "i") 1#64 body)
    (havoid : avoidsLocal (ofString "iend") body = true) :
    TerminatingProgBoundedOn fq12MulGuard
      (.while (.cmp .notLower (.var .local (ofString "iend")) (.var .local (ofString "i"))) body)
      ((12 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank fq12MulGuard
    (.cmp .notLower (.var .local (ofString "iend")) (.var .local (ofString "i"))) body B 12
    fq12MulInnerMu
    (fun s hP => ⟨guestInv_decClock s hP.1, hP.2⟩)
    (fun s hc hP => hbody s hc hP.1)
    (fun s _ _ _ => fq12MulInnerMu_le s) ?_
  intro F s _ ⟨hg, we, hwe, hwe11⟩ hact hflow
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨ve, vi, hve, hvi, hword⟩ := evalAt_cmp s .notLower _ _ word hw
  have hve_eq : ve = we := by simpa [evalAt, evalHOLExact, hwe] using hve.symm
  subst hve_eq
  have hli : s.locals.lookup (ofString "i") = some (.val (.word vi)) := by
    simpa [evalAt, evalHOLExact] using hvi
  have hcmp : wordCmpHOL .notLower we vi = true := by
    by_cases hc : wordCmpHOL .notLower we vi = true
    · exact hc
    · simp [hc] at hword; exact absurd hword hnz
  have hle : vi.toNat ≤ we.toNat := by
    simp only [wordCmpHOL, BitVec.lt_def] at hcmp
    by_contra hgt
    have hlt' : we.toNat < vi.toNat := by omega
    simp [hlt'] at hcmp
  have hip := hstep (decClockHOLFinite s) vi hli hflow
  have hkeep := evaluate_avoidsLocal_flowing (ofString "iend") body havoid (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  have hwe_post : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "iend") =
      some (.val (.word we)) := hkeep.trans hwe
  have hadd1 : (vi + 1#64).toNat = vi.toNat + 1 := BitVec.toNat_add_of_lt (by simp; omega)
  refine ⟨⟨guestInv_evaluate _ _ (guestInv_decClock s hg), we, hwe_post, hwe11⟩, ?_⟩
  unfold fq12MulInnerMu
  rw [hip, hwe_post, hli, hwe, if_pos hwe11, hadd1]
  omega

/-- 5. `fb_fq12_mul` (`k < 23` outer, `iend <= 11` inner) -/
theorem fb_fq12_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_mul") K.«fq12_mul» := by
  have _ := fb_fq12_reduce
  fg_unfold 659 Guest.Software.guestFn_fq12_mul
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv' fb_heap_mark
    apply decCall_guestInv' fb_alloc
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply while_up_unsigned_const_guestInv (ofString "k") (BitVec.ofNat 64 23)
      · apply dec_guestInv
        apply dec_guestInv
        apply TerminatingProgBoundedOn.seq_guestInv
        · exact TerminatingProgBoundedOn.ite_on (straightOn _ rfl) (straightOn _ rfl)
        · apply dec_guestInv
          apply seq_step_on (P := GuestInv) (Q := fq12MulGuard)
            (straightOn _ rfl)
          · intro F s _ hg hnone
            rw [evaluateHOLFiniteState_ite] at hnone ⊢
            split at hnone
            · rename_i cw hcw
              simp only [evalHOLExact] at hcw
              rcases hlk : s.locals.lookup (ofString "iend") with _ | vend
              · simp [hlk] at hcw
              rcases vend with ⟨⟨we⟩⟩ | _ | _ <;> try (simp [hlk] at hcw; done)
              split
              · rename_i hcw0
                have hle11 : we.toNat ≤ 11 := by
                  simp only [hlk, wordCmpHOL, BitVec.lt_def, BitVec.toNat_ofNat] at hcw
                  by_cases h11 : 11 < we.toNat
                  · simp [h11] at hcw; subst cw; cases hcw0
                  · omega
                rw [evaluateHOLFiniteState_skip]
                exact ⟨hg, we, hlk, hle11⟩
              · have hass : evaluateHOLFiniteState s
                    (.assign .local (ofString "iend") (.const 11#64)) =
                    (none, setVarHOLFinite (ofString "iend") (.val (.word 11#64)) s) := by
                  simp [evaluateHOLFiniteState_assign, evalHOLExact, lookupKvarHOLExact, hlk,
                    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
                rw [hass]
                exact ⟨guestInv_setVar _ _ s hg, 11#64,
                  by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], by decide⟩
            · simp at hnone
          · apply seq_to_guestInv (fun _ h => h.1)
            · exact while_fq12_mul_inner
                (dec_guestInv _ _ _
                  (dec_guestInv _ _ _
                    (decCall_guestInv' fb_fq_mul
                      (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq_add)
                        (straightOn _ rfl)))))
                (by counter_step)
                rfl
            · exact TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl) (straightOn _ rfl)
      · counter_step
    · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq12_reduce)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memcpy)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_heap_release)
      exact straightOn _ rfl
  · rw [show (BitVec.ofNat 64 23).toNat = 23 by decide]
    fg_arith K.«fq12_mul»

/-- Inner-loop helpers for `fq12_sqr`: `while (i <u k - i)` when `k < 23` and `i ≤ k`. -/
private def fq12SqrInnerGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ wi wk : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word wi)) ∧
    s.locals.lookup (ofString "k") = some (.val (.word wk)) ∧
    wi.toNat ≤ wk.toNat ∧ wk.toNat < 23

private def fq12SqrInnerMu {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "k") with
  | some (.val (.word wi)), some (.val (.word wk)) =>
    if wk.toNat < 23 then wk.toNat - wi.toNat else 0
  | _, _ => 0

private theorem fq12SqrInnerMu_le {F : Type} (s : PanSemStateFiniteExact 64 F) :
    fq12SqrInnerMu s ≤ 22 := by
  unfold fq12SqrInnerMu
  split
  · split_ifs <;> omega
  · omega

private theorem while_fq12_sqr_inner {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep (ofString "i") 1#64 body)
    (havoid : avoidsLocal (ofString "k") body = true) :
    TerminatingProgBoundedOn fq12SqrInnerGuard
      (.while (.cmp .lower (.var .local (ofString "i"))
        (.op .sub [.var .local (ofString "k"), .var .local (ofString "i")])) body)
      ((22 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank fq12SqrInnerGuard
    (.cmp .lower (.var .local (ofString "i"))
      (.op .sub [.var .local (ofString "k"), .var .local (ofString "i")])) body B 22
    fq12SqrInnerMu
    (fun s hP => ⟨guestInv_decClock s hP.1, hP.2⟩)
    (fun s hc hP => hbody s hc hP.1)
    (fun s _ _ _ => fq12SqrInnerMu_le s) ?_
  intro F s _ ⟨hg, wi, wk, hwi, hwk, hilek, hwk23⟩ hact hflow
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨vi, vsub, hvi, hvsub, hword⟩ := evalAt_cmp s .lower _ _ word hw
  have hvi_eq : vi = wi := by simpa [evalAt, evalHOLExact, hwi] using hvi.symm
  subst hvi_eq
  have hsub_eq : vsub = wk - wi := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hwk, hwi, wordOpHOL, wordOp, valueIsWord, valueWord] using hvsub.symm
  subst hsub_eq
  have hcmp : wordCmpHOL .lower wi (wk - wi) = true := by
    by_cases hc : wordCmpHOL .lower wi (wk - wi) = true
    · exact hc
    · simp [hc] at hword; exact absurd hword hnz
  have hlt_sub : wi.toNat < (wk - wi).toNat := by
    simpa [wordCmpHOL, BitVec.lt_def] using hcmp
  have hsub_nat : (wk - wi).toNat = wk.toNat - wi.toNat := by
    rw [BitVec.toNat_sub]
    have := wk.isLt; have := wi.isLt
    omega
  have hip := hstep (decClockHOLFinite s) wi hwi hflow
  have hkeep := evaluate_avoidsLocal_flowing (ofString "k") body havoid (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  have hwk_post : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "k") =
      some (.val (.word wk)) := hkeep.trans hwk
  have hadd1 : (wi + 1#64).toNat = wi.toNat + 1 := BitVec.toNat_add_of_lt (by simp; omega)
  refine ⟨⟨guestInv_evaluate _ _ (guestInv_decClock s hg),
    wi + 1#64, wk, hip, hwk_post, by omega, hwk23⟩, ?_⟩
  unfold fq12SqrInnerMu
  rw [hip, hwk_post, hwi, hwk, if_pos hwk23, hadd1]
  omega

private def fq12SqrKGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ wk : BitVec 64,
    s.locals.lookup (ofString "k") = some (.val (.word wk)) ∧ wk.toNat < 23

private theorem while_up_const_active_k23 {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn fq12SqrKGuard body B)
    (hadd : CounterStep (ofString "k") 1#64 body) :
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .lower (.var .local (ofString "k")) (.const 23#64)) body)
      ((23 + 1) * (B + 1)) := by
  intro F state hcode hg
  have haux := while_rank_stationary_aux (P := GuestInv)
    (condition := .cmp .lower (.var .local (ofString "k")) (.const 23#64))
    (body := body) (B := B)
    (constUpRank (ofString "k") 23#64)
    (fun s hs_code hs_g hact => by
      obtain ⟨word, hw, hnz⟩ := hact
      change evalAt s _ = _ at hw
      obtain ⟨w, v, hl, hv, hword⟩ := evalAt_cmp s .lower _ _ word hw
      have hv_eq : v = 23#64 := by simpa [evalAt, evalHOLExact] using hv.symm
      subst hv_eq
      have hlw : s.locals.lookup (ofString "k") = some (.val (.word w)) := by
        simpa [evalAt, evalHOLExact] using hl
      have hcmp : wordCmpHOL .lower w 23#64 = true := by
        by_cases hc : wordCmpHOL .lower w 23#64 = true
        · exact hc
        · simp [hc] at hword; exact absurd hword hnz
      have hlt : w.toNat < 23 := by simpa [wordCmpHOL, BitVec.lt_def] using hcmp
      exact hbody (decClockHOLFinite s) hs_code ⟨guestInv_decClock s hs_g, w, hlw, hlt⟩)
    (fun s _ hs_g hact hflow => by
      obtain ⟨word, hw, hnz⟩ := hact
      change evalAt s _ = _ at hw
      obtain ⟨w, v, hl, hv, hword⟩ := evalAt_cmp s .lower _ _ word hw
      have hv_eq : v = 23#64 := by simpa [evalAt, evalHOLExact] using hv.symm
      subst hv_eq
      have hlw : s.locals.lookup (ofString "k") = some (.val (.word w)) := by
        simpa [evalAt, evalHOLExact] using hl
      have hcmp : wordCmpHOL .lower w 23#64 = true := by
        by_cases hc : wordCmpHOL .lower w 23#64 = true
        · exact hc
        · simp [hc] at hword; exact absurd hword hnz
      have hlt : w.toNat < 23 := by simpa [wordCmpHOL, BitVec.lt_def] using hcmp
      have heff := hadd (decClockHOLFinite s) w hlw hflow
      have hnext : (w + 1#64).toNat = w.toNat + 1 := BitVec.toNat_add_of_lt (by simp; omega)
      refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs_g), Or.inl ?_⟩
      simp only [constUpRank, heff, hlw, hnext, show (23#64 : BitVec 64).toNat = 23 by decide]
      omega)
    (23 + 1) state hcode hg
    (fun _ => by unfold constUpRank; split <;> (simp only [show (23#64 : BitVec 64).toNat = 23 by decide]; omega))
  exact haux

/-- 6. `fb_fq12_sqr` (`k < 23` outer, `i < k - i` inner) -/
theorem fb_fq12_sqr :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_sqr") K.«fq12_sqr» := by
  have _ := fb_fq12_reduce
  fg_unfold 660 Guest.Software.guestFn_fq12_sqr
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv' fb_heap_mark
    apply decCall_guestInv' fb_alloc
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply while_up_const_active_k23
      · have hglo : GuestLocalsOnly ["k"] fq12SqrKGuard := {
          toGuest := fun _ h => h.1
          congr := fun _ _ hg hkeep ⟨_, wk, hk, hk23⟩ =>
            ⟨hg, wk, (hkeep "k" (by simp)).trans hk, hk23⟩
        }
        apply dec_avoids_on hglo _ (by decide)
        intro F state hcode ⟨hg, wk, hwk, hwk23⟩ hnt
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
        dsimp only [evalHOLExact] at hnt ⊢
        rw [if_pos (show shapeEqHOL ShapeHOL.one (shapeOfHOLExact (.val (.word 0#64))) = true by simp [shapeOfHOLExact, shapeEqHOL])] at hnt ⊢
        dsimp only at hnt ⊢
        let s0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) state
        have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
          simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs0_k : s0.locals.lookup (ofString "k") = some (.val (.word wk)) := by
          simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "k" by decide, hwk]
        have hs0 : fq12SqrInnerGuard s0 := ⟨guestInv_setVar _ _ state hg, 0#64, wk, hs0_i, hs0_k, by simp, hwk23⟩
        have hprog : TerminatingProgBoundedOn fq12SqrInnerGuard _ _ := by
          apply seq_step_on (P := fq12SqrInnerGuard) (Q := fq12SqrInnerGuard)
            (fun s hc hP => TerminatingProgBoundedOn.ite_on (straightOn _ rfl) (straightOn _ rfl) s hc hP.1)
          · intro F' s _ ⟨hgs, wi, wk', hwi', hwk', hilek, hwk23'⟩ hnone
            rw [evaluateHOLFiniteState_ite] at hnone ⊢
            have hcond : @evalHOLExact 64 F' _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
                (.cmp .lower (.const 11#64) (.var .local (ofString "k"))) =
                some (.val (.word (if 11 < wk'.toNat then 1#64 else 0#64))) := by
              simp only [evalHOLExact, hwk', wordCmpHOL, BitVec.lt_def, BitVec.toNat_ofNat]
              split_ifs <;> rfl
            rw [hcond] at hnone ⊢
            by_cases h11 : 11 < wk'.toNat
            · simp only [if_pos h11, show ¬ ((1#64 : BitVec 64) = 0) by decide, ↓reduceIte] at hnone ⊢
              have hass : evaluateHOLFiniteState s
                  (.assign .local (ofString "i") (.op .sub [.var .local (ofString "k"), .const 11#64])) =
                  (none, setVarHOLFinite (ofString "i") (.val (.word (wk' - 11#64))) s) := by
                simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hwk', hwi',
                  wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
                  isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
              rw [hass]
              refine ⟨guestInv_setVar _ _ s hgs, wk' - 11#64, wk',
                by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
                by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "i" ≠ ofString "k" by decide, hwk'],
                ?_, hwk23'⟩
              rw [BitVec.toNat_sub]
              have := wk'.isLt
              change (18446744073709551616 - 11 + wk'.toNat) % 18446744073709551616 ≤ wk'.toNat
              omega
            · simp only [if_neg h11, ↓reduceIte] at hnone ⊢
              rw [evaluateHOLFiniteState_skip]
              exact ⟨hgs, wi, wk', hwi', hwk', hilek, hwk23'⟩
          · apply seq_to_guestInv (fun _ h => h.1)
            · exact while_fq12_sqr_inner
                (dec_guestInv _ _ _
                  (dec_guestInv _ _ _
                    (decCall_guestInv' fb_fq_mul
                      (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq_add)
                        (straightOn _ rfl)))))
                (by counter_step)
                rfl
            · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq_add)
              apply TerminatingProgBoundedOn.seq_guestInv
              · exact TerminatingProgBoundedOn.ite_on
                  (dec_guestInv _ _ _ (decCall_guestInv' fb_fq_mul (call_guestInv' fb_fq_add)))
                  (straightOn _ rfl)
              · exact TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl) (straightOn _ rfl)
        simpa [s0, setVarHOLFinite] using hprog s0 hcode hs0 hnt
      · counter_step
    · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq12_reduce)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memcpy)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_heap_release)
      exact straightOn _ rfl
  · fg_arith K.«fq12_sqr»

/-- Helper for `ecp_mul`: `while (i <u len)` when `len ≤ 256` (`2^8`). -/
private def ecpMulGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ wlen : BitVec 64,
    s.locals.lookup (ofString "len") = some (.val (.word wlen)) ∧ wlen.toNat ≤ 256

private def ecpMulMu {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "len") with
  | some (.val (.word wi)), some (.val (.word wl)) =>
    if wl.toNat ≤ 256 then wl.toNat - wi.toNat else 0
  | _, _ => 0

private theorem ecpMulMu_le {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ecpMulMu s ≤ 2 ^ 8 := by
  unfold ecpMulMu
  split
  · split_ifs <;> omega
  · omega

private theorem while_ecp_mul_loop {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep (ofString "i") 1#64 body)
    (havoid : avoidsLocal (ofString "len") body = true) :
    TerminatingProgBoundedOn ecpMulGuard
      (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) body)
      ((2 ^ 8 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank ecpMulGuard
    (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) body B (2 ^ 8)
    ecpMulMu
    (fun s hP => ⟨guestInv_decClock s hP.1, hP.2⟩)
    (fun s hc hP => hbody s hc hP.1)
    (fun s _ _ _ => ecpMulMu_le s) ?_
  intro F s _ ⟨hg, wlen, hwlen, hwlen256⟩ hact hflow
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨vi, vl, hvi, hvl, hword⟩ := evalAt_cmp s .lower _ _ word hw
  have hvl_eq : vl = wlen := by simpa [evalAt, evalHOLExact, hwlen] using hvl.symm
  subst hvl_eq
  have hli : s.locals.lookup (ofString "i") = some (.val (.word vi)) := by
    simpa [evalAt, evalHOLExact] using hvi
  have hcmp : wordCmpHOL .lower vi wlen = true := by
    by_cases hc : wordCmpHOL .lower vi wlen = true
    · exact hc
    · simp [hc] at hword; exact absurd hword hnz
  have hlt : vi.toNat < wlen.toNat := by simpa [wordCmpHOL, BitVec.lt_def] using hcmp
  have hip := hstep (decClockHOLFinite s) vi hli hflow
  have hkeep := evaluate_avoidsLocal_flowing (ofString "len") body havoid (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  have hwlen_post : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "len") =
      some (.val (.word wlen)) := hkeep.trans hwlen
  have hadd1 : (vi + 1#64).toNat = vi.toNat + 1 := BitVec.toNat_add_of_lt (by simp; omega)
  refine ⟨⟨guestInv_evaluate _ _ (guestInv_decClock s hg), wlen, hwlen_post, hwlen256⟩, ?_⟩
  unfold ecpMulMu
  rw [hip, hwlen_post, hli, hwlen, if_pos hwlen256, hadd1]
  omega

/-- Self-contained return bound `≤ 64` for `bit_length64` and `≤ 256` for `u256_bit_length`. -/
private def fnBody64 (d : Decl (BitVec 64)) : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body

private theorem lookup_bit_length64_spec :
    originalRuntimeCode.lookup (ofString "bit_length64") =
      some ([(ofString "x", .one)], fnBody64 Guest.Software.guestFn_bit_length64, .one) :=
  lookup_of_guestAst_getElem 77 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bit_length64) rfl

private theorem lookupCode_one_word_spec {code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fn p1 : MlS} {body foundBody : ProgHOL 64} {rs foundRs : ShapeHOL}
    {v1 : ValueHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlookup : code fn = some ([(p1, .one)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1] =
      some (foundBody, locals, foundRs)) :
    foundBody = body ∧ ∃ w1 : BitVec 64, locals.lookup p1 = some (.val (.word w1)) := by
  have hb := lookupCodeHOLFinite_installed_body code fn _ body foundBody rs foundRs
    [v1] locals hlookup hfound
  refine ⟨hb, ?_⟩
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
  split at hfound
  · cases hfound
  · rename_i _ _ _ raw
    cases v1 with
    | val wl =>
      cases wl with
      | word w1 =>
        have hraw : lookupCodeHOLExact code fn [ValueHOL.val (HolWordLab.word w1)] =
            some (body,
              (fun current => if current = p1 then some (ValueHOL.val (HolWordLab.word w1)) else none),
              rs) := by
          simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL]
        rw [hraw] at raw
        cases raw
        cases hfound
        exact ⟨w1, by simp⟩
    | rStruct _ =>
      simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL] at raw
    | nStruct _ _ =>
      simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL] at raw

private theorem bit_length64_step_le {F : Type}
    (s : PanSemStateFiniteExact 64 F) (k : BitVec 64)
    (n x : BitVec 64) (hx : x.toNat < 2 ^ (2 * k.toNat))
    (hk_pos : 0 < k.toNat) (hk_le : k.toNat ≤ 32)
    (hn_le : n.toNat + 2 * k.toNat ≤ 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hx_loc : s.locals.lookup (ofString "x") = some (.val (.word x))) :
    let stepProg : ProgHOL 64 :=
      .ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64))
        (.seq
          (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k]))
          (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))))
        .skip
    ∀ s', evaluateHOLFiniteState s stepProg = (none, s') →
      ∃ n' x',
        s'.locals.lookup (ofString "n") = some (.val (.word n')) ∧
        s'.locals.lookup (ofString "x") = some (.val (.word x')) ∧
        x'.toNat < 2 ^ k.toNat ∧
        n'.toNat + k.toNat ≤ 64 := by
  dsimp only
  intro s' hrun
  rw [evaluateHOLFiniteState_ite] at hrun
  have hk_not64 : ¬ (¬ k.toNat = 0 ∧ 64 ≤ k.toNat) := by omega
  have hcond : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64)) =
      some (.val (.word (if x >>> k.toNat = 0#64 then 0#64 else 1#64))) := by
    simp [evalHOLExact, hx_loc, Compiler.Encoders.Asm.wordCmpHOL, wordShiftHOL, hk_not64]
  rw [hcond] at hrun
  dsimp only at hrun
  by_cases hz : x >>> k.toNat = 0#64
  · rw [if_pos hz] at hrun
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    rw [if_pos h0, evaluateHOLFiniteState_skip] at hrun
    cases hrun
    refine ⟨n, x, hn, hx_loc, ?_, by omega⟩
    have hzt := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hzt
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hzt
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k.toNat)).mp hzt
  · rw [if_neg hz, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide),
      evaluateHOLFiniteState_seq_line780] at hrun
    have hasgn_n : evaluateHOLFiniteState s
        (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k])) =
        (none, setVarHOLFinite (ofString "n") (.val (.word (n + k))) s) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hn,
        wordOpHOL, wordOp, valueIsWord, valueWord,
        lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, setVarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hasgn_n] at hrun
    dsimp only at hrun
    let s1 := setVarHOLFinite (ofString "n") (.val (.word (n + k))) s
    have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word (n + k))) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_x : s1.locals.lookup (ofString "x") = some (.val (.word x)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "x" by decide, hx_loc]
    have hasgn_x : evaluateHOLFiniteState s1
        (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))) =
        (none, setVarHOLFinite (ofString "x") (.val (.word (x >>> k.toNat))) s1) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hs1_x, wordShiftHOL, hk_not64,
        lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, setVarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hasgn_x] at hrun
    cases hrun
    refine ⟨n + k, x >>> k.toNat, ?_, ?_, ?_, ?_⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "x" ≠ ofString "n" by decide, hs1_n]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hpow : 2 ^ (2 * k.toNat) = 2 ^ k.toNat * 2 ^ k.toNat := by
        rw [Nat.two_mul, Nat.pow_add]
      rw [hpow] at hx
      exact Nat.div_lt_of_lt_mul hx
    · have hadd : (n + k).toNat = n.toNat + k.toNat := BitVec.toNat_add_of_lt (by omega)
      omega

private theorem evaluate_bit_length64_le64 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (x : BitVec 64)
    (hx : state.locals.lookup (ofString "x") = some (.val (.word x))) :
    ∀ w, (evaluateHOLFiniteState state (fnBody64 Guest.Software.guestFn_bit_length64)).1 =
      some (.returned w) →
      ∃ b : BitVec 64, w = .val (.word b) ∧ b.toNat ≤ 64 := by
  intro w hrun
  unfold fnBody64 at hrun
  dsimp only [extractFn, Guest.Software.guestFn_bit_length64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hrun
  let s0 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) state
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_x : s0.locals.lookup (ofString "x") = some (.val (.word x)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "x" by decide, hx]
  have hno_ret_step : ∀ (k : BitVec 64) (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState st
        (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64))
          (.seq
            (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k]))
            (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))))
          .skip)).1 ≠ some (.returned w) := by
    intro k st hc
    rw [evaluateHOLFiniteState_ite] at hc
    split at hc
    · split at hc
      · rw [evaluateHOLFiniteState_skip] at hc; simp at hc
      · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hc
        split at hc
        · simp at hc
        · split at hc
          · dsimp only at hc
            rw [evaluateHOLFiniteState_assign] at hc
            split at hc
            · simp at hc
            · split at hc <;> simp at hc
          · simp at hc
    · simp at hc
  have hstep_seq : ∀ {p1 p2 : ProgHOL 64} {st : PanSemStateFiniteExact 64 F},
      (evaluateHOLFiniteState st (.seq p1 p2)).1 = some (.returned w) →
      (evaluateHOLFiniteState st p1).1 ≠ some (.returned w) →
      ∃ sm, evaluateHOLFiniteState st p1 = (none, sm) ∧
        (evaluateHOLFiniteState sm p2).1 = some (.returned w) := by
    intro p1 p2 st hs hnr
    rw [evaluateHOLFiniteState_seq_line780] at hs
    rcases hr1 : evaluateHOLFiniteState st p1 with ⟨r1, sm⟩
    rw [hr1] at hs hnr
    cases r1 with
    | none => exact ⟨sm, rfl, hs⟩
    | some _ => exact False.elim (hnr hs)
  obtain ⟨s1, hr1, hrun⟩ := hstep_seq hrun (hno_ret_step 32#64 s0)
  obtain ⟨n1, x1, hn1, hx1, hxb1, hnb1⟩ := bit_length64_step_le s0 32#64 0#64 x
    (by change x.toNat < 2 ^ 64; exact x.isLt) (by decide) (by decide) (by decide) hs0_n hs0_x s1 hr1
  obtain ⟨s2, hr2, hrun⟩ := hstep_seq hrun (hno_ret_step 16#64 s1)
  obtain ⟨n2, x2, hn2, hx2, hxb2, hnb2⟩ := bit_length64_step_le s1 16#64 n1 x1
    hxb1 (by decide) (by decide) (by change n1.toNat + 32 ≤ 64; exact hnb1) hn1 hx1 s2 hr2
  obtain ⟨s3, hr3, hrun⟩ := hstep_seq hrun (hno_ret_step 8#64 s2)
  obtain ⟨n3, x3, hn3, hx3, hxb3, hnb3⟩ := bit_length64_step_le s2 8#64 n2 x2
    hxb2 (by decide) (by decide) (by change n2.toNat + 16 ≤ 64; exact hnb2) hn2 hx2 s3 hr3
  obtain ⟨s4, hr4, hrun⟩ := hstep_seq hrun (hno_ret_step 4#64 s3)
  obtain ⟨n4, x4, hn4, hx4, hxb4, hnb4⟩ := bit_length64_step_le s3 4#64 n3 x3
    hxb3 (by decide) (by decide) (by change n3.toNat + 8 ≤ 64; exact hnb3) hn3 hx3 s4 hr4
  obtain ⟨s5, hr5, hrun⟩ := hstep_seq hrun (hno_ret_step 2#64 s4)
  obtain ⟨n5, x5, hn5, hx5, hxb5, hnb5⟩ := bit_length64_step_le s4 2#64 n4 x4
    hxb4 (by decide) (by decide) (by change n4.toNat + 4 ≤ 64; exact hnb4) hn4 hx4 s5 hr5
  obtain ⟨s6, hr6, hrun⟩ := hstep_seq hrun (hno_ret_step 1#64 s5)
  obtain ⟨n6, x6, hn6, hx6, hxb6, hnb6⟩ := bit_length64_step_le s5 1#64 n5 x5
    hxb5 (by decide) (by decide) (by change n5.toNat + 2 ≤ 64; exact hnb5) hn5 hx5 s6 hr6
  rw [evaluateHOLFiniteState_return] at hrun
  have hev_ret : @evalHOLExact 64 F _ s6.toExact
      (fun a => Classical.propDecidable (s6.memaddrs a))
      (.op .add [.var .local (ofString "n"), .var .local (ofString "x")]) =
      some (.val (.word (n6 + x6))) := by
    simp [evalHOLExact, evalListHOLExact, hn6, hx6, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hev_ret] at hrun
  dsimp only at hrun
  split at hrun
  · simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hrun
    subst hrun
    refine ⟨n6 + x6, rfl, ?_⟩
    change x6.toNat < 2 ^ 1 at hxb6
    change n6.toNat + 1 ≤ 64 at hnb6
    have hadd : (n6 + x6).toNat = n6.toNat + x6.toNat := BitVec.toNat_add_of_lt (by omega)
    omega
  · simp at hrun

private theorem u256_bit_length_ret_le_256 {F : Type}
    (entry post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hcode : entry.code = originalRuntimeCode)
    (hrun : evaluateHOLFiniteState entry (fnBody64 Guest.Software.guestFn_u256_bit_length) =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 256 := by
  unfold fnBody64 at hrun
  dsimp only [extractFn, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hrun
  have hbranch : ∀ (s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64) (nm : MlS)
      (arg : ExpHOL 64) (off : BitVec 64) (rest : ProgHOL 64),
      off.toNat ≤ 192 →
      s.code = originalRuntimeCode →
      evaluateHOLFiniteState s
        (.seq (.ite cond (.decCall nm .one (ofString "bit_length64") [arg]
          (.return (.op .add [.const off, .var .local nm]))) .skip) rest) =
        (some (.returned v), post) →
      (∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 256) ∨
      evaluateHOLFiniteState s rest = (some (.returned v), post) := by
    intro s cond nm arg off rest hoff hs_code hseq
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hseq
    split at hseq
    · split at hseq
      · rw [evaluateHOLFiniteState_skip] at hseq; exact Or.inr hseq
      · rcases hdc : evaluateHOLFiniteState s
            (.decCall nm .one (ofString "bit_length64") [arg]
              (.return (.op .add [.const off, .var .local nm]))) with ⟨rdc, sdc⟩
        rw [hdc] at hseq
        dsimp only at hseq
        have hdc1 := congrArg Prod.fst hdc
        dsimp only at hdc1
        rw [evaluateHOLFiniteState_decCall_total] at hdc1
        rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] with _ | vs
        · rw [hargs] at hdc1; subst rdc; cases hseq
        · rw [hargs] at hdc1; dsimp only at hdc1
          have hvs1 : ∃ v1, vs = [v1] := by
            rw [evalListHOLFinite_eq_toExact] at hargs
            simp only [evalListHOLExact] at hargs
            rcases ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg with _ | v1
            · rw [ha] at hargs; cases hargs
            · rw [ha] at hargs; cases hargs; exact ⟨v1, rfl⟩
          obtain ⟨v1, rfl⟩ := hvs1
          rcases hlk : lookupCodeHOLFinite s.code.lookup (ofString "bit_length64") [v1] with _ | ⟨b, cal, rs⟩
          · rw [hlk] at hdc1; subst rdc; cases hseq
          · rw [hlk] at hdc1; dsimp only at hdc1
            split at hdc1
            · subst rdc; cases hseq
            · rcases hrb : evaluateHOLFiniteState (callEntryStateHOLFinite s cal) b with ⟨rb, sb⟩
              rw [hrb] at hdc1
              cases rb with
              | none => dsimp only at hdc1; subst rdc; cases hseq
              | some rr =>
                cases rr with
                | «break» => dsimp only at hdc1; subst rdc; cases hseq
                | «continue» => dsimp only at hdc1; subst rdc; cases hseq
                | error => dsimp only at hdc1; subst rdc; cases hseq
                | timeOut => dsimp only at hdc1; subst rdc; cases hseq
                | exception _ _ => dsimp only at hdc1; subst rdc; cases hseq
                | finalFfi _ => dsimp only at hdc1; subst rdc; cases hseq
                | returned vv =>
                  dsimp only at hdc1
                  split at hdc1
                  · dsimp only at hdc1
                    have hlk' := hlk; rw [hs_code] at hlk'
                    obtain ⟨rfl, w1, hw1⟩ := lookupCode_one_word_spec lookup_bit_length64_spec hlk'
                    obtain ⟨wb, rfl, hwb64⟩ := evaluate_bit_length64_le64
                      (callEntryStateHOLFinite s cal) w1 hw1 vv (by rw [hrb])
                    rw [evaluateHOLFiniteState_return] at hdc1
                    simp only [evalHOLExact, evalListHOLExact, setVarHOLFinite,
                      HolFiniteMapExact.lookup_update, FUPDATE, ↓reduceIte,
                      wordOpHOL, wordOp, valueIsWord, valueWord] at hdc1
                    split at hdc1
                    · subst rdc
                      have hinj := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj hseq).1)
                      subst hinj
                      refine Or.inl ⟨off + wb, rfl, ?_⟩
                      have hadd : (off + wb).toNat = off.toNat + wb.toNat := BitVec.toNat_add_of_lt (by omega)
                      omega
                    · subst rdc; cases hseq
                  · subst rdc; cases hseq
    · cases hseq
  rcases hbranch entry _ (ofString "n3") _ 192#64 _ (by decide) hcode hrun with h | h1
  · exact h
  · rcases hbranch entry _ (ofString "n2") _ 128#64 _ (by decide) hcode h1 with h | h2
    · exact h
    · rcases hbranch entry _ (ofString "n1") _ 64#64 _ (by decide) hcode h2 with h | h3
      · exact h
      · rw [evaluateHOLFiniteState_call] at h3
        rcases hargs : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
            [.rfield 0 (.var .local (ofString "a"))] with _ | vs
        · rw [hargs] at h3; cases h3
        · rw [hargs] at h3; dsimp only at h3
          have hvs1 : ∃ v1, vs = [v1] := by
            rw [evalListHOLFinite_eq_toExact] at hargs
            simp only [evalListHOLExact] at hargs
            rcases ha : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a))
                (.rfield 0 (.var .local (ofString "a"))) with _ | v1
            · rw [ha] at hargs; cases hargs
            · rw [ha] at hargs; cases hargs; exact ⟨v1, rfl⟩
          obtain ⟨v1, rfl⟩ := hvs1
          rcases hlk : lookupCodeHOLFinite entry.code.lookup (ofString "bit_length64") [v1] with _ | ⟨b, cal, rs⟩
          · rw [hlk] at h3; cases h3
          · rw [hlk] at h3; dsimp only at h3
            split at h3
            · cases h3
            · rcases hrb : evaluateHOLFiniteState (callEntryStateHOLFinite entry cal) b with ⟨rb, sb⟩
              rw [hrb] at h3
              cases rb with
              | none => cases h3
              | some rr =>
                cases rr with
                | returned vv =>
                  dsimp only at h3
                  split at h3
                  · have hinj := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj h3).1)
                    subst hinj
                    have hlk' := hlk; rw [hcode] at hlk'
                    obtain ⟨rfl, w1, hw1⟩ := lookupCode_one_word_spec lookup_bit_length64_spec hlk'
                    obtain ⟨wb, rfl, hwb64⟩ := evaluate_bit_length64_le64
                      (callEntryStateHOLFinite entry cal) w1 hw1 vv (by rw [hrb])
                    exact ⟨wb, rfl, by omega⟩
                  · cases h3
                | _ => cases h3

/-- 7. `fb_ecp_mul` (`len = u256_bit_length(n) ≤ 256 = 2^8`) -/
theorem fb_ecp_mul :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_mul") K.«ecp_mul» := by
  have h_fe_mul := fb_fe_mul_of fb_fq12_mul
  have h_fe_sqr := fb_fe_sqr_of h_fe_mul fb_fq12_sqr
  have h_fe_mul_small := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fe_mul_small
  have h_fe_sub := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fe_sub
  have h_fe_eq := fb_fe_eq_of fb_memeq
  have h_ecp_double := fb_ecp_double_of h_fe_mul h_fe_mul_small h_fe_sqr h_fe_sub
  have h_ecp_add := fb_ecp_add_of h_ecp_double h_fe_eq h_fe_mul h_fe_mul_small h_fe_sqr h_fe_sub
  fg_unfold 675 Guest.Software.guestFn_ecp_mul
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply decCall_guestInv' fb_heap_mark
    apply decCall_guestInv' fb_alloc
    apply decCall_guestInv' fb_alloc
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_ecp_set_inf)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memcpy)
    apply TerminatingProgBoundedOn.decCall_on (Q := ecpMulGuard) fb_u256_bit_length
    · intro F s _ _ callee _ _ hg _ _
      exact guestInv_callEntry s callee hg
    · intro F s values body' callee ret' value post hcode hg _ hfound hrun
      have hlook_ubl : originalRuntimeCode.lookup (ofString "u256_bit_length") =
          some ([(ofString "a", .comb [.one, .one, .one, .one])],
                fnBody64 Guest.Software.guestFn_u256_bit_length, .one) :=
        lookup_of_guestAst_getElem 78 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_u256_bit_length) rfl
      have hfound' := hfound; rw [hcode] at hfound'
      have hb_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
        (ofString "u256_bit_length") _ (fnBody64 Guest.Software.guestFn_u256_bit_length)
        body' .one ret' values callee hlook_ubl hfound'
      subst body'
      obtain ⟨wlen, rfl, hwlen256⟩ := u256_bit_length_ret_le_256
        (callEntryStateHOLFinite s callee) post value hcode hrun
      have hpostG : GuestInv post := by
        have := guestInv_evaluate (callEntryStateHOLFinite s callee)
          (fnBody64 Guest.Software.guestFn_u256_bit_length)
          (guestInv_callEntry s callee hg)
        rw [hrun] at this; exact this
      refine ⟨guestInv_setVar _ _ _ (guestInv_with_locals_clock post s.locals post.clock hpostG),
        wlen, ?_, hwlen256⟩
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · have hglo : GuestLocalsOnly ["len"] ecpMulGuard := {
        toGuest := fun _ h => h.1
        congr := fun _ _ hg hkeep ⟨_, wl, hl, hl256⟩ =>
          ⟨hg, wl, (hkeep "len" (by simp)).trans hl, hl256⟩
      }
      apply dec_avoids_on hglo _ (by decide)
      apply seq_to_guestInv (fun _ h => h.1)
      · exact while_ecp_mul_loop
          (decCall_guestInv' fb_u256_bit
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.ite_on (call_guestInv' h_ecp_add) (straightOn _ rfl))
              (TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
                (TerminatingProgBoundedOn.ite_on (call_guestInv' h_ecp_double) (straightOn _ rfl)))))
          (CounterStep.decCall _ _ _ _ _ _ (by decide)
            (CounterStep.seq _ _ _ rfl rfl
              (CounterStep.suffix _ _ _ (CounterStep.assign _ _) rfl)))
          rfl
      · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memcpy)
        apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_heap_release)
        exact straightOn _ rfl
  · fg_arith K.«ecp_mul»

end InitECandidate.Solver.Wave8GuestInv.R16ArithPort.Capped
