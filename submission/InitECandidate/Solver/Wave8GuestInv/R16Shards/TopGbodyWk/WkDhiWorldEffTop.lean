import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDhiSplitWorldEff

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

theorem worldEff_decode_payload_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)} {wp wlen : BitVec 64}
    (hWOK : WorldOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) B dhiGw)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word wp)))
    (hlen : entry.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_payload)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_payload)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_payload)).2 (dhiOffsRegions s) B dhiGw := by
  dsimp only [Guest.Software.guestFn_decode_payload, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_seq hnt hcr
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff _ _ hnt_a hcr_a)
    (fun m1 hm1 heff1 hnt1 hcr1 => ?_)
  obtain ⟨hm1_eq, _⟩ := ite_ssz_fail_keeps entry m1 heff.code _ _ hm1
  have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm1_eq]; exact hp
  have hm1_len : m1.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm1_eq]; exact hlen
  refine worldEff_decCall_alloc_const heff1 (ofString "pl") 136 (by rfl) (by decide) hnt1 hcr1
    (fun w_pl m2 hm2_loc heff_cp _ hpl_lo hpl_hi _ hnt2 hcr2 => ?_)
  have hm2_pl : m2.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_p,
      show ofString "pl" ≠ ofString "p" by decide]
  have hm2_len : m2.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_len,
      show ofString "pl" ≠ ofString "len" by decide]
  refine worldEff_seq_store_fresh heff_cp (ofString "pl") w_pl 136 0 hm2_pl hpl_lo hpl_hi (by omega) _
    (eval_var_local_word m2 _ wp hm2_p) hnt2 hcr2 (fun m3 hm3_loc heff3 hnt3 hcr3 => ?_)
  refine worldEff_seq_store_fresh heff3 (ofString "pl") w_pl 136 8 (by rw [hm3_loc]; exact hm2_pl) hpl_lo hpl_hi (by omega) _
    (eval_var_local_word m3 _ wlen (by rw [hm3_loc]; exact hm2_len)) hnt3 hcr3 (fun m4 hm4_loc heff4 hnt4 hcr4 => ?_)
  have hm4_pl : m4.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm4_loc, hm3_loc]; exact hm2_pl
  refine worldEff_dec heff4 _ _ _ hnt4 hcr4 (fun v_oex hv_oex _ hnt5 hcr5 => ?_)
  obtain ⟨w_oex, rfl, _⟩ := eval_le32_word_lt m4 _ _ _ _ v_oex hv_oex
  let m5 := setVarHOLFinite (ofString "o_extra") (.val (.word w_oex)) m4
  refine worldEff_dec (heff4.locals_clock _ _) _ _ _ hnt5 hcr5 (fun v_otx hv_otx _ hnt6 hcr6 => ?_)
  obtain ⟨w_otx, rfl, _⟩ := eval_le32_word_lt m5 _ _ _ _ v_otx hv_otx
  let m6 := setVarHOLFinite (ofString "o_txs") (.val (.word w_otx)) m5
  refine worldEff_dec (heff4.locals_clock _ _) _ _ _ hnt6 hcr6 (fun v_owd hv_owd _ hnt7 hcr7 => ?_)
  obtain ⟨w_owd, rfl, _⟩ := eval_le32_word_lt m6 _ _ _ _ v_owd hv_owd
  let m7 := setVarHOLFinite (ofString "o_wd") (.val (.word w_owd)) m6
  refine worldEff_dec (heff4.locals_clock _ _) _ _ _ hnt7 hcr7 (fun v_obl hv_obl _ hnt8 hcr8 => ?_)
  obtain ⟨w_obl, rfl, _⟩ := eval_le32_word_lt m7 _ _ _ _ v_obl hv_obl
  let m8 := setVarHOLFinite (ofString "o_bal") (.val (.word w_obl)) m7
  have hm8_pl : m8.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    dsimp only [m8, m7, m6, m5]
    iterate 4 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm4_pl
  have hm8_oex : m8.locals.lookup (ofString "o_extra") = some (.val (.word w_oex)) := by
    dsimp only [m8, m7, m6, m5]
    iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm8_otx : m8.locals.lookup (ofString "o_txs") = some (.val (.word w_otx)) := by
    dsimp only [m8, m7, m6]
    iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm8_owd : m8.locals.lookup (ofString "o_wd") = some (.val (.word w_owd)) := by
    dsimp only [m8, m7]
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm8_obl : m8.locals.lookup (ofString "o_bal") = some (.val (.word w_obl)) := lookup_setVar_eq _ _ _
  refine worldEff_seq_store_ssz_offs_const hWOK (heff4.locals_clock _ _) 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
    (eval_var_local_word m8 _ w_oex hm8_oex) hnt8 hcr8 (fun m9 hm9_loc heff9 hnt9 hcr9 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff9 8 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m9 _ w_otx (by rw [hm9_loc]; exact hm8_otx)) hnt9 hcr9 (fun m10 hm10_loc heff10 hnt10 hcr10 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff10 16 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m10 _ w_owd (by rw [hm10_loc, hm9_loc]; exact hm8_owd)) hnt10 hcr10 (fun m11 hm11_loc heff11 hnt11 hcr11 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff11 24 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m11 _ w_obl (by rw [hm11_loc, hm10_loc, hm9_loc]; exact hm8_obl)) hnt11 hcr11 (fun m12 hm12_loc heff12 hnt12 hcr12 => ?_)
  have hm12_pl : m12.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hm12_loc, hm11_loc, hm10_loc, hm9_loc]; exact hm8_pl
  refine worldEff_seq hnt12 hcr12
    (fun hnt_a hcr_a => worldEff_call0_ro heff12 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m13 hm13 heff13 hnt13 hcr13 => ?_)
  have hm13_pl : m13.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    have hk := evaluate_keepLocal (ofString "pl") _ (by decide) m12 (Or.inl (congrArg Prod.fst hm13))
    rw [hm13] at hk; rw [hk]; exact hm12_pl
  refine worldEff_seq hnt13 hcr13
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff13 _ _ hnt_a hcr_a)
    (fun m14 hm14 heff14 hnt14 hcr14 => ?_)
  obtain ⟨hm14_eq, _⟩ := ite_ssz_fail_keeps m13 m14 heff13.code _ _ hm14
  have hm14_pl : m14.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm14_eq]; exact hm13_pl
  refine worldEff_seq_store_fresh heff14 (ofString "pl") w_pl 136 16 hm14_pl hpl_lo hpl_hi (by omega) _
    (eval_op_word m14 _ ⟨_, _, rfl⟩) hnt14 hcr14 (fun m15 hm15_loc heff15 hnt15 hcr15 => ?_)
  refine worldEff_seq_store_fresh heff15 (ofString "pl") w_pl 136 24 (by rw [hm15_loc]; exact hm14_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m15 _ ⟨_, _, rfl⟩) hnt15 hcr15 (fun m16 hm16_loc heff16 hnt16 hcr16 => ?_)
  have hm16_pl : m16.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm16_loc, hm15_loc]; exact hm14_pl
  refine worldEff_decCall_eff heff16 _ _ _ _ _ _ _ lookup_ssz_split_var_list
    (fun callee _ _ _ hnt_c hres_c => worldEff_ssz_split_var_list_body (heff16.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
    (fun _ _ rv_txs cpost_txs _ _ _ hsh_txs heff_txs hnt17 hcr17 => ?_) hnt16 hcr16
  obtain ⟨w_txp, w_ntx, rfl⟩ := shape_two_words_dhi rv_txs hsh_txs
  let m17 := setVarHOLFinite (ofString "txs") (.rStruct [.val (.word w_txp), .val (.word w_ntx)]) { cpost_txs with locals := m16.locals }
  have hm17_txs : m17.locals.lookup (ofString "txs") = some (.rStruct [.val (.word w_txp), .val (.word w_ntx)]) :=
    lookup_setVar_eq _ _ _
  have hm17_pl : m17.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    dsimp only [m17]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm16_pl
  refine worldEff_seq_store_fresh (heff_txs.locals_clock _ _) (ofString "pl") w_pl 136 32 hm17_pl hpl_lo hpl_hi (by omega) _
    (eval_rfield_word m17 0 _ w_txp w_ntx hm17_txs (Or.inl rfl)) hnt17 hcr17 (fun m18 hm18_loc heff18 hnt18 hcr18 => ?_)
  refine worldEff_seq_store_fresh heff18 (ofString "pl") w_pl 136 40 (by rw [hm18_loc]; exact hm17_pl) hpl_lo hpl_hi (by omega) _
    (eval_rfield_word m18 1 _ w_txp w_ntx (by rw [hm18_loc]; exact hm17_txs) (Or.inr rfl)) hnt18 hcr18 (fun m19 hm19_loc heff19 hnt19 hcr19 => ?_)
  have hm19_pl : m19.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm19_loc, hm18_loc]; exact hm17_pl
  refine worldEff_decCall_ro heff19 ro_ssz_fixed_list_count _ _ _ hnt19 hcr19
    (fun rv_nwd cpost_nwd hsh_nwd hcp_eq hnt20 hcr20 => ?_)
  obtain ⟨w_nwd, rfl⟩ := val_word_of_shapeEq_one hsh_nwd
  have heff_nwd : WorldEff s (setVarHOLFinite (ofString "nwd") (.val (.word w_nwd)) { cpost_nwd with locals := m19.locals }) (dhiOffsRegions s) B dhiGw := by
    rw [hcp_eq]; exact heff19.locals_clock _ _
  let m20 := setVarHOLFinite (ofString "nwd") (.val (.word w_nwd)) { cpost_nwd with locals := m19.locals }
  have hm20_nwd : m20.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) := lookup_setVar_eq _ _ _
  have hm20_pl : m20.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    dsimp only [m20]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm19_pl
  refine worldEff_seq_store_fresh heff_nwd (ofString "pl") w_pl 136 48 hm20_pl hpl_lo hpl_hi (by omega) _
    (eval_op_word m20 _ ⟨_, _, rfl⟩) hnt20 hcr20 (fun m21 hm21_loc heff21 hnt21 hcr21 => ?_)
  refine worldEff_seq_store_fresh heff21 (ofString "pl") w_pl 136 56 (by rw [hm21_loc]; exact hm20_pl) hpl_lo hpl_hi (by omega) _
    (eval_var_local_word m21 _ w_nwd (by rw [hm21_loc]; exact hm20_nwd)) hnt21 hcr21 (fun m22 hm22_loc heff22 hnt22 hcr22 => ?_)
  have hm22_pl : m22.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm22_loc, hm21_loc]; exact hm20_pl
  refine worldEff_seq_store_fresh heff22 (ofString "pl") w_pl 136 64 hm22_pl hpl_lo hpl_hi (by omega) _
    (eval_op_word m22 _ ⟨_, _, rfl⟩) hnt22 hcr22 (fun m23 hm23_loc heff23 hnt23 hcr23 => ?_)
  refine worldEff_seq_store_fresh heff23 (ofString "pl") w_pl 136 72 (by rw [hm23_loc]; exact hm22_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m23 _ ⟨_, _, rfl⟩) hnt23 hcr23 (fun m24 hm24_loc heff24 hnt24 hcr24 => ?_)
  have hm24_pl : m24.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm24_loc, hm23_loc]; exact hm22_pl
  refine worldEff_seq_store_fresh heff24 (ofString "pl") w_pl 136 80 hm24_pl hpl_lo hpl_hi (by omega) _
    (eval_op_word m24 _ ⟨_, _, rfl⟩) hnt24 hcr24 (fun m25 hm25_loc heff25 hnt25 hcr25 => ?_)
  refine worldEff_seq_store_fresh heff25 (ofString "pl") w_pl 136 88 (by rw [hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m25 _ ⟨_, _, rfl⟩) hnt25 hcr25 (fun m26 hm26_loc heff26 hnt26 hcr26 => ?_)
  refine worldEff_seq_store_fresh heff26 (ofString "pl") w_pl 136 96 (by rw [hm26_loc, hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m26 _ ⟨_, _, rfl⟩) hnt26 hcr26 (fun m27 hm27_loc heff27 hnt27 hcr27 => ?_)
  refine worldEff_seq_store_fresh heff27 (ofString "pl") w_pl 136 104 (by rw [hm27_loc, hm26_loc, hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m27 _ ⟨_, _, rfl⟩) hnt27 hcr27 (fun m28 hm28_loc heff28 hnt28 hcr28 => ?_)
  refine worldEff_seq_store_fresh heff28 (ofString "pl") w_pl 136 112 (by rw [hm28_loc, hm27_loc, hm26_loc, hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m28 _ ⟨_, _, rfl⟩) hnt28 hcr28 (fun m29 hm29_loc heff29 hnt29 hcr29 => ?_)
  refine worldEff_seq_store_fresh heff29 (ofString "pl") w_pl 136 120 (by rw [hm29_loc, hm28_loc, hm27_loc, hm26_loc, hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m29 _ ⟨_, _, rfl⟩) hnt29 hcr29 (fun m30 hm30_loc heff30 hnt30 hcr30 => ?_)
  refine worldEff_seq_store_fresh heff30 (ofString "pl") w_pl 136 128 (by rw [hm30_loc, hm29_loc, hm28_loc, hm27_loc, hm26_loc, hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m30 _ ⟨_, _, rfl⟩) hnt30 hcr30 (fun m31 _ heff31 _ _ => worldEff_return heff31 _)

theorem worldEff_decode_requests_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_requests)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_requests)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_requests)).2 (dhiOffsRegions s) B dhiGw := by
  dsimp only [Guest.Software.guestFn_decode_requests, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_seq hnt hcr
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff _ _ hnt_a hcr_a)
    (fun m1 _ heff1 hnt1 hcr1 => ?_)
  refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun v_i hv_i _ hnt2 hcr2 => ?_)
  have hv_i_eq : v_i = .val (.word 0#64) := by
    simp [evalHOLExact] at hv_i; exact hv_i.symm
  subst hv_i_eq
  let m2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m1
  let Inv : PanSemStateFiniteExact 64 F → Prop :=
    fun t => ∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧ wi.toNat ≤ 5
  refine worldEff_seq hnt2 hcr2
    (fun hnt_w hcr_w =>
      worldEff_while_cond_dhi _ Inv (fun _ h => h)
        (fun t0 cw hcond hnz heff_t ⟨wi, ht_i, hwi_le⟩ hnt_b hcr_b => ?_)
        m2.clock m2 rfl (heff1.locals_clock _ _) ⟨0#64, lookup_setVar_eq _ _ _, by decide⟩ hnt_w hcr_w)
    (fun m3 _ heff3 hnt3 hcr3 => ?_)
  · have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
    have h5_63 : 5 < (2 : Nat) ^ 63 := by decide
    have hwi_lt : wi.toNat < 5 := by
      rw [evalHOLFinite_eq_toExact] at hcond
      simp only [evalHOLExact, evalListHOLExact, toExact, ht0_i,
        Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small wi 5#64 (by omega) (by decide)] at hcond
      by_cases hlt : wi.toNat < 5
      · exact hlt
      · have h5 : (5#64 : BitVec 64).toNat = 5 := rfl
        simp [h5, hlt] at hcond; exact absurd hcond.symm hnz
    have hoff_eq : (wi * 8#64).toNat = wi.toNat * 8 := by
      rw [BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, fun hf => ?_⟩
    · refine worldEff_seq hnt_b hcr_b
        (fun _ _ => worldEff_store_ssz_offs_dyn hWOK heff_t _ _ (wi * 8#64)
          (by simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, decClockHOLFinite, ht0_i, valueIsWord, valueWord])
          (by omega) (eval_op_word (decClockHOLFinite t0) _ ⟨_, _, rfl⟩))
        (fun tb _ heff_tb _ _ => worldEff_assign_local heff_tb _ _)
    · exact evaluate_incTail_le (ofString "i") 5 (by decide) _ (by decide) (decClockHOLFinite t0) wi ht_i hwi_lt hf
  · refine worldEff_seq hnt3 hcr3
      (fun hnt_a hcr_a => worldEff_call0_ro heff3 ro_ssz_check_offsets_local _ hnt_a hcr_a)
      (fun m4 _ heff4 hnt4 hcr4 => ?_)
    refine worldEff_decCall_alloc_const heff4 (ofString "rq") 80 (by rfl) (by decide) hnt4 hcr4
      (fun w_rq m5 hm5_loc heff_cp _ hrq_lo hrq_hi _ hnt5 hcr5 => ?_)
    have hm5_rq : m5.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := by
      rw [hm5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_dec heff_cp _ _ _ hnt5 hcr5 (fun v_o0 hv_o0 _ hnt6 hcr6 => ?_)
    obtain ⟨w_o0, rfl⟩ := eval_load_one_word m5 _ v_o0 hv_o0
    let m6 := setVarHOLFinite (ofString "o0") (.val (.word w_o0)) m5
    refine worldEff_dec (heff_cp.locals_clock _ _) _ _ _ hnt6 hcr6 (fun v_o1 hv_o1 _ hnt7 hcr7 => ?_)
    obtain ⟨w_o1, rfl⟩ := eval_load_one_word m6 _ v_o1 hv_o1
    let m7 := setVarHOLFinite (ofString "o1") (.val (.word w_o1)) m6
    refine worldEff_dec (heff_cp.locals_clock _ _) _ _ _ hnt7 hcr7 (fun v_o2 hv_o2 _ hnt8 hcr8 => ?_)
    obtain ⟨w_o2, rfl⟩ := eval_load_one_word m7 _ v_o2 hv_o2
    let m8 := setVarHOLFinite (ofString "o2") (.val (.word w_o2)) m7
    refine worldEff_dec (heff_cp.locals_clock _ _) _ _ _ hnt8 hcr8 (fun v_o3 hv_o3 _ hnt9 hcr9 => ?_)
    obtain ⟨w_o3, rfl⟩ := eval_load_one_word m8 _ v_o3 hv_o3
    let m9 := setVarHOLFinite (ofString "o3") (.val (.word w_o3)) m8
    refine worldEff_dec (heff_cp.locals_clock _ _) _ _ _ hnt9 hcr9 (fun v_o4 hv_o4 _ hnt10 hcr10 => ?_)
    obtain ⟨w_o4, rfl⟩ := eval_load_one_word m9 _ v_o4 hv_o4
    let m10 := setVarHOLFinite (ofString "o4") (.val (.word w_o4)) m9
    have hm10_rq : m10.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := by
      dsimp only [m10, m9, m8, m7, m6]
      iterate 5 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact hm5_rq
    refine worldEff_decCall_ro (heff_cp.locals_clock _ _) ro_ssz_fixed_list_count _ _ _ hnt10 hcr10
      (fun rv_n0 cp0 hsh0 hcp0 hnt11 hcr11 => ?_)
    obtain ⟨w_n0, rfl⟩ := val_word_of_shapeEq_one hsh0
    have heff_n0 : WorldEff s (setVarHOLFinite (ofString "n0") (.val (.word w_n0)) { cp0 with locals := m10.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp0]; exact heff_cp.locals_clock _ _
    let m11 := setVarHOLFinite (ofString "n0") (.val (.word w_n0)) { cp0 with locals := m10.locals }
    refine worldEff_decCall_ro heff_n0 ro_ssz_fixed_list_count _ _ _ hnt11 hcr11
      (fun rv_n1 cp1 hsh1 hcp1 hnt12 hcr12 => ?_)
    obtain ⟨w_n1, rfl⟩ := val_word_of_shapeEq_one hsh1
    have heff_n1 : WorldEff s (setVarHOLFinite (ofString "n1") (.val (.word w_n1)) { cp1 with locals := m11.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp1]; exact heff_n0.locals_clock _ _
    let m12 := setVarHOLFinite (ofString "n1") (.val (.word w_n1)) { cp1 with locals := m11.locals }
    refine worldEff_decCall_ro heff_n1 ro_ssz_fixed_list_count _ _ _ hnt12 hcr12
      (fun rv_n2 cp2 hsh2 hcp2 hnt13 hcr13 => ?_)
    obtain ⟨w_n2, rfl⟩ := val_word_of_shapeEq_one hsh2
    have heff_n2 : WorldEff s (setVarHOLFinite (ofString "n2") (.val (.word w_n2)) { cp2 with locals := m12.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp2]; exact heff_n1.locals_clock _ _
    let m13 := setVarHOLFinite (ofString "n2") (.val (.word w_n2)) { cp2 with locals := m12.locals }
    refine worldEff_decCall_ro heff_n2 ro_ssz_fixed_list_count _ _ _ hnt13 hcr13
      (fun rv_n3 cp3 hsh3 hcp3 hnt14 hcr14 => ?_)
    obtain ⟨w_n3, rfl⟩ := val_word_of_shapeEq_one hsh3
    have heff_n3 : WorldEff s (setVarHOLFinite (ofString "n3") (.val (.word w_n3)) { cp3 with locals := m13.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp3]; exact heff_n2.locals_clock _ _
    let m14 := setVarHOLFinite (ofString "n3") (.val (.word w_n3)) { cp3 with locals := m13.locals }
    refine worldEff_decCall_ro heff_n3 ro_ssz_fixed_list_count _ _ _ hnt14 hcr14
      (fun rv_n4 cp4 hsh4 hcp4 hnt15 hcr15 => ?_)
    obtain ⟨w_n4, rfl⟩ := val_word_of_shapeEq_one hsh4
    have heff_n4 : WorldEff s (setVarHOLFinite (ofString "n4") (.val (.word w_n4)) { cp4 with locals := m14.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp4]; exact heff_n3.locals_clock _ _
    let m15 := setVarHOLFinite (ofString "n4") (.val (.word w_n4)) { cp4 with locals := m14.locals }
    have hm15_rq : m15.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := by
      dsimp only [m15, m14, m13, m12, m11]
      iterate 5 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact hm10_rq
    have hm15_n0 : m15.locals.lookup (ofString "n0") = some (.val (.word w_n0)) := by
      dsimp only [m15, m14, m13, m12, m11]
      iterate 4 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
    have hm15_n1 : m15.locals.lookup (ofString "n1") = some (.val (.word w_n1)) := by
      dsimp only [m15, m14, m13, m12]
      iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
    have hm15_n2 : m15.locals.lookup (ofString "n2") = some (.val (.word w_n2)) := by
      dsimp only [m15, m14, m13]
      iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
    have hm15_n3 : m15.locals.lookup (ofString "n3") = some (.val (.word w_n3)) := by
      dsimp only [m15, m14]
      rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
    have hm15_n4 : m15.locals.lookup (ofString "n4") = some (.val (.word w_n4)) := lookup_setVar_eq _ _ _
    refine worldEff_seq_store_fresh heff_n4 (ofString "rq") w_rq 80 0 hm15_rq hrq_lo hrq_hi (by omega) _
      (eval_op_word m15 _ ⟨_, _, rfl⟩) hnt15 hcr15 (fun s1 hl1 he1 hnt_1 hcr_1 => ?_)
    refine worldEff_seq_store_fresh he1 (ofString "rq") w_rq 80 8 (by rw [hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_var_local_word s1 _ w_n0 (by rw [hl1]; exact hm15_n0)) hnt_1 hcr_1 (fun s2 hl2 he2 hnt_2 hcr_2 => ?_)
    refine worldEff_seq_store_fresh he2 (ofString "rq") w_rq 80 16 (by rw [hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_op_word s2 _ ⟨_, _, rfl⟩) hnt_2 hcr_2 (fun s3 hl3 he3 hnt_3 hcr_3 => ?_)
    refine worldEff_seq_store_fresh he3 (ofString "rq") w_rq 80 24 (by rw [hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_var_local_word s3 _ w_n1 (by rw [hl3, hl2, hl1]; exact hm15_n1)) hnt_3 hcr_3 (fun s4 hl4 he4 hnt_4 hcr_4 => ?_)
    refine worldEff_seq_store_fresh he4 (ofString "rq") w_rq 80 32 (by rw [hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_op_word s4 _ ⟨_, _, rfl⟩) hnt_4 hcr_4 (fun s5 hl5 he5 hnt_5 hcr_5 => ?_)
    refine worldEff_seq_store_fresh he5 (ofString "rq") w_rq 80 40 (by rw [hl5, hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_var_local_word s5 _ w_n2 (by rw [hl5, hl4, hl3, hl2, hl1]; exact hm15_n2)) hnt_5 hcr_5 (fun s6 hl6 he6 hnt_6 hcr_6 => ?_)
    refine worldEff_seq_store_fresh he6 (ofString "rq") w_rq 80 48 (by rw [hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_op_word s6 _ ⟨_, _, rfl⟩) hnt_6 hcr_6 (fun s7 hl7 he7 hnt_7 hcr_7 => ?_)
    refine worldEff_seq_store_fresh he7 (ofString "rq") w_rq 80 56 (by rw [hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_var_local_word s7 _ w_n3 (by rw [hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_n3)) hnt_7 hcr_7 (fun s8 hl8 he8 hnt_8 hcr_8 => ?_)
    refine worldEff_seq_store_fresh he8 (ofString "rq") w_rq 80 64 (by rw [hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_op_word s8 _ ⟨_, _, rfl⟩) hnt_8 hcr_8 (fun s9 hl9 he9 hnt_9 hcr_9 => ?_)
    refine worldEff_seq_store_fresh he9 (ofString "rq") w_rq 80 72 (by rw [hl9, hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_var_local_word s9 _ w_n4 (by rw [hl9, hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_n4)) hnt_9 hcr_9 (fun s10 _ he10 _ _ => worldEff_return he10 _)

theorem worldEff_decode_stateless_input_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input)).2 (dhiOffsRegions s) B dhiGw := by
  dsimp only [Guest.Software.guestFn_decode_stateless_input, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_seq hnt hcr
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff _ _ hnt_a hcr_a)
    (fun m1 _ heff1 hnt1 hcr1 => ?_)
  refine worldEff_seq hnt1 hcr1
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff1 _ _ hnt_a hcr_a)
    (fun m2 _ heff2 hnt2 hcr2 => ?_)
  refine worldEff_seq hnt2 hcr2
    (fun _ _ => worldEff_assign_local heff2 _ _)
    (fun m3 _ heff3 hnt3 hcr3 => ?_)
  refine worldEff_seq hnt3 hcr3
    (fun _ _ => worldEff_assign_local heff3 _ _)
    (fun m4 _ heff4 hnt4 hcr4 => ?_)
  refine worldEff_seq hnt4 hcr4
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff4 _ _ hnt_a hcr_a)
    (fun m5 _ heff5 hnt5 hcr5 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff5 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
    (eval_op_word m5 _ ⟨_, _, rfl⟩) hnt5 hcr5 (fun m6 _ heff6 hnt6 hcr6 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff6 8 (by omega) _ _ (Or.inr rfl)
    (eval_op_word m6 _ ⟨_, _, rfl⟩) hnt6 hcr6 (fun m7 _ heff7 hnt7 hcr7 => ?_)
  refine worldEff_seq hnt7 hcr7
    (fun hnt_a hcr_a => worldEff_call0_ro heff7 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m8 _ heff8 hnt8 hcr8 => ?_)
  refine worldEff_dec heff8 _ _ _ hnt8 hcr8 (fun _ _ _ hnt9 hcr9 => ?_)
  refine worldEff_dec (heff8.locals_clock _ _) _ _ _ hnt9 hcr9 (fun _ _ _ hnt10 hcr10 => ?_)
  refine worldEff_decCall_alloc_const (heff8.locals_clock _ _) (ofString "si") 96 (by rfl) (by decide) hnt10 hcr10
    (fun w_si m11 hm11_loc heff_si _ hsi_lo hsi_hi _ hnt11 hcr11 => ?_)
  have hm11_si : m11.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_seq_store_fresh heff_si (ofString "si") w_si 96 88 hm11_si hsi_lo hsi_hi (by omega) _
    (eval_op_word m11 _ ⟨_, _, rfl⟩) hnt11 hcr11 (fun m12 hm12_loc heff12 hnt12 hcr12 => ?_)
  have hm12_si : m12.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm12_loc]; exact hm11_si
  refine worldEff_dec heff12 _ _ _ hnt12 hcr12 (fun v_np _ _ hnt13 hcr13 => ?_)
  let m13 := setVarHOLFinite (ofString "np") v_np m12
  refine worldEff_dec (heff12.locals_clock _ _) _ _ _ hnt13 hcr13 (fun v_nlen _ _ hnt14 hcr14 => ?_)
  let m14 := setVarHOLFinite (ofString "nlen") v_nlen m13
  have hm14_si : m14.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m14, m13]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm12_si
  refine worldEff_seq hnt14 hcr14
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff12.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m15 hm15 heff15 hnt15 hcr15 => ?_)
  obtain ⟨hm15_eq, _⟩ := ite_ssz_fail_keeps m14 m15 heff12.code _ _ hm15
  have hm15_si : m15.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm15_eq]; exact hm14_si
  refine worldEff_dec heff15 _ _ _ hnt15 hcr15 (fun v_opl hv_opl _ hnt16 hcr16 => ?_)
  obtain ⟨w_opl, rfl, _⟩ := eval_le32_word_lt m15 _ _ _ _ v_opl hv_opl
  let m16 := setVarHOLFinite (ofString "o_pl") (.val (.word w_opl)) m15
  refine worldEff_dec (heff15.locals_clock _ _) _ _ _ hnt16 hcr16 (fun v_ovh hv_ovh _ hnt17 hcr17 => ?_)
  obtain ⟨w_ovh, rfl, _⟩ := eval_le32_word_lt m16 _ _ _ _ v_ovh hv_ovh
  let m17 := setVarHOLFinite (ofString "o_vh") (.val (.word w_ovh)) m16
  refine worldEff_dec (heff15.locals_clock _ _) _ _ _ hnt17 hcr17 (fun v_orq hv_orq _ hnt18 hcr18 => ?_)
  obtain ⟨w_orq, rfl, _⟩ := eval_le32_word_lt m17 _ _ _ _ v_orq hv_orq
  let m18 := setVarHOLFinite (ofString "o_rq") (.val (.word w_orq)) m17
  have hm18_si : m18.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m18, m17, m16]; iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm15_si
  have hm18_opl : m18.locals.lookup (ofString "o_pl") = some (.val (.word w_opl)) := by
    dsimp only [m18, m17, m16]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm18_ovh : m18.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by
    dsimp only [m18, m17]; rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm18_orq : m18.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := lookup_setVar_eq _ _ _
  refine worldEff_seq_store_ssz_offs_const hWOK (heff15.locals_clock _ _) 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
    (eval_var_local_word m18 _ w_opl hm18_opl) hnt18 hcr18 (fun m19 hm19_loc heff19 hnt19 hcr19 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff19 8 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m19 _ w_ovh (by rw [hm19_loc]; exact hm18_ovh)) hnt19 hcr19 (fun m20 hm20_loc heff20 hnt20 hcr20 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff20 16 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m20 _ w_orq (by rw [hm20_loc, hm19_loc]; exact hm18_orq)) hnt20 hcr20 (fun m21 hm21_loc heff21 hnt21 hcr21 => ?_)
  have hm21_si : m21.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm21_loc, hm20_loc, hm19_loc]; exact hm18_si
  refine worldEff_seq hnt21 hcr21
    (fun hnt_a hcr_a => worldEff_call0_ro heff21 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m22 hm22 heff22 hnt22 hcr22 => ?_)
  have hm22_si : m22.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    have hk := evaluate_keepLocal (ofString "si") _ (by decide) m21 (Or.inl (congrArg Prod.fst hm22))
    rw [hm22] at hk; rw [hk]; exact hm21_si
  refine worldEff_decCall_eff heff22 _ _ _ _ _ _ _ lookup_decode_payload
    (fun callee vals _ hlook hnt_c hres_c => ?_)
    (fun _ _ rv_pl cp_pl _ _ _ hsh_pl heff_pl hnt23 hcr23 => ?_) hnt22 hcr22
  · obtain ⟨wp_c, wlen_c, _, hc_p, hc_len⟩ :=
      lookupCode_two_words (by decide) lookup_decode_payload (by rwa [heff22.code] at hlook)
    exact worldEff_decode_payload_body hWOK (heff22.locals_clock callee _) hc_p hc_len hnt_c (contOrRes_of_resumes_dhi hres_c)
  · obtain ⟨w_pl, rfl⟩ := val_word_of_shapeEq_one hsh_pl
    let m23 := setVarHOLFinite (ofString "pl") (.val (.word w_pl)) { cp_pl with locals := m22.locals }
    have hm23_pl : m23.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := lookup_setVar_eq _ _ _
    have hm23_si : m23.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_si
    refine worldEff_seq_store_fresh (heff_pl.locals_clock _ _) (ofString "si") w_si 96 0 hm23_si hsi_lo hsi_hi (by omega) _
      (eval_var_local_word m23 _ w_pl hm23_pl) hnt23 hcr23 (fun m24 hm24_loc heff24 hnt24 hcr24 => ?_)
    have hm24_si : m24.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm24_loc]; exact hm23_si
    refine worldEff_decCall_ro heff24 ro_ssz_fixed_list_count _ _ _ hnt24 hcr24
      (fun rv_nvh cp_nvh hsh_nvh hcp_nvh hnt25 hcr25 => ?_)
    obtain ⟨w_nvh, rfl⟩ := val_word_of_shapeEq_one hsh_nvh
    have heff_nvh : WorldEff s (setVarHOLFinite (ofString "nvh") (.val (.word w_nvh)) { cp_nvh with locals := m24.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp_nvh]; exact heff24.locals_clock _ _
    let m25 := setVarHOLFinite (ofString "nvh") (.val (.word w_nvh)) { cp_nvh with locals := m24.locals }
    have hm25_nvh : m25.locals.lookup (ofString "nvh") = some (.val (.word w_nvh)) := lookup_setVar_eq _ _ _
    have hm25_si : m25.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      dsimp only [m25]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm24_si
    refine worldEff_seq_store_fresh heff_nvh (ofString "si") w_si 96 8 hm25_si hsi_lo hsi_hi (by omega) _
      (eval_op_word m25 _ ⟨_, _, rfl⟩) hnt25 hcr25 (fun m26 hm26_loc heff26 hnt26 hcr26 => ?_)
    refine worldEff_seq_store_fresh heff26 (ofString "si") w_si 96 16 (by rw [hm26_loc]; exact hm25_si) hsi_lo hsi_hi (by omega) _
      (eval_var_local_word m26 _ w_nvh (by rw [hm26_loc]; exact hm25_nvh)) hnt26 hcr26 (fun m27 hm27_loc heff27 hnt27 hcr27 => ?_)
    refine worldEff_seq_store_fresh heff27 (ofString "si") w_si 96 24 (by rw [hm27_loc, hm26_loc]; exact hm25_si) hsi_lo hsi_hi (by omega) _
      (eval_op_word m27 _ ⟨_, _, rfl⟩) hnt27 hcr27 (fun m28 hm28_loc heff28 hnt28 hcr28 => ?_)
    have hm28_si : m28.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      rw [hm28_loc, hm27_loc, hm26_loc]; exact hm25_si
    refine worldEff_decCall_eff heff28 _ _ _ _ _ _ _ lookup_decode_requests
      (fun callee _ _ _ hnt_c hres_c => worldEff_decode_requests_body hWOK (heff28.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
      (fun _ _ rv_rq cp_rq _ _ _ hsh_rq heff_rq hnt29 hcr29 => ?_) hnt28 hcr28
    obtain ⟨w_rq, rfl⟩ := val_word_of_shapeEq_one hsh_rq
    let m29 := setVarHOLFinite (ofString "rq") (.val (.word w_rq)) { cp_rq with locals := m28.locals }
    have hm29_rq : m29.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := lookup_setVar_eq _ _ _
    have hm29_si : m29.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      dsimp only [m29]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm28_si
    refine worldEff_seq_store_fresh (heff_rq.locals_clock _ _) (ofString "si") w_si 96 32 hm29_si hsi_lo hsi_hi (by omega) _
      (eval_var_local_word m29 _ w_rq hm29_rq) hnt29 hcr29 (fun m30 hm30_loc heff30 hnt30 hcr30 => ?_)
    have hm30_si : m30.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm30_loc]; exact hm29_si
    refine worldEff_dec heff30 _ _ _ hnt30 hcr30 (fun v_wp _ _ hnt31 hcr31 => ?_)
    let m31 := setVarHOLFinite (ofString "wp") v_wp m30
    refine worldEff_dec (heff30.locals_clock _ _) _ _ _ hnt31 hcr31 (fun v_wlen _ _ hnt32 hcr32 => ?_)
    let m32 := setVarHOLFinite (ofString "wlen") v_wlen m31
    have hm32_si : m32.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      dsimp only [m32, m31]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact hm30_si
    refine worldEff_seq hnt32 hcr32
      (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff30.locals_clock _ _) _ _ hnt_a hcr_a)
      (fun m33 hm33 heff33 hnt33 hcr33 => ?_)
    obtain ⟨hm33_eq, _⟩ := ite_ssz_fail_keeps m32 m33 heff30.code _ _ hm33
    have hm33_si : m33.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm33_eq]; exact hm32_si
    refine worldEff_dec heff33 _ _ _ hnt33 hcr33 (fun v_i hv_i _ hnt34 hcr34 => ?_)
    have hv_i_eq : v_i = .val (.word 0#64) := by
      simp [evalHOLExact] at hv_i; exact hv_i.symm
    subst hv_i_eq
    let m34 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m33
    have hm34_si : m34.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      dsimp only [m34]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm33_si
    let Inv3 : PanSemStateFiniteExact 64 F → Prop :=
      fun t => ∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧ wi.toNat ≤ 3
    refine worldEff_seq hnt34 hcr34
      (fun hnt_w hcr_w =>
        worldEff_while_cond_dhi _ Inv3 (fun _ h => h)
          (fun t0 cw hcond hnz heff_t ⟨wi, ht_i, hwi_le⟩ hnt_b hcr_b => ?_)
          m34.clock m34 rfl (heff33.locals_clock _ _) ⟨0#64, lookup_setVar_eq _ _ _, by decide⟩ hnt_w hcr_w)
      (fun m35 hm35 heff35 hnt35 hcr35 => ?_)
    · have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
      have h3_63 : 3 < (2 : Nat) ^ 63 := by decide
      have hwi_lt : wi.toNat < 3 := by
        rw [evalHOLFinite_eq_toExact] at hcond
        simp only [evalHOLExact, evalListHOLExact, toExact, ht0_i,
          Compiler.Encoders.Asm.wordCmpHOL,
          holAsmSignedLess_small wi 3#64 (by omega) (by decide)] at hcond
        by_cases hlt : wi.toNat < 3
        · exact hlt
        · have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
          simp [h3, hlt] at hcond; exact absurd hcond.symm hnz
      have hoff_eq : (wi * 8#64).toNat = wi.toNat * 8 := by
        rw [BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
      refine ⟨?_, fun hf => ?_⟩
      · refine worldEff_seq hnt_b hcr_b
          (fun _ _ => worldEff_store_ssz_offs_dyn hWOK heff_t _ _ (wi * 8#64)
            (by simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, decClockHOLFinite, ht0_i, valueIsWord, valueWord])
            (by omega) (eval_op_word (decClockHOLFinite t0) _ ⟨_, _, rfl⟩))
          (fun tb _ heff_tb _ _ => worldEff_assign_local heff_tb _ _)
      · exact evaluate_incTail_le (ofString "i") 3 (by decide) _ (by decide) (decClockHOLFinite t0) wi ht_i hwi_lt hf
    · have hm35_si : m35.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        have hk := evaluate_keepLocal (ofString "si") _ (by decide) m34 (Or.inl (congrArg Prod.fst hm35))
        rw [hm35] at hk; rw [hk]; exact hm34_si
      refine worldEff_seq hnt35 hcr35
        (fun hnt_a hcr_a => worldEff_call0_ro heff35 ro_ssz_check_offsets_local _ hnt_a hcr_a)
        (fun m36 hm36 heff36 hnt36 hcr36 => ?_)
      have hm36_si : m36.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        have hk := evaluate_keepLocal (ofString "si") _ (by decide) m35 (Or.inl (congrArg Prod.fst hm36))
        rw [hm36] at hk; rw [hk]; exact hm35_si
      refine worldEff_dec heff36 _ _ _ hnt36 hcr36 (fun v_w0 _ _ hnt37 hcr37 => ?_)
      let m37 := setVarHOLFinite (ofString "w0") v_w0 m36
      refine worldEff_dec (heff36.locals_clock _ _) _ _ _ hnt37 hcr37 (fun v_w1 _ _ hnt38 hcr38 => ?_)
      let m38 := setVarHOLFinite (ofString "w1") v_w1 m37
      refine worldEff_dec (heff36.locals_clock _ _) _ _ _ hnt38 hcr38 (fun v_w2 _ _ hnt39 hcr39 => ?_)
      let m39 := setVarHOLFinite (ofString "w2") v_w2 m38
      have hm39_si : m39.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        dsimp only [m39, m38, m37]; iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm36_si
      refine worldEff_decCall_eff (heff36.locals_clock _ _) _ _ _ _ _ _ _ lookup_decode_bytes_list
        (fun callee _ _ _ hnt_c hres_c => worldEff_decode_bytes_list_body (heff36.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
        (fun _ _ rv_st0 cp_st0 _ _ _ hsh_st0 heff_st0 hnt40 hcr40 => ?_) hnt39 hcr39
      obtain ⟨w_st0a, w_st0b, rfl⟩ := shape_two_words_dhi rv_st0 hsh_st0
      let m40 := setVarHOLFinite (ofString "st0") (.rStruct [.val (.word w_st0a), .val (.word w_st0b)]) { cp_st0 with locals := m39.locals }
      have hm40_st0 : m40.locals.lookup (ofString "st0") = some (.rStruct [.val (.word w_st0a), .val (.word w_st0b)]) := lookup_setVar_eq _ _ _
      have hm40_si : m40.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        dsimp only [m40]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm39_si
      refine worldEff_seq_store_fresh (heff_st0.locals_clock _ _) (ofString "si") w_si 96 40 hm40_si hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m40 0 _ w_st0a w_st0b hm40_st0 (Or.inl rfl)) hnt40 hcr40 (fun m41 hm41_loc heff41 hnt41 hcr41 => ?_)
      refine worldEff_seq_store_fresh heff41 (ofString "si") w_si 96 48 (by rw [hm41_loc]; exact hm40_si) hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m41 1 _ w_st0a w_st0b (by rw [hm41_loc]; exact hm40_st0) (Or.inr rfl)) hnt41 hcr41 (fun m42 hm42_loc heff42 hnt42 hcr42 => ?_)
      have hm42_si : m42.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm42_loc, hm41_loc]; exact hm40_si
      refine worldEff_decCall_eff heff42 _ _ _ _ _ _ _ lookup_decode_bytes_list
        (fun callee _ _ _ hnt_c hres_c => worldEff_decode_bytes_list_body (heff42.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
        (fun _ _ rv_cd cp_cd _ _ _ hsh_cd heff_cd hnt43 hcr43 => ?_) hnt42 hcr42
      obtain ⟨w_cda, w_cdb, rfl⟩ := shape_two_words_dhi rv_cd hsh_cd
      let m43 := setVarHOLFinite (ofString "cd") (.rStruct [.val (.word w_cda), .val (.word w_cdb)]) { cp_cd with locals := m42.locals }
      have hm43_cd : m43.locals.lookup (ofString "cd") = some (.rStruct [.val (.word w_cda), .val (.word w_cdb)]) := lookup_setVar_eq _ _ _
      have hm43_si : m43.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        dsimp only [m43]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm42_si
      refine worldEff_seq_store_fresh (heff_cd.locals_clock _ _) (ofString "si") w_si 96 56 hm43_si hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m43 0 _ w_cda w_cdb hm43_cd (Or.inl rfl)) hnt43 hcr43 (fun m44 hm44_loc heff44 hnt44 hcr44 => ?_)
      refine worldEff_seq_store_fresh heff44 (ofString "si") w_si 96 64 (by rw [hm44_loc]; exact hm43_si) hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m44 1 _ w_cda w_cdb (by rw [hm44_loc]; exact hm43_cd) (Or.inr rfl)) hnt44 hcr44 (fun m45 hm45_loc heff45 hnt45 hcr45 => ?_)
      have hm45_si : m45.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm45_loc, hm44_loc]; exact hm43_si
      refine worldEff_decCall_eff heff45 _ _ _ _ _ _ _ lookup_decode_bytes_list
        (fun callee _ _ _ hnt_c hres_c => worldEff_decode_bytes_list_body (heff45.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
        (fun _ _ rv_hd cp_hd _ _ _ hsh_hd heff_hd hnt46 hcr46 => ?_) hnt45 hcr45
      obtain ⟨w_hda, w_hdb, rfl⟩ := shape_two_words_dhi rv_hd hsh_hd
      let m46 := setVarHOLFinite (ofString "hd") (.rStruct [.val (.word w_hda), .val (.word w_hdb)]) { cp_hd with locals := m45.locals }
      have hm46_hd : m46.locals.lookup (ofString "hd") = some (.rStruct [.val (.word w_hda), .val (.word w_hdb)]) := lookup_setVar_eq _ _ _
      have hm46_si : m46.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        dsimp only [m46]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm45_si
      refine worldEff_seq_store_fresh (heff_hd.locals_clock _ _) (ofString "si") w_si 96 72 hm46_si hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m46 0 _ w_hda w_hdb hm46_hd (Or.inl rfl)) hnt46 hcr46 (fun m47 hm47_loc heff47 hnt47 hcr47 => ?_)
      refine worldEff_seq_store_fresh heff47 (ofString "si") w_si 96 80 (by rw [hm47_loc]; exact hm46_si) hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m47 1 _ w_hda w_hdb (by rw [hm47_loc]; exact hm46_hd) (Or.inr rfl)) hnt47 hcr47 (fun m48 _ heff48 _ _ => worldEff_return heff48 _)

theorem worldEff_decode_host_input_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_host_input)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_host_input)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_host_input)).2 (dhiOffsRegions s) B dhiGw := by
  dsimp only [Guest.Software.guestFn_decode_host_input, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_seq hnt hcr
    (fun hnt_a hcr_a => worldEff_call0_eff heff _ _ _ _ _ lookup_precheck_host_ssz_header
      (fun callee _ _ _ hnt_c hres_c => worldEff_precheck_host_ssz_header_body hWOK (heff.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
      hnt_a hcr_a)
    (fun m1 _ heff1 hnt1 hcr1 => ?_)
  refine worldEff_decCall_eff heff1 _ _ _ _ _ _ _ lookup_input_blob
    (fun callee _ _ _ hnt_c hres_c => worldEff_input_blob_body (heff1.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
    (fun _ _ _ cp_inp _ _ _ _ heff_inp hnt2 hcr2 => ?_) hnt1 hcr1
  exact worldEff_tailCall_eff (heff_inp.locals_clock _ _) _ _ _ _ _ lookup_decode_stateless_input
    (fun callee _ _ _ hnt_c hres_c => worldEff_decode_stateless_input_body hWOK (heff_inp.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
    hnt2 hcr2

theorem wk_decode_host_input_noExtra :
    WorldKeeps WorldOK
      (fun s => [(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "decode_host_input") := by
  refine ⟨_, _, _, lookup_decode_host_input, ?_⟩
  intro F s hc hWOK hl hnt hres
  have heff : WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2
      (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw :=
    worldEff_decode_host_input_body hWOK
      (WorldEff.refl s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw hWOK.1 hc)
      hnt (contOrRes_of_resumes_dhi hres)
  exact R16Shards.WorldEff.to_worldStep_Q (R := dhiOffsRegions)
    hWOK (by intro _ h; cases h)
    (by decide)
    heff (fun _ _ _ _ _ _ _ _ => trivial)

/-! ### `RetInputSound` Postcondition Helpers -/


end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
