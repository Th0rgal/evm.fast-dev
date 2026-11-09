import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDhiUdivmodPre

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

theorem worldEff_precheck_host_ssz_header_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_precheck_host_ssz_header)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_precheck_host_ssz_header)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_precheck_host_ssz_header)).2 (dhiOffsRegions s) B dhiGw := by
  dsimp only [Guest.Software.guestFn_precheck_host_ssz_header, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_dec heff _ _ _ hnt hcr (fun _ _ _ hnt1 hcr1 => ?_)
  refine worldEff_seq hnt1 hcr1
    (fun _ _ => worldEff_shMemLoad_local (heff.locals_clock _ _) _ _ _)
    (fun m1 _ heff1 hnt2 hcr2 => ?_)
  refine worldEff_seq hnt2 hcr2
    (fun hnt_a hcr_a => worldEff_ite heff1 _ hnt_a hcr_a
      (fun _ _ _ _ _ => worldEff_return heff1 _)
      (fun _ _ _ => worldEff_skip heff1))
    (fun m2 _ heff2 hnt3 hcr3 => ?_)
  refine worldEff_seq hnt3 hcr3
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff2 _ _ hnt_a hcr_a)
    (fun m3 _ heff3 hnt4 hcr4 => ?_)
  refine worldEff_decCall_eff heff3 _ _ _ _ _ _ _ lookup_host_input_byte
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_byte_body (heff3.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ _ _ _ _ _ _ heff4 hnt5 hcr5 => ?_) hnt4 hcr4
  refine worldEff_decCall_eff (heff4.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_byte
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_byte_body (heff4.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ _ _ _ _ _ _ heff5 hnt6 hcr6 => ?_) hnt5 hcr5
  refine worldEff_seq hnt6 hcr6
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff5.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m6 _ heff6 hnt7 hcr7 => ?_)
  refine worldEff_dec heff6 _ _ _ hnt7 hcr7 (fun _ _ _ hnt8 hcr8 => ?_)
  refine worldEff_seq hnt8 hcr8
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff6.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m7 _ heff7 hnt9 hcr9 => ?_)
  refine worldEff_decCall_eff heff7 _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff7.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv1 cpost1 _ _ _ hsh1 heff8 hnt10 hcr10 => ?_) hnt9 hcr9
  obtain ⟨w_onpr, rfl⟩ := val_word_of_shapeEq_one hsh1
  refine worldEff_decCall_eff (heff8.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff8.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv2 cpost2 _ _ _ hsh2 heff9 hnt11 hcr11 => ?_) hnt10 hcr10
  obtain ⟨w_owit, rfl⟩ := val_word_of_shapeEq_one hsh2
  have honpr_m8 : (setVarHOLFinite (ofString "o_wit") (.val (.word w_owit))
      { cpost2 with locals := (setVarHOLFinite (ofString "o_npr") (.val (.word w_onpr)) { cpost1 with locals := m7.locals }).locals }).locals.lookup
      (ofString "o_npr") = some (.val (.word w_onpr)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
  have howit_m8 : (setVarHOLFinite (ofString "o_wit") (.val (.word w_owit))
      { cpost2 with locals := (setVarHOLFinite (ofString "o_npr") (.val (.word w_onpr)) { cpost1 with locals := m7.locals }).locals }).locals.lookup
      (ofString "o_wit") = some (.val (.word w_owit)) :=
    lookup_setVar_eq _ _ _
  refine worldEff_seq hnt11 hcr11
    (fun _ _ => worldEff_store_ssz_offs_const hWOK (heff9.locals_clock _ _) 0 (by decide) _ _ (Or.inl ⟨rfl, rfl⟩)
      (eval_local_word _ _ _ honpr_m8))
    (fun m9 hm9 heff10 hnt12 hcr12 => ?_)
  have hm9_loc := store_keeps_locals _ _ _ _ hm9
  have howit_m9 : m9.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by
    rw [hm9_loc]; exact howit_m8
  refine worldEff_seq hnt12 hcr12
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff10 8 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ howit_m9))
    (fun m10 _ heff11 hnt13 hcr13 => ?_)
  refine worldEff_seq hnt13 hcr13
    (fun hnt_a hcr_a => worldEff_call0_ro heff11 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m11 _ heff12 hnt14 hcr14 => ?_)
  refine worldEff_dec heff12 _ _ _ hnt14 hcr14 (fun _ _ _ hnt15 hcr15 => ?_)
  refine worldEff_seq hnt15 hcr15
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff12.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m12 _ heff13 hnt16 hcr16 => ?_)
  refine worldEff_dec heff13 _ _ _ hnt16 hcr16 (fun v_np _ _ hnt17 hcr17 => ?_)
  let m12_np := setVarHOLFinite (ofString "np") v_np m12
  refine worldEff_decCall_eff (heff13.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff13.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_pl cpost_pl _ _ _ hsh_pl heff14 hnt18 hcr18 => ?_) hnt17 hcr17
  obtain ⟨w_opl, rfl⟩ := val_word_of_shapeEq_one hsh_pl
  refine worldEff_decCall_eff (heff14.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff14.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_vh cpost_vh _ _ _ hsh_vh heff15 hnt19 hcr19 => ?_) hnt18 hcr18
  obtain ⟨w_ovh, rfl⟩ := val_word_of_shapeEq_one hsh_vh
  refine worldEff_decCall_eff (heff15.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff15.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_rq cpost_rq _ _ _ hsh_rq heff16 hnt20 hcr20 => ?_) hnt19 hcr19
  obtain ⟨w_orq, rfl⟩ := val_word_of_shapeEq_one hsh_rq
  have hopl_0 : (setVarHOLFinite (ofString "o_rq") (.val (.word w_orq))
      { cpost_rq with locals := (setVarHOLFinite (ofString "o_vh") (.val (.word w_ovh))
        { cpost_vh with locals := (setVarHOLFinite (ofString "o_pl") (.val (.word w_opl))
          { cpost_pl with locals := m12_np.locals }).locals }).locals }).locals.lookup (ofString "o_pl") =
      some (.val (.word w_opl)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    change (setVarHOLFinite (ofString "o_vh") _ _).locals.lookup _ = _
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hovh_0 : (setVarHOLFinite (ofString "o_rq") (.val (.word w_orq))
      { cpost_rq with locals := (setVarHOLFinite (ofString "o_vh") (.val (.word w_ovh))
        { cpost_vh with locals := (setVarHOLFinite (ofString "o_pl") (.val (.word w_opl))
          { cpost_pl with locals := m12_np.locals }).locals }).locals }).locals.lookup (ofString "o_vh") =
      some (.val (.word w_ovh)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have horq_0 : (setVarHOLFinite (ofString "o_rq") (.val (.word w_orq))
      { cpost_rq with locals := (setVarHOLFinite (ofString "o_vh") (.val (.word w_ovh))
        { cpost_vh with locals := (setVarHOLFinite (ofString "o_pl") (.val (.word w_opl))
          { cpost_pl with locals := m12_np.locals }).locals }).locals }).locals.lookup (ofString "o_rq") =
      some (.val (.word w_orq)) :=
    lookup_setVar_eq _ _ _
  refine worldEff_seq hnt20 hcr20
    (fun _ _ => worldEff_store_ssz_offs_const hWOK (heff16.locals_clock _ _) 0 (by decide) _ _ (Or.inl ⟨rfl, rfl⟩)
      (eval_local_word _ _ _ hopl_0))
    (fun m20 hm20 heff17 hnt21 hcr21 => ?_)
  have hm20_loc := store_keeps_locals _ _ _ _ hm20
  have hovh_1 : m20.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by
    rw [hm20_loc]; exact hovh_0
  have horq_1 : m20.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by
    rw [hm20_loc]; exact horq_0
  refine worldEff_seq hnt21 hcr21
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff17 8 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ hovh_1))
    (fun m21 hm21 heff18 hnt22 hcr22 => ?_)
  have hm21_loc := store_keeps_locals _ _ _ _ hm21
  have horq_2 : m21.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by
    rw [hm21_loc]; exact horq_1
  refine worldEff_seq hnt22 hcr22
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff18 16 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ horq_2))
    (fun m22 _ heff19 hnt23 hcr23 => ?_)
  refine worldEff_seq hnt23 hcr23
    (fun hnt_a hcr_a => worldEff_call0_ro heff19 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m23 _ heff20 hnt24 hcr24 => ?_)
  refine worldEff_dec heff20 _ _ _ hnt24 hcr24 (fun _ _ _ hnt25 hcr25 => ?_)
  refine worldEff_seq hnt25 hcr25
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff20.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m24 _ heff21 hnt26 hcr26 => ?_)
  refine worldEff_dec heff21 _ _ _ hnt26 hcr26 (fun v_pld _ _ hnt27 hcr27 => ?_)
  let m24_pld := setVarHOLFinite (ofString "payload") v_pld m24
  refine worldEff_decCall_eff (heff21.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff21.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_ex cpost_ex _ _ _ hsh_ex heff22 hnt28 hcr28 => ?_) hnt27 hcr27
  obtain ⟨w_oex, rfl⟩ := val_word_of_shapeEq_one hsh_ex
  refine worldEff_decCall_eff (heff22.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff22.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_tx cpost_tx _ _ _ hsh_tx heff23 hnt29 hcr29 => ?_) hnt28 hcr28
  obtain ⟨w_otx, rfl⟩ := val_word_of_shapeEq_one hsh_tx
  refine worldEff_decCall_eff (heff23.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff23.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_wd cpost_wd _ _ _ hsh_wd heff24 hnt30 hcr30 => ?_) hnt29 hcr29
  obtain ⟨w_owd, rfl⟩ := val_word_of_shapeEq_one hsh_wd
  refine worldEff_decCall_eff (heff24.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff24.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_bl cpost_bl _ _ _ hsh_bl heff25 hnt31 hcr31 => ?_) hnt30 hcr30
  obtain ⟨w_obl, rfl⟩ := val_word_of_shapeEq_one hsh_bl
  have hoex_0 : (setVarHOLFinite (ofString "o_bal") (.val (.word w_obl))
      { cpost_bl with locals := (setVarHOLFinite (ofString "o_wd") (.val (.word w_owd))
        { cpost_wd with locals := (setVarHOLFinite (ofString "o_txs") (.val (.word w_otx))
          { cpost_tx with locals := (setVarHOLFinite (ofString "o_extra") (.val (.word w_oex))
            { cpost_ex with locals := m24_pld.locals }).locals }).locals }).locals }).locals.lookup (ofString "o_extra") =
      some (.val (.word w_oex)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    change (setVarHOLFinite (ofString "o_wd") _ _).locals.lookup _ = _
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    change (setVarHOLFinite (ofString "o_txs") _ _).locals.lookup _ = _
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hotx_0 : (setVarHOLFinite (ofString "o_bal") (.val (.word w_obl))
      { cpost_bl with locals := (setVarHOLFinite (ofString "o_wd") (.val (.word w_owd))
        { cpost_wd with locals := (setVarHOLFinite (ofString "o_txs") (.val (.word w_otx))
          { cpost_tx with locals := (setVarHOLFinite (ofString "o_extra") (.val (.word w_oex))
            { cpost_ex with locals := m24_pld.locals }).locals }).locals }).locals }).locals.lookup (ofString "o_txs") =
      some (.val (.word w_otx)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    change (setVarHOLFinite (ofString "o_wd") _ _).locals.lookup _ = _
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have howd_0 : (setVarHOLFinite (ofString "o_bal") (.val (.word w_obl))
      { cpost_bl with locals := (setVarHOLFinite (ofString "o_wd") (.val (.word w_owd))
        { cpost_wd with locals := (setVarHOLFinite (ofString "o_txs") (.val (.word w_otx))
          { cpost_tx with locals := (setVarHOLFinite (ofString "o_extra") (.val (.word w_oex))
            { cpost_ex with locals := m24_pld.locals }).locals }).locals }).locals }).locals.lookup (ofString "o_wd") =
      some (.val (.word w_owd)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hobl_0 : (setVarHOLFinite (ofString "o_bal") (.val (.word w_obl))
      { cpost_bl with locals := (setVarHOLFinite (ofString "o_wd") (.val (.word w_owd))
        { cpost_wd with locals := (setVarHOLFinite (ofString "o_txs") (.val (.word w_otx))
          { cpost_tx with locals := (setVarHOLFinite (ofString "o_extra") (.val (.word w_oex))
            { cpost_ex with locals := m24_pld.locals }).locals }).locals }).locals }).locals.lookup (ofString "o_bal") =
      some (.val (.word w_obl)) :=
    lookup_setVar_eq _ _ _
  refine worldEff_seq hnt31 hcr31
    (fun _ _ => worldEff_store_ssz_offs_const hWOK (heff25.locals_clock _ _) 0 (by decide) _ _ (Or.inl ⟨rfl, rfl⟩)
      (eval_local_word _ _ _ hoex_0))
    (fun m31 hm31 heff26 hnt32 hcr32 => ?_)
  have hm31_loc := store_keeps_locals _ _ _ _ hm31
  have hotx_1 : m31.locals.lookup (ofString "o_txs") = some (.val (.word w_otx)) := by
    rw [hm31_loc]; exact hotx_0
  have howd_1 : m31.locals.lookup (ofString "o_wd") = some (.val (.word w_owd)) := by
    rw [hm31_loc]; exact howd_0
  have hobl_1 : m31.locals.lookup (ofString "o_bal") = some (.val (.word w_obl)) := by
    rw [hm31_loc]; exact hobl_0
  refine worldEff_seq hnt32 hcr32
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff26 8 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ hotx_1))
    (fun m32 hm32 heff27 hnt33 hcr33 => ?_)
  have hm32_loc := store_keeps_locals _ _ _ _ hm32
  have howd_2 : m32.locals.lookup (ofString "o_wd") = some (.val (.word w_owd)) := by
    rw [hm32_loc]; exact howd_1
  have hobl_2 : m32.locals.lookup (ofString "o_bal") = some (.val (.word w_obl)) := by
    rw [hm32_loc]; exact hobl_1
  refine worldEff_seq hnt33 hcr33
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff27 16 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ howd_2))
    (fun m33 hm33 heff28 hnt34 hcr34 => ?_)
  have hm33_loc := store_keeps_locals _ _ _ _ hm33
  have hobl_3 : m33.locals.lookup (ofString "o_bal") = some (.val (.word w_obl)) := by
    rw [hm33_loc]; exact hobl_2
  refine worldEff_seq hnt34 hcr34
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff28 24 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ hobl_3))
    (fun m34 _ heff29 hnt35 hcr35 => ?_)
  refine worldEff_seq hnt35 hcr35
    (fun hnt_a hcr_a => worldEff_call0_ro heff29 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m35 _ heff30 _ _ => worldEff_return heff30 _)

theorem lookup_input_blob :
    originalRuntimeCode.lookup (ofString "input_blob") =
      some ([], sourceFnBody Guest.Software.guestFn_input_blob, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 29 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_input_blob) rfl

theorem lookup_ssz_split_var_list :
    originalRuntimeCode.lookup (ofString "ssz_split_var_list") =
      some ([(ofString "p", .one), (ofString "len", .one), (ofString "lim", .one)],
        sourceFnBody Guest.Software.guestFn_ssz_split_var_list, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 202 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ssz_split_var_list) rfl

theorem lookup_decode_payload :
    originalRuntimeCode.lookup (ofString "decode_payload") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_decode_payload, .one) :=
  lookup_of_guestAst_getElem 204 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_payload) rfl

theorem lookup_decode_requests :
    originalRuntimeCode.lookup (ofString "decode_requests") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_decode_requests, .one) :=
  lookup_of_guestAst_getElem 205 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_requests) rfl

theorem lookup_decode_bytes_list :
    originalRuntimeCode.lookup (ofString "decode_bytes_list") =
      some ([(ofString "p", .one), (ofString "len", .one), (ofString "lim", .one), (ofString "maxb", .one)],
        sourceFnBody Guest.Software.guestFn_decode_bytes_list, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 206 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_bytes_list) rfl

theorem lookup_decode_stateless_input :
    originalRuntimeCode.lookup (ofString "decode_stateless_input") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_decode_stateless_input, .one) :=
  lookup_of_guestAst_getElem 207 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_stateless_input) rfl

theorem lookup_decode_host_input :
    originalRuntimeCode.lookup (ofString "decode_host_input") =
      some ([], sourceFnBody Guest.Software.guestFn_decode_host_input, .one) :=
  lookup_of_guestAst_getElem 200 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_host_input) rfl

theorem worldEff_while_cond_dhi {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (cond : ExpHOL 64) {body : ProgHOL 64}
    (Inv : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, Inv t → Inv (decClockHOLFinite t))
    (hb : ∀ t (cw : BitVec 64),
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s (decClockHOLFinite t) Rl B gw → Inv (decClockHOLFinite t) →
      (evaluateHOLFiniteState (decClockHOLFinite t) body).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite t) body).1 →
      WorldEff s (evaluateHOLFiniteState (decClockHOLFinite t) body).2 Rl B gw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite t) body).1 = some .continue) →
        Inv (evaluateHOLFiniteState (decClockHOLFinite t) body).2)) :
    ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F), cur.clock = k →
      WorldEff s cur Rl B gw → Inv cur →
      (evaluateHOLFiniteState cur (.while cond body)).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur (.while cond body)).1 →
      WorldEff s (evaluateHOLFiniteState cur (.while cond body)).2 Rl B gw := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro cur hclk heff hinv hnt hcr
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hcr ⊢
    rcases hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
    · exact heff
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try exact heff
      rw [hc] at hnt hcr; dsimp only at hnt hcr ⊢
      by_cases hw0 : cw = 0
      · subst hw0; simp; exact heff
      · rw [if_pos hw0] at hnt hcr ⊢
        by_cases hk0 : cur.clock = 0
        · rw [if_pos hk0] at hnt; exact absurd rfl hnt
        · rw [if_neg hk0] at hnt hcr ⊢
          have heff_d : WorldEff s (decClockHOLFinite cur) Rl B gw := heff.locals_clock cur.locals (cur.clock - 1)
          have hinv_d : Inv (decClockHOLFinite cur) := hdec cur hinv
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) body
          rcases hbo : evaluateHOLFiniteState (decClockHOLFinite cur) body with ⟨rb, sb⟩
          simp only [hbo] at hnt hcr hrem ⊢
          have hlt : sb.clock < k := by
            change sb.clock ≤ cur.clock - 1 at hrem; omega
          cases rb with
          | none =>
            obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
              (by rw [hbo]; simp) (by rw [hbo]; exact Or.inl rfl)
            rw [hbo] at heff_b hinv_b
            exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inl rfl)) hnt hcr
          | some r1 =>
            cases r1 with
            | «continue» =>
              obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hbo] at heff_b hinv_b
              exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inr rfl)) hnt hcr
            | «break» =>
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inl rfl))
              rw [hbo] at heff_b; exact heff_b
            | timeOut => exact absurd rfl hnt
            | returned v =>
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hbo] at heff_b; exact heff_b
            | exception eid ev =>
              have hres_e : InitECandidate.Solver.Wave8GuestInv.Resumes (some (.exception eid ev)) := by
                rcases hcr with h | h | h | hr <;> [cases h; cases h; cases h; exact hr]
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr hres_e)))
              rw [hbo] at heff_b; exact heff_b
            | error =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h
            | finalFfi _ =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h

theorem flowing_of_none_or_continue {r : Option (PanSemResultExact 64)}
    (h : r = none ∨ r = some .continue) : Flowing r := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem worldEff_input_blob_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s entry Rl B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob)).2 Rl B dhiGw := by
  dsimp only [Guest.Software.guestFn_input_blob, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_dec heff _ _ _ hnt hcr (fun _ _ _ hnt1 hcr1 => ?_)
  refine worldEff_seq hnt1 hcr1
    (fun _ _ => worldEff_shMemLoad_local (heff.locals_clock _ _) _ _ _)
    (fun m1 _ heff1 hnt2 hcr2 => ?_)
  refine worldEff_seq hnt2 hcr2
    (fun hnt_a hcr_a => worldEff_ite heff1 _ hnt_a hcr_a
      (fun _ _ _ hnt_y hcr_y => worldEff_call_trap_with heff1 _ hnt_y hcr_y)
      (fun _ _ _ => worldEff_skip heff1))
    (fun m2 hm2 heff2 hnt3 hcr3 => ?_)
  obtain ⟨hm2_eq, hcond_le⟩ := ite_trap_with_keeps m1 m2 heff1.code _ _ hm2
  have hlen_m1 : ∃ wlen : BitVec 64,
      m1.locals.lookup (ofString "len") = some (.val (.word wlen)) ∧ wlen.toNat ≤ 1073741808 := by
    simp only [evalHOLExact, evalListHOLExact, toExact] at hcond_le
    rcases hl : m1.locals.lookup (ofString "len") with _ | lv
    · simp [hl] at hcond_le
    · rcases lv with ⟨⟨wlen⟩⟩ | _ | _ <;>
        simp [hl, Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond_le
      refine ⟨wlen, rfl, ?_⟩
      exact BitVec.le_def.1 hcond_le
  obtain ⟨wlen, hwlen_m1, hwlen_le⟩ := hlen_m1
  have hwlen_m2 : m2.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm2_eq]; exact hwlen_m1
  refine worldEff_decCall_alloc heff2 (by decide) (ofString "p") _ hnt3 hcr3
    (fun pw nw m3 hsz_ev _ hm3_loc _ heff3 _ _ hpw_lo hpw_add hhp3_hi _ hnt4 hcr4 => ?_)
  have hnw_eq : nw = wlen + 8#64 := by
    simp [evalHOLExact, evalListHOLExact, toExact, hwlen_m2, wordOpHOL, wordOp, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have hnw_nat : (wlen + 8#64).toNat = wlen.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt]; · rfl
    · change wlen.toNat + 8 < 2 ^ 64; omega
  have hpw_hi : pw.toNat + wlen.toNat + 8 ≤ heapLimit := by omega
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  refine worldEff_dec heff3 _ _ _ hnt4 hcr4 (fun vi hvi _ hnt5 hcr5 => ?_)
  have hvi0 : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi0
  refine worldEff_dec (heff3.locals_clock _ _) _ _ _ hnt5 hcr5 (fun vw hvw _ hnt6 hcr6 => ?_)
  have hvw0 : vw = .val (.word 0#64) := by simp [evalHOLExact] at hvw; exact hvw.symm
  subst hvw0
  let m5 := setVarHOLFinite (ofString "w") (.val (.word 0#64)) (setVarHOLFinite (ofString "i") (.val (.word 0#64)) m3)
  let InvIb : PanSemStateFiniteExact 64 F → Prop := fun t =>
    t.locals.lookup (ofString "p") = some (.val (.word pw)) ∧
    t.locals.lookup (ofString "len") = some (.val (.word wlen)) ∧
    (∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi))) ∧
    (∃ ww : BitVec 64, t.locals.lookup (ofString "w") = some (.val (.word ww)))
  have hinv_m5 : InvIb m5 := by
    refine ⟨?_, ?_, ⟨0#64, ?_⟩, ⟨0#64, lookup_setVar_eq _ _ _⟩⟩
    · dsimp only [m5]
      rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), hm3_loc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE]
    · dsimp only [m5]
      rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), hm3_loc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, hwlen_m2,
        show ofString "p" ≠ ofString "len" by decide]
    · dsimp only [m5]
      rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
  refine worldEff_seq hnt6 hcr6
    (fun hnt_w hcr_w =>
      worldEff_while_cond_dhi _ InvIb (fun _ h => h)
        (fun t0 cw hcond hnz heff_t ⟨ht_p, ht_len, ⟨wi, ht_i⟩, ⟨ww, ht_w⟩⟩ hnt_b hcr_b => ?_)
        m5.clock m5 rfl (heff3.locals_clock _ _) hinv_m5 hnt_w hcr_w)
    (fun m6 _ heff6 _ _ => worldEff_return heff6 _)
  have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
  have ht0_len : t0.locals.lookup (ofString "len") = some (.val (.word wlen)) := ht_len
  have hwi_lt : wi.toNat < wlen.toNat := by
    rw [evalHOLFinite_eq_toExact] at hcond
    simp [evalHOLExact, evalListHOLExact, toExact, ht0_i, ht0_len,
      Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond
    by_contra hge
    have hnlt : ¬(wi < wlen) := by simp [BitVec.lt_def]; omega
    simp [hnlt] at hcond
    exact hnz hcond.symm
  refine ⟨?_, fun hf => ?_⟩
  · refine worldEff_seq hnt_b hcr_b
      (fun _ _ => worldEff_shMemLoad_local heff_t _ _ _)
      (fun u1 hu1 heff_u1 hnt_s hcr_s => ?_)
    obtain ⟨ww', hu1_eq⟩ := shMemLoad_local_none_inv (decClockHOLFinite t0) .opW (ofString "w") _ hu1
    have hu1_p : u1.locals.lookup (ofString "p") = some (.val (.word pw)) := by
      rw [hu1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht_p,
        show ofString "w" ≠ ofString "p" by decide]
    have hu1_i : u1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
      rw [hu1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht_i,
        show ofString "w" ≠ ofString "i" by decide]
    have hu1_w : u1.locals.lookup (ofString "w") = some (.val (.word ww')) := by
      rw [hu1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_seq hnt_s hcr_s
      (fun _ _ => worldEff_store_word heff_u1 _ _
        (eval_local_word _ _ _ hu1_w)
        (fun x hx _ => ?_))
      (fun u2 _ heff_u2 _ _ => worldEff_assign_local heff_u2 _ _)
    simp [evalHOLExact, evalListHOLExact, toExact, hu1_p, hu1_i, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
    subst hx
    have hx_nat : (pw + wi).toNat = pw.toNat + wi.toNat := by
      rw [BitVec.toNat_add_of_lt]; omega
    exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
  · have hfl := flowing_of_none_or_continue hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [evaluate_keepLocal (ofString "p") _ (by decide) _ hfl]; exact ht_p
    · rw [evaluate_keepLocal (ofString "len") _ (by decide) _ hfl]; exact ht_len
    · exact evaluate_wordLocal (ofString "i") _ (by decide) _ ⟨wi, ht_i⟩ hfl
    · exact evaluate_wordLocal (ofString "w") _ (by decide) _ ⟨ww, ht_w⟩ hfl

theorem eval_op_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (h_op : ∃ bop args, e = .op bop args) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  obtain ⟨bop, args, rfl⟩ := h_op
  intro v hv
  simp only [evalHOLExact] at hv
  split at hv
  · split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  · cases hv

theorem eval_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one e) = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | ve
  · simp [evalHOLExact, isWfShapeExactHOL, he] at hv
  · cases ve with
    | val wl =>
      cases wl with
      | word a =>
        cases hm : s.memory a with
        | word w =>
          by_cases hd : s.memaddrs a
          · simp [evalHOLExact, isWfShapeExactHOL, he, memLoadHOLExact, hd, hm] at hv
            exact ⟨w, hv.symm⟩
          · simp [evalHOLExact, isWfShapeExactHOL, he, memLoadHOLExact, hd] at hv
    | _ =>
      simp [evalHOLExact, isWfShapeExactHOL, he] at hv

theorem eval_rfield_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (idx : Nat) (name : MlS) (w0 w1 : BitVec 64)
    (hl : s.locals.lookup name = some (.rStruct [.val (.word w0), .val (.word w1)]))
    (hidx : idx = 0 ∨ idx = 1) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.rfield idx (.var .local name)) = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  rcases hidx with rfl | rfl <;>
  · simp [evalHOLExact, toExact, hl] at hv
    exact ⟨_, hv.symm⟩

theorem eval_loadByte_lt_256 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.loadByte e) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 256 := by
  simp only [evalHOLExact] at hv
  split at hv
  · rename_i a ha
    dsimp only [panMemLoadByteHOL] at hv
    split at hv
    · simp only [Option.map_some, Option.some.injEq] at hv
      subst hv
      refine ⟨_, rfl, ?_⟩
      rw [BitVec.toNat_ofNat]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (UInt8.toNat_lt _)
    · simp at hv
  · simp at hv

theorem eval_or4_bytes_lt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (l0 l1 l2 l3 : ExpHOL 64) (v : ValueHOL 64)
    (h0 : ∀ v0, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l0 = some v0 →
      ∃ w0 : BitVec 64, v0 = .val (.word w0) ∧ w0.toNat < 256)
    (h1 : ∀ v1, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l1 = some v1 →
      ∃ w1 : BitVec 64, v1 = .val (.word w1) ∧ w1.toNat < 256)
    (h2 : ∀ v2, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l2 = some v2 →
      ∃ w2 : BitVec 64, v2 = .val (.word w2) ∧ w2.toNat < 256)
    (h3 : ∀ v3, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l3 = some v3 →
      ∃ w3 : BitVec 64, v3 = .val (.word w3) ∧ w3.toNat < 256)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .or [l0, .shift .lsl l1 (.const 8#64), .shift .lsl l2 (.const 16#64), .shift .lsl l3 (.const 24#64)]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 32 := by
  rcases hb0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l0 with _ | v0
  · simp [evalHOLExact, evalListHOLExact, hb0] at hv
  rcases hb1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l1 with _ | v1
  · simp [evalHOLExact, evalListHOLExact, hb0, hb1] at hv
  rcases hb2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l2 with _ | v2
  · simp [evalHOLExact, evalListHOLExact, hb0, hb1, hb2] at hv
  rcases hb3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l3 with _ | v3
  · simp [evalHOLExact, evalListHOLExact, hb0, hb1, hb2, hb3] at hv
  obtain ⟨w0, rfl, hw0⟩ := h0 v0 hb0
  obtain ⟨w1, rfl, hw1⟩ := h1 v1 hb1
  obtain ⟨w2, rfl, hw2⟩ := h2 v2 hb2
  obtain ⟨w3, rfl, hw3⟩ := h3 v3 hb3
  simp [evalHOLExact, evalListHOLExact, hb0, hb1, hb2, hb3, wordShiftHOL, wordOpHOL, wordOp,
    valueIsWord, valueWord] at hv
  subst hv
  refine ⟨_, rfl, ?_⟩
  have hsh_lt : ∀ (x : BitVec 64) (s m : Nat),
      x.toNat < 256 → s ≤ 24 → 256 * 2 ^ s ≤ 2 ^ m → m ≤ 32 →
      (x <<< s).toNat < 2 ^ m := by
    intro x s m hx hs hsm hm32
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have h1 : x.toNat * 2 ^ s < 256 * 2 ^ s := Nat.mul_lt_mul_of_pos_right hx (by positivity)
    have h2 : 2 ^ m ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hm32
    have h3 : 2 ^ 32 < 2 ^ 64 := by decide
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hor_lt : ∀ (u v : BitVec 64) (m : Nat),
      u.toNat < 2 ^ m → v.toNat < 2 ^ m → (u ||| v).toNat < 2 ^ m := by
    intro u v m hu hv
    rw [BitVec.toNat_or]
    exact Nat.or_lt_two_pow hu hv
  change (w0 ||| ((w1 <<< 8) ||| ((w2 <<< 16) ||| ((w3 <<< 24) ||| 0#64)))).toNat < 2 ^ 32
  rw [BitVec.or_zero]
  exact hor_lt w0 _ 32 (by omega)
    (hor_lt (w1 <<< 8) _ 32 (hsh_lt w1 8 32 hw1 (by omega) (by decide) (by omega))
      (hor_lt (w2 <<< 16) (w3 <<< 24) 32
        (hsh_lt w2 16 32 hw2 (by omega) (by decide) (by omega))
        (hsh_lt w3 24 32 hw3 (by omega) (by decide) (by omega))))

theorem eval_le32_word_lt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e0 e1 e2 e3 : ExpHOL 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .or [.loadByte e0,
                .shift .lsl (.loadByte e1) (.const 8#64),
                .shift .lsl (.loadByte e2) (.const 16#64),
                .shift .lsl (.loadByte e3) (.const 24#64)]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 32 :=
  eval_or4_bytes_lt s _ _ _ _ v
    (eval_loadByte_lt_256 s e0)
    (eval_loadByte_lt_256 s e1)
    (eval_loadByte_lt_256 s e2)
    (eval_loadByte_lt_256 s e3)
    hv

theorem worldEff_store_fresh_const {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s cur Rl B dhiGw)
    (bname : MlS) (bw : BitVec 64) (sz off : Nat)
    (hb : cur.locals.lookup bname = some (.val (.word bw)))
    (hlo : globN s "heap_ptr" ≤ bw.toNat)
    (hhi : bw.toNat + sz ≤ heapLimit)
    (hoff : off + 8 ≤ sz)
    (valExp : ExpHOL 64)
    (hword : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w)) :
    WorldEff s
      (evaluateHOLFiniteState cur (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) valExp)).2
      Rl B dhiGw := by
  have hhl : heapLimit < 2 ^ 64 := by decide
  refine worldEff_store_word heff _ valExp hword (fun x hx _ => ?_)
  simp [evalHOLExact, evalListHOLExact, toExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
  subst hx
  have hoff_nat : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx_nat : (bw + BitVec.ofNat 64 off).toNat = bw.toNat + off := by
    rw [BitVec.toNat_add_of_lt] <;> omega
  exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))

def hasIncTail (x : MlS) : ProgHOL 64 → Bool
  | .assign .local nm (.op .add [.var .local nm', .const c]) =>
    decide (nm = x ∧ nm' = x ∧ c = 1#64)
  | .seq a b => noLocalAssign x a && hasIncTail x b
  | .dec nm _ _ b => decide (x ≠ nm) && hasIncTail x b
  | _ => false

theorem evaluate_incTail_le {F : Type} (x : MlS) (bound : Nat) (hbound : bound < 2 ^ 64)
    (p : ProgHOL 64) (hinc : hasIncTail x p = true) :
    ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      st.locals.lookup x = some (.val (.word wi)) →
      wi.toNat < bound →
      ((evaluateHOLFiniteState st p).1 = none ∨ (evaluateHOLFiniteState st p).1 = some .continue) →
      ∃ wi' : BitVec 64,
        (evaluateHOLFiniteState st p).2.locals.lookup x = some (.val (.word wi')) ∧
        wi'.toNat ≤ bound := by
  match hp_eq : p with
  | .assign vk nm rhs =>
    cases vk with
    | global => simp [hasIncTail] at hinc
    | «local» =>
      cases rhs with
      | op bop args =>
        cases bop <;> try simp [hasIncTail] at hinc
        rcases args with _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩ <;> try simp [hasIncTail] at hinc
        cases a1 with
        | var vk1 nm' =>
          cases vk1 <;> try simp [hasIncTail] at hinc
          cases a2 with
          | const c =>
            simp only [hasIncTail, decide_eq_true_eq] at hinc
            obtain ⟨rfl, rfl, rfl⟩ := hinc
            intro st wi hst hlt hf
            rw [evaluateHOLFiniteState_assign]
            simp only [evalHOLExact, evalListHOLExact, toExact, hst, wordOpHOL, wordOp, valueIsWord, valueWord,
              Option.map_some, List.all_cons, List.all_nil, Bool.and_self, ↓reduceIte,
              List.map, List.foldr, BitVec.add_zero] at hf ⊢
            split_ifs at hf ⊢ with hv
            · refine ⟨wi + 1#64, ?_, ?_⟩
              · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
                omega
            · exact ⟨wi, hst, by omega⟩
          | _ => simp [hasIncTail] at hinc
        | _ => simp [hasIncTail] at hinc
      | _ => simp [hasIncTail] at hinc
  | .seq a b =>
    simp only [hasIncTail, Bool.and_eq_true] at hinc
    intro st wi hst hlt hf
    rw [evaluateHOLFiniteState_seq_line780] at hf ⊢
    rcases ha : evaluateHOLFiniteState st a with ⟨ra, mid⟩
    rw [ha] at hf
    cases ra with
    | none =>
      dsimp only at hf ⊢
      have hmid : mid.locals.lookup x = some (.val (.word wi)) := by
        have hk := evaluate_keepLocal x a hinc.1 st (Or.inl (by rw [ha]))
        rw [ha] at hk; rw [hk]; exact hst
      exact evaluate_incTail_le x bound hbound b hinc.2 mid wi hmid hlt hf
    | some r1 =>
      rcases hf with h | h
      · simp at h
      · injection h with h'; subst h'
        dsimp only
        have hmid : mid.locals.lookup x = some (.val (.word wi)) := by
          have hk := evaluate_keepLocal x a hinc.1 st (Or.inr (Or.inr (by rw [ha])))
          rw [ha] at hk; rw [hk]; exact hst
        exact ⟨wi, hmid, by omega⟩
  | .dec nm sh rhs b =>
    simp only [hasIncTail, Bool.and_eq_true, decide_eq_true_eq] at hinc
    intro st wi hst hlt hf
    revert hf; rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · intro hf; rcases hf with h | h <;> simp at h
    · split
      · rename_i v _ _
        intro hf
        have hset : (setVarHOLFinite nm v st).locals.lookup x = some (.val (.word wi)) := by
          rw [lookup_setVar_ne _ _ _ _ hinc.1]; exact hst
        obtain ⟨wi', hwi', hle'⟩ := evaluate_incTail_le x bound hbound b hinc.2 (setVarHOLFinite nm v st) wi hset hlt hf
        refine ⟨wi', ?_, hle'⟩
        dsimp only
        rw [resVarEq_lookup_local, if_neg hinc.1, hwi']
      · intro hf; rcases hf with h | h <;> simp at h
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _
  | .store _ _ | .storeByte _ _ | .ite _ _ _ | .while _ _ | .decCall _ _ _ _ _
  | .call _ _ _ | .shMemLoad _ _ _ _ | .shMemStore _ _ _ | .extCall _ _ _ _ _ =>
    simp [hasIncTail] at hinc
termination_by sizeOf p
decreasing_by
  all_goals
    subst hp_eq
    decreasing_tactic

theorem shape_two_words_dhi (v : ValueHOL 64)
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one]) = true) :
    ∃ a b : BitVec 64,
      v = .rStruct [.val (.word a), .val (.word b)] := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at h
  · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h)
    rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    exact ⟨a, b, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL] at h

theorem contOrRes_of_resumes_dhi {r : Option (PanSemResultExact 64)}
    (h : InitECandidate.Solver.Wave8GuestInv.Resumes r) : ContOrRes r :=
  Or.inr (Or.inr (Or.inr h))

theorem worldEff_decCall_alloc_const {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s cur Rl B dhiGw)
    (name : MlS) (sz : Nat) (hsz8 : (sz + 7) / 8 * 8 = sz) (hsz_lt : sz < 2 ^ 64)
    {cont : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.decCall name .one (ofString "alloc") [.const (BitVec.ofNat 64 sz)] cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.decCall name .one (ofString "alloc") [.const (BitVec.ofNat 64 sz)] cont)).1)
    (hcont : ∀ (pw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      mid.locals = cur.locals.update (name, .val (.word pw)) →
      WorldEff s mid Rl B dhiGw →
      pw.toNat % 8 = 0 →
      globN s "heap_ptr" ≤ pw.toNat →
      pw.toNat + sz ≤ heapLimit →
      WordsOK mid (pw.toNat, sz) →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B dhiGw) :
    WorldEff s (evaluateHOLFiniteState cur (.decCall name .one (ofString "alloc") [.const (BitVec.ofNat 64 sz)] cont)).2 Rl B dhiGw := by
  refine worldEff_decCall_alloc heff (by decide) name (.const (BitVec.ofNat 64 sz)) hnt hcr
    (fun pw nw mid hsz_ev _ hloc _ heff_m hal _ hlo hhp_eq hhp_hi hwok hnt_k hcr_k => ?_)
  have hnw : nw = BitVec.ofNat 64 sz := by
    simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hnw
  have hnw_nat : (BitVec.ofNat 64 sz).toNat = sz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz_lt]
  rw [hnw_nat, hsz8] at hhp_eq hwok
  exact hcont pw mid hloc heff_m hal hlo (by omega) hwok hnt_k hcr_k

theorem worldEff_seq_store_fresh {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s cur Rl B dhiGw)
    (bname : MlS) (bw : BitVec 64) (sz off : Nat)
    (hb : cur.locals.lookup bname = some (.val (.word bw)))
    (hlo : globN s "heap_ptr" ≤ bw.toNat)
    (hhi : bw.toNat + sz ≤ heapLimit)
    (hoff : off + 8 ≤ sz)
    (valExp : ExpHOL 64) {cont : ProgHOL 64}
    (hword : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hnt : (evaluateHOLFiniteState cur (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) valExp) cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) valExp) cont)).1)
    (hcont : ∀ mid, mid.locals = cur.locals → WorldEff s mid Rl B dhiGw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B dhiGw) :
    WorldEff s (evaluateHOLFiniteState cur (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) valExp) cont)).2 Rl B dhiGw :=
  worldEff_seq hnt hcr
    (fun _ _ => worldEff_store_fresh_const heff bname bw sz off hb hlo hhi hoff valExp hword)
    (fun mid hmid heff_m hnt_c hcr_c => hcont mid (store_keeps_locals cur mid _ valExp hmid) heff_m hnt_c hcr_c)

theorem worldEff_seq_store_ssz_offs_const {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s cur (dhiOffsRegions s) B dhiGw)
    (off : Nat) (hoff : off + 8 ≤ 64)
    (dst valExp : ExpHOL 64) {cont : ProgHOL 64}
    (hdst : (dst = .var .global (ofString "ssz_offs") ∧ off = 0) ∨
            dst = .op .add [.var .global (ofString "ssz_offs"), .const (BitVec.ofNat 64 off)])
    (hword : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hnt : (evaluateHOLFiniteState cur (.seq (.store dst valExp) cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.seq (.store dst valExp) cont)).1)
    (hcont : ∀ mid, mid.locals = cur.locals → WorldEff s mid (dhiOffsRegions s) B dhiGw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 (dhiOffsRegions s) B dhiGw) :
    WorldEff s (evaluateHOLFiniteState cur (.seq (.store dst valExp) cont)).2 (dhiOffsRegions s) B dhiGw :=
  worldEff_seq hnt hcr
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff off hoff dst valExp hdst hword)
    (fun mid hmid heff_m hnt_c hcr_c => hcont mid (store_keeps_locals cur mid dst valExp hmid) heff_m hnt_c hcr_c)

theorem worldEff_ssz_split_var_list_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s entry Rl B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list)).2 Rl B dhiGw := by
  dsimp only [Guest.Software.guestFn_ssz_split_var_list, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_seq hnt hcr
    (fun hnt_a hcr_a => worldEff_ite heff _ hnt_a hcr_a
      (fun _ _ _ _ _ => worldEff_return heff _)
      (fun _ _ _ => worldEff_skip heff))
    (fun m1 _ heff1 hnt1 hcr1 => ?_)
  refine worldEff_seq hnt1 hcr1
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff1 _ _ hnt_a hcr_a)
    (fun m2 _ heff2 hnt2 hcr2 => ?_)
  refine worldEff_dec heff2 _ _ _ hnt2 hcr2 (fun v_first hv_first _ hnt3 hcr3 => ?_)
  obtain ⟨w_first, rfl, hfirst_lt⟩ := eval_le32_word_lt m2 _ _ _ _ v_first hv_first
  let m3 := setVarHOLFinite (ofString "first") (.val (.word w_first)) m2
  refine worldEff_seq hnt3 hcr3
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff2.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m4 hm4 heff4 hnt4 hcr4 => ?_)
  obtain ⟨hm4_eq, hcond21⟩ := ite_ssz_fail_keeps m3 m4 heff2.code _ _ hm4
  have hm3_first : m3.locals.lookup (ofString "first") = some (.val (.word w_first)) :=
    lookup_setVar_eq _ _ _
  have hfirst_pos : 4 ≤ w_first.toNat := by
    dsimp only [evalHOLExact, evalListHOLExact, toExact] at hcond21
    rw [hm3_first] at hcond21
    rcases hl_len : m3.locals.lookup (ofString "len") with _ | lv_len
    · simp [hl_len] at hcond21
    · rcases lv_len with ⟨⟨w_len⟩⟩ | _ | _ <;>
        (try simp [hl_len, Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord] at hcond21; done)
      simp only [hl_len, Compiler.Encoders.Asm.wordCmpHOL,
        wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all_cons, List.all_nil, Bool.and_self, Option.map_some, ↓reduceIte,
        List.map, List.foldr,
        Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hcond21
      have hcond21' :
          (if (!0#64 == (if (w_first == 0#64) = true then 1#64 else 0#64) |||
              ((if (!w_first &&& (3#64 &&& ~~~0#64) == 0#64) = true then 1#64 else 0#64) |||
                ((if decide (w_len < w_first) = true then 1#64 else 0#64) ||| 0#64))) = true
            then 1#64 else 0#64) = 0#64 := hcond21
      have hne0 : w_first ≠ 0#64 := by
        intro hz; subst hz
        simp at hcond21'
      have hmod4 : w_first.toNat % 4 = 0 := by
        have hand3 : (3#64 &&& ~~~0#64 : BitVec 64) = 3#64 := rfl
        rw [hand3] at hcond21'
        by_cases hm : (w_first &&& 3#64) == 0#64
        · have hm' : w_first &&& 3#64 = 0#64 := eq_of_beq hm
          have hn := congrArg BitVec.toNat hm'
          rw [BitVec.toNat_and] at hn
          change w_first.toNat &&& (2 ^ 2 - 1) = 0 at hn
          rwa [Nat.and_two_pow_sub_one_eq_mod _ 2] at hn
        · exfalso
          simp [hm] at hcond21'
          revert hcond21'
          split <;> split <;> simp
      have hf_pos : 0 < w_first.toNat := by
        by_cases hp : w_first.toNat = 0
        · exact absurd (BitVec.eq_of_toNat_eq hp) hne0
        · omega
      omega
  have hm4_first : m4.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
    rw [hm4_eq]; exact hm3_first
  refine worldEff_dec heff4 _ _ _ hnt4 hcr4 (fun v_cnt hv_cnt _ hnt5 hcr5 => ?_)
  have hv_cnt_eq : v_cnt = .val (.word (w_first >>> 2)) := by
    simp [evalHOLExact, toExact, hm4_first, wordShiftHOL] at hv_cnt
    exact hv_cnt.symm
  subst hv_cnt_eq
  let w_cnt := w_first >>> 2
  have hw_cnt_nat : w_cnt.toNat = w_first.toNat / 4 := by
    dsimp only [w_cnt]
    change (w_first >>> (2 : Nat)).toNat = w_first.toNat / 4
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hcnt_pos : 1 ≤ w_cnt.toNat := by omega
  have hcnt_lt : w_cnt.toNat < 2 ^ 30 := by omega
  let m5 := setVarHOLFinite (ofString "count") (.val (.word w_cnt)) m4
  refine worldEff_seq hnt5 hcr5
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff4.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m6 hm6 heff6 hnt6 hcr6 => ?_)
  obtain ⟨hm6_eq, _⟩ := ite_ssz_fail_keeps m5 m6 heff4.code _ _ hm6
  have hm6_cnt : m6.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by
    rw [hm6_eq]; exact lookup_setVar_eq _ _ _
  have hm6_first : m6.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
    rw [hm6_eq]; dsimp only [m5]
    rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm4_first
  refine worldEff_decCall_alloc heff6 (by decide) (ofString "arr") _ hnt6 hcr6
    (fun w_arr nw m7 hsz_ev _ hm7_loc _ heff7 _ _ harr_lo harr_add hhp7_hi _ hnt7 hcr7 => ?_)
  have hnw_eq : nw = w_cnt * 16#64 := by
    simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hm6_cnt, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have hnw_nat : (w_cnt * 16#64).toNat = w_cnt.toNat * 16 := by
    rw [BitVec.toNat_mul, show (16#64 : BitVec 64).toNat = 16 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have harr_hi : w_arr.toNat + w_cnt.toNat * 16 ≤ heapLimit := by omega
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hm7_cnt : m7.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by
    rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_cnt,
      show ofString "arr" ≠ ofString "count" by decide]
  have hm7_first : m7.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
    rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_first,
      show ofString "arr" ≠ ofString "first" by decide]
  have hm7_arr : m7.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
    rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_dec heff7 _ _ _ hnt7 hcr7 (fun vi hvi _ hnt8 hcr8 => ?_)
  have hvi0 : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi0
  let m8 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m7
  have hm8_first : m8.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
    dsimp only [m8]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm7_first
  refine worldEff_dec (heff7.locals_clock _ _) _ _ _ hnt8 hcr8 (fun vprev hvprev _ hnt9 hcr9 => ?_)
  have hvprev_eq : vprev = .val (.word w_first) := by
    change @evalHOLExact 64 F _ m8.toExact (fun a => Classical.propDecidable (m8.memaddrs a)) _ = _ at hvprev
    simp [evalHOLExact, toExact, hm8_first] at hvprev; exact hvprev.symm
  subst hvprev_eq
  let m9 := setVarHOLFinite (ofString "prev") (.val (.word w_first)) m8
  let InvSp : PanSemStateFiniteExact 64 F → Prop := fun t =>
    t.locals.lookup (ofString "arr") = some (.val (.word w_arr)) ∧
    t.locals.lookup (ofString "count") = some (.val (.word w_cnt)) ∧
    ∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧ wi.toNat ≤ w_cnt.toNat
  have hinv_m9 : InvSp m9 := by
    refine ⟨?_, ?_, ⟨0#64, ?_, Nat.zero_le _⟩⟩
    · dsimp only [m9, m8]
      rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
      exact hm7_arr
    · dsimp only [m9, m8]
      rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
      exact hm7_cnt
    · dsimp only [m9, m8]
      rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
  refine worldEff_seq hnt9 hcr9
    (fun hnt_w hcr_w =>
      worldEff_while_cond_dhi _ InvSp (fun _ h => h)
        (fun t0 cw hcond hnz heff_t ⟨ht_arr, ht_cnt, wi, ht_i, hwi_le⟩ hnt_b hcr_b => ?_)
        m9.clock m9 rfl (heff7.locals_clock _ _) hinv_m9 hnt_w hcr_w)
    (fun m10 hm10 heff10 hnt10 hcr10 => ?_)
  · have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
    have ht0_cnt : t0.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := ht_cnt
    have h2_30_63 : (2 : Nat) ^ 30 < 2 ^ 63 := by decide
    have hwi_lt : wi.toNat < w_cnt.toNat := by
      rw [evalHOLFinite_eq_toExact] at hcond
      simp only [evalHOLExact, evalListHOLExact, toExact, ht0_i, ht0_cnt,
        Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small wi w_cnt (by omega) (by omega)] at hcond
      by_cases hlt : wi.toNat < w_cnt.toNat
      · exact hlt
      · simp [hlt] at hcond; exact absurd hcond.symm hnz
    refine ⟨?_, fun hf => ?_⟩
    · refine worldEff_dec heff_t _ _ _ hnt_b hcr_b (fun v_o hv_o _ hnt_s1 hcr_s1 => ?_)
      obtain ⟨w_o, rfl, _⟩ := eval_le32_word_lt (decClockHOLFinite t0) _ _ _ _ v_o hv_o
      let u0 := setVarHOLFinite (ofString "o") (.val (.word w_o)) (decClockHOLFinite t0)
      refine worldEff_seq hnt_s1 hcr_s1
        (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff_t.locals_clock _ _) _ _ hnt_a hcr_a)
        (fun u1 hu1 heff_u1 hnt_s2 hcr_s2 => ?_)
      obtain ⟨hu1_eq, _⟩ := ite_ssz_fail_keeps u0 u1 heff_t.code _ _ hu1
      have hu1_arr : u1.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_arr
      have hu1_i : u1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_i
      refine worldEff_seq hnt_s2 hcr_s2
        (fun hnt_a hcr_a => worldEff_ite heff_u1 _ hnt_a hcr_a
          (fun cw_gt hcond_gt hnz_gt _ _ => ?_)
          (fun _ _ _ => worldEff_skip heff_u1))
        (fun u2 hu2 heff_u2 hnt_s3 hcr_s3 => ?_)
      · have hwi_pos : 0 < wi.toNat := by
          simp only [evalHOLExact, evalListHOLExact, toExact, hu1_i,
            Compiler.Encoders.Asm.wordCmpHOL,
            holAsmSignedLess_small 0#64 wi (by decide) (by omega),
            show (0#64 : BitVec 64).toNat = 0 from rfl] at hcond_gt
          by_cases hp : 0 < wi.toNat
          · exact hp
          · simp [hp] at hcond_gt; exact absurd hcond_gt.symm hnz_gt
        refine worldEff_store_word heff_u1 _ _ (eval_op_word u1 _ ⟨_, _, rfl⟩) (fun x hx _ => ?_)
        simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hu1_arr, hu1_i,
          wordOpHOL, wordOp, valueIsWord, valueWord] at hx
        subst hx
        have hsub1 : (wi - 1#64).toNat = wi.toNat - 1 := by
          rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
          rfl
        have hmul16 : ((wi - 1#64) * 16#64).toNat = (wi.toNat - 1) * 16 := by
          rw [BitVec.toNat_mul, hsub1, show (16#64 : BitVec 64).toNat = 16 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have hadd_r : (((wi - 1#64) * 16#64) + 8#64).toNat = (wi.toNat - 1) * 16 + 8 := by
          rw [BitVec.toNat_add_of_lt]
          · rw [hmul16]; rfl
          · rw [hmul16]; change (wi.toNat - 1) * 16 + 8 < 2 ^ 64; omega
        have hx_nat : (w_arr + (((wi - 1#64) * 16#64) + 8#64)).toNat = w_arr.toNat + (wi.toNat - 1) * 16 + 8 := by
          rw [BitVec.toNat_add_of_lt] <;> omega
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
      · have hu2_arr : u2.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
          have hk := evaluate_keepLocal (ofString "arr") _ (by decide) u1 (Or.inl (congrArg Prod.fst hu2))
          rw [hu2] at hk; rw [hk]; exact hu1_arr
        have hu2_i : u2.locals.lookup (ofString "i") = some (.val (.word wi)) := by
          have hk := evaluate_keepLocal (ofString "i") _ (by decide) u1 (Or.inl (congrArg Prod.fst hu2))
          rw [hu2] at hk; rw [hk]; exact hu1_i
        refine worldEff_seq hnt_s3 hcr_s3
          (fun _ _ => worldEff_store_word heff_u2 _ _ (eval_op_word u2 _ ⟨_, _, rfl⟩) (fun x hx _ => ?_))
          (fun u3 _ heff_u3 hnt_s4 hcr_s4 =>
            worldEff_seq hnt_s4 hcr_s4
              (fun _ _ => worldEff_assign_local heff_u3 _ _)
              (fun u4 _ heff_u4 _ _ => worldEff_assign_local heff_u4 _ _))
        simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hu2_arr, hu2_i,
          wordOpHOL, wordOp, valueIsWord, valueWord] at hx
        subst hx
        have hmul16 : (wi * 16#64).toNat = wi.toNat * 16 := by
          rw [BitVec.toNat_mul, show (16#64 : BitVec 64).toNat = 16 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have hx_nat : (w_arr + (wi * 16#64)).toNat = w_arr.toNat + wi.toNat * 16 := by
          rw [BitVec.toNat_add_of_lt] <;> omega
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · have hfl := flowing_of_none_or_continue hf
      refine ⟨?_, ?_, ?_⟩
      · rw [evaluate_keepLocal (ofString "arr") _ (by decide) _ hfl]; exact ht_arr
      · rw [evaluate_keepLocal (ofString "count") _ (by decide) _ hfl]; exact ht_cnt
      · exact evaluate_incTail_le (ofString "i") w_cnt.toNat (by omega) _ (by decide)
          (decClockHOLFinite t0) wi ht_i hwi_lt hf
  · have hm10_arr : m10.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
      have hk := evaluate_keepLocal (ofString "arr") _ (by decide) _ (Or.inl (congrArg Prod.fst hm10))
      rw [hm10] at hk; rw [hk]; exact hinv_m9.1
    have hm10_cnt : m10.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by
      have hk := evaluate_keepLocal (ofString "count") _ (by decide) _ (Or.inl (congrArg Prod.fst hm10))
      rw [hm10] at hk; rw [hk]; exact hinv_m9.2.1
    refine worldEff_seq hnt10 hcr10
      (fun _ _ => worldEff_store_word heff10 _ _ (eval_op_word m10 _ ⟨_, _, rfl⟩) (fun x hx _ => ?_))
      (fun m11 _ heff11 _ _ => worldEff_return heff11 _)
    simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hm10_arr, hm10_cnt,
      wordOpHOL, wordOp, valueIsWord, valueWord] at hx
    subst hx
    have hsub1 : (w_cnt - 1#64).toNat = w_cnt.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
      rfl
    have hmul16 : ((w_cnt - 1#64) * 16#64).toNat = (w_cnt.toNat - 1) * 16 := by
      rw [BitVec.toNat_mul, hsub1, show (16#64 : BitVec 64).toNat = 16 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    have hadd_r : (((w_cnt - 1#64) * 16#64) + 8#64).toNat = (w_cnt.toNat - 1) * 16 + 8 := by
      rw [BitVec.toNat_add_of_lt]
      · rw [hmul16]; rfl
      · rw [hmul16]; change (w_cnt.toNat - 1) * 16 + 8 < 2 ^ 64; omega
    have hx_nat : (w_arr + (((w_cnt - 1#64) * 16#64) + 8#64)).toNat = w_arr.toNat + (w_cnt.toNat - 1) * 16 + 8 := by
      rw [BitVec.toNat_add_of_lt] <;> omega
    exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))

theorem eval_var_local_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : MlS) (w : BitVec 64) (hl : s.locals.lookup nm = some (.val (.word w))) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local nm) = some v →
      ∃ w' : BitVec 64, v = .val (.word w') := by
  intro v hv; simp [evalHOLExact, toExact, hl] at hv; exact ⟨w, hv.symm⟩

theorem worldEff_decode_bytes_list_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s entry Rl B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list)).2 Rl B dhiGw := by
  dsimp only [Guest.Software.guestFn_decode_bytes_list, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_decCall_eff heff _ _ _ _ _ _ _ lookup_ssz_split_var_list
    (fun callee _ _ _ hnt_c hres_c => worldEff_ssz_split_var_list_body (heff.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
    (fun _ _ _ cp_dbl _ _ _ _ heff_cp hnt_k hcr_k => ?_) hnt hcr
  refine worldEff_dec (heff_cp.locals_clock _ _) _ _ _ hnt_k hcr_k (fun _ _ _ hnt1 hcr1 => ?_)
  refine worldEff_seq hnt1 hcr1
    (fun hnt_w hcr_w => ?_)
    (fun m_end _ heff_end _ _ => worldEff_return heff_end _)
  exact worldEff_while _ (fun _ => True) (fun _ _ => trivial)
    (fun t0 heff_t _ hnt_b hcr_b =>
      ⟨worldEff_seq hnt_b hcr_b
        (fun hnt_i hcr_i => worldEff_ite_ssz_fail heff_t _ _ hnt_i hcr_i)
        (fun tb _ heff_tb _ _ => worldEff_assign_local heff_tb _ _),
       fun _ => trivial⟩)
    _ _ rfl (heff_cp.locals_clock _ _) trivial hnt_w hcr_w


end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
