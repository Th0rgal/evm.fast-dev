import InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeStatelessSlicesR32

/-!
# `decode_payload` and `decode_host_input`: where the transaction slices point (R32)

Replay of `WkDecodeHostInputTop.decode_payload_body_returns` and
`DecodeStatelessSlicesR32.decode_stateless_input_body_returns_slices` with the
additional postcondition that every transaction slice (`pl + 32` / `pl + 40`)
lies inside the input region `[p, p + len)` the function was called on, and is
therefore `WitnessSliceOK` in the exit state of `decode_host_input`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeSlicesR32

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
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish

/-- Argument values of a call `f(a + b, c - d, c1)` on word locals. -/
theorem evalList_add_sub_const {F : Type} (cur : PanSemStateFiniteExact 64 F)
    (na nb nc nd : MlS) (wa wb wc wd c1 : BitVec 64) (vals : List (ValueHOL 64))
    (ha : cur.locals.lookup na = some (.val (.word wa)))
    (hb : cur.locals.lookup nb = some (.val (.word wb)))
    (hc : cur.locals.lookup nc = some (.val (.word wc)))
    (hd : cur.locals.lookup nd = some (.val (.word wd)))
    (h : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
      [.op .add [.var .local na, .var .local nb], .op .sub [.var .local nc, .var .local nd],
       .const c1] = some vals) :
    vals = [.val (.word (wa + wb)), .val (.word (wc - wd)), .val (.word c1)] := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp [evalListHOLExact, evalHOLExact, toExact, ha, hb, hc, hd, wordOpHOL, wordOp, valueIsWord, valueWord] at h
  exact h.symm

/-- Argument values of a call `f(a + b, c - d)` on word locals. -/
theorem evalList_add_sub_two {F : Type} (cur : PanSemStateFiniteExact 64 F)
    (na nb nc nd : MlS) (wa wb wc wd : BitVec 64) (vals : List (ValueHOL 64))
    (ha : cur.locals.lookup na = some (.val (.word wa)))
    (hb : cur.locals.lookup nb = some (.val (.word wb)))
    (hc : cur.locals.lookup nc = some (.val (.word wc)))
    (hd : cur.locals.lookup nd = some (.val (.word wd)))
    (h : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
      [.op .add [.var .local na, .var .local nb], .op .sub [.var .local nc, .var .local nd]] = some vals) :
    vals = [.val (.word (wa + wb)), .val (.word (wc - wd))] := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp [evalListHOLExact, evalHOLExact, toExact, ha, hb, hc, hd, wordOpHOL, wordOp, valueIsWord, valueWord] at h
  exact h.symm

private theorem assign_local_returned_split_eq {F : Type}
    {cur post : PanSemStateFiniteExact 64 F} {nm : MlS} {valExp : ExpHOL 64}
    {cont : ProgHOL 64} {rv : ValueHOL 64}
    (hrun : evaluateHOLFiniteState cur (.seq (.assign .local nm valExp) cont) = (some (.returned rv), post)) :
    ∃ v mid,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v ∧
      mid = { cur with locals := cur.locals.update (nm, v), clock := mid.clock } ∧
      evaluateHOLFiniteState mid cont = (some (.returned rv), post) := by
  obtain ⟨mid, hasg, hk⟩ := seq_returned_split (assign_noret_dhi cur _ _ _) hrun
  rw [evaluateHOLFiniteState_assign] at hasg
  rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp with _ | v
  · rw [hv] at hasg; simp at hasg
  · rw [hv] at hasg; dsimp only at hasg
    by_cases hvalid : isValidValueHOLFinite cur .local nm v = true
    · rw [if_pos hvalid] at hasg
      injection hasg with _ hmid
      subst hmid
      exact ⟨v, setKvarHOLFinite .local nm v cur, rfl, by cases cur; rfl, hk⟩
    · rw [if_neg hvalid] at hasg; simp at hasg

/-- A slice inside `[p + o_txs, p + o_wd)` is a slice inside `[p, p + len)`. -/
theorem slice_rebase_payload (wp wlen w_otx w_owd : BitVec 64) (m ln o : Nat)
    (hotx : w_otx.toNat ≤ w_owd.toNat) (howd : w_owd.toNat ≤ wlen.toNat)
    (hm : m = ((wp + w_otx).toNat + o) % 2 ^ 64)
    (hl : o + ln ≤ (w_owd - w_otx).toNat) :
    ∃ o' : Nat, m = (wp.toNat + o') % 2 ^ 64 ∧ o' + ln ≤ wlen.toNat := by
  have hsub : (w_owd - w_otx).toNat = w_owd.toNat - w_otx.toNat :=
    BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
  refine ⟨w_otx.toNat + o, ?_, by omega⟩
  rw [hm]
  simp only [BitVec.toNat_add]
  omega

/-- A slice inside the payload region `[p0 + 2 + o_npr + o_pl, … + (o_vh - o_pl))`
is a slice inside `[p0, p0 + len0)`. -/
theorem slice_rebase_npr (wp0 wlen0 w_onpr w_owit w_opl w_ovh : BitVec 64) (m ln o : Nat)
    (h2 : 2 ≤ wlen0.toNat)
    (honpr : w_onpr.toNat ≤ w_owit.toNat)
    (howit : w_owit.toNat ≤ wlen0.toNat - 2)
    (hopl : w_opl.toNat ≤ w_ovh.toNat)
    (hovh : w_ovh.toNat ≤ w_owit.toNat - w_onpr.toNat)
    (hm : m = (((wp0 + 2#64) + w_onpr + w_opl).toNat + o) % 2 ^ 64)
    (hl : o + ln ≤ (w_ovh - w_opl).toNat) :
    ∃ o' : Nat, m = (wp0.toNat + o') % 2 ^ 64 ∧ o' + ln ≤ wlen0.toNat := by
  have hsub : (w_ovh - w_opl).toNat = w_ovh.toNat - w_opl.toNat :=
    BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
  refine ⟨2 + w_onpr.toNat + w_opl.toNat + o, ?_, by omega⟩
  rw [hm]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ### `decode_payload` Return Postcondition with Transaction Slices -/

theorem decode_payload_body_returns_slices {F : Type}
    {s entry post : PanSemStateFiniteExact 64 F}
    {wp wlen : BitVec 64} {rv : ValueHOL 64}
    (hOK : DhiOffsOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word wp)))
    (hlen : entry.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_payload) =
      (some (.returned rv), post)) :
    WorldEff s post (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw ∧
    WorldEff entry post (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw ∧
    ∃ (w_pl : BitVec 64),
      rv = .val (.word w_pl) ∧
      w_pl.toNat % 8 = 0 ∧
      sourceBase ≤ w_pl.toNat ∧
      globN entry "heap_ptr" ≤ w_pl.toNat ∧
      w_pl.toNat + 136 ≤ globN post "heap_ptr" ∧
      globN post "heap_ptr" ≤ heapLimit ∧
      WordsOK post (w_pl.toNat, 136) ∧
      PayloadAt post w_pl.toNat ∧
      memW post (w_pl.toNat + 40) < 2 ^ 32 ∧
      memW post (w_pl.toNat + 56) < 2 ^ 32 ∧
      (memW post (w_pl.toNat + 32)) % 8 = 0 ∧
      WordsOK post (memW post (w_pl.toNat + 32), 16 * memW post (w_pl.toNat + 40)) ∧
      ((memW post (w_pl.toNat + 40) = 0 ∧ memW post (w_pl.toNat + 32) = 0) ∨
       (1 ≤ memW post (w_pl.toNat + 40) ∧
        sourceBase ≤ memW post (w_pl.toNat + 32) ∧
        globN entry "heap_ptr" ≤ memW post (w_pl.toNat + 32) ∧
        memW post (w_pl.toNat + 32) + 16 * memW post (w_pl.toNat + 40) ≤ globN post "heap_ptr" ∧
        w_pl.toNat + 136 ≤ memW post (w_pl.toNat + 32) ∧
        ∀ j : Nat, j < memW post (w_pl.toNat + 40) →
          ∃ o : Nat, memW post (memW post (w_pl.toNat + 32) + 16 * j) = (wp.toNat + o) % 2 ^ 64 ∧
            o + memW post (memW post (w_pl.toNat + 32) + 16 * j + 8) ≤ wlen.toNat)) := by
  have hhl : heapLimit < 2 ^ 64 := by decide
  have hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_payload)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_payload)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have heff_s_post : WorldEff s post (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw := by
    have h := worldEff_decode_payload_body_ok hOK heff hp hlen hnt hcr
    rwa [hrun] at h
  have hOK_entry : DhiOffsOK entry := dhiOffsOK_of_worldEff hOK heff
  have heff_entry_refl : WorldEff entry entry (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw :=
    WorldEff.refl entry (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw heff.arena heff.code
  have heff_entry_post : WorldEff entry post (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    have h := worldEff_decode_payload_body_ok hOK_entry heff_entry_refl hp hlen hnt hcr
    rwa [hrun] at h
  dsimp only [Guest.Software.guestFn_decode_payload, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  obtain ⟨m1, hm1, hk1⟩ := seq_returned_split (ite_call0_noret_dhi entry _ _ _) hrun
  obtain ⟨hm1_eq, _⟩ := ite_ssz_fail_keeps entry m1 heff.code _ _ hm1
  have heff1 : WorldEff entry m1 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm1_eq]; exact heff_entry_refl.locals_clock _ _
  have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm1_eq]; exact hp
  have hm1_len : m1.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm1_eq]; exact hlen
  obtain ⟨w_pl, nw_pl, m2, post_pl, hsz_pl, _, hm2_loc, _, heff2, hpl_al, hpl_sb, hpl_lo, hpl_hp, hpl_lim, _, hk2, hpost_pl⟩ :=
    decCall_alloc_returned_split heff1 hk1
  have hnw_pl : nw_pl = 136#64 := by simp [evalHOLExact] at hsz_pl; exact hsz_pl.symm
  subst hnw_pl
  have hm2_pl : m2.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_p, show ofString "pl" ≠ ofString "p" by decide]
  have hm2_len : m2.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_len, show ofString "pl" ≠ ofString "len" by decide]
  have hpl_136 : w_pl.toNat + 136 = globN m2 "heap_ptr" := by simpa using hpl_hp
  obtain ⟨m3, _, _, hm3_loc, hm3_glob, heff3, _, _, hk3⟩ :=
    seq_store_fresh_returned heff2 (ofString "pl") w_pl 136 0 hm2_pl hpl_lo (by omega) (by omega) _
      (eval_var_local_word m2 _ wp hm2_p) hk2
  obtain ⟨m4, _, _, hm4_loc, hm4_glob, heff4, _, _, hk4⟩ :=
    seq_store_fresh_returned heff3 (ofString "pl") w_pl 136 8 (by rw [hm3_loc]; exact hm2_pl) hpl_lo (by omega) (by omega) _
      (eval_var_local_word m3 _ wlen (by rw [hm3_loc]; exact hm2_len)) hk3
  obtain ⟨v_oex, post_oex, hv_oex, _, hk5, hpost_oex⟩ := dec_returned_split hk4
  obtain ⟨w_oex, rfl, hoex_lt⟩ := eval_le32_word_lt m4 _ _ _ _ v_oex hv_oex
  let m5 := setVarHOLFinite (ofString "o_extra") (.val (.word w_oex)) m4
  obtain ⟨v_otx, post_otx, hv_otx, _, hk6, hpost_otx⟩ := dec_returned_split hk5
  obtain ⟨w_otx, rfl, hotx_lt⟩ := eval_le32_word_lt m5 _ _ _ _ v_otx hv_otx
  let m6 := setVarHOLFinite (ofString "o_txs") (.val (.word w_otx)) m5
  obtain ⟨v_owd, post_owd, hv_owd, _, hk7, hpost_owd⟩ := dec_returned_split hk6
  obtain ⟨w_owd, rfl, howd_lt⟩ := eval_le32_word_lt m6 _ _ _ _ v_owd hv_owd
  let m7 := setVarHOLFinite (ofString "o_wd") (.val (.word w_owd)) m6
  obtain ⟨v_obl, post_obl, hv_obl, _, hk8, hpost_obl⟩ := dec_returned_split hk7
  obtain ⟨w_obl, rfl, hobl_lt⟩ := eval_le32_word_lt m7 _ _ _ _ v_obl hv_obl
  let m8 := setVarHOLFinite (ofString "o_bal") (.val (.word w_obl)) m7
  have hm8_glob : m8.globals = m2.globals := by
    dsimp only [m8, m7, m6, m5, setVarHOLFinite]
    rw [hm4_glob, hm3_glob]
  have hm4_pl : m4.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm4_loc, hm3_loc]; exact hm2_pl
  have hm4_p : m4.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm4_loc, hm3_loc]; exact hm2_p
  have hm4_len : m4.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm4_loc, hm3_loc]; exact hm2_len
  have hm8_pl : m8.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    dsimp only [m8, m7, m6, m5]
    iterate 4 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm4_pl
  have hm8_p : m8.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    dsimp only [m8, m7, m6, m5]
    iterate 4 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm4_p
  have hm8_len : m8.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    dsimp only [m8, m7, m6, m5]
    iterate 4 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm4_len
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
  have heff8 : WorldEff entry m8 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff4.locals_clock _ _
  obtain ⟨m9, vw9, hv9_ev, hm9_loc, hm9_glob, heff9, hm9_eq, hm9_ne, hk9⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff8 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
      (eval_var_local_word m8 _ w_oex hm8_oex) hk8
  have hvw9 : vw9 = w_oex := by simp [evalHOLExact, toExact, hm8_oex] at hv9_ev; exact hv9_ev.symm
  rw [hvw9] at hm9_eq
  obtain ⟨m10, vw10, hv10_ev, hm10_loc, hm10_glob, heff10, hm10_eq, hm10_ne, hk10⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff9 8 (by omega) _ _ (Or.inr rfl)
      (eval_var_local_word m9 _ w_otx (by rw [hm9_loc]; exact hm8_otx)) hk9
  have hvw10 : vw10 = w_otx := by
    have h9 : m9.locals.lookup (ofString "o_txs") = some (.val (.word w_otx)) := by rw [hm9_loc]; exact hm8_otx
    simp [evalHOLExact, toExact, h9] at hv10_ev; exact hv10_ev.symm
  rw [hvw10] at hm10_eq
  obtain ⟨m11, vw11, hv11_ev, hm11_loc, hm11_glob, heff11, hm11_eq, hm11_ne, hk11⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff10 16 (by omega) _ _ (Or.inr rfl)
      (eval_var_local_word m10 _ w_owd (by rw [hm10_loc, hm9_loc]; exact hm8_owd)) hk10
  have hvw11 : vw11 = w_owd := by
    have h10 : m10.locals.lookup (ofString "o_wd") = some (.val (.word w_owd)) := by rw [hm10_loc, hm9_loc]; exact hm8_owd
    simp [evalHOLExact, toExact, h10] at hv11_ev; exact hv11_ev.symm
  rw [hvw11] at hm11_eq
  obtain ⟨m12, vw12, hv12_ev, hm12_loc, hm12_glob, heff12, hm12_eq, hm12_ne, hk12⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff11 24 (by omega) _ _ (Or.inr rfl)
      (eval_var_local_word m11 _ w_obl (by rw [hm11_loc, hm10_loc, hm9_loc]; exact hm8_obl)) hk11
  have hvw12 : vw12 = w_obl := by
    have h11 : m11.locals.lookup (ofString "o_bal") = some (.val (.word w_obl)) := by rw [hm11_loc, hm10_loc, hm9_loc]; exact hm8_obl
    simp [evalHOLExact, toExact, h11] at hv12_ev; exact hv12_ev.symm
  rw [hvw12] at hm12_eq
  have hm12_loc_eq : m12.locals = m8.locals := by rw [hm12_loc, hm11_loc, hm10_loc, hm9_loc]
  have hm12_len_ev : @evalHOLExact 64 F _ m12.toExact (fun a => Classical.propDecidable (m12.memaddrs a))
      (.var .local (ofString "len")) = some (.val (.word wlen)) := by
    have h : m12.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm12_loc_eq]; exact hm8_len
    simp [evalHOLExact, toExact, h]
  obtain ⟨m13, hm13_mem, hm13_glob, hm13_loc, heff13, hchk0, hchk_b, hchk_m, hk13⟩ :=
    call0_ssz_check_offsets_returned_ok hOK_entry heff12 4#64 540#64 (.var .local (ofString "len"))
      (by decide) (by decide) hm12_len_ev hk12
  have hhe : heapEnd < 2 ^ 64 := by decide
  have hoff_hi : globN entry "ssz_offs" + 64 ≤ heapEnd := by
    rcases hOK_entry.2 with hg0 | ⟨_, hhi, _, _⟩
    · exfalso
      obtain ⟨mid_s, hst_s, _⟩ := seq_returned_split (store_noret_dhi m8 _ _) hk8
      obtain ⟨sw, hsw_e⟩ := hOK_entry.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
      have hsw8 : m8.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
        (heff8.gw_kept (ofString "ssz_offs") (by decide)).symm.trans hsw_e
      have hsw0 : sw = 0#64 := BitVec.eq_of_toNat_eq (by unfold GlobalWord at hsw_e; simp [globN, hsw_e] at hg0; simp [hg0])
      subst hsw0
      rw [evaluateHOLFiniteState_store] at hst_s
      have hndom : ¬ m8.memaddrs 0#64 := by
        rw [heff8.memaddrs, hOK_entry.1.1.memaddrs, ordinaryDomain_iff]
        have : 0 < sourceBase := by decide
        simp; omega
      simp [evalHOLExact, toExact, hsw8, hm8_oex, flattenHOL, panMemStoresHOL, panMemStoreHOL, hndom] at hst_s
    · exact hhi
  have hm12_0 : memW m12 (globN entry "ssz_offs") = w_oex.toNat := by
    rw [hm12_ne _ (by omega) (by omega), hm11_ne _ (by omega) (by omega), hm10_ne _ (by omega) (by omega)]
    simpa using hm9_eq
  have hm12_8 : memW m12 (globN entry "ssz_offs" + 8) = w_otx.toNat := by
    rw [hm12_ne _ (by omega) (by omega), hm11_ne _ (by omega) (by omega)]
    exact hm10_eq
  have hm12_16 : memW m12 (globN entry "ssz_offs" + 16) = w_owd.toNat := by
    rw [hm12_ne _ (by omega) (by omega)]
    exact hm11_eq
  have hm12_24 : memW m12 (globN entry "ssz_offs" + 24) = w_obl.toNat := hm12_eq
  have hoex_le_otx : w_oex.toNat ≤ w_otx.toNat := by
    have hm := hchk_m 0 (by decide)
    simpa [hm12_0, hm12_8] using hm
  have hotx_le_owd : w_otx.toNat ≤ w_owd.toNat := by
    have hm := hchk_m 1 (by decide)
    simpa [hm12_8, hm12_16] using hm
  have hwd_obl_mono : w_owd.toNat ≤ w_obl.toNat := by
    have hm := hchk_m 2 (by decide)
    simpa [hm12_16, hm12_24] using hm
  have howd_le_obl : w_obl.toNat ≤ wlen.toNat := by
    have hb := (hchk_b 3 (by decide)).2
    simpa [hm12_24] using hb
  obtain ⟨m14, hm14, hk14⟩ := seq_returned_split (ite_call0_noret_dhi m13 _ _ _) hk13
  obtain ⟨hm14_eq, hm14_cond⟩ := ite_ssz_fail_keeps m13 m14 heff13.code _ _ hm14
  have hm13_loc_eq : m13.locals = m8.locals := by rw [hm13_loc, hm12_loc_eq]
  have hextra_le_32 : (w_otx - w_oex).toNat ≤ 32 := by
    have h13_otx : m13.locals.lookup (ofString "o_txs") = some (.val (.word w_otx)) := by rw [hm13_loc_eq]; exact hm8_otx
    have h13_oex : m13.locals.lookup (ofString "o_extra") = some (.val (.word w_oex)) := by rw [hm13_loc_eq]; exact hm8_oex
    by_cases hlt : 32#64 < w_otx - w_oex
    · simp [evalHOLExact, evalListHOLExact, toExact, h13_otx, h13_oex, wordOpHOL, wordOp,
        Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord, hlt] at hm14_cond
    · exact Nat.le_of_not_lt (fun h => hlt ((BitVec.lt_def).2 h))
  have heff14 : WorldEff entry m14 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm14_eq]; exact heff13.locals_clock _ _
  have hm14_loc_eq : m14.locals = m8.locals := by rw [hm14_eq]; exact hm13_loc_eq
  have hm14_glob_eq : m14.globals = m2.globals := by
    rw [hm14_eq, hm13_glob, hm12_glob, hm11_glob, hm10_glob, hm9_glob, hm8_glob]
  have hm14_pl : m14.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm14_loc_eq]; exact hm8_pl
  obtain ⟨m15, _, _, hm15_loc, hm15_glob, heff15, _, _, hk15⟩ :=
    seq_store_fresh_returned heff14 (ofString "pl") w_pl 136 16 hm14_pl hpl_lo (by omega) (by omega) _
      (eval_op_word m14 _ ⟨_, _, rfl⟩) hk14
  have hm15_loc_eq : m15.locals = m8.locals := by rw [hm15_loc]; exact hm14_loc_eq
  obtain ⟨m16, vw_exlen, hv_exlen_ev, hm16_loc, hm16_glob, heff16, hm16_pl24, _, hk16⟩ :=
    seq_store_fresh_returned heff15 (ofString "pl") w_pl 136 24 (by rw [hm15_loc_eq]; exact hm8_pl) hpl_lo (by omega) (by omega) _
      (eval_op_word m15 _ ⟨_, _, rfl⟩) hk15
  have hvw_exlen : vw_exlen = w_otx - w_oex := by
    have h15_otx : m15.locals.lookup (ofString "o_txs") = some (.val (.word w_otx)) := by rw [hm15_loc_eq]; exact hm8_otx
    have h15_oex : m15.locals.lookup (ofString "o_extra") = some (.val (.word w_oex)) := by rw [hm15_loc_eq]; exact hm8_oex
    simp [evalHOLExact, evalListHOLExact, toExact, h15_otx, h15_oex, wordOpHOL, wordOp, valueIsWord, valueWord] at hv_exlen_ev
    exact hv_exlen_ev.symm
  rw [hvw_exlen] at hm16_pl24
  have hm16_loc_eq : m16.locals = m8.locals := by rw [hm16_loc]; exact hm15_loc_eq
  have hm16_hp : globN m16 "heap_ptr" = w_pl.toNat + 136 := by
    have hg : m16.globals = m2.globals := by rw [hm16_glob, hm15_glob, hm14_glob_eq]
    have hge : globN m16 "heap_ptr" = globN m2 "heap_ptr" := by unfold globN; rw [hg]
    omega
  -- Next: decCall "txs" ssz_split_var_list [p + o_txs, o_wd - o_txs, 1073741824]
  obtain ⟨vals_tx, fc_tx, crv_tx, cp_tx, post_tx, hargs_tx, hl_tx, _, hc_tx, hsh_tx, _, hk17, hpost_tx⟩ :=
    decCall_returned_split heff16.code lookup_ssz_split_var_list hk16
  obtain ⟨w_tx_p, w_tx_len, w_tx_lim, hvs_tx, hfc_tx_p, hfc_tx_len, hfc_tx_lim⟩ :=
    lookupCode_three_words_any_dhi (by decide) (by decide) (by decide) lookup_ssz_split_var_list hl_tx
  have hm16_p : m16.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm16_loc_eq]; exact hm8_p
  have hm16_otx : m16.locals.lookup (ofString "o_txs") = some (.val (.word w_otx)) := by rw [hm16_loc_eq]; exact hm8_otx
  have hm16_owd : m16.locals.lookup (ofString "o_wd") = some (.val (.word w_owd)) := by rw [hm16_loc_eq]; exact hm8_owd
  have hvs_tx_eq := evalList_add_sub_const m16 _ _ _ _ wp w_otx w_owd w_otx _ _ hm16_p hm16_otx hm16_owd hm16_otx hargs_tx
  rw [hvs_tx_eq] at hvs_tx
  injection hvs_tx with h1 htl; injection htl with h2 _
  injection h1 with h1'; injection h1' with htx_p_eq; subst htx_p_eq
  injection h2 with h2'; injection h2' with htx_len_eq; subst htx_len_eq
  have htx_len_lt : (w_owd - w_otx).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; exact hotx_le_owd)]
    omega
  let ent_tx := callEntryStateHOLFinite m16 fc_tx
  have heff_m16_ent_tx : WorldEff m16 ent_tx ([] : List Ivl) ([] : List (String × Nat)) dhiGw :=
    (WorldEff.refl m16 ([] : List Ivl) ([] : List (String × Nat)) dhiGw heff16.arena heff16.code).locals_clock _ _
  have heff_ent_tx : WorldEff entry ent_tx (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw :=
    heff16.locals_clock _ _
  obtain ⟨_, heff_step_tx, w_txp, w_ntx, hcrv_tx, _, hntx_lt30, htxp_al, hwok_tx_cp, htx_cases⟩ :=
    ssz_split_var_list_body_returns_slices heff_m16_ent_tx hfc_tx_p hfc_tx_len hfc_tx_lim hc_tx
  have heff_cp_tx : WorldEff entry cp_tx (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw :=
    (ssz_split_var_list_body_returns heff_ent_tx hfc_tx_p hfc_tx_len hfc_tx_lim hc_tx).1
  subst hcrv_tx
  have hcp_pl24 : memW cp_tx (w_pl.toNat + 24) = (w_otx - w_oex).toNat := by
    have hbv : (BitVec.ofNat 64 (w_pl.toNat + 24)).toNat = w_pl.toNat + 24 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsame : cp_tx.memory (BitVec.ofNat 64 (w_pl.toNat + 24)) = m16.memory (BitVec.ofNat 64 (w_pl.toNat + 24)) := by
      by_contra hdiff
      rcases heff_step_tx.cell_frame (BitVec.ofNat 64 (w_pl.toNat + 24)) hdiff with
        ⟨_, hiv, _, _, _⟩ | ⟨_, hgs, _⟩ | ⟨_, hfg1, _⟩ | ⟨_, hhf1, _⟩
      · cases hiv
      · cases hgs
      · dsimp only [freeGap] at hfg1
        have hfmp : scratchStart ≤ globN ent_tx "frame_mem_ptr" := heff16.arena.2.2.2.1
        have hls : heapLimit ≤ scratchStart := by decide
        omega
      · dsimp only [heapFree] at hhf1
        have h1 : globN ent_tx "heap_ptr" = globN m16 "heap_ptr" := rfl
        omega
    unfold memW at hm16_pl24 ⊢
    rw [hsame]; exact hm16_pl24
  let m17 := setVarHOLFinite (ofString "txs") (.rStruct [.val (.word w_txp), .val (.word w_ntx)])
    { cp_tx with locals := m16.locals }
  have heff17 : WorldEff entry m17 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw :=
    heff_cp_tx.locals_clock _ _
  have hm17_txs : m17.locals.lookup (ofString "txs") = some (.rStruct [.val (.word w_txp), .val (.word w_ntx)]) :=
    lookup_setVar_eq _ _ _
  have hm17_rest : ∀ k : MlS, k ≠ ofString "txs" → m17.locals.lookup k = m8.locals.lookup k := by
    intro k hk
    dsimp only [m17]
    rw [lookup_setVar_ne _ _ _ _ hk]
    dsimp only
    rw [hm16_loc_eq]
  have hm17_pl : m17.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hm17_rest _ (by decide)]; exact hm8_pl
  obtain ⟨m18, vw_txp, hv_txp_ev, hm18_loc, hm18_glob, heff18, hm18_pl32, hm18_ne, hk18⟩ :=
    seq_store_fresh_returned heff17 (ofString "pl") w_pl 136 32 hm17_pl hpl_lo (by omega) (by omega) _
      (eval_rfield_word m17 0 (ofString "txs") w_txp w_ntx hm17_txs (Or.inl rfl)) hk17
  have hvw_txp : vw_txp = w_txp := by
    simp [evalHOLExact, toExact, hm17_txs] at hv_txp_ev; exact hv_txp_ev.symm
  rw [hvw_txp] at hm18_pl32
  obtain ⟨m19, vw_ntx, hv_ntx_ev, hm19_loc, hm19_glob, heff19, hm19_pl40, hm19_ne, hk19⟩ :=
    seq_store_fresh_returned heff18 (ofString "pl") w_pl 136 40 (by rw [hm18_loc]; exact hm17_pl) hpl_lo (by omega) (by omega) _
      (eval_rfield_word m18 1 (ofString "txs") w_txp w_ntx (by rw [hm18_loc]; exact hm17_txs) (Or.inr rfl)) hk18
  have hvw_ntx : vw_ntx = w_ntx := by
    have h18_txs : m18.locals.lookup (ofString "txs") = some (.rStruct [.val (.word w_txp), .val (.word w_ntx)]) := by
      rw [hm18_loc]; exact hm17_txs
    simp [evalHOLExact, toExact, h18_txs] at hv_ntx_ev; exact hv_ntx_ev.symm
  rw [hvw_ntx] at hm19_pl40
  have hm19_loc_eq : m19.locals = m17.locals := by rw [hm19_loc, hm18_loc]
  have hm19_wd_ev : @evalHOLExact 64 F _ m19.toExact (fun a => Classical.propDecidable (m19.memaddrs a))
      (.op .sub [.var .local (ofString "o_bal"), .var .local (ofString "o_wd")]) =
      some (.val (.word (w_obl - w_owd))) := by
    have h_obl : m19.locals.lookup (ofString "o_bal") = some (.val (.word w_obl)) := by
      rw [hm19_loc_eq, hm17_rest _ (by decide)]; exact hm8_obl
    have h_owd : m19.locals.lookup (ofString "o_wd") = some (.val (.word w_owd)) := by
      rw [hm19_loc_eq, hm17_rest _ (by decide)]; exact hm8_owd
    simp [evalHOLExact, evalListHOLExact, toExact, h_obl, h_owd, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨w_nwd, m20, post_nwd, _, hmul_nwd, _, hm20_mem, hm20_glob, hm20_loc, heff20, hk20, hpost_nwd⟩ :=
    decCall_ssz_fixed_list_count_returned heff19 (ofString "nwd") _ 44#64 9223372036854775807#64 hm19_wd_ev hk19
  have hnwd_lt32 : w_nwd.toNat < 2 ^ 32 := by
    have hsub : (w_obl - w_owd).toNat = w_obl.toNat - w_owd.toNat :=
      BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
    rw [show (44#64 : BitVec 64).toNat = 44 from rfl, hsub] at hmul_nwd
    omega
  have hm20_pl : m20.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hm20_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm19_loc_eq, hm17_pl,
      show ofString "nwd" ≠ ofString "pl" by decide]
  have hm20_nwd : m20.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) := by
    rw [hm20_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨s1, _, _, hl1, hg1, hs1, _, hne1, hks1⟩ :=
    seq_store_fresh_returned heff20 (ofString "pl") w_pl 136 48 hm20_pl hpl_lo (by omega) (by omega) _
      (eval_op_word m20 _ ⟨_, _, rfl⟩) hk20
  obtain ⟨s2, vw_s2, hvw_s2_ev, hl2, hg2, hs2, hs2_pl56, hne2, hks2⟩ :=
    seq_store_fresh_returned hs1 (ofString "pl") w_pl 136 56 (by rw [hl1]; exact hm20_pl) hpl_lo (by omega) (by omega) _
      (eval_var_local_word s1 _ w_nwd (by rw [hl1]; exact hm20_nwd)) hks1
  have hvw_s2 : vw_s2 = w_nwd := by
    have hs1_nwd : s1.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) := by
      rw [hl1]; exact hm20_nwd
    simp [evalHOLExact, toExact, hs1_nwd] at hvw_s2_ev; exact hvw_s2_ev.symm
  rw [hvw_s2] at hs2_pl56
  obtain ⟨s3, _, _, hl3, hg3, hs3, _, hne3, hks3⟩ :=
    seq_store_fresh_returned hs2 (ofString "pl") w_pl 136 64 (by rw [hl2, hl1]; exact hm20_pl) hpl_lo (by omega) (by omega) _
      (eval_op_word s2 _ ⟨_, _, rfl⟩) hks2
  obtain ⟨s4, _, _, hl4, hg4, hs4, _, hne4, hks4⟩ :=
    seq_store_fresh_returned hs3 (ofString "pl") w_pl 136 72 (by rw [hl3, hl2, hl1]; exact hm20_pl) hpl_lo (by omega) (by omega) _
      (eval_op_word s3 _ ⟨_, _, rfl⟩) hks3
  obtain ⟨s5, _, _, hl5, hg5, hs5, _, hne5, hks5⟩ :=
    seq_store_fresh_returned hs4 (ofString "pl") w_pl 136 80 (by rw [hl4, hl3, hl2, hl1]; exact hm20_pl) hpl_lo (by omega) (by omega) _
      (eval_op_word s4 _ ⟨_, _, rfl⟩) hks4
  obtain ⟨s6, _, _, hl6, hg6, hs6, _, hne6, hks6⟩ :=
    seq_store_fresh_returned hs5 (ofString "pl") w_pl 136 88 (by rw [hl5, hl4, hl3, hl2, hl1]; exact hm20_pl) hpl_lo (by omega) (by omega) _
      (eval_op_word s5 _ ⟨_, _, rfl⟩) hks5
  obtain ⟨s7, _, _, hl7, hg7, hs7, _, hne7, hks7⟩ :=
    seq_store_fresh_returned hs6 (ofString "pl") w_pl 136 96 (by rw [hl6, hl5, hl4, hl3, hl2, hl1]; exact hm20_pl) hpl_lo (by omega) (by omega) _
      (eval_op_word s6 _ ⟨_, _, rfl⟩) hks6
  obtain ⟨s8, _, _, hl8, hg8, hs8, _, hne8, hks8⟩ :=
    seq_store_fresh_returned hs7 (ofString "pl") w_pl 136 104 (by rw [hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm20_pl) hpl_lo (by omega) (by omega) _
      (eval_op_word s7 _ ⟨_, _, rfl⟩) hks7
  obtain ⟨s9, _, _, hl9, hg9, hs9, _, hne9, hks9⟩ :=
    seq_store_fresh_returned hs8 (ofString "pl") w_pl 136 112 (by rw [hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm20_pl) hpl_lo (by omega) (by omega) _
      (eval_op_word s8 _ ⟨_, _, rfl⟩) hks8
  obtain ⟨s10, _, _, hl10, hg10, hs10, _, hne10, hks10⟩ :=
    seq_store_fresh_returned hs9 (ofString "pl") w_pl 136 120 (by rw [hl9, hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm20_pl) hpl_lo (by omega) (by omega) _
      (eval_op_word s9 _ ⟨_, _, rfl⟩) hks9
  obtain ⟨s11, _, _, hl11, hg11, hs11, _, hne11, hks11⟩ :=
    seq_store_fresh_returned hs10 (ofString "pl") w_pl 136 128 (by rw [hl10, hl9, hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm20_pl) hpl_lo (by omega) (by omega) _
      (eval_op_word s10 _ ⟨_, _, rfl⟩) hks10
  have hs11_pl : s11.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hl11, hl10, hl9, hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm20_pl
  rw [evaluateHOLFiniteState_return] at hks11
  simp [evalHOLExact, toExact, hs11_pl, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hks11
  obtain ⟨hrv_eq, hs11_post⟩ := hks11
  have hpost_mem : post.memory = s11.memory := by
    rw [hpost_pl, hpost_oex, hpost_otx, hpost_owd, hpost_obl, hpost_tx, hpost_nwd, ← hs11_post]
    rfl
  have hpost_glob : post.globals = cp_tx.globals := by
    rw [hpost_pl, hpost_oex, hpost_otx, hpost_owd, hpost_obl, hpost_tx, hpost_nwd, ← hs11_post]
    dsimp only [emptyLocalsHOLFinite]
    rw [hg11, hg10, hg9, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hg1, hm20_glob, hm19_glob, hm18_glob]
    rfl
  have hpost_memW_s11 : ∀ a, memW post a = memW s11 a := fun a => by unfold memW; rw [hpost_mem]
  have hs11_keep_m19 : ∀ a : Nat, a < 2 ^ 64 →
      (a < w_pl.toNat + 48 ∨ w_pl.toNat + 136 ≤ a) → memW s11 a = memW m19 a := by
    intro a ha hout
    rw [hne11 a ha (by omega), hne10 a ha (by omega), hne9 a ha (by omega), hne8 a ha (by omega),
        hne7 a ha (by omega), hne6 a ha (by omega), hne5 a ha (by omega), hne4 a ha (by omega),
        hne3 a ha (by omega), hne2 a ha (by omega), hne1 a ha (by omega)]
    unfold memW; rw [hm20_mem]
  have hpost_pl24 : memW post (w_pl.toNat + 24) = (w_otx - w_oex).toNat := by
    rw [hpost_memW_s11, hs11_keep_m19 _ (by omega) (Or.inl (by omega)),
        hm19_ne _ (by omega) (by omega), hm18_ne _ (by omega) (by omega)]
    simpa [m17, setVarHOLFinite, memW] using hcp_pl24
  have hpost_pl32 : memW post (w_pl.toNat + 32) = w_txp.toNat := by
    rw [hpost_memW_s11, hs11_keep_m19 _ (by omega) (Or.inl (by omega)),
        hm19_ne _ (by omega) (by omega), hm18_pl32]
  have hpost_pl40 : memW post (w_pl.toNat + 40) = w_ntx.toNat := by
    rw [hpost_memW_s11, hs11_keep_m19 _ (by omega) (Or.inl (by omega)), hm19_pl40]
  have hpost_pl56 : memW post (w_pl.toNat + 56) = w_nwd.toNat := by
    rw [hpost_memW_s11, hne11 _ (by omega) (by omega), hne10 _ (by omega) (by omega),
        hne9 _ (by omega) (by omega), hne8 _ (by omega) (by omega), hne7 _ (by omega) (by omega),
        hne6 _ (by omega) (by omega), hne5 _ (by omega) (by omega), hne4 _ (by omega) (by omega),
        hne3 _ (by omega) (by omega), hs2_pl56]
  have hpost_hp_cp : globN post "heap_ptr" = globN cp_tx "heap_ptr" := by
    unfold globN; rw [hpost_glob]
  have hcp_hp_ge : w_pl.toNat + 136 ≤ globN cp_tx "heap_ptr" := by
    have h1 := heff_step_tx.hp_lo
    change globN m16 "heap_ptr" ≤ globN cp_tx "heap_ptr" at h1
    omega
  have hwok_pl_post : WordsOK post (w_pl.toNat, 136) :=
    wordsOK_preserved_of_worldEff heff_entry_post hpl_al (by omega) hpl_sb (by have := heff_entry_post.arena.2.2.1; omega)
  have hntx_lt32 : w_ntx.toNat < 2 ^ 32 := by omega
  refine ⟨heff_s_post, heff_entry_post, w_pl, hrv_eq.symm, hpl_al, hpl_sb, hpl_lo,
    by omega, heff_entry_post.arena.2.2.1, hwok_pl_post, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- PayloadAt post w_pl.toNat
    refine ⟨hwok_pl_post, by rw [hpost_pl24]; exact hextra_le_32, by rw [hpost_pl40]; exact hntx_lt32, ?_⟩
    intro i hi
    rw [hpost_pl40] at hi
    rw [hpost_pl32]
    rcases htx_cases with ⟨hc0, _, _⟩ | ⟨_, htxp_sb, htxp_lo_m16, htxp_hi_cp, _, htx_el, _⟩
    · omega
    · have h16_lo : w_pl.toNat + 136 ≤ w_txp.toNat := by
        change globN m16 "heap_ptr" ≤ w_txp.toNat at htxp_lo_m16; omega
      have hel_keep : memW post (w_txp.toNat + 16 * i + 8) = memW cp_tx (w_txp.toNat + 16 * i + 8) := by
        rw [hpost_memW_s11, hs11_keep_m19 _ (by omega) (Or.inr (by omega)),
            hm19_ne _ (by omega) (by omega), hm18_ne _ (by omega) (by omega)]
        rfl
      rw [hel_keep]
      exact Nat.lt_of_le_of_lt (htx_el i hi) htx_len_lt
  · rw [hpost_pl40]; exact hntx_lt32
  · rw [hpost_pl56]; exact hnwd_lt32
  · rw [hpost_pl32]; exact htxp_al
  · rw [hpost_pl32, hpost_pl40]
    rcases htx_cases with ⟨hc0, ha0, _⟩ | ⟨_, htxp_sb, _, htxp_hi_cp, hcp_lim, _, _⟩
    · refine ⟨by simp [ha0], by simp [hc0], fun k hk => by simp [hc0] at hk⟩
    · exact wordsOK_preserved_of_worldEff heff_entry_post htxp_al (by omega) htxp_sb (by omega)
  · rw [hpost_pl32, hpost_pl40]
    rcases htx_cases with ⟨hc0, ha0, _⟩ | ⟨hc1, htxp_sb, htxp_lo_m16, htxp_hi_cp, hcp_lim, _, htx_sl⟩
    · exact Or.inl ⟨hc0, ha0⟩
    · have h16_lo : w_pl.toNat + 136 ≤ w_txp.toNat := by
        change globN m16 "heap_ptr" ≤ w_txp.toNat at htxp_lo_m16; omega
      refine Or.inr ⟨hc1, htxp_sb, by omega, by omega, h16_lo, fun j hj => ?_⟩
      obtain ⟨o, ho1, ho2⟩ := htx_sl j hj
      have e1 : memW post (w_txp.toNat + 16 * j) = memW cp_tx (w_txp.toNat + 16 * j) := by
        rw [hpost_memW_s11, hs11_keep_m19 _ (by omega) (Or.inr (by omega)),
            hm19_ne _ (by omega) (by omega), hm18_ne _ (by omega) (by omega)]
        rfl
      have e2 : memW post (w_txp.toNat + 16 * j + 8) = memW cp_tx (w_txp.toNat + 16 * j + 8) := by
        rw [hpost_memW_s11, hs11_keep_m19 _ (by omega) (Or.inr (by omega)),
            hm19_ne _ (by omega) (by omega), hm18_ne _ (by omega) (by omega)]
        rfl
      rw [e1, e2]
      exact slice_rebase_payload wp wlen w_otx w_owd _ _ o hotx_le_owd (by omega) ho1 ho2

/-! ### `decode_stateless_input`: transaction slices lie inside `[p, p + len)` -/

theorem decode_stateless_input_body_returns_tx_slices {F : Type}
    {s entry post : PanSemStateFiniteExact 64 F}
    {wp0 wlen0 : BitVec 64} {rv : ValueHOL 64}
    (hOK : DhiOffsOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word wp0)))
    (hlen : entry.locals.lookup (ofString "len") = some (.val (.word wlen0)))
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input) =
      (some (.returned rv), post)) :
    ∃ (w_si : BitVec 64),
      rv = .val (.word w_si) ∧
      ∀ j, j < memW post (memW post w_si.toNat + 40) →
        ∃ o : Nat, memW post (memW post (memW post w_si.toNat + 32) + 16 * j) = (wp0.toNat + o) % 2 ^ 64 ∧
          o + memW post (memW post (memW post w_si.toNat + 32) + 16 * j + 8) ≤ wlen0.toNat := by
  have hhl : heapLimit < 2 ^ 64 := by decide
  have hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have hOK_entry : DhiOffsOK entry := dhiOffsOK_of_worldEff hOK heff
  have heff_entry_refl : WorldEff entry entry (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw :=
    WorldEff.refl entry (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw heff.arena heff.code
  have heff_entry_post : WorldEff entry post (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    have h := worldEff_decode_stateless_input_body_ok hOK_entry heff_entry_refl hnt hcr
    rwa [hrun] at h
  dsimp only [Guest.Software.guestFn_decode_stateless_input, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  -- 1. ite (len < 2) ssz_fail
  obtain ⟨m1, hm1_ite, hk1⟩ := seq_returned_split (ite_call0_noret_dhi entry _ _ _) hrun
  obtain ⟨hm1_eq, hlen0_ge2_cond⟩ := ite_ssz_fail_keeps entry m1 heff_entry_refl.code _ _ hm1_ite
  have hlen0_ge2 : 2 ≤ wlen0.toNat := by
    simp only [evalHOLExact, evalListHOLExact, toExact, hlen,
      Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hlen0_ge2_cond
    by_cases hlt : wlen0 < 2#64
    · simp [hlt] at hlen0_ge2_cond
    · simp [BitVec.lt_def] at hlt; exact hlt
  have heff1 : WorldEff entry m1 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm1_eq]; exact heff_entry_refl
  -- 2. ite (version != 21, 1) ssz_fail
  obtain ⟨m2, hm2_ite, hk2⟩ := seq_returned_split (ite_call0_noret_dhi m1 _ _ _) hk1
  obtain ⟨hm2_eq, _⟩ := ite_ssz_fail_keeps m1 m2 heff1.code _ _ hm2_ite
  have heff2 : WorldEff entry m2 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm2_eq]; exact heff1
  have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word wp0)) := by
    rw [hm2_eq, hm1_eq]; exact hp
  have hm2_len : m2.locals.lookup (ofString "len") = some (.val (.word wlen0)) := by
    rw [hm2_eq, hm1_eq]; exact hlen
  -- 3. assign p := p + 2; assign len := len - 2
  obtain ⟨vp, m3, hvp_ev, hm3_eq, hk3⟩ :=
    assign_local_returned_split_eq hk2
  have hvp_eq : vp = .val (.word (wp0 + 2#64)) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm2_p, wordOpHOL, wordOp, valueIsWord, valueWord] at hvp_ev
    exact hvp_ev.symm
  subst hvp_eq
  have heff3 : WorldEff entry m3 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm3_eq]; exact heff2.locals_clock _ _
  have hm3_len0 : m3.locals.lookup (ofString "len") = some (.val (.word wlen0)) := by
    rw [hm3_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_len, show ofString "p" ≠ ofString "len" by decide]
  obtain ⟨vlen, m4, hvlen_ev, hm4_eq, hk4⟩ :=
    assign_local_returned_split_eq hk3
  have hvlen_eq : vlen = .val (.word (wlen0 - 2#64)) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm3_len0, wordOpHOL, wordOp, valueIsWord, valueWord] at hvlen_ev
    exact hvlen_ev.symm
  subst hvlen_eq
  have heff4 : WorldEff entry m4 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm4_eq]; exact heff3.locals_clock _ _
  let wp := wp0 + 2#64
  let wlen := wlen0 - 2#64
  have hwlen_nat : wlen.toNat = wlen0.toNat - 2 :=
    BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; exact hlen0_ge2)
  have hm4_p : m4.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm4_eq, hm3_eq]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "len" ≠ ofString "p" by decide, wp]
  have hm4_len : m4.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, wlen]
  -- 4. ite (len < 16) ssz_fail
  obtain ⟨m5, hm5_ite, hk5⟩ := seq_returned_split (ite_call0_noret_dhi m4 _ _ _) hk4
  obtain ⟨hm5_eq, _⟩ := ite_ssz_fail_keeps m4 m5 heff4.code _ _ hm5_ite
  have heff5 : WorldEff entry m5 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm5_eq]; exact heff4
  have hm5_p : m5.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm5_eq]; exact hm4_p
  have hm5_len : m5.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm5_eq]; exact hm4_len
  -- 5. store ssz_offs+0 := le32(p), store ssz_offs+8 := le32(p+4), ssz_check_offsets(ssz_offs, 2, 16, len)
  obtain ⟨m6, vw6, hv6_ev, hm6_loc, _, heff6, hm6_eq, hm6_ne, hk6⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff5 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
      (eval_op_word m5 _ ⟨_, _, rfl⟩) hk5
  obtain ⟨w_le0, hwle0_val, hwle0_lt⟩ := eval_le32_word_lt m5 _ _ _ _ (.val (.word vw6)) hv6_ev
  injection hwle0_val with h1; injection h1 with hw6_eq; subst hw6_eq
  obtain ⟨m7, vw7, hv7_ev, hm7_loc, _, heff7, hm7_eq, hm7_ne, hk7⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff6 8 (by omega) _ _ (Or.inr rfl)
      (eval_op_word m6 _ ⟨_, _, rfl⟩) hk6
  obtain ⟨w_le1, hwle1_val, hwle1_lt⟩ := eval_le32_word_lt m6 _ _ _ _ (.val (.word vw7)) hv7_ev
  injection hwle1_val with h1; injection h1 with hw7_eq; subst hw7_eq
  have hm7_p : m7.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm7_loc, hm6_loc]; exact hm5_p
  have hm7_len : m7.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm7_loc, hm6_loc]; exact hm5_len
  have hlen7_ev : @evalHOLExact 64 F _ m7.toExact (fun a => Classical.propDecidable (m7.memaddrs a))
      (.var .local (ofString "len")) = some (.val (.word wlen)) := by
    simp [evalHOLExact, toExact, hm7_len]
  obtain ⟨m8, hm8_mem, hm8_glob, hm8_loc, heff8, hm7_off0, hm7_bounds, hm7_mono, hk8⟩ :=
    call0_ssz_check_offsets_returned_ok hOK_entry heff7 2#64 16#64 (.var .local (ofString "len"))
      (by decide) (by decide) hlen7_ev hk7
  -- 6. dec o_npr := load ssz_offs; dec o_wit := load (ssz_offs + 8)
  have hm8_m7_memW : ∀ a, memW m8 a = memW m7 a := fun a => by unfold memW; rw [hm8_mem]
  obtain ⟨vonpr, post_onpr, hvonpr, _, hk9, hpost_onpr⟩ := dec_returned_split hk8
  obtain ⟨w_onpr, rfl, hwonpr_eq⟩ := load_ssz_offs_const_eval hOK_entry heff8 0 (by decide) (by decide) _ (Or.inl ⟨rfl, rfl⟩) hvonpr
  rw [Nat.add_zero, hm8_m7_memW] at hwonpr_eq
  let m9 := setVarHOLFinite (ofString "o_npr") (.val (.word w_onpr)) m8
  have heff9 : WorldEff entry m9 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff8.locals_clock _ _
  obtain ⟨vowit, post_owit, hvowit, _, hk10, hpost_owit⟩ := dec_returned_split hk9
  obtain ⟨w_owit, rfl, hwowit_eq⟩ := load_ssz_offs_const_eval hOK_entry heff9 8 (by decide) (by decide) _ (Or.inr rfl) hvowit
  have hm9_m8_memW : ∀ a, memW m9 a = memW m8 a := fun _ => rfl
  rw [hm9_m8_memW, hm8_m7_memW] at hwowit_eq
  have howit_lt32 : w_owit.toNat < 2 ^ 32 := by rw [hwowit_eq, hm7_eq]; exact hwle1_lt
  have honpr_chain : w_onpr.toNat = 16 ∧ w_onpr.toNat ≤ w_owit.toNat ∧ w_owit.toNat ≤ wlen.toNat := by
    have h01 := hm7_mono 0 (by decide)
    have hb1 := (hm7_bounds 1 (by decide)).2
    have hn8 : 0 * 8 = 0 ∧ (0 + 1) * 8 = 8 ∧ 1 * 8 = 8 := by decide
    rw [hn8.1, hn8.2.1, Nat.add_zero] at h01
    rw [hn8.2.2] at hb1
    have h16 : (16#64 : BitVec 64).toNat = 16 := rfl
    omega
  let m10 := setVarHOLFinite (ofString "o_wit") (.val (.word w_owit)) m9
  have heff10 : WorldEff entry m10 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff9.locals_clock _ _
  have hm10_p : m10.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    dsimp only [m10, m9]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    rw [hm8_loc]; exact hm7_p
  have hm10_len : m10.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    dsimp only [m10, m9]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    rw [hm8_loc]; exact hm7_len
  have hm10_onpr : m10.locals.lookup (ofString "o_npr") = some (.val (.word w_onpr)) := by
    dsimp only [m10]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
  have hm10_owit : m10.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := lookup_setVar_eq _ _ _
  -- 7. decCall si := alloc(96); store (si + 88) ...
  obtain ⟨w_si, nw_si, m11, post_si, hsz_si, hm11_mem, hm11_loc, _, heff11,
    hsi_al, hsi_sb, hsi_lo_m10, hsi_add_m11, hm11_lim, hwok_si_m11, hk11, hpost_si⟩ :=
    decCall_alloc_returned_split heff10 hk10
  have hnw_si : nw_si = 96#64 := by simp [evalHOLExact] at hsz_si; exact hsz_si.symm
  subst hnw_si
  have hsi_hi_m11 : w_si.toNat + 96 = globN m11 "heap_ptr" := by
    simpa [show (96#64 : BitVec 64).toNat = 96 from rfl] using hsi_add_m11
  have hsi_lo : globN entry "heap_ptr" ≤ w_si.toNat := by
    have h1 := heff10.hp_lo; omega
  have hm11_si : m11.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm11_p : m11.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_p, show ofString "si" ≠ ofString "p" by decide]
  have hm11_len : m11.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_len, show ofString "si" ≠ ofString "len" by decide]
  have hm11_onpr : m11.locals.lookup (ofString "o_npr") = some (.val (.word w_onpr)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_onpr, show ofString "si" ≠ ofString "o_npr" by decide]
  have hm11_owit : m11.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_owit, show ofString "si" ≠ ofString "o_wit" by decide]
  obtain ⟨m12, _, _, hm12_loc, hm12_glob, heff12, _, _, hk12⟩ :=
    seq_store_fresh_returned heff11 (ofString "si") w_si 96 88 hm11_si hsi_lo (by omega) (by omega) _
      (eval_op_word m11 _ ⟨_, _, rfl⟩) hk11
  have hm12_hp : globN m12 "heap_ptr" = globN m11 "heap_ptr" := by unfold globN; rw [hm12_glob]
  have hm12_si : m12.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm12_loc]; exact hm11_si
  have hm12_p : m12.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm12_loc]; exact hm11_p
  have hm12_len : m12.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm12_loc]; exact hm11_len
  have hm12_onpr : m12.locals.lookup (ofString "o_npr") = some (.val (.word w_onpr)) := by rw [hm12_loc]; exact hm11_onpr
  have hm12_owit : m12.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by rw [hm12_loc]; exact hm11_owit
  -- 8. dec np := p + o_npr; dec nlen := o_wit - o_npr; ite (nlen < 44) ssz_fail
  obtain ⟨vnp, post_np, hvnp, _, hk13, hpost_np⟩ := dec_returned_split hk12
  have hvnp_eq : vnp = .val (.word (wp + w_onpr)) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm12_p, hm12_onpr, wordOpHOL, wordOp, valueIsWord, valueWord] at hvnp
    exact hvnp.symm
  subst hvnp_eq
  let w_np := wp + w_onpr
  let m13 := setVarHOLFinite (ofString "np") (.val (.word w_np)) m12
  obtain ⟨vnlen, post_nlen, hvnlen, _, hk14, hpost_nlen⟩ := dec_returned_split hk13
  have hm13_onpr : m13.locals.lookup (ofString "o_npr") = some (.val (.word w_onpr)) := by
    dsimp only [m13]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm12_onpr
  have hm13_owit : m13.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by
    dsimp only [m13]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm12_owit
  have hvnlen_eq : vnlen = .val (.word (w_owit - w_onpr)) := by
    change @evalHOLExact 64 F _ m13.toExact (fun a => Classical.propDecidable (m13.memaddrs a)) _ = _ at hvnlen
    simp [evalHOLExact, evalListHOLExact, toExact, hm13_owit, hm13_onpr, wordOpHOL, wordOp, valueIsWord, valueWord] at hvnlen
    exact hvnlen.symm
  subst hvnlen_eq
  let w_nlen := w_owit - w_onpr
  have hnlen_nat : w_nlen.toNat = w_owit.toNat - w_onpr.toNat :=
    BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
  let m14 := setVarHOLFinite (ofString "nlen") (.val (.word w_nlen)) m13
  have heff14 : WorldEff entry m14 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff12.locals_clock _ _
  obtain ⟨m15, hm15_ite, hk15⟩ := seq_returned_split (ite_call0_noret_dhi m14 _ _ _) hk14
  obtain ⟨hm15_eq, _⟩ := ite_ssz_fail_keeps m14 m15 heff14.code _ _ hm15_ite
  have heff15 : WorldEff entry m15 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm15_eq]; exact heff14
  -- 9. dec o_pl, o_vh, o_rq; store into ssz_offs + {0, 8, 16}; ssz_check_offsets(ssz_offs, 3, 44, nlen)
  obtain ⟨vopl, post_opl, hvopl, _, hk16, hpost_opl⟩ := dec_returned_split hk15
  obtain ⟨w_opl, rfl, _⟩ := eval_le32_word_lt m15 _ _ _ _ vopl hvopl
  let m16 := setVarHOLFinite (ofString "o_pl") (.val (.word w_opl)) m15
  obtain ⟨vovh, post_ovh, hvovh, _, hk17, hpost_ovh⟩ := dec_returned_split hk16
  obtain ⟨w_ovh, rfl, hovh_lt⟩ := eval_le32_word_lt m16 _ _ _ _ vovh hvovh
  let m17 := setVarHOLFinite (ofString "o_vh") (.val (.word w_ovh)) m16
  obtain ⟨vorq, post_orq, hvorq, _, hk18, hpost_orq⟩ := dec_returned_split hk17
  obtain ⟨w_orq, rfl, horq_lt⟩ := eval_le32_word_lt m17 _ _ _ _ vorq hvorq
  let m18 := setVarHOLFinite (ofString "o_rq") (.val (.word w_orq)) m17
  have heff18 : WorldEff entry m18 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff15.locals_clock _ _
  have hm18_hp : globN m18 "heap_ptr" = globN m11 "heap_ptr" := by
    change globN m15 "heap_ptr" = globN m11 "heap_ptr"
    rw [hm15_eq]; exact hm12_hp
  have hm15_si : m15.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm15_eq]; dsimp only [m14, m13]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]; exact hm12_si
  have hm15_np : m15.locals.lookup (ofString "np") = some (.val (.word w_np)) := by
    rw [hm15_eq]; dsimp only [m14]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
  have hm15_nlen : m15.locals.lookup (ofString "nlen") = some (.val (.word w_nlen)) := by
    rw [hm15_eq]; exact lookup_setVar_eq _ _ _
  have hm18_si : m18.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m18, m17, m16]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm15_si
  have hm18_np : m18.locals.lookup (ofString "np") = some (.val (.word w_np)) := by
    dsimp only [m18, m17, m16]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm15_np
  have hm18_nlen : m18.locals.lookup (ofString "nlen") = some (.val (.word w_nlen)) := by
    dsimp only [m18, m17, m16]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm15_nlen
  have hm18_opl : m18.locals.lookup (ofString "o_pl") = some (.val (.word w_opl)) := by
    dsimp only [m18, m17, m16]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm18_ovh : m18.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by
    dsimp only [m18, m17]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
  have hm18_orq : m18.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := lookup_setVar_eq _ _ _
  obtain ⟨m19, vw19, hv19_ev, hm19_loc, hm19_glob, heff19, hm19_eq, hm19_ne, hk19⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff18 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
      (eval_var_local_word m18 _ w_opl hm18_opl) hk18
  have hvw19 : vw19 = w_opl := by simp [evalHOLExact, toExact, hm18_opl] at hv19_ev; exact hv19_ev.symm
  rw [hvw19] at hm19_eq
  obtain ⟨m20, vw20, hv20_ev, hm20_loc, hm20_glob, heff20, hm20_eq, hm20_ne, hk20⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff19 8 (by omega) _ _ (Or.inr rfl)
      (eval_var_local_word m19 _ w_ovh (by rw [hm19_loc]; exact hm18_ovh)) hk19
  have hvw20 : vw20 = w_ovh := by
    have h : m19.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by rw [hm19_loc]; exact hm18_ovh
    simp [evalHOLExact, toExact, h] at hv20_ev; exact hv20_ev.symm
  rw [hvw20] at hm20_eq
  obtain ⟨m21, vw21, hv21_ev, hm21_loc, hm21_glob, heff21, hm21_eq, hm21_ne, hk21⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff20 16 (by omega) _ _ (Or.inr rfl)
      (eval_var_local_word m20 _ w_orq (by rw [hm20_loc, hm19_loc]; exact hm18_orq)) hk20
  have hvw21 : vw21 = w_orq := by
    have h : m20.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by rw [hm20_loc, hm19_loc]; exact hm18_orq
    simp [evalHOLExact, toExact, h] at hv21_ev; exact hv21_ev.symm
  rw [hvw21] at hm21_eq
  have hm21_nlen : m21.locals.lookup (ofString "nlen") = some (.val (.word w_nlen)) := by
    rw [hm21_loc, hm20_loc, hm19_loc]; exact hm18_nlen
  have hnlen21_ev : @evalHOLExact 64 F _ m21.toExact (fun a => Classical.propDecidable (m21.memaddrs a))
      (.var .local (ofString "nlen")) = some (.val (.word w_nlen)) := by
    simp [evalHOLExact, toExact, hm21_nlen]
  obtain ⟨m22, hm22_mem, hm22_glob, hm22_loc, heff22, hm21_off0, hm21_bounds, hm21_mono, hk22⟩ :=
    call0_ssz_check_offsets_returned_ok hOK_entry heff21 3#64 44#64 (.var .local (ofString "nlen"))
      (by decide) (by decide) hnlen21_ev hk21
  have hm22_hp : globN m22 "heap_ptr" = globN m11 "heap_ptr" := by
    unfold globN; rw [hm22_glob, hm21_glob, hm20_glob, hm19_glob]; exact hm18_hp
  have hnpr_chain : w_opl.toNat = 44 ∧ w_opl.toNat ≤ w_ovh.toNat ∧ w_ovh.toNat ≤ w_orq.toNat ∧ w_orq.toNat ≤ w_nlen.toNat := by
    have hhe : heapEnd < 2 ^ 64 := by decide
    have hoff_hi : globN entry "ssz_offs" + 64 ≤ heapEnd := by
      rcases hOK_entry.2 with hg0 | ⟨_, hhi, _, _⟩
      · exfalso
        obtain ⟨mid_s, hst_s, _⟩ := seq_returned_split (store_noret_dhi m18 _ _) hk18
        obtain ⟨sw, hsw_e⟩ := hOK_entry.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
        have hsw18 : m18.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
          (heff18.gw_kept (ofString "ssz_offs") (by decide)).symm.trans hsw_e
        have hsw0 : sw = 0#64 := BitVec.eq_of_toNat_eq (by unfold GlobalWord at hsw_e; simp [globN, hsw_e] at hg0; simp [hg0])
        subst hsw0
        rw [evaluateHOLFiniteState_store] at hst_s
        have hndom : ¬ m18.memaddrs 0#64 := by
          rw [heff18.memaddrs, hOK_entry.1.1.memaddrs, ordinaryDomain_iff]
          have : 0 < sourceBase := by decide
          simp; omega
        simp [evalHOLExact, toExact, hsw18, hm18_opl, flattenHOL, panMemStoresHOL, panMemStoreHOL, hndom] at hst_s
      · exact hhi
    have ha0 : memW m21 (globN entry "ssz_offs") = w_opl.toNat := by
      rw [hm21_ne _ (by omega) (by omega), hm20_ne _ (by omega) (by omega)]; simpa using hm19_eq
    have ha1 : memW m21 (globN entry "ssz_offs" + 8) = w_ovh.toNat := by
      rw [hm21_ne _ (by omega) (by omega), hm20_eq]
    have ha2 : memW m21 (globN entry "ssz_offs" + 16) = w_orq.toNat := hm21_eq
    have hm01 := hm21_mono 0 (by decide)
    have hm12 := hm21_mono 1 (by decide)
    have hb2 := (hm21_bounds 2 (by decide)).2
    have hn8 : 0 * 8 = 0 ∧ (0 + 1) * 8 = 8 ∧ 1 * 8 = 8 ∧ (1 + 1) * 8 = 16 ∧ 2 * 8 = 16 := by decide
    rw [hn8.1, hn8.2.1, Nat.add_zero] at hm01
    rw [hn8.2.2.1, hn8.2.2.2.1] at hm12
    rw [hn8.2.2.2.2] at hb2
    have h44 : (44#64 : BitVec 64).toNat = 44 := rfl
    omega
  have hm22_loc_m18 : m22.locals = m18.locals := by rw [hm22_loc, hm21_loc, hm20_loc, hm19_loc]
  have hm22_si : m22.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm22_loc_m18]; exact hm18_si
  have hm22_np : m22.locals.lookup (ofString "np") = some (.val (.word w_np)) := by rw [hm22_loc_m18]; exact hm18_np
  have hm22_opl : m22.locals.lookup (ofString "o_pl") = some (.val (.word w_opl)) := by rw [hm22_loc_m18]; exact hm18_opl
  have hm22_ovh : m22.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by rw [hm22_loc_m18]; exact hm18_ovh
  have hm22_orq : m22.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by rw [hm22_loc_m18]; exact hm18_orq
  have hm22_nlen : m22.locals.lookup (ofString "nlen") = some (.val (.word w_nlen)) := by rw [hm22_loc_m18]; exact hm18_nlen
  have hm22_len : m22.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm22_loc_m18]; dsimp only [m18, m17, m16]
    iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    rw [hm15_eq]; dsimp only [m14, m13]
    iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm12_len
  have hm22_owit : m22.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by
    rw [hm22_loc_m18]; dsimp only [m18, m17, m16]
    iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    rw [hm15_eq]; dsimp only [m14, m13]
    iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm12_owit
  -- 10. decCall pl := decode_payload(np + o_pl, o_vh - o_pl); store (si + 0) pl
  obtain ⟨vals_pl, fc_pl, rv_pl, cp_pl, post_pl, hargs_pl, hl_pl, _, hc_pl, _, _, hk23, hpost_pl⟩ :=
    decCall_returned_split heff22.code lookup_decode_payload hk22
  obtain ⟨wp_pl, wlen_pl, hvs_pl, hfc_pl_p, hfc_pl_len⟩ :=
    lookupCode_two_words_any_dhi (by decide) lookup_decode_payload hl_pl
  have hvs_pl_eq := evalList_add_sub_two m22 _ _ _ _ w_np w_opl w_ovh w_opl _ hm22_np hm22_opl hm22_ovh hm22_opl hargs_pl
  rw [hvs_pl_eq] at hvs_pl
  injection hvs_pl with h1 htl; injection htl with h2 _
  injection h1 with h1'; injection h1' with hpl_p_eq; subst hpl_p_eq
  injection h2 with h2'; injection h2' with hpl_len_eq; subst hpl_len_eq
  obtain ⟨heff_cp_pl, heff_step_pl, w_pl, rfl, hpl_al, hpl_sb, hpl_lo_m22, hpl_hi_cp, hcp_pl_lim,
    hwok_pl_cp, hpl_at_cp, hntx_lt32_cp, hnwd_lt32_cp, htxp_al_cp, hwok_tx_cp, htx_cases_cp⟩ :=
    decode_payload_body_returns_slices hOK_entry (heff22.locals_clock fc_pl (m22.clock - 1)) hfc_pl_p hfc_pl_len hc_pl
  have hpl_lo_si : w_si.toNat + 96 ≤ w_pl.toNat := by
    change globN m22 "heap_ptr" ≤ w_pl.toNat at hpl_lo_m22; omega
  let m23 := setVarHOLFinite (ofString "pl") (.val (.word w_pl)) { cp_pl with locals := m22.locals }
  have heff23 : WorldEff entry m23 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff_cp_pl.locals_clock _ _
  have hm23_pl : m23.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := lookup_setVar_eq _ _ _
  have hm23_si : m23.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_si
  obtain ⟨m24, vw24, hv24_ev, hm24_loc, hm24_glob, heff24, hm24_si0, hm24_ne, hk24⟩ :=
    seq_store_fresh_returned heff23 (ofString "si") w_si 96 0 hm23_si hsi_lo (by have := heff_step_pl.hp_lo; change globN m22 "heap_ptr" ≤ _ at this; omega) (by omega) _
      (eval_var_local_word m23 _ w_pl hm23_pl) hk23
  have hvw24 : vw24 = w_pl := by simp [evalHOLExact, toExact, hm23_pl] at hv24_ev; exact hv24_ev.symm
  rw [hvw24, Nat.add_zero] at hm24_si0
  -- 11. Rest of decode_stateless_input up to return si
  have hm24_ovh : m24.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by
    rw [hm24_loc]; dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_ovh
  have hm24_orq : m24.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by
    rw [hm24_loc]; dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_orq
  have hsub_vh_ev : @evalHOLExact 64 F _ m24.toExact (fun a => Classical.propDecidable (m24.memaddrs a))
      (.op .sub [.var .local (ofString "o_rq"), .var .local (ofString "o_vh")]) =
      some (.val (.word (w_orq - w_ovh))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm24_orq, hm24_ovh, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨w_nvh, m25, post_nvh, _, _, _, hm25_mem, hm25_glob, hm25_loc, heff25, hk25, hpost_nvh⟩ :=
    decCall_ssz_fixed_list_count_returned heff24 (ofString "nvh") _ 32#64 9223372036854775807#64 hsub_vh_ev hk24
  have hm25_hp : globN m25 "heap_ptr" = globN cp_pl "heap_ptr" := by
    unfold globN; rw [hm25_glob, hm24_glob]; rfl
  have hm25_si : m25.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm25_loc, hm24_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm23_si, show ofString "nvh" ≠ ofString "si" by decide]
  have hm25_nvh : m25.locals.lookup (ofString "nvh") = some (.val (.word w_nvh)) := by
    rw [hm25_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨m26, _, _, hm26_loc, hm26_glob, heff26, _, hm26_ne, hk26⟩ :=
    seq_store_fresh_returned heff25 (ofString "si") w_si 96 8 hm25_si hsi_lo (by omega) (by omega) _
      (eval_op_word m25 _ ⟨_, _, rfl⟩) hk25
  obtain ⟨m27, _, _, hm27_loc, hm27_glob, heff27, _, hm27_ne, hk27⟩ :=
    seq_store_fresh_returned heff26 (ofString "si") w_si 96 16 (by rw [hm26_loc]; exact hm25_si) hsi_lo
      (by have : globN m26 "heap_ptr" = globN m25 "heap_ptr" := by unfold globN; rw [hm26_glob]
          omega) (by omega) _
      (eval_var_local_word m26 _ w_nvh (by rw [hm26_loc]; exact hm25_nvh)) hk26
  obtain ⟨m28, _, _, hm28_loc, hm28_glob, heff28, _, hm28_ne, hk28⟩ :=
    seq_store_fresh_returned heff27 (ofString "si") w_si 96 24 (by rw [hm27_loc, hm26_loc]; exact hm25_si) hsi_lo
      (by have : globN m27 "heap_ptr" = globN m25 "heap_ptr" := by unfold globN; rw [hm27_glob, hm26_glob]
          omega) (by omega) _
      (eval_op_word m27 _ ⟨_, _, rfl⟩) hk27
  have hm28_hp : globN m28 "heap_ptr" = globN cp_pl "heap_ptr" := by
    unfold globN; rw [hm28_glob, hm27_glob, hm26_glob]; exact hm25_hp
  have hm28_loc_m25 : m28.locals = m25.locals := by rw [hm28_loc, hm27_loc, hm26_loc]
  have hm28_si : m28.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm28_loc_m25]; exact hm25_si
  have hm28_np : m28.locals.lookup (ofString "np") = some (.val (.word w_np)) := by
    rw [hm28_loc_m25, hm25_loc, hm24_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "nvh" ≠ ofString "np" by decide]
    dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_np
  have hm28_nlen : m28.locals.lookup (ofString "nlen") = some (.val (.word w_nlen)) := by
    rw [hm28_loc_m25, hm25_loc, hm24_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "nvh" ≠ ofString "nlen" by decide]
    dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_nlen
  have hm28_orq : m28.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by
    rw [hm28_loc_m25, hm25_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm24_orq, show ofString "nvh" ≠ ofString "o_rq" by decide]
  -- 12. decCall rq := decode_requests(np + o_rq, nlen - o_rq); store (si + 32) rq
  obtain ⟨vals_rq, fc_rq, rv_rq, cp_rq, post_rq, hargs_rq, hl_rq, _, hc_rq, _, _, hk29, hpost_rq⟩ :=
    decCall_returned_split heff28.code lookup_decode_requests hk28
  obtain ⟨wp_rq, wlen_rq, hvs_rq, hfc_rq_p, hfc_rq_len⟩ :=
    lookupCode_two_words_any_dhi (by decide) lookup_decode_requests hl_rq
  have hargs_rq_eq : vals_rq = [.val (.word (w_np + w_orq)), .val (.word (w_nlen - w_orq))] := by
    rw [evalListHOLFinite_eq_toExact] at hargs_rq
    simp [evalListHOLExact, evalHOLExact, toExact, hm28_np, hm28_nlen, hm28_orq, wordOpHOL, wordOp, valueIsWord, valueWord] at hargs_rq
    exact hargs_rq.symm
  rw [hargs_rq_eq] at hvs_rq
  injection hvs_rq with h1 htl; injection htl with h2 _
  injection h2 with h2'; injection h2' with hlen_rq_eq; subst hlen_rq_eq
  have hlen_rq_lt32 : (w_nlen - w_orq).toNat < 2 ^ 32 := by
    have hsub : (w_nlen - w_orq).toNat = w_nlen.toNat - w_orq.toNat :=
      BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
    omega
  obtain ⟨heff_cp_rq, heff_step_rq, w_rq, rfl, hrq_al, hrq_sb, hrq_lo_m28, hrq_hi_cp, _, _, _⟩ :=
    decode_requests_body_returns hOK_entry (heff28.locals_clock fc_rq (m28.clock - 1)) hfc_rq_p hfc_rq_len hlen_rq_lt32 hc_rq
  let m29 := setVarHOLFinite (ofString "rq") (.val (.word w_rq)) { cp_rq with locals := m28.locals }
  have heff29 : WorldEff entry m29 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff_cp_rq.locals_clock _ _
  have hm29_rq : m29.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := lookup_setVar_eq _ _ _
  have hm29_si : m29.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m29]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm28_si
  obtain ⟨m30, _, _, hm30_loc, hm30_glob, heff30, _, hm30_ne, hk30⟩ :=
    seq_store_fresh_returned heff29 (ofString "si") w_si 96 32 hm29_si hsi_lo
      (by have := heff_step_rq.hp_lo; change globN m28 "heap_ptr" ≤ _ at this; omega) (by omega) _
      (eval_var_local_word m29 _ w_rq hm29_rq) hk29
  have hm30_hp : globN m30 "heap_ptr" = globN cp_rq "heap_ptr" := by unfold globN; rw [hm30_glob]; rfl
  have hm30_si : m30.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm30_loc]; exact hm29_si
  have hm30_len : m30.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm30_loc]; dsimp only [m29]; rw [lookup_setVar_ne _ _ _ _ (by decide)]
    rw [hm28_loc_m25, hm25_loc, hm24_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "nvh" ≠ ofString "len" by decide]
    dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_len
  have hm30_owit : m30.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by
    rw [hm30_loc]; dsimp only [m29]; rw [lookup_setVar_ne _ _ _ _ (by decide)]
    rw [hm28_loc_m25, hm25_loc, hm24_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "nvh" ≠ ofString "o_wit" by decide]
    dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_owit
  -- 13. Witness section up to return si
  obtain ⟨vwp, post_wpw, _, _, hk31, hpost_wpw⟩ := dec_returned_split hk30
  let m31 := setVarHOLFinite (ofString "wp") vwp m30
  obtain ⟨vwlen, post_wlenw, hvwlen_w, _, hk32, hpost_wlenw⟩ := dec_returned_split hk31
  let m32 := setVarHOLFinite (ofString "wlen") vwlen m31
  have hm31_len : m31.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    dsimp only [m31]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm30_len
  have hm31_owit : m31.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by
    dsimp only [m31]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm30_owit
  have hvwlen_eq : vwlen = .val (.word (wlen - w_owit)) :=
    eval_sub_locals m31 _ _ _ _ _ hm31_len hm31_owit hvwlen_w
  have heff32 : WorldEff entry m32 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff30.locals_clock _ _
  obtain ⟨m33, hm33_ite, hk33⟩ := seq_returned_split (ite_call0_noret_dhi m32 _ _ _) hk32
  obtain ⟨hm33_eq, _⟩ := ite_ssz_fail_keeps m32 m33 heff32.code _ _ hm33_ite
  have heff33 : WorldEff entry m33 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm33_eq]; exact heff32
  obtain ⟨vi3, post_i3, hvi3, _, hk34, hpost_i3⟩ := dec_returned_split hk33
  have hvi3_eq : vi3 = .val (.word 0#64) := by simp [evalHOLExact] at hvi3; exact hvi3.symm
  subst hvi3_eq
  let m34 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m33
  have heff34 : WorldEff entry m34 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff33.locals_clock _ _
  obtain ⟨m35, hm35_w, hk35⟩ := seq_returned_split
    (while_noret_dhi m34 _ _ (fun u =>
      seq_noret_dhi u (store_noret_dhi u _ _) (fun u2 _ => assign_noret_dhi u2 _ _ _))) hk34
  let Inv3 : PanSemStateFiniteExact 64 F → Prop :=
    fun t => ∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧ wi.toNat ≤ 3
  have heff_34_35 : WorldEff m34 m35 (dhiOffsRegions m34) ([] : List (String × Nat)) dhiGw := by
    have hOK_34 := dhiOffsOK_of_worldEff hOK_entry heff34
    have heff34_refl := WorldEff.refl m34 (dhiOffsRegions m34) ([] : List (String × Nat)) dhiGw heff34.arena heff34.code
    exact worldEff_of_none_dhi hm35_w (fun hnt_w hcr_w =>
      worldEff_while_cond_dhi _ Inv3 (fun _ h => h)
        (fun t0 cw hcond hnz heff_t ⟨wi, ht_i, hwi_le⟩ hnt_b hcr_b => by
          have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
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
              (fun _ _ => worldEff_store_ssz_offs_dyn_ok hOK_34 heff_t _ _ (wi * 8#64)
                (by simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, decClockHOLFinite, ht0_i, valueIsWord, valueWord])
                (by omega) (eval_op_word (decClockHOLFinite t0) _ ⟨_, _, rfl⟩))
              (fun tb _ heff_tb _ _ => worldEff_assign_local heff_tb _ _)
          · exact evaluate_incTail_le (ofString "i") 3 (by decide) _ (by decide) (decClockHOLFinite t0) wi ht_i hwi_lt hf)
        m34.clock m34 rfl heff34_refl ⟨0#64, lookup_setVar_eq _ _ _, by decide⟩ hnt_w hcr_w)
  have heff35 : WorldEff entry m35 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    have hr := dhiOffsRegions_eq_of_worldEff heff34
    rw [hr] at heff_34_35
    exact heff34.trans_noBuf heff_34_35 (by intro _ h; cases h) dhi_no_gb
  have hm34_wlen : m34.locals.lookup (ofString "wlen") = some (.val (.word (wlen - w_owit))) := by
    dsimp only [m34]; rw [lookup_setVar_ne _ _ _ _ (by decide), hm33_eq]
    dsimp only [m32]
    rw [lookup_setVar_eq, hvwlen_eq]
  have hm35_wlen : m35.locals.lookup (ofString "wlen") = some (.val (.word (wlen - w_owit))) := by
    have hk := evaluate_keepLocal (ofString "wlen") _ (by decide) m34 (Or.inl (congrArg Prod.fst hm35_w))
    rw [hm35_w] at hk; rw [hk]; exact hm34_wlen
  have hOK_35 : DhiOffsOK m35 := dhiOffsOK_of_worldEff hOK_entry heff35
  have hwlen35_ev : @evalHOLExact 64 F _ m35.toExact (fun a => Classical.propDecidable (m35.memaddrs a))
      (.var .local (ofString "wlen")) = some (.val (.word (wlen - w_owit))) := by
    simp [evalHOLExact, toExact, hm35_wlen]
  obtain ⟨m36, _, _, hm36_loc, heff_35_36, _, _, _, hk36⟩ :=
    call0_ssz_check_offsets_returned_ok hOK_35
      (WorldEff.refl m35 (dhiOffsRegions m35) ([] : List (String × Nat)) dhiGw heff35.arena heff35.code)
      3#64 12#64 (.var .local (ofString "wlen")) (by decide) (by decide) hwlen35_ev hk35
  have heff36 : WorldEff entry m36 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    have hr := dhiOffsRegions_eq_of_worldEff heff35
    rw [hr] at heff_35_36
    exact heff35.trans_noBuf heff_35_36 (by intro _ h; cases h) dhi_no_gb
  have hm34_si : m34.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m34]; rw [lookup_setVar_ne _ _ _ _ (by decide), hm33_eq]
    dsimp only [m32, m31]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm30_si
  have hm35_si : m35.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    have hk := evaluate_keepLocal (ofString "si") _ (by decide) m34 (Or.inl (congrArg Prod.fst hm35_w))
    rw [hm35_w] at hk; rw [hk]; exact hm34_si
  have hm36_si : m36.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm36_loc]; exact hm35_si
  obtain ⟨vw0, post_w0, _, _, hk37, hpost_w0⟩ := dec_returned_split hk36
  let m37 := setVarHOLFinite (ofString "w0") vw0 m36
  obtain ⟨vw1, post_w1, _, _, hk38, hpost_w1⟩ := dec_returned_split hk37
  let m38 := setVarHOLFinite (ofString "w1") vw1 m37
  obtain ⟨vw2, post_w2, _, _, hk39, hpost_w2⟩ := dec_returned_split hk38
  let m39 := setVarHOLFinite (ofString "w2") vw2 m38
  have heff39 : WorldEff entry m39 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff36.locals_clock _ _
  have hm30_39_eff : WorldEff m30 m39 (dhiOffsRegions m30) ([] : List (String × Nat)) dhiGw := by
    have hr30 := dhiOffsRegions_eq_of_worldEff heff30
    have hr34 := dhiOffsRegions_eq_of_worldEff heff34
    have hr35 := dhiOffsRegions_eq_of_worldEff heff35
    rw [hr34, ← hr30] at heff_34_35
    rw [hr35, ← hr30] at heff_35_36
    have h30_34 : WorldEff m30 m34 (dhiOffsRegions m30) ([] : List (String × Nat)) dhiGw := by
      have h33 : WorldEff m30 m33 (dhiOffsRegions m30) ([] : List (String × Nat)) dhiGw := by
        rw [hm33_eq]; exact (WorldEff.refl m30 _ _ _ heff30.arena heff30.code).locals_clock _ _
      exact h33.locals_clock _ _
    have h30_35 := h30_34.trans_noBuf heff_34_35 (by intro _ h; cases h) dhi_no_gb
    have h30_36 := h30_35.trans_noBuf heff_35_36 (by intro _ h; cases h) dhi_no_gb
    exact h30_36.locals_clock _ _
  have hm39_hp_ge : globN cp_rq "heap_ptr" ≤ globN m39 "heap_ptr" := by
    have h1 := hm30_39_eff.hp_lo; omega
  have hm39_si : m39.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m39, m38, m37]
    iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm36_si
  -- 14. Three decode_bytes_list calls and return si
  obtain ⟨vals_st0, fc_st0, rv_st0, cp_st0, post_st0, _, hl_st0, _, hc_st0, _, _, hk40, hpost_st0⟩ :=
    decCall_returned_split heff39.code lookup_decode_bytes_list hk39
  obtain ⟨wp_st0, wlen_st0, wlim_st0, wmax_st0, _, hfc_st0_p, hfc_st0_len, hfc_st0_lim, hfc_st0_max⟩ :=
    lookupCode_four_words_any_dhi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_decode_bytes_list hl_st0
  obtain ⟨heff_cp_st0, heff_step_st0, w_st0a, w_st0b, rfl, _, _, _, _, _⟩ :=
    decode_bytes_list_body_returns (heff39.locals_clock fc_st0 (m39.clock - 1))
      hfc_st0_p hfc_st0_len hfc_st0_lim hfc_st0_max hc_st0
  let m40 := setVarHOLFinite (ofString "st0") (.rStruct [.val (.word w_st0a), .val (.word w_st0b)]) { cp_st0 with locals := m39.locals }
  have heff40 : WorldEff entry m40 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff_cp_st0.locals_clock _ _
  have hm40_st0 : m40.locals.lookup (ofString "st0") = some (.rStruct [.val (.word w_st0a), .val (.word w_st0b)]) :=
    lookup_setVar_eq _ _ _
  have hm40_si : m40.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m40]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm39_si
  have hm40_hp_ge : globN cp_rq "heap_ptr" ≤ globN m40 "heap_ptr" := by
    have h1 := heff_step_st0.hp_lo
    change globN m39 "heap_ptr" ≤ globN cp_st0 "heap_ptr" at h1
    change globN cp_rq "heap_ptr" ≤ globN cp_st0 "heap_ptr"; omega
  obtain ⟨m41, _, _, hm41_loc, hm41_glob, heff41, _, hm41_ne, hk41⟩ :=
    seq_store_fresh_returned heff40 (ofString "si") w_si 96 40 hm40_si hsi_lo
      (by have := heff_step_rq.hp_lo; change globN m28 "heap_ptr" ≤ _ at this; omega) (by omega) _
      (eval_rfield_word m40 0 (ofString "st0") w_st0a w_st0b hm40_st0 (Or.inl rfl)) hk40
  obtain ⟨m42, _, _, hm42_loc, hm42_glob, heff42, _, hm42_ne, hk42⟩ :=
    seq_store_fresh_returned heff41 (ofString "si") w_si 96 48 (by rw [hm41_loc]; exact hm40_si) hsi_lo
      (by have : globN m41 "heap_ptr" = globN m40 "heap_ptr" := by unfold globN; rw [hm41_glob]
          have := heff_step_rq.hp_lo; change globN m28 "heap_ptr" ≤ _ at this; omega) (by omega) _
      (eval_rfield_word m41 1 (ofString "st0") w_st0a w_st0b (by rw [hm41_loc]; exact hm40_st0) (Or.inr rfl)) hk41
  have hm42_hp : globN m42 "heap_ptr" = globN cp_st0 "heap_ptr" := by
    unfold globN; rw [hm42_glob, hm41_glob]; rfl
  have hm42_si : m42.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm42_loc, hm41_loc]; exact hm40_si
  obtain ⟨vals_cd, fc_cd, rv_cd, cp_cd, post_cd, _, hl_cd, _, hc_cd, _, _, hk43, hpost_cd⟩ :=
    decCall_returned_split heff42.code lookup_decode_bytes_list hk42
  obtain ⟨wp_cd, wlen_cd, wlim_cd, wmax_cd, _, hfc_cd_p, hfc_cd_len, hfc_cd_lim, hfc_cd_max⟩ :=
    lookupCode_four_words_any_dhi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_decode_bytes_list hl_cd
  obtain ⟨heff_cp_cd, heff_step_cd, w_cda, w_cdb, rfl, _, _, _, _, _⟩ :=
    decode_bytes_list_body_returns (heff42.locals_clock fc_cd (m42.clock - 1))
      hfc_cd_p hfc_cd_len hfc_cd_lim hfc_cd_max hc_cd
  let m43 := setVarHOLFinite (ofString "cd") (.rStruct [.val (.word w_cda), .val (.word w_cdb)]) { cp_cd with locals := m42.locals }
  have heff43 : WorldEff entry m43 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff_cp_cd.locals_clock _ _
  have hm43_cd : m43.locals.lookup (ofString "cd") = some (.rStruct [.val (.word w_cda), .val (.word w_cdb)]) :=
    lookup_setVar_eq _ _ _
  have hm43_si : m43.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m43]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm42_si
  have hm43_hp_ge : globN cp_st0 "heap_ptr" ≤ globN m43 "heap_ptr" := by
    have h1 := heff_step_cd.hp_lo
    change globN m42 "heap_ptr" ≤ globN cp_cd "heap_ptr" at h1
    change globN cp_st0 "heap_ptr" ≤ globN cp_cd "heap_ptr"; omega
  obtain ⟨m44, _, _, hm44_loc, hm44_glob, heff44, _, hm44_ne, hk44⟩ :=
    seq_store_fresh_returned heff43 (ofString "si") w_si 96 56 hm43_si hsi_lo
      (by have := heff_step_rq.hp_lo; change globN m28 "heap_ptr" ≤ _ at this; omega) (by omega) _
      (eval_rfield_word m43 0 (ofString "cd") w_cda w_cdb hm43_cd (Or.inl rfl)) hk43
  obtain ⟨m45, _, _, hm45_loc, hm45_glob, heff45, _, hm45_ne, hk45⟩ :=
    seq_store_fresh_returned heff44 (ofString "si") w_si 96 64 (by rw [hm44_loc]; exact hm43_si) hsi_lo
      (by have : globN m44 "heap_ptr" = globN m43 "heap_ptr" := by unfold globN; rw [hm44_glob]
          have := heff_step_rq.hp_lo; change globN m28 "heap_ptr" ≤ _ at this; omega) (by omega) _
      (eval_rfield_word m44 1 (ofString "cd") w_cda w_cdb (by rw [hm44_loc]; exact hm43_cd) (Or.inr rfl)) hk44
  have hm45_hp : globN m45 "heap_ptr" = globN cp_cd "heap_ptr" := by
    unfold globN; rw [hm45_glob, hm44_glob]; rfl
  have hm45_si : m45.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm45_loc, hm44_loc]; exact hm43_si
  obtain ⟨vals_hd, fc_hd, rv_hd, cp_hd, post_hd, _, hl_hd, _, hc_hd, _, _, hk46, hpost_hd⟩ :=
    decCall_returned_split heff45.code lookup_decode_bytes_list hk45
  obtain ⟨wp_hd, wlen_hd, wlim_hd, wmax_hd, _, hfc_hd_p, hfc_hd_len, hfc_hd_lim, hfc_hd_max⟩ :=
    lookupCode_four_words_any_dhi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_decode_bytes_list hl_hd
  obtain ⟨heff_cp_hd, heff_step_hd, w_hda, w_hdb, rfl, _, _, _, _, _⟩ :=
    decode_bytes_list_body_returns (heff45.locals_clock fc_hd (m45.clock - 1))
      hfc_hd_p hfc_hd_len hfc_hd_lim hfc_hd_max hc_hd
  let m46 := setVarHOLFinite (ofString "hd") (.rStruct [.val (.word w_hda), .val (.word w_hdb)]) { cp_hd with locals := m45.locals }
  have heff46 : WorldEff entry m46 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff_cp_hd.locals_clock _ _
  have hm46_hd : m46.locals.lookup (ofString "hd") = some (.rStruct [.val (.word w_hda), .val (.word w_hdb)]) :=
    lookup_setVar_eq _ _ _
  have hm46_si : m46.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m46]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm45_si
  have hm46_hp_ge : globN cp_cd "heap_ptr" ≤ globN m46 "heap_ptr" := by
    have h1 := heff_step_hd.hp_lo
    change globN m45 "heap_ptr" ≤ globN cp_hd "heap_ptr" at h1
    change globN cp_cd "heap_ptr" ≤ globN cp_hd "heap_ptr"; omega
  obtain ⟨m47, _, _, hm47_loc, hm47_glob, heff47, _, hm47_ne, hk47⟩ :=
    seq_store_fresh_returned heff46 (ofString "si") w_si 96 72 hm46_si hsi_lo
      (by have := heff_step_rq.hp_lo; change globN m28 "heap_ptr" ≤ _ at this; omega) (by omega) _
      (eval_rfield_word m46 0 (ofString "hd") w_hda w_hdb hm46_hd (Or.inl rfl)) hk46
  obtain ⟨m48, _, _, hm48_loc, hm48_glob, heff48, _, hm48_ne, hk48⟩ :=
    seq_store_fresh_returned heff47 (ofString "si") w_si 96 80 (by rw [hm47_loc]; exact hm46_si) hsi_lo
      (by have : globN m47 "heap_ptr" = globN m46 "heap_ptr" := by unfold globN; rw [hm47_glob]
          have := heff_step_rq.hp_lo; change globN m28 "heap_ptr" ≤ _ at this; omega) (by omega) _
      (eval_rfield_word m47 1 (ofString "hd") w_hda w_hdb (by rw [hm47_loc]; exact hm46_hd) (Or.inr rfl)) hk47
  have hm48_si : m48.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm48_loc, hm47_loc]; exact hm46_si
  rw [evaluateHOLFiniteState_return] at hk48
  simp [evalHOLExact, toExact, hm48_si, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hk48
  obtain ⟨hrv_eq, hm48_post⟩ := hk48
  have hpost_mem : post.memory = m48.memory := by
    rw [hpost_onpr, hpost_owit, hpost_si, hpost_np, hpost_nlen, hpost_opl, hpost_ovh, hpost_orq,
        hpost_pl, hpost_nvh, hpost_rq, hpost_wpw, hpost_wlenw, hpost_i3, hpost_w0, hpost_w1, hpost_w2,
        hpost_st0, hpost_cd, hpost_hd, ← hm48_post]
    rfl
  have hpost_memW : ∀ a, memW post a = memW m48 a := fun a => by unfold memW; rw [hpost_mem]
  have hm45_46_keep : ∀ a, a % 8 = 0 → globN entry "heap_ptr" ≤ a → a + 8 ≤ globN cp_cd "heap_ptr" → memW m46 a = memW m45 a :=
    fun a hal hlo hhi => by
      change memW cp_hd a = memW m45 a
      have hr := dhiOffsRegions_eq_of_worldEff heff45
      have hstep : WorldEff m45 cp_hd (dhiOffsRegions m45) ([] : List (String × Nat)) dhiGw := by
        rw [hr]
        exact (WorldEff.refl m45 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw heff45.arena heff45.code).trans_noBuf
          ((WorldEff.refl m45 _ _ _ heff45.arena heff45.code).locals_clock fc_hd (m45.clock - 1) |>.trans_noBuf
            heff_step_hd (by intro _ h; cases h) dhi_no_gb)
          (by intro _ h; cases h) dhi_no_gb
      exact worldEff_dhi_keeps_heap_memW_ok hOK_entry heff45 hstep hal hlo (by rw [hm45_hp]; exact hhi)
  have hm42_43_keep : ∀ a, a % 8 = 0 → globN entry "heap_ptr" ≤ a → a + 8 ≤ globN cp_st0 "heap_ptr" → memW m43 a = memW m42 a :=
    fun a hal hlo hhi => by
      change memW cp_cd a = memW m42 a
      have hr := dhiOffsRegions_eq_of_worldEff heff42
      have hstep : WorldEff m42 cp_cd (dhiOffsRegions m42) ([] : List (String × Nat)) dhiGw := by
        rw [hr]
        exact ((WorldEff.refl m42 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw heff42.arena heff42.code).locals_clock
          fc_cd (m42.clock - 1)).trans_noBuf heff_step_cd (by intro _ h; cases h) dhi_no_gb
      exact worldEff_dhi_keeps_heap_memW_ok hOK_entry heff42 hstep hal hlo (by rw [hm42_hp]; exact hhi)
  have hm39_40_keep : ∀ a, a % 8 = 0 → globN entry "heap_ptr" ≤ a → a + 8 ≤ globN m39 "heap_ptr" → memW m40 a = memW m39 a :=
    fun a hal hlo hhi => by
      change memW cp_st0 a = memW m39 a
      have hr := dhiOffsRegions_eq_of_worldEff heff39
      have hstep : WorldEff m39 cp_st0 (dhiOffsRegions m39) ([] : List (String × Nat)) dhiGw := by
        rw [hr]
        exact ((WorldEff.refl m39 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw heff39.arena heff39.code).locals_clock
          fc_st0 (m39.clock - 1)).trans_noBuf heff_step_st0 (by intro _ h; cases h) dhi_no_gb
      exact worldEff_dhi_keeps_heap_memW_ok hOK_entry heff39 hstep hal hlo hhi
  have hm30_39_keep : ∀ a, a % 8 = 0 → globN entry "heap_ptr" ≤ a → a + 8 ≤ globN cp_rq "heap_ptr" → memW m39 a = memW m30 a :=
    fun a hal hlo hhi =>
      worldEff_dhi_keeps_heap_memW_ok hOK_entry heff30 hm30_39_eff hal hlo (by rw [hm30_hp]; exact hhi)
  have hm28_29_keep : ∀ a, a % 8 = 0 → globN entry "heap_ptr" ≤ a → a + 8 ≤ globN cp_pl "heap_ptr" → memW m29 a = memW m28 a :=
    fun a hal hlo hhi => by
      change memW cp_rq a = memW m28 a
      have hstep : WorldEff m28 cp_rq (dhiOffsRegions m28) ([] : List (String × Nat)) dhiGw :=
        ((WorldEff.refl m28 (dhiOffsRegions m28) ([] : List (String × Nat)) dhiGw heff28.arena heff28.code).locals_clock
          fc_rq (m28.clock - 1)).trans_noBuf heff_step_rq (by intro _ h; cases h) dhi_no_gb
      exact worldEff_dhi_keeps_heap_memW_ok hOK_entry heff28 hstep hal hlo (by rw [hm28_hp]; exact hhi)
  have hsi_lt_cp_pl : w_si.toNat + 96 ≤ globN cp_pl "heap_ptr" := by omega
  have hcp_pl_le_rq : globN cp_pl "heap_ptr" ≤ globN cp_rq "heap_ptr" := by
    have h := heff_step_rq.hp_lo
    change globN m28 "heap_ptr" ≤ globN cp_rq "heap_ptr" at h
    omega
  have hcp_rq_le_st0 : globN cp_rq "heap_ptr" ≤ globN cp_st0 "heap_ptr" := by
    change globN cp_rq "heap_ptr" ≤ globN m40 "heap_ptr"; exact hm40_hp_ge
  have hcp_st0_le_cd : globN cp_st0 "heap_ptr" ≤ globN cp_cd "heap_ptr" := by
    change globN cp_st0 "heap_ptr" ≤ globN m43 "heap_ptr"; exact hm43_hp_ge
  have hcp_cd_le_hd : globN cp_cd "heap_ptr" ≤ globN cp_hd "heap_ptr" := by
    change globN cp_cd "heap_ptr" ≤ globN m46 "heap_ptr"; exact hm46_hp_ge
  have hpost_si0 : memW post w_si.toNat = w_pl.toNat := by
    have hm25_24 : ∀ a, memW m25 a = memW m24 a := fun a => by unfold memW; rw [hm25_mem]
    rw [hpost_memW, hm48_ne _ (by omega) (by omega), hm47_ne _ (by omega) (by omega),
        hm45_46_keep _ (by omega) (by omega) (by omega), hm45_ne _ (by omega) (by omega), hm44_ne _ (by omega) (by omega),
        hm42_43_keep _ (by omega) (by omega) (by omega), hm42_ne _ (by omega) (by omega), hm41_ne _ (by omega) (by omega),
        hm39_40_keep _ (by omega) (by omega) (by omega), hm30_39_keep _ (by omega) (by omega) (by omega), hm30_ne _ (by omega) (by omega),
        hm28_29_keep _ (by omega) (by omega) (by omega), hm28_ne _ (by omega) (by omega), hm27_ne _ (by omega) (by omega),
        hm26_ne _ (by omega) (by omega), hm25_24, hm24_si0]
  have hkeep_after_rq : ∀ a, a % 8 = 0 → w_si.toNat + 96 ≤ a → a + 8 ≤ globN cp_rq "heap_ptr" → memW post a = memW m30 a := by
    intro a hal ha_lo ha_hi
    rw [hpost_memW, hm48_ne _ (by omega) (by omega), hm47_ne _ (by omega) (by omega),
        hm45_46_keep _ hal (by omega) (by omega), hm45_ne _ (by omega) (by omega), hm44_ne _ (by omega) (by omega),
        hm42_43_keep _ hal (by omega) (by omega), hm42_ne _ (by omega) (by omega), hm41_ne _ (by omega) (by omega),
        hm39_40_keep _ hal (by omega) (by omega), hm30_39_keep _ hal (by omega) ha_hi]
  have hkeep_after_pl : ∀ a, a % 8 = 0 → w_si.toNat + 96 ≤ a → a + 8 ≤ globN cp_pl "heap_ptr" → memW post a = memW cp_pl a := by
    intro a hal ha_lo ha_hi
    have hm25_24 : ∀ x, memW m25 x = memW m24 x := fun x => by unfold memW; rw [hm25_mem]
    rw [hkeep_after_rq a hal ha_lo (by omega), hm30_ne _ (by omega) (by omega),
        hm28_29_keep _ hal (by omega) ha_hi, hm28_ne _ (by omega) (by omega), hm27_ne _ (by omega) (by omega),
        hm26_ne _ (by omega) (by omega), hm25_24, hm24_ne _ (by omega) (by omega)]
    rfl
  have hpl_32_eq : memW post (w_pl.toNat + 32) = memW cp_pl (w_pl.toNat + 32) :=
    hkeep_after_pl _ (by omega) (by omega) (by omega)
  have hpl_40_eq : memW post (w_pl.toNat + 40) = memW cp_pl (w_pl.toNat + 40) :=
    hkeep_after_pl _ (by omega) (by omega) (by omega)
  refine ⟨w_si, hrv_eq.symm, fun j hj => ?_⟩
  rw [hpost_si0, hpl_40_eq] at hj
  rw [hpost_si0, hpl_32_eq]
  rcases htx_cases_cp with ⟨hc0, _⟩ | ⟨_, _, _, htx_hi_cp, hpl_tx_lo, htx_sl_cp⟩
  · omega
  · obtain ⟨o, ho1, ho2⟩ := htx_sl_cp j hj
    have e1 := hkeep_after_pl (memW cp_pl (w_pl.toNat + 32) + 16 * j) (by omega) (by omega) (by omega)
    have e2 := hkeep_after_pl (memW cp_pl (w_pl.toNat + 32) + 16 * j + 8) (by omega) (by omega) (by omega)
    rw [e1, e2]
    exact slice_rebase_npr wp0 wlen0 w_onpr w_owit w_opl w_ovh _ _ o hlen0_ge2
      honpr_chain.2.1 (by omega) hnpr_chain.2.1 (by omega) ho1 ho2

/-! ### `decode_host_input`: every transaction slice is `WitnessSliceOK` -/

theorem decode_host_input_body_returns_tx_slices {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {rv : ValueHOL 64}
    (hWOK : WorldOK s)
    (heff : WorldEff s s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw)
    (hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input) =
      (some (.returned rv), post)) :
    ∃ (w_si : BitVec 64),
      rv = .val (.word w_si) ∧
      ∀ j, j < memW post (memW post w_si.toNat + 40) →
        WitnessSliceOK post (memW post (memW post w_si.toNat + 32) + 16 * j) := by
  have hOK := dhiOffsOK_of_worldOK hWOK
  have hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have hrun0 := hrun
  dsimp only [Guest.Software.guestFn_decode_host_input, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  obtain ⟨m1, hm1_pre, hk1⟩ := seq_returned_split (call0_noret_dhi s _ _) hrun
  have heff1 : WorldEff s m1 (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw :=
    worldEff_of_none_dhi hm1_pre (fun hnt_a hcr_a =>
      worldEff_call0_eff heff _ _ _ _ _ lookup_precheck_host_ssz_header
        (fun callee _ _ _ hnt_c hres_c => worldEff_precheck_host_ssz_header_body hWOK (heff.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
        hnt_a hcr_a)
  obtain ⟨vals_inp, fc_inp, rv_inp, cp_inp, post_inp, _, _, _, hc_inp, _, _, hk2, hpost_inp⟩ :=
    decCall_returned_split heff1.code lookup_input_blob hk1
  obtain ⟨heff_cp_inp, _, wp_inp, wlen_inp, rfl, hinp_len, hinp_sb, _, _, _, hinp_hi⟩ :=
    input_blob_body_returns_heap (heff1.locals_clock fc_inp (m1.clock - 1)) hc_inp
  let m2 := setVarHOLFinite (ofString "inp") (.rStruct [.val (.word wp_inp), .val (.word wlen_inp)]) { cp_inp with locals := m1.locals }
  have heff2 : WorldEff s m2 (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw := heff_cp_inp.locals_clock _ _
  obtain ⟨vals_dsi, fc_dsi, cp_dsi, hargs_dsi, hl_dsi, _, hc_dsi, _, hpost_dsi⟩ :=
    tailCall_returned_split heff2.code lookup_decode_stateless_input hk2
  obtain ⟨wp_d, wlen_d, hvs_dsi, hfc_d_p, hfc_d_len⟩ :=
    lookupCode_two_words_any_dhi (by decide) lookup_decode_stateless_input hl_dsi
  have hm2_inp : m2.locals.lookup (ofString "inp") =
      some (.rStruct [.val (.word wp_inp), .val (.word wlen_inp)]) := lookup_setVar_eq _ _ _
  have hargs_dsi_eq := evalList_two_rfields m2 _ _ _ _ hm2_inp hargs_dsi
  rw [hargs_dsi_eq] at hvs_dsi
  injection hvs_dsi with h1 htl; injection htl with h2 _
  injection h1 with h1'; injection h1' with hp_d_eq; subst hp_d_eq
  injection h2 with h2'; injection h2' with hlen_d_eq; subst hlen_d_eq
  obtain ⟨heff_s_cp, heff_step_dsi, w_si, rfl, hcells_cp, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    decode_stateless_input_body_returns_slices hOK (heff2.locals_clock fc_dsi (m2.clock - 1)) hfc_d_p hfc_d_len hc_dsi
  obtain ⟨w_si', hsi'_eq, hsl_tx⟩ :=
    decode_stateless_input_body_returns_tx_slices hOK (heff2.locals_clock fc_dsi (m2.clock - 1)) hfc_d_p hfc_d_len hc_dsi
  injection hsi'_eq with hsi'_eq'; injection hsi'_eq' with hsi'_eq''; subst hsi'_eq''
  have hpost_mem : post.memory = cp_dsi.memory := by
    rw [hpost_inp, hpost_dsi]; rfl
  have hpost_glob : post.globals = cp_dsi.globals := by
    rw [hpost_inp, hpost_dsi]; rfl
  have hpost_ma : post.memaddrs = cp_dsi.memaddrs := by
    rw [hpost_inp, hpost_dsi]; rfl
  have hpost_hp : globN post "heap_ptr" = globN cp_dsi "heap_ptr" := by unfold globN; rw [hpost_glob]
  have hpost_memW : ∀ a, memW post a = memW cp_dsi a := fun a => by unfold memW; rw [hpost_mem]
  have hwordAt_eq : ∀ a, WordAt post a ↔ WordAt cp_dsi a := fun a => by
    unfold WordAt; rw [hpost_ma, hpost_mem]
  have hwok_eq : ∀ iv, WordsOK post iv ↔ WordsOK cp_dsi iv := fun iv => by
    simp only [WordsOK, hwordAt_eq]
  have hstep_hp : globN cp_inp "heap_ptr" ≤ globN cp_dsi "heap_ptr" := heff_step_dsi.hp_lo
  have hcp_lim : globN cp_dsi "heap_ptr" ≤ heapLimit := heff_s_cp.arena.2.2.1
  have hhl : heapLimit < 2 ^ 64 := by decide
  refine ⟨w_si, rfl, fun j hj => ?_⟩
  rw [hpost_memW, hpost_memW] at hj
  rw [hpost_memW, hpost_memW]
  have hmem : (memW cp_dsi (memW cp_dsi w_si.toNat + 32), 16 * memW cp_dsi (memW cp_dsi w_si.toNat + 40)) ∈
      runAttemptCells cp_dsi w_si.toNat := by simp [runAttemptCells]
  obtain ⟨_, hins, hwok⟩ := hcells_cp _ hmem
  rcases hins with ⟨_, h0⟩ | ⟨hlo, hhi⟩
  · exfalso
    change 16 * memW cp_dsi (memW cp_dsi w_si.toNat + 40) = 0 at h0
    omega
  · change globN cp_inp "heap_ptr" ≤ _ at hlo
    change _ + 16 * _ ≤ globN cp_dsi "heap_ptr" at hhi
    exact witnessSliceOK_of_slice post
      (memW cp_dsi (memW cp_dsi w_si.toNat + 32))
      (memW cp_dsi (memW cp_dsi w_si.toNat + 40))
      wp_inp.toNat wlen_inp.toNat j ((hwok_eq _).2 hwok)
      (by omega) (by rw [hpost_hp]; exact hhi) hinp_sb (by rw [hpost_hp]; omega) (by rw [hpost_hp]; omega)
      (by omega) hj (by simpa only [hpost_memW] using hsl_tx j hj)

/-- The transaction-slice post of `decode_host_input`: from a `WorldOK` state,
a returned word `w` has every transaction slice (`pl + 32` / `pl + 40`, where
`pl = memW post w.toNat`) satisfying `WitnessSliceOK` in the exit state. -/
abbrev WdtxLeaf : Prop :=
  FunSpec WorldOK
    (fun _ r post => ∀ w : BitVec 64, r = some (.returned (.val (.word w))) →
      ∀ j, j < memW post (memW post w.toNat + 40) →
        WitnessSliceOK post (memW post (memW post w.toNat + 32) + 16 * j))
    (ofString "decode_host_input")

theorem wdtx_of_decode : WdtxLeaf := by
  refine ⟨_, _, _, lookup_decode_host_input, fun {F} s hc hWOK _ _ w hr => ?_⟩
  have heff0 : WorldEff s s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw :=
    WorldEff.refl s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw hWOK.1 hc
  have hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input) =
      (some (.returned (.val (.word w))), (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2) :=
    Prod.ext hr rfl
  obtain ⟨w_si, hw_eq, htx⟩ := decode_host_input_body_returns_tx_slices hWOK heff0 hrun
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  exact htx

end InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeSlicesR32
