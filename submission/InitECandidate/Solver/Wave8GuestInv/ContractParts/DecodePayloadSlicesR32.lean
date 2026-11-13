import InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeStatelessSlicesR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.MainEntryWitR32

/-!
# `decode_payload`: where the transaction slices point (R32)

Replay of `WkDecodeHostInputTop.decode_payload_body_returns` with a stronger
post: every slice of the transaction array (`pl + 32`, count `pl + 40`) lies
inside the payload region `[p, p + len)` the function was called on.  Then
threaded through `decode_stateless_input` and `decode_host_input` to prove
`wdtx_of_decode`: when `decode_host_input` returns `word w` from a `WorldOK`
state, every transaction slice `memW post (memW post w.toNat + 32) + 16 * j`
(`j < memW post (memW post w.toNat + 40)`) satisfies `WitnessSliceOK post`.
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

/-- A slice inside the sub-list `[p + o_txs, p + o_txs + (o_wd - o_txs))` of
the payload region `[p, p + len)` is a slice inside the payload region. -/
theorem slice_rebase_payload (wp wlen w_otx w_owd : BitVec 64) (m ln o : Nat)
    (hotx_le : w_otx.toNat ≤ w_owd.toNat)
    (howd_le : w_owd.toNat ≤ wlen.toNat)
    (hm : m = ((wp + w_otx).toNat + o) % 2 ^ 64)
    (hl : o + ln ≤ (w_owd - w_otx).toNat) :
    ∃ o' : Nat, m = (wp.toNat + o') % 2 ^ 64 ∧ o' + ln ≤ wlen.toNat := by
  have hsub : (w_owd - w_otx).toNat = w_owd.toNat - w_otx.toNat :=
    BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; exact hotx_le)
  refine ⟨w_otx.toNat + o, ?_, by omega⟩
  rw [hm]
  simp only [BitVec.toNat_add]
  omega

/-- A slice inside the payload `[p + 2 + o_npr + o_pl, … + (o_vh - o_pl))` of
the input region `[p, p + len)` is a slice inside the input region. -/
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
    BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; exact hopl)
  refine ⟨2 + w_onpr.toNat + w_opl.toNat + o, ?_, by omega⟩
  rw [hm]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

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

/-! ### `decode_payload`: transaction slice bounds -/

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
        w_pl.toNat + 136 ≤ memW post (w_pl.toNat + 32))) ∧
      (∀ j, j < memW post (w_pl.toNat + 40) →
        ∃ o : Nat, memW post (memW post (w_pl.toNat + 32) + 16 * j) = (wp.toNat + o) % 2 ^ 64 ∧
          o + memW post (memW post (w_pl.toNat + 32) + 16 * j + 8) ≤ wlen.toNat) := by
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
  -- Next: decCall "txs" ssz_split_var_list [p + o_txs, o_wd - o_txs, 2^63 - 1]
  obtain ⟨vals_tx, fc_tx, crv_tx, cp_tx, post_tx, hargs_tx, hl_tx, _, hc_tx, hsh_tx, _, hk17, hpost_tx⟩ :=
    decCall_returned_split heff16.code lookup_ssz_split_var_list hk16
  obtain ⟨w_tx_p, w_tx_len, w_tx_lim, hvs_tx, hfc_tx_p, hfc_tx_len, hfc_tx_lim⟩ :=
    lookupCode_three_words_any_dhi (by decide) (by decide) (by decide) lookup_ssz_split_var_list hl_tx
  have hm16_p : m16.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm16_loc_eq]; exact hm8_p
  have hm16_otx : m16.locals.lookup (ofString "o_txs") = some (.val (.word w_otx)) := by rw [hm16_loc_eq]; exact hm8_otx
  have hm16_owd : m16.locals.lookup (ofString "o_wd") = some (.val (.word w_owd)) := by rw [hm16_loc_eq]; exact hm8_owd
  have htx_p_eq : w_tx_p = wp + w_otx := by
    rw [evalListHOLFinite_eq_toExact] at hargs_tx
    simp only [evalListHOLExact, evalHOLExact, toExact, hm16_p, hm16_otx, hm16_owd,
      wordOpHOL, wordOp, valueIsWord, valueWord, Option.map_some] at hargs_tx
    rw [hvs_tx] at hargs_tx
    injection hargs_tx with hlist
    injection hlist with h1 _
    injection h1 with h1'; injection h1' with h1''; exact h1''.symm
  have htx_len_eq : w_tx_len = w_owd - w_otx := by
    rw [evalListHOLFinite_eq_toExact] at hargs_tx
    simp only [evalListHOLExact, evalHOLExact, toExact, hm16_p, hm16_otx, hm16_owd,
      wordOpHOL, wordOp, valueIsWord, valueWord, Option.map_some] at hargs_tx
    rw [hvs_tx] at hargs_tx
    injection hargs_tx with hlist
    injection hlist with _ ht1
    injection ht1 with h2 _
    injection h2 with h2'; injection h2' with h2''; exact h2''.symm
  have htx_len_lt : w_tx_len.toNat < 2 ^ 32 := by
    rw [htx_len_eq, BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; exact hotx_le_owd)]
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
  -- Preserve pl+24 across ssz_split_var_list (ssz_split_var_list has Rl = []!)
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
  -- Next: decCall "nwd" ssz_fixed_list_count [o_bal - o_wd, 44, 2^63 - 1]
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
  -- Stores to pl + {48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128}, then return pl!
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
      (eval_op_word s9 _ ⟨_, _, rfl⟩) hks10
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
    by omega, heff_entry_post.arena.2.2.1, hwok_pl_post, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rcases htx_cases with ⟨hc0, ha0, _⟩ | ⟨hc1, htxp_sb, htxp_lo_m16, htxp_hi_cp, _, _, _⟩
    · exact Or.inl ⟨hc0, ha0⟩
    · have h16_lo : w_pl.toNat + 136 ≤ w_txp.toNat := by
        change globN m16 "heap_ptr" ≤ w_txp.toNat at htxp_lo_m16; omega
      exact Or.inr ⟨hc1, htxp_sb, by omega, by omega, h16_lo⟩
  · intro j hj
    rw [hpost_pl40] at hj
    rw [hpost_pl32]
    rcases htx_cases with ⟨hc0, _, _⟩ | ⟨_, htxp_sb, htxp_lo_m16, htxp_hi_cp, hcp_lim, _, hsl⟩
    · omega
    · have h16_lo : w_pl.toNat + 136 ≤ w_txp.toNat := by
        change globN m16 "heap_ptr" ≤ w_txp.toNat at htxp_lo_m16; omega
      obtain ⟨o, ho1, ho2⟩ := hsl j hj
      have e1 : memW post (w_txp.toNat + 16 * j) = memW cp_tx (w_txp.toNat + 16 * j) := by
        rw [hpost_memW_s11, hs11_keep_m19 _ (by omega) (Or.inr (by omega)),
            hm19_ne _ (by omega) (by omega), hm18_ne _ (by omega) (by omega)]
        rfl
      have e2 : memW post (w_txp.toNat + 16 * j + 8) = memW cp_tx (w_txp.toNat + 16 * j + 8) := by
        rw [hpost_memW_s11, hs11_keep_m19 _ (by omega) (Or.inr (by omega)),
            hm19_ne _ (by omega) (by omega), hm18_ne _ (by omega) (by omega)]
        rfl
      rw [e1, e2]
      rw [htx_p_eq] at ho1
      rw [htx_len_eq] at ho2
      exact slice_rebase_payload wp wlen w_otx w_owd _ _ o hotx_le_owd (by omega) ho1 ho2

end InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeSlicesR32
