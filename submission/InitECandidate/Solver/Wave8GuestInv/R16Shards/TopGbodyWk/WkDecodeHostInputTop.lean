import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDecodeHostInputRet
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyRunAttempt

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

theorem dhiOffsRegions_eq_of_worldEff {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s cur Rl B dhiGw) :
    dhiOffsRegions cur = dhiOffsRegions s := by
  have hg := globN_eq_of_lookup (heff.gw_kept (ofString "ssz_offs") (by decide))
  simp [dhiOffsRegions, hg]

theorem assign_local_returned_split {F : Type}
    {cur post : PanSemStateFiniteExact 64 F} {nm : MlS} {valExp : ExpHOL 64}
    {cont : ProgHOL 64} {rv : ValueHOL 64}
    (hrun : evaluateHOLFiniteState cur (.seq (.assign .local nm valExp) cont) = (some (.returned rv), post)) :
    ∃ v mid,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v ∧
      mid.memory = cur.memory ∧
      mid.globals = cur.globals ∧
      mid.code = cur.code ∧
      mid.memaddrs = cur.memaddrs ∧
      mid.locals = cur.locals.update (nm, v) ∧
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
      refine ⟨v, setKvarHOLFinite .local nm v cur, rfl, rfl, rfl, rfl, rfl, ?_, hk⟩
      simp [setKvarHOLFinite, setVarHOLFinite]
    · rw [if_neg hvalid] at hasg; simp at hasg

theorem decCall_ssz_fixed_list_count_returned {F : Type}
    {s cur post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s cur Rl B dhiGw)
    (nm : MlS) (lenExp : ExpHOL 64) (szVal limVal : BitVec 64)
    {cont : ProgHOL 64} {rv : ValueHOL 64}
    {wlen : BitVec 64}
    (hlen_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) lenExp =
      some (.val (.word wlen)))
    (hrun : evaluateHOLFiniteState cur
      (.decCall nm .one (ofString "ssz_fixed_list_count") [lenExp, .const szVal, .const limVal] cont) =
      (some (.returned rv), post)) :
    ∃ (qw : BitVec 64) (mid post0 : PanSemStateFiniteExact 64 F),
      0 < szVal.toNat ∧
      qw.toNat * szVal.toNat = wlen.toNat ∧
      qw.toNat ≤ limVal.toNat ∧
      mid.memory = cur.memory ∧
      mid.globals = cur.globals ∧
      mid.locals = cur.locals.update (nm, .val (.word qw)) ∧
      WorldEff s mid Rl B dhiGw ∧
      evaluateHOLFiniteState mid cont = (some (.returned rv), post0) ∧
      post = { post0 with locals := HolFiniteMapExact.resVarEq post0.locals (nm, cur.locals.lookup nm) } := by
  have hnt_dc : (evaluateHOLFiniteState cur
      (.decCall nm .one (ofString "ssz_fixed_list_count") [lenExp, .const szVal, .const limVal] cont)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  obtain ⟨vals, fc, crv, cp, post0, hargs, hl, _, hc, hsh1, _, hk, hpost⟩ :=
    decCall_returned_split heff.code lookup_ssz_fixed_list_count_dhi hrun
  obtain ⟨w1, w2, w3, hvs_eq, hfc_len, hfc_sz, hfc_lim⟩ :=
    lookupCode_three_words_any_dhi (by decide) (by decide) (by decide) lookup_ssz_fixed_list_count_dhi hl
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, evalHOLExact, hlen_ev, Option.map_some] at hargs
  rw [hvs_eq] at hargs
  injection hargs with hlist
  injection hlist with hw1 ht1
  injection hw1 with hw1'; injection hw1' with hw1''; subst hw1''
  injection ht1 with hw2 ht2
  injection hw2 with hw2'; injection hw2' with hw2''; subst hw2''
  injection ht2 with hw3 _
  injection hw3 with hw3'; injection hw3' with hw3''; subst hw3''
  let ent := callEntryStateHOLFinite cur fc
  have hent_G : GuestInv ent := guestInv_callEntry cur fc heff.arena.1
  obtain ⟨hsz_pos, qw, hcrv_eq, hmul_eq, hqw_le⟩ :=
    ssz_fixed_list_count_body_returns ent wlen szVal limVal heff.code hent_G hfc_len hfc_sz hfc_lim crv cp hc
  subst hcrv_eq
  obtain ⟨params', body', ret', hlook_ro, hspec_ro⟩ := ro_ssz_fixed_list_count
  have hsame_ro : body' = sourceFnBody Guest.Software.guestFn_ssz_fixed_list_count ∧ ret' = .one := by
    rw [lookup_ssz_fixed_list_count_dhi] at hlook_ro
    injection hlook_ro with h'; injection h' with _ h2; injection h2 with hb hr
    exact ⟨hb.symm, hr.symm⟩
  rcases hsame_ro with ⟨rfl, rfl⟩
  have hentryEq : ent = { cur with locals := fc, clock := ent.clock } := by cases cur; rfl
  have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ssz_fixed_list_count") vs =
      some (sourceFnBody Guest.Software.guestFn_ssz_fixed_list_count, ent.locals, .one) :=
    ⟨vals, hl⟩
  have hro := hspec_ro ent heff.code hent_G hex (by dsimp only [ent]; rw [hc]; simp)
    (by dsimp only [ent]; rw [hc]; exact Or.inl ⟨.val (.word qw), rfl⟩)
  dsimp only [ent] at hro; rw [hc] at hro; dsimp only at hro
  have hcp_eq : cp = { cur with locals := cp.locals, clock := cp.clock } :=
    InitECandidate.Solver.Wave8GuestInv.R13.state_trans_locals_clock hentryEq hro
  let mid := setVarHOLFinite nm (.val (.word qw)) { cp with locals := cur.locals }
  have hmid_mem : mid.memory = cur.memory := by dsimp only [mid, setVarHOLFinite]; rw [hcp_eq]
  have hmid_glob : mid.globals = cur.globals := by dsimp only [mid, setVarHOLFinite]; rw [hcp_eq]
  have heff_mid : WorldEff s mid Rl B dhiGw := by
    dsimp only [mid]; rw [hcp_eq]; exact heff.locals_clock _ _
  exact ⟨qw, mid, post0, hsz_pos, hmul_eq, hqw_le, hmid_mem, hmid_glob, rfl, heff_mid, hk, hpost⟩

theorem call0_ssz_check_offsets_returned {F : Type}
    {s cur post : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s cur (dhiOffsRegions s) B dhiGw)
    (nVal fixedVal : BitVec 64) (lenExp : ExpHOL 64)
    {cont : ProgHOL 64} {rv : ValueHOL 64}
    {wlen : BitVec 64}
    (hn_pos : 0 < nVal.toNat) (hn_lt : nVal.toNat ≤ 8)
    (hlen_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) lenExp =
      some (.val (.word wlen)))
    (hrun : evaluateHOLFiniteState cur
      (.seq (.call (some (none, none)) (ofString "ssz_check_offsets")
        [.var .global (ofString "ssz_offs"), .const nVal, .const fixedVal, lenExp]) cont) =
      (some (.returned rv), post)) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.memory = cur.memory ∧
      mid.globals = cur.globals ∧
      mid.locals = cur.locals ∧
      WorldEff s mid (dhiOffsRegions s) B dhiGw ∧
      memW cur (globN s "ssz_offs") = fixedVal.toNat ∧
      (∀ j : Nat, j < nVal.toNat →
        fixedVal.toNat ≤ memW cur (globN s "ssz_offs" + j * 8) ∧
        memW cur (globN s "ssz_offs" + j * 8) ≤ wlen.toNat) ∧
      (∀ j : Nat, j + 1 < nVal.toNat →
        memW cur (globN s "ssz_offs" + j * 8) ≤ memW cur (globN s "ssz_offs" + (j + 1) * 8)) ∧
      evaluateHOLFiniteState mid cont = (some (.returned rv), post) := by
  obtain ⟨mid, hcall, hk⟩ := seq_returned_split (call0_noret_dhi cur _ _) hrun
  have hg_kept := heff.gw_kept (ofString "ssz_offs") (by decide)
  obtain ⟨sw, hsw_s⟩ := hWOK.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
  have hsw_cur : cur.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
    hg_kept.symm.trans hsw_s
  have hglob : globN s "ssz_offs" = sw.toNat := by unfold GlobalWord at hsw_s; simp [globN, hsw_s]
  obtain ⟨vals, fc, crv, cpost, hargs, hl, _, hc, _, hmid_eq⟩ :=
    call0_returned_split heff.code lookup_ssz_check_offsets_dhi hcall
  obtain ⟨w1, w2, w3, w4, hvs_eq, hfc_offs, hfc_n, hfc_fix, hfc_len⟩ :=
    lookupCode_four_words_any_dhi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_ssz_check_offsets_dhi hl
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, evalHOLExact, toExact, hsw_cur, hlen_ev, Option.map_some] at hargs
  rw [hvs_eq] at hargs
  injection hargs with hlist
  injection hlist with hw1 ht1; injection hw1 with hw1'; injection hw1' with hw1''; subst hw1''
  injection ht1 with hw2 ht2; injection hw2 with hw2'; injection hw2' with hw2''; subst hw2''
  injection ht2 with hw3 ht3; injection hw3 with hw3'; injection hw3' with hw3''; subst hw3''
  injection ht3 with hw4 _; injection hw4 with hw4'; injection hw4' with hw4''; subst hw4''
  have hsw_hi : sw.toNat + nVal.toNat * 8 ≤ 2 ^ 64 := by
    have hOK := dhiOffsOK_of_worldOK hWOK
    have hhe : heapEnd < 2 ^ 64 := by decide
    rcases hOK.2 with hg0 | ⟨_, hhi, _, _⟩ <;> omega
  let ent := callEntryStateHOLFinite cur fc
  obtain ⟨_, hm0, hbounds, hmono⟩ :=
    ssz_check_offsets_body_returns ent sw nVal fixedVal wlen heff.code hfc_offs hfc_n hfc_fix hfc_len
      hn_pos (by omega) hsw_hi crv cpost hc
  obtain ⟨params', body', ret', hlook_ro, hspec_ro⟩ := ro_ssz_check_offsets_local
  have hsame_ro : body' = sourceFnBody Guest.Software.guestFn_ssz_check_offsets ∧ ret' = .one := by
    rw [lookup_ssz_check_offsets_dhi] at hlook_ro
    injection hlook_ro with h'; injection h' with _ h2; injection h2 with hb hr
    exact ⟨hb.symm, hr.symm⟩
  rcases hsame_ro with ⟨rfl, rfl⟩
  have hentryEq : ent = { cur with locals := fc, clock := ent.clock } := by cases cur; rfl
  have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ssz_check_offsets") vs =
      some (sourceFnBody Guest.Software.guestFn_ssz_check_offsets, ent.locals, .one) :=
    ⟨vals, hl⟩
  have hro := hspec_ro ent heff.code (guestInv_callEntry cur fc heff.arena.1) hex
    (by dsimp only [ent]; rw [hc]; simp)
    (by dsimp only [ent]; rw [hc]; exact Or.inl ⟨crv, rfl⟩)
  dsimp only [ent] at hro; rw [hc] at hro; dsimp only at hro
  have hcpost_eq : cpost = { cur with locals := cpost.locals, clock := cpost.clock } :=
    InitECandidate.Solver.Wave8GuestInv.R13.state_trans_locals_clock hentryEq hro
  have hmid_cur : mid = { cur with clock := mid.clock } := by
    rw [hmid_eq, hcpost_eq]; cases cur; rfl
  have heff_mid : WorldEff s mid (dhiOffsRegions s) B dhiGw := by
    rw [hmid_cur]; exact heff.locals_clock _ _
  have hent_memW : ∀ a, memW ent a = memW cur a := fun _ => rfl
  rw [← hglob] at hm0 hbounds hmono
  refine ⟨mid, by rw [hmid_cur], by rw [hmid_cur], by rw [hmid_cur], heff_mid,
    by simpa [hent_memW] using hm0,
    fun j hj => by simpa [hent_memW] using hbounds j hj,
    fun j hj => by simpa [hent_memW] using hmono j hj,
    hk⟩

theorem worldEff_seq_store_ssz_offs_const_ok {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
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
    (fun _ _ => worldEff_store_ssz_offs_const_ok hOK heff off hoff dst valExp hdst hword)
    (fun mid hmid heff_m hnt_c hcr_c => hcont mid (store_keeps_locals cur mid dst valExp hmid) heff_m hnt_c hcr_c)

theorem worldEff_decode_payload_body_ok {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    {wp wlen : BitVec 64}
    (hOK : DhiOffsOK s)
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
  refine worldEff_seq_store_ssz_offs_const_ok hOK (heff4.locals_clock _ _) 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
    (eval_var_local_word m8 _ w_oex hm8_oex) hnt8 hcr8 (fun m9 hm9_loc heff9 hnt9 hcr9 => ?_)
  refine worldEff_seq_store_ssz_offs_const_ok hOK heff9 8 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m9 _ w_otx (by rw [hm9_loc]; exact hm8_otx)) hnt9 hcr9 (fun m10 hm10_loc heff10 hnt10 hcr10 => ?_)
  refine worldEff_seq_store_ssz_offs_const_ok hOK heff10 16 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m10 _ w_owd (by rw [hm10_loc, hm9_loc]; exact hm8_owd)) hnt10 hcr10 (fun m11 hm11_loc heff11 hnt11 hcr11 => ?_)
  refine worldEff_seq_store_ssz_offs_const_ok hOK heff11 24 (by omega) _ _ (Or.inr rfl)
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
  have hm17_txs : m17.locals.lookup (ofString "txs") = some (.rStruct [.val (.word w_txp), .val (.word w_ntx)]) := lookup_setVar_eq _ _ _
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

theorem worldEff_decode_requests_body_ok {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
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
        (fun _ _ => worldEff_store_ssz_offs_dyn_ok hOK heff_t _ _ (wi * 8#64)
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

theorem call0_ssz_check_offsets_returned_ok {F : Type}
    {s cur post : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
    (heff : WorldEff s cur (dhiOffsRegions s) B dhiGw)
    (nVal fixedVal : BitVec 64) (lenExp : ExpHOL 64)
    {cont : ProgHOL 64} {rv : ValueHOL 64}
    {wlen : BitVec 64}
    (hn_pos : 0 < nVal.toNat) (hn_lt : nVal.toNat ≤ 8)
    (hlen_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) lenExp =
      some (.val (.word wlen)))
    (hrun : evaluateHOLFiniteState cur
      (.seq (.call (some (none, none)) (ofString "ssz_check_offsets")
        [.var .global (ofString "ssz_offs"), .const nVal, .const fixedVal, lenExp]) cont) =
      (some (.returned rv), post)) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.memory = cur.memory ∧
      mid.globals = cur.globals ∧
      mid.locals = cur.locals ∧
      WorldEff s mid (dhiOffsRegions s) B dhiGw ∧
      memW cur (globN s "ssz_offs") = fixedVal.toNat ∧
      (∀ j : Nat, j < nVal.toNat →
        fixedVal.toNat ≤ memW cur (globN s "ssz_offs" + j * 8) ∧
        memW cur (globN s "ssz_offs" + j * 8) ≤ wlen.toNat) ∧
      (∀ j : Nat, j + 1 < nVal.toNat →
        memW cur (globN s "ssz_offs" + j * 8) ≤ memW cur (globN s "ssz_offs" + (j + 1) * 8)) ∧
      evaluateHOLFiniteState mid cont = (some (.returned rv), post) := by
  obtain ⟨mid, hcall, hk⟩ := seq_returned_split (call0_noret_dhi cur _ _) hrun
  have hg_kept := heff.gw_kept (ofString "ssz_offs") (by decide)
  obtain ⟨sw, hsw_s⟩ := hOK.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
  have hsw_cur : cur.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
    hg_kept.symm.trans hsw_s
  have hglob : globN s "ssz_offs" = sw.toNat := by unfold GlobalWord at hsw_s; simp [globN, hsw_s]
  obtain ⟨vals, fc, crv, cpost, hargs, hl, _, hc, _, hmid_eq⟩ :=
    call0_returned_split heff.code lookup_ssz_check_offsets_dhi hcall
  obtain ⟨w1, w2, w3, w4, hvs_eq, hfc_offs, hfc_n, hfc_fix, hfc_len⟩ :=
    lookupCode_four_words_any_dhi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_ssz_check_offsets_dhi hl
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, evalHOLExact, toExact, hsw_cur, hlen_ev, Option.map_some] at hargs
  rw [hvs_eq] at hargs
  injection hargs with hlist
  injection hlist with hw1 ht1; injection hw1 with hw1'; injection hw1' with hw1''; subst hw1''
  injection ht1 with hw2 ht2; injection hw2 with hw2'; injection hw2' with hw2''; subst hw2''
  injection ht2 with hw3 ht3; injection hw3 with hw3'; injection hw3' with hw3''; subst hw3''
  injection ht3 with hw4 _; injection hw4 with hw4'; injection hw4' with hw4''; subst hw4''
  have hsw_hi : sw.toNat + nVal.toNat * 8 ≤ 2 ^ 64 := by
    have hhe : heapEnd < 2 ^ 64 := by decide
    rcases hOK.2 with hg0 | ⟨_, hhi, _, _⟩ <;> omega
  let ent := callEntryStateHOLFinite cur fc
  obtain ⟨_, hm0, hbounds, hmono⟩ :=
    ssz_check_offsets_body_returns ent sw nVal fixedVal wlen heff.code hfc_offs hfc_n hfc_fix hfc_len
      hn_pos (by omega) hsw_hi crv cpost hc
  obtain ⟨params', body', ret', hlook_ro, hspec_ro⟩ := ro_ssz_check_offsets_local
  have hsame_ro : body' = sourceFnBody Guest.Software.guestFn_ssz_check_offsets ∧ ret' = .one := by
    rw [lookup_ssz_check_offsets_dhi] at hlook_ro
    injection hlook_ro with h'; injection h' with _ h2; injection h2 with hb hr
    exact ⟨hb.symm, hr.symm⟩
  rcases hsame_ro with ⟨rfl, rfl⟩
  have hentryEq : ent = { cur with locals := fc, clock := ent.clock } := by cases cur; rfl
  have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ssz_check_offsets") vs =
      some (sourceFnBody Guest.Software.guestFn_ssz_check_offsets, ent.locals, .one) :=
    ⟨vals, hl⟩
  have hro := hspec_ro ent heff.code (guestInv_callEntry cur fc heff.arena.1) hex
    (by dsimp only [ent]; rw [hc]; simp)
    (by dsimp only [ent]; rw [hc]; exact Or.inl ⟨crv, rfl⟩)
  dsimp only [ent] at hro; rw [hc] at hro; dsimp only at hro
  have hcpost_eq : cpost = { cur with locals := cpost.locals, clock := cpost.clock } :=
    InitECandidate.Solver.Wave8GuestInv.R13.state_trans_locals_clock hentryEq hro
  have hmid_cur : mid = { cur with clock := mid.clock } := by
    rw [hmid_eq, hcpost_eq]; cases cur; rfl
  have heff_mid : WorldEff s mid (dhiOffsRegions s) B dhiGw := by
    rw [hmid_cur]; exact heff.locals_clock _ _
  have hent_memW : ∀ a, memW ent a = memW cur a := fun _ => rfl
  rw [← hglob] at hm0 hbounds hmono
  refine ⟨mid, by rw [hmid_cur], by rw [hmid_cur], by rw [hmid_cur], heff_mid,
    by simpa [hent_memW] using hm0,
    fun j hj => by simpa [hent_memW] using hbounds j hj,
    fun j hj => by simpa [hent_memW] using hmono j hj,
    hk⟩

theorem seq_store_ssz_offs_const_returned_ok {F : Type}
    {s cur post : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
    (heff : WorldEff s cur (dhiOffsRegions s) B dhiGw)
    (off : Nat) (hoff : off + 8 ≤ 64)
    (dst valExp : ExpHOL 64) {cont : ProgHOL 64} {rv : ValueHOL 64}
    (hdst : (dst = .var .global (ofString "ssz_offs") ∧ off = 0) ∨
            dst = .op .add [.var .global (ofString "ssz_offs"), .const (BitVec.ofNat 64 off)])
    (hword : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hrun : evaluateHOLFiniteState cur (.seq (.store dst valExp) cont) = (some (.returned rv), post)) :
    ∃ (mid : PanSemStateFiniteExact 64 F) (vw : BitVec 64),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some (.val (.word vw)) ∧
      mid.locals = cur.locals ∧
      mid.globals = cur.globals ∧
      WorldEff s mid (dhiOffsRegions s) B dhiGw ∧
      memW mid (globN s "ssz_offs" + off) = vw.toNat ∧
      (∀ y : Nat, y < 2 ^ 64 → y ≠ globN s "ssz_offs" + off → memW mid y = memW cur y) ∧
      evaluateHOLFiniteState mid cont = (some (.returned rv), post) := by
  obtain ⟨mid, hst, hk⟩ := seq_returned_split (store_noret_dhi cur _ _) hrun
  have heff_m : WorldEff s mid (dhiOffsRegions s) B dhiGw := by
    have h1 := worldEff_store_ssz_offs_const_ok hOK heff off hoff dst valExp hdst hword
    rwa [hst] at h1
  have hg_kept := heff.gw_kept (ofString "ssz_offs") (by decide)
  obtain ⟨sw, hsw_s⟩ := hOK.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
  have hsw_cur : cur.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
    hg_kept.symm.trans hsw_s
  have hglob : globN s "ssz_offs" = sw.toNat := by unfold GlobalWord at hsw_s; simp [globN, hsw_s]
  have hdst_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dst =
      some (.val (.word (sw + BitVec.ofNat 64 off))) := by
    rcases hdst with ⟨rfl, rfl⟩ | rfl
    · simp [evalHOLExact, toExact, hsw_cur]
    · simp [evalHOLExact, evalListHOLExact, toExact, hsw_cur, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨xw, vw, hdst', hval_ev, hloc, hglob_eq, _, _, hm_eq, hm_ne⟩ :=
    store_none_evals cur mid dst valExp hst ⟨_, hdst_ev⟩ hword
  rw [hdst_ev] at hdst'
  injection hdst' with h1; injection h1 with h2; injection h2 with hxw_eq
  subst hxw_eq
  rcases hOK.2 with hg0 | ⟨hlo, hhi, _, _⟩
  · exfalso
    rw [evaluateHOLFiniteState_store] at hst
    rcases hval_ev' : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp with _ | vv
    · simp [hdst_ev, hval_ev'] at hst
    · obtain ⟨vw', rfl⟩ := hword vv hval_ev'
      simp only [hdst_ev, hval_ev', flattenHOL, panMemStoresHOL, panMemStoreHOL] at hst
      have hsw0 : sw = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
      subst hsw0
      have hndom : ¬ cur.memaddrs (0#64 + BitVec.ofNat 64 off) := by
        rw [heff.memaddrs, hOK.1.1.memaddrs, ordinaryDomain_iff]
        have hsb : 64 < sourceBase := by decide
        have h1 : (0#64 + BitVec.ofNat 64 off).toNat = off := by simp [BitVec.toNat_ofNat]; omega
        omega
      rw [if_neg hndom] at hst
      simp at hst
  · have hhe : heapEnd < 2 ^ 64 := by decide
    have hx_nat : (sw + BitVec.ofNat 64 off).toNat = globN s "ssz_offs" + off := by
      rw [BitVec.toNat_add_of_lt]
      · simp [hglob, BitVec.toNat_ofNat]; omega
      · simp [BitVec.toNat_ofNat]; omega
    rw [hx_nat] at hm_eq hm_ne
    exact ⟨mid, vw, hval_ev, hloc, hglob_eq, heff_m, hm_eq, hm_ne, hk⟩

theorem load_ssz_offs_const_eval {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
    (heff : WorldEff s cur Rl B dhiGw)
    (off : Nat) (hoff8 : off % 8 = 0) (hoff : off + 8 ≤ 64)
    (addrExp : ExpHOL 64)
    (haddr : (addrExp = .var .global (ofString "ssz_offs") ∧ off = 0) ∨
             addrExp = .op .add [.var .global (ofString "ssz_offs"), .const (BitVec.ofNat 64 off)])
    {v : ValueHOL 64}
    (hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) (.load .one addrExp) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memW cur (globN s "ssz_offs" + off) := by
  have hg_kept := heff.gw_kept (ofString "ssz_offs") (by decide)
  obtain ⟨sw, hsw_s⟩ := hOK.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
  have hsw_cur : cur.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
    hg_kept.symm.trans hsw_s
  have hglob : globN s "ssz_offs" = sw.toNat := by unfold GlobalWord at hsw_s; simp [globN, hsw_s]
  have haddr_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) addrExp =
      some (.val (.word (sw + BitVec.ofNat 64 off))) := by
    rcases haddr with ⟨rfl, rfl⟩ | rfl
    · simp [evalHOLExact, toExact, hsw_cur]
    · simp [evalHOLExact, evalListHOLExact, toExact, hsw_cur, wordOpHOL, wordOp, valueIsWord, valueWord]
  rcases hOK.2 with hg0 | ⟨hlo, hhi, hmod, _⟩
  · exfalso
    have hsw0 : sw = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hsw0
    have hndom : ¬ cur.memaddrs (BitVec.ofNat 64 off) := by
      rw [heff.memaddrs, hOK.1.1.memaddrs, ordinaryDomain_iff]
      have hsb : 64 < sourceBase := by decide
      have h1 : (BitVec.ofNat 64 off).toNat = off := by simp [BitVec.toNat_ofNat]; omega
      omega
    simp [evalHOLExact, isWfShapeExactHOL, haddr_ev, memLoadHOLExact, hndom] at hv
  · have hhe : heapEnd < 2 ^ 64 := by decide
    have hx_nat : (sw + BitVec.ofNat 64 off).toNat = globN s "ssz_offs" + off := by
      rw [BitVec.toNat_add_of_lt]
      · simp [hglob, BitVec.toNat_ofNat]; omega
      · simp [BitVec.toNat_ofNat]; omega
    have hdom : cur.memaddrs (sw + BitVec.ofNat 64 off) := by
      rw [heff.memaddrs, hOK.1.1.memaddrs, ordinaryDomain_iff, hx_nat]
      exact ⟨by omega, by omega, by omega⟩
    cases hm : cur.memory (sw + BitVec.ofNat 64 off) with
    | word w =>
      simp [evalHOLExact, isWfShapeExactHOL, haddr_ev, memLoadHOLExact, hdom, hm, toExact] at hv
      subst hv
      refine ⟨w, rfl, ?_⟩
      unfold memW
      have hbv : BitVec.ofNat 64 (globN s "ssz_offs" + off) = sw + BitVec.ofNat 64 off := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hx_nat]
      rw [hbv, hm]

/-! ### `decode_payload` Return Postcondition -/

theorem decode_payload_body_returns {F : Type}
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
      (memW post (w_pl.toNat + 32)) % 8 = 0 ∧
      WordsOK post (memW post (w_pl.toNat + 32), 16 * memW post (w_pl.toNat + 40)) ∧
      ((memW post (w_pl.toNat + 40) = 0 ∧ memW post (w_pl.toNat + 32) = 0) ∨
       (1 ≤ memW post (w_pl.toNat + 40) ∧
        sourceBase ≤ memW post (w_pl.toNat + 32) ∧
        globN entry "heap_ptr" ≤ memW post (w_pl.toNat + 32) ∧
        memW post (w_pl.toNat + 32) + 16 * memW post (w_pl.toNat + 40) ≤ globN post "heap_ptr" ∧
        w_pl.toNat + 136 ≤ memW post (w_pl.toNat + 32))) ∧
      memW post (w_pl.toNat + 56) < 2 ^ 32 := by
  -- (R32 amendment) the `pl + 56` withdrawal count bound: `pl + 56` stores
  -- `nwd = ssz_fixed_list_count (o_bal - o_wd, 44, 2^63 - 1)` and the span is
  -- u32-bounded (`w_owd ≤ w_obl < 2^32`), so the count is `< 2^32`. Required
  -- by `MainEntryR32.hdhi_hoare_r32` (the `nwd` conjunct of `InputAtR32`).
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
  have howd_le_obl : w_obl.toNat ≤ wlen.toNat := by
    have hb := (hchk_b 3 (by decide)).2
    simpa [hm12_24] using hb
  have howd_le_bal : w_owd.toNat ≤ w_obl.toNat := by
    have hm := hchk_m 2 (by decide)
    simpa [hm12_16, hm12_24] using hm
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
    ssz_split_var_list_body_returns heff_m16_ent_tx hfc_tx_p hfc_tx_len hfc_tx_lim hc_tx
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
  have hm20_pl : m20.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hm20_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm19_loc_eq, hm17_pl,
      show ofString "nwd" ≠ ofString "pl" by decide]
  have hm20_nwd : m20.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) := by
    rw [hm20_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  -- Stores to pl + {48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128}, then return pl!
  obtain ⟨s1, _, _, hl1, hg1, hs1, _, hne1, hks1⟩ :=
    seq_store_fresh_returned heff20 (ofString "pl") w_pl 136 48 hm20_pl hpl_lo (by omega) (by omega) _
      (eval_op_word m20 _ ⟨_, _, rfl⟩) hk20
  obtain ⟨s2, vw_nwd, hv_nwd_ev, hl2, hg2, hs2, hs2_pl56, hne2, hks2⟩ :=
    seq_store_fresh_returned hs1 (ofString "pl") w_pl 136 56 (by rw [hl1]; exact hm20_pl) hpl_lo (by omega) (by omega) _
      (eval_var_local_word s1 _ w_nwd (by rw [hl1]; exact hm20_nwd)) hks1
  have hvw_nwd : vw_nwd = w_nwd := by
    have h1' : s1.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) := by rw [hl1]; exact hm20_nwd
    simp [evalHOLExact, toExact, h1'] at hv_nwd_ev; exact hv_nwd_ev.symm
  rw [hvw_nwd] at hs2_pl56
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
        hne3 _ (by omega) (by omega)]
    exact hs2_pl56
  have hpost_hp_cp : globN post "heap_ptr" = globN cp_tx "heap_ptr" := by
    unfold globN; rw [hpost_glob]
  have hcp_hp_ge : w_pl.toNat + 136 ≤ globN cp_tx "heap_ptr" := by
    have h1 := heff_step_tx.hp_lo
    change globN m16 "heap_ptr" ≤ globN cp_tx "heap_ptr" at h1
    omega
  have hwok_pl_post : WordsOK post (w_pl.toNat, 136) :=
    wordsOK_preserved_of_worldEff heff_entry_post hpl_al (by omega) hpl_sb (by have := heff_entry_post.arena.2.2.1; omega)
  have hntx_lt32 : w_ntx.toNat < 2 ^ 32 := by omega
  have hnwd_lt32 : w_nwd.toNat < 2 ^ 32 := by
    have h44 : (44#64).toNat = 44 := by decide
    rw [h44] at hmul_nwd
    have hsub : (w_obl - w_owd).toNat = w_obl.toNat - w_owd.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr howd_le_bal)
    omega
  refine ⟨heff_s_post, heff_entry_post, w_pl, hrv_eq.symm, hpl_al, hpl_sb, hpl_lo,
    by omega, heff_entry_post.arena.2.2.1, hwok_pl_post, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- PayloadAt post w_pl.toNat
    refine ⟨hwok_pl_post, by rw [hpost_pl24]; exact hextra_le_32, by rw [hpost_pl40]; exact hntx_lt32, ?_⟩
    intro i hi
    rw [hpost_pl40] at hi
    rw [hpost_pl32]
    rcases htx_cases with ⟨hc0, _, _⟩ | ⟨_, htxp_sb, htxp_lo_m16, htxp_hi_cp, _, htx_el⟩
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
  · rw [hpost_pl32]; exact htxp_al
  · rw [hpost_pl32, hpost_pl40]
    rcases htx_cases with ⟨hc0, ha0, _⟩ | ⟨_, htxp_sb, _, htxp_hi_cp, hcp_lim, _⟩
    · refine ⟨by simp [ha0], by simp [hc0], fun k hk => by simp [hc0] at hk⟩
    · exact wordsOK_preserved_of_worldEff heff_entry_post htxp_al (by omega) htxp_sb (by omega)
  · rw [hpost_pl32, hpost_pl40]
    rcases htx_cases with ⟨hc0, ha0, _⟩ | ⟨hc1, htxp_sb, htxp_lo_m16, htxp_hi_cp, _, _⟩
    · exact Or.inl ⟨hc0, ha0⟩
    · have h16_lo : w_pl.toNat + 136 ≤ w_txp.toNat := by
        change globN m16 "heap_ptr" ≤ w_txp.toNat at htxp_lo_m16; omega
      exact Or.inr ⟨hc1, htxp_sb, by omega, by omega, h16_lo⟩
  · rw [hpost_pl56]; exact hnwd_lt32

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
