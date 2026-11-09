import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDecodeHostInputTop

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

/-! ### `DhiOffsOK` Heap Preservation & Call Splitters -/

theorem worldEff_dhi_keeps_heap_memW_ok {F : Type}
    {s cur next : PanSemStateFiniteExact 64 F}
    (hOK_s : DhiOffsOK s)
    (heff_s_cur : WorldEff s cur (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw)
    (heff_step : WorldEff cur next (dhiOffsRegions cur) ([] : List (String × Nat)) dhiGw)
    {addr : Nat}
    (hal8 : addr % 8 = 0)
    (hlo : globN s "heap_ptr" ≤ addr)
    (hhi : addr + 8 ≤ globN cur "heap_ptr") :
    memW next addr = memW cur addr := by
  have hcur_hp_lim : globN cur "heap_ptr" ≤ heapLimit := heff_s_cur.arena.2.2.1
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have ha_lt : addr < 2 ^ 64 := by omega
  have hbv_nat : (BitVec.ofNat 64 addr).toNat = addr := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hoff_eq : dhiOffsRegions cur = dhiOffsRegions s :=
    dhiOffsRegions_eq_of_worldEff heff_s_cur
  unfold memW
  by_cases hmem : next.memory (BitVec.ofNat 64 addr) = cur.memory (BitVec.ofNat 64 addr)
  · rw [hmem]
  · exfalso
    rcases heff_step.cell_frame (BitVec.ofNat 64 addr) hmem with ⟨iv, hiv, hpos, hc1, hc2⟩ | ⟨_, hgs, _⟩ | ⟨_, hfg1, _⟩ | ⟨_, hhf1, _⟩
    · rw [hoff_eq] at hiv
      simp only [dhiOffsRegions, List.mem_singleton] at hiv
      subst hiv
      rcases hOK_s.2 with hg0 | ⟨h_sb, _, _, hcases⟩
      · simp [hg0] at hpos
      · have hg_ne0 : globN s "ssz_offs" ≠ 0 := by
          have hsb : 0 < sourceBase := by decide
          omega
        simp only [hg_ne0, ↓reduceIte] at hc1 hc2
        have hlim_sc : heapLimit ≤ scratchStart := by decide
        rcases hcases with ⟨_, hhp⟩ | ⟨hsc, _⟩ <;> omega
    · cases hgs
    · dsimp only [freeGap] at hfg1
      have hfmp_lo : scratchStart ≤ globN cur "frame_mem_ptr" := heff_s_cur.arena.2.2.2.1
      have hlim_sc : heapLimit ≤ scratchStart := by decide
      omega
    · dsimp only [heapFree] at hhf1
      omega

theorem worldEff_of_none_dhi {F : Type}
    {s cur post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    {prog : ProgHOL 64}
    (hrun : evaluateHOLFiniteState cur prog = (none, post))
    (hstep : (evaluateHOLFiniteState cur prog).1 ≠ some .timeOut →
             ContOrRes (evaluateHOLFiniteState cur prog).1 →
             WorldEff s (evaluateHOLFiniteState cur prog).2 Rl B gw) :
    WorldEff s post Rl B gw := by
  have h := hstep (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl rfl)
  rwa [hrun] at h

/-! ### `worldOwned` Equality & Disjointness for `dhiGw = ["heap_ptr"]` -/

theorem fixedObjects_eq_of_worldEff_dhi {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {S Nd : List Nat}
    (hAs : ArenaReady s)
    (heff : WorldEff s post Rl ([] : List (String × Nat)) dhiGw)
    (hWT : WorldTypedWith s S Nd)
    (hDisjR : IvlsDisj Rl (worldTypedIvls s S Nd)) :
    fixedObjects post = fixedObjects s := by
  obtain ⟨hT, _, hF, _⟩ := hWT
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g hg => by
    unfold globN; rw [heff.gw_kept (ofString g) (dhi_core_out g hg)]
  have hdom_wr : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a :=
    heff.out_dom
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega),
     mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega)⟩
  let keep0 : List Ivl := Rl ++ [freeGap s]
  have hfr_pos : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ j ∈ keep0, CellHitsPos a.toNat j) ∨ CellHitsPos a.toNat (heapFree s) := by
    intro a hne
    rcases heff.cell_frame a hne with ⟨ivl, hivl, hhit⟩ | ⟨_, hgs, _⟩ | hfg | hhf
    · exact Or.inl ⟨ivl, List.mem_append_left _ hivl, hhit⟩
    · simp at hgs
    · exact Or.inl ⟨freeGap s, List.mem_append_right _ List.mem_cons_self, hfg⟩
    · exact Or.inr hhf
  have hu_wti_aligned : ∀ i ∈ worldTypedIvls s S Nd, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 →
      IvlUnhit s post i := by
    intro i hi hal hi1 hi2
    refine ivlUnhit_of_cellHitsPos hi1 hi2 hfr_pos (fun j hj => ?_) (disj_allocated_heapFree hAs.2 hal)
    simp only [keep0, List.mem_append, List.mem_singleton] at hj
    rcases hj with hjR | rfl
    · exact Disj.flip (hDisjR j hjR i hi)
    · exact disj_allocated_freeGap hAs.2 hal
  have hu_fix_wti : ∀ i ∈ worldTypedIvls s S Nd, i ∈ fixedObjects s → i.2 ≠ 0 → IvlUnhit s post i := by
    intro i hwti hfi hpos
    rcases hF.1 i hfi with h0 | ⟨hal, hw⟩
    · exact absurd h0 hpos
    · exact hu_wti_aligned i hwti hal hw.1 hw.2.1
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
    intro t ht i hi
    have hal := ((hT.2.1 t ht).2 i hi).1
    have hw := ((hT.2.1 t ht).1.1 i hi).2
    refine hu_wti_aligned i ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; left
    exact List.mem_flatMap.2 ⟨t, ht, hi⟩
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords]))
      (by simp)
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi h24 =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hpos =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
      (by omega)
  have hbo_eq := (blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst).1
  have hbal_eq := (balObjects_eq_of_unhit hAs.2 hT hF (hcore "bal_accounts" (by decide))
    hu_tab hu_bal hlow).1
  have hgb_eq : ∀ gn ∈ globalBuffers, globN post gn.1 = globN s gn.1 := fun gn hgn => by
    unfold globN; rw [heff.gw_kept (ofString gn.1) (dhi_no_gb gn hgn)]
  unfold fixedObjects
  rw [hbo_eq, hbal_eq, hcore "journal" (by decide), hcore "journal_cap" (by decide)]
  congr 3
  apply List.map_congr_left
  intro gn hgn
  simp [bufferRegion, hgb_eq gn hgn]

theorem disj_worldOwned_of_zero_or_fresh_dhi {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {S Nd : List Nat} {cells : List Ivl}
    (hAs : ArenaReady s)
    (heff : WorldEff s post Rl ([] : List (String × Nat)) dhiGw)
    (hWT : WorldTypedWith s S Nd)
    (hDisjR : IvlsDisj Rl (worldTypedIvls s S Nd))
    (hne_eq : nodeExtents post Nd = nodeExtents s Nd)
    (hfp_eq : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hcells : ∀ c ∈ cells, c.2 = 0 ∨ Inside c (globN s "heap_ptr") (globN post "heap_ptr")) :
    IvlsDisj cells (worldOwned post S Nd) := by
  have hfix_eq := fixedObjects_eq_of_worldEff_dhi hAs heff hWT hDisjR
  have htab_eq : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) :=
    List.flatMap_congr hfp_eq
  have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    rw [htab_eq, hfix_eq, hne_eq]
  rw [hwo_eq]
  intro c hc j hj
  rcases hcells c hc with hc0 | hin_c
  · exact Or.inl hc0
  · have hj_za : j.2 = 0 ∨ Allocated s j := by
      unfold worldOwned at hj
      rcases List.mem_append.1 hj with h1 | hnd
      · rcases List.mem_append.1 h1 with htab | hfix
        · obtain ⟨u, hu, hj_fp⟩ := List.mem_flatMap.1 htab
          exact Or.inr (((hWT.1.2.1 u hu).2 j hj_fp).1)
        · rcases hWT.2.2.1.1 j hfix with h0 | ⟨hal, _⟩
          · exact Or.inl h0
          · exact Or.inr hal
      · obtain ⟨n, hn, hj_n⟩ := List.mem_flatMap.1 hnd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_n
        rcases hj_n with rfl | rfl
        · exact Or.inr (hWT.2.2.2.1.1 n hn).2.1
        · unfold nodePath
          split
          · rename_i hcond
            rcases (hWT.2.2.2.1.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
            · exact absurd h0 hcond.2
            · exact Or.inr hal
          · exact Or.inl rfl
    rcases hj_za with hj0 | hal
    · exact Or.inr (Or.inl hj0)
    · rcases hal with ⟨_, hj2⟩ | ⟨hj1, _⟩
      · exact Or.inr (Or.inr (Or.inr (by dsimp [Inside] at hin_c; omega)))
      · have hp_lim := heff.arena.2.2.1
        have hs_fr := hAs.2.2.2.1
        have hs_gap := hAs.2.2.2.2.1
        have hsep : heapLimit ≤ scratchStart := by decide
        exact Or.inr (Or.inr (Or.inl (by dsimp [Inside] at hin_c; omega)))

/-! ### `decode_requests` Return Postcondition -/

theorem decode_requests_body_returns {F : Type}
    {s entry post : PanSemStateFiniteExact 64 F}
    {wp wlen : BitVec 64} {rv : ValueHOL 64}
    (hOK : DhiOffsOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word wp)))
    (hlen : entry.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hlen_lt : wlen.toNat < 2 ^ 32)
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_requests) =
      (some (.returned rv), post)) :
    WorldEff s post (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw ∧
    WorldEff entry post (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw ∧
    ∃ (w_rq : BitVec 64),
      rv = .val (.word w_rq) ∧
      w_rq.toNat % 8 = 0 ∧
      sourceBase ≤ w_rq.toNat ∧
      globN entry "heap_ptr" ≤ w_rq.toNat ∧
      w_rq.toNat + 80 ≤ globN post "heap_ptr" ∧
      globN post "heap_ptr" ≤ heapLimit ∧
      WordsOK post (w_rq.toNat, 80) ∧
      RequestsAt post w_rq.toNat := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_requests)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_requests)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have heff_s_post : WorldEff s post (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw := by
    have h := worldEff_decode_requests_body_ok hOK heff hnt hcr
    rwa [hrun] at h
  have hOK_entry : DhiOffsOK entry := dhiOffsOK_of_worldEff hOK heff
  have heff_entry_refl : WorldEff entry entry (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw :=
    WorldEff.refl entry (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw heff.arena heff.code
  have heff_entry_post : WorldEff entry post (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    have h := worldEff_decode_requests_body_ok hOK_entry heff_entry_refl hnt hcr
    rwa [hrun] at h
  dsimp only [Guest.Software.guestFn_decode_requests, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  obtain ⟨m1, hm1_ite, hk1⟩ := seq_returned_split (ite_call0_noret_dhi entry _ _ _) hrun
  obtain ⟨hm1_eq, _⟩ := ite_ssz_fail_keeps entry m1 heff.code _ _ hm1_ite
  have heff1 : WorldEff entry m1 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm1_eq]; exact heff_entry_refl.locals_clock _ _
  have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm1_eq]; exact hp
  have hm1_len : m1.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm1_eq]; exact hlen
  obtain ⟨v_i, post_i, hv_i, _, hk2, hpost_i⟩ := dec_returned_split hk1
  have hv_i_eq : v_i = .val (.word 0#64) := by simp [evalHOLExact] at hv_i; exact hv_i.symm
  subst hv_i_eq
  let m2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m1
  have heff2 : WorldEff entry m2 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw :=
    heff1.locals_clock _ _
  have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    dsimp only [m2]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm1_p
  have hm2_len : m2.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    dsimp only [m2]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm1_len
  obtain ⟨m3, hm3_w, hk3⟩ := seq_returned_split
    (while_noret_dhi m2 _ _ (fun u =>
      seq_noret_dhi u (store_noret_dhi u _ _) (fun u2 _ => assign_noret_dhi u2 _ _ _))) hk2
  let Inv5 : PanSemStateFiniteExact 64 F → Prop :=
    fun t => ∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧ wi.toNat ≤ 5
  have heff3 : WorldEff entry m3 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw :=
    worldEff_of_none_dhi hm3_w (fun hnt_w hcr_w =>
      worldEff_while_cond_dhi _ Inv5 (fun _ h => h)
        (fun t0 cw hcond hnz heff_t ⟨wi, ht_i, hwi_le⟩ hnt_b hcr_b => by
          have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
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
              (fun _ _ => worldEff_store_ssz_offs_dyn_ok hOK_entry heff_t _ _ (wi * 8#64)
                (by simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, decClockHOLFinite, ht0_i, valueIsWord, valueWord])
                (by omega) (eval_op_word (decClockHOLFinite t0) _ ⟨_, _, rfl⟩))
              (fun tb _ heff_tb _ _ => worldEff_assign_local heff_tb _ _)
          · exact evaluate_incTail_le (ofString "i") 5 (by decide) _ (by decide) (decClockHOLFinite t0) wi ht_i hwi_lt hf)
        m2.clock m2 rfl heff2 ⟨0#64, lookup_setVar_eq _ _ _, by decide⟩ hnt_w hcr_w)
  have hm3_p : m3.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    have hk := evaluate_keepLocal (ofString "p") _ (by decide) m2 (Or.inl (congrArg Prod.fst hm3_w))
    rw [hm3_w] at hk; rw [hk]; exact hm2_p
  have hm3_len : m3.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    have hk := evaluate_keepLocal (ofString "len") _ (by decide) m2 (Or.inl (congrArg Prod.fst hm3_w))
    rw [hm3_w] at hk; rw [hk]; exact hm2_len
  have hlen3_ev : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
      (.var .local (ofString "len")) = some (.val (.word wlen)) := by
    simp [evalHOLExact, toExact, hm3_len]
  obtain ⟨m4, hm4_mem, hm4_glob, hm4_loc, heff4, hm3_off0, hm3_bounds, hm3_mono, hk4⟩ :=
    call0_ssz_check_offsets_returned_ok hOK_entry heff3 5#64 20#64 (.var .local (ofString "len"))
      (by decide) (by decide) hlen3_ev hk3
  have hm4_p : m4.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm4_loc]; exact hm3_p
  have hm4_len : m4.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm4_loc]; exact hm3_len
  obtain ⟨w_rq, nw, m5, post_rq, hsz_ev, hm5_mem, hm5_loc, hm5_glob_ne, heff5,
    hrq_al, hrq_sb, hrq_lo, hrq_add, hhp5_hi, _, hk5, hpost_rq⟩ :=
    decCall_alloc_returned_split heff4 hk4
  have hnw80 : nw = 80#64 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hnw80
  have hrq_hp5 : globN m5 "heap_ptr" = w_rq.toNat + 80 := by
    have h1 : w_rq.toNat + 80 = globN m5 "heap_ptr" := by
      simpa [show (80#64 : BitVec 64).toNat = 80 from rfl] using hrq_add
    exact h1.symm
  have hm5_m3_memW : ∀ a, memW m5 a = memW m3 a := fun a => by
    unfold memW; rw [hm5_mem, hm4_mem]
  have hm5_rq : m5.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := by
    rw [hm5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm5_p : m5.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm4_p, show ofString "rq" ≠ ofString "p" by decide]
  have hm5_len : m5.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm4_len, show ofString "rq" ≠ ofString "len" by decide]
  obtain ⟨vo0, post_o0, hvo0, _, hk6, hpost_o0⟩ := dec_returned_split hk5
  obtain ⟨w_o0, rfl, hwo0_eq⟩ := load_ssz_offs_const_eval hOK_entry heff5 0 (by decide) (by decide) _ (Or.inl ⟨rfl, rfl⟩) hvo0
  simp only [Nat.add_zero] at hwo0_eq
  rw [hm5_m3_memW, hm3_off0] at hwo0_eq
  let m6 := setVarHOLFinite (ofString "o0") (.val (.word w_o0)) m5
  have heff6 : WorldEff entry m6 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff5.locals_clock _ _
  obtain ⟨vo1, post_o1, hvo1, _, hk7, hpost_o1⟩ := dec_returned_split hk6
  obtain ⟨w_o1, rfl, hwo1_eq⟩ := load_ssz_offs_const_eval hOK_entry heff6 8 (by decide) (by decide) _ (Or.inr rfl) hvo1
  have hm6_m5 : ∀ a, memW m6 a = memW m5 a := fun _ => rfl
  rw [hm6_m5, hm5_m3_memW] at hwo1_eq
  let m7 := setVarHOLFinite (ofString "o1") (.val (.word w_o1)) m6
  have heff7 : WorldEff entry m7 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff6.locals_clock _ _
  obtain ⟨vo2, post_o2, hvo2, _, hk8, hpost_o2⟩ := dec_returned_split hk7
  obtain ⟨w_o2, rfl, hwo2_eq⟩ := load_ssz_offs_const_eval hOK_entry heff7 16 (by decide) (by decide) _ (Or.inr rfl) hvo2
  have hm7_m5 : ∀ a, memW m7 a = memW m5 a := fun _ => rfl
  rw [hm7_m5, hm5_m3_memW] at hwo2_eq
  let m8 := setVarHOLFinite (ofString "o2") (.val (.word w_o2)) m7
  have heff8 : WorldEff entry m8 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff7.locals_clock _ _
  obtain ⟨vo3, post_o3, hvo3, _, hk9, hpost_o3⟩ := dec_returned_split hk8
  obtain ⟨w_o3, rfl, hwo3_eq⟩ := load_ssz_offs_const_eval hOK_entry heff8 24 (by decide) (by decide) _ (Or.inr rfl) hvo3
  have hm8_m5 : ∀ a, memW m8 a = memW m5 a := fun _ => rfl
  rw [hm8_m5, hm5_m3_memW] at hwo3_eq
  let m9 := setVarHOLFinite (ofString "o3") (.val (.word w_o3)) m8
  have heff9 : WorldEff entry m9 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff8.locals_clock _ _
  obtain ⟨vo4, post_o4, hvo4, _, hk10, hpost_o4⟩ := dec_returned_split hk9
  obtain ⟨w_o4, rfl, hwo4_eq⟩ := load_ssz_offs_const_eval hOK_entry heff9 32 (by decide) (by decide) _ (Or.inr rfl) hvo4
  have hm9_m5 : ∀ a, memW m9 a = memW m5 a := fun _ => rfl
  rw [hm9_m5, hm5_m3_memW] at hwo4_eq
  let m10 := setVarHOLFinite (ofString "o4") (.val (.word w_o4)) m9
  have heff10 : WorldEff entry m10 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff9.locals_clock _ _
  have hmono01 := hm3_mono 0 (by decide)
  have hmono12 := hm3_mono 1 (by decide)
  have hmono23 := hm3_mono 2 (by decide)
  have hmono34 := hm3_mono 3 (by decide)
  have hbnd4 := (hm3_bounds 4 (by decide)).2
  have hn8_0 : 0 * 8 = 0 ∧ (0 + 1) * 8 = 8 ∧ 1 * 8 = 8 ∧ (1 + 1) * 8 = 16 ∧
      2 * 8 = 16 ∧ (2 + 1) * 8 = 24 ∧ 3 * 8 = 24 ∧ (3 + 1) * 8 = 32 ∧ 4 * 8 = 32 := by decide
  rw [hn8_0.1, hn8_0.2.1, Nat.add_zero] at hmono01
  rw [hn8_0.2.2.1, hn8_0.2.2.2.1] at hmono12
  rw [hn8_0.2.2.2.2.1, hn8_0.2.2.2.2.2.1] at hmono23
  rw [hn8_0.2.2.2.2.2.2.1, hn8_0.2.2.2.2.2.2.2.1] at hmono34
  rw [hn8_0.2.2.2.2.2.2.2.2] at hbnd4
  have ho_chain : w_o0.toNat = 20 ∧ w_o0.toNat ≤ w_o1.toNat ∧ w_o1.toNat ≤ w_o2.toNat ∧
      w_o2.toNat ≤ w_o3.toNat ∧ w_o3.toNat ≤ w_o4.toNat ∧ w_o4.toNat ≤ wlen.toNat := by
    have h20 : (20#64 : BitVec 64).toNat = 20 := rfl
    omega
  have hm10_rq : m10.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := by
    dsimp only [m10, m9, m8, m7, m6]; iterate 5 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm5_rq
  have hm10_len : m10.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    dsimp only [m10, m9, m8, m7, m6]; iterate 5 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm5_len
  have hm10_o0 : m10.locals.lookup (ofString "o0") = some (.val (.word w_o0)) := by
    dsimp only [m10, m9, m8, m7, m6]; iterate 4 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm10_o1 : m10.locals.lookup (ofString "o1") = some (.val (.word w_o1)) := by
    dsimp only [m10, m9, m8, m7]; iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm10_o2 : m10.locals.lookup (ofString "o2") = some (.val (.word w_o2)) := by
    dsimp only [m10, m9, m8]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm10_o3 : m10.locals.lookup (ofString "o3") = some (.val (.word w_o3)) := by
    dsimp only [m10, m9]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
  have hm10_o4 : m10.locals.lookup (ofString "o4") = some (.val (.word w_o4)) :=
    lookup_setVar_eq _ _ _
  have hsub01_ev : @evalHOLExact 64 F _ m10.toExact (fun a => Classical.propDecidable (m10.memaddrs a))
      (.op .sub [.var .local (ofString "o1"), .var .local (ofString "o0")]) =
      some (.val (.word (w_o1 - w_o0))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm10_o1, hm10_o0, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨w_n0, q1, post_n0, _, hmul_n0, _, hq1_mem, hq1_glob, hq1_loc_def, heff_q1, hkn0, hpost_n0⟩ :=
    decCall_ssz_fixed_list_count_returned heff10 (ofString "n0") _ 192#64 9223372036854775807#64 hsub01_ev hk10
  have hn0_lt : w_n0.toNat * 192 < 2 ^ 36 := by
    have hsub : (w_o1 - w_o0).toNat = w_o1.toNat - w_o0.toNat :=
      BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
    rw [show (192#64 : BitVec 64).toNat = 192 from rfl, hsub] at hmul_n0
    omega
  have hq1_o1 : q1.locals.lookup (ofString "o1") = some (.val (.word w_o1)) := by
    rw [hq1_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_o1, show ofString "n0" ≠ ofString "o1" by decide]
  have hq1_o2 : q1.locals.lookup (ofString "o2") = some (.val (.word w_o2)) := by
    rw [hq1_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_o2, show ofString "n0" ≠ ofString "o2" by decide]
  have hsub12_ev : @evalHOLExact 64 F _ q1.toExact (fun a => Classical.propDecidable (q1.memaddrs a))
      (.op .sub [.var .local (ofString "o2"), .var .local (ofString "o1")]) =
      some (.val (.word (w_o2 - w_o1))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hq1_o2, hq1_o1, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨w_n1, q2, post_n1, _, hmul_n1, _, hq2_mem, hq2_glob, hq2_loc_def, heff_q2, hkn1, hpost_n1⟩ :=
    decCall_ssz_fixed_list_count_returned heff_q1 (ofString "n1") _ 76#64 9223372036854775807#64 hsub12_ev hkn0
  have hn1_lt : w_n1.toNat * 192 < 2 ^ 36 := by
    have hsub : (w_o2 - w_o1).toNat = w_o2.toNat - w_o1.toNat :=
      BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
    rw [show (76#64 : BitVec 64).toNat = 76 from rfl, hsub] at hmul_n1
    omega
  have hq2_o2 : q2.locals.lookup (ofString "o2") = some (.val (.word w_o2)) := by
    rw [hq2_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hq1_o2, show ofString "n1" ≠ ofString "o2" by decide]
  have hq2_o3 : q2.locals.lookup (ofString "o3") = some (.val (.word w_o3)) := by
    rw [hq2_loc_def, hq1_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_o3,
      show ofString "n1" ≠ ofString "o3" by decide, show ofString "n0" ≠ ofString "o3" by decide]
  have hsub23_ev : @evalHOLExact 64 F _ q2.toExact (fun a => Classical.propDecidable (q2.memaddrs a))
      (.op .sub [.var .local (ofString "o3"), .var .local (ofString "o2")]) =
      some (.val (.word (w_o3 - w_o2))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hq2_o3, hq2_o2, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨w_n2, q3, post_n2, _, hmul_n2, _, hq3_mem, hq3_glob, hq3_loc_def, heff_q3, hkn2, hpost_n2⟩ :=
    decCall_ssz_fixed_list_count_returned heff_q2 (ofString "n2") _ 116#64 9223372036854775807#64 hsub23_ev hkn1
  have hn2_lt : w_n2.toNat * 192 < 2 ^ 36 := by
    have hsub : (w_o3 - w_o2).toNat = w_o3.toNat - w_o2.toNat :=
      BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
    rw [show (116#64 : BitVec 64).toNat = 116 from rfl, hsub] at hmul_n2
    omega
  have hq3_o3 : q3.locals.lookup (ofString "o3") = some (.val (.word w_o3)) := by
    rw [hq3_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hq2_o3, show ofString "n2" ≠ ofString "o3" by decide]
  have hq3_o4 : q3.locals.lookup (ofString "o4") = some (.val (.word w_o4)) := by
    rw [hq3_loc_def, hq2_loc_def, hq1_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_o4,
      show ofString "n2" ≠ ofString "o4" by decide, show ofString "n1" ≠ ofString "o4" by decide,
      show ofString "n0" ≠ ofString "o4" by decide]
  have hsub34_ev : @evalHOLExact 64 F _ q3.toExact (fun a => Classical.propDecidable (q3.memaddrs a))
      (.op .sub [.var .local (ofString "o4"), .var .local (ofString "o3")]) =
      some (.val (.word (w_o4 - w_o3))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hq3_o4, hq3_o3, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨w_n3, q4, post_n3, _, hmul_n3, _, hq4_mem, hq4_glob, hq4_loc_def, heff_q4, hkn3, hpost_n3⟩ :=
    decCall_ssz_fixed_list_count_returned heff_q3 (ofString "n3") _ 184#64 9223372036854775807#64 hsub34_ev hkn2
  have hn3_lt : w_n3.toNat * 192 < 2 ^ 36 := by
    have hsub : (w_o4 - w_o3).toNat = w_o4.toNat - w_o3.toNat :=
      BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
    rw [show (184#64 : BitVec 64).toNat = 184 from rfl, hsub] at hmul_n3
    omega
  have hq4_o4 : q4.locals.lookup (ofString "o4") = some (.val (.word w_o4)) := by
    rw [hq4_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hq3_o4, show ofString "n3" ≠ ofString "o4" by decide]
  have hq4_len : q4.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hq4_loc_def, hq3_loc_def, hq2_loc_def, hq1_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_len,
      show ofString "n3" ≠ ofString "len" by decide, show ofString "n2" ≠ ofString "len" by decide,
      show ofString "n1" ≠ ofString "len" by decide, show ofString "n0" ≠ ofString "len" by decide]
  have hsub4l_ev : @evalHOLExact 64 F _ q4.toExact (fun a => Classical.propDecidable (q4.memaddrs a))
      (.op .sub [.var .local (ofString "len"), .var .local (ofString "o4")]) =
      some (.val (.word (wlen - w_o4))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hq4_len, hq4_o4, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨w_n4, q5, post_n4, _, hmul_n4, _, hq5_mem, hq5_glob, hq5_loc_def, heff_q5, hkn4, hpost_n4⟩ :=
    decCall_ssz_fixed_list_count_returned heff_q4 (ofString "n4") _ 68#64 9223372036854775807#64 hsub4l_ev hkn3
  have hn4_lt : w_n4.toNat * 192 < 2 ^ 36 := by
    have hsub : (wlen - w_o4).toNat = wlen.toNat - w_o4.toNat :=
      BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
    rw [show (68#64 : BitVec 64).toNat = 68 from rfl, hsub] at hmul_n4
    omega
  have hq5_rq : q5.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := by
    rw [hq5_loc_def, hq4_loc_def, hq3_loc_def, hq2_loc_def, hq1_loc_def]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_rq,
      show ofString "n4" ≠ ofString "rq" by decide, show ofString "n3" ≠ ofString "rq" by decide,
      show ofString "n2" ≠ ofString "rq" by decide, show ofString "n1" ≠ ofString "rq" by decide,
      show ofString "n0" ≠ ofString "rq" by decide]
  have hq5_n4 : q5.locals.lookup (ofString "n4") = some (.val (.word w_n4)) := by
    rw [hq5_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hq5_n3 : q5.locals.lookup (ofString "n3") = some (.val (.word w_n3)) := by
    rw [hq5_loc_def, hq4_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "n4" ≠ ofString "n3" by decide]
  have hq5_n2 : q5.locals.lookup (ofString "n2") = some (.val (.word w_n2)) := by
    rw [hq5_loc_def, hq4_loc_def, hq3_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n4" ≠ ofString "n2" by decide, show ofString "n3" ≠ ofString "n2" by decide]
  have hq5_n1 : q5.locals.lookup (ofString "n1") = some (.val (.word w_n1)) := by
    rw [hq5_loc_def, hq4_loc_def, hq3_loc_def, hq2_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n4" ≠ ofString "n1" by decide, show ofString "n3" ≠ ofString "n1" by decide,
      show ofString "n2" ≠ ofString "n1" by decide]
  have hq5_n0 : q5.locals.lookup (ofString "n0") = some (.val (.word w_n0)) := by
    rw [hq5_loc_def, hq4_loc_def, hq3_loc_def, hq2_loc_def, hq1_loc_def]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n4" ≠ ofString "n0" by decide, show ofString "n3" ≠ ofString "n0" by decide,
      show ofString "n2" ≠ ofString "n0" by decide, show ofString "n1" ≠ ofString "n0" by decide]
  obtain ⟨r1, _, _, hrl1, hrg1, hrs1, _, _, hkr1⟩ :=
    seq_store_fresh_returned heff_q5 (ofString "rq") w_rq 80 0 hq5_rq hrq_lo (by omega) (by omega) _
      (eval_op_word q5 _ ⟨_, _, rfl⟩) hkn4
  obtain ⟨r2, vn0, hvn0_ev, hrl2, hrg2, hrs2, hm_rq8, hne2, hkr2⟩ :=
    seq_store_fresh_returned hrs1 (ofString "rq") w_rq 80 8 (by rw [hrl1]; exact hq5_rq) hrq_lo (by omega) (by omega) _
      (fun v hv => by simp [evalHOLExact, toExact, hrl1, hq5_n0] at hv; exact ⟨_, hv.symm⟩) hkr1
  have hvn0 : vn0 = w_n0 := by simp [evalHOLExact, toExact, hrl1, hq5_n0] at hvn0_ev; exact hvn0_ev.symm
  rw [hvn0] at hm_rq8
  obtain ⟨r3, _, _, hrl3, hrg3, hrs3, _, hne3, hkr3⟩ :=
    seq_store_fresh_returned hrs2 (ofString "rq") w_rq 80 16 (by rw [hrl2, hrl1]; exact hq5_rq) hrq_lo (by omega) (by omega) _
      (eval_op_word r2 _ ⟨_, _, rfl⟩) hkr2
  obtain ⟨r4, vn1, hvn1_ev, hrl4, hrg4, hrs4, hm_rq24, hne4, hkr4⟩ :=
    seq_store_fresh_returned hrs3 (ofString "rq") w_rq 80 24 (by rw [hrl3, hrl2, hrl1]; exact hq5_rq) hrq_lo (by omega) (by omega) _
      (fun v hv => by simp [evalHOLExact, toExact, hrl3, hrl2, hrl1, hq5_n1] at hv; exact ⟨_, hv.symm⟩) hkr3
  have hvn1 : vn1 = w_n1 := by simp [evalHOLExact, toExact, hrl3, hrl2, hrl1, hq5_n1] at hvn1_ev; exact hvn1_ev.symm
  rw [hvn1] at hm_rq24
  obtain ⟨r5, _, _, hrl5, hrg5, hrs5, _, hne5, hkr5⟩ :=
    seq_store_fresh_returned hrs4 (ofString "rq") w_rq 80 32 (by rw [hrl4, hrl3, hrl2, hrl1]; exact hq5_rq) hrq_lo (by omega) (by omega) _
      (eval_op_word r4 _ ⟨_, _, rfl⟩) hkr4
  obtain ⟨r6, vn2, hvn2_ev, hrl6, hrg6, hrs6, hm_rq40, hne6, hkr6⟩ :=
    seq_store_fresh_returned hrs5 (ofString "rq") w_rq 80 40 (by rw [hrl5, hrl4, hrl3, hrl2, hrl1]; exact hq5_rq) hrq_lo (by omega) (by omega) _
      (fun v hv => by simp [evalHOLExact, toExact, hrl5, hrl4, hrl3, hrl2, hrl1, hq5_n2] at hv; exact ⟨_, hv.symm⟩) hkr5
  have hvn2 : vn2 = w_n2 := by simp [evalHOLExact, toExact, hrl5, hrl4, hrl3, hrl2, hrl1, hq5_n2] at hvn2_ev; exact hvn2_ev.symm
  rw [hvn2] at hm_rq40
  obtain ⟨r7, _, _, hrl7, hrg7, hrs7, _, hne7, hkr7⟩ :=
    seq_store_fresh_returned hrs6 (ofString "rq") w_rq 80 48 (by rw [hrl6, hrl5, hrl4, hrl3, hrl2, hrl1]; exact hq5_rq) hrq_lo (by omega) (by omega) _
      (eval_op_word r6 _ ⟨_, _, rfl⟩) hkr6
  obtain ⟨r8, vn3, hvn3_ev, hrl8, hrg8, hrs8, hm_rq56, hne8, hkr8⟩ :=
    seq_store_fresh_returned hrs7 (ofString "rq") w_rq 80 56 (by rw [hrl7, hrl6, hrl5, hrl4, hrl3, hrl2, hrl1]; exact hq5_rq) hrq_lo (by omega) (by omega) _
      (fun v hv => by simp [evalHOLExact, toExact, hrl7, hrl6, hrl5, hrl4, hrl3, hrl2, hrl1, hq5_n3] at hv; exact ⟨_, hv.symm⟩) hkr7
  have hvn3 : vn3 = w_n3 := by simp [evalHOLExact, toExact, hrl7, hrl6, hrl5, hrl4, hrl3, hrl2, hrl1, hq5_n3] at hvn3_ev; exact hvn3_ev.symm
  rw [hvn3] at hm_rq56
  obtain ⟨r9, _, _, hrl9, hrg9, hrs9, _, hne9, hkr9⟩ :=
    seq_store_fresh_returned hrs8 (ofString "rq") w_rq 80 64 (by rw [hrl8, hrl7, hrl6, hrl5, hrl4, hrl3, hrl2, hrl1]; exact hq5_rq) hrq_lo (by omega) (by omega) _
      (eval_op_word r8 _ ⟨_, _, rfl⟩) hkr8
  obtain ⟨r10, vn4, hvn4_ev, hrl10, hrg10, hrs10, hm_rq72, hne10, hkr10⟩ :=
    seq_store_fresh_returned hrs9 (ofString "rq") w_rq 80 72 (by rw [hrl9, hrl8, hrl7, hrl6, hrl5, hrl4, hrl3, hrl2, hrl1]; exact hq5_rq) hrq_lo (by omega) (by omega) _
      (fun v hv => by simp [evalHOLExact, toExact, hrl9, hrl8, hrl7, hrl6, hrl5, hrl4, hrl3, hrl2, hrl1, hq5_n4] at hv; exact ⟨_, hv.symm⟩) hkr9
  have hvn4 : vn4 = w_n4 := by simp [evalHOLExact, toExact, hrl9, hrl8, hrl7, hrl6, hrl5, hrl4, hrl3, hrl2, hrl1, hq5_n4] at hvn4_ev; exact hvn4_ev.symm
  rw [hvn4] at hm_rq72
  have hr10_rq : r10.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := by
    rw [hrl10, hrl9, hrl8, hrl7, hrl6, hrl5, hrl4, hrl3, hrl2, hrl1]; exact hq5_rq
  rw [evaluateHOLFiniteState_return] at hkr10
  simp [evalHOLExact, toExact, hr10_rq, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hkr10
  obtain ⟨hrv_eq, hr10_post⟩ := hkr10
  have hpost_mem : post.memory = r10.memory := by
    rw [hpost_i, hpost_rq, hpost_o0, hpost_o1, hpost_o2, hpost_o3, hpost_o4,
        hpost_n0, hpost_n1, hpost_n2, hpost_n3, hpost_n4, ← hr10_post]
    rfl
  have hpost_glob : post.globals = m5.globals := by
    rw [hpost_i, hpost_rq, hpost_o0, hpost_o1, hpost_o2, hpost_o3, hpost_o4,
        hpost_n0, hpost_n1, hpost_n2, hpost_n3, hpost_n4, ← hr10_post]
    dsimp only [PanSemStateFiniteExact.emptyLocalsHOLFinite]
    rw [hrg10, hrg9, hrg8, hrg7, hrg6, hrg5, hrg4, hrg3, hrg2, hrg1,
        hq5_glob, hq4_glob, hq3_glob, hq2_glob, hq1_glob]
    rfl
  have hpost_hp : globN post "heap_ptr" = w_rq.toNat + 80 := by
    have h1 : globN post "heap_ptr" = globN m5 "heap_ptr" := by unfold globN; rw [hpost_glob]
    omega
  have hpost_memW : ∀ a, memW post a = memW r10 a := fun a => by unfold memW; rw [hpost_mem]
  have hwok_rq : WordsOK post (w_rq.toNat, 80) :=
    wordsOK_preserved_of_worldEff heff_entry_post hrq_al (by omega) hrq_sb (by have := heff_entry_post.arena.2.2.1; omega)
  refine ⟨heff_s_post, heff_entry_post, w_rq, hrv_eq.symm, hrq_al, hrq_sb,
    hrq_lo, by omega, heff_entry_post.arena.2.2.1, hwok_rq, hwok_rq, ?_⟩
  intro idx hidx
  rw [hpost_memW]
  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero]
    rw [hne10 _ (by omega) (by omega), hne9 _ (by omega) (by omega), hne8 _ (by omega) (by omega),
        hne7 _ (by omega) (by omega), hne6 _ (by omega) (by omega), hne5 _ (by omega) (by omega),
        hne4 _ (by omega) (by omega), hne3 _ (by omega) (by omega), hm_rq8]
    exact hn0_lt
  · have hidx1 : w_rq.toNat + 16 * 1 + 8 = w_rq.toNat + 24 := by omega
    rw [hidx1, hne10 _ (by omega) (by omega), hne9 _ (by omega) (by omega), hne8 _ (by omega) (by omega),
        hne7 _ (by omega) (by omega), hne6 _ (by omega) (by omega), hne5 _ (by omega) (by omega), hm_rq24]
    exact hn1_lt
  · have hidx2 : w_rq.toNat + 16 * 2 + 8 = w_rq.toNat + 40 := by omega
    rw [hidx2, hne10 _ (by omega) (by omega), hne9 _ (by omega) (by omega), hne8 _ (by omega) (by omega),
        hne7 _ (by omega) (by omega), hm_rq40]
    exact hn2_lt
  · have hidx3 : w_rq.toNat + 16 * 3 + 8 = w_rq.toNat + 56 := by omega
    rw [hidx3, hne10 _ (by omega) (by omega), hne9 _ (by omega) (by omega), hm_rq56]
    exact hn3_lt
  · have hidx4 : w_rq.toNat + 16 * 4 + 8 = w_rq.toNat + 72 := by omega
    rw [hidx4, hm_rq72]
    exact hn4_lt

/-! ### `worldEff_decode_stateless_input_body_ok` -/

theorem worldEff_decode_stateless_input_body_ok {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
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
  refine worldEff_seq_store_ssz_offs_const_ok hOK heff5 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
    (eval_op_word m5 _ ⟨_, _, rfl⟩) hnt5 hcr5 (fun m6 _ heff6 hnt6 hcr6 => ?_)
  refine worldEff_seq_store_ssz_offs_const_ok hOK heff6 8 (by omega) _ _ (Or.inr rfl)
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
  refine worldEff_seq_store_ssz_offs_const_ok hOK (heff15.locals_clock _ _) 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
    (eval_var_local_word m18 _ w_opl hm18_opl) hnt18 hcr18 (fun m19 hm19_loc heff19 hnt19 hcr19 => ?_)
  refine worldEff_seq_store_ssz_offs_const_ok hOK heff19 8 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m19 _ w_ovh (by rw [hm19_loc]; exact hm18_ovh)) hnt19 hcr19 (fun m20 hm20_loc heff20 hnt20 hcr20 => ?_)
  refine worldEff_seq_store_ssz_offs_const_ok hOK heff20 16 (by omega) _ _ (Or.inr rfl)
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
    exact worldEff_decode_payload_body_ok hOK (heff22.locals_clock callee _) hc_p hc_len hnt_c (contOrRes_of_resumes_dhi hres_c)
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
      (fun callee _ _ _ hnt_c hres_c => worldEff_decode_requests_body_ok hOK (heff28.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
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
          (fun _ _ => worldEff_store_ssz_offs_dyn_ok hOK heff_t _ _ (wi * 8#64)
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

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
