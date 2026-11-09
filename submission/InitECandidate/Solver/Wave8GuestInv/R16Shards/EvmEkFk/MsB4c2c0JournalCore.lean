import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2bWorldStepCode
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21

/-!
# Scratch Rung B4c2c0: Journal-Append & `ts+32`-Delete `WorldStepCodeSc` Core

`NonTrieStep` for the journal append and the `htab_del` of the `ts+32` table, so both
`worldStepCodeSc_of_journal_append` and `worldStepCodeSc_of_htabDel_ts32` close
`CodeRootsValsEq` together with the non-trie world preservation.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

private theorem coreWorldGlobals_no_jn_not_hp_jn {g : String}
    (hg : g ∈ (["ws", "bs", "ts", "bo", "bal_accounts", "bal_idx_accts",
      "bal_idx_stor", "journal", "journal_cap"] : List String)) :
    ofString g ∉ (["heap_ptr", "journal_n"] : List String).map ofString := by
  revert g hg; decide

private theorem globalBuffers_not_hp_jn {gn : String × Nat} (hgn : gn ∈ globalBuffers) :
    ofString gn.1 ∉ (["heap_ptr", "journal_n"] : List String).map ofString := by
  revert gn hgn; decide

/-! ## 1. `PosBufList acctMutBufs` -/

theorem posBufList_acctMutBufs : PosBufList acctMutBufs := by
  refine ⟨validBufList_acctMutBufs, fun p hp => ?_⟩
  simp only [acctMutBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> decide

/-! ## 2. Code-Root Preservation for Journal Append & `ts+32` Deletion -/

private theorem nonTrieStep_of_journal_append {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {tw : BitVec 64} (jnw : BitVec 64)
    (hW0 : WorldOK s) (hAp : ArenaReady post) (_hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg_kept : GlobalsKept ["heap_ptr", "journal_n"] s post)
    (hjn_s : globN s "journal_n" = jnw.toNat)
    (hjn_lt : globN s "journal_n" < globN s "journal_cap")
    (hjn_post : globN post "journal_n" = globN s "journal_n" + 1)
    (hdom_wr : ∀ x : BitVec 64, post.memory x ≠ s.memory x → s.memaddrs x)
    (hcell : ∀ x : BitVec 64, post.memory x ≠ s.memory x →
      CellHitsPos x.toNat (globN s "journal" + 32 * jnw.toNat, 32) ∨
      CellHitsPos x.toNat (freeGap s) ∨
      CellHitsPos x.toNat (heapFree s))
    (hbyte : ∀ a : Nat, a < 2 ^ 64 → memB post a ≠ memB s a →
      InIvl a (globN s "journal" + 32 * jnw.toNat, 32) ∨
      InIvl a (freeGap s) ∨
      InIvl a (heapFree s))
    (hm_r0 : memW post (globN s "journal" + 32 * jnw.toNat) = tw.toNat)
    (htw_ok : ∀ S, TablesTyped s S → tw.toNat ∈ S ∧
      let jrNew :=
        let j := globN s "journal" + 32 * jnw.toNat
        (tw.toNat, journalRole s tw.toNat) ::
          (if memW post (j + 16) ≠ 0 ∧ journalRole s tw.toNat = "ts+32" then
            [(memW post (j + 24), "ts.inner")] else [])
      ∀ p ∈ jrNew, p ∈ worldRoleSlots s) :
    NonTrieStep [] s post := by
  have hAs := hW0.1
  have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hg_kept (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsp_eq]⟩
  have hcore_no_jn : ∀ g ∈ (["ws", "bs", "ts", "bo", "bal_accounts", "bal_idx_accts",
      "bal_idx_stor", "journal", "journal_cap"] : List String), globN post g = globN s g :=
    fun g hg => globN_eq_of_lookup (hg_kept (ofString g) (coreWorldGlobals_no_jn_not_hp_jn hg))
  have hbuf_same : FreshBufsOK s post := by
    refine ⟨fun gn hgn => Or.inl (globN_eq_of_lookup (hg_kept (ofString gn.1) (globalBuffers_not_hp_jn hgn))),
      List.pairwise_iff_getElem.2 fun i _ _ _ _ ha _ => absurd ?_ ha.1⟩
    exact globN_eq_of_lookup (hg_kept (ofString globalBuffers[i].1)
      (globalBuffers_not_hp_jn (List.getElem_mem ‹i < globalBuffers.length›)))
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [EvmBase.sourceBase_val]; omega),
     mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [EvmBase.sourceBase_val]; omega)⟩
  set jrec : Ivl := (globN s "journal" + 32 * jnw.toNat, 32)
  have hjcap_nz : globN s "journal_cap" ≠ 0 := by omega
  have hj_fo : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
    unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; right; simp [hjcap_nz]
  have hjrec_in : Inside jrec (globN s "journal") (globN s "journal" + 32 * globN s "journal_cap") := by
    dsimp [Inside, jrec]; omega
  have hunhit_disj_jr : ∀ i : Ivl, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 →
      Disj i (globN s "journal", 32 * globN s "journal_cap") → IvlUnhit s post i := by
    intro i hal hi1 hi2 hdj x hx8 hhit
    by_contra hne
    have hdj_rec : Disj i jrec := (disj_of_inside_left hjrec_in hdj.flip).flip
    have hin_i : i.1 ≤ x.toNat ∧ x.toNat + 8 ≤ i.1 + i.2 := by unfold CellHits at hhit; omega
    rcases hcell x hne with hrec_hit | hfg_hit | hhf_hit
    · exact not_cellHitsPos_of_disj hin_i hdj_rec hrec_hit
    · exact not_cellHitsPos_of_disj hin_i (disj_allocated_freeGap hAs.2 hal) hfg_hit
    · exact not_cellHitsPos_of_disj hin_i (disj_allocated_heapFree hAs.2 hal) hhf_hit
  intro S Nd hWT _
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hfo_split : fixedObjects s = (globalBuffers.map (bufferRegion s)) ++
      ([(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s ++ balObjects s) := by
    unfold fixedObjects
    have hmap : (List.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) globalBuffers) =
        globalBuffers.map (bufferRegion s) := rfl
    rw [hmap]; simp [List.append_assoc]
  have hpw_fo := hF.2
  rw [hfo_split] at hpw_fo
  obtain ⟨_, hpw_right, hcross_gb⟩ := List.pairwise_append.1 hpw_fo
  have hpw_jr_rest : (([(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
      blockOutObjects s ++ balObjects s)).Pairwise Disj := hpw_right
  rw [List.append_assoc] at hpw_jr_rest
  have hcross_jr_rest := (List.pairwise_cons.1 hpw_jr_rest).1
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := fun t ht i hi => by
    have hal := ((hT.2.1 t ht).2 i hi).1
    have hw := ((hT.2.1 t ht).1.1 i hi).2
    exact hunhit_disj_jr i hal hw.1 hw.2.1 (((hT.2.1 t ht).2 i hi).2 _ hj_fo)
  have hu_gb_rec : ∀ r : String × Nat, r ∈ typedRecords → globN s r.1 ≠ 0 →
      IvlUnhit s post (globN s r.1, r.2) := fun r hr hnz => by
    have hmf := typedRecord_mem_fixedObjects s hr
    simp only [hnz, ↓reduceIte] at hmf
    rcases hF.1 _ hmf with h0 | ⟨hal, hw⟩
    · have : r.2 ≠ 0 := by
        simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      exact absurd h0 this
    · have hm_gb : (globN s r.1, r.2) ∈ globalBuffers.map (bufferRegion s) := by
        have hm0 : bufferRegion s r ∈ globalBuffers.map (bufferRegion s) :=
          List.mem_map.2 ⟨r, typedRecord_mem_globalBuffers hr, rfl⟩
        simpa [bufferRegion, hnz] using hm0
      have hm_jr : (globN s "journal", 32 * globN s "journal_cap") ∈
          [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
            blockOutObjects s ++ balObjects s := by simp [hjcap_nz]
      exact hunhit_disj_jr _ hal hw.1 hw.2.1 (hcross_gb _ hm_gb _ hm_jr)
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) :=
    hu_gb_rec ("ws", 40) (by simp [typedRecords])
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) :=
    hu_gb_rec ("bs", 80) (by simp [typedRecords])
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) :=
    hu_gb_rec ("ts", 72) (by simp [typedRecords])
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) :=
    hu_gb_rec ("bo", 88) (by simp [typedRecords])
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi h24 => by
    have hmf : i ∈ fixedObjects s := by
      unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))
    rcases hF.1 i hmf with h0 | ⟨hal, hw⟩
    · omega
    · have hdj : Disj (globN s "journal", 32 * globN s "journal_cap") i := by
        simpa [hjcap_nz] using hcross_jr_rest i (List.mem_append_left (balObjects s) hi)
      exact hunhit_disj_jr i hal hw.1 hw.2.1 hdj.flip
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hpos => by
    have hmf : i ∈ fixedObjects s := by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
    rcases hF.1 i hmf with h0 | ⟨hal, hw⟩
    · exact absurd h0 hpos
    · have hdj : Disj (globN s "journal", 32 * globN s "journal_cap") i := by
        simpa [hjcap_nz] using hcross_jr_rest i (List.mem_append_right (blockOutObjects s) hi)
      exact hunhit_disj_jr i hal hw.1 hw.2.1 hdj.flip
  have hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hal := (hTr.1.1 n hn).2.1
    have hw := (hTr.1.1 n hn).2.2.2.1
    have hne_mem : nodeIvl s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    exact hunhit_disj_jr _ hal hw.1 hw.2.1 ((hTr.2.1 _ hne_mem).2 _ hj_fo)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      by_contra hne_b
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; dsimp at this; omega
      have hdj_jr : Disj (memW s (n + 32), memW s (n + 40)) jrec :=
        (disj_of_inside_left hjrec_in ((hTr.2.1 _ hp_ne).2 _ hj_fo).flip).flip
      have hdj_fg := disj_allocated_freeGap hAs.2 hal_p
      have hdj_hf := disj_allocated_heapFree hAs.2 hal_p
      rcases hbyte _ ha_lt hne_b with hin_rec | hin_fg | hin_hf
      · unfold InIvl at hin_rec; rcases hdj_jr with h0 | h0 | h1 | h2 <;> (dsimp [jrec] at *; omega)
      · unfold InIvl at hin_fg; rcases hdj_fg with h0 | h0 | h1 | h2 <;> (dsimp [freeGap] at *; omega)
      · unfold InIvl at hin_hf; rcases hdj_hf with h0 | h0 | h1 | h2 <;> (dsimp [heapFree] at *; omega)
  have hbo_part := Fast_C08WkShard03.blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore_no_jn "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst
  have hbal_part := balObjects_eq_of_unhit hAs.2 hT hF (hcore_no_jn "bal_accounts" (by decide))
    hu_tab hu_bal hlow
  obtain ⟨hF_post, _⟩ := Fast_C08WkShard03.fixedTyped_of_freshBufsOK hAs hAp hag hF
    (hcore_no_jn "journal" (by decide)) (hcore_no_jn "journal_cap" (by decide))
    hbo_part.1 hbal_part.1 hbuf_same
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_part.1, hbal_part.1, hcore_no_jn "journal" (by decide), hcore_no_jn "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hg_eq : globN post gn.1 = globN s gn.1 :=
      globN_eq_of_lookup (hg_kept (ofString gn.1) (globalBuffers_not_hp_jn hgn))
    simp [hg_eq]
  obtain ⟨hNH_post, hne_eq⟩ := Fast_C08WkShard03.nodeHeap_congr_bytes hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
    have h264_he : heapEnd ≤ 2 ^ 64 := by decide
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact R10Shards.Fast_GbodyC17ToC21.htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab t ht _ ht_fp)
  rcases hJ.2.2.1 with hjc0 | ⟨hal_jr, hw_jr⟩
  · exact absurd hjc0 hjcap_nz
  have hj_hi := (ivl_allocated_bound hAs.2 hal_jr).2
  have hj8 : (globN s "journal") % 8 = 0 := hw_jr.1
  have hu_jr_old : ∀ i, i < globN s "journal_n" →
      IvlUnhit s post (globN s "journal" + 32 * i, 32) := fun i hi x hx8 hhit => by
    by_contra hne
    have hdj_rec : Disj (globN s "journal" + 32 * i, 32) jrec := by
      right; right; left; dsimp [jrec]; omega
    have hal_i : Allocated s (globN s "journal" + 32 * i, 32) := by
      have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ.1
      rcases hal_jr with ⟨hlo, hhi_hp⟩ | ⟨hlo, hhi_sc⟩
      · exact Or.inl ⟨by dsimp at hlo ⊢; omega, by dsimp at hhi_hp ⊢; omega⟩
      · exact Or.inr ⟨by dsimp at hlo ⊢; omega, by dsimp at hhi_sc ⊢; omega⟩
    have hin_i : globN s "journal" + 32 * i ≤ x.toNat ∧ x.toNat + 8 ≤ globN s "journal" + 32 * i + 32 := by
      unfold CellHits at hhit; omega
    rcases hcell x hne with hrec_hit | hfg_hit | hhf_hit
    · exact not_cellHitsPos_of_disj hin_i hdj_rec hrec_hit
    · exact not_cellHitsPos_of_disj hin_i (disj_allocated_freeGap hAs.2 hal_i) hfg_hit
    · exact not_cellHitsPos_of_disj hin_i (disj_allocated_heapFree hAs.2 hal_i) hhf_hit
  have hj_old_words : ∀ i, i < globN s "journal_n" →
      memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) ∧
      memW post (globN s "journal" + 32 * i + 16) = memW s (globN s "journal" + 32 * i + 16) ∧
      memW post (globN s "journal" + 32 * i + 24) = memW s (globN s "journal" + 32 * i + 24) := by
    intro i hi
    have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ.1
    have hhi_i : globN s "journal" + 32 * i + 32 ≤ 2 ^ 64 := by dsimp at hj_hi; omega
    have hui := hu_jr_old i hi
    exact ⟨memW_eq_of_ivlUnhit hui (by omega) hhi_i ⟨by omega, by omega⟩,
           memW_eq_of_ivlUnhit hui (by omega) hhi_i ⟨by omega, by omega⟩,
           memW_eq_of_ivlUnhit hui (by omega) hhi_i ⟨by omega, by omega⟩⟩
  have hts_g : globN post "ts" = globN s "ts" := hcore_no_jn "ts" (by decide)
  have hj_g : globN post "journal" = globN s "journal" := hcore_no_jn "journal" (by decide)
  have hrole_eq : ∀ t, journalRole post t = journalRole s t := fun t => by
    unfold journalRole
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw16 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 16) (by omega) (by omega)
      have hw32 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      have hw48 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 48) (by omega) (by omega)
      have hw64 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 64) (by omega) (by omega)
      simp only [hts_g] at hw16 hw32 hw48 hw64 ⊢
      rw [hw16, hw32, hw48, hw64]
  obtain ⟨htw_S, hjrNew_sub⟩ := htw_ok S hT
  have hJ_post : JournalTyped post S := by
    unfold JournalTyped
    rw [hjn_post, hcore_no_jn "journal_cap" (by decide), hj_g]
    refine ⟨by omega, hJ.2.1, Or.inr ⟨hag.allocated hal_jr, wordsOK_transfer hAs.1 hAp.1 hw_jr⟩, ?_⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
    · rw [(hj_old_words i hlt).1]; exact hJ.2.2.2 i hlt
    · rw [hjn_s, hm_r0]; exact htw_S
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s := by
    have hws_g : globN post "ws" = globN s "ws" := hcore_no_jn "ws" (by decide)
    have hbs_g : globN post "bs" = globN s "bs" := hcore_no_jn "bs" (by decide)
    have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hcore_no_jn "bal_accounts" (by decide)
    have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" := hcore_no_jn "bal_idx_accts" (by decide)
    have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" := hcore_no_jn "bal_idx_stor" (by decide)
    have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
        recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
      unfold recRoles
      by_cases h : globN s "ws" = 0
      · simp [hws_g, h]
      · simp only [hws_g, h, ↓reduceIte]; apply List.map_congr_left
        intro ⟨k, _⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) hk.1 hk.2
        simp only [hws_g] at hw; simp [hw]
    have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
        recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
      unfold recRoles
      by_cases h : globN s "bs" = 0
      · simp [hbs_g, h]
      · simp only [hbs_g, h, ↓reduceIte]; apply List.map_congr_left
        intro ⟨k, _⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
        simp only [hbs_g] at hw; simp [hw]
    have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
        recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
      unfold recRoles
      by_cases h : globN s "ts" = 0
      · simp [hts_g, h]
      · simp only [hts_g, h, ↓reduceIte]; apply List.map_congr_left
        intro ⟨k, _⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) hk.1 hk.2
        simp only [hts_g] at hw; simp [hw]
    have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
      unfold nestRoles
      by_cases h : globN s "bs" = 0
      · simp [hbs_g, h]
      · have hw32 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
        simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "bs" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s (globN s "bs" + 32) ∈ S := by
            rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm; exact absurd h0 h32; exact hm
          rw [R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
      unfold nestRoles
      by_cases h : globN s "ts" = 0
      · simp [hts_g, h]
      · have hw32 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
        simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "ts" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s (globN s "ts" + 32) ∈ S := by
            rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm; exact absurd h0 h32; exact hm
          rw [R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    have hrecs_bal := Fast_C08WkShard03.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
    congr 1; congr 1
    apply List.flatMap_congr
    intro ad had
    rw [← hrecs_bal] at had
    obtain ⟨h0, h8, _⟩ := hbal_part.2 ad had
    rw [h0, h8]
  let jrNew :=
    let j := globN s "journal" + 32 * jnw.toNat
    (tw.toNat, journalRole s tw.toNat) ::
      (if memW post (j + 16) ≠ 0 ∧ journalRole s tw.toNat = "ts+32" then
        [(memW post (j + 24), "ts.inner")] else [])
  have hjrs_post : journalRoleSlots post = journalRoleSlots s ++ jrNew := by
    unfold journalRoleSlots
    rw [hjn_post, hj_g, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    congr 1
    · apply List.flatMap_congr
      intro i hi
      rw [List.mem_range] at hi
      obtain ⟨hc0, hc16, hc24⟩ := hj_old_words i hi
      simp only [hc0, hc16, hc24, hrole_eq]
    · simp only [hjn_s, hm_r0, hrole_eq, jrNew]
  have hT_post : TablesTyped post S := by
    have hT0 := hT
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    have hws_g : globN post "ws" = globN s "ws" := hcore_no_jn "ws" (by decide)
    have hbs_g : globN post "bs" = globN s "bs" := hcore_no_jn "bs" (by decide)
    have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hcore_no_jn "bal_accounts" (by decide)
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2, hfix_eq]
      exact ⟨R10Shards.Fast_GbodyC17ToC21.htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, ((hTt t ht).2 i hi).2⟩⟩
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp t ht u hu_mem hne
    · intro k hk hnz; rw [hws_g] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hwsR k hk hnz
    · intro k hk hnz; rw [hbs_g] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hbsR k hk hnz
    · intro k hk hnz; rw [hts_g] at hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) htk.1 htk.2]
      exact htsR k hk hnz
    · intro g hg
      have hg_eq : globN post g = globN s g := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> exact hcore_no_jn _ (by decide)
      rw [hg_eq]; exact hgR g hg
    · intro hnz hm; rw [hbs_g] at hnz
      have hw32 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact Fast_C08WkShard03.htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (hbsN hnz hm)
    · intro hnz hm; rw [hts_g] at hnz
      have hw32 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact Fast_C08WkShard03.htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (htsN hnz hm)
    · intro ad had
      obtain ⟨h0, h8, _, hkl, hll⟩ := hbal_part.2 ad had
      have hrecs := Fast_C08WkShard03.balRecords_eq_of_unhit hT0 hba_g (fun hnz => by
        rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0' | hm
        · exact absurd h0' hnz
        · exact hu_tab _ hm)
      rw [hrecs] at had
      have had_old := hbalT ad had
      exact ⟨by rw [h0]; exact had_old.1, by rw [h8]; exact had_old.2.1, hkl, hll⟩
    · rw [hwrs_eq, hjrs_post]
      exact rolesOK_append_journal_sub_wrs hroles
        (fun u hu => (htab_fp_hdr u hu).1 0 (by omega))
        hjrNew_sub
  have hTr_post : TriesTypedWith post S Nd := by
    have hws_g : globN post "ws" = globN s "ws" := hcore_no_jn "ws" (by decide)
    refine ⟨hNH_post, ?_, ?_⟩
    · rw [hne_eq, hfix_eq]
      intro o ho
      refine ⟨fun t ht i hi => ?_, (hTr.2.1 o ho).2⟩
      rw [(htab_fp_hdr t ht).2] at hi
      exact (hTr.2.1 o ho).1 t ht i hi
    · intro hnz; rw [hws_g] at hnz
      have hw24 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit (hT.2.1 _ hm).1 (hu_tab _ hm)
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]; exact hr32 hm i hi
  have hnto_eq : nonTrieOwned post S = nonTrieOwned s S := by
    unfold nonTrieOwned
    rw [hfix_eq]
    congr 1
    apply List.flatMap_congr
    intro t ht; exact (htab_fp_hdr t ht).2
  refine ⟨⟨Nd, hT_post, hJ_post, hF_post, hTr_post⟩, ?_, ?_⟩
  · intro o ho; rw [hnto_eq] at ho; exact Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩)
  · intro a hkeep hnot_hf
    by_contra hne
    rcases hcell a hne with ⟨_, hhit_rec⟩ | ⟨_, hhit_fg⟩ | ⟨_, hhit_hf⟩
    · have hhit_jr : CellHits a.toNat (globN s "journal", 32 * globN s "journal_cap") := by
        unfold CellHits at hhit_rec ⊢; dsimp [jrec] at hhit_rec; omega
      have hnto_jr : (globN s "journal", 32 * globN s "journal_cap") ∈ nonTrieOwned s S := by
        unfold nonTrieOwned; exact List.mem_append_right _ hj_fo
      exact hkeep _ (List.mem_append_left _ (List.mem_append_left _ hnto_jr)) hhit_jr
    · exact hkeep (freeGap s) (List.mem_append_right _ List.mem_cons_self) hhit_fg
    · apply hnot_hf
      exact hhit_hf

theorem worldStepCodeSc_of_journal_append {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {tw : BitVec 64} (jnw : BitVec 64)
    (hW0 : WorldOK s) (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg_kept : GlobalsKept ["heap_ptr", "journal_n"] s post)
    (hjn_s : globN s "journal_n" = jnw.toNat)
    (hjn_lt : globN s "journal_n" < globN s "journal_cap")
    (hjn_post : globN post "journal_n" = globN s "journal_n" + 1)
    (hdom_wr : ∀ x : BitVec 64, post.memory x ≠ s.memory x → s.memaddrs x)
    (hcell : ∀ x : BitVec 64, post.memory x ≠ s.memory x →
      CellHitsPos x.toNat (globN s "journal" + 32 * jnw.toNat, 32) ∨
      CellHitsPos x.toNat (freeGap s) ∨
      CellHitsPos x.toNat (heapFree s))
    (hbyte : ∀ a : Nat, a < 2 ^ 64 → memB post a ≠ memB s a →
      InIvl a (globN s "journal" + 32 * jnw.toNat, 32) ∨
      InIvl a (freeGap s) ∨
      InIvl a (heapFree s))
    (hm_r0 : memW post (globN s "journal" + 32 * jnw.toNat) = tw.toNat)
    (htw_ok : ∀ S, TablesTyped s S → tw.toNat ∈ S ∧
      let jrNew :=
        let j := globN s "journal" + 32 * jnw.toNat
        (tw.toNat, journalRole s tw.toNat) ::
          (if memW post (j + 16) ≠ 0 ∧ journalRole s tw.toNat = "ts+32" then
            [(memW post (j + 24), "ts.inner")] else [])
      ∀ p ∈ jrNew, p ∈ worldRoleSlots s) :
    WorldStepCodeSc [] ["heap_ptr", "journal_n"] s r post := by
  have hbase := worldStepSc_of_journal_append (r := r) jnw hW0 hAp hbe hhp hg_kept hjn_s hjn_lt hjn_post
      hdom_wr hcell hbyte hm_r0 htw_ok
  obtain ⟨⟨hAp', hhp', hG', hK', hWs⟩, hsc⟩ := hbase
  refine ⟨⟨⟨hAp', hhp', hG', hK', fun S Nd hWT hD => ?_⟩, hsc⟩,
    nonTrieStep_of_journal_append jnw hW0 hAp hbe hhp hg_kept hjn_s hjn_lt hjn_post
      hdom_wr hcell hbyte hm_r0 htw_ok⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hWs S Nd hWT hD
  refine ⟨S', Nd', hsub, hWT', hOG, hFO, ?_⟩
  have hAs := hW0.1
  have hjcap_nz : globN s "journal_cap" ≠ 0 := by omega
  have hj_fo : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
    unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; right; simp [hjcap_nz]
  set jrec : Ivl := (globN s "journal" + 32 * jnw.toNat, 32)
  have hjrec_in : Inside jrec (globN s "journal") (globN s "journal" + 32 * globN s "journal_cap") := by
    dsimp [Inside, jrec]; omega
  intro g k hm hgnz htnz
  have htS := codeRoot_mem_S hWT.1 hm hgnz htnz
  apply R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit (hWT.1.2.1 _ htS).1
  intro i hi x hx8 hhit
  by_contra hne
  have hal := ((hWT.1.2.1 _ htS).2 i hi).1
  have hwords := ((hWT.1.2.1 _ htS).1.1 i hi).2
  have hi1_al : i.1 % 8 = 0 := hwords.1
  have hi2_al : i.2 % 8 = 0 := hwords.2.1
  have hdj_jr : Disj i (globN s "journal", 32 * globN s "journal_cap") :=
    ((hWT.1.2.1 _ htS).2 i hi).2 _ hj_fo
  have hdj_rec : Disj i jrec := (disj_of_inside_left hjrec_in hdj_jr.flip).flip
  have hin_i : i.1 ≤ x.toNat ∧ x.toNat + 8 ≤ i.1 + i.2 := by
    unfold CellHits at hhit; omega
  rcases hcell x hne with hrec_hit | hfg_hit | hhf_hit
  · exact not_cellHitsPos_of_disj hin_i hdj_rec hrec_hit
  · exact not_cellHitsPos_of_disj hin_i (disj_allocated_freeGap hAs.2 hal) hfg_hit
  · exact not_cellHitsPos_of_disj hin_i (disj_allocated_heapFree hAs.2 hal) hhf_hit


private theorem coreWorldGlobals_not_hp {g : String}
    (hg : g ∈ R10Shards.P26_P28.coreWorldGlobals) :
    ofString g ∉ (["heap_ptr"] : List String).map ofString := by
  revert g hg; decide

private theorem globalBuffers_not_hp {gn : String × Nat} (hgn : gn ∈ globalBuffers) :
    ofString gn.1 ∉ (["heap_ptr"] : List String).map ofString := by
  revert gn hgn; decide

theorem nonTrieStep_of_htabDel_ts32 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hW0 : WorldOK s) (hbe : post.be = s.be)
    (hg_nonHeap : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k)
    (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + 32) ≠ 0)
    (hAp : ArenaReady post) (hwf_t0 : HtabWF post (memW s (globN s "ts" + 32)))
    (hhdr0_t0 : hdr post (memW s (globN s "ts" + 32)) 0 = hdr s (memW s (globN s "ts" + 32)) 0)
    (hvals_sub : ∀ x ∈ htabValues post (memW s (globN s "ts" + 32)),
      x ∈ htabValues s (memW s (globN s "ts" + 32)))
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfp_t0 : ∀ i ∈ htabFootprint post (memW s (globN s "ts" + 32)), Allocated post i ∧
      ((∃ j ∈ htabFootprint s (memW s (globN s "ts" + 32)), Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))))
    (hfr : FrameOutside s post (htabFootprint s (memW s (globN s "ts" + 32)))
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    NonTrieStep [] s post := by
  set t0 := memW s (globN s "ts" + 32)
  have hAs := hW0.1
  have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hg_nonHeap (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsp_eq]⟩
  have hcore : ∀ g ∈ R10Shards.P26_P28.coreWorldGlobals, globN post g = globN s g := fun g hg =>
    globN_eq_of_lookup (hg_nonHeap (ofString g) (coreWorldGlobals_not_hp hg))
  have hbuf_same : FreshBufsOK s post := by
    refine ⟨fun gn hgn => Or.inl (globN_eq_of_lookup (hg_nonHeap (ofString gn.1) (globalBuffers_not_hp hgn))),
      List.pairwise_iff_getElem.2 fun i _ _ _ _ ha _ => absurd ?_ ha.1⟩
    exact globN_eq_of_lookup (hg_nonHeap (ofString globalBuffers[i].1)
      (globalBuffers_not_hp (List.getElem_mem ‹i < globalBuffers.length›)))
  intro S Nd hWT _
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨ht0_S, hno_bs32, hno_ba, hno_ad, hno_ws32, hno_ts32⟩ := ts32Slot_disj s S hT hts_nz ht0_nz
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have h1 := hAs.2.2.2.2.2.2.1; have h2 := hAp.2.2.2.2.2.2.1; omega
  have ht0_al : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hT.2.1 t0 ht0_S).1.1 j hj).2; exact ⟨hw.1, hw.2.1⟩
  have hunhit_disj : ∀ i : Ivl, i.2 ≠ 0 → (∀ j ∈ htabFootprint s t0, Disj i j) →
      Allocated s i → IvlUnhit s post i := fun i hipos hdi hal =>
    ivlUnhit_of_frameOutside_aligned hipos hfr ht0_al hf_al hdi
      (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr hal))
  have hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, IvlUnhit s post i := fun u hu hne i hi =>
    hunhit_disj i (htabFootprint_len_pos (hT.2.1 u hu).1 hi)
      (fun j hj => hT.2.2.1 u hu t0 ht0_S hne i hi j hj) (((hT.2.1 u hu).2 i hi).1)
  have hu_fix : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hipos =>
    hunhit_disj i hipos (fun j hj => (((hT.2.1 t0 ht0_S).2 j hj).2 i hi).flip)
      (by rcases hF.1 i hi with h0 | ⟨hal, _⟩; exact absurd h0 hipos; exact hal)
  have hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hmem : nodeIvl s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    have hpos : (nodeIvl s n).2 ≠ 0 := by dsimp [nodeIvl]; unfold nodeSize; split_ifs <;> decide
    exact hunhit_disj _ hpos (fun j hj => (hTr.2.1 _ hmem).1 t0 ht0_S j hj) ((hTr.1.1 n hn).2.1)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; dsimp at this; omega
      let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
      have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
      have hmem := hfr c
        (fun j hj hcj => by
          obtain ⟨h1, h2⟩ := hcj; rw [hc_nat] at h1 h2
          have hj_al := ((hT.2.1 t0 ht0_S).1.1 j hj).2
          have hj1 := hj_al.1; have hj2 := hj_al.2.1
          have hdj := (hTr.2.1 _ hp_ne).1 t0 ht0_S j hj
          rcases hdj with d | d | d | d <;> omega)
        (fun hcf => by
          obtain ⟨h1, h2⟩ := hcf; dsimp at h1 h2; rw [hc_nat] at h1 h2
          have hp_hp8 : (globN post "heap_ptr") % 8 = 0 := hAp.2.2.2.2.2.2.1
          have hdj := disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr hal_p)
          try dsimp at hdj
          rcases hdj with d | d | d | d <;> omega)
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v post.be).toNat) =
             (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
      rw [hmem, hbe]
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          obtain ⟨h1, _⟩ := hcj; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := ((hT.2.1 t0 ht0_S).1.1 j hj).1.1; omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf; dsimp at h1; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := hAs.2.1; omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz => by
    apply hu_fix _ _ (by dsimp only; omega); unfold fixedObjects
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hnz]
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi h24 =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))) (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hipos =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)) hipos
  have hbo_eq := Fast_C08WkShard03.blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst
  have hbal_eq := balObjects_eq_of_unhit_except hAs.2 hT hF
    (hcore "bal_accounts" (by decide)) hu_other ⟨hno_ba, hno_ad⟩ hu_bal hm0
  obtain ⟨hF_post, _⟩ := Fast_C08WkShard03.fixedTyped_of_freshBufsOK hAs hAp hag hF
    (hcore "journal" (by decide)) (hcore "journal_cap" (by decide)) hbo_eq.1 hbal_eq.1 hbuf_same
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_eq.1, hbal_eq.1, hcore "journal" (by decide), hcore "journal_cap" (by decide)]
    congr 3; apply List.map_congr_left; intro gn hgn
    simp [globN_eq_of_lookup (hg_nonHeap (ofString gn.1) (globalBuffers_not_hp hgn))]
  obtain ⟨hjr_eq, hJ_post⟩ := Fast_C08WkShard03.journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hcore hu_ts hu_jr
  obtain ⟨hNH_post, hne_eq⟩ := Fast_C08WkShard03.nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hother_fp : ∀ u ∈ S, u ≠ t0 →
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu hne
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    exact R10Shards.Fast_GbodyC17ToC21.htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
      (by have := (hfp _ ht_fp).1.2; dsimp at this; omega) (hu_other u hu hne _ ht_fp)
  have ht0_disj_other : ∀ i ∈ htabFootprint post t0,
      (∀ u ∈ S, u ≠ t0 → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects s, Disj i j) ∧ (∀ o ∈ nodeExtents s Nd, Disj i o) := by
    intro i hi
    rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
    · refine ⟨fun u hu hne j hj => disj_of_inside_left hin (hT.2.2.1 t0 ht0_S u hu hne.symm k hk j hj),
              fun j hj => disj_of_inside_left hin (((hT.2.1 t0 ht0_S).2 k hk).2 j hj),
              fun o ho => disj_of_inside_left hin ((hTr.2.1 o ho).1 t0 ht0_S k hk).flip⟩
    · refine ⟨fun u hu _ j hj => (disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr ((hT.2.1 u hu).2 j hj).1))).flip,
              fun j hj => (disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp
                  (by rcases hF.1 j hj with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal))).flip,
              fun o ho => (disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (by
                  unfold nodeExtents at ho; obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
                  rcases hno with rfl | rfl
                  · exact Or.inr (hTr.1.1 n hn).2.1
                  · unfold nodePath; split_ifs with hc
                    · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
                      · exact absurd h0 hc.2
                      · exact Or.inr hal
                    · exact Or.inl rfl))).flip⟩
  have hT_post : TablesTyped post S := by
    have hT0 := hT
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    have ews := hcore "ws" (by decide); have ebs := hcore "bs" (by decide); have ets := hcore "ts" (by decide)
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq.2, ?_⟩
    · intro u hu; by_cases heq : u = t0
      · subst heq; rw [hfix_eq]; exact ⟨hwf_t0, fun i hi => ⟨(hfp_t0 i hi).1, (ht0_disj_other i hi).2.1⟩⟩
      · rw [(hother_fp u hu heq).2, hfix_eq]
        exact ⟨R10Shards.Fast_GbodyC17ToC21.htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_other u hu heq),
          fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, ((htwf u hu).2 i hi).2⟩⟩
    · intro u hu v hv hne i hi j hj; by_cases hu0 : u = t0
      · subst hu0; rw [(hother_fp v hv hne.symm).2] at hj; exact (ht0_disj_other i hi).1 v hv hne.symm j hj
      · by_cases hv0 : v = t0
        · subst hv0; rw [(hother_fp u hu hu0).2] at hi; exact ((ht0_disj_other j hj).1 u hu hu0 i hi).flip
        · rw [(hother_fp u hu hu0).2] at hi; rw [(hother_fp v hv hv0).2] at hj; exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz; rw [ews] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega
      rw [Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hnz (hu_ws hnz) hk8.1 hk8.2]; exact hwsR k hk hnz
    · intro k hk hnz; rw [ebs] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) hk8.1 hk8.2]; exact hbsR k hk hnz
    · intro k hk hnz; rw [ets] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) hk8.1 hk8.2]; exact htsR k hk hnz
    · intro g hg_mem
      rw [hcore g (by simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg_mem; rcases hg_mem with rfl | rfl | rfl <;> decide)]
      exact hgR g hg_mem
    · intro hnz hmem; rw [ebs] at hnz
      have ew := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact Fast_C08WkShard03.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_bs32 hnz)) (fun _ hx => hx) (hbsN hnz hmem)
    · intro hnz hmem; rw [ets] at hnz
      have ew := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      intro i hi
      have hmem_v : nodeF post (hdr post t0 5) (memW post (hdr post t0 6 + 8 * i)) 8 ∈ htabValues post t0 := by
        unfold htabValues; exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
      have hmem_s := hvals_sub _ hmem_v
      unfold htabValues at hmem_s
      obtain ⟨j, hj, heq⟩ := List.mem_map.1 hmem_s
      rw [← heq]; exact htsN hnz hmem j (List.mem_range.1 hj)
    · intro ad had
      have had_s : ad ∈ balRecords s := by
        rwa [Fast_C08WkShard03.balRecords_eq_of_unhit hT0 (hcore "bal_accounts" (by decide)) (fun hnz => by
          rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0 | hm; exact absurd h0 hnz; exact hu_other _ hm hno_ba)] at had
      obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq.2 ad had
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
    · have hws_g : globN post "ws" = globN s "ws" := hcore "ws" (by decide)
      have hbs_g : globN post "bs" = globN s "bs" := hcore "bs" (by decide)
      have hts_g : globN post "ts" = globN s "ts" := hcore "ts" (by decide)
      have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hcore "bal_accounts" (by decide)
      have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" := hcore "bal_idx_accts" (by decide)
      have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" := hcore "bal_idx_stor" (by decide)
      have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
          recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
        unfold recRoles
        by_cases h : globN s "ws" = 0
        · simp [hws_g, h]
        · simp only [hws_g, h, ↓reduceIte]; apply List.map_congr_left
          intro ⟨k, r⟩ hkr
          have hk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
            rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
          have hw := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) hk.1 hk.2
          simp only [hws_g] at hw; simp [hw]
      have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
          (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
          recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
          (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
        unfold recRoles
        by_cases h : globN s "bs" = 0
        · simp [hbs_g, h]
        · simp only [hbs_g, h, ↓reduceIte]; apply List.map_congr_left
          intro ⟨k, r⟩ hkr
          have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
            rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
          have hw := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
          simp only [hbs_g] at hw; simp [hw]
      have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
          (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
          recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
          (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
        unfold recRoles
        by_cases h : globN s "ts" = 0
        · simp [hts_g, h]
        · simp only [hts_g, h, ↓reduceIte]; apply List.map_congr_left
          intro ⟨k, r⟩ hkr
          have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
            rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
          have hw := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) hk.1 hk.2
          simp only [hts_g] at hw; simp [hw]
      have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
        unfold nestRoles
        by_cases h : globN s "bs" = 0
        · simp [hbs_g, h]
        · have hw32 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
          simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
          by_cases h32 : memW s (globN s "bs" + 32) = 0
          · simp [h32]
          · simp only [h32, ↓reduceIte]
            have hmS : memW s (globN s "bs" + 32) ∈ S := by
              rcases hbsR 32 (by simp [bsTableSlots]) h with h0 | hm; exact absurd h0 h32; exact hm
            rw [R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit (htwf _ hmS).1 (hu_other _ hmS (hno_bs32 h))]
      have hnest_ts_sub : ∀ p ∈ (nestRoles post "ts" "ts.inner").filter (fun a => a.1 != 0),
          p ∈ (nestRoles s "ts" "ts.inner").filter (fun a => a.1 != 0) := by
        intro p hp
        rw [List.mem_filter] at hp ⊢
        refine ⟨?_, hp.2⟩
        unfold nestRoles at hp ⊢
        have hw32 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hts_nz (hu_ts hts_nz) (k := 32) (by omega) (by omega)
        simp only [hts_g] at hw32
        have ht0_nz' : memW s (globN s "ts" + 32) ≠ 0 := ht0_nz
        simp only [hts_g, hts_nz, ↓reduceIte, hw32, ht0_nz'] at hp ⊢
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hp.1
        exact List.mem_map.2 ⟨v, hvals_sub v hv, rfl⟩
      have hrecs_bal := Fast_C08WkShard03.balRecords_eq_of_unhit hT0 hba_g (fun hnz => by
        rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
        · exact absurd h0 hnz
        · exact hu_other _ hm hno_ba)
      have hbal_part_eq : ((balRecords post).flatMap fun ad => [(memW post ad, "bal.stor"), (memW post (ad + 8), "bal.reads")]) =
          ((balRecords s).flatMap fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]) := by
        rw [hrecs_bal]; apply List.flatMap_congr
        intro ad had
        rw [← hrecs_bal] at had
        obtain ⟨h0, h8, _⟩ := hbal_eq.2 ad had
        rw [h0, h8]
      let preList := (recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
        recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] ++
        recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] ++
        [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"), (globN s "bal_idx_stor", "bal_idx_stor")] ++
        nestRoles s "bs" "bs.inner").filter (fun a => a.1 != 0)
      let sufList := ((balRecords s).flatMap fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]).filter (fun a => a.1 != 0)
      have hwrs_s : worldRoleSlots s = preList ++ (nestRoles s "ts" "ts.inner").filter (fun a => a.1 != 0) ++ sufList := by
        unfold worldRoleSlots; dsimp only [preList, sufList]; simp only [List.filter_append, List.append_assoc]
      have hwrs_p : worldRoleSlots post = preList ++ (nestRoles post "ts" "ts.inner").filter (fun a => a.1 != 0) ++ sufList := by
        unfold worldRoleSlots
        rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hbal_part_eq]
        dsimp only [preList, sufList]; simp only [List.filter_append, List.append_assoc]
      rw [hwrs_p, hjr_eq]; rw [hwrs_s] at hroles
      exact rolesOK_nest_sub hroles
        (fun u hu => by
          by_cases hu0 : u = t0
          · subst hu0; exact hhdr0_t0
          · exact (hother_fp u hu hu0).1 0 (by omega))
        (fun x hx => by
          have hx' := hnest_ts_sub x hx
          have hmem := (List.mem_filter.1 hx).1
          have hts_g_post : globN post "ts" ≠ 0 := by rw [hts_g]; exact hts_nz
          simp only [nestRoles, hts_g_post, ↓reduceIte] at hmem
          by_cases hm32_p : memW post (globN post "ts" + 32) = 0
          · simp [hm32_p] at hmem
          · simp only [hm32_p, ↓reduceIte] at hmem
            obtain ⟨v, _, rfl⟩ := List.mem_map.1 hmem
            exact ⟨hx', rfl⟩)
  have hTr_post : TriesTypedWith post S Nd := by
    have ews := hcore "ws" (by decide)
    refine ⟨hNH_post, ?_, ?_⟩
    · rw [hne_eq, hfix_eq]; intro o ho; refine ⟨fun u hu i hi => ?_, (hTr.2.1 o ho).2⟩
      by_cases hu0 : u = t0
      · subst hu0; exact ((ht0_disj_other i hi).2.2 o ho).flip
      · rw [(hother_fp u hu hu0).2] at hi; exact (hTr.2.1 o ho).1 u hu i hi
    · intro hws_nz; rw [ews] at hws_nz
      have e24 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := Fast_C08WkShard03.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]; obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hne32 := hno_ws32 hws_nz
      have hvals_eq := R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit (hT.2.1 _ htS).1 (hu_other _ htS hne32)
      obtain ⟨hhdr32, _⟩ := hother_fp _ htS hne32
      rw [hhdr32 3 (by omega)] at hi
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]; exact hr32 htS i hi
  refine ⟨⟨Nd, hT_post, hJ_post, hF_post, hTr_post⟩, ?_, ?_⟩
  · intro o ho; unfold nonTrieOwned at ho
    rcases List.mem_append.1 ho with ho_tab | ho_fix
    · obtain ⟨u, hu, hi⟩ := List.mem_flatMap.1 ho_tab
      by_cases hu0 : u = t0
      · subst hu0
        rcases (hfp_t0 o hi).2 with ⟨j, hj, hin⟩ | hfresh
        · refine Or.inr (Or.inl ⟨j, ?_, hin⟩); unfold nonTrieOwned
          exact List.mem_append_left _ (List.mem_flatMap.2 ⟨t0, ht0_S, hj⟩)
        · exact Or.inr (Or.inr ⟨hfresh.1, by
            have h2 := hfresh.2
            exact le_trans h2 (Nat.add_sub_of_le hhp).le⟩)
      · rw [(hother_fp u hu hu0).2] at hi
        refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩); unfold nonTrieOwned
        exact List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hi⟩)
    · rw [hfix_eq] at ho_fix
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩); unfold nonTrieOwned
      exact List.mem_append_right _ ho_fix
  · intro a hkeep hnot_hf
    apply hfr a
    · intro j hj
      apply hkeep j
      apply List.mem_append_left; apply List.mem_append_left
      unfold nonTrieOwned
      exact List.mem_append_left _ (List.mem_flatMap.2 ⟨t0, ht0_S, hj⟩)
    · intro hcf
      apply hnot_hf
      have hhl : globN post "heap_ptr" ≤ heapLimit := hAp.2.2.1
      exact ⟨hcf.1, lt_of_lt_of_le hcf.2 (by
        change globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr") ≤
          globN s "heap_ptr" + (heapLimit - globN s "heap_ptr")
        exact Nat.add_le_add_left (Nat.sub_le_sub_right hhl _) _)⟩

theorem worldStepCodeSc_of_htabDel_ts32 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {gw : List String}
    (hW0 : WorldOK s) (hbe : post.be = s.be)
    (hg_kept : GlobalsKept gw s post)
    (hg_nonHeap : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k)
    (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + 32) ≠ 0)
    (hAp : ArenaReady post) (hwf_t0 : HtabWF post (memW s (globN s "ts" + 32)))
    (hhdr0_t0 : hdr post (memW s (globN s "ts" + 32)) 0 = hdr s (memW s (globN s "ts" + 32)) 0)
    (hvals_sub : ∀ x ∈ htabValues post (memW s (globN s "ts" + 32)),
      x ∈ htabValues s (memW s (globN s "ts" + 32)))
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfp_t0 : ∀ i ∈ htabFootprint post (memW s (globN s "ts" + 32)), Allocated post i ∧
      ((∃ j ∈ htabFootprint s (memW s (globN s "ts" + 32)), Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))))
    (hfr : FrameOutside s post (htabFootprint s (memW s (globN s "ts" + 32)))
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    WorldStepCodeSc [] gw s r post := by
  have hbase := worldStepSc_of_htabDel_ts32 (r := r) hW0 hbe hg_kept hg_nonHeap hts_nz ht0_nz
    hAp hwf_t0 hhdr0_t0 hvals_sub hhp hfp_t0 hfr
  obtain ⟨⟨hAp', hhp', hG', hK', hWs⟩, hsc⟩ := hbase
  have hAs := hW0.1
  set t0 := memW s (globN s "ts" + 32)
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have h1 := hAs.2.2.2.2.2.2.1; have h2 := hAp.2.2.2.2.2.2.1; omega
  have hcode : ∀ S Nd, WorldTypedWith s S Nd → CodeRootsValsEq s r post S Nd := by
    intro S Nd hWT g k hm hgnz htnz
    have ht0_S : t0 ∈ S := (ts32Slot_disj s S hWT.1 hts_nz ht0_nz).1
    have ht0_al : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
      have hw := ((hWT.1.2.1 t0 ht0_S).1.1 j hj).2
      exact ⟨hw.1, hw.2.1⟩
    have htS := codeRoot_mem_S hWT.1 hm hgnz htnz
    have hne_t0 : memW s (globN s g + k) ≠ t0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · intro heq
        have hws : (memW s (globN s "ws" + 16), "ws+16") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "ws" 16 "ws+16" hgnz htnz
          apply List.mem_append.2; left; apply List.mem_append.2; left
          unfold recRoles; simp [hgnz]
        have ht0_wrs : (t0, "ts+32") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "ts" 32 "ts+32" hts_nz ht0_nz
          apply List.mem_append.2; right; unfold recRoles; simp [hts_nz]
        exact slot_ne_of_diff_nonshared_role hWT.1.2.2.2.2.2.2.2.2.2.2.2 hws ht0_wrs (by decide) heq
      · intro heq
        have hbs : (memW s (globN s "bs" + 48), "bs+48") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "bs" 48 "bs+48" hgnz htnz
          apply List.mem_append.2; left; apply List.mem_append.2; right
          unfold recRoles; simp [hgnz]
        have ht0_wrs : (t0, "ts+32") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "ts" 32 "ts+32" hts_nz ht0_nz
          apply List.mem_append.2; right; unfold recRoles; simp [hts_nz]
        exact slot_ne_of_diff_nonshared_role hWT.1.2.2.2.2.2.2.2.2.2.2.2 hbs ht0_wrs (by decide) heq
      · intro heq
        have hts48 : (memW s (globN s "ts" + 48), "ts+48") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "ts" 48 "ts+48" hgnz htnz
          apply List.mem_append.2; right; unfold recRoles; simp [hgnz]
        have ht0_wrs : (t0, "ts+32") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "ts" 32 "ts+32" hts_nz ht0_nz
          apply List.mem_append.2; right; unfold recRoles; simp [hts_nz]
        exact slot_ne_of_diff_nonshared_role hWT.1.2.2.2.2.2.2.2.2.2.2.2 hts48 ht0_wrs (by decide) heq
    apply R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit (hWT.1.2.1 _ htS).1
    intro i hi
    exact ivlUnhit_of_frameOutside_aligned
      (htabFootprint_len_pos (hWT.1.2.1 _ htS).1 hi) hfr ht0_al hf_al
      (fun j hj => hWT.1.2.2.1 _ htS t0 ht0_S hne_t0 i hi j hj)
      (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr ((hWT.1.2.1 _ htS).2 i hi).1))
  refine ⟨⟨⟨hAp', hhp', hG', hK', fun S Nd hWT hD => ?_⟩, hsc⟩,
    nonTrieStep_of_htabDel_ts32 hW0 hbe hg_nonHeap hts_nz ht0_nz hAp hwf_t0 hhdr0_t0
      hvals_sub hhp hfp_t0 hfr⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hWs S Nd hWT hD
  exact ⟨S', Nd', hsub, hWT', hOG, hFO, hcode S Nd hWT⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
