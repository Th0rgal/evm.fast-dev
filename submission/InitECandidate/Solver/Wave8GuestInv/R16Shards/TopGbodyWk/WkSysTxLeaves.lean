import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkAcctWsBase
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalInitFresh
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard06b
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memcpy
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_msg_new
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rt_te_new

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

theorem lookup_process_checked_system_transaction :
    originalRuntimeCode.lookup (ofString "process_checked_system_transaction") =
      some ([(ofString "target", .one)],
        sourceFnBody Guest.Software.guestFn_process_checked_system_transaction, .one) :=
  lookup_of_guestAst_getElem 871 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_checked_system_transaction) rfl

theorem lookup_process_unchecked_system_transaction :
    originalRuntimeCode.lookup (ofString "process_unchecked_system_transaction") =
      some ([(ofString "target", .one), (ofString "data", .one), (ofString "data_n", .one)],
        sourceFnBody Guest.Software.guestFn_process_unchecked_system_transaction, .one) :=
  GuestTrapAndLookup.lookup_process_unchecked_system_transaction

abbrev sysTxBufs : BufList :=
  [("b2_v", 128), ("bal_key_buf", 64), ("bn_expw", 352), ("bn_gamma", 384),
   ("evm_key_buf", 32), ("keccak_pad", 136), ("keccak_st", 200),
   ("mpt_nib_scratch", 64), ("pre_hdr_buf", 96), ("rmd_h", 40),
   ("rmd_pad", 128), ("rmd_x", 128), ("sha_pad", 128), ("sha_st", 64),
   ("sk_buf", 52), ("u256_ws", 640)]

abbrev sysTxGlobals : List String :=
  ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr",
   "journal_n", "scratch_ptr", "ts"]

abbrev sysTxKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
   ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]

theorem validBufList_sysTxBufs : ValidBufList sysTxBufs := by
  intro p hp
  simp only [sysTxBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨128, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩
  · exact ⟨352, by decide, by decide, by decide⟩
  · exact ⟨384, by decide, by decide, by decide⟩
  · exact ⟨32, by decide, by decide, by decide⟩
  · exact ⟨136, by decide, by decide, by decide⟩
  · exact ⟨200, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩
  · exact ⟨96, by decide, by decide, by decide⟩
  · exact ⟨40, by decide, by decide, by decide⟩
  · exact ⟨128, by decide, by decide, by decide⟩
  · exact ⟨128, by decide, by decide, by decide⟩
  · exact ⟨128, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩
  · exact ⟨640, by decide, by decide, by decide⟩

def KeepSub (k1 k2 : List (String × List Nat)) : Prop :=
  ∀ r ∈ k1, ∃ ks, (r.1, ks) ∈ k2 ∧ ∀ off ∈ r.2, off ∈ ks

theorem recordsKept_mono_keep {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {k1 k2 : List (String × List Nat)} {s post : PanSemStateFiniteExact 64 F}
    (hsub : KeepSub k1 k2) (h : RecordsKept R k2 s post) :
    RecordsKept R k1 s post := by
  intro r hr hnz off hoff hno
  obtain ⟨ks, hks, hoff'⟩ := hsub r hr
  exact h (r.1, ks) hks hnz off (hoff' off hoff) hno

theorem keepSub_sysTxKeep_stdKeep : KeepSub sysTxKeep stdKeep := by
  intro r hr
  simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨[0, 8, 16, 24, 32], by simp [stdKeep], fun _ h => h⟩
  · refine ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72], by simp [stdKeep], ?_⟩
    intro off hoff
    simp at hoff ⊢
    omega
  · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64], by simp [stdKeep], fun _ h => by cases h⟩
  · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80], by simp [stdKeep], fun _ h => h⟩

theorem keepSub_sysTxKeep_freshTx :
    KeepSub sysTxKeep
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] := by
  intro r hr
  simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨[0, 8, 16, 24, 32], by simp, fun _ h => h⟩
  · refine ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72], by simp, ?_⟩
    intro off hoff
    simp at hoff ⊢
    omega
  · exact ⟨[], by simp, fun _ h => h⟩
  · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80], by simp, fun _ h => h⟩

theorem worldStep_mono_bufs_keep {F : Type}
    {B1 B2 : BufList} {gw1 gw2 : List String}
    {k1 k2 : List (String × List Nat)}
    {Q1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : ∀ p ∈ B1, p ∈ B2)
    (hgw : ∀ g ∈ gw1, g ∈ gw2)
    (hk : KeepSub k2 k1)
    (h : WorldStep (bufRegions B1) gw1 k1 Q1 s r post) :
    WorldStep (bufRegions B2) gw2 k2 NoExtra s r post := by
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := h
  have hsubR : ∀ i ∈ bufRegions B1 s, i ∈ bufRegions B2 s := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
    exact List.mem_map.2 ⟨p, hB p hp, rfl⟩
  refine ⟨hAp, hhp, ?_, ?_, ?_⟩
  · intro k hk'
    apply hG k
    intro hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk' (List.mem_map.2 ⟨g, hgw g hg, rfl⟩)
  · have hK' : RecordsKept (bufRegions B2) k1 s post :=
      fun rec hrec hnz off hoff hno =>
        hK rec hrec hnz off hoff (fun i hi => hno i (hsubR i hi))
    exact recordsKept_mono_keep hk hK'
  · intro S Nd hWT hD
    have hD1 : IvlsDisj (bufRegions B1 s) (worldTypedIvls s S Nd) :=
      fun i hi j hj => hD i (hsubR i hi) j hj
    obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hW S Nd hWT hD1
    refine ⟨S', Nd', hsub, hWT', hOG, ?_, trivial⟩
    intro a ha hhf
    apply hFO a _ hhf
    intro i hi
    rcases List.mem_append.1 hi with hi1 | hfg
    · rcases List.mem_append.1 hi1 with hwo | hR1
      · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo))
      · exact ha i (List.mem_append_left _ (List.mem_append_right _ (hsubR i hR1)))
    · exact ha i (List.mem_append_right _ hfg)

def SysTxPrefixStep {F : Type}
    (s : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s r post ∧
    globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    (globN post "bn_expw" = globN s "bn_expw") ∧
    (globN post "bn_gamma" = globN s "bn_gamma")

theorem bufRegions_sysTx_eq_of_prefix {F : Type}
    {s1 s2 : PanSemStateFiniteExact 64 F} {r1 : Option (PanSemResultExact 64)}
    (h12 : SysTxPrefixStep s1 r1 s2) :
    bufRegions sysTxBufs s2 = bufRegions sysTxBufs s1 := by
  obtain ⟨⟨_, _, hG12, _, _⟩, _, _, hbn1, hbn2⟩ := h12
  unfold bufRegions
  apply List.map_congr_left
  intro p hp
  simp only [sysTxBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "b2_v") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "bal_key_buf") (by decide))]
  · simp [bufferRegion, hbn1]
  · simp [bufferRegion, hbn2]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "evm_key_buf") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "keccak_pad") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "keccak_st") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "mpt_nib_scratch") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "pre_hdr_buf") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "rmd_h") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "rmd_pad") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "rmd_x") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "sha_pad") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "sha_st") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "sk_buf") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG12 (ofString "u256_ws") (by decide))]

theorem worldStep_sysTx_trans_prefix {F : Type}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hA1 : ArenaReady s1)
    (h12 : SysTxPrefixStep s1 r1 s2)
    (h23 : WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s2 r2 s3) :
    WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s1 r2 s3 := by
  have hbuf21 : bufRegions sysTxBufs s2 = bufRegions sysTxBufs s1 :=
    bufRegions_sysTx_eq_of_prefix h12
  obtain ⟨⟨hA2, hhp12, hG12, hK12, hW12⟩, hfmp12, hsp12, _, _⟩ := h12
  obtain ⟨hA3, hhp23, hG23, hK23, hW23⟩ := h23
  have hfmp_sp1 : globN s1 "frame_mem_ptr" ≤ globN s1 "scratch_ptr" := hA1.2.2.2.2.1
  refine ⟨hA3, le_trans hhp12 hhp23,
    fun k hk => (hG12 k hk).trans (hG23 k hk), ?_, ?_⟩
  · intro rec hrec hnz off hoff hno
    simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · have hg_rec : globN s2 "ws" = globN s1 "ws" :=
        globN_eq_of_lookup (hG12 (ofString "ws") (by decide))
      have h2 := hK23 ("ws", [0, 8, 16, 24, 32]) (by simp [sysTxKeep])
        (by rw [hg_rec]; exact hnz) off hoff
        (by change ∀ i ∈ bufRegions sysTxBufs s2, ¬ CellHits (globN s2 "ws" + off) i
            rw [hbuf21, hg_rec]; exact hno)
      rw [hg_rec] at h2
      exact h2.trans (hK12 ("ws", [0, 8, 16, 24, 32]) (by simp [sysTxKeep]) hnz off hoff hno)
    · have hg_rec : globN s2 "bs" = globN s1 "bs" :=
        globN_eq_of_lookup (hG12 (ofString "bs") (by decide))
      have h2 := hK23 ("bs", [0, 8, 16, 24, 32, 40, 48, 72]) (by simp [sysTxKeep])
        (by rw [hg_rec]; exact hnz) off hoff
        (by change ∀ i ∈ bufRegions sysTxBufs s2, ¬ CellHits (globN s2 "bs" + off) i
            rw [hbuf21, hg_rec]; exact hno)
      rw [hg_rec] at h2
      exact h2.trans (hK12 ("bs", [0, 8, 16, 24, 32, 40, 48, 72]) (by simp [sysTxKeep]) hnz off hoff hno)
    · cases hoff
    · have hg_rec : globN s2 "bo" = globN s1 "bo" :=
        globN_eq_of_lookup (hG12 (ofString "bo") (by decide))
      have h2 := hK23 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [sysTxKeep])
        (by rw [hg_rec]; exact hnz) off hoff
        (by change ∀ i ∈ bufRegions sysTxBufs s2, ¬ CellHits (globN s2 "bo" + off) i
            rw [hbuf21, hg_rec]; exact hno)
      rw [hg_rec] at h2
      exact h2.trans (hK12 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
        (by simp [sysTxKeep]) hnz off hoff hno)
  · intro S Nd hWT1 hD1
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, _⟩ := hW12 S Nd hWT1 hD1
    have hD2 : IvlsDisj (bufRegions sysTxBufs s2) (worldTypedIvls s2 S2 Nd2) :=
      validBufList_disj validBufList_sysTxBufs hWT2
    obtain ⟨S3, Nd3, hsub23, hWT3, hOG23, hFO23, _⟩ := hW23 S2 Nd2 hWT2 hD2
    refine ⟨S3, Nd3, fun t ht => hsub23 t (hsub12 t ht), hWT3, ?_, ?_, trivial⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          exact Prod.ext (by omega) (by omega)
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
            le_trans hin_oj.2 (le_trans hin_j12.2 hhp23)⟩)
      · exact Or.inr (Or.inr ⟨le_trans hhp12 hin_o23.1, hin_o23.2⟩)
    · intro a ha hhf
      have hm12 : s2.memory a = s1.memory a := hFO12 a ha hhf
      have hm23 : s3.memory a = s2.memory a := by
        apply hFO23 a
        · intro i hi hch
          obtain ⟨hc1, hc2⟩ := hch
          rcases List.mem_append.1 hi with hi1 | hfg2
          · rcases List.mem_append.1 hi1 with hwo2 | hR2
            · rcases hOG12 i hwo2 with rfl | ⟨k, hk, hin_ik⟩ | hin_i12
              · dsimp only at hc2; omega
              · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                  ⟨by dsimp only [Inside] at hin_ik; omega,
                   by dsimp only [Inside] at hin_ik; omega⟩
              · have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
                exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega,
                           by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega⟩
            · change i ∈ bufRegions sysTxBufs s2 at hR2
              rw [hbuf21] at hR2
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hR2)) ⟨hc1, hc2⟩
          · simp only [List.mem_singleton] at hfg2
            subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by
                have hc1' : a.toNat + 8 > globN s2 "frame_mem_ptr" := hc1
                change a.toNat + 8 > globN s1 "frame_mem_ptr"
                omega,
               by
                have hc2' : a.toNat < globN s2 "frame_mem_ptr" + (globN s2 "scratch_ptr" - globN s2 "frame_mem_ptr") := hc2
                have hfmp_sp2 : globN s2 "frame_mem_ptr" ≤ globN s2 "scratch_ptr" := hA2.2.2.2.2.1
                change a.toNat < globN s1 "frame_mem_ptr" + (globN s1 "scratch_ptr" - globN s1 "frame_mem_ptr")
                omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12

theorem sysTxPrefixStep_refl {F : Type}
    (s : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (hA : ArenaReady s) :
    SysTxPrefixStep s r s :=
  ⟨(WorldStepSc.refl s r hA).1, le_rfl, le_rfl, rfl, rfl⟩

theorem sysTxPrefixStep_with_locals_clock {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    (h : SysTxPrefixStep s r post)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    SysTxPrefixStep s r' { post with locals := L, clock := k } := by
  obtain ⟨⟨hAp, hhp, hG, hK, hW⟩, hfmp, hsp, hbn1, hbn2⟩ := h
  refine ⟨⟨localsFree_arenaReady post L k hAp, hhp, hG, hK, fun S Nd hWT hD => ?_⟩,
    hfmp, hsp, hbn1, hbn2⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hW S Nd hWT hD
  obtain ⟨hT', hJ', hF', hNH', hndisj', hws'⟩ := hWT'
  have hWT'' : WorldTypedWith { post with locals := L, clock := k } S' Nd' :=
    ⟨(tablesTyped_with_locals post L k S').2 hT', hJ', hF', hNH', hndisj', hws'⟩
  exact ⟨S', Nd', hsub, hWT'', hOG, hFO, trivial⟩

theorem sysTxPrefixStep_of_pre_locals_clock {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (h : SysTxPrefixStep { s with locals := L, clock := k } r post) :
    SysTxPrefixStep s r post := by
  obtain ⟨⟨hAp, hhp, hG, hK, hW⟩, hfmp, hsp, hbn1, hbn2⟩ := h
  refine ⟨⟨hAp, hhp, hG, hK, fun S Nd hWT hD => ?_⟩, hfmp, hsp, hbn1, hbn2⟩
  obtain ⟨hT, hJ, hF, hNH, hndisj, hws⟩ := hWT
  have hWT' : WorldTypedWith { s with locals := L, clock := k } S Nd :=
    ⟨(tablesTyped_with_locals s L k S).2 hT, hJ, hF, hNH, hndisj, hws⟩
  exact hW S Nd hWT' hD

theorem sysTxPrefixStep_from_entry {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    {callee L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (h : SysTxPrefixStep (callEntryStateHOLFinite s callee) r post) :
    SysTxPrefixStep s r' { post with locals := L, clock := k } :=
  sysTxPrefixStep_with_locals_clock (sysTxPrefixStep_of_pre_locals_clock h) L k

theorem sysTxPrefixStep_trans {F : Type}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hA1 : ArenaReady s1)
    (h12 : SysTxPrefixStep s1 r1 s2)
    (h23 : SysTxPrefixStep s2 r2 s3) :
    SysTxPrefixStep s1 r2 s3 :=
  ⟨worldStep_sysTx_trans_prefix hA1 h12 h23.1,
    le_trans h12.2.1 h23.2.1,
    le_trans h23.2.2.1 h12.2.2.1,
    h23.2.2.2.1.trans h12.2.2.2.1,
    h23.2.2.2.2.trans h12.2.2.2.2⟩

theorem worldStep_with_locals_clock {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    (h : WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s r post)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra
      s r' { post with locals := L, clock := k } := by
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := h
  refine ⟨localsFree_arenaReady post L k hAp, hhp, hG, hK, fun S Nd hWT hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hW S Nd hWT hD
  obtain ⟨hT', hJ', hF', hNH', hndisj', hws'⟩ := hWT'
  have hWT'' : WorldTypedWith { post with locals := L, clock := k } S' Nd' :=
    ⟨(tablesTyped_with_locals post L k S').2 hT', hJ', hF', hNH', hndisj', hws'⟩
  exact ⟨S', Nd', hsub, hWT'', hOG, hFO, trivial⟩

theorem worldStep_of_pre_locals_clock {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (h : WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra
      { s with locals := L, clock := k } r post) :
    WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s r post := by
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := h
  refine ⟨hAp, hhp, hG, hK, fun S Nd hWT hD => ?_⟩
  obtain ⟨hT, hJ, hF, hNH, hndisj, hws⟩ := hWT
  have hWT' : WorldTypedWith { s with locals := L, clock := k } S Nd :=
    ⟨(tablesTyped_with_locals s L k S).2 hT, hJ, hF, hNH, hndisj, hws⟩
  exact hW S Nd hWT' hD

theorem worldStep_from_entry {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    {callee L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (h : WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra
      (callEntryStateHOLFinite s callee) r post) :
    WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra
      s r' { post with locals := L, clock := k } :=
  worldStep_with_locals_clock (worldStep_of_pre_locals_clock h) L k

theorem worldOK_of_sysTxStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hs : WorldOK s)
    (h : WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s r post) :
    WorldOK post := by
  obtain ⟨_, S, hS⟩ := hs
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hS
  exact h.worldOK ⟨S, Nd, hWT, validBufList_disj validBufList_sysTxBufs hWT⟩

def ProgPrefixStep (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → WorldOK s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowingOrResumes (evaluateHOLFiniteState s prog).1 →
    SysTxPrefixStep s (evaluateHOLFiniteState s prog).1 (evaluateHOLFiniteState s prog).2

def ProgSysTxStep (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → WorldOK s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowingOrResumes (evaluateHOLFiniteState s prog).1 →
    WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra
      s (evaluateHOLFiniteState s prog).1 (evaluateHOLFiniteState s prog).2

theorem progSysTxStep_of_prefix {prog : ProgHOL 64} (h : ProgPrefixStep prog) :
    ProgSysTxStep prog :=
  fun s hc hW hnt hfr => (h s hc hW hnt hfr).1

theorem progPrefixStep_skip : ProgPrefixStep .skip := by
  intro F s _ hW _ _
  rw [evaluateHOLFiniteState_skip]
  exact sysTxPrefixStep_refl s none hW.1

theorem progPrefixStep_return (e : ExpHOL 64) : ProgPrefixStep (.return e) := by
  intro F s _ hW _ hfr
  rw [evaluateHOLFiniteState_return] at hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hfr ⊢
    split
    · exact sysTxPrefixStep_with_locals_clock (sysTxPrefixStep_refl s none hW.1) _ s.clock
    · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progPrefixStep_raise (eid : MlS) (e : ExpHOL 64) : ProgPrefixStep (.raise eid e) := by
  intro F s _ hW _ hfr
  rw [evaluateHOLFiniteState_raise] at hfr ⊢
  rcases hsh : s.eshapes.lookup eid with _ | sh
  · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hsh] at hfr ⊢
    rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hev] at hfr ⊢
      split
      · exact sysTxPrefixStep_with_locals_clock (sysTxPrefixStep_refl s none hW.1) _ s.clock
      · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progPrefixStep_dec {x : MlS} {sh : ShapeHOL} {e : ExpHOL 64}
    {body : ProgHOL 64} (hb : ProgPrefixStep body) :
    ProgPrefixStep (.dec x sh e body) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hnt hfr ⊢
    by_cases hok : shapeEqHOL sh (shapeOfHOLExact val) = true
    · simp only [hok, ↓reduceIte] at hnt hfr ⊢
      set s1 := setVarHOLFinite x val s
      have hW1 : WorldOK s1 := localsFree_worldOK s _ s.clock hW
      have hstep := hb s1 hc hW1 hnt hfr
      exact sysTxPrefixStep_with_locals_clock
        (sysTxPrefixStep_of_pre_locals_clock hstep) _ (evaluateHOLFiniteState s1 body).2.clock
    · simp [hok] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progPrefixStep_ite {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hy : ProgPrefixStep yes) (hn : ProgPrefixStep no) :
    ProgPrefixStep (.ite cond yes no) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · rcases cv with ⟨⟨w⟩⟩ | _ | _
    · simp only [hev] at hnt hfr ⊢
      by_cases hw : w = 0
      · simp only [hw, ↓reduceIte] at hnt hfr ⊢; exact hn s hc hW hnt hfr
      · simp only [hw, ↓reduceIte] at hnt hfr ⊢; exact hy s hc hW hnt hfr
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progPrefixStep_seq {p1 p2 : ProgHOL 64}
    (h1 : ProgPrefixStep p1) (h2 : ProgPrefixStep p2) :
    ProgPrefixStep (.seq p1 p2) := by
  intro F s hc hW hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p1).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hfr ⊢
  cases r1 with
  | none =>
    have hs1 := h1 s hc hW (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hs1
    dsimp only at hs1
    have hs2 := h2 mid (hmeta.trans hc) (worldOK_of_sysTxStep hW hs1.1) hnt hfr
    exact ⟨worldStep_sysTx_trans_prefix hW.1 hs1 hs2.1,
      le_trans hs1.2.1 hs2.2.1, le_trans hs2.2.2.1 hs1.2.2.1,
      hs2.2.2.2.1.trans hs1.2.2.2.1, hs2.2.2.2.2.trans hs1.2.2.2.2⟩
  | some _ =>
    have hs1 := h1 s hc hW (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    simpa only [hr1] using hs1

theorem progSysTxStep_seq_prefix {p1 p2 : ProgHOL 64}
    (h1 : ProgPrefixStep p1) (h2 : ProgSysTxStep p2) :
    ProgSysTxStep (.seq p1 p2) := by
  intro F s hc hW hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p1).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hfr ⊢
  cases r1 with
  | none =>
    have hs1 := h1 s hc hW (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hs1; dsimp only at hs1
    have hW_mid : WorldOK mid := worldOK_of_sysTxStep hW hs1.1
    have hs2 := h2 mid (hmeta.trans hc) hW_mid hnt hfr
    exact worldStep_sysTx_trans_prefix hW.1 hs1 hs2
  | some _ =>
    have hs1 := h1 s hc hW (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hs1
    exact hs1.1

theorem progSysTxStep_decCall_prefix
    {x : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : FunSpec WorldOK (fun s r post => Resumes r → SysTxPrefixStep s r post) fname)
    (hcont : ProgSysTxStep cont) :
    ProgSysTxStep (.decCall x sh fname args cont) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun hmeta
        simp only [hrun] at hmeta hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              have hstep1 := hspec (Or.inl ⟨v, rfl⟩)
              set s1 := setVarHOLFinite x v { cpost with locals := s.locals }
              have hs1_step : SysTxPrefixStep s none s1 :=
                sysTxPrefixStep_from_entry (post := cpost) (L := s1.locals) hstep1
              have hWs1 : WorldOK s1 := worldOK_of_sysTxStep hW hs1_step.1
              have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hc
              have hstep2 := hcont s1 hs1_code hWs1 hnt hfr
              have hstep2' := worldStep_with_locals_clock (r' := (evaluateHOLFiniteState s1 cont).1) hstep2
                (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x))
                (evaluateHOLFiniteState s1 cont).2.clock
              exact worldStep_sysTx_trans_prefix hW.1 hs1_step hstep2'
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact (sysTxPrefixStep_from_entry (hspec hres_ex)).1

theorem progPrefixStep_decCall
    {x : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : FunSpec WorldOK (fun s r post => Resumes r → SysTxPrefixStep s r post) fname)
    (hcont : ProgPrefixStep cont) :
    ProgPrefixStep (.decCall x sh fname args cont) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun hmeta
        simp only [hrun] at hmeta hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              have hstep1 := hspec (Or.inl ⟨v, rfl⟩)
              set s1 := setVarHOLFinite x v { cpost with locals := s.locals }
              have hs1_step : SysTxPrefixStep s none s1 :=
                sysTxPrefixStep_from_entry (post := cpost) (L := s1.locals) hstep1
              have hWs1 : WorldOK s1 := worldOK_of_sysTxStep hW hs1_step.1
              have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hc
              have hstep2 := hcont s1 hs1_code hWs1 hnt hfr
              have hstep2' := sysTxPrefixStep_with_locals_clock (r' := (evaluateHOLFiniteState s1 cont).1) hstep2
                (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x))
                (evaluateHOLFiniteState s1 cont).2.clock
              exact sysTxPrefixStep_trans hW.1 hs1_step hstep2'
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact sysTxPrefixStep_from_entry (hspec hres_ex)

theorem progPrefixStep_call0
    {fname : MlS} {args : List (ExpHOL 64)}
    (hf : FunSpec WorldOK (fun s r post => Resumes r → SysTxPrefixStep s r post) fname) :
    ProgPrefixStep (.call (some (none, none)) fname args) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun
        simp only [hrun] at hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hfr ⊢
            split
            · have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              exact sysTxPrefixStep_from_entry (hspec (Or.inl ⟨v, rfl⟩))
            · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact sysTxPrefixStep_from_entry (hspec hres_ex)

def ProgLocalsOnly (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    FlowingOrResumes (evaluateHOLFiniteState s prog).1 →
    (evaluateHOLFiniteState s prog).2 =
      { s with locals := (evaluateHOLFiniteState s prog).2.locals,
               clock := (evaluateHOLFiniteState s prog).2.clock }

theorem progLocalsOnly_skip : ProgLocalsOnly .skip := by
  intro F s _
  rw [evaluateHOLFiniteState_skip]

theorem progLocalsOnly_return (e : ExpHOL 64) : ProgLocalsOnly (.return e) := by
  intro F s hfr
  rw [evaluateHOLFiniteState_return] at hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hfr ⊢
    split
    · rfl
    · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progLocalsOnly_raise (eid : MlS) (e : ExpHOL 64) : ProgLocalsOnly (.raise eid e) := by
  intro F s hfr
  rw [evaluateHOLFiniteState_raise] at hfr ⊢
  rcases hsh : s.eshapes.lookup eid with _ | sh
  · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hsh] at hfr ⊢
    rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hev] at hfr ⊢
      split
      · rfl
      · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progLocalsOnly_ite {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hy : ProgLocalsOnly yes) (hn : ProgLocalsOnly no) :
    ProgLocalsOnly (.ite cond yes no) := by
  intro F s hfr
  rw [evaluateHOLFiniteState_ite] at hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · rcases cv with ⟨⟨w⟩⟩ | _ | _
    · simp only [hev] at hfr ⊢
      by_cases hw : w = 0
      · simp only [hw, ↓reduceIte] at hfr ⊢; exact hn s hfr
      · simp only [hw, ↓reduceIte] at hfr ⊢; exact hy s hfr
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progLocalsOnly_seq {p1 p2 : ProgHOL 64}
    (h1 : ProgLocalsOnly p1) (h2 : ProgLocalsOnly p2) :
    ProgLocalsOnly (.seq p1 p2) := by
  intro F s hfr
  rw [evaluateHOLFiniteState_seq_line780] at hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, mid⟩
  simp only [hr1] at hfr ⊢
  cases r1 with
  | none =>
    have hm1 : mid = { s with locals := mid.locals, clock := mid.clock } := by
      have h := h1 s (by rw [hr1]; exact Or.inl rfl)
      simpa [hr1] using h
    have hm2 := h2 mid hfr
    rw [hm2, hm1]
  | some _ =>
    have hm1 := h1 s (by rw [hr1]; exact hfr)
    simpa [hr1] using hm1

theorem progSysTxStep_decCall_tail
    {x : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : WorldKeeps WorldOK (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra fname)
    (hcont : ProgLocalsOnly cont) :
    ProgSysTxStep (.decCall x sh fname args cont) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun
        simp only [hrun] at hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              have hstep1 := hspec (Or.inl ⟨v, rfl⟩)
              set s1 := setVarHOLFinite x v { cpost with locals := s.locals }
              have hs1_step : WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s none s1 :=
                worldStep_from_entry (post := cpost) (L := s1.locals) hstep1
              have hlo := hcont s1 hfr
              have hfinal : { (evaluateHOLFiniteState s1 cont).2 with
                  locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x) } =
                  { s1 with
                    locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x),
                    clock := (evaluateHOLFiniteState s1 cont).2.clock } := by
                conv_lhs => rw [hlo]
              rw [hfinal]
              exact worldStep_with_locals_clock hs1_step _ _
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact worldStep_from_entry (hspec hres_ex)

theorem sysTxPrefix_state_fresh_tx :
    FunSpec WorldOK (fun s r post => Resumes r → SysTxPrefixStep s r post)
      (ofString "state_fresh_tx") := by
  obtain ⟨ps, body, ret, hl, hb⟩ := WkBal.wk_state_fresh_tx
  refine ⟨ps, body, ret, hl, fun s hc hW hex hnt hres => ?_⟩
  have hstep := hb s hc hW hex hnt hres
  have hG := hstep.2.2.1
  have hfmp : globN (evaluateHOLFiniteState s body).2 "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    globN_eq_of_lookup (hG (ofString "frame_mem_ptr") (by decide))
  have hsp : globN (evaluateHOLFiniteState s body).2 "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hG (ofString "scratch_ptr") (by decide))
  have hbn1 : globN (evaluateHOLFiniteState s body).2 "bn_expw" = globN s "bn_expw" :=
    globN_eq_of_lookup (hG (ofString "bn_expw") (by decide))
  have hbn2 : globN (evaluateHOLFiniteState s body).2 "bn_gamma" = globN s "bn_gamma" :=
    globN_eq_of_lookup (hG (ofString "bn_gamma") (by decide))
  have hwStep : WorldStep (bufRegions []) ["heap_ptr", "journal_n", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2 :=
    hstep
  refine ⟨worldStep_mono_bufs_keep (fun _ h => by cases h)
      (by intro g hg; simp at hg; rcases hg with rfl | rfl | rfl <;> simp [sysTxGlobals])
      keepSub_sysTxKeep_freshTx hwStep,
    by rw [hfmp], by rw [hsp], hbn1, hbn2⟩

theorem sysTxPrefix_ext_code_of :
    FunSpec WorldOK (fun s r post => Resumes r → SysTxPrefixStep s r post)
      (ofString "ext_code_of") := by
  obtain ⟨ps, body, ret, hl, hb⟩ := wkSc_ext_code_of
  refine ⟨ps, body, ret, hl, fun s hc hW hex hnt hres => ?_⟩
  obtain ⟨hstep, hsp⟩ := hb s hc hW hex hnt hres
  have hG := hstep.2.2.1
  have hfmp : globN (evaluateHOLFiniteState s body).2 "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    globN_eq_of_lookup (hG (ofString "frame_mem_ptr") (by decide))
  have hbn1 : globN (evaluateHOLFiniteState s body).2 "bn_expw" = globN s "bn_expw" :=
    globN_eq_of_lookup (hG (ofString "bn_expw") (by decide))
  have hbn2 : globN (evaluateHOLFiniteState s body).2 "bn_gamma" = globN s "bn_gamma" :=
    globN_eq_of_lookup (hG (ofString "bn_gamma") (by decide))
  refine ⟨worldStep_mono_bufs_keep
      (by intro p hp
          simp only [extCodeBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl <;> simp [sysTxBufs])
      (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp [sysTxGlobals])
      keepSub_sysTxKeep_stdKeep hstep,
    by rw [hfmp], hsp, hbn1, hbn2⟩

theorem sysTxPrefix_of_heapOnly
    {fname : MlS}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hf : WorldKeeps WorldOK (bufRegions []) ["heap_ptr"] stdKeep Q fname) :
    FunSpec WorldOK (fun s r post => Resumes r → SysTxPrefixStep s r post) fname := by
  obtain ⟨ps, body, ret, hl, hb⟩ := hf
  refine ⟨ps, body, ret, hl, fun s hc hW hex hnt hres => ?_⟩
  have hstep := hb s hc hW hex hnt hres
  have hG := hstep.2.2.1
  have hfmp : globN (evaluateHOLFiniteState s body).2 "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    globN_eq_of_lookup (hG (ofString "frame_mem_ptr") (by decide))
  have hsp : globN (evaluateHOLFiniteState s body).2 "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hG (ofString "scratch_ptr") (by decide))
  have hbn1 : globN (evaluateHOLFiniteState s body).2 "bn_expw" = globN s "bn_expw" :=
    globN_eq_of_lookup (hG (ofString "bn_expw") (by decide))
  have hbn2 : globN (evaluateHOLFiniteState s body).2 "bn_gamma" = globN s "bn_gamma" :=
    globN_eq_of_lookup (hG (ofString "bn_gamma") (by decide))
  refine ⟨worldStep_mono_bufs_keep (fun _ h => by cases h)
      (by intro g hg; simp at hg; subst hg; simp [sysTxGlobals])
      keepSub_sysTxKeep_stdKeep hstep,
    by rw [hfmp], by rw [hsp], hbn1, hbn2⟩

theorem sysTxPrefix_alloc :
    FunSpec WorldOK (fun s r post => Resumes r → SysTxPrefixStep s r post)
      (ofString "alloc") :=
  sysTxPrefix_of_heapOnly R13Shards.wk_alloc_impl

theorem sysTxPrefix_te_new :
    FunSpec WorldOK (fun s r post => Resumes r → SysTxPrefixStep s r post)
      (ofString "te_new") :=
  sysTxPrefix_of_heapOnly R13Wk06b.wk_te_new

theorem sysTxPrefix_msg_new :
    FunSpec WorldOK (fun s r post => Resumes r → SysTxPrefixStep s r post)
      (ofString "msg_new") :=
  sysTxPrefix_of_heapOnly R13Wk06b.wk_msg_new

theorem panMemStoresHOL_frame_sysTx {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (ws : List (HolWordLab 64)) (x : BitVec 64) (mem mem' : BitVec 64 → HolWordLab 64),
      @panMemStoresHOL 64 _ x ws dom dec mem = some mem' →
      ∀ a : BitVec 64, (∀ k, k < ws.length → a ≠ x + BitVec.ofNat 64 (8 * k)) → mem' a = mem a
  | [], _, mem, mem', hst, a, _ => by
    simp only [panMemStoresHOL, Option.some.injEq] at hst
    rw [← hst]
  | w :: ws, x, mem, mem', hst, a, hne => by
    unfold panMemStoresHOL panMemStoreHOL at hst
    split_ifs at hst with hdom
    have hbw : (panBytesInWord 64 : BitVec 64) = BitVec.ofNat 64 8 := by decide
    have ih := panMemStoresHOL_frame_sysTx ws (x + panBytesInWord 64)
      (fun current => if current = x then w else mem current) mem' hst a (fun k hk => by
        have hk1 : k + 1 < (w :: ws).length := by simp; omega
        have hne1 := hne (k + 1) hk1
        rw [hbw]
        intro heq
        apply hne1
        rw [heq, BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega)
    rw [ih]
    exact if_neg (by simpa using hne 0 (by simp))

theorem panMemStoresHOL_dom_of_ne {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (ws : List (HolWordLab 64)) (x : BitVec 64) (mem mem' : BitVec 64 → HolWordLab 64),
      @panMemStoresHOL 64 _ x ws dom dec mem = some mem' →
      ∀ a : BitVec 64, mem' a ≠ mem a → dom a
  | [], _, mem, mem', hst, a, hne => by
    simp only [panMemStoresHOL, Option.some.injEq] at hst
    subst hst
    exact absurd rfl hne
  | w :: ws, x, mem, mem', hst, a, hne => by
    unfold panMemStoresHOL panMemStoreHOL at hst
    split_ifs at hst with hdom
    by_cases hax : a = x
    · subst hax; exact hdom
    · have hprev : (fun current => if current = x then w else mem current) a = mem a := if_neg hax
      exact panMemStoresHOL_dom_of_ne ws (x + panBytesInWord 64)
        (fun current => if current = x then w else mem current) mem' hst a (by simpa only [if_neg hax] using hne)

theorem panMemStoresHOL_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom}
    {ws : List (HolWordLab 64)} {x : BitVec 64} {mem mem' : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ x ws dom dec mem = some mem')
    {a : BitVec 64} (ha : ¬ dom a) : mem' a = mem a := by
  by_contra hne
  exact ha (panMemStoresHOL_dom_of_ne ws x mem mem' hst a hne)

theorem panMemStore32HOL_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom}
    {mem mem' : BitVec 64 → HolWordLab 64} {be : Bool} {addr : BitVec 64} {val : BitVec 32}
    (hst : @panMemStore32HOL 64 _ mem dom dec be addr val = some mem')
    {a : BitVec 64} (ha : ¬ dom a) : mem' a = mem a := by
  unfold panMemStore32HOL at hst
  split at hst
  · dsimp only at hst
    cases hm : mem (panByteAlignHOL (width := 64) addr) with
    | word cell =>
      rw [hm] at hst
      dsimp only at hst
      split at hst
      · rename_i hdom
        simp only [Option.some.injEq] at hst
        subst hst
        exact if_neg (fun heq : a = panByteAlignHOL (width := 64) addr =>
          ha (heq.symm ▸ hdom))
      · cases hst
  · cases hst

theorem panMemStoreByteWord8HOL_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom}
    {mem mem' : BitVec 64 → HolWordLab 64} {be : Bool} {addr : BitVec 64} {b : BitVec 8}
    (hst : @panMemStoreByteWord8HOL 64 _ mem dom dec be addr b = some mem')
    {a : BitVec 64} (ha : ¬ dom a) : mem' a = mem a := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hm : mem (panByteAlignHOL (width := 64) addr) with
  | word cell =>
    rw [hm] at hst
    dsimp only at hst
    split at hst
    · rename_i hdom
      simp only [Option.some.injEq] at hst
      subst hst
      exact if_neg (fun heq : a = panByteAlignHOL (width := 64) addr =>
        ha (heq.symm ▸ hdom))
    · cases hst

theorem panWriteBytearrayWord8HOL_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (bs : List (BitVec 8)) (addr : BitVec 64) (mem : BitVec 64 → HolWordLab 64) (be : Bool)
      {a : BitVec 64}, ¬ dom a →
      @panWriteBytearrayWord8HOL 64 _ addr bs mem dom dec be a = mem a
  | [], _, _, _, _, _ => rfl
  | b :: bs, addr, mem, be, a, ha => by
    unfold panWriteBytearrayWord8HOL
    cases hst : @panMemStoreByteWord8HOL 64 _
        (@panWriteBytearrayWord8HOL 64 _ (addr + 1) bs mem dom dec be) dom dec be addr b with
    | none => rfl
    | some updated =>
      exact (panMemStoreByteWord8HOL_out_dom hst ha).trans
        (panWriteBytearrayWord8HOL_out_dom bs (addr + 1) mem be ha)

theorem shMemStore_mem_eq {F : Type} (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (address value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemStore operator address value)).2.memory = state.memory := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · unfold shMemStoreHOLExact
    split <;> split
    all_goals simp [ofExact, toExact]
    all_goals split <;> simp
  · rfl

theorem shMemLoad_mem_eq {F : Type} (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (kind : VarKind) (name : MlS) (address : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemLoad operator kind name address)).2.memory = state.memory := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source]
  split
  · split
    · unfold shMemLoadHOLFiniteExact
      dsimp only
      cases kind <;> split <;> split <;> (try split) <;>
        simp [emptyLocalsHOLFinite, setKvarFfiHOLFinite, setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite]
    · rfl
  · rfl

theorem call_out_dom_aux {F : Type}
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (function : MlS) (arguments : List (ExpHOL 64)) (state : PanSemStateFiniteExact 64 F)
    {a : BitVec 64} (ha : ¬ state.memaddrs a)
    (ihBody : ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup function values = some (body, callee, rs) →
      state.clock ≠ 0 →
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.memory a = state.memory a)
    (ihHandler : ∀ dest hid hv hp, info = some (dest, some (hid, hv, hp)) →
      ∀ (t : PanSemStateFiniteExact 64 F),
        t.clock < state.clock → ¬ t.memaddrs a →
        (evaluateHOLFiniteState t hp).2.memory a = t.memory a) :
    (evaluateHOLFiniteState state (.call info function arguments)).2.memory a = state.memory a := by
  rw [evaluateHOLFiniteState_call]
  split
  · rfl
  · rename_i values _
    split
    · rfl
    · rename_i body callee rs found
      split
      · rfl
      · rename_i nonzero
        have ih := ihBody values body callee rs found nonzero
        have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite state callee) body
        have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
        generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
        obtain ⟨r, st⟩ := out
        dsimp only at ih meta' cl ⊢
        change st.clock ≤ state.clock - 1 at cl
        have stc : st.clock < state.clock := by omega
        have st_ha : ¬ st.memaddrs a := by
          have hm : st.memaddrs = state.memaddrs := meta'.2.1
          rw [hm]; exact ha
        rcases info with _ | ⟨dest, handler⟩
        · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
            simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite, emptyLocalsHOLFinite, ih]
        · rcases handler with _ | ⟨hid, hv, hp⟩
          · rcases dest with _ | ⟨⟨⟩, nm⟩ <;>
              rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite, emptyLocalsHOLFinite, ih]
          · rcases dest with _ | ⟨⟨⟩, nm⟩ <;>
              rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              first
                | (exact (ihHandler _ hid hv hp rfl _ (by exact stc) (by exact st_ha)).trans ih)
                | (simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite, emptyLocalsHOLFinite, ih])

theorem evaluateHOLFiniteState_mem_out_dom {F : Type}
    (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64)
    {a : BitVec 64} (ha : ¬ state.memaddrs a) :
    (evaluateHOLFiniteState state program).2.memory a = state.memory a := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · split
      · exact evaluateHOLFiniteState_mem_out_dom _ body ha
      · rfl
  | decCall name kind function arguments continuation =>
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        split
        · rfl
        · rename_i nonzero
          dsimp only
          have ih : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.memory a = state.memory a :=
            evaluateHOLFiniteState_mem_out_dom (callEntryStateHOLFinite state callee) body ha
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
            (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at ih meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have st_ha : ¬ st.memaddrs a := by
            have hm : st.memaddrs = state.memaddrs := meta'.2.1
            rw [hm]; exact ha
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [emptyLocalsHOLFinite])
          all_goals (try exact ih)
          split
          · have small : st.clock < state.clock := by omega
            exact (evaluateHOLFiniteState_mem_out_dom
              (setVarHOLFinite name v { st with locals := state.locals })
              continuation st_ha).trans ih
          · exact ih
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · rfl
    · split
      · cases kind <;> rfl
      · rfl
  | seq first second =>
    have memory := evaluateHOLFiniteState_mem_out_dom state first ha
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at memory remaining meta'
      dsimp only at memory remaining meta'
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        have m_ha : ¬ middle.memaddrs a := by rw [meta'.2.1]; exact ha
        exact (evaluateHOLFiniteState_mem_out_dom middle second m_ha).trans memory
      | some _ => exact memory
  | ite condition yes no =>
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluateHOLFiniteState_mem_out_dom state no ha
      · exact evaluateHOLFiniteState_mem_out_dom state yes ha
    · rfl
  | «while» condition body =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have memory := evaluateHOLFiniteState_mem_out_dom (decClockHOLFinite state) body ha
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
            (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at memory remaining meta'
            dsimp only at memory remaining meta'
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            have m_ha : ¬ middle.memaddrs a := by rw [meta'.2.1]; exact ha
            cases result with
            | none => exact (evaluateHOLFiniteState_mem_out_dom middle (.while condition body) m_ha).trans memory
            | some result =>
              cases result with
              | «continue» =>
                exact (evaluateHOLFiniteState_mem_out_dom middle (.while condition body) m_ha).trans memory
              | «break» | returned _ | exception _ _ | finalFfi _ | error | timeOut => exact memory
      · rfl
    · rfl
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot _ _ => rw [evaluateHOLFiniteState_annot]
  | tick =>
    rw [evaluateHOLFiniteState_tick]
    split <;> rfl
  | raise _ value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> rfl
    · rfl
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  | store destination value =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · rename_i mem' hst
          exact panMemStoresHOL_out_dom hst ha
        · rfl
      · rfl
    · rfl
  | store32 destination value =>
    rw [evaluateHOLFiniteState_store32]
    split
    · split
      · split
        · rename_i mem' hst
          exact panMemStore32HOL_out_dom hst ha
        · rfl
      · rfl
    · rfl
  | storeByte destination value =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · rename_i mem' hst
          exact panMemStoreByteWord8HOL_out_dom hst ha
        · rfl
      · rfl
    · rfl
  | extCall _ _ _ _ _ =>
    rw [evaluateHOLFiniteState_extCall_source]
    split
    · split
      · split
        · rfl
        · dsimp only [ofExact, toExact]
          exact panWriteBytearrayWord8HOL_out_dom _ _ _ _ ha
      · rfl
    · rfl
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | shMemStore op addr val =>
    exact congrFun (shMemStore_mem_eq state op addr val) a
  | shMemLoad op kind name addr =>
    exact congrFun (shMemLoad_mem_eq state op kind name addr) a
  | call info function arguments =>
    refine call_out_dom_aux info function arguments state ha
      (fun values body callee rs _ _ =>
        evaluateHOLFiniteState_mem_out_dom (callEntryStateHOLFinite state callee) body ha)
      (fun _ _ _ hp _ t _ tha => evaluateHOLFiniteState_mem_out_dom t hp tha)
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | (simp only [callEntryStateHOLFinite] at small; exact Or.inl small)
      | omega
      | (by_cases hc : state.clock = 0
         · right; refine ⟨by omega, ?_⟩; simp +arith
         · left; omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · right; refine ⟨h, ?_⟩; simp +arith)
      | (right; refine ⟨rfl, ?_⟩; simp +arith)

theorem worldStep_store_in_block {F : Type}
    {s : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {base sz off : Nat} {w_base x : BitVec 64} {v : ValueHOL 64}
    {mem' : BitVec 64 → HolWordLab 64}
    (hW : WorldOK s)
    (hbase_lu : w_base.toNat = base)
    (hbase8 : base % 8 = 0) (_hsz8 : sz % 8 = 0) (_hoff8 : off % 8 = 0)
    (hin_blk : Inside (base, sz) sourceBase (globN s "heap_ptr"))
    (hx_eq : x = w_base + BitVec.ofNat 64 off)
    (hoff_fit : off + 8 * (flattenHOL v).length ≤ sz)
    (hst : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    WorldStep (fun _ => [(base, sz)]) [] stdKeep NoExtra s r { s with memory := mem' } := by
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hW.1.2.2.1
  have hx_nat : x.toNat = base + off := by
    rw [hx_eq, BitVec.toNat_add, hbase_lu, BitVec.toNat_ofNat]
    have hoff_lt : off < 2 ^ 64 := by unfold Inside at hin_blk; omega
    rw [Nat.mod_eq_of_lt hoff_lt]
    exact Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)
  have hcell : ∀ a : BitVec 64, ¬ CellHits a.toNat (base, sz) → mem' a = s.memory a := by
    intro a hnh
    apply panMemStoresHOL_frame_sysTx (flattenHOL v) x s.memory mem' hst a
    intro k hk h_eq
    apply hnh
    have ha_nat : a.toNat = base + off + 8 * k := by
      rw [h_eq, BitVec.toNat_add, hx_nat, BitVec.toNat_ofNat]
      have hk_lt : 8 * k < 2 ^ 64 := by unfold Inside at hin_blk; omega
      rw [Nat.mod_eq_of_lt hk_lt]
      exact Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)
    unfold CellHits
    rw [ha_nat]
    exact ⟨by omega, by omega⟩
  refine InitECandidate.Solver.Wave8Contracts.M08.worldStep_of_region_writes
    (r := r) (R := fun _ => [(base, sz)]) hW
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun a hkeep _ => hcell a (hkeep (base, sz) (by simp)))
    (fun b hb64 hnb => ?_)
    (fun a hne => panMemStoresHOL_dom_of_ne (flattenHOL v) x s.memory mem' hst a hne)
  unfold memB
  dsimp only
  have hal_eq : mem' (panByteAlignHOL (BitVec.ofNat 64 b)) =
      s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
    apply hcell
    intro ⟨hc1, hc2⟩
    have hal_nat : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
      rw [panByteAlign_toNat64,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64]
    rw [hal_nat] at hc1 hc2
    exact hnb (base, sz) (by simp) ⟨by omega, by omega⟩
  rw [hal_eq]

theorem worldTypedIvls_sub_worldOwned_sysTx {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) : ∀ i ∈ worldTypedIvls s S Nd, i ∈ worldOwned s S Nd := by
  intro i hi
  unfold worldTypedIvls at hi
  unfold worldOwned
  simp only [List.mem_append] at hi ⊢
  rcases hi with ((((ht | hr) | hjr) | hbo) | hbal) | hnd
  · exact Or.inl (Or.inl ht)
  · obtain ⟨r, hrec, rfl⟩ := List.mem_map.1 hr
    refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    refine List.mem_map.2 ⟨r, ?_, rfl⟩
    simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl <;> decide
  · refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    exact hjr
  · refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_right
    exact hbo
  · refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    exact List.mem_append_right _ hbal
  · exact Or.inr hnd

theorem sysTxPrefix_store_fresh_block {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {base sz off : Nat} {w_base x : BitVec 64} {v : ValueHOL 64}
    {mem' : BitVec 64 → HolWordLab 64}
    (hW0 : WorldOK s0) (h0 : SysTxPrefixStep s0 none s)
    (hbase_lu : w_base.toNat = base)
    (hbase8 : base % 8 = 0) (hsz8 : sz % 8 = 0) (hoff8 : off % 8 = 0)
    (hin_fresh : Inside (base, sz) (globN s0 "heap_ptr") (globN s "heap_ptr"))
    (hdisj_step : ∀ S Nd, WorldTypedWith s0 S Nd →
      IvlsDisj (bufRegions sysTxBufs s0) (worldTypedIvls s0 S Nd) →
      ∃ S' Nd',
        (∀ t ∈ S, t ∈ S') ∧
        WorldTypedWith s S' Nd' ∧
        OwnedGrows s0 s (worldOwned s0 S Nd) (worldOwned s S' Nd') ∧
        FrameOutside s0 s (worldOwned s0 S Nd ++ bufRegions sysTxBufs s0 ++ [freeGap s0]) (heapFree s0) ∧
        IvlsDisj [(base, sz)] (worldOwned s S' Nd'))
    (hx_eq : x = w_base + BitVec.ofNat 64 off)
    (hoff_fit : off + 8 * (flattenHOL v).length ≤ sz)
    (hst : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    SysTxPrefixStep s0 r { s with memory := mem' } ∧
      WorldOK { s with memory := mem' } := by
  have hWs : WorldOK s := worldOK_of_sysTxStep hW0 h0.1
  have hp0_lo : sourceBase ≤ globN s0 "heap_ptr" := hW0.1.2.1
  have hin_blk : Inside (base, sz) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hp0_lo hin_fresh.1, hin_fresh.2⟩
  have hst_blk : WorldStep (fun _ => [(base, sz)]) [] stdKeep NoExtra s r { s with memory := mem' } :=
    worldStep_store_in_block hWs hbase_lu hbase8 hsz8 hoff8 hin_blk hx_eq hoff_fit hst
  obtain ⟨⟨hAs, hhp0s, hG0s, hK0s, _⟩, hfmp0s, hsp0s, hbn1, hbn2⟩ := h0
  obtain ⟨hAp, _, _, hK_st, hW_st⟩ := hst_blk
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hx_nat : x.toNat = base + off := by
    rw [hx_eq, BitVec.toNat_add, hbase_lu, BitVec.toNat_ofNat]
    have hoff_lt : off < 2 ^ 64 := by unfold Inside at hin_blk; omega
    rw [Nat.mod_eq_of_lt hoff_lt]
    exact Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)
  have hcell_blk : ∀ a : BitVec 64, ¬ CellHits a.toNat (base, sz) → mem' a = s.memory a := by
    intro a hnh
    apply panMemStoresHOL_frame_sysTx (flattenHOL v) x s.memory mem' hst a
    intro k hk h_eq
    apply hnh
    have ha_nat : a.toNat = base + off + 8 * k := by
      rw [h_eq, BitVec.toNat_add, hx_nat, BitVec.toNat_ofNat]
      have hk_lt : 8 * k < 2 ^ 64 := by unfold Inside at hin_blk; omega
      rw [Nat.mod_eq_of_lt hk_lt]
      exact Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)
    unfold CellHits
    rw [ha_nat]
    exact ⟨by omega, by omega⟩
  obtain ⟨S0_w, hS0_w⟩ := hW0.2
  obtain ⟨Nd0_w, hWT0_w⟩ := (worldTyped_iff_with s0 S0_w).1 hS0_w
  obtain ⟨Sw, Ndw, _, hWT_sw, _, _, hdisj_sw⟩ :=
    hdisj_step S0_w Nd0_w hWT0_w (validBufList_disj validBufList_sysTxBufs hWT0_w)
  have hRK0 : RecordsKept (bufRegions sysTxBufs) sysTxKeep s0 { s with memory := mem' } := by
    intro rec hrec hnz off_r hoff_r hno
    have h1 := hK0s rec hrec hnz off_r hoff_r hno
    have htr_ex : ∃ rsz, (rec.1, rsz) ∈ typedRecords ∧ off_r ∈ rec.2 ∧ off_r + 8 ≤ rsz := by
      simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, hoff_r, ?_⟩; simp at hoff_r; omega
      · refine ⟨80, by decide, hoff_r, ?_⟩; simp at hoff_r; omega
      · cases hoff_r
      · refine ⟨88, by decide, hoff_r, ?_⟩; simp at hoff_r; omega
    obtain ⟨rsz, htr_mem, _, hoff_le⟩ := htr_ex
    have hg_rec : globN s rec.1 = globN s0 rec.1 := by
      simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · exact globN_eq_of_lookup (hG0s (ofString "ws") (by decide))
      · exact globN_eq_of_lookup (hG0s (ofString "bs") (by decide))
      · cases hoff_r
      · exact globN_eq_of_lookup (hG0s (ofString "bo") (by decide))
    have hwo_rec : (globN s rec.1, rsz) ∈ worldOwned s Sw Ndw := by
      have hwti : (globN s rec.1, if globN s rec.1 = 0 then 0 else rsz) ∈ worldTypedIvls s Sw Ndw := by
        unfold worldTypedIvls
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        apply List.mem_append_left; apply List.mem_append_right
        exact List.mem_map.2 ⟨(rec.1, rsz), htr_mem, rfl⟩
      rw [if_neg (by rw [hg_rec]; exact hnz)] at hwti
      exact worldTypedIvls_sub_worldOwned_sysTx s Sw Ndw _ hwti
    have hm_eq : memW { s with memory := mem' } (globN s0 rec.1 + off_r) = memW s (globN s0 rec.1 + off_r) := by
      unfold memW
      dsimp only
      have ha_lt : globN s0 rec.1 + off_r < 2 ^ 64 := by
        rcases InitECandidate.Solver.Wave8Contracts.M08.worldOwned_allocated hWT_sw hwo_rec with h0_r | hal_r
        · dsimp only at h0_r; omega
        · have hb_r := InitECandidate.Solver.Wave8GuestInv.M13.allocated_le_2pow64 hAs.2 hal_r
          dsimp only at hb_r; rw [hg_rec] at hb_r; omega
      by_cases hsz : sz = 0
      · have hlen : (flattenHOL v).length = 0 := by omega
        rw [panMemStoresHOL_frame_sysTx (flattenHOL v) x s.memory mem' hst _
          (by intro k hk; rw [hlen] at hk; omega)]
      rw [hcell_blk]
      intro ⟨hc1, hc2⟩
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt, ← hg_rec] at hc1 hc2
      rcases hdisj_sw (base, sz) (by simp) (globN s rec.1, rsz) hwo_rec with h0_d | h0_d | hd | hd
      all_goals
        dsimp only at *
        omega
    exact hm_eq.trans h1
  have hstep_out : SysTxPrefixStep s0 r { s with memory := mem' } := by
    refine ⟨⟨hAp, hhp0s, hG0s, hRK0, fun S Nd hWT0 hD0 => ?_⟩, hfmp0s, hsp0s, hbn1, hbn2⟩
    obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, hdisj1⟩ := hdisj_step S Nd hWT0 hD0
    have hdisj_t1 : IvlsDisj [(base, sz)] (worldTypedIvls s S1 Nd1) :=
      fun i hi j hj => hdisj1 i hi j (worldTypedIvls_sub_worldOwned_sysTx s S1 Nd1 j hj)
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, _, _⟩ := hW_st S1 Nd1 hWT1 hdisj_t1
    refine ⟨S2, Nd2, fun t ht => hsub12 t (hsub01 t ht), hWT2, ?_, ?_, trivial⟩
    · intro o ho
      rcases hOG12 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o12
      · exact Or.inl rfl
      · rcases hOG01 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j01
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          exact Prod.ext (by omega) (by omega)
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hin_j01.1 hin_oj.1, le_trans hin_oj.2 hin_j01.2⟩)
      · exact Or.inr (Or.inr ⟨le_trans hhp0s hin_o12.1, hin_o12.2⟩)
    · intro a ha hhf
      have hm1 : mem' a = s.memory a := by
        apply hcell_blk
        intro ⟨hc1, hc2⟩
        apply hhf
        unfold heapFree
        dsimp only [Inside] at hin_fresh ⊢
        exact ⟨by omega, by omega⟩
      exact hm1.trans (hFO01 a ha hhf)
  exact ⟨hstep_out, worldOK_of_sysTxStep hW0 hstep_out.1⟩

theorem adjoin_local_table_sysTx {F : Type} {post : PanSemStateFiniteExact 64 F}
    {U Nd' : List Nat} {t klen : Nat}
    (hWU : WorldTypedWith post U Nd')
    (hwf_t : HtabWF post t)
    (hfp_t : ∀ i ∈ htabFootprint post t, Allocated post i ∧ ∀ o ∈ worldOwned post U Nd', Disj i o)
    (hklen : hdr post t 0 = klen) :
    t ∉ U ∧ t ≠ 0 ∧
    (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t) ∧
    WorldTypedWith post (U ++ [t]) Nd' := by
  have ht_nz : t ≠ 0 := by
    have hlo := (hwf_t.1 (t, 88) (by simp [htabFootprint])).1.1
    have hsb0 : 0 < sourceBase := by decide
    dsimp at hlo; omega
  have ht_not_U : t ∉ U := by
    intro htU
    have hmem_ow : (t, 88) ∈ worldOwned post U Nd' := by
      unfold worldOwned
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t, htU, by simp [htabFootprint]⟩))))
    rcases (hfp_t (t, 88) (by simp [htabFootprint])).2 (t, 88) hmem_ow with hd | hd | hd | hd <;> dsimp at hd <;> omega
  obtain ⟨hTU, hJU, hFU, hTrU⟩ := hWU
  have ht_unass : ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t := by
    intro a ha heq
    have haU := (hTU.2.2.2.2.2.2.2.2.2.2.2.1 a ha).1
    rw [heq] at haU; exact ht_not_U haU
  have hsub_Ut : ∀ u ∈ U, u ∈ U ++ [t] := fun u hu => List.mem_append.2 (Or.inl hu)
  have hroot_Ut : ∀ {v}, RootIn U v → RootIn (U ++ [t]) v := by
    rintro v (rfl | hv); exact Or.inl rfl; exact Or.inr (hsub_Ut v hv)
  have hval_Ut : ∀ {u}, HtabValuesIn post u U → HtabValuesIn post u (U ++ [t]) :=
    fun hv i hi => hsub_Ut _ (hv i hi)
  obtain ⟨hndU, hTtU, hTpU, hwsU, hbsU, htsU, hgU, hbsNU, htsNU, hbalU, hboU, hrolesU⟩ := hTU
  have hTU' : TablesTyped post (U ++ [t]) := by
    refine ⟨List.nodup_append.2 ⟨hndU, List.nodup_singleton t, fun x hx y hy heq => by
        have := List.mem_singleton.1 hy; subst this; subst heq; exact ht_not_U hx⟩,
      ?_, ?_,
      fun k hk hnz => hroot_Ut (hwsU k hk hnz),
      fun k hk hnz => hroot_Ut (hbsU k hk hnz),
      fun k hk hnz => hroot_Ut (htsU k hk hnz),
      fun g hg => hroot_Ut (hgU g hg),
      ?_, ?_,
      fun ad had => ⟨hsub_Ut _ (hbalU ad had).1, hsub_Ut _ (hbalU ad had).2.1, (hbalU ad had).2.2⟩,
      hboU,
      ⟨fun a ha => ⟨hsub_Ut _ (hrolesU.1 a ha).1, (hrolesU.1 a ha).2⟩, hrolesU.2⟩⟩
    · intro u hu
      rcases List.mem_append.1 hu with huU | hut
      · exact hTtU u huU
      · simp only [List.mem_singleton] at hut; subst hut
        refine ⟨hwf_t, fun i hi => ⟨(hfp_t i hi).1, fun j hj => ?_⟩⟩
        apply (hfp_t i hi).2 j
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
    · intro u hu v hv hne i hi j hj
      rcases List.mem_append.1 hu with huU | hut <;> rcases List.mem_append.1 hv with hvU | hvt
      · exact hTpU u huU v hvU hne i hi j hj
      · simp only [List.mem_singleton] at hvt; subst hvt
        apply Disj.flip; apply (hfp_t j hj).2 i
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, huU, hi⟩))))
      · simp only [List.mem_singleton] at hut; subst hut
        apply (hfp_t i hi).2 j
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨v, hvU, hj⟩))))
      · simp only [List.mem_singleton] at hut hvt; subst hut; exact absurd hvt.symm hne
    · intro hnz hm
      rcases List.mem_append.1 hm with hmU | hmt
      · exact hval_Ut (hbsNU hnz hmU)
      · simp only [List.mem_singleton] at hmt
        rcases hbsU 32 (by simp [bsTableSlots]) hnz with h0 | hmU
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmU) ht_not_U
    · intro hnz hm
      rcases List.mem_append.1 hm with hmU | hmt
      · exact hval_Ut (htsNU hnz hmU)
      · simp only [List.mem_singleton] at hmt
        rcases htsU 32 (by simp [tsTableSlots]) hnz with h0 | hmU
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmU) ht_not_U
  have hJU' : JournalTyped post (U ++ [t]) :=
    ⟨hJU.1, hJU.2.1, hJU.2.2.1, fun i hi => hsub_Ut _ (hJU.2.2.2 i hi)⟩
  have hTrU' : TriesTypedWith post (U ++ [t]) Nd' := by
    refine ⟨hTrU.1, fun o ho => ⟨fun u hu i hi => ?_, (hTrU.2.1 o ho).2⟩, ?_⟩
    · rcases List.mem_append.1 hu with huU | hut
      · exact (hTrU.2.1 o ho).1 u huU i hi
      · simp only [List.mem_singleton] at hut; subst hut
        apply Disj.flip; apply (hfp_t i hi).2 o
        unfold worldOwned; exact List.mem_append.2 (Or.inr ho)
    · intro hnz
      refine ⟨(hTrU.2.2 hnz).1, fun hm => ?_⟩
      rcases List.mem_append.1 hm with hmU | hmt
      · exact (hTrU.2.2 hnz).2 hmU
      · simp only [List.mem_singleton] at hmt
        rcases hwsU 32 (by simp [wsTableSlots]) hnz with h0 | hmU
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmU) ht_not_U
  have _ := hklen
  exact ⟨ht_not_U, ht_nz, ht_unass, hTU', hJU', hFU, hTrU'⟩

theorem sameTypedCells_of_heap_sp0_sysTx {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hWT : WorldTypedWith s S Nd)
    (hout_dom : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a)
    (hfr : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    M13.SameTypedCells s post S Nd := by
  have hk0 : ∀ j ∈ ([(globN s "scratch_ptr", 0)] : List Ivl), ∃ sp, j = (sp, 0) ∧ sp % 8 = 0 := by
    intro j hj
    simp only [List.mem_singleton] at hj
    exact ⟨globN s "scratch_ptr", hj, hAs.2.2.2.2.2.2.2.2.1⟩
  have hno_sp0 : ∀ a : BitVec 64, a.toNat % 8 = 0 →
      ∀ j ∈ ([(globN s "scratch_ptr", 0)] : List Ivl), ¬ CellHits a.toNat j := by
    intro a ha8 j hj ⟨hc1, hc2⟩
    simp only [List.mem_singleton] at hj
    subst hj
    have hsp8 := hAs.2.2.2.2.2.2.2.2.1
    dsimp only at hc1 hc2
    omega
  refine ⟨hbe, hAp.1.memaddrs.trans hAs.1.memaddrs.symm, hAs.1.memaddrs, hout_dom, ?_, ?_⟩
  · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
    rcases M13.worldTypedIvls_allocated hWT hi with hi0 | hal_i
    · omega
    · have ha_mod : (BitVec.ofNat 64 a).toNat = a := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
      apply hfr (BitVec.ofNat 64 a) (hno_sp0 (BitVec.ofNat 64 a) (by rw [ha_mod]; exact ha8))
      intro ⟨hc1, hc2⟩
      dsimp only at hc1 hc2
      rw [ha_mod] at hc1 hc2
      rcases hal_i with ⟨_, hi_hp⟩ | ⟨hi_sc, _⟩
      · have : i.1 + i.2 ≤ globN s "heap_ptr" := hi_hp
        omega
      · have hlim_s := hAs.2.2.1
        have hlim := hAp.2.2.1
        have hsc0 := hAs.2.2.2.1
        have hgap := hAs.2.2.2.2.1
        rw [M13.heapLimit_val] at hlim_s hlim
        rw [M13.scratchStart_val] at hsc0
        have : globN s "scratch_ptr" ≤ i.1 := hi_sc
        omega
  · intro b _ ⟨i, hi, hb1, hb2⟩
    rcases M13.worldTypedIvls_allocated hWT hi with hi0 | hal_i
    · omega
    · exact WkBal.memB_eq_of_allocated_heap_sp0 hAs.2 hAp.2 hbe hal_i hk0 hfr ⟨hb1, hb2⟩

theorem worldTypedWith_htab_new_sysTx {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t klen : Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsp : globN post "scratch_ptr" = globN s "scratch_ptr")
    (hwf_t : HtabWF post t)
    (hklen : hdr post t 0 = klen)
    (hfp_t : ∀ i ∈ htabFootprint post t,
      Allocated post i ∧ Inside i (globN s "heap_ptr") (globN post "heap_ptr"))
    (hout_dom : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a)
    (hfr : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hgl : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k)
    (hWT : WorldTypedWith s S Nd) :
    t ∉ S ∧ t ≠ 0 ∧
    (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t) ∧
    WorldTypedWith post (S ++ [t]) Nd ∧
    OwnedGrows s post (worldOwned s S Nd) (worldOwned post (S ++ [t]) Nd) ∧
    worldRoleSlots post = worldRoleSlots s ∧
    journalRoleSlots post = journalRoleSlots s ∧
    fixedObjects post = fixedObjects s ∧
    nodeExtents post Nd = nodeExtents s Nd ∧
    (∀ u ∈ S, hdr post u 0 = hdr s u 0) ∧
    (∀ u ∈ S, htabFootprint post u = htabFootprint s u) := by
  have hcell : M13.SameTypedCells s post S Nd :=
    sameTypedCells_of_heap_sp0_sysTx hAs hAp hbe hWT hout_dom hfr
  have hg_core : ∀ g ∈ M13.coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" := by revert g hg; decide
    exact (M13.globN_eq_of_lookup_eq (hgl (ofString g) hne)).symm
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [M13.blockOutObjects_eq hAs.2 hWT.2.2.1 hcell (hg_core "bo" (by decide)),
        M13.balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell (hg_core "bal_accounts" (by decide)),
        hg_core "journal" (by decide),
        hg_core "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    rw [(M13.globN_eq_of_lookup_eq (hgl (ofString gn.1) hne)).symm]
  have hsc_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := le_of_eq hsp
  have hFT_post : FixedTyped post := M13.fixedTyped_of_eq hAp hWT.2.2.1 hhp hsc_le hfeq
  obtain ⟨hWT_S, hOG_S⟩ := M13.worldTypedWith_congr_w1 hAs hAp hhp hsc_le hg_core hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hne_eq : nodeExtents post Nd = nodeExtents s Nd := M13.nodeExtents_eq hWT.2.2.2.1 hcell
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s :=
    M13.worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hg_core
  have hjrs_eq : journalRoleSlots post = journalRoleSlots s :=
    M13.journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hg_core
  have hhdr_eq : ∀ u ∈ S, hdr post u 0 = hdr s u 0 := by
    intro u hu
    have htb := ((hWT.1.2.1 u hu).1.1 (u, 88) (by simp [htabFootprint])).1
    exact M13.htab_hdr_eq hcell hu htb 0 (by omega)
  have hfp_S_eq : ∀ u ∈ S, htabFootprint post u = htabFootprint s u :=
    fun u hu => M13.htabFootprint_eq hcell hu (hWT.1.2.1 u hu).1
  have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    have hfl : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) :=
      List.flatMap_congr hfp_S_eq
    rw [hfl, hfeq, hne_eq]
  have hdisj_fresh : ∀ o ∈ worldOwned s S Nd, ∀ i : Ivl,
      Inside i (globN s "heap_ptr") (globN post "heap_ptr") → Disj i o := by
    intro o ho i hin
    have ho_wti : o ∈ worldTypedIvls s S Nd ∨ o ∈ fixedObjects s := by
      unfold worldOwned at ho
      rcases List.mem_append.1 ho with h1 | hnd
      · rcases List.mem_append.1 h1 with htab | hfix
        · exact Or.inl (by
            unfold worldTypedIvls
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ (List.mem_append_left _ htab)))))
        · exact Or.inr hfix
      · exact Or.inl (M13.mem_worldTypedIvls_nodeExtents hnd)
    have ho_al : o.2 = 0 ∨ Allocated s o := by
      rcases ho_wti with hwti | hfix
      · exact M13.worldTypedIvls_allocated hWT hwti
      · rcases hWT.2.2.1.1 o hfix with h0 | ⟨hal, _⟩
        · exact Or.inl h0
        · exact Or.inr hal
    rcases ho_al with h0 | hal
    · exact Or.inr (Or.inl h0)
    · rcases hal with ⟨_, ho_hp⟩ | ⟨ho_sc, _⟩
      · exact Or.inr (Or.inr (Or.inr (le_trans ho_hp hin.1)))
      · have hlim := hAp.2.2.1
        have hsc0 := hAs.2.2.2.1
        have hgap := hAs.2.2.2.2.1
        rw [M13.heapLimit_val] at hlim
        rw [M13.scratchStart_val] at hsc0
        have hin2 : i.1 + i.2 ≤ globN post "heap_ptr" := hin.2
        have ho1 : globN s "scratch_ptr" ≤ o.1 := ho_sc
        exact Or.inr (Or.inr (Or.inl (by omega)))
  have hfp_disj : ∀ i ∈ htabFootprint post t,
      Allocated post i ∧ ∀ o ∈ worldOwned post S Nd, Disj i o := by
    intro i hi
    refine ⟨(hfp_t i hi).1, fun o ho => ?_⟩
    rw [hwo_eq] at ho
    exact hdisj_fresh o ho i (hfp_t i hi).2
  obtain ⟨ht_not_S, ht_nz, hslot_ne, hWT_ext⟩ :=
    adjoin_local_table_sysTx hWT_S hwf_t hfp_disj hklen
  have hOG_ext : OwnedGrows s post (worldOwned s S Nd) (worldOwned post (S ++ [t]) Nd) := by
    intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htab_S | htab_t
        · exact hOG_S o (List.mem_append_left _ (List.mem_append_left _ htab_S))
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htab_t
          exact Or.inr (Or.inr (hfp_t o htab_t).2)
      · exact hOG_S o (List.mem_append_left _ (List.mem_append_right _ hfix))
    · exact hOG_S o (List.mem_append_right _ hnd)
  exact ⟨ht_not_S, ht_nz, hslot_ne, hWT_ext, hOG_ext,
    hwrs_eq, hjrs_eq, hfeq, hne_eq, hhdr_eq, hfp_S_eq⟩

theorem sysTxPrefixStep_of_htab_new {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {t klen : Nat}
    (hW : WorldOK s)
    (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsp : globN post "scratch_ptr" = globN s "scratch_ptr")
    (hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr")
    (hwf_t : HtabWF post t)
    (hklen : hdr post t 0 = klen)
    (hfp_t : ∀ i ∈ htabFootprint post t,
      Allocated post i ∧ Inside i (globN s "heap_ptr") (globN post "heap_ptr"))
    (hfr : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hgl : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k)
    (hout_dom : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a) :
    SysTxPrefixStep s r post := by
  have hfr_hf : ∀ a : BitVec 64, ¬ CellHits a.toNat (heapFree s) → post.memory a = s.memory a := by
    intro a hnhf
    by_cases hdom : ordinaryDomain a
    · have ha8 : a.toNat % 8 = 0 := (M13.ordinaryDomain_iff a).1 hdom |>.2.2
      have hsp8 := hW.1.2.2.2.2.2.2.2.2.1
      apply hfr a
      · intro j hj ⟨hc1, hc2⟩
        simp only [List.mem_singleton] at hj; subst hj
        dsimp only at hc1 hc2; omega
      · intro ⟨hc1, hc2⟩
        apply hnhf
        unfold heapFree
        have hp_lim := hAp.2.2.1
        dsimp only at hc1 hc2 ⊢
        exact ⟨hc1, by omega⟩
    · exact hout_dom a hdom
  have hG : GlobalsKept sysTxGlobals s post := by
    intro k hk
    apply hgl k
    intro heq
    subst heq
    exact hk (by simp [sysTxGlobals])
  have hRK_std : RecordsKept (fun _ => []) stdKeep s post :=
    InitECandidate.Solver.Wave8Contracts.M08.recordsKept_of_free_writes
      (R := fun {F} (_ : PanSemStateFiniteExact 64 F) => []) hW
      (fun a _ hnhf => hfr_hf a hnhf)
  have hRK_bufs : RecordsKept (bufRegions sysTxBufs) stdKeep s post := by
    intro rec hrec hnz k hk _
    exact hRK_std rec hrec hnz k hk (fun _ hi => by cases hi)
  have hRK : RecordsKept (bufRegions sysTxBufs) sysTxKeep s post :=
    recordsKept_mono_keep keepSub_sysTxKeep_stdKeep hRK_bufs
  have hbn1 : globN post "bn_expw" = globN s "bn_expw" :=
    globN_eq_of_lookup (hgl (ofString "bn_expw") (by decide))
  have hbn2 : globN post "bn_gamma" = globN s "bn_gamma" :=
    globN_eq_of_lookup (hgl (ofString "bn_gamma") (by decide))
  refine ⟨⟨hAp, hhp, hG, hRK, fun S Nd hWT _ => ?_⟩,
    le_of_eq hfmp.symm, le_of_eq hsp, hbn1, hbn2⟩
  obtain ⟨_, _, _, hWT_ext, hOG_ext, _, _, _, _, _, _⟩ :=
    worldTypedWith_htab_new_sysTx hW.1 hAp hbe hhp hsp hwf_t hklen hfp_t hout_dom hfr hgl hWT
  refine ⟨S ++ [t], Nd, fun u hu => List.mem_append_left _ hu, hWT_ext, hOG_ext,
    fun a _ hnhf => hfr_hf a hnhf, trivial⟩

theorem decCall_htab_new_sysTxStep {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (kw capw : BitVec 64) (cont : ProgHOL 64)
    (hW : WorldOK s)
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN mid "heap_ptr" ∧
      WorldOK mid ∧
      mid.code = s.code ∧
      mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      HtabWF mid tw.toNat ∧
      hdr mid tw.toNat 3 = 0 ∧
      hdr mid tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint mid tw.toNat,
        Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      (∀ a : BitVec 64, ¬ ordinaryDomain a → mid.memory a = s.memory a) ∧
      SysTxPrefixStep s none mid ∧
      mid.locals.lookup x = some (.val (.word tw)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      FlowingOrResumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  have hAR : ArenaReady s := hW.1
  have hdc_nt := hnt
  have hdc_fr := hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const kw, .const capw] = some [.val (.word kw), .val (.word capw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "htab_new")
    (ofString "key_len") (ofString "cap") (sourceFnBody Guest.Software.guestFn_htab_new) kw capw
    (by decide) (by rw [hAR.1.code]; exact R10Shards.SoloHtabNew.lookup_htab_new)
  rw [hargs] at hnt hfr; dsimp only at hnt hfr
  rw [hlk] at hnt hfr; dsimp only at hnt hfr
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt hfr
    let cmap := (HolFiniteMapExact.empty.update (ofString "key_len", ValueHOL.val (.word kw))).update
      (ofString "cap", ValueHOL.val (.word capw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAR
    have hent_k : ent.locals.lookup (ofString "key_len") = some (.val (.word kw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "cap" ≠ ofString "key_len" by decide]
    have hent_c : ent.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hout_ent : ∀ a : BitVec 64, ¬ ordinaryDomain a →
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_new)).2.memory a =
          s.memory a := by
      intro a hna
      have hma : ¬ ent.memaddrs a := by
        change ¬ s.memaddrs a
        rw [hAR.1.memaddrs]
        exact hna
      exact evaluateHOLFiniteState_mem_out_dom ent (sourceFnBody Guest.Software.guestFn_htab_new) hma
    have hmeta_ent := (PanRunBounded.evaluateHOLFiniteState_metadata ent
      (sourceFnBody Guest.Software.guestFn_htab_new)).1
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_new) with ⟨rb, sb⟩
    have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_htab_new) = (rb, sb) := hrun
    rw [hrun'] at hnt hfr
    cases rb with
    | none => exact absurd hfr not_flowingOrResumes_error
    | some rb' =>
      cases rb' with
      | timeOut => exact absurd rfl hnt
      | «break» | «continue» | error => exact absurd hfr not_flowingOrResumes_error
      | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
      | exception e ev =>
        dsimp only at hfr
        exfalso
        rcases hfr with h | h | h | hr <;> try simp at h
        rcases hr with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
        · simp at h
        · injection h with h'; injection h' with he1 he2; subst he1 he2
          exact WkBal.htab_new_no_catchable_exn ent hAR.1.code e ev hne (congrArg Prod.fst hrun)
      | returned vb =>
        have hprops := WkBal.htab_new_heap_props ent kw capw hent_AR hkl hcl hent_k hent_c vb
          (congrArg Prod.fst hrun)
        have hrun_snd : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_new)).2 = sb :=
          congrArg Prod.snd hrun
        dsimp only at hprops
        rw [hrun_snd] at hprops hout_ent hmeta_ent
        obtain ⟨tw, rfl, htw_lo, htw_hi, hAsb, hbe_sb, hsp_sb, hfmp_sb,
          hwf_sb, hcnt0, hhdr0, hfp_sb, hfr_sb, hgl_sb⟩ := hprops
        dsimp only at hnt hfr
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at hnt hfr
        let mid := setVarHOLFinite x (.val (.word tw)) { sb with locals := s.locals }
        have hmid_AR : ArenaReady mid := (arenaReady_with_locals sb _ sb.clock).2 hAsb
        have hmid_wf : HtabWF mid tw.toNat := (htabWF_with_locals sb _ sb.clock tw.toNat).2 hwf_sb
        have hmid_fp : ∀ i ∈ htabFootprint mid tw.toNat,
            Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr") := by
          intro i hi
          exact hfp_sb i hi
        have hhp_le : globN s "heap_ptr" ≤ globN mid "heap_ptr" := by
          change globN ent "heap_ptr" ≤ globN sb "heap_ptr"
          omega
        have hstep_mid : SysTxPrefixStep s none mid :=
          sysTxPrefixStep_of_htab_new hW hmid_AR hbe_sb hhp_le hsp_sb hfmp_sb
            hmid_wf hhdr0 hmid_fp hfr_sb hgl_sb hout_ent
        have hW_mid : WorldOK mid := worldOK_of_sysTxStep hW hstep_mid.1
        have heval_eq : evaluateHOLFiniteState s
            (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont) =
            ((evaluateHOLFiniteState mid cont).1,
              { (evaluateHOLFiniteState mid cont).2 with
                locals := HolFiniteMapExact.resVarEq
                  (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
          dsimp only; rw [hlk]; dsimp only
          rw [if_neg hcz, hrun']; dsimp only
          rw [if_pos hsh]
        exact ⟨tw, mid, htw_lo, htw_hi, hW_mid, hmeta_ent, hbe_sb, hsp_sb, hfmp_sb,
          hmid_wf, hcnt0, hhdr0, hmid_fp, hfr_sb, hout_ent, hstep_mid,
          by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
          fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
          fun k hk1 => hgl_sb k hk1,
          hnt, hfr, by rw [heval_eq], by rw [heval_eq]⟩

theorem progPrefixStep_decCall_htab_new
    {x : MlS} {kw capw : BitVec 64} {cont : ProgHOL 64}
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hcont : ProgPrefixStep cont) :
    ProgPrefixStep (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont) := by
  intro F s hc hW hnt hfr
  obtain ⟨_, mid, _, _, hW_mid, hcode_mid, _, _, _, _, _, _, _, _, _, hstep_mid, _, _, _,
    hnt_c, hfr_c, hr_eq, hs_eq⟩ := decCall_htab_new_sysTxStep s x kw capw cont hW hkl hcl hnt hfr
  have hstep2 := hcont mid (hcode_mid.trans hc) hW_mid hnt_c hfr_c
  have hstep2' := sysTxPrefixStep_with_locals_clock (r' := (evaluateHOLFiniteState mid cont).1)
    hstep2
    (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x))
    (evaluateHOLFiniteState mid cont).2.clock
  rw [hr_eq, hs_eq]
  exact sysTxPrefixStep_trans hW.1 hstep_mid hstep2'

theorem progSysTxStep_decCall_htab_new
    {x : MlS} {kw capw : BitVec 64} {cont : ProgHOL 64}
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hcont : ProgSysTxStep cont) :
    ProgSysTxStep (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont) := by
  intro F s hc hW hnt hfr
  obtain ⟨_, mid, _, _, hW_mid, hcode_mid, _, _, _, _, _, _, _, _, _, hstep_mid, _, _, _,
    hnt_c, hfr_c, hr_eq, hs_eq⟩ := decCall_htab_new_sysTxStep s x kw capw cont hW hkl hcl hnt hfr
  have hstep2 := hcont mid (hcode_mid.trans hc) hW_mid hnt_c hfr_c
  have hstep2' := worldStep_with_locals_clock (r' := (evaluateHOLFiniteState mid cont).1)
    hstep2
    (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x))
    (evaluateHOLFiniteState mid cont).2.clock
  rw [hr_eq, hs_eq]
  exact worldStep_sysTx_trans_prefix hW.1 hstep_mid hstep2'

theorem rolesOK_sysTx_msgReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hT : TablesTyped s S) {aa ak : Nat}
    (haa : aa ∈ S) (hak : ak ∈ S) (hne : aa ≠ ak)
    (hka : hdr s aa 0 = 20) (hkk : hdr s ak 0 = 52)
    (hla : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa)
    (hlk : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) :
    RolesOK s S (worldRoleSlots s ++ [(aa, "frame.addr"), (ak, "frame.key")])
      (journalRoleSlots s) := by
  obtain ⟨hr1, hr2, hr3⟩ := hT.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [List.append_assoc] at ha
    rcases List.mem_append.1 ha with hw | ht
    · exact hr1 a (List.mem_append_left _ hw)
    · rcases List.mem_append.1 ht with hf | hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl
        · exact ⟨haa, hka⟩
        · exact ⟨hak, hkk⟩
      · exact hr1 a (List.mem_append_right _ hj)
  · rw [List.pairwise_append]
    refine ⟨hr2, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_singleton _ _⟩
      intro b hb heq
      simp only [List.mem_singleton] at hb
      subst b
      exact (hne heq).elim
    · intro a ha b hb heq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (hla a (List.mem_append_left _ ha) heq).elim
      · exact (hlk a (List.mem_append_left _ ha) heq).elim
  · intro a ha b hb heq
    rw [List.append_assoc] at hb
    rcases List.mem_append.1 hb with hw | ht
    · exact hr3 a ha b (List.mem_append_left _ hw) heq
    · rcases List.mem_append.1 ht with hf | hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl
        · exact (hla a (List.mem_append_right _ ha) heq).elim
        · exact (hlk a (List.mem_append_right _ ha) heq).elim
      · exact hr3 a ha b (List.mem_append_right _ hj) heq

theorem msgReady_of_sysTx_owned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hA : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (hin : Inside (locN s "msg", 176) sourceBase (globN s "heap_ptr"))
    (hwords : WordsOK s (locN s "msg", 176))
    (hdisj : ∀ o ∈ worldOwned s S Nd, Disj (locN s "msg", 176) o)
    (haa : memW s (locN s "msg" + 152) ∈ S)
    (hak : memW s (locN s "msg" + 160) ∈ S)
    (hgas : memW s (locN s "msg" + 40) < 2 ^ 63)
    (hroles : RolesOK s S (worldRoleSlots s ++
      [(memW s (locN s "msg" + 152), "frame.addr"),
       (memW s (locN s "msg" + 160), "frame.key")]) (journalRoleSlots s)) :
    MsgReady s := by
  refine ⟨hA, S, ⟨hW.1, hW.2.1, hW.2.2.1, Nd, hW.2.2.2⟩,
    haa, hak, hin, hwords, ?_, ?_, ?_, hgas, hroles⟩
  · intro t ht i hi
    apply hdisj i
    unfold worldOwned
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.2 ⟨t, ht, hi⟩))
  · intro j hj
    apply hdisj j
    unfold worldOwned
    exact List.mem_append_left _ (List.mem_append_right _ hj)
  · refine ⟨Nd, hW.2.2.2, ?_⟩
    intro o ho j hj
    simp only [List.mem_singleton] at ho
    subst o
    apply hdisj j
    unfold worldOwned
    exact List.mem_append_right _ hj

theorem msgReady_of_sysTx_parts {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hA : ArenaReady s) (hW : WorldTypedWith s S Nd)
    {m aa ak : Nat} (hm : locN s "msg" = m)
    (hm152 : memW s (m + 152) = aa) (hm160 : memW s (m + 160) = ak)
    (haa : aa ∈ S) (hak : ak ∈ S)
    (hka : hdr s aa 0 = 20) (hkk : hdr s ak 0 = 52)
    (hla : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa)
    (hlk : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak)
    (hin : Inside (m, 176) sourceBase (globN s "heap_ptr"))
    (hm8 : m % 8 = 0)
    (hdisj : ∀ o ∈ worldOwned s S Nd, Disj (m, 176) o)
    (hgas : memW s (m + 40) = 30000000) : MsgReady s := by
  have hwords : WordsOK s (m, 176) :=
    R10Shards.P26_P28.wordsOK_of_inside_heap hA.1 hm8 (by decide) hin.1
      (le_trans hin.2 (le_trans hA.2.2.1 (by decide : heapLimit ≤ heapEnd)))
  apply msgReady_of_sysTx_owned hA hW
  · simpa only [hm] using hin
  · simpa only [hm] using hwords
  · simpa only [hm] using hdisj
  · simpa only [hm, hm152] using haa
  · simpa only [hm, hm160] using hak
  · rw [hm, hgas]
    decide
  · have hne : aa ≠ ak := by
      rintro rfl
      omega
    simpa only [hm, hm152, hm160] using
      rolesOK_sysTx_msgReady hW.1 haa hak hne hka hkk hla hlk

def SysTxFreshBlockStep {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (s : PanSemStateFiniteExact 64 F) (w_base : BitVec 64) (sz : Nat) : Prop :=
  SysTxPrefixStep s0 r s ∧
  w_base.toNat % 8 = 0 ∧
  sz % 8 = 0 ∧
  Inside (w_base.toNat, sz) (globN s0 "heap_ptr") (globN s "heap_ptr") ∧
  ∀ S Nd, WorldTypedWith s0 S Nd →
    IvlsDisj (bufRegions sysTxBufs s0) (worldTypedIvls s0 S Nd) →
    ∃ S' Nd',
      (∀ t ∈ S, t ∈ S') ∧
      WorldTypedWith s S' Nd' ∧
      OwnedGrows s0 s (worldOwned s0 S Nd) (worldOwned s S' Nd') ∧
      FrameOutside s0 s (worldOwned s0 S Nd ++ bufRegions sysTxBufs s0 ++ [freeGap s0]) (heapFree s0) ∧
      IvlsDisj [(w_base.toNat, sz)] (worldOwned s S' Nd')

theorem sysTxFreshBlockStep_with_locals_clock {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    {w_base : BitVec 64} {sz : Nat}
    (h : SysTxFreshBlockStep s0 r s w_base sz)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    SysTxFreshBlockStep s0 r' { s with locals := L, clock := k } w_base sz := by
  obtain ⟨h0, hb8, hsz8, hin, hdisj⟩ := h
  refine ⟨sysTxPrefixStep_with_locals_clock h0 L k, hb8, hsz8, hin, fun S Nd hWT hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hdisj'⟩ := hdisj S Nd hWT hD
  obtain ⟨hT', hJ', hF', hNH', hndisj', hws'⟩ := hWT'
  exact ⟨S', Nd', hsub,
    ⟨(tablesTyped_with_locals s L k S').2 hT', hJ', hF', hNH', hndisj', hws'⟩,
    hOG, hFO, hdisj'⟩

theorem sysTxFreshBlockStep_store {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F}
    {w_base : BitVec 64} {sz off : Nat} {x : BitVec 64} {v : ValueHOL 64}
    {mem' : BitVec 64 → HolWordLab 64}
    (hW0 : WorldOK s0) (h0 : SysTxFreshBlockStep s0 none s w_base sz)
    (hoff8 : off % 8 = 0)
    (hx_eq : x = w_base + BitVec.ofNat 64 off)
    (hoff_fit : off + 8 * (flattenHOL v).length ≤ sz)
    (hst : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    SysTxFreshBlockStep s0 none { s with memory := mem' } w_base sz ∧
      WorldOK { s with memory := mem' } ∧
      ({ s with memory := mem' } : PanSemStateFiniteExact 64 F).locals = s.locals ∧
      ({ s with memory := mem' } : PanSemStateFiniteExact 64 F).code = s.code ∧
      (∀ a : BitVec 64, (∀ k, k < (flattenHOL v).length → a ≠ x + BitVec.ofNat 64 (8 * k)) →
        mem' a = s.memory a) := by
  obtain ⟨hp0, hb8, hsz8, hin_fresh, hdisj_step⟩ := h0
  obtain ⟨hp_out, hW_out⟩ :=
    sysTxPrefix_store_fresh_block hW0 hp0 rfl hb8 hsz8 hoff8 hin_fresh hdisj_step hx_eq hoff_fit hst
  have hWs : WorldOK s := worldOK_of_sysTxStep hW0 hp0.1
  have hp0_lo : sourceBase ≤ globN s0 "heap_ptr" := hW0.1.2.1
  have hin_blk : Inside (w_base.toNat, sz) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hp0_lo hin_fresh.1, hin_fresh.2⟩
  have hst_blk : WorldStep (fun _ => [(w_base.toNat, sz)]) [] stdKeep NoExtra
      s none { s with memory := mem' } :=
    worldStep_store_in_block hWs rfl hb8 hsz8 hoff8 hin_blk hx_eq hoff_fit hst
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hp0.1.1.2.2.1
  have hx_nat : x.toNat = w_base.toNat + off := by
    rw [hx_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    have hoff_lt : off < 2 ^ 64 := by unfold Inside at hin_blk; omega
    rw [Nat.mod_eq_of_lt hoff_lt]
    exact Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)
  have hcell_blk : ∀ a : BitVec 64, ¬ CellHits a.toNat (w_base.toNat, sz) → mem' a = s.memory a := by
    intro a hnh
    apply panMemStoresHOL_frame_sysTx (flattenHOL v) x s.memory mem' hst a
    intro k hk h_eq
    apply hnh
    have ha_nat : a.toNat = w_base.toNat + off + 8 * k := by
      rw [h_eq, BitVec.toNat_add, hx_nat, BitVec.toNat_ofNat]
      have hk_lt : 8 * k < 2 ^ 64 := by unfold Inside at hin_blk; omega
      rw [Nat.mod_eq_of_lt hk_lt]
      exact Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)
    unfold CellHits
    rw [ha_nat]
    exact ⟨by omega, by omega⟩
  refine ⟨⟨hp_out, hb8, hsz8, hin_fresh, fun S Nd hWT0 hD0 => ?_⟩,
    hW_out, rfl, rfl,
    fun a hne => panMemStoresHOL_frame_sysTx (flattenHOL v) x s.memory mem' hst a hne⟩
  obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, hdisj1⟩ := hdisj_step S Nd hWT0 hD0
  have hdisj_t1 : IvlsDisj [(w_base.toNat, sz)] (worldTypedIvls s S1 Nd1) :=
    fun i hi j hj => hdisj1 i hi j (worldTypedIvls_sub_worldOwned_sysTx s S1 Nd1 j hj)
  have hcell_s1 : M13.SameTypedCells s { s with memory := mem' } S1 Nd1 := by
    refine ⟨rfl, rfl, hWs.1.1.memaddrs,
      fun a hnd => panMemStoresHOL_out_dom hst (by rw [hWs.1.1.memaddrs]; exact hnd), ?_, ?_⟩
    · intro a ha _ ⟨i, hi, ha1, ha2⟩
      have ha_mod : (BitVec.ofNat 64 a).toNat = a := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
      apply hcell_blk (BitVec.ofNat 64 a)
      intro ⟨hc1, hc2⟩
      rw [ha_mod] at hc1 hc2
      rcases hdisj_t1 (w_base.toNat, sz) (by simp) i hi with h0_d | h0_d | hd | hd <;>
        dsimp only at * <;> omega
    · intro b hb64 ⟨i, hi, hb1, hb2⟩
      unfold memB
      dsimp only
      have hal_eq : mem' (panByteAlignHOL (BitVec.ofNat 64 b)) =
          s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
        apply hcell_blk
        intro ⟨hc1, hc2⟩
        have hal_nat : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
          rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64]
        rw [hal_nat] at hc1 hc2
        rcases hdisj_t1 (w_base.toNat, sz) (by simp) i hi with h0_d | h0_d | hd | hd <;>
          dsimp only at * <;> omega
      rw [hal_eq]
  have hg_core : ∀ g ∈ M13.coreWorldGlobals, globN ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) g = globN s g :=
    fun _ _ => rfl
  have hfeq : fixedObjects ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) = fixedObjects s := by
    unfold fixedObjects
    rw [M13.blockOutObjects_eq hWs.1.2 hWT1.2.2.1 hcell_s1 rfl,
        M13.balObjects_eq hWs.1.2 hWT1.1 hWT1.2.2.1 hcell_s1 rfl]
    rfl
  have hFT_post : FixedTyped ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) :=
    M13.fixedTyped_of_eq hW_out.1 hWT1.2.2.1 le_rfl le_rfl hfeq
  obtain ⟨hWT_post, _⟩ := M13.worldTypedWith_congr_w1 hWs.1 hW_out.1 le_rfl le_rfl hg_core hcell_s1 hWT1
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hne_eq : nodeExtents ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) Nd1 = nodeExtents s Nd1 :=
    M13.nodeExtents_eq hWT1.2.2.2.1 hcell_s1
  have hfp_eq : ∀ u ∈ S1, htabFootprint ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) u = htabFootprint s u :=
    fun u hu => M13.htabFootprint_eq hcell_s1 hu (hWT1.1.2.1 u hu).1
  have hwo_eq : worldOwned ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) S1 Nd1 = worldOwned s S1 Nd1 := by
    unfold worldOwned
    rw [List.flatMap_congr hfp_eq, hfeq, hne_eq]
  refine ⟨S1, Nd1, hsub01, hWT_post,
    by rw [hwo_eq]; exact hOG01,
    fun a ha hhf => (hcell_blk a (fun ⟨hc1, hc2⟩ => hhf (by
      unfold heapFree; dsimp only [Inside] at hin_fresh ⊢; exact ⟨by omega, by omega⟩))).trans (hFO01 a ha hhf),
    by rw [hwo_eq]; exact hdisj1⟩

theorem sysTxFreshBlockStep_of_ctor {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {w_base : BitVec 64} {sz : Nat}
    (_hW : WorldOK s)
    (hstep : WorldStep (bufRegions []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ p => [(p, sz)]))
      s (some (.returned (.val (.word w_base)))) post)
    (hb8 : w_base.toNat % 8 = 0)
    (hsz8 : sz % 8 = 0)
    (hin : Inside (w_base.toNat, sz) (globN s "heap_ptr") (globN post "heap_ptr")) :
    SysTxFreshBlockStep s (some (.returned (.val (.word w_base)))) post w_base sz := by
  have hG := hstep.2.2.1
  have hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    globN_eq_of_lookup (hG (ofString "frame_mem_ptr") (by decide))
  have hsp : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hG (ofString "scratch_ptr") (by decide))
  have hbn1 : globN post "bn_expw" = globN s "bn_expw" :=
    globN_eq_of_lookup (hG (ofString "bn_expw") (by decide))
  have hbn2 : globN post "bn_gamma" = globN s "bn_gamma" :=
    globN_eq_of_lookup (hG (ofString "bn_gamma") (by decide))
  have hkeep_sub : KeepSub sysTxKeep
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] := by
    intro p hp
    simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨[0, 8, 16, 24, 32], by simp, fun _ h => h⟩
    · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72], by simp, by
        intro k hk; simp at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp⟩
    · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64], by simp, fun _ h => by cases h⟩
    · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80], by simp, fun _ h => h⟩
  have hws_noextra : WorldStep (bufRegions []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra s (some (.returned (.val (.word w_base)))) post := by
    obtain ⟨hAp, hhp, hGs, hK, hW_fn⟩ := hstep
    refine ⟨hAp, hhp, hGs, hK, fun S Nd hWT hD => ?_⟩
    obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hW_fn S Nd hWT hD
    exact ⟨S', Nd', hsub, hWT', hOG, hFO, trivial⟩
  have hprefix : SysTxPrefixStep s (some (.returned (.val (.word w_base)))) post :=
    ⟨worldStep_mono_bufs_keep (fun _ h => by cases h)
       (by intro g hg; simp at hg; subst hg; simp [sysTxGlobals])
       hkeep_sub hws_noextra,
     by rw [hfmp], by rw [hsp], hbn1, hbn2⟩
  refine ⟨hprefix, hb8, hsz8, hin, fun S Nd hWT _ => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hav⟩ :=
    hstep.2.2.2.2 S Nd hWT (fun _ h => by cases h)
  obtain ⟨w', hw_eq, hdisj⟩ := hav (.val (.word w_base)) rfl
  have hw' : w_base = w' := by injection hw_eq with h1; injection h1
  subst hw'
  refine ⟨S', Nd', hsub, hWT', hOG,
    fun a ha hhf => hFO a (fun i hi hch => by
      rcases List.mem_append.1 hi with hi1 | hfg
      · rcases List.mem_append.1 hi1 with hwo | hbuf
        · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo)) hch
        · cases hbuf
      · exact ha i (List.mem_append_right _ hfg) hch) hhf,
    hdisj⟩

theorem sysTxFreshBlockStep_of_pre_locals_clock {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    {w_base : BitVec 64} {sz : Nat}
    (h : SysTxFreshBlockStep { s with locals := L, clock := k } r post w_base sz) :
    SysTxFreshBlockStep s r post w_base sz := by
  obtain ⟨h0, hb8, hsz8, hin, hdisj⟩ := h
  refine ⟨sysTxPrefixStep_of_pre_locals_clock h0, hb8, hsz8, hin, fun S Nd hWT hD => ?_⟩
  obtain ⟨hT, hJ, hF, hNH, hndisj, hws⟩ := hWT
  exact hdisj S Nd ⟨(tablesTyped_with_locals s L k S).2 hT, hJ, hF, hNH, hndisj, hws⟩ hD

theorem sysTxFreshBlockStep_from_entry {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    {callee L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    {w_base : BitVec 64} {sz : Nat}
    (h : SysTxFreshBlockStep (callEntryStateHOLFinite s callee) r post w_base sz) :
    SysTxFreshBlockStep s r' { post with locals := L, clock := k } w_base sz :=
  sysTxFreshBlockStep_with_locals_clock (sysTxFreshBlockStep_of_pre_locals_clock h) L k

theorem sysTxFreshBlockStep_prepend {F : Type}
    {s0 s1 s2 : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {w_base : BitVec 64} {sz : Nat}
    (hW0 : WorldOK s0)
    (h01 : SysTxPrefixStep s0 none s1)
    (h12 : SysTxFreshBlockStep s1 r s2 w_base sz) :
    SysTxFreshBlockStep s0 r s2 w_base sz := by
  obtain ⟨hp12, hb8, hsz8, hin12, hdisj12⟩ := h12
  have hA0 : ArenaReady s0 := hW0.1
  have hA1 : ArenaReady s1 := h01.1.1
  have hbuf10 : bufRegions sysTxBufs s1 = bufRegions sysTxBufs s0 := by
    unfold bufRegions sysTxBufs bufferRegion
    simp only [List.map]
    have hg : ∀ g : String, ofString g ∉ (sysTxGlobals.map ofString) →
        globN s1 g = globN s0 g := by
      intro g hng
      exact globN_eq_of_lookup (h01.1.2.2.1 (ofString g) hng)
    rw [hg "b2_v" (by decide), hg "bal_key_buf" (by decide),
        h01.2.2.2.1, h01.2.2.2.2,
        hg "evm_key_buf" (by decide), hg "keccak_pad" (by decide),
        hg "keccak_st" (by decide), hg "mpt_nib_scratch" (by decide),
        hg "pre_hdr_buf" (by decide), hg "rmd_h" (by decide),
        hg "rmd_pad" (by decide), hg "rmd_x" (by decide),
        hg "sha_pad" (by decide), hg "sha_st" (by decide),
        hg "sk_buf" (by decide), hg "u256_ws" (by decide)]
  refine ⟨sysTxPrefixStep_trans hA0 h01 hp12, hb8, hsz8,
    ⟨le_trans h01.1.2.1 hin12.1, hin12.2⟩, fun S Nd hWT0 hD0 => ?_⟩
  obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, _⟩ := h01.1.2.2.2.2 S Nd hWT0 hD0
  have hD1 : IvlsDisj (bufRegions sysTxBufs s1) (worldTypedIvls s1 S1 Nd1) :=
    validBufList_disj validBufList_sysTxBufs hWT1
  obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, hdisj2⟩ := hdisj12 S1 Nd1 hWT1 hD1
  refine ⟨S2, Nd2, fun t ht => hsub12 t (hsub01 t ht), hWT2, ?_, ?_, hdisj2⟩
  · intro o ho
    rcases hOG12 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o12
    · exact Or.inl rfl
    · rcases hOG01 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j01
      · left
        rcases o with ⟨o1, o2⟩
        dsimp only [Inside] at hin_oj
        exact Prod.ext (by omega) (by omega)
      · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
      · exact Or.inr (Or.inr ⟨le_trans hin_j01.1 hin_oj.1,
          le_trans hin_oj.2 (le_trans hin_j01.2 hp12.1.2.1)⟩)
    · exact Or.inr (Or.inr ⟨le_trans h01.1.2.1 hin_o12.1, hin_o12.2⟩)
  · intro a ha hhf
    have hm01 : s1.memory a = s0.memory a := hFO01 a ha hhf
    have hm12 : s2.memory a = s1.memory a := by
      apply hFO12 a
      · intro i hi hch
        obtain ⟨hc1, hc2⟩ := hch
        rcases List.mem_append.1 hi with hi1 | hfg1
        · rcases List.mem_append.1 hi1 with hwo1 | hR1
          · rcases hOG01 i hwo1 with rfl | ⟨k, hk, hin_ik⟩ | hin_i01
            · dsimp only at hc2; omega
            · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                ⟨by dsimp only [Inside] at hin_ik; omega,
                 by dsimp only [Inside] at hin_ik; omega⟩
            · have hp1_lim : globN s1 "heap_ptr" ≤ heapLimit := hA1.2.2.1
              exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i01 ⊢; omega,
                         by unfold heapFree; dsimp only [Inside] at hin_i01 ⊢; omega⟩
          · change i ∈ bufRegions sysTxBufs s1 at hR1
            rw [hbuf10] at hR1
            exact ha i (List.mem_append_left _ (List.mem_append_right _ hR1)) ⟨hc1, hc2⟩
        · simp only [List.mem_singleton] at hfg1
          subst hfg1
          exact ha (freeGap s0) (List.mem_append_right _ (List.mem_singleton.2 rfl))
            ⟨by
              have hc1' : a.toNat + 8 > globN s1 "frame_mem_ptr" := hc1
              have := h01.2.1
              change a.toNat + 8 > globN s0 "frame_mem_ptr"
              omega,
             by
              have hc2' : a.toNat < globN s1 "frame_mem_ptr" + (globN s1 "scratch_ptr" - globN s1 "frame_mem_ptr") := hc2
              have hfmp_sp1 : globN s1 "frame_mem_ptr" ≤ globN s1 "scratch_ptr" := hA1.2.2.2.2.1
              have := h01.2.1; have := h01.2.2.1
              change a.toNat < globN s0 "frame_mem_ptr" + (globN s0 "scratch_ptr" - globN s0 "frame_mem_ptr")
              omega⟩
      · intro ⟨hc1, hc2⟩
        have hp1_lim : globN s1 "heap_ptr" ≤ heapLimit := hA1.2.2.1
        have := h01.1.2.1
        exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                   by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
    exact hm12.trans hm01

theorem decCall_te_new_freshStep {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hnt : (evaluateHOLFiniteState s (.decCall x .one (ofString "te_new") [] cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.decCall x .one (ofString "te_new") [] cont)).1) :
    (SysTxPrefixStep s
      (evaluateHOLFiniteState s (.decCall x .one (ofString "te_new") [] cont)).1
      (evaluateHOLFiniteState s (.decCall x .one (ofString "te_new") [] cont)).2 ∧
     ∃ e ev, (evaluateHOLFiniteState s (.decCall x .one (ofString "te_new") [] cont)).1 =
       some (.exception e ev)) ∨
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      SysTxFreshBlockStep s none mid tw 200 ∧
      WorldOK mid ∧
      mid.code = originalRuntimeCode ∧
      mid.locals.lookup x = some (.val (.word tw)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k, k < 25 → memW mid (tw.toNat + 8 * k) = 0) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      FlowingOrResumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "te_new") [] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "te_new") [] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [] = some [] := rfl
  rw [hargs] at hnt hfr ⊢; dsimp only at hnt hfr ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "te_new") [] with _ | ⟨body', callee, ret'⟩
  · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hl] at hnt hfr ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt hfr ⊢
      let ent := callEntryStateHOLFinite s callee
      have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
      have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
      rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
      simp only [ent] at hrun hmeta
      simp only [hrun] at hmeta hnt hfr ⊢
      have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
        simp only [ent, hrun]; rintro rfl; simp at hnt
      cases res with
      | none => exact absurd hfr not_flowingOrResumes_error
      | some cr =>
        cases cr with
        | timeOut => simp at hnt
        | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
        | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
        | exception eid ev =>
          dsimp only at hfr ⊢
          have hres_ex : Resumes (some (.exception eid ev)) := by
            rcases hfr with h | h | h | hr <;> try simp at h
            exact hr
          have hspec := FunSpec.at_lookup sysTxPrefix_te_new s hc [] body' callee ret' hl hWent hnt_c
          simp only [ent, hrun] at hspec
          exact Or.inl ⟨sysTxPrefixStep_from_entry (hspec hres_ex), eid, ev, rfl⟩
        | returned v =>
          dsimp only at hnt hfr ⊢
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) .one && shapeEqHOL (shapeOfHOLExact v) ret') = true
          · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
            have hrt_spec : Returns ArenaReady
                (fun s post m => FreshBlock s post m 200 ∧
                  ∀ k, k < 25 → memW post (m + 8 * k) = 0)
                (ofString "te_new") := Wave8Contracts.M27.rt_te_new
            have hrt := FunSpec.at_lookup hrt_spec s hc [] body' callee ret' hl hWent.1 hnt_c
              v (by simp [ent, hrun])
            simp only [ent, hrun] at hrt
            obtain ⟨tw, rfl, _, _, ⟨htw8, hin_tw, _⟩, hzero⟩ := hrt
            have hin_tw' : Inside (tw.toNat, 200) (globN ent "heap_ptr") (globN cpost "heap_ptr") :=
              ⟨hin_tw.1, by simpa [show (200 + 7) / 8 * 8 = 200 by decide] using hin_tw.2⟩
            have hres_tw : Resumes ((ent.evaluateHOLFiniteState body').1) :=
              Or.inl ⟨.val (.word tw), by simp [ent, hrun]⟩
            have hwk := FunSpec.at_lookup R13Wk06b.wk_te_new s hc [] body' callee ret' hl hWent hnt_c hres_tw
            simp only [ent, hrun] at hwk
            have hfb_ent : SysTxFreshBlockStep ent (some (.returned (.val (.word tw)))) cpost tw 200 :=
              sysTxFreshBlockStep_of_ctor hWent hwk htw8 (by decide) hin_tw'
            set mid := setVarHOLFinite x (.val (.word tw)) { cpost with locals := s.locals }
            have hfb_mid : SysTxFreshBlockStep s none mid tw 200 :=
              sysTxFreshBlockStep_from_entry (post := cpost) (L := mid.locals) hfb_ent
            have hW_mid : WorldOK mid := worldOK_of_sysTxStep hW hfb_mid.1.1
            refine Or.inr ⟨tw, mid, hfb_mid, hW_mid, hmeta.trans hc,
              by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
              fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hy],
              fun k hk => hzero k hk,
              hnt, hfr, rfl, rfl⟩
          · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem decCall_msg_new_freshStep {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hnt : (evaluateHOLFiniteState s (.decCall x .one (ofString "msg_new") [] cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.decCall x .one (ofString "msg_new") [] cont)).1) :
    (SysTxPrefixStep s
      (evaluateHOLFiniteState s (.decCall x .one (ofString "msg_new") [] cont)).1
      (evaluateHOLFiniteState s (.decCall x .one (ofString "msg_new") [] cont)).2 ∧
     ∃ e ev, (evaluateHOLFiniteState s (.decCall x .one (ofString "msg_new") [] cont)).1 =
       some (.exception e ev)) ∨
    ∃ (mw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      SysTxFreshBlockStep s none mid mw 176 ∧
      WorldOK mid ∧
      mid.code = originalRuntimeCode ∧
      mid.locals.lookup x = some (.val (.word mw)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k, k < 22 → memW mid (mw.toNat + 8 * k) = 0) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      FlowingOrResumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "msg_new") [] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "msg_new") [] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [] = some [] := rfl
  rw [hargs] at hnt hfr ⊢; dsimp only at hnt hfr ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "msg_new") [] with _ | ⟨body', callee, ret'⟩
  · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hl] at hnt hfr ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt hfr ⊢
      let ent := callEntryStateHOLFinite s callee
      have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
      have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
      rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
      simp only [ent] at hrun hmeta
      simp only [hrun] at hmeta hnt hfr ⊢
      have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
        simp only [ent, hrun]; rintro rfl; simp at hnt
      cases res with
      | none => exact absurd hfr not_flowingOrResumes_error
      | some cr =>
        cases cr with
        | timeOut => simp at hnt
        | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
        | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
        | exception eid ev =>
          dsimp only at hfr ⊢
          have hres_ex : Resumes (some (.exception eid ev)) := by
            rcases hfr with h | h | h | hr <;> try simp at h
            exact hr
          have hspec := FunSpec.at_lookup sysTxPrefix_msg_new s hc [] body' callee ret' hl hWent hnt_c
          simp only [ent, hrun] at hspec
          exact Or.inl ⟨sysTxPrefixStep_from_entry (hspec hres_ex), eid, ev, rfl⟩
        | returned v =>
          dsimp only at hnt hfr ⊢
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) .one && shapeEqHOL (shapeOfHOLExact v) ret') = true
          · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
            have hrt_spec : Returns ArenaReady
                (fun s post m => FreshBlock s post m 176 ∧
                  ∀ k, k < 22 → memW post (m + 8 * k) = 0)
                (ofString "msg_new") := Wave8Contracts.M26.rt_msg_new
            have hrt := FunSpec.at_lookup hrt_spec s hc [] body' callee ret' hl hWent.1 hnt_c
              v (by simp [ent, hrun])
            simp only [ent, hrun] at hrt
            obtain ⟨mw, rfl, _, _, ⟨hmw8, hin_mw, _⟩, hzero⟩ := hrt
            have hin_mw' : Inside (mw.toNat, 176) (globN ent "heap_ptr") (globN cpost "heap_ptr") :=
              ⟨hin_mw.1, by simpa [show (176 + 7) / 8 * 8 = 176 by decide] using hin_mw.2⟩
            have hres_mw : Resumes ((ent.evaluateHOLFiniteState body').1) :=
              Or.inl ⟨.val (.word mw), by simp [ent, hrun]⟩
            have hwk := FunSpec.at_lookup R13Wk06b.wk_msg_new s hc [] body' callee ret' hl hWent hnt_c hres_mw
            simp only [ent, hrun] at hwk
            have hfb_ent : SysTxFreshBlockStep ent (some (.returned (.val (.word mw)))) cpost mw 176 :=
              sysTxFreshBlockStep_of_ctor hWent hwk hmw8 (by decide) hin_mw'
            set mid := setVarHOLFinite x (.val (.word mw)) { cpost with locals := s.locals }
            have hfb_mid : SysTxFreshBlockStep s none mid mw 176 :=
              sysTxFreshBlockStep_from_entry (post := cpost) (L := mid.locals) hfb_ent
            have hW_mid : WorldOK mid := worldOK_of_sysTxStep hW hfb_mid.1.1
            refine Or.inr ⟨mw, mid, hfb_mid, hW_mid, hmeta.trans hc,
              by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
              fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hy],
              fun k hk => hzero k hk,
              hnt, hfr, rfl, rfl⟩
          · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem evalAt_add_local_const_sysTx {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name : MlS} {w : BitVec 64} {off : Nat} {x : BitVec 64}
    (hl : s.locals.lookup name = some (.val (.word w)))
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local name, .const (BitVec.ofNat 64 off)]) = some (.val (.word x))) :
    x = w + BitVec.ofNat 64 off := by
  simp only [evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord,
    wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
    Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hev
  rw [← hev]
  simp [BitVec.add_zero]

theorem evalHOLExact_load_comb4_len {F : Type} {s : PanSemStateFiniteExact 64 F}
    {addr : ExpHOL 64} {v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load (.comb [.one, .one, .one, .one]) addr) = some v) :
    (flattenHOL v).length = 4 := by
  simp only [evalHOLExact] at hev
  split_ifs at hev with hwf
  rcases ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addr with _ | va
  · rw [ha] at hev; simp at hev
  · rw [ha] at hev
    cases va with
    | rStruct _ => simp at hev
    | nStruct _ => simp at hev
    | val wl =>
      cases wl with
      | word a =>
        dsimp only at hev
        have hone : ∀ {b : BitVec 64} {v1 : ValueHOL 64},
            @memLoadHOLExact 64 _ .one b s.memaddrs (fun x => Classical.propDecidable (s.memaddrs x))
              s.memory s.structs = some v1 → (flattenHOL v1).length = 1 := by
          intro b v1 h1
          unfold memLoadHOLExact at h1
          split_ifs at h1
          simp only [Option.some.injEq] at h1
          subst h1
          simp [flattenHOL]
        unfold memLoadHOLExact at hev
        rcases hm0 : @memLoadsHOLExact 64 _ [.one, .one, .one, .one] a s.memaddrs
            (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs0
        · rw [hm0] at hev; simp at hev
        · rw [hm0] at hev
          simp only [Option.some.injEq] at hev
          subst hev
          unfold memLoadsHOLExact at hm0
          rcases hl1 : @memLoadHOLExact 64 _ .one a s.memaddrs
              (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v1
          · rw [hl1] at hm0; simp at hm0
          · rw [hl1] at hm0
            rcases hm1 : @memLoadsHOLExact 64 _ [.one, .one, .one] _ s.memaddrs
                (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs1
            · rw [hm1] at hm0; simp at hm0
            · rw [hm1] at hm0
              simp only [Option.some.injEq] at hm0
              subst hm0
              unfold memLoadsHOLExact at hm1
              rcases hl2 : @memLoadHOLExact 64 _ .one _ s.memaddrs
                  (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v2
              · rw [hl2] at hm1; simp at hm1
              · rw [hl2] at hm1
                rcases hm2 : @memLoadsHOLExact 64 _ [.one, .one] _ s.memaddrs
                    (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs2
                · rw [hm2] at hm1; simp at hm1
                · rw [hm2] at hm1
                  simp only [Option.some.injEq] at hm1
                  subst hm1
                  unfold memLoadsHOLExact at hm2
                  rcases hl3 : @memLoadHOLExact 64 _ .one _ s.memaddrs
                      (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v3
                  · rw [hl3] at hm2; simp at hm2
                  · rw [hl3] at hm2
                    rcases hm3 : @memLoadsHOLExact 64 _ [.one] _ s.memaddrs
                        (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs3
                    · rw [hm3] at hm2; simp at hm2
                    · rw [hm3] at hm2
                      simp only [Option.some.injEq] at hm2
                      subst hm2
                      unfold memLoadsHOLExact at hm3
                      rcases hl4 : @memLoadHOLExact 64 _ .one _ s.memaddrs
                          (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v4
                      · rw [hl4] at hm3; simp at hm3
                      · rw [hl4] at hm3
                        rcases hm4 : @memLoadsHOLExact 64 _ [] _ s.memaddrs
                            (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs4
                        · rw [hm4] at hm3; simp at hm3
                        · rw [hm4] at hm3
                          simp only [Option.some.injEq] at hm3
                          subst hm3
                          unfold memLoadsHOLExact at hm4
                          simp only [Option.some.injEq] at hm4
                          subst hm4
                          have c1 := hone hl1
                          have c2 := hone hl2
                          have c3 := hone hl3
                          have c4 := hone hl4
                          conv_lhs => unfold flattenHOL
                          simp [c1, c2, c3, c4]

theorem evalHOLExact_rfield_len_le_one {F : Type} {s : PanSemStateFiniteExact 64 F}
    {idx : Nat} {v : ValueHOL 64}
    (hcode_sh : ∀ vc, s.locals.lookup (ofString "code") = some vc →
      shapeEqHOL (shapeOfHOLExact vc) (.comb [.one, .one]) = true)
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.rfield idx (.var .local (ofString "code"))) = some v) :
    (flattenHOL v).length ≤ 1 := by
  simp only [evalHOLExact] at hev
  rcases hc : s.locals.lookup (ofString "code") with _ | vc
  · rw [hc] at hev; simp at hev
  · rw [hc] at hev
    have hsh := (shapeEqHOL_eq_true _ _).1 (hcode_sh vc hc)
    cases vc with
    | val _ => simp [shapeOfHOLExact] at hsh
    | nStruct _ _ => simp [shapeOfHOLExact] at hsh
    | rStruct vs =>
      simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
      rcases vs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩ <;> simp at hsh
      rcases hsh with ⟨hv0, hv1⟩
      have hone_len : ∀ u : ValueHOL 64, shapeOfHOLExact u = .one → (flattenHOL u).length ≤ 1 := by
        intro u hu
        cases u with
        | val wl => cases wl; simp [flattenHOL]
        | rStruct _ => simp [shapeOfHOLExact] at hu
        | nStruct _ _ => simp [shapeOfHOLExact] at hu
      rcases idx with _ | ⟨_ | _⟩
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hev; subst hev; exact hone_len v0 hv0
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hev
        subst hev; exact hone_len v1 hv1
      · simp at hev

theorem evalHOLExact_var_word_len_le_one {F : Type} {s : PanSemStateFiniteExact 64 F}
    {vk : VarKind} {nm : MlS} {v : ValueHOL 64}
    (hw : ∃ w : BitVec 64, (match vk with | .local => s.locals.lookup nm | .global => s.globals.lookup nm) =
      some (.val (.word w)))
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var vk nm) = some v) :
    (flattenHOL v).length ≤ 1 := by
  obtain ⟨w, hlu⟩ := hw
  cases vk <;> (simp only [evalHOLExact, hlu, Option.some.injEq] at hev; subst hev; simp [flattenHOL])

theorem evalHOLExact_const_len_le_one {F : Type} {s : PanSemStateFiniteExact 64 F}
    {c : BitVec 64} {v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const c) = some v) :
    (flattenHOL v).length ≤ 1 := by
  simp only [evalHOLExact, Option.some.injEq] at hev
  subst hev
  simp [flattenHOL]

theorem evalHOLExact_panop_mul_const_len_le_one {F : Type} {s : PanSemStateFiniteExact 64 F}
    {c1 c2 : BitVec 64} {v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.panop .mul [.const c1, .const c2]) = some v) :
    (flattenHOL v).length ≤ 1 := by
  simp only [evalHOLExact, evalListHOLExact, valueIsWord, valueWord, panOpHOL,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, Option.some.injEq] at hev
  subst hev
  simp [flattenHOL]

theorem seq_store_freshBlock_step {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F}
    {bname : MlS} {w_base : BitVec 64} {sz off : Nat} {src : ExpHOL 64} {cont : ProgHOL 64}
    (hW0 : WorldOK s0)
    (h0 : SysTxFreshBlockStep s0 none s w_base sz)
    (hl : s.locals.lookup bname = some (.val (.word w_base)))
    (hoff8 : off % 8 = 0)
    (hfit : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src = some v →
      off + 8 * (flattenHOL v).length ≤ sz)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) src) cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) src) cont)).1) :
    ∃ (mem' : BitVec 64 → HolWordLab 64) (v : ValueHOL 64),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src = some v ∧
      @panMemStoresHOL 64 _ (w_base + BitVec.ofNat 64 off) (flattenHOL v) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem' ∧
      SysTxFreshBlockStep s0 none { s with memory := mem' } w_base sz ∧
      WorldOK { s with memory := mem' } ∧
      (∀ a : BitVec 64,
        (∀ k, k < (flattenHOL v).length → a ≠ (w_base + BitVec.ofNat 64 off) + BitVec.ofNat 64 (8 * k)) →
        mem' a = s.memory a) ∧
      (evaluateHOLFiniteState { s with memory := mem' } cont).1 ≠ some .timeOut ∧
      FlowingOrResumes (evaluateHOLFiniteState { s with memory := mem' } cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) src) cont) =
        evaluateHOLFiniteState { s with memory := mem' } cont := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hnt hfr ⊢
  rcases hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) with _ | vx
  · simp [hx] at hfr; exact absurd hfr not_flowingOrResumes_error
  · rcases vx with ⟨⟨x⟩⟩ | _ | _
    · rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src with _ | v
      · simp [hx, hv] at hfr; exact absurd hfr not_flowingOrResumes_error
      · rcases hst : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
            (fun a => Classical.propDecidable (s.memaddrs a)) s.memory with _ | mem'
        · simp [hx, hv, hst] at hfr; exact absurd hfr not_flowingOrResumes_error
        · have hv' : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src = some v := hv
          have hst' : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
              (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem' := hst
          simp only [hx, hv, hst] at hnt hfr ⊢
          have hx_eq : x = w_base + BitVec.ofNat 64 off := evalAt_add_local_const_sysTx hl hx
          subst hx_eq
          obtain ⟨hfb', hW', _, _, hframe⟩ :=
            sysTxFreshBlockStep_store hW0 h0 hoff8 rfl (hfit v hv') hst'
          exact ⟨mem', v, rfl, hst', hfb', hW', hframe, hnt, hfr, rfl⟩
    · simp [hx] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp [hx] at hfr; exact absurd hfr not_flowingOrResumes_error

def SysTxMsgTablesStep {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (s : PanSemStateFiniteExact 64 F)
    (w_m : BitVec 64)
    (tabs : List (Nat × Nat)) : Prop :=
  SysTxPrefixStep s0 none s ∧
  w_m.toNat % 8 = 0 ∧
  Inside (w_m.toNat, 176) (globN s0 "heap_ptr") (globN s "heap_ptr") ∧
  ∀ S Nd, WorldTypedWith s0 S Nd →
    IvlsDisj (bufRegions sysTxBufs s0) (worldTypedIvls s0 S Nd) →
    ∃ S' Nd',
      (∀ t ∈ S, t ∈ S') ∧
      WorldTypedWith s S' Nd' ∧
      OwnedGrows s0 s (worldOwned s0 S Nd) (worldOwned s S' Nd') ∧
      FrameOutside s0 s (worldOwned s0 S Nd ++ bufRegions sysTxBufs s0 ++ [freeGap s0]) (heapFree s0) ∧
      IvlsDisj [(w_m.toNat, 176)] (worldOwned s S' Nd') ∧
      ∀ p ∈ tabs, p.1 ∈ S' ∧ hdr s p.1 0 = p.2 ∧
        ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ p.1

theorem sysTxMsgTablesStep_of_freshBlock {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {w_m : BitVec 64}
    (h : SysTxFreshBlockStep s0 none s w_m 176) :
    SysTxMsgTablesStep s0 s w_m [] := by
  obtain ⟨hp, hm8, _, hin, hdisj⟩ := h
  refine ⟨hp, hm8, hin, fun S Nd hWT0 hD0 => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hdisj'⟩ := hdisj S Nd hWT0 hD0
  exact ⟨S', Nd', hsub, hWT', hOG, hFO, hdisj', fun _ hp' => by cases hp'⟩

theorem sysTxMsgTablesStep_htab_new {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F}
    {w_m : BitVec 64} {tabs : List (Nat × Nat)}
    {x : MlS} {kw capw : BitVec 64} {cont : ProgHOL 64}
    (hW0 : WorldOK s0)
    (h0 : SysTxMsgTablesStep s0 s w_m tabs)
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      SysTxMsgTablesStep s0 mid w_m (tabs ++ [(tw.toNat, kw.toNat)]) ∧
      WorldOK mid ∧
      mid.code = s.code ∧
      mid.locals.lookup x = some (.val (.word tw)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ a : BitVec 64, ¬ CellHits a.toNat (heapFree s) → mid.memory a = s.memory a) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      FlowingOrResumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  obtain ⟨hp0, hm8, hin_m0, hstep0⟩ := h0
  have hWs : WorldOK s := worldOK_of_sysTxStep hW0 hp0.1
  obtain ⟨tw, mid, htw_lo, _, hW_mid, hcode_mid, hbe_mid, hsp_mid, hfmp_mid,
    hwf_mid, _, hhdr0_mid, hfp_mid, hfr_mid, hout_mid, hstep_mid,
    hlx, hly, hgl_mid, hnt_c, hfr_c, hr_eq, hs_eq⟩ :=
    decCall_htab_new_sysTxStep s x kw capw cont hWs hkl hcl hnt hfr
  have hfr_hf : ∀ a : BitVec 64, ¬ CellHits a.toNat (heapFree s) → mid.memory a = s.memory a := by
    intro a hnhf
    by_cases hdom : ordinaryDomain a
    · have ha8 : a.toNat % 8 = 0 := (M13.ordinaryDomain_iff a).1 hdom |>.2.2
      have hsp8 := hWs.1.2.2.2.2.2.2.2.2.1
      apply hfr_mid a
      · intro j hj ⟨hc1, hc2⟩
        simp only [List.mem_singleton] at hj; subst hj
        dsimp only at hc1 hc2; omega
      · intro ⟨hc1, hc2⟩
        apply hnhf
        unfold heapFree
        have hp_lim := hW_mid.1.2.2.1
        dsimp only at hc1 hc2 ⊢
        exact ⟨hc1, by omega⟩
    · exact hout_mid a hdom
  have hp_tot : SysTxPrefixStep s0 none mid := sysTxPrefixStep_trans hW0.1 hp0 hstep_mid
  have hin_m_mid : Inside (w_m.toNat, 176) (globN s0 "heap_ptr") (globN mid "heap_ptr") :=
    ⟨hin_m0.1, le_trans hin_m0.2 hstep_mid.1.2.1⟩
  refine ⟨tw, mid, ⟨hp_tot, hm8, hin_m_mid, fun S Nd hWT0 hD0 => ?_⟩,
    hW_mid, hcode_mid, hlx, hly, hfr_hf, hnt_c, hfr_c, hr_eq, hs_eq⟩
  obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, hdisj1, htabs1⟩ := hstep0 S Nd hWT0 hD0
  obtain ⟨_, _, hslot_tw, hWT2, hOG12, hwrs_eq, hjrs_eq, hfeq, hne_eq, hhdr_eq, hfp_S_eq⟩ :=
    worldTypedWith_htab_new_sysTx hWs.1 hW_mid.1 hbe_mid hstep_mid.1.2.1 hsp_mid
      hwf_mid hhdr0_mid hfp_mid hout_mid hfr_mid hgl_mid hWT1
  have hwo_S1_eq : worldOwned mid S1 Nd1 = worldOwned s S1 Nd1 := by
    unfold worldOwned
    rw [List.flatMap_congr hfp_S_eq, hfeq, hne_eq]
  refine ⟨S1 ++ [tw.toNat], Nd1,
    fun t ht => List.mem_append_left _ (hsub01 t ht),
    hWT2, ?_, ?_, ?_, ?_⟩
  · intro o ho
    rcases hOG12 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o12
    · exact Or.inl rfl
    · rcases hOG01 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j01
      · left
        rcases o with ⟨o1, o2⟩
        dsimp only [Inside] at hin_oj
        exact Prod.ext (by omega) (by omega)
      · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
      · exact Or.inr (Or.inr ⟨le_trans hin_j01.1 hin_oj.1,
          le_trans hin_oj.2 (le_trans hin_j01.2 hstep_mid.1.2.1)⟩)
    · exact Or.inr (Or.inr ⟨le_trans hp0.1.2.1 hin_o12.1, hin_o12.2⟩)
  · intro a ha hhf0
    have hm12 : mid.memory a = s.memory a := by
      apply hfr_hf a
      intro ⟨hc1, hc2⟩
      apply hhf0
      unfold heapFree at hc1 hc2 ⊢
      have := hp0.1.2.1
      have := hWs.1.2.2.1
      dsimp only at hc1 hc2 ⊢
      exact ⟨by omega, by omega⟩
    exact hm12.trans (hFO01 a ha hhf0)
  · intro i hi o ho
    simp only [List.mem_singleton] at hi; subst hi
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htab_S1 | htab_tw
        · exact hdisj1 (w_m.toNat, 176) (by simp) o (by
            rw [← hwo_S1_eq]
            exact List.mem_append_left _ (List.mem_append_left _ htab_S1))
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htab_tw
          have hin_tw_o := (hfp_mid o htab_tw).2
          exact Or.inr (Or.inr (Or.inl (le_trans hin_m0.2 hin_tw_o.1)))
      · exact hdisj1 (w_m.toNat, 176) (by simp) o (by
          rw [← hwo_S1_eq]
          exact List.mem_append_left _ (List.mem_append_right _ hfix))
    · exact hdisj1 (w_m.toNat, 176) (by simp) o (by
        rw [← hwo_S1_eq]
        exact List.mem_append_right _ hnd)
  · intro p hp_mem
    rcases List.mem_append.1 hp_mem with hp_old | hp_new
    · obtain ⟨hp_S1, hp_hdr, hp_slot⟩ := htabs1 p hp_old
      refine ⟨List.mem_append_left _ hp_S1, ?_, ?_⟩
      · rw [hhdr_eq p.1 hp_S1]; exact hp_hdr
      · rw [hwrs_eq, hjrs_eq]; exact hp_slot
    · simp only [List.mem_singleton] at hp_new; subst hp_new
      exact ⟨List.mem_append_right _ (List.mem_singleton.2 rfl), hhdr0_mid, hslot_tw⟩

theorem sysTxMsgTablesStep_store_word {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F}
    {bname : MlS} {w_m w_val : BitVec 64} {tabs : List (Nat × Nat)}
    {off : Nat} {src : ExpHOL 64} {cont : ProgHOL 64}
    (hW0 : WorldOK s0)
    (h0 : SysTxMsgTablesStep s0 s w_m tabs)
    (hl_m : s.locals.lookup bname = some (.val (.word w_m)))
    (hoff8 : off % 8 = 0)
    (hoff_fit : off + 8 ≤ 176)
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src =
      some (.val (.word w_val)))
    (hnt : (evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) src) cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) src) cont)).1) :
    ∃ mem' : BitVec 64 → HolWordLab 64,
      SysTxMsgTablesStep s0 { s with memory := mem' } w_m tabs ∧
      WorldOK { s with memory := mem' } ∧
      memW ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_m.toNat + off) = w_val.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ 176 → off' ≠ off →
        memW ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_m.toNat + off') =
          memW s (w_m.toNat + off')) ∧
      (evaluateHOLFiniteState { s with memory := mem' } cont).1 ≠ some .timeOut ∧
      FlowingOrResumes (evaluateHOLFiniteState { s with memory := mem' } cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) src) cont) =
        evaluateHOLFiniteState { s with memory := mem' } cont := by
  obtain ⟨hp0, hm8, hin_m, hstep0⟩ := h0
  have hfb0 : SysTxFreshBlockStep s0 none s w_m 176 :=
    ⟨hp0, hm8, by decide, hin_m, fun S Nd hWT0 hD0 => by
      obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hdisj, _⟩ := hstep0 S Nd hWT0 hD0
      exact ⟨S', Nd', hsub, hWT', hOG, hFO, hdisj⟩⟩
  obtain ⟨mem', v, hv_eq, hst, hfb', hW', hframe, hnt_c, hfr_c, heval_eq⟩ :=
    seq_store_freshBlock_step hW0 hfb0 hl_m hoff8
      (fun v hv => by rw [hsrc] at hv; injection hv with hv'; subst hv'; simp [flattenHOL]; omega)
      hnt hfr
  rw [hsrc] at hv_eq
  injection hv_eq with hv_eq'; subst hv_eq'
  have hWs : WorldOK s := worldOK_of_sysTxStep hW0 hp0.1
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hp0.1.1.2.2.1
  have hp0_lo : sourceBase ≤ globN s0 "heap_ptr" := hW0.1.2.1
  have hin_blk : Inside (w_m.toNat, 176) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hp0_lo hin_m.1, hin_m.2⟩
  have hx_nat : (w_m + BitVec.ofNat 64 off).toNat = w_m.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hoff_lt : off < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hoff_lt]
    exact Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)
  have hcell_blk : ∀ a : BitVec 64, ¬ CellHits a.toNat (w_m.toNat, 176) → mem' a = s.memory a := by
    intro a hnh
    apply hframe a
    intro k hk h_eq
    simp [flattenHOL] at hk
    subst hk
    apply hnh
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h_eq
    rw [h_eq]
    unfold CellHits
    rw [hx_nat]
    exact ⟨by omega, by omega⟩
  have hst_read : memW ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_m.toNat + off) = w_val.toNat := by
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hst
    split_ifs at hst with hdom
    simp only [Option.some.injEq] at hst
    have hbv : BitVec.ofNat 64 (w_m.toNat + off) = w_m + BitVec.ofNat 64 off := by
      apply BitVec.eq_of_toNat_eq
      rw [hx_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)]
    unfold memW
    dsimp only
    rw [hbv, ← hst]
    simp
  have hst_other : ∀ off' : Nat, off' + 8 ≤ 176 → off' ≠ off →
      memW ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_m.toNat + off') =
        memW s (w_m.toNat + off') := by
    intro off' hoff'_fit hne
    unfold memW
    dsimp only
    rw [hframe (BitVec.ofNat 64 (w_m.toNat + off'))]
    intro k hk h_eq
    simp [flattenHOL] at hk
    subst hk
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h_eq
    have hlhs : (BitVec.ofNat 64 (w_m.toNat + off')).toNat = w_m.toNat + off' := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)]
    have := congrArg BitVec.toNat h_eq
    rw [hlhs, hx_nat] at this
    omega
  refine ⟨mem', ⟨hfb'.1, hm8, hin_m, fun S Nd hWT0 hD0 => ?_⟩,
    hW', hst_read, hst_other, hnt_c, hfr_c, heval_eq⟩
  obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, hdisj1, htabs1⟩ := hstep0 S Nd hWT0 hD0
  have hdisj_t1 : IvlsDisj [(w_m.toNat, 176)] (worldTypedIvls s S1 Nd1) :=
    fun i hi j hj => hdisj1 i hi j (worldTypedIvls_sub_worldOwned_sysTx s S1 Nd1 j hj)
  have hcell_s1 : M13.SameTypedCells s { s with memory := mem' } S1 Nd1 := by
    refine ⟨rfl, rfl, hWs.1.1.memaddrs,
      fun a hnd => panMemStoresHOL_out_dom hst (by rw [hWs.1.1.memaddrs]; exact hnd), ?_, ?_⟩
    · intro a ha _ ⟨i, hi, ha1, ha2⟩
      have ha_mod : (BitVec.ofNat 64 a).toNat = a := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
      apply hcell_blk (BitVec.ofNat 64 a)
      intro ⟨hc1, hc2⟩
      rw [ha_mod] at hc1 hc2
      rcases hdisj_t1 (w_m.toNat, 176) (by simp) i hi with h0_d | h0_d | hd | hd <;>
        dsimp only at * <;> omega
    · intro b hb64 ⟨i, hi, hb1, hb2⟩
      unfold memB
      dsimp only
      have hal_eq : mem' (panByteAlignHOL (BitVec.ofNat 64 b)) =
          s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
        apply hcell_blk
        intro ⟨hc1, hc2⟩
        have hal_nat : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
          rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64]
        rw [hal_nat] at hc1 hc2
        rcases hdisj_t1 (w_m.toNat, 176) (by simp) i hi with h0_d | h0_d | hd | hd <;>
          dsimp only at * <;> omega
      rw [hal_eq]
  have hg_core : ∀ g ∈ M13.coreWorldGlobals, globN ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) g = globN s g :=
    fun _ _ => rfl
  have hfeq : fixedObjects ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) = fixedObjects s := by
    unfold fixedObjects
    rw [M13.blockOutObjects_eq hWs.1.2 hWT1.2.2.1 hcell_s1 rfl,
        M13.balObjects_eq hWs.1.2 hWT1.1 hWT1.2.2.1 hcell_s1 rfl]
    rfl
  have hFT_post : FixedTyped ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) :=
    M13.fixedTyped_of_eq hW'.1 hWT1.2.2.1 le_rfl le_rfl hfeq
  obtain ⟨hWT_post, _⟩ := M13.worldTypedWith_congr_w1 hWs.1 hW'.1 le_rfl le_rfl hg_core hcell_s1 hWT1
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hne_eq : nodeExtents ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) Nd1 = nodeExtents s Nd1 :=
    M13.nodeExtents_eq hWT1.2.2.2.1 hcell_s1
  have hfp_eq : ∀ u ∈ S1, htabFootprint ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) u = htabFootprint s u :=
    fun u hu => M13.htabFootprint_eq hcell_s1 hu (hWT1.1.2.1 u hu).1
  have hwo_eq : worldOwned ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) S1 Nd1 = worldOwned s S1 Nd1 := by
    unfold worldOwned
    rw [List.flatMap_congr hfp_eq, hfeq, hne_eq]
  have hwrs_eq : worldRoleSlots ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) = worldRoleSlots s :=
    M13.worldRoleSlots_eq hWs.1.2 hWT1.1 hWT1.2.2.1 hcell_s1 hg_core
  have hjrs_eq : journalRoleSlots ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) = journalRoleSlots s :=
    M13.journalRoleSlots_eq hWs.1.2 hWT1.2.1 hWT1.2.2.1 hcell_s1 hg_core
  have hhdr_eq : ∀ u ∈ S1, hdr ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) u 0 = hdr s u 0 := by
    intro u hu
    have htb := ((hWT1.1.2.1 u hu).1.1 (u, 88) (by simp [htabFootprint])).1
    exact M13.htab_hdr_eq hcell_s1 hu htb 0 (by omega)
  refine ⟨S1, Nd1, hsub01, hWT_post,
    by rw [hwo_eq]; exact hOG01,
    fun a ha hhf => (hcell_blk a (fun ⟨hc1, hc2⟩ => hhf (by
      unfold heapFree; dsimp only [Inside] at hin_m ⊢; exact ⟨by omega, by omega⟩))).trans (hFO01 a ha hhf),
    by rw [hwo_eq]; exact hdisj1,
    fun p hp_mem => ?_⟩
  obtain ⟨hp_S1, hp_hdr, hp_slot⟩ := htabs1 p hp_mem
  refine ⟨hp_S1, ?_, ?_⟩
  · rw [hhdr_eq p.1 hp_S1]; exact hp_hdr
  · rw [hwrs_eq, hjrs_eq]; exact hp_slot

theorem lookupCode_unchecked_sysTx_words {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "process_unchecked_system_transaction") vals =
        some (sourceFnBody Guest.Software.guestFn_process_unchecked_system_transaction, L, .one)) :
    ∃ wt wd wdn : BitVec 64,
      L.lookup (ofString "target") = some (.val (.word wt)) ∧
      L.lookup (ofString "data") = some (.val (.word wd)) ∧
      L.lookup (ofString "data_n") = some (.val (.word wdn)) := by
  obtain ⟨wt, wd, wdn, _, ht, hd, hdn⟩ :=
    lookupCode_three_words (by decide) (by decide) (by decide)
      lookup_process_unchecked_system_transaction hl
  exact ⟨wt, wd, wdn, ht, hd, hdn⟩

theorem seq_call0_prefix_step {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hc : s.code = originalRuntimeCode) (hW0 : WorldOK s0)
    (h0 : SysTxPrefixStep s0 none s)
    (hf : FunSpec WorldOK (fun s r post => Resumes r → SysTxPrefixStep s r post) fname)
    (hnt : (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) cont)).1) :
    (SysTxPrefixStep s0
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) cont)).1
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) cont)).2 ∧
     ∃ e ev, (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) cont)).1 =
       some (.exception e ev)) ∨
    ∃ mid : PanSemStateFiniteExact 64 F,
      SysTxPrefixStep s0 none mid ∧
      WorldOK mid ∧
      mid.code = originalRuntimeCode ∧
      mid.locals = s.locals ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      FlowingOrResumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) cont) =
        evaluateHOLFiniteState mid cont := by
  have hWs : WorldOK s := worldOK_of_sysTxStep hW0 h0.1
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s (.call (some (none, none)) fname args)).1
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hWs
        have hmeta_c := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun hmeta_c
        simp only [hrun] at hmeta_c hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact Or.inl ⟨sysTxPrefixStep_trans hW0.1 h0 (sysTxPrefixStep_from_entry (hspec hres_ex)),
              eid, ev, rfl⟩
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              set mid := { cpost with locals := s.locals }
              have hs1 : SysTxPrefixStep s none mid :=
                sysTxPrefixStep_from_entry (post := cpost) (L := s.locals) (hspec (Or.inl ⟨v, rfl⟩))
              have hp_tot := sysTxPrefixStep_trans hW0.1 h0 hs1
              exact Or.inr ⟨mid, hp_tot, worldOK_of_sysTxStep hW0 hp_tot.1, hmeta_c.trans hc, rfl, hnt, hfr, rfl⟩
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem decCall_prefix_shaped_step {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F}
    {x : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hc : s.code = originalRuntimeCode) (hW0 : WorldOK s0)
    (h0 : SysTxPrefixStep s0 none s)
    (hf : FunSpec WorldOK (fun s r post => Resumes r → SysTxPrefixStep s r post) fname)
    (hnt : (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1) :
    (SysTxPrefixStep s0
      (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1
      (evaluateHOLFiniteState s (.decCall x sh fname args cont)).2 ∧
     ∃ e ev, (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 =
       some (.exception e ev)) ∨
    ∃ (v : ValueHOL 64) (mid : PanSemStateFiniteExact 64 F),
      SysTxPrefixStep s0 none mid ∧
      WorldOK mid ∧
      mid.code = originalRuntimeCode ∧
      shapeOfHOLExact v = sh ∧
      mid.locals.lookup x = some v ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      FlowingOrResumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x sh fname args cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  have hWs : WorldOK s := worldOK_of_sysTxStep hW0 h0.1
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hWs
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun hmeta
        simp only [hrun] at hmeta hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact Or.inl ⟨sysTxPrefixStep_trans hW0.1 h0 (sysTxPrefixStep_from_entry (hspec hres_ex)),
              eid, ev, rfl⟩
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hv_sh : shapeOfHOLExact v = sh :=
                (shapeEqHOL_eq_true _ _).1 ((Bool.and_eq_true _ _ ▸ hsh).1)
              have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              set mid := setVarHOLFinite x v { cpost with locals := s.locals }
              have hs1 : SysTxPrefixStep s none mid :=
                sysTxPrefixStep_from_entry (post := cpost) (L := mid.locals) (hspec (Or.inl ⟨v, rfl⟩))
              have hp_tot := sysTxPrefixStep_trans hW0.1 h0 hs1
              exact Or.inr ⟨v, mid, hp_tot, worldOK_of_sysTxStep hW0 hp_tot.1, hmeta.trans hc, hv_sh,
                by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
                fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hy],
                hnt, hfr, rfl, rfl⟩
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem msgReady_of_sysTxMsgTablesStep {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {w_m w_aa w_ak : BitVec 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    (hW0 : WorldOK s0)
    (hstep : SysTxMsgTablesStep s0 s w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hgas : memW s (w_m.toNat + 40) = 30000000)
    (hm152 : memW s (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s (w_m.toNat + 160) = w_ak.toNat)
    (hcallee : callee.lookup (ofString "msg") = some (.val (.word w_m))) :
    MsgReady (callEntryStateHOLFinite s callee) := by
  obtain ⟨hp, hm8, hin_m, htabs_step⟩ := hstep
  obtain ⟨hA0, S0, hS0⟩ := hW0
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s0 S0).1 hS0
  have hD0 : IvlsDisj (bufRegions sysTxBufs s0) (worldTypedIvls s0 S0 Nd0) :=
    validBufList_disj validBufList_sysTxBufs hWT0
  obtain ⟨S', Nd', _, hWT', _, _, hdisj', htabs⟩ := htabs_step S0 Nd0 hWT0 hD0
  obtain ⟨haa_S, haa_hdr, haa_slot⟩ := htabs (w_aa.toNat, 20) (by simp)
  obtain ⟨hak_S, hak_hdr, hak_slot⟩ := htabs (w_ak.toNat, 52) (by simp)
  set ent := callEntryStateHOLFinite s callee
  have hA_ent : ArenaReady ent := localsFree_arenaReady s callee (s.clock - 1) hp.1.1
  have hWT_ent : WorldTypedWith ent S' Nd' :=
    ⟨(tablesTyped_with_locals s callee (s.clock - 1) S').2 hWT'.1,
      hWT'.2.1, hWT'.2.2.1, hWT'.2.2.2.1, hWT'.2.2.2.2.1, hWT'.2.2.2.2.2⟩
  have hloc_msg : locN ent "msg" = w_m.toNat := by
    simp [ent, callEntryStateHOLFinite, decClockHOLFinite, locN, hcallee]
  have hin_m_ent : Inside (w_m.toNat, 176) sourceBase (globN ent "heap_ptr") :=
    ⟨le_trans hA0.2.1 hin_m.1, hin_m.2⟩
  exact msgReady_of_sysTx_parts hA_ent hWT_ent hloc_msg hm152 hm160
    haa_S hak_S haa_hdr hak_hdr haa_slot hak_slot hin_m_ent hm8
    (fun o ho => hdisj' (w_m.toNat, 176) (by simp) o ho) hgas

def SysTxPrefixOutcome {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (prog : ProgHOL 64)
    (pmcCont : ProgHOL 64) : Prop :=
  (SysTxPrefixStep s0 (evaluateHOLFiniteState s0 prog).1 (evaluateHOLFiniteState s0 prog).2 ∧
   ∃ e ev, (evaluateHOLFiniteState s0 prog).1 = some (.exception e ev)) ∨
  ∃ (s_pmc : PanSemStateFiniteExact 64 F) (w_m w_aa w_ak : BitVec 64)
    (L_wrap : HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64)),
    SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)] ∧
    WorldOK s_pmc ∧
    s_pmc.code = originalRuntimeCode ∧
    s_pmc.locals.lookup (ofString "m") = some (.val (.word w_m)) ∧
    memW s_pmc (w_m.toNat + 152) = w_aa.toNat ∧
    memW s_pmc (w_m.toNat + 160) = w_ak.toNat ∧
    (∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      callee.lookup (ofString "msg") = some (.val (.word w_m)) →
      MsgReady (callEntryStateHOLFinite s_pmc callee)) ∧
    (evaluateHOLFiniteState s_pmc
      (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] pmcCont)).1 ≠
      some .timeOut ∧
    FlowingOrResumes (evaluateHOLFiniteState s_pmc
      (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] pmcCont)).1 ∧
    (evaluateHOLFiniteState s0 prog).1 =
      (evaluateHOLFiniteState s_pmc
        (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] pmcCont)).1 ∧
    (evaluateHOLFiniteState s0 prog).2 =
      { (evaluateHOLFiniteState s_pmc
          (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] pmcCont)).2 with
        locals := L_wrap
          (evaluateHOLFiniteState s_pmc
            (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] pmcCont)).2.locals }

def SysTxAtProg {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (prog : ProgHOL 64)
    (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) : Prop :=
  ∃ L_wrap : HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64),
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut ∧
    FlowingOrResumes (evaluateHOLFiniteState s p).1 ∧
    (evaluateHOLFiniteState s0 prog).1 = (evaluateHOLFiniteState s p).1 ∧
    (evaluateHOLFiniteState s0 prog).2 =
      { (evaluateHOLFiniteState s p).2 with locals := L_wrap (evaluateHOLFiniteState s p).2.locals }

theorem sysTxAtProg_refl {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (prog : ProgHOL 64)
    (hnt : (evaluateHOLFiniteState s0 prog).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s0 prog).1) :
    SysTxAtProg s0 prog s0 prog :=
  ⟨id, hnt, hfr, rfl, rfl⟩

theorem sysTxAtProg_eq {F : Type}
    {s0 s s' : PanSemStateFiniteExact 64 F} {prog p p' : ProgHOL 64}
    (h : SysTxAtProg s0 prog s p)
    (hnt' : (evaluateHOLFiniteState s' p').1 ≠ some .timeOut)
    (hfr' : FlowingOrResumes (evaluateHOLFiniteState s' p').1)
    (heq : evaluateHOLFiniteState s p = evaluateHOLFiniteState s' p') :
    SysTxAtProg s0 prog s' p' := by
  obtain ⟨Lw, _, _, hr, hs⟩ := h
  exact ⟨Lw, hnt', hfr', hr.trans (congrArg Prod.fst heq), by rw [hs, heq]⟩

theorem sysTxAtProg_resVar {F : Type}
    {s0 s s' : PanSemStateFiniteExact 64 F} {prog p p' : ProgHOL 64}
    {x : MlS}
    (h : SysTxAtProg s0 prog s p)
    (hnt' : (evaluateHOLFiniteState s' p').1 ≠ some .timeOut)
    (hfr' : FlowingOrResumes (evaluateHOLFiniteState s' p').1)
    (hr_eq : (evaluateHOLFiniteState s p).1 = (evaluateHOLFiniteState s' p').1)
    (hs_eq : (evaluateHOLFiniteState s p).2 =
      { (evaluateHOLFiniteState s' p').2 with
        locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s' p').2.locals (x, s.locals.lookup x) }) :
    SysTxAtProg s0 prog s' p' := by
  obtain ⟨Lw, _, _, hr, hs⟩ := h
  exact ⟨fun L => Lw (HolFiniteMapExact.resVarEq L (x, s.locals.lookup x)),
    hnt', hfr', hr.trans hr_eq, by rw [hs, hs_eq]⟩

theorem sysTxPrefixOutcome_ex {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {prog pmcCont p : ProgHOL 64}
    (hat : SysTxAtProg s0 prog s p)
    (hex : SysTxPrefixStep s0 (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2 ∧
      ∃ e ev, (evaluateHOLFiniteState s p).1 = some (.exception e ev)) :
    SysTxPrefixOutcome s0 prog pmcCont := by
  obtain ⟨Lw, _, _, hr, hs⟩ := hat
  obtain ⟨hstep, e, ev, hev⟩ := hex
  refine Or.inl ⟨?_, e, ev, hr.trans hev⟩
  rw [hr, hs]
  exact sysTxPrefixStep_with_locals_clock hstep _ (evaluateHOLFiniteState s p).2.clock

theorem sysTxPrefixOutcome_done {F : Type}
    {s0 s_pmc : PanSemStateFiniteExact 64 F} {prog pmcCont : ProgHOL 64}
    {w_m w_aa w_ak : BitVec 64}
    (hat : SysTxAtProg s0 prog s_pmc
      (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] pmcCont))
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hW : WorldOK s_pmc)
    (hc : s_pmc.code = originalRuntimeCode)
    (hl_m : s_pmc.locals.lookup (ofString "m") = some (.val (.word w_m)))
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hmr : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      callee.lookup (ofString "msg") = some (.val (.word w_m)) →
      MsgReady (callEntryStateHOLFinite s_pmc callee)) :
    SysTxPrefixOutcome s0 prog pmcCont := by
  obtain ⟨Lw, hnt, hfr, hr, hs⟩ := hat
  exact Or.inr ⟨s_pmc, w_m, w_aa, w_ak, Lw, hmt, hW, hc, hl_m, hm152, hm160, hmr, hnt, hfr, hr, hs⟩

def sysTxAfterIncorporate : ProgHOL 64 :=
  .dec (ofString "system_mark") .one
    (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 80)]))
    (.seq
      (.ite (.cmp .notEqual (.var .local (ofString "system_mark")) (.const (BitVec.ofNat 64 0)))
        (.dec (ofString "system_ret_n") .one
          (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 48)]))
          (.seq
            (.ite (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "system_ret_n")))
              (.decCall (ofString "system_ret") .one (ofString "alloc")
                [.op .add [.var .local (ofString "system_ret_n"), .const (BitVec.ofNat 64 8)]]
                (.seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "system_ret"),
                     .load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 40)]),
                     .var .local (ofString "system_ret_n")])
                  (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 40)])
                    (.var .local (ofString "system_ret")))))
              .skip)
            (.seq
              (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "system_mark")])
              (.call (some (none, none)) (ofString "frame_mem_release")
                [.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)])]))))
        .skip)
      (.return (.var .local (ofString "out"))))

@[irreducible] def sysTxPmcCont : ProgHOL 64 :=
  .seq .skip
    (.seq (.call (some (none, none)) (ofString "incorporate_tx_into_block") [])
      sysTxAfterIncorporate)

theorem sysTxAfterIncorporate_zero_mark {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hmark : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "out"), .const 80#64])) =
        some (.val (.word 0#64))) :
    evaluateHOLFiniteState s sysTxAfterIncorporate =
      let mid := setVarHOLFinite (ofString "system_mark") (.val (.word 0#64)) s
      let result := evaluateHOLFiniteState mid (.return (.var .local (ofString "out")))
      (result.1,
        { result.2 with
          locals := HolFiniteMapExact.resVarEq result.2.locals
            (ofString "system_mark", s.locals.lookup (ofString "system_mark")) }) := by
  unfold sysTxAfterIncorporate
  rw [evaluateHOLFiniteState_dec_total]
  simp only [hmark, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  simp [evalHOLExact, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    evaluateHOLFiniteState_skip]

@[irreducible] def sysTxAfterMsgNewMidProg (pmcCont : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 40)])
      (.const (BitVec.ofNat 64 30000000)))
    (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 48)])
        (.panop .mul [.const (BitVec.ofNat 64 97920), .const (BitVec.ofNat 64 16)]))
      (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 88)])
          (.var .local (ofString "data")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 96)])
            (.var .local (ofString "data_n")))
          (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 104)])
              (.var .local (ofString "target")))
            (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 112)])
                (.rfield 0 (.var .local (ofString "code"))))
              (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 120)])
                  (.rfield 1 (.var .local (ofString "code"))))
                (.decCall (ofString "aa") .one (ofString "htab_new")
                  [.const (BitVec.ofNat 64 20), .const (BitVec.ofNat 64 8)]
                  (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 152)])
                      (.var .local (ofString "aa")))
                    (.decCall (ofString "ak") .one (ofString "htab_new")
                      [.const (BitVec.ofNat 64 52), .const (BitVec.ofNat 64 8)]
                      (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 160)])
                          (.var .local (ofString "ak")))
                        (.seq .skip
                          (.decCall (ofString "out") .one (ofString "process_message_call")
                            [.var .local (ofString "m")] pmcCont))))))))))))

@[irreducible] def sysTxAfterMsgNewProg (pmcCont : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 0)])
      (.var .global (ofString "be")))
    (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 8)])
        (.var .local (ofString "te")))
      (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 16)])
          (.var .global (ofString "vm_system_address")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 24)])
            (.var .local (ofString "target")))
          (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 32)])
              (.var .local (ofString "target")))
            (sysTxAfterMsgNewMidProg pmcCont)))))

theorem sourceFnBody_unchecked_sysTx_eq :
    sourceFnBody Guest.Software.guestFn_process_unchecked_system_transaction =
      .seq (.call (some (none, none)) (ofString "state_fresh_tx") [])
        (.decCall (ofString "code") (.comb [.one, .one]) (ofString "ext_code_of")
          [.var .local (ofString "target")]
          (.decCall (ofString "te") .one (ofString "te_new") []
            (.seq (.store (.op .add [.var .local (ofString "te"), .const (BitVec.ofNat 64 0)])
                (.var .global (ofString "vm_system_address")))
              (.seq (.store (.op .add [.var .local (ofString "te"), .const (BitVec.ofNat 64 8)])
                  (.var .local (ofString "target")))
                (.seq (.store (.op .add [.var .local (ofString "te"), .const (BitVec.ofNat 64 48)])
                    (.load (.comb [.one, .one, .one, .one])
                      (.op .add [.var .global (ofString "be"), .const (BitVec.ofNat 64 48)])))
                  (.seq (.store (.op .add [.var .local (ofString "te"), .const (BitVec.ofNat 64 80)])
                      (.const (BitVec.ofNat 64 30000000)))
                    (.seq (.store (.op .add [.var .local (ofString "te"), .const (BitVec.ofNat 64 88)])
                        (.panop .mul [.const (BitVec.ofNat 64 97920), .const (BitVec.ofNat 64 16)]))
                      (.decCall (ofString "m") .one (ofString "msg_new") [] (sysTxAfterMsgNewProg sysTxPmcCont))))))))) := by
  unfold sysTxAfterMsgNewProg sysTxAfterMsgNewMidProg sysTxPmcCont sysTxAfterIncorporate
  rfl

@[irreducible] def sysTxAfterMsgNewTailProg (pmcCont : ProgHOL 64) : ProgHOL 64 :=
  .decCall (ofString "aa") .one (ofString "htab_new")
    [.const (BitVec.ofNat 64 20), .const (BitVec.ofNat 64 8)]
    (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 152)])
        (.var .local (ofString "aa")))
      (.decCall (ofString "ak") .one (ofString "htab_new")
        [.const (BitVec.ofNat 64 52), .const (BitVec.ofNat 64 8)]
        (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 160)])
            (.var .local (ofString "ak")))
          (.seq .skip
            (.decCall (ofString "out") .one (ofString "process_message_call")
              [.var .local (ofString "m")] pmcCont)))))

theorem sysTxAfterMsgNewMidProg_eq (pmcCont : ProgHOL 64) :
    sysTxAfterMsgNewMidProg pmcCont =
      .seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 40)])
          (.const (BitVec.ofNat 64 30000000)))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 48)])
            (.panop .mul [.const (BitVec.ofNat 64 97920), .const (BitVec.ofNat 64 16)]))
          (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 88)])
              (.var .local (ofString "data")))
            (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 96)])
                (.var .local (ofString "data_n")))
              (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 104)])
                  (.var .local (ofString "target")))
                (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 112)])
                    (.rfield 0 (.var .local (ofString "code"))))
                  (.seq (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 120)])
                      (.rfield 1 (.var .local (ofString "code"))))
                    (sysTxAfterMsgNewTailProg pmcCont))))))) := by
  unfold sysTxAfterMsgNewMidProg sysTxAfterMsgNewTailProg
  rfl

theorem prefix_unchecked_sysTx_after_msg_new_tail {F : Type}
    {s0 s21 : PanSemStateFiniteExact 64 F} {prog pmcCont : ProgHOL 64}
    {w_m : BitVec 64}
    (hW0 : WorldOK s0)
    (hat21 : SysTxAtProg s0 prog s21 (sysTxAfterMsgNewTailProg pmcCont))
    (hmt21 : SysTxMsgTablesStep s0 s21 w_m [])
    (hW21 : WorldOK s21)
    (hc21 : s21.code = originalRuntimeCode)
    (hl_m21 : s21.locals.lookup (ofString "m") = some (.val (.word w_m)))
    (hgas21 : memW s21 (w_m.toNat + 40) = 30000000) :
    SysTxPrefixOutcome s0 prog pmcCont := by
  have hnt21 := hat21.choose_spec.1
  have hfr21 := hat21.choose_spec.2.1
  unfold sysTxAfterMsgNewTailProg at hat21 hnt21 hfr21
  obtain ⟨w_aa, s22, hmt22, hW22, hc22, hl_aa22, hl_other22, hfr_aa22, hnt22, hfr22, hr22, hs22⟩ :=
    sysTxMsgTablesStep_htab_new hW0 hmt21 (by decide) (by decide) hnt21 hfr21
  have hat22 := sysTxAtProg_resVar hat21 hnt22 hfr22 hr22 hs22
  have hl_m22 : s22.locals.lookup (ofString "m") = some (.val (.word w_m)) :=
    (hl_other22 _ (by decide)).trans hl_m21
  have hgas22 : memW s22 (w_m.toNat + 40) = 30000000 := by
    have hin21 := hmt21.2.2.1
    have hp0_lo := hW0.1.2.1
    have hhp21_lim := hW21.1.2.2.1
    have h264 : heapLimit ≤ heapEnd ∧ heapEnd < 2 ^ 64 := ⟨by decide, by decide⟩
    unfold memW
    rw [hfr_aa22 (BitVec.ofNat 64 (w_m.toNat + 40))]
    · exact hgas21
    · intro ⟨hc1, _⟩
      unfold heapFree at hc1
      have hlhs : (BitVec.ofNat 64 (w_m.toNat + 40)).toNat = w_m.toNat + 40 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Inside at hin21; omega)]
      dsimp only at hc1
      rw [hlhs] at hc1
      unfold Inside at hin21
      omega
  obtain ⟨mem23, hmt23, hW23, hm152_23, hoth23, hnt23, hfr23, heq23⟩ :=
    sysTxMsgTablesStep_store_word hW0 hmt22 hl_m22 (by decide) (by decide)
      (w_val := w_aa) (by simp [evalHOLExact, hl_aa22]) hnt22 hfr22
  set s23 : PanSemStateFiniteExact 64 F := { s22 with memory := mem23 }
  have hat23 := sysTxAtProg_eq hat22 hnt23 hfr23 heq23
  have hgas23 : memW s23 (w_m.toNat + 40) = 30000000 := (hoth23 40 (by decide) (by decide)).trans hgas22
  obtain ⟨w_ak, s24, hmt24, hW24, hc24, hl_ak24, hl_other24, hfr_ak24, hnt24, hfr24, hr24, hs24⟩ :=
    sysTxMsgTablesStep_htab_new (s := s23) hW0 hmt23 (by decide) (by decide) hnt23 hfr23
  have hat24 := sysTxAtProg_resVar hat23 hnt24 hfr24 hr24 hs24
  have hl_m24 : s24.locals.lookup (ofString "m") = some (.val (.word w_m)) :=
    (hl_other24 _ (by decide)).trans hl_m22
  have hin23 := hmt23.2.2.1
  have hp0_lo := hW0.1.2.1
  have hhp23_lim := hW23.1.2.2.1
  have h264 : heapLimit ≤ heapEnd ∧ heapEnd < 2 ^ 64 := ⟨by decide, by decide⟩
  have hgas24 : memW s24 (w_m.toNat + 40) = 30000000 := by
    unfold memW
    rw [hfr_ak24 (BitVec.ofNat 64 (w_m.toNat + 40))]
    · exact hgas23
    · intro ⟨hc1, _⟩
      unfold heapFree at hc1
      have hlhs : (BitVec.ofNat 64 (w_m.toNat + 40)).toNat = w_m.toNat + 40 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Inside at hin23; omega)]
      dsimp only at hc1
      rw [hlhs] at hc1
      unfold Inside at hin23
      omega
  have hm152_24 : memW s24 (w_m.toNat + 152) = w_aa.toNat := by
    unfold memW
    rw [hfr_ak24 (BitVec.ofNat 64 (w_m.toNat + 152))]
    · exact hm152_23
    · intro ⟨hc1, _⟩
      unfold heapFree at hc1
      have hlhs : (BitVec.ofNat 64 (w_m.toNat + 152)).toNat = w_m.toNat + 152 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Inside at hin23; omega)]
      dsimp only at hc1
      rw [hlhs] at hc1
      unfold Inside at hin23
      omega
  obtain ⟨mem25, hmt25, hW25, hm160_25, hoth25, hnt25, hfr25, heq25⟩ :=
    sysTxMsgTablesStep_store_word hW0 hmt24 hl_m24 (by decide) (by decide)
      (w_val := w_ak) (by simp [evalHOLExact, hl_ak24]) hnt24 hfr24
  set s25 : PanSemStateFiniteExact 64 F := { s24 with memory := mem25 }
  have hat25 := sysTxAtProg_eq hat24 hnt25 hfr25 heq25
  have hgas25 := (hoth25 40 (by decide) (by decide)).trans hgas24
  have hm152_25 := (hoth25 152 (by decide) (by decide)).trans hm152_24
  have hskip : evaluateHOLFiniteState s25
      (.seq .skip (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] pmcCont)) =
      evaluateHOLFiniteState s25
        (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] pmcCont) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip]
  rw [hskip] at hnt25 hfr25
  have hat26 := sysTxAtProg_eq hat25 hnt25 hfr25 hskip
  have hc25 : s25.code = originalRuntimeCode := hc24.trans (hc22.trans hc21)
  exact sysTxPrefixOutcome_done hat26 hmt25 hW25 hc25 hl_m24 hm152_25 hm160_25
    (fun callee hcallee => msgReady_of_sysTxMsgTablesStep hW0 hmt25 hgas25 hm152_25 hm160_25 hcallee)

theorem prefix_unchecked_sysTx_after_msg_new_mid {F : Type}
    {s0 s14 : PanSemStateFiniteExact 64 F} {prog pmcCont : ProgHOL 64}
    {w_m wt wd wdn wc0 wc1 : BitVec 64}
    (hW0 : WorldOK s0)
    (hat14 : SysTxAtProg s0 prog s14 (sysTxAfterMsgNewMidProg pmcCont))
    (hmt14 : SysTxMsgTablesStep s0 s14 w_m [])
    (hc14 : s14.code = originalRuntimeCode)
    (hl_m14 : s14.locals.lookup (ofString "m") = some (.val (.word w_m)))
    (hl_t14 : s14.locals.lookup (ofString "target") = some (.val (.word wt)))
    (hl_d14 : s14.locals.lookup (ofString "data") = some (.val (.word wd)))
    (hl_dn14 : s14.locals.lookup (ofString "data_n") = some (.val (.word wdn)))
    (hl_code14 : s14.locals.lookup (ofString "code") = some (.rStruct [.val (.word wc0), .val (.word wc1)])) :
    SysTxPrefixOutcome s0 prog pmcCont := by
  have hnt14 := hat14.choose_spec.1
  have hfr14 := hat14.choose_spec.2.1
  rw [sysTxAfterMsgNewMidProg_eq] at hat14 hnt14 hfr14
  obtain ⟨mem15, hmt15, _, hgas15, _, hnt15, hfr15, heq15⟩ :=
    sysTxMsgTablesStep_store_word hW0 hmt14 hl_m14 (by decide) (by decide)
      (w_val := BitVec.ofNat 64 30000000) (by simp [evalHOLExact]) hnt14 hfr14
  let s15 : PanSemStateFiniteExact 64 F := { s14 with memory := mem15 }
  have hat15 := sysTxAtProg_eq hat14 hnt15 hfr15 heq15
  obtain ⟨mem16, hmt16, _, _, hoth16, hnt16, hfr16, heq16⟩ :=
    sysTxMsgTablesStep_store_word (s := s15) hW0 hmt15 hl_m14 (by decide) (by decide)
      (w_val := BitVec.ofNat 64 97920 * BitVec.ofNat 64 16)
      (by simp [s15, evalHOLExact, evalListHOLExact, valueIsWord, valueWord, panOpHOL]) hnt15 hfr15
  let s16 : PanSemStateFiniteExact 64 F := { s14 with memory := mem16 }
  have hat16 := sysTxAtProg_eq hat15 hnt16 hfr16 heq16
  have hgas16 : memW s16 (w_m.toNat + 40) = 30000000 :=
    (hoth16 40 (by decide) (by decide)).trans (by simpa using hgas15)
  obtain ⟨mem17, hmt17, _, _, hoth17, hnt17, hfr17, heq17⟩ :=
    sysTxMsgTablesStep_store_word (s := s16) hW0 hmt16 hl_m14 (by decide) (by decide)
      (w_val := wd) (by simp [s16, evalHOLExact, hl_d14]) hnt16 hfr16
  let s17 : PanSemStateFiniteExact 64 F := { s14 with memory := mem17 }
  have hat17 := sysTxAtProg_eq hat16 hnt17 hfr17 heq17
  have hgas17 : memW s17 (w_m.toNat + 40) = 30000000 := (hoth17 40 (by decide) (by decide)).trans hgas16
  obtain ⟨mem18, hmt18, _, _, hoth18, hnt18, hfr18, heq18⟩ :=
    sysTxMsgTablesStep_store_word (s := s17) hW0 hmt17 hl_m14 (by decide) (by decide)
      (w_val := wdn) (by simp [s17, evalHOLExact, hl_dn14]) hnt17 hfr17
  let s18 : PanSemStateFiniteExact 64 F := { s14 with memory := mem18 }
  have hat18 := sysTxAtProg_eq hat17 hnt18 hfr18 heq18
  have hgas18 : memW s18 (w_m.toNat + 40) = 30000000 := (hoth18 40 (by decide) (by decide)).trans hgas17
  obtain ⟨mem19, hmt19, _, _, hoth19, hnt19, hfr19, heq19⟩ :=
    sysTxMsgTablesStep_store_word (s := s18) hW0 hmt18 hl_m14 (by decide) (by decide)
      (w_val := wt) (by simp [s18, evalHOLExact, hl_t14]) hnt18 hfr18
  let s19 : PanSemStateFiniteExact 64 F := { s14 with memory := mem19 }
  have hat19 := sysTxAtProg_eq hat18 hnt19 hfr19 heq19
  have hgas19 : memW s19 (w_m.toNat + 40) = 30000000 := (hoth19 40 (by decide) (by decide)).trans hgas18
  obtain ⟨mem20, hmt20, _, _, hoth20, hnt20, hfr20, heq20⟩ :=
    sysTxMsgTablesStep_store_word (s := s19) hW0 hmt19 hl_m14 (by decide) (by decide)
      (w_val := wc0) (by simp [s19, evalHOLExact, hl_code14]) hnt19 hfr19
  let s20 : PanSemStateFiniteExact 64 F := { s14 with memory := mem20 }
  have hat20 := sysTxAtProg_eq hat19 hnt20 hfr20 heq20
  have hgas20 : memW s20 (w_m.toNat + 40) = 30000000 := (hoth20 40 (by decide) (by decide)).trans hgas19
  obtain ⟨mem21, hmt21, hW21, _, hoth21, hnt21, hfr21, heq21⟩ :=
    sysTxMsgTablesStep_store_word (s := s20) hW0 hmt20 hl_m14 (by decide) (by decide)
      (w_val := wc1) (by simp [s20, evalHOLExact, hl_code14]) hnt20 hfr20
  let s21 : PanSemStateFiniteExact 64 F := { s14 with memory := mem21 }
  have hat21 := sysTxAtProg_eq hat20 hnt21 hfr21 heq21
  have hgas21 : memW s21 (w_m.toNat + 40) = 30000000 := (hoth21 40 (by decide) (by decide)).trans hgas20
  exact prefix_unchecked_sysTx_after_msg_new_tail hW0 hat21 hmt21 hW21 hc14 hl_m14 hgas21

theorem prefix_unchecked_sysTx_after_msg_new {F : Type}
    {s0 s9 : PanSemStateFiniteExact 64 F} {prog pmcCont : ProgHOL 64}
    {w_te w_m wt wd wdn wc0 wc1 : BitVec 64}
    (hW0 : WorldOK s0)
    (hat9 : SysTxAtProg s0 prog s9 (sysTxAfterMsgNewProg pmcCont))
    (hmt9 : SysTxMsgTablesStep s0 s9 w_m [])
    (hW9 : WorldOK s9)
    (hc9 : s9.code = originalRuntimeCode)
    (hl_m9 : s9.locals.lookup (ofString "m") = some (.val (.word w_m)))
    (hl_te9 : s9.locals.lookup (ofString "te") = some (.val (.word w_te)))
    (hl_t9 : s9.locals.lookup (ofString "target") = some (.val (.word wt)))
    (hl_d9 : s9.locals.lookup (ofString "data") = some (.val (.word wd)))
    (hl_dn9 : s9.locals.lookup (ofString "data_n") = some (.val (.word wdn)))
    (hl_code9 : s9.locals.lookup (ofString "code") = some (.rStruct [.val (.word wc0), .val (.word wc1)])) :
    SysTxPrefixOutcome s0 prog pmcCont := by
  have hnt9 := hat9.choose_spec.1
  have hfr9 := hat9.choose_spec.2.1
  unfold sysTxAfterMsgNewProg at hat9 hnt9 hfr9
  have hgw9 := hW9.1.2.2.2.2.2.2.2.2.2
  obtain ⟨w_be, hw_be⟩ := hgw9 "be" (by decide)
  obtain ⟨w_vsa, hw_vsa⟩ := hgw9 "vm_system_address" (by decide)
  obtain ⟨mem10, hmt10, _, _, _, hnt10, hfr10, heq10⟩ :=
    sysTxMsgTablesStep_store_word hW0 hmt9 hl_m9 (by decide) (by decide)
      (w_val := w_be) (by unfold GlobalWord at hw_be; simp [evalHOLExact, hw_be]) hnt9 hfr9
  let s10 : PanSemStateFiniteExact 64 F := { s9 with memory := mem10 }
  have hat10 := sysTxAtProg_eq hat9 hnt10 hfr10 heq10
  obtain ⟨mem11, hmt11, _, _, _, hnt11, hfr11, heq11⟩ :=
    sysTxMsgTablesStep_store_word (s := s10) hW0 hmt10 hl_m9 (by decide) (by decide)
      (w_val := w_te) (by simp [s10, evalHOLExact, hl_te9]) hnt10 hfr10
  let s11 : PanSemStateFiniteExact 64 F := { s9 with memory := mem11 }
  have hat11 := sysTxAtProg_eq hat10 hnt11 hfr11 heq11
  obtain ⟨mem12, hmt12, _, _, _, hnt12, hfr12, heq12⟩ :=
    sysTxMsgTablesStep_store_word (s := s11) hW0 hmt11 hl_m9 (by decide) (by decide)
      (w_val := w_vsa) (by unfold GlobalWord at hw_vsa; simp [s11, evalHOLExact, hw_vsa]) hnt11 hfr11
  let s12 : PanSemStateFiniteExact 64 F := { s9 with memory := mem12 }
  have hat12 := sysTxAtProg_eq hat11 hnt12 hfr12 heq12
  obtain ⟨mem13, hmt13, _, _, _, hnt13, hfr13, heq13⟩ :=
    sysTxMsgTablesStep_store_word (s := s12) hW0 hmt12 hl_m9 (by decide) (by decide)
      (w_val := wt) (by simp [s12, evalHOLExact, hl_t9]) hnt12 hfr12
  let s13 : PanSemStateFiniteExact 64 F := { s9 with memory := mem13 }
  have hat13 := sysTxAtProg_eq hat12 hnt13 hfr13 heq13
  obtain ⟨mem14, hmt14, _, _, _, hnt14, hfr14, heq14⟩ :=
    sysTxMsgTablesStep_store_word (s := s13) hW0 hmt13 hl_m9 (by decide) (by decide)
      (w_val := wt) (by simp [s13, evalHOLExact, hl_t9]) hnt13 hfr13
  let s14 : PanSemStateFiniteExact 64 F := { s9 with memory := mem14 }
  have hat14 := sysTxAtProg_eq hat13 hnt14 hfr14 heq14
  exact prefix_unchecked_sysTx_after_msg_new_mid hW0 hat14 hmt14 hc9 hl_m9 hl_t9 hl_d9 hl_dn9 hl_code9

theorem prefix_unchecked_sysTx_to_pmc {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (hc0 : s0.code = originalRuntimeCode)
    (hW0 : WorldOK s0)
    (wt wd wdn : BitVec 64)
    (hl_t0 : s0.locals.lookup (ofString "target") = some (.val (.word wt)))
    (hl_d0 : s0.locals.lookup (ofString "data") = some (.val (.word wd)))
    (hl_dn0 : s0.locals.lookup (ofString "data_n") = some (.val (.word wdn)))
    (hnt0 : (evaluateHOLFiniteState s0
      (sourceFnBody Guest.Software.guestFn_process_unchecked_system_transaction)).1 ≠ some .timeOut)
    (hfr0 : FlowingOrResumes (evaluateHOLFiniteState s0
      (sourceFnBody Guest.Software.guestFn_process_unchecked_system_transaction)).1) :
    SysTxPrefixOutcome s0
      (sourceFnBody Guest.Software.guestFn_process_unchecked_system_transaction) sysTxPmcCont := by
  rw [sourceFnBody_unchecked_sysTx_eq] at hnt0 hfr0
  have hat0' : SysTxAtProg s0 (sourceFnBody Guest.Software.guestFn_process_unchecked_system_transaction) s0 _ :=
    ⟨id, hnt0, hfr0, congrArg Prod.fst (congrArg (evaluateHOLFiniteState s0) sourceFnBody_unchecked_sysTx_eq),
      congrArg Prod.snd (congrArg (evaluateHOLFiniteState s0) sourceFnBody_unchecked_sysTx_eq)⟩
  have hp0 : SysTxPrefixStep s0 none s0 := sysTxPrefixStep_refl s0 none hW0.1
  rcases seq_call0_prefix_step hc0 hW0 hp0 sysTxPrefix_state_fresh_tx hnt0 hfr0 with
    hex | ⟨s1, hp1, hW1, hc1, hloc1, hnt1, hfr1, heq1⟩
  · exact sysTxPrefixOutcome_ex hat0' hex
  have hat1 := sysTxAtProg_eq hat0' hnt1 hfr1 heq1
  rcases decCall_prefix_shaped_step hc1 hW0 hp1 sysTxPrefix_ext_code_of hnt1 hfr1 with
    hex | ⟨vcode, s2, hp2, hW2, hc2, hcode_sh, hl_code2, hl_other2, hnt2, hfr2, hr2, hs2⟩
  · exact sysTxPrefixOutcome_ex hat1 hex
  have hat2 := sysTxAtProg_resVar hat1 hnt2 hfr2 hr2 hs2
  have hl_t2 : s2.locals.lookup (ofString "target") = some (.val (.word wt)) :=
    (hl_other2 _ (by decide)).trans ((congrArg (fun L => L.lookup (ofString "target")) hloc1).trans hl_t0)
  have hl_d2 : s2.locals.lookup (ofString "data") = some (.val (.word wd)) :=
    (hl_other2 _ (by decide)).trans ((congrArg (fun L => L.lookup (ofString "data")) hloc1).trans hl_d0)
  have hl_dn2 : s2.locals.lookup (ofString "data_n") = some (.val (.word wdn)) :=
    (hl_other2 _ (by decide)).trans ((congrArg (fun L => L.lookup (ofString "data_n")) hloc1).trans hl_dn0)
  rcases decCall_te_new_freshStep s2 (ofString "te") _ hc2 hW2 hnt2 hfr2 with
    ⟨hstep_ex, e, ev, hev⟩ | ⟨w_te, s3, hfb3_2, hW3, hc3, hl_te3, hl_other3, _, hnt3, hfr3, hr3, hs3⟩
  · exact sysTxPrefixOutcome_ex hat2 ⟨sysTxPrefixStep_trans hW0.1 hp2 hstep_ex, e, ev, hev⟩
  have hat3 := sysTxAtProg_resVar hat2 hnt3 hfr3 hr3 hs3
  have hfb3 : SysTxFreshBlockStep s0 none s3 w_te 200 := sysTxFreshBlockStep_prepend hW0 hp2 hfb3_2
  have hl_t3 : s3.locals.lookup (ofString "target") = some (.val (.word wt)) :=
    (hl_other3 _ (by decide)).trans hl_t2
  have hl_d3 : s3.locals.lookup (ofString "data") = some (.val (.word wd)) :=
    (hl_other3 _ (by decide)).trans hl_d2
  have hl_dn3 : s3.locals.lookup (ofString "data_n") = some (.val (.word wdn)) :=
    (hl_other3 _ (by decide)).trans hl_dn2
  have hl_code3 : s3.locals.lookup (ofString "code") = some vcode :=
    (hl_other3 _ (by decide)).trans hl_code2
  have hgw3 := hW3.1.2.2.2.2.2.2.2.2.2
  obtain ⟨wvsa3, hwvsa3⟩ := hgw3 "vm_system_address" (by decide)
  obtain ⟨mem4, _, _, _, hfb4, hW4, _, hnt4, hfr4, heq4⟩ :=
    seq_store_freshBlock_step hW0 hfb3 hl_te3 (by decide)
      (fun v hv => by
        unfold GlobalWord at hwvsa3
        simp only [evalHOLExact, hwvsa3, Option.some.injEq] at hv
        subst hv; simp [flattenHOL]) hnt3 hfr3
  have hat4 := sysTxAtProg_eq hat3 hnt4 hfr4 heq4
  obtain ⟨mem5, _, _, _, hfb5, hW5, _, hnt5, hfr5, heq5⟩ :=
    seq_store_freshBlock_step hW0 hfb4 hl_te3 (by decide)
      (fun v hv => by
        simp only [evalHOLExact, hl_t3, Option.some.injEq] at hv
        subst hv; simp [flattenHOL]) hnt4 hfr4
  have hat5 := sysTxAtProg_eq hat4 hnt5 hfr5 heq5
  obtain ⟨mem6, _, _, _, hfb6, hW6, _, hnt6, hfr6, heq6⟩ :=
    seq_store_freshBlock_step hW0 hfb5 hl_te3 (by decide)
      (fun v hv => by
        rw [evalHOLExact_load_comb4_len hv]; omega) hnt5 hfr5
  have hat6 := sysTxAtProg_eq hat5 hnt6 hfr6 heq6
  obtain ⟨mem7, _, _, _, hfb7, hW7, _, hnt7, hfr7, heq7⟩ :=
    seq_store_freshBlock_step hW0 hfb6 hl_te3 (by decide)
      (fun v hv => by
        have := evalHOLExact_const_len_le_one hv; omega) hnt6 hfr6
  have hat7 := sysTxAtProg_eq hat6 hnt7 hfr7 heq7
  obtain ⟨mem8, _, _, _, hfb8, hW8, _, hnt8, hfr8, heq8⟩ :=
    seq_store_freshBlock_step hW0 hfb7 hl_te3 (by decide)
      (fun v hv => by
        have := evalHOLExact_panop_mul_const_len_le_one hv; omega) hnt7 hfr7
  have hat8 := sysTxAtProg_eq hat7 hnt8 hfr8 heq8
  set s8 := { s3 with memory := mem8 }
  have hp8 : SysTxPrefixStep s0 none s8 := hfb8.1
  have hc8 : s8.code = originalRuntimeCode := hc3
  rcases decCall_msg_new_freshStep s8 (ofString "m") _ hc8 hW8 hnt8 hfr8 with
    ⟨hstep_ex, e, ev, hev⟩ | ⟨w_m, s9, hfb9_8, hW9, hc9, hl_m9, hl_other9, _, hnt9, hfr9, hr9, hs9⟩
  · exact sysTxPrefixOutcome_ex hat8 ⟨sysTxPrefixStep_trans hW0.1 hp8 hstep_ex, e, ev, hev⟩
  have hat9 := sysTxAtProg_resVar hat8 hnt9 hfr9 hr9 hs9
  have hfb9 : SysTxFreshBlockStep s0 none s9 w_m 176 := sysTxFreshBlockStep_prepend hW0 hp8 hfb9_8
  have hmt9 : SysTxMsgTablesStep s0 s9 w_m [] := sysTxMsgTablesStep_of_freshBlock hfb9
  have hl_te9 : s9.locals.lookup (ofString "te") = some (.val (.word w_te)) :=
    (hl_other9 _ (by decide)).trans hl_te3
  have hl_t9 : s9.locals.lookup (ofString "target") = some (.val (.word wt)) :=
    (hl_other9 _ (by decide)).trans hl_t3
  have hl_d9 : s9.locals.lookup (ofString "data") = some (.val (.word wd)) :=
    (hl_other9 _ (by decide)).trans hl_d3
  have hl_dn9 : s9.locals.lookup (ofString "data_n") = some (.val (.word wdn)) :=
    (hl_other9 _ (by decide)).trans hl_dn3
  have hl_code9 : s9.locals.lookup (ofString "code") = some vcode :=
    (hl_other9 _ (by decide)).trans hl_code3
  have hcode_pair : ∃ c0 c1 : BitVec 64, vcode = .rStruct [.val (.word c0), .val (.word c1)] := by
    cases vcode with
    | val _ => simp [shapeOfHOLExact] at hcode_sh
    | nStruct _ _ => simp [shapeOfHOLExact] at hcode_sh
    | rStruct vs =>
      simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hcode_sh
      rcases vs with _ | ⟨u0, _ | ⟨u1, _ | _⟩⟩ <;> simp at hcode_sh
      rcases u0 with ⟨⟨c0⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact] at hcode_sh
      rcases u1 with ⟨⟨c1⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact] at hcode_sh
      exact ⟨c0, c1, rfl⟩
  obtain ⟨wc0, wc1, rfl⟩ := hcode_pair
  exact prefix_unchecked_sysTx_after_msg_new hW0 hat9 hmt9 hW9 hc9 hl_m9 hl_te9 hl_t9 hl_d9 hl_dn9 hl_code9

theorem lookup_frame_mem_release_sysTx :
    originalRuntimeCode.lookup (ofString "frame_mem_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_frame_mem_release, .one) :=
  lookup_of_guestAst_getElem 12 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_mem_release) rfl

theorem lookup_scratch_release_sysTx :
    originalRuntimeCode.lookup (ofString "scratch_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_scratch_release, .one) :=
  lookup_of_guestAst_getElem 15 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_release) rfl

theorem scratch_release_call_exact_sysTx {F : Type}
    (st : PanSemStateFiniteExact 64 F) (mExp : ExpHOL 64) (mw : BitVec 64)
    (hcode : st.code = originalRuntimeCode)
    (hA : ArenaReady st)
    (hm : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hnt : (evaluateHOLFiniteState st (.call (some (none, none)) (ofString "scratch_release") [mExp])).1 ≠
      some .timeOut) :
    ∃ ck, evaluateHOLFiniteState st (.call (some (none, none)) (ofString "scratch_release") [mExp]) =
      (none, { st with
        globals := st.globals.update (ofString "scratch_ptr", .val (.word mw))
        clock := ck }) := by
  obtain ⟨spw, hsp⟩ := hA.2.2.2.2.2.2.2.2.2 "scratch_ptr" (by decide)
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [mExp] =
      some [.val (.word mw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hm]
  have hl := pan_one_word_lookup st.code.lookup (ofString "scratch_release") (ofString "m")
    (sourceFnBody Guest.Software.guestFn_scratch_release) mw
    (by rw [hcode]; exact lookup_scratch_release_sysTx)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢; rw [hl] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hz : st.clock = 0
  · simp [hz] at hnt
  · rw [if_neg hz]
    let entry := callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw)))
    have hb : sourceFnBody Guest.Software.guestFn_scratch_release =
        .seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := rfl
    have hev_b : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_scratch_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mw)) entry)) := by
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
      have hm_ent : entry.locals.lookup (ofString "m") = some (.val (.word mw)) := by
        simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsp_ent : entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word spw)) := hsp
      simp [evalHOLExact, hm_ent, isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact,
        hsp_ent, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
        evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
    have hev_b' : evaluateHOLFiniteState
        (callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw))))
        (sourceFnBody Guest.Software.guestFn_scratch_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mw)) entry)) := hev_b
    rw [hev_b']; dsimp only
    have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh]
    exact ⟨st.clock - 1, rfl⟩

theorem frame_mem_release_call_exact_sysTx {F : Type}
    (st : PanSemStateFiniteExact 64 F) (mExp : ExpHOL 64) (mw : BitVec 64)
    (hcode : st.code = originalRuntimeCode)
    (hA : ArenaReady st)
    (hm : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hnt : (evaluateHOLFiniteState st (.call (some (none, none)) (ofString "frame_mem_release") [mExp])).1 ≠
      some .timeOut) :
    ∃ ck, evaluateHOLFiniteState st (.call (some (none, none)) (ofString "frame_mem_release") [mExp]) =
      (none, { st with
        globals := st.globals.update (ofString "frame_mem_ptr", .val (.word mw))
        clock := ck }) := by
  obtain ⟨fpw, hfp⟩ := hA.2.2.2.2.2.2.2.2.2 "frame_mem_ptr" (by decide)
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [mExp] =
      some [.val (.word mw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hm]
  have hl := pan_one_word_lookup st.code.lookup (ofString "frame_mem_release") (ofString "m")
    (sourceFnBody Guest.Software.guestFn_frame_mem_release) mw
    (by rw [hcode]; exact lookup_frame_mem_release_sysTx)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢; rw [hl] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hz : st.clock = 0
  · simp [hz] at hnt
  · rw [if_neg hz]
    let entry := callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw)))
    have hb : sourceFnBody Guest.Software.guestFn_frame_mem_release =
        .seq (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := rfl
    have hev_b : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_frame_mem_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word mw)) entry)) := by
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
      have hm_ent : entry.locals.lookup (ofString "m") = some (.val (.word mw)) := by
        simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hfp_ent : entry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fpw)) := hfp
      simp [evalHOLExact, hm_ent, isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact,
        hfp_ent, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
        evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
    have hev_b' : evaluateHOLFiniteState
        (callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw))))
        (sourceFnBody Guest.Software.guestFn_frame_mem_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word mw)) entry)) := hev_b
    rw [hev_b']; dsimp only
    have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh]
    exact ⟨st.clock - 1, rfl⟩

theorem worldOwned_zero_base_sysTx {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hWT : WorldTypedWith s S Nd) {j : Ivl} (hj : j ∈ worldOwned s S Nd) (hj0 : j.2 = 0) :
    j = (0, 0) := by
  obtain ⟨hT, _, _, hTr⟩ := hWT
  have hlst : ∀ (l esz : Nat), (esz = 8 ∨ esz = 16 ∨ esz = 24 ∨ esz = 40) →
      (l ≠ 0 → LstOK s l) → ∀ x ∈ lstObjects s l esz, x.2 = 0 → x = (0, 0) := by
    intro l esz hesz hlok x hx hx0
    unfold lstObjects at hx
    by_cases hl0 : l = 0
    · rw [if_pos hl0] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
      exact hx
    · rw [if_neg hl0] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h1 | h2
      · subst h1; simp at hx0
      · subst h2
        have hcap : 1 ≤ memW s (l + 16) := (hlok hl0).1
        have hesz_pos : 0 < esz := by rcases hesz with rfl | rfl | rfl | rfl <;> decide
        have hpos : 0 < esz * memW s (l + 16) := Nat.mul_pos hesz_pos (by omega)
        dsimp only at hx0; omega
  have hobj : ∀ p len : Nat,
      (if globN s "bo" = 0 ∨ p = 0 ∨ len = 0 then ((0, 0) : Ivl) else (p, len)).2 = 0 →
      (if globN s "bo" = 0 ∨ p = 0 ∨ len = 0 then ((0, 0) : Ivl) else (p, len)) = (0, 0) := by
    intro p len hx0
    by_cases hc : globN s "bo" = 0 ∨ p = 0 ∨ len = 0
    · rw [if_pos hc]
    · rw [if_neg hc] at hx0; dsimp only at hx0; exfalso; exact hc (Or.inr (Or.inr hx0))
  unfold worldOwned at hj
  rcases List.mem_append.1 hj with h12 | hnd
  · rcases List.mem_append.1 h12 with htab | hfix
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 htab
      have hwf : HtabWF s t := (hT.2.1 t ht).1
      have hstr_pos : 0 < hdr s t 1 := by
        have hk1 : 1 ≤ hdr s t 0 := hwf.2.2.1
        have hstr : hdr s t 1 = (hdr s t 0 + 7) / 8 * 8 := hwf.2.2.2.2.1
        omega
      simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at hfp
      rcases hfp with h1 | (h2 | (h3 | h4))
      · subst h1; dsimp only at hj0; omega
      · subst h2; dsimp only at hj0
        exact False.elim (Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos (hdr s t 10)) hstr_pos) hj0)
      · subst h3; dsimp only at hj0
        exact False.elim (Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos (hdr s t 10)) (by decide)) hj0)
      · subst h4; dsimp only at hj0
        exact False.elim (Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos (hdr s t 10)) (by decide)) hj0)
    · unfold fixedObjects at hfix
      simp only [List.mem_append] at hfix
      rcases hfix with ((hgb | hjr) | hbo) | hbal
      · obtain ⟨gn, hgn, hgn_eq⟩ := List.mem_map.1 hgb
        subst hgn_eq
        dsimp only at hj0
        by_cases hgz : globN s gn.1 = 0
        · simp [hgz]
        · rw [if_neg hgz] at hj0
          have hpos : ∀ p ∈ globalBuffers, 0 < p.2 := by decide
          have := hpos gn hgn
          omega
      · simp only [List.mem_singleton] at hjr
        subst hjr
        dsimp only at hj0
        have hcz : globN s "journal_cap" = 0 := by omega
        simp [hcz]
      · unfold blockOutObjects at hbo
        dsimp only at hbo
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hbo
        rcases hbo with ((h24 | h32 | h56) | hl40) | hl72
        · subst h24; exact hobj _ _ hj0
        · subst h32; exact hobj _ _ hj0
        · subst h56; exact hobj _ _ hj0
        · by_cases hc : globN s "bo" = 0 ∨ memW s (globN s "bo" + 40) = 0
          · rw [if_pos hc] at hl40
            simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl40
            exact hl40
          · rw [if_neg hc] at hl40
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl40
            rcases hl40 with h1 | h2 <;> (subst j; exact hobj _ _ hj0)
        · by_cases hc : globN s "bo" = 0 ∨ memW s (globN s "bo" + 72) = 0
          · rw [if_pos hc] at hl72
            simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hl72
            exact hl72
          · rw [if_neg hc] at hl72
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl72
            rcases hl72 with h1 | h2 <;> (subst j; exact hobj _ _ hj0)
      · unfold balObjects at hbal
        obtain ⟨ad, had, had_mem⟩ := List.mem_flatMap.1 hbal
        have hbal_t := hT.2.2.2.2.2.2.2.2.2.1 ad had
        simp only [List.cons_append, List.mem_cons, List.mem_append] at had_mem
        rcases had_mem with h0 | (((hl16 | hl24) | hl32) | hstor)
        · subst h0; dsimp only at hj0; omega
        · exact hlst (memW s (ad + 16)) 40 (by decide)
            (fun _ => hbal_t.2.2.1 16 (by simp)) j hl16 hj0
        · exact hlst (memW s (ad + 24)) 16 (by decide)
            (fun _ => hbal_t.2.2.1 24 (by simp)) j hl24 hj0
        · exact hlst (memW s (ad + 32)) 24 (by decide)
            (fun _ => hbal_t.2.2.1 32 (by simp)) j hl32 hj0
        · obtain ⟨l, hl_mem, hj_l⟩ := List.mem_flatMap.1 hstor
          exact hlst l 40 (by decide) (fun _ => hbal_t.2.2.2 l hl_mem) j hj_l hj0
  · unfold nodeExtents at hnd
    obtain ⟨n, _, hni⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
    rcases hni with h1 | h2
    · subst h1
      unfold nodeIvl nodeSize at hj0
      dsimp only at hj0
      split_ifs at hj0 <;> omega
    · subst h2
      unfold nodePath at hj0 ⊢
      split_ifs at hj0 ⊢ with hp
      · exfalso; exact hp.2 hj0
      · rfl

theorem worldTypedWith_release_marks_sysTx {F : Type}
    {s_pmc s_cur : PanSemStateFiniteExact 64 F}
    {S_pmc Nd_pmc S_cur Nd_cur : List Nat}
    {w_mark w_fmark : BitVec 64} {ck : Nat}
    (hA_pmc : ArenaReady s_pmc)
    (hA_cur : ArenaReady s_cur)
    (hWT_pmc : WorldTypedWith s_pmc S_pmc Nd_pmc)
    (hWT_cur : WorldTypedWith s_cur S_cur Nd_cur)
    (hOG : OwnedGrows s_pmc s_cur (worldOwned s_pmc S_pmc Nd_pmc) (worldOwned s_cur S_cur Nd_cur))
    (hhp_le : globN s_pmc "heap_ptr" ≤ globN s_cur "heap_ptr")
    (hmark_eq : w_mark.toNat = globN s_pmc "scratch_ptr")
    (hfmark_eq : w_fmark.toNat = globN s_pmc "frame_mem_ptr") :
    let s_rel : PanSemStateFiniteExact 64 F :=
      { s_cur with
        globals := (s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))).update
          (ofString "frame_mem_ptr", .val (.word w_fmark))
        clock := ck }
    ArenaReady s_rel ∧
      WorldTypedWith s_rel S_cur Nd_cur ∧
      worldOwned s_rel S_cur Nd_cur = worldOwned s_cur S_cur Nd_cur := by
  intro s_rel
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT_cur
  have hgi_rel : GuestInv s_rel := guestInv_congr (s := s_cur) rfl rfl rfl rfl hA_cur.1
  have hgw1 : GlobalsWord { s_cur with globals := s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark)) } :=
    globalsWord_update (ofString "scratch_ptr") w_mark rfl hA_cur.2.2.2.2.2.2.2.2.2
  have hgw_rel : GlobalsWord s_rel :=
    globalsWord_update (ofString "frame_mem_ptr") w_fmark rfl hgw1
  have hg_ne : ∀ name : String,
      ofString name ≠ ofString "frame_mem_ptr" →
      ofString name ≠ ofString "scratch_ptr" →
      globN s_rel name = globN s_cur name := by
    intro name hne1 hne2
    simp [s_rel, globN, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne1, Ne.symm hne2]
  have hhp_rel : globN s_rel "heap_ptr" = globN s_cur "heap_ptr" :=
    hg_ne "heap_ptr" (by decide) (by decide)
  have hfmp_rel : globN s_rel "frame_mem_ptr" = globN s_pmc "frame_mem_ptr" := by
    simp [s_rel, globN, HolFiniteMapExact.lookup_update, FUPDATE, hfmark_eq]
  have hsp_rel : globN s_rel "scratch_ptr" = globN s_pmc "scratch_ptr" := by
    have hne : ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" := by decide
    simp [s_rel, globN, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne, hmark_eq]
  have hA_rel : ArenaReady s_rel := by
    refine ⟨hgi_rel, ?_⟩
    unfold ArenaOK
    rw [hhp_rel, hfmp_rel, hsp_rel]
    exact ⟨hA_cur.2.1, hA_cur.2.2.1, hA_pmc.2.2.2.1, hA_pmc.2.2.2.2.1, hA_pmc.2.2.2.2.2.1,
      hA_cur.2.2.2.2.2.2.1, hA_pmc.2.2.2.2.2.2.2.1, hA_pmc.2.2.2.2.2.2.2.2.1, hgw_rel⟩
  have hmemW : memW s_rel = memW s_cur := rfl
  have hhdr : hdr s_rel = hdr s_cur := rfl
  have hnodeF : nodeF s_rel = nodeF s_cur := rfl
  have hfp : htabFootprint s_rel = htabFootprint s_cur := rfl
  have hhWF : ∀ t, HtabWF s_cur t → HtabWF s_rel t := fun t h =>
    InitECandidate.Solver.Wave8Contracts.M08.htabWF_congr_unhit hA_cur.1 hA_rel.1 h (fun _ _ _ _ _ _ => rfl)
  have hlstOK : ∀ l, LstOK s_rel l ↔ LstOK s_cur l := fun _ => Iff.rfl
  have hhVals : htabValues s_rel = htabValues s_cur := rfl
  have hwordsOK : ∀ i, WordsOK s_rel i ↔ WordsOK s_cur i := fun _ => Iff.rfl
  have hba_eq : globN s_rel "bal_accounts" = globN s_cur "bal_accounts" := hg_ne "bal_accounts" (by decide) (by decide)
  have hbia_eq : globN s_rel "bal_idx_accts" = globN s_cur "bal_idx_accts" := hg_ne "bal_idx_accts" (by decide) (by decide)
  have hbis_eq : globN s_rel "bal_idx_stor" = globN s_cur "bal_idx_stor" := hg_ne "bal_idx_stor" (by decide) (by decide)
  have hbo_eq : globN s_rel "bo" = globN s_cur "bo" := hg_ne "bo" (by decide) (by decide)
  have hws_eq : globN s_rel "ws" = globN s_cur "ws" := hg_ne "ws" (by decide) (by decide)
  have hbs_eq : globN s_rel "bs" = globN s_cur "bs" := hg_ne "bs" (by decide) (by decide)
  have hts_eq : globN s_rel "ts" = globN s_cur "ts" := hg_ne "ts" (by decide) (by decide)
  have hjc_eq : globN s_rel "journal_cap" = globN s_cur "journal_cap" := hg_ne "journal_cap" (by decide) (by decide)
  have hjr_eq : globN s_rel "journal" = globN s_cur "journal" := hg_ne "journal" (by decide) (by decide)
  have hjn_eq : globN s_rel "journal_n" = globN s_cur "journal_n" := hg_ne "journal_n" (by decide) (by decide)
  have hbalRecs : balRecords s_rel = balRecords s_cur := by
    simp only [balRecords, hba_eq, hhdr, hnodeF, hmemW]
  have hbalObjs : balObjects s_rel = balObjects s_cur := by
    simp only [balObjects, hbalRecs, lstObjects, hhVals, hmemW]
  have hboObjs : blockOutObjects s_rel = blockOutObjects s_cur := by
    simp only [blockOutObjects, hbo_eq, hmemW]
  have hgb_ne1 : ∀ gn ∈ globalBuffers, ofString gn.1 ≠ ofString "frame_mem_ptr" := by decide
  have hgb_ne2 : ∀ gn ∈ globalBuffers, ofString gn.1 ≠ ofString "scratch_ptr" := by decide
  have hgb_map :
      (globalBuffers.map fun gn => (globN s_rel gn.1, if globN s_rel gn.1 = 0 then 0 else gn.2)) =
      (globalBuffers.map fun gn => (globN s_cur gn.1, if globN s_cur gn.1 = 0 then 0 else gn.2)) := by
    apply List.map_congr_left
    intro gn hgn
    rw [hg_ne gn.1 (hgb_ne1 gn hgn) (hgb_ne2 gn hgn)]
  have hfixObjs : fixedObjects s_rel = fixedObjects s_cur := by
    simp only [fixedObjects, hgb_map, hjc_eq, hjr_eq, hboObjs, hbalObjs]
  have hnodeExt : nodeExtents s_rel Nd_cur = nodeExtents s_cur Nd_cur := rfl
  have hwo_eq : worldOwned s_rel S_cur Nd_cur = worldOwned s_cur S_cur Nd_cur := by
    simp only [worldOwned, hfp, hfixObjs, hnodeExt]
  have hss_pos : 0 < scratchStart := by decide
  have halloc_owned : ∀ i ∈ worldOwned s_cur S_cur Nd_cur, Allocated s_cur i → Allocated s_rel i := by
    intro i hi hal_cur
    rcases hOG i hi with rfl | ⟨j, hj, hin_ij⟩ | hin_fresh
    · rcases hal_cur with h_hp | h_sp
      · exact Or.inl ⟨h_hp.1, by rw [hhp_rel]; exact h_hp.2⟩
      · exfalso
        have : scratchStart ≤ 0 := le_trans (le_trans hA_cur.2.2.2.1 hA_cur.2.2.2.2.1) h_sp.1
        omega
    · rcases InitECandidate.Solver.Wave8Contracts.M08.worldOwned_allocated hWT_pmc hj with hj0 | hal_j
      · have hj_zero : j = (0, 0) := worldOwned_zero_base_sysTx hWT_pmc hj hj0
        subst hj_zero
        have hi_zero : i = (0, 0) := by
          rcases i with ⟨i1, i2⟩
          dsimp only [Inside] at hin_ij
          exact Prod.ext (by omega) (by omega)
        subst hi_zero
        rcases hal_cur with h_hp | h_sp
        · exact Or.inl ⟨h_hp.1, by rw [hhp_rel]; exact h_hp.2⟩
        · exfalso
          have : scratchStart ≤ 0 := le_trans (le_trans hA_cur.2.2.2.1 hA_cur.2.2.2.2.1) h_sp.1
          omega
      · rcases hal_j with hj_hp | hj_sp
        · exact Or.inl ⟨le_trans hj_hp.1 hin_ij.1,
            by rw [hhp_rel]; exact le_trans hin_ij.2 (le_trans hj_hp.2 hhp_le)⟩
        · exact Or.inr ⟨by rw [hsp_rel]; exact le_trans hj_sp.1 hin_ij.1,
            le_trans hin_ij.2 hj_sp.2⟩
    · exact Or.inl ⟨le_trans hA_pmc.2.1 hin_fresh.1,
        by rw [hhp_rel]; exact hin_fresh.2⟩
  have hrecR_ws : ∀ ks, recRoles s_rel "ws" ks = recRoles s_cur "ws" ks := fun _ => by
    simp only [recRoles, hws_eq, hmemW]
  have hrecR_bs : ∀ ks, recRoles s_rel "bs" ks = recRoles s_cur "bs" ks := fun _ => by
    simp only [recRoles, hbs_eq, hmemW]
  have hrecR_ts : ∀ ks, recRoles s_rel "ts" ks = recRoles s_cur "ts" ks := fun _ => by
    simp only [recRoles, hts_eq, hmemW]
  have hnest_bs : nestRoles s_rel "bs" "bs.inner" = nestRoles s_cur "bs" "bs.inner" := by
    simp only [nestRoles, hbs_eq, hmemW, hhVals]
  have hnest_ts : nestRoles s_rel "ts" "ts.inner" = nestRoles s_cur "ts" "ts.inner" := by
    simp only [nestRoles, hts_eq, hmemW, hhVals]
  have hwrs : worldRoleSlots s_rel = worldRoleSlots s_cur := by
    simp only [worldRoleSlots, hrecR_ws, hrecR_bs, hrecR_ts, hba_eq, hbia_eq, hbis_eq,
      hnest_bs, hnest_ts, hbalRecs, hmemW]
  have hjRole : journalRole s_rel = journalRole s_cur := by
    funext t
    simp only [journalRole, hts_eq, hmemW]
  have hjrs : journalRoleSlots s_rel = journalRoleSlots s_cur := by
    simp only [journalRoleSlots, hjn_eq, hjr_eq, hjRole, hmemW]
  refine ⟨hA_rel, ⟨?_, ?_, ?_, ?_⟩, hwo_eq⟩
  · obtain ⟨hnd, htf, htp, hws_s, hbs_s, hts_s, hgt_s, hb_in, ht_in, hbal_t, hbo_t, hrol⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      refine ⟨hhWF t (htf t ht).1, fun i hi => ?_⟩
      rw [hfp] at hi
      rw [hfixObjs]
      have hwo_i : i ∈ worldOwned s_cur S_cur Nd_cur :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hi⟩))
      exact ⟨halloc_owned i hwo_i ((htf t ht).2 i hi).1, ((htf t ht).2 i hi).2⟩
    · simpa only [hfp] using htp
    · simpa only [hws_eq, hmemW] using hws_s
    · simpa only [hbs_eq, hmemW] using hbs_s
    · simpa only [hts_eq, hmemW] using hts_s
    · intro g hg
      have hg_ne1 : ofString g ≠ ofString "frame_mem_ptr" := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide
      have hg_ne2 : ofString g ≠ ofString "scratch_ptr" := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide
      rw [hg_ne g hg_ne1 hg_ne2]
      exact hgt_s g hg
    · simpa only [hbs_eq, hmemW, HtabValuesIn, hhdr, hnodeF] using hb_in
    · simpa only [hts_eq, hmemW, HtabValuesIn, hhdr, hnodeF] using ht_in
    · simpa only [hbalRecs, hmemW, hlstOK, hhVals] using hbal_t
    · simpa only [hbo_eq, hmemW, hlstOK] using hbo_t
    · simpa only [hwrs, hjrs, RolesOK, hhdr] using hrol
  · refine ⟨by rw [hjn_eq, hjc_eq]; exact hJ.1,
      by rw [hjc_eq]; exact hJ.2.1, ?_, ?_⟩
    · rw [hjc_eq, hjr_eq]
      rcases hJ.2.2.1 with h0 | ⟨ha, hw⟩
      · exact Or.inl h0
      · by_cases hcz : globN s_cur "journal_cap" = 0
        · exact Or.inl hcz
        · have hwo_j : (globN s_cur "journal", 32 * globN s_cur "journal_cap") ∈
              worldOwned s_cur S_cur Nd_cur := by
            apply List.mem_append_left; apply List.mem_append_right
            unfold fixedObjects
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
            simp [hcz]
          exact Or.inr ⟨halloc_owned _ hwo_j ha, (hwordsOK _).2 hw⟩
    · intro i hi
      rw [hjn_eq] at hi
      rw [hjr_eq, hmemW]
      exact hJ.2.2.2 i hi
  · unfold FixedTyped; rw [hfixObjs]
    refine ⟨fun i hi => ?_, hF.2⟩
    have hwo_i : i ∈ worldOwned s_cur S_cur Nd_cur :=
      List.mem_append_left _ (List.mem_append_right _ hi)
    exact (hF.1 i hi).elim Or.inl (fun h => Or.inr ⟨halloc_owned i hwo_i h.1, (hwordsOK i).2 h.2⟩)
  · unfold TriesTypedWith
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨fun n hn => ?_, by simpa only [nodeIvl, hmemW] using hTr.1.2⟩
      obtain ⟨hk, hal_n, hin_n, hw_n, hext, hbr, hkey, h16, h56, h168⟩ := hTr.1.1 n hn
      have hwo_n : nodeIvl s_cur n ∈ worldOwned s_cur S_cur Nd_cur := by
        apply List.mem_append_right
        exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
      refine ⟨hk, halloc_owned _ hwo_n hal_n, hin_n, hw_n, hext, hbr, ?_, h16, h56, h168⟩
      intro h12
      rcases hkey h12 with hlen0 | ⟨hnib, hal_k, hin_k, hdisj_k⟩
      · exact Or.inl hlen0
      · by_cases hlen_z : memW s_cur (n + 40) = 0
        · exact Or.inl hlen_z
        · have hwo_k : (memW s_cur (n + 32), memW s_cur (n + 40)) ∈ worldOwned s_cur S_cur Nd_cur := by
            apply List.mem_append_right
            have hnp : nodePath s_cur n = (memW s_cur (n + 32), memW s_cur (n + 40)) := by
              unfold nodePath; rw [if_pos ⟨h12, hlen_z⟩]
            exact List.mem_flatMap.2 ⟨n, hn, List.mem_cons_of_mem _ (List.mem_singleton.2 hnp.symm)⟩
          exact Or.inr ⟨hnib, halloc_owned _ hwo_k hal_k, hin_k, hdisj_k⟩
    · rw [hnodeExt, hfixObjs]; simpa only [hfp] using hTr.2.1
    · simpa only [hws_eq, hmemW, hfp, hhdr, hnodeF] using hTr.2.2

theorem evalHOLExact_load_word_in_block_sysTx {F : Type}
    {s : PanSemStateFiniteExact 64 F} {w_out : BitVec 64} {off : Nat}
    (hA : ArenaOK s)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hw_out : WordsOK s (w_out.toNat, 96))
    (hin_out : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr"))
    (hoff8 : off % 8 = 0)
    (hoff_le : off + 8 ≤ 96) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW s (w_out.toNat + off))))) := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp : globN s "heap_ptr" ≤ heapLimit := hA.2.1
  have hin_bound : w_out.toNat + 96 ≤ 2 ^ 64 := by
    unfold Inside at hin_out; omega
  have hoff_lt : off < 2 ^ 64 := by omega
  have hsum_lt : w_out.toNat + off < 2 ^ 64 := by omega
  have haddr_nat : (w_out + BitVec.ofNat 64 off).toNat = w_out.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt, Nat.mod_eq_of_lt hsum_lt]
  have hk_lt : off / 8 < 96 / 8 := by omega
  have hk_eq : w_out.toNat + 8 * (off / 8) = w_out.toNat + off := by omega
  obtain ⟨wc, hdom, hm_eq⟩ := hw_out.2.2 (off / 8) hk_lt
  rw [hk_eq] at hdom hm_eq
  have haddr_eq : BitVec.ofNat 64 (w_out.toNat + off) = w_out + BitVec.ofNat 64 off := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum_lt, haddr_nat]
  rw [haddr_eq] at hdom hm_eq
  have hmw : BitVec.ofNat 64 (memW s (w_out.toNat + off)) = wc := by
    unfold memW
    rw [haddr_eq, hm_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hmw]
  simp [evalHOLExact, evalListHOLExact, hl_out, valueIsWord, valueWord,
    wordOpHOL, wordOp, isWfShapeExactHOL, memLoadHOLExact, hdom, hm_eq]

@[irreducible] def sysTxCopyRetBodyProg : ProgHOL 64 :=
  .decCall (ofString "system_ret") .one (ofString "alloc")
    [.op .add [.var .local (ofString "system_ret_n"), .const (BitVec.ofNat 64 8)]]
    (.seq
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "system_ret"),
         .load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 40)]),
         .var .local (ofString "system_ret_n")])
      (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 40)])
        (.var .local (ofString "system_ret"))))

@[irreducible] def sysTxCopyRetSeqProg : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "system_ret"),
       .load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 40)]),
       .var .local (ofString "system_ret_n")])
    (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 40)])
      (.var .local (ofString "system_ret")))

private def noReturnOrRaise_sysTx : ProgHOL 64 → Bool
  | .seq a b => noReturnOrRaise_sysTx a && noReturnOrRaise_sysTx b
  | .ite _ a b => noReturnOrRaise_sysTx a && noReturnOrRaise_sysTx b
  | .while _ a => noReturnOrRaise_sysTx a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem not_resumes_error_sysTx :
    ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

private theorem evaluate_noReturnOrRaise_sysTx {F : Type}
    (p : ProgHOL 64) (hp : noReturnOrRaise_sysTx p = true)
    (s : PanSemStateFiniteExact 64 F) :
    ¬ Resumes (evaluateHOLFiniteState s p).1 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturnOrRaise_sysTx] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact not_resumes_error_sysTx
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error_sysTx
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error_sysTx
      · exact not_resumes_error_sysTx
    · exact not_resumes_error_sysTx
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error_sysTx
      · exact not_resumes_error_sysTx
    · exact not_resumes_error_sysTx
  | seq a b =>
    have hab : noReturnOrRaise_sysTx a = true ∧ noReturnOrRaise_sysTx b = true := by
      simpa [shape, noReturnOrRaise_sysTx, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnOrRaise_sysTx a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      exact evaluate_noReturnOrRaise_sysTx b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturnOrRaise_sysTx a = true ∧ noReturnOrRaise_sysTx b = true := by
      simpa [shape, noReturnOrRaise_sysTx, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnOrRaise_sysTx b hab.2 s
      · exact evaluate_noReturnOrRaise_sysTx a hab.1 s
    · exact not_resumes_error_sysTx
  | «while» cond body =>
    have hb : noReturnOrRaise_sysTx body = true := by simpa [shape, noReturnOrRaise_sysTx] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturnOrRaise_sysTx body hb (decClockHOLFinite s)
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem
            omega
          cases r1 with
          | none =>
            exact evaluate_noReturnOrRaise_sysTx (.while cond body)
              (by simpa [noReturnOrRaise_sysTx] using hb) mid
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noReturnOrRaise_sysTx (.while cond body)
                (by simpa [noReturnOrRaise_sysTx] using hb) mid
            | «break» => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | returned _ => exact ih1
            | exception _ _ => exact ih1
            | timeOut => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | error => exact not_resumes_error_sysTx
            | finalFfi _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
    · exact not_resumes_error_sysTx
  | _ => simp [shape, noReturnOrRaise_sysTx] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

theorem memcpy_body_resumes_returned_sysTx {F : Type}
    (ent : PanSemStateFiniteExact 64 F)
    (hres : Resumes (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_memcpy)).1) :
    ∃ v, (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_memcpy)).1 =
      some (.returned v) := by
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · intro h; exact absurd h not_resumes_error_sysTx
  · split
    · set s1 := setVarHOLFinite (ofString "i") _ ent
      rw [evaluateHOLFiniteState_seq_line780]
      set iteProg : ProgHOL 64 := .ite _ _ .skip
      have hite_nrr : noReturnOrRaise_sysTx iteProg = true := rfl
      rcases hite_run : evaluateHOLFiniteState s1 iteProg with ⟨r_ite, s2⟩
      cases r_ite with
      | some _ =>
        intro hres
        exact absurd hres (by simpa [hite_run] using evaluate_noReturnOrRaise_sysTx iteProg hite_nrr s1)
      | none =>
        dsimp only
        rw [evaluateHOLFiniteState_seq_line780]
        set loop3 : ProgHOL 64 := .while _ _
        have hl3_nrr : noReturnOrRaise_sysTx loop3 = true := rfl
        rcases hw3 : evaluateHOLFiniteState s2 loop3 with ⟨rw3, s3⟩
        cases rw3 with
        | some _ =>
          intro hres
          exact absurd hres (by simpa [hw3] using evaluate_noReturnOrRaise_sysTx loop3 hl3_nrr s2)
        | none =>
          dsimp only
          rw [evaluateHOLFiniteState_seq_line780]
          set loop4 : ProgHOL 64 := .while _ _
          have hl4_nrr : noReturnOrRaise_sysTx loop4 = true := rfl
          rcases hw4 : evaluateHOLFiniteState s3 loop4 with ⟨rw4, s4⟩
          cases rw4 with
          | some _ =>
            intro hres
            exact absurd hres (by simpa [hw4] using evaluate_noReturnOrRaise_sysTx loop4 hl4_nrr s3)
          | none =>
            dsimp only
            intro _
            exact ⟨.val (.word 0#64), by
              simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
                sizeOfShapeWithContextHOL]⟩
    · intro h; exact absurd h not_resumes_error_sysTx

abbrev pmcSysTxBufs : BufList :=
  [("b2_v", 128), ("bn_expw", 352), ("bn_gamma", 384),
   ("evm_key_buf", 32), ("keccak_pad", 136), ("keccak_st", 200),
   ("mpt_nib_scratch", 64), ("pre_hdr_buf", 96), ("rmd_h", 40),
   ("rmd_pad", 128), ("rmd_x", 128), ("sha_pad", 128), ("sha_st", 64),
   ("sk_buf", 52), ("u256_ws", 640)]

abbrev pmcSysTxGlobals : List String :=
  ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr",
   "journal_n", "scratch_ptr"]

abbrev pmcSysTxKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
   ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
   ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]

abbrev incSysTxBufs : BufList :=
  [("bal_key_buf", 64), ("keccak_pad", 136), ("keccak_st", 200),
   ("mpt_nib_scratch", 64), ("sk_buf", 52)]

abbrev incSysTxGlobals : List String :=
  ["heap_ptr", "scratch_ptr"]

theorem validBufList_pmcSysTxBufs : ValidBufList pmcSysTxBufs := by
  intro p hp
  have hm : p ∈ sysTxBufs := by
    simp only [pmcSysTxBufs, sysTxBufs, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact validBufList_sysTxBufs p hm

def RetSysTxPmc : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd =>
    RetMessageOutput s r post S Nd ∧
    globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    ∀ v, r = some (.returned v) → ∃ w : BitVec 64,
      v = .val (.word w) ∧
      Inside (w.toNat, 96) (globN s "heap_ptr") (globN post "heap_ptr") ∧
      (memW post (w.toNat + 80) ≠ 0 →
        memW post (w.toNat + 80) = globN s "scratch_ptr" ∧
        memW post (w.toNat + 88) = globN s "frame_mem_ptr" ∧
        memW post (w.toNat + 48) ≤ scratchEnd)

def SysTxPostPmcStepWith {F : Type}
    (s_pmc : PanSemStateFiniteExact 64 F) (_r : Option (PanSemResultExact 64))
    (s : PanSemStateFiniteExact 64 F) (w_m w_out : BitVec 64)
    (extraIvls : List Ivl) : Prop :=
  ArenaReady s ∧
  globN s_pmc "heap_ptr" ≤ globN s "heap_ptr" ∧
  globN s_pmc "frame_mem_ptr" ≤ globN s "frame_mem_ptr" ∧
  globN s "scratch_ptr" ≤ globN s_pmc "scratch_ptr" ∧
  GlobalsKept sysTxGlobals s_pmc s ∧
  RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) sysTxKeep s_pmc s ∧
  WordsOK s (w_out.toNat, 96) ∧
  Inside (w_out.toNat, 96) (globN s_pmc "heap_ptr") (globN s "heap_ptr") ∧
  (memW s (w_out.toNat + 80) ≠ 0 →
    memW s (w_out.toNat + 80) = globN s_pmc "scratch_ptr" ∧
    memW s (w_out.toNat + 88) = globN s_pmc "frame_mem_ptr" ∧
    memW s (w_out.toNat + 48) ≤ scratchEnd) ∧
  ∀ S Nd,
    WorldTypedWith s_pmc S Nd →
    memW s_pmc (w_m.toNat + 152) ∈ S →
    memW s_pmc (w_m.toNat + 160) ∈ S →
    IvlsDisj ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc) (worldTypedIvls s_pmc S Nd) →
    ∃ S' Nd',
      (∀ t ∈ S, t ∈ S') ∧
      WorldTypedWith s S' Nd' ∧
      OwnedGrows s_pmc s (worldOwned s_pmc S Nd) (worldOwned s S' Nd') ∧
      FrameOutside s_pmc s
        (worldOwned s_pmc S Nd ++ ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc) ++ [freeGap s_pmc])
        (heapFree s_pmc) ∧
      IvlsDisj ((w_out.toNat, 96) :: extraIvls) (worldOwned s S' Nd')

abbrev SysTxPostPmcStep {F : Type}
    (s_pmc : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (s : PanSemStateFiniteExact 64 F) (w_m w_out : BitVec 64) : Prop :=
  SysTxPostPmcStepWith s_pmc r s w_m w_out []

theorem sysTxPostPmcStepWith_mono {F : Type}
    {s_pmc s : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {w_m w_out : BitVec 64} {ex1 ex2 : List Ivl}
    (hsub : ∀ x ∈ ex2, x ∈ ex1)
    (h : SysTxPostPmcStepWith s_pmc r s w_m w_out ex1) :
    SysTxPostPmcStepWith s_pmc r s w_m w_out ex2 := by
  obtain ⟨hAs, hhp, hfmp, hsp, hG, hK, hw_out, hin_out, hmk, hW⟩ := h
  refine ⟨hAs, hhp, hfmp, hsp, hG, hK, hw_out, hin_out, hmk, fun S Nd hWT hm152 hm160 hD => ?_⟩
  obtain ⟨S', Nd', hsubS, hWT', hOG, hFO, hd⟩ := hW S Nd hWT hm152 hm160 hD
  refine ⟨S', Nd', hsubS, hWT', hOG, hFO, fun i hi o ho => ?_⟩
  rcases List.mem_cons.1 hi with rfl | hi'
  · exact hd (w_out.toNat, 96) (List.mem_cons_self ..) o ho
  · exact hd i (List.mem_cons_of_mem _ (hsub i hi')) o ho

theorem sysTxPostPmcStep_with_locals_clock {F : Type}
    {s_pmc s : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    {w_m w_out : BitVec 64}
    (h : SysTxPostPmcStep s_pmc r s w_m w_out)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    SysTxPostPmcStep s_pmc r' { s with locals := L, clock := k } w_m w_out := by
  obtain ⟨hAs, hhp, hfmp, hsp, hG, hK, hw_out, hin_out, hmk, hW⟩ := h
  refine ⟨localsFree_arenaReady s L k hAs, hhp, hfmp, hsp, hG, hK, hw_out, hin_out, hmk,
    fun S Nd hWT hm152 hm160 hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hd_out⟩ := hW S Nd hWT hm152 hm160 hD
  obtain ⟨hT', hJ', hF', hNH', hndisj', hws'⟩ := hWT'
  have hWT'' : WorldTypedWith { s with locals := L, clock := k } S' Nd' :=
    ⟨(tablesTyped_with_locals s L k S').2 hT', hJ', hF', hNH', hndisj', hws'⟩
  exact ⟨S', Nd', hsub, hWT'', hOG, hFO, hd_out⟩

theorem sysTxPostPmcStepWith_worldOK {F : Type}
    {s0 s_pmc s : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {w_m w_aa w_ak w_out : BitVec 64} {extraIvls : List Ivl}
    (hW0 : WorldOK s0)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hpost : SysTxPostPmcStepWith s_pmc r s w_m w_out extraIvls) :
    WorldOK s ∧ ∃ S' Nd', WorldTypedWith s S' Nd' ∧
      IvlsDisj ((w_out.toNat, 96) :: extraIvls) (worldOwned s S' Nd') := by
  obtain ⟨_, _, _, htabs_step⟩ := hmt
  obtain ⟨_, S0, hS0⟩ := hW0
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s0 S0).1 hS0
  have hD0 : IvlsDisj (bufRegions sysTxBufs s0) (worldTypedIvls s0 S0 Nd0) :=
    validBufList_disj validBufList_sysTxBufs hWT0
  obtain ⟨S_pmc, Nd_pmc, _, hWT_pmc, _, _, hdisj_m_owned, htabs⟩ :=
    htabs_step S0 Nd0 hWT0 hD0
  obtain ⟨haa_S, _, _⟩ := htabs (w_aa.toNat, 20) (by simp)
  obtain ⟨hak_S, _, _⟩ := htabs (w_ak.toNat, 52) (by simp)
  have hD_pmc : IvlsDisj ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc)
      (worldTypedIvls s_pmc S_pmc Nd_pmc) := by
    intro i hi j hj
    rcases List.mem_cons.1 hi with rfl | hi_buf
    · exact hdisj_m_owned (w_m.toNat, 176) (by simp) j (worldTypedIvls_sub_worldOwned_sysTx s_pmc S_pmc Nd_pmc j hj)
    · exact validBufList_disj validBufList_sysTxBufs hWT_pmc i hi_buf j hj
  obtain ⟨S', Nd', _, hWT', _, _, hd_out⟩ :=
    hpost.2.2.2.2.2.2.2.2.2 S_pmc Nd_pmc hWT_pmc (by rw [hm152]; exact haa_S)
      (by rw [hm160]; exact hak_S) hD_pmc
  exact ⟨⟨hpost.1, S', (worldTyped_iff_with s S').2 ⟨Nd', hWT'⟩⟩, S', Nd', hWT', hd_out⟩

theorem sysTxPostPmcStep_worldOK {F : Type}
    {s0 s_pmc s : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {w_m w_aa w_ak w_out : BitVec 64}
    (hW0 : WorldOK s0)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hpost : SysTxPostPmcStep s_pmc r s w_m w_out) :
    WorldOK s ∧ ∃ S' Nd', WorldTypedWith s S' Nd' ∧ IvlsDisj [(w_out.toNat, 96)] (worldOwned s S' Nd') :=
  sysTxPostPmcStepWith_worldOK hW0 hmt hm152 hm160 hpost

theorem ownedGrows_trans_sysTx {F : Type}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {os1 os2 os3 : List Ivl}
    (hhp12 : globN s1 "heap_ptr" ≤ globN s2 "heap_ptr")
    (hhp23 : globN s2 "heap_ptr" ≤ globN s3 "heap_ptr")
    (h12 : OwnedGrows s1 s2 os1 os2)
    (h23 : OwnedGrows s2 s3 os2 os3) :
    OwnedGrows s1 s3 os1 os3 := by
  intro o ho
  rcases h23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
  · exact Or.inl rfl
  · rcases h12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
    · left
      rcases o with ⟨o1, o2⟩
      dsimp only [Inside] at hin_oj
      exact Prod.ext (by omega) (by omega)
    · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
    · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
        le_trans hin_oj.2 (le_trans hin_j12.2 hhp23)⟩)
  · exact Or.inr (Or.inr ⟨le_trans hhp12 hin_o23.1, hin_o23.2⟩)

theorem frameOutside_postPmc_trans_free_writes {F : Type}
    {s_pmc s1 s2 : PanSemStateFiniteExact 64 F}
    {S Nd S1 Nd1 : List Nat} {w_m : BitVec 64} {R2 : List Ivl}
    (hA_pmc : ArenaReady s_pmc)
    (hA1 : ArenaReady s1)
    (hhp_pmc1 : globN s_pmc "heap_ptr" ≤ globN s1 "heap_ptr")
    (hfmp_pmc1 : globN s_pmc "frame_mem_ptr" ≤ globN s1 "frame_mem_ptr")
    (hsp_pmc1 : globN s1 "scratch_ptr" ≤ globN s_pmc "scratch_ptr")
    (hOG01 : OwnedGrows s_pmc s1 (worldOwned s_pmc S Nd) (worldOwned s1 S1 Nd1))
    (hFO01 : FrameOutside s_pmc s1
      (worldOwned s_pmc S Nd ++ ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc) ++ [freeGap s_pmc])
      (heapFree s_pmc))
    (hFO12 : FrameOutside s1 s2
      (worldOwned s1 S1 Nd1 ++ R2 ++ [freeGap s1])
      (heapFree s1))
    (hR2_in_free : ∀ i ∈ R2,
      (∃ j ∈ (w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc, Inside i j.1 (j.1 + j.2)) ∨
      Inside i (globN s_pmc "heap_ptr") heapLimit) :
    FrameOutside s_pmc s2
      (worldOwned s_pmc S Nd ++ ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc) ++ [freeGap s_pmc])
      (heapFree s_pmc) := by
  intro a ha hhf
  have hm01 : s1.memory a = s_pmc.memory a := hFO01 a ha hhf
  have hm12 : s2.memory a = s1.memory a := by
    apply hFO12 a
    · intro i hi ⟨hc1, hc2⟩
      rcases List.mem_append.1 hi with hi1 | hfg1
      · rcases List.mem_append.1 hi1 with hwo1 | hR2
        · rcases hOG01 i hwo1 with rfl | ⟨k, hk, hin_ik⟩ | hin_i01
          · dsimp only at hc2; omega
          · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
              ⟨by dsimp only [Inside] at hin_ik; omega,
               by dsimp only [Inside] at hin_ik; omega⟩
          · have hp1_lim : globN s1 "heap_ptr" ≤ heapLimit := hA1.2.2.1
            exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i01 ⊢; omega,
                       by unfold heapFree; dsimp only [Inside] at hin_i01 ⊢; omega⟩
        · rcases hR2_in_free i hR2 with ⟨j, hj, hin_ij⟩ | hin_hf
          · exact ha j (List.mem_append_left _ (List.mem_append_right _ hj))
              ⟨by dsimp only [Inside] at hin_ij; omega,
               by dsimp only [Inside] at hin_ij; omega⟩
          · exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_hf ⊢; omega,
                       by unfold heapFree; dsimp only [Inside] at hin_hf ⊢; omega⟩
      · simp only [List.mem_singleton] at hfg1
        subst hfg1
        have hfmp_sp_pmc : globN s_pmc "frame_mem_ptr" ≤ globN s_pmc "scratch_ptr" := hA_pmc.2.2.2.2.1
        have hfmp_sp1 : globN s1 "frame_mem_ptr" ≤ globN s1 "scratch_ptr" := hA1.2.2.2.2.1
        exact ha (freeGap s_pmc) (List.mem_append_right _ (List.mem_singleton.2 rfl))
          ⟨by
            have hc1' : a.toNat + 8 > globN s1 "frame_mem_ptr" := hc1
            change a.toNat + 8 > globN s_pmc "frame_mem_ptr"; omega,
           by
            have hc2' : a.toNat < globN s1 "frame_mem_ptr" + (globN s1 "scratch_ptr" - globN s1 "frame_mem_ptr") := hc2
            change a.toNat < globN s_pmc "frame_mem_ptr" + (globN s_pmc "scratch_ptr" - globN s_pmc "frame_mem_ptr")
            omega⟩
    · intro ⟨hc1, hc2⟩
      have hp1_lim : globN s1 "heap_ptr" ≤ heapLimit := hA1.2.2.1
      exact hhf ⟨by
        have hc1' : a.toNat + 8 > globN s1 "heap_ptr" := hc1
        change a.toNat + 8 > globN s_pmc "heap_ptr"; omega,
       by
        have hc2' : a.toNat < globN s1 "heap_ptr" + (heapLimit - globN s1 "heap_ptr") := hc2
        change a.toNat < globN s_pmc "heap_ptr" + (heapLimit - globN s_pmc "heap_ptr")
        omega⟩
  exact hm12.trans hm01

theorem recordsKept_postPmc_trans_heap_ivl {F : Type}
    {s_pmc s1 s2 : PanSemStateFiniteExact 64 F}
    {w_m : BitVec 64} {ivl : Ivl}
    (hW1 : WorldOK s1)
    (hG01 : GlobalsKept sysTxGlobals s_pmc s1)
    (hK01 : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) sysTxKeep s_pmc s1)
    (hK12 : RecordsKept (fun _ => [ivl]) stdKeep s1 s2)
    (hivl8 : ivl.1 % 8 = 0)
    (hin_ivl : Inside ivl (globN s1 "heap_ptr") heapLimit ∨
      ∃ S1 Nd1, WorldTypedWith s1 S1 Nd1 ∧ IvlsDisj [ivl] (worldTypedIvls s1 S1 Nd1)) :
    RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) sysTxKeep s_pmc s2 := by
  obtain ⟨hA1, S1w, hS1w⟩ := hW1
  obtain ⟨Nd1w, hWT1w⟩ := (worldTyped_iff_with s1 S1w).1 hS1w
  have hF1 := hWT1w.2.2.1
  have hkeep_sub : KeepSub sysTxKeep stdKeep := by
    intro r hr
    simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨[0, 8, 16, 24, 32], by simp [stdKeep], fun off hoff => hoff⟩
    · refine ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72], by simp [stdKeep], fun off hoff => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff ⊢
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64], by simp [stdKeep], fun _ h => False.elim (by simp at h)⟩
    · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80], by simp [stdKeep], fun off hoff => hoff⟩
  have hK12' := recordsKept_mono_keep hkeep_sub hK12
  intro rec hrec hnz off hoff hno
  have hg_rec : globN s1 rec.1 = globN s_pmc rec.1 := by
    simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · exact globN_eq_of_lookup (hG01 (ofString "ws") (by decide))
    · exact globN_eq_of_lookup (hG01 (ofString "bs") (by decide))
    · cases hoff
    · exact globN_eq_of_lookup (hG01 (ofString "bo") (by decide))
  have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ off % 8 = 0 ∧ off + 8 ≤ sz := by
    simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · refine ⟨40, by simp [typedRecords], ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;> omega
    · refine ⟨80, by simp [typedRecords], ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · cases hoff
    · refine ⟨88, by simp [typedRecords], ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨sz, htr, hoff8, hoff_sz⟩ := hrec_sz
  have hnz1 : globN s1 rec.1 ≠ 0 := by rw [hg_rec]; exact hnz
  have hmf : (globN s1 rec.1, sz) ∈ fixedObjects s1 := by
    have hm := typedRecord_mem_fixedObjects s1 htr
    simpa [hnz1] using hm
  rcases hF1.1 _ hmf with h0 | ⟨hal, hwords⟩
  · omega
  · have hg8 : globN s1 rec.1 % 8 = 0 := hwords.1
    have hdisj_ivl : Disj (globN s1 rec.1, sz) ivl := by
      · rcases hin_ivl with hfresh | ⟨S1, Nd1, _, hd_all⟩
        · rcases hal with hheap | hscr
          · exact Or.inr (Or.inr (Or.inl (le_trans hheap.2 hfresh.1)))
          · have hsep : heapLimit ≤ scratchStart := by decide
            have := hA1.2.2.2.1; have := hA1.2.2.2.2.1
            exact Or.inr (Or.inr (Or.inr (by dsimp only [Inside] at hfresh hscr ⊢; omega)))
        · have htr_mem : (globN s1 rec.1, sz) ∈ worldTypedIvls s1 S1 Nd1 := by
            unfold worldTypedIvls
            apply List.mem_append_left; apply List.mem_append_left
            apply List.mem_append_left; apply List.mem_append_left
            apply List.mem_append_right
            have hm : (fun r : String × Nat =>
                (globN s1 r.1, if globN s1 r.1 = 0 then 0 else r.2)) (rec.1, sz) ∈
                typedRecords.map (fun r => (globN s1 r.1, if globN s1 r.1 = 0 then 0 else r.2)) :=
              List.mem_map.2 ⟨(rec.1, sz), htr, rfl⟩
            simpa [hnz1] using hm
          exact InitECandidate.Solver.Wave8Contracts.M08.disj_symm
            (hd_all ivl (by simp) _ htr_mem)
    have hno_ivl : ∀ i ∈ ([ivl] : List Ivl), ¬ CellHits (globN s1 rec.1 + off) i := by
      intro i hi
      simp only [List.mem_singleton] at hi
      subst i
      exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj
        (i := (globN s1 rec.1, sz)) (by omega) hivl8 ⟨by omega, by omega⟩ hdisj_ivl
    have h2 := hK12' rec hrec hnz1 off hoff hno_ivl
    rw [hg_rec] at h2
    exact h2.trans (hK01 rec hrec hnz off hoff hno)

theorem sysTxPostPmc_store_out40_step {F : Type}
    {s0 s_pmc s : PanSemStateFiniteExact 64 F}
    {w_m w_aa w_ak w_out w_sr : BitVec 64}
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hstep : SysTxPostPmcStep s_pmc none s w_m w_out)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hl_sr : s.locals.lookup (ofString "system_ret") = some (.val (.word w_sr))) :
    ∃ s_st : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s
        (.store (.op .add [.var .local (ofString "out"), .const 40#64])
          (.var .local (ofString "system_ret"))) = (none, s_st) ∧
      s_st.locals = s.locals ∧
      s_st.code = s.code ∧
      SysTxPostPmcStep s_pmc none s_st w_m w_out ∧
      memW s_st (w_out.toNat + 88) = memW s (w_out.toNat + 88) := by
  obtain ⟨hWs, S_ex, Nd_ex, hWT_ex, hd_ex⟩ := sysTxPostPmcStep_worldOK hW0 hmt hm152 hm160 hstep
  obtain ⟨hAs, hhp, hfmp, hsp, hG, hK, hw_out, hin_out, hmk, hW⟩ := hstep
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hlo_pmc : sourceBase ≤ globN s_pmc "heap_ptr" := hA_pmc.2.1
  have hin_s : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hlo_pmc hin_out.1, hin_out.2⟩
  have hin_bound : w_out.toNat + 96 ≤ 2 ^ 64 := by
    unfold Inside at hin_s; omega
  have hsum_lt : w_out.toNat + 40 < 2 ^ 64 := by omega
  have hx_nat : (w_out + 40#64).toNat = w_out.toNat + 40 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h40 : 40 < 2 ^ 64 := by decide
    rw [Nat.mod_eq_of_lt h40, Nat.mod_eq_of_lt hsum_lt]
  obtain ⟨_, hdom40, _⟩ := hw_out.2.2 5 (by omega)
  have hbv40 : BitVec.ofNat 64 (w_out.toNat + 8 * 5) = w_out + 40#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hx_nat, Nat.mod_eq_of_lt (by omega)]
  rw [hbv40] at hdom40
  have hev_addr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "out"), .const 40#64]) = some (.val (.word (w_out + 40#64))) := by
    simp [evalHOLExact, evalListHOLExact, hl_out, valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_zero]
  have hev_val : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "system_ret")) = some (.val (.word w_sr)) := by
    simp [evalHOLExact, hl_sr]
  let mem' : BitVec 64 → HolWordLab 64 :=
    Function.update s.memory (w_out + 40#64) (.word w_sr)
  have hst : @panMemStoresHOL 64 _ (w_out + 40#64) (flattenHOL (.val (.word w_sr))) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem' := by
    simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom40, mem']
    funext current
    by_cases hcur : current = w_out + 40#64
    · subst hcur; simp [Function.update]
    · simp [Function.update, hcur]
  have heval : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "out"), .const 40#64])
        (.var .local (ofString "system_ret"))) = (none, { s with memory := mem' }) := by
    rw [evaluateHOLFiniteState_store]
    simp [hev_addr, hev_val, hst]
  have hws_step : WorldStep (fun _ => [(w_out.toNat, 96)]) [] stdKeep NoExtra
      s none { s with memory := mem' } :=
    worldStep_store_in_block (r := none) hWs rfl hw_out.1 hw_out.2.1 (by decide)
      hin_s rfl (by simp [flattenHOL]) hst
  obtain ⟨hA_st, _, _, hK_st, hW_st⟩ := hws_step
  have hframe_off : ∀ off' : Nat, off' + 8 ≤ 96 → off' ≠ 40 →
      memW ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_out.toNat + off') =
        memW s (w_out.toNat + off') := by
    intro off' hoff' hne
    unfold memW
    dsimp only [mem']
    have hne_bv : BitVec.ofNat 64 (w_out.toNat + off') ≠ w_out + 40#64 := by
      intro heq
      have h1 := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hx_nat] at h1
      omega
    rw [Function.update_of_ne hne_bv]
  have hw_out_st : WordsOK ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_out.toNat, 96) :=
    InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hA_st.1 hw_out
  have hK_tot : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st)
      sysTxKeep s_pmc { s with memory := mem' } :=
    recordsKept_postPmc_trans_heap_ivl hWs hG hK hK_st hw_out.1
      (Or.inr ⟨S_ex, Nd_ex, hWT_ex,
        fun i hi j hj => hd_ex i hi j (worldTypedIvls_sub_worldOwned_sysTx s S_ex Nd_ex j hj)⟩)
  have hm80 : memW ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_out.toNat + 80) =
      memW s (w_out.toNat + 80) := hframe_off 80 (by omega) (by omega)
  have hm88 : memW ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_out.toNat + 88) =
      memW s (w_out.toNat + 88) := hframe_off 88 (by omega) (by omega)
  have hm48 : memW ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_out.toNat + 48) =
      memW s (w_out.toNat + 48) := hframe_off 48 (by omega) (by omega)
  refine ⟨{ s with memory := mem' }, heval, rfl, rfl, ⟨hA_st, hhp, hfmp, hsp, hG, hK_tot,
    hw_out_st, hin_out, ?_, fun S Nd hWT hm152' hm160' hD => ?_⟩, hm88⟩
  · rw [hm80, hm88, hm48]; exact hmk
  · obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, hd_out1⟩ := hW S Nd hWT hm152' hm160' hD
    have hD_st : IvlsDisj [(w_out.toNat, 96)] (worldTypedIvls s S1 Nd1) :=
      fun i hi j hj => hd_out1 i hi j (worldTypedIvls_sub_worldOwned_sysTx s S1 Nd1 j hj)
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, _⟩ := hW_st S1 Nd1 hWT1 hD_st
    refine ⟨S2, Nd2, fun t ht => hsub12 t (hsub01 t ht), hWT2,
      ownedGrows_trans_sysTx hhp le_rfl hOG01 hOG12,
      frameOutside_postPmc_trans_free_writes hA_pmc hAs hhp hfmp hsp hOG01 hFO01 hFO12
        (fun i hi => by
          simp only [List.mem_singleton] at hi; subst i
          exact Or.inr ⟨hin_out.1, le_trans hin_out.2 hhp_lim⟩),
      ?_⟩
    intro i hi o ho
    simp only [List.mem_singleton] at hi; subst i
    rcases hOG12 o ho with rfl | ⟨j, hj, hin_oj⟩ | hfresh
    · exact InitECandidate.Solver.Wave8Contracts.M08.disj_zero_right _
    · exact InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hin_oj
        (hd_out1 (w_out.toNat, 96) (by simp) j hj)
    · exact Or.inr (Or.inr (Or.inl (le_trans hin_out.2 hfresh.1)))

private theorem lookup_memcpy_sysTx :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem sysTxPostPmc_memcpy_step {F : Type}
    {s0 s_pmc s : PanSemStateFiniteExact 64 F}
    {w_m w_aa w_ak w_out w_sr w_rn : BitVec 64}
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hc : s.code = originalRuntimeCode)
    (hstep : SysTxPostPmcStepWith s_pmc none s w_m w_out [(w_sr.toNat, w_rn.toNat)])
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hl_sr : s.locals.lookup (ofString "system_ret") = some (.val (.word w_sr)))
    (hl_rn : s.locals.lookup (ofString "system_ret_n") = some (.val (.word w_rn)))
    (hsr8 : w_sr.toNat % 8 = 0)
    (hin_sr : Inside (w_sr.toNat, w_rn.toNat) (globN s_pmc "heap_ptr") (globN s "heap_ptr"))
    (hdisj_sr_out : Disj (w_out.toNat, 96) (w_sr.toNat, w_rn.toNat))
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "system_ret"),
         .load .one (.op .add [.var .local (ofString "out"), .const 40#64]),
         .var .local (ofString "system_ret_n")])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "system_ret"),
         .load .one (.op .add [.var .local (ofString "out"), .const 40#64]),
         .var .local (ofString "system_ret_n")])).1) :
    ∃ s_mc : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "system_ret"),
           .load .one (.op .add [.var .local (ofString "out"), .const 40#64]),
           .var .local (ofString "system_ret_n")]) = (none, s_mc) ∧
      s_mc.locals = s.locals ∧
      s_mc.code = originalRuntimeCode ∧
      SysTxPostPmcStep s_pmc none s_mc w_m w_out ∧
      memW s_mc (w_out.toNat + 88) = memW s (w_out.toNat + 88) := by
  obtain ⟨hWs, S_u, Nd_u, hWT_u, hd_u⟩ := sysTxPostPmcStepWith_worldOK hW0 hmt hm152 hm160 hstep
  obtain ⟨hAs, hhp, hfmp, hsp, hG, hK, hw_out, hin_out, hmk, hW⟩ := hstep
  have hlo_pmc : sourceBase ≤ globN s_pmc "heap_ptr" := hA_pmc.2.1
  have hin_s : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hlo_pmc hin_out.1, hin_out.2⟩
  have hload40 := evalHOLExact_load_word_in_block_sysTx (off := 40) hAs.2 hl_out hw_out hin_s
    (by decide) (by decide)
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "system_ret"),
       .load .one (.op .add [.var .local (ofString "out"), .const 40#64]),
       .var .local (ofString "system_ret_n")] =
      some [.val (.word w_sr), .val (.word (BitVec.ofNat 64 (memW s (w_out.toNat + 40)))),
            .val (.word w_rn)] := by
    have he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.var .local (ofString "system_ret")) = some (.val (.word w_sr)) := by
      simp [evalHOLExact, hl_sr]
    have he3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.var .local (ofString "system_ret_n")) = some (.val (.word w_rn)) := by
      simp [evalHOLExact, hl_rn]
    unfold evalListHOLFinite
    dsimp only [evalListHOLExact]
    rw [he1, hload40, he3]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "memcpy")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_memcpy) w_sr
    (BitVec.ofNat 64 (memW s (w_out.toNat + 40))) w_rn
    (by decide) (by decide) (by decide)
    (by rw [hc]; exact lookup_memcpy_sysTx)
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rw [hargs] at hnt hfr ⊢; dsimp only at hnt hfr ⊢
  rw [hlk] at hnt hfr ⊢; dsimp only at hnt hfr ⊢
  by_cases hz : s.clock = 0
  · simp [hz] at hnt
  · rw [if_neg hz] at hnt hfr ⊢
    set callee : HolFiniteMapExact MlS (ValueHOL 64) :=
      (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word w_sr))).update
        (ofString "src", .val (.word (BitVec.ofNat 64 (memW s (w_out.toNat + 40)))))).update
        (ofString "n", .val (.word w_rn)))
    let ent := callEntryStateHOLFinite s callee
    have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hWs
    have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent
      (sourceFnBody Guest.Software.guestFn_memcpy)).1
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨res, cpost⟩
    simp only [ent] at hrun hmeta
    simp only [hrun] at hmeta hnt hfr ⊢
    have hnt_c : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_memcpy)).1 ≠ some .timeOut := by
      simp only [ent, hrun]; rintro rfl; simp at hnt
    cases res with
    | none => exact absurd hfr not_flowingOrResumes_error
    | some cr =>
      cases cr with
      | timeOut => simp at hnt
      | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
      | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
      | exception eid ev =>
        dsimp only at hfr
        have hres_ex : Resumes (some (.exception eid ev)) := by
          rcases hfr with h | h | h | hr <;> try simp at h
          exact hr
        have hret := memcpy_body_resumes_returned_sysTx ent (by simpa [ent, hrun] using hres_ex)
        simp [ent, hrun] at hret
      | returned v =>
        dsimp only at hnt hfr ⊢
        by_cases hsh : shapeEqHOL (shapeOfHOLExact v) .one = true
        · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
          have hwk_mc : WorldKeeps WorldOK (fun st => [(locN st "dst", locN st "n")]) [] stdKeep
              NoExtra (ofString "memcpy") :=
            InitECandidate.Solver.Wave8Contracts.M08.«wk_memcpy»
          have hspec := FunSpec.at_lookup hwk_mc
            s hc [.val (.word w_sr), .val (.word (BitVec.ofNat 64 (memW s (w_out.toNat + 40)))),
                  .val (.word w_rn)]
            (sourceFnBody Guest.Software.guestFn_memcpy) callee .one hlk hWent hnt_c
          simp only [ent, hrun] at hspec
          have hws_mc := hspec (Or.inl ⟨v, rfl⟩)
          have hloc_dst : locN ent "dst" = w_sr.toNat := by
            have hne1 : ofString "dst" ≠ ofString "n" := by decide
            have hne2 : ofString "dst" ≠ ofString "src" := by decide
            simp [ent, callee, callEntryStateHOLFinite, decClockHOLFinite, locN,
              HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne1, Ne.symm hne2]
          have hloc_n : locN ent "n" = w_rn.toNat := by
            simp [ent, callee, callEntryStateHOLFinite, decClockHOLFinite, locN,
              HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨hA_cp, hhp_cp, hG_cp, hK_cp, hW_cp⟩ := hws_mc
          set s_mc : PanSemStateFiniteExact 64 F := { cpost with locals := s.locals }
          have hA_mc : ArenaReady s_mc := localsFree_arenaReady cpost s.locals cpost.clock hA_cp
          have hG_s_mc : GlobalsKept [] s s_mc := hG_cp
          have hg_eq : ∀ g : String, globN s_mc g = globN s g :=
            fun g => globN_eq_of_lookup (hG_s_mc (ofString g) (by simp))
          have hhp_mc : globN s_mc "heap_ptr" = globN s "heap_ptr" := hg_eq "heap_ptr"
          have hfmp_mc : globN s_mc "frame_mem_ptr" = globN s "frame_mem_ptr" := hg_eq "frame_mem_ptr"
          have hsp_mc : globN s_mc "scratch_ptr" = globN s "scratch_ptr" := hg_eq "scratch_ptr"
          have hG_tot : GlobalsKept sysTxGlobals s_pmc s_mc :=
            fun k hk => (hG k hk).trans (hG_s_mc k (by simp))
          have hK_mc' : RecordsKept (fun _ => [(w_sr.toNat, w_rn.toNat)]) stdKeep s s_mc := by
            intro rec hrec hnz off hoff hno
            exact hK_cp rec hrec hnz off hoff (by
              intro i hi
              simp only [List.mem_singleton, hloc_dst, hloc_n] at hi
              subst i
              exact hno (w_sr.toNat, w_rn.toNat) (by simp))
          have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
          have h264 : heapLimit ≤ 2 ^ 64 := by decide
          have hin_bound : w_out.toNat + 96 ≤ 2 ^ 64 := by unfold Inside at hin_s; omega
          have hd_sr_u : IvlsDisj [(w_sr.toNat, w_rn.toNat)] (worldTypedIvls s S_u Nd_u) := by
            intro i hi j hj
            simp only [List.mem_singleton] at hi; subst i
            exact hd_u (w_sr.toNat, w_rn.toNat) (by simp) j
              (worldTypedIvls_sub_worldOwned_sysTx s S_u Nd_u j hj)
          have hK_tot : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st)
              sysTxKeep s_pmc s_mc :=
            recordsKept_postPmc_trans_heap_ivl hWs hG hK hK_mc' hsr8
              (Or.inr ⟨S_u, Nd_u, hWT_u, hd_sr_u⟩)
          have hWT_u_ent : WorldTypedWith ent S_u Nd_u :=
            ⟨(tablesTyped_with_locals s callee (s.clock - 1) S_u).2 hWT_u.1,
              hWT_u.2.1, hWT_u.2.2.1, hWT_u.2.2.2.1, hWT_u.2.2.2.2.1, hWT_u.2.2.2.2.2⟩
          have hD_u_ent : IvlsDisj [(locN ent "dst", locN ent "n")] (worldTypedIvls ent S_u Nd_u) := by
            rw [hloc_dst, hloc_n]
            exact hd_sr_u
          obtain ⟨S_u', Nd_u', _, _, _, hFO_u, _⟩ := hW_cp S_u Nd_u hWT_u_ent hD_u_ent
          have hunhit_out : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s s_mc (w_out.toNat, 96) := by
            intro a ha8 ha1 ha2
            apply hFO_u a
            · intro j hj ⟨hc1, hc2⟩
              rcases List.mem_append.1 hj with hj12 | hfg
              · rcases List.mem_append.1 hj12 with hj_ow | hj_R
                · have hj_ow_s : j ∈ worldOwned s S_u Nd_u := hj_ow
                  have hd_oj := hd_u (w_out.toNat, 96) (by simp) j hj_ow_s
                  rcases j with ⟨j1, j2⟩
                  by_cases hj2z : j2 = 0
                  · have hj0 := worldOwned_zero_base_sysTx hWT_u hj_ow_s hj2z
                    cases hj0
                    dsimp only at hc2; omega
                  · rcases hd_oj with h0 | h0 | hle | hle <;> dsimp only at * <;> omega
                · simp only [List.mem_singleton, hloc_dst, hloc_n] at hj_R
                  subst j
                  exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj
                    (i := (w_out.toNat, 96)) ha8 hsr8 ⟨ha1, ha2⟩ hdisj_sr_out ⟨hc1, hc2⟩
              · simp only [List.mem_singleton] at hfg
                subst j
                have hsep : heapLimit ≤ scratchStart := by decide
                have hfmp_ge : scratchStart ≤ globN s "frame_mem_ptr" := hAs.2.2.2.1
                have hfmp_ent : (freeGap (callEntryStateHOLFinite s callee)).1 = globN s "frame_mem_ptr" := rfl
                rw [hfmp_ent] at hc2
                unfold Inside at hin_s
                omega
            · intro ⟨hc1, hc2⟩
              change a.toNat + 8 > globN s "heap_ptr" at hc1
              unfold Inside at hin_s
              omega
          have hw_out_mc : WordsOK s_mc (w_out.toNat, 96) :=
            InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hA_mc.1 hw_out
          have hm80 : memW s_mc (w_out.toNat + 80) = memW s (w_out.toNat + 80) :=
            InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hunhit_out
              (by have := hw_out.1; omega) hin_bound ⟨by omega, by omega⟩
          have hm88 : memW s_mc (w_out.toNat + 88) = memW s (w_out.toNat + 88) :=
            InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hunhit_out
              (by have := hw_out.1; omega) hin_bound ⟨by omega, by omega⟩
          have hm48 : memW s_mc (w_out.toNat + 48) = memW s (w_out.toNat + 48) :=
            InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hunhit_out
              (by have := hw_out.1; omega) hin_bound ⟨by omega, by omega⟩
          refine ⟨s_mc, rfl, rfl, hmeta.trans hc, ⟨hA_mc,
            by rw [hhp_mc]; exact hhp,
            by rw [hfmp_mc]; exact hfmp,
            by rw [hsp_mc]; exact hsp,
            hG_tot, hK_tot, hw_out_mc,
            by rw [hhp_mc]; exact hin_out,
            by rw [hm80, hm88, hm48]; exact hmk,
            fun S Nd hWT hm152' hm160' hD => ?_⟩, hm88⟩
          obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, hd_out1⟩ := hW S Nd hWT hm152' hm160' hD
          have hWT1_ent : WorldTypedWith ent S1 Nd1 :=
            ⟨(tablesTyped_with_locals s callee (s.clock - 1) S1).2 hWT1.1,
              hWT1.2.1, hWT1.2.2.1, hWT1.2.2.2.1, hWT1.2.2.2.2.1, hWT1.2.2.2.2.2⟩
          have hD1_ent : IvlsDisj [(locN ent "dst", locN ent "n")] (worldTypedIvls ent S1 Nd1) := by
            rw [hloc_dst, hloc_n]
            intro i hi j hj
            simp only [List.mem_singleton] at hi; subst i
            exact hd_out1 (w_sr.toNat, w_rn.toNat) (by simp) j
              (worldTypedIvls_sub_worldOwned_sysTx s S1 Nd1 j hj)
          obtain ⟨S2, Nd2, hsub12, hWT2_cp, hOG12_cp, hFO12_cp, _⟩ := hW_cp S1 Nd1 hWT1_ent hD1_ent
          have hWT2 : WorldTypedWith s_mc S2 Nd2 :=
            ⟨(tablesTyped_with_locals cpost s.locals cpost.clock S2).2 hWT2_cp.1,
              hWT2_cp.2.1, hWT2_cp.2.2.1, hWT2_cp.2.2.2.1, hWT2_cp.2.2.2.2.1, hWT2_cp.2.2.2.2.2⟩
          have hOG12 : OwnedGrows s s_mc (worldOwned s S1 Nd1) (worldOwned s_mc S2 Nd2) := hOG12_cp
          have hFO12 : FrameOutside s s_mc
              (worldOwned s S1 Nd1 ++ [(w_sr.toNat, w_rn.toNat)] ++ [freeGap s]) (heapFree s) := by
            intro a hno_hit hno_hf
            apply hFO12_cp a
            · intro j hj hch
              apply hno_hit j _ hch
              rcases List.mem_append.1 hj with hj12 | hfg
              · rcases List.mem_append.1 hj12 with hj_ow | hj_R
                · exact List.mem_append_left _ (List.mem_append_left _ hj_ow)
                · simp only [List.mem_singleton] at hj_R
                  subst j
                  have h1 : locN (callEntryStateHOLFinite s callee) "dst" = w_sr.toNat := hloc_dst
                  have h2 : locN (callEntryStateHOLFinite s callee) "n" = w_rn.toNat := hloc_n
                  rw [h1, h2]
                  exact List.mem_append_left _ (List.mem_append_right _ (by simp))
              · exact List.mem_append_right _ hfg
            · exact hno_hf
          refine ⟨S2, Nd2, fun t ht => hsub12 t (hsub01 t ht), hWT2,
            ownedGrows_trans_sysTx hhp (by rw [hhp_mc]) hOG01 hOG12,
            frameOutside_postPmc_trans_free_writes hA_pmc hAs hhp hfmp hsp hOG01 hFO01 hFO12
              (fun i hi => by
                simp only [List.mem_singleton] at hi; subst i
                exact Or.inr ⟨hin_sr.1, le_trans hin_sr.2 hhp_lim⟩),
            ?_⟩
          intro i hi o ho
          simp only [List.mem_singleton] at hi; subst i
          rcases hOG12 o ho with rfl | ⟨j, hj, hin_oj⟩ | hfresh
          · exact InitECandidate.Solver.Wave8Contracts.M08.disj_zero_right _
          · exact InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hin_oj
              (hd_out1 (w_out.toNat, 96) (by simp) j hj)
          · exact Or.inr (Or.inr (Or.inl (le_trans hin_out.2 hfresh.1)))
        · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem sysTxCopyRetSeqProg_step {F : Type}
    {s0 s_pmc s : PanSemStateFiniteExact 64 F}
    {w_m w_aa w_ak w_out w_sr w_rn : BitVec 64}
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hc : s.code = originalRuntimeCode)
    (hstep : SysTxPostPmcStepWith s_pmc none s w_m w_out [(w_sr.toNat, w_rn.toNat)])
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hl_sr : s.locals.lookup (ofString "system_ret") = some (.val (.word w_sr)))
    (hl_rn : s.locals.lookup (ofString "system_ret_n") = some (.val (.word w_rn)))
    (hsr8 : w_sr.toNat % 8 = 0)
    (hin_sr : Inside (w_sr.toNat, w_rn.toNat) (globN s_pmc "heap_ptr") (globN s "heap_ptr"))
    (hdisj_sr_out : Disj (w_out.toNat, 96) (w_sr.toNat, w_rn.toNat))
    (hnt : (evaluateHOLFiniteState s sysTxCopyRetSeqProg).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s sysTxCopyRetSeqProg).1) :
    ∃ s_seq : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s sysTxCopyRetSeqProg = (none, s_seq) ∧
      s_seq.locals = s.locals ∧
      s_seq.code = originalRuntimeCode ∧
      SysTxPostPmcStep s_pmc none s_seq w_m w_out ∧
      memW s_seq (w_out.toNat + 88) = memW s (w_out.toNat + 88) := by
  unfold sysTxCopyRetSeqProg at hnt hfr ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  set callMc : ProgHOL 64 :=
    .call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "system_ret"),
       .load .one (.op .add [.var .local (ofString "out"), .const 40#64]),
       .var .local (ofString "system_ret_n")]
  have hnt_mc : (evaluateHOLFiniteState s callMc).1 ≠ some .timeOut := by
    rintro hto
    rcases hmc : evaluateHOLFiniteState s callMc with ⟨r1, m1⟩
    rw [hmc] at hto hnt
    dsimp only at hto
    subst hto
    exact hnt rfl
  have hfr_mc : FlowingOrResumes (evaluateHOLFiniteState s callMc).1 := by
    rcases hmc : evaluateHOLFiniteState s callMc with ⟨r1, m1⟩
    rw [hmc] at hfr
    dsimp only
    cases r1 with
    | none => exact Or.inl rfl
    | some r1' =>
      dsimp only at hfr
      exact hfr
  obtain ⟨s_mc, hmc_eq, hmc_loc, hmc_code, hmc_step, hmc_88⟩ :=
    sysTxPostPmc_memcpy_step hW0 hA_pmc hmt hm152 hm160 hc hstep hl_out hl_sr hl_rn
      hsr8 hin_sr hdisj_sr_out hnt_mc hfr_mc
  rw [hmc_eq]; dsimp only
  obtain ⟨s_st, hst_eq, hst_loc, hst_code, hst_step, hst_88⟩ :=
    sysTxPostPmc_store_out40_step hW0 hA_pmc hmt hm152 hm160 hmc_step
      (by rw [hmc_loc]; exact hl_out) (by rw [hmc_loc]; exact hl_sr)
  exact ⟨s_st, hst_eq, hst_loc.trans hmc_loc, hst_code.trans hmc_code, hst_step,
    hst_88.trans hmc_88⟩

theorem sysTxCopyRetBodyProg_step {F : Type}
    {s0 s_pmc s : PanSemStateFiniteExact 64 F}
    {w_m w_aa w_ak w_out w_rn : BitVec 64}
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hc : s.code = originalRuntimeCode)
    (hstep : SysTxPostPmcStep s_pmc none s w_m w_out)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hl_rn : s.locals.lookup (ofString "system_ret_n") = some (.val (.word w_rn)))
    (hrn_le : w_rn.toNat ≤ scratchEnd)
    (hnt : (evaluateHOLFiniteState s sysTxCopyRetBodyProg).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s sysTxCopyRetBodyProg).1) :
    ∃ s_body : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s sysTxCopyRetBodyProg = (none, s_body) ∧
      (∀ k, k ≠ ofString "system_ret" → s_body.locals.lookup k = s.locals.lookup k) ∧
      s_body.code = originalRuntimeCode ∧
      SysTxPostPmcStep s_pmc none s_body w_m w_out ∧
      memW s_body (w_out.toNat + 88) = memW s (w_out.toNat + 88) := by
  have hbody_eq : sysTxCopyRetBodyProg =
      .decCall (ofString "system_ret") .one (ofString "alloc")
        [.op .add [.var .local (ofString "system_ret_n"), .const 8#64]]
        sysTxCopyRetSeqProg := by
    unfold sysTxCopyRetBodyProg sysTxCopyRetSeqProg; rfl
  rw [hbody_eq] at hnt hfr ⊢
  obtain ⟨hWs, _⟩ := sysTxPostPmcStep_worldOK hW0 hmt hm152 hm160 hstep
  obtain ⟨hAs, hhp, hfmp, hsp, hG, hK, hw_out, hin_out, hmk, hW⟩ := hstep
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "system_ret_n"), .const 8#64]] =
      some [.val (.word (w_rn + 8#64))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hl_rn,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) (w_rn + 8#64)
    (by rw [hc]; exact R13Shards.lookup_alloc_r13)
  rw [evaluateHOLFiniteState_decCall_total] at hnt hfr ⊢
  rw [hargs] at hnt hfr ⊢; dsimp only at hnt hfr ⊢
  rw [hlk] at hnt hfr ⊢; dsimp only at hnt hfr ⊢
  by_cases hz : s.clock = 0
  · simp [hz] at hnt
  · simp only [hz, ↓reduceIte] at hnt hfr ⊢
    try dsimp only at hnt hfr ⊢
    rw [fixClockHOLFinite_evaluateState] at hnt hfr ⊢
    set callee : HolFiniteMapExact MlS (ValueHOL 64) :=
      HolFiniteMapExact.empty.update (ofString "n", .val (.word (w_rn + 8#64)))
    let ent := callEntryStateHOLFinite s callee
    have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hWs
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res, post⟩
    simp only [ent] at hrun
    simp only [hrun] at hnt hfr ⊢
    cases res with
    | none => exact absurd hfr not_flowingOrResumes_error
    | some cr =>
      cases cr with
      | timeOut => simp at hnt
      | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
      | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
      | exception eid ev =>
        dsimp only at hfr
        have hres_ex : Wave8Contracts.M12.Resumes
            (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
          simp only [ent, hrun]
          rcases hfr with h | h | h | ⟨⟨rv, hrv⟩ | ⟨eid', ev', hexc, hne⟩⟩ <;> try simp at h
          · simp at hrv
          · injection hexc with hexc'
            injection hexc' with heid hev
            subst heid; subst hev
            exact Or.inr ⟨eid, ev, rfl, hne⟩
        obtain ⟨p, _, hrv, _⟩ := R13Shards.alloc_body_resumes_props ent hc hWent.1 hres_ex
        simp [ent, hrun] at hrv
      | returned v =>
        dsimp only at hnt hfr ⊢
        have hres_al : Wave8Contracts.M12.Resumes
            (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
          simp only [ent, hrun]; exact Or.inl ⟨v, rfl⟩
        obtain ⟨p, q, hrv, hp_eq, hq_eq, hq_hi, hq_al, hp_le_q,
          hpost_g, hpost_m, hpost_be, _, hA_post, hpost_hp, hpost_sp⟩ :=
          R13Shards.alloc_body_resumes_props ent hc hWent.1 hres_al
        simp only [ent, hrun] at hrv hpost_g hpost_m hpost_be hA_post hpost_hp hpost_sp
        injection hrv with hrv'; injection hrv' with hrv''; subst hrv''
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word p))) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word p))) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hnt hfr ⊢
        let s_al : PanSemStateFiniteExact 64 F :=
          setVarHOLFinite (ofString "system_ret") (.val (.word p)) { post with locals := s.locals }
        have hcode_meta := (PanRunBounded.evaluateHOLFiniteState_metadata ent
          (sourceFnBody Guest.Software.guestFn_alloc)).1
        simp only [ent, hrun] at hcode_meta
        have hs_al_code : s_al.code = originalRuntimeCode := by
          dsimp only [s_al, setVarHOLFinite]
          exact hcode_meta.trans hc
        have hs_al_out : s_al.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
          dsimp only [s_al, setVarHOLFinite]
          rw [HolFiniteMapExact.lookup_update]
          simp [FUPDATE, hl_out, show ofString "system_ret" ≠ ofString "out" by decide]
        have hs_al_sr : s_al.locals.lookup (ofString "system_ret") = some (.val (.word p)) := by
          dsimp only [s_al, setVarHOLFinite]
          rw [HolFiniteMapExact.lookup_update]
          simp [FUPDATE]
        have hs_al_rn : s_al.locals.lookup (ofString "system_ret_n") = some (.val (.word w_rn)) := by
          dsimp only [s_al, setVarHOLFinite]
          rw [HolFiniteMapExact.lookup_update]
          simp [FUPDATE, hl_rn, show ofString "system_ret" ≠ ofString "system_ret_n" by decide]
        have hs_al_loc_other : ∀ k, k ≠ ofString "system_ret" → s_al.locals.lookup k = s.locals.lookup k := by
          intro k hk
          dsimp only [s_al, setVarHOLFinite]
          rw [HolFiniteMapExact.lookup_update]
          simp [FUPDATE, hk.symm]
        have hp_s : p.toNat = globN s "heap_ptr" := hp_eq
        have hp8 : p.toNat % 8 = 0 := by rw [hp_s]; exact hAs.2.2.2.2.2.2.1
        have hse8 : scratchEnd + 8 < 2 ^ 64 := by decide
        have hrn8_nat : (w_rn + 8#64).toNat = w_rn.toNat + 8 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          have h8 : 8 < 2 ^ 64 := by decide
          rw [Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt (by omega)]
        have hloc_n : locN ent "n" = w_rn.toNat + 8 := by
          unfold locN
          dsimp only [ent, callEntryStateHOLFinite, callee]
          rw [HolFiniteMapExact.lookup_update]
          simp [FUPDATE, hrn8_nat]
        have hq_ge : p.toNat + w_rn.toNat ≤ q.toNat := by
          rw [hq_eq, hloc_n]; omega
        have hs_al_hp : globN s_al "heap_ptr" = q.toNat := hpost_hp
        have hs_al_fmp : globN s_al "frame_mem_ptr" = globN s "frame_mem_ptr" := by
          unfold globN
          dsimp only [s_al, setVarHOLFinite]
          rw [hpost_g, HolFiniteMapExact.lookup_update]
          simp only [FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide, ↓reduceIte]
          rfl
        have hs_al_sp : globN s_al "scratch_ptr" = globN s "scratch_ptr" := hpost_sp
        have hwk_al : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"] stdKeep
            (RetAvoids (fun st _ w => [(w, (locN st "n" + 7) / 8 * 8)])) (ofString "alloc") :=
          R13Shards.wk_alloc_impl
        have hnt_al : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc)).1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro h; cases h
        have hspec_al := FunSpec.at_lookup hwk_al s hc [.val (.word (w_rn + 8#64))]
          (sourceFnBody Guest.Software.guestFn_alloc) callee .one hlk hWent hnt_al
        simp only [ent, hrun] at hspec_al
        have hws_al := hspec_al (Or.inl ⟨.val (.word p), rfl⟩)
        obtain ⟨_, _, _, _, hW_al⟩ := hws_al
        have hA_al : ArenaReady s_al :=
          localsFree_arenaReady post (s.locals.update (ofString "system_ret", .val (.word p))) post.clock hA_post
        have hG_al : GlobalsKept sysTxGlobals s_pmc s_al := by
          intro k hk
          have hk_hp : ofString "heap_ptr" ≠ k := fun h => by
            subst h; exact hk (by simp [sysTxGlobals])
          dsimp only [s_al, setVarHOLFinite]
          rw [hpost_g, HolFiniteMapExact.lookup_update]
          simp only [FUPDATE, beq_iff_eq, hk_hp, Bool.false_eq_true, ↓reduceIte]
          exact hG k hk
        have hmemW_eq : ∀ addr, memW s_al addr = memW s addr := by
          intro addr
          unfold memW
          change (post.memory _).1.toNat = (s.memory _).1.toNat
          rw [hpost_m]; rfl
        have hK_al : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st)
            sysTxKeep s_pmc s_al := by
          intro rec hrec hnz off hoff hno
          rw [hmemW_eq]
          exact hK rec hrec hnz off hoff hno
        have hw_out_al : WordsOK s_al (w_out.toNat, 96) :=
          InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hA_al.1 hw_out
        have hin_out_al : Inside (w_out.toNat, 96) (globN s_pmc "heap_ptr") (globN s_al "heap_ptr") :=
          ⟨hin_out.1, le_trans hin_out.2 (by rw [hs_al_hp, ← hp_s]; exact hp_le_q)⟩
        have hmk_al : memW s_al (w_out.toNat + 80) ≠ 0 →
            memW s_al (w_out.toNat + 80) = globN s_pmc "scratch_ptr" ∧
            memW s_al (w_out.toNat + 88) = globN s_pmc "frame_mem_ptr" ∧
            memW s_al (w_out.toNat + 48) ≤ scratchEnd := by
          rw [hmemW_eq (w_out.toNat + 80), hmemW_eq (w_out.toNat + 88), hmemW_eq (w_out.toNat + 48)]
          exact hmk
        have hstep_al : SysTxPostPmcStepWith s_pmc none s_al w_m w_out [(p.toNat, w_rn.toNat)] := by
          refine ⟨hA_al, le_trans hhp (by rw [hs_al_hp, ← hp_s]; exact hp_le_q),
            by rw [hs_al_fmp]; exact hfmp,
            by rw [hs_al_sp]; exact hsp,
            hG_al, hK_al, hw_out_al, hin_out_al, hmk_al,
            fun S Nd hWT_pmc hm152' hm160' hD_pmc => ?_⟩
          obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, hd_out1⟩ :=
            hW S Nd hWT_pmc hm152' hm160' hD_pmc
          have hWT1_ent : WorldTypedWith ent S1 Nd1 :=
            ⟨(tablesTyped_with_locals s callee (s.clock - 1) S1).2 hWT1.1,
              hWT1.2.1, hWT1.2.2.1, hWT1.2.2.2.1, hWT1.2.2.2.2.1, hWT1.2.2.2.2.2⟩
          obtain ⟨S2, Nd2, hsub12, hWT2_p, hOG12_p, _, hret_al⟩ :=
            hW_al S1 Nd1 hWT1_ent (fun i hi => by simp at hi)
          have hWT2 : WorldTypedWith s_al S2 Nd2 :=
            ⟨(tablesTyped_with_locals post (s.locals.update (ofString "system_ret", .val (.word p))) post.clock S2).2 hWT2_p.1,
              hWT2_p.2.1, hWT2_p.2.2.1, hWT2_p.2.2.2.1, hWT2_p.2.2.2.2.1, hWT2_p.2.2.2.2.2⟩
          have hOG12 : OwnedGrows s s_al (worldOwned s S1 Nd1) (worldOwned s_al S2 Nd2) := hOG12_p
          have hFO02 : FrameOutside s_pmc s_al
              (worldOwned s_pmc S Nd ++ ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc) ++ [freeGap s_pmc])
              (heapFree s_pmc) := by
            intro a ha hhf
            dsimp only [s_al, setVarHOLFinite]
            rw [hpost_m]
            exact hFO01 a ha hhf
          obtain ⟨w_ret, hw_ret_eq, hav_p⟩ := hret_al (.val (.word p)) rfl
          have hw_ret_p : w_ret = p := by
            injection hw_ret_eq with h1
            injection h1 with h2
            exact h2.symm
          subst w_ret
          refine ⟨S2, Nd2, fun t ht => hsub12 t (hsub01 t ht), hWT2,
            ownedGrows_trans_sysTx hhp (by rw [hs_al_hp, ← hp_s]; exact hp_le_q) hOG01 hOG12,
            hFO02, ?_⟩
          intro i hi o ho
          rcases List.mem_cons.1 hi with rfl | hi_sr
          · rcases hOG12 o ho with rfl | ⟨j, hj, hin_oj⟩ | hfresh
            · exact InitECandidate.Solver.Wave8Contracts.M08.disj_zero_right _
            · exact InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hin_oj
                (hd_out1 (w_out.toNat, 96) (by simp) j hj)
            · exact Or.inr (Or.inr (Or.inl (le_trans hin_out.2 hfresh.1)))
          · simp only [List.mem_singleton] at hi_sr; subst i
            have hd_alloc : Disj (p.toNat, (locN ent "n" + 7) / 8 * 8) o :=
              hav_p (p.toNat, (locN ent "n" + 7) / 8 * 8) (by simp [ent]) o ho
            refine InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left ?_ hd_alloc
            rw [hloc_n]
            exact ⟨le_rfl, by dsimp only; omega⟩
        have hin_sr : Inside (p.toNat, w_rn.toNat) (globN s_pmc "heap_ptr") (globN s_al "heap_ptr") :=
          ⟨by rw [hp_s]; exact hhp, by rw [hs_al_hp]; exact hq_ge⟩
        have hdisj_sr_out : Disj (w_out.toNat, 96) (p.toNat, w_rn.toNat) :=
          Or.inr (Or.inr (Or.inl (by rw [hp_s]; exact hin_out.2)))
        have hnt_seq : (evaluateHOLFiniteState s_al sysTxCopyRetSeqProg).1 ≠ some .timeOut := by
          simpa [s_al] using hnt
        have hfr_seq : FlowingOrResumes (evaluateHOLFiniteState s_al sysTxCopyRetSeqProg).1 := by
          simpa [s_al] using hfr
        obtain ⟨s_seq, hseq_eq, hseq_loc, hseq_code, hseq_step, hseq_88⟩ :=
          sysTxCopyRetSeqProg_step hW0 hA_pmc hmt hm152 hm160 hs_al_code hstep_al
            hs_al_out hs_al_sr hs_al_rn hp8 hin_sr hdisj_sr_out hnt_seq hfr_seq
        let s_body : PanSemStateFiniteExact 64 F :=
          { s_seq with locals := HolFiniteMapExact.resVarEq s_seq.locals (ofString "system_ret", s.locals.lookup (ofString "system_ret")) }
        refine ⟨s_body, ?_, ?_, hseq_code, ?_, hseq_88.trans (hmemW_eq (w_out.toNat + 88))⟩
        · dsimp only [s_al] at hseq_eq
          rw [hseq_eq]
        · intro k hk
          dsimp only [s_body]
          have hres_ne : (HolFiniteMapExact.resVarEq s_seq.locals
              (ofString "system_ret", s.locals.lookup (ofString "system_ret"))).lookup k =
              s_seq.locals.lookup k := by
            cases s.locals.lookup (ofString "system_ret") <;>
              simp [HolFiniteMapExact.resVarEq, FDOMSUB_HOL, FUPDATE_HOL, hk, Ne.symm hk]
          rw [hres_ne, hseq_loc]
          exact hs_al_loc_other k hk
        · obtain ⟨hA_sq, hhp_sq, hfmp_sq, hsp_sq, hG_sq, hK_sq, hw_sq, hin_sq, hmk_sq, hW_sq⟩ := hseq_step
          have hA_bd : ArenaReady s_body :=
            localsFree_arenaReady s_seq s_body.locals s_seq.clock hA_sq
          have hw_bd : WordsOK s_body (w_out.toNat, 96) :=
            InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hA_sq.1 hA_bd.1 hw_sq
          refine ⟨hA_bd, hhp_sq, hfmp_sq, hsp_sq, hG_sq, hK_sq, hw_bd, hin_sq, hmk_sq,
            fun S Nd hWT_pmc hm152' hm160' hD_pmc => ?_⟩
          obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hd_out⟩ :=
            hW_sq S Nd hWT_pmc hm152' hm160' hD_pmc
          have hWT_b : WorldTypedWith s_body S' Nd' :=
            ⟨(tablesTyped_with_locals s_seq s_body.locals s_seq.clock S').2 hWT'.1,
              hWT'.2.1, hWT'.2.2.1, hWT'.2.2.2.1, hWT'.2.2.2.2.1, hWT'.2.2.2.2.2⟩
          exact ⟨S', Nd', hsub, hWT_b, hOG, hFO, hd_out⟩

theorem worldStep_of_msgTables_and_postPmc {F : Type}
    {s0 s_pmc post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {w_m w_aa w_ak : BitVec 64}
    (hW0 : WorldOK s0)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hA_post : ArenaReady post)
    (hhp_post : globN s_pmc "heap_ptr" ≤ globN post "heap_ptr")
    (hG_post : GlobalsKept sysTxGlobals s_pmc post)
    (hK_post : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) sysTxKeep s_pmc post)
    (hW_post : ∀ S Nd,
      WorldTypedWith s_pmc S Nd →
      memW s_pmc (w_m.toNat + 152) ∈ S →
      memW s_pmc (w_m.toNat + 160) ∈ S →
      IvlsDisj ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc) (worldTypedIvls s_pmc S Nd) →
      ∃ S' Nd',
        (∀ t ∈ S, t ∈ S') ∧
        WorldTypedWith post S' Nd' ∧
        OwnedGrows s_pmc post (worldOwned s_pmc S Nd) (worldOwned post S' Nd') ∧
        FrameOutside s_pmc post
          (worldOwned s_pmc S Nd ++ ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc) ++ [freeGap s_pmc])
          (heapFree s_pmc)) :
    WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s0 r post := by
  obtain ⟨hA0, S0w, hS0w⟩ := hW0
  obtain ⟨Nd0w, hWT0w⟩ := (worldTyped_iff_with s0 S0w).1 hS0w
  have hF0 := hWT0w.2.2.1
  obtain ⟨hp_mt, hm8, hin_m, htabs_step⟩ := hmt
  have hbuf_eq : bufRegions sysTxBufs s_pmc = bufRegions sysTxBufs s0 :=
    bufRegions_sysTx_eq_of_prefix hp_mt
  obtain ⟨⟨hA_pmc, hhp01, hG01, hK01, _⟩, hfmp01, hsp01, _, _⟩ := hp_mt
  have hfmp_sp0 : globN s0 "frame_mem_ptr" ≤ globN s0 "scratch_ptr" := hA0.2.2.2.2.1
  have hfmp_sp_pmc : globN s_pmc "frame_mem_ptr" ≤ globN s_pmc "scratch_ptr" := hA_pmc.2.2.2.2.1
  have hhp_pmc_lim : globN s_pmc "heap_ptr" ≤ heapLimit := hA_pmc.2.2.1
  refine ⟨hA_post, le_trans hhp01 hhp_post,
    fun k hk => (hG01 k hk).trans (hG_post k hk), ?_, ?_⟩
  · intro rec hrec hnz off hoff hno
    have hg_rec : globN s_pmc rec.1 = globN s0 rec.1 := by
      simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · exact globN_eq_of_lookup (hG01 (ofString "ws") (by decide))
      · exact globN_eq_of_lookup (hG01 (ofString "bs") (by decide))
      · cases hoff
      · exact globN_eq_of_lookup (hG01 (ofString "bo") (by decide))
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ off % 8 = 0 ∧ off + 8 ≤ sz := by
      simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl | rfl | rfl <;> omega
      · refine ⟨80, by simp [typedRecords], ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · cases hoff
      · refine ⟨88, by simp [typedRecords], ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    obtain ⟨sz, htr, hoff8, hoff_sz⟩ := hrec_sz
    have hmf : (globN s0 rec.1, sz) ∈ fixedObjects s0 := by
      have hm := typedRecord_mem_fixedObjects s0 htr
      simpa [hnz] using hm
    rcases hF0.1 _ hmf with h0 | ⟨hal, hwords⟩
    · omega
    · have hg8 : globN s0 rec.1 % 8 = 0 := hwords.1
      have hdisj_m : Disj (globN s0 rec.1, sz) (w_m.toNat, 176) := by
        rcases hal with hheap | hscr
        · exact Or.inr (Or.inr (Or.inl (le_trans hheap.2 hin_m.1)))
        · have hsep : heapLimit ≤ scratchStart := by decide
          have := hA0.2.2.2.1; have := hA0.2.2.2.2.1
          exact Or.inr (Or.inr (Or.inr (by dsimp only [Inside] at hin_m hscr ⊢; omega)))
      have hno_pmc : ∀ i ∈ (w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc,
          ¬ CellHits (globN s_pmc rec.1 + off) i := by
        intro i hi
        rw [hg_rec]
        rcases List.mem_cons.1 hi with rfl | hi_buf
        · exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj
            (i := (globN s0 rec.1, sz)) (by omega) hm8 ⟨by omega, by omega⟩ hdisj_m
        · rw [hbuf_eq] at hi_buf
          exact hno i hi_buf
      have h2 := hK_post rec hrec (by rw [hg_rec]; exact hnz) off hoff hno_pmc
      rw [hg_rec] at h2
      exact h2.trans (hK01 rec hrec hnz off hoff hno)
  · intro S0 Nd0 hWT0 hD0
    obtain ⟨S_pmc, Nd_pmc, hsub01, hWT_pmc, hOG01, hFO01, hdisj_m, htabs⟩ :=
      htabs_step S0 Nd0 hWT0 hD0
    obtain ⟨haa_S, _, _⟩ := htabs (w_aa.toNat, 20) (by simp)
    obtain ⟨hak_S, _, _⟩ := htabs (w_ak.toNat, 52) (by simp)
    have hD_pmc : IvlsDisj ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc)
        (worldTypedIvls s_pmc S_pmc Nd_pmc) := by
      intro i hi j hj
      rcases List.mem_cons.1 hi with rfl | hi_buf
      · exact hdisj_m (w_m.toNat, 176) (by simp) j
          (worldTypedIvls_sub_worldOwned_sysTx s_pmc S_pmc Nd_pmc j hj)
      · exact validBufList_disj validBufList_sysTxBufs hWT_pmc i hi_buf j hj
    obtain ⟨S', Nd', hsub12, hWT', hOG12, hFO12⟩ :=
      hW_post S_pmc Nd_pmc hWT_pmc (by rw [hm152]; exact haa_S)
        (by rw [hm160]; exact hak_S) hD_pmc
    refine ⟨S', Nd', fun t ht => hsub12 t (hsub01 t ht), hWT',
      ownedGrows_trans_sysTx hhp01 hhp_post hOG01 hOG12, ?_, trivial⟩
    intro a ha hhf0
    have hm01 : s_pmc.memory a = s0.memory a := hFO01 a ha hhf0
    have hm12 : post.memory a = s_pmc.memory a := by
      apply hFO12 a
      · intro i hi ⟨hc1, hc2⟩
        rcases List.mem_append.1 hi with hi1 | hfg1
        · rcases List.mem_append.1 hi1 with hwo1 | hR1
          · rcases hOG01 i hwo1 with rfl | ⟨k, hk, hin_ik⟩ | hin_i01
            · dsimp only at hc2; omega
            · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                ⟨by dsimp only [Inside] at hin_ik; omega,
                 by dsimp only [Inside] at hin_ik; omega⟩
            · exact hhf0 ⟨by unfold heapFree; dsimp only [Inside] at hin_i01 ⊢; omega,
                         by unfold heapFree; dsimp only [Inside] at hin_i01 ⊢; omega⟩
          · rcases List.mem_cons.1 hR1 with rfl | hbuf1
            · exact hhf0 ⟨by unfold heapFree; dsimp only [Inside] at hin_m ⊢; omega,
                         by unfold heapFree; dsimp only [Inside] at hin_m ⊢; omega⟩
            · rw [hbuf_eq] at hbuf1
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hbuf1)) ⟨hc1, hc2⟩
        · simp only [List.mem_singleton] at hfg1
          subst hfg1
          exact ha (freeGap s0) (List.mem_append_right _ (List.mem_singleton.2 rfl))
            ⟨by
              have hc1' : a.toNat + 8 > globN s_pmc "frame_mem_ptr" := hc1
              change a.toNat + 8 > globN s0 "frame_mem_ptr"; omega,
             by
              have hc2' : a.toNat < globN s_pmc "frame_mem_ptr" + (globN s_pmc "scratch_ptr" - globN s_pmc "frame_mem_ptr") := hc2
              change a.toNat < globN s0 "frame_mem_ptr" + (globN s0 "scratch_ptr" - globN s0 "frame_mem_ptr")
              omega⟩
      · intro ⟨hc1, hc2⟩
        exact hhf0 ⟨by
          have hc1' : a.toNat + 8 > globN s_pmc "heap_ptr" := hc1
          change a.toNat + 8 > globN s0 "heap_ptr"; omega,
         by
          have hc2' : a.toNat < globN s_pmc "heap_ptr" + (heapLimit - globN s_pmc "heap_ptr") := hc2
          change a.toNat < globN s0 "heap_ptr" + (heapLimit - globN s0 "heap_ptr")
          omega⟩
    exact hm12.trans hm01

theorem worldStep_of_sysTxPostPmcStep {F : Type}
    {s0 s_pmc post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {w_m w_aa w_ak w_out : BitVec 64}
    (hW0 : WorldOK s0)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hpost : SysTxPostPmcStep s_pmc r post w_m w_out) :
    WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s0 r post := by
  obtain ⟨hA_post, hhp_post, _, _, hG_post, hK_post, _, _, _, hW_post⟩ := hpost
  exact worldStep_of_msgTables_and_postPmc hW0 hmt hm152 hm160 hA_post hhp_post hG_post hK_post
    (fun S Nd hWT hm152' hm160' hD =>
      let ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hW_post S Nd hWT hm152' hm160' hD
      ⟨S', Nd', hsub, hWT', hOG, hFO⟩)

theorem pmcSysTxBufs_sub_sysTxBufs : ∀ p ∈ pmcSysTxBufs, p ∈ sysTxBufs := by
  intro p hp
  simp only [pmcSysTxBufs, sysTxBufs, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem pmcSysTxGlobals_sub_sysTxGlobals : ∀ g ∈ pmcSysTxGlobals, g ∈ sysTxGlobals := by
  intro g hg
  simp only [pmcSysTxGlobals, sysTxGlobals, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem incSysTxBufs_sub_sysTxBufs : ∀ p ∈ incSysTxBufs, p ∈ sysTxBufs := by
  intro p hp
  simp only [incSysTxBufs, sysTxBufs, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp

theorem validBufList_incSysTxBufs : ValidBufList incSysTxBufs :=
  fun p hp => validBufList_sysTxBufs p (incSysTxBufs_sub_sysTxBufs p hp)

theorem incSysTxGlobals_sub_sysTxGlobals : ∀ g ∈ incSysTxGlobals, g ∈ sysTxGlobals := by
  intro g hg
  simp only [incSysTxGlobals, sysTxGlobals, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
  rcases hg with rfl | rfl <;> simp

theorem keepSub_sysTxKeep_pmcSysTxKeep : KeepSub sysTxKeep pmcSysTxKeep := by
  intro r hr
  simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨[0, 8, 16, 24, 32], by simp [pmcSysTxKeep], fun _ h => h⟩
  · exact ⟨[0, 8, 16, 24, 32, 40, 48, 72], by simp [pmcSysTxKeep], fun _ h => h⟩
  · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64], by simp [pmcSysTxKeep], fun _ h => by cases h⟩
  · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80], by simp [pmcSysTxKeep], fun _ h => h⟩

theorem pmc_lookup_msg_sysTx
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {body' : ProgHOL 64} {ret' : ShapeHOL} {w_m : BitVec 64}
    (hlk' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "process_message_call")
      [.val (.word w_m)] = some (body', callee, ret')) :
    callee.lookup (ofString "msg") = some (.val (.word w_m)) := by
  obtain ⟨b_pmc, hpmc_lk⟩ : ∃ b_pmc, originalRuntimeCode.lookup (ofString "process_message_call") =
      some ([(ofString "msg", .one)], b_pmc, .one) :=
    ⟨_, GuestTrapAndLookup.lookup_process_message_call⟩
  have hpan := pan_one_word_lookup originalRuntimeCode.lookup (ofString "process_message_call")
    (ofString "msg") b_pmc w_m hpmc_lk
  rw [hpan] at hlk'
  injection hlk' with htuple
  injection htuple with _ hrest
  injection hrest with hcal _
  rw [← hcal]
  simp [HolFiniteMapExact.lookup_update, FUPDATE]

theorem pmc_sysTx_exc_worldStep {F : Type}
    {s0 s_pmc cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {w_m w_aa w_ak : BitVec 64} {eid : MlS} {ev : ValueHOL 64}
    (hW0 : WorldOK s0)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hl_msg : callee.lookup (ofString "msg") = some (.val (.word w_m)))
    (hwstep : WorldStepIn
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) :: bufRegions pmcSysTxBufs s)
      pmcSysTxGlobals pmcSysTxKeep RetSysTxPmc
      (callEntryStateHOLFinite s_pmc callee) (some (.exception eid ev)) cpost) :
    WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s0
      (some (.exception eid ev)) (emptyLocalsHOLFinite cpost) := by
  let ent := callEntryStateHOLFinite s_pmc callee
  have hloc_msg : locN ent "msg" = w_m.toNat := by
    simp [ent, callEntryStateHOLFinite, decClockHOLFinite, locN, hl_msg]
  have hsubR : ∀ i ∈ (locN ent "msg", 176) :: bufRegions pmcSysTxBufs ent,
      i ∈ (w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc := by
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi_buf
    · rw [hloc_msg]; exact List.mem_cons_self ..
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi_buf
      exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨p, pmcSysTxBufs_sub_sysTxBufs p hp, rfl⟩)
  obtain ⟨hA_cp, hhp_cp, hG_cp, hK_cp, hW_cp⟩ := hwstep
  set post_ex : PanSemStateFiniteExact 64 F := emptyLocalsHOLFinite cpost
  have hA_ex : ArenaReady post_ex := localsFree_arenaReady cpost HolFiniteMapExact.empty cpost.clock hA_cp
  have hG_ex : GlobalsKept sysTxGlobals s_pmc post_ex := by
    intro k hk'
    apply hG_cp k
    intro hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk' (List.mem_map.2 ⟨g, pmcSysTxGlobals_sub_sysTxGlobals g hg, rfl⟩)
  have hK_ex : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) sysTxKeep s_pmc post_ex := by
    have hK1 : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) pmcSysTxKeep s_pmc post_ex :=
      fun rec hrec hnz off hoff hno =>
        hK_cp rec hrec hnz off hoff (fun i hi => hno i (hsubR i hi))
    exact recordsKept_mono_keep keepSub_sysTxKeep_pmcSysTxKeep hK1
  refine worldStep_of_msgTables_and_postPmc hW0 hmt hm152 hm160 hA_ex hhp_cp hG_ex hK_ex
    (fun S Nd hWT hm152' hm160' hD => ?_)
  have hWT_ent : WorldTypedWith ent S Nd :=
    ⟨(tablesTyped_with_locals s_pmc callee (s_pmc.clock - 1) S).2 hWT.1,
      hWT.2.1, hWT.2.2.1, hWT.2.2.2.1, hWT.2.2.2.2.1, hWT.2.2.2.2.2⟩
  have hTS_ent : ∀ t ∈ [memW ent (locN ent "msg" + 152), memW ent (locN ent "msg" + 160)], t ∈ S := by
    intro t ht
    rw [hloc_msg] at ht
    change t ∈ [memW s_pmc (w_m.toNat + 152), memW s_pmc (w_m.toNat + 160)] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hm152'
    · exact hm160'
  have hD_ent : IvlsDisj ((locN ent "msg", 176) :: bufRegions pmcSysTxBufs ent)
      (worldTypedIvls ent S Nd) :=
    fun i hi j hj => hD i (hsubR i hi) j hj
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hW_cp S Nd hWT_ent hTS_ent hD_ent
  have hWT_ex : WorldTypedWith post_ex S' Nd' :=
    ⟨(tablesTyped_with_locals cpost HolFiniteMapExact.empty cpost.clock S').2 hWT'.1,
      hWT'.2.1, hWT'.2.2.1, hWT'.2.2.2.1, hWT'.2.2.2.2.1, hWT'.2.2.2.2.2⟩
  have hFO_ex : FrameOutside s_pmc post_ex
      (worldOwned s_pmc S Nd ++ ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc) ++ [freeGap s_pmc])
      (heapFree s_pmc) := by
    intro a ha hhf
    apply hFO a _ hhf
    intro i hi
    rcases List.mem_append.1 hi with hi1 | hfg
    · rcases List.mem_append.1 hi1 with hwo | hR
      · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo))
      · exact ha i (List.mem_append_left _ (List.mem_append_right _ (hsubR i hR)))
    · exact ha i (List.mem_append_right _ hfg)
  exact ⟨S', Nd', hsub, hWT_ex, hOG, hFO_ex⟩

theorem pmc_sysTx_ret_postStep {F : Type}
    {s0 s_pmc cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {w_m w_aa w_ak : BitVec 64} {v : ValueHOL 64}
    (hW0 : WorldOK s0)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hl_msg : callee.lookup (ofString "msg") = some (.val (.word w_m)))
    (hwstep : WorldStepIn
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) :: bufRegions pmcSysTxBufs s)
      pmcSysTxGlobals pmcSysTxKeep RetSysTxPmc
      (callEntryStateHOLFinite s_pmc callee) (some (.returned v)) cpost) :
    ∃ w_out : BitVec 64,
      v = .val (.word w_out) ∧
      SysTxPostPmcStep s_pmc none
        (setVarHOLFinite (ofString "out") (.val (.word w_out)) { cpost with locals := s_pmc.locals })
        w_m w_out := by
  let ent := callEntryStateHOLFinite s_pmc callee
  have hloc_msg : locN ent "msg" = w_m.toNat := by
    simp [ent, callEntryStateHOLFinite, decClockHOLFinite, locN, hl_msg]
  have hsubR : ∀ i ∈ (locN ent "msg", 176) :: bufRegions pmcSysTxBufs ent,
      i ∈ (w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc := by
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi_buf
    · rw [hloc_msg]; exact List.mem_cons_self ..
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi_buf
      exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨p, pmcSysTxBufs_sub_sysTxBufs p hp, rfl⟩)
  obtain ⟨hA_cp, hhp_cp, hG_cp, hK_cp, hW_cp⟩ := hwstep
  obtain ⟨_, S0w, hS0w⟩ := hW0
  obtain ⟨Nd0w, hWT0w⟩ := (worldTyped_iff_with s0 S0w).1 hS0w
  obtain ⟨_, _, _, htabs_step⟩ := hmt
  obtain ⟨S_p, Nd_p, _, hWT_p, _, _, hdisj_m_p, htabs_p⟩ :=
    htabs_step S0w Nd0w hWT0w (validBufList_disj validBufList_sysTxBufs hWT0w)
  obtain ⟨haa_Sp, _, _⟩ := htabs_p (w_aa.toNat, 20) (by simp)
  obtain ⟨hak_Sp, _, _⟩ := htabs_p (w_ak.toNat, 52) (by simp)
  have hWT_ent0 : WorldTypedWith ent S_p Nd_p :=
    ⟨(tablesTyped_with_locals s_pmc callee (s_pmc.clock - 1) S_p).2 hWT_p.1,
      hWT_p.2.1, hWT_p.2.2.1, hWT_p.2.2.2.1, hWT_p.2.2.2.2.1, hWT_p.2.2.2.2.2⟩
  have hTS_ent0 : ∀ t ∈ [memW ent (locN ent "msg" + 152), memW ent (locN ent "msg" + 160)], t ∈ S_p := by
    intro t ht
    rw [hloc_msg] at ht
    change t ∈ [memW s_pmc (w_m.toNat + 152), memW s_pmc (w_m.toNat + 160)] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · rw [hm152]; exact haa_Sp
    · rw [hm160]; exact hak_Sp
  have hD_p : IvlsDisj ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc)
      (worldTypedIvls s_pmc S_p Nd_p) := by
    intro i hi j hj
    rcases List.mem_cons.1 hi with rfl | hi_buf
    · exact hdisj_m_p (w_m.toNat, 176) (by simp) j
        (worldTypedIvls_sub_worldOwned_sysTx s_pmc S_p Nd_p j hj)
    · exact validBufList_disj validBufList_sysTxBufs hWT_p i hi_buf j hj
  have hD_ent0 : IvlsDisj ((locN ent "msg", 176) :: bufRegions pmcSysTxBufs ent)
      (worldTypedIvls ent S_p Nd_p) :=
    fun i hi j hj => hD_p i (hsubR i hi) j hj
  obtain ⟨_, _, _, _, _, _, hret0⟩ := hW_cp S_p Nd_p hWT_ent0 hTS_ent0 hD_ent0
  obtain ⟨hrmo0, hfmp_cp, hsp_cp, hextra0⟩ := hret0
  obtain ⟨w_out, hv_eq, hw_out_cp, _, _, _⟩ := hrmo0 v rfl
  obtain ⟨w_out', hv_eq', hin_out_cp, hmk_cp⟩ := hextra0 v rfl
  have hw_eq : w_out' = w_out := by
    rw [hv_eq] at hv_eq'
    injection hv_eq' with h1
    injection h1 with h2
    exact h2.symm
  cases hw_eq
  subst hv_eq
  set s1 : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "out") (.val (.word w_out)) { cpost with locals := s_pmc.locals }
  have hA_s1 : ArenaReady s1 := localsFree_arenaReady cpost s1.locals cpost.clock hA_cp
  have hw_out_s1 : WordsOK s1 (w_out.toNat, 96) :=
    InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hA_cp.1 hA_s1.1 hw_out_cp
  have hG_s1 : GlobalsKept sysTxGlobals s_pmc s1 := by
    intro k hk'
    apply hG_cp k
    intro hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk' (List.mem_map.2 ⟨g, pmcSysTxGlobals_sub_sysTxGlobals g hg, rfl⟩)
  have hK_s1 : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) sysTxKeep s_pmc s1 := by
    have hK1 : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) pmcSysTxKeep s_pmc s1 :=
      fun rec hrec hnz off hoff hno =>
        hK_cp rec hrec hnz off hoff (fun i hi => hno i (hsubR i hi))
    exact recordsKept_mono_keep keepSub_sysTxKeep_pmcSysTxKeep hK1
  refine ⟨w_out, rfl, hA_s1, hhp_cp, hfmp_cp, hsp_cp, hG_s1, hK_s1, hw_out_s1, hin_out_cp, hmk_cp,
    fun S Nd hWT hm152' hm160' hD => ?_⟩
  have hWT_ent : WorldTypedWith ent S Nd :=
    ⟨(tablesTyped_with_locals s_pmc callee (s_pmc.clock - 1) S).2 hWT.1,
      hWT.2.1, hWT.2.2.1, hWT.2.2.2.1, hWT.2.2.2.2.1, hWT.2.2.2.2.2⟩
  have hTS_ent : ∀ t ∈ [memW ent (locN ent "msg" + 152), memW ent (locN ent "msg" + 160)], t ∈ S := by
    intro t ht
    rw [hloc_msg] at ht
    change t ∈ [memW s_pmc (w_m.toNat + 152), memW s_pmc (w_m.toNat + 160)] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hm152'
    · exact hm160'
  have hD_ent : IvlsDisj ((locN ent "msg", 176) :: bufRegions pmcSysTxBufs ent)
      (worldTypedIvls ent S Nd) :=
    fun i hi j hj => hD i (hsubR i hi) j hj
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hret_S⟩ := hW_cp S Nd hWT_ent hTS_ent hD_ent
  obtain ⟨w_out2, hv2, _, _, hd_out2, _⟩ := hret_S.1 (.val (.word w_out)) rfl
  have hw2 : w_out2 = w_out := by
    injection hv2 with h1
    injection h1 with h2
    exact h2.symm
  subst hw2
  have hWT_s1 : WorldTypedWith s1 S' Nd' :=
    ⟨(tablesTyped_with_locals cpost s1.locals cpost.clock S').2 hWT'.1,
      hWT'.2.1, hWT'.2.2.1, hWT'.2.2.2.1, hWT'.2.2.2.2.1, hWT'.2.2.2.2.2⟩
  have hFO_s1 : FrameOutside s_pmc s1
      (worldOwned s_pmc S Nd ++ ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc) ++ [freeGap s_pmc])
      (heapFree s_pmc) := by
    intro a ha hhf
    apply hFO a _ hhf
    intro i hi
    rcases List.mem_append.1 hi with hi1 | hfg
    · rcases List.mem_append.1 hi1 with hwo | hR
      · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo))
      · exact ha i (List.mem_append_left _ (List.mem_append_right _ (hsubR i hR)))
    · exact ha i (List.mem_append_right _ hfg)
  exact ⟨S', Nd', hsub, hWT_s1, hOG, hFO_s1, hd_out2⟩

theorem pmc_decCall_sysTx_step {F : Type}
    {s0 s_pmc : PanSemStateFiniteExact 64 F}
    {w_m w_aa w_ak : BitVec 64} {cont : ProgHOL 64}
    (hW0 : WorldOK s0)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (_hW_pmc : WorldOK s_pmc)
    (hc_pmc : s_pmc.code = originalRuntimeCode)
    (hl_m : s_pmc.locals.lookup (ofString "m") = some (.val (.word w_m)))
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hmsg : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      callee.lookup (ofString "msg") = some (.val (.word w_m)) →
      MsgReady (callEntryStateHOLFinite s_pmc callee))
    (hpmc : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) :: bufRegions pmcSysTxBufs s)
      pmcSysTxGlobals pmcSysTxKeep RetSysTxPmc (ofString "process_message_call"))
    (hnt : (evaluateHOLFiniteState s_pmc
      (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] cont)).1 ≠
      some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s_pmc
      (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] cont)).1) :
    (WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s0
      (evaluateHOLFiniteState s_pmc
        (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] cont)).1
      (evaluateHOLFiniteState s_pmc
        (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] cont)).2 ∧
     ∃ e ev, (evaluateHOLFiniteState s_pmc
       (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] cont)).1 =
       some (.exception e ev)) ∨
    ∃ (w_out : BitVec 64) (s1 : PanSemStateFiniteExact 64 F),
      SysTxPostPmcStep s_pmc none s1 w_m w_out ∧
      s1.code = originalRuntimeCode ∧
      s1.locals.lookup (ofString "out") = some (.val (.word w_out)) ∧
      (evaluateHOLFiniteState s1 cont).1 ≠ some .timeOut ∧
      FlowingOrResumes (evaluateHOLFiniteState s1 cont).1 ∧
      (evaluateHOLFiniteState s_pmc
        (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] cont)).1 =
        (evaluateHOLFiniteState s1 cont).1 ∧
      (evaluateHOLFiniteState s_pmc
        (.decCall (ofString "out") .one (ofString "process_message_call") [.var .local (ofString "m")] cont)).2 =
        { (evaluateHOLFiniteState s1 cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals
            (ofString "out", s_pmc.locals.lookup (ofString "out")) } := by
  have hargs : evalListHOLFinite s_pmc (h := fun a => Classical.propDecidable (s_pmc.memaddrs a))
      [.var .local (ofString "m")] = some [.val (.word w_m)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hl_m]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rw [hargs] at hnt hfr ⊢; dsimp only at hnt hfr ⊢
  rcases hlk : lookupCodeHOLFinite s_pmc.code.lookup (ofString "process_message_call")
      [.val (.word w_m)] with _ | ⟨body', callee, ret'⟩
  · simp [hlk] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hlk] at hnt hfr ⊢
    by_cases hz : s_pmc.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt hfr ⊢
      have hlk' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "process_message_call")
          [.val (.word w_m)] = some (body', callee, ret') := by
        simpa [hc_pmc] using hlk
      have hl_msg : callee.lookup (ofString "msg") = some (.val (.word w_m)) :=
        pmc_lookup_msg_sysTx hlk'
      let ent := callEntryStateHOLFinite s_pmc callee
      have hMsg_ent : MsgReady ent := hmsg callee hl_msg
      have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
      rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
      simp only [ent] at hrun hmeta
      simp only [hrun] at hmeta hnt hfr ⊢
      have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
        simp only [ent, hrun]; rintro rfl; simp at hnt
      cases res with
      | none => exact absurd hfr not_flowingOrResumes_error
      | some cr =>
        cases cr with
        | timeOut => simp at hnt
        | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
        | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
        | exception eid ev =>
          left
          dsimp only at hfr ⊢
          have hres_ex : Resumes (some (.exception eid ev)) := by
            rcases hfr with h | h | h | hr <;> try simp at h
            exact hr
          have hspec := FunSpec.at_lookup hpmc s_pmc hc_pmc [.val (.word w_m)] body' callee ret' hlk hMsg_ent hnt_c
          simp only [ent, hrun] at hspec
          exact ⟨pmc_sysTx_exc_worldStep hW0 hmt hm152 hm160 hl_msg (hspec hres_ex), eid, ev, rfl⟩
        | returned v =>
          dsimp only at hnt hfr ⊢
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) .one && shapeEqHOL (shapeOfHOLExact v) ret') = true
          · right
            simp only [hsh, ↓reduceIte] at hnt hfr ⊢
            have hspec := FunSpec.at_lookup hpmc s_pmc hc_pmc [.val (.word w_m)] body' callee ret' hlk hMsg_ent hnt_c
            simp only [ent, hrun] at hspec
            obtain ⟨w_out, hv_eq, hstep_s1⟩ :=
              pmc_sysTx_ret_postStep hW0 hmt hm152 hm160 hl_msg (hspec (Or.inl ⟨v, rfl⟩))
            subst hv_eq
            set s1 : PanSemStateFiniteExact 64 F :=
              setVarHOLFinite (ofString "out") (.val (.word w_out)) { cpost with locals := s_pmc.locals }
            have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hc_pmc
            have hl_out1 : s1.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            exact ⟨w_out, s1, hstep_s1, hs1_code, hl_out1, hnt, hfr, rfl, rfl⟩
          · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error

abbrev RetSysTxIncorporate : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s _ post _ _ =>
    globN post "scratch_ptr" ≤ globN s "scratch_ptr"

theorem bufRegions_incSysTx_eq_of_postPmc {F : Type}
    {s_pmc s : PanSemStateFiniteExact 64 F}
    (hG : GlobalsKept sysTxGlobals s_pmc s) :
    bufRegions incSysTxBufs s = bufRegions incSysTxBufs s_pmc := by
  unfold bufRegions
  apply List.map_congr_left
  intro p hp
  simp only [incSysTxBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · simp [bufferRegion, globN_eq_of_lookup (hG (ofString "bal_key_buf") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG (ofString "keccak_pad") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG (ofString "keccak_st") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG (ofString "mpt_nib_scratch") (by decide))]
  · simp [bufferRegion, globN_eq_of_lookup (hG (ofString "sk_buf") (by decide))]

theorem recordsKept_postPmc_trans_incSysTx {F : Type}
    {s_pmc s1 s2 : PanSemStateFiniteExact 64 F}
    {w_m : BitVec 64}
    (hG01 : GlobalsKept sysTxGlobals s_pmc s1)
    (hK01 : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) sysTxKeep s_pmc s1)
    (hK12 : RecordsKept (bufRegions incSysTxBufs) sysTxKeep s1 s2) :
    RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) sysTxKeep s_pmc s2 := by
  have hbuf_eq : bufRegions incSysTxBufs s1 = bufRegions incSysTxBufs s_pmc :=
    bufRegions_incSysTx_eq_of_postPmc hG01
  intro rec hrec hnz off hoff hno
  have hg_rec : globN s1 rec.1 = globN s_pmc rec.1 := by
    simp only [sysTxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · exact globN_eq_of_lookup (hG01 (ofString "ws") (by decide))
    · exact globN_eq_of_lookup (hG01 (ofString "bs") (by decide))
    · cases hoff
    · exact globN_eq_of_lookup (hG01 (ofString "bo") (by decide))
  have hno1 : ∀ i ∈ bufRegions incSysTxBufs s1, ¬ CellHits (globN s1 rec.1 + off) i := by
    intro i hi
    rw [hbuf_eq] at hi
    rw [hg_rec]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
    exact hno (bufferRegion s_pmc p)
      (List.mem_cons_of_mem _ (List.mem_map.2 ⟨p, incSysTxBufs_sub_sysTxBufs p hp, rfl⟩))
  have h2 := hK12 rec hrec (by rw [hg_rec]; exact hnz) off hoff hno1
  rw [hg_rec] at h2
  exact h2.trans (hK01 rec hrec hnz off hoff hno)

theorem inc_sysTx_exc_worldStep {F : Type}
    {s0 s_pmc s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {w_m w_aa w_ak w_out : BitVec 64} {eid : MlS} {ev : ValueHOL 64}
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hstep : SysTxPostPmcStep s_pmc none s w_m w_out)
    (hwstep : WorldStep (bufRegions incSysTxBufs) incSysTxGlobals sysTxKeep RetSysTxIncorporate
      (callEntryStateHOLFinite s callee) (some (.exception eid ev)) cpost) :
    WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s0
      (some (.exception eid ev)) (emptyLocalsHOLFinite cpost) := by
  let ent := callEntryStateHOLFinite s callee
  obtain ⟨hAs, hhp, hfmp, hsp, hG, hK, _, _, _, hW⟩ := hstep
  obtain ⟨hA_cp, hhp_cp, hG_cp, hK_cp, hW_cp⟩ := hwstep
  set post_ex : PanSemStateFiniteExact 64 F := emptyLocalsHOLFinite cpost
  have hA_ex : ArenaReady post_ex := localsFree_arenaReady cpost HolFiniteMapExact.empty cpost.clock hA_cp
  have hG_ex : GlobalsKept sysTxGlobals s_pmc post_ex := by
    intro k hk
    refine (hG k hk).trans (hG_cp k fun hm => ?_)
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk (List.mem_map.2 ⟨g, incSysTxGlobals_sub_sysTxGlobals g hg, rfl⟩)
  have hK_ex : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) sysTxKeep s_pmc post_ex :=
    recordsKept_postPmc_trans_incSysTx hG hK hK_cp
  have hbuf_eq : bufRegions incSysTxBufs s = bufRegions incSysTxBufs s_pmc :=
    bufRegions_incSysTx_eq_of_postPmc hG
  refine worldStep_of_msgTables_and_postPmc hW0 hmt hm152 hm160 hA_ex (le_trans hhp hhp_cp) hG_ex hK_ex
    (fun S Nd hWT hm152' hm160' hD => ?_)
  obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, _⟩ := hW S Nd hWT hm152' hm160' hD
  have hWT1_ent : WorldTypedWith ent S1 Nd1 :=
    ⟨(tablesTyped_with_locals s callee (s.clock - 1) S1).2 hWT1.1,
      hWT1.2.1, hWT1.2.2.1, hWT1.2.2.2.1, hWT1.2.2.2.2.1, hWT1.2.2.2.2.2⟩
  have hD1_ent : IvlsDisj (bufRegions incSysTxBufs ent) (worldTypedIvls ent S1 Nd1) :=
    validBufList_disj validBufList_incSysTxBufs hWT1_ent
  obtain ⟨S2, Nd2, hsub12, hWT2_cp, hOG12_cp, hFO12_cp, _⟩ := hW_cp S1 Nd1 hWT1_ent hD1_ent
  have hWT2 : WorldTypedWith post_ex S2 Nd2 :=
    ⟨(tablesTyped_with_locals cpost HolFiniteMapExact.empty cpost.clock S2).2 hWT2_cp.1,
      hWT2_cp.2.1, hWT2_cp.2.2.1, hWT2_cp.2.2.2.1, hWT2_cp.2.2.2.2.1, hWT2_cp.2.2.2.2.2⟩
  have hFO_tot : FrameOutside s_pmc post_ex
      (worldOwned s_pmc S Nd ++ ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc) ++ [freeGap s_pmc])
      (heapFree s_pmc) :=
    frameOutside_postPmc_trans_free_writes hA_pmc hAs hhp hfmp hsp hOG01 hFO01 hFO12_cp
      (fun i hi => by
        change i ∈ bufRegions incSysTxBufs s at hi
        rw [hbuf_eq] at hi
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
        exact Or.inl ⟨bufferRegion s_pmc p,
          List.mem_cons_of_mem _ (List.mem_map.2 ⟨p, incSysTxBufs_sub_sysTxBufs p hp, rfl⟩),
          ⟨le_rfl, le_rfl⟩⟩)
  exact ⟨S2, Nd2, fun t ht => hsub12 t (hsub01 t ht), hWT2,
    ownedGrows_trans_sysTx hhp hhp_cp hOG01 hOG12_cp, hFO_tot⟩

theorem inc_sysTx_ret_postStep {F : Type}
    {s0 s_pmc s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {w_m w_aa w_ak w_out : BitVec 64} {v : ValueHOL 64}
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hstep : SysTxPostPmcStep s_pmc none s w_m w_out)
    (hwstep : WorldStep (bufRegions incSysTxBufs) incSysTxGlobals sysTxKeep RetSysTxIncorporate
      (callEntryStateHOLFinite s callee) (some (.returned v)) cpost) :
    SysTxPostPmcStep s_pmc none { cpost with locals := s.locals } w_m w_out := by
  let ent := callEntryStateHOLFinite s callee
  obtain ⟨_, S_u, Nd_u, hWT_u, hd_u⟩ := sysTxPostPmcStep_worldOK hW0 hmt hm152 hm160 hstep
  obtain ⟨hAs, hhp, hfmp, hsp, hG, hK, hw_out, hin_out, hmk, hW⟩ := hstep
  obtain ⟨hA_cp, hhp_cp, hG_cp, hK_cp, hW_cp⟩ := hwstep
  set s_inc : PanSemStateFiniteExact 64 F := { cpost with locals := s.locals }
  have hA_inc : ArenaReady s_inc := localsFree_arenaReady cpost s.locals cpost.clock hA_cp
  have hfmp_inc : globN s_inc "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    globN_eq_of_lookup (s := s) (post := s_inc) (hG_cp (ofString "frame_mem_ptr") (by decide))
  have hG_inc : GlobalsKept sysTxGlobals s_pmc s_inc := by
    intro k hk
    refine (hG k hk).trans (hG_cp k fun hm => ?_)
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk (List.mem_map.2 ⟨g, incSysTxGlobals_sub_sysTxGlobals g hg, rfl⟩)
  have hK_inc : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) sysTxKeep s_pmc s_inc :=
    recordsKept_postPmc_trans_incSysTx hG hK hK_cp
  have hbuf_eq : bufRegions incSysTxBufs s = bufRegions incSysTxBufs s_pmc :=
    bufRegions_incSysTx_eq_of_postPmc hG
  have hWT_u_ent : WorldTypedWith ent S_u Nd_u :=
    ⟨(tablesTyped_with_locals s callee (s.clock - 1) S_u).2 hWT_u.1,
      hWT_u.2.1, hWT_u.2.2.1, hWT_u.2.2.2.1, hWT_u.2.2.2.2.1, hWT_u.2.2.2.2.2⟩
  have hD_u_ent : IvlsDisj (bufRegions incSysTxBufs ent) (worldTypedIvls ent S_u Nd_u) :=
    validBufList_disj validBufList_incSysTxBufs hWT_u_ent
  obtain ⟨S_u', Nd_u', _, _, _, hFO_u, hsp_inc_le⟩ := hW_cp S_u Nd_u hWT_u_ent hD_u_ent
  have hlo_pmc : sourceBase ≤ globN s_pmc "heap_ptr" := hA_pmc.2.1
  have hin_s : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hlo_pmc hin_out.1, hin_out.2⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hin_bound : w_out.toNat + 96 ≤ 2 ^ 64 := by unfold Inside at hin_s; omega
  have hunhit_out : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s s_inc (w_out.toNat, 96) := by
    intro a ha8 ha1 ha2
    apply hFO_u a
    · intro j hj ⟨hc1, hc2⟩
      rcases List.mem_append.1 hj with hj12 | hfg
      · rcases List.mem_append.1 hj12 with hj_ow | hj_R
        · have hj_ow_s : j ∈ worldOwned s S_u Nd_u := hj_ow
          have hd_oj := hd_u (w_out.toNat, 96) (by simp) j hj_ow_s
          rcases j with ⟨j1, j2⟩
          by_cases hj2z : j2 = 0
          · have hj0 := worldOwned_zero_base_sysTx hWT_u hj_ow_s hj2z
            cases hj0
            dsimp only at hc2; omega
          · rcases hd_oj with h0 | h0 | hle | hle <;> dsimp only at * <;> omega
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_R
          have hbr_eq : bufferRegion (callEntryStateHOLFinite s callee) p = bufferRegion s p := rfl
          rw [hbr_eq] at hc1 hc2
          by_cases hgz : globN s p.1 = 0
          · simp [bufferRegion, hgz] at hc2
          · obtain ⟨fsz, hgb, _, hle_sz⟩ := validBufList_incSysTxBufs p hp
            have hp2_pos : 0 < p.2 := by
              simp only [incSysTxBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
            have hm_fo : (globN s p.1, fsz) ∈ worldOwned s S_u Nd_u := by
              apply List.mem_append_left; apply List.mem_append_right
              unfold fixedObjects
              apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              have hm : (fun r : String × Nat => (globN s r.1, if globN s r.1 = 0 then 0 else r.2))
                  (p.1, fsz) ∈
                  globalBuffers.map (fun r => (globN s r.1, if globN s r.1 = 0 then 0 else r.2)) :=
                List.mem_map.2 ⟨(p.1, fsz), hgb, rfl⟩
              simpa [hgz] using hm
            have hd_ob := hd_u (w_out.toNat, 96) (by simp) (globN s p.1, fsz) hm_fo
            simp only [bufferRegion, hgz, ↓reduceIte] at hc1 hc2
            rcases hd_ob with h0 | h0 | hle | hle <;> dsimp only at * <;> omega
      · simp only [List.mem_singleton] at hfg
        subst j
        have hsep : heapLimit ≤ scratchStart := by decide
        have hfmp_ge : scratchStart ≤ globN s "frame_mem_ptr" := hAs.2.2.2.1
        have hfmp_ent : (freeGap (callEntryStateHOLFinite s callee)).1 = globN s "frame_mem_ptr" := rfl
        rw [hfmp_ent] at hc2
        unfold Inside at hin_s
        omega
    · intro ⟨hc1, _⟩
      change a.toNat + 8 > globN s "heap_ptr" at hc1
      unfold Inside at hin_s
      omega
  have hw_out_inc : WordsOK s_inc (w_out.toNat, 96) :=
    InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hA_inc.1 hw_out
  have hm80 : memW s_inc (w_out.toNat + 80) = memW s (w_out.toNat + 80) :=
    InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hunhit_out
      (by have := hw_out.1; omega) hin_bound ⟨by omega, by omega⟩
  have hm88 : memW s_inc (w_out.toNat + 88) = memW s (w_out.toNat + 88) :=
    InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hunhit_out
      (by have := hw_out.1; omega) hin_bound ⟨by omega, by omega⟩
  have hm48 : memW s_inc (w_out.toNat + 48) = memW s (w_out.toNat + 48) :=
    InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hunhit_out
      (by have := hw_out.1; omega) hin_bound ⟨by omega, by omega⟩
  refine ⟨hA_inc, le_trans hhp hhp_cp,
    by rw [hfmp_inc]; exact hfmp,
    le_trans hsp_inc_le hsp,
    hG_inc, hK_inc, hw_out_inc,
    ⟨hin_out.1, le_trans hin_out.2 hhp_cp⟩,
    by rw [hm80, hm88, hm48]; exact hmk,
    fun S Nd hWT hm152' hm160' hD => ?_⟩
  obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, hd_out1⟩ := hW S Nd hWT hm152' hm160' hD
  have hWT1_ent : WorldTypedWith ent S1 Nd1 :=
    ⟨(tablesTyped_with_locals s callee (s.clock - 1) S1).2 hWT1.1,
      hWT1.2.1, hWT1.2.2.1, hWT1.2.2.2.1, hWT1.2.2.2.2.1, hWT1.2.2.2.2.2⟩
  have hD1_ent : IvlsDisj (bufRegions incSysTxBufs ent) (worldTypedIvls ent S1 Nd1) :=
    validBufList_disj validBufList_incSysTxBufs hWT1_ent
  obtain ⟨S2, Nd2, hsub12, hWT2_cp, hOG12_cp, hFO12_cp, _⟩ := hW_cp S1 Nd1 hWT1_ent hD1_ent
  have hWT2 : WorldTypedWith s_inc S2 Nd2 :=
    ⟨(tablesTyped_with_locals cpost s.locals cpost.clock S2).2 hWT2_cp.1,
      hWT2_cp.2.1, hWT2_cp.2.2.1, hWT2_cp.2.2.2.1, hWT2_cp.2.2.2.2.1, hWT2_cp.2.2.2.2.2⟩
  have hFO_tot : FrameOutside s_pmc s_inc
      (worldOwned s_pmc S Nd ++ ((w_m.toNat, 176) :: bufRegions sysTxBufs s_pmc) ++ [freeGap s_pmc])
      (heapFree s_pmc) :=
    frameOutside_postPmc_trans_free_writes hA_pmc hAs hhp hfmp hsp hOG01 hFO01 hFO12_cp
      (fun i hi => by
        change i ∈ bufRegions incSysTxBufs s at hi
        rw [hbuf_eq] at hi
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
        exact Or.inl ⟨bufferRegion s_pmc p,
          List.mem_cons_of_mem _ (List.mem_map.2 ⟨p, incSysTxBufs_sub_sysTxBufs p hp, rfl⟩),
          ⟨le_rfl, le_rfl⟩⟩)
  refine ⟨S2, Nd2, fun t ht => hsub12 t (hsub01 t ht), hWT2,
    ownedGrows_trans_sysTx hhp hhp_cp hOG01 hOG12_cp, hFO_tot, ?_⟩
  intro i hi o ho
  simp only [List.mem_singleton] at hi; subst i
  rcases hOG12_cp o ho with rfl | ⟨j, hj, hin_oj⟩ | hfresh
  · exact InitECandidate.Solver.Wave8Contracts.M08.disj_zero_right _
  · exact InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hin_oj
      (hd_out1 (w_out.toNat, 96) (by simp) j hj)
  · exact Or.inr (Or.inr (Or.inl (le_trans hin_out.2 hfresh.1)))

theorem sysTxPostPmc_incorporate_step {F : Type}
    {s0 s_pmc s : PanSemStateFiniteExact 64 F}
    {w_m w_aa w_ak w_out : BitVec 64}
    (hinc : WorldKeeps WorldOK (bufRegions incSysTxBufs) incSysTxGlobals sysTxKeep
      RetSysTxIncorporate (ofString "incorporate_tx_into_block"))
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hc : s.code = originalRuntimeCode)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hstep : SysTxPostPmcStep s_pmc none s w_m w_out)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "incorporate_tx_into_block") [])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "incorporate_tx_into_block") [])).1) :
    let res := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "incorporate_tx_into_block") [])
    (WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s0 res.1 res.2 ∧
      ∃ eid ev, res.1 = some (.exception eid ev)) ∨
    (res.1 = none ∧
      SysTxPostPmcStep s_pmc none res.2 w_m w_out ∧
      res.2.code = originalRuntimeCode ∧
      res.2.locals.lookup (ofString "out") = some (.val (.word w_out))) := by
  have hWs : WorldOK s := (sysTxPostPmcStep_worldOK hW0 hmt hm152 hm160 hstep).1
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [] = some [] := rfl
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rw [hargs] at hnt hfr ⊢; dsimp only at hnt hfr ⊢
  rcases hlk : lookupCodeHOLFinite s.code.lookup (ofString "incorporate_tx_into_block") [] with
    _ | ⟨body', callee, ret'⟩
  · simp [hlk] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hlk] at hnt hfr ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt hfr ⊢
      let ent := callEntryStateHOLFinite s callee
      have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hWs
      have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
      rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
      simp only [ent] at hrun hmeta
      simp only [hrun] at hmeta hnt hfr ⊢
      have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
        simp only [ent, hrun]; rintro rfl; simp at hnt
      cases res with
      | none => exact absurd hfr not_flowingOrResumes_error
      | some cr =>
        cases cr with
        | timeOut => simp at hnt
        | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
        | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
        | exception eid ev =>
          left
          dsimp only at hfr ⊢
          have hres_ex : Resumes (some (.exception eid ev)) := by
            rcases hfr with h | h | h | hr <;> try simp at h
            exact hr
          have hspec := FunSpec.at_lookup hinc s hc [] body' callee ret' hlk hWent hnt_c
          simp only [ent, hrun] at hspec
          exact ⟨inc_sysTx_exc_worldStep hW0 hA_pmc hmt hm152 hm160 hstep (hspec hres_ex), eid, ev, rfl⟩
        | returned v =>
          dsimp only at hnt hfr ⊢
          by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
          · right
            simp only [hsh, ↓reduceIte] at hnt hfr ⊢
            have hspec := FunSpec.at_lookup hinc s hc [] body' callee ret' hlk hWent hnt_c
            simp only [ent, hrun] at hspec
            have hstep_inc := inc_sysTx_ret_postStep hW0 hA_pmc hmt hm152 hm160 hstep (hspec (Or.inl ⟨v, rfl⟩))
            have hcode_inc : ({ cpost with locals := s.locals } : PanSemStateFiniteExact 64 F).code =
                originalRuntimeCode := by
              dsimp only
              rw [hmeta]
              exact hc
            exact ⟨trivial, hstep_inc, hcode_inc, hl_out⟩
          · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem sysTxPostPmcStep_release_marks {F : Type}
    {s_pmc s_cur : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    {w_m w_out w_mark w_fmark : BitVec 64} {ck : Nat}
    (hA_pmc : ArenaReady s_pmc)
    (hstep : SysTxPostPmcStep s_pmc none s_cur w_m w_out)
    (hmark_eq : w_mark.toNat = globN s_pmc "scratch_ptr")
    (hfmark_eq : w_fmark.toNat = globN s_pmc "frame_mem_ptr") :
    let s_rel : PanSemStateFiniteExact 64 F :=
      { s_cur with
        globals := (s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))).update
          (ofString "frame_mem_ptr", .val (.word w_fmark))
        clock := ck }
    SysTxPostPmcStep s_pmc r s_rel w_m w_out := by
  intro s_rel
  obtain ⟨hA_cur, hhp, _, _, hG, hK, hw_out, hin_out, hmk, hW⟩ := hstep
  have hg_ne : ∀ k : MlS,
      k ≠ ofString "frame_mem_ptr" →
      k ≠ ofString "scratch_ptr" →
      s_rel.globals.lookup k = s_cur.globals.lookup k := by
    intro k hne1 hne2
    simp [s_rel, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne1, Ne.symm hne2]
  have hhp_rel : globN s_rel "heap_ptr" = globN s_cur "heap_ptr" :=
    globN_eq_of_lookup (hg_ne (ofString "heap_ptr") (by decide) (by decide))
  have hfmp_rel : globN s_rel "frame_mem_ptr" = globN s_pmc "frame_mem_ptr" := by
    simp [s_rel, globN, HolFiniteMapExact.lookup_update, FUPDATE, hfmark_eq]
  have hsp_rel : globN s_rel "scratch_ptr" = globN s_pmc "scratch_ptr" := by
    have hne : ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" := by decide
    simp [s_rel, globN, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne, hmark_eq]
  have hG_rel : GlobalsKept sysTxGlobals s_pmc s_rel := by
    intro k hk
    have hne_fmp : k ≠ ofString "frame_mem_ptr" := fun h =>
      hk (h ▸ List.mem_map.2 ⟨"frame_mem_ptr", by simp [sysTxGlobals], rfl⟩)
    have hne_sp : k ≠ ofString "scratch_ptr" := fun h =>
      hk (h ▸ List.mem_map.2 ⟨"scratch_ptr", by simp [sysTxGlobals], rfl⟩)
    exact (hG k hk).trans (hg_ne k hne_fmp hne_sp).symm
  have hK_rel : RecordsKept (fun st => (w_m.toNat, 176) :: bufRegions sysTxBufs st) sysTxKeep s_pmc s_rel :=
    hK
  have hgi_rel : GuestInv s_rel := guestInv_congr (s := s_cur) rfl rfl rfl rfl hA_cur.1
  have hgw1 : GlobalsWord { s_cur with globals := s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark)) } :=
    globalsWord_update (ofString "scratch_ptr") w_mark rfl hA_cur.2.2.2.2.2.2.2.2.2
  have hgw_rel : GlobalsWord s_rel :=
    globalsWord_update (ofString "frame_mem_ptr") w_fmark rfl hgw1
  have hA_rel : ArenaReady s_rel := by
    refine ⟨hgi_rel, ?_⟩
    unfold ArenaOK
    rw [hhp_rel, hfmp_rel, hsp_rel]
    exact ⟨hA_cur.2.1, hA_cur.2.2.1, hA_pmc.2.2.2.1, hA_pmc.2.2.2.2.1, hA_pmc.2.2.2.2.2.1,
      hA_cur.2.2.2.2.2.2.1, hA_pmc.2.2.2.2.2.2.2.1, hA_pmc.2.2.2.2.2.2.2.2.1, hgw_rel⟩
  refine ⟨hA_rel, by rw [hhp_rel]; exact hhp, by rw [hfmp_rel], by rw [hsp_rel],
    hG_rel, hK_rel, hw_out, by rw [hhp_rel]; exact hin_out, hmk,
    fun S Nd hWT_pmc hm152 hm160 hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT_cur, hOG, hFO, hd_out⟩ := hW S Nd hWT_pmc hm152 hm160 hD
  obtain ⟨_, hWT_rel, hwo_eq⟩ :=
    worldTypedWith_release_marks_sysTx (ck := ck) hA_pmc hA_cur hWT_pmc hWT_cur hOG hhp hmark_eq hfmark_eq
  have hOG_rel : OwnedGrows s_pmc s_rel (worldOwned s_pmc S Nd) (worldOwned s_rel S' Nd') := by
    rw [hwo_eq]
    intro o ho
    rcases hOG o ho with rfl | hprev | hfresh
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hprev)
    · exact Or.inr (Or.inr ⟨hfresh.1, by rw [hhp_rel]; exact hfresh.2⟩)
  refine ⟨S', Nd', hsub, hWT_rel, hOG_rel, hFO, by rw [hwo_eq]; exact hd_out⟩

theorem sysTxAfterIncorporate_step {F : Type}
    {s0 s_pmc s : PanSemStateFiniteExact 64 F}
    {w_m w_aa w_ak w_out : BitVec 64}
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hc : s.code = originalRuntimeCode)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hstep : SysTxPostPmcStep s_pmc none s w_m w_out)
    (hnt : (evaluateHOLFiniteState s sysTxAfterIncorporate).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s sysTxAfterIncorporate).1) :
    WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s0
      (evaluateHOLFiniteState s sysTxAfterIncorporate).1
      (evaluateHOLFiniteState s sysTxAfterIncorporate).2 := by
  have hstep_s : SysTxPostPmcStep s_pmc none s w_m w_out := hstep
  obtain ⟨hAs, hhp, hfmp, hsp, hG, hK, hw_out, hin_out, hmk, hW⟩ := hstep
  have hin_out_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hA_pmc.2.1 hin_out.1, hin_out.2⟩
  have hload80 := evalHOLExact_load_word_in_block_sysTx (off := 80)
    hAs.2 hl_out hw_out hin_out_sb (by decide) (by decide)
  set w_mark : BitVec 64 := BitVec.ofNat 64 (memW s (w_out.toNat + 80))
  have hmark_lt : memW s (w_out.toNat + 80) < 2 ^ 64 := by
    unfold memW; cases s.memory (BitVec.ofNat 64 (w_out.toNat + 80)); exact BitVec.isLt _
  have hw_mark_nat : w_mark.toNat = memW s (w_out.toNat + 80) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmark_lt]
  by_cases hmz : memW s (w_out.toNat + 80) = 0
  · have hw_mark0 : w_mark = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [hw_mark_nat, hmz]; rfl
    have hload80' : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "out"), .const 80#64])) =
          some (.val (.word 0#64)) := by
      simpa only [show BitVec.ofNat 64 80 = 80#64 from rfl, hw_mark0] using hload80
    rw [sysTxAfterIncorporate_zero_mark s hload80']
    dsimp only
    let mid := setVarHOLFinite (ofString "system_mark") (.val (.word 0#64)) s
    have hl_out_mid : mid.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
      simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_out,
        show ofString "system_mark" ≠ ofString "out" by decide]
    have hret_mid : evaluateHOLFiniteState mid (.return (.var .local (ofString "out"))) =
        (some (.returned (.val (.word w_out))), emptyLocalsHOLFinite mid) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, hl_out_mid,
        shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hret_mid]; dsimp only
    have hstep_fin : SysTxPostPmcStep s_pmc (some (.returned (.val (.word w_out))))
        { emptyLocalsHOLFinite mid with
          locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite mid).locals
            (ofString "system_mark", s.locals.lookup (ofString "system_mark")) } w_m w_out :=
      sysTxPostPmcStep_with_locals_clock hstep_s _ s.clock
    exact worldStep_of_sysTxPostPmcStep hW0 hmt hm152 hm160 hstep_fin
  · obtain ⟨hm80_eq, hm88_eq, hm48_le⟩ := hmk hmz
    have hw_mark_nz : w_mark ≠ 0#64 := by
      intro h0
      apply hmz
      rw [← hw_mark_nat, h0]; rfl
    have hafter_eq : sysTxAfterIncorporate =
        .dec (ofString "system_mark") .one
          (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 80)]))
          (.seq
            (.ite (.cmp .notEqual (.var .local (ofString "system_mark")) (.const (BitVec.ofNat 64 0)))
              (.dec (ofString "system_ret_n") .one
                (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 48)]))
                (.seq
                  (.ite (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "system_ret_n")))
                    sysTxCopyRetBodyProg
                    .skip)
                  (.seq
                    (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "system_mark")])
                    (.call (some (none, none)) (ofString "frame_mem_release")
                      [.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)])]))))
              .skip)
            (.return (.var .local (ofString "out")))) := by
      unfold sysTxAfterIncorporate sysTxCopyRetBodyProg; rfl
    rw [hafter_eq] at hnt hfr ⊢
    rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
    have hload80_w : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 80)])) =
          some (.val (.word w_mark)) := hload80
    simp only [hload80_w, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hfr ⊢
    let s1 := setVarHOLFinite (ofString "system_mark") (.val (.word w_mark)) s
    change WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s0
      (evaluateHOLFiniteState s1
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "system_mark")) (.const (BitVec.ofNat 64 0)))
            (.dec (ofString "system_ret_n") .one
              (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 48)]))
              (.seq
                (.ite (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "system_ret_n")))
                  sysTxCopyRetBodyProg
                  .skip)
                (.seq
                  (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "system_mark")])
                  (.call (some (none, none)) (ofString "frame_mem_release")
                    [.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)])]))))
            .skip)
          (.return (.var .local (ofString "out"))))).1
      { (evaluateHOLFiniteState s1
          (.seq
            (.ite (.cmp .notEqual (.var .local (ofString "system_mark")) (.const (BitVec.ofNat 64 0)))
              (.dec (ofString "system_ret_n") .one
                (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 48)]))
                (.seq
                  (.ite (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "system_ret_n")))
                    sysTxCopyRetBodyProg
                    .skip)
                  (.seq
                    (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "system_mark")])
                    (.call (some (none, none)) (ofString "frame_mem_release")
                      [.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)])]))))
              .skip)
            (.return (.var .local (ofString "out"))))).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState s1
            (.seq
              (.ite (.cmp .notEqual (.var .local (ofString "system_mark")) (.const (BitVec.ofNat 64 0)))
                (.dec (ofString "system_ret_n") .one
                  (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 48)]))
                  (.seq
                    (.ite (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "system_ret_n")))
                      sysTxCopyRetBodyProg
                      .skip)
                    (.seq
                      (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "system_mark")])
                      (.call (some (none, none)) (ofString "frame_mem_release")
                        [.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)])]))))
                .skip)
              (.return (.var .local (ofString "out"))))).2.locals
          (ofString "system_mark", s.locals.lookup (ofString "system_mark")) }
    have hl_sm1 : s1.locals.lookup (ofString "system_mark") = some (.val (.word w_mark)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hl_out1 : s1.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_out,
        show ofString "system_mark" ≠ ofString "out" by decide]
    have hstep1 : SysTxPostPmcStep s_pmc none s1 w_m w_out :=
      sysTxPostPmcStep_with_locals_clock hstep_s s1.locals s.clock
    rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
    rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
    have hcond_sm : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "system_mark") (.val (.word w_mark)) s).toExact
        (fun a => Classical.propDecidable ((setVarHOLFinite (ofString "system_mark") (.val (.word w_mark)) s).memaddrs a))
        (.cmp .notEqual (.var .local (ofString "system_mark")) (.const (BitVec.ofNat 64 0))) =
          some (.val (.word 1#64)) := by
      simp [evalHOLExact, hl_sm1, s1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw_mark_nz]
    have hcond_sm1 : @evalHOLExact 64 F _ s1.toExact
        (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "system_mark")) (.const (BitVec.ofNat 64 0))) =
          some (.val (.word 1#64)) := hcond_sm
    simp only [hcond_sm, hcond_sm1, show (1#64 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hnt hfr ⊢
    have hload48_1 : @evalHOLExact 64 F _ s1.toExact
        (fun a => Classical.propDecidable (s1.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 48)])) =
          some (.val (.word (BitVec.ofNat 64 (memW s1 (w_out.toNat + 48))))) :=
      evalHOLExact_load_word_in_block_sysTx (off := 48)
        hstep1.1.2 hl_out1 hw_out hin_out_sb (by decide) (by decide)
    set w_rn : BitVec 64 := BitVec.ofNat 64 (memW s (w_out.toNat + 48))
    have hrn_lt : memW s (w_out.toNat + 48) < 2 ^ 64 := by
      unfold memW; cases s.memory (BitVec.ofNat 64 (w_out.toNat + 48)); exact BitVec.isLt _
    have hw_rn_nat : w_rn.toNat = memW s (w_out.toNat + 48) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrn_lt]
    have hrn_le : w_rn.toNat ≤ scratchEnd := by rw [hw_rn_nat]; exact hm48_le
    rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
    have hload48_w : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "system_mark") (.val (.word w_mark)) s).toExact
        (fun a => Classical.propDecidable ((setVarHOLFinite (ofString "system_mark") (.val (.word w_mark)) s).memaddrs a))
        (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 48)])) =
          some (.val (.word w_rn)) := hload48_1
    have hload48_w1 : @evalHOLExact 64 F _ s1.toExact
        (fun a => Classical.propDecidable (s1.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 48)])) =
          some (.val (.word w_rn)) := hload48_1
    simp only [hload48_w, hload48_w1, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hfr ⊢
    let s2 := setVarHOLFinite (ofString "system_ret_n") (.val (.word w_rn)) s1
    have hl_rn2 : s2.locals.lookup (ofString "system_ret_n") = some (.val (.word w_rn)) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hl_sm2 : s2.locals.lookup (ofString "system_mark") = some (.val (.word w_mark)) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_sm1,
        show ofString "system_ret_n" ≠ ofString "system_mark" by decide]
    have hl_out2 : s2.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_out1,
        show ofString "system_ret_n" ≠ ofString "out" by decide]
    have hstep2 : SysTxPostPmcStep s_pmc none s2 w_m w_out :=
      sysTxPostPmcStep_with_locals_clock hstep_s s2.locals s.clock
    have hc2 : s2.code = originalRuntimeCode := hc
    set iteProg : ProgHOL 64 :=
      .ite (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "system_ret_n")))
        sysTxCopyRetBodyProg .skip
    set relProg : ProgHOL 64 :=
      .seq (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "system_mark")])
        (.call (some (none, none)) (ofString "frame_mem_release")
          [.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)])])
    rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
    have hnt_ite : (evaluateHOLFiniteState s2 iteProg).1 ≠ some .timeOut := by
      dsimp only [s2, s1]
      rcases hr : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "system_ret_n") (.val (.word w_rn))
            (setVarHOLFinite (ofString "system_mark") (.val (.word w_mark)) s)) iteProg with ⟨r_i, m_i⟩
      rintro rfl
      simp [hr] at hnt
    have hfr_ite : FlowingOrResumes (evaluateHOLFiniteState s2 iteProg).1 := by
      dsimp only [s2, s1]
      rcases hr : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "system_ret_n") (.val (.word w_rn))
            (setVarHOLFinite (ofString "system_mark") (.val (.word w_mark)) s)) iteProg with ⟨r_i, m_i⟩
      cases r_i with
      | none => exact Or.inl rfl
      | some cr =>
        simp only [hr] at hfr
        exact hfr
    have hite_ok : ∃ s3 : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState s2 iteProg = (none, s3) ∧
        s3.locals.lookup (ofString "out") = some (.val (.word w_out)) ∧
        s3.locals.lookup (ofString "system_mark") = some (.val (.word w_mark)) ∧
        s3.code = originalRuntimeCode ∧
        SysTxPostPmcStep s_pmc none s3 w_m w_out ∧
        memW s3 (w_out.toNat + 88) = memW s (w_out.toNat + 88) := by
      dsimp only [iteProg] at hnt_ite hfr_ite ⊢
      rw [evaluateHOLFiniteState_ite] at hnt_ite hfr_ite ⊢
      by_cases hrn_z : w_rn = 0#64
      · have hcmp_zero : @evalHOLExact 64 F _ s2.toExact
            (fun a => Classical.propDecidable (s2.memaddrs a))
            (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "system_ret_n"))) =
              some (.val (.word 0#64)) := by
          simp [evalHOLExact, hl_rn2, hrn_z, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        simp only [hcmp_zero, ↓reduceIte, evaluateHOLFiniteState_skip]
        exact ⟨s2, rfl, hl_out2, hl_sm2, hc2, hstep2, rfl⟩
      · have hrn_pos : (0#64 : BitVec 64) < w_rn := by
          rw [BitVec.lt_def]
          have : w_rn.toNat ≠ 0 := fun hz => hrn_z (BitVec.eq_of_toNat_eq hz)
          change 0 < w_rn.toNat
          omega
        have hcmp_pos : @evalHOLExact 64 F _ s2.toExact
            (fun a => Classical.propDecidable (s2.memaddrs a))
            (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "system_ret_n"))) =
              some (.val (.word 1#64)) := by
          simp [evalHOLExact, hl_rn2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hrn_pos]
        simp only [hcmp_pos, show (1#64 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hnt_ite hfr_ite ⊢
        obtain ⟨s3, hs3_eq, hs3_loc, hs3_code, hs3_step, hs3_88⟩ :=
          sysTxCopyRetBodyProg_step hW0 hA_pmc hmt hm152 hm160 hc2 hstep2 hl_out2 hl_rn2 hrn_le hnt_ite hfr_ite
        exact ⟨s3, hs3_eq,
          (hs3_loc (ofString "out") (by decide)).trans hl_out2,
          (hs3_loc (ofString "system_mark") (by decide)).trans hl_sm2,
          hs3_code, hs3_step, hs3_88⟩
    obtain ⟨s3, hs3_eq, hl_out3, hl_sm3, hc3, hstep3, hm88_s3⟩ := hite_ok
    have hs3_eq' : evaluateHOLFiniteState
        (setVarHOLFinite (ofString "system_ret_n") (.val (.word w_rn))
          (setVarHOLFinite (ofString "system_mark") (.val (.word w_mark)) s)) iteProg = (none, s3) := hs3_eq
    rw [hs3_eq'] at hnt hfr ⊢
    dsimp only at hnt hfr ⊢
    dsimp only [relProg] at hnt hfr ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
    have hnt_sr : (evaluateHOLFiniteState s3
        (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "system_mark")])).1 ≠
        some .timeOut := by
      rcases hr : evaluateHOLFiniteState s3
          (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "system_mark")]) with ⟨r_s, m_s⟩
      rintro rfl
      simp [hr] at hnt
    have hev_sm3 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.var .local (ofString "system_mark")) = some (.val (.word w_mark)) := by
      simp [evalHOLExact, hl_sm3]
    obtain ⟨ck_sr, hsr_eq⟩ := scratch_release_call_exact_sysTx s3
      (.var .local (ofString "system_mark")) w_mark hc3 hstep3.1 hev_sm3 hnt_sr
    rw [hsr_eq] at hnt hfr ⊢
    dsimp only at hnt hfr ⊢
    set s4 : PanSemStateFiniteExact 64 F :=
      { s3 with
        globals := s3.globals.update (ofString "scratch_ptr", .val (.word w_mark))
        clock := ck_sr }
    have hmark_eq_sp : w_mark.toNat = globN s_pmc "scratch_ptr" :=
      hw_mark_nat.trans hm80_eq
    have hsp_s4 : globN s4 "scratch_ptr" = globN s_pmc "scratch_ptr" := by
      simp [s4, globN, HolFiniteMapExact.lookup_update, FUPDATE, hmark_eq_sp]
    have hhp_s4 : globN s4 "heap_ptr" = globN s3 "heap_ptr" := by
      have hne : ofString "heap_ptr" ≠ ofString "scratch_ptr" := by decide
      simp [s4, globN, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
    have hfmp_s4 : globN s4 "frame_mem_ptr" = globN s3 "frame_mem_ptr" := by
      have hne : ofString "frame_mem_ptr" ≠ ofString "scratch_ptr" := by decide
      simp [s4, globN, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
    have hgi_s4 : GuestInv s4 := guestInv_congr (s := s3) rfl rfl rfl rfl hstep3.1.1
    have hA_s4 : ArenaReady s4 := by
      obtain ⟨_, hb_s3, hl_s3, hf1_s3, hf2_s3, _, hp8_s3, hf8_s3, _, hgw_s3⟩ := hstep3.1
      refine ⟨hgi_s4, ?_⟩
      unfold ArenaOK
      rw [hhp_s4, hfmp_s4, hsp_s4]
      have hfmp_le_sp : globN s3 "frame_mem_ptr" ≤ globN s_pmc "scratch_ptr" := by
        have := hstep3.2.2.2.1
        omega
      exact ⟨hb_s3, hl_s3, hf1_s3, hfmp_le_sp, hA_pmc.2.2.2.2.2.1,
        hp8_s3, hf8_s3, hA_pmc.2.2.2.2.2.2.2.2.1,
        globalsWord_update (ofString "scratch_ptr") w_mark rfl hgw_s3⟩
    have hin_out_s4 : Inside (w_out.toNat, 96) sourceBase (globN s4 "heap_ptr") := by
      rw [hhp_s4]
      exact ⟨le_trans hA_pmc.2.1 hstep3.2.2.2.2.2.2.2.1.1, hstep3.2.2.2.2.2.2.2.1.2⟩
    have hw_out_s4 : WordsOK s4 (w_out.toNat, 96) := hstep3.2.2.2.2.2.2.1
    have hload88_s4 := evalHOLExact_load_word_in_block_sysTx (off := 88)
      hA_s4.2 hl_out3 hw_out_s4 hin_out_s4 (by decide) (by decide)
    set w_fmark : BitVec 64 := BitVec.ofNat 64 (memW s4 (w_out.toNat + 88))
    have hnt_fmr : (evaluateHOLFiniteState s4
        (.call (some (none, none)) (ofString "frame_mem_release")
          [.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)])])).1 ≠
        some .timeOut := by
      rcases hr : evaluateHOLFiniteState s4
          (.call (some (none, none)) (ofString "frame_mem_release")
            [.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)])]) with ⟨r_f, m_f⟩
      rintro rfl
      simp [hr] at hnt
    obtain ⟨ck_fmr, hfmr_eq⟩ := frame_mem_release_call_exact_sysTx s4
      (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)]))
      w_fmark hc3 hA_s4 hload88_s4 hnt_fmr
    rw [hfmr_eq] at hnt hfr ⊢
    dsimp only at hnt hfr ⊢
    have hfmark_lt : memW s4 (w_out.toNat + 88) < 2 ^ 64 := by
      unfold memW; cases s4.memory (BitVec.ofNat 64 (w_out.toNat + 88)); exact BitVec.isLt _
    have hfmark_eq_fmp : w_fmark.toNat = globN s_pmc "frame_mem_ptr" := by
      have h1 : w_fmark.toNat = memW s4 (w_out.toNat + 88) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfmark_lt]
      have h2 : memW s4 (w_out.toNat + 88) = memW s3 (w_out.toNat + 88) := rfl
      exact h1.trans ((h2.trans hm88_s3).trans hm88_eq)
    set s5 : PanSemStateFiniteExact 64 F :=
      { s4 with
        globals := s4.globals.update (ofString "frame_mem_ptr", .val (.word w_fmark))
        clock := ck_fmr }
    have hstep5 : SysTxPostPmcStep s_pmc (some (.returned (.val (.word w_out)))) s5 w_m w_out :=
      sysTxPostPmcStep_release_marks (ck := ck_fmr) hA_pmc hstep3 hmark_eq_sp hfmark_eq_fmp
    let s5_res : PanSemStateFiniteExact 64 F :=
      { s5 with
        locals := HolFiniteMapExact.resVarEq s5.locals
          (ofString "system_ret_n", s1.locals.lookup (ofString "system_ret_n")) }
    have hl_out_s5r : s5_res.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
      have hres_ne : (HolFiniteMapExact.resVarEq s5.locals
          (ofString "system_ret_n", s1.locals.lookup (ofString "system_ret_n"))).lookup (ofString "out") =
          s5.locals.lookup (ofString "out") := by
        cases s1.locals.lookup (ofString "system_ret_n") <;>
          simp [HolFiniteMapExact.resVarEq, FDOMSUB_HOL, FUPDATE_HOL,
            show ofString "system_ret_n" ≠ ofString "out" by decide,
            show ofString "out" ≠ ofString "system_ret_n" by decide]
      exact hres_ne.trans hl_out3
    have hret_s5r : evaluateHOLFiniteState s5_res (.return (.var .local (ofString "out"))) =
        (some (.returned (.val (.word w_out))), emptyLocalsHOLFinite s5_res) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, hl_out_s5r,
        shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hret_s5r]
    dsimp only
    have hstep_fin : SysTxPostPmcStep s_pmc (some (.returned (.val (.word w_out))))
        { emptyLocalsHOLFinite s5_res with
          locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite s5_res).locals
            (ofString "system_mark", s.locals.lookup (ofString "system_mark")) } w_m w_out :=
      sysTxPostPmcStep_with_locals_clock hstep5 _ ck_fmr
    exact worldStep_of_sysTxPostPmcStep hW0 hmt hm152 hm160 hstep_fin

theorem «wk_process_checked_system_transaction_of_unchecked»
    (h_unchecked :
      WorldKeeps WorldOK
        (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                   (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                   (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                   (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                   (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                   (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                   (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                   (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                   (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                   (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                   (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                   (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                   (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                   (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                   (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                   (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
        ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr",
         "journal_n", "scratch_ptr", "ts"]
        [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
         ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
        NoExtra (ofString "process_unchecked_system_transaction")) :
    WorldKeeps WorldOK
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr",
       "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_checked_system_transaction") := by
  refine ⟨_, _, _, lookup_process_checked_system_transaction, fun s hc hW _ hnt hres => ?_⟩
  have hp : ProgSysTxStep (sourceFnBody Guest.Software.guestFn_process_checked_system_transaction) := by
    dsimp only [sourceFnBody, sourceFunctionEntry,
      Guest.Software.guestFn_process_checked_system_transaction,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    refine progSysTxStep_seq_prefix (progPrefixStep_call0 sysTxPrefix_state_fresh_tx) ?_
    refine progSysTxStep_decCall_prefix sysTxPrefix_ext_code_of ?_
    refine progSysTxStep_seq_prefix
      (progPrefixStep_ite (progPrefixStep_raise _ _) progPrefixStep_skip) ?_
    refine progSysTxStep_decCall_prefix sysTxPrefix_alloc ?_
    refine progSysTxStep_decCall_tail h_unchecked ?_
    exact progLocalsOnly_seq
      (progLocalsOnly_ite (progLocalsOnly_raise _ _) progLocalsOnly_skip)
      (progLocalsOnly_return _)
  exact hp s hc hW hnt (Or.inr (Or.inr (Or.inr hres)))

theorem sysTxPmcCont_step {F : Type}
    {s0 s_pmc s : PanSemStateFiniteExact 64 F}
    {w_m w_aa w_ak w_out : BitVec 64}
    (hinc : WorldKeeps WorldOK (bufRegions incSysTxBufs) incSysTxGlobals sysTxKeep
      RetSysTxIncorporate (ofString "incorporate_tx_into_block"))
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : SysTxMsgTablesStep s0 s_pmc w_m [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hc : s.code = originalRuntimeCode)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hstep : SysTxPostPmcStep s_pmc none s w_m w_out)
    (hnt : (evaluateHOLFiniteState s sysTxPmcCont).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s sysTxPmcCont).1) :
    WorldStep (bufRegions sysTxBufs) sysTxGlobals sysTxKeep NoExtra s0
      (evaluateHOLFiniteState s sysTxPmcCont).1
      (evaluateHOLFiniteState s sysTxPmcCont).2 := by
  unfold sysTxPmcCont at hnt hfr ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hrun : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "incorporate_tx_into_block") []) with ⟨r1, mid⟩
  simp only [hrun] at hnt hfr ⊢
  cases r1 with
  | none =>
    have hinc_step := sysTxPostPmc_incorporate_step hinc hW0 hA_pmc hmt hm152 hm160 hc hl_out hstep
      (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl rfl)
    dsimp only at hinc_step
    rw [hrun] at hinc_step
    rcases hinc_step with ⟨_, eid, ev, hex⟩ | ⟨_, hstep_mid, hc_mid, hl_out_mid⟩
    · cases hex
    · exact sysTxAfterIncorporate_step hW0 hA_pmc hmt hm152 hm160 hc_mid hl_out_mid hstep_mid hnt hfr
  | some cr =>
    have hinc_step := sysTxPostPmc_incorporate_step hinc hW0 hA_pmc hmt hm152 hm160 hc hl_out hstep
      (by rw [hrun]; exact hnt) (by rw [hrun]; exact hfr)
    dsimp only at hinc_step
    rw [hrun] at hinc_step
    rcases hinc_step with ⟨hwStep, _⟩ | ⟨hnone, _⟩
    · exact hwStep
    · cases hnone

theorem «wk_process_unchecked_system_transaction_of»
    (hpmc : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) :: bufRegions pmcSysTxBufs s)
      pmcSysTxGlobals pmcSysTxKeep RetSysTxPmc (ofString "process_message_call"))
    (hinc : WorldKeeps WorldOK (bufRegions incSysTxBufs) incSysTxGlobals sysTxKeep
      RetSysTxIncorporate (ofString "incorporate_tx_into_block")) :
    WorldKeeps WorldOK
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr",
       "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_unchecked_system_transaction") := by
  refine ⟨_, _, _, lookup_process_unchecked_system_transaction, fun s0 hc0 hW0 ⟨vals, hlk⟩ hnt0 hres0 => ?_⟩
  obtain ⟨wt, wd, wdn, hl_t0, hl_d0, hl_dn0⟩ := lookupCode_unchecked_sysTx_words hlk
  have hfr0 : FlowingOrResumes
      (evaluateHOLFiniteState s0
        (sourceFnBody Guest.Software.guestFn_process_unchecked_system_transaction)).1 :=
    Or.inr (Or.inr (Or.inr hres0))
  rcases prefix_unchecked_sysTx_to_pmc s0 hc0 hW0 wt wd wdn hl_t0 hl_d0 hl_dn0 hnt0 hfr0 with
    ⟨hp_ex, _⟩ |
    ⟨s_pmc, w_m, w_aa, w_ak, L_wrap, hmt, hW_pmc, hc_pmc, hl_m, hm152, hm160, hmsg,
      hnt_pmc, hfr_pmc, hr_eq, hs_eq⟩
  · exact hp_ex.1
  · rcases pmc_decCall_sysTx_step hW0 hmt hW_pmc hc_pmc hl_m hm152 hm160 hmsg hpmc hnt_pmc hfr_pmc with
      ⟨hw_ex, _⟩ | ⟨w_out, s1, hstep1, hc1, hl_out1, hnt1, hfr1, hr1, hs1⟩
    · rw [hr_eq, hs_eq]
      exact worldStep_with_locals_clock hw_ex _ _
    · have hw_cont := sysTxPmcCont_step hinc hW0 hW_pmc.1 hmt hm152 hm160 hc1 hl_out1 hstep1 hnt1 hfr1
      rw [hr_eq, hs_eq, hr1, hs1]
      exact worldStep_with_locals_clock hw_cont _ _

theorem «wk_process_checked_system_transaction_of»
    (hpmc : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) :: bufRegions pmcSysTxBufs s)
      pmcSysTxGlobals pmcSysTxKeep RetSysTxPmc (ofString "process_message_call"))
    (hinc : WorldKeeps WorldOK (bufRegions incSysTxBufs) incSysTxGlobals sysTxKeep
      RetSysTxIncorporate (ofString "incorporate_tx_into_block")) :
    WorldKeeps WorldOK
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr",
       "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_checked_system_transaction") :=
  «wk_process_checked_system_transaction_of_unchecked»
    («wk_process_unchecked_system_transaction_of» hpmc hinc)

theorem worldKeeps_incSysTx_of_sc {keep : List (String × List Nat)}
    (hkeep : KeepSub sysTxKeep keep)
    (hinc : WorldKeepsSc WorldOK (bufRegions incSysTxBufs) incSysTxGlobals keep
      NoExtra (ofString "incorporate_tx_into_block")) :
    WorldKeeps WorldOK (bufRegions incSysTxBufs) incSysTxGlobals sysTxKeep
      RetSysTxIncorporate (ofString "incorporate_tx_into_block") := by
  obtain ⟨ps, body, ret, hl, hb⟩ := hinc
  refine ⟨ps, body, ret, hl, fun s hc hW hex hnt hres => ?_⟩
  obtain ⟨⟨hAp, hhp, hG, hK, hWT⟩, hsc⟩ := hb s hc hW hex hnt hres
  refine ⟨hAp, hhp, hG, recordsKept_mono_keep hkeep hK, fun S Nd hT hD => ?_⟩
  obtain ⟨S', Nd', hsub, hT', hOG, hFO, _⟩ := hWT S Nd hT hD
  exact ⟨S', Nd', hsub, hT', hOG, hFO, hsc⟩

abbrev incWithdrawalKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
   ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]

theorem «wk_process_unchecked_system_transaction_of_sc»
    (hpmc : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) :: bufRegions pmcSysTxBufs s)
      pmcSysTxGlobals pmcSysTxKeep RetSysTxPmc (ofString "process_message_call"))
    (hinc : WorldKeepsSc WorldOK (bufRegions incSysTxBufs) incSysTxGlobals incWithdrawalKeep
      NoExtra (ofString "incorporate_tx_into_block")) :
    WorldKeeps WorldOK
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr",
       "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_unchecked_system_transaction") :=
  «wk_process_unchecked_system_transaction_of» hpmc
    (worldKeeps_incSysTx_of_sc keepSub_sysTxKeep_freshTx hinc)

theorem «wk_process_checked_system_transaction_of_sc»
    (hpmc : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) :: bufRegions pmcSysTxBufs s)
      pmcSysTxGlobals pmcSysTxKeep RetSysTxPmc (ofString "process_message_call"))
    (hinc : WorldKeepsSc WorldOK (bufRegions incSysTxBufs) incSysTxGlobals incWithdrawalKeep
      NoExtra (ofString "incorporate_tx_into_block")) :
    WorldKeeps WorldOK
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr",
       "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_checked_system_transaction") :=
  «wk_process_checked_system_transaction_of» hpmc
    (worldKeeps_incSysTx_of_sc keepSub_sysTxKeep_freshTx hinc)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
