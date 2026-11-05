import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkAcctWsBase
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalInitFresh
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard06b

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

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
