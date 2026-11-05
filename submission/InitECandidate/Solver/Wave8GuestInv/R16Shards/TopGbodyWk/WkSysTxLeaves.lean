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
