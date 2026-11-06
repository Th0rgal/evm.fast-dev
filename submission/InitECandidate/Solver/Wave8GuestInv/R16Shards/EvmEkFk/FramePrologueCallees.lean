import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChild
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge
import InitECandidate.Solver.Wave8GuestInv.R13Shards.Common
import InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_sub
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmHtabStep
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmStepLemmas
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Tables
import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabSetBase
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.AllocJournalStep
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.ExtendMemoryHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.StackPushInv
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_is_zero
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmFrameSpecs
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01HtabCopy

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R13
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
  (IvlUnhit not_cellHits_of_disj memW_eq_of_ivlUnhit worldOwned_zero_or_allocated
   worldOwned_zero_aligned worldTypedWith_erase_local adjoin_local_table
   htabWF_congr_unhit htabFootprint_eq_of_hdr_unhit htabValues_eq_of_unhit
   disj_zero_right disj_of_inside_left disj_of_inside_right globN_eq_of_lookup
   ivl_allocated_bound zero_not_mem_S worldTypedIvls_sub_worldOwned)
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2
  (worldTypedWith_perm)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish
  (allocated_disj_ownedGrows)
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
  (BufList ValidBufList bufRegions validBufList_disj SafeStepGlobals WorldStepSc WorldKeepsSc)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
  (ChainCellsKept HeadMemChainWF evmKeeps_aligned)

abbrev FrameStartAvoids {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
   (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
   (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
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
   (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]

def EvmStepCC (gw : List String) {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  EvmStep gw s post ∧ ChainCellsAgree s post

def EvmProgStep (gw : List String) (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → EvmInv s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowsOrResumes (evaluateHOLFiniteState s prog).1 →
    EvmStepCC gw s (evaluateHOLFiniteState s prog).2

/-! ## Milestone 1: `WorldStepSc → EvmStep + ChainCellsAgree` Bridge -/

private theorem wordsOK_transfer_local {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {i : Ivl} (hw : WordsOK s i) :
    WordsOK post i := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨_, hdom, _⟩ := hw.2.2 k hk
  rcases hm : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with ⟨w⟩
  exact ⟨w, hgP.memaddrs.trans hgS.memaddrs.symm ▸ hdom, hm⟩

private def AllocatedEvm {F : Type} (s : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  Inside i sourceBase (globN s "heap_ptr") ∨
    Inside i scratchStart (globN s "frame_mem_ptr") ∨
    Inside i (globN s "scratch_ptr") scratchEnd

private theorem allocatedEvm_of_allocated {F : Type}
    {s : PanSemStateFiniteExact 64 F} {i : Ivl} (hi : Allocated s i) :
    AllocatedEvm s i := by
  rcases hi with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

private theorem allocatedEvm_disj_freeGap {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hAs : ArenaOK s) {i : Ivl}
    (hi : i.2 = 0 ∨ AllocatedEvm s i) :
    Disj i (freeGap s) := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  unfold freeGap
  rcases hi with hz | h | h | h
  · exact Or.inl hz
  · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp; omega)))

private theorem allocatedEvm_disj_heapFree {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hAs : ArenaOK s) {i : Ivl}
    (hi : i.2 = 0 ∨ AllocatedEvm s i) :
    Disj i (heapFree s) := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  unfold heapFree
  rcases hi with hz | h | h | h
  · exact Or.inl hz
  · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp; omega)))

private theorem allocatedEvm_disj_freshHeap {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {i j : Ivl} (hi : i.2 = 0 ∨ AllocatedEvm s i)
    (hj : Inside j (globN s "heap_ptr") (globN post "heap_ptr")) :
    Disj i j := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp
  rcases hi with hz | h | h | h
  · exact Or.inl hz
  · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h hj; omega)))
  · exact Or.inr (Or.inr (Or.inr (by unfold Inside at h hj; omega)))
  · exact Or.inr (Or.inr (Or.inr (by unfold Inside at h hj; omega)))

private theorem allocatedEvm_disj_ownedGrows {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {o : Ivl} {old new : List Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : o.2 = 0 ∨ AllocatedEvm s o)
    (hold : ∀ i ∈ old, Disj o i)
    (hgrow : OwnedGrows s post old new) :
    ∀ j ∈ new, Disj o j := by
  intro j hj
  rcases hgrow j hj with rfl | ⟨i, hi, hin⟩ | hfresh
  · exact disj_zero_right o
  · exact disj_of_inside_right hin (hold i hi)
  · exact allocatedEvm_disj_freshHeap hAs hAp hhp ho hfresh

private theorem allocatedEvm_bound {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hAs : ArenaOK s) {i : Ivl}
    (hi : AllocatedEvm s i) :
    i.1 + i.2 ≤ 2 ^ 64 := by
  have hlim1 : heapLimit ≤ 2 ^ 64 := by decide
  have hlim2 : scratchEnd ≤ 2 ^ 64 := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, hs_se, _⟩ := hAs
  rcases hi with h | h | h <;> unfold Inside at h <;> omega

private theorem frameObject_zero_or_allocatedEvm {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat} {ec o : Ivl}
    (hAs : ArenaOK s) (hFW : FrameWF s S ec) (ho : o ∈ frameObjects s ec) :
    o.2 = 0 ∨ AllocatedEvm s o := by
  obtain ⟨hscr, hmem_in, _, _, _, _, _, _, _, _, _, _, hlogs_in, _,
    hret_in, hll_ok, _⟩ := hFW
  unfold frameObjects at ho
  rcases List.mem_append.1 ho with ho7 | holog
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
    rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (hscr (ec.1, 280) (by simp)).1))
    · exact Or.inr (Or.inr (Or.inr (hscr (ec.2, 104) (by simp)).1))
    · exact Or.inr (Or.inr (Or.inr (hscr (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1))
    · exact Or.inr (Or.inr (Or.inl hmem_in))
    · exact Or.inr (Or.inr (Or.inr (hscr (memW s (ec.1 + 88), 24) (by simp)).1))
    · rcases hlogs_in with hin | hin
      · exact Or.inr (Or.inl hin)
      · exact Or.inr (Or.inr (Or.inr hin))
    · rcases hret_in with ⟨hz, _⟩ | ⟨hin, _⟩
      · unfold frameRet; simp [hz]
      · exact Or.inr (Or.inl hin)
  · unfold frameLogObjects at holog; dsimp only at holog
    obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
    rw [List.mem_range] at hidx_mem
    rcases hll_ok with hz | ⟨_, _, _, _, hent⟩
    · exfalso
      have hlo := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      have hss0 : 0 < scratchStart := by decide
      have := hAs.2.2.1; have := hAs.2.2.2.1
      dsimp at hlo; omega
    · have hle := (hent idx hidx_mem).2
      have ho_rec := (List.mem_filter.1 ho_own).1
      simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
      rcases ho_rec with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl hle.2.1)
      · exact Or.inr (Or.inl hle.2.2.2.2.1)
      · exact Or.inr (Or.inl hle.2.2.2.2.2.1)
      · exact Or.inr (Or.inl hle.2.2.2.2.2.2)

private theorem ivlUnhit_of_worldStep_frameOutside {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old R : List Ivl} {i : Ivl}
    (hAs : ArenaOK s)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (hold_z : ∀ j ∈ old, j.2 = 0 → j.1 % 8 = 0)
    (hR_z : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hi1 : i.1 % 8 = 0) (hi2 : i.2 % 8 = 0)
    (hi_al : i.2 = 0 ∨ AllocatedEvm s i)
    (hi_old : ∀ j ∈ old, Disj i j)
    (hi_R : ∀ j ∈ R, Disj i j) :
    IvlUnhit s post i := by
  have hfg_z : (freeGap s).2 = 0 → (freeGap s).1 % 8 = 0 := fun _ => hAs.2.2.2.2.2.2.1
  have hhf_z : (heapFree s).2 = 0 → (heapFree s).1 % 8 = 0 := fun _ => hAs.2.2.2.2.2.1
  have hi_fg := allocatedEvm_disj_freeGap hAs hi_al
  have hi_hf := allocatedEvm_disj_heapFree hAs hi_al
  intro a ha8 hhit
  apply hfr a
  · intro j hj hcj
    rcases List.mem_append.1 hj with hj12 | hfg
    · rcases List.mem_append.1 hj12 with hj_old | hj_R
      · exact not_cellHits_of_disj hi1 hi2 ha8 (hold_z j hj_old) hhit (hi_old j hj_old) hcj
      · exact not_cellHits_of_disj hi1 hi2 ha8 (hR_z j hj_R) hhit (hi_R j hj_R) hcj
    · simp only [List.mem_singleton] at hfg; subst hfg
      exact not_cellHits_of_disj hi1 hi2 ha8 hfg_z hhit hi_fg hcj
  · intro hcf
    exact not_cellHits_of_disj hi1 hi2 ha8 hhf_z hhit hi_hf hcf

private theorem worldTypedWith_strip_frame_tables {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hW : WorldTypedWith s S Nd) (L : List Nat)
    (hL_local : ∀ t ∈ L, ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t) :
    ∃ S_w F_rem : List Nat,
      F_rem.Nodup ∧
      (∀ t ∈ F_rem, t ∈ L ∧ t ∉ S_w) ∧
      (∀ t ∈ L, t ∉ S_w) ∧
      S.Perm (S_w ++ F_rem) ∧
      WorldTypedWith s S_w Nd := by
  induction L generalizing S with
  | nil =>
    exact ⟨S, [], List.nodup_nil, fun _ h => False.elim (List.not_mem_nil h),
      fun _ h => False.elim (List.not_mem_nil h), by simp, hW⟩
  | cons t rest ih =>
    have ht_loc : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t :=
      hL_local t (by simp)
    have hrest_loc : ∀ u ∈ rest, ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ u :=
      fun u hu => hL_local u (by simp [hu])
    by_cases htS : t ∈ S
    · have hW_er : WorldTypedWith s (S.erase t) Nd := worldTypedWith_erase_local hW ht_loc
      obtain ⟨S_w, F_rem, hnd_F, hF_in, hrest_not, hperm_er, hW_Sw⟩ := ih hW_er hrest_loc
      have ht_not_er : t ∉ S.erase t := (List.Nodup.mem_erase_iff hW.1.1).not.2 (fun h => h.1 rfl)
      have ht_not_SwF : t ∉ S_w ++ F_rem := fun hm => ht_not_er (hperm_er.symm.subset hm)
      have ht_not_Sw : t ∉ S_w := fun hm => ht_not_SwF (List.mem_append_left _ hm)
      have ht_not_F : t ∉ F_rem := fun hm => ht_not_SwF (List.mem_append_right _ hm)
      refine ⟨S_w, t :: F_rem, List.nodup_cons.2 ⟨ht_not_F, hnd_F⟩, ?_, ?_, ?_, hW_Sw⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu'
        · exact ⟨by simp, ht_not_Sw⟩
        · exact ⟨by simp [(hF_in u hu').1], (hF_in u hu').2⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu'
        · exact ht_not_Sw
        · exact hrest_not u hu'
      · have h1 : S.Perm (t :: S.erase t) := List.perm_cons_erase htS
        have h2 : (t :: S.erase t).Perm (t :: (S_w ++ F_rem)) := hperm_er.cons t
        have h3 : (t :: (S_w ++ F_rem)).Perm (S_w ++ (t :: F_rem)) := List.perm_middle.symm
        exact h1.trans (h2.trans h3)
    · obtain ⟨S_w, F_rem, hnd_F, hF_in, hrest_not, hperm, hW_Sw⟩ := ih hW hrest_loc
      have ht_not_Sw : t ∉ S_w := fun hm => htS (hperm.symm.subset (List.mem_append_left _ hm))
      refine ⟨S_w, F_rem, hnd_F, ?_, ?_, hperm, hW_Sw⟩
      · intro u hu
        exact ⟨by simp [(hF_in u hu).1], (hF_in u hu).2⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu'
        · exact ht_not_Sw
        · exact hrest_not u hu'

private theorem adjoin_local_table_list {F : Type}
    {post : PanSemStateFiniteExact 64 F} {U Nd' : List Nat}
    (hWU : WorldTypedWith post U Nd')
    (F_rem : List Nat) (hnd_F : F_rem.Nodup)
    (hwf_F : ∀ t ∈ F_rem, HtabWF post t)
    (hall_F : ∀ t ∈ F_rem, ∀ i ∈ htabFootprint post t, Allocated post i)
    (hdj_U : ∀ t ∈ F_rem, ∀ i ∈ htabFootprint post t, ∀ o ∈ worldOwned post U Nd', Disj i o)
    (hdj_FF : ∀ t ∈ F_rem, ∀ u ∈ F_rem, t ≠ u →
      ∀ i ∈ htabFootprint post t, ∀ j ∈ htabFootprint post u, Disj i j) :
    WorldTypedWith post (U ++ F_rem) Nd' := by
  induction F_rem generalizing U with
  | nil => simpa using hWU
  | cons t rest ih =>
    obtain ⟨ht_not_rest, hnd_rest⟩ := List.nodup_cons.1 hnd_F
    have hwf_t : HtabWF post t := hwf_F t (by simp)
    have hfp_t : ∀ i ∈ htabFootprint post t, Allocated post i ∧ ∀ o ∈ worldOwned post U Nd', Disj i o :=
      fun i hi => ⟨hall_F t (by simp) i hi, hdj_U t (by simp) i hi⟩
    obtain ⟨_, _, _, hW_Ut⟩ := adjoin_local_table hWU hwf_t hfp_t rfl
    have hdj_Ut : ∀ u ∈ rest, ∀ i ∈ htabFootprint post u, ∀ o ∈ worldOwned post (U ++ [t]) Nd', Disj i o := by
      intro u hu i hi o ho
      have hu_ne_t : u ≠ t := fun heq => ht_not_rest (heq ▸ hu)
      unfold worldOwned at ho
      rcases List.mem_append.1 ho with h1 | hnd
      · rcases List.mem_append.1 h1 with htab | hfix
        · rw [List.flatMap_append] at htab
          rcases List.mem_append.1 htab with htabU | htabt
          · apply hdj_U u (by simp [hu]) i hi o
            unfold worldOwned; exact List.mem_append_left _ (List.mem_append_left _ htabU)
          · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htabt
            exact hdj_FF u (by simp [hu]) t (by simp) hu_ne_t i hi o htabt
        · apply hdj_U u (by simp [hu]) i hi o
          unfold worldOwned; exact List.mem_append_left _ (List.mem_append_right _ hfix)
      · apply hdj_U u (by simp [hu]) i hi o
        unfold worldOwned; exact List.mem_append_right _ hnd
    have hres := ih hW_Ut hnd_rest
      (fun u hu => hwf_F u (by simp [hu]))
      (fun u hu => hall_F u (by simp [hu]))
      hdj_Ut
      (fun u hu v hv => hdj_FF u (by simp [hu]) v (by simp [hv]))
    simpa [List.append_assoc] using hres

private theorem frameRole_ne_worldOrJournal {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat} {ch : List Ivl}
    (hRoles : RolesOK s S (worldRoleSlots s ++ frameRoleSlots s ch) (journalRoleSlots s))
    {t : Nat} {rf : String}
    (hfr : (t, rf) ∈ frameRoleSlots s ch)
    (hrf : rf ∈ ["frame.del", "frame.addr", "frame.key"]) :
    ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t := by
  have hwrs_role : ∀ a ∈ worldRoleSlots s, a.2 ∉ (["frame.del", "frame.addr", "frame.key"] : List String) := by
    intro a ha
    have hm := (List.mem_filter.1 ha).1
    rcases List.mem_append.1 hm with h1 | hbal
    · rcases List.mem_append.1 h1 with h2 | hnts
      · rcases List.mem_append.1 h2 with h3 | hnbs
        · rcases List.mem_append.1 h3 with h4 | hg
          · rcases List.mem_append.1 h4 with h5 | hts
            · rcases List.mem_append.1 h5 with hws | hbs
              · unfold recRoles at hws; split at hws
                · cases hws
                · obtain ⟨⟨k, r⟩, hkr, rfl⟩ := List.mem_map.1 hws
                  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
                  rcases hkr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (dsimp only; decide)
              · unfold recRoles at hbs; split at hbs
                · cases hbs
                · obtain ⟨⟨k, r⟩, hkr, rfl⟩ := List.mem_map.1 hbs
                  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
                  rcases hkr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (dsimp only; decide)
            · unfold recRoles at hts; split at hts
              · cases hts
              · obtain ⟨⟨k, r⟩, hkr, rfl⟩ := List.mem_map.1 hts
                simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
                rcases hkr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (dsimp only; decide)
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with rfl | rfl | rfl <;> (dsimp only; decide)
        · unfold nestRoles at hnbs; split_ifs at hnbs with c1 c2
          · cases hnbs
          · cases hnbs
          · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hnbs; dsimp only; decide
      · unfold nestRoles at hnts; split_ifs at hnts with c1 c2
        · cases hnts
        · cases hnts
        · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hnts; dsimp only; decide
    · obtain ⟨ad, _, had⟩ := List.mem_flatMap.1 hbal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at had
      rcases had with rfl | rfl <;> (dsimp only; decide)
  have hjrs_role : ∀ a ∈ journalRoleSlots s, a.2 ∉ (["frame.del", "frame.addr", "frame.key"] : List String) := by
    intro a ha
    unfold journalRoleSlots at ha
    obtain ⟨idx, _, hai⟩ := List.mem_flatMap.1 ha
    dsimp only at hai
    rcases List.mem_cons.1 hai with rfl | hrest
    · dsimp only; unfold journalRole; split_ifs <;> decide
    · split_ifs at hrest with hc
      · simp only [List.mem_singleton] at hrest; subst hrest; dsimp only; decide
      · cases hrest
  intro a ha heq
  rcases List.mem_append.1 ha with haw | haj
  · obtain ⟨_, _, hcross⟩ := List.pairwise_append.1 hRoles.2.1
    have hreq := (hcross a haw (t, rf) hfr heq).1
    exact hwrs_role a haw (hreq ▸ hrf)
  · have hreq := hRoles.2.2 a haj (t, rf) (List.mem_append_left _ (List.mem_append_right _ hfr)) heq
    exact hjrs_role a haj (hreq ▸ hrf)

private theorem worldTableRefs_in_worldOrJournalRoleSlots {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S)
    {u : Nat} (hu : u ≠ 0) (hw : u ∈ worldTableRefs s S) :
    ∃ r, (u, r) ∈ worldRoleSlots s ++ journalRoleSlots s := by
  have h0S : 0 ∉ S := zero_not_mem_S hT
  unfold worldTableRefs at hw
  dsimp only at hw
  rcases List.mem_append.1 hw with h16 | hjr
  · rcases List.mem_append.1 h16 with h15 | hbal
    · rcases List.mem_append.1 h15 with h14 | hnts
      · rcases List.mem_append.1 h14 with h13 | hnbs
        · rcases List.mem_append.1 h13 with h12 | hg
          · rcases List.mem_append.1 h12 with h11 | hts
            · rcases List.mem_append.1 h11 with hws | hbs
              · unfold recordSlots at hws; split_ifs at hws with h0
                · cases hws
                · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hws
                  simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
                  rcases hk with rfl | rfl
                  · refine ⟨"ws+16", List.mem_append_left _ (List.mem_filter.2 ⟨?_, by simp [hu]⟩)⟩
                    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                    unfold recRoles; simp [h0]
                  · refine ⟨"ws+32", List.mem_append_left _ (List.mem_filter.2 ⟨?_, by simp [hu]⟩)⟩
                    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                    unfold recRoles; simp [h0]
              · unfold recordSlots at hbs; split_ifs at hbs with h0
                · cases hbs
                · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hbs
                  have hex : ∃ r, (memW s (globN s "bs" + k), r) ∈ recRoles s "bs"
                      [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
                    unfold recRoles; simp only [h0, ↓reduceIte]
                    simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
                    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
                    · exact ⟨"bs+8", by simp⟩
                    · exact ⟨"bs+16", by simp⟩
                    · exact ⟨"bs+24", by simp⟩
                    · exact ⟨"bs+32", by simp⟩
                    · exact ⟨"bs+40", by simp⟩
                    · exact ⟨"bs+48", by simp⟩
                    · exact ⟨"bs+72", by simp⟩
                  obtain ⟨r, hr⟩ := hex
                  refine ⟨r, List.mem_append_left _ (List.mem_filter.2 ⟨?_, by simp [hu]⟩)⟩
                  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                  apply List.mem_append_left; apply List.mem_append_left; exact List.mem_append_right _ hr
            · unfold recordSlots at hts; split_ifs at hts with h0
              · cases hts
              · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hts
                have hex : ∃ r, (memW s (globN s "ts" + k), r) ∈ recRoles s "ts"
                    [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
                  unfold recRoles; simp only [h0, ↓reduceIte]
                  simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
                  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                  · exact ⟨"ts+8", by simp⟩
                  · exact ⟨"ts+16", by simp⟩
                  · exact ⟨"ts+24", by simp⟩
                  · exact ⟨"ts+32", by simp⟩
                  · exact ⟨"ts+40", by simp⟩
                  · exact ⟨"ts+48", by simp⟩
                  · exact ⟨"ts+56", by simp⟩
                  · exact ⟨"ts+64", by simp⟩
                obtain ⟨r, hr⟩ := hex
                refine ⟨r, List.mem_append_left _ (List.mem_filter.2 ⟨?_, by simp [hu]⟩)⟩
                apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                apply List.mem_append_left; exact List.mem_append_right _ hr
          · obtain ⟨g, hgm, rfl⟩ := List.mem_map.1 hg
            refine ⟨g, List.mem_append_left _ (List.mem_filter.2 ⟨?_, by simp [hu]⟩)⟩
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            apply List.mem_append_right
            simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hgm
            rcases hgm with rfl | rfl | rfl <;> simp
        · split_ifs at hnbs with hc
          · have h32nz : memW s (globN s "bs" + 32) ≠ 0 := fun h0 => h0S (h0 ▸ hc.2)
            refine ⟨"bs.inner", List.mem_append_left _ (List.mem_filter.2 ⟨?_, by simp [hu]⟩)⟩
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
            unfold nestRoles; simp [hc.1, h32nz]
            exact hnbs
          · cases hnbs
      · split_ifs at hnts with hc
        · have h32nz : memW s (globN s "ts" + 32) ≠ 0 := fun h0 => h0S (h0 ▸ hc.2)
          refine ⟨"ts.inner", List.mem_append_left _ (List.mem_filter.2 ⟨?_, by simp [hu]⟩)⟩
          apply List.mem_append_left; apply List.mem_append_right
          unfold nestRoles; simp [hc.1, h32nz]
          exact hnts
        · cases hnts
    · obtain ⟨ad, had, had_u⟩ := List.mem_flatMap.1 hbal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at had_u
      rcases had_u with rfl | rfl
      · refine ⟨"bal.stor", List.mem_append_left _ (List.mem_filter.2 ⟨?_, by simp [hu]⟩)⟩
        exact List.mem_append_right _ (List.mem_flatMap.2 ⟨ad, had, by simp⟩)
      · refine ⟨"bal.reads", List.mem_append_left _ (List.mem_filter.2 ⟨?_, by simp [hu]⟩)⟩
        exact List.mem_append_right _ (List.mem_flatMap.2 ⟨ad, had, by simp⟩)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hjr
    exact ⟨journalRole s (memW s (globN s "journal" + 32 * k)),
      List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hk, by simp⟩)⟩

private theorem disj_comm {i j : Ivl} (h : Disj i j) : Disj j i := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

private theorem avoidsTries_join_msgs {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat} {os ch : List Ivl}
    (hAT : AvoidsTries s S os)
    (hMsgs : ∀ ec ∈ ch, AvoidsTries s S [(memW s (ec.1 + 112), 176)]) :
    ∃ Nd : List Nat, TriesTypedWith s S Nd ∧
      (∀ o ∈ os, ∀ j ∈ nodeExtents s Nd, Disj o j) ∧
      (∀ ec ∈ ch, ∀ j ∈ nodeExtents s Nd, Disj (memW s (ec.1 + 112), 176) j) := by
  induction ch with
  | nil =>
    obtain ⟨Nd, hTr, hdj⟩ := hAT
    exact ⟨Nd, hTr, hdj, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons ec rest ih =>
    obtain ⟨Nd1, hTr1, hdj_os, hdj_rest⟩ :=
      ih (fun ec' hec' => hMsgs ec' (List.mem_cons_of_mem _ hec'))
    obtain ⟨Nd2, hTr2, hdj_ec⟩ := hMsgs ec List.mem_cons_self
    obtain ⟨hTr_int, hsub⟩ := EvmStepLemmas.triesTypedWith_inter hTr1 hTr2
    refine ⟨_, hTr_int, ?_, ?_⟩
    · intro o ho j hj
      exact hdj_os o ho j (hsub j hj).1
    · intro ec' hec' j hj
      rcases List.mem_cons.1 hec' with rfl | hmem
      · exact hdj_ec (memW s (ec'.1 + 112), 176) (List.mem_singleton.2 rfl) j (hsub j hj).2
      · exact hdj_rest ec' hmem j (hsub j hj).1

private theorem globalBuffers_sz_pos {gn : String × Nat} (h : gn ∈ globalBuffers) :
    0 < gn.2 := by
  revert gn h; decide

private theorem bufRegions_zero_aligned {F : Type}
    {s : PanSemStateFiniteExact 64 F} {B : BufList}
    (hB : ValidBufList B) (hF : FixedTyped s) :
    ∀ j ∈ bufRegions B s, j.2 = 0 → j.1 % 8 = 0 := by
  intro j hj _
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
  obtain ⟨sz, hgb, _, _⟩ := hB p hp
  by_cases hz : globN s p.1 = 0
  · simp [bufferRegion, hz]
  · have hfix : bufferRegion s (p.1, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
    have hpos : 0 < sz := globalBuffers_sz_pos hgb
    rcases hF.1 _ hfix with h0 | ⟨_, hw⟩
    · simp [bufferRegion, hz] at h0; omega
    · have h1 := hw.1
      simp only [bufferRegion, hz, ↓reduceIte] at h1 ⊢
      exact h1

private theorem bufRegions_disj_of_disj_fixedObjects {F : Type}
    {s : PanSemStateFiniteExact 64 F} {B : BufList} {i : Ivl}
    (hB : ValidBufList B) (hfix_dj : ∀ j ∈ fixedObjects s, Disj i j) :
    ∀ j ∈ bufRegions B s, Disj i j := by
  intro j hj
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
  obtain ⟨sz, hgb, _, hle⟩ := hB p hp
  by_cases hz : globN s p.1 = 0
  · exact Or.inr (Or.inl (by simp [bufferRegion, hz]))
  · have hfix : bufferRegion s (p.1, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
    have hd := hfix_dj _ hfix
    have hin : Inside (bufferRegion s p) (bufferRegion s (p.1, sz)).1
        ((bufferRegion s (p.1, sz)).1 + (bufferRegion s (p.1, sz)).2) := by
      simp only [bufferRegion, hz, ↓reduceIte, Inside]
      exact ⟨le_rfl, by omega⟩
    exact disj_of_inside_right hin hd

private theorem htabFootprint_len_pos {F : Type}
    {s : PanSemStateFiniteExact 64 F} {u : Nat} (hwf : HtabWF s u) :
    ∀ o ∈ htabFootprint s u, 0 < o.2 := by
  obtain ⟨_, _, hk1, _, hstr, hncap, _⟩ := hwf
  intro o ho
  simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · dsimp only; decide
  · dsimp only
    have hspos : 0 < hdr s u 1 := by omega
    have hnpos : 0 < hdr s u 10 + 1 := by omega
    exact Nat.mul_pos hnpos hspos
  · dsimp only; omega
  · dsimp only; omega

private theorem worldOwned_inside_heap_or_mark_of_ownedGrows {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S S_w S_w' Nd Nd' : List Nat} {m : Nat}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hSw_sub : ∀ v ∈ S_w, v ∈ S)
    (hTr : TriesTypedWith s S Nd)
    (hm8_Sw : ∀ v ∈ S_w, ∀ k ∈ htabFootprint s v,
      Inside k sourceBase heapLimit ∨ Inside k m scratchEnd)
    (hm9 : ∀ j ∈ fixedObjects s, j.2 = 0 ∨ Inside j sourceBase heapLimit ∨ Inside j m scratchEnd)
    (hgrow : OwnedGrows s post (worldOwned s S_w Nd) (worldOwned post S_w' Nd')) :
    ∀ o ∈ worldOwned post S_w' Nd', 0 < o.2 →
      Inside o sourceBase heapLimit ∨ Inside o m scratchEnd := by
  intro o ho hpos
  rcases hgrow o ho with rfl | ⟨j, hj, hin⟩ | hfresh
  · simp at hpos
  · have hj_pos : 0 < j.2 := by unfold Inside at hin; omega
    have hj_loc : Inside j sourceBase heapLimit ∨ Inside j m scratchEnd := by
      unfold worldOwned at hj
      rcases List.mem_append.1 hj with hj1 | hj_nd
      · rcases List.mem_append.1 hj1 with hj_tab | hj_fix
        · obtain ⟨v, hv, hjv⟩ := List.mem_flatMap.1 hj_tab
          exact hm8_Sw v hv j hjv
        · rcases hm9 j hj_fix with hz | hloc
          · omega
          · exact hloc
      · unfold nodeExtents at hj_nd
        obtain ⟨n, hn, hjn⟩ := List.mem_flatMap.1 hj_nd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hjn
        rcases hjn with rfl | rfl
        · exact Or.inl (hTr.1.1 n hn).2.2.1
        · unfold nodePath at hj_pos ⊢
          split_ifs at hj_pos ⊢ with hc
          · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with hz | ⟨_, _, hin_k, _⟩
            · exact absurd hz hc.2
            · exact Or.inl hin_k
          · simp at hj_pos
    rcases hj_loc with hh | hm
    · exact Or.inl ⟨le_trans hh.1 hin.1, le_trans hin.2 hh.2⟩
    · exact Or.inr ⟨le_trans hm.1 hin.1, le_trans hin.2 hm.2⟩
  · exact Or.inl ⟨le_trans hAs.1 hfresh.1, le_trans hfresh.2 hAp.2.1⟩

theorem worldStepSc_to_evmStepCC {F : Type}
    {B : BufList} {gw gw_out : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : ValidBufList B)
    (hgw : SafeStepGlobals gw)
    (hgw_sub : ∀ g ∈ gw, g ∈ gw_out)
    (hInv_s : EvmInv s)
    (hstep : WorldStepSc (bufRegions B) gw keep Q s r post) :
    EvmStepCC gw_out s post := by
  obtain ⟨⟨hAp, hhp, hG, _, htyped⟩, hsc⟩ := hstep
  have hag : AllocatorGrows s post := ⟨hhp, hsc⟩
  obtain ⟨hAs, S, hInvAt⟩ := (evmInv_iff_at s).1 hInv_s
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW,
    hFO_pw, hFO_disj, hAT_fo, hMarks, hRoles, hGas⟩ := hInvAt
  obtain ⟨hT, hJ, hF, _⟩ := hW
  set ch := evmChain s
  -- 1. Single persistent-trie witness `Nd` avoiding all frame objects AND all frame messages.
  obtain ⟨Nd, hTr, hAT_fo_Nd, hAT_msg_Nd⟩ :=
    avoidsTries_join_msgs hAT_fo (fun ec hec => (hFW_all ec hec).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hWT_S : WorldTypedWith s S Nd := ⟨hT, hJ, hF, hTr⟩
  -- 2. Strip frame-local tables `L` from `S`.
  let L : List Nat := ch.flatMap fun ec =>
    [memW s (ec.1 + 136), memW s (ec.1 + 168), memW s (ec.1 + 176)]
  have hL_local : ∀ t ∈ L, ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t := by
    intro t ht
    obtain ⟨ec, hec, ht_ec⟩ := List.mem_flatMap.1 ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht_ec
    rcases ht_ec with rfl | rfl | rfl
    · exact frameRole_ne_worldOrJournal hRoles (rf := "frame.del")
        (List.mem_flatMap.2 ⟨ec, hec, by simp⟩) (by decide)
    · exact frameRole_ne_worldOrJournal hRoles (rf := "frame.addr")
        (List.mem_flatMap.2 ⟨ec, hec, by simp⟩) (by decide)
    · exact frameRole_ne_worldOrJournal hRoles (rf := "frame.key")
        (List.mem_flatMap.2 ⟨ec, hec, by simp⟩) (by decide)
  obtain ⟨S_w, F_rem, hnd_F, hF_in, hL_not_Sw, hperm_S, hWT_Sw⟩ :=
    worldTypedWith_strip_frame_tables hWT_S L hL_local
  have hSw_sub_S : ∀ t ∈ S_w, t ∈ S :=
    fun t ht => hperm_S.symm.subset (List.mem_append_left _ ht)
  have hF_sub_S : ∀ t ∈ F_rem, t ∈ S :=
    fun t ht => hperm_S.symm.subset (List.mem_append_right _ ht)
  -- 3. Instantiate `WorldStep` on `(S_w, Nd)`.
  have hR_disj : IvlsDisj (bufRegions B s) (worldTypedIvls s S_w Nd) :=
    validBufList_disj hB hWT_Sw
  obtain ⟨S_w', Nd', hSw_sub_Sw', hWT_Sw', hgrow, hfr, _⟩ := htyped S_w Nd hWT_Sw hR_disj
  have hold_z : ∀ j ∈ worldOwned s S_w Nd, j.2 = 0 → j.1 % 8 = 0 :=
    worldOwned_zero_aligned hWT_Sw
  have hR_z : ∀ j ∈ bufRegions B s, j.2 = 0 → j.1 % 8 = 0 :=
    bufRegions_zero_aligned hB hF
  -- 4. Kept globals.
  have hg_keep : ∀ g : String,
      ofString g ∉ (["heap_ptr", "scratch_ptr", "journal_n"] : List String).map ofString →
      globN post g = globN s g :=
    fun g hnot => globN_eq_of_lookup (hG (ofString g) (hgw.not_mem_map hnot))
  have hev_eq : globN post "ev" = globN s "ev" := hg_keep "ev" (by decide)
  have hcc_eq : globN post "cur_cont" = globN s "cur_cont" := hg_keep "cur_cont" (by decide)
  have hfm_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := hg_keep "frame_mem_ptr" (by decide)
  have hevm_empty_eq : globN post "evm_empty" = globN s "evm_empty" := hg_keep "evm_empty" (by decide)
  have hvmsa_eq : globN post "vm_system_address" = globN s "vm_system_address" :=
    hg_keep "vm_system_address" (by decide)
  -- 5. Disjointness of `frameObjects`, `msg`, and `F_rem` from `worldOwned s S_w Nd` and `bufRegions B s`,
  --    and preservation across `OwnedGrows`.
  have hfo_disj_old : ∀ ec ∈ ch, ∀ o ∈ frameObjects s ec, ∀ j ∈ worldOwned s S_w Nd, Disj o j := by
    intro ec hec o ho j hj
    unfold worldOwned at hj
    rcases List.mem_append.1 hj with hj1 | hj_nd
    · rcases List.mem_append.1 hj1 with hj_tab | hj_fix
      · obtain ⟨u, hu, hju⟩ := List.mem_flatMap.1 hj_tab
        exact (hFO_disj ec hec o ho).1 u (hSw_sub_S u hu) j hju
      · exact (hFO_disj ec hec o ho).2 j hj_fix
    · have hflat : o ∈ (ch.map (frameObjects s)).flatten :=
        List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map_of_mem hec, ho⟩
      exact hAT_fo_Nd o hflat j hj_nd
  have hfo_disj_new : ∀ ec ∈ ch, ∀ o ∈ frameObjects s ec, ∀ j ∈ worldOwned post S_w' Nd', Disj o j :=
    fun ec hec o ho => allocatedEvm_disj_ownedGrows hAs.2 hAp.2 hhp
      (frameObject_zero_or_allocatedEvm hAs.2 (hFW_all ec hec) ho)
      (hfo_disj_old ec hec o ho) hgrow
  have hfo_unhit : ∀ ec ∈ ch, ∀ o ∈ frameObjects s ec, WordsOK s o → IvlUnhit s post o := by
    intro ec hec o ho hwo
    exact ivlUnhit_of_worldStep_frameOutside hAs.2 hfr hold_z hR_z hwo.1 hwo.2.1
      (frameObject_zero_or_allocatedEvm hAs.2 (hFW_all ec hec) ho)
      (hfo_disj_old ec hec o ho)
      (bufRegions_disj_of_disj_fixedObjects hB (hFO_disj ec hec o ho).2)
  have hfo_bound : ∀ ec ∈ ch, ∀ o ∈ frameObjects s ec, o.2 = 0 ∨ o.1 + o.2 ≤ 2 ^ 64 := by
    intro ec hec o ho
    rcases frameObject_zero_or_allocatedEvm hAs.2 (hFW_all ec hec) ho with hz | hal
    · exact Or.inl hz
    · exact Or.inr (allocatedEvm_bound hAs.2 hal)
  -- 6. Frame records, `evmChain`, `ChainCellsAgree`, `frameLogs`, `frameRet`, `frameLogObjects`, `frameObjects`.
  have hrec_eq : ∀ ec ∈ ch,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    have hw1 : WordsOK s (ec.1, 280) := (hFW.1 (ec.1, 280) (by simp)).2
    have hw2 : WordsOK s (ec.2, 104) := (hFW.1 (ec.2, 104) (by simp)).2
    have hw88 : WordsOK s (memW s (ec.1 + 88), 24) := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2
    have hb1 : ec.1 + 280 ≤ 2 ^ 64 := by
      rcases hfo_bound ec hec (ec.1, 280) (by simp [frameObjects]) with h0 | hb
      · simp at h0
      · exact hb
    have hb2 : ec.2 + 104 ≤ 2 ^ 64 := by
      rcases hfo_bound ec hec (ec.2, 104) (by simp [frameObjects]) with h0 | hb
      · simp at h0
      · exact hb
    have hb88 : memW s (ec.1 + 88) + 24 ≤ 2 ^ 64 := by
      rcases hfo_bound ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]) with h0 | hb
      · simp at h0
      · exact hb
    have he1_8 := hw1.1; have he2_8 := hw2.1; have he88_8 := hw88.1
    refine ⟨fun k hk hk8 => memW_eq_of_ivlUnhit
              (hfo_unhit ec hec (ec.1, 280) (by simp [frameObjects]) hw1) (by omega) hb1 ⟨by omega, by omega⟩,
            fun k hk hk8 => memW_eq_of_ivlUnhit
              (hfo_unhit ec hec (ec.2, 104) (by simp [frameObjects]) hw2) (by omega) hb2 ⟨by omega, by omega⟩,
            fun k hk hk8 => memW_eq_of_ivlUnhit
              (hfo_unhit ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]) hw88) (by omega) hb88 ⟨by omega, by omega⟩⟩
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ ch) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ ch := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = ch := by
    unfold evmChain; rw [hev_eq, hcc_eq]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hcc_agree : ChainCellsAgree s post := by
    intro ec hec
    obtain ⟨he_eq, hc_eq, _⟩ := hrec_eq ec hec
    exact ⟨he_eq 24 (by omega) (by omega), he_eq 32 (by omega) (by omega),
           he_eq 40 (by omega) (by omega), hc_eq 56 (by omega) (by omega)⟩
  have hframeLogs_eq : ∀ ec ∈ ch, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by
          simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ ch, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ ch,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    set logs := memW s (ec.1 + 88)
    have hl0 : memW post logs = memW s logs := by simpa [logs] using h88_eq 0 (by omega) (by omega)
    have hl8 : memW post (logs + 8) = memW s (logs + 8) := h88_eq 8 (by omega) (by omega)
    have hl16 : memW post (logs + 16) = memW s (logs + 16) := h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (logs + 8) →
        memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (logs + 8) ≤ memW s (logs + 16) := hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_w : WordsOK s (frameLogs s ec) := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : memW s logs + 8 * memW s (logs + 16) ≤ 2 ^ 64 := by
        rcases hfo_bound ec hec (frameLogs s ec) hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only [logs] at h0 hi hlen_le; omega
        · simpa [frameLogs, logs] using hb
      have hfl_8 : (memW s logs) % 8 = 0 := hfl_w.1
      exact memW_eq_of_ivlUnhit
        (hfo_unhit ec hec (frameLogs s ec) hfl_in hfl_w)
        (by omega) hfl_b
        ⟨by simp only [frameLogs]; dsimp only [logs] at hi hlen_le ⊢; omega,
         by simp only [frameLogs]; dsimp only [logs] at hi hlen_le ⊢; omega⟩
    have hlr_eq : ∀ i (hi : i < memW s (logs + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s logs + 8 * i) + off) = memW s (memW s (memW s logs + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s logs + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only [logs]
        refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩
        unfold logOwnedIvls logRecordIvls
        exact List.mem_filter.2 ⟨by simp, by simp⟩
      have hlr_b : memW s (memW s logs + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfo_bound ec hec _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_w : WordsOK s (memW s (memW s logs + 8 * i), 40) := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (logs, 24) (by simp [logs])).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          have hss0 : 0 < scratchStart := by decide
          dsimp only at he88_in; omega
        · exact (hent i hi).2.1
      have hlr_8 := hlr_w.1
      exact memW_eq_of_ivlUnhit
        (hfo_unhit ec hec _ hlr_in hlr_w) (by omega) hlr_b ⟨by omega, by omega⟩
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hvmsa_eq]
    · rw [he_eq 88 (by omega) (by omega)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨wordsOK_transfer_local hAs.1 hAp.1 hw_l, hag.allocated hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        have hwa_post : WordAt post (memW s logs + 8 * i) := by
          obtain ⟨_, hdom, _⟩ := hwa
          rcases hm : post.memory (BitVec.ofNat 64 (memW s logs + 8 * i)) with ⟨w⟩
          exact ⟨w, hAp.1.memaddrs.trans hAs.1.memaddrs.symm ▸ hdom, hm⟩
        refine ⟨hwa_post, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32]
        exact ⟨wordsOK_transfer_local hAs.1 hAp.1 hle.1,
          ⟨hle.2.1.1, le_trans hle.2.1.2 hhp⟩,
          hle.2.2.1, hle.2.2.2.1,
          ⟨hle.2.2.2.2.1.1, le_trans hle.2.2.2.2.1.2 hhp⟩,
          ⟨hle.2.2.2.2.2.1.1, le_trans hle.2.2.2.2.2.1.2 hhp⟩,
          ⟨hle.2.2.2.2.2.2.1, le_trans hle.2.2.2.2.2.2.2 hhp⟩⟩
  have hframeObjects_eq : ∀ ec ∈ ch, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ ch, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 88 (by omega) (by omega)]
  have hmap_fo_eq : (ch.map (frameObjects post)).flatten = (ch.map (frameObjects s)).flatten := by
    congr 1; exact List.map_congr_left hframeObjects_eq
  -- 7. Preserve `F_rem` tables and adjoin `F_rem` onto `S_w'`.
  have hF_disj_old : ∀ t ∈ F_rem, ∀ i ∈ htabFootprint s t, ∀ j ∈ worldOwned s S_w Nd, Disj i j := by
    intro t ht i hi j hj
    have htS := hF_sub_S t ht
    have ht_not_Sw := (hF_in t ht).2
    unfold worldOwned at hj
    rcases List.mem_append.1 hj with hj1 | hj_nd
    · rcases List.mem_append.1 hj1 with hj_tab | hj_fix
      · obtain ⟨u, hu, hju⟩ := List.mem_flatMap.1 hj_tab
        have hne : t ≠ u := fun heq => ht_not_Sw (heq ▸ hu)
        exact hT.2.2.1 t htS u (hSw_sub_S u hu) hne i hi j hju
      · exact ((hT.2.1 t htS).2 i hi).2 j hj_fix
    · exact disj_comm ((hTr.2.1 j hj_nd).1 t htS i hi)
  have hF_unhit : ∀ t ∈ F_rem, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
    intro t ht i hi
    have htS := hF_sub_S t ht
    have hwo := ((hT.2.1 t htS).1.1 i hi).2
    have hal := ((hT.2.1 t htS).2 i hi).1
    exact ivlUnhit_of_worldStep_frameOutside hAs.2 hfr hold_z hR_z hwo.1 hwo.2.1
      (Or.inr (allocatedEvm_of_allocated hal))
      (hF_disj_old t ht i hi)
      (bufRegions_disj_of_disj_fixedObjects hB ((hT.2.1 t htS).2 i hi).2)
  have hF_hdr_fp : ∀ t ∈ F_rem,
      (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
    intro t ht
    have htS := hF_sub_S t ht
    have hwf := (hT.2.1 t htS).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; omega
    exact htabFootprint_eq_of_hdr_unhit ht8 hhi (hF_unhit t ht _ ht_fp)
  have hwf_F_post : ∀ t ∈ F_rem, HtabWF post t :=
    fun t ht => htabWF_congr_unhit hAs.1 hAp.1 (hT.2.1 t (hF_sub_S t ht)).1 (hF_unhit t ht)
  have hall_F_post : ∀ t ∈ F_rem, ∀ i ∈ htabFootprint post t, Allocated post i := by
    intro t ht i hi
    rw [(hF_hdr_fp t ht).2] at hi
    exact hag.allocated (((hT.2.1 t (hF_sub_S t ht)).2 i hi).1)
  have hdj_F_Sw' : ∀ t ∈ F_rem, ∀ i ∈ htabFootprint post t, ∀ o ∈ worldOwned post S_w' Nd', Disj i o := by
    intro t ht i hi
    rw [(hF_hdr_fp t ht).2] at hi
    have hal := ((hT.2.1 t (hF_sub_S t ht)).2 i hi).1
    exact allocatedEvm_disj_ownedGrows hAs.2 hAp.2 hhp
      (Or.inr (allocatedEvm_of_allocated hal))
      (hF_disj_old t ht i hi) hgrow
  have hdj_FF_post : ∀ t ∈ F_rem, ∀ u ∈ F_rem, t ≠ u →
      ∀ i ∈ htabFootprint post t, ∀ j ∈ htabFootprint post u, Disj i j := by
    intro t ht u hu hne i hi j hj
    rw [(hF_hdr_fp t ht).2] at hi
    rw [(hF_hdr_fp u hu).2] at hj
    exact hT.2.2.1 t (hF_sub_S t ht) u (hF_sub_S u hu) hne i hi j hj
  set S' := S_w' ++ F_rem
  have hWT_S' : WorldTypedWith post S' Nd' :=
    adjoin_local_table_list hWT_Sw' F_rem hnd_F hwf_F_post hall_F_post hdj_F_Sw' hdj_FF_post
  have hS_sub_S' : ∀ t ∈ S, t ∈ S' := by
    intro t ht
    rcases List.mem_append.1 (hperm_S.subset ht) with htw | htf
    · exact List.mem_append_left _ (hSw_sub_Sw' t htw)
    · exact List.mem_append_right _ htf
  have hnd_S' : S'.Nodup := hWT_S'.1.1
  have hSw'_disj_F : ∀ a ∈ S_w', ∀ b ∈ F_rem, a ≠ b := by
    intro a ha b hb heq
    subst heq
    obtain ⟨_, _, hdj⟩ := List.nodup_append.1 hnd_S'
    exact hdj a ha a hb rfl
  -- 8. `RolesOK post S' (worldRoleSlots post ++ frameRoleSlots post ch) (journalRoleSlots post)`.
  have hfrs_eq : frameRoleSlots post ch = frameRoleSlots s ch := by
    unfold frameRoleSlots
    apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega),
        he_eq 176 (by omega) (by omega)]
  have hfrs_in_F : ∀ b ∈ frameRoleSlots s ch, b.1 ∈ F_rem := by
    intro b hb
    have hbS : b.1 ∈ S :=
      (hRoles.1 b (List.mem_append_left _ (List.mem_append_right _ hb))).1
    have hbL : b.1 ∈ L := by
      unfold frameRoleSlots at hb
      obtain ⟨ec, hec, hbec⟩ := List.mem_flatMap.1 hb
      refine List.mem_flatMap.2 ⟨ec, hec, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbec
      rcases hbec with rfl | rfl | rfl <;> simp
    rcases List.mem_append.1 (hperm_S.subset hbS) with hbw | hbf
    · exact absurd hbw (hL_not_Sw b.1 hbL)
    · exact hbf
  have hRoles_Sw' : RolesOK post S_w' (worldRoleSlots post) (journalRoleSlots post) :=
    hWT_Sw'.1.2.2.2.2.2.2.2.2.2.2.2
  have hRoles_S' : RolesOK post S' (worldRoleSlots post ++ frameRoleSlots post ch) (journalRoleSlots post) := by
    rw [hfrs_eq]
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with hasl | hajr
      · rcases List.mem_append.1 hasl with haw | hafr
        · obtain ⟨haSw', hhdr⟩ := hRoles_Sw'.1 a (List.mem_append_left _ haw)
          exact ⟨List.mem_append_left _ haSw', hhdr⟩
        · have haF := hfrs_in_F a hafr
          have hhdr_s := (hRoles.1 a (List.mem_append_left _ (List.mem_append_right _ hafr))).2
          exact ⟨List.mem_append_right _ haF, ((hF_hdr_fp a.1 haF).1 0 (by omega)).trans hhdr_s⟩
      · obtain ⟨haSw', hhdr⟩ := hRoles_Sw'.1 a (List.mem_append_right _ hajr)
        exact ⟨List.mem_append_left _ haSw', hhdr⟩
    · have hpw_fr : (frameRoleSlots s ch).Pairwise
          (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) :=
        (List.pairwise_append.1 hRoles.2.1).2.1
      refine List.pairwise_append.2 ⟨hRoles_Sw'.2.1, hpw_fr, ?_⟩
      intro a ha b hb heq
      have haSw' := (hRoles_Sw'.1 a (List.mem_append_left _ ha)).1
      exact absurd heq (hSw'_disj_F a.1 haSw' b.1 (hfrs_in_F b hb))
    · intro a ha b hb heq
      have haSw' := (hRoles_Sw'.1 a (List.mem_append_right _ ha)).1
      rcases List.mem_append.1 hb with hbsl | hbjr
      · rcases List.mem_append.1 hbsl with hbw | hbfr
        · exact hRoles_Sw'.2.2 a ha b (List.mem_append_left _ hbw) heq
        · exact absurd heq (hSw'_disj_F a.1 haSw' b.1 (hfrs_in_F b hbfr))
      · exact hRoles_Sw'.2.2 a ha b (List.mem_append_right _ hbjr) heq
  -- 9. `DelExclusive` preservation for `u ∈ F_rem`.
  have hdelEx_F : ∀ (i : Nat) (hi : i + 1 < ch.length) (u : Nat),
      u ∈ F_rem → DelExclusive s S ch i u → DelExclusive post S' ch i u := by
    intro i hi u huF ⟨_, hu_frames⟩
    have huS' : u ∈ S' := List.mem_append_right _ huF
    have hu_nz : u ≠ 0 := fun h0 => zero_not_mem_S hWT_S'.1 (h0 ▸ huS')
    refine ⟨?_, ?_⟩
    · intro hw_post
      obtain ⟨r_u, hru⟩ := worldTableRefs_in_worldOrJournalRoleSlots hWT_S'.1 hu_nz hw_post
      have huSw' : u ∈ S_w' := (hRoles_Sw'.1 (u, r_u) hru).1
      exact hSw'_disj_F u huSw' u huF rfl
    · intro j hj k hk hmem_eq
      have hj_mem : ch[j] ∈ ch := List.getElem_mem _
      have hk_le : k + 8 ≤ 280 ∧ k % 8 = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [(hrec_eq _ hj_mem).1 k hk_le.1 hk_le.2] at hmem_eq
      exact hu_frames j hj k hk hmem_eq
  -- 10. Assemble `EvmInv post` and `EvmStepCC gw_out s post`.
  have hW_post : WorldTyped post S' := (worldTyped_iff_with post S').2 ⟨Nd', hWT_S'⟩
  have hG_out : GlobalsKept gw_out s post := by
    intro k hk
    apply hG k
    intro hmem
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hmem
    exact hk (List.mem_map.2 ⟨g, hgw_sub g hg, rfl⟩)
  have hmap_gas : (ch.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
      (ch.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
    apply List.map_congr_left; intro ec hec
    rw [(hrec_eq ec hec).1 64 (by decide) (by decide),
        (hrec_eq ec hec).1 192 (by decide) (by decide)]
  refine ⟨⟨?_, hhp, hG_out, hchain_eq⟩, hcc_agree⟩
  refine (evmInv_iff_at post).2 ⟨hAp, S', hW_post, ?_⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, hmap_fo_eq ▸ hFO_pw, ?_, ?_, ?_, hRoles_S', hmap_gas ▸ hGas⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S' (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega)]
      set m := memW s (ec.1 + 112)
      obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, _⟩ := c17
      have hm_disj_old : ∀ j ∈ worldOwned s S_w Nd, Disj (m, 176) j := by
        intro j hj
        unfold worldOwned at hj
        rcases List.mem_append.1 hj with hj1 | hj_nd
        · rcases List.mem_append.1 hj1 with hj_tab | hj_fix
          · obtain ⟨u, hu, hju⟩ := List.mem_flatMap.1 hj_tab
            exact hdt u (hSw_sub_S u hu) j hju
          · exact hdf j hj_fix
        · exact hAT_msg_Nd ec hec j hj_nd
      have hm_disj_new : ∀ j ∈ worldOwned post S_w' Nd', Disj (m, 176) j :=
        allocatedEvm_disj_ownedGrows hAs.2 hAp.2 hhp
          (Or.inr (allocatedEvm_of_allocated hal_m)) hm_disj_old hgrow
      refine ⟨hag.allocated hal_m, wordsOK_transfer_local hAs.1 hAp.1 hw_m, ?_, ?_, ?_,
        ⟨Nd', hWT_S'.2.2.2, fun o ho j hj => ?_⟩⟩
      · intro u hu i hi
        rcases List.mem_append.1 hu with huw | huf
        · apply hm_disj_new i
          unfold worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, huw, hi⟩))
        · rw [(hF_hdr_fp u huf).2] at hi
          exact hdt u (hF_sub_S u huf) i hi
      · intro j hj
        apply hm_disj_new j
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ hj)
      · rw [hchain_eq]
        intro ec' hec' o ho
        rw [hframeObjects_eq ec' hec'] at ho
        exact hdfo ec' hec' o ho
      · simp only [List.mem_singleton] at ho; subst ho
        apply hm_disj_new j
        unfold worldOwned
        exact List.mem_append_right _ hj
    unfold FrameWF; dsimp only
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
        he_eq 40 (by omega) (by omega), he_eq 16 (by omega) (by omega),
        he_eq 32 (by omega) (by omega), he_eq 136 (by omega) (by omega),
        he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec, he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
        hframeRet_eq ec hec, hfm_eq, hevm_empty_eq]
    rw [he_eq 88 (by omega) (by omega)] at hlo_ok
    refine ⟨fun i hi => ⟨⟨le_trans hsc (c1 i hi).1.1, (c1 i hi).1.2⟩,
              wordsOK_transfer_local hAs.1 hAp.1 (c1 i hi).2⟩,
      c2, wordsOK_transfer_local hAs.1 hAp.1 c3, c4, c5, c6, c7,
      hS_sub_S' _ c8, hS_sub_S' _ c9, hS_sub_S' _ c10, c11, c12,
      ?_, wordsOK_transfer_local hAs.1 hAp.1 c14, ?_, hlo_ok, hmsg_ok⟩
    · rcases c13 with h | h
      · exact Or.inl ⟨h.1, le_trans h.2 hhp⟩
      · exact Or.inr ⟨le_trans hsc h.1, h.2⟩
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨⟨hin.1, le_trans hin.2 hhp⟩, wordsOK_transfer_local hAs.1 hAp.1 hw⟩
  · intro ec hec
    have hec_mem := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_eq ec hec_mem).1 16 (by omega) (by omega),
        (hrec_eq ec hec_mem).1 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : ch[i]'(by omega) ∈ ch := List.getElem_mem _
    have hi1 : ch[i + 1] ∈ ch := List.getElem_mem _
    rw [(hrec_eq _ hi0).2.1 80 (by decide) (by decide),
        (hrec_eq _ hi0).2.1 72 (by decide) (by decide),
        (hrec_eq _ hi1).1 40 (by decide) (by decide)]
    exact hRW i hi
  · intro ec hec o ho
    have ho_s : o ∈ frameObjects s ec := by rwa [← hframeObjects_eq ec hec]
    refine ⟨fun u hu i hi => ?_, fun j hj => ?_⟩
    · rcases List.mem_append.1 hu with huw | huf
      · apply hfo_disj_new ec hec o ho_s i
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, huw, hi⟩))
      · rw [(hF_hdr_fp u huf).2] at hi
        exact (hFO_disj ec hec o ho_s).1 u (hF_sub_S u huf) i hi
    · apply hfo_disj_new ec hec o ho_s j
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_right _ hj)
  · rw [hmap_fo_eq]
    refine ⟨Nd', hWT_S'.2.2.2, fun o ho j hj => ?_⟩
    obtain ⟨fo, hfo_map, ho_fo⟩ := List.mem_flatten.1 ho
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
    apply hfo_disj_new ec hec o ho_fo j
    unfold worldOwned
    exact List.mem_append_right _ hj
  · intro i hi
    have hi_mem : ch[i]'(by omega) ∈ ch := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega)
    have htake_eq : (ch.take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        (ch.take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
    have hM := hMarks i hi
    dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    have hm8_Sw : ∀ v ∈ S_w, ∀ k ∈ htabFootprint s v,
        Inside k sourceBase heapLimit ∨ Inside k (memW s ((ch[i]'(by omega)).2 + 48)) scratchEnd := by
      intro v hv
      rcases m8 v (hSw_sub_S v hv) with ⟨htake, _⟩ | hloc
      · obtain ⟨ec_v, hec_take, hv_eq⟩ := List.mem_map.1 htake
        have hvL : v ∈ L := by
          rw [← hv_eq]
          exact List.mem_flatMap.2 ⟨ec_v, List.mem_of_mem_take hec_take, by simp⟩
        exact absurd hv (hL_not_Sw v hvL)
      · exact hloc
    have howned_loc := worldOwned_inside_heap_or_mark_of_ownedGrows
      hAs.2 hAp.2 hhp hSw_sub_S hTr hm8_Sw m9 hgrow
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, ?_⟩
    · intro j hj hij
      have hj_mem : ch[j] ∈ ch := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by omega)]
      exact m5 j hj hij
    · intro u hu
      rcases List.mem_append.1 hu with huw | huf
      · right
        intro o ho
        have hpos := htabFootprint_len_pos (hWT_Sw'.1.2.1 u huw).1 o ho
        apply howned_loc o _ hpos
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, huw, ho⟩))
      · rw [(hF_hdr_fp u huf).2]
        rcases m8 u (hF_sub_S u huf) with ⟨htake, hdel⟩ | hloc
        · exact Or.inl ⟨htake, hdelEx_F i hi u huf hdel⟩
        · exact Or.inr hloc
    · intro o ho
      by_cases hz : o.2 = 0
      · exact Or.inl hz
      · right
        apply howned_loc o _ (Nat.pos_of_ne_zero hz)
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ ho)

theorem worldKeepsSc_to_evmKeeps_cc
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {B : BufList} {gw gw_out : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {R_av : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {fname : MlS}
    (hB : ValidBufList B)
    (hgw : SafeStepGlobals gw)
    (hgw_sub : ∀ g ∈ gw, g ∈ gw_out)
    (hP : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), EvmAvoids R_av s → P s)
    (hwk : WorldKeepsSc P (bufRegions B) gw keep Q fname) :
    EvmKeeps (EvmAvoids R_av) gw_out fname ∧ ChainCellsKept (EvmAvoids R_av) fname := by
  obtain ⟨ps, body, ret, hl, hb⟩ := hwk
  have hevm_of_av : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), EvmAvoids R_av s → EvmInv s :=
    fun s h => ⟨h.1, h.2.elim fun S hS => ⟨S, hS.1⟩⟩
  refine ⟨⟨ps, body, ret, hl, fun s hc hav hsh hnt hr => ?_⟩,
          ⟨ps, body, ret, hl, fun s hc hav hsh hnt hr => ?_⟩⟩
  · exact (worldStepSc_to_evmStepCC hB hgw hgw_sub (hevm_of_av s hav)
      (hb s hc (hP s hav) hsh hnt hr)).1
  · exact (worldStepSc_to_evmStepCC hB hgw hgw_sub (hevm_of_av s hav)
      (hb s hc (hP s hav) hsh hnt hr)).2

/-! ## Milestone 2: `move_ether` (`wkSc_move_ether`, `ek_move_ether`, `cc_move_ether`) -/

section MoveEther
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

private theorem lookup_move_ether_local :
    originalRuntimeCode.lookup (ofString "move_ether") =
      some ((sourceFunctionEntry Guest.Software.guestFn_move_ether).2) :=
  lookup_of_guestAst_getElem 395 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_move_ether) rfl

private theorem noCallee_good_local :
    ∀ f, (fun (_ : MlS) => false) f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      roProgR16 (fun _ => false) body = true :=
  fun _ hf => by cases hf

private theorem ro_u256_lt_local : ReadOnlyFn (ofString "u256_lt") :=
  readOnlyFn_of_roProgR16 46 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_lt rfl (fun _ => false) noCallee_good_local (by decide)

private theorem ro_u256_sub_local : ReadOnlyFn (ofString "u256_sub") :=
  Wave8Contracts.M18.ro_u256_sub

private theorem worldEff_call0_memcpy_local {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (dstExp srcExp nExp : ExpHOL 64)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).1)
    (hin : ∀ (dstw srcw nw : BitVec 64),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
        some (.val (.word dstw)) →
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp =
        some (.val (.word srcw)) →
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) nExp =
        some (.val (.word nw)) →
      0 < nw.toNat →
      (∃ j ∈ Rl, j.1 ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ dstw.toNat ∧
        dstw.toNat + nw.toNat ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ heapLimit)) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).2 Rl B gw := by
  by_cases hgood : ∃ (dw sw nw : BitVec 64),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
        some (.val (.word dw)) ∧
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp =
        some (.val (.word sw)) ∧
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) nExp =
        some (.val (.word nw))
  · obtain ⟨dw, sw, nw, hd, hsw, hn⟩ := hgood
    have hargs_good : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
        [dstExp, srcExp, nExp] = some [.val (.word dw), .val (.word sw), .val (.word nw)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, hd, hsw, hn]
    have hb := Fast_C08WkShard03.call0_byteEff Fast_C08WkShard03.funByteEff_memcpy cur
      [dstExp, srcExp, nExp] [(dw.toNat, nw.toNat)] h.code h.arena.1
      (fun vals hargs i hi _ => by
        rw [hargs_good] at hargs
        injection hargs with hargs_eq
        subst hargs_eq
        simp only [List.mem_singleton, Fast_C08WkShard03.valWordNat] at hi
        subst hi
        exact ⟨(dw.toNat, nw.toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
      hnt hor
    exact h.of_byteEff hb (fun iv hiv hpos => by
      simp only [List.mem_singleton] at hiv
      subst hiv
      exact hin dw sw nw hd hsw hn hpos)
  · have hpost_eq : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
        [dstExp, srcExp, nExp])).2 = cur := by
      rw [evaluateHOLFiniteState_call]
      rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
          [dstExp, srcExp, nExp] with _ | vals
      · rfl
      · dsimp only
        rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "memcpy") vals with _ | ⟨b', c', r'⟩
        · rfl
        · exfalso
          have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "memcpy") vals = some (b', c', r') := by
            rwa [← h.code]
          have hinst := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "memcpy")
            _ _ b' _ r' vals c' lookup_memcpy_r16 hl'
          have hret := lookupCodeHOLFinite_installed_return cur (ofString "memcpy")
            _ _ _ _ r' vals c' (by rw [h.code]; exact lookup_memcpy_r16) hl
          subst hinst hret
          obtain ⟨dw, sw, nw, hvals, _, _, _⟩ := Fast_C08WkShard03.lookupCode_three_words
            (by decide) (by decide) (by decide) lookup_memcpy_r16 hl'
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases hd : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp with _ | vd
          · simp [hd] at hargs
          · rcases hs : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp with _ | vs
            · simp [hd, hs] at hargs
            · rcases hn : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) nExp with _ | vn
              · simp [hd, hs, hn] at hargs
              · rw [hd, hs, hn] at hargs
                injection hargs with hargs_eq
                have hvals2 := hargs_eq.trans hvals
                injection hvals2 with h1 ht1; injection ht1 with h2 ht2; injection ht2 with h3 _
                subst h1 h2 h3
                exact hgood ⟨dw, sw, nw, hd, hs, hn⟩
    rwa [hpost_eq]

private theorem flattenHOL_shape_u256_local {v : ValueHOL 64}
    (hsh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true) :
    (flattenHOL v).length = 4 := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
  · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh)
    rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;>
      rcases v2 with ⟨⟨c⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨d⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
    simp [flattenHOL]
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh

private theorem shapeEq_u256_symm {v : ValueHOL 64} {rsh : ShapeHOL}
    (hsh : (shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) &&
      shapeEqHOL (shapeOfHOLExact v) rsh) = true) :
    shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true := by
  have h12 : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true := by
    revert hsh
    cases shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) <;> simp
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at h12
  · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h12; done)
    rcases v0 with ⟨⟨_⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨_⟩⟩ | _ | _ <;>
      rcases v2 with ⟨⟨_⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨_⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h12 ⊢
  · simp [shapeOfHOLExact, shapeEqHOL] at h12

private theorem acct_copy_var_step {F : Type} (vname : MlS) (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (.local, vname), none)) (ofString "acct_copy")
        [.var .local vname])).1 ≠ some .timeOut)
    (hfr : R16WkAcctWs.FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, vname), none)) (ofString "acct_copy")
        [.var .local vname])).1) :
    let res := (evaluateHOLFiniteState s
      (.call (some (some (.local, vname), none)) (ofString "acct_copy")
        [.var .local vname])).1
    let post := (evaluateHOLFiniteState s
      (.call (some (some (.local, vname), none)) (ofString "acct_copy")
        [.var .local vname])).2
    WorldEff s post [] [] ["heap_ptr"] ∧
    (res = none → ∃ bw : BitVec 64,
      post.locals = s.locals.update (vname, .val (.word bw)) ∧
      globN s "heap_ptr" ≤ bw.toNat ∧ bw.toNat + 56 ≤ heapLimit) := by
  dsimp only
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  have heff0 : WorldEff s s [] [] ["heap_ptr"] :=
    WorldEff.refl s [] [] ["heap_ptr"] hA hcode
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local vname] with _ | vals
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_copy") vals with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hb_eq : body' = sourceFnBody Guest.Software.guestFn_acct_copy :=
          lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "acct_copy")
            _ _ body' _ ret' vals callee lookup_acct_copy (by rwa [← hcode])
        have hr_eq : ret' = .one :=
          lookupCodeHOLFinite_installed_return s (ofString "acct_copy")
            _ _ _ _ ret' vals callee (by rw [hcode]; exact lookup_acct_copy) hl
        subst hb_eq hr_eq
        obtain ⟨aw, rfl, haw_c⟩ := lookupCode_one_word lookup_acct_copy (by rwa [← hcode])
        let ent := callEntryStateHOLFinite s callee
        have heff_ent : WorldEff s ent [] [] ["heap_ptr"] := heff0.locals_clock _ _
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_acct_copy) with ⟨rc, pc⟩
        have hrun_ent : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy) = (rc, pc) := hrun
        have hnt_ent : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy)).1 ≠ some .timeOut := by
          rw [hrun_ent]; rintro rfl; simp [hrun] at hnt
        simp only [hrun] at hnt hfr ⊢
        cases rc with
        | none => exact absurd hfr R16WkAcctWs.not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr R16WkAcctWs.not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr R16WkAcctWs.not_flowingOrResumes_finalFfi
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have heff_pc : WorldEff s pc [] [] ["heap_ptr"] := by
              have hbody_eq2 : sourceFnBody Guest.Software.guestFn_acct_copy =
                  .decCall (ofString "b") .one (ofString "alloc") [.const 56#64]
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                      (.return (.var .local (ofString "b")))) := rfl
              have hex_ev : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy)).1 =
                  some (.exception eid ev) := by dsimp only [ent]; rw [hrun]
              have hp_ev : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy)).2 = pc := by
                dsimp only [ent]; rw [hrun]
              rw [← hp_ev, hbody_eq2]
              refine worldEff_decCall_alloc heff_ent (by decide) (ofString "b") (.const 56#64)
                (by rw [← hbody_eq2]; exact hnt_ent)
                (by rw [← hbody_eq2, hex_ev]; exact Or.inr (Or.inr (Or.inr hres_ex)))
                (fun bw nw m1 hsz_ev _ hm1_loc _ heff_m1 _ _ hbw_lo hbw_end _ _ hnt1 hcr1 => ?_)
              have hnw_eq : nw = 56#64 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
              subst hnw_eq
              have hbw_hi : bw.toNat + 56 ≤ heapLimit := by
                change bw.toNat + (56 + 7) / 8 * 8 = globN m1 "heap_ptr" at hbw_end; omega
              have hm1_b : m1.locals.lookup (ofString "b") = some (.val (.word bw)) := by
                rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
              refine worldEff_seq hnt1 hcr1
                (fun hnt_mc hcr_mc => worldEff_call0_memcpy_local heff_m1 _ _ _ hnt_mc
                  (by rcases hcr_mc with h | h | h | hr
                      · exact Or.inl h
                      · exfalso
                        rw [evaluateHOLFiniteState_call] at h; split at h <;> try simp at h
                        split at h <;> try simp at h
                        split at h <;> try simp at h
                        split at h <;> try simp at h
                        · split at h <;> simp_all
                        · simp_all
                      · exfalso
                        rw [evaluateHOLFiniteState_call] at h; split at h <;> try simp at h
                        split at h <;> try simp at h
                        split at h <;> try simp at h
                        split at h <;> try simp at h
                        · split at h <;> simp_all
                        · simp_all
                      · exact Or.inr hr)
                  (fun dstw _ nw' hd _ hn _ => by
                    simp [evalHOLExact, toExact, hm1_b] at hd hn
                    subst hd hn
                    exact Or.inr (Or.inr (Or.inr ⟨hbw_lo, hbw_hi⟩))))
                (fun m2 _ heff_m2 _ _ => worldEff_return heff_m2 _)
            exact ⟨heff_pc.locals_clock _ _, fun h => by simp at h⟩
          | returned rv =>
            dsimp only at hfr ⊢
            split
            · rename_i hsh_rv
              split
              · have hbody_eq2 : sourceFnBody Guest.Software.guestFn_acct_copy =
                    .decCall (ofString "b") .one (ofString "alloc") [.const 56#64]
                      (.seq
                        (.call (some (none, none)) (ofString "memcpy")
                          [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                        (.return (.var .local (ofString "b")))) := rfl
                rw [hbody_eq2] at hrun_ent
                rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun_ent
                have hargs56 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
                    [.const 56#64] = some [.val (.word 56#64)] := by
                  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
                have hlk56 := pan_one_word_lookup ent.code.lookup (ofString "alloc") (ofString "n")
                  (sourceFnBody Guest.Software.guestFn_alloc) 56#64
                  (by rw [show ent.code = originalRuntimeCode from hcode]; exact lookup_alloc_r16)
                rw [hargs56] at hrun_ent; dsimp only at hrun_ent
                rw [hlk56] at hrun_ent; dsimp only at hrun_ent
                by_cases hcz_ent : ent.clock = 0
                · simp [hcz_ent] at hrun_ent
                rw [if_neg hcz_ent] at hrun_ent
                obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, ent.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
                  globalWord_of_globN_pos ent "heap_ptr"
                    (by have := heff_ent.arena.2.1; rw [sourceBase_val] at this; omega)
                let ent_al := callEntryStateHOLFinite ent (HolFiniteMapExact.empty.update (ofString "n", .val (.word 56#64)))
                rcases hrun_al : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ral, pal⟩
                dsimp only [ent_al] at hrun_al
                rw [hrun_al] at hrun_ent
                have hres_al : Wave8Contracts.M18.Resumes ral := by
                  cases ral with
                  | none => simp at hrun_ent
                  | some c0 =>
                    cases c0 with
                    | returned r0 => exact Or.inl ⟨r0, rfl⟩
                    | exception e0 v0 => dsimp only at hrun_ent; injection hrun_ent with hr0 _; cases hr0
                    | _ => simp at hrun_ent
                have hal := R13.alloc_body_resumes ent_al pw hcode hpw_lk
                  (by dsimp only [ent_al]; rw [hrun_al]; exact hres_al)
                dsimp only [ent_al] at hal
                rw [hrun_al] at hal
                obtain ⟨nw', hnw'_lk, hral_eq, hcmp1, hcmp2, hpal_eq⟩ := hal
                have hnw56 : nw' = 56#64 := by
                  simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at hnw'_lk; exact hnw'_lk.symm
                subst hnw56
                dsimp only at hral_eq hpal_eq
                subst hral_eq
                dsimp only at hrun_ent
                have hsh_pw : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
                    shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
                  simp [shapeOfHOLExact, shapeEqHOL]
                rw [if_pos hsh_pw] at hrun_ent
                set m1 := setVarHOLFinite (ofString "b") (.val (.word pw)) { pal with locals := ent.locals }
                have hm1_next : m1 = { ent with
                    globals := ent.globals.update (ofString "heap_ptr", .val (.word ((pw + (56#64 + 7)) &&& ((0 : BitVec 64) - 8)))),
                    locals := m1.locals, clock := m1.clock } := by
                  dsimp only [m1, setVarHOLFinite]; rw [hpal_eq]; rfl
                obtain ⟨heff_m1, _, _, _, hp_lo_s, hp_add, hp_hi, _⟩ :=
                  worldEff_alloc_step heff_ent (by decide) hpw_lk hcmp1 hcmp2 hm1_next
                have hpw_hi : pw.toNat + 56 ≤ heapLimit := by
                  change pw.toNat + (56 + 7) / 8 * 8 = globN m1 "heap_ptr" at hp_add; omega
                have hm1_b : m1.locals.lookup (ofString "b") = some (.val (.word pw)) := by
                  simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                rcases hseq_m1 : evaluateHOLFiniteState m1
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                      (.return (.var .local (ofString "b")))) with ⟨rseq, pseq⟩
                rw [hseq_m1] at hrun_ent
                dsimp only at hrun_ent
                have hrseq_eq : rseq = some (.returned rv) := (Prod.mk.inj hrun_ent).1
                have hpc_pseq : pc = { pseq with locals := (HolFiniteMapExact.resVarEq pseq.locals
                    (ofString "b", ent.locals.lookup (ofString "b"))) } := ((Prod.mk.inj hrun_ent).2).symm
                rw [evaluateHOLFiniteState_seq_line780] at hseq_m1
                rcases hmc : evaluateHOLFiniteState m1
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64]) with ⟨rmc, m2⟩
                rw [hmc] at hseq_m1
                cases rmc with
                | some cr_mc =>
                  exfalso
                  dsimp only at hseq_m1
                  have hcr_ret : some cr_mc = some (.returned rv) := (Prod.mk.inj hseq_m1).1.trans hrseq_eq
                  injection hcr_ret with hcr_eq; subst hcr_eq
                  rw [evaluateHOLFiniteState_call] at hmc
                  rcases ha_mc : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
                      [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64] with _ | vs_mc
                  · rw [ha_mc] at hmc; simp at hmc
                  · rw [ha_mc] at hmc; dsimp only at hmc
                    rcases hl_mc : lookupCodeHOLFinite m1.code.lookup (ofString "memcpy") vs_mc with _ | ⟨bmc, cmc, rmc'⟩
                    · rw [hl_mc] at hmc; simp at hmc
                    · rw [hl_mc] at hmc; dsimp only at hmc
                      by_cases hcz_m1 : m1.clock = 0
                      · simp [hcz_m1] at hmc
                      · rw [if_neg hcz_m1] at hmc
                        rcases hrun_mc : evaluateHOLFiniteState (callEntryStateHOLFinite m1 cmc) bmc with ⟨rmc0, pmc0⟩
                        rw [hrun_mc] at hmc
                        cases rmc0 with
                        | none => simp at hmc
                        | some c0 =>
                          cases c0 with
                          | returned v0 =>
                            dsimp only at hmc
                            by_cases hsh0 : shapeEqHOL (shapeOfHOLExact v0) rmc' = true
                            · simp [hsh0] at hmc
                            · simp [hsh0] at hmc
                          | exception _ _ => simp at hmc
                          | _ => simp at hmc
                | none =>
                  dsimp only at hseq_m1
                  have heff_m2 : WorldEff s m2 [] [] ["heap_ptr"] := by
                    have hw := worldEff_call0_memcpy_local heff_m1
                      (.var .local (ofString "b")) (.var .local (ofString "a")) (.const 56#64)
                      (by rw [hmc]; simp) (by rw [hmc]; exact Or.inl rfl)
                      (fun dstw _ nw' hd _ hn _ => by
                        simp [evalHOLExact, toExact, hm1_b] at hd hn
                        subst hd hn
                        exact Or.inr (Or.inr (Or.inr ⟨hp_lo_s, hpw_hi⟩)))
                    rw [hmc] at hw; exact hw
                  have hm2_loc : m2.locals = m1.locals := by
                    have hk := fun k => evaluate_avoidsLocal_flowing k
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                      rfl m1 (by rw [hmc]; exact Or.inl rfl)
                    apply HolFiniteMapExact.ext; funext k; simpa [hmc] using hk k
                  rw [evaluateHOLFiniteState_return] at hseq_m1
                  simp only [evalHOLExact, toExact, hm2_loc, hm1_b, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                    show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hseq_m1
                  have hrv_pw_opt : (some (PanSemResultExact.returned (.val (.word pw))) : Option (PanSemResultExact 64)) =
                      some (PanSemResultExact.returned rv) :=
                    (Prod.mk.inj hseq_m1).1.trans hrseq_eq
                  injection hrv_pw_opt with hrv_eq
                  injection hrv_eq with hrv_eq'
                  subst hrv_eq'
                  have hpseq_eq : pseq = { m2 with locals := HolFiniteMapExact.empty } :=
                    ((Prod.mk.inj hseq_m1).2).symm
                  have hpc_m2 : pc = { m2 with locals := pc.locals, clock := pc.clock } := by
                    rw [hpc_pseq, hpseq_eq]
                  have heff_out : WorldEff s (setVarHOLFinite vname (.val (.word pw)) { pc with locals := s.locals })
                      [] [] ["heap_ptr"] := by
                    rw [hpc_m2]; exact heff_m2.locals_clock _ _
                  exact ⟨heff_out, fun _ => ⟨pw, rfl, hp_lo_s, hpw_hi⟩⟩
              · rename_i hbad; simp only [hsh_rv, hbad, ↓reduceIte] at hfr
                exact absurd hfr R16WkAcctWs.not_flowingOrResumes_error
            · rename_i hbad; simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hfr
              exact absurd hfr R16WkAcctWs.not_flowingOrResumes_error

theorem wkSc_move_ether :
    WorldKeepsSc WorldOK (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
      stdKeep NoExtra (ofString "move_ether") := by
  have hB := validBufList_acctMutBufs
  have hgw := safeStepGlobals_hp_jn_sp
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  have hB_ga : ∀ p ∈ wsAcctBufs, p ∈ acctMutBufs := by
    intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs]
  have hgw_ga : ∀ g ∈ (["heap_ptr", "scratch_ptr"] : List String), g ∈ ["heap_ptr", "journal_n", "scratch_ptr"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp
  have hB_msc : ∀ p ∈ ([("sk_buf", 52)] : BufList), p ∈ acctMutBufs := by
    intro p hp; simp at hp; subst hp; simp [acctMutBufs]
  have hgw_msc : ∀ g ∈ (["heap_ptr", "journal_n"] : List String), g ∈ ["heap_ptr", "journal_n", "scratch_ptr"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp
  refine R16WkAcctWs.worldKeepsSc_of_progWStep lookup_move_ether_local ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_move_ether,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  -- 1. `decCall "s" "get_account" [sender]`
  refine R16WkAcctWs.progWStep_decCall hB hgw hB_ga hgw_ga wkSc_get_account ?_
  -- 2. `decCall "lt" "u256_lt" [load (s + 8), amount]`
  refine R16WkAcctWs.progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (R16WkAcctWs.worldKeepsSc_of_readOnly ro_u256_lt_local) ?_
  -- 3. `seq (ite (lt != 0) (raise "StateErr" 4) skip) ...`
  refine R16WkAcctWs.progWStep_seq hB hgw
    (R16WkAcctWs.progWStep_ite (R16WkAcctWs.progWStep_raise _ _ _ _) (R16WkAcctWs.progWStep_skip _ _)) ?_
  -- 4. `seq (call "s" "acct_copy" [s]) (decCall "nb" "u256_sub" [load (s+8), amount] (seq (store (s+8) nb) ...))`
  intro F s0 hc0 hW0 hnt0 hfr0
  rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
  rcases h1 : evaluateHOLFiniteState s0
      (.call (some (some (.local, ofString "s"), none)) (ofString "acct_copy")
        [.var .local (ofString "s")]) with ⟨r1, s1⟩
  simp only [h1] at hnt0 hfr0 ⊢
  cases r1 with
  | some cr1 =>
    have hac := acct_copy_var_step (ofString "s") s0 hc0 hW0.1 (by rw [h1]; exact hnt0) (by rw [h1]; exact hfr0)
    rw [h1] at hac
    have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s0 (some cr1) s1 :=
      hac.1.to_worldStep_Q hW0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
    exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, hac.1.sp_hi⟩
  | none =>
    dsimp only at hnt0 hfr0 ⊢
    have hac := acct_copy_var_step (ofString "s") s0 hc0 hW0.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    rw [h1] at hac; dsimp only at hac
    obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
    have hs1_s : s1.locals.lookup (ofString "s") = some (.val (.word bw)) := by
      rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt0 hfr0 ⊢
    rcases hargs_nb : @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        [.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "s"), .const 8#64]),
         .var .local (ofString "amount")] with _ | vnb_args
    · simp [evalListHOLFinite, hargs_nb] at hfr0; exact absurd hfr0 R16WkAcctWs.not_flowingOrResumes_error
    · simp only [evalListHOLFinite, hargs_nb] at hnt0 hfr0 ⊢
      rcases hl_nb : lookupCodeHOLFinite s1.code.lookup (ofString "u256_sub") vnb_args with _ | ⟨bnb, cnb, rnb⟩
      · simp [hl_nb] at hfr0; exact absurd hfr0 R16WkAcctWs.not_flowingOrResumes_error
      · simp only [hl_nb] at hnt0 hfr0 ⊢
        by_cases hcz1 : s1.clock = 0
        · simp [hcz1] at hnt0
        rw [if_neg hcz1] at hnt0 hfr0 ⊢
        rcases hrun_nb : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb with ⟨res_nb, p_nb⟩
        have hrun_nb' : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb = (res_nb, p_nb) := hrun_nb
        simp only [hrun_nb] at hnt0 hfr0 ⊢
        cases res_nb with
        | none => exact absurd hfr0 R16WkAcctWs.not_flowingOrResumes_error
        | some cr_nb =>
          cases cr_nb with
          | timeOut => simp at hnt0
          | error | «break» | «continue» => exact absurd hfr0 R16WkAcctWs.not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr0 R16WkAcctWs.not_flowingOrResumes_finalFfi
          | exception eid ev =>
            dsimp only at hfr0 ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr0 with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, rfl⟩ := h
              exact Or.inr ⟨eid, ev, rfl, hne⟩
            have hro := FunSpec.at_lookup ro_u256_sub_local s1 hac.1.code vnb_args bnb cnb rnb hl_nb
              (guestInv_callEntry s1 cnb hac.1.arena.1) (by rw [hrun_nb']; simp)
            have hro' : ((evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb).2) = _ :=
              hro (by rw [hrun_nb']; exact hres_ex)
            rw [hrun_nb'] at hro'; dsimp only at hro'
            have heff_ex : WorldEff s0 (emptyLocalsHOLFinite p_nb) [] [] ["heap_ptr"] :=
              (hac.1.of_readOnly hro').locals_clock _ p_nb.clock
            have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra
                s0 (some (.exception eid ev)) (emptyLocalsHOLFinite p_nb) :=
              heff_ex.to_worldStep_Q hW0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
            exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, heff_ex.sp_hi⟩
          | returned vnb =>
            dsimp only at hnt0 hfr0 ⊢
            by_cases hsh_nb : (shapeEqHOL (shapeOfHOLExact vnb) (.comb [.one, .one, .one, .one]) &&
                shapeEqHOL (shapeOfHOLExact vnb) rnb) = true
            · simp only [hsh_nb, ↓reduceIte] at hnt0 hfr0 ⊢
              have hsh_u256 : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vnb) = true :=
                shapeEq_u256_symm hsh_nb
              have hro := FunSpec.at_lookup ro_u256_sub_local s1 hac.1.code vnb_args bnb cnb rnb hl_nb
                (guestInv_callEntry s1 cnb hac.1.arena.1) (by rw [hrun_nb']; simp)
              have hro' : ((evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb).2) = _ :=
                hro (by rw [hrun_nb']; exact Or.inl ⟨vnb, rfl⟩)
              rw [hrun_nb'] at hro'; dsimp only at hro'
              set s2 := setVarHOLFinite (ofString "nb") vnb { p_nb with locals := s1.locals }
              have heff2 : WorldEff s0 s2 [] [] ["heap_ptr"] :=
                (hac.1.of_readOnly hro').locals_clock _ _
              have hs2_s : s2.locals.lookup (ofString "s") = some (.val (.word bw)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_s,
                  show ofString "nb" ≠ ofString "s" by decide]
              have hs2_nb : s2.locals.lookup (ofString "nb") = some vnb := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
              rcases hst : evaluateHOLFiniteState s2
                  (.store (.op .add [.var .local (ofString "s"), .const 8#64]) (.var .local (ofString "nb"))) with ⟨rst, s3⟩
              simp only [hst] at hnt0 hfr0 ⊢
              have heff3 : WorldEff s0 s3 [] [] ["heap_ptr"] := by
                have hs3_eq : s3 = (evaluateHOLFiniteState s2
                    (.store (.op .add [.var .local (ofString "s"), .const 8#64]) (.var .local (ofString "nb")))).2 := by
                  rw [hst]
                rw [hs3_eq]
                exact worldEff_store_multi heff2 _ _ 4 (by decide)
                  (fun v hv => by
                    simp [evalHOLExact, toExact, hs2_nb] at hv
                    subst hv
                    exact flattenHOL_shape_u256_local hsh_u256)
                  (fun x hx => by
                    simp [evalHOLExact, evalListHOLExact, toExact, hs2_s, panOpHOL, wordOpHOL, wordOp,
                      valueIsWord, valueWord] at hx
                    subst hx
                    have hx8 : (bw + 8#64).toNat = bw.toNat + 8 := by
                      apply BitVec.toNat_add_of_lt; change bw.toNat + 8 < 2 ^ 64; omega
                    exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩)
              have hstep03 : WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                  stdKeep NoExtra s0 rst s3 := by
                have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s0 rst s3 :=
                  heff3.to_worldStep_Q hW0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
                exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, heff3.sp_hi⟩
              cases rst with
              | some cr_st =>
                exact hstep03.with_locals_clock _ _
              | none =>
                dsimp only at hnt0 hfr0 ⊢
                have hWs3 : WorldOK s3 := hstep03.worldOK_bufs hB hW0
                -- 5. Now run `seq (call modify_state_commit [sender, s]) (decCall "r" "get_account" [recipient] ...)` on `s3`!
                have htail_prog : R16WkAcctWs.ProgWStep acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"]
                    (.seq (.call (some (none, none)) (ofString "modify_state_commit")
                            [.var .local (ofString "sender"), .var .local (ofString "s")])
                      (.decCall (ofString "r") .one (ofString "get_account") [.var .local (ofString "recipient")]
                        (.seq (.call (some (some (.local, ofString "r"), none)) (ofString "acct_copy")
                                [.var .local (ofString "r")])
                          (.seq (.call (some (some (.local, ofString "nb"), none)) (ofString "u256_add")
                                  [.load (.comb [.one, .one, .one, .one])
                                     (.op .add [.var .local (ofString "r"), .const 8#64]),
                                   .var .local (ofString "amount")])
                            (.seq (.store (.op .add [.var .local (ofString "r"), .const 8#64])
                                    (.var .local (ofString "nb")))
                              (.seq (.call (some (none, none)) (ofString "modify_state_commit")
                                      [.var .local (ofString "recipient"), .var .local (ofString "r")])
                                (.return (.const 0#64)))))))) := by
                  refine R16WkAcctWs.progWStep_seq hB hgw
                    (R16WkAcctWs.progWStep_call0 hB_msc hgw_msc wkSc_modify_state_commit) ?_
                  refine R16WkAcctWs.progWStep_decCall hB hgw hB_ga hgw_ga wkSc_get_account ?_
                  --Recipient `acct_copy` + `u256_add` + `store` + `modify_state_commit` + `return 0`:
                  intro F' t0 htc0 hWt0 hnt_t0 hfr_t0
                  rw [evaluateHOLFiniteState_seq_line780] at hnt_t0 hfr_t0 ⊢
                  rcases hr1 : evaluateHOLFiniteState t0
                      (.call (some (some (.local, ofString "r"), none)) (ofString "acct_copy")
                        [.var .local (ofString "r")]) with ⟨rr1, t1⟩
                  simp only [hr1] at hnt_t0 hfr_t0 ⊢
                  cases rr1 with
                  | some crr1 =>
                    have hac_r := acct_copy_var_step (ofString "r") t0 htc0 hWt0.1
                      (by rw [hr1]; exact hnt_t0) (by rw [hr1]; exact hfr_t0)
                    rw [hr1] at hac_r
                    have hws_r0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra
                        t0 (some crr1) t1 :=
                      hac_r.1.to_worldStep_Q hWt0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
                    exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws_r0, hac_r.1.sp_hi⟩
                  | none =>
                    dsimp only at hnt_t0 hfr_t0 ⊢
                    have hac_r := acct_copy_var_step (ofString "r") t0 htc0 hWt0.1
                      (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
                    rw [hr1] at hac_r; dsimp only at hac_r
                    obtain ⟨bwr, ht1_loc, hbwr_lo, hbwr_hi⟩ := hac_r.2 rfl
                    have ht1_r : t1.locals.lookup (ofString "r") = some (.val (.word bwr)) := by
                      rw [ht1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                    rw [evaluateHOLFiniteState_seq_line780] at hnt_t0 hfr_t0 ⊢
                    rcases hadd : evaluateHOLFiniteState t1
                        (.call (some (some (.local, ofString "nb"), none)) (ofString "u256_add")
                          [.load (.comb [.one, .one, .one, .one])
                             (.op .add [.var .local (ofString "r"), .const 8#64]),
                           .var .local (ofString "amount")]) with ⟨radd, t2⟩
                    simp only [hadd] at hnt_t0 hfr_t0 ⊢
                    -- Unpack `call (some (some (.local, "nb"), none)) "u256_add"` on `t1`:
                    have hadd_eff : WorldEff t0 t2 [] [] ["heap_ptr"] ∧
                        (radd = none → ∃ vadd : ValueHOL 64,
                          t2.locals = t1.locals.update (ofString "nb", vadd) ∧
                          shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vadd) = true) := by
                      have hnt_add : (evaluateHOLFiniteState t1
                          (.call (some (some (.local, ofString "nb"), none)) (ofString "u256_add")
                            [.load (.comb [.one, .one, .one, .one])
                               (.op .add [.var .local (ofString "r"), .const 8#64]),
                             .var .local (ofString "amount")])).1 ≠ some .timeOut := by
                        rw [hadd]; cases radd with | none => simp | some ca => cases ca <;> simp at hnt_t0 ⊢
                      have hfr_add : R16WkAcctWs.FlowingOrResumes (evaluateHOLFiniteState t1
                          (.call (some (some (.local, ofString "nb"), none)) (ofString "u256_add")
                            [.load (.comb [.one, .one, .one, .one])
                               (.op .add [.var .local (ofString "r"), .const 8#64]),
                             .var .local (ofString "amount")])).1 := by
                        rw [hadd]; cases radd with | none => exact Or.inl rfl | some ca => exact hfr_t0
                      rw [evaluateHOLFiniteState_call] at hadd hnt_add hfr_add
                      rcases ha_a : @evalListHOLExact 64 F' _ t1.toExact (fun a => Classical.propDecidable (t1.memaddrs a))
                          [.load (.comb [.one, .one, .one, .one])
                             (.op .add [.var .local (ofString "r"), .const 8#64]),
                           .var .local (ofString "amount")] with _ | vs_a
                      · simp [evalListHOLFinite, ha_a] at hfr_add
                        exact absurd hfr_add R16WkAcctWs.not_flowingOrResumes_error
                      · simp only [evalListHOLFinite, ha_a] at hadd hnt_add hfr_add
                        rcases hl_a : lookupCodeHOLFinite t1.code.lookup (ofString "u256_add") vs_a with _ | ⟨ba, ca, ra⟩
                        · simp [hl_a] at hfr_add
                          exact absurd hfr_add R16WkAcctWs.not_flowingOrResumes_error
                        · simp only [hl_a] at hadd hnt_add hfr_add
                          by_cases hcz_t1 : t1.clock = 0
                          · simp [hcz_t1] at hnt_add
                          rw [if_neg hcz_t1] at hadd hnt_add hfr_add
                          have hra_eq : ra = .comb [.one, .one, .one, .one] :=
                            lookupCodeHOLFinite_installed_return t1 (ofString "u256_add")
                              _ _ _ _ ra vs_a ca (by rw [hac_r.1.code]; exact lookup_u256_add) hl_a
                          subst hra_eq
                          rcases hrun_a : evaluateHOLFiniteState (callEntryStateHOLFinite t1 ca) ba with ⟨resa, pa⟩
                          have hrun_a' : evaluateHOLFiniteState (callEntryStateHOLFinite t1 ca) ba = (resa, pa) := hrun_a
                          simp only [hrun_a] at hadd hnt_add hfr_add
                          cases resa with
                          | none => exact absurd hfr_add R16WkAcctWs.not_flowingOrResumes_error
                          | some cra =>
                            cases cra with
                            | timeOut => simp at hnt_add
                            | error | «break» | «continue» =>
                              exact absurd hfr_add R16WkAcctWs.not_flowingOrResumes_error
                            | finalFfi _ => exact absurd hfr_add R16WkAcctWs.not_flowingOrResumes_finalFfi
                            | exception eid2 ev2 =>
                              dsimp only at hadd hfr_add
                              have hres_ex2 : Wave8Contracts.M18.Resumes (some (.exception eid2 ev2)) := by
                                rcases hfr_add with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
                                obtain ⟨rfl, rfl⟩ := h
                                exact Or.inr ⟨eid2, ev2, rfl, hne⟩
                              have hro2 := FunSpec.at_lookup ro_u256_add t1 hac_r.1.code vs_a ba ca _ hl_a
                                (guestInv_callEntry t1 ca hac_r.1.arena.1) (by rw [hrun_a']; simp)
                              have hro2' : ((evaluateHOLFiniteState (callEntryStateHOLFinite t1 ca) ba).2) = _ :=
                                hro2 (by rw [hrun_a']; exact hres_ex2)
                              rw [hrun_a'] at hro2'; dsimp only at hro2'
                              obtain ⟨hradd_eq, ht2_eq⟩ := Prod.mk.inj hadd
                              rw [← ht2_eq, ← hradd_eq]
                              exact ⟨(hac_r.1.of_readOnly hro2').locals_clock _ _, fun h => by simp at h⟩
                            | returned vadd =>
                              dsimp only at hadd hfr_add
                              split at hadd
                              · rename_i hsh_vadd
                                split at hadd
                                · rename_i hval_vadd
                                  have hro2 := FunSpec.at_lookup ro_u256_add t1 hac_r.1.code vs_a ba ca _ hl_a
                                    (guestInv_callEntry t1 ca hac_r.1.arena.1) (by rw [hrun_a']; simp)
                                  have hro2' : ((evaluateHOLFiniteState (callEntryStateHOLFinite t1 ca) ba).2) = _ :=
                                    hro2 (by rw [hrun_a']; exact Or.inl ⟨vadd, rfl⟩)
                                  rw [hrun_a'] at hro2'; dsimp only at hro2'
                                  obtain ⟨hradd_eq, ht2_eq⟩ := Prod.mk.inj hadd
                                  rw [← ht2_eq, ← hradd_eq]
                                  have hsh_symm : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vadd) = true :=
                                    shapeEq_u256_symm (rsh := .comb [.one, .one, .one, .one]) (by simp [hsh_vadd])
                                  exact ⟨(hac_r.1.of_readOnly hro2').locals_clock _ _,
                                    fun _ => ⟨vadd, rfl, hsh_symm⟩⟩
                                · rename_i hbad_val
                                  simp only [hsh_vadd, hbad_val, Bool.false_eq_true, ↓reduceIte] at hfr_add
                                  exact absurd hfr_add R16WkAcctWs.not_flowingOrResumes_error
                              · rename_i hbad
                                simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hfr_add
                                exact absurd hfr_add R16WkAcctWs.not_flowingOrResumes_error
                    cases radd with
                    | some cr_add =>
                      have hws_r1 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra
                          t0 (some cr_add) t2 :=
                        hadd_eff.1.to_worldStep_Q hWt0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
                      exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws_r1, hadd_eff.1.sp_hi⟩
                    | none =>
                      dsimp only at hnt_t0 hfr_t0 ⊢
                      obtain ⟨vadd, ht2_loc, hsh_vadd⟩ := hadd_eff.2 rfl
                      have ht2_r : t2.locals.lookup (ofString "r") = some (.val (.word bwr)) := by
                        rw [ht2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht1_r,
                          show ofString "nb" ≠ ofString "r" by decide]
                      have ht2_nb : t2.locals.lookup (ofString "nb") = some vadd := by
                        rw [ht2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                      rw [evaluateHOLFiniteState_seq_line780] at hnt_t0 hfr_t0 ⊢
                      rcases hst_r : evaluateHOLFiniteState t2
                          (.store (.op .add [.var .local (ofString "r"), .const 8#64])
                            (.var .local (ofString "nb"))) with ⟨rst_r, t3⟩
                      simp only [hst_r] at hnt_t0 hfr_t0 ⊢
                      have heff_t3 : WorldEff t0 t3 [] [] ["heap_ptr"] := by
                        have ht3_eq : t3 = (evaluateHOLFiniteState t2
                            (.store (.op .add [.var .local (ofString "r"), .const 8#64])
                              (.var .local (ofString "nb")))).2 := by rw [hst_r]
                        rw [ht3_eq]
                        exact worldEff_store_multi hadd_eff.1 _ _ 4 (by decide)
                          (fun v hv => by
                            simp [evalHOLExact, toExact, ht2_nb] at hv
                            subst hv
                            exact flattenHOL_shape_u256_local hsh_vadd)
                          (fun x hx => by
                            simp [evalHOLExact, evalListHOLExact, toExact, ht2_r, panOpHOL, wordOpHOL, wordOp,
                              valueIsWord, valueWord] at hx
                            subst hx
                            have hx8 : (bwr + 8#64).toNat = bwr.toNat + 8 := by
                              apply BitVec.toNat_add_of_lt; change bwr.toNat + 8 < 2 ^ 64; omega
                            exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩)
                      have hstep_t03 : WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                          stdKeep NoExtra t0 rst_r t3 := by
                        have hws_r2 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra
                            t0 rst_r t3 :=
                          heff_t3.to_worldStep_Q hWt0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
                        exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws_r2, heff_t3.sp_hi⟩
                      cases rst_r with
                      | some cr_str => exact hstep_t03
                      | none =>
                        dsimp only at hnt_t0 hfr_t0 ⊢
                        have hWt3 : WorldOK t3 := hstep_t03.worldOK_bufs hB hWt0
                        have hfin := R16WkAcctWs.progWStep_seq hB hgw
                          (R16WkAcctWs.progWStep_call0 hB_msc hgw_msc wkSc_modify_state_commit)
                          (R16WkAcctWs.progWStep_return _ _ _)
                          t3 heff_t3.code hWt3 hnt_t0 hfr_t0
                        exact WorldStepSc.trans hB hgw hstep_t03 hfin
                have htail_step := htail_prog s3 heff3.code hWs3 hnt0 hfr0
                exact WorldStepSc.trans hB hgw hstep03 (htail_step.with_locals_clock _ _)
            · simp [hsh_nb] at hfr0; exact absurd hfr0 R16WkAcctWs.not_flowingOrResumes_error

private theorem ek_cc_move_ether :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "move_ether") ∧
    ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "move_ether") :=
  worldKeepsSc_to_evmKeeps_cc validBufList_acctMutBufs safeStepGlobals_hp_jn_sp
    (by intro g hg; simp [frameStartGw] at hg ⊢; rcases hg with rfl | rfl | rfl <;> simp)
    (fun s hav => worldOK_of_evmInv s ⟨hav.1, hav.2.elim fun S hS => ⟨S, hS.1⟩⟩)
    wkSc_move_ether

theorem ek_move_ether :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "move_ether") :=
  ek_cc_move_ether.1

theorem cc_move_ether :
    ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "move_ether") :=
  ek_cc_move_ether.2

end MoveEther

def FrameStartSysReady {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr") ∧
    memW s (memW s (globN s "ev" + 88) + 8) + 1 < 2 ^ 28

theorem head_log_count_succ_lt_of_evmInv {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    memW s (memW s (globN s "ev" + 88) + 8) + 1 < 2 ^ 28 := by
  obtain ⟨hAs, S, hInvAt⟩ := hInv
  have hFW := hInvAt.2.2.2.2.1 (globN s "ev", globN s "cur_cont") List.mem_cons_self
  have hlen_le : memW s (memW s (globN s "ev" + 88) + 8) ≤
      memW s (memW s (globN s "ev" + 88) + 16) :=
    hFW.2.2.2.2.2.2.2.2.2.2.2.1
  have hfl_in :
      (Inside (frameLogs s (globN s "ev", globN s "cur_cont")) sourceBase (globN s "heap_ptr") ∨
        Inside (frameLogs s (globN s "ev", globN s "cur_cont")) (globN s "scratch_ptr") scratchEnd) :=
    hFW.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcap_lt : memW s (memW s (globN s "ev" + 88) + 16) < 2 ^ 25 := by
    rcases hfl_in with hheap | hscratch
    · have hhl := hAs.2.2.1
      rw [R11Shards.heapLimit_val] at hhl
      rw [R11Shards.sourceBase_val] at hheap
      unfold frameLogs Inside at hheap
      dsimp only at hheap
      omega
    · have hlo := hAs.2.2.2.1
      have hmid := hAs.2.2.2.2.1
      rw [R11Shards.scratchStart_val] at hlo
      rw [R11Shards.scratchEnd_val] at hscratch
      unfold frameLogs Inside at hscratch
      dsimp only at hscratch
      omega
  omega

theorem frameStartSysReady_of_evmInv {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (hsys : Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")) :
    FrameStartSysReady s :=
  ⟨hsys, head_log_count_succ_lt_of_evmInv hInv⟩

theorem ek_cc_of_readOnly {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS}
    (hP : ∀ {F : Type} {s : PanSemStateFiniteExact 64 F}, P s → EvmInv s)
    (hf : ReadOnlyFn fname) :
    EvmKeeps P [] fname ∧ ChainCellsKept P fname := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  refine ⟨⟨params, body, ret, hlook, ?_⟩, ⟨params, body, ret, hlook, ?_⟩⟩
  · intro F s hcode hPs hex hnt hres
    have hInv : EvmInv s := hP hPs
    have heq := hspec s hcode hInv.1.1 hex hnt hres
    exact (EvmFrameSpecs.evmStep_refl_locals_clock hInv heq).1
  · intro F s hcode hPs hex hnt hres
    have hInv : EvmInv s := hP hPs
    have heq := hspec s hcode hInv.1.1 hex hnt hres
    intro ec hec
    rw [heq]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem logEntryOK_of_transfer {F : Type}
    {s : PanSemStateFiniteExact 64 F} {log topics data : Nat}
    (hwords : WordsOK s (log, 40))
    (hlog : Inside (log, 40) sourceBase (globN s "heap_ptr"))
    (hsys : Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (htopics : Inside (topics, 96) sourceBase (globN s "heap_ptr"))
    (hdata : Inside (data, 32) sourceBase (globN s "heap_ptr"))
    (haddr : memW s log = globN s "vm_system_address")
    (htopics_ptr : memW s (log + 8) = topics)
    (htopics_len : memW s (log + 16) = 3)
    (hdata_ptr : memW s (log + 24) = data)
    (hdata_len : memW s (log + 32) = 32) :
    LogEntryOK s log := by
  unfold LogEntryOK
  rw [haddr, htopics_ptr, htopics_len, hdata_ptr, hdata_len]
  exact ⟨hwords, hlog, by decide, by decide, hsys, htopics, hdata⟩

theorem logOwnedIvls_of_transfer {F : Type}
    {s : PanSemStateFiniteExact 64 F} {log topics data : Nat}
    (haddr : memW s log = globN s "vm_system_address")
    (htopics_ptr : memW s (log + 8) = topics)
    (htopics_len : memW s (log + 16) = 3)
    (hdata_ptr : memW s (log + 24) = data)
    (hdata_len : memW s (log + 32) = 32) :
    logOwnedIvls s log = [(log, 40), (topics, 96), (data, 32)] := by
  unfold logOwnedIvls logRecordIvls
  rw [haddr, htopics_ptr, htopics_len, hdata_ptr, hdata_len]
  simp

theorem transfer_allocations_pairwise (log topics data : Nat)
    (hlog_topics : log + 40 ≤ topics)
    (htopics_data : topics + 96 ≤ data) :
    ([(log, 40), (topics, 96), (data, 32)] : List Ivl).Pairwise Disj := by
  refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, by simp⟩⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl hlog_topics))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact Or.inr (Or.inr (Or.inl htopics_data))

theorem transfer_logOwnedIvls_pairwise {F : Type}
    {s : PanSemStateFiniteExact 64 F} {log topics data : Nat}
    (haddr : memW s log = globN s "vm_system_address")
    (htopics_ptr : memW s (log + 8) = topics)
    (htopics_len : memW s (log + 16) = 3)
    (hdata_ptr : memW s (log + 24) = data)
    (hdata_len : memW s (log + 32) = 32)
    (hlog_topics : log + 40 ≤ topics)
    (htopics_data : topics + 96 ≤ data) :
    (logOwnedIvls s log).Pairwise Disj := by
  rw [logOwnedIvls_of_transfer haddr htopics_ptr htopics_len hdata_ptr hdata_len]
  exact transfer_allocations_pairwise log topics data hlog_topics htopics_data

theorem logsListOK_of_append {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs log : Nat}
    (hlogs : LogsListOK s logs) (hnz : logs ≠ 0)
    (hheader : WordsOK post (logs, 24)) (halloc : Allocated post (logs, 24))
    (hlen : memW post (logs + 8) = memW s (logs + 8) + 1)
    (hbound : memW s (logs + 8) + 1 < 2 ^ 28)
    (hcap : memW s (logs + 8) + 1 ≤ memW post (logs + 16))
    (hold : ∀ i, i < memW s (logs + 8) →
      WordAt post (memW post logs + 8 * i) ∧
        LogEntryOK post (memW post (memW post logs + 8 * i)))
    (hslot : WordAt post (memW post logs + 8 * memW s (logs + 8)))
    (hnew : memW post (memW post logs + 8 * memW s (logs + 8)) = log)
    (hentry : LogEntryOK post log) :
    LogsListOK post logs := by
  rcases hlogs with hz | hlogs
  · exact False.elim (hnz hz)
  · refine Or.inr ⟨hheader, halloc, by omega, by omega, ?_⟩
    intro i hi
    by_cases hlt : i < memW s (logs + 8)
    · exact hold i hlt
    · have hi_eq : i = memW s (logs + 8) := by omega
      subst i
      exact ⟨hslot, hnew ▸ hentry⟩

theorem frameLogObjects_of_append {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ec : Ivl} {log : Nat}
    (hheader : memW post (ec.1 + 88) = memW s (ec.1 + 88))
    (hlen : memW post (memW s (ec.1 + 88) + 8) =
      memW s (memW s (ec.1 + 88) + 8) + 1)
    (hold : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      logOwnedIvls post (memW post (memW post (memW s (ec.1 + 88)) + 8 * i)) =
        logOwnedIvls s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)))
    (hnew : memW post (memW post (memW s (ec.1 + 88)) +
      8 * memW s (memW s (ec.1 + 88) + 8)) = log) :
    frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls post log := by
  unfold frameLogObjects
  dsimp only
  rw [hheader, hlen, List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hnew]
  congr 1
  apply List.flatMap_congr
  intro i hi
  exact hold i (List.mem_range.mp hi)

theorem memW_slot_copied {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {p0 np n i : Nat}
    (hbe : post.be = s.be)
    (hp0_al : p0 % 8 = 0) (hnp_al : np % 8 = 0)
    (hp0_lt : p0 + 8 * n < 2 ^ 64) (hnp_lt : np + 8 * n < 2 ^ 64)
    (hi : i < n)
    (hcopy : ∀ b : Nat, b < 8 * n → memB post (np + b) = memB s (p0 + b)) :
    memW post (np + 8 * i) = memW s (p0 + 8 * i) := by
  refine (InitECandidate.Solver.Wave8GuestInv.SoloHtabSet.memW_eq_iff_memB hbe
    (by omega) (by omega) (by omega) (by omega)).mpr ?_
  intro r hr
  have h1 : np + 8 * i + r = np + (8 * i + r) := by omega
  have h2 : p0 + 8 * i + r = p0 + (8 * i + r) := by omega
  rw [h1, h2]
  exact hcopy (8 * i + r) (by omega)

private theorem chainCellsAgree_of_heap_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) :
    ChainCellsAgree s post := by
  have hword : ∀ base sz k : Nat, base + sz ≤ 2 ^ 64 → base % 8 = 0 → k % 8 = 0 → k + 8 ≤ sz →
      scratchStart ≤ base → memW post (base + k) = memW s (base + k) := by
    intro base sz k hbnd hb8 hk8 hk hss
    have hp_lim : globN post "heap_ptr" ≤ scratchStart := by
      have h1 := hAp.2.2.1
      rw [R11Shards.heapLimit_val] at h1
      rw [R11Shards.scratchStart_val]
      omega
    by_cases hdom : s.memaddrs (BitVec.ofNat 64 (base + k))
    · have hdom' := hAs.1.memaddrs ▸ hdom
      have hhe : (BitVec.ofNat 64 (base + k)).toNat < heapEnd :=
        (Wave8Contracts.M08.ordinaryDomain_iff _).mp hdom' |>.2.2
      have hhe_val : heapEnd = 33806089704 := R11Shards.heapEnd_val
      have ha8 : base + k + 8 < 2 ^ 64 := by
        by_cases hlt64 : base + k < 2 ^ 64
        · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at hhe
          omega
        · omega
      refine (InitECandidate.Solver.Wave8GuestInv.SoloHtabSet.memW_eq_iff_memB hbe
        (by omega) (by omega) ha8 ha8).mpr ?_
      intro r hr
      exact hbyte (base + k + r) (by omega) (by omega)
    · unfold memW
      rw [hout_dom _ hdom]
  intro ec hec
  have hFW := hInv.2.2.2.2.1 ec hec
  have hse_le : scratchEnd ≤ 2 ^ 64 := by
    rw [R11Shards.scratchEnd_val]
    decide
  have hb1 : ec.1 + 280 ≤ 2 ^ 64 := le_trans (hFW.1 (ec.1, 280) (by simp)).1.2 hse_le
  have hb2 : ec.2 + 104 ≤ 2 ^ 64 := le_trans (hFW.1 (ec.2, 104) (by simp)).1.2 hse_le
  have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
  have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
  have he1_ss : scratchStart ≤ ec.1 :=
    le_trans (le_trans hAs.2.2.2.1 hAs.2.2.2.2.1) (hFW.1 (ec.1, 280) (by simp)).1.1
  have he2_ss : scratchStart ≤ ec.2 :=
    le_trans (le_trans hAs.2.2.2.1 hAs.2.2.2.2.1) (hFW.1 (ec.2, 104) (by simp)).1.1
  exact ⟨hword ec.1 280 24 hb1 he1_8 (by omega) (by omega) he1_ss,
    hword ec.1 280 32 hb1 he1_8 (by omega) (by omega) he1_ss,
    hword ec.1 280 40 hb1 he1_8 (by omega) (by omega) he1_ss,
    hword ec.2 104 56 hb2 he2_8 (by omega) (by omega) he2_ss⟩

theorem frameStartSysReady_of_preserved_log_count {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hready : FrameStartSysReady s)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (hcount : memW post (memW post (globN post "ev" + 88) + 8) =
      memW s (memW s (globN s "ev" + 88) + 8)) :
    FrameStartSysReady post := by
  refine ⟨?_, ?_⟩
  · rw [hsys]
    exact ⟨hready.1.1, le_trans hready.1.2 hhp⟩
  · rw [hcount]
    exact hready.2

 theorem evmStepCC_of_fresh_heap_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg : GlobalsKept ["heap_ptr"] s post)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) :
    EvmStepCC ["heap_ptr"] s post := by
  obtain ⟨hinv, hchain, _⟩ :=
    OpHandlersB.evmInvAt_of_fresh_heap_step hAs hInv hAp hbe hhp hg hout hbyte
  exact ⟨⟨⟨hAp, S, hinv⟩, hhp, hg, hchain⟩,
    chainCellsAgree_of_heap_step hAs hInv hAp hbe hout hbyte⟩

theorem evmStepCC_of_allocated_heap_effect {F : Type}
    {s allocated post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s allocated)
    (hmem : allocated.memory = s.memory) (hbe : allocated.be = s.be)
    (heff : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect allocated post Rl)
    (hin : ∀ i ∈ Rl, Inside i (globN s "heap_ptr") (globN allocated "heap_ptr")) :
    EvmStepCC ["heap_ptr"] s post := by
  obtain ⟨hA, S, hAt⟩ := (evmInv_iff_at s).1 hInv
  have hAA : ArenaReady allocated := hstep.1.1.1
  have hAP : ArenaReady post := ⟨guestInv_congr heff.code heff.memaddrs
    heff.shMemaddrs heff.baseAddr hAA.1, arenaOK_congr heff.globals hAA.2⟩
  have hhp : globN post "heap_ptr" = globN allocated "heap_ptr" := by
    simp [globN, heff.globals]
  apply evmStepCC_of_fresh_heap_step hA hAt hAP (heff.be.trans hbe)
  · rw [hhp]; exact hstep.1.2.1
  · intro k hk
    rw [heff.globals]
    exact hstep.1.2.2.1 k hk
  · intro a ha
    rw [heff.out_dom a (by simpa [hAA.1.memaddrs, hA.1.memaddrs] using ha), hmem]
  · intro b hb hnot
    rw [heff.byte_frame b hb (by
      intro i hi hbi
      have hi' := hin i hi
      unfold Inside at hi'
      unfold InIvl at hbi
      exact hnot ⟨by omega, by rw [hhp]; omega⟩)]
    unfold memB
    rw [hmem, hbe]

theorem evmStepCC_of_accumulated_heap_effect {F : Type}
    {s allocated post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s allocated)
    (hbe : allocated.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → allocated.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN allocated "heap_ptr") →
      memB allocated b = memB s b)
    (heff : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect allocated post Rl)
    (hin : ∀ i ∈ Rl, Inside i (globN s "heap_ptr") (globN allocated "heap_ptr")) :
    EvmStepCC ["heap_ptr"] s post ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) := by
  obtain ⟨hA, S, hAt⟩ := (evmInv_iff_at s).1 hInv
  have hAA : ArenaReady allocated := hstep.1.1.1
  have hAP : ArenaReady post := ⟨guestInv_congr heff.code heff.memaddrs
    heff.shMemaddrs heff.baseAddr hAA.1, arenaOK_congr heff.globals hAA.2⟩
  have hhp : globN post "heap_ptr" = globN allocated "heap_ptr" := by
    simp [globN, heff.globals]
  have hout' : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a := by
    intro a ha
    rw [heff.out_dom a (by simpa [hAA.1.memaddrs, hA.1.memaddrs] using ha)]
    exact hout a ha
  have hbyte' : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b := by
    intro b hb hn
    rw [heff.byte_frame b hb (by
      intro i hi hbi
      have hi' := hin i hi
      unfold Inside at hi'
      unfold InIvl at hbi
      exact hn ⟨by omega, by rw [hhp]; omega⟩)]
    apply hbyte b hb
    simpa only [hhp] using hn
  refine ⟨evmStepCC_of_fresh_heap_step hA hAt hAP (heff.be.trans hbe) ?_ ?_ hout' hbyte',
    hout', hbyte'⟩
  · rw [hhp]; exact hstep.1.2.1
  · intro k hk
    rw [heff.globals]
    exact hstep.1.2.2.1 k hk

section HeadLogAppendInv

open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
  (globN_eq_of_lookup_eq allocated_mono_scr wordsOK_of_allocated_scr)
open InitECandidate.Solver.Wave8Contracts.M23

theorem evmStepCC_of_head_log_append {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd_at : List Nat}
    {freshArr : Ivl} {log : Nat} {newLogs : List Ivl}
    (hAs : ArenaReady s)
    (hInv : EvmInvAt s S)
    (hTr_at : TriesTypedWith s S Nd_at)
    (hAT_at : ∀ o ∈ ((evmChain s).map (frameObjects s)).flatten, ∀ j ∈ nodeExtents s Nd_at, Disj o j)
    (hApost : ArenaReady post)
    (heff : ByteRegionEffect s post
      [freshArr, (memW s (globN s "ev" + 88), 24),
       frameLogs s (globN s "ev", globN s "cur_cont")])
    (hfresh_alloc : freshArr = (0, 0) ∨
      (freshArr.1 % 8 = 0 ∧ freshArr.2 % 8 = 0 ∧
        Inside freshArr sourceBase (globN s "heap_ptr")))
    (hfresh_disj_s : ∀ x ∈ freshArr :: newLogs,
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj x i) ∧
      (∀ j ∈ fixedObjects s, Disj x j) ∧
      (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj x o) ∧
      (∀ j ∈ nodeExtents s Nd_at, Disj x j) ∧
      (∀ ec ∈ evmChain s, Disj x (memW s (ec.1 + 112), 176)))
    (hnewLogs_pw : (freshArr :: newLogs).Pairwise Disj)
    (harr_case :
      (freshArr = (0, 0) ∧
        memW post (memW s (globN s "ev" + 88)) = memW s (memW s (globN s "ev" + 88)) ∧
        memW post (memW s (globN s "ev" + 88) + 16) = memW s (memW s (globN s "ev" + 88) + 16)) ∨
      (freshArr.2 ≠ 0 ∧
        (memW post (memW s (globN s "ev" + 88)),
         8 * memW post (memW s (globN s "ev" + 88) + 16)) = freshArr))
    (hlen_post : memW post (memW s (globN s "ev" + 88) + 8) =
      memW s (memW s (globN s "ev" + 88) + 8) + 1)
    (hlen_lt : memW s (memW s (globN s "ev" + 88) + 8) + 1 < 2 ^ 28)
    (hcap_pos : 1 ≤ memW post (memW s (globN s "ev" + 88) + 16))
    (hcap_le : memW s (memW s (globN s "ev" + 88) + 8) + 1 ≤
      memW post (memW s (globN s "ev" + 88) + 16))
    (hold_slots : ∀ i, i < memW s (memW s (globN s "ev" + 88) + 8) →
      memW post (memW post (memW s (globN s "ev" + 88)) + 8 * i) =
        memW s (memW s (memW s (globN s "ev" + 88)) + 8 * i))
    (hnew_slot : memW post (memW post (memW s (globN s "ev" + 88)) +
      8 * memW s (memW s (globN s "ev" + 88) + 8)) = log)
    (hentry_post : LogEntryOK post log)
    (hnewLogs_eq : logOwnedIvls post log = newLogs) :
    EvmStepCC [] s post := by
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, _, hMarks, hRoles, hGas⟩ := hInv
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  set l0 := memW s (e0 + 88)
  set oldFl : Ivl := frameLogs s (e0, c0)
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  have hl0_8 : l0 % 8 = 0 := (hhead_FW.1 (l0, 24) (by simp [l0])).2.1
  have holdFl_8 : oldFl.1 % 8 = 0 := hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  have hRl_list : ∀ x ∈ ([freshArr, (l0, 24), oldFl] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rcases hfresh_alloc with rfl | ⟨h8, _⟩
      · rfl
      · exact h8
    · exact hl0_8
    · exact holdFl_8
  have hdom_eq : post.memaddrs = s.memaddrs := heff.memaddrs
  have hglob_eq : ∀ g : String, globN post g = globN s g := by
    intro g; unfold globN; rw [heff.globals]
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq "heap_ptr"]
  have hsc_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq "scratch_ptr"]
  have hfo_disj_wti : ∀ o ∈ frameObjects s (e0, c0), ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj o i := by
    intro o ho i hi
    unfold worldTypedIvls at hi; simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem o ho).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, ho⟩) i h6)
  have hfresh_disj_wti : ∀ x ∈ freshArr :: newLogs, ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj x i := by
    intro x hx i hi
    obtain ⟨hd_t, hd_f, _, hd_ne, _⟩ := hfresh_disj_s x hx
    unfold worldTypedIvls at hi; simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr (hd_t t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr (hd_f _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr (hd_f _ hfix_j)
    · exact Or.inr (hd_f _ (blockOut_in_fixedObjects h4))
    · exact Or.inr (hd_f _ (bal_in_fixedObjects h5))
    · exact Or.inr (hd_ne i h6)
  have hwrite_disj_wti : ∀ x ∈ ([freshArr, (l0, 24), oldFl] : List Ivl),
      ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj x i := by
    intro x hx i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hfresh_disj_wti x (by simp) i hi
    · exact hfo_disj_wti (l0, 24) (by simp [frameObjects, l0]) i hi
    · exact hfo_disj_wti oldFl (by simp [frameObjects, oldFl]) i hi
  have hcell : SameTypedCells s post S Nd_at :=
    ByteRegionEffect.sameTypedCells (Rl := []) (extra := [freshArr, (l0, 24), oldFl])
      hAs.1.memaddrs hWT (fun _ h => by simp at h) hwrite_disj_wti (by simpa using heff)
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [blockOutObjects_eq hAs.2 hWT.2.2.1 hcell (hglob_eq "bo"),
        balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell (hglob_eq "bal_accounts"),
        hglob_eq "journal", hglob_eq "journal_cap"]
    congr 3
    apply List.map_congr_left
    intro gn _
    rw [hglob_eq gn.1]
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc_le hfeq
  have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g _ => hglob_eq g
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc_le hcg hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hmemW_disj : ∀ {base sz k : Nat}, base + sz ≤ 2 ^ 64 → base % 8 = 0 → k % 8 = 0 → k + 8 ≤ sz →
      (∀ x ∈ ([freshArr, (l0, 24), oldFl] : List Ivl), Disj x (base, sz)) →
      memW post (base + k) = memW s (base + k) := by
    intro base sz k hbnd hb8 hk8 hk hdj
    unfold memW
    have ha : base + k < 2 ^ 64 := by omega
    have hbk8 : (base + k) % 8 = 0 := by omega
    have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
    rw [heff.cell_frame (BitVec.ofNat 64 (base + k))]
    intro x hx; rw [hbit]
    exact not_cellHits_of_disj_aligned (i := (base, sz)) hbk8 (hRl_list x hx)
      (Nat.le_add_right base k) (Nat.add_le_add_left hk base) (R11Shards.Disj.symm (hdj x hx))
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hhead_pw := hpw_head_tail.1
  unfold frameObjects at hhead_pw
  have hp0 := List.pairwise_cons.1 hhead_pw
  have hp1 := List.pairwise_cons.1 hp0.2
  have hp2 := List.pairwise_cons.1 hp1.2
  have hp3 := List.pairwise_cons.1 hp2.2
  have hp4 := List.pairwise_cons.1 hp3.2
  have hp5 := List.pairwise_cons.1 hp4.2
  have hp6 := List.pairwise_cons.1 hp5.2
  have hfresh_disj_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec,
      ∀ x ∈ freshArr :: newLogs, Disj x o :=
    fun ec hec o ho x hx => (hfresh_disj_s x hx).2.2.1 ec hec o ho
  have hlog_in_flo : ∀ ec : Ivl, ∀ i < memW s (memW s (ec.1 + 88) + 8),
      (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameLogObjects s ec := by
    intro ec i hi; unfold frameLogObjects; dsimp only
    exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
  have hwrite_disj_ec : ∀ ec ∈ evmChain s,
      (∀ x ∈ ([freshArr, (l0, 24), oldFl] : List Ivl), Disj x (ec.1, 280)) ∧
      (∀ x ∈ ([freshArr, (l0, 24), oldFl] : List Ivl), Disj x (ec.2, 104)) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        ∀ x ∈ ([freshArr, (l0, 24), oldFl] : List Ivl),
          Disj x (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · refine ⟨?_, ?_, ?_⟩
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hhead_mem _ (by simp [frameObjects]) _ (by simp)
        · exact R11Shards.Disj.symm (hp0.1 _ (by simp [l0]))
        · exact R11Shards.Disj.symm (hp0.1 _ (by simp [oldFl]))
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hhead_mem _ (by simp [frameObjects]) _ (by simp)
        · exact R11Shards.Disj.symm (hp1.1 _ (by simp [l0]))
        · exact R11Shards.Disj.symm (hp1.1 _ (by simp [oldFl]))
      · intro i hi x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        have hli := hlog_in_flo (e0, c0) i hi
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hhead_mem _ (by unfold frameObjects; exact List.mem_append_right _ hli) _ (by simp)
        · exact hp4.1 _ (by simp [hli])
        · exact hp5.1 _ (by simp [hli])
    · have hmem_ec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
      have hall : ∀ o2 ∈ frameObjects s ec, ∀ x ∈ ([freshArr, (l0, 24), oldFl] : List Ivl), Disj x o2 := by
        intro o2 ho2 x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo ec hmem_ec o2 ho2 _ (by simp)
        · exact hpw_head_tail.2 _ (by simp [frameObjects, l0]) ec htail o2 ho2
        · exact hpw_head_tail.2 _ (by simp [frameObjects, oldFl]) ec htail o2 ho2
      exact ⟨hall _ (by simp [frameObjects]),
             hall _ (by simp [frameObjects]),
             fun i hi => hall _ (by unfold frameObjects; exact List.mem_append_right _ (hlog_in_flo ec i hi))⟩
  have hrec_ec : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, hb_c, _, _⟩ := frameWF_bounds hAs.2 hFW
    have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    obtain ⟨hd_e, hd_c, _⟩ := hwrite_disj_ec ec hec
    exact ⟨fun k hk hk8 => hmemW_disj hb_e he8 hk8 hk hd_e,
           fun k hk hk8 => hmemW_disj hb_c hc8 hk8 hk hd_c⟩
  have htail_88_fl : ∀ ec ∈ chTail,
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    have hFW := hFW_all ec hec
    obtain ⟨_, _, hb_88, hfob⟩ := frameWF_bounds hAs.2 hFW
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    have hall : ∀ o2 ∈ frameObjects s ec, ∀ x ∈ ([freshArr, (l0, 24), oldFl] : List Ivl), Disj x o2 := by
      intro o2 ho2 x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hfresh_disj_fo ec hec o2 ho2 _ (by simp)
      · exact hpw_head_tail.2 _ (by simp [frameObjects, l0]) ec htail o2 ho2
      · exact hpw_head_tail.2 _ (by simp [frameObjects, oldFl]) ec htail o2 ho2
    refine ⟨fun k hk hk8 => hmemW_disj hb_88 h88_8 hk8 hk (hall _ (by simp [frameObjects])), ?_⟩
    intro i hi
    have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
    have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
      hFW.2.2.2.2.2.2.2.2.2.2.2.1
    have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
      rcases hfob _ hfl_in with h0 | hb
      · unfold frameLogs at h0; dsimp only at h0; omega
      · exact hb
    have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
    exact hmemW_disj hfl_b hfl_8 (by omega) (by unfold frameLogs; dsimp only; omega) (hall _ hfl_in)
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq⟩ := hrec_ec (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain
    rw [hglob_eq "ev", hglob_eq "cur_cont"]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _⟩ := hrec_ec ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _⟩ := hrec_ec ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have htail_frameLogs_eq : ∀ ec ∈ chTail, frameLogs post ec = frameLogs s ec := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    obtain ⟨he_eq, _⟩ := hrec_ec ec hec
    obtain ⟨h88_eq, _⟩ := htail_88_fl ec htail
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hlr_eq : ∀ ec ∈ evmChain s, ∀ i (_hi : i < memW s (memW s (ec.1 + 88) + 8)) off,
      off + 8 ≤ 40 → off % 8 = 0 →
      memW post ((memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) + off) =
        memW s ((memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) + off) := by
    intro ec hec i hi off hoff hoff8
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
      unfold frameObjects; exact List.mem_append_right _ (hlog_in_flo ec i hi)
    have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
      rcases hfob _ hlr_in with h0 | hb
      · dsimp only at h0; omega
      · exact hb
    have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
      · obtain ⟨he88_in, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
        have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
        rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
      · exact (hent i hi).2.1.1
    exact hmemW_disj hlr_b hlr_8 hoff8 hoff ((hwrite_disj_ec ec hec).2.2 i hi)
  have htail_logs_congr : ∀ ec ∈ chTail,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    have hFW := hFW_all ec hec
    obtain ⟨he_eq, _⟩ := hrec_ec ec hec
    obtain ⟨h88_eq, harr_eq⟩ := htail_88_fl ec htail
    have hl0_t : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8_t := h88_eq 8 (by omega) (by omega)
    have hl16_t := h88_eq 16 (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega), hl8_t]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0_t, harr_eq i hi]
      have r0 := hlr_eq ec hec i hi 0 (by omega) (by omega)
      have r8 := hlr_eq ec hec i hi 8 (by omega) (by omega)
      have r16 := hlr_eq ec hec i hi 16 (by omega) (by omega)
      have r24 := hlr_eq ec hec i hi 24 (by omega) (by omega)
      have r32 := hlr_eq ec hec i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hglob_eq "vm_system_address"]
    · rw [he_eq 88 (by omega) (by omega)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(wordsOK_congr_dom hdom_eq).2 hw_l, allocated_mono_scr hh hsc_le hal_l,
          by rw [hl8_t]; exact hlt28, by rw [hl8_t, hl16_t]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8_t] at hi; rw [hl0_t]
        obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(wordAt_congr_dom hdom_eq).2 hwa, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq ec hec i hi 0 (by omega) (by omega)
        have r8 := hlr_eq ec hec i hi 8 (by omega) (by omega)
        have r16 := hlr_eq ec hec i hi 16 (by omega) (by omega)
        have r24 := hlr_eq ec hec i hi 24 (by omega) (by omega)
        have r32 := hlr_eq ec hec i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr"]
        exact ⟨(wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have he0_88 : memW post (e0 + 88) = l0 := (hrec_ec (e0, c0) hhead_mem).1 88 (by omega) (by omega)
  have hl0_nz : l0 ≠ 0 := by
    obtain ⟨hl0_in, _⟩ := (hhead_FW.1 (l0, 24) (by simp [l0])).1
    have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hl0_in; omega
  have hhead_fl_post : Inside (frameLogs post (e0, c0)) sourceBase (globN post "heap_ptr") ∨
      Inside (frameLogs post (e0, c0)) (globN post "scratch_ptr") scratchEnd := by
    unfold frameLogs; dsimp only; rw [he0_88, hglob_eq "heap_ptr", hglob_eq "scratch_ptr"]
    rcases harr_case with ⟨_, h0_eq, h16_eq⟩ | ⟨hnz, hfl_eq⟩
    · rw [h0_eq, h16_eq]; exact hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.1
    · rw [hfl_eq]
      rcases hfresh_alloc with rfl | ⟨_, _, hfin⟩
      · exact absurd rfl hnz
      · exact Or.inl hfin
  have hhead_fl_words : WordsOK post (frameLogs post (e0, c0)) := by
    have hal_fl : Allocated post (frameLogs post (e0, c0)) := hhead_fl_post
    unfold frameLogs at hal_fl ⊢; dsimp only at hal_fl ⊢
    rw [he0_88] at hal_fl ⊢
    rcases harr_case with ⟨_, h0_eq, h16_eq⟩ | ⟨hnz, hfl_eq⟩
    · rw [h0_eq, h16_eq]
      exact (wordsOK_congr_dom hdom_eq).2 hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · rw [hfl_eq] at hal_fl ⊢
      rcases hfresh_alloc with rfl | ⟨hf8, hfsz8, _⟩
      · exact absurd rfl hnz
      · exact wordsOK_of_allocated_scr hApost hal_fl hf8 hfsz8
  have hhead_flo_eq : frameLogObjects post (e0, c0) = frameLogObjects s (e0, c0) ++ newLogs := by
    rw [← hnewLogs_eq]
    refine frameLogObjects_of_append he0_88 hlen_post ?_ hnew_slot
    intro i hi
    rw [hold_slots i hi]
    have r0 := hlr_eq (e0, c0) hhead_mem i hi 0 (by omega) (by omega)
    have r8 := hlr_eq (e0, c0) hhead_mem i hi 8 (by omega) (by omega)
    have r16 := hlr_eq (e0, c0) hhead_mem i hi 16 (by omega) (by omega)
    have r24 := hlr_eq (e0, c0) hhead_mem i hi 24 (by omega) (by omega)
    have r32 := hlr_eq (e0, c0) hhead_mem i hi 32 (by omega) (by omega)
    simp only [Nat.add_zero] at r0
    unfold logOwnedIvls logRecordIvls
    rw [r0, r8, r16, r24, r32, hglob_eq "vm_system_address"]
  have hhead_ll_post : LogsListOK post (memW post (e0 + 88)) := by
    rw [he0_88]
    rcases hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, _, _, hent⟩
    · exact absurd hz hl0_nz
    · refine logsListOK_of_append (Or.inr ⟨hw_l, hal_l, ?_, ?_, hent⟩) hl0_nz
        ((wordsOK_congr_dom hdom_eq).2 hw_l) (allocated_mono_scr hh hsc_le hal_l)
        hlen_post hlen_lt hcap_le ?_ ?_ hnew_slot hentry_post
      · omega
      · exact hhead_FW.2.2.2.2.2.2.2.2.2.2.2.1
      · intro i hi
        have hslot_wa : WordAt post (memW post l0 + 8 * i) := by
          have hkj : i < (frameLogs post (e0, c0)).2 / 8 := by
            unfold frameLogs; dsimp only; rw [he0_88]; omega
          have hbase_eq : (frameLogs post (e0, c0)).1 = memW post l0 := by
            unfold frameLogs; dsimp only; rw [he0_88]
          rw [← hbase_eq]
          exact hhead_fl_words.2.2 i hkj
        refine ⟨hslot_wa, ?_⟩
        rw [hold_slots i hi]
        obtain ⟨_, hle⟩ := hent i hi
        have r0 := hlr_eq (e0, c0) hhead_mem i hi 0 (by omega) (by omega)
        have r8 := hlr_eq (e0, c0) hhead_mem i hi 8 (by omega) (by omega)
        have r16 := hlr_eq (e0, c0) hhead_mem i hi 16 (by omega) (by omega)
        have r24 := hlr_eq (e0, c0) hhead_mem i hi 24 (by omega) (by omega)
        have r32 := hlr_eq (e0, c0) hhead_mem i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr"]
        exact ⟨(wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
      · have hkj : memW s (l0 + 8) < (frameLogs post (e0, c0)).2 / 8 := by
          unfold frameLogs; dsimp only; rw [he0_88]; omega
        have hbase_eq : (frameLogs post (e0, c0)).1 = memW post l0 := by
          unfold frameLogs; dsimp only; rw [he0_88]
        rw [← hbase_eq]
        exact hhead_fl_words.2.2 (memW s (l0 + 8)) hkj
  have htail_fo_eq : ∀ ec ∈ chTail, frameObjects post ec = frameObjects s ec := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    obtain ⟨he_eq, _⟩ := hrec_ec ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega),
        htail_frameLogs_eq ec htail, hframeRet_eq ec hec, (htail_logs_congr ec htail).1]
  have hfo_post_cases : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects post ec,
      o ∈ frameObjects s ec ∨ (ec = (e0, c0) ∧ o ∈ freshArr :: newLogs) := by
    intro ec hec o ho
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · unfold frameObjects at ho
      obtain ⟨he_eq, _⟩ := hrec_ec (e0, c0) hhead_mem
      rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
          he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
          he0_88, hframeRet_eq (e0, c0) hhead_mem, hhead_flo_eq] at ho
      rcases List.mem_append.1 ho with ho7 | holog
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
        rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects, l0])
        · rcases harr_case with ⟨_, h0_eq, h16_eq⟩ | ⟨_, hfl_eq⟩
          · left
            have hfl_s : frameLogs post (e0, c0) = frameLogs s (e0, c0) := by
              unfold frameLogs; dsimp only; rw [he0_88, h0_eq, h16_eq]
            rw [hfl_s]; simp [frameObjects]
          · right; unfold frameLogs; dsimp only; rw [he0_88, hfl_eq]; exact ⟨rfl, by simp⟩
        · exact Or.inl (by simp [frameObjects])
      · rcases List.mem_append.1 holog with ho_old | ho_new
        · exact Or.inl (by unfold frameObjects; exact List.mem_append_right _ ho_old)
        · exact Or.inr ⟨rfl, List.mem_cons_of_mem _ ho_new⟩
    · left; rwa [htail_fo_eq ec htail] at ho
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _⟩ := hrec_ec ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hR_eq : evmR post = evmR s :=
    evmR_eq_of_chain_and_words hchain_eq (fun ec hec =>
      ⟨(hrec_ec ec hec).1 64 (by omega) (by omega),
       (hrec_ec ec hec).1 192 (by omega) (by omega)⟩)
  have hCC : ChainCellsAgree s post := by
    intro ec hec
    obtain ⟨he_eq, hc_eq⟩ := hrec_ec ec hec
    exact ⟨he_eq 24 (by omega) (by omega), he_eq 32 (by omega) (by omega),
           he_eq 40 (by omega) (by omega), hc_eq 56 (by omega) (by omega)⟩
  have hgk_nil : GlobalsKept [] s post := fun k _ => by rw [heff.globals]
  refine ⟨⟨⟨hApost, S, hW_post, ?_⟩, hh, hgk_nil, hchain_eq⟩, hCC⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_ec ec hec_mem).2 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _⟩ := hrec_ec ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega)]
      obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
      obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
      set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd_m))
      have hcell_i : SameTypedCells s post S Ndi := by
        have hwti_sub : ∀ i ∈ worldTypedIvls s S Ndi, i ∈ worldTypedIvls s S Nd_at := by
          intro i hi; unfold worldTypedIvls at hi ⊢
          rcases List.mem_append.1 hi with hpre | hne
          · exact List.mem_append_left _ hpre
          · apply List.mem_append_right; unfold nodeExtents at hne ⊢
            obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
            exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
        refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
          fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
          fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
      obtain ⟨hWT_i_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc_le hcg hcell_i
        ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
        ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
      refine ⟨allocated_mono_scr hh hsc_le hal_m, (wordsOK_congr_dom hdom_eq).2 hw_m,
        fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
        by rw [hfeq]; exact hdf,
        ?_,
        Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
      · rw [hchain_eq]; intro ec' hec' o ho
        rcases hfo_post_cases ec' hec' o ho with ho_old | ⟨_, ho_new⟩
        · exact hdfo ec' hec' o ho_old
        · exact R11Shards.Disj.symm ((hfresh_disj_s o ho_new).2.2.2.2 ec hec)
      · rw [nodeExtents_eq hTr_int.1 hcell_i] at hj
        exact hdj_m o ho j (hsub_int j hj).2
    have hret_in_post : (memW s (ec.1 + 216) = 0 ∧ memW s (ec.1 + 144) = globN s "evm_empty") ∨
        Inside (frameRet s ec) sourceBase (globN s "heap_ptr") ∧ WordsOK post (frameRet s ec) := by
      rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (wordsOK_congr_dom hdom_eq).2 hw⟩
    unfold FrameWF; dsimp only
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 16 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 32 (by omega) (by omega),
        he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega),
        he_eq 176 (by omega) (by omega),
        he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
        hframeRet_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    have hscr_post : ∀ i ∈ [(ec.1, 280), (ec.2, 104), (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)), (memW post (ec.1 + 88), 24)],
        Inside i (globN s "scratch_ptr") scratchEnd ∧ WordsOK post i := by
      rw [he_eq 88 (by omega) (by omega)]
      intro i hi; exact ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · have hfl_in_head : Inside (frameLogs post (e0, c0)) sourceBase (globN s "heap_ptr") ∨
          Inside (frameLogs post (e0, c0)) (globN s "scratch_ptr") scratchEnd := by
        simpa only [hglob_eq "heap_ptr", hglob_eq "scratch_ptr"] using hhead_fl_post
      refine ⟨hscr_post, c2, (wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10,
        ?_, ?_, hfl_in_head, hhead_fl_words, hret_in_post, hhead_ll_post, hmsg_ok⟩
      · rw [he0_88]; exact hcap_pos
      · rw [he0_88, hlen_post]; exact hcap_le
    · obtain ⟨h88_eq, _⟩ := htail_88_fl ec htail
      have hlo_ok := (htail_logs_congr ec htail).2
      have hscr_tail : ∀ i ∈ [(ec.1, 280), (ec.2, 104), (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)), (memW s (ec.1 + 88), 24)],
          Inside i (globN s "scratch_ptr") scratchEnd ∧ WordsOK post i := by
        intro i hi; exact ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩
      rw [he_eq 88 (by omega) (by omega),
          h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
          htail_frameLogs_eq ec htail]
      exact ⟨hscr_tail, c2, (wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10,
        c11, c12, c13, (wordsOK_congr_dom hdom_eq).2 c14, hret_in_post,
        by rwa [he_eq 88 (by omega) (by omega)] at hlo_ok, hmsg_ok⟩
  · intro ec hec
    have htail : ec ∈ chTail := by rw [hch_eq, List.tail_cons] at hec; exact hec
    have hec_mem : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    unfold FrameRoom
    rw [(hrec_ec ec hec_mem).1 16 (by omega) (by omega),
        (hrec_ec ec hec_mem).1 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_ec _ hi0).2 80 (by omega) (by omega),
        (hrec_ec _ hi0).2 72 (by omega) (by omega),
        (hrec_ec _ hi1).1 40 (by omega) (by omega)]
    exact hRW i hi
  · have htail_map_eq : chTail.map (frameObjects post) = chTail.map (frameObjects s) :=
      List.map_congr_left htail_fo_eq
    rw [hch_eq, List.map_cons, List.flatten_cons, htail_map_eq, List.pairwise_append]
    have hFO_pw' := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw'
    refine ⟨?_, hFO_pw'.2.1, ?_⟩
    · have hp_nl := List.pairwise_cons.1 hnewLogs_pw
      have hhead_fo_post : frameObjects post (e0, c0) =
          [(e0, 280), (c0, 104), (memW s (e0 + 8), 32 * memW s (e0 + 232)),
           (memW s (e0 + 24), memW s (e0 + 40)), (l0, 24), frameLogs post (e0, c0),
           frameRet s (e0, c0)] ++ (frameLogObjects s (e0, c0) ++ newLogs) := by
        unfold frameObjects
        obtain ⟨he_eq, _⟩ := hrec_ec (e0, c0) hhead_mem
        rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
            he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
            he0_88, hframeRet_eq (e0, c0) hhead_mem, hhead_flo_eq]
      rw [hhead_fo_post]
      have hfl_cases : frameLogs post (e0, c0) = oldFl ∨ frameLogs post (e0, c0) = freshArr := by
        rcases harr_case with ⟨_, h0_eq, h16_eq⟩ | ⟨_, hfl_eq⟩
        · left; change frameLogs post (e0, c0) = frameLogs s (e0, c0)
          unfold frameLogs; dsimp only; rw [he0_88, h0_eq, h16_eq]
        · right; unfold frameLogs; dsimp only; rw [he0_88, hfl_eq]
      have hflo_nl_pw : (frameLogObjects s (e0, c0) ++ newLogs).Pairwise Disj := by
        rw [List.pairwise_append]
        refine ⟨hp6.2, hp_nl.2, fun o1 ho1 o2 ho2 => ?_⟩
        exact R11Shards.Disj.symm (hfresh_disj_fo (e0, c0) hhead_mem o1
          (by unfold frameObjects; exact List.mem_append_right _ ho1) o2 (List.mem_cons_of_mem _ ho2))
      have hret_pw : (frameRet s (e0, c0) :: (frameLogObjects s (e0, c0) ++ newLogs)).Pairwise Disj := by
        refine List.pairwise_cons.2 ⟨fun o ho => ?_, hflo_nl_pw⟩
        rcases List.mem_append.1 ho with ho1 | ho2
        · exact hp6.1 o ho1
        · exact R11Shards.Disj.symm (hfresh_disj_fo (e0, c0) hhead_mem (frameRet s (e0, c0))
            (by simp [frameObjects]) o (List.mem_cons_of_mem _ ho2))
      have hfl_pw : (frameLogs post (e0, c0) :: frameRet s (e0, c0) :: (frameLogObjects s (e0, c0) ++ newLogs)).Pairwise Disj := by
        refine List.pairwise_cons.2 ⟨fun o ho => ?_, hret_pw⟩
        simp only [List.mem_cons, List.mem_append] at ho
        rcases hfl_cases with hfl_old | hfl_fr
        · rw [hfl_old]
          rcases ho with rfl | ho1 | ho2
          · exact hp5.1 _ (by simp)
          · exact hp5.1 _ (by simp [ho1])
          · exact R11Shards.Disj.symm (hfresh_disj_fo (e0, c0) hhead_mem oldFl
              (by simp [frameObjects, oldFl]) o (List.mem_cons_of_mem _ ho2))
        · rw [hfl_fr]
          rcases ho with rfl | ho1 | ho2
          · exact hfresh_disj_fo (e0, c0) hhead_mem _ (by simp [frameObjects]) freshArr (by simp)
          · exact hfresh_disj_fo (e0, c0) hhead_mem o (by unfold frameObjects; exact List.mem_append_right _ ho1) freshArr (by simp)
          · exact hp_nl.1 o ho2
      have hpre_disj : ∀ p ∈ ([(e0, 280), (c0, 104), (memW s (e0 + 8), 32 * memW s (e0 + 232)),
          (memW s (e0 + 24), memW s (e0 + 40)), (l0, 24)] : List Ivl),
          ∀ q ∈ frameLogs post (e0, c0) :: frameRet s (e0, c0) :: (frameLogObjects s (e0, c0) ++ newLogs),
            Disj p q := by
        intro p hp q hq
        have hp_fo : p ∈ frameObjects s (e0, c0) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [frameObjects, l0]
        simp only [List.mem_cons, List.mem_append] at hq
        rcases hq with rfl | rfl | hq1 | hq2
        · rcases hfl_cases with hfl_old | hfl_fr
          · rw [hfl_old]
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl
            · exact hp0.1 _ (by simp [oldFl])
            · exact hp1.1 _ (by simp [oldFl])
            · exact hp2.1 _ (by simp [oldFl])
            · exact hp3.1 _ (by simp [oldFl])
            · exact hp4.1 _ (by simp [oldFl])
          · rw [hfl_fr]
            exact R11Shards.Disj.symm (hfresh_disj_fo (e0, c0) hhead_mem p hp_fo freshArr (by simp))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl
          · exact hp0.1 _ (by simp)
          · exact hp1.1 _ (by simp)
          · exact hp2.1 _ (by simp)
          · exact hp3.1 _ (by simp)
          · exact hp4.1 _ (by simp)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl
          · exact hp0.1 _ (by simp [hq1])
          · exact hp1.1 _ (by simp [hq1])
          · exact hp2.1 _ (by simp [hq1])
          · exact hp3.1 _ (by simp [hq1])
          · exact hp4.1 _ (by simp [hq1])
        · exact R11Shards.Disj.symm (hfresh_disj_fo (e0, c0) hhead_mem p hp_fo q (List.mem_cons_of_mem _ hq2))
      have hpre5_pw : ([(e0, 280), (c0, 104), (memW s (e0 + 8), 32 * memW s (e0 + 232)),
          (memW s (e0 + 24), memW s (e0 + 40)), (l0, 24)] : List Ivl).Pairwise Disj := by
        refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, by simp⟩⟩⟩⟩
        · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl <;> exact hp0.1 _ (by simp [l0])
        · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl <;> exact hp1.1 _ (by simp [l0])
        · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl <;> exact hp2.1 _ (by simp [l0])
        · intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact hp3.1 _ (by simp [l0])
      change ([(e0, 280), (c0, 104), (memW s (e0 + 8), 32 * memW s (e0 + 232)),
        (memW s (e0 + 24), memW s (e0 + 40)), (l0, 24)] ++
        (frameLogs post (e0, c0) :: frameRet s (e0, c0) :: (frameLogObjects s (e0, c0) ++ newLogs))).Pairwise Disj
      exact List.pairwise_append.2 ⟨hpre5_pw, hfl_pw, hpre_disj⟩
    · intro o1 ho1 o2 ho2
      obtain ⟨l2, hl2, ho2_in⟩ := List.mem_flatten.1 ho2
      obtain ⟨ec2, hec2, rfl⟩ := List.mem_map.1 hl2
      have hec2_mem : ec2 ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ hec2
      rcases hfo_post_cases _ hhead_mem o1 ho1 with ho1_old | ⟨_, ho1_new⟩
      · exact hFO_pw'.2.2 o1 ho1_old o2 ho2
      · exact hfresh_disj_fo ec2 hec2_mem o2 ho2_in o1 ho1_new
  · intro ec hec o ho
    rw [hfeq]
    rcases hfo_post_cases ec hec o ho with ho_old | ⟨_, ho_new⟩
    · exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho_old).1 t ht i hi,
        (hFO_disj ec hec o ho_old).2⟩
    · refine ⟨fun t ht i hi => ?_, (hfresh_disj_s o ho_new).2.1⟩
      rw [hfp_eq_all t ht] at hi
      exact (hfresh_disj_s o ho_new).1 t ht i hi
  · refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [nodeExtents_eq hTr_at.1 hcell] at hj
    obtain ⟨fo, hfo_map, ho_in⟩ := List.mem_flatten.1 ho
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
    rcases hfo_post_cases ec hec o ho_in with ho_old | ⟨_, ho_new⟩
    · exact hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho_old⟩) j hj
    · exact (hfresh_disj_s o ho_new).2.2.2.1 j hj
  · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
      unfold worldTableRefs recordSlots
      rw [hglob_eq "ws", hglob_eq "bs", hglob_eq "ts",
          show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
            simp only [globalTableRoots, List.map, hglob_eq],
          balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts"),
          hglob_eq "journal_n", hglob_eq "journal"]
      have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
          (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz
          (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
      have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
          (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz
          (by simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
          (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz
          (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
          (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
        by_cases hnz : globN s "bs" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "bs" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
          (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
        by_cases hnz : globN s "ts" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "ts" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
          (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
        apply List.flatMap_congr; intro ad had
        have had_mem := balRecord_ivl_mem had
        rcases fixedObject_le_2pow64 hAs.2 hWT.2.2.1 (bal_in_fixedObjects had_mem) with h0 | had_bnd
        · dsimp only at h0; omega
        · dsimp only at had_bnd
          have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
          rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
              memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
      have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
          (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
        apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
        have hjc_le := hWT.2.1.1
        have hjc_ne : globN s "journal_cap" ≠ 0 := by omega
        rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
        · exact absurd h0 hjc_ne
        · have hbnd := allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
          have hkle : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by omega
          exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd_at) hjc_ne)
            ⟨by dsimp only; omega, by dsimp only; omega⟩
      dsimp only
      rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t; unfold DelExclusive; rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 ∧ k % 8 = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [(hrec_ec _ hj_mem).1 k hk_ok.1 hk_ok.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_ec _ hi_mem).2 48 (by omega) (by omega)
    have hmm_eq := (hrec_ec _ hi_mem).2 56 (by omega) (by omega)
    have he24_eq := (hrec_ec _ hi_mem).1 24 (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_ec ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
    have hM := hMarks i hi; dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_tail : (evmChain s)[j] ∈ chTail := by
        rcases j with _ | j'
        · omega
        · simp [hch_eq]
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, htail_fo_eq _ hj_tail, htail_frameLogs_eq _ hj_tail,
          (hrec_ec _ hj_mem).1 112 (by omega) (by omega)]
      exact m5 j hj hij
    · intro t ht
      rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
  · rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
        hframeRoleSlots_eq,
        journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
    rw [htab_hdr_eq hcell haS htb 0 (by omega)]; exact ⟨haS, hkl⟩
  · have hsum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      unfold evmR at hR_eq; rw [hchain_eq] at hR_eq; exact hR_eq
    rw [hsum_eq]; exact hGas

end HeadLogAppendInv

/-! ## Milestone 3b: Operational stepping for `u256_to_be32`, `lst_push`, `log_append`, and `emit_transfer_log` -/

section EmitTransferLogStep

open InitECandidate.Solver.GuestGlobalKeep (lookupCode_installed)
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA (wordsOK_congr_dom)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
  (noCatchableRaise evaluate_noCatchableRaise)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
  (globN_eq_of_lookup_eq allocated_mono_scr wordsOK_of_allocated_scr)
open InitECandidate.Solver.Wave8Contracts.M23

theorem alloc_body_evmStepCC {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hInv : EvmInv s)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    EvmStepCC ["heap_ptr"] s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2 := by
  obtain ⟨hA, S, hAt⟩ := (evmInv_iff_at s).1 hInv
  obtain ⟨p, q, hr, hp, hq, hlim, h8, hpq, hg, hm, hb, hma, hAp, hhp, hsp⟩ :=
    R13Shards.alloc_body_resumes_props s hA.1.code hA hres
  apply evmStepCC_of_fresh_heap_step hA hAt hAp hb
  · rw [hhp, ← hp]
    exact hpq
  · intro k hk
    rw [hg, HolFiniteMapExact.lookup_update]
    have hne : ofString "heap_ptr" ≠ k := by
      intro heq
      apply hk
      simp [← heq]
    simp [FUPDATE, hne]
  · intro a ha
    rw [hm]
  · intro b hb64 hnot
    unfold memB
    rw [hm, hb]

theorem transfer_alloc_body_spec {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat)
    (hn : n = 40 ∨ n = 96 ∨ n = 32)
    (hInv : EvmInv s) (hsize : locN s "n" = n)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)
    ∃ p : BitVec 64, out.1 = some (.returned (.val (.word p))) ∧
      p.toNat = globN s "heap_ptr" ∧
      globN out.2 "heap_ptr" = p.toNat + n ∧
      WordsOK out.2 (p.toNat, n) ∧
      Inside (p.toNat, n) sourceBase (globN out.2 "heap_ptr") ∧
      EvmStepCC ["heap_ptr"] s out.2 := by
  dsimp only
  have hA : ArenaReady s := hInv.1
  obtain ⟨p, q, hr, hp, hq, hlim, h8, hpq, hg, hm, hb, hma, hAp, hhp, hsp⟩ :=
    R13Shards.alloc_body_resumes_props s hA.1.code hA hres
  have halign : (n + 7) / 8 * 8 = n := by rcases hn with rfl | rfl | rfl <;> decide
  rw [hsize, halign] at hq
  have hlo : sourceBase ≤ p.toNat := by rw [hp]; exact hA.2.1
  have hin : Inside (p.toNat, n) sourceBase (globN
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2 "heap_ptr") := by
    exact ⟨hlo, by rw [hhp, hq]⟩
  refine ⟨p, hr, hp, hhp.trans hq, ?_, hin, alloc_body_evmStepCC s hInv hres⟩
  apply wordsOK_of_inside_heap _ hAp.1.memaddrs
  · rw [hp]; exact hA.2.2.2.2.2.2.1
  · rcases hn with rfl | rfl | rfl <;> decide
  · exact hlo
  · have : heapLimit ≤ heapEnd := by decide
    omega

theorem transfer_decCall_alloc_exact_spec {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS)
    (cont : ProgHOL 64) (p : BitVec 64) (n : Nat)
    (hn : n = 40 ∨ n = 96 ∨ n = 32) (hInv : EvmInv s)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).1) :
    ∃ next : PanSemStateFiniteExact 64 F,
      next.locals.lookup x = some (.val (.word p)) ∧
      globN next "heap_ptr" = p.toNat + n ∧
      WordsOK next (p.toNat, n) ∧
      EvmStepCC ["heap_ptr"] s next ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).1 =
        (evaluateHOLFiniteState next cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).2 =
        { (evaluateHOLFiniteState next cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState next cont).2.locals
            (x, s.locals.lookup x) } ∧
      next.memory = s.memory ∧ next.be = s.be ∧
      (∀ k, k ≠ x → next.locals.lookup k = s.locals.lookup k) := by
  have hA : ArenaReady s := hInv.1
  obtain ⟨clk, hq, hlim, h8, hpq, hAp, hr, hs⟩ :=
    R13Shards.step_decCall_alloc_resumes s x (.const (BitVec.ofNat 64 n)) cont
      (BitVec.ofNat 64 n) p hA.1.code hA hp rfl hres
  let q := (p + (BitVec.ofNat 64 n + 7)) &&& ((0 : BitVec 64) - 8)
  let next : PanSemStateFiniteExact 64 F := {s with
    locals := s.locals.update (x, .val (.word p))
    globals := s.globals.update (ofString "heap_ptr", .val (.word q))
    clock := clk}
  change ArenaReady next at hAp
  have hnorm : ((BitVec.ofNat 64 n).toNat + 7) / 8 * 8 = n := by
    rcases hn with rfl | rfl | rfl <;> decide
  rw [hnorm] at hq
  have hhp : globN next "heap_ptr" = p.toNat + n := by
    change q.toNat = _
    exact hq
  have hpglob : globN s "heap_ptr" = p.toNat := by simp [globN, hp]
  have hstep : EvmStepCC ["heap_ptr"] s next := by
    obtain ⟨_, S, hAt⟩ := (evmInv_iff_at s).1 hInv
    apply evmStepCC_of_fresh_heap_step hA hAt hAp rfl
    · rw [hhp, hpglob]; omega
    · intro k hk
      change s.globals.lookup k = (s.globals.update _).lookup k
      rw [HolFiniteMapExact.lookup_update]
      have hne : ofString "heap_ptr" ≠ k := by
        intro heq
        apply hk
        simp [← heq]
      simp [FUPDATE, hne]
    · intro a ha; rfl
    · intro b hb hnot; rfl
  refine ⟨next, ?_, hhp, ?_, hstep, hr, hs, rfl, rfl, ?_⟩
  · simp [next, HolFiniteMapExact.lookup_update, FUPDATE]
  · apply wordsOK_of_inside_heap _ hAp.1.memaddrs
    · rw [← hpglob]; exact hA.2.2.2.2.2.2.1
    · rcases hn with rfl | rfl | rfl <;> decide
    · rw [← hpglob]; exact hA.2.1
    · have : heapLimit ≤ heapEnd := by decide
      change q.toNat ≤ heapLimit at hlim
      change q.toNat = p.toNat + n at hq
      omega
  · intro k hk
    simp [next, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]

theorem transfer_decCall_alloc_spec {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS)
    (cont : ProgHOL 64) (p : BitVec 64) (n : Nat)
    (hn : n = 40 ∨ n = 96 ∨ n = 32) (hInv : EvmInv s)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).1) :
    ∃ next : PanSemStateFiniteExact 64 F,
      next.locals.lookup x = some (.val (.word p)) ∧
      globN next "heap_ptr" = p.toNat + n ∧
      WordsOK next (p.toNat, n) ∧
      EvmStepCC ["heap_ptr"] s next ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).1 =
        (evaluateHOLFiniteState next cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).2 =
        { (evaluateHOLFiniteState next cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState next cont).2.locals
            (x, s.locals.lookup x) } := by
  obtain ⟨next, hx, hhp, hwords, hstep, hr, hs, _⟩ :=
    transfer_decCall_alloc_exact_spec s x cont p n hn hInv hp hres
  exact ⟨next, hx, hhp, hwords, hstep, hr, hs⟩

theorem transfer_decCall_alloc_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (cont : ProgHOL 64) (p : BitVec 64) (n : Nat)
    (hn : n = 40 ∨ n = 96 ∨ n = 32) (hInv : EvmInv s)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).1)
    (hcont : ∀ next : PanSemStateFiniteExact 64 F,
      next.locals.lookup x = some (.val (.word p)) →
      globN next "heap_ptr" = p.toNat + n →
      WordsOK next (p.toNat, n) → EvmStepCC ["heap_ptr"] s next →
      next.memory = s.memory → next.be = s.be →
      (∀ k, k ≠ x → next.locals.lookup k = s.locals.lookup k) →
      Resumes (evaluateHOLFiniteState next cont).1 →
      EvmStepCC ["heap_ptr"] next (evaluateHOLFiniteState next cont).2) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).2 := by
  obtain ⟨next, hx, hhp, hwords, hstep, hr, hs, hm, hb, hl⟩ :=
    transfer_decCall_alloc_exact_spec s x cont p n hn hInv hp hres
  have hc := hcont next hx hhp hwords hstep hm hb hl (hr ▸ hres)
  have hboth : EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState next cont).2 := by
    refine ⟨⟨hc.1.1, le_trans hstep.1.2.1 hc.1.2.1,
      fun k hk => (hstep.1.2.2.1 k hk).trans (hc.1.2.2.1 k hk),
      hc.1.2.2.2.trans hstep.1.2.2.2⟩, ?_⟩
    intro ec hec
    obtain ⟨a, b, c, d⟩ := hstep.2 ec hec
    obtain ⟨a', b', c', d'⟩ := hc.2 ec (hstep.1.2.2.2.symm ▸ hec)
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩
  rw [hs]
  exact ⟨⟨localsFree_evmInv _ _ _ hboth.1.1, hboth.1.2.1, hboth.1.2.2.1,
    (evmChain_with_locals _ _ _).trans hboth.1.2.2.2⟩, hboth.2⟩

theorem ek_cc_alloc :
    EvmKeeps EvmInv ["heap_ptr"] (ofString "alloc") ∧
      ChainCellsKept EvmInv (ofString "alloc") := by
  constructor
  · refine ⟨_, _, _, R13Shards.lookup_alloc_r13, ?_⟩
    intro F s hcode hInv hex hnt hres
    exact (alloc_body_evmStepCC s hInv hres).1
  · refine ⟨_, _, _, R13Shards.lookup_alloc_r13, ?_⟩
    intro F s hcode hInv hex hnt hres
    exact (alloc_body_evmStepCC s hInv hres).2

private theorem lookup_lst_push_local :
    originalRuntimeCode.lookup (ofString "lst_push") =
      some ([(ofString "l", .one), (ofString "esz", .one)],
        sourceFnBody Guest.Software.guestFn_lst_push, .one) :=
  lookup_of_guestAst_getElem 410 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_push) rfl

private theorem lookup_log_append_local :
    originalRuntimeCode.lookup (ofString "log_append") =
      some ([(ofString "e", .one), (ofString "log", .one)],
        sourceFnBody Guest.Software.guestFn_log_append, .one) :=
  lookup_of_guestAst_getElem 523 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_log_append) rfl

private theorem lookup_emit_transfer_log_local :
    originalRuntimeCode.lookup (ofString "emit_transfer_log") =
      some ([(ofString "sender", .one), (ofString "recipient", .one),
             (ofString "amount", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_emit_transfer_log, .one) :=
  lookup_of_guestAst_getElem 567 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_emit_transfer_log) rfl

private theorem lookup_u256_is_zero_local :
    originalRuntimeCode.lookup (ofString "u256_is_zero") =
      some ([(ofString "a", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_u256_is_zero, .one) :=
  lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_is_zero) rfl

private theorem lookup_trap_with_local :
    originalRuntimeCode.lookup (ofString "trap_with") =
      some ([(ofString "code", .one)],
        sourceFnBody Guest.Software.guestFn_trap_with, .one) :=
  lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_trap_with) rfl

private theorem lookup_memzero_local :
    originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memzero, .one) :=
  lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memzero) rfl

private def emitLogNcrCallees (f : MlS) : Bool :=
  f == ofString "trap_with" ||
  f == ofString "alloc" ||
  f == ofString "memcpy" ||
  f == ofString "memzero" ||
  f == ofString "bswap64" ||
  f == ofString "st_be32" ||
  f == ofString "st_be64" ||
  f == ofString "u256_is_zero" ||
  f == ofString "u256_to_be32" ||
  f == ofString "lst_push" ||
  f == ofString "log_append" ||
  f == ofString "emit_transfer_log"

private theorem emitLogNcrCallees_good :
    ∀ f, emitLogNcrCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise emitLogNcrCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
  simp only [emitLogNcrCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · rw [lookup_trap_with_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [R13Shards.lookup_alloc_r13] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [EvmFrameSpecs.lookup_memcpy] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_memzero_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [EvmFrameSpecs.lookup_bswap64] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [EvmFrameSpecs.lookup_st_be32] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [EvmFrameSpecs.lookup_st_be64] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_u256_is_zero_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [EvmFrameSpecs.lookup_u256_to_be32] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_lst_push_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_log_append_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_emit_transfer_log_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

private theorem emit_transfer_log_resumes_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_emit_transfer_log)).1) :
    ∃ v, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_emit_transfer_log)).1 =
      some (.returned v) := by
  rcases hres with h | ⟨e, v, he, hne⟩
  · exact h
  · exact absurd he (evaluate_noCatchableRaise emitLogNcrCallees emitLogNcrCallees_good
      (sourceFnBody Guest.Software.guestFn_emit_transfer_log) rfl s hcode e v hne)

private theorem m11_bre_to_m23 {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : InitECandidate.Solver.Wave8GuestInv.M11.ByteRegionEffect s post Rl) :
    ByteRegionEffect s post Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, h.out_dom, h.cell_frame, h.byte_frame⟩

theorem m23_bre_of_store_word {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {Rl : List Ivl}
    (hma : s.memaddrs = ordinaryDomain)
    (hrun : evaluateHOLFiniteState s (.store dstExp valExp) = (none, post))
    (hword : ∀ v,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word addr)) →
      s.memaddrs addr →
      ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ i.1 + i.2) :
    ByteRegionEffect s post Rl ∧ post.locals = s.locals := by
  obtain ⟨heff, hloc⟩ :=
    InitECandidate.Solver.Wave8GuestInv.M11.ByteRegionEffect.of_store_word hma hrun hword hin
  exact ⟨m11_bre_to_m23 heff, hloc⟩

theorem transfer_allocated_store_step {F : Type}
    {s allocated post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl}
    (hInv : EvmInv s) (halloc : EvmStepCC ["heap_ptr"] s allocated)
    (hmem : allocated.memory = s.memory) (hbe : allocated.be = s.be)
    (hrun : evaluateHOLFiniteState allocated (.store dst val) = (none, post))
    (hword : ∀ v, @evalHOLExact 64 F _ allocated.toExact
      (fun a => Classical.propDecidable (allocated.memaddrs a)) val = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hdst : ∀ addr : BitVec 64, @evalHOLExact 64 F _ allocated.toExact
      (fun a => Classical.propDecidable (allocated.memaddrs a)) dst = some (.val (.word addr)) →
      allocated.memaddrs addr →
      ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ i.1 + i.2)
    (hin : ∀ i ∈ Rl, Inside i (globN s "heap_ptr") (globN allocated "heap_ptr")) :
    EvmStepCC ["heap_ptr"] s post ∧
      ByteRegionEffect allocated post Rl ∧ post.locals = allocated.locals := by
  obtain ⟨heff, hl⟩ := m23_bre_of_store_word halloc.1.1.1.1.memaddrs hrun hword hdst
  exact ⟨evmStepCC_of_allocated_heap_effect hInv halloc hmem hbe heff hin, heff, hl⟩

theorem transfer_log_address_store_spec {F : Type}
    (s allocated : PanSemStateFiniteExact 64 F) (logw sysw : BitVec 64)
    (hInv : EvmInv s) (halloc : EvmStepCC ["heap_ptr"] s allocated)
    (hmem : allocated.memory = s.memory) (hbe : allocated.be = s.be)
    (hlog : allocated.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hsys : allocated.globals.lookup (ofString "vm_system_address") = some (.val (.word sysw)))
    (hwords : WordsOK allocated (logw.toNat, 40))
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN allocated "heap_ptr")) :
    let out := evaluateHOLFiniteState allocated
      (.store (.op .add [.var .local (ofString "log"), .const 0])
        (.var .global (ofString "vm_system_address")))
    out.1 = none ∧ EvmStepCC ["heap_ptr"] s out.2 ∧
      memW out.2 logw.toNat = globN out.2 "vm_system_address" ∧
      ByteRegionEffect allocated out.2 [(logw.toNat, 40)] ∧ out.2.locals = allocated.locals := by
  dsimp only
  have hd : allocated.memaddrs logw := by
    have hw := hwords.2.2 0 (by omega)
    obtain ⟨w, hdom, _⟩ := hw
    simpa using hdom
  have hrun : evaluateHOLFiniteState allocated
      (.store (.op .add [.var .local (ofString "log"), .const 0])
        (.var .global (ofString "vm_system_address"))) =
      (none, { allocated with memory := fun a => if a = logw then .word sysw else allocated.memory a }) := by
    simp [evaluateHOLFiniteState_store, evalHOLExact, evalListHOLExact, hlog, hsys,
      wordOpHOL, wordOp, valueIsWord, valueWord, flattenHOL, panMemStoresHOL,
      panMemStoreHOL, hd]
  rw [hrun]
  obtain ⟨hstep, heff, hl⟩ := transfer_allocated_store_step hInv halloc hmem hbe hrun
    (Rl := [(logw.toNat, 40)])
    (fun v hv => ⟨sysw, by simpa [evalHOLExact, hsys] using hv.symm⟩)
    (fun addr ha _ => by
      have heq : addr = logw := by
        simpa [evalHOLExact, evalListHOLExact, hlog, wordOpHOL, wordOp, valueIsWord, valueWord]
          using ha.symm
      subst addr
      exact ⟨(logw.toNat, 40), by simp, le_rfl, by omega⟩)
    (fun i hi => by rcases List.mem_singleton.mp hi with rfl; exact hin)
  refine ⟨rfl, hstep, ?_, heff, hl⟩
  simp [memW, globN, hsys]

theorem transfer_alloc_log_address_prefix {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p sysw : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hsys : s.globals.lookup (ofString "vm_system_address") = some (.val (.word sysw)))
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "log") .one (ofString "alloc") [.const 40]
        (.seq (.store (.op .add [.var .local (ofString "log"), .const 0])
          (.var .global (ofString "vm_system_address"))) cont))).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.locals.lookup (ofString "log") = some (.val (.word p)) ∧
      globN mid "heap_ptr" = p.toNat + 40 ∧
      memW mid p.toNat = globN mid "vm_system_address" ∧
      WordsOK mid (p.toNat, 40) ∧
      EvmStepCC ["heap_ptr"] s mid ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "log") .one (ofString "alloc") [.const 40]
          (.seq (.store (.op .add [.var .local (ofString "log"), .const 0])
            (.var .global (ofString "vm_system_address"))) cont))).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "log") .one (ofString "alloc") [.const 40]
          (.seq (.store (.op .add [.var .local (ofString "log"), .const 0])
            (.var .global (ofString "vm_system_address"))) cont))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString "log", s.locals.lookup (ofString "log")) } ∧
      mid.be = s.be ∧
      (∀ k, k ≠ ofString "log" → mid.locals.lookup k = s.locals.lookup k) ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) := by
  obtain ⟨allocated, hx, hhp, hwords, hstep, hr, hs, hm, hb, hl⟩ :=
    transfer_decCall_alloc_exact_spec s (ofString "log") _ p 40 (Or.inl rfl) hInv hp hres
  have hsys' : allocated.globals.lookup (ofString "vm_system_address") = some (.val (.word sysw)) :=
    (hstep.1.2.2.1 _ (by decide)).symm.trans hsys
  have hp0 : globN s "heap_ptr" = p.toNat := by simp [globN, hp]
  have hin : Inside (p.toNat, 40) (globN s "heap_ptr") (globN allocated "heap_ptr") :=
    ⟨by rw [hp0], by rw [hhp]⟩
  obtain ⟨hnone, hstore_step, haddr, heff, hloc⟩ :=
    transfer_log_address_store_spec s allocated p sysw hInv hstep hm hb hx hsys' hwords hin
  let mid := (evaluateHOLFiniteState allocated
    (.store (.op .add [.var .local (ofString "log"), .const 0])
      (.var .global (ofString "vm_system_address")))).2
  have hseq : evaluateHOLFiniteState allocated
      (.seq (.store (.op .add [.var .local (ofString "log"), .const 0])
        (.var .global (ofString "vm_system_address"))) cont) = evaluateHOLFiniteState mid cont := by
    rw [evaluateHOLFiniteState_seq_line780]
    simp only [hnone]
    rfl
  change ByteRegionEffect allocated mid [(p.toNat, 40)] at heff
  change EvmStepCC ["heap_ptr"] s mid at hstore_step
  rw [hseq] at hr hs
  have frames := evmStepCC_of_accumulated_heap_effect hInv hstep hb
    (fun a _ => congrFun hm a) (fun b _ _ => by simp only [memB, hm, hb]) heff
    (fun i hi => by rcases List.mem_singleton.mp hi with rfl; exact hin)
  refine ⟨mid, hloc ▸ hx, ?_, haddr, ?_, hstore_step, hr ▸ hres, hr, hs,
    heff.be.trans hb, fun k hk => by rw [hloc]; exact hl k hk, frames.2.1, frames.2.2⟩
  · simpa only [globN, heff.globals] using hhp
  · apply wordsOK_of_inside_heap _ hstore_step.1.1.1.1.memaddrs
    · exact hwords.1
    · decide
    · rw [← hp0]; exact hInv.1.2.1
    · have hlim := hstore_step.1.1.1.2.2.1
      have hhp_mid : globN mid "heap_ptr" = p.toNat + 40 := by
        simpa only [globN, heff.globals] using hhp
      have : heapLimit ≤ heapEnd := by decide
      omega

private theorem word_dom_lt_heapEnd_local {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma addr) :
    addr.toNat + 8 ≤ heapEnd := by
  rw [hma, Wave8Contracts.M08.ordinaryDomain_iff] at hdom
  rw [R11Shards.heapEnd_val] at hdom ⊢
  omega

private theorem bv_add_off_nat_local (base : BitVec 64) (off : Nat)
    (hbase : base.toNat < heapEnd) (hoff : off ≤ 96) :
    (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  rw [R11Shards.heapEnd_val] at hbase
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  have ho_lt : off < 18446744073709551616 := by omega
  have hsum_lt : base.toNat + off < 18446744073709551616 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, h264, Nat.mod_eq_of_lt ho_lt, Nat.mod_eq_of_lt hsum_lt]

private theorem eval_var_local_eq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (w : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word w))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString nm)) =
      some (.val (.word w)) := hloc

private theorem eval_var_local_zero_eq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString nm)) =
      some (.val (.word (base + BitVec.ofNat 64 0))) := by
  have hz : base + BitVec.ofNat 64 0 = base := BitVec.add_zero base
  rw [hz]; exact hloc

private theorem eval_add_local_const_eq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64) (off : Nat)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (base + BitVec.ofNat 64 off))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (base + w)))) hz

private theorem eval_align8_eq0_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .and [.var .local (ofString nm), .const 7#64]) (.const 0#64)) =
      some (.val (.word (if (base &&& 7#64) = 0#64 then 1 else 0))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    Compiler.Encoders.Asm.wordCmpHOL]
  have h7 : (7#64 : BitVec 64) &&& 18446744073709551615#64 = 7#64 := by decide
  change some (ValueHOL.val (HolWordLab.word (if decide ((base &&& (7#64 &&& 18446744073709551615#64)) = 0#64) = true then 1 else 0))) = _
  rw [h7]
  by_cases hc : (base &&& 7#64) = 0#64 <;> simp [hc]

private theorem return_const0_step_local {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.return (.const 0#64))).1 = some (.returned (.val (.word 0))) ∧
    (evaluateHOLFiniteState s (.return (.const 0#64))).2 = emptyLocalsHOLFinite s := by
  rw [evaluateHOLFiniteState_return]
  have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 0#64) = some (.val (.word 0)) := rfl
  rw [he]
  have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  dsimp only
  rw [if_pos hsz]
  exact ⟨rfl, rfl⟩

private theorem return_eff_local {F : Type} (s : PanSemStateFiniteExact 64 F) (ex : ExpHOL 64) (Rl : List Ivl) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.return ex)).2 Rl := by
  have hret : (evaluateHOLFiniteState s (.return ex)).2 =
      { s with locals := (evaluateHOLFiniteState s (.return ex)).2.locals } := by
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  conv => arg 2; rw [hret]
  exact (ByteRegionEffect.refl s Rl).with_locals_clock _ s.clock

private theorem bswap64_body_ro_local {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).2 Rl := by
  have hb : sourceFnBody Guest.Software.guestFn_bswap64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_bswap64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_bswap64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  have hasgn : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64),
      (evaluateHOLFiniteState st (.assign .local nm ex)).2 =
        { st with locals := (evaluateHOLFiniteState st (.assign .local nm ex)).2.locals } := by
    intro st nm ex
    rw [evaluateHOLFiniteState_assign]
    split
    · rfl
    · split <;> rfl
  have hseq_ro : ∀ (st : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64),
      ByteRegionEffect st (evaluateHOLFiniteState st a).2 Rl →
      (∀ m, ByteRegionEffect st m Rl → ByteRegionEffect st (evaluateHOLFiniteState m b).2 Rl) →
      ByteRegionEffect st (evaluateHOLFiniteState st (.seq a b)).2 Rl := by
    intro st a b ha hb'
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState st a with ⟨r1, s1⟩
    rw [h1] at ha
    cases r1 with
    | none => exact hb' s1 ha
    | some _ => exact ha
  have hasgn_eff : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64),
      ByteRegionEffect st (evaluateHOLFiniteState st (.assign .local nm ex)).2 Rl := by
    intro st nm ex
    conv => arg 2; rw [hasgn st nm ex]
    exact (ByteRegionEffect.refl st Rl).with_locals_clock _ st.clock
  refine hseq_ro s _ _ (hasgn_eff s _ _) fun s1 hs1 => ?_
  exact hs1.trans (hseq_ro s1 _ _ (hasgn_eff s1 _ _) (fun s2 hs2 => hs2.trans (return_eff_local s2 _ Rl)))

private theorem decCall_bswap64_eff_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    {argExp : ExpHOL 64} {cont : ProgHOL 64} {Rl : List Ivl}
    (hcode : s.code = originalRuntimeCode)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode →
      mid.memaddrs = s.memaddrs →
      mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") →
      (∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv))) →
      ByteRegionEffect mid (evaluateHOLFiniteState mid cont).2 Rl) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.decCall (ofString "w") .one (ofString "bswap64") [argExp] cont)).2
      Rl := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] with _ | vals
  · exact ByteRegionEffect.refl s Rl
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨body', callee, ret'⟩
    · exact ByteRegionEffect.refl s Rl
    · dsimp only
      have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact EvmFrameSpecs.lookup_bswap64) hl
      subst hinst
      have hret_eq : ret' = .one :=
        lookupCodeHOLFinite_installed_return s (ofString "bswap64") _ _ _ .one ret' vals callee
          (by rw [hcode]; exact EvmFrameSpecs.lookup_bswap64) hl
      subst hret_eq
      split
      · exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro_local (callEntryStateHOLFinite s callee) Rl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
        rw [hb] at heff_b
        dsimp only at heff_b ⊢
        have heff_sb : ByteRegionEffect s sb Rl := heff_entry.trans heff_b
        cases rb with
        | none => exact heff_sb
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · rename_i hsh
              have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                rcases v with ⟨⟨wv⟩⟩ | _ | _
                · exact ⟨wv, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
              obtain ⟨wv, rfl⟩ := hvw
              let mid := setVarHOLFinite (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
              have heff_mid : ByteRegionEffect s mid Rl := heff_sb.with_locals_clock _ _
              have hout_mid : mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "w" ≠ ofString "out" by decide]
              have hw_mid : ∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv)) :=
                ⟨wv, by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
              have heff_c := hcont mid (heff_mid.code.trans hcode) heff_mid.memaddrs hout_mid hw_mid
              exact (heff_mid.trans heff_c).with_locals_clock _ _
            · exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ => exact heff_sb.with_locals_clock _ _
          | «break» | «continue» => exact heff_sb

private theorem seq_call_bswap64_eff_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    {argExp : ExpHOL 64} {cont : ProgHOL 64} {Rl : List Ivl}
    (hcode : s.code = originalRuntimeCode)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode →
      mid.memaddrs = s.memaddrs →
      mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") →
      (∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv))) →
      ByteRegionEffect mid (evaluateHOLFiniteState mid cont).2 Rl) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [argExp]) cont)).2
      Rl := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [argExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] with _ | vals
  · rw [hargs] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s Rl
  · rw [hargs] at hc; dsimp only at hc
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s Rl
    · rw [hl] at hc; dsimp only at hc
      have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact EvmFrameSpecs.lookup_bswap64) hl
      subst hinst
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro_local (callEntryStateHOLFinite s callee) Rl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
        rw [hb] at hc heff_b
        dsimp only at heff_b
        have heff_sb : ByteRegionEffect s sb Rl := heff_entry.trans heff_b
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hc
            have hret_eq : ret' = .one :=
              lookupCodeHOLFinite_installed_return s (ofString "bswap64") _ _ _ .one ret' vals callee
                (by rw [hcode]; exact EvmFrameSpecs.lookup_bswap64) hl
            subst hret_eq
            split at hc
            · rename_i hsh
              have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                rcases v with ⟨⟨wv⟩⟩ | _ | _
                · exact ⟨wv, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
              obtain ⟨wv, rfl⟩ := hvw
              split at hc
              · injection hc with hr hsc; subst hr hsc
                dsimp only
                let mid := setKvarHOLFinite .local (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
                have heff_mid : ByteRegionEffect s mid Rl := heff_sb.with_locals_clock _ _
                have hout_mid : mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                  simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "w" ≠ ofString "out" by decide]
                have hw_mid : ∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv)) :=
                  ⟨wv, by simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
                exact heff_mid.trans (hcont mid (heff_mid.code.trans hcode) heff_mid.memaddrs hout_mid hw_mid)
              · injection hc with hr hsc; subst hr hsc; exact heff_sb
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb

private theorem seq_store_word_eff_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {base w : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hma : s.memaddrs = ordinaryDomain)
    (hlen : len ≤ 32)
    (hoff : off + 8 ≤ len)
    (hprev : off > 0 → base.toNat < heapEnd)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w)))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd →
      s1.code = s.code →
      s1.memaddrs = s.memaddrs →
      s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.seq (.store dstExp valExp) cont)).2 [(base.toNat, len)] := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s (.store dstExp valExp) with ⟨r1, s1⟩
  cases r1 with
  | some _ =>
    have h1' := h1
    rw [evaluateHOLFiniteState_store, hdst, hval] at h1'
    dsimp only at h1'
    split at h1'
    · cases h1'
    · injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
  | none =>
    have hbase_lt : base.toNat < heapEnd := by
      have hrun' := h1
      rw [evaluateHOLFiniteState_store, hdst, hval] at hrun'
      dsimp only at hrun'
      split at hrun'
      · rename_i m' hst
        unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
        by_cases hd : s.memaddrs (base + BitVec.ofNat 64 off)
        · by_cases hz : off = 0
          · subst hz; have h0 : base + BitVec.ofNat 64 0 = base := by simp
            rw [h0] at hd; have := word_dom_lt_heapEnd_local hma base hd; omega
          · exact hprev (by omega)
        · simp [hd] at hst
      · cases hrun'
    have heff1 := m23_bre_of_store_word (Rl := [(base.toNat, len)]) hma h1
      (fun v hv => by rw [hval] at hv; injection hv with h; exact ⟨w, h.symm⟩)
      (fun addr ha _ => by
        rw [hdst] at ha
        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
        have hnat := bv_add_off_nat_local base off hbase_lt (by omega)
        exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact heff1.1.trans (hcont s1 hbase_lt heff1.1.code heff1.1.memaddrs heff1.2)

private theorem u256_to_be32_aligned_body_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hout_lu : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hout8 : out.toNat % 8 = 0) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2
      [(out.toNat, 32)] := by
  have hal : (out &&& 7#64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h7 : (7#64 : BitVec 64).toNat = 7 := rfl
    rw [h7]
    have hmod : out.toNat &&& 7 = out.toNat % 8 := Nat.and_two_pow_sub_one_eq_mod out.toNat 3
    rw [hmod, hout8]; rfl
  have hb : sourceFnBody Guest.Software.guestFn_u256_to_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_to_be32).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  have hcond := eval_align8_eq0_local s "out" out hout_lu
  have hdc_ne_none : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL)
      (fn : MlS) (args : List (ExpHOL 64)) (c : ProgHOL 64),
      (∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m c).1 ≠ none) →
      (evaluateHOLFiniteState st (.decCall nm sh fn args c)).1 ≠ none := by
    intro st nm sh fn args c hc_nn
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) args with _ | _
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite st.code.lookup fn _ with _ | ⟨b', cal', rs'⟩
      · simp
      · dsimp only; split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite st cal') b' with ⟨rb, sb⟩
          cases rb with
          | none => simp
          | some r =>
            cases r with
            | returned _ => dsimp only; split <;> [ exact hc_nn _; simp ]
            | _ => simp
  have hseq_ne_none : ∀ {p1 p2 : ProgHOL 64},
      (∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m p2).1 ≠ none) →
      ∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m (.seq p1 p2)).1 ≠ none := by
    intro p1 p2 hp2 m
    rw [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState m p1 with ⟨r1, m1⟩
    cases r1 with
    | none => exact hp2 m1
    | some _ => simp
  have hret_ne_none : ∀ (m : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState m (.return (.const 0#64))).1 ≠ none := by
    intro m; rw [(return_const0_step_local m).1]; simp
  let yesProg256 : ProgHOL 64 :=
    .decCall (ofString "w") .one (ofString "bswap64") [.rfield 3 (.var .local (ofString "a"))]
      (.seq (.store (.var .local (ofString "out")) (.var .local (ofString "w")))
        (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 2 (.var .local (ofString "a"))])
          (.seq (.store (.op .add [.var .local (ofString "out"), .const 8#64]) (.var .local (ofString "w")))
            (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 1 (.var .local (ofString "a"))])
              (.seq (.store (.op .add [.var .local (ofString "out"), .const 16#64]) (.var .local (ofString "w")))
                (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 0 (.var .local (ofString "a"))])
                  (.seq (.store (.op .add [.var .local (ofString "out"), .const 24#64]) (.var .local (ofString "w")))
                    (.return (.const 0#64)))))))))
  have hyes256_nn : (evaluateHOLFiniteState s yesProg256).1 ≠ none :=
    hdc_ne_none s _ _ _ _ _
      (hseq_ne_none (hseq_ne_none (hseq_ne_none (hseq_ne_none
        (hseq_ne_none (hseq_ne_none (hseq_ne_none hret_ne_none)))))))
  have hgoal_yes256 : evaluateHOLFiniteState s
      (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7#64]) (.const 0#64)) yesProg256 .skip)
        (.seq (.call (some (none, none)) (ofString "st_be64") [.var .local (ofString "out"), .rfield 3 (.var .local (ofString "a"))])
          (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 8#64], .rfield 2 (.var .local (ofString "a"))])
            (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 16#64], .rfield 1 (.var .local (ofString "a"))])
              (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 24#64], .rfield 0 (.var .local (ofString "a"))])
                (.return (.const 0#64))))))) = evaluateHOLFiniteState s yesProg256 := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
    simp only [hal, ↓reduceIte]
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10]
    rcases hy : evaluateHOLFiniteState s yesProg256 with ⟨ry, sy⟩
    rw [hy] at hyes256_nn
    cases ry with
    | none => exact absurd rfl hyes256_nn
    | some _ => rfl
  rw [hgoal_yes256]
  exact decCall_bswap64_eff_local (s := s) (Rl := [(out.toNat, 32)]) hcode
    fun mid0 hc_m0 hm_m0 hout_m0 ⟨wv0, hw_m0⟩ => by
      have ho0 : mid0.locals.lookup (ofString "out") = some (.val (.word out)) := by
        rw [hout_m0]; exact hout_lu
      refine seq_store_word_eff_local (s := mid0) (base := out) (w := wv0) (off := 0) (len := 32)
        (hm_m0.trans hma) (by omega) (by omega) (fun h => by omega)
        (eval_var_local_zero_eq mid0 "out" out ho0)
        (eval_var_local_eq mid0 "w" wv0 hw_m0) fun s1 hout_lt hc_s1 hm_s1 hl_s1 => ?_
      refine seq_call_bswap64_eff_local (s := s1) (Rl := [(out.toNat, 32)])
        (hc_s1.trans hc_m0) fun mid1 hc_m1 hm_m1 hout_m1 ⟨wv1, hw_m1⟩ => ?_
      have ho1 : mid1.locals.lookup (ofString "out") = some (.val (.word out)) := by
        rw [hout_m1, hl_s1]; exact ho0
      refine seq_store_word_eff_local (s := mid1) (base := out) (w := wv1) (off := 8) (len := 32)
        (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))) (by omega) (by omega) (fun _ => hout_lt)
        (eval_add_local_const_eq mid1 "out" out 8 ho1)
        (eval_var_local_eq mid1 "w" wv1 hw_m1) fun s2 _ hc_s2 hm_s2 hl_s2 => ?_
      refine seq_call_bswap64_eff_local (s := s2) (Rl := [(out.toNat, 32)])
        (hc_s2.trans hc_m1) fun mid2 hc_m2 hm_m2 hout_m2 ⟨wv2, hw_m2⟩ => ?_
      have ho2 : mid2.locals.lookup (ofString "out") = some (.val (.word out)) := by
        rw [hout_m2, hl_s2]; exact ho1
      refine seq_store_word_eff_local (s := mid2) (base := out) (w := wv2) (off := 16) (len := 32)
        (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))))) (by omega) (by omega)
        (fun _ => hout_lt)
        (eval_add_local_const_eq mid2 "out" out 16 ho2)
        (eval_var_local_eq mid2 "w" wv2 hw_m2) fun s3 _ hc_s3 hm_s3 hl_s3 => ?_
      refine seq_call_bswap64_eff_local (s := s3) (Rl := [(out.toNat, 32)])
        (hc_s3.trans hc_m2) fun mid3 _ hm_m3 hout_m3 ⟨wv3, hw_m3⟩ => ?_
      have ho3 : mid3.locals.lookup (ofString "out") = some (.val (.word out)) := by
        rw [hout_m3, hl_s3]; exact ho2
      refine seq_store_word_eff_local (s := mid3) (base := out) (w := wv3) (off := 24) (len := 32)
        (hm_m3.trans (hm_s3.trans (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma)))))))
        (by omega) (by omega) (fun _ => hout_lt)
        (eval_add_local_const_eq mid3 "out" out 24 ho3)
        (eval_var_local_eq mid3 "w" wv3 hw_m3) fun s4 _ _ _ _ => return_eff_local s4 _ _

theorem eval_call_u256_to_be32_aligned_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F) (aExp outExp : ExpHOL 64)
    (av : ValueHOL 64) (out0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) aExp =
      some av)
    (hout : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) outExp =
      some (.val (.word out0)))
    (hout8 : out0.toNat % 8 = 0)
    (hsub : ∃ ivl ∈ Rl, ivl.1 ≤ out0.toNat ∧ out0.toNat + 32 ≤ ivl.1 + ivl.2)
    (hnone : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "u256_to_be32") [aExp, outExp])).1 = none) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "u256_to_be32") [aExp, outExp])
    ByteRegionEffect s out.2 Rl ∧ out.2.locals = s.locals := by
  dsimp only
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [aExp, outExp] =
      some [av, .val (.word out0)] := by
    simp [evalListHOLFinite, evalListHOLExact, ha, hout]
  rw [hargs] at hnone ⊢; dsimp only at hnone ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_to_be32") [av, .val (.word out0)] with _ | ⟨body', callee, ret'⟩
  · rw [hl] at hnone; simp at hnone
  · rw [hl] at hnone; dsimp only at hnone ⊢
    by_cases hclk0 : s.clock = 0
    · rw [if_pos hclk0] at hnone; simp at hnone
    · rw [if_neg hclk0] at hnone ⊢
      have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "u256_to_be32")
        _ _ body' _ ret' [av, .val (.word out0)] callee
        (by rw [hcode]; exact EvmFrameSpecs.lookup_u256_to_be32) hl
      have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "u256_to_be32")
        _ _ _ .one ret' [av, .val (.word out0)] callee
        (by rw [hcode]; exact EvmFrameSpecs.lookup_u256_to_be32) hl
      subst hinst hret_eq
      have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
        s.code.lookup (ofString "u256_to_be32") [av, .val (.word out0)] _ callee .one hl
      rw [hcode] at hx
      simp only [Flapjack.lookupCodeHOLExact, EvmFrameSpecs.lookup_u256_to_be32] at hx
      have hcal_out : callee.lookup (ofString "out") = some (.val (.word out0)) := by
        split at hx
        · have hmap := congrArg (fun x => x.2.1) (Option.some.inj hx)
          have := congrFun hmap.symm (ofString "out")
          simpa [List.map, List.zip, List.foldl] using this
        · cases hx
      let entry := callEntryStateHOLFinite s callee
      have hent_out : entry.locals.lookup (ofString "out") = some (.val (.word out0)) := hcal_out
      have heff_b := u256_to_be32_aligned_body_bre entry out0 hcode hma hent_out hout8
      rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_u256_to_be32) with ⟨br, bs⟩
      have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
          (sourceFnBody Guest.Software.guestFn_u256_to_be32) = (br, bs) := hb
      simp only [hb'] at hnone ⊢
      rw [hb] at heff_b; dsimp only at heff_b
      cases br with
      | none => simp at hnone
      | some r =>
        cases r with
        | returned rv =>
          dsimp only at hnone ⊢
          split at hnone
          · rename_i hsh
            rw [if_pos hsh]
            have heff_s_ent : ByteRegionEffect s entry [(out0.toNat, 32)] :=
              (ByteRegionEffect.refl s _).with_locals_clock entry.locals entry.clock
            have heff32 : ByteRegionEffect s { bs with locals := s.locals } [(out0.toNat, 32)] :=
              (heff_s_ent.trans heff_b).with_locals_clock s.locals bs.clock
            have heff_out : ByteRegionEffect s { bs with locals := s.locals } Rl :=
              heff32.mono fun i hi => by
                simp only [List.mem_singleton] at hi; subst hi
                exact hsub
            exact ⟨heff_out, rfl⟩
          · simp at hnone
        | _ => simp at hnone

private theorem lst_push_body_returned_spec {F : Type}
    (ent : PanSemStateFiniteExact 64 F)
    (lw : BitVec 64)
    (hAs : ArenaReady ent)
    (hent_l : ent.locals.lookup (ofString "l") = some (.val (.word lw)))
    (hent_e : ent.locals.lookup (ofString "esz") = some (.val (.word 8#64)))
    (hlw_words : WordsOK ent (lw.toNat, 24))
    (hlw_disj_heap : globN ent "heap_ptr" ≤ lw.toNat + 24 → heapLimit ≤ lw.toNat)
    (hlst0 : 1 ≤ memW ent (lw.toNat + 16) ∧ memW ent (lw.toNat + 8) ≤ memW ent (lw.toNat + 16))
    (hcap_bnd : memW ent (lw.toNat + 16) < 2 ^ 32)
    (hp0_words : WordsOK ent (memW ent lw.toNat, 8 * memW ent (lw.toNat + 16)))
    (hp0_disj_lw : Disj (lw.toNat, 24) (memW ent lw.toNat, 8 * memW ent (lw.toNat + 16)))
    (hp0_disj_heap :
      globN ent "heap_ptr" < memW ent lw.toNat + 8 * memW ent (lw.toNat + 16) →
      heapLimit ≤ memW ent lw.toNat)
    (vb : ValueHOL 64) (sb : PanSemStateFiniteExact 64 F)
    (hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_push) =
      (some (.returned vb), sb)) :
    let n0 := memW ent (lw.toNat + 8)
    let cap0 := memW ent (lw.toNat + 16)
    let p0 := memW ent lw.toNat
    -- No-grow branch (`n0 < cap0`):
    (n0 < cap0 ∧
      ∃ ew : BitVec 64,
        vb = .val (.word ew) ∧
        ew.toNat = p0 + 8 * n0 ∧
        ew.toNat % 8 = 0 ∧
        ent.memaddrs ew ∧
        ArenaReady sb ∧
        ByteRegionEffect ent sb [(lw.toNat, 24)] ∧
        memW sb lw.toNat = p0 ∧
        memW sb (lw.toNat + 8) = n0 + 1 ∧
        memW sb (lw.toNat + 16) = cap0 ∧
        (∀ i < n0, memW sb (p0 + 8 * i) = memW ent (p0 + 8 * i))) ∨
    -- Grow branch (`n0 = cap0`):
    (n0 = cap0 ∧
      ∃ (ma : PanSemStateFiniteExact 64 F) (npw ew : BitVec 64),
        vb = .val (.word ew) ∧
        ArenaReady ma ∧
        ma.memory = ent.memory ∧
        ma.be = ent.be ∧
        ma.memaddrs = ent.memaddrs ∧
        npw.toNat = globN ent "heap_ptr" ∧
        npw.toNat % 8 = 0 ∧
        globN ma "heap_ptr" = npw.toNat + 16 * cap0 ∧
        GlobalsKept ["heap_ptr"] ent ma ∧
        ew.toNat = npw.toNat + 8 * n0 ∧
        ew.toNat % 8 = 0 ∧
        sb.memaddrs ew ∧
        ArenaReady sb ∧
        ByteRegionEffect ma sb [(npw.toNat, 16 * cap0), (lw.toNat, 24)] ∧
        memW sb lw.toNat = npw.toNat ∧
        memW sb (lw.toNat + 8) = n0 + 1 ∧
        memW sb (lw.toNat + 16) = 2 * cap0 ∧
        (∀ i < n0, memW sb (npw.toNat + 8 * i) = memW ma (p0 + 8 * i))) := by
  dsimp only
  have hent_ma : ent.memaddrs = ordinaryDomain := hAs.1.memaddrs
  have hent_code : ent.code = originalRuntimeCode := hAs.1.code
  obtain ⟨pw0, hd0, hm_l0_raw⟩ := hlw_words.2.2 0 (by omega)
  obtain ⟨nw, hd8, hm_l8_raw⟩ := hlw_words.2.2 1 (by omega)
  obtain ⟨capw, hd16, hm_l16_raw⟩ := hlw_words.2.2 2 (by omega)
  have hlw_lt_he : lw.toNat < heapEnd := by
    rw [Nat.add_zero] at hd0
    rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff] at hd0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lw.isLt] at hd0
    exact hd0.2.2
  have hl0_bv : lw + 0#64 = BitVec.ofNat 64 lw.toNat := by simp
  have hl8_bv : lw + 8#64 = BitVec.ofNat 64 (lw.toNat + 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv_add_off_nat_local lw 8 hlw_lt_he (by omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by rw [R11Shards.heapEnd_val] at hlw_lt_he; omega)]
  have hl16_bv : lw + 16#64 = BitVec.ofNat 64 (lw.toNat + 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv_add_off_nat_local lw 16 hlw_lt_he (by omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by rw [R11Shards.heapEnd_val] at hlw_lt_he; omega)]
  have hdom_l0 : ent.memaddrs (lw + 0#64) := by rw [hl0_bv]; simpa using hd0
  have hdom_l8 : ent.memaddrs (lw + 8#64) := by rw [hl8_bv]; simpa using hd8
  have hdom_l16 : ent.memaddrs (lw + 16#64) := by rw [hl16_bv]; simpa using hd16
  have hm_l0 : ent.memory (lw + 0#64) = .word pw0 := by rw [hl0_bv]; simpa using hm_l0_raw
  have hm_l8 : ent.memory (lw + 8#64) = .word nw := by rw [hl8_bv]; simpa using hm_l8_raw
  have hm_l16 : ent.memory (lw + 16#64) = .word capw := by rw [hl16_bv]; simpa using hm_l16_raw
  have hpw0_eq : memW ent lw.toNat = pw0.toNat := by unfold memW; rw [← hl0_bv, hm_l0]
  have hnw_eq : memW ent (lw.toNat + 8) = nw.toNat := by unfold memW; rw [← hl8_bv, hm_l8]
  have hcapw_eq : memW ent (lw.toNat + 16) = capw.toNat := by unfold memW; rw [← hl16_bv, hm_l16]
  have hp0_al : (memW ent lw.toNat) % 8 = 0 := hp0_words.1
  have hp0_bnd : memW ent lw.toNat + 8 * memW ent (lw.toNat + 16) < 2 ^ 64 := by
    obtain ⟨_, hd, _⟩ := hp0_words.2.2 (memW ent (lw.toNat + 16) - 1) (by have := hlst0.1; omega)
    rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff] at hd
    have hhe_val : heapEnd = 33806089704 := R11Shards.heapEnd_val
    have hlt64 : memW ent lw.toNat + 8 * (memW ent (lw.toNat + 16) - 1) < 2 ^ 64 := by
      obtain ⟨_, hdb, _⟩ := hp0_words.2.2 0 (by have := hlst0.1; omega)
      rw [Nat.add_zero] at hdb
      rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff] at hdb
      have hp0_lt64 : memW ent lw.toNat < 2 ^ 64 := by rw [hpw0_eq]; exact pw0.isLt
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp0_lt64] at hdb
      have := hdb.2.2; omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at hd
    have := hd.2.2; have := hlst0.1; omega
  let e1 := setVarHOLFinite (ofString "n") (.val (.word nw)) ent
  let e2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) e1
  let growProg : ProgHOL 64 :=
    .decCall (ofString "np") .one (ofString "alloc")
      [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]]
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "np"),
           .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
           .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
        (.seq
          (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np")))
          (.store (.op .add [.var .local (ofString "l"), .const 16#64])
            (.panop .mul [.var .local (ofString "cap"), .const 2#64]))))
  let tailProg : ProgHOL 64 :=
    .seq
      (.store (.op .add [.var .local (ofString "l"), .const 8#64])
        (.op .add [.var .local (ofString "n"), .const 1#64]))
      (.return (.op .add
        [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
         .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))
  have hbody_e2 : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_push) =
      (let out := evaluateHOLFiniteState e2
        (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
                growProg .skip)
              tailProg);
       (out.1, { out.2 with
         locals := HolFiniteMapExact.resVarEq
           (HolFiniteMapExact.resVarEq out.2.locals (ofString "cap", e1.locals.lookup (ofString "cap")))
           (ofString "n", ent.locals.lookup (ofString "n")) })) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_lst_push,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
    have hz_16 : (16#64 : BitVec 64) + 0 = 16#64 := BitVec.add_zero _
    have hev1 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) =
        some (.val (.word nw)) := by
      simp only [evalHOLExact, evalListHOLExact, hent_l, valueIsWord, valueWord,
        wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_8,
        memLoadHOLExact, isWfShapeExactHOL, hdom_l8, hm_l8, ↓reduceIte]
    rw [hev1]; dsimp only
    rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
    have he1_def : setVarHOLFinite (ofString "n") (.val (.word nw)) ent = e1 := rfl
    rw [he1_def, evaluateHOLFiniteState_dec_total]; dsimp only
    have he1_l : e1.locals.lookup (ofString "l") = some (.val (.word lw)) := by
      simp [e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "l" by decide, hent_l]
    have he1_dom16 : e1.memaddrs (lw + 16#64) := hdom_l16
    have he1_m16 : e1.memory (lw + 16#64) = .word capw := hm_l16
    have hev2 : @evalHOLExact 64 F _ e1.toExact (fun a => Classical.propDecidable (e1.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "l"), .const 16#64])) =
        some (.val (.word capw)) := by
      simp only [evalHOLExact, evalListHOLExact, he1_l, valueIsWord, valueWord,
        wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_16,
        memLoadHOLExact, isWfShapeExactHOL, he1_dom16, he1_m16, ↓reduceIte]
    rw [hev2]; dsimp only
    rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
  rw [hbody_e2] at hrun; dsimp only at hrun
  rcases hout_e2 : evaluateHOLFiniteState e2
      (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
              growProg .skip)
            tailProg) with ⟨ro2, so2⟩
  rw [hout_e2] at hrun
  injection hrun with hro2 hsb_eq
  subst hro2
  have he2_AR : ArenaReady e2 := (arenaReady_with_locals ent e2.locals ent.clock).2 hAs
  have he2_l : e2.locals.lookup (ofString "l") = some (.val (.word lw)) := by
    simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "l" by decide,
      show ofString "n" ≠ ofString "l" by decide, hent_l]
  have he2_e : e2.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
    simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "esz" by decide,
      show ofString "n" ≠ ofString "esz" by decide, hent_e]
  have he2_n : e2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "n" by decide]
  have he2_c : e2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
    simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_nl : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap"))) =
      some (.val (.word (if capw.toNat ≤ nw.toNat then 1#64 else 0#64))) := by
    simp only [evalHOLExact, he2_n, he2_c, Compiler.Encoders.Asm.wordCmpHOL,
      BitVec.ult, decide_eq_true_eq]
    by_cases hle : capw.toNat ≤ nw.toNat
    · have hlt_f : ¬ (nw < capw) := fun h => by have := (BitVec.lt_def).1 h; omega
      simp [hle, hlt_f]
    · have hlt_bv : nw < capw := (BitVec.lt_def).2 (by omega)
      simp [hle, hlt_bv]
  rw [evaluateHOLFiniteState_seq_line780] at hout_e2
  rcases hite_out : evaluateHOLFiniteState e2
      (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
        growProg .skip) with ⟨ri, si⟩
  rw [hite_out] at hout_e2
  cases ri with
  | some ri' =>
    dsimp only at hout_e2
    injection hout_e2 with hri _
    exfalso
    rw [evaluateHOLFiniteState_ite, hcmp_nl] at hite_out; dsimp only at hite_out
    by_cases hgrow_cond : capw.toNat ≤ nw.toNat
    · rw [if_pos hgrow_cond, if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hite_out
      have hgr : (evaluateHOLFiniteState e2 growProg).1 = some (.returned vb) := by
        rw [hite_out, hri]
      dsimp only [growProg] at hgr
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hgr
      split at hgr <;> try simp at hgr
      split at hgr <;> try simp at hgr
      split at hgr <;> try simp at hgr
      split at hgr <;> try simp at hgr
      · split at hgr <;> try simp at hgr
        try dsimp only at hgr
        rw [evaluateHOLFiniteState_seq_line780] at hgr
        rcases hmc_o : evaluateHOLFiniteState _
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "np"),
             .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
             .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) with ⟨rmc, smc⟩
        rw [hmc_o] at hgr
        cases rmc with
        | some _ =>
          dsimp only at hgr
          rw [evaluateHOLFiniteState_call] at hmc_o
          split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
          split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
          split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
          split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
          split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
          · rename_i hnotret _ _ _
            exact hnotret vb hgr
        | none =>
          dsimp only at hgr
          rw [evaluateHOLFiniteState_seq_line780] at hgr
          rcases hst1_o : evaluateHOLFiniteState smc
            (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np"))) with ⟨rst1, sst1⟩
          rw [hst1_o] at hgr
          cases rst1 with
          | some _ =>
            dsimp only at hgr
            rw [evaluateHOLFiniteState_store] at hst1_o
            split at hst1_o <;> try (injection hst1_o with hr _; rw [← hr] at hgr; simp at hgr)
            split at hst1_o <;> try (injection hst1_o with hr _; rw [← hr] at hgr; simp at hgr)
            split at hst1_o <;> try (injection hst1_o with hr _; rw [← hr] at hgr; simp at hgr)
          | none =>
            dsimp only at hgr
            rw [evaluateHOLFiniteState_store] at hgr
            split at hgr <;> try simp at hgr
            split at hgr <;> try simp at hgr
            split at hgr <;> try simp at hgr
      · rename_i hnotret _
        exact hnotret vb hgr
    · rw [if_neg hgrow_cond, if_pos (by decide : (0#64 : BitVec 64) = 0), evaluateHOLFiniteState_skip] at hite_out
      simp at hite_out
  | none =>
    dsimp only at hout_e2
    rw [evaluateHOLFiniteState_ite, hcmp_nl] at hite_out; dsimp only at hite_out
    by_cases hgrow_cond : capw.toNat ≤ nw.toNat
    · right
      have hn_eq_cap : nw.toNat = capw.toNat := by rw [hnw_eq, hcapw_eq] at hlst0; omega
      have hnw_eq_capw : nw = capw := BitVec.eq_of_toNat_eq hn_eq_cap
      refine ⟨by rw [hnw_eq, hcapw_eq]; exact hn_eq_cap, ?_⟩
      rw [if_pos hgrow_cond, if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hite_out
      change evaluateHOLFiniteState e2
        (.decCall (ofString "np") .one (ofString "alloc")
          [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "np"),
               .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
               .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
            (.seq
              (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np")))
              (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                (.panop .mul [.var .local (ofString "cap"), .const 2#64]))))) = (none, si) at hite_out
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hite_out
      have hev_alloc : evalListHOLFinite e2 (h := fun a => Classical.propDecidable (e2.memaddrs a))
          [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]] =
          some [.val (.word (8#64 * capw * 2#64))] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, he2_e, he2_c,
          valueIsWord, valueWord, panOpHOL]
      have hlk_alloc := pan_one_word_lookup e2.code.lookup (ofString "alloc") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_alloc) (8#64 * capw * 2#64)
        (by rw [he2_AR.1.code]; exact R13Shards.lookup_alloc_r13)
      rw [hev_alloc] at hite_out; dsimp only at hite_out
      rw [hlk_alloc] at hite_out; dsimp only at hite_out
      by_cases hc_e2 : e2.clock = 0
      · rw [if_pos hc_e2] at hite_out; simp at hite_out
      · rw [if_neg hc_e2] at hite_out
        let cmap_a := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (8#64 * capw * 2#64)))
        let ent_a := callEntryStateHOLFinite e2 cmap_a
        have hent_a_AR : ArenaReady ent_a := (arenaReady_with_locals e2 cmap_a (e2.clock - 1)).2 he2_AR
        have hent_a_n : locN ent_a "n" = (8#64 * capw * 2#64).toNat := by
          simp [ent_a, cmap_a, locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rcases hrun_a : evaluateHOLFiniteState ent_a (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, sa⟩
        have hrun_a' : evaluateHOLFiniteState (callEntryStateHOLFinite e2 cmap_a)
            (sourceFnBody Guest.Software.guestFn_alloc) = (ra, sa) := hrun_a
        rw [hrun_a'] at hite_out
        cases ra with
        | none => simp at hite_out
        | some ra' =>
          cases ra' with
          | timeOut | «break» | «continue» | error | finalFfi _ | exception _ _ =>
            simp at hite_out
          | returned va =>
            have hres_enta : Wave8Contracts.M12.Resumes
                (evaluateHOLFiniteState ent_a (sourceFnBody Guest.Software.guestFn_alloc)).1 :=
              Or.inl ⟨va, congrArg Prod.fst hrun_a⟩
            obtain ⟨npw, qw, hrv_a, hnpw_eq, hqw_eq, hqw_lim, hqw8, hnpw_le_qw,
              hsa_g, hsa_m, hsa_be, hsa_ma, hAsa, hsa_hp, hsa_sp⟩ :=
              R13Shards.alloc_body_resumes_props ent_a he2_AR.1.code hent_a_AR hres_enta
            rw [hrun_a] at hrv_a hsa_g hsa_m hsa_be hsa_ma hAsa hsa_hp hsa_sp
            dsimp only at hrv_a hsa_g hsa_m hsa_be hsa_ma hAsa hsa_hp hsa_sp hite_out
            injection hrv_a with hva; injection hva with hva'; subst hva'
            rw [hent_a_n] at hqw_eq
            have hsh_a : (shapeEqHOL (shapeOfHOLExact (.val (.word npw) : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.val (.word npw) : ValueHOL 64)) .one) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            rw [if_pos hsh_a] at hite_out
            let ma := setVarHOLFinite (ofString "np") (.val (.word npw)) { sa with locals := e2.locals }
            have hma_AR : ArenaReady ma := (arenaReady_with_locals sa _ sa.clock).2 hAsa
            have hma_m : ma.memory = ent.memory := hsa_m
            have hma_be : ma.be = ent.be := hsa_be
            have hma_ma : ma.memaddrs = ordinaryDomain := hsa_ma.trans hent_ma
            have hma_code : ma.code = originalRuntimeCode := hma_AR.1.code
            have hma_gk : GlobalsKept ["heap_ptr"] ent ma := by
              intro k hk
              have hk1 : k ≠ ofString "heap_ptr" := by simpa using hk
              change ent.globals.lookup k = sa.globals.lookup k
              have hent_a_gl : ent_a.globals = ent.globals := rfl
              rw [hsa_g, hent_a_gl]
              simp [HolFiniteMapExact.lookup_update, FUPDATE, hk1, Ne.symm hk1]
            have hnpw_eq_s : npw.toNat = globN ent "heap_ptr" := hnpw_eq
            have hnpw8 : npw.toNat % 8 = 0 := by rw [hnpw_eq_s]; exact hAs.2.2.2.2.2.2.1
            have hcapw_lt32 : capw.toNat < 2 ^ 32 := by rwa [← hcapw_eq]
            have hmul8_lt : 8 * capw.toNat < 2 ^ 64 := by omega
            have h8c_bv : (8#64 * capw).toNat = 8 * capw.toNat := by
              have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
              rw [BitVec.toNat_mul, h8, Nat.mod_eq_of_lt hmul8_lt]
            have hmul16_lt : 8 * capw.toNat * 2 < 2 ^ 64 := by omega
            have hmul2_toNat : (8#64 * capw * 2#64).toNat = 16 * capw.toNat := by
              have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
              rw [BitVec.toNat_mul, h8c_bv, h2, Nat.mod_eq_of_lt hmul16_lt]; omega
            have hmul2_div : (16 * capw.toNat + 7) / 8 * 8 = 16 * capw.toNat := by omega
            have hma_hp : globN ma "heap_ptr" = npw.toNat + 16 * capw.toNat := by
              change globN sa "heap_ptr" = _
              rw [hsa_hp, hqw_eq, hmul2_toNat, hmul2_div]
            have hnpw_hi_lim : npw.toNat + 16 * capw.toNat ≤ heapLimit := by
              rw [← hma_hp]; exact hma_AR.2.2.1
            rcases hma_cont : evaluateHOLFiniteState ma
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "np"),
                   .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                   .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                (.seq
                  (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np")))
                  (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                    (.panop .mul [.var .local (ofString "cap"), .const 2#64])))) with ⟨rg1, sg1⟩
            rw [hma_cont] at hite_out; dsimp only at hite_out
            injection hite_out with hrg1 hsi_eq
            subst hrg1
            rw [evaluateHOLFiniteState_seq_line780] at hma_cont
            rcases hmc_out : evaluateHOLFiniteState ma
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "np"),
                 .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                 .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) with ⟨rmc, smc⟩
            rw [hmc_out] at hma_cont
            cases rmc with
            | some _ => dsimp only at hma_cont; simp at hma_cont
            | none =>
              dsimp only at hma_cont
              have hma_np : ma.locals.lookup (ofString "np") = some (.val (.word npw)) := by
                simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hma_l : ma.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "np" ≠ ofString "l" by decide, he2_l]
              have hma_e : ma.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
                simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "np" ≠ ofString "esz" by decide, he2_e]
              have hma_n : ma.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "np" ≠ ofString "n" by decide, he2_n]
              have hma_c : ma.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
                simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "np" ≠ ofString "cap" by decide, he2_c]
              have hma_dom0 : ma.memaddrs (lw + 0#64) := by rw [hma_ma, ← hent_ma]; exact hdom_l0
              have hma_m0 : ma.memory (lw + 0#64) = .word pw0 := by rw [hma_m]; exact hm_l0
              have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
              have hev_mc_dst : @evalHOLExact 64 F _ ma.toExact (fun a => Classical.propDecidable (ma.memaddrs a))
                  (.var .local (ofString "np")) = some (.val (.word npw)) := by
                simp [evalHOLExact, hma_np]
              have hev_mc_src : @evalHOLExact 64 F _ ma.toExact (fun a => Classical.propDecidable (ma.memaddrs a))
                  (.load .one (.op .add [.var .local (ofString "l"), .const 0#64])) =
                  some (.val (.word pw0)) := by
                simp only [evalHOLExact, evalListHOLExact, hma_l, valueIsWord, valueWord,
                  wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
                  memLoadHOLExact, isWfShapeExactHOL, hma_dom0, hma_m0, ↓reduceIte]
              have hev_mc_n : @evalHOLExact 64 F _ ma.toExact (fun a => Classical.propDecidable (ma.memaddrs a))
                  (.panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]) =
                  some (.val (.word (8#64 * nw))) := by
                simp [evalHOLExact, evalListHOLExact, hma_e, hma_n, valueIsWord, valueWord, panOpHOL]
              let Rg : List Ivl := [(npw.toNat, 16 * capw.toNat), (lw.toNat, 24)]
              have h8n_bv : (8#64 * nw).toNat = 8 * nw.toNat := by
                rw [hnw_eq_capw, h8c_bv, ← hn_eq_cap]
              -- Extract both `ByteRegionEffect` AND `MemCopyRel` from `memcpy(npw, pw0, 8 * nw)`:
              have hmc_bre_all := InitECandidate.Solver.Wave8GuestInv.M11.eval_call_memcpy_bre
                ma _ _ _ npw pw0 (8#64 * nw) Rg hma_code hma_ma hev_mc_dst hev_mc_src hev_mc_n
                (fun _ => ⟨(npw.toNat, 16 * capw.toNat), by simp [Rg], le_refl _,
                  by dsimp only; rw [h8n_bv, hn_eq_cap]; omega⟩)
                (by rw [hmc_out]; simp)
              obtain ⟨heff_mc_m11, hsmc_loc⟩ := hmc_bre_all.1 (by rw [hmc_out])
              rw [hmc_out] at heff_mc_m11 hsmc_loc; dsimp only at heff_mc_m11 hsmc_loc
              have heff_mc : ByteRegionEffect ma smc Rg := m11_bre_to_m23 heff_mc_m11
              -- Also extract byte copy via `SoloHtabSet.memcpy_body_spec`:
              have hmc_copy : ∀ b : Nat, b < 8 * nw.toNat →
                  memB smc (npw.toNat + b) = memB ma (pw0.toNat + b) := by
                have hmc_call := hmc_out
                rw [evaluateHOLFiniteState_call] at hmc_call
                have hargs_mc : evalListHOLFinite ma (h := fun a => Classical.propDecidable (ma.memaddrs a))
                    [.var .local (ofString "np"),
                     .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                     .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]] =
                    some [.val (.word npw), .val (.word pw0), .val (.word (8#64 * nw))] := by
                  simp [evalListHOLFinite, evalListHOLExact, hev_mc_dst, hev_mc_src, hev_mc_n]
                have hlook_mc := pan_three_word_lookup ma.code.lookup (ofString "memcpy")
                  (ofString "dst") (ofString "src") (ofString "n")
                  (sourceFnBody Guest.Software.guestFn_memcpy) npw pw0 (8#64 * nw)
                  (by decide) (by decide) (by decide)
                  (by rw [hma_code]; exact InitECandidate.Solver.Wave8GuestInv.M11.lookup_memcpy)
                rw [hargs_mc] at hmc_call; dsimp only at hmc_call
                rw [hlook_mc] at hmc_call; dsimp only at hmc_call
                by_cases hclk_mc : ma.clock = 0
                · rw [if_pos hclk_mc] at hmc_call; simp at hmc_call
                · rw [if_neg hclk_mc] at hmc_call
                  let cmap_mc : HolFiniteMapExact MlS (ValueHOL 64) :=
                    ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word npw))).update
                      (ofString "src", ValueHOL.val (.word pw0))).update (ofString "n", ValueHOL.val (.word (8#64 * nw)))
                  let ent_mc := callEntryStateHOLFinite ma cmap_mc
                  have hent_mc_dst : ent_mc.locals.lookup (ofString "dst") = some (.val (.word npw)) := by
                    simp [ent_mc, cmap_mc, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "n" ≠ ofString "dst" by decide,
                      show ofString "src" ≠ ofString "dst" by decide]
                  have hent_mc_src : ent_mc.locals.lookup (ofString "src") = some (.val (.word pw0)) := by
                    simp [ent_mc, cmap_mc, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "n" ≠ ofString "src" by decide]
                  have hent_mc_n : ent_mc.locals.lookup (ofString "n") = some (.val (.word (8#64 * nw))) := by
                    simp [ent_mc, cmap_mc, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rcases hb_mc : evaluateHOLFiniteState ent_mc (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨br_mc, bs_mc⟩
                  have hb_mc' : evaluateHOLFiniteState (callEntryStateHOLFinite ma cmap_mc)
                      (sourceFnBody Guest.Software.guestFn_memcpy) = (br_mc, bs_mc) := hb_mc
                  rw [hb_mc'] at hmc_call
                  cases br_mc with
                  | none => simp at hmc_call
                  | some r_mc =>
                    cases r_mc with
                    | returned v_mc =>
                      dsimp only at hmc_call
                      split at hmc_call
                      · injection hmc_call with _ hsmc_eq
                        have hhl_val : heapLimit = 2952790016 := R11Shards.heapLimit_val
                        have hd_nw : npw.toNat + (8#64 * nw).toNat < 2 ^ 64 := by
                          rw [h8n_bv, hn_eq_cap]; omega
                        have hs_nw : pw0.toNat + (8#64 * nw).toNat < 2 ^ 64 := by
                          rw [h8n_bv, hn_eq_cap, ← hpw0_eq, ← hcapw_eq]; exact hp0_bnd
                        have hn_small : (8#64 * nw).toNat + 32 < 2 ^ 63 := by
                          rw [h8n_bv]; omega
                        have hdisj_mc : Disj (npw.toNat, (8#64 * nw).toNat) (pw0.toNat, (8#64 * nw).toNat) := by
                          rw [h8n_bv, hn_eq_cap]
                          by_cases hle_hp : pw0.toNat + 8 * capw.toNat ≤ npw.toNat
                          · exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
                          · have hge_hl : heapLimit ≤ pw0.toNat := by
                              rw [← hpw0_eq]
                              apply hp0_disj_heap
                              rw [← hnpw_eq_s, hpw0_eq, hcapw_eq]; omega
                            exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
                        have hspec := InitECandidate.Solver.Wave8GuestInv.SoloHtabSet.memcpy_body_spec
                          ent_mc npw pw0 (8#64 * nw) hd_nw hs_nw hn_small hdisj_mc
                          hent_mc_dst hent_mc_src hent_mc_n v_mc (congrArg Prod.fst hb_mc)
                        rw [hb_mc] at hspec; dsimp only at hspec
                        intro b hb_lt
                        have hb_lt' : b < (8#64 * nw).toNat := by rwa [h8n_bv]
                        have hcp_b := hspec.2.2.2.2.2.2.2.2.1 b hb_lt'
                        have hdst_add : (npw + BitVec.ofNat 64 b).toNat = npw.toNat + b := by
                          rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                        have hsrc_add : (pw0 + BitVec.ofNat 64 b).toNat = pw0.toNat + b := by
                          rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                        rw [hdst_add, hsrc_add] at hcp_b
                        have hsmc_mem : smc.memory = bs_mc.memory ∧ smc.be = bs_mc.be := by
                          rw [← hsmc_eq]; exact ⟨rfl, rfl⟩
                        unfold memB at hcp_b ⊢
                        rw [hsmc_mem.1, hsmc_mem.2]; exact hcp_b
                      · simp at hmc_call
                    | _ => simp at hmc_call
              -- Now `[l+0] := np` and `[l+16] := cap * 2` on `smc`:
              rw [evaluateHOLFiniteState_seq_line780] at hma_cont
              rcases hst0_out : evaluateHOLFiniteState smc
                (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np"))) with ⟨rst0, sst0⟩
              rw [hst0_out] at hma_cont
              cases rst0 with
              | some _ => dsimp only at hma_cont; simp at hma_cont
              | none =>
                dsimp only at hma_cont
                have hsmc_ma : smc.memaddrs = ordinaryDomain := heff_mc.memaddrs.trans hma_ma
                have hsmc_l : smc.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                  rw [hsmc_loc]; exact hma_l
                have hsmc_np : smc.locals.lookup (ofString "np") = some (.val (.word npw)) := by
                  rw [hsmc_loc]; exact hma_np
                have hsmc_dom0' : smc.memaddrs lw := by
                  have : smc.memaddrs (lw + 0#64) := by rw [hsmc_ma, ← hent_ma]; exact hdom_l0
                  simpa using this
                have hev_st0_d : @evalHOLExact 64 F _ smc.toExact (fun a => Classical.propDecidable (smc.memaddrs a))
                    (.op .add [.var .local (ofString "l"), .const 0#64]) =
                    some (.val (.word (lw + 0#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hsmc_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                have hev_st0_v : @evalHOLExact 64 F _ smc.toExact (fun a => Classical.propDecidable (smc.memaddrs a))
                    (.var .local (ofString "np")) = some (.val (.word npw)) := by
                  simp [evalHOLExact, hsmc_np]
                have hst0_eq : evaluateHOLFiniteState smc
                    (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np"))) =
                    (none, { smc with memory := fun a => if a = lw + 0#64 then .word npw else smc.memory a }) := by
                  rw [evaluateHOLFiniteState_store, hev_st0_d, hev_st0_v]; dsimp only
                  simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsmc_dom0', FUPDATE]
                obtain ⟨heff_st0, _⟩ := m23_bre_of_store_word (Rl := Rg) hsmc_ma hst0_out
                  (fun v hv => by rw [hev_st0_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                  (fun addr hdst _ => by
                    rw [hev_st0_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                    subst hd3
                    have : (lw + 0#64).toNat = lw.toNat := by simp
                    exact ⟨(lw.toNat, 24), by simp [Rg], by dsimp only; omega, by dsimp only; omega⟩)
                have hsst0_eq : sst0 = { smc with memory := fun a => if a = lw + 0#64 then .word npw else smc.memory a } := by
                  rw [hst0_out] at hst0_eq; exact (Prod.mk.inj hst0_eq).2
                have hsst0_ma : sst0.memaddrs = ordinaryDomain := heff_st0.memaddrs.trans hsmc_ma
                have hsst0_loc : sst0.locals = ma.locals := by rw [hsst0_eq]; exact hsmc_loc
                have hsst0_l : sst0.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                  rw [hsst0_loc]; exact hma_l
                have hsst0_c : sst0.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
                  rw [hsst0_loc]; exact hma_c
                have hsst0_dom16 : sst0.memaddrs (lw + 16#64) := by rw [hsst0_ma, ← hent_ma]; exact hdom_l16
                have hev_st16_d : @evalHOLExact 64 F _ sst0.toExact (fun a => Classical.propDecidable (sst0.memaddrs a))
                    (.op .add [.var .local (ofString "l"), .const 16#64]) =
                    some (.val (.word (lw + 16#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hsst0_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                have hev_st16_v : @evalHOLExact 64 F _ sst0.toExact (fun a => Classical.propDecidable (sst0.memaddrs a))
                    (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
                    some (.val (.word (capw * 2#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hsst0_c, valueIsWord, valueWord, panOpHOL]
                have hst16_eq : evaluateHOLFiniteState sst0
                    (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                      (.panop .mul [.var .local (ofString "cap"), .const 2#64])) =
                    (none, { sst0 with memory := fun a => if a = lw + 16#64 then .word (capw * 2#64) else sst0.memory a }) := by
                  rw [evaluateHOLFiniteState_store, hev_st16_d, hev_st16_v]; dsimp only
                  simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsst0_dom16, FUPDATE]
                obtain ⟨heff_st16, _⟩ := m23_bre_of_store_word (Rl := Rg) hsst0_ma hma_cont
                  (fun v hv => by rw [hev_st16_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                  (fun addr hdst _ => by
                    rw [hev_st16_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                    subst hd3
                    have h16_nat : (lw + 16#64).toNat = lw.toNat + 16 := bv_add_off_nat_local lw 16 hlw_lt_he (by omega)
                    exact ⟨(lw.toNat, 24), by simp [Rg], by dsimp only; omega, by dsimp only; omega⟩)
                have hsg1_eq : sg1 = { sst0 with memory := fun a => if a = lw + 16#64 then .word (capw * 2#64) else sst0.memory a } := by
                  rw [hma_cont] at hst16_eq; exact (Prod.mk.inj hst16_eq).2
                have hsi_ma : si.memaddrs = ordinaryDomain := by
                  rw [← hsi_eq]; exact heff_st16.memaddrs.trans hsst0_ma
                have hsi_l : si.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                  rw [← hsi_eq]; dsimp only
                  rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq]; exact hsst0_l
                have hsi_n : si.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                  rw [← hsi_eq]; dsimp only
                  rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq, hsst0_loc]; exact hma_n
                have hsi_e : si.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
                  rw [← hsi_eq]; dsimp only
                  rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq, hsst0_loc]; exact hma_e
                have hsi_dom8 : si.memaddrs (lw + 8#64) := by rw [hsi_ma, ← hent_ma]; exact hdom_l8
                have hsi_dom0 : si.memaddrs (lw + 0#64) := by rw [hsi_ma, ← hent_ma]; exact hdom_l0
                dsimp only [tailProg] at hout_e2
                rw [evaluateHOLFiniteState_seq_line780] at hout_e2
                have hev_st8_d : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                    (.op .add [.var .local (ofString "l"), .const 8#64]) =
                    some (.val (.word (lw + 8#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hsi_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                have hev_st8_v : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                    (.op .add [.var .local (ofString "n"), .const 1#64]) =
                    some (.val (.word (nw + 1#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hsi_n, valueIsWord, valueWord, wordOpHOL, wordOp]
                have hst8_eq : evaluateHOLFiniteState si
                    (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                      (.op .add [.var .local (ofString "n"), .const 1#64])) =
                    (none, { si with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else si.memory a }) := by
                  rw [evaluateHOLFiniteState_store, hev_st8_d, hev_st8_v]; dsimp only
                  simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsi_dom8, FUPDATE]
                rw [hst8_eq] at hout_e2; dsimp only at hout_e2
                obtain ⟨heff_st8, _⟩ := m23_bre_of_store_word (Rl := Rg) hsi_ma hst8_eq
                  (fun v hv => by rw [hev_st8_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                  (fun addr hdst _ => by
                    rw [hev_st8_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                    subst hd3
                    have h8_nat : (lw + 8#64).toNat = lw.toNat + 8 := bv_add_off_nat_local lw 8 hlw_lt_he (by omega)
                    exact ⟨(lw.toNat, 24), by simp [Rg], by dsimp only; omega, by dsimp only; omega⟩)
                let st8 : PanSemStateFiniteExact 64 F :=
                  { si with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else si.memory a }
                have h8_nat : (lw + 8#64).toNat = lw.toNat + 8 := bv_add_off_nat_local lw 8 hlw_lt_he (by omega)
                have h16_nat : (lw + 16#64).toNat = lw.toNat + 16 := bv_add_off_nat_local lw 16 hlw_lt_he (by omega)
                have h0_nat : (lw + 0#64).toNat = lw.toNat := by simp
                have hne_0_16 : lw + 0#64 ≠ lw + 16#64 := fun h => by have := congrArg BitVec.toNat h; omega
                have hne_0_8 : lw + 0#64 ≠ lw + 8#64 := fun h => by have := congrArg BitVec.toNat h; omega
                have hne_16_8 : lw + 16#64 ≠ lw + 8#64 := fun h => by have := congrArg BitVec.toNat h; omega
                have hst8_m0 : st8.memory (lw + 0#64) = .word npw := by
                  dsimp [st8]; rw [if_neg hne_0_8, ← hsi_eq]; dsimp only
                  rw [hsg1_eq]; dsimp only; rw [if_neg hne_0_16, hsst0_eq]; simp
                have hst8_m8 : st8.memory (lw + 8#64) = .word (nw + 1#64) := by dsimp [st8]; simp
                have hst8_m16 : st8.memory (lw + 16#64) = .word (capw * 2#64) := by
                  dsimp [st8]; rw [if_neg hne_16_8, ← hsi_eq]; dsimp only; rw [hsg1_eq]; simp
                have hst8_dom0 : st8.memaddrs (lw + 0#64) := hsi_dom0
                have hev_ret : @evalHOLExact 64 F _ st8.toExact (fun a => Classical.propDecidable (st8.memaddrs a))
                    (.op .add
                      [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                       .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
                    some (.val (.word (npw + nw * 8#64))) := by
                  have hst8_l : st8.locals.lookup (ofString "l") = some (.val (.word lw)) := hsi_l
                  have hst8_n : st8.locals.lookup (ofString "n") = some (.val (.word nw)) := hsi_n
                  have hst8_e : st8.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := hsi_e
                  simp only [evalHOLExact, evalListHOLExact, hst8_l, hst8_n, hst8_e,
                    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                    List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
                    memLoadHOLExact, isWfShapeExactHOL, hst8_dom0, hst8_m0, ↓reduceIte]
                  simp
                rw [evaluateHOLFiniteState_return, hev_ret] at hout_e2; dsimp only at hout_e2
                rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])] at hout_e2
                injection hout_e2 with hvb_eq hso2_eq
                injection hvb_eq with hvb_ret
                injection hvb_ret with hvb_val
                let ew := npw + nw * 8#64
                have heff_si : ByteRegionEffect ma si Rg := by
                  rw [← hsi_eq]
                  exact ((heff_mc.trans heff_st0).trans heff_st16).with_locals_clock _ sg1.clock
                have hsb_mem_eq : sb = { st8 with locals := sb.locals, clock := sb.clock } := by
                  rw [← hsb_eq, ← hso2_eq]; rfl
                have heff_sb : ByteRegionEffect ma sb Rg := by
                  rw [hsb_mem_eq]
                  exact (heff_si.trans heff_st8).with_locals_clock sb.locals sb.clock
                have hAsb : ArenaReady sb := by
                  refine ⟨⟨heff_sb.code.trans hma_AR.1.code, heff_sb.memaddrs.trans hma_AR.1.memaddrs,
                    heff_sb.shMemaddrs.trans hma_AR.1.shMemaddrs, heff_sb.baseAddr.trans hma_AR.1.baseAddr⟩, ?_⟩
                  simpa only [ArenaOK, globN, GlobalsWord, GlobalWord, heff_sb.globals] using hma_AR.2
                have hn8_bv : (nw * 8#64).toNat = 8 * nw.toNat := by
                  rw [BitVec.mul_comm, h8n_bv]
                have hhl_val : heapLimit = 2952790016 := R11Shards.heapLimit_val
                have hhe_val : heapEnd = 33806089704 := R11Shards.heapEnd_val
                have hew_toNat : ew.toNat = npw.toNat + 8 * nw.toNat := by
                  have hlt : npw.toNat + 8 * nw.toNat < 2 ^ 64 := by rw [hn_eq_cap]; omega
                  rw [BitVec.toNat_add, hn8_bv, Nat.mod_eq_of_lt hlt]
                have hew_al : ew.toNat % 8 = 0 := by rw [hew_toNat]; omega
                have hew_dom : sb.memaddrs ew := by
                  rw [heff_sb.memaddrs, hma_ma, Wave8Contracts.M08.ordinaryDomain_iff]
                  have hnp_ge : sourceBase ≤ npw.toNat := by rw [hnpw_eq_s]; exact hAs.2.1
                  have hcp_pos : 1 ≤ capw.toNat := by rw [← hcapw_eq]; exact hlst0.1
                  exact ⟨hew_al, by rw [hew_toNat]; omega, by rw [hew_toNat, hn_eq_cap]; omega⟩
                have hsb_mem_fn : sb.memory = st8.memory := by rw [hsb_mem_eq]
                have hsb_m0 : memW sb lw.toNat = npw.toNat := by
                  unfold memW; rw [← hl0_bv, hsb_mem_fn, hst8_m0]
                have hnp1_toNat : (nw + 1#64).toNat = nw.toNat + 1 := by
                  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
                  rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by rw [hn_eq_cap]; omega)]
                have hsb_m8 : memW sb (lw.toNat + 8) = nw.toNat + 1 := by
                  unfold memW; rw [← hl8_bv, hsb_mem_fn, hst8_m8]; exact hnp1_toNat
                have hcap2_toNat : (capw * 2#64).toNat = 2 * capw.toNat := by
                  have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
                  rw [BitVec.toNat_mul, h2, Nat.mod_eq_of_lt (by omega)]; omega
                have hsb_m16 : memW sb (lw.toNat + 16) = 2 * capw.toNat := by
                  unfold memW; rw [← hl16_bv, hsb_mem_fn, hst8_m16]; exact hcap2_toNat
                -- Also show the three header stores `[l+0]`, `[l+16]`, `[l+8]` did not touch `[npw, npw + 8*nw)`:
                have hsb_slots : ∀ i < nw.toNat, memW sb (npw.toNat + 8 * i) = memW ma (pw0.toNat + 8 * i) := by
                  have hst_eff : ByteRegionEffect smc sb [(lw.toNat, 24)] := by
                    have h0' : ByteRegionEffect smc sst0 [(lw.toNat, 24)] :=
                      (m23_bre_of_store_word (Rl := [(lw.toNat, 24)]) hsmc_ma hst0_out
                        (fun v hv => by rw [hev_st0_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                        (fun addr hdst _ => by
                          rw [hev_st0_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                          subst hd3; exact ⟨(lw.toNat, 24), by simp, by dsimp only; omega, by dsimp only; omega⟩)).1
                    have h16' : ByteRegionEffect sst0 sg1 [(lw.toNat, 24)] :=
                      (m23_bre_of_store_word (Rl := [(lw.toNat, 24)]) hsst0_ma hma_cont
                        (fun v hv => by rw [hev_st16_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                        (fun addr hdst _ => by
                          rw [hev_st16_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                          subst hd3; exact ⟨(lw.toNat, 24), by simp, by dsimp only; omega, by dsimp only; omega⟩)).1
                    have hsi' : ByteRegionEffect smc si [(lw.toNat, 24)] := by
                      rw [← hsi_eq]; exact (h0'.trans h16').with_locals_clock _ sg1.clock
                    have h8' : ByteRegionEffect si st8 [(lw.toNat, 24)] :=
                      (m23_bre_of_store_word (Rl := [(lw.toNat, 24)]) hsi_ma hst8_eq
                        (fun v hv => by rw [hev_st8_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                        (fun addr hdst _ => by
                          rw [hev_st8_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                          subst hd3; exact ⟨(lw.toNat, 24), by simp, by dsimp only; omega, by dsimp only; omega⟩)).1
                    rw [hsb_mem_eq]; exact (hsi'.trans h8').with_locals_clock sb.locals sb.clock
                  have hdisj_lw_np : Disj (lw.toNat, 24) (npw.toNat, 16 * capw.toNat) := by
                    by_cases hle_hp : lw.toNat + 24 ≤ npw.toNat
                    · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
                    · have hge_hl : heapLimit ≤ lw.toNat := by
                        apply hlw_disj_heap; rw [← hnpw_eq_s]; omega
                      exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
                  intro i hi
                  have hsb_smc : memW sb (npw.toNat + 8 * i) = memW smc (npw.toNat + 8 * i) := by
                    unfold memW
                    have ha : npw.toNat + 8 * i < 2 ^ 64 := by rw [hn_eq_cap] at hi; omega
                    have hbit : (BitVec.ofNat 64 (npw.toNat + 8 * i)).toNat = npw.toNat + 8 * i :=
                      Nat.mod_eq_of_lt ha
                    rw [hst_eff.cell_frame (BitVec.ofNat 64 (npw.toNat + 8 * i))]
                    intro x hx; simp only [List.mem_singleton] at hx; subst hx; rw [hbit]
                    exact not_cellHits_of_disj_aligned
                      (i := (npw.toNat, 16 * capw.toNat)) (by omega) hlw_words.1
                      (Nat.le_add_right _ _) (by rw [hn_eq_cap] at hi; omega)
                      (R11Shards.Disj.symm hdisj_lw_np)
                  rw [hsb_smc]
                  exact memW_slot_copied heff_mc.be (by rwa [← hpw0_eq]) hnpw8
                    (by rw [hn_eq_cap, ← hpw0_eq, ← hcapw_eq]; exact hp0_bnd)
                    (by rw [hn_eq_cap]; omega) hi hmc_copy
                exact ⟨ma, npw, ew, hvb_val.symm, hma_AR, hma_m, hma_be,
                  hma_ma.trans hent_ma.symm, hnpw_eq_s, hnpw8,
                  by rw [hma_hp, hcapw_eq], hma_gk,
                  by rw [hew_toNat, hnw_eq], hew_al, hew_dom, hAsb,
                  by rw [hcapw_eq]; exact heff_sb,
                  hsb_m0, by rw [hsb_m8, hnw_eq], by rw [hsb_m16, hcapw_eq],
                  by rw [hnw_eq, hpw0_eq]; exact hsb_slots⟩
    · -- NO-GROW BRANCH (`nw.toNat < capw.toNat`)
      left
      refine ⟨by rw [hnw_eq, hcapw_eq]; omega, ?_⟩
      rw [if_neg hgrow_cond, if_pos (by decide : (0#64 : BitVec 64) = 0), evaluateHOLFiniteState_skip] at hite_out
      injection hite_out with _ hsi_eq
      subst hsi_eq
      dsimp only [tailProg] at hout_e2
      rw [evaluateHOLFiniteState_seq_line780] at hout_e2
      have he2_ma : e2.memaddrs = ordinaryDomain := hent_ma
      have he2_dom8 : e2.memaddrs (lw + 8#64) := hdom_l8
      have he2_dom0 : e2.memaddrs (lw + 0#64) := hdom_l0
      have hev_st8_d : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
          (.op .add [.var .local (ofString "l"), .const 8#64]) =
          some (.val (.word (lw + 8#64))) := by
        simp [evalHOLExact, evalListHOLExact, he2_l, valueIsWord, valueWord, wordOpHOL, wordOp]
      have hev_st8_v : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
          (.op .add [.var .local (ofString "n"), .const 1#64]) =
          some (.val (.word (nw + 1#64))) := by
        simp [evalHOLExact, evalListHOLExact, he2_n, valueIsWord, valueWord, wordOpHOL, wordOp]
      have hst8_eq : evaluateHOLFiniteState e2
          (.store (.op .add [.var .local (ofString "l"), .const 8#64])
            (.op .add [.var .local (ofString "n"), .const 1#64])) =
          (none, { e2 with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else e2.memory a }) := by
        rw [evaluateHOLFiniteState_store, hev_st8_d, hev_st8_v]; dsimp only
        simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, he2_dom8, FUPDATE]
      rw [hst8_eq] at hout_e2; dsimp only at hout_e2
      have h8_nat : (lw + 8#64).toNat = lw.toNat + 8 := bv_add_off_nat_local lw 8 hlw_lt_he (by omega)
      have h16_nat : (lw + 16#64).toNat = lw.toNat + 16 := bv_add_off_nat_local lw 16 hlw_lt_he (by omega)
      have h0_nat : (lw + 0#64).toNat = lw.toNat := by simp
      obtain ⟨heff_st8, _⟩ := m23_bre_of_store_word (Rl := [(lw.toNat, 24)]) he2_ma hst8_eq
        (fun v hv => by rw [hev_st8_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
        (fun addr hdst _ => by
          rw [hev_st8_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
          subst hd3; exact ⟨(lw.toNat, 24), by simp, by dsimp only; omega, by dsimp only; omega⟩)
      let st8 : PanSemStateFiniteExact 64 F :=
        { e2 with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else e2.memory a }
      have hne_0_8 : lw + 0#64 ≠ lw + 8#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_16_8 : lw + 16#64 ≠ lw + 8#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hst8_m0 : st8.memory (lw + 0#64) = .word pw0 := by dsimp [st8]; rw [if_neg hne_0_8]; exact hm_l0
      have hst8_m8 : st8.memory (lw + 8#64) = .word (nw + 1#64) := by dsimp [st8]; simp
      have hst8_m16 : st8.memory (lw + 16#64) = .word capw := by dsimp [st8]; rw [if_neg hne_16_8]; exact hm_l16
      have hst8_dom0 : st8.memaddrs (lw + 0#64) := he2_dom0
      have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
      have hev_ret : @evalHOLExact 64 F _ st8.toExact (fun a => Classical.propDecidable (st8.memaddrs a))
          (.op .add
            [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
             .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
          some (.val (.word (pw0 + nw * 8#64))) := by
        have hst8_l : st8.locals.lookup (ofString "l") = some (.val (.word lw)) := he2_l
        have hst8_n : st8.locals.lookup (ofString "n") = some (.val (.word nw)) := he2_n
        have hst8_e : st8.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := he2_e
        simp only [evalHOLExact, evalListHOLExact, hst8_l, hst8_n, hst8_e,
          valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
          List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
          memLoadHOLExact, isWfShapeExactHOL, hst8_dom0, hst8_m0, ↓reduceIte]
        simp
      rw [evaluateHOLFiniteState_return, hev_ret] at hout_e2; dsimp only at hout_e2
      rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])] at hout_e2
      injection hout_e2 with hvb_eq hso2_eq
      injection hvb_eq with hvb_ret
      injection hvb_ret with hvb_val
      let ew := pw0 + nw * 8#64
      have hsb_mem_eq : sb = { st8 with locals := sb.locals, clock := sb.clock } := by
        rw [← hsb_eq, ← hso2_eq]; rfl
      have heff_e2_sb : ByteRegionEffect e2 sb [(lw.toNat, 24)] := by
        rw [hsb_mem_eq]; exact heff_st8.with_locals_clock sb.locals sb.clock
      have heff_ent_e2 : ByteRegionEffect ent e2 [(lw.toNat, 24)] :=
        (ByteRegionEffect.refl ent _).with_locals_clock e2.locals e2.clock
      have heff_sb : ByteRegionEffect ent sb [(lw.toNat, 24)] := heff_ent_e2.trans heff_e2_sb
      have hAsb : ArenaReady sb := by
        refine ⟨⟨heff_sb.code.trans hAs.1.code, heff_sb.memaddrs.trans hAs.1.memaddrs,
          heff_sb.shMemaddrs.trans hAs.1.shMemaddrs, heff_sb.baseAddr.trans hAs.1.baseAddr⟩, ?_⟩
        simpa only [ArenaOK, globN, GlobalsWord, GlobalWord, heff_sb.globals] using hAs.2
      have hcapw_lt32 : capw.toNat < 2 ^ 32 := by rwa [← hcapw_eq]
      have hn8_bv : (nw * 8#64).toNat = 8 * nw.toNat := by
        have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
        rw [BitVec.toNat_mul, h8, Nat.mod_eq_of_lt (by omega)]; omega
      have hew_toNat : ew.toNat = pw0.toNat + 8 * nw.toNat := by
        have hlt : pw0.toNat + 8 * nw.toNat < 2 ^ 64 := by
          rw [← hpw0_eq]; have := hp0_bnd; rw [hcapw_eq] at this; omega
        rw [BitVec.toNat_add, hn8_bv, Nat.mod_eq_of_lt hlt]
      have hew_al : ew.toNat % 8 = 0 := by rw [hew_toNat, ← hpw0_eq]; omega
      have hew_dom : ent.memaddrs ew := by
        obtain ⟨_, hd, _⟩ := hp0_words.2.2 nw.toNat (by rw [hcapw_eq]; omega)
        have hew_bv : BitVec.ofNat 64 (memW ent lw.toNat + 8 * nw.toNat) = ew := by
          apply BitVec.eq_of_toNat_eq
          rw [hew_toNat, hpw0_eq, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by rw [← hpw0_eq]; have := hp0_bnd; rw [hcapw_eq] at this; omega)]
        rwa [hew_bv] at hd
      have hsb_mem_fn : sb.memory = st8.memory := by rw [hsb_mem_eq]
      have hsb_m0 : memW sb lw.toNat = pw0.toNat := by
        unfold memW; rw [← hl0_bv, hsb_mem_fn, hst8_m0]
      have hnp1_toNat : (nw + 1#64).toNat = nw.toNat + 1 := by
        have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
        rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
      have hsb_m8 : memW sb (lw.toNat + 8) = nw.toNat + 1 := by
        unfold memW; rw [← hl8_bv, hsb_mem_fn, hst8_m8]; exact hnp1_toNat
      have hsb_m16 : memW sb (lw.toNat + 16) = capw.toNat := by
        unfold memW; rw [← hl16_bv, hsb_mem_fn, hst8_m16]
      have hsb_slots : ∀ i < nw.toNat, memW sb (pw0.toNat + 8 * i) = memW ent (pw0.toNat + 8 * i) := by
        intro i hi
        unfold memW
        have ha : pw0.toNat + 8 * i < 2 ^ 64 := by
          rw [← hpw0_eq]; have := hp0_bnd; rw [hcapw_eq] at this; omega
        have hbit : (BitVec.ofNat 64 (pw0.toNat + 8 * i)).toNat = pw0.toNat + 8 * i :=
          Nat.mod_eq_of_lt ha
        rw [heff_sb.cell_frame (BitVec.ofNat 64 (pw0.toNat + 8 * i))]
        intro x hx; simp only [List.mem_singleton] at hx; subst hx; rw [hbit]
        have hp0_al' : pw0.toNat % 8 = 0 := by rwa [← hpw0_eq]
        have hdisj' : Disj (lw.toNat, 24) (pw0.toNat, 8 * capw.toNat) := by
          rwa [← hpw0_eq, ← hcapw_eq]
        exact not_cellHits_of_disj_aligned
          (i := (pw0.toNat, 8 * capw.toNat)) (by omega) hlw_words.1
          (Nat.le_add_right _ _) (by omega) (R11Shards.Disj.symm hdisj')
      exact ⟨ew, hvb_val.symm, by rw [hew_toNat, hpw0_eq, hnw_eq], hew_al, hew_dom, hAsb,
        heff_sb, by rw [hsb_m0, hpw0_eq], by rw [hsb_m8, hnw_eq], by rw [hsb_m16, hcapw_eq],
        by rw [hpw0_eq, hnw_eq]; exact hsb_slots⟩

private theorem disj_fresh_heap_of_evmInv {F : Type}
    {s : PanSemStateFiniteExact 64 F} {x : Ivl} {hp1 : Nat}
    (hInv : EvmInv s)
    (hhp1_lim : hp1 ≤ heapLimit)
    (hx_in : x = (0, 0) ∨ Inside x (globN s "heap_ptr") hp1) :
    (∀ t, ∀ S0, TablesTyped s S0 → t ∈ S0 → ∀ i ∈ htabFootprint s t, Disj x i) ∧
    (∀ j ∈ fixedObjects s, Disj x j) ∧
    (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj x o) ∧
    (∀ S0 Nd0, TriesTypedWith s S0 Nd0 → ∀ j ∈ nodeExtents s Nd0, Disj x j) ∧
    (∀ ec ∈ evmChain s, Disj x (memW s (ec.1 + 112), 176)) := by
  obtain ⟨hAs, S, hW, _, _, _, hFW_all, _, _, _, _, _⟩ := hInv
  have hdisj_alloc : ∀ i : Ivl, i.2 = 0 ∨ Allocated s i → Disj x i := by
    intro i hi
    rcases hx_in with rfl | ⟨hx1, hx2⟩
    · exact Or.inl rfl
    · rcases hi with hz | (⟨_, hi2⟩ | ⟨hi1, _⟩)
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr (Or.inr (by omega)))
      · have hfr := hAs.2.2.2.1; have hgap := hAs.2.2.2.2.1
        rw [R11Shards.heapLimit_val] at hhp1_lim; rw [R11Shards.scratchStart_val] at hfr
        exact Or.inr (Or.inr (Or.inl (by omega)))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t S0 hT ht i hi
    exact hdisj_alloc i (Or.inr ((hT.2.1 t ht).2 i hi).1)
  · intro j hj
    rcases hW.2.2.1.1 j hj with hz | ⟨hal, _⟩
    · exact hdisj_alloc j (Or.inl hz)
    · exact hdisj_alloc j (Or.inr hal)
  · intro ec hec o ho
    have hFW := hFW_all ec hec
    unfold frameObjects at ho
    rcases List.mem_append.1 ho with h7 | hlog
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h7
      rcases h7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hdisj_alloc _ (Or.inr (Or.inr (hFW.1 _ (by simp)).1))
      · exact hdisj_alloc _ (Or.inr (Or.inr (hFW.1 _ (by simp)).1))
      · exact hdisj_alloc _ (Or.inr (Or.inr (hFW.1 _ (by simp)).1))
      · have hfm1 : scratchStart ≤ memW s (ec.1 + 24) := (hFW.2.1).1
        rcases hx_in with rfl | ⟨hx1, hx2⟩
        · exact Or.inl rfl
        · rw [R11Shards.heapLimit_val] at hhp1_lim; rw [R11Shards.scratchStart_val] at hfm1
          exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact hdisj_alloc _ (Or.inr (Or.inr (hFW.1 _ (by simp)).1))
      · exact hdisj_alloc _ (Or.inr hFW.2.2.2.2.2.2.2.2.2.2.2.2.1)
      · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨h216, _⟩ | ⟨hin_ret, _⟩
        · unfold frameRet; rw [if_pos h216]; exact hdisj_alloc _ (Or.inl rfl)
        · exact hdisj_alloc _ (Or.inr (Or.inl hin_ret))
    · unfold frameLogObjects at hlog; dsimp only at hlog
      obtain ⟨idx, hidx, ho_own⟩ := List.mem_flatMap.1 hlog
      rw [List.mem_range] at hidx
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
      · obtain ⟨he88_in, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
        have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
        rw [R11Shards.scratchStart_val] at h1; omega
      · have hle := (hent idx hidx).2
        have ho_rec := (List.mem_filter.1 ho_own).1
        unfold logRecordIvls at ho_rec
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho_rec
        rcases ho_rec with rfl | rfl | rfl | rfl
        · exact hdisj_alloc _ (Or.inr (Or.inl hle.2.1))
        · exact hdisj_alloc _ (Or.inr (Or.inl hle.2.2.2.2.1))
        · exact hdisj_alloc _ (Or.inr (Or.inl hle.2.2.2.2.2.1))
        · exact hdisj_alloc _ (Or.inr (Or.inl hle.2.2.2.2.2.2))
  · intro S0 Nd0 hTr j hj
    unfold nodeExtents at hj
    obtain ⟨n, hn, hjn⟩ := List.mem_flatMap.1 hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hjn
    rcases hjn with rfl | rfl
    · exact hdisj_alloc _ (Or.inr (hTr.1.1 n hn).2.1)
    · unfold nodePath
      split
      · rename_i hcond
        rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
        · exact absurd h0 hcond.2
        · exact hdisj_alloc _ (Or.inr hal)
      · exact hdisj_alloc _ (Or.inl rfl)
  · intro ec hec
    exact hdisj_alloc _ (Or.inr (hFW_all ec hec).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

private theorem logEntryOK_congr_of_bre {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {log : Nat}
    (heff : ByteRegionEffect s post Rl)
    (hAs : ArenaReady s)
    (hRl_8 : ∀ x ∈ Rl, x.1 % 8 = 0)
    (hdisj : ∀ x ∈ Rl, Disj x (log, 40))
    (hle : LogEntryOK s log) :
    LogEntryOK post log ∧ logOwnedIvls post log = logOwnedIvls s log := by
  have hlog8 : log % 8 = 0 := hle.1.1
  have hl_in2 : log + 40 ≤ globN s "heap_ptr" := hle.2.1.2
  have hhl := hAs.2.2.1
  rw [R11Shards.heapLimit_val] at hhl
  have hlbnd : log + 40 ≤ 2 ^ 64 := by omega
  have hmw : ∀ k : Nat, k % 8 = 0 → k + 8 ≤ 40 → memW post (log + k) = memW s (log + k) := by
    intro k hk8 hk
    unfold memW
    have ha : log + k < 2 ^ 64 := by omega
    have hbit : (BitVec.ofNat 64 (log + k)).toNat = log + k := Nat.mod_eq_of_lt ha
    rw [heff.cell_frame (BitVec.ofNat 64 (log + k))]
    intro x hx; rw [hbit]
    exact not_cellHits_of_disj_aligned (i := (log, 40))
      (by omega) (hRl_8 x hx) (Nat.le_add_right log k) (Nat.add_le_add_left hk log)
      (R11Shards.Disj.symm (hdisj x hx))
  have hm0 : memW post log = memW s log := by simpa using hmw 0 (by omega) (by omega)
  have hm8 := hmw 8 (by omega) (by omega)
  have hm16 := hmw 16 (by omega) (by omega)
  have hm24 := hmw 24 (by omega) (by omega)
  have hm32 := hmw 32 (by omega) (by omega)
  have hhp_eq : globN post "heap_ptr" = globN s "heap_ptr" := by unfold globN; rw [heff.globals]
  have hsys_eq : globN post "vm_system_address" = globN s "vm_system_address" := by
    unfold globN; rw [heff.globals]
  refine ⟨?_, ?_⟩
  · unfold LogEntryOK at hle ⊢
    rw [hm0, hm8, hm16, hm24, hm32, hhp_eq]
    exact ⟨(wordsOK_congr_dom heff.memaddrs).2 hle.1, hle.2⟩
  · unfold logOwnedIvls logRecordIvls
    rw [hm0, hm8, hm16, hm24, hm32, hsys_eq]

private theorem log_append_head_returned_spec {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (evw logw : BitVec 64)
    (hInv : EvmInv s)
    (S Nd_at : List Nat) (hInvAt_s : EvmInvAt s S)
    (hTr_at_s : TriesTypedWith s S Nd_at)
    (hAT_at_s : ∀ o ∈ ((evmChain s).map (frameObjects s)).flatten,
      ∀ j ∈ nodeExtents s Nd_at, Disj o j)
    (hev_eq : evw.toNat = globN s "ev")
    (hlogs_lt : memW s (memW s (globN s "ev" + 88) + 8) + 1 < 2 ^ 28)
    (hlog_ok : LogEntryOK s logw.toNat)
    (hlog_disj : ∀ x ∈ logOwnedIvls s logw.toNat,
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj x i) ∧
      (∀ j ∈ fixedObjects s, Disj x j) ∧
      (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj x o) ∧
      (∀ j ∈ nodeExtents s Nd_at, Disj x j) ∧
      (∀ ec ∈ evmChain s, Disj x (memW s (ec.1 + 112), 176)))
    (hlog_pw : (logOwnedIvls s logw.toNat).Pairwise Disj)
    (hlog_disj_l0 : Disj (memW s (globN s "ev" + 88), 24) (logw.toNat, 40))
    (hlog_disj_fl : Disj (frameLogs s (globN s "ev", globN s "cur_cont")) (logw.toNat, 40))
    (hcall : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])).1 = none)
    (heval_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "ev")) = some (.val (.word evw)))
    (heval_log : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "log")) = some (.val (.word logw))) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])
    EvmStepCC ["heap_ptr"] s out.2 ∧ out.2.locals = s.locals := by
  dsimp only
  have hAs : ArenaReady s := hInv.1
  have hs_code : s.code = originalRuntimeCode := hAs.1.code
  have hs_ma : s.memaddrs = ordinaryDomain := hAs.1.memaddrs
  rw [evaluateHOLFiniteState_call] at hcall ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .global (ofString "ev"), .var .local (ofString "log")] =
      some [.val (.word evw), .val (.word logw)] := by
    simp [evalListHOLFinite, evalListHOLExact, heval_ev, heval_log]
  have hlook := pan_two_word_lookup s.code.lookup (ofString "log_append")
    (ofString "e") (ofString "log")
    (sourceFnBody Guest.Software.guestFn_log_append) evw logw
    (by decide)
    (by rw [hs_code]; exact lookup_log_append_local)
  rw [hargs] at hcall ⊢; dsimp only at hcall ⊢
  rw [hlook] at hcall ⊢; dsimp only at hcall ⊢
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hcall; simp at hcall
  · rw [if_neg hclk0] at hcall ⊢
    let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      (HolFiniteMapExact.empty.update (ofString "e", ValueHOL.val (.word evw))).update
        (ofString "log", ValueHOL.val (.word logw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAs
    have hent_code : ent.code = originalRuntimeCode := hs_code
    have hent_ma : ent.memaddrs = ordinaryDomain := hs_ma
    have hent_e : ent.locals.lookup (ofString "e") = some (.val (.word evw)) := by
      have hne : ofString "log" ≠ ofString "e" := by decide
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
    have hent_log : ent.locals.lookup (ofString "log") = some (.val (.word logw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState
        (callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "e", ValueHOL.val (.word evw))).update
            (ofString "log", ValueHOL.val (.word logw))))
        (sourceFnBody Guest.Software.guestFn_log_append) with ⟨br, bs⟩
    rw [hb] at hcall
    have hb_ent : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_log_append) = (br, bs) := hb
    cases br with
    | none => simp at hcall
    | some r =>
      cases r with
      | returned rv =>
        dsimp only at hcall ⊢
        split at hcall
        · rename_i hsh_rv
          rw [if_pos hsh_rv]
          refine ⟨?_, rfl⟩
          -- Unfold `guestFn_log_append` body at `ent`:
          have hb := hb_ent
          have hbody_eq : sourceFnBody Guest.Software.guestFn_log_append =
              .decCall (ofString "slot") .one (ofString "lst_push")
                [.load .one (.op .add [.var .local (ofString "e"), .const 88#64]), .const 8#64]
                (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                      (.return (.const 0#64))) := rfl
          rw [hbody_eq, evaluateHOLFiniteState_decCall_fixClockRewrite] at hb
          -- Evaluate `*(e + 88)`:
          have hW := hInvAt_s.1
          have hFW_all := hInvAt_s.2.2.2.2.1
          have hFO_pw := hInvAt_s.2.2.2.2.2.2.2.1
          set e0 := globN s "ev"
          set c0 := globN s "cur_cont"
          have hhead_mem : (e0, c0) ∈ evmChain s := List.mem_cons_self
          have hhead_FW := hFW_all (e0, c0) hhead_mem
          have he0_words : WordsOK s (e0, 280) := (hhead_FW.1 (e0, 280) (by simp)).2
          obtain ⟨lw, hd_e88, hm_e88⟩ := he0_words.2.2 11 (by omega)
          have hev_lt_he : evw.toNat < heapEnd := by
            obtain ⟨_, hd_e0, _⟩ := he0_words.2.2 0 (by omega)
            rw [Nat.add_zero] at hd_e0
            rw [hs_ma, Wave8Contracts.M08.ordinaryDomain_iff] at hd_e0
            rw [← hev_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt evw.isLt] at hd_e0
            exact hd_e0.2.2
          have he88_bv : evw + 88#64 = BitVec.ofNat 64 (e0 + 88) := by
            apply BitVec.eq_of_toNat_eq
            rw [bv_add_off_nat_local evw 88 hev_lt_he (by omega), hev_eq,
                BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [R11Shards.heapEnd_val] at hev_lt_he; omega)]
          have hent_dom88 : ent.memaddrs (evw + 88#64) := by rw [he88_bv]; simpa [ent, callEntryStateHOLFinite] using hd_e88
          have hent_m88 : ent.memory (evw + 88#64) = .word lw := by rw [he88_bv]; simpa [ent, callEntryStateHOLFinite] using hm_e88
          have hlw_eq : lw.toNat = memW s (e0 + 88) := by
            unfold memW; rw [← he88_bv]; dsimp only [ent, callEntryStateHOLFinite] at hent_m88; rw [hent_m88]
          have hz_88 : (88#64 : BitVec 64) + 0 = 88#64 := rfl
          have hev_arg1 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
              (.load .one (.op .add [.var .local (ofString "e"), .const 88#64])) =
              some (.val (.word lw)) := by
            simp only [evalHOLExact, evalListHOLExact, hent_e, valueIsWord, valueWord,
              wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_88,
              memLoadHOLExact, isWfShapeExactHOL, hent_dom88, hent_m88, ↓reduceIte]
          have hargs_lp : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
              [.load .one (.op .add [.var .local (ofString "e"), .const 88#64]), .const 8#64] =
              some [.val (.word lw), .val (.word 8#64)] := by
            unfold evalListHOLFinite evalListHOLExact
            rw [hev_arg1]; rfl
          have hlook_lp := pan_two_word_lookup ent.code.lookup (ofString "lst_push")
            (ofString "l") (ofString "esz")
            (sourceFnBody Guest.Software.guestFn_lst_push) lw 8#64
            (by decide)
            (by rw [hent_code]; exact lookup_lst_push_local)
          rw [hargs_lp] at hb; dsimp only at hb
          rw [hlook_lp] at hb; dsimp only at hb
          by_cases hclk_ent : ent.clock = 0
          · rw [if_pos hclk_ent] at hb; simp at hb
          · rw [if_neg hclk_ent] at hb
            let cmap_lp : HolFiniteMapExact MlS (ValueHOL 64) :=
              (HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
                (ofString "esz", ValueHOL.val (.word 8#64))
            let ent_lp := callEntryStateHOLFinite ent cmap_lp
            have hent_lp_AR : ArenaReady ent_lp := (arenaReady_with_locals ent cmap_lp (ent.clock - 1)).2 hent_AR
            have hent_lp_l : ent_lp.locals.lookup (ofString "l") = some (.val (.word lw)) := by
              have hne : ofString "esz" ≠ ofString "l" := by decide
              simp [ent_lp, cmap_lp, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
            have hent_lp_e : ent_lp.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
              simp [ent_lp, cmap_lp, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            rcases hlp_run : evaluateHOLFiniteState
                (callEntryStateHOLFinite ent
                  ((HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
                    (ofString "esz", ValueHOL.val (.word 8#64))))
                (sourceFnBody Guest.Software.guestFn_lst_push) with ⟨rlp, slp⟩
            rw [hlp_run] at hb
            have hlp_run_ent : evaluateHOLFiniteState ent_lp
                (sourceFnBody Guest.Software.guestFn_lst_push) = (rlp, slp) := hlp_run
            cases rlp with
            | none => simp at hb
            | some rlp0 =>
              cases rlp0 with
              | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ => simp at hb
              | returned vlp =>
                dsimp only at hb
                -- Prepare `lst_push_body_returned_spec` preconditions on `ent_lp` (which has same memory/globals as `s`):
                have hlp_run := hlp_run_ent
                have hlw_words : WordsOK ent_lp (lw.toNat, 24) := by
                  rw [hlw_eq]; exact (hhead_FW.1 (memW s (e0 + 88), 24) (by simp)).2
                have hlw_in_scr : Inside (lw.toNat, 24) (globN s "scratch_ptr") scratchEnd := by
                  rw [hlw_eq]; exact (hhead_FW.1 (memW s (e0 + 88), 24) (by simp)).1
                have hlw_disj_heap : globN ent_lp "heap_ptr" ≤ lw.toNat + 24 → heapLimit ≤ lw.toNat := by
                  intro _
                  have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
                  rw [R11Shards.heapLimit_val]; rw [R11Shards.scratchStart_val] at h1
                  dsimp only [Inside] at hlw_in_scr; omega
                have hlst0 : 1 ≤ memW ent_lp (lw.toNat + 16) ∧ memW ent_lp (lw.toNat + 8) ≤ memW ent_lp (lw.toNat + 16) := by
                  change 1 ≤ memW s (lw.toNat + 16) ∧ memW s (lw.toNat + 8) ≤ memW s (lw.toNat + 16)
                  rw [hlw_eq]
                  exact ⟨hhead_FW.2.2.2.2.2.2.2.2.2.2.1, hhead_FW.2.2.2.2.2.2.2.2.2.2.2.1⟩
                have hfl_in := hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.1
                have hcap_bnd : memW ent_lp (lw.toNat + 16) < 2 ^ 32 := by
                  change memW s (lw.toNat + 16) < 2 ^ 32; rw [hlw_eq]
                  rcases hfl_in with h1 | h2
                  · have hhl := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hhl
                    unfold frameLogs Inside at h1; dsimp only at h1; omega
                  · have hse : scratchEnd = 2965299200 := R11Shards.scratchEnd_val
                    unfold frameLogs Inside at h2; dsimp only at h2; omega
                have hp0_words : WordsOK ent_lp (memW ent_lp lw.toNat, 8 * memW ent_lp (lw.toNat + 16)) := by
                  change WordsOK s (memW s lw.toNat, 8 * memW s (lw.toNat + 16)); rw [hlw_eq]
                  exact hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                have hp0_disj_lw : Disj (lw.toNat, 24) (memW ent_lp lw.toNat, 8 * memW ent_lp (lw.toNat + 16)) := by
                  change Disj (lw.toNat, 24) (memW s lw.toNat, 8 * memW s (lw.toNat + 16)); rw [hlw_eq]
                  have hpw_head : (frameObjects s (e0, c0)).Pairwise Disj := by
                    have hpw := hFO_pw
                    change (((e0, c0) :: (evmChain s).tail).map (frameObjects s)).flatten.Pairwise Disj at hpw
                    rw [List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
                    exact hpw.1
                  unfold frameObjects at hpw_head
                  have hp0 := List.pairwise_cons.1 hpw_head
                  have hp1 := List.pairwise_cons.1 hp0.2
                  have hp2 := List.pairwise_cons.1 hp1.2
                  have hp3 := List.pairwise_cons.1 hp2.2
                  have hp4 := List.pairwise_cons.1 hp3.2
                  exact hp4.1 _ (by simp [frameLogs])
                have hp0_disj_heap :
                    globN ent_lp "heap_ptr" < memW ent_lp lw.toNat + 8 * memW ent_lp (lw.toNat + 16) →
                    heapLimit ≤ memW ent_lp lw.toNat := by
                  change globN s "heap_ptr" < memW s lw.toNat + 8 * memW s (lw.toNat + 16) → heapLimit ≤ memW s lw.toNat
                  rw [hlw_eq]; intro hge
                  rcases hfl_in with h1 | h2
                  · unfold frameLogs Inside at h1; dsimp only at h1; omega
                  · have h1 := hAs.2.2.2.1; have h2' := hAs.2.2.2.2.1
                    rw [R11Shards.heapLimit_val]; rw [R11Shards.scratchStart_val] at h1
                    unfold frameLogs Inside at h2; dsimp only at h2; omega
                have hspec := lst_push_body_returned_spec ent_lp lw hent_lp_AR hent_lp_l hent_lp_e
                  hlw_words hlw_disj_heap hlst0 hcap_bnd hp0_words hp0_disj_lw hp0_disj_heap vlp slp hlp_run
                dsimp only at hspec
                -- Both branches return `vlp = .val (.word ew)`:
                rcases hspec with
                  ⟨hn_lt_cap, ew, rfl, hew_nat, hew_al, hew_dom_ent, hAslp, heff_slp,
                   hslp_m0, hslp_m8, hslp_m16, hslp_slots⟩ |
                  ⟨hn_eq_cap, ma, npw, ew, rfl, hma_AR, hma_m, hma_be, hma_ma, hnpw_eq, hnpw8,
                   hma_hp, hma_gk, hew_nat, hew_al, hew_dom_slp, hAslp, heff_slp,
                   hslp_m0, hslp_m8, hslp_m16, hslp_slots⟩
                · -- NO-GROW BRANCH (`n0 < cap0`)
                  have hsh_ew : (shapeEqHOL (shapeOfHOLExact (ValueHOL.val (HolWordLab.word ew))) .one &&
                      shapeEqHOL (shapeOfHOLExact (ValueHOL.val (HolWordLab.word ew))) .one) = true := by
                    simp [shapeOfHOLExact, shapeEqHOL]
                  rw [if_pos hsh_ew] at hb
                  let st_slot := setVarHOLFinite (ofString "slot") (.val (.word ew)) { slp with locals := ent.locals }
                  rcases hcont_out : evaluateHOLFiniteState st_slot
                      (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                            (.return (.const 0#64))) with ⟨rcont, scont⟩
                  rw [hcont_out] at hb; dsimp only at hb
                  injection hb with hrv_eq hbs_eq
                  rw [evaluateHOLFiniteState_seq_line780] at hcont_out
                  have hst_slot_ma : st_slot.memaddrs = ordinaryDomain := by
                    change slp.memaddrs = ordinaryDomain; rw [heff_slp.memaddrs]; exact hent_ma
                  have hst_slot_dom : st_slot.memaddrs ew := by
                    change slp.memaddrs ew; rw [heff_slp.memaddrs]; exact hew_dom_ent
                  have hst_slot_s : st_slot.locals.lookup (ofString "slot") = some (.val (.word ew)) := by
                    simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hst_slot_l : st_slot.locals.lookup (ofString "log") = some (.val (.word logw)) := by
                    have hne : ofString "slot" ≠ ofString "log" := by decide
                    simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hent_log]
                  have hev_st_d : @evalHOLExact 64 F _ st_slot.toExact (fun a => Classical.propDecidable (st_slot.memaddrs a))
                      (.var .local (ofString "slot")) = some (.val (.word ew)) := by
                    simp [evalHOLExact, hst_slot_s]
                  have hev_st_v : @evalHOLExact 64 F _ st_slot.toExact (fun a => Classical.propDecidable (st_slot.memaddrs a))
                      (.var .local (ofString "log")) = some (.val (.word logw)) := by
                    simp [evalHOLExact, hst_slot_l]
                  have hst_eq : evaluateHOLFiniteState st_slot
                      (.store (.var .local (ofString "slot")) (.var .local (ofString "log"))) =
                      (none, { st_slot with memory := fun a => if a = ew then .word logw else st_slot.memory a }) := by
                    rw [evaluateHOLFiniteState_store, hev_st_d, hev_st_v]; dsimp only
                    simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hst_slot_dom, FUPDATE]
                  let Rl0 : List Ivl := [(0, 0), (memW s (e0 + 88), 24), frameLogs s (e0, c0)]
                  have hew_in_fl : ew.toNat ≥ (frameLogs s (e0, c0)).1 ∧
                      ew.toNat + 8 ≤ (frameLogs s (e0, c0)).1 + (frameLogs s (e0, c0)).2 := by
                    unfold frameLogs; dsimp only
                    have hp0_eq_s : memW ent_lp lw.toNat = memW s (memW s (e0 + 88)) := by
                      change memW s lw.toNat = _; rw [hlw_eq]
                    have hn0_eq_s : memW ent_lp (lw.toNat + 8) = memW s (memW s (e0 + 88) + 8) := by
                      change memW s (lw.toNat + 8) = _; rw [hlw_eq]
                    have hcap0_eq_s : memW ent_lp (lw.toNat + 16) = memW s (memW s (e0 + 88) + 16) := by
                      change memW s (lw.toNat + 16) = _; rw [hlw_eq]
                    rw [hew_nat, hp0_eq_s, hn0_eq_s]
                    rw [hn0_eq_s, hcap0_eq_s] at hn_lt_cap
                    omega
                  obtain ⟨heff_store, _⟩ := m23_bre_of_store_word (Rl := Rl0) hst_slot_ma hst_eq
                    (fun v hv => by rw [hev_st_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                    (fun addr hdst _ => by
                      rw [hev_st_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                      subst hd3; exact ⟨frameLogs s (e0, c0), by simp [Rl0], hew_in_fl.1, hew_in_fl.2⟩)
                  let st_after := { st_slot with memory := fun a => if a = ew then .word logw else st_slot.memory a }
                  rw [hst_eq] at hcont_out; dsimp only at hcont_out
                  have hret0 := return_const0_step_local st_after
                  have hcont_eq2 : scont = emptyLocalsHOLFinite st_after := by
                    have h2 := congrArg Prod.snd hcont_out
                    dsimp only at h2
                    exact h2.symm.trans hret0.2
                  let post := { bs with locals := s.locals }
                  have hpost_eq : post = { st_after with locals := s.locals, clock := bs.clock } := by
                    dsimp only [post]; rw [← hbs_eq, hcont_eq2]; rfl
                  have heff_s_entlp : ByteRegionEffect s ent_lp Rl0 :=
                    (ByteRegionEffect.refl s Rl0).with_locals_clock ent_lp.locals ent_lp.clock
                  have heff_slp_Rl0 : ByteRegionEffect ent_lp slp Rl0 :=
                    heff_slp.mono fun x hx => by
                      simp only [List.mem_singleton] at hx; subst hx
                      exact ⟨(memW s (e0 + 88), 24), by simp [Rl0], by dsimp only; rw [hlw_eq], by dsimp only; rw [hlw_eq]⟩
                  have heff_stslot : ByteRegionEffect s st_slot Rl0 :=
                    (heff_s_entlp.trans heff_slp_Rl0).with_locals_clock st_slot.locals st_slot.clock
                  have heff_post : ByteRegionEffect s post Rl0 := by
                    rw [hpost_eq]
                    exact (heff_stslot.trans heff_store).with_locals_clock s.locals bs.clock
                  have hApost : ArenaReady post := by
                    refine ⟨⟨heff_post.code.trans hAs.1.code, heff_post.memaddrs.trans hAs.1.memaddrs,
                      heff_post.shMemaddrs.trans hAs.1.shMemaddrs, heff_post.baseAddr.trans hAs.1.baseAddr⟩, ?_⟩
                    simpa only [ArenaOK, globN, GlobalsWord, GlobalWord, heff_post.globals] using hAs.2
                  -- Show the final store at `ew` didn't touch `(lw, 24)` or earlier slots `i < n0`:
                  have hpost_mem_fn : post.memory = st_after.memory := by rw [hpost_eq]
                  have hew_disj_lw : ∀ k : Nat, k < 24 → k % 8 = 0 → BitVec.ofNat 64 (lw.toNat + k) ≠ ew := by
                    intro k hk hk8 heq_bv
                    have hlt_l : lw.toNat + k < 2 ^ 64 := by rw [R11Shards.heapEnd_val] at hev_lt_he; have := hlw_in_scr.2; rw [R11Shards.scratchEnd_val] at this; dsimp only at this; omega
                    have hn_eq : lw.toNat + k = ew.toNat := by
                      have := congrArg BitVec.toNat heq_bv
                      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_l] at this
                    have hd : Disj (lw.toNat, 24) (frameLogs s (e0, c0)) := by
                      unfold frameLogs
                      have hp0_eq_s : memW ent_lp lw.toNat = memW s (memW s (e0 + 88)) := by
                        change memW s lw.toNat = _; rw [hlw_eq]
                      have hcap0_eq_s : memW ent_lp (lw.toNat + 16) = memW s (memW s (e0 + 88) + 16) := by
                        change memW s (lw.toNat + 16) = _; rw [hlw_eq]
                      rw [← hp0_eq_s, ← hcap0_eq_s]
                      exact hp0_disj_lw
                    have h1 := hew_in_fl.1; have h2 := hew_in_fl.2
                    unfold Disj at hd; dsimp only at hd
                    rcases hd with h | h | h | h <;> omega
                  have hpost_m0 : memW post (memW s (e0 + 88)) = memW s (memW s (e0 + 88)) := by
                    have hne := hew_disj_lw 0 (by omega) (by omega)
                    rw [Nat.add_zero] at hne
                    have hm : memW post lw.toNat = memW slp lw.toNat := by
                      unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
                    rw [← hlw_eq, hm]; exact hslp_m0
                  have hpost_m8 : memW post (memW s (e0 + 88) + 8) = memW s (memW s (e0 + 88) + 8) + 1 := by
                    have hne := hew_disj_lw 8 (by omega) (by omega)
                    have hm : memW post (lw.toNat + 8) = memW slp (lw.toNat + 8) := by
                      unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
                    rw [← hlw_eq, hm]; exact hslp_m8
                  have hpost_m16 : memW post (memW s (e0 + 88) + 16) = memW s (memW s (e0 + 88) + 16) := by
                    have hne := hew_disj_lw 16 (by omega) (by omega)
                    have hm : memW post (lw.toNat + 16) = memW slp (lw.toNat + 16) := by
                      unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
                    rw [← hlw_eq, hm]; exact hslp_m16
                  have hpost_old_slots : ∀ i, i < memW s (memW s (e0 + 88) + 8) →
                      memW post (memW post (memW s (e0 + 88)) + 8 * i) =
                      memW s (memW s (memW s (e0 + 88)) + 8 * i) := by
                    intro i hi
                    rw [hpost_m0]
                    have hp0_eq_s : memW ent_lp lw.toNat = memW s (memW s (e0 + 88)) := by
                      change memW s lw.toNat = _; rw [hlw_eq]
                    have hn0_eq_s : memW ent_lp (lw.toNat + 8) = memW s (memW s (e0 + 88) + 8) := by
                      change memW s (lw.toNat + 8) = _; rw [hlw_eq]
                    have hcap0_eq_s : memW ent_lp (lw.toNat + 16) = memW s (memW s (e0 + 88) + 16) := by
                      change memW s (lw.toNat + 16) = _; rw [hlw_eq]
                    have hp_bnd : memW s (memW s (e0 + 88)) + 8 * memW s (memW s (e0 + 88) + 16) < 2 ^ 64 := by
                      rcases hfl_in with h1 | h2
                      · unfold frameLogs Inside at h1; dsimp only at h1
                        have hlim := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hlim; omega
                      · unfold frameLogs Inside at h2; dsimp only at h2
                        have hse := R11Shards.scratchEnd_val; omega
                    have hn_lt_s : memW s (memW s (e0 + 88) + 8) < memW s (memW s (e0 + 88) + 16) := by
                      rwa [← hn0_eq_s, ← hcap0_eq_s]
                    let idxAddr := memW s (memW s (e0 + 88)) + 8 * i
                    have hne : BitVec.ofNat 64 idxAddr ≠ ew := by
                      intro heq_bv
                      have hn_eq : idxAddr = ew.toNat := by
                        have := congrArg BitVec.toNat heq_bv
                        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp only [idxAddr]; omega)] at this
                      dsimp only [idxAddr] at hn_eq
                      rw [hew_nat, hp0_eq_s, hn0_eq_s] at hn_eq; omega
                    have hm : memW post idxAddr = memW slp idxAddr := by
                      unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
                    dsimp only [idxAddr] at hm
                    rw [hm, ← hp0_eq_s]
                    have hsl := hslp_slots i (by rwa [hn0_eq_s])
                    exact hsl
                  have hpost_new_slot :
                      memW post (memW post (memW s (e0 + 88)) + 8 * memW s (memW s (e0 + 88) + 8)) = logw.toNat := by
                    rw [hpost_m0]
                    have hp0_eq_s : memW ent_lp lw.toNat = memW s (memW s (e0 + 88)) := by
                      change memW s lw.toNat = _; rw [hlw_eq]
                    have hn0_eq_s : memW ent_lp (lw.toNat + 8) = memW s (memW s (e0 + 88) + 8) := by
                      change memW s (lw.toNat + 8) = _; rw [hlw_eq]
                    have hcap0_eq_s : memW ent_lp (lw.toNat + 16) = memW s (memW s (e0 + 88) + 16) := by
                      change memW s (lw.toNat + 16) = _; rw [hlw_eq]
                    have hp_bnd : memW s (memW s (e0 + 88)) + 8 * memW s (memW s (e0 + 88) + 16) < 2 ^ 64 := by
                      rcases hfl_in with h1 | h2
                      · unfold frameLogs Inside at h1; dsimp only at h1
                        have hlim := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hlim; omega
                      · unfold frameLogs Inside at h2; dsimp only at h2
                        have hse := R11Shards.scratchEnd_val; omega
                    have hn_lt_s : memW s (memW s (e0 + 88) + 8) < memW s (memW s (e0 + 88) + 16) := by
                      rwa [← hn0_eq_s, ← hcap0_eq_s]
                    let newAddr := memW s (memW s (e0 + 88)) + 8 * memW s (memW s (e0 + 88) + 8)
                    have hew_bv : BitVec.ofNat 64 newAddr = ew := by
                      apply BitVec.eq_of_toNat_eq
                      dsimp only [newAddr]
                      rw [hew_nat, hp0_eq_s, hn0_eq_s, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                    have hmem_post : post.memory ew = .word logw := by
                      rw [hpost_mem_fn]; dsimp only [st_after]; rw [if_pos rfl]
                    have hmw_eq : memW post newAddr = logw.toNat := by
                      unfold memW; rw [hew_bv, hmem_post]
                    exact hmw_eq
                  -- `LogEntryOK post logw.toNat`:
                  have hRl0_8 : ∀ x ∈ Rl0, x.1 % 8 = 0 := by
                    intro x hx; simp only [Rl0, List.mem_cons, List.not_mem_nil, or_false] at hx
                    rcases hx with rfl | rfl | rfl
                    · rfl
                    · exact (hhead_FW.1 (memW s (e0 + 88), 24) (by simp)).2.1
                    · exact hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
                  have hRl0_disj_log : ∀ x ∈ Rl0, Disj x (logw.toNat, 40) := by
                    intro x hx; simp only [Rl0, List.mem_cons, List.not_mem_nil, or_false] at hx
                    rcases hx with rfl | rfl | rfl
                    · exact Or.inl rfl
                    · exact hlog_disj_l0
                    · exact hlog_disj_fl
                  obtain ⟨hlog_post_ok, hlog_owned_eq⟩ :=
                    logEntryOK_congr_of_bre heff_post hAs hRl0_8 hRl0_disj_log hlog_ok
                  have hstep0 : EvmStepCC [] s post :=
                    evmStepCC_of_head_log_append (freshArr := (0, 0)) (log := logw.toNat)
                      (newLogs := logOwnedIvls s logw.toNat)
                      hAs hInvAt_s hTr_at_s hAT_at_s hApost heff_post (Or.inl rfl)
                      (fun x hx => by
                        rcases List.mem_cons.1 hx with rfl | hx_nl
                        · exact ⟨fun _ _ _ _ => Or.inl rfl,
                            fun _ _ => Or.inl rfl,
                            fun _ _ _ _ => Or.inl rfl,
                            fun _ _ => Or.inl rfl,
                            fun _ _ => Or.inl rfl⟩
                        · obtain ⟨hd1, hd2, hd3, hd4, hd5⟩ := hlog_disj x hx_nl
                          exact ⟨hd1, hd2, hd3, hd4, hd5⟩)
                      (List.pairwise_cons.2 ⟨fun _ _ => Or.inl rfl, hlog_pw⟩)
                      (Or.inl ⟨rfl, hpost_m0, hpost_m16⟩)
                      hpost_m8 hlogs_lt
                      (by rw [hpost_m16, ← hlw_eq]; exact hlst0.1)
                      (by rw [hpost_m16, ← hlw_eq]; exact hn_lt_cap)
                      hpost_old_slots hpost_new_slot hlog_post_ok hlog_owned_eq
                  exact ⟨⟨hstep0.1.1, hstep0.1.2.1, fun k hk => hstep0.1.2.2.1 k (by simp), hstep0.1.2.2.2⟩,
                    hstep0.2⟩
                · -- GROW BRANCH (`n0 = cap0`): `s -> ma` via `evmStepCC_of_fresh_heap_step`, then `ma -> post` via `evmStepCC_of_head_log_append`!
                  have hsh_ew : (shapeEqHOL (shapeOfHOLExact (ValueHOL.val (HolWordLab.word ew))) .one &&
                      shapeEqHOL (shapeOfHOLExact (ValueHOL.val (HolWordLab.word ew))) .one) = true := by
                    simp [shapeOfHOLExact, shapeEqHOL]
                  rw [if_pos hsh_ew] at hb
                  -- Step 1: `EvmStepCC ["heap_ptr"] s ma` and `EvmInvAt ma S`:
                  have hma_m_s : ma.memory = s.memory := hma_m
                  have hma_be_s : ma.be = s.be := hma_be
                  have hcap0_eq_s : memW ent_lp (lw.toNat + 16) = memW s (memW s (e0 + 88) + 16) := by
                    change memW s (lw.toNat + 16) = _; rw [hlw_eq]
                  have hn0_eq_s : memW ent_lp (lw.toNat + 8) = memW s (memW s (e0 + 88) + 8) := by
                    change memW s (lw.toNat + 8) = _; rw [hlw_eq]
                  have hp0_eq_s : memW ent_lp lw.toNat = memW s (memW s (e0 + 88)) := by
                    change memW s lw.toNat = _; rw [hlw_eq]
                  have hnpw_s : npw.toNat = globN s "heap_ptr" := hnpw_eq
                  have hhp_le_ma : globN s "heap_ptr" ≤ globN ma "heap_ptr" := by
                    rw [hma_hp, hnpw_s]; omega
                  obtain ⟨hInvAt_ma, hchain_ma, _⟩ :=
                    OpHandlersB.evmInvAt_of_fresh_heap_step hAs hInvAt_s hma_AR hma_be_s
                      hhp_le_ma hma_gk
                      (fun a _ => by rw [hma_m_s])
                      (fun b _ _ => by unfold memB; rw [hma_m_s, hma_be_s])
                  have hstep_ma : EvmStepCC ["heap_ptr"] s ma :=
                    ⟨⟨⟨hma_AR, S, hInvAt_ma⟩, hhp_le_ma, hma_gk, hchain_ma⟩,
                      chainCellsAgree_of_heap_step hAs hInvAt_s hma_AR hma_be_s
                        (fun a _ => by rw [hma_m_s])
                        (fun b _ _ => by unfold memB; rw [hma_m_s, hma_be_s])⟩
                  -- Since `ma.memory = s.memory` and all non-`heap_ptr` globals of `ma` equal `s`:
                  have hma_glob_ne : ∀ g : String, ofString g ≠ ofString "heap_ptr" → globN ma g = globN s g := by
                    intro g hne
                    exact (Wave8Contracts.M23.globN_eq_of_lookup_eq (hma_gk (ofString g) (by simp [hne]))).symm
                  have hma_ev : globN ma "ev" = e0 := hma_glob_ne "ev" (by decide)
                  have hma_cc : globN ma "cur_cont" = c0 := hma_glob_ne "cur_cont" (by decide)
                  have hma_sys : globN ma "vm_system_address" = globN s "vm_system_address" :=
                    hma_glob_ne "vm_system_address" (by decide)
                  have hmemW_ma : ∀ a : Nat, memW ma a = memW s a := fun a => by unfold memW; rw [hma_m_s]
                  -- Step 2: evaluate store `[slot] := log` and `return 0` from `slp` to `post`:
                  let st_slot := setVarHOLFinite (ofString "slot") (.val (.word ew)) { slp with locals := ent.locals }
                  rcases hcont_out : evaluateHOLFiniteState st_slot
                      (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                            (.return (.const 0#64))) with ⟨rcont, scont⟩
                  rw [hcont_out] at hb; dsimp only at hb
                  injection hb with hrv_eq hbs_eq
                  rw [evaluateHOLFiniteState_seq_line780] at hcont_out
                  have hst_slot_ma : st_slot.memaddrs = ordinaryDomain := by
                    change slp.memaddrs = ordinaryDomain; rw [heff_slp.memaddrs, hma_ma]; exact hent_ma
                  have hst_slot_dom : st_slot.memaddrs ew := hew_dom_slp
                  have hst_slot_s : st_slot.locals.lookup (ofString "slot") = some (.val (.word ew)) := by
                    simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hst_slot_l : st_slot.locals.lookup (ofString "log") = some (.val (.word logw)) := by
                    have hne : ofString "slot" ≠ ofString "log" := by decide
                    simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hent_log]
                  have hev_st_d : @evalHOLExact 64 F _ st_slot.toExact (fun a => Classical.propDecidable (st_slot.memaddrs a))
                      (.var .local (ofString "slot")) = some (.val (.word ew)) := by
                    simp [evalHOLExact, hst_slot_s]
                  have hev_st_v : @evalHOLExact 64 F _ st_slot.toExact (fun a => Classical.propDecidable (st_slot.memaddrs a))
                      (.var .local (ofString "log")) = some (.val (.word logw)) := by
                    simp [evalHOLExact, hst_slot_l]
                  have hst_eq : evaluateHOLFiniteState st_slot
                      (.store (.var .local (ofString "slot")) (.var .local (ofString "log"))) =
                      (none, { st_slot with memory := fun a => if a = ew then .word logw else st_slot.memory a }) := by
                    rw [evaluateHOLFiniteState_store, hev_st_d, hev_st_v]; dsimp only
                    simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hst_slot_dom, FUPDATE]
                  let freshArr : Ivl := (npw.toNat, 16 * memW s (memW s (e0 + 88) + 16))
                  let RlG : List Ivl := [freshArr, (memW ma (globN ma "ev" + 88), 24),
                    frameLogs ma (globN ma "ev", globN ma "cur_cont")]
                  have hew_in_fresh : ew.toNat ≥ freshArr.1 ∧ ew.toNat + 8 ≤ freshArr.1 + freshArr.2 := by
                    dsimp only [freshArr]
                    rw [hew_nat, hn0_eq_s]
                    rw [hn0_eq_s, hcap0_eq_s] at hn_eq_cap
                    have hcp_pos : 1 ≤ memW s (memW s (e0 + 88) + 16) := by rw [← hcap0_eq_s]; exact hlst0.1
                    omega
                  obtain ⟨heff_store, _⟩ := m23_bre_of_store_word (Rl := RlG) hst_slot_ma hst_eq
                    (fun v hv => by rw [hev_st_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                    (fun addr hdst _ => by
                      rw [hev_st_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                      subst hd3; exact ⟨freshArr, by simp [RlG], hew_in_fresh.1, hew_in_fresh.2⟩)
                  let st_after := { st_slot with memory := fun a => if a = ew then .word logw else st_slot.memory a }
                  rw [hst_eq] at hcont_out; dsimp only at hcont_out
                  have hret0 := return_const0_step_local st_after
                  have hcont_eq2 : scont = emptyLocalsHOLFinite st_after := by
                    have h2 := congrArg Prod.snd hcont_out
                    dsimp only at h2
                    exact h2.symm.trans hret0.2
                  let post := { bs with locals := s.locals }
                  have hpost_eq : post = { st_after with locals := s.locals, clock := bs.clock } := by
                    dsimp only [post]; rw [← hbs_eq, hcont_eq2]; rfl
                  have heff_slp_RlG : ByteRegionEffect ma slp RlG :=
                    heff_slp.mono fun x hx => by
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                      rcases hx with rfl | rfl
                      · exact ⟨freshArr, by simp [RlG], le_refl _, by dsimp only [freshArr]; rw [hcap0_eq_s]⟩
                      · refine ⟨(memW ma (globN ma "ev" + 88), 24), by simp [RlG], ?_, ?_⟩
                        · dsimp only; rw [hma_ev, hmemW_ma, hlw_eq]
                        · dsimp only; rw [hma_ev, hmemW_ma, hlw_eq]
                  have heff_stslot : ByteRegionEffect ma st_slot RlG :=
                    heff_slp_RlG.with_locals_clock st_slot.locals st_slot.clock
                  have heff_post : ByteRegionEffect ma post RlG := by
                    rw [hpost_eq]
                    exact (heff_stslot.trans heff_store).with_locals_clock s.locals bs.clock
                  have hApost : ArenaReady post := by
                    refine ⟨⟨heff_post.code.trans hma_AR.1.code, heff_post.memaddrs.trans hma_AR.1.memaddrs,
                      heff_post.shMemaddrs.trans hma_AR.1.shMemaddrs, heff_post.baseAddr.trans hma_AR.1.baseAddr⟩, ?_⟩
                    simpa only [ArenaOK, globN, GlobalsWord, GlobalWord, heff_post.globals] using hma_AR.2
                  have hpost_mem_fn : post.memory = st_after.memory := by rw [hpost_eq]
                  -- Disjointness of `freshArr` from `(lw, 24)`:
                  have hew_disj_lw : ∀ k : Nat, k < 24 → k % 8 = 0 → BitVec.ofNat 64 (lw.toNat + k) ≠ ew := by
                    intro k hk hk8 heq_bv
                    have hlt_l : lw.toNat + k < 2 ^ 64 := by
                      have := hlw_in_scr.2; rw [R11Shards.scratchEnd_val] at this; dsimp only at this; omega
                    have hn_eq : lw.toNat + k = ew.toNat := by
                      have := congrArg BitVec.toNat heq_bv
                      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_l] at this
                    have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
                    have hma_lim := hma_AR.2.2.1
                    rw [R11Shards.heapLimit_val] at hma_lim; rw [R11Shards.scratchStart_val] at h1
                    rw [hma_hp, hcap0_eq_s] at hma_lim
                    dsimp only [freshArr] at hew_in_fresh
                    dsimp only [Inside] at hlw_in_scr
                    omega
                  have hpost_m0 : memW post (memW ma (globN ma "ev" + 88)) = npw.toNat := by
                    rw [hma_ev, hmemW_ma, ← hlw_eq]
                    have hne := hew_disj_lw 0 (by omega) (by omega); rw [Nat.add_zero] at hne
                    have hm : memW post lw.toNat = memW slp lw.toNat := by
                      unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
                    rw [hm]; exact hslp_m0
                  have hpost_m8 : memW post (memW ma (globN ma "ev" + 88) + 8) =
                      memW ma (memW ma (globN ma "ev" + 88) + 8) + 1 := by
                    rw [hma_ev, hmemW_ma, hmemW_ma, ← hlw_eq]
                    have hne := hew_disj_lw 8 (by omega) (by omega)
                    have hm : memW post (lw.toNat + 8) = memW slp (lw.toNat + 8) := by
                      unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
                    rw [hm]; exact hslp_m8
                  have hpost_m16 : memW post (memW ma (globN ma "ev" + 88) + 16) =
                      2 * memW s (memW s (e0 + 88) + 16) := by
                    rw [hma_ev, hmemW_ma, ← hcap0_eq_s, ← hlw_eq]
                    have hne := hew_disj_lw 16 (by omega) (by omega)
                    have hm : memW post (lw.toNat + 16) = memW slp (lw.toNat + 16) := by
                      unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
                    rw [hm]; exact hslp_m16
                  have hpost_old_slots : ∀ i, i < memW ma (memW ma (globN ma "ev" + 88) + 8) →
                      memW post (memW post (memW ma (globN ma "ev" + 88)) + 8 * i) =
                      memW ma (memW ma (memW ma (globN ma "ev" + 88)) + 8 * i) := by
                    intro i hi
                    rw [hpost_m0]
                    rw [hma_ev, hmemW_ma, hmemW_ma] at hi ⊢
                    rw [hmemW_ma]
                    have hma_lim := hma_AR.2.2.1; rw [R11Shards.heapLimit_val] at hma_lim
                    rw [hma_hp, hcap0_eq_s] at hma_lim
                    rw [hn0_eq_s, hcap0_eq_s] at hn_eq_cap
                    have hne : BitVec.ofNat 64 (npw.toNat + 8 * i) ≠ ew := by
                      intro heq_bv
                      have hn_eq : npw.toNat + 8 * i = ew.toNat := by
                        have := congrArg BitVec.toNat heq_bv
                        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
                      rw [hew_nat, hn0_eq_s] at hn_eq; omega
                    have hm : memW post (npw.toNat + 8 * i) = memW slp (npw.toNat + 8 * i) := by
                      unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
                    rw [hm, ← hp0_eq_s]
                    have hsl := hslp_slots i (by rwa [hn0_eq_s])
                    rwa [hmemW_ma] at hsl
                  have hpost_new_slot :
                      memW post (memW post (memW ma (globN ma "ev" + 88)) +
                        8 * memW ma (memW ma (globN ma "ev" + 88) + 8)) = logw.toNat := by
                    rw [hpost_m0, hma_ev, hmemW_ma, hmemW_ma]
                    have hma_lim := hma_AR.2.2.1; rw [R11Shards.heapLimit_val] at hma_lim
                    rw [hma_hp, hcap0_eq_s] at hma_lim
                    have hn_eq_cap_s : memW s (memW s (e0 + 88) + 8) = memW s (memW s (e0 + 88) + 16) := by
                      rwa [← hn0_eq_s, ← hcap0_eq_s]
                    let newAddr := npw.toNat + 8 * memW s (memW s (e0 + 88) + 8)
                    have hew_bv : BitVec.ofNat 64 newAddr = ew := by
                      apply BitVec.eq_of_toNat_eq
                      dsimp only [newAddr]
                      rw [hew_nat, hn0_eq_s, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                    have hmem_post : post.memory ew = .word logw := by
                      rw [hpost_mem_fn]; dsimp only [st_after]; rw [if_pos rfl]
                    have hmw_eq : memW post newAddr = logw.toNat := by
                      unfold memW; rw [hew_bv, hmem_post]
                    exact hmw_eq
                  -- Establish `LogEntryOK post logw.toNat` and `hfresh_disj_s` on `ma`:
                  have hlog_ok_ma : LogEntryOK ma logw.toNat := by
                    unfold LogEntryOK at hlog_ok ⊢
                    simp only [hmemW_ma]
                    exact ⟨(wordsOK_congr_dom (hma_AR.1.memaddrs.trans hs_ma.symm)).2 hlog_ok.1,
                      ⟨hlog_ok.2.1.1, le_trans hlog_ok.2.1.2 hhp_le_ma⟩,
                      hlog_ok.2.2.1, hlog_ok.2.2.2.1,
                      ⟨hlog_ok.2.2.2.2.1.1, le_trans hlog_ok.2.2.2.2.1.2 hhp_le_ma⟩,
                      ⟨hlog_ok.2.2.2.2.2.1.1, le_trans hlog_ok.2.2.2.2.2.1.2 hhp_le_ma⟩,
                      ⟨hlog_ok.2.2.2.2.2.2.1, le_trans hlog_ok.2.2.2.2.2.2.2 hhp_le_ma⟩⟩
                  have hlog_owned_ma : logOwnedIvls ma logw.toNat = logOwnedIvls s logw.toNat := by
                    unfold logOwnedIvls logRecordIvls
                    simp only [hmemW_ma, hma_sys]
                  have hRlG_8 : ∀ x ∈ RlG, x.1 % 8 = 0 := by
                    intro x hx; simp only [RlG, List.mem_cons, List.not_mem_nil, or_false] at hx
                    rcases hx with rfl | rfl | rfl
                    · exact hnpw8
                    · rw [hma_ev, hmemW_ma]; exact (hhead_FW.1 (memW s (e0 + 88), 24) (by simp)).2.1
                    · unfold frameLogs; dsimp only; rw [hma_ev, hmemW_ma, hmemW_ma]
                      exact hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
                  have hfresh_disj_log : Disj freshArr (logw.toNat, 40) := by
                    have hl_in := hlog_ok.2.1
                    dsimp only [freshArr]; dsimp only [Inside] at hl_in
                    exact Or.inr (Or.inr (Or.inr (by rw [hnpw_s]; omega)))
                  have hRlG_disj_log : ∀ x ∈ RlG, Disj x (logw.toNat, 40) := by
                    intro x hx; simp only [RlG, List.mem_cons, List.not_mem_nil, or_false] at hx
                    rcases hx with rfl | rfl | rfl
                    · exact hfresh_disj_log
                    · rw [hma_ev, hmemW_ma]; exact hlog_disj_l0
                    · unfold frameLogs; dsimp only; rw [hma_ev, hmemW_ma, hmemW_ma, hmemW_ma]
                      exact hlog_disj_fl
                  obtain ⟨hlog_post_ok, hlog_owned_post⟩ :=
                    logEntryOK_congr_of_bre heff_post hma_AR hRlG_8 hRlG_disj_log hlog_ok_ma
                  -- Congruence between `ma` and `s` for `fixedObjects`, `frameObjects`, `htabFootprint`, `nodeExtents`:
                  have hcell_ma : Wave8Contracts.M23.SameTypedCells s ma S Nd_at :=
                    ⟨hma_be_s, hma_AR.1.memaddrs.trans hs_ma.symm, hs_ma,
                      fun a _ => by rw [hma_m_s],
                      fun a _ _ _ => by rw [hma_m_s],
                      fun b _ _ => by unfold memB; rw [hma_m_s, hma_be_s]⟩
                  have hfixed_ma : fixedObjects ma = fixedObjects s := by
                    unfold fixedObjects
                    rw [Wave8Contracts.M23.blockOutObjects_eq hAs.2 hW.2.2.1 hcell_ma (hma_glob_ne "bo" (by decide)),
                        Wave8Contracts.M23.balObjects_eq hAs.2 hW.1 hW.2.2.1 hcell_ma (hma_glob_ne "bal_accounts" (by decide)),
                        hma_glob_ne "journal" (by decide),
                        hma_glob_ne "journal_cap" (by decide)]
                    congr 3
                    apply List.map_congr_left
                    intro gn hgn
                    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
                    rw [hma_glob_ne gn.1 hne]
                  have hfo_ma : ∀ ec, frameObjects ma ec = frameObjects s ec := by
                    intro ec
                    unfold frameObjects frameLogs frameRet frameLogObjects logOwnedIvls logRecordIvls
                    simp only [hmemW_ma, hma_sys]
                  have hfp_ma : ∀ t, htabFootprint ma t = htabFootprint s t := by
                    intro t; unfold htabFootprint hdr; simp only [hmemW_ma]
                  have hne_ma : ∀ Nd0, nodeExtents ma Nd0 = nodeExtents s Nd0 := by
                    intro Nd0; unfold nodeExtents nodeIvl nodePath; simp only [hmemW_ma]
                  have hFT_ma := Wave8Contracts.M23.fixedTyped_of_eq hma_AR hW.2.2.1 hhp_le_ma
                    (by rw [hma_glob_ne "scratch_ptr" (by decide)]) hfixed_ma
                  obtain ⟨hWT_ma, _⟩ := Wave8Contracts.M23.worldTypedWith_congr_w1 hAs hma_AR hhp_le_ma
                    (by rw [hma_glob_ne "scratch_ptr" (by decide)])
                    (fun g hg => hma_glob_ne g (by revert g hg; decide))
                    hcell_ma ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at_s⟩
                    ⟨hFT_ma, fun o ho => Or.inl (by rw [← hfixed_ma]; exact ho)⟩
                  have hAT_at_ma :
                      ∀ o ∈ ((evmChain ma).map (frameObjects ma)).flatten,
                        ∀ j ∈ nodeExtents ma Nd_at, Disj o j := by
                    rw [hchain_ma, show (evmChain s).map (frameObjects ma) = (evmChain s).map (frameObjects s) from
                      List.map_congr_left (fun ec _ => hfo_ma ec), hne_ma Nd_at]
                    exact hAT_at_s
                  have hma_lim_hp : globN ma "heap_ptr" ≤ heapLimit := hma_AR.2.2.1
                  have hfresh_disj_s_arr := disj_fresh_heap_of_evmInv (x := freshArr) (hp1 := globN ma "heap_ptr")
                    hInv hma_lim_hp
                    (Or.inr ⟨by dsimp only [freshArr]; rw [hnpw_s],
                      by dsimp only [freshArr]; rw [hma_hp, hcap0_eq_s]⟩)
                  have hfresh_alloc_ma :
                      freshArr = (0, 0) ∨
                        (freshArr.1 % 8 = 0 ∧ freshArr.2 % 8 = 0 ∧
                          Inside freshArr sourceBase (globN ma "heap_ptr")) := by
                    right
                    refine ⟨hnpw8, by dsimp only [freshArr]; omega, ?_⟩
                    have hsb : sourceBase ≤ globN s "heap_ptr" := hAs.2.1
                    exact ⟨by dsimp only [freshArr]; rw [hnpw_s]; exact hsb,
                      by dsimp only [freshArr]; rw [hma_hp, hcap0_eq_s]⟩
                  have hfresh_disj_ma : ∀ x ∈ freshArr :: logOwnedIvls s logw.toNat,
                      (∀ t ∈ S, ∀ i ∈ htabFootprint ma t, Disj x i) ∧
                      (∀ j ∈ fixedObjects ma, Disj x j) ∧
                      (∀ ec ∈ evmChain ma, ∀ o ∈ frameObjects ma ec, Disj x o) ∧
                      (∀ j ∈ nodeExtents ma Nd_at, Disj x j) ∧
                      (∀ ec ∈ evmChain ma, Disj x (memW ma (ec.1 + 112), 176)) := by
                    intro x hx
                    rw [hfixed_ma, hchain_ma, hne_ma Nd_at]
                    rcases List.mem_cons.1 hx with rfl | hx_nl
                    · refine ⟨fun t ht i hi => ?_, hfresh_disj_s_arr.2.1,
                        fun ec hec o ho => ?_,
                        fun j hj => hfresh_disj_s_arr.2.2.2.1 S Nd_at hTr_at_s j hj,
                        fun ec hec => ?_⟩
                      · rw [hfp_ma t] at hi; exact hfresh_disj_s_arr.1 t S hW.1 ht i hi
                      · rw [hfo_ma ec] at ho; exact hfresh_disj_s_arr.2.2.1 ec hec o ho
                      · rw [hmemW_ma]; exact hfresh_disj_s_arr.2.2.2.2 ec hec
                    · obtain ⟨hd1, hd2, hd3, hd4, hd5⟩ := hlog_disj x hx_nl
                      refine ⟨fun t ht i hi => ?_, hd2,
                        fun ec hec o ho => ?_, hd4, fun ec hec => ?_⟩
                      · rw [hfp_ma t] at hi; exact hd1 t ht i hi
                      · rw [hfo_ma ec] at ho; exact hd3 ec hec o ho
                      · rw [hmemW_ma]; exact hd5 ec hec
                  have hfresh_pw : (freshArr :: logOwnedIvls s logw.toNat).Pairwise Disj := by
                    refine List.pairwise_cons.2 ⟨fun y hy => ?_, hlog_pw⟩
                    have hy_rec := (List.mem_filter.1 hy).1
                    unfold logRecordIvls at hy_rec
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy_rec
                    have ha1 : freshArr.1 = globN s "heap_ptr" := by dsimp only [freshArr]; exact hnpw_s
                    rcases hy_rec with rfl | rfl | rfl | rfl
                    · have hle := hlog_ok.2.1.2; exact Or.inr (Or.inr (Or.inr (by omega)))
                    · have hle := hlog_ok.2.2.2.2.1.2; exact Or.inr (Or.inr (Or.inr (by omega)))
                    · have hle := hlog_ok.2.2.2.2.2.1.2; exact Or.inr (Or.inr (Or.inr (by omega)))
                    · have hle := hlog_ok.2.2.2.2.2.2.2; exact Or.inr (Or.inr (Or.inr (by omega)))
                  have hstepG : EvmStepCC [] ma post :=
                    evmStepCC_of_head_log_append (freshArr := freshArr) (log := logw.toNat)
                      (newLogs := logOwnedIvls s logw.toNat)
                      hma_AR hInvAt_ma hWT_ma.2.2.2 hAT_at_ma hApost heff_post hfresh_alloc_ma
                      hfresh_disj_ma hfresh_pw
                      (Or.inr ⟨by dsimp only [freshArr]; have := hlst0.1; rw [hcap0_eq_s] at this; omega,
                        by ext <;> dsimp only [freshArr]
                           · exact hpost_m0
                           · rw [hpost_m16]; omega⟩)
                      hpost_m8
                      (by rw [hma_ev, hmemW_ma, hmemW_ma]; exact hlogs_lt)
                      (by rw [hpost_m16]; have := hlst0.1; rw [hcap0_eq_s] at this; omega)
                      (by rw [hpost_m16, hma_ev, hmemW_ma, hmemW_ma]; have := hlst0.2; rw [hn0_eq_s, hcap0_eq_s] at this; omega)
                      hpost_old_slots hpost_new_slot hlog_post_ok
                      (hlog_owned_post.trans hlog_owned_ma)
                  have hstepG_hp : EvmStepCC ["heap_ptr"] ma post :=
                    ⟨⟨hstepG.1.1, hstepG.1.2.1, fun k _ => hstepG.1.2.2.1 k (by simp), hstepG.1.2.2.2⟩,
                      hstepG.2⟩
                  exact ⟨⟨hstepG_hp.1.1, le_trans hstep_ma.1.2.1 hstepG_hp.1.2.1,
                      fun k hk => (hstep_ma.1.2.2.1 k hk).trans (hstepG_hp.1.2.2.1 k hk),
                      hstepG_hp.1.2.2.2.trans hstep_ma.1.2.2.2⟩,
                    fun ec hec =>
                      let ⟨a1, b1, c1, d1⟩ := hstep_ma.2 ec hec
                      let ⟨a2, b2, c2, d2⟩ := hstepG_hp.2 ec (hstep_ma.1.2.2.2.symm ▸ hec)
                      ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1⟩⟩
        · simp at hcall
      | _ => simp at hcall

theorem transfer_log_append_returned_step_at {F : Type}
    (s : PanSemStateFiniteExact 64 F) (evw logw : BitVec 64) (topics data : Nat)
    (S Nd : List Nat) (hInvAt : EvmInvAt s S) (hTr : TriesTypedWith s S Nd)
    (hAT : ∀ o ∈ ((evmChain s).map (frameObjects s)).flatten,
      ∀ j ∈ nodeExtents s Nd, Disj o j)
    (hInv : EvmInv s) (hev : evw.toNat = globN s "ev")
    (hwords : WordsOK s (logw.toNat, 40))
    (hlog : Inside (logw.toNat, 40) sourceBase (globN s "heap_ptr"))
    (hsys : Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (htopics : Inside (topics, 96) sourceBase (globN s "heap_ptr"))
    (hdata : Inside (data, 32) sourceBase (globN s "heap_ptr"))
    (haddr : memW s logw.toNat = globN s "vm_system_address")
    (htp : memW s (logw.toNat + 8) = topics)
    (htn : memW s (logw.toNat + 16) = 3)
    (hdp : memW s (logw.toNat + 24) = data)
    (hdn : memW s (logw.toNat + 32) = 32)
    (hlt : logw.toNat + 40 ≤ topics) (htd : topics + 96 ≤ data)
    (hdisj : ∀ x ∈ logOwnedIvls s logw.toNat,
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj x i) ∧
      (∀ j ∈ fixedObjects s, Disj x j) ∧
      (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj x o) ∧
      (∀ j ∈ nodeExtents s Nd, Disj x j) ∧
      (∀ ec ∈ evmChain s, Disj x (memW s (ec.1 + 112), 176)))
    (hcall : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])).1 = none)
    (heval_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "ev")) = some (.val (.word evw)))
    (heval_log : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "log")) = some (.val (.word logw))) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])
    EvmStepCC ["heap_ptr"] s out.2 ∧ out.2.locals = s.locals := by
  have hrecord : (logw.toNat, 40) ∈ logOwnedIvls s logw.toNat := by
    rw [logOwnedIvls_of_transfer haddr htp htn hdp hdn]
    simp
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := List.mem_cons_self
  have hframe := (hdisj _ hrecord).2.2.1 _ hhead
  have hdisj_header : Disj (memW s (globN s "ev" + 88), 24) (logw.toNat, 40) :=
    disj_comm (hframe _ (by simp [frameObjects]))
  have hdisj_array : Disj (frameLogs s (globN s "ev", globN s "cur_cont")) (logw.toNat, 40) :=
    disj_comm (hframe _ (by simp [frameObjects]))
  apply log_append_head_returned_spec s evw logw hInv S Nd hInvAt hTr hAT hev
    (head_log_count_succ_lt_of_evmInv hInv)
    (logEntryOK_of_transfer hwords hlog hsys htopics hdata haddr htp htn hdp hdn)
    hdisj
    (transfer_logOwnedIvls_pairwise haddr htp htn hdp hdn hlt htd)
    hdisj_header hdisj_array hcall heval_ev heval_log

theorem transfer_log_append_returned_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (evw logw : BitVec 64) (topics data : Nat)
    (hInv : EvmInv s) (hev : evw.toNat = globN s "ev")
    (hwords : WordsOK s (logw.toNat, 40))
    (hlog : Inside (logw.toNat, 40) sourceBase (globN s "heap_ptr"))
    (hsys : Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (htopics : Inside (topics, 96) sourceBase (globN s "heap_ptr"))
    (hdata : Inside (data, 32) sourceBase (globN s "heap_ptr"))
    (haddr : memW s logw.toNat = globN s "vm_system_address")
    (htp : memW s (logw.toNat + 8) = topics)
    (htn : memW s (logw.toNat + 16) = 3)
    (hdp : memW s (logw.toNat + 24) = data)
    (hdn : memW s (logw.toNat + 32) = 32)
    (hlt : logw.toNat + 40 ≤ topics) (htd : topics + 96 ≤ data)
    (hdisj : ∀ x ∈ logOwnedIvls s logw.toNat,
      (∀ t, ∀ S0, TablesTyped s S0 → t ∈ S0 → ∀ i ∈ htabFootprint s t, Disj x i) ∧
      (∀ j ∈ fixedObjects s, Disj x j) ∧
      (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj x o) ∧
      (∀ S0 Nd0, TriesTypedWith s S0 Nd0 → ∀ j ∈ nodeExtents s Nd0, Disj x j) ∧
      (∀ ec ∈ evmChain s, Disj x (memW s (ec.1 + 112), 176)))
    (hcall : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])).1 = none)
    (heval_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "ev")) = some (.val (.word evw)))
    (heval_log : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "log")) = some (.val (.word logw))) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])
    EvmStepCC ["heap_ptr"] s out.2 ∧ out.2.locals = s.locals := by
  obtain ⟨_, S, inv⟩ := (evmInv_iff_at s).1 hInv
  obtain ⟨Nd, tries, avoids⟩ := inv.2.2.2.2.2.2.2.2.2.1
  exact transfer_log_append_returned_step_at s evw logw topics data S Nd inv tries avoids
    hInv hev hwords hlog hsys htopics hdata haddr htp htn hdp hdn hlt htd
    (fun x hx => ⟨fun t ht => (hdisj x hx).1 t S inv.1.1 ht,
      (hdisj x hx).2.1, (hdisj x hx).2.2.1,
      (hdisj x hx).2.2.2.1 S Nd tries, (hdisj x hx).2.2.2.2⟩)
    hcall heval_ev heval_log

private theorem transfer_call0_no_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | _
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fn _ with _ | ⟨_, _, _⟩
    · simp
    · dsimp only; split
      · simp
      · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned _ => dsimp only; split <;> simp
          | _ => simp

theorem transfer_u256_to_be32_call_no_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (amount dst : ExpHOL 64)
    (hcode : s.code = originalRuntimeCode) :
    ¬ Resumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "u256_to_be32") [amount, dst])).1 := by
  intro hr
  rcases hr with ⟨v, hv⟩ | ⟨e, v, hv, hne⟩
  · exact transfer_call0_no_return s _ _ v hv
  · exact evaluate_noCatchableRaise emitLogNcrCallees emitLogNcrCallees_good
      (.call (some (none, none)) (ofString "u256_to_be32") [amount, dst])
      rfl s hcode e v hne hv

theorem transfer_log_append_tail_resumes_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (hr : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")]) (.return (.const 0)))).1) :
    ∃ v, (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")]) (.return (.const 0)))).1 =
        some (.returned v) := by
  rcases hr with h | ⟨e, v, he, hne⟩
  · exact h
  · exact False.elim (evaluate_noCatchableRaise emitLogNcrCallees emitLogNcrCallees_good
      (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")]) (.return (.const 0)))
      rfl s hcode e v hne he)

theorem transfer_log_append_return_tail {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hstep : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])).1 = none →
      EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "log_append")
          [.var .global (ofString "ev"), .var .local (ofString "log")])).2)
    (hres : ∃ v, (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])
        (.return (.const 0)))).1 = some (.returned v)) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])
        (.return (.const 0)))).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  rcases hc : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")]) with ⟨r, mid⟩
  simp only [hc] at hres ⊢
  cases r with
  | none =>
    have hs := hstep (by rw [hc])
    rw [hc] at hs
    simp only [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
      sizeOfShapeWithContextHOL] at hres ⊢
    exact ⟨⟨localsFree_evmInv _ _ _ hs.1.1, hs.1.2.1, hs.1.2.2.1,
      (evmChain_with_locals _ _ _).trans hs.1.2.2.2⟩, hs.2⟩
  | some r =>
    obtain ⟨v, hv⟩ := hres
    simp only at hv
    have hret : r = .returned v := Option.some.inj hv
    exact False.elim (transfer_call0_no_return s _ _ v (by rw [hc, hret]))

theorem transfer_log_append_tail_step_at {F : Type}
    (s : PanSemStateFiniteExact 64 F) (evw logw : BitVec 64) (topics data : Nat)
    (S Nd : List Nat) (hInvAt : EvmInvAt s S) (hTr : TriesTypedWith s S Nd)
    (hAT : ∀ o ∈ ((evmChain s).map (frameObjects s)).flatten,
      ∀ j ∈ nodeExtents s Nd, Disj o j)
    (hInv : EvmInv s) (hev : evw.toNat = globN s "ev")
    (hwords : WordsOK s (logw.toNat, 40))
    (hlog : Inside (logw.toNat, 40) sourceBase (globN s "heap_ptr"))
    (hsys : Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (htopics : Inside (topics, 96) sourceBase (globN s "heap_ptr"))
    (hdata : Inside (data, 32) sourceBase (globN s "heap_ptr"))
    (haddr : memW s logw.toNat = globN s "vm_system_address")
    (htp : memW s (logw.toNat + 8) = topics)
    (htn : memW s (logw.toNat + 16) = 3)
    (hdp : memW s (logw.toNat + 24) = data)
    (hdn : memW s (logw.toNat + 32) = 32)
    (hlt : logw.toNat + 40 ≤ topics) (htd : topics + 96 ≤ data)
    (hdisj : ∀ x ∈ logOwnedIvls s logw.toNat,
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj x i) ∧
      (∀ j ∈ fixedObjects s, Disj x j) ∧
      (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj x o) ∧
      (∀ j ∈ nodeExtents s Nd, Disj x j) ∧
      (∀ ec ∈ evmChain s, Disj x (memW s (ec.1 + 112), 176)))
    (heval_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "ev")) = some (.val (.word evw)))
    (heval_log : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "log")) = some (.val (.word logw)))
    (hres : ∃ v, (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])
        (.return (.const 0)))).1 = some (.returned v)) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])
        (.return (.const 0)))).2 := by
  apply transfer_log_append_return_tail s (fun hcall => ?_) hres
  exact (transfer_log_append_returned_step_at s evw logw topics data S Nd hInvAt hTr hAT
    hInv hev hwords hlog hsys htopics hdata haddr htp htn hdp hdn hlt htd hdisj
    hcall heval_ev heval_log).1

theorem transfer_log_append_tail_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (evw logw : BitVec 64) (topics data : Nat)
    (hInv : EvmInv s) (hev : evw.toNat = globN s "ev")
    (hwords : WordsOK s (logw.toNat, 40))
    (hlog : Inside (logw.toNat, 40) sourceBase (globN s "heap_ptr"))
    (hsys : Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (htopics : Inside (topics, 96) sourceBase (globN s "heap_ptr"))
    (hdata : Inside (data, 32) sourceBase (globN s "heap_ptr"))
    (haddr : memW s logw.toNat = globN s "vm_system_address")
    (htp : memW s (logw.toNat + 8) = topics)
    (htn : memW s (logw.toNat + 16) = 3)
    (hdp : memW s (logw.toNat + 24) = data)
    (hdn : memW s (logw.toNat + 32) = 32)
    (hlt : logw.toNat + 40 ≤ topics) (htd : topics + 96 ≤ data)
    (hdisj : ∀ x ∈ logOwnedIvls s logw.toNat,
      (∀ t, ∀ S0, TablesTyped s S0 → t ∈ S0 → ∀ i ∈ htabFootprint s t, Disj x i) ∧
      (∀ j ∈ fixedObjects s, Disj x j) ∧
      (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj x o) ∧
      (∀ S0 Nd0, TriesTypedWith s S0 Nd0 → ∀ j ∈ nodeExtents s Nd0, Disj x j) ∧
      (∀ ec ∈ evmChain s, Disj x (memW s (ec.1 + 112), 176)))
    (heval_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "ev")) = some (.val (.word evw)))
    (heval_log : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "log")) = some (.val (.word logw)))
    (hres : ∃ v, (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])
        (.return (.const 0)))).1 = some (.returned v)) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")])
        (.return (.const 0)))).2 := by
  apply transfer_log_append_return_tail s (fun hcall => ?_) hres
  exact (transfer_log_append_returned_step s evw logw topics data hInv hev hwords
    hlog hsys htopics hdata haddr htp htn hdp hdn hlt htd hdisj hcall heval_ev heval_log).1

end EmitTransferLogStep

/-! ## Precompile dispatch composition -/

open InitECandidate.Solver.Wave8GuestInv.R13

open InitECandidate.Solver.Wave8Contracts.M23

theorem transfer_seq_resumes_left {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : ProgHOL 64) (hr : Resumes (evaluateHOLFiniteState s (.seq a b)).1) :
    (evaluateHOLFiniteState s a).1 = none ∨ Resumes (evaluateHOLFiniteState s a).1 := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  cases he : (evaluateHOLFiniteState s a).1 with
  | none => exact Or.inl rfl
  | some r =>
    right
    simpa only [he] using hr

theorem transfer_accumulated_memcpy_step {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (dst src n : ExpHOL 64)
    (dw sw nw : BitVec 64) (Rl : List Ivl)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hd : @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) dst = some (.val (.word dw)))
    (hs : @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) src = some (.val (.word sw)))
    (hn : @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) n = some (.val (.word nw)))
    (hsub : 0 < nw.toNat → ∃ i ∈ Rl, i.1 ≤ dw.toNat ∧ dw.toNat + nw.toNat ≤ i.1 + i.2)
    (hin : ∀ i ∈ Rl, Inside i (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memcpy") [dst, src, n])).1 = none ∨
      Resumes (evaluateHOLFiniteState cur
        (.call (some (none, none)) (ofString "memcpy") [dst, src, n])).1) :
    let out := evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memcpy") [dst, src, n])
    out.1 = none ∧ EvmStepCC ["heap_ptr"] s out.2 ∧
      ByteRegionEffect cur out.2 Rl ∧ out.2.locals = cur.locals ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → out.2.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN out.2 "heap_ptr") → memB out.2 b = memB s b) := by
  dsimp only
  have hnt : (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memcpy") [dst, src, n])).1 ≠ some .timeOut := by
    intro he
    rcases hr with hz | hr
    · rw [he] at hz; cases hz
    · rcases hr with ⟨v, hv⟩ | ⟨e, v, hv, _⟩ <;> rw [he] at hv <;> cases hv
  obtain ⟨hgood, hbad⟩ := M11.eval_call_memcpy_bre cur dst src n dw sw nw Rl
    hstep.1.1.1.1.code hstep.1.1.1.1.memaddrs hd hs hn hsub hnt
  have hz : (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memcpy") [dst, src, n])).1 = none := by
    by_contra hne
    exact hr.elim hne (hbad hne)
  obtain ⟨heff, hl⟩ := hgood hz
  have heff' : ByteRegionEffect cur (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memcpy") [dst, src, n])).2 Rl :=
    ⟨heff.code, heff.memaddrs, heff.shMemaddrs, heff.baseAddr, heff.be,
      heff.globals, heff.out_dom, heff.cell_frame, heff.byte_frame⟩
  obtain ⟨hstep', hout', hbyte'⟩ :=
    evmStepCC_of_accumulated_heap_effect hInv hstep hbe hout hbyte heff' hin
  exact ⟨hz, hstep', heff', hl, hout', hbyte'⟩

theorem transfer_topic_copy_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (topics topic : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (ht : cur.locals.lookup (ofString "topics") = some (.val (.word topics)))
    (hsrc : cur.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hin : Inside (topics.toNat, 96) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.seq (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "topics"), .var .global (ofString "transfer_topic"), .const 32]) cont)).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid ∧ ByteRegionEffect cur mid [(topics.toNat, 96)] ∧
      mid.locals = cur.locals ∧ Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      evaluateHOLFiniteState cur
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "topics"), .var .global (ofString "transfer_topic"), .const 32]) cont) =
        evaluateHOLFiniteState mid cont := by
  let call : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy")
    [.var .local (ofString "topics"), .var .global (ofString "transfer_topic"), .const 32]
  have hleft := transfer_seq_resumes_left cur call cont hr
  obtain ⟨hz, hstep', heff, hl, hout', hbyte'⟩ :=
    transfer_accumulated_memcpy_step s cur _ _ _ topics topic 32 [(topics.toNat, 96)]
      hInv hstep hbe hout hbyte
      (by simpa [evalHOLExact] using ht)
      (by simpa [evalHOLExact] using hsrc)
      rfl
      (fun _ => ⟨(topics.toNat, 96), by simp, le_rfl, by simp⟩)
      (fun i hi => by rcases List.mem_singleton.mp hi with rfl; exact hin) hleft
  let mid := (evaluateHOLFiniteState cur call).2
  have heq : evaluateHOLFiniteState cur (.seq call cont) = evaluateHOLFiniteState mid cont := by
    rw [evaluateHOLFiniteState_seq_line780]
    change (evaluateHOLFiniteState cur call).1 = none at hz
    simp only [hz]
    rfl
  exact ⟨mid, hstep', heff, hl, heq ▸ hr, hout', hbyte', heq⟩

theorem transfer_accumulated_memzero_step {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (dst n : ExpHOL 64)
    (dw nw : BitVec 64) (Rl : List Ivl)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hd : @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) dst = some (.val (.word dw)))
    (hn : @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) n = some (.val (.word nw)))
    (hsub : 0 < nw.toNat → ∃ i ∈ Rl, i.1 ≤ dw.toNat ∧ dw.toNat + nw.toNat ≤ i.1 + i.2)
    (hin : ∀ i ∈ Rl, Inside i (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memzero") [dst, n])).1 = none ∨
      Resumes (evaluateHOLFiniteState cur
        (.call (some (none, none)) (ofString "memzero") [dst, n])).1) :
    let out := evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memzero") [dst, n])
    out.1 = none ∧ EvmStepCC ["heap_ptr"] s out.2 ∧
      ByteRegionEffect cur out.2 Rl ∧ out.2.locals = cur.locals ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → out.2.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN out.2 "heap_ptr") → memB out.2 b = memB s b) := by
  dsimp only
  have hnt : (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memzero") [dst, n])).1 ≠ some .timeOut := by
    intro he
    rcases hr with hz | hr
    · rw [he] at hz; cases hz
    · rcases hr with ⟨v, hv⟩ | ⟨e, v, hv, _⟩ <;> rw [he] at hv <;> cases hv
  obtain ⟨hgood, hbad⟩ := R16Shards.OpHandlersB.eval_call_memzero_bre cur dst n dw nw Rl
    hstep.1.1.1.1.code hstep.1.1.1.1.memaddrs hd hn hsub hnt
  have hz : (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memzero") [dst, n])).1 = none := by
    by_contra hne
    exact hr.elim hne (hbad hne)
  obtain ⟨heff, hl⟩ := hgood hz
  obtain ⟨hstep', hout', hbyte'⟩ :=
    evmStepCC_of_accumulated_heap_effect hInv hstep hbe hout hbyte heff hin
  exact ⟨hz, hstep', heff, hl, hout', hbyte'⟩

theorem transfer_topic_padding_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (topics : BitVec 64) (offset : Nat) (cont : ProgHOL 64)
    (hoff : offset = 32 ∨ offset = 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (ht : cur.locals.lookup (ofString "topics") = some (.val (.word topics)))
    (hin : Inside (topics.toNat, 96) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.seq (.call (some (none, none)) (ofString "memzero")
        [.op .add [.var .local (ofString "topics"), .const (BitVec.ofNat 64 offset)], .const 12]) cont)).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid ∧ ByteRegionEffect cur mid [(topics.toNat, 96)] ∧
      mid.locals = cur.locals ∧ Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      evaluateHOLFiniteState cur
        (.seq (.call (some (none, none)) (ofString "memzero")
          [.op .add [.var .local (ofString "topics"), .const (BitVec.ofNat 64 offset)], .const 12]) cont) =
        evaluateHOLFiniteState mid cont := by
  let dst : ExpHOL 64 := .op .add [.var .local (ofString "topics"), .const (BitVec.ofNat 64 offset)]
  let call : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [dst, .const 12]
  have hleft := transfer_seq_resumes_left cur call cont hr
  have hbound : topics.toNat + 96 ≤ heapLimit := le_trans hin.2 hstep.1.1.1.2.2.1
  have ho : offset ≤ 64 := by rcases hoff with rfl | rfl <;> omega
  have hadd : (topics + BitVec.ofNat 64 offset).toNat = topics.toNat + offset := by
    have hlim : heapLimit < 2 ^ 64 := by decide
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt]
    omega
  obtain ⟨hz, hstep', heff, hl, hout', hbyte'⟩ :=
    transfer_accumulated_memzero_step s cur dst (.const 12)
      (topics + BitVec.ofNat 64 offset) 12 [(topics.toNat, 96)]
      hInv hstep hbe hout hbyte
      (by simp [dst, evalHOLExact, evalListHOLExact, ht, wordOpHOL, wordOp, valueIsWord, valueWord])
      rfl
      (fun _ => ⟨(topics.toNat, 96), by simp, by rw [hadd]; omega, by rw [hadd]; simp; omega⟩)
      (fun i hi => by rcases List.mem_singleton.mp hi with rfl; exact hin) hleft
  let mid := (evaluateHOLFiniteState cur call).2
  have heq : evaluateHOLFiniteState cur (.seq call cont) = evaluateHOLFiniteState mid cont := by
    rw [evaluateHOLFiniteState_seq_line780]
    change (evaluateHOLFiniteState cur call).1 = none at hz
    simp only [hz]
    rfl
  exact ⟨mid, hstep', heff, hl, heq ▸ hr, hout', hbyte', heq⟩

theorem transfer_topic_party_copy_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (topics party : BitVec 64)
    (name : MlS) (offset : Nat) (cont : ProgHOL 64)
    (hoff : offset = 44 ∨ offset = 76)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (ht : cur.locals.lookup (ofString "topics") = some (.val (.word topics)))
    (hparty : cur.locals.lookup name = some (.val (.word party)))
    (hin : Inside (topics.toNat, 96) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.seq (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "topics"), .const (BitVec.ofNat 64 offset)],
          .var .local name, .const 20]) cont)).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid ∧ ByteRegionEffect cur mid [(topics.toNat, 96)] ∧
      mid.locals = cur.locals ∧ Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      evaluateHOLFiniteState cur
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "topics"), .const (BitVec.ofNat 64 offset)],
            .var .local name, .const 20]) cont) = evaluateHOLFiniteState mid cont := by
  let dst : ExpHOL 64 := .op .add [.var .local (ofString "topics"), .const (BitVec.ofNat 64 offset)]
  let call : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy") [dst, .var .local name, .const 20]
  have hleft := transfer_seq_resumes_left cur call cont hr
  have hbound : topics.toNat + 96 ≤ heapLimit := le_trans hin.2 hstep.1.1.1.2.2.1
  have ho : offset ≤ 76 := by rcases hoff with rfl | rfl <;> omega
  have hadd : (topics + BitVec.ofNat 64 offset).toNat = topics.toNat + offset := by
    have hlim : heapLimit < 2 ^ 64 := by decide
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt]
    omega
  obtain ⟨hz, hstep', heff, hl, hout', hbyte'⟩ :=
    transfer_accumulated_memcpy_step s cur dst (.var .local name) (.const 20)
      (topics + BitVec.ofNat 64 offset) party 20 [(topics.toNat, 96)]
      hInv hstep hbe hout hbyte
      (by simp [dst, evalHOLExact, evalListHOLExact, ht, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by simpa [evalHOLExact] using hparty)
      rfl
      (fun _ => ⟨(topics.toNat, 96), by simp, by rw [hadd]; omega, by rw [hadd]; simp; omega⟩)
      (fun i hi => by rcases List.mem_singleton.mp hi with rfl; exact hin) hleft
  let mid := (evaluateHOLFiniteState cur call).2
  have heq : evaluateHOLFiniteState cur (.seq call cont) = evaluateHOLFiniteState mid cont := by
    rw [evaluateHOLFiniteState_seq_line780]
    change (evaluateHOLFiniteState cur call).1 = none at hz
    simp only [hz]
    rfl
  exact ⟨mid, hstep', heff, hl, heq ▸ hr, hout', hbyte', heq⟩

def transferTopicWrites (cont : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "memcpy")
    [.var .local (ofString "topics"), .var .global (ofString "transfer_topic"), .const 32])
  (.seq (.call (some (none, none)) (ofString "memzero")
    [.op .add [.var .local (ofString "topics"), .const 32], .const 12])
  (.seq (.call (some (none, none)) (ofString "memcpy")
    [.op .add [.var .local (ofString "topics"), .const 44], .var .local (ofString "sender"), .const 20])
  (.seq (.call (some (none, none)) (ofString "memzero")
    [.op .add [.var .local (ofString "topics"), .const 64], .const 12])
  (.seq (.call (some (none, none)) (ofString "memcpy")
    [.op .add [.var .local (ofString "topics"), .const 76], .var .local (ofString "recipient"), .const 20]) cont))))

theorem transfer_topic_writes_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (topics topic sender recipient : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (ht : cur.locals.lookup (ofString "topics") = some (.val (.word topics)))
    (hsrc : cur.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hs : cur.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hrc : cur.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (hin : Inside (topics.toNat, 96) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur (transferTopicWrites cont)).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid ∧ ByteRegionEffect cur mid [(topics.toNat, 96)] ∧
      mid.locals = cur.locals ∧ Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      evaluateHOLFiniteState cur (transferTopicWrites cont) = evaluateHOLFiniteState mid cont := by
  unfold transferTopicWrites at hr ⊢
  obtain ⟨m1, st1, ef1, l1, r1, o1, b1, eq1⟩ :=
    transfer_topic_copy_prefix s cur topics topic _ hInv hstep hbe hout hbyte ht hsrc hin hr
  have in1 : Inside (topics.toNat, 96) (globN s "heap_ptr") (globN m1 "heap_ptr") := by
    simpa only [globN, ef1.globals] using hin
  obtain ⟨m2, st2, ef2, l2, r2, o2, b2, eq2⟩ :=
    transfer_topic_padding_prefix s m1 topics 32 _ (Or.inl rfl) hInv st1
      (ef1.be.trans hbe) o1 b1 (l1 ▸ ht) in1 r1
  have ef02 := ef1.trans ef2
  have l02 := l2.trans l1
  have in2 : Inside (topics.toNat, 96) (globN s "heap_ptr") (globN m2 "heap_ptr") := by
    simpa only [globN, ef02.globals] using hin
  obtain ⟨m3, st3, ef3, l3, r3, o3, b3, eq3⟩ :=
    transfer_topic_party_copy_prefix s m2 topics sender (ofString "sender") 44 _ (Or.inl rfl)
      hInv st2 (ef02.be.trans hbe) o2 b2 (l02 ▸ ht) (l02 ▸ hs) in2 r2
  have ef03 := ef02.trans ef3
  have l03 := l3.trans l02
  have in3 : Inside (topics.toNat, 96) (globN s "heap_ptr") (globN m3 "heap_ptr") := by
    simpa only [globN, ef03.globals] using hin
  obtain ⟨m4, st4, ef4, l4, r4, o4, b4, eq4⟩ :=
    transfer_topic_padding_prefix s m3 topics 64 _ (Or.inr rfl) hInv st3
      (ef03.be.trans hbe) o3 b3 (l03 ▸ ht) in3 r3
  have ef04 := ef03.trans ef4
  have l04 := l4.trans l03
  have in4 : Inside (topics.toNat, 96) (globN s "heap_ptr") (globN m4 "heap_ptr") := by
    simpa only [globN, ef04.globals] using hin
  obtain ⟨m5, st5, ef5, l5, r5, o5, b5, eq5⟩ :=
    transfer_topic_party_copy_prefix s m4 topics recipient (ofString "recipient") 76 cont (Or.inr rfl)
      hInv st4 (ef04.be.trans hbe) o4 b4 (l04 ▸ ht) (l04 ▸ hrc) in4 r4
  exact ⟨m5, st5, ef04.trans ef5, l5.trans l04, r5, o5, b5,
    eq1.trans (eq2.trans (eq3.trans (eq4.trans eq5)))⟩

theorem transfer_alloc_topics_writes_prefix {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p topic sender recipient : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (htopic : s.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hsender : s.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hrecipient : s.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (hr : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] (transferTopicWrites cont))).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.locals.lookup (ofString "topics") = some (.val (.word p)) ∧
      globN mid "heap_ptr" = p.toNat + 96 ∧ EvmStepCC ["heap_ptr"] s mid ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] (transferTopicWrites cont))).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] (transferTopicWrites cont))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString "topics", s.locals.lookup (ofString "topics")) } := by
  obtain ⟨allocated, ht, hhp, hw, st, er, es, hm, hb, hl⟩ :=
    transfer_decCall_alloc_exact_spec s (ofString "topics") _ p 96
      (Or.inr (Or.inl rfl)) hInv hp hr
  have hp0 : globN s "heap_ptr" = p.toNat := by simp [globN, hp]
  have hin : Inside (p.toNat, 96) (globN s "heap_ptr") (globN allocated "heap_ptr") :=
    ⟨by rw [hp0], by rw [hhp]⟩
  obtain ⟨mid, st', ef, loc, resum, out, bytes, eq⟩ :=
    transfer_topic_writes_prefix s allocated p topic sender recipient cont hInv st hb
      (fun _ _ => congrFun hm _) (fun _ _ _ => by simp only [memB, hm, hb]) ht
      ((st.1.2.2.1 _ (by decide)).symm.trans htopic)
      ((hl _ (by decide)).trans hsender)
      ((hl _ (by decide)).trans hrecipient) hin (er ▸ hr)
  refine ⟨mid, loc ▸ ht, ?_, st', resum, ?_, ?_⟩
  · simpa only [globN, ef.globals] using hhp
  · exact er.trans (congrArg Prod.fst eq)
  · exact es.trans (congrArg (fun out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F =>
      { out.2 with locals := (HolFiniteMapExact.resVarEq out.2.locals
        (ofString "topics", s.locals.lookup (ofString "topics"))) }) eq)

theorem transfer_topics_alloc_prefix {F : Type}
    (s : PanSemStateFiniteExact 64 F) (logp p : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hlog : s.locals.lookup (ofString "log") = some (.val (.word logp)))
    (haddr : memW s logp.toNat = globN s "vm_system_address")
    (hwords : WordsOK s (logp.toNat, 40))
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] cont)).1) :
    ∃ next : PanSemStateFiniteExact 64 F,
      next.locals.lookup (ofString "topics") = some (.val (.word p)) ∧
      next.locals.lookup (ofString "log") = some (.val (.word logp)) ∧
      globN next "heap_ptr" = p.toNat + 96 ∧
      memW next logp.toNat = globN next "vm_system_address" ∧
      WordsOK next (logp.toNat, 40) ∧ WordsOK next (p.toNat, 96) ∧
      EvmStepCC ["heap_ptr"] s next ∧
      Resumes (evaluateHOLFiniteState next cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] cont)).1 =
        (evaluateHOLFiniteState next cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] cont)).2 =
        { (evaluateHOLFiniteState next cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState next cont).2.locals
            (ofString "topics", s.locals.lookup (ofString "topics")) } := by
  obtain ⟨next, ht, hhp, htw, hstep, hr, hs, hm, hb, hl⟩ :=
    transfer_decCall_alloc_exact_spec s (ofString "topics") cont p 96
      (Or.inr (Or.inl rfl)) hInv hp hres
  refine ⟨next, ht, (hl _ (by decide)).trans hlog, hhp, ?_, ?_, htw,
    hstep, hr ▸ hres, hr, hs⟩
  · have hg := hstep.1.2.2.1 (ofString "vm_system_address") (by decide)
    simpa only [memW, hm, globN, hg] using haddr
  · refine ⟨hwords.1, hwords.2.1, ?_⟩
    intro k hk
    obtain ⟨w, ha, hw⟩ := hwords.2.2 k hk
    refine ⟨w, ?_, hm ▸ hw⟩
    rw [hstep.1.1.1.1.memaddrs, ← hInv.1.1.memaddrs]
    exact ha

theorem transfer_alloc_topics_writes_locals_prefix {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p topic sender recipient : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (htopic : s.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hsender : s.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hrecipient : s.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (hr : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] (transferTopicWrites cont))).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.locals.lookup (ofString "topics") = some (.val (.word p)) ∧
      globN mid "heap_ptr" = p.toNat + 96 ∧ EvmStepCC ["heap_ptr"] s mid ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] (transferTopicWrites cont))).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] (transferTopicWrites cont))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString "topics", s.locals.lookup (ofString "topics")) } ∧
      (∀ k, k ≠ ofString "topics" → mid.locals.lookup k = s.locals.lookup k) ∧
      mid.be = s.be ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) := by
  obtain ⟨allocated, ht, hhp, hw, st, er, es, hm, hb, hl⟩ :=
    transfer_decCall_alloc_exact_spec s (ofString "topics") _ p 96
      (Or.inr (Or.inl rfl)) hInv hp hr
  have hp0 : globN s "heap_ptr" = p.toNat := by simp [globN, hp]
  have hin : Inside (p.toNat, 96) (globN s "heap_ptr") (globN allocated "heap_ptr") :=
    ⟨by rw [hp0], by rw [hhp]⟩
  obtain ⟨mid, st', ef, loc, resum, out, bytes, eq⟩ :=
    transfer_topic_writes_prefix s allocated p topic sender recipient cont hInv st hb
      (fun _ _ => congrFun hm _) (fun _ _ _ => by simp only [memB, hm, hb]) ht
      ((st.1.2.2.1 _ (by decide)).symm.trans htopic)
      ((hl _ (by decide)).trans hsender)
      ((hl _ (by decide)).trans hrecipient) hin (er ▸ hr)
  refine ⟨mid, loc ▸ ht, ?_, st', resum, ?_, ?_, ?_, ef.be.trans hb, out, bytes⟩
  · simpa only [globN, ef.globals] using hhp
  · exact er.trans (congrArg Prod.fst eq)
  · exact es.trans (congrArg (fun out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F =>
      { out.2 with locals := (HolFiniteMapExact.resVarEq out.2.locals
        (ofString "topics", s.locals.lookup (ofString "topics"))) }) eq)
  · intro k hk
    rw [loc]
    exact hl k hk

theorem transfer_alloc_topics_data_prefix {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p topic sender recipient : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (htopic : s.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hsender : s.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hrecipient : s.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (hr : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
        (transferTopicWrites (.decCall (ofString "data") .one (ofString "alloc") [.const 32] cont)))).1) :
    ∃ (mid : PanSemStateFiniteExact 64 F) (data : BitVec 64),
      mid.locals.lookup (ofString "topics") = some (.val (.word p)) ∧
      mid.locals.lookup (ofString "data") = some (.val (.word data)) ∧
      data.toNat = p.toNat + 96 ∧ globN mid "heap_ptr" = data.toNat + 32 ∧
      WordsOK mid (data.toNat, 32) ∧ EvmStepCC ["heap_ptr"] s mid ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
          (transferTopicWrites (.decCall (ofString "data") .one (ofString "alloc") [.const 32] cont)))).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
          (transferTopicWrites (.decCall (ofString "data") .one (ofString "alloc") [.const 32] cont)))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
              (ofString "data", s.locals.lookup (ofString "data")))
            (ofString "topics", s.locals.lookup (ofString "topics")) } := by
  obtain ⟨topicsState, ht, hhp, st, resum, er, es, hlocals, hbe, hout, hbyte⟩ :=
    transfer_alloc_topics_writes_locals_prefix s p topic sender recipient _ hInv hp htopic hsender hrecipient hr
  obtain ⟨data, hd⟩ := globalWord_of_globN_pos topicsState "heap_ptr" (by rw [hhp]; omega)
  have hdNat : data.toNat = p.toNat + 96 := by
    have hg : globN topicsState "heap_ptr" = data.toNat := by
      change topicsState.globals.lookup (ofString "heap_ptr") = _ at hd
      simp [globN, hd]
    exact hg.symm.trans hhp
  obtain ⟨mid, hdata, hheap, hw, st', er', es', hm, hb, hl⟩ :=
    transfer_decCall_alloc_exact_spec topicsState (ofString "data") cont data 32
      (Or.inr (Or.inr rfl)) st.1.1 hd resum
  have hboth : EvmStepCC ["heap_ptr"] s mid := by
    refine ⟨⟨st'.1.1, le_trans st.1.2.1 st'.1.2.1,
      fun k hk => (st.1.2.2.1 k hk).trans (st'.1.2.2.1 k hk),
      st'.1.2.2.2.trans st.1.2.2.2⟩, ?_⟩
    intro ec hec
    obtain ⟨a, b, c, d⟩ := st.2 ec hec
    obtain ⟨a', b', c', d'⟩ := st'.2 ec (st.1.2.2.2.symm ▸ hec)
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩
  refine ⟨mid, data, (hl _ (by decide)).trans ht, hdata, hdNat, hheap, hw,
    hboth, er' ▸ resum, er.trans er', ?_⟩
  have he : (evaluateHOLFiniteState topicsState
      (.decCall (ofString "data") .one (ofString "alloc") [.const 32] cont)).2 =
      { (evaluateHOLFiniteState mid cont).2 with
        locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
          (ofString "data", topicsState.locals.lookup (ofString "data")) } := es'
  exact es.trans ((congrArg (fun out : PanSemStateFiniteExact 64 F =>
    { out with locals := (HolFiniteMapExact.resVarEq out.locals
      (ofString "topics", s.locals.lookup (ofString "topics"))) }) he).trans (by
        rw [hlocals _ (by decide)]))

theorem transfer_accumulated_u256_to_be32_step {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (amount dst : ExpHOL 64)
    (av : ValueHOL 64) (dw : BitVec 64) (Rl : List Ivl)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (ha : @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) amount = some av)
    (hd : @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) dst = some (.val (.word dw)))
    (halign : dw.toNat % 8 = 0)
    (hsub : ∃ i ∈ Rl, i.1 ≤ dw.toNat ∧ dw.toNat + 32 ≤ i.1 + i.2)
    (hin : ∀ i ∈ Rl, Inside i (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hz : (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "u256_to_be32") [amount, dst])).1 = none) :
    let out := evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "u256_to_be32") [amount, dst])
    EvmStepCC ["heap_ptr"] s out.2 ∧ ByteRegionEffect cur out.2 Rl ∧
      out.2.locals = cur.locals ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → out.2.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN out.2 "heap_ptr") → memB out.2 b = memB s b) := by
  dsimp only
  obtain ⟨eff, hl⟩ := eval_call_u256_to_be32_aligned_bre cur amount dst av dw Rl
    hstep.1.1.1.1.code hstep.1.1.1.1.memaddrs ha hd halign hsub hz
  obtain ⟨step, out, bytes⟩ :=
    evmStepCC_of_accumulated_heap_effect hInv hstep hbe hout hbyte eff hin
  exact ⟨step, eff, hl, out, bytes⟩

theorem transfer_data_write_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (data : BitVec 64)
    (av : ValueHOL 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (ha : cur.locals.lookup (ofString "amount") = some av)
    (hd : cur.locals.lookup (ofString "data") = some (.val (.word data)))
    (halign : data.toNat % 8 = 0)
    (hin : Inside (data.toNat, 32) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.seq (.call (some (none, none)) (ofString "u256_to_be32")
        [.var .local (ofString "amount"), .var .local (ofString "data")]) cont)).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid ∧ ByteRegionEffect cur mid [(data.toNat, 32)] ∧
      mid.locals = cur.locals ∧ Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      evaluateHOLFiniteState cur
        (.seq (.call (some (none, none)) (ofString "u256_to_be32")
          [.var .local (ofString "amount"), .var .local (ofString "data")]) cont) =
        evaluateHOLFiniteState mid cont := by
  let call : ProgHOL 64 := .call (some (none, none)) (ofString "u256_to_be32")
    [.var .local (ofString "amount"), .var .local (ofString "data")]
  have hz : (evaluateHOLFiniteState cur call).1 = none := by
    rcases transfer_seq_resumes_left cur call cont hr with hz | resum
    · exact hz
    · exact False.elim (transfer_u256_to_be32_call_no_resumes cur _ _ hstep.1.1.1.1.code resum)
  obtain ⟨step, eff, hl, out, bytes⟩ := transfer_accumulated_u256_to_be32_step
    s cur (.var .local (ofString "amount")) (.var .local (ofString "data")) av data
    [(data.toNat, 32)] hInv hstep hbe hout hbyte
    (by simpa only [evalHOLExact] using ha) (by simpa only [evalHOLExact] using hd)
    halign ⟨(data.toNat, 32), by simp, le_refl _, le_refl _⟩
    (fun i hi => by rcases List.mem_singleton.mp hi with rfl; exact hin) hz
  let mid := (evaluateHOLFiniteState cur call).2
  have eq : evaluateHOLFiniteState cur (.seq call cont) = evaluateHOLFiniteState mid cont := by
    rw [evaluateHOLFiniteState_seq_line780]
    simp only [hz]
    rfl
  exact ⟨mid, step, eff, hl, eq ▸ hr, out, bytes, eq⟩

theorem transfer_accumulated_store_step {F : Type}
    {s cur post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hrun : evaluateHOLFiniteState cur (.store dst val) = (none, post))
    (hword : ∀ v, @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) val = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hdst : ∀ addr : BitVec 64, @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) dst = some (.val (.word addr)) →
      cur.memaddrs addr → ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ i.1 + i.2)
    (hin : ∀ i ∈ Rl, Inside i (globN s "heap_ptr") (globN cur "heap_ptr")) :
    EvmStepCC ["heap_ptr"] s post ∧ ByteRegionEffect cur post Rl ∧ post.locals = cur.locals ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) := by
  obtain ⟨eff, hl⟩ := m23_bre_of_store_word hstep.1.1.1.1.memaddrs hrun hword hdst
  obtain ⟨step, out, bytes⟩ :=
    evmStepCC_of_accumulated_heap_effect hInv hstep hbe hout hbyte eff hin
  exact ⟨step, eff, hl, out, bytes⟩

theorem transfer_log_field_store_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (logw value addr : BitVec 64)
    (off : Nat) (valueExp : ExpHOL 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hlog : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hv : @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) valueExp = some (.val (.word value)))
    (haddr : addr = logw + BitVec.ofNat 64 off)
    (hnat : addr.toNat = logw.toNat + off) (hoff : off + 8 ≤ 40)
    (hdom : cur.memaddrs addr)
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.seq (.store (.op .add [.var .local (ofString "log"), .const (BitVec.ofNat 64 off)]) valueExp) cont)).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid ∧ ByteRegionEffect cur mid [(logw.toNat, 40)] ∧
      mid.locals = cur.locals ∧ memW mid (logw.toNat + off) = value.toNat ∧
      (∀ b : Nat, b < 2 ^ 64 → b ≠ logw.toNat + off → memW mid b = memW cur b) ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      evaluateHOLFiniteState cur
        (.seq (.store (.op .add [.var .local (ofString "log"), .const (BitVec.ofNat 64 off)]) valueExp) cont) =
        evaluateHOLFiniteState mid cont := by
  let dst : ExpHOL 64 := .op .add [.var .local (ofString "log"), .const (BitVec.ofNat 64 off)]
  have hd : @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) dst = some (.val (.word addr)) := by
    simp [dst, evalHOLExact, evalListHOLExact, hlog, wordOpHOL, wordOp,
      valueIsWord, valueWord, haddr]
  let mid : PanSemStateFiniteExact 64 F :=
    {cur with memory := fun a => if a = addr then .word value else cur.memory a}
  have run : evaluateHOLFiniteState cur (.store dst valueExp) = (none, mid) := by
    simp [evaluateHOLFiniteState_store, hd, hv, flattenHOL, panMemStoresHOL,
      panMemStoreHOL, hdom, mid]
  obtain ⟨step, eff, hl, out, bytes⟩ := transfer_accumulated_store_step hInv hstep hbe hout hbyte
    (Rl := [(logw.toNat, 40)]) run
    (fun v he => ⟨value, Option.some.inj (he.symm.trans hv)⟩)
    (fun a he _ => by
      have heq : a = addr := by simpa only [hd, Option.some.injEq, ValueHOL.val.injEq,
        HolWordLab.word.injEq] using he.symm
      subst a
      exact ⟨(logw.toNat, 40), by simp, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    (fun i hi => by rcases List.mem_singleton.mp hi with rfl; exact hin)
  have eq : evaluateHOLFiniteState cur (.seq (.store dst valueExp) cont) =
      evaluateHOLFiniteState mid cont := by
    rw [evaluateHOLFiniteState_seq_line780, run]
  refine ⟨mid, step, eff, hl, ?_, ?_, eq ▸ hr, out, bytes, eq⟩
  · have hword : BitVec.ofNat 64 (logw.toNat + off) = addr := by rw [← hnat]; simp
    simp [memW, mid, hword]
  · intro b hb hne
    have haddrNe : BitVec.ofNat 64 b ≠ addr := by
      intro he
      have ht := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, hnat] at ht
      exact hne ht
    simp [memW, mid, haddrNe]

theorem transfer_alloc_data_write_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (data : BitVec 64)
    (av : ValueHOL 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (ha : cur.locals.lookup (ofString "amount") = some av)
    (hp : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word data)))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.decCall (ofString "data") .one (ofString "alloc") [.const 32]
        (.seq (.call (some (none, none)) (ofString "u256_to_be32")
          [.var .local (ofString "amount"), .var .local (ofString "data")]) cont))).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.locals.lookup (ofString "data") = some (.val (.word data)) ∧
      globN mid "heap_ptr" = data.toNat + 32 ∧
      EvmStepCC ["heap_ptr"] s mid ∧ Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      (∀ k, k ≠ ofString "data" → mid.locals.lookup k = cur.locals.lookup k) ∧
      mid.be = s.be ∧
      (∀ b : Nat, b < 2 ^ 64 → b + 8 ≤ data.toNat → memW mid b = memW cur b) ∧
      (evaluateHOLFiniteState cur
        (.decCall (ofString "data") .one (ofString "alloc") [.const 32]
          (.seq (.call (some (none, none)) (ofString "u256_to_be32")
            [.var .local (ofString "amount"), .var .local (ofString "data")]) cont))).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState cur
        (.decCall (ofString "data") .one (ofString "alloc") [.const 32]
          (.seq (.call (some (none, none)) (ofString "u256_to_be32")
            [.var .local (ofString "amount"), .var .local (ofString "data")]) cont))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString "data", cur.locals.lookup (ofString "data")) } := by
  obtain ⟨allocated, hd, hheap, hw, st, er, es, hm, hb, hl⟩ :=
    transfer_decCall_alloc_exact_spec cur (ofString "data") _ data 32
      (Or.inr (Or.inr rfl)) hstep.1.1 hp hr
  have hboth : EvmStepCC ["heap_ptr"] s allocated := by
    refine ⟨⟨st.1.1, le_trans hstep.1.2.1 st.1.2.1,
      fun k hk => (hstep.1.2.2.1 k hk).trans (st.1.2.2.1 k hk),
      st.1.2.2.2.trans hstep.1.2.2.2⟩, ?_⟩
    intro ec hec
    obtain ⟨a, b, c, d⟩ := hstep.2 ec hec
    obtain ⟨a', b', c', d'⟩ := st.2 ec (hstep.1.2.2.2.symm ▸ hec)
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩
  have hpNat : globN cur "heap_ptr" = data.toNat := by simp [globN, hp]
  have hbAllocated : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN allocated "heap_ptr") →
      memB allocated b = memB s b := by
    intro b hb64 hn
    rw [show memB allocated b = memB cur b by simp only [memB, hm, hb]]
    apply hbyte b hb64
    have hmono := st.1.2.1
    omega
  obtain ⟨mid, step, eff, loc, resum, out, bytes, eq⟩ :=
    transfer_data_write_prefix s allocated data av cont hInv hboth (hb.trans hbe)
      (fun a hn => (congrFun hm a).trans (hout a hn)) hbAllocated
      ((hl _ (by decide)).trans ha) hd hw.1
      ⟨by rw [← hpNat]; exact hstep.1.2.1, by rw [hheap]⟩ (er ▸ hr)
  refine ⟨mid, loc ▸ hd, ?_, step, resum, out, bytes, ?_, eff.be.trans (hb.trans hbe),
    ?_, er.trans (congrArg Prod.fst eq), ?_⟩
  · simpa only [globN, eff.globals] using hheap
  · intro k hk
    rw [loc]
    exact hl k hk
  · intro b hb64 hsep
    have ha : (BitVec.ofNat 64 b).toNat = b := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64]
    have hm' := eff.cell_frame (BitVec.ofNat 64 b) (by
      intro i hi
      rcases List.mem_singleton.mp hi with rfl
      rw [ha]
      simp only [CellHits]
      omega)
    simp only [memW, hm', hm]
  · exact es.trans (congrArg (fun out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F =>
      { out.2 with locals := (HolFiniteMapExact.resVarEq out.2.locals
        (ofString "data", cur.locals.lookup (ofString "data"))) }) eq)

theorem transfer_log_field_address {F : Type}
    (cur : PanSemStateFiniteExact 64 F) (logw : BitVec 64) (off : Nat)
    (hwords : WordsOK cur (logw.toNat, 40))
    (hma : cur.memaddrs = ordinaryDomain)
    (hoff : off = 8 ∨ off = 16 ∨ off = 24 ∨ off = 32) :
    (logw + BitVec.ofNat 64 off).toNat = logw.toNat + off ∧
      cur.memaddrs (logw + BitVec.ofNat 64 off) ∧ off + 8 ≤ 40 := by
  have h0 := hwords.2.2 0 (by omega)
  obtain ⟨w, hd0, _⟩ := h0
  have hlogBound : logw.toNat < heapEnd := by
    rw [Nat.add_zero] at hd0
    rw [hma, Wave8Contracts.M08.ordinaryDomain_iff] at hd0
    simpa using hd0.2.2
  have hoffBound : off ≤ 32 := by rcases hoff with rfl | rfl | rfl | rfl <;> omega
  have hlim : heapEnd + 32 < 2 ^ 64 := by
    rw [R11Shards.heapEnd_val]
    decide
  have hn : (logw + BitVec.ofNat 64 off).toNat = logw.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have heq : logw + BitVec.ofNat 64 off = BitVec.ofNat 64 (logw.toNat + off) := by
    apply BitVec.eq_of_toNat_eq
    rw [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hn, ?_, by omega⟩
  rw [heq]
  rcases hoff with rfl | rfl | rfl | rfl
  · obtain ⟨_, hd, _⟩ := hwords.2.2 1 (by omega)
    exact hd
  · obtain ⟨_, hd, _⟩ := hwords.2.2 2 (by omega)
    exact hd
  · obtain ⟨_, hd, _⟩ := hwords.2.2 3 (by omega)
    exact hd
  · obtain ⟨_, hd, _⟩ := hwords.2.2 4 (by omega)
    exact hd

theorem transfer_log_field_store_words_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (logw value : BitVec 64)
    (off : Nat) (valueExp : ExpHOL 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hlog : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hv : @evalHOLExact 64 F _ cur.toExact
      (fun a => Classical.propDecidable (cur.memaddrs a)) valueExp = some (.val (.word value)))
    (hwords : WordsOK cur (logw.toNat, 40))
    (hoff : off = 8 ∨ off = 16 ∨ off = 24 ∨ off = 32)
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.seq (.store (.op .add [.var .local (ofString "log"), .const (BitVec.ofNat 64 off)]) valueExp) cont)).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid ∧ ByteRegionEffect cur mid [(logw.toNat, 40)] ∧
      mid.locals = cur.locals ∧ memW mid (logw.toNat + off) = value.toNat ∧
      WordsOK mid (logw.toNat, 40) ∧
      (∀ b : Nat, b < 2 ^ 64 → b ≠ logw.toNat + off → memW mid b = memW cur b) ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      evaluateHOLFiniteState cur
        (.seq (.store (.op .add [.var .local (ofString "log"), .const (BitVec.ofNat 64 off)]) valueExp) cont) =
        evaluateHOLFiniteState mid cont := by
  obtain ⟨hn, hd, ho⟩ := transfer_log_field_address cur logw off hwords hstep.1.1.1.1.memaddrs hoff
  obtain ⟨mid, step, eff, hl, hw, frame, resum, out, bytes, eq⟩ :=
    transfer_log_field_store_prefix s cur logw value _ off valueExp cont hInv hstep
      hbe hout hbyte hlog hv rfl hn ho hd hin hr
  refine ⟨mid, step, eff, hl, hw, ?_, frame, resum, out, bytes, eq⟩
  apply wordsOK_of_inside_heap _ step.1.1.1.1.memaddrs
  · exact hwords.1
  · decide
  · exact le_trans hInv.1.2.1 hin.1
  · have hlim := hstep.1.1.1.2.2.1
    have hheap : globN cur "heap_ptr" ≤ heapLimit := hlim
    have hle := hin.2
    have : heapLimit ≤ heapEnd := by decide
    omega

def transferRecordWrites (cont : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "log"), .const 8]) (.var .local (ofString "topics")))
  (.seq (.store (.op .add [.var .local (ofString "log"), .const 16]) (.const 3))
  (.seq (.store (.op .add [.var .local (ofString "log"), .const 24]) (.var .local (ofString "data")))
  (.seq (.store (.op .add [.var .local (ofString "log"), .const 32]) (.const 32)) cont)))

theorem transfer_record_writes_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (logw topics data : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hl : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (ht : cur.locals.lookup (ofString "topics") = some (.val (.word topics)))
    (hd : cur.locals.lookup (ofString "data") = some (.val (.word data)))
    (hw : WordsOK cur (logw.toNat, 40))
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur (transferRecordWrites cont)).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid ∧ ByteRegionEffect cur mid [(logw.toNat, 40)] ∧
      mid.locals = cur.locals ∧ WordsOK mid (logw.toNat, 40) ∧
      memW mid logw.toNat = memW cur logw.toNat ∧
      memW mid (logw.toNat + 8) = topics.toNat ∧
      memW mid (logw.toNat + 16) = 3 ∧
      memW mid (logw.toNat + 24) = data.toNat ∧
      memW mid (logw.toNat + 32) = 32 ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      evaluateHOLFiniteState cur (transferRecordWrites cont) = evaluateHOLFiniteState mid cont := by
  have hbound : logw.toNat + 40 < 2 ^ 64 := by
    have hlim := hstep.1.1.1.2.2.1
    have hle := hin.2
    have h64 : heapLimit < 2 ^ 64 := by decide
    omega
  unfold transferRecordWrites at hr ⊢
  obtain ⟨m1, st1, ef1, l1, w1, ws1, fr1, r1, o1, b1, eq1⟩ :=
    transfer_log_field_store_words_prefix s cur logw topics 8 _ _ hInv hstep hbe hout hbyte
      hl (by simpa only [evalHOLExact] using ht) hw (Or.inl rfl) hin hr
  have in1 : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN m1 "heap_ptr") := by
    simpa only [globN, ef1.globals] using hin
  obtain ⟨m2, st2, ef2, l2, w2, ws2, fr2, r2, o2, b2, eq2⟩ :=
    transfer_log_field_store_words_prefix s m1 logw 3 16 _ _ hInv st1 (ef1.be.trans hbe) o1 b1
      (l1 ▸ hl) rfl ws1 (Or.inr (Or.inl rfl)) in1 r1
  have ef02 := ef1.trans ef2
  have l02 := l2.trans l1
  have in2 : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN m2 "heap_ptr") := by
    simpa only [globN, ef02.globals] using hin
  obtain ⟨m3, st3, ef3, l3, w3, ws3, fr3, r3, o3, b3, eq3⟩ :=
    transfer_log_field_store_words_prefix s m2 logw data 24 _ _ hInv st2 (ef02.be.trans hbe) o2 b2
      (l02 ▸ hl) (by simpa only [evalHOLExact, l02] using hd) ws2
      (Or.inr (Or.inr (Or.inl rfl))) in2 r2
  have ef03 := ef02.trans ef3
  have l03 := l3.trans l02
  have in3 : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN m3 "heap_ptr") := by
    simpa only [globN, ef03.globals] using hin
  obtain ⟨m4, st4, ef4, l4, w4, ws4, fr4, r4, o4, b4, eq4⟩ :=
    transfer_log_field_store_words_prefix s m3 logw 32 32 _ cont hInv st3 (ef03.be.trans hbe) o3 b3
      (l03 ▸ hl) rfl ws3 (Or.inr (Or.inr (Or.inr rfl))) in3 r3
  refine ⟨m4, st4, ef03.trans ef4, l4.trans l03, ws4, ?_, ?_, ?_, ?_, w4,
    r4, o4, b4, eq1.trans (eq2.trans (eq3.trans eq4))⟩
  · rw [fr4 _ (by omega) (by omega), fr3 _ (by omega) (by omega),
      fr2 _ (by omega) (by omega), fr1 _ (by omega) (by omega)]
  · rw [fr4 _ (by omega) (by omega), fr3 _ (by omega) (by omega),
      fr2 _ (by omega) (by omega)]
    exact w1
  · rw [fr4 _ (by omega) (by omega), fr3 _ (by omega) (by omega)]
    exact w2
  · rw [fr4 _ (by omega) (by omega)]
    exact w3

theorem transfer_record_writes_step {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (logw topics data : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hl : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (ht : cur.locals.lookup (ofString "topics") = some (.val (.word topics)))
    (hd : cur.locals.lookup (ofString "data") = some (.val (.word data)))
    (hw : WordsOK cur (logw.toNat, 40))
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur (transferRecordWrites cont)).1)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid → ByteRegionEffect cur mid [(logw.toNat, 40)] →
      mid.locals = cur.locals → WordsOK mid (logw.toNat, 40) →
      memW mid logw.toNat = memW cur logw.toNat →
      memW mid (logw.toNat + 8) = topics.toNat →
      memW mid (logw.toNat + 16) = 3 →
      memW mid (logw.toNat + 24) = data.toNat →
      memW mid (logw.toNat + 32) = 32 →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      EvmStepCC ["heap_ptr"] mid (evaluateHOLFiniteState mid cont).2) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState cur (transferRecordWrites cont)).2 := by
  obtain ⟨mid, step, eff, loc, words, addr, tp, tn, dp, dn, resum, out, bytes, eq⟩ :=
    transfer_record_writes_prefix s cur logw topics data cont hInv hstep hbe hout hbyte hl ht hd hw hin hr
  have tail := hcont mid step eff loc words addr tp tn dp dn resum
  rw [eq]
  refine ⟨⟨tail.1.1, le_trans step.1.2.1 tail.1.2.1,
    fun k hk => (step.1.2.2.1 k hk).trans (tail.1.2.2.1 k hk),
    tail.1.2.2.2.trans step.1.2.2.2⟩, ?_⟩
  intro ec hec
  obtain ⟨a, b, c, d⟩ := step.2 ec hec
  obtain ⟨a', b', c', d'⟩ := tail.2 ec (step.1.2.2.2.symm ▸ hec)
  exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩

theorem transfer_record_append_tail_step {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (evw logw topics data : BitVec 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hl : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (ht : cur.locals.lookup (ofString "topics") = some (.val (.word topics)))
    (hd : cur.locals.lookup (ofString "data") = some (.val (.word data)))
    (hev : cur.globals.lookup (ofString "ev") = some (.val (.word evw)))
    (hw : WordsOK cur (logw.toNat, 40))
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hsys : Inside (globN cur "vm_system_address", 20) sourceBase (globN cur "heap_ptr"))
    (htop : Inside (topics.toNat, 96) sourceBase (globN cur "heap_ptr"))
    (hdata : Inside (data.toNat, 32) sourceBase (globN cur "heap_ptr"))
    (haddr : memW cur logw.toNat = globN cur "vm_system_address")
    (hlt : logw.toNat + 40 ≤ topics.toNat) (htd : topics.toNat + 96 ≤ data.toNat)
    (hdisj : ∀ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid → ByteRegionEffect cur mid [(logw.toNat, 40)] →
      ∀ x ∈ [(logw.toNat, 40), (topics.toNat, 96), (data.toNat, 32)],
      (∀ t, ∀ S0, TablesTyped mid S0 → t ∈ S0 → ∀ i ∈ htabFootprint mid t, Disj x i) ∧
      (∀ j ∈ fixedObjects mid, Disj x j) ∧
      (∀ ec ∈ evmChain mid, ∀ o ∈ frameObjects mid ec, Disj x o) ∧
      (∀ S0 Nd0, TriesTypedWith mid S0 Nd0 → ∀ j ∈ nodeExtents mid Nd0, Disj x j) ∧
      (∀ ec ∈ evmChain mid, Disj x (memW mid (ec.1 + 112), 176)))
    (hr : Resumes (evaluateHOLFiniteState cur
      (transferRecordWrites (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")]) (.return (.const 0))))).1) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState cur
      (transferRecordWrites (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")]) (.return (.const 0))))).2 := by
  apply transfer_record_writes_step s cur logw topics data _ hInv hstep hbe hout hbyte hl ht hd hw hin hr
  intro mid step eff loc words addr tp tn dp dn resum
  have g (name : String) : globN mid name = globN cur name := by simp only [globN, eff.globals]
  have hret : ∃ v, (evaluateHOLFiniteState mid
      (.seq (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")]) (.return (.const 0)))).1 =
        some (.returned v) := by
    exact transfer_log_append_tail_resumes_returned mid step.1.1.1.1.code resum
  apply transfer_log_append_tail_step mid evw logw topics.toNat data.toNat step.1.1
    (by simp [globN, eff.globals, hev]) words
    ⟨le_trans hInv.1.2.1 hin.1, by simpa only [g] using hin.2⟩
    (by simpa only [g] using hsys) (by simpa only [g] using htop)
    (by simpa only [g] using hdata) (by rw [addr, haddr, g]) tp tn dp dn hlt htd
    (by rw [logOwnedIvls_of_transfer (addr.trans haddr |>.trans (g _).symm) tp tn dp dn];
        exact hdisj mid step eff)
    (by simpa only [evalHOLExact, eff.globals] using hev)
    (by simpa only [evalHOLExact, loc] using hl) hret

def transferRecordPairWrites (off : Nat) (name : MlS) (count : BitVec 64)
    (cont : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "log"), .const (BitVec.ofNat 64 off)]) (.var .local name))
  (.seq (.store (.op .add [.var .local (ofString "log"), .const (BitVec.ofNat 64 (off + 8))]) (.const count)) cont)

theorem transfer_record_pair_writes_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (logw ptr count : BitVec 64)
    (off : Nat) (name : MlS) (cont : ProgHOL 64)
    (hoff : off = 8 ∨ off = 24)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hl : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hp : cur.locals.lookup name = some (.val (.word ptr)))
    (hw : WordsOK cur (logw.toNat, 40))
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur (transferRecordPairWrites off name count cont)).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid ∧ ByteRegionEffect cur mid [(logw.toNat, 40)] ∧
      mid.locals = cur.locals ∧ WordsOK mid (logw.toNat, 40) ∧
      memW mid (logw.toNat + off) = ptr.toNat ∧
      memW mid (logw.toNat + (off + 8)) = count.toNat ∧
      (∀ b : Nat, b < 2 ^ 64 → b ≠ logw.toNat + off → b ≠ logw.toNat + (off + 8) →
        memW mid b = memW cur b) ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      evaluateHOLFiniteState cur (transferRecordPairWrites off name count cont) =
        evaluateHOLFiniteState mid cont := by
  have ho : off = 8 ∨ off = 16 ∨ off = 24 ∨ off = 32 := by
    rcases hoff with rfl | rfl <;> simp
  have ho' : off + 8 = 8 ∨ off + 8 = 16 ∨ off + 8 = 24 ∨ off + 8 = 32 := by
    rcases hoff with rfl | rfl <;> simp
  have hbound : logw.toNat + off < 2 ^ 64 := by
    have hlim := hstep.1.1.1.2.2.1
    have hle := hin.2
    have h64 : heapLimit < 2 ^ 64 := by decide
    rcases hoff with rfl | rfl <;> omega
  unfold transferRecordPairWrites at hr ⊢
  obtain ⟨m1, st1, ef1, l1, w1, ws1, fr1, r1, o1, b1, eq1⟩ :=
    transfer_log_field_store_words_prefix s cur logw ptr off _ _ hInv hstep hbe hout hbyte
      hl (by simpa only [evalHOLExact] using hp) hw ho hin hr
  have in1 : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN m1 "heap_ptr") := by
    simpa only [globN, ef1.globals] using hin
  obtain ⟨m2, st2, ef2, l2, w2, ws2, fr2, r2, o2, b2, eq2⟩ :=
    transfer_log_field_store_words_prefix s m1 logw count (off + 8) _ cont hInv st1
      (ef1.be.trans hbe) o1 b1 (l1 ▸ hl) rfl ws1 ho' in1 r1
  refine ⟨m2, st2, ef1.trans ef2, l2.trans l1, ws2, ?_, w2, ?_, r2, o2, b2, eq1.trans eq2⟩
  · rw [fr2 _ hbound (by omega)]
    exact w1
  · intro b hb hn hn'
    rw [fr2 b hb hn', fr1 b hb hn]

theorem transfer_alloc_data_record_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (data logw : BitVec 64)
    (av : ValueHOL 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (ha : cur.locals.lookup (ofString "amount") = some av)
    (hl : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hw : WordsOK cur (logw.toNat, 40))
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hp : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word data)))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.decCall (ofString "data") .one (ofString "alloc") [.const 32]
        (.seq (.call (some (none, none)) (ofString "u256_to_be32")
          [.var .local (ofString "amount"), .var .local (ofString "data")])
          (transferRecordPairWrites 24 (ofString "data") 32 cont)))).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.locals.lookup (ofString "data") = some (.val (.word data)) ∧
      mid.locals.lookup (ofString "log") = some (.val (.word logw)) ∧
      globN mid "heap_ptr" = data.toNat + 32 ∧ EvmStepCC ["heap_ptr"] s mid ∧
      mid.globals.lookup (ofString "ev") = cur.globals.lookup (ofString "ev") ∧
      globN mid "vm_system_address" = globN cur "vm_system_address" ∧
      WordsOK mid (logw.toNat, 40) ∧
      memW mid (logw.toNat + 24) = data.toNat ∧ memW mid (logw.toNat + 32) = 32 ∧
      (∀ b : Nat, b < 2 ^ 64 → b + 8 ≤ data.toNat →
        b ≠ logw.toNat + 24 → b ≠ logw.toNat + 32 → memW mid b = memW cur b) ∧
      mid.be = s.be ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState cur
        (.decCall (ofString "data") .one (ofString "alloc") [.const 32]
          (.seq (.call (some (none, none)) (ofString "u256_to_be32")
            [.var .local (ofString "amount"), .var .local (ofString "data")])
            (transferRecordPairWrites 24 (ofString "data") 32 cont)))).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState cur
        (.decCall (ofString "data") .one (ofString "alloc") [.const 32]
          (.seq (.call (some (none, none)) (ofString "u256_to_be32")
            [.var .local (ofString "amount"), .var .local (ofString "data")])
            (transferRecordPairWrites 24 (ofString "data") 32 cont)))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString "data", cur.locals.lookup (ofString "data")) } := by
  obtain ⟨written, hd, heap, step, resum, out, bytes, loc, wb, wframe, er, es⟩ :=
    transfer_alloc_data_write_prefix s cur data av _ hInv hstep hbe hout hbyte ha hp hr
  have ww : WordsOK written (logw.toNat, 40) := by
    apply wordsOK_of_inside_heap _ step.1.1.1.1.memaddrs
    · exact hw.1
    · decide
    · exact le_trans hInv.1.2.1 hin.1
    · have hlim := hstep.1.1.1.2.2.1
      have hle := hin.2
      have : heapLimit ≤ heapEnd := by decide
      omega
  have wi : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN written "heap_ptr") :=
    ⟨hin.1, le_trans hin.2 (by
      have hpNat : globN cur "heap_ptr" = data.toNat := by simp [globN, hp]
      rw [hpNat, heap]; omega)⟩
  obtain ⟨mid, st', eff, lc, words, ptr, count, frame, res, out', bytes', eq⟩ :=
    transfer_record_pair_writes_prefix s written logw data 32 24 (ofString "data") cont
      (Or.inr rfl) hInv step wb out bytes ((loc _ (by decide)).trans hl) hd ww wi resum
  refine ⟨mid, lc ▸ hd, lc ▸ ((loc _ (by decide)).trans hl), ?_, st', ?_, ?_, words, ptr, count,
    ?_, eff.be.trans wb, out', bytes', res, er.trans (congrArg Prod.fst eq), ?_⟩
  · simpa only [globN, eff.globals] using heap
  · exact (hstep.1.2.2.1 _ (by decide)).symm.trans (st'.1.2.2.1 _ (by decide)) |>.symm
  · unfold globN
    rw [(st'.1.2.2.1 _ (by decide)).symm, hstep.1.2.2.1 _ (by decide)]
  · intro b hb hsep hn hn'
    rw [frame b hb hn hn', wframe b hb hsep]
  · exact es.trans (congrArg (fun out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F =>
      { out.2 with locals := (HolFiniteMapExact.resVarEq out.2.locals
        (ofString "data", cur.locals.lookup (ofString "data"))) }) eq)

def transferAppendReturn : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "log_append")
    [.var .global (ofString "ev"), .var .local (ofString "log")]) (.return (.const 0))

def transferDataTail : ProgHOL 64 :=
  .decCall (ofString "data") .one (ofString "alloc") [.const 32]
    (.seq (.call (some (none, none)) (ofString "u256_to_be32")
      [.var .local (ofString "amount"), .var .local (ofString "data")])
      (transferRecordPairWrites 24 (ofString "data") 32 transferAppendReturn))

theorem transfer_data_tail_step {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (data logw evw : BitVec 64) (topics : Nat)
    (av : ValueHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (ha : cur.locals.lookup (ofString "amount") = some av)
    (hl : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hev : cur.globals.lookup (ofString "ev") = some (.val (.word evw)))
    (hw : WordsOK cur (logw.toNat, 40))
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hp : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word data)))
    (hsys : Inside (globN cur "vm_system_address", 20) sourceBase (globN cur "heap_ptr"))
    (htop : Inside (topics, 96) sourceBase (globN cur "heap_ptr"))
    (haddr : memW cur logw.toNat = globN cur "vm_system_address")
    (htp : memW cur (logw.toNat + 8) = topics)
    (htn : memW cur (logw.toNat + 16) = 3)
    (hlt : logw.toNat + 40 ≤ topics) (htd : topics + 96 ≤ data.toNat)
    (hdisj : ∀ mid : PanSemStateFiniteExact 64 F,
      EvmStepCC ["heap_ptr"] s mid →
      globN mid "heap_ptr" = data.toNat + 32 →
      mid.be = s.be →
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) →
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) →
      ∃ S Nd, EvmInvAt mid S ∧ TriesTypedWith mid S Nd ∧
      (∀ o ∈ ((evmChain mid).map (frameObjects mid)).flatten,
        ∀ j ∈ nodeExtents mid Nd, Disj o j) ∧
      ∀ x ∈ [(logw.toNat, 40), (topics, 96), (data.toNat, 32)],
      (∀ t ∈ S, ∀ i ∈ htabFootprint mid t, Disj x i) ∧
      (∀ j ∈ fixedObjects mid, Disj x j) ∧
      (∀ ec ∈ evmChain mid, ∀ o ∈ frameObjects mid ec, Disj x o) ∧
      (∀ j ∈ nodeExtents mid Nd, Disj x j) ∧
      (∀ ec ∈ evmChain mid, Disj x (memW mid (ec.1 + 112), 176)))
    (hr : Resumes (evaluateHOLFiniteState cur transferDataTail).1) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState cur transferDataTail).2 := by
  obtain ⟨mid, hd, hl', heap, step, ev, sys, words, dp, dn, frame, be, out, bytes, resum, er, es⟩ :=
    transfer_alloc_data_record_prefix s cur data logw av transferAppendReturn
      hInv hstep hbe hout hbyte ha hl hw hin hp hr
  have hbound : logw.toNat + 40 < 2 ^ 64 := by
    have hpNat : globN cur "heap_ptr" = data.toNat := by simp [globN, hp]
    have h64 := data.isLt
    omega
  have addr : memW mid logw.toNat = globN mid "vm_system_address" := by
    rw [frame _ (by omega) (by omega) (by omega) (by omega), haddr, sys]
  have tp : memW mid (logw.toNat + 8) = topics := by
    rw [frame _ (by omega) (by omega) (by omega) (by omega), htp]
  have tn : memW mid (logw.toNat + 16) = 3 := by
    rw [frame _ (by omega) (by omega) (by omega) (by omega), htn]
  have hmono : globN cur "heap_ptr" ≤ globN mid "heap_ptr" := by
    have hpNat : globN cur "heap_ptr" = data.toNat := by simp [globN, hp]
    rw [hpNat, heap]; omega
  have tail : EvmStepCC ["heap_ptr"] mid (evaluateHOLFiniteState mid transferAppendReturn).2 := by
    obtain ⟨S, Nd, inv, tries, avoids, disj⟩ := hdisj mid step heap be out bytes
    apply transfer_log_append_tail_step_at mid evw logw topics data.toNat S Nd inv tries avoids step.1.1
      (by simp [globN, ev, hev]) words
      ⟨le_trans hInv.1.2.1 hin.1, le_trans hin.2 hmono⟩
      ⟨by simpa only [sys] using hsys.1, by rw [sys]; exact le_trans hsys.2 hmono⟩
      ⟨htop.1, le_trans htop.2 hmono⟩
      ⟨by
          have hlo := hstep.1.1.1.2.1
          have hpNat : globN cur "heap_ptr" = data.toNat := by simp [globN, hp]
          change sourceBase ≤ data.toNat
          omega,
        by rw [heap]⟩ addr tp tn dp dn hlt htd
      (by rw [logOwnedIvls_of_transfer addr tp tn dp dn]; exact disj)
      (by simpa only [evalHOLExact, ev] using hev)
      (by simpa only [evalHOLExact] using hl')
      (transfer_log_append_tail_resumes_returned mid step.1.1.1.1.code resum)
  have both : EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState mid transferAppendReturn).2 := by
    refine ⟨⟨tail.1.1, le_trans step.1.2.1 tail.1.2.1,
      fun k hk => (step.1.2.2.1 k hk).trans (tail.1.2.2.1 k hk),
      tail.1.2.2.2.trans step.1.2.2.2⟩, ?_⟩
    intro ec hec
    obtain ⟨a, b, c, d⟩ := step.2 ec hec
    obtain ⟨a', b', c', d'⟩ := tail.2 ec (step.1.2.2.2.symm ▸ hec)
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩
  change EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState cur
    (.decCall (ofString "data") .one (ofString "alloc") [.const 32]
      (.seq (.call (some (none, none)) (ofString "u256_to_be32")
        [.var .local (ofString "amount"), .var .local (ofString "data")])
        (transferRecordPairWrites 24 (ofString "data") 32 transferAppendReturn)))).2
  rw [es]
  exact ⟨⟨localsFree_evmInv _ _ _ both.1.1, both.1.2.1, both.1.2.2.1,
    (evmChain_with_locals _ _ _).trans both.1.2.2.2⟩, both.2⟩

theorem transfer_accumulated_alloc_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (name : MlS) (p : BitVec 64)
    (n : Nat) (cont : ProgHOL 64) (hn : n = 40 ∨ n = 96 ∨ n = 32)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hp : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.decCall name .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).1) :
    ∃ allocated : PanSemStateFiniteExact 64 F,
      allocated.locals.lookup name = some (.val (.word p)) ∧
      globN allocated "heap_ptr" = p.toNat + n ∧ WordsOK allocated (p.toNat, n) ∧
      EvmStepCC ["heap_ptr"] s allocated ∧ allocated.memory = cur.memory ∧
      allocated.be = s.be ∧
      (∀ k, k ≠ name → allocated.locals.lookup k = cur.locals.lookup k) ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → allocated.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN allocated "heap_ptr") → memB allocated b = memB s b) ∧
      Resumes (evaluateHOLFiniteState allocated cont).1 ∧
      (evaluateHOLFiniteState cur
        (.decCall name .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).1 =
        (evaluateHOLFiniteState allocated cont).1 ∧
      (evaluateHOLFiniteState cur
        (.decCall name .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).2 =
        { (evaluateHOLFiniteState allocated cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState allocated cont).2.locals
            (name, cur.locals.lookup name) } := by
  obtain ⟨allocated, hx, hhp, hw, st, er, es, hm, hb, hl⟩ :=
    transfer_decCall_alloc_exact_spec cur name cont p n hn hstep.1.1 hp hr
  have both : EvmStepCC ["heap_ptr"] s allocated := by
    refine ⟨⟨st.1.1, le_trans hstep.1.2.1 st.1.2.1,
      fun k hk => (hstep.1.2.2.1 k hk).trans (st.1.2.2.1 k hk),
      st.1.2.2.2.trans hstep.1.2.2.2⟩, ?_⟩
    intro ec hec
    obtain ⟨a, b, c, d⟩ := hstep.2 ec hec
    obtain ⟨a', b', c', d'⟩ := st.2 ec (hstep.1.2.2.2.symm ▸ hec)
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩
  refine ⟨allocated, hx, hhp, hw, both, hm, hb.trans hbe, hl, ?_, ?_, er ▸ hr, er, es⟩
  · intro a ha
    exact (congrFun hm a).trans (hout a ha)
  · intro b hb64 hnot
    rw [show memB allocated b = memB cur b by simp only [memB, hm, hb]]
    apply hbyte b hb64
    have hmono := st.1.2.1
    omega

theorem transfer_accumulated_topics_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (p topic sender recipient : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hp : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (htopic : cur.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hsender : cur.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hrecipient : cur.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] (transferTopicWrites cont))).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.locals.lookup (ofString "topics") = some (.val (.word p)) ∧
      globN mid "heap_ptr" = p.toNat + 96 ∧ EvmStepCC ["heap_ptr"] s mid ∧
      mid.be = s.be ∧
      (∀ k, k ≠ ofString "topics" → mid.locals.lookup k = cur.locals.lookup k) ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      (∀ b : Nat, b < 2 ^ 64 → b + 8 ≤ p.toNat → memW mid b = memW cur b) ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState cur
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] (transferTopicWrites cont))).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState cur
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96] (transferTopicWrites cont))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString "topics", cur.locals.lookup (ofString "topics")) } := by
  obtain ⟨allocated, ht, hheap, hw, st, hm, hb, hl, out, bytes, resum, er, es⟩ :=
    transfer_accumulated_alloc_prefix s cur (ofString "topics") p 96 _
      (Or.inr (Or.inl rfl)) hInv hstep hbe hout hbyte hp hr
  have hpNat : globN cur "heap_ptr" = p.toNat := by simp [globN, hp]
  have hi : Inside (p.toNat, 96) (globN s "heap_ptr") (globN allocated "heap_ptr") :=
    ⟨by rw [← hpNat]; exact hstep.1.2.1, by rw [hheap]⟩
  obtain ⟨mid, step, eff, loc, res, out', bytes', eq⟩ :=
    transfer_topic_writes_prefix s allocated p topic sender recipient cont hInv st hb out bytes ht
      (((st.1.2.2.1 _ (by decide)).symm.trans (hstep.1.2.2.1 _ (by decide))).trans htopic)
      ((hl _ (by decide)).trans hsender) ((hl _ (by decide)).trans hrecipient) hi resum
  refine ⟨mid, loc ▸ ht, ?_, step, eff.be.trans hb, ?_, out', bytes', ?_, res,
    er.trans (congrArg Prod.fst eq), ?_⟩
  · simpa only [globN, eff.globals] using hheap
  · intro k hk
    rw [loc]
    exact hl k hk
  · intro b hb64 hsep
    have ha : (BitVec.ofNat 64 b).toNat = b := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64]
    have hm' := eff.cell_frame (BitVec.ofNat 64 b) (by
      intro i hi
      rcases List.mem_singleton.mp hi with rfl
      rw [ha]
      simp only [CellHits]
      omega)
    simp only [memW, hm', hm]
  · exact es.trans (congrArg (fun out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F =>
      { out.2 with locals := (HolFiniteMapExact.resVarEq out.2.locals
        (ofString "topics", cur.locals.lookup (ofString "topics"))) }) eq)

theorem transfer_accumulated_topics_record_prefix {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (p topic sender recipient logw : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hp : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (htopic : cur.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hsender : cur.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hrecipient : cur.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (hl : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hw : WordsOK cur (logw.toNat, 40))
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
        (transferTopicWrites (transferRecordPairWrites 8 (ofString "topics") 3 cont)))).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.locals.lookup (ofString "topics") = some (.val (.word p)) ∧
      globN mid "heap_ptr" = p.toNat + 96 ∧ EvmStepCC ["heap_ptr"] s mid ∧
      mid.be = s.be ∧ WordsOK mid (logw.toNat, 40) ∧
      memW mid logw.toNat = memW cur logw.toNat ∧
      memW mid (logw.toNat + 8) = p.toNat ∧ memW mid (logw.toNat + 16) = 3 ∧
      (∀ k, k ≠ ofString "topics" → mid.locals.lookup k = cur.locals.lookup k) ∧
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState cur
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
          (transferTopicWrites (transferRecordPairWrites 8 (ofString "topics") 3 cont)))).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState cur
        (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
          (transferTopicWrites (transferRecordPairWrites 8 (ofString "topics") 3 cont)))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString "topics", cur.locals.lookup (ofString "topics")) } := by
  obtain ⟨written, ht, heap, step, wb, loc, out, bytes, frame, resum, er, es⟩ :=
    transfer_accumulated_topics_prefix s cur p topic sender recipient _ hInv hstep hbe hout hbyte
      hp htopic hsender hrecipient hr
  have hpNat : globN cur "heap_ptr" = p.toNat := by simp [globN, hp]
  have hmono : globN cur "heap_ptr" ≤ globN written "heap_ptr" := by rw [hpNat, heap]; omega
  have ww : WordsOK written (logw.toNat, 40) := by
    apply wordsOK_of_inside_heap _ step.1.1.1.1.memaddrs
    · exact hw.1
    · decide
    · exact le_trans hInv.1.2.1 hin.1
    · have hlim := hstep.1.1.1.2.2.1
      have hle := hin.2
      have : heapLimit ≤ heapEnd := by decide
      omega
  obtain ⟨mid, st', eff, lc, words, ptr, count, fr, res, out', bytes', eq⟩ :=
    transfer_record_pair_writes_prefix s written logw p 3 8 (ofString "topics") cont
      (Or.inl rfl) hInv step wb out bytes ((loc _ (by decide)).trans hl) ht ww
      ⟨hin.1, le_trans hin.2 hmono⟩ resum
  refine ⟨mid, lc ▸ ht, ?_, st', eff.be.trans wb, words, ?_, ptr, count, ?_, out', bytes',
    res, er.trans (congrArg Prod.fst eq), ?_⟩
  · simpa only [globN, eff.globals] using heap
  · have h64 := logw.isLt
    rw [fr _ h64 (by omega) (by omega), frame _ h64 (by have hle := hin.2; omega)]
  · intro k hk
    rw [lc]
    exact loc k hk
  · exact es.trans (congrArg (fun out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F =>
      { out.2 with locals := (HolFiniteMapExact.resVarEq out.2.locals
        (ofString "topics", cur.locals.lookup (ofString "topics"))) }) eq)

theorem transfer_accumulated_topics_record_step {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (p topic sender recipient logw : BitVec 64) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hp : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (htopic : cur.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hsender : cur.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hrecipient : cur.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (hl : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hw : WordsOK cur (logw.toNat, 40))
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState cur
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
        (transferTopicWrites (transferRecordPairWrites 8 (ofString "topics") 3 cont)))).1)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.locals.lookup (ofString "topics") = some (.val (.word p)) →
      globN mid "heap_ptr" = p.toNat + 96 → EvmStepCC ["heap_ptr"] s mid →
      mid.be = s.be → WordsOK mid (logw.toNat, 40) →
      memW mid logw.toNat = memW cur logw.toNat →
      memW mid (logw.toNat + 8) = p.toNat → memW mid (logw.toNat + 16) = 3 →
      (∀ k, k ≠ ofString "topics" → mid.locals.lookup k = cur.locals.lookup k) →
      (∀ a : BitVec 64, ¬ s.memaddrs a → mid.memory a = s.memory a) →
      (∀ b : Nat, b < 2 ^ 64 →
        ¬ (globN s "heap_ptr" ≤ b ∧ b < globN mid "heap_ptr") → memB mid b = memB s b) →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState mid cont).2) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState cur
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
        (transferTopicWrites (transferRecordPairWrites 8 (ofString "topics") 3 cont)))).2 := by
  obtain ⟨mid, ht, heap, step, be, words, addr, tp, tn, loc, out, bytes, resum, er, es⟩ :=
    transfer_accumulated_topics_record_prefix s cur p topic sender recipient logw cont
      hInv hstep hbe hout hbyte hp htopic hsender hrecipient hl hw hin hr
  have tail := hcont mid ht heap step be words addr tp tn loc out bytes resum
  rw [es]
  exact ⟨⟨localsFree_evmInv _ _ _ tail.1.1, tail.1.2.1, tail.1.2.2.1,
    (evmChain_with_locals _ _ _).trans tail.1.2.2.2⟩, tail.2⟩

theorem transfer_memW_of_accumulated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b)
    (a : Nat) (ha : a + 8 ≤ 2 ^ 64)
    (hsep : a + 8 ≤ globN s "heap_ptr" ∨ globN post "heap_ptr" ≤ a) :
    memW post a = memW s a := by
  have hnat : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt (by omega)
  unfold memW
  by_cases hd : ordinaryDomain (BitVec.ofNat 64 a)
  · rw [R13Shards.mem_eq_of_bytes_eq_ord hbe _ hd (by
      intro k hk
      rw [hnat]
      apply hbyte _ (by omega)
      rcases hsep with hl | hh <;> omega)]
  · rw [hout _ (by rwa [hInv.1.1.memaddrs])]

theorem transfer_sameTypedCells_of_accumulated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s post)
    (hWT : WorldTypedWith s S Nd) (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) :
    SameTypedCells s post S Nd := by
  have sep : ∀ i ∈ worldTypedIvls s S Nd,
      i.2 = 0 ∨ globN post "heap_ptr" ≤ i.1 ∨ i.1 + i.2 ≤ globN s "heap_ptr" := by
    intro i hi
    rcases worldTypedIvls_allocated hWT hi with hz | hal
    · exact Or.inl hz
    · rcases hal with hh | hs
      · exact Or.inr (Or.inr hh.2)
      · have hp := hstep.1.1.1.2.2.1
        have hlow := hs.1
        have hf := hInv.1.2.2.2.1
        have hg := hInv.1.2.2.2.2.1
        rw [R11Shards.heapLimit_val] at hp
        rw [R11Shards.scratchStart_val] at hf
        exact Or.inr (Or.inl (by omega))
  refine ⟨hbe, hstep.1.1.1.1.memaddrs.trans hInv.1.1.memaddrs.symm,
    hInv.1.1.memaddrs, ?_, ?_, ?_⟩
  · intro a ha
    exact hout a (by rwa [hInv.1.1.memaddrs])
  · intro a ha ha8 ⟨i, hi, hlo, hhi⟩
    have hn : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
    by_cases hd : ordinaryDomain (BitVec.ofNat 64 a)
    · apply R13Shards.mem_eq_of_bytes_eq_ord hbe _ hd
      intro k hk
      rw [hn]
      apply hbyte _ (by omega)
      rcases sep i hi with hz | hh | hh <;> omega
    · exact hout _ (by rwa [hInv.1.1.memaddrs])
  · intro b hb ⟨i, hi, hlo, hhi⟩
    apply hbyte b hb
    rcases sep i hi with hz | hh | hh <;> omega

theorem transfer_world_footprints_of_accumulated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s post)
    (hWT : WorldTypedWith s S Nd) (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) :
    fixedObjects post = fixedObjects s ∧
    (∀ t ∈ S, htabFootprint post t = htabFootprint s t) ∧
    nodeExtents post Nd = nodeExtents s Nd := by
  have cell := transfer_sameTypedCells_of_accumulated_frame hInv hstep hWT hbe hout hbyte
  refine ⟨?_, ?_, nodeExtents_eq hWT.2.2.2.1 cell⟩
  · have hg : ∀ name, ofString name ≠ ofString "heap_ptr" → globN post name = globN s name := by
      intro name hn
      unfold globN
      rw [hstep.1.2.2.1 _ (by simpa using hn)]
    unfold fixedObjects
    rw [blockOutObjects_eq hInv.1.2 hWT.2.2.1 cell (hg "bo" (by decide)),
      balObjects_eq hInv.1.2 hWT.1 hWT.2.2.1 cell (hg "bal_accounts" (by decide)),
      hg "journal" (by decide), hg "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hn : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    rw [hg gn.1 hn]
  · intro t ht
    exact htabFootprint_eq cell ht (hWT.1.2.1 t ht).1

theorem transfer_memW_of_allocated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s post)
    (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b)
    (hi : Allocated s i) (a : Nat) (hlo : i.1 ≤ a) (hhi : a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  apply transfer_memW_of_accumulated_frame hInv hbe hout hbyte
  · have hb := ivl_allocated_bound hInv.1.2 hi
    omega
  · rcases hi with hh | hs
    · exact Or.inl (le_trans hhi hh.2)
    · have hp := hstep.1.1.1.2.2.1
      have hf := hInv.1.2.2.2.1
      have hg := hInv.1.2.2.2.2.1
      have hlow := hs.1
      rw [R11Shards.heapLimit_val] at hp
      rw [R11Shards.scratchStart_val] at hf
      exact Or.inr (by omega)

theorem transfer_frame_footprints_of_accumulated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s post)
    (hFW : FrameWF s S ec) (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) :
    frameLogObjects post ec = frameLogObjects s ec ∧
      frameObjects post ec = frameObjects s ec := by
  obtain ⟨hscr, _, _, _, _, _, _, _, _, _, _, hlen, hlogs_in, _, _, hlogs_ok, _⟩ := hFW
  have field : ∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro k hk
    exact transfer_memW_of_allocated_frame hInv hstep hbe hout hbyte
      (Or.inr (hscr (ec.1, 280) (by simp)).1) _ (by omega) (by simpa using hk)
  have header : ∀ k, k + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k) := by
    intro k hk
    exact transfer_memW_of_allocated_frame hInv hstep hbe hout hbyte
      (Or.inr (hscr (memW s (ec.1 + 88), 24) (by simp)).1) _ (by omega) (by simpa using hk)
  have hzero := header 0 (by decide)
  simp only [Nat.add_zero] at hzero
  have ptr : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
    intro i hi
    have hal : Allocated s (frameLogs s ec) := hlogs_in
    apply transfer_memW_of_allocated_frame hInv hstep hbe hout hbyte hal
    · simp only [frameLogs]; omega
    · simp only [frameLogs]; omega
  have logwords : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      let log := memW s (memW s (memW s (ec.1 + 88)) + 8 * i)
      ∀ k, k + 8 ≤ 40 → memW post (log + k) = memW s (log + k) := by
    intro i hi log k hk
    have hnonzero : memW s (ec.1 + 88) ≠ 0 := by
      have hlo := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      have hf := hInv.1.2.2.2.1
      have hg := hInv.1.2.2.2.2.1
      rw [R11Shards.scratchStart_val] at hf
      intro hz
      rw [hz] at hlo
      omega
    rcases hlogs_ok with hz | ⟨_, _, _, _, entries⟩
    · exact False.elim (hnonzero hz)
    · exact transfer_memW_of_allocated_frame hInv hstep hbe hout hbyte
        (Or.inl (entries i hi).2.2.1) _ (by dsimp only [log]; omega)
        (by dsimp only [log]; omega)
  have logs : frameLogObjects post ec = frameLogObjects s ec := by
    unfold frameLogObjects
    dsimp only
    rw [field 88 (by decide), header 8 (by decide)]
    apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [hzero, ptr i hi]
    have w0 := logwords i hi 0 (by decide)
    simp only [Nat.add_zero] at w0
    unfold logOwnedIvls logRecordIvls
    have hg : globN post "vm_system_address" = globN s "vm_system_address" := by
      unfold globN
      rw [hstep.1.2.2.1 _ (by decide)]
    rw [w0, logwords i hi 8 (by decide), logwords i hi 16 (by decide),
      logwords i hi 24 (by decide), logwords i hi 32 (by decide), hg]
  refine ⟨logs, ?_⟩
  unfold frameObjects frameLogs frameRet
  rw [field 8 (by decide), field 232 (by decide), field 24 (by decide),
    field 40 (by decide), field 88 (by decide), field 216 (by decide),
    field 144 (by decide), hzero, header 16 (by decide), logs]

theorem transfer_chain_footprints_of_accumulated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s post)
    (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) :
    ∀ ec ∈ evmChain s,
      frameObjects post ec = frameObjects s ec ∧
      frameLogObjects post ec = frameLogObjects s ec ∧
      memW post (ec.1 + 112) = memW s (ec.1 + 112) := by
  have inv := hInv
  obtain ⟨_, S, _, _, _, _, frames, _⟩ := inv
  intro ec hec
  have fw := frames ec hec
  have fp := transfer_frame_footprints_of_accumulated_frame hInv hstep fw hbe hout hbyte
  refine ⟨fp.2, fp.1, ?_⟩
  apply transfer_memW_of_allocated_frame hInv hstep hbe hout hbyte
    (Or.inr (fw.1 (ec.1, 280) (by simp)).1) <;> simp only <;> omega

theorem transfer_frame_disjoint_of_accumulated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {x : Ivl}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s post)
    (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b)
    (hframe : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj x o)
    (hmsg : ∀ ec ∈ evmChain s, Disj x (memW s (ec.1 + 112), 176)) :
    (∀ ec ∈ evmChain post, ∀ o ∈ frameObjects post ec, Disj x o) ∧
      (∀ ec ∈ evmChain post, Disj x (memW post (ec.1 + 112), 176)) := by
  have fp := transfer_chain_footprints_of_accumulated_frame hInv hstep hbe hout hbyte
  rw [hstep.1.2.2.2]
  constructor
  · intro ec hec o ho
    rw [(fp ec hec).1] at ho
    exact hframe ec hec o ho
  · intro ec hec
    rw [(fp ec hec).2.2]
    exact hmsg ec hec

theorem transfer_worldOwned_of_accumulated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s post)
    (hWT : WorldTypedWith s S Nd) (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) :
    worldOwned post S Nd = worldOwned s S Nd := by
  obtain ⟨fix, tables, nodes⟩ :=
    transfer_world_footprints_of_accumulated_frame hInv hstep hWT hbe hout hbyte
  unfold worldOwned
  rw [fix, nodes]
  congr 2
  exact List.flatMap_congr tables

theorem transfer_owned_disjoint_of_accumulated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {x : Ivl}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s post)
    (hWT : WorldTypedWith s S Nd) (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b)
    (hworld : ∀ o ∈ worldOwned s S Nd, Disj x o)
    (hframe : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj x o)
    (hmsg : ∀ ec ∈ evmChain s, Disj x (memW s (ec.1 + 112), 176)) :
    (∀ o ∈ worldOwned post S Nd, Disj x o) ∧
    (∀ ec ∈ evmChain post, ∀ o ∈ frameObjects post ec, Disj x o) ∧
    (∀ ec ∈ evmChain post, Disj x (memW post (ec.1 + 112), 176)) := by
  refine ⟨?_, transfer_frame_disjoint_of_accumulated_frame
    hInv hstep hbe hout hbyte hframe hmsg⟩
  rw [transfer_worldOwned_of_accumulated_frame hInv hstep hWT hbe hout hbyte]
  exact hworld

theorem transfer_fresh_disjoint_of_accumulated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {x : Ivl}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s post)
    (hWT : WorldTypedWith s S Nd) (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b)
    (hx : x = (0, 0) ∨ Inside x (globN s "heap_ptr") (globN post "heap_ptr")) :
    (∀ o ∈ worldOwned post S Nd, Disj x o) ∧
    (∀ ec ∈ evmChain post, ∀ o ∈ frameObjects post ec, Disj x o) ∧
    (∀ ec ∈ evmChain post, Disj x (memW post (ec.1 + 112), 176)) := by
  have fresh := disj_fresh_heap_of_evmInv hInv hstep.1.1.1.2.2.1 hx
  apply transfer_owned_disjoint_of_accumulated_frame hInv hstep hWT hbe hout hbyte
  · intro o ho
    simp only [worldOwned, List.mem_append, List.mem_flatMap] at ho
    rcases ho with (⟨t, ht, hi⟩ | hf) | hn
    · exact fresh.1 t S hWT.1 ht o hi
    · exact fresh.2.1 o hf
    · exact fresh.2.2.2.1 S Nd hWT.2.2.2 o hn
  · exact fresh.2.2.1
  · exact fresh.2.2.2.2

theorem transfer_fixed_witness_of_accumulated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hInv : EvmInv s) (hAt : EvmInvAt s S)
    (hTr : TriesTypedWith s S Nd)
    (hAT : ∀ o ∈ ((evmChain s).map (frameObjects s)).flatten,
      ∀ j ∈ nodeExtents s Nd, Disj o j)
    (hstep : EvmStepCC ["heap_ptr"] s post) (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) :
    EvmInvAt post S ∧ TriesTypedWith post S Nd ∧
      (∀ o ∈ ((evmChain post).map (frameObjects post)).flatten,
        ∀ j ∈ nodeExtents post Nd, Disj o j) := by
  have inv := (OpHandlersB.evmInvAt_of_fresh_heap_step hInv.1 hAt hstep.1.1.1 hbe
    hstep.1.2.1 hstep.1.2.2.1 hout hbyte).1
  have wt : WorldTypedWith s S Nd := ⟨hAt.1.1, hAt.1.2.1, hAt.1.2.2.1, hTr⟩
  obtain ⟨fix, tables, nodes⟩ :=
    transfer_world_footprints_of_accumulated_frame hInv hstep wt hbe hout hbyte
  have cell := transfer_sameTypedCells_of_accumulated_frame hInv hstep wt hbe hout hbyte
  have globals : ∀ name, ofString name ≠ ofString "heap_ptr" → globN post name = globN s name := by
    intro name hn
    unfold globN
    rw [hstep.1.2.2.1 _ (by simpa using hn)]
  have wt' := (worldTypedWith_congr_w1 hInv.1 hstep.1.1.1 hstep.1.2.1
    (by rw [globals "scratch_ptr" (by decide)])
    (fun g hg => globals g (by revert g hg; decide)) cell wt
    ⟨inv.1.2.2.1, fun o ho => Or.inl (fix ▸ ho)⟩).1
  refine ⟨inv, wt'.2.2.2, ?_⟩
  have frames := transfer_chain_footprints_of_accumulated_frame hInv hstep hbe hout hbyte
  rw [hstep.1.2.2.2, nodes]
  have eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left (fun ec hec => (frames ec hec).1)
  rw [eq]
  exact hAT

theorem transfer_fresh_fixed_disjoint_of_accumulated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {x : Ivl}
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s post)
    (hWT : WorldTypedWith s S Nd) (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b)
    (hx : Inside x (globN s "heap_ptr") (globN post "heap_ptr")) :
    (∀ t ∈ S, ∀ i ∈ htabFootprint post t, Disj x i) ∧
    (∀ j ∈ fixedObjects post, Disj x j) ∧
    (∀ ec ∈ evmChain post, ∀ o ∈ frameObjects post ec, Disj x o) ∧
    (∀ j ∈ nodeExtents post Nd, Disj x j) ∧
    (∀ ec ∈ evmChain post, Disj x (memW post (ec.1 + 112), 176)) := by
  obtain ⟨world, frames, msgs⟩ := transfer_fresh_disjoint_of_accumulated_frame
    hInv hstep hWT hbe hout hbyte (Or.inr hx)
  refine ⟨fun t ht i hi => world i ?_, fun j hj => world j ?_, frames,
    fun j hj => world j ?_, msgs⟩
  · simp only [worldOwned, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl ⟨t, ht, hi⟩)
  · simp only [worldOwned, List.mem_append]
    exact Or.inl (Or.inr hj)
  · simp only [worldOwned, List.mem_append]
    exact Or.inr hj

theorem transfer_data_tail_fresh_step {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (data logw evw : BitVec 64) (topics : Nat)
    (av : ValueHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (ha : cur.locals.lookup (ofString "amount") = some av)
    (hl : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hev : cur.globals.lookup (ofString "ev") = some (.val (.word evw)))
    (hw : WordsOK cur (logw.toNat, 40))
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hp : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word data)))
    (hsys : Inside (globN cur "vm_system_address", 20) sourceBase (globN cur "heap_ptr"))
    (htop : Inside (topics, 96) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (haddr : memW cur logw.toNat = globN cur "vm_system_address")
    (htp : memW cur (logw.toNat + 8) = topics)
    (htn : memW cur (logw.toNat + 16) = 3)
    (hlt : logw.toNat + 40 ≤ topics) (htd : topics + 96 ≤ data.toNat)
    (hr : Resumes (evaluateHOLFiniteState cur transferDataTail).1) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState cur transferDataTail).2 := by
  apply transfer_data_tail_step s cur data logw evw topics av hInv hstep hbe hout hbyte ha hl hev hw hin hp
    hsys ⟨le_trans hInv.1.2.1 htop.1, htop.2⟩ haddr htp htn hlt htd (hr := hr)
  intro mid step heap be out bytes
  obtain ⟨_, S, inv⟩ := (evmInv_iff_at s).1 hInv
  obtain ⟨Nd, tries, avoids⟩ := inv.2.2.2.2.2.2.2.2.2.1
  obtain ⟨inv', tries', avoids'⟩ := transfer_fixed_witness_of_accumulated_frame
    hInv inv tries avoids step be out bytes
  refine ⟨S, Nd, inv', tries', avoids', ?_⟩
  intro x hx
  have inCur : globN cur "heap_ptr" = data.toNat := by simp [globN, hp]
  have mono : globN cur "heap_ptr" ≤ globN mid "heap_ptr" := by
    rw [inCur, heap]; omega
  apply transfer_fresh_fixed_disjoint_of_accumulated_frame hInv step
    ⟨inv.1.1, inv.1.2.1, inv.1.2.2.1, tries⟩ be out bytes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨hin.1, le_trans hin.2 mono⟩
  · exact ⟨htop.1, le_trans htop.2 mono⟩
  · exact ⟨by rw [← inCur]; exact hstep.1.2.1, by omega⟩

theorem transfer_topics_data_tail_step {F : Type}
    (s cur : PanSemStateFiniteExact 64 F) (p topic sender recipient logw evw : BitVec 64)
    (av : ValueHOL 64)
    (hInv : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s cur)
    (hbe : cur.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → cur.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN cur "heap_ptr") → memB cur b = memB s b)
    (hp : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (htopic : cur.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hsender : cur.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hrecipient : cur.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (ha : cur.locals.lookup (ofString "amount") = some av)
    (hl : cur.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hev : cur.globals.lookup (ofString "ev") = some (.val (.word evw)))
    (hw : WordsOK cur (logw.toNat, 40))
    (hin : Inside (logw.toNat, 40) (globN s "heap_ptr") (globN cur "heap_ptr"))
    (hsys : Inside (globN cur "vm_system_address", 20) sourceBase (globN cur "heap_ptr"))
    (haddr : memW cur logw.toNat = globN cur "vm_system_address")
    (hr : Resumes (evaluateHOLFiniteState cur
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
        (transferTopicWrites (transferRecordPairWrites 8 (ofString "topics") 3 transferDataTail)))).1) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState cur
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
        (transferTopicWrites (transferRecordPairWrites 8 (ofString "topics") 3 transferDataTail)))).2 := by
  apply transfer_accumulated_topics_record_step s cur p topic sender recipient logw transferDataTail
    hInv hstep hbe hout hbyte hp htopic hsender hrecipient hl hw hin hr
  intro mid ht heap step be words addr tp tn loc out bytes resum
  obtain ⟨data, hd⟩ : ∃ data : BitVec 64,
      mid.globals.lookup (ofString "heap_ptr") = some (.val (.word data)) :=
    globalWord_of_globN_pos mid "heap_ptr"
      (by have h := step.1.1.1.2.1; rw [sourceBase_val] at h; omega)
  have hdata : data.toNat = globN mid "heap_ptr" := by simp [globN, hd]
  have gp : globN cur "heap_ptr" = p.toNat := by simp [globN, hp]
  have globals (name : String) (hn : ofString name ≠ ofString "heap_ptr") :
      cur.globals.lookup (ofString name) = mid.globals.lookup (ofString name) :=
    (hstep.1.2.2.1 _ (by simpa using hn)).symm.trans (step.1.2.2.1 _ (by simpa using hn))
  have sys : globN mid "vm_system_address" = globN cur "vm_system_address" := by
    unfold globN; rw [globals "vm_system_address" (by decide)]
  apply transfer_data_tail_fresh_step s mid data logw evw p.toNat av hInv step be out bytes
    ((loc _ (by decide)).trans ha) ((loc _ (by decide)).trans hl)
    ((globals "ev" (by decide)).symm.trans hev) words
    ⟨hin.1, by rw [heap]; have h := hin.2; omega⟩ hd
    ⟨by rw [sys]; exact hsys.1, by rw [sys, heap]; have h := hsys.2; omega⟩
    ⟨by rw [← gp]; exact hstep.1.2.1, by rw [heap]⟩
    (by rw [addr, haddr, sys]) tp tn
    (by have h := hin.2; omega) (by rw [hdata, heap]) resum

def transferLogTail : ProgHOL 64 :=
  .decCall (ofString "log") .one (ofString "alloc") [.const 40]
    (.seq (.store (.op .add [.var .local (ofString "log"), .const 0])
      (.var .global (ofString "vm_system_address")))
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
        (transferTopicWrites (transferRecordPairWrites 8 (ofString "topics") 3 transferDataTail))))

theorem transfer_log_tail_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p sysw topic sender recipient evw : BitVec 64)
    (av : ValueHOL 64) (hInv : EvmInv s)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hsysw : s.globals.lookup (ofString "vm_system_address") = some (.val (.word sysw)))
    (htopic : s.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hsender : s.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hrecipient : s.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (ha : s.locals.lookup (ofString "amount") = some av)
    (hev : s.globals.lookup (ofString "ev") = some (.val (.word evw)))
    (hsys : Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState s transferLogTail).1) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState s transferLogTail).2 := by
  obtain ⟨mid, hl, heap, addr, words, step, resum, er, es, be, loc, out, bytes⟩ :=
    transfer_alloc_log_address_prefix s p sysw _ hInv hp hsysw hr
  obtain ⟨topics, ht⟩ : ∃ topics : BitVec 64,
      mid.globals.lookup (ofString "heap_ptr") = some (.val (.word topics)) :=
    globalWord_of_globN_pos mid "heap_ptr"
      (by have h := step.1.1.1.2.1; rw [sourceBase_val] at h; omega)
  have g (name : String) (hn : ofString name ≠ ofString "heap_ptr") :
      mid.globals.lookup (ofString name) = s.globals.lookup (ofString name) :=
    (step.1.2.2.1 _ (by simpa using hn)).symm
  have sys : globN mid "vm_system_address" = globN s "vm_system_address" := by
    unfold globN; rw [g _ (by decide)]
  have tail := transfer_topics_data_tail_step s mid topics topic sender recipient p evw av hInv step
    be out bytes ht ((g _ (by decide)).trans htopic)
    ((loc _ (by decide)).trans hsender) ((loc _ (by decide)).trans hrecipient)
    ((loc _ (by decide)).trans ha) hl ((g _ (by decide)).trans hev) words
    ⟨by simp [globN, hp], by rw [heap]⟩
    ⟨by rw [sys]; exact hsys.1, by rw [sys]; exact le_trans hsys.2 step.1.2.1⟩ addr resum
  change EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState s
    (.decCall (ofString "log") .one (ofString "alloc") [.const 40]
      (.seq (.store (.op .add [.var .local (ofString "log"), .const 0])
        (.var .global (ofString "vm_system_address"))) _))).2
  rw [es]
  exact ⟨⟨localsFree_evmInv _ _ _ tail.1.1, tail.1.2.1, tail.1.2.2.1,
    (evmChain_with_locals _ _ _).trans tail.1.2.2.2⟩, tail.2⟩

theorem transfer_decCall_readOnly_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (name fn : MlS) (shape : ShapeHOL)
    (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hInv : EvmInv s) (hro : ReadOnlyFn fn)
    (hr : Resumes (evaluateHOLFiniteState s (.decCall name shape fn args cont)).1)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F,
      mid = {s with locals := mid.locals, clock := mid.clock} →
      (∀ k, k ≠ name → mid.locals.lookup k = s.locals.lookup k) →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState mid cont).2) :
    EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState s (.decCall name shape fn args cont)).2 := by
  obtain ⟨params, body, ret, lookup, spec⟩ := hro
  have hcode := hInv.1.1.code
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr ⊢
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · simp only [ha] at hr; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  simp only [ha] at hr ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup fn vals with _ | ⟨body', callee, ret'⟩
  · simp only [hl] at hr; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  simp only [hl] at hr ⊢
  by_cases hz : s.clock = 0
  · simp only [hz, ↓reduceIte] at hr; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  simp only [hz, ↓reduceIte] at hr ⊢
  have hb := lookupCodeHOLFinite_installed_body s.code.lookup fn params body body' ret ret' vals callee
    (by rw [hcode]; exact lookup) hl
  subst hb
  have entry : callEntryStateHOLFinite s callee =
      {s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock} := by cases s; rfl
  have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fn vs =
      some (body', (callEntryStateHOLFinite s callee).locals, ret) := by
    have he := lookupCodeHOLFinite_installed_return s fn params body' body' ret ret' vals callee
      (by rw [hcode]; exact lookup) hl
    subst he
    exact ⟨vals, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
  rcases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
  simp only [run] at hr ⊢
  cases res with
  | none => rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  | some result =>
    cases result with
    | returned v =>
      dsimp only at hr ⊢
      split at hr
      · rename_i hs
        simp only [hs, ↓reduceIte]
        have ro := spec (callEntryStateHOLFinite s callee) hcode
          (guestInv_callEntry s callee hInv.1.1) hex (by rw [run]; simp)
          (by rw [run]; exact Or.inl ⟨v, rfl⟩)
        rw [run] at ro
        have postEq := state_trans_locals_clock entry ro
        let mid := setVarHOLFinite name v {post with locals := s.locals}
        have midEq : mid = {s with locals := mid.locals, clock := mid.clock} := by
          have h : mid = {post with locals := mid.locals, clock := post.clock} := by cases post; rfl
          exact state_trans_locals_clock postEq h
        have tail := hcont mid midEq (by
          intro k hk; simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]) hr
        exact ⟨⟨localsFree_evmInv _ _ _ tail.1.1, tail.1.2.1, tail.1.2.2.1,
          (evmChain_with_locals _ _ _).trans tail.1.2.2.2⟩, tail.2⟩
      · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
    | exception e v =>
      have res : Resumes (some (.exception e v)) := hr
      have ro := spec (callEntryStateHOLFinite s callee) hcode
        (guestInv_callEntry s callee hInv.1.1) hex (by rw [run]; simp) (by rw [run]; exact res)
      rw [run] at ro
      have postEq := state_trans_locals_clock entry ro
      have eq : emptyLocalsHOLFinite post =
          {s with locals := (emptyLocalsHOLFinite post).locals, clock := (emptyLocalsHOLFinite post).clock} := by
        have h : emptyLocalsHOLFinite post =
            {post with locals := (emptyLocalsHOLFinite post).locals, clock := post.clock} := by cases post; rfl
        exact state_trans_locals_clock postEq h
      dsimp only
      rw [eq]
      exact ⟨⟨localsFree_evmInv _ _ _ hInv, le_rfl, fun _ _ => rfl, evmChain_with_locals _ _ _⟩,
        fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩
    | _ => rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h

theorem emit_transfer_log_body_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (sender recipient topic : BitVec 64) (av : ValueHOL 64)
    (hInv : EvmInv s)
    (hsys : Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (htopic : s.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hsender : s.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hrecipient : s.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (ha : s.locals.lookup (ofString "amount") = some av)
    (hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_emit_transfer_log)).1) :
    EvmStepCC ["heap_ptr"] s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_emit_transfer_log)).2 := by
  have body : sourceFnBody Guest.Software.guestFn_emit_transfer_log =
      .decCall (ofString "z") .one (ofString "u256_is_zero") [.var .local (ofString "amount")]
        (.seq (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0))
          (.return (.const 0)) .skip) transferLogTail) := rfl
  rw [body] at hr ⊢
  apply transfer_decCall_readOnly_step s (ofString "z") (ofString "u256_is_zero") .one _ _
    hInv ro_u256_is_zero hr
  intro mid eq loc resum
  have inv : EvmInv mid := by rw [eq]; exact localsFree_evmInv _ _ _ hInv
  have tail (ht : Resumes (evaluateHOLFiniteState mid transferLogTail).1) :
      EvmStepCC ["heap_ptr"] s (evaluateHOLFiniteState mid transferLogTail).2 := by
    obtain ⟨p, hp⟩ : ∃ p : BitVec 64, mid.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) :=
      globalWord_of_globN_pos mid "heap_ptr"
        (by have h := inv.1.2.1; rw [sourceBase_val] at h; omega)
    have ready : Inside (globN mid "vm_system_address", 20) sourceBase (globN mid "heap_ptr") := by
      rw [eq]; exact hsys
    obtain ⟨sysw, hsysw⟩ : ∃ w : BitVec 64,
        mid.globals.lookup (ofString "vm_system_address") = some (.val (.word w)) :=
      globalWord_of_globN_pos mid "vm_system_address"
        (by have h := ready.1; rw [sourceBase_val] at h; omega)
    have htopic' : mid.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)) := by
      rw [eq]; exact htopic
    obtain ⟨evw, hev⟩ : ∃ w : BitVec 64, mid.globals.lookup (ofString "ev") = some (.val (.word w)) :=
      globalWord_of_globN_pos mid "ev" (by
        obtain ⟨_, S, invAt⟩ := (evmInv_iff_at mid).1 inv
        have fw := invAt.2.2.2.2.1 (globN mid "ev", globN mid "cur_cont") List.mem_cons_self
        have hlo := (fw.1 (globN mid "ev", 280) (by simp)).1.1
        have hgap := inv.1.2.2.2.1
        have hsp := inv.1.2.2.2.2.1
        rw [R11Shards.scratchStart_val] at hgap
        omega)
    have st := transfer_log_tail_step mid p sysw topic sender recipient evw av inv hp hsysw htopic'
      ((loc _ (by decide)).trans hsender) ((loc _ (by decide)).trans hrecipient)
      ((loc _ (by decide)).trans ha) hev ready ht
    conv at st => arg 2; rw [eq]
    refine ⟨⟨st.1.1, st.1.2.1, st.1.2.2.1, st.1.2.2.2.trans (evmChain_with_locals _ _ _)⟩, ?_⟩
    intro ec hec
    exact st.2 ec ((evmChain_with_locals _ _ _).symm ▸ hec)
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at resum ⊢
  split at resum
  · rename_i w hw
    split at resum
    · rename_i hz
      simp only [hw, hz, ↓reduceIte, evaluateHOLFiniteState_skip] at resum ⊢
      exact tail resum
    · rename_i hz
      simp only [hw, hz, ↓reduceIte, evaluateHOLFiniteState_return, evalHOLExact,
        shapeOfHOLExact, sizeOfShapeWithContextHOL, show (1 : Nat) ≤ 32 from by decide,
        ↓reduceIte, emptyLocalsHOLFinite] at resum ⊢
      have eq' : {mid with locals := HolFiniteMapExact.empty} =
          {s with locals := HolFiniteMapExact.empty, clock := mid.clock} := by rw [eq]
      change EvmStepCC ["heap_ptr"] s {mid with locals := HolFiniteMapExact.empty}
      rw [eq']
      exact ⟨⟨localsFree_evmInv _ _ _ hInv, le_rfl, fun _ _ => rfl, evmChain_with_locals _ _ _⟩,
        fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  · rcases resum with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h

private theorem emit_transfer_log_params {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "emit_transfer_log") vs =
      some (sourceFnBody Guest.Software.guestFn_emit_transfer_log, s.locals, .one)) :
    ∃ (sender recipient : BitVec 64) (amount : ValueHOL 64),
      s.locals.lookup (ofString "sender") = some (.val (.word sender)) ∧
      s.locals.lookup (ofString "recipient") = some (.val (.word recipient)) ∧
      s.locals.lookup (ofString "amount") = some amount := by
  obtain ⟨vals, hl⟩ := hex
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "emit_transfer_log")
    vals _ s.locals .one hl
  simp only [lookupCodeHOLExact, lookup_emit_transfer_log_local] at hx
  rcases vals with _ | ⟨vs, _ | ⟨vr, _ | ⟨va, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases vs with ⟨⟨sender⟩⟩ | _ | _ <;> rcases vr with ⟨⟨recipient⟩⟩ | _ | _ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL] at hx)
    simp [shapeOfHOLExact, shapeEqHOL,
      show ofString "sender" ≠ ofString "recipient" by decide,
      show ofString "sender" ≠ ofString "amount" by decide,
      show ofString "recipient" ≠ ofString "amount" by decide] at hx
    have hL := hx.2
    refine ⟨sender, recipient, va, ?_, ?_, ?_⟩ <;>
      (simp only [← hL]; simp [show ofString "sender" ≠ ofString "recipient" by decide,
        show ofString "sender" ≠ ofString "amount" by decide,
        show ofString "recipient" ≠ ofString "sender" by decide,
        show ofString "recipient" ≠ ofString "amount" by decide,
        show ofString "amount" ≠ ofString "sender" by decide,
        show ofString "amount" ≠ ofString "recipient" by decide])
  · simp at hx

theorem ek_cc_emit_transfer_log_ready :
    EvmKeeps (fun s => EvmAvoids FrameStartAvoids s ∧ FrameStartSysReady s)
      frameStartGw (ofString "emit_transfer_log") ∧
    ChainCellsKept (fun s => EvmAvoids FrameStartAvoids s ∧ FrameStartSysReady s)
      (ofString "emit_transfer_log") := by
  have step {F : Type} (s : PanSemStateFiniteExact 64 F)
      (hP : EvmAvoids FrameStartAvoids s ∧ FrameStartSysReady s)
      (hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "emit_transfer_log") vs =
        some (sourceFnBody Guest.Software.guestFn_emit_transfer_log, s.locals, .one))
      (hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_emit_transfer_log)).1) :
      EvmStepCC frameStartGw s
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_emit_transfer_log)).2 := by
    obtain ⟨hA, S, inv, _⟩ := hP.1
    have hInv : EvmInv s := ⟨hA, S, inv⟩
    obtain ⟨sender, recipient, amount, hs, hrp, ha⟩ := emit_transfer_log_params hex
    obtain ⟨topic, htopic⟩ := hA.2.2.2.2.2.2.2.2.2 "transfer_topic" (by decide)
    have st := emit_transfer_log_body_step s sender recipient topic amount hInv hP.2.1 htopic hs hrp ha hr
    exact ⟨⟨st.1.1, st.1.2.1, fun k hk => st.1.2.2.1 k (by
      intro he; apply hk; simp only [List.map_cons, List.map_nil, List.mem_singleton] at he
      rw [he]; simp [frameStartGw]), st.1.2.2.2⟩, st.2⟩
  constructor
  · refine ⟨_, _, _, lookup_emit_transfer_log_local, ?_⟩
    intro F s hcode hP hex hnt hr
    exact (step s hP hex hr).1
  · refine ⟨_, _, _, lookup_emit_transfer_log_local, ?_⟩
    intro F s hcode hP hex hnt hr
    exact (step s hP hex hr).2

theorem ek_emit_transfer_log_ready :
    EvmKeeps (fun s => EvmAvoids FrameStartAvoids s ∧ FrameStartSysReady s)
      frameStartGw (ofString "emit_transfer_log") :=
  ek_cc_emit_transfer_log_ready.1

theorem cc_emit_transfer_log_ready :
    ChainCellsKept (fun s => EvmAvoids FrameStartAvoids s ∧ FrameStartSysReady s)
      (ofString "emit_transfer_log") :=
  ek_cc_emit_transfer_log_ready.2

theorem frameStartSysReady_of_system_log {F : Type}
    {s : PanSemStateFiniteExact 64 F} {log : Nat}
    (hInv : EvmInv s) (hlog : LogEntryOK s log)
    (haddr : memW s log = globN s "vm_system_address") :
    FrameStartSysReady s := by
  apply frameStartSysReady_of_evmInv hInv
  rw [← haddr]
  exact hlog.2.2.2.2.1

theorem ek_cc_emit_transfer_log_of_system_heap
    (hready : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmAvoids FrameStartAvoids s →
      Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")) :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "emit_transfer_log") ∧
      ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "emit_transfer_log") := by
  obtain ⟨⟨ps, body, ret, lookup, keeps⟩, ⟨ps', body', ret', lookup', cells⟩⟩ :=
    ek_cc_emit_transfer_log_ready
  have ready {F : Type} (s : PanSemStateFiniteExact 64 F)
      (h : EvmAvoids FrameStartAvoids s) : FrameStartSysReady s := by
    have inv := h
    obtain ⟨arena, S, invAt, _⟩ := inv
    exact frameStartSysReady_of_evmInv ⟨arena, S, invAt⟩ (hready s h)
  exact ⟨⟨ps, body, ret, lookup, fun s code h => keeps s code ⟨h, ready s h⟩⟩,
    ⟨ps', body', ret', lookup', fun s code h => cells s code ⟨h, ready s h⟩⟩⟩

theorem system_heap_premise_iff_evmInv :
    (∀ {F : Type} (s : PanSemStateFiniteExact 64 F), EvmAvoids FrameStartAvoids s →
      Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")) ↔
    (∀ {F : Type} (s : PanSemStateFiniteExact 64 F), EvmInv s →
      Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")) := by
  constructor
  · intro h F s inv
    exact h s (evmAvoids_frameStart_of_evmInv s inv)
  · intro h F s avoids
    obtain ⟨arena, S, invAt, _⟩ := avoids
    exact h s ((evmInv_iff_at s).2 ⟨arena, S, invAt⟩)

theorem system_heap_excludes_scratch {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hArena : ArenaOK s)
    (hscratch : globN s "scratch_ptr" ≤ globN s "vm_system_address") :
    ¬ Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr") := by
  intro hheap
  have hhi := hArena.2.1
  have hlo := hArena.2.2.1
  have hsep := hArena.2.2.2.1
  dsimp [Inside] at hheap
  unfold heapLimit at hhi
  omega

theorem system_log_excludes_scratch {F : Type} {s : PanSemStateFiniteExact 64 F}
    {log : Nat} (hArena : ArenaOK s) (hlog : LogEntryOK s log)
    (haddr : memW s log = globN s "vm_system_address") :
    ¬ globN s "scratch_ptr" ≤ globN s "vm_system_address" := by
  intro hscratch
  apply system_heap_excludes_scratch hArena hscratch
  rw [← haddr]
  exact hlog.2.2.2.2.1

def PrecompileDispatchSpecs : Prop :=
  ∀ f ∈ (["pre_ecrecover", "pre_sha256", "pre_ripemd160", "pre_identity",
    "pre_alt_bn128_add", "pre_alt_bn128_mul", "pre_alt_bn128_pairing_check",
    "pre_modexp", "pre_blake2f", "pre_kzg_point_evaluation", "pre_bls_g1_add",
    "pre_bls_g1_msm", "pre_bls_g2_add", "pre_bls_g2_msm", "pre_bls_pairing",
    "pre_bls_map_fp_to_g1", "pre_bls_map_fp2_to_g2", "pre_p256verify"] : List String),
    EvmProgStep frameStartGw (.call (some (none, none)) (ofString f) [])

theorem precompile_head_update_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) (hGuest : GuestInv post)
    (hglobals : post.globals = s.globals) (hbe : post.be = s.be)
    (hmemory : ∀ x : BitVec 64,
      (∀ addr ∈ R11Shards.headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 addr) → post.memory x = s.memory x)
    (hgas : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192))
    (hcells : ChainCellsAgree s post) : EvmStepCC frameStartGw s post := by
  obtain ⟨inv, chain, _⟩ := R11Shards.evmInv_of_head_status_gas_update
    hInv hGuest hglobals hbe hmemory hgas
  refine ⟨⟨inv, ?_, ?_, chain⟩, hcells⟩
  · simp [globN, hglobals]
  · intro k _
    rw [hglobals]

theorem precompile_chain_cells_of_head_update {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hE : EvmInv s)
    (hmem : ∀ x : BitVec 64,
      (∀ addr ∈ R11Shards.headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 addr) → post.memory x = s.memory x) :
    ChainCellsAgree s post := by
  obtain ⟨_, S, _, hrest⟩ := hE
  dsimp only at hrest
  obtain ⟨_, _, _, hFWF, _, _, hPair, _⟩ := hrest
  obtain ⟨tl, hcs⟩ : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl :=
    ⟨_, OpHandlersB.HeadMemBridge.evmChain_cons s⟩
  have hSE : scratchEnd = 2965299200 := rfl
  have hhead := hFWF _ (by rw [hcs]; exact List.mem_cons_self)
  have he_in := (hhead.1 (globN s "ev", 280) (by simp)).1.2
  have hc_in := (hhead.1 (globN s "cur_cont", 104) (by simp)).1.2
  dsimp only at he_in hc_in
  rw [hcs, List.map_cons, List.flatten_cons, List.pairwise_append] at hPair
  obtain ⟨hP0, _, hcross⟩ := hPair
  have hdec : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
    unfold frameObjects at hP0
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hP0).1).1 _ (by simp)
  have hsafe : ∀ a : Nat, a < 2 ^ 64 →
      (∀ addr ∈ R11Shards.headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        a ≠ addr) → memW post a = memW s a := by
    intro a hlt hne
    unfold memW
    rw [hmem (BitVec.ofNat 64 a)]
    intro addr haddr heq
    have hal : addr < 2 ^ 64 := by
      simp only [R11Shards.headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
      rw [hSE] at he_in hc_in
      rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt hal] at this
    exact hne addr haddr this
  intro ec hec
  rw [hcs] at hec
  rcases List.mem_cons.mp hec with rfl | htl
  · unfold Disj at hdec
    dsimp only at hdec
    rw [hSE] at he_in hc_in
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply hsafe <;> (try dsimp only) <;> (try omega) <;>
      (intro addr haddr
       simp only [R11Shards.headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
       rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  · have hFec := hFWF ec (by rw [hcs]; exact List.mem_cons_of_mem _ htl)
    have hr_in := (hFec.1 (ec.1, 280) (by simp)).1.2
    have hk_in := (hFec.1 (ec.2, 104) (by simp)).1.2
    dsimp only at hr_in hk_in
    have hmemb : ∀ o ∈ [(ec.1, 280), (ec.2, 104)],
        o ∈ ((tl.map (frameObjects s)).flatten) := by
      intro o ho
      exact List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map_of_mem htl,
        by unfold frameObjects
           simp only [List.mem_cons, List.mem_append] at ho ⊢
           tauto⟩
    have hA : (globN s "ev", 280) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
      unfold frameObjects; simp
    have hB : (globN s "cur_cont", 104) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
      unfold frameObjects; simp
    have d1 := hcross _ hA _ (hmemb (ec.1, 280) (by simp))
    have d2 := hcross _ hB _ (hmemb (ec.1, 280) (by simp))
    have d3 := hcross _ hA _ (hmemb (ec.2, 104) (by simp))
    have d4 := hcross _ hB _ (hmemb (ec.2, 104) (by simp))
    unfold Disj at d1 d2 d3 d4
    dsimp only at d1 d2 d3 d4
    rw [hSE] at he_in hc_in hr_in hk_in
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply hsafe <;> (try omega) <;>
      (intro addr haddr
       simp only [R11Shards.headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
       rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)

theorem precompile_head_update_step_of_effect {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) (hGuest : GuestInv post)
    (hglobals : post.globals = s.globals) (hbe : post.be = s.be)
    (hmemory : ∀ x : BitVec 64,
      (∀ addr ∈ R11Shards.headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 addr) → post.memory x = s.memory x)
    (hgas : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) :
    EvmStepCC frameStartGw s post :=
  precompile_head_update_step hInv hGuest hglobals hbe hmemory hgas
    (precompile_chain_cells_of_head_update hInv hmemory)

theorem precompile_output_fields_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) (hGuest : GuestInv post)
    (hglobals : post.globals = s.globals) (hbe : post.be = s.be)
    (hmemory : ∀ x : BitVec 64,
      x ≠ BitVec.ofNat 64 (globN s "ev" + 120) →
      x ≠ BitVec.ofNat 64 (globN s "ev" + 128) → post.memory x = s.memory x)
    (hgas : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) :
    EvmStepCC frameStartGw s post := by
  apply precompile_head_update_step_of_effect hInv hGuest hglobals hbe _ hgas
  intro x hx
  exact hmemory x (hx _ (by simp [R11Shards.headAllowedOffsets]))
    (hx _ (by simp [R11Shards.headAllowedOffsets]))

theorem precompile_output_fields_gas_eq {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (hmemory : ∀ x : BitVec 64,
      x ≠ BitVec.ofNat 64 (globN s "ev" + 120) →
      x ≠ BitVec.ofNat 64 (globN s "ev" + 128) → post.memory x = s.memory x) :
    memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) =
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
  obtain ⟨he_lt, _, _, _, _⟩ := R11Shards.evm_head_globals hInv
  have hne (a b : Nat) (ha : a < 280) (hb : b < 280) (hab : a ≠ b) :
      BitVec.ofNat 64 (globN s "ev" + a) ≠
        BitVec.ofNat 64 (globN s "ev" + b) := by
    intro heq
    have he := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show globN s "ev" + a < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN s "ev" + b < 2 ^ 64 by omega)] at he
    omega
  unfold memW
  rw [hmemory _ (hne 64 120 (by decide) (by decide) (by decide))
    (hne 64 128 (by decide) (by decide) (by decide)),
    hmemory _ (hne 192 120 (by decide) (by decide) (by decide))
    (hne 192 128 (by decide) (by decide) (by decide))]

theorem precompile_store_output_at {F : Type} (s : PanSemStateFiniteExact 64 F)
    (off : Nat) (hoff : off = 120 ∨ off = 128) (val : ExpHOL 64)
    (hInv : EvmInv s)
    (hword : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
        ∃ w : BitVec 64, v = .val (.word w))
    (hfr : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) val)).1) :
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) val)).2 := by
  rcases hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) val) with ⟨r, post⟩
  simp only [hrun] at hfr ⊢
  cases r with
  | some res =>
    have herr : res = .error := by
      rw [evaluateHOLFiniteState_store] at hrun
      split at hrun <;> (try split at hrun) <;> (try split at hrun) <;>
        simp_all
    subst res
    rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h
  | none =>
    obtain ⟨he_lt, _, ⟨evw, hevw, hevn⟩, _, _⟩ := R11Shards.evm_head_globals hInv
    obtain ⟨w, _, hp⟩ := R11Shards.store_global_off_word (t := s) (post := post)
      (gname := "ev") (gbase := globN s "ev") (off := off) hevw hevn
      (by rcases hoff with rfl | rfl <;> omega) hword hrun
    have hmem : ∀ x : BitVec 64,
        x ≠ BitVec.ofNat 64 (globN s "ev" + 120) →
        x ≠ BitVec.ofNat 64 (globN s "ev" + 128) → post.memory x = s.memory x := by
      intro x h120 h128
      rw [hp]
      rcases hoff with rfl | rfl <;> simp [R11Shards.updW, h120, h128]
    apply precompile_output_fields_step hInv
      (by rw [hp]; exact guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1)
      (by rw [hp]) (by rw [hp]) hmem
    exact le_of_eq (precompile_output_fields_gas_eq hInv hmem)

theorem precompile_store_output_step (off : Nat) (hoff : off = 120 ∨ off = 128)
    (val : ExpHOL 64)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
        ∃ w : BitVec 64, v = .val (.word w)) :
    EvmProgStep frameStartGw
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) val) := by
  intro F s _ hInv _ hfr
  exact precompile_store_output_at s off hoff val hInv (hword s) hfr

theorem precompile_store_output_local_at {F : Type} (s : PanSemStateFiniteExact 64 F)
    (off : Nat) (hoff : off = 120 ∨ off = 128) (name : MlS) (w : BitVec 64)
    (hInv : EvmInv s) (hl : s.locals.lookup name = some (.val (.word w)))
    (hfr : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)])
        (.var .local name))).1) :
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)])
        (.var .local name))).2 := by
  apply precompile_store_output_at s off hoff _ hInv _ hfr
  intro v hv
  simp only [evalHOLExact, hl, Option.some.injEq] at hv
  exact ⟨w, hv.symm⟩

/-- Gas charging preserves all cells outside its two gas counters, including on errors. -/
theorem precompile_charge_gas_memory {F : Type} (s : PanSemStateFiniteExact 64 F)
    (evw amtw : BitVec 64)
    (hev : s.globals.lookup (ofString "ev") = some (.val (.word evw)))
    (hamt : s.locals.lookup (ofString "amount") = some (.val (.word amtw))) :
    ∀ x : BitVec 64, x ≠ evw + 64 → x ≠ evw + 184 →
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)).2.memory x = s.memory x := by
  intro x h64 h184
  change x ≠ evw + 64#64 at h64
  change x ≠ evw + 184#64 at h184
  have hbody : sourceFnBody Guest.Software.guestFn_charge_gas =
      .dec (ofString "gl") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 64]))
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount")))
            (.raise (ofString "EvmErr") (.const 4)) .skip)
          (.seq
            (.store (.op .add [.var .global (ofString "ev"), .const 64])
              (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")]))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 184])
                (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                  .var .local (ofString "amount")]))
              (.return (.const 0))))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · rename_i glv hgl
    obtain ⟨glw, rfl⟩ := EvmFrameSpecs.word_of_load_one s _ glv hgl
    simp only [shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
    let s1 := setVarHOLFinite (ofString "gl") (.val (.word glw)) s
    have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount"))) =
        some (.val (.word (if glw < amtw then 1 else 0))) := by
      simp [s1, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "gl" ≠ ofString "amount" by decide, hamt,
        Compiler.Encoders.Asm.wordCmpHOL]
    change (match evaluateHOLFiniteState s1 _ with
      | (r, post) => (r, {post with locals := (post.locals.resVarEq
          (ofString "gl", s.locals.lookup (ofString "gl")))})).2.memory x = s.memory x
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcmp]
    by_cases hlt : glw < amtw
    · simp only [hlt, ↓reduceIte, show (1 : BitVec 64) ≠ 0 by decide]
      rw [evaluateHOLFiniteState_raise]
      cases hs : s1.eshapes.lookup (ofString "EvmErr") <;>
        simp [evalHOLExact, hs, shapeOfHOLExact, emptyLocalsHOLFinite] <;>
        (first | rfl | (split_ifs <;> rfl))
    · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip]
      have hev1 : s1.globals.lookup (ofString "ev") = some (.val (.word evw)) := hev
      have hgl1 : s1.locals.lookup (ofString "gl") = some (.val (.word glw)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hamt1 : s1.locals.lookup (ofString "amount") = some (.val (.word amtw)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "gl" ≠ ofString "amount" by decide, hamt]
      dsimp only [s1, setVarHOLFinite] at *
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
      simp only [evalHOLExact, evalListHOLExact, hev1, hgl1, hamt1,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map,
        Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero,
        BitVec.sub_zero, flattenHOL, panMemStoresHOL, panMemStoreHOL,
        BitVec.add_zero]
      by_cases hd64 : s.memaddrs (evw + 64)
      · simp only [show (64 + 0 : BitVec 64) = 64 by decide, hd64, ↓reduceIte]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
        simp [evalHOLExact, evalListHOLExact, hev, hamt,
          HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "gl" ≠ ofString "amount" by decide,
          wordOpHOL, wordOp, valueIsWord, valueWord, memLoadHOLExact,
          flattenHOL, panMemStoresHOL, panMemStoreHOL, h64, h184,
          evaluateHOLFiniteState_return, emptyLocalsHOLFinite]
        by_cases hd184 : s.memaddrs (evw + 184)
        · change s.memaddrs (evw + 184#64) at hd184
          simp only [hd184, ↓reduceIte]
          cases hw : s.memory (evw + 184#64) with
          | word w =>
            simp [hw, valueWord, flattenHOL, panMemStoresHOL, panMemStoreHOL,
              hd184, h64, h184, shapeOfHOLExact, sizeOfShapeWithContextHOL]
        · change ¬s.memaddrs (evw + 184#64) at hd184
          simp [hd184, h64]
      · simp only [show (64 + 0 : BitVec 64) = 64 by decide, hd64, ↓reduceIte]

theorem precompile_charge_gas_chain_cells {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hInv : EvmInv s) (amtw : BitVec 64)
    (hamt : s.locals.lookup (ofString "amount") = some (.val (.word amtw))) :
    ChainCellsAgree s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)).2 := by
  obtain ⟨hb, _, ⟨evw, hev, hevn⟩, _, _⟩ := R11Shards.evm_head_globals hInv
  apply precompile_chain_cells_of_head_update hInv
  intro x hx
  apply precompile_charge_gas_memory s evw amtw hev hamt x
  · have hn := hx (globN s "ev" + 64) (by simp [R11Shards.headAllowedOffsets])
    simpa [← hevn, BitVec.ofNat_add, BitVec.ofNat_toNat] using hn
  · have hn := hx (globN s "ev" + 184) (by simp [R11Shards.headAllowedOffsets])
    simpa [← hevn, BitVec.ofNat_add, BitVec.ofNat_toNat] using hn

theorem precompile_charge_gas_chainCellsKept :
    ChainCellsKept EvmInv (ofString "charge_gas") := by
  refine ⟨_, _, _, EvmFrameSpecs.lookup_charge_gas, ?_⟩
  intro F s hcode hInv hex hnt hres
  obtain ⟨amtw, hamt⟩ := R11Shards.one_word_param_of_lookup
    EvmFrameSpecs.lookup_charge_gas hex
  exact precompile_charge_gas_chain_cells s hInv amtw hamt

private theorem precompile_step_locals_left {F : Type} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} (ls : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : EvmStepCC gw {s with locals := ls, clock := k} post) : EvmStepCC gw s post := by
  refine ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1,
    h.1.2.2.2.trans (evmChain_with_locals s ls k)⟩, ?_⟩
  intro ec hec
  exact h.2 ec ((evmChain_with_locals s ls k).symm ▸ hec)

private theorem precompile_step_locals_right {F : Type} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} (ls : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : EvmStepCC gw s post) : EvmStepCC gw s {post with locals := ls, clock := k} := by
  refine ⟨⟨localsFree_evmInv post ls k h.1.1, h.1.2.1, h.1.2.2.1,
    (evmChain_with_locals post ls k).trans h.1.2.2.2⟩, ?_⟩
  exact h.2

theorem precompile_call0_locals_on_flow {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64))
    (hr : (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call] at hr ⊢
  simp only [evalListHOLFinite_eq_toExact] at hr ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · simp [ha] at hr
  · simp only [ha] at hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fn vals with _ | ⟨body, callee, ret⟩
    · simp [hl] at hr
    · simp only [hl] at hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz, ↓reduceIte] at hr ⊢
        rcases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
        simp only [run] at hr ⊢
        cases res with
        | none => simp at hr
        | some r =>
          cases r <;> try simp at hr
          case returned v =>
            dsimp only at hr ⊢
            split at hr <;> simp_all

theorem precompile_step_call0 {fname : MlS}
    (hk : EvmKeeps EvmInv frameStartGw fname) (hc : ChainCellsKept EvmInv fname)
    (args : List (ExpHOL 64)) :
    EvmProgStep frameStartGw (.call (some (none, none)) fname args) := by
  have bad : ¬ R13.FlowsOrResumes (some (.error : PanSemResultExact 64)) := by
    rintro (h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩) <;> cases h
  intro F s hcode hInv hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp only [hargs] at hfr; exact absurd hfr bad
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · simp only [hl] at hfr; exact absurd hfr bad
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have heq : callEntryStateHOLFinite s callee =
            {s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock} := by
          cases s; rfl
        have hi : EvmInv (callEntryStateHOLFinite s callee) := by
          rw [heq]; exact localsFree_evmInv s callee _ hInv
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        have hp (hsafe : res ≠ some .timeOut) (hr : Resumes res) : EvmStepCC frameStartGw s post := by
          have hst := FunSpec.at_lookup hk s hcode values body' callee ret' hl hi
            (by rw [hrun]; exact hsafe)
          have hcc := FunSpec.at_lookup hc s hcode values body' callee ret' hl hi
            (by rw [hrun]; exact hsafe)
          rw [hrun] at hst hcc
          have hh : EvmStepCC frameStartGw (callEntryStateHOLFinite s callee) post := ⟨hst hr, hcc hr⟩
          rw [heq] at hh
          exact precompile_step_locals_left _ _ hh
        cases res with
        | none => exact absurd hfr bad
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hfr ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
            · simp only [hsh, ↓reduceIte] at hfr ⊢
              exact precompile_step_locals_right s.locals post.clock
                (hp (by simp) (Or.inl ⟨v, rfl⟩))
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              exact absurd hfr bad
          | exception e v =>
            dsimp only at hfr ⊢
            have hr : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hemp : emptyLocalsHOLFinite post =
                {post with locals := (emptyLocalsHOLFinite post).locals, clock := post.clock} := by
              cases post; rfl
            rw [hemp]
            exact precompile_step_locals_right _ post.clock (hp (by simp) hr)
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

theorem precompile_step_weaken {F : Type} {gw gw' : List String}
    {s post : PanSemStateFiniteExact 64 F}
    (hsub : ∀ k ∈ gw.map ofString, k ∈ gw'.map ofString)
    (h : EvmStepCC gw s post) : EvmStepCC gw' s post := by
  refine ⟨⟨h.1.1, h.1.2.1, ?_, h.1.2.2.2⟩, h.2⟩
  intro k hk
  exact h.1.2.2.1 k (fun hm => hk (hsub k hm))

theorem ek_cc_precompile_alloc :
    EvmKeeps EvmInv frameStartGw (ofString "alloc") ∧
      ChainCellsKept EvmInv (ofString "alloc") := by
  constructor
  · refine ⟨_, _, _, lookup_alloc_r16, ?_⟩
    intro F s hcode hi hex hnt hres
    exact (precompile_step_weaken (gw' := frameStartGw)
      (by intro k hk; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hk
          subst k; simp [frameStartGw])
      (alloc_body_evmStepCC s hi hres)).1
  · refine ⟨_, _, _, lookup_alloc_r16, ?_⟩
    intro F s hcode hi hex hnt hres
    exact (alloc_body_evmStepCC s hi hres).2

theorem precompile_decCall_alloc_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (cont : ProgHOL 64) (p : BitVec 64) (n : Nat)
    (hn : n = 40 ∨ n = 96 ∨ n = 32) (hInv : EvmInv s)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).1)
    (hcont : ∀ next : PanSemStateFiniteExact 64 F,
      next.locals.lookup x = some (.val (.word p)) →
      globN next "heap_ptr" = p.toNat + n →
      WordsOK next (p.toNat, n) → EvmStepCC frameStartGw s next →
      next.memory = s.memory → next.be = s.be →
      (∀ k, k ≠ x → next.locals.lookup k = s.locals.lookup k) →
      Resumes (evaluateHOLFiniteState next cont).1 →
      EvmStepCC frameStartGw next (evaluateHOLFiniteState next cont).2) :
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [.const (BitVec.ofNat 64 n)] cont)).2 := by
  obtain ⟨next, hx, hhp, hwords, hstep, hr, hs, hm, hb, hl⟩ :=
    transfer_decCall_alloc_exact_spec s x cont p n hn hInv hp hres
  have hstep' : EvmStepCC frameStartGw s next := precompile_step_weaken
    (by intro k hk; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hk
        subst k; simp [frameStartGw]) hstep
  have hc := hcont next hx hhp hwords hstep' hm hb hl (hr ▸ hres)
  have hboth : EvmStepCC frameStartGw s (evaluateHOLFiniteState next cont).2 := by
    refine ⟨⟨hc.1.1, le_trans hstep'.1.2.1 hc.1.2.1,
      fun k hk => (hstep'.1.2.2.1 k hk).trans (hc.1.2.2.1 k hk),
      hc.1.2.2.2.trans hstep'.1.2.2.2⟩, ?_⟩
    intro ec hec
    obtain ⟨a, b, c, d⟩ := hstep'.2 ec hec
    obtain ⟨a', b', c', d'⟩ := hc.2 ec (hstep'.1.2.2.2.symm ▸ hec)
    exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩
  rw [hs]
  exact ⟨⟨localsFree_evmInv _ _ _ hboth.1.1, hboth.1.2.1, hboth.1.2.2.1,
    (evmChain_with_locals _ _ _).trans hboth.1.2.2.2⟩, hboth.2⟩

theorem precompile_alloc_call_step (args : List (ExpHOL 64)) :
    EvmProgStep frameStartGw (.call (some (none, none)) (ofString "alloc") args) :=
  precompile_step_call0 ek_cc_precompile_alloc.1 ek_cc_precompile_alloc.2 args

theorem precompile_charge_gas_call_step (args : List (ExpHOL 64)) :
    EvmProgStep frameStartGw (.call (some (none, none)) (ofString "charge_gas") args) := by
  apply precompile_step_call0 (hc := precompile_charge_gas_chainCellsKept)
  obtain ⟨params, body, ret, hl, hs⟩ := EvmFrameSpecs.ek_charge_gas
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hcode hInv hex hnt hr
  have hh := hs s hcode hInv hex hnt hr
  exact ⟨hh.1, hh.2.1, fun k _ => hh.2.2.1 k (by simp), hh.2.2.2⟩

theorem precompile_step_dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64)
    {body : ProgHOL 64} (hb : EvmProgStep frameStartGw body) :
    EvmProgStep frameStartGw (.dec name shape init body) := by
  have bad : ¬ R13.FlowsOrResumes (some (.error : PanSemResultExact 64)) := by
    rintro (h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩) <;> cases h
  intro F s hcode hInv hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · exact absurd hfr bad
  · rename_i v hv
    by_cases hsh : shapeEqHOL shape (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
      have hset : setVarHOLFinite name v s =
          {s with locals := (setVarHOLFinite name v s).locals, clock := s.clock} := by
        cases s; rfl
      have hi : EvmInv (setVarHOLFinite name v s) := by
        rw [hset]; exact localsFree_evmInv s _ _ hInv
      have hh := hb (setVarHOLFinite name v s) hcode hi hnt hfr
      rw [hset] at hh
      exact precompile_step_locals_right _ _ (precompile_step_locals_left _ _ hh)
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
      exact absurd hfr bad

theorem precompile_step_decCall_ro_at {fn : MlS} (hf : ReadOnlyFn fn)
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hc : ∀ (v : ValueHOL 64) (k : Nat),
      let mid := {s with locals := (setVarHOLFinite name v s).locals, clock := k}
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      R13.FlowsOrResumes (evaluateHOLFiniteState mid cont).1 →
      EvmStepCC frameStartGw mid (evaluateHOLFiniteState mid cont).2)
    (hnt : (evaluateHOLFiniteState s (.decCall name shape fn args cont)).1 ≠ some .timeOut)
    (hfr : R13.FlowsOrResumes (evaluateHOLFiniteState s (.decCall name shape fn args cont)).1) :
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s (.decCall name shape fn args cont)).2 := by
  have bad : ¬ R13.FlowsOrResumes (some (.error : PanSemResultExact 64)) := by
    rintro (h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩) <;> cases h
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · simp only [ha] at hfr; exact absurd hfr bad
  · simp only [ha] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fn vals with _ | ⟨body', callee, ret'⟩
    · simp only [hl] at hfr; exact absurd hfr bad
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fn params body body'
          ret ret' vals callee (by rw [hcode]; exact hlook) hl
        subst hsame
        have hrEq := lookupCodeHOLFinite_installed_return s fn params body' body'
          ret ret' vals callee (by rw [hcode]; exact hlook) hl
        subst hrEq
        have entry : callEntryStateHOLFinite s callee =
            {s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock} := by cases s; rfl
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fn vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨vals, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
        rcases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [run] at hnt hfr ⊢
        cases res with
        | none => exact absurd hfr bad
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have ro := hspec (callEntryStateHOLFinite s callee) hcode
                (guestInv_callEntry s callee hInv.1.1) hex
                (by rw [run]; simp) (by rw [run]; exact Or.inl ⟨v, rfl⟩)
              rw [run] at ro
              dsimp only at ro
              have postEq := state_trans_locals_clock entry ro
              have midEq : setVarHOLFinite name v {post with locals := s.locals} =
                  {s with locals := (setVarHOLFinite name v s).locals, clock := post.clock} := by
                rw [postEq]; cases s; rfl
              rw [midEq] at hnt hfr ⊢
              have hh := hc v post.clock hnt hfr
              exact precompile_step_locals_right _ _ (precompile_step_locals_left _ _ hh)
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              exact absurd hfr bad
          | exception e v =>
            dsimp only at hfr ⊢
            have hr : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have ro := hspec (callEntryStateHOLFinite s callee) hcode
              (guestInv_callEntry s callee hInv.1.1) hex
              (by rw [run]; simp) (by rw [run]; exact hr)
            rw [run] at ro
            dsimp only at ro
            have postEq := state_trans_locals_clock entry ro
            have hemp : emptyLocalsHOLFinite post =
                {s with locals := (emptyLocalsHOLFinite post).locals, clock := post.clock} := by
              rw [postEq]; cases s; rfl
            rw [hemp]
            refine ⟨⟨localsFree_evmInv s _ _ hInv, le_refl _, fun _ _ => rfl,
              evmChain_with_locals s _ _⟩, ?_⟩
            intro ec hec; exact ⟨rfl, rfl, rfl, rfl⟩
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

theorem precompile_step_decCall_ro {fn : MlS} (hf : ReadOnlyFn fn)
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hc : EvmProgStep frameStartGw cont) :
    EvmProgStep frameStartGw (.decCall name shape fn args cont) := by
  intro F s hcode hInv hnt hfr
  apply precompile_step_decCall_ro_at hf name shape args cont s hcode hInv _ hnt hfr
  intro v k
  exact hc _ hcode (localsFree_evmInv s _ _ hInv)

theorem precompile_ro_add_sat : ReadOnlyFn (ofString "add_sat") := by
  refine R13.readOnlyFn_of_guestAst 441 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_add_sat rfl ?_
  dsimp only [Guest.Software.guestFn_add_sat, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact R13.ReadOnlyProg.dec _ _ _ (R13.ReadOnlyProg.seq
    (R13.ReadOnlyProg.ite _ (R13.ReadOnlyProg.ret _) R13.ReadOnlyProg.skip) (R13.ReadOnlyProg.ret _))

theorem precompile_ro_ceil32 : ReadOnlyFn (ofString "ceil32") := by
  refine R13.readOnlyFn_of_guestAst 442 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_ceil32 rfl ?_
  dsimp only [Guest.Software.guestFn_ceil32, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact R13.ReadOnlyProg.dec _ _ _ (R13.ReadOnlyProg.seq
    (R13.ReadOnlyProg.ite _ (R13.ReadOnlyProg.ret _) R13.ReadOnlyProg.skip)
    (R13.ReadOnlyProg.decCall precompile_ro_add_sat _ _ _ (R13.ReadOnlyProg.ret _)))

theorem precompile_ro_words_of : ReadOnlyFn (ofString "words_of") := by
  refine R13.readOnlyFn_of_guestAst 443 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_words_of rfl ?_
  dsimp only [Guest.Software.guestFn_words_of, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact R13.ReadOnlyProg.decCall precompile_ro_ceil32 _ _ _ (R13.ReadOnlyProg.ret _)

private theorem dispatch_step_trans {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    (h1 : EvmStepCC frameStartGw s mid) (h2 : EvmStepCC frameStartGw mid post) :
    EvmStepCC frameStartGw s post := by
  refine ⟨⟨h2.1.1, le_trans h1.1.2.1 h2.1.2.1,
    fun k hk => (h1.1.2.2.1 k hk).trans (h2.1.2.2.1 k hk),
    h2.1.2.2.2.trans h1.1.2.2.2⟩, ?_⟩
  intro ec hec
  obtain ⟨a, b, c, d⟩ := h1.2 ec hec
  obtain ⟨a', b', c', d'⟩ := h2.2 ec (h1.1.2.2.2.symm ▸ hec)
  exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩

private theorem dispatch_step_ro {p : ProgHOL 64} (h : ReadOnlyProg p) :
    EvmProgStep frameStartGw p := by
  intro F s hcode hInv hnt hfr
  have heq := h s hcode hInv.1.1 hnt hfr
  have hs := (EvmFrameSpecs.evmStep_refl_locals_clock hInv heq).1
  refine ⟨⟨hs.1, hs.2.1, fun k _ => hs.2.2.1 k (by simp), hs.2.2.2⟩, ?_⟩
  intro ec hec
  rw [heq]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem dispatch_step_seq {a b : ProgHOL 64}
    (ha : EvmProgStep frameStartGw a) (hb : EvmProgStep frameStartGw b) :
    EvmProgStep frameStartGw (.seq a b) := by
  intro F s hcode hInv hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s a).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
  simp only [hr] at hmeta hnt hfr ⊢
  change mid.code = s.code at hmeta
  cases r with
  | none =>
    have hs := ha s hcode hInv (by rw [hr]; simp) (by rw [hr]; exact Or.inl rfl)
    rw [hr] at hs
    exact dispatch_step_trans hs (hb mid (hmeta.trans hcode) hs.1.1 hnt hfr)
  | some r =>
    have hs := ha s hcode hInv (by rw [hr]; exact hnt) (by rw [hr]; exact hfr)
    rw [hr] at hs
    exact hs

theorem precompile_step_seq_at {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : ProgHOL 64)
    (ha : (evaluateHOLFiniteState s a).1 ≠ some .timeOut →
      R13.FlowsOrResumes (evaluateHOLFiniteState s a).1 →
        EvmStepCC frameStartGw s (evaluateHOLFiniteState s a).2)
    (hb : (evaluateHOLFiniteState s a).1 = none →
      (evaluateHOLFiniteState (evaluateHOLFiniteState s a).2 b).1 ≠ some .timeOut →
      R13.FlowsOrResumes (evaluateHOLFiniteState (evaluateHOLFiniteState s a).2 b).1 →
      EvmStepCC frameStartGw (evaluateHOLFiniteState s a).2
        (evaluateHOLFiniteState (evaluateHOLFiniteState s a).2 b).2)
    (hnt : (evaluateHOLFiniteState s (.seq a b)).1 ≠ some .timeOut)
    (hfr : R13.FlowsOrResumes (evaluateHOLFiniteState s (.seq a b)).1) :
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s (.seq a b)).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
  simp only [hr] at ha hb hnt hfr ⊢
  cases r with
  | none => exact dispatch_step_trans (ha (by simp) (Or.inl rfl)) (hb rfl hnt hfr)
  | some r => exact ha hnt hfr

theorem precompile_store_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addr val : ExpHOL 64) :
    (evaluateHOLFiniteState s (.store addr val)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_store]
  split <;> (try split) <;> (try split) <;> rfl

theorem precompile_seq_flows_left {F : Type}
    (s : PanSemStateFiniteExact 64 F) (first cont : ProgHOL 64)
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s (.seq first cont)).1) :
    R13.FlowsOrResumes (evaluateHOLFiniteState s first).1 := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases he : evaluateHOLFiniteState s first with ⟨r,t⟩
  cases r with
  | none => exact Or.inl rfl
  | some r => simpa only [he] using hr

theorem precompile_seq_flow_cases {F : Type}
    (s : PanSemStateFiniteExact 64 F) (first cont : ProgHOL 64)
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s (.seq first cont)).1) :
    ((evaluateHOLFiniteState s first).1 = none ∧
      R13.FlowsOrResumes
        (evaluateHOLFiniteState (evaluateHOLFiniteState s first).2 cont).1) ∨
      ((evaluateHOLFiniteState s first).1 = some .break ∨
        (evaluateHOLFiniteState s first).1 = some .continue ∨
        Resumes (evaluateHOLFiniteState s first).1) := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases he : evaluateHOLFiniteState s first with ⟨r,t⟩
  cases r with
  | none => exact Or.inl ⟨rfl,by simpa only [he] using hr⟩
  | some r =>
    right
    have hf : R13.FlowsOrResumes (some r) := by simpa only [he] using hr
    rcases hf with h | h
    · cases h
    · exact h

theorem precompile_seq_nonzero_or_early {F : Type}
    (s : PanSemStateFiniteExact 64 F) (first cont : ProgHOL 64)
    (pad : BitVec 64) (Rl : List Ivl) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (he : R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s first).2 Rl)
    (hc : ∀ t : PanSemStateFiniteExact 64 F, GuestInv t →
      t.globals.lookup (ofString "sha_pad") = some (.val (.word pad)) →
      R13.FlowsOrResumes (evaluateHOLFiniteState t cont).1 → pad.toNat ≠ 0)
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s (.seq first cont)).1) :
    pad.toNat ≠ 0 ∨
      (evaluateHOLFiniteState s first).1 = some .break ∨
      (evaluateHOLFiniteState s first).1 = some .continue ∨
      Resumes (evaluateHOLFiniteState s first).1 := by
  rcases precompile_seq_flow_cases s first cont hr with ⟨hn,hflow⟩ | hctrl
  · left
    exact hc _ (guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi)
      (by rw [he.globals]; exact hp) hflow
  · exact Or.inr hctrl

theorem precompile_while_no_loop_control {F : Type}
    (s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64) (body : ProgHOL 64) :
    (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .break ∧
    (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · simp
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        rcases run : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r,m⟩
        rw [run] at hle
        have hlt : m.clock < s.clock := by
          change m.clock ≤ s.clock - 1 at hle
          omega
        cases r with
        | none => exact precompile_while_no_loop_control m cond body
        | some r =>
          cases r with
          | «continue» => exact precompile_while_no_loop_control m cond body
          | _ => simp
    · simp
  · simp
termination_by s.clock

theorem precompile_while_not_resumes {F : Type}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hb : ∀ t : PanSemStateFiniteExact 64 F,
      ¬ Resumes (evaluateHOLFiniteState t body).1)
    (s : PanSemStateFiniteExact 64 F) :
    ¬ Resumes (evaluateHOLFiniteState s (.while cond body)).1 := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · simp [Resumes]
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have hn := hb (decClockHOLFinite s)
        have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        rcases run : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r,m⟩
        rw [run] at hn hle
        have hlt : m.clock < s.clock := by
          change m.clock ≤ s.clock - 1 at hle
          omega
        cases r with
        | none => exact precompile_while_not_resumes cond body hb m
        | some r =>
          cases r with
          | «continue» => exact precompile_while_not_resumes cond body hb m
          | _ => simpa [Resumes] using hn
    · simp [Resumes]
  · simp [Resumes]
termination_by s.clock

theorem precompile_seq_while_flows_right {F : Type}
    (s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64) (body cont : ProgHOL 64)
    (hb : ∀ t : PanSemStateFiniteExact 64 F,
      ¬ Resumes (evaluateHOLFiniteState t body).1)
    (hr : R13.FlowsOrResumes
      (evaluateHOLFiniteState s (.seq (.while cond body) cont)).1) :
    (evaluateHOLFiniteState s (.while cond body)).1 = none ∧
      R13.FlowsOrResumes (evaluateHOLFiniteState
        (evaluateHOLFiniteState s (.while cond body)).2 cont).1 := by
  rcases precompile_seq_flow_cases s (.while cond body) cont hr with h | h
  · exact h
  · rcases h with h | h | h
    · exact False.elim ((precompile_while_no_loop_control s cond body).1 h)
    · exact False.elim ((precompile_while_no_loop_control s cond body).2 h)
    · exact False.elim (precompile_while_not_resumes cond body hb s h)

theorem precompile_while_not_resumes_code {F : Type}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hb : ∀ t : PanSemStateFiniteExact 64 F, t.code = originalRuntimeCode →
      ¬ Resumes (evaluateHOLFiniteState t body).1)
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) :
    ¬ Resumes (evaluateHOLFiniteState s (.while cond body)).1 := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · simp [Resumes]
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have hn := hb (decClockHOLFinite s) hc
        have hmeta := evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
        have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        rcases run : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r,m⟩
        rw [run] at hn hle hmeta
        have hlt : m.clock < s.clock := by
          change m.clock ≤ s.clock - 1 at hle
          omega
        cases r with
        | none => exact precompile_while_not_resumes_code cond body hb m (hmeta.1.trans hc)
        | some r =>
          cases r with
          | «continue» => exact precompile_while_not_resumes_code cond body hb m (hmeta.1.trans hc)
          | _ => simpa [Resumes] using hn
    · simp [Resumes]
  · simp [Resumes]
termination_by s.clock

theorem precompile_memzero_null_128 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : GuestInv s)
    (hp : s.locals.lookup (ofString "dst") = some (.val (.word 0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 128))) :
    ¬ R13.FlowsOrResumes
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memzero)).1 := by
  have hd : ¬ s.memaddrs (BitVec.ofNat 64 0) := by
    rw [hi.memaddrs,Wave8Contracts.M08.ordinaryDomain_iff]
    norm_num [InitE.sourceBase]
  dsimp only [sourceFnBody,sourceFunctionEntry,Guest.Software.guestFn_memzero,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,Bool.true_eq,ite_true]
  intro hr
  have hr := precompile_seq_flows_left _ _ _ hr
  rw [evaluateHOLFiniteState_ite] at hr
  simp [evalHOLExact,evalListHOLExact,setVarHOLFinite,
    HolFiniteMapExact.lookup_update,FUPDATE,hp,valueIsWord,valueWord,
    wordOpHOL,wordOp,Compiler.Encoders.Asm.wordCmpHOL] at hr
  have hr := precompile_seq_flows_left _ _ _ hr
  rw [evaluateHOLFiniteState_while_total] at hr
  simp [evalHOLExact,evalListHOLExact,setVarHOLFinite,
    HolFiniteMapExact.lookup_update,FUPDATE,hp,hn,valueIsWord,valueWord,
    wordOpHOL,wordOp,Compiler.Encoders.Asm.wordCmpHOL] at hr
  norm_num [show ofString "i" ≠ ofString "n" by decide] at hr
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_store] at hr
  simp [evalHOLExact,evalListHOLExact,decClockHOLFinite,
    HolFiniteMapExact.lookup_update,FUPDATE,hp,valueIsWord,valueWord,
    wordOpHOL,wordOp,panMemStoresHOL,panMemStoreHOL,flattenHOL,hd,
    show ofString "i" ≠ ofString "dst" by decide] at hr
  split at hr <;> simp_all [R13.FlowsOrResumes,Resumes]

theorem precompile_sha256_state_init_null {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : GuestInv s)
    (hp : s.locals.lookup (ofString "stp") = some (.val (.word 0))) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256_state_init) =
      (some .error,s) := by
  have hd : ¬ s.memaddrs (0 : BitVec 64) := by
    rw [hi.memaddrs,Wave8Contracts.M08.ordinaryDomain_iff]
    change ¬ (0 % 8 = 0 ∧ sourceBase ≤ 0 ∧ 0 < heapEnd)
    norm_num [sourceBase]
  have hd' : ¬ s.memaddrs (BitVec.ofNat 64 0) := hd
  dsimp only [sourceFnBody,sourceFunctionEntry,Guest.Software.guestFn_sha256_state_init,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_store]
  simp [InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    evalHOLExact,evalListHOLExact,hp,panMemStoresHOL,panMemStoreHOL,
    valueIsWord,valueWord,wordOpHOL,wordOp,flattenHOL,hd']

theorem precompile_sha256_state_init_effect {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : BitVec 64) (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.locals.lookup (ofString "stp") = some (.val (.word p))) :
    R10Shards.P26_P28.ByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256_state_init)).2
      [(p.toNat, 64)] := by
  exact (R10Shards.P26_P28.checkWordStoresLocal_sound (ofString "stp") 64 (by decide) []
    (sourceFnBody Guest.Software.guestFn_sha256_state_init) rfl s p hc hi hp (by simp)).1

theorem precompile_sha256_block_no_catchable_exception {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (eid : MlS) (v : ValueHOL 64) (hne : eid ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256_block)).1 ≠
      some (.exception eid v) := by
  exact R16WkAcctWs.evaluate_noCatchableRaise (fun _ => false)
    (by intro f hf; cases hf) _ (by decide) s hc eid v hne

theorem precompile_sha256_block_effect {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : BitVec 64) (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.locals.lookup (ofString "stp") = some (.val (.word p))) :
    R10Shards.P26_P28.ByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256_block)).2
      [(p.toNat, 64)] := by
  exact (R10Shards.P26_P28.checkWordStoresLocal_sound (ofString "stp") 64 (by decide) []
    (sourceFnBody Guest.Software.guestFn_sha256_block) rfl s p hc hi hp (by simp)).1

theorem precompile_byteEff_to_region {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : R10Shards.P26_P28.ByteEff s post Rl) :
    InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s post Rl := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, ?_, ?_, ?_⟩
  · intro a ha
    by_contra hn
    exact ha (h.out_dom a hn)
  · intro a ha
    by_contra hn
    obtain ⟨i, hi, hh⟩ := h.cell_frame a hn
    exact ha i hi hh.2
  · intro b hb hn
    by_contra he
    obtain ⟨i, hi, hh⟩ := h.byte_frame b hb he
    exact hn i hi hh

theorem precompile_sha256_state_init_region {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : BitVec 64) (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.locals.lookup (ofString "stp") = some (.val (.word p))) :
    InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256_state_init)).2
      [(p.toNat, 64)] :=
  precompile_byteEff_to_region (precompile_sha256_state_init_effect s p hc hi hp)

theorem precompile_sha256_block_region {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : BitVec 64) (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.locals.lookup (ofString "stp") = some (.val (.word p))) :
    InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256_block)).2
      [(p.toNat, 64)] :=
  precompile_byteEff_to_region (precompile_sha256_block_effect s p hc hi hp)

theorem precompile_funByteEff_sha256_state_init :
    R10Shards.P26_P28.FunByteEff (ofString "sha256_state_init")
      (fun vals _ => [(R10Shards.P26_P28.valWordNat (vals[0]?.getD (.rStruct [])), 64)]) := by
  have hl : originalRuntimeCode.lookup (ofString "sha256_state_init") =
      some ([(ofString "stp", .one)], sourceFnBody Guest.Software.guestFn_sha256_state_init, .one) :=
    lookup_of_guestAst_getElem 92 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_state_init) rfl
  refine ⟨_, _, _, hl, ?_⟩
  intro F s vals hc hi hlook hnt hres
  obtain ⟨p, rfl, hp⟩ := R10Shards.P26_P28.lookupCode_one_word hl hlook
  exact precompile_sha256_state_init_effect s p hc hi hp

theorem precompile_funByteEff_sha256_block :
    R10Shards.P26_P28.FunByteEff (ofString "sha256_block")
      (fun vals _ => [(R10Shards.P26_P28.valWordNat (vals[0]?.getD (.rStruct [])), 64)]) := by
  have hl : originalRuntimeCode.lookup (ofString "sha256_block") =
      some ([(ofString "stp", .one), (ofString "blk", .one)],
        sourceFnBody Guest.Software.guestFn_sha256_block, .one) :=
    lookup_of_guestAst_getElem 93 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_block) rfl
  refine ⟨_, _, _, hl, ?_⟩
  intro F s vals hc hi hlook hnt hres
  obtain ⟨p, b, rfl, hp, hb⟩ := R10Shards.P26_P28.lookupCode_two_words (by decide) hl hlook
  exact precompile_sha256_block_effect s p hc hi hp

theorem precompile_byteEff_while_inv {F : Type}
    (P : PanSemStateFiniteExact 64 F → Prop) (cond : ExpHOL 64) (body : ProgHOL 64)
    (Rl : List Ivl)
    (hdec : ∀ s, P s → P (decClockHOLFinite s))
    (hb : ∀ (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → GuestInv s → P s →
      R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s body).2 Rl ∧
      ((evaluateHOLFiniteState s body).1 = none ∨
        (evaluateHOLFiniteState s body).1 = some .continue →
        P (evaluateHOLFiniteState s body).2))
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (hi : GuestInv s) (hp : P s) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s (.while cond body)).2 Rl := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · exact (R10Shards.P26_P28.ByteEff.refl s Rl).locals_clock _ s.clock
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have hgd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hi
        obtain ⟨he, hP⟩ := hb (decClockHOLFinite s) hc hgd (hdec s hp)
        have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        rcases run : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r, mid⟩
        rw [run] at he hP rem
        have hlt : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
        have heff : R10Shards.P26_P28.ByteEff s mid Rl :=
          ((R10Shards.P26_P28.ByteEff.refl s Rl).locals_clock _ _).trans he
        have hgm : GuestInv mid := guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hi
        cases r with
        | none => exact heff.trans (precompile_byteEff_while_inv P cond body Rl hdec hb
            mid (heff.code.trans hc) hgm (hP (Or.inl rfl)))
        | some r =>
          cases r with
          | «continue» => exact heff.trans (precompile_byteEff_while_inv P cond body Rl hdec hb
              mid (heff.code.trans hc) hgm (hP (Or.inr rfl)))
          | _ => exact heff
    · exact R10Shards.P26_P28.ByteEff.refl s Rl
  · exact R10Shards.P26_P28.ByteEff.refl s Rl
termination_by s.clock

theorem precompile_byteEff_while_guard_inv {F : Type}
    (P : PanSemStateFiniteExact 64 F → Prop) (cond : ExpHOL 64) (body : ProgHOL 64)
    (Rl : List Ivl)
    (hdec : ∀ s, P s → P (decClockHOLFinite s))
    (hb : ∀ (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → GuestInv s → P s →
      LoopActive cond s →
      R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s body).2 Rl ∧
      ((evaluateHOLFiniteState s body).1 = none ∨
        (evaluateHOLFiniteState s body).1 = some .continue →
        P (evaluateHOLFiniteState s body).2))
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (hi : GuestInv s) (hp : P s) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s (.while cond body)).2 Rl := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · exact (R10Shards.P26_P28.ByteEff.refl s Rl).locals_clock _ s.clock
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have hgd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hi
        have hguard : LoopActive cond (decClockHOLFinite s) :=
          loopActive_decClock ⟨_, by assumption, by assumption⟩
        obtain ⟨he, hP⟩ := hb (decClockHOLFinite s) hc hgd (hdec s hp) hguard
        have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        rcases run : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r, mid⟩
        rw [run] at he hP rem
        have hlt : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
        have heff : R10Shards.P26_P28.ByteEff s mid Rl :=
          ((R10Shards.P26_P28.ByteEff.refl s Rl).locals_clock _ _).trans he
        have hgm : GuestInv mid := guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hi
        cases r with
        | none => exact heff.trans (precompile_byteEff_while_guard_inv P cond body Rl hdec hb
            mid (heff.code.trans hc) hgm (hP (Or.inl rfl)))
        | some r =>
          cases r with
          | «continue» => exact heff.trans (precompile_byteEff_while_guard_inv P cond body Rl hdec hb
              mid (heff.code.trans hc) hgm (hP (Or.inr rfl)))
          | _ => exact heff
    · exact R10Shards.P26_P28.ByteEff.refl s Rl
  · exact R10Shards.P26_P28.ByteEff.refl s Rl
termination_by s.clock

theorem precompile_sha256_finish_store_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out i : BitVec 64) (value : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hindex : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hib : i.toNat < 8) (hob : out.toNat + 32 < 2^64)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be32")
      [.op .add [.var .local (ofString "out"),
        .panop .mul [.var .local (ofString "i"), .const 4]], value])).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be32")
      [.op .add [.var .local (ofString "out"),
        .panop .mul [.var .local (ofString "i"), .const 4]], value])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be32")
      [.op .add [.var .local (ofString "out"),
        .panop .mul [.var .local (ofString "i"), .const 4]], value])).1) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "st_be32")
        [.op .add [.var .local (ofString "out"),
          .panop .mul [.var .local (ofString "i"), .const 4]], value])).2 [(out.toNat,32)] := by
  apply R10Shards.P26_P28.call0_byteEff R10Shards.P26_P28.funByteEff_st_be32 s _ _ hc hi ?_ hnt hr
  intro vals hvals region hregion hpos
  have hm : (i * (4 : BitVec 64)).toNat = i.toNat * 4 := by
    rw [BitVec.toNat_mul]
    change (i.toNat * 4) % 2^64 = i.toNat * 4
    exact Nat.mod_eq_of_lt (by omega)
  have ha : (out + i * (4 : BitVec 64)).toNat = out.toNat + i.toNat * 4 := by
    rw [BitVec.toNat_add, hm]
    exact Nat.mod_eq_of_lt (by omega)
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hout, hindex,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] at hvals
  split at hvals
  · rename_i v vs hv hvs
    injection hvals with hvls
    subst vals
    injection hv with hv
    subst v
    simp only [List.getElem?_cons_zero, Option.getD_some, R10Shards.P26_P28.valWordNat,
      List.mem_singleton] at hregion
    subst region
    refine ⟨(out.toNat,32), List.mem_singleton.mpr rfl, ?_, ?_⟩
    · change out.toNat ≤ (out + i * (4 : BitVec 64)).toNat
      rw [ha]; omega
    · change (out + i * (4 : BitVec 64)).toNat + 4 ≤ out.toNat + 32
      rw [ha]; omega
  · simp at hvals

theorem precompile_sha256_finish_guard {F : Type}
    (s : PanSemStateFiniteExact 64 F) (i : BitVec 64)
    (hindex : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hsmall : i.toNat < 2^63)
    (ha : LoopActive (.cmp .less (.var .local (ofString "i")) (.const 8)) s) :
    i.toNat < 8 := by
  obtain ⟨v, hv, hn⟩ := ha
  simp [evalHOLFinite, evalHOLExact, hindex, Compiler.Encoders.Asm.wordCmpHOL] at hv
  have hs := holAsmSignedLess_small i (8#64) hsmall (by decide)
  simp only [hs, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_true_eq] at hv
  by_cases h : i.toNat < 8
  · exact h
  · simp [h] at hv
    exact False.elim (hn hv.symm)

theorem precompile_sha256_finish_increment {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out i : BitVec 64)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hindex : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hvalid : isValidValueHOLExact s.toExact .local (ofString "i")
      (.val (.word (i+1))) = true) :
    let post := (evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))).2
    post.locals.lookup (ofString "out") = some (.val (.word out)) ∧
    post.locals.lookup (ofString "i") = some (.val (.word (i+1))) := by
  change isValidValueHOLExact s.toExact .local (ofString "i")
    (.val (.word (i+1#64))) = true at hvalid
  simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hindex,
    valueIsWord, valueWord, wordOpHOL, wordOp, setVarHOLFinite,
    HolFiniteMapExact.lookup_update, FUPDATE, hout, hvalid, setKvarHOLFinite,
    show ofString "i" ≠ ofString "out" by decide]

theorem precompile_call0_byteEff_total {F : Type} (fname : MlS)
    (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (ret : ShapeHOL)
    (argR : List (ValueHOL 64) → List Ivl)
    (hl : originalRuntimeCode.lookup fname = some (params, body, ret))
    (hf : ∀ (entry : PanSemStateFiniteExact 64 F) vals,
      entry.code = originalRuntimeCode → GuestInv entry →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, entry.locals, ret) →
      R10Shards.P26_P28.ByteEff entry (evaluateHOLFiniteState entry body).2 (argR vals))
    (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64)) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hsub : ∀ vals,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      ∀ i ∈ argR vals, 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    R10Shards.P26_P28.ByteEff s
      (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 Rl := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact R10Shards.P26_P28.ByteEff.refl s Rl
  · dsimp only
    rcases hlook : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact R10Shards.P26_P28.ByteEff.refl s Rl
    · dsimp only
      have heq := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hl) hlook
      subst heq
      have heq := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hl) hlook
      subst heq
      by_cases hz : s.clock = 0
      · simp only [hz, ↓reduceIte]
        exact (R10Shards.P26_P28.ByteEff.refl s Rl).locals_clock _ _
      · simp only [hz, ↓reduceIte]
        let entry := callEntryStateHOLFinite s callee
        have hge : GuestInv entry := guestInv_callEntry s callee hi
        have hle : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals =
            some (body', entry.locals, ret') := by
          simpa [hc, entry, callEntryStateHOLFinite] using hlook
        have he := hf entry vals hc hge hle
        dsimp only [entry] at he
        rcases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        rw [run] at he
        have eff : R10Shards.P26_P28.ByteEff s post Rl :=
          (((R10Shards.P26_P28.ByteEff.refl s _).locals_clock _ _).trans he).mono (hsub vals hargs)
        cases res with
        | none => exact eff.locals_clock _ _
        | some r =>
          cases r <;> dsimp only
          all_goals first
            | exact eff.locals_clock _ _
            | (split <;> exact eff.locals_clock _ _)

theorem precompile_sha256_block_call_not_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64))
    (hc : s.code = originalRuntimeCode) :
    ¬ Resumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256_block") args)).1 := by
  have hl : originalRuntimeCode.lookup (ofString "sha256_block") =
      some ([(ofString "stp",.one),(ofString "blk",.one)],
        sourceFnBody Guest.Software.guestFn_sha256_block,.one) :=
    lookup_of_guestAst_getElem 93 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_block) rfl
  have hn := R16WkAcctWs.evaluate_noCatchableRaise
    (fun f => f == ofString "sha256_block") ?_
    (.call (some (none,none)) (ofString "sha256_block") args) rfl s hc
  · intro hr
    rcases hr with ⟨v,hr⟩ | ⟨e,v,hr,hne⟩
    · rw [evaluateHOLFiniteState_call] at hr
      split at hr
      · simp at hr
      · dsimp only at hr
        split at hr
        · simp at hr
        · split at hr
          · simp at hr
          · split at hr <;> try simp_all
            split at hr <;> simp_all
    · exact hn e v hne hr
  · intro f hf vals body callee ret hlook
    have he : f = ofString "sha256_block" := by simpa using hf
    subst f
    have he := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ ret _ callee hl hlook
    subst he
    decide

theorem precompile_sha256_blocks_body_not_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) :
    ¬ Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (none,none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"),.var .local (ofString "i")]])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"),.const 64])))).1 := by
  have hn := precompile_sha256_block_call_not_resumes s
    [.var .global (ofString "sha_st"),
      .op .add [.var .local (ofString "p"),.var .local (ofString "i")]] hc
  rw [evaluateHOLFiniteState_seq_line780]
  rcases run : evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"),.var .local (ofString "i")]]) with ⟨r,m⟩
  cases r with
  | none =>
    dsimp only
    rw [evaluateHOLFiniteState_assign]
    split
    · simp [Resumes]
    · split <;> simp [Resumes]
  | some r => simpa only [run] using hn

theorem precompile_sha256_block_call_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (stp : BitVec 64) (ptr block : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) ptr =
      some (.val (.word stp))) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "sha256_block") [ptr, block])).2 [(stp.toNat,64)] := by
  have hl : originalRuntimeCode.lookup (ofString "sha256_block") =
      some ([(ofString "stp", .one), (ofString "blk", .one)],
        sourceFnBody Guest.Software.guestFn_sha256_block, .one) :=
    lookup_of_guestAst_getElem 93 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_block) rfl
  refine precompile_call0_byteEff_total _ _ _ _
    (fun vals => [(R10Shards.P26_P28.valWordNat (vals[0]?.getD (.rStruct [])),64)]) hl ?_ s _ _ hc hi ?_
  · intro entry vals hce hge hle
    obtain ⟨p, b, rfl, hpe, hbe⟩ := R10Shards.P26_P28.lookupCode_two_words (by decide) hl hle
    exact precompile_sha256_block_effect entry p hce hge hpe
  · intro vals hv r hr hpos
    change @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) ptr = some (.val (.word stp)) at hp
    simp [evalListHOLFinite, evalListHOLExact, hp] at hv
    split at hv
    · rename_i v vs hv1 hv2
      injection hv1 with hv1
      subst v
      injection hv with hv
      subst vals
      simp only [List.getElem?_cons_zero, Option.getD_some, R10Shards.P26_P28.valWordNat,
        List.mem_singleton] at hr
      subst r
      exact ⟨(stp.toNat,64), List.mem_singleton.mpr rfl, le_rfl, le_rfl⟩
    · simp at hv

theorem precompile_sha256_init_call_null_not_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ptr : ExpHOL 64) (hi : GuestInv s)
    (hp : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) ptr =
      some (.val (.word 0))) :
    ¬ Resumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256_state_init") [ptr])).1 := by
  have hl : originalRuntimeCode.lookup (ofString "sha256_state_init") =
      some ([(ofString "stp",.one)],sourceFnBody Guest.Software.guestFn_sha256_state_init,.one) :=
    lookup_of_guestAst_getElem 92 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_state_init) rfl
  rw [evaluateHOLFiniteState_call]
  have hv : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ptr] =
      some [.val (.word 0)] := by
    change @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) ptr = _ at hp
    simp [evalListHOLFinite,evalListHOLExact,hp]
  rw [hv]
  dsimp only
  rcases hlook : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup
      (ofString "sha256_state_init") [.val (.word 0)] with _ | ⟨body,callee,ret⟩
  · simp [Resumes]
  · dsimp only
    have heq := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ ret _ callee
      (by rw [hi.code]; exact hl) hlook
    subst heq
    have heq := lookupCodeHOLFinite_installed_return s _ _ _ _ .one ret _ callee
      (by rw [hi.code]; exact hl) hlook
    subst heq
    obtain ⟨p,hvals,hpe⟩ := R10Shards.P26_P28.lookupCode_one_word hl
      (by simpa only [hi.code] using hlook)
    have hp0 : p = 0 := by simpa using hvals.symm
    subst p
    by_cases hz : s.clock = 0
    · simp [hz,Resumes]
    · rw [if_neg hz]
      rw [precompile_sha256_state_init_null _ (guestInv_callEntry s callee hi) hpe]
      simp [Resumes]

theorem precompile_sha256_init_call_null_not_flows {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ptr : ExpHOL 64) (hi : GuestInv s)
    (hp : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) ptr =
      some (.val (.word 0))) :
    ¬ R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256_state_init") [ptr])).1 := by
  have hl : originalRuntimeCode.lookup (ofString "sha256_state_init") =
      some ([(ofString "stp",.one)],sourceFnBody Guest.Software.guestFn_sha256_state_init,.one) :=
    lookup_of_guestAst_getElem 92 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_state_init) rfl
  rw [evaluateHOLFiniteState_call]
  have hv : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ptr] =
      some [.val (.word 0)] := by
    change @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) ptr = _ at hp
    simp [evalListHOLFinite,evalListHOLExact,hp]
  rw [hv]
  dsimp only
  rcases hlook : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup
      (ofString "sha256_state_init") [.val (.word 0)] with _ | ⟨body,callee,ret⟩
  · simp [R13.FlowsOrResumes,Resumes]
  · dsimp only
    have heq := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ ret _ callee
      (by rw [hi.code]; exact hl) hlook
    subst heq
    have heq := lookupCodeHOLFinite_installed_return s _ _ _ _ .one ret _ callee
      (by rw [hi.code]; exact hl) hlook
    subst heq
    obtain ⟨p,hvals,hpe⟩ := R10Shards.P26_P28.lookupCode_one_word hl
      (by simpa only [hi.code] using hlook)
    have hp0 : p = 0 := by simpa using hvals.symm
    subst p
    by_cases hz : s.clock = 0
    · simp [hz,R13.FlowsOrResumes,Resumes]
    · rw [if_neg hz]
      rw [precompile_sha256_state_init_null _ (guestInv_callEntry s callee hi) hpe]
      simp [R13.FlowsOrResumes,Resumes]

theorem precompile_memzero_call_null_128_not_flows {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ptr : ExpHOL 64) (hi : GuestInv s)
    (hp : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) ptr =
      some (.val (.word 0))) :
    ¬ R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "memzero") [ptr,.const 128])).1 := by
  have hl : originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst",.one),(ofString "n",.one)],
        sourceFnBody Guest.Software.guestFn_memzero,.one) :=
    lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_memzero) rfl
  intro hr
  rw [evaluateHOLFiniteState_call] at hr
  have hv : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [ptr,.const 128] = some [.val (.word 0),.val (.word 128)] := by
    change @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) ptr = _ at hp
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hp]
  rw [hv] at hr
  dsimp only at hr
  rcases hlook : lookupCodeHOLFinite s.code.lookup (ofString "memzero")
      [.val (.word 0),.val (.word 128)] with _ | ⟨body,callee,ret⟩
  · rw [hlook] at hr
    simp [R13.FlowsOrResumes,Resumes] at hr
  · rw [hlook] at hr
    dsimp only at hr
    have heq := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ ret _ callee
      (by rw [hi.code]; exact hl) hlook
    subst heq
    have heq := lookupCodeHOLFinite_installed_return s _ _ _ _ .one ret _ callee
      (by rw [hi.code]; exact hl) hlook
    subst heq
    obtain ⟨p,n,hvals,hpe,hne⟩ := R10Shards.P26_P28.lookupCode_two_words (by decide) hl
      (by simpa only [hi.code] using hlook)
    have he : p = 0 ∧ n = 128 := by simpa using hvals.symm
    rcases he with ⟨rfl,rfl⟩
    by_cases hz : s.clock = 0
    · simp [hz,R13.FlowsOrResumes,Resumes] at hr
    · rw [if_neg hz] at hr
      apply precompile_memzero_null_128 _ (guestInv_callEntry s callee hi) hpe hne
      rcases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
          (sourceFnBody Guest.Software.guestFn_memzero) with ⟨r,post⟩
      cases r with
      | none => exact Or.inl rfl
      | some r => cases r <;> simp_all [R13.FlowsOrResumes,Resumes]

theorem precompile_memzero_128_nonzero_of_flow {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ptr : ExpHOL 64) (pad : BitVec 64)
    (hi : GuestInv s)
    (hp : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) ptr =
      some (.val (.word pad)))
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "memzero") [ptr,.const 128])).1) :
    pad.toNat ≠ 0 := by
  intro hz
  have he : pad = 0 := BitVec.eq_of_toNat_eq hz
  subst pad
  exact precompile_memzero_call_null_128_not_flows s ptr hi hp hr

theorem precompile_sha256_padding_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad : BitVec 64) (cont : ProgHOL 64)
    (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.seq (.call (some (none,none)) (ofString "memzero")
        [.var .global (ofString "sha_pad"),.const 128]) cont)).1) :
    pad.toNat ≠ 0 :=
  precompile_memzero_128_nonzero_of_flow s _ pad hi
    (by simp [evalHOLFinite,evalHOLExact,hp])
    (precompile_seq_flows_left s _ cont hr)

theorem precompile_sha256_remainder_padding_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad : BitVec 64)
    (init : ExpHOL 64) (cont : ProgHOL 64) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.dec (ofString "rem") .one init
        (.seq (.call (some (none,none)) (ofString "memzero")
          [.var .global (ofString "sha_pad"),.const 128]) cont))).1) :
    pad.toNat ≠ 0 := by
  rw [evaluateHOLFiniteState_dec_total] at hr
  dsimp only at hr
  split at hr
  · simp [R13.FlowsOrResumes,Resumes] at hr
  · split at hr
    · exact precompile_sha256_padding_nonzero _ pad cont
        (guestInv_setVar _ _ s hi) hp hr
    · simp [R13.FlowsOrResumes,Resumes] at hr

theorem precompile_sha256_loop_exit_padding_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp : BitVec 64)
    (init : ExpHOL 64) (cont : ProgHOL 64) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.seq (.while (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"),.const 64]))
        (.seq (.call (some (none,none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .local (ofString "p"),.var .local (ofString "i")]])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"),.const 64]))))
        (.dec (ofString "rem") .one init
          (.seq (.call (some (none,none)) (ofString "memzero")
            [.var .global (ofString "sha_pad"),.const 128]) cont)))).1) :
    pad.toNat ≠ 0 := by
  have he : R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"),.const 64]))
        (.seq (.call (some (none,none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .local (ofString "p"),.var .local (ofString "i")]])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"),.const 64]))))).2
      [(stp.toNat,64)] := by
    apply precompile_byteEff_while_inv
      (fun t => t.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
      _ _ _ (by intro t ht; exact ht) ?_ s hi.code hi hs
    intro t hct hgt hpt
    have he := precompile_sha256_block_call_effect t stp
      (.var .global (ofString "sha_st"))
      (.op .add [.var .local (ofString "p"),.var .local (ofString "i")])
      hct hgt (by simp [evalHOLFinite,evalHOLExact,hpt])
    have hes := R10Shards.P26_P28.byteEff_seq he
      (fun m hm => R10Shards.P26_P28.byteEff_assign_local m (ofString "i")
        (.op .add [.var .local (ofString "i"),.const 64]) _)
    exact ⟨hes,fun _ => by rw [hes.globals]; exact hpt⟩
  have hloop : (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"),.const 64]))
        (.seq (.call (some (none,none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .local (ofString "p"),.var .local (ofString "i")]])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"),.const 64]))))).1 = none := by
    rcases precompile_seq_flow_cases s _ _ hr with h | h
    · exact h.1
    · rcases h with h | h | h
      · exact False.elim ((precompile_while_no_loop_control s _ _).1 h)
      · exact False.elim ((precompile_while_no_loop_control s _ _).2 h)
      · exact False.elim (precompile_while_not_resumes_code _ _
          (fun t ht => precompile_sha256_blocks_body_not_resumes t ht) s hi.code h)
  rw [evaluateHOLFiniteState_seq_line780] at hr
  dsimp only at hr
  rw [hloop] at hr
  exact precompile_sha256_remainder_padding_nonzero _ pad init cont
    (guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi)
    (by rw [he.globals]; exact hp) hr

theorem precompile_sha256_init_nonzero_of_flow {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ptr : ExpHOL 64) (stp : BitVec 64)
    (hi : GuestInv s)
    (hp : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) ptr =
      some (.val (.word stp)))
    (hflow : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256_state_init") [ptr])).1) :
    stp.toNat ≠ 0 := by
  intro hz
  have hzero : stp = 0 := BitVec.eq_of_toNat_eq hz
  subst stp
  exact precompile_sha256_init_call_null_not_flows s ptr hi hp hflow

theorem precompile_sha256_init_nonzero_of_sequence {F : Type}
    (s : PanSemStateFiniteExact 64 F) (ptr : ExpHOL 64) (stp : BitVec 64)
    (cont : ProgHOL 64) (hi : GuestInv s)
    (hp : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) ptr =
      some (.val (.word stp)))
    (hflow : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.seq (.call (some (none,none)) (ofString "sha256_state_init") [ptr]) cont)).1) :
    stp.toNat ≠ 0 :=
  precompile_sha256_init_nonzero_of_flow s ptr stp hi hp
    (precompile_seq_flows_left s _ cont hflow)

theorem precompile_sha256_body_state_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (stp : BitVec 64) (hi : GuestInv s)
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hflow : R13.FlowsOrResumes
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256)).1) :
    stp.toNat ≠ 0 := by
  change R13.FlowsOrResumes (evaluateHOLFiniteState s (.seq
    (.call (some (none,none)) (ofString "sha256_state_init")
      [.var .global (ofString "sha_st")]) _)).1 at hflow
  exact precompile_sha256_init_nonzero_of_sequence s _ stp _ hi
    (by simp [evalHOLFinite,evalHOLExact,hs]) hflow

theorem precompile_sha256_call_state_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (stp : BitVec 64) (args : List (ExpHOL 64))
    (hi : GuestInv s)
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256") args)).1) :
    stp.toNat ≠ 0 := by
  have hl : originalRuntimeCode.lookup (ofString "sha256") =
      some ([(ofString "p",.one),(ofString "len",.one),(ofString "out",.one)],
        sourceFnBody Guest.Software.guestFn_sha256,.one) :=
    lookup_of_guestAst_getElem 95 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256) rfl
  rw [evaluateHOLFiniteState_call] at hr
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · rw [ha] at hr
    simp [R13.FlowsOrResumes,Resumes] at hr
  · rw [ha] at hr
    dsimp only at hr
    rcases hlook : lookupCodeHOLFinite s.code.lookup (ofString "sha256") vals with _ | ⟨body,callee,ret⟩
    · simp [hlook,R13.FlowsOrResumes,Resumes] at hr
    · rw [hlook] at hr
      dsimp only at hr
      have heq := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ ret _ callee
        (by rw [hi.code]; exact hl) hlook
      subst heq
      by_cases hz : s.clock = 0
      · simp [hz,R13.FlowsOrResumes,Resumes] at hr
      · rw [if_neg hz] at hr
        have hbody : R13.FlowsOrResumes (evaluateHOLFiniteState
            (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_sha256)).1 := by
          rcases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
              (sourceFnBody Guest.Software.guestFn_sha256) with ⟨r,post⟩
          cases r with
          | none => exact Or.inl rfl
          | some r =>
            cases r <;> simp_all [R13.FlowsOrResumes,Resumes]
        exact precompile_sha256_body_state_nonzero _ stp
          (guestInv_callEntry s callee hi) hs hbody

theorem precompile_sha256_init_call_not_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64))
    (hc : s.code = originalRuntimeCode) :
    ¬ Resumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256_state_init") args)).1 := by
  have hl : originalRuntimeCode.lookup (ofString "sha256_state_init") =
      some ([(ofString "stp",.one)],
        sourceFnBody Guest.Software.guestFn_sha256_state_init,.one) :=
    lookup_of_guestAst_getElem 92 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_state_init) rfl
  have hn := R16WkAcctWs.evaluate_noCatchableRaise
    (fun f => f == ofString "sha256_state_init") ?_
    (.call (some (none,none)) (ofString "sha256_state_init") args) rfl s hc
  · intro hr
    rcases hr with ⟨v,hr⟩ | ⟨e,v,hr,hne⟩
    · rw [evaluateHOLFiniteState_call] at hr
      split at hr
      · simp at hr
      · dsimp only at hr
        split at hr
        · simp at hr
        · split at hr
          · simp at hr
          · split at hr <;> try simp_all
            split at hr <;> simp_all
    · exact hn e v hne hr
  · intro f hf vals body callee ret hlook
    have he : f = ofString "sha256_state_init" := by simpa using hf
    subst f
    have he := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ ret _ callee hl hlook
    subst he
    decide

theorem precompile_sha256_init_call_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (stp : BitVec 64) (ptr : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) ptr =
      some (.val (.word stp))) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "sha256_state_init") [ptr])).2 [(stp.toNat,64)] := by
  have hl : originalRuntimeCode.lookup (ofString "sha256_state_init") =
      some ([(ofString "stp", .one)], sourceFnBody Guest.Software.guestFn_sha256_state_init, .one) :=
    lookup_of_guestAst_getElem 92 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_state_init) rfl
  refine precompile_call0_byteEff_total _ _ _ _
    (fun vals => [(R10Shards.P26_P28.valWordNat (vals[0]?.getD (.rStruct [])),64)]) hl ?_ s _ _ hc hi ?_
  · intro entry vals hce hge hle
    obtain ⟨p, rfl, hpe⟩ := R10Shards.P26_P28.lookupCode_one_word hl hle
    exact precompile_sha256_state_init_effect entry p hce hge hpe
  · intro vals hv r hr hpos
    change @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) ptr = some (.val (.word stp)) at hp
    simp [evalListHOLFinite, evalListHOLExact, hp] at hv
    subst vals
    simp only [List.getElem?_cons_zero, Option.getD_some, R10Shards.P26_P28.valWordNat,
      List.mem_singleton] at hr
    subst r
    exact ⟨(stp.toNat,64), List.mem_singleton.mpr rfl, le_rfl, le_rfl⟩

theorem precompile_sha256_blocks_loop_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (stp : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_st") = some (.val (.word stp))) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"), .const 64]))
        (.seq (.call (some (none, none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 64]))))).2 [(stp.toNat,64)] := by
  apply precompile_byteEff_while_inv
    (fun t => t.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    _ _ _ (by intro t ht; exact ht) ?_ s hc hi hp
  intro t hct hgt hpt
  have he := precompile_sha256_block_call_effect t stp
    (.var .global (ofString "sha_st"))
    (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])
    hct hgt (by simp [evalHOLFinite, evalHOLExact, hpt])
  have hes := R10Shards.P26_P28.byteEff_seq he
    (fun m hm => R10Shards.P26_P28.byteEff_assign_local m (ofString "i")
      (.op .add [.var .local (ofString "i"), .const 64]) _)
  refine ⟨hes, ?_⟩
  intro hr
  rw [hes.globals]
  exact hpt

theorem precompile_sha256_body_padding_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp : BitVec 64) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hr : R13.FlowsOrResumes
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256)).1) :
    pad.toNat ≠ 0 := by
  change R13.FlowsOrResumes (evaluateHOLFiniteState s (.seq
    (.call (some (none,none)) (ofString "sha256_state_init")
      [.var .global (ofString "sha_st")]) _)).1 at hr
  have he := precompile_sha256_init_call_effect s stp (.var .global (ofString "sha_st"))
    hi.code hi (by simp [evalHOLFinite,evalHOLExact,hs])
  rcases precompile_seq_flow_cases s _ _ hr with ⟨hn,hflow⟩ | hctrl
  · have him := guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi
    have hpm := hp
    rw [←he.globals] at hpm
    have hsm := hs
    rw [←he.globals] at hsm
    change R13.FlowsOrResumes (evaluateHOLFiniteState _ (.dec (ofString "i") .one (.const 0) _)).1 at hflow
    rw [evaluateHOLFiniteState_dec_total] at hflow
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,Bool.true_eq,ite_true] at hflow
    exact precompile_sha256_loop_exit_padding_nonzero _ pad stp _ _
      (guestInv_setVar _ _ _ him) hpm hsm hflow
  · rcases hctrl with h | h | h
    · rw [evaluateHOLFiniteState_call] at h
      split at h <;> try simp_all
      try dsimp only at h
      split at h <;> try simp_all
      split at h <;> try simp_all
      split at h <;> try simp_all
      split at h <;> simp_all
    · rw [evaluateHOLFiniteState_call] at h
      split at h <;> try simp_all
      try dsimp only at h
      split at h <;> try simp_all
      split at h <;> try simp_all
      split at h <;> try simp_all
      split at h <;> simp_all
    · exact False.elim (precompile_sha256_init_call_not_resumes s _ hi.code h)

theorem precompile_sha256_call_padding_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp : BitVec 64) (args : List (ExpHOL 64))
    (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256") args)).1) :
    pad.toNat ≠ 0 := by
  have hl : originalRuntimeCode.lookup (ofString "sha256") =
      some ([(ofString "p",.one),(ofString "len",.one),(ofString "out",.one)],
        sourceFnBody Guest.Software.guestFn_sha256,.one) :=
    lookup_of_guestAst_getElem 95 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256) rfl
  rw [evaluateHOLFiniteState_call] at hr
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · rw [ha] at hr
    simp [R13.FlowsOrResumes,Resumes] at hr
  · rw [ha] at hr
    dsimp only at hr
    rcases hlook : lookupCodeHOLFinite s.code.lookup (ofString "sha256") vals with _ | ⟨body,callee,ret⟩
    · simp [hlook,R13.FlowsOrResumes,Resumes] at hr
    · rw [hlook] at hr
      dsimp only at hr
      have heq := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ ret _ callee
        (by rw [hi.code]; exact hl) hlook
      subst heq
      by_cases hz : s.clock = 0
      · simp [hz,R13.FlowsOrResumes,Resumes] at hr
      · rw [if_neg hz] at hr
        have hbody : R13.FlowsOrResumes (evaluateHOLFiniteState
            (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_sha256)).1 := by
          rcases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
              (sourceFnBody Guest.Software.guestFn_sha256) with ⟨r,post⟩
          cases r with
          | none => exact Or.inl rfl
          | some r => cases r <;> simp_all [R13.FlowsOrResumes,Resumes]
        exact precompile_sha256_body_padding_nonzero _ pad stp
          (guestInv_callEntry s callee hi) hp hs hbody

theorem precompile_st_be32_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    R10Shards.P26_P28.ByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).2 [(p.toNat,4)] :=
  (R10Shards.P26_P28.checkByteStoresLocal_sound (ofString "p") 4 (by decide)
    (sourceFnBody Guest.Software.guestFn_st_be32) rfl s p hc hi hp).1

theorem precompile_st_be32_call_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64) (ptr value : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) ptr =
      some (.val (.word p))) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "st_be32") [ptr, value])).2 [(p.toNat,4)] := by
  have hl : originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
    lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_be32) rfl
  refine precompile_call0_byteEff_total _ _ _ _
    (fun vals => [(R10Shards.P26_P28.valWordNat (vals[0]?.getD (.rStruct [])),4)]) hl ?_ s _ _ hc hi ?_
  · intro entry vals hce hge hle
    obtain ⟨p, b, rfl, hpe, hbe⟩ := R10Shards.P26_P28.lookupCode_two_words (by decide) hl hle
    exact precompile_st_be32_effect entry p hce hge hpe
  · intro vals hv r hr hpos
    change @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) ptr = some (.val (.word p)) at hp
    simp [evalListHOLFinite, evalListHOLExact, hp] at hv
    split at hv
    · rename_i v vs hv1 hv2
      injection hv1 with hv1
      subst v
      injection hv with hv
      subst vals
      simp only [List.getElem?_cons_zero, Option.getD_some, R10Shards.P26_P28.valWordNat,
        List.mem_singleton] at hr
      subst r
      exact ⟨(p.toNat,4), List.mem_singleton.mpr rfl, le_rfl, le_rfl⟩
    · simp at hv

theorem precompile_sha256_finish_store_total {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out i : BitVec 64) (value : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hindex : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hib : i.toNat < 8) (hob : out.toNat + 32 < 2^64) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "st_be32")
        [.op .add [.var .local (ofString "out"),
          .panop .mul [.var .local (ofString "i"), .const 4]], value])).2 [(out.toNat,32)] := by
  have hm : (i * (4 : BitVec 64)).toNat = i.toNat * 4 := by
    rw [BitVec.toNat_mul]
    change (i.toNat * 4) % 2^64 = i.toNat * 4
    exact Nat.mod_eq_of_lt (by omega)
  have ha : (out + i * (4 : BitVec 64)).toNat = out.toNat + i.toNat * 4 := by
    rw [BitVec.toNat_add, hm]
    exact Nat.mod_eq_of_lt (by omega)
  have he := precompile_st_be32_call_effect s (out + i * (4 : BitVec 64))
    (.op .add [.var .local (ofString "out"),
      .panop .mul [.var .local (ofString "i"), .const 4]]) value hc hi
    (by simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hout, hindex,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL])
  apply he.mono
  intro r hr hpos
  simp only [List.mem_singleton] at hr
  subst r
  refine ⟨(out.toNat,32), List.mem_singleton.mpr rfl, ?_, ?_⟩
  · change out.toNat ≤ (out + i * (4 : BitVec 64)).toNat
    rw [ha]; omega
  · change (out + i * (4 : BitVec 64)).toNat + 4 ≤ out.toNat + 32
    rw [ha]; omega

theorem precompile_call0_ne_continue {F : Type} (u : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vals
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite u.code.lookup fn vals with _ | ⟨body, callee, ret⟩
    · simp
    · dsimp only
      by_cases hk : u.clock = 0
      · rw [if_pos hk]; simp
      · rw [if_neg hk]
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite u callee) body with ⟨r, st⟩
        cases r with
        | none => simp
        | some r1 =>
          cases r1 with
          | returned rv => dsimp only; split <;> simp
          | _ => simp

theorem precompile_sha256_finish_loop_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out : BitVec 64) (value : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hindex : ∃ i : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ 8)
    (hob : out.toNat + 32 < 2^64) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.while (.cmp .less (.var .local (ofString "i")) (.const 8))
        (.seq (.call (some (none, none)) (ofString "st_be32")
          [.op .add [.var .local (ofString "out"),
            .panop .mul [.var .local (ofString "i"), .const 4]], value])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 1]))))).2 [(out.toNat,32)] := by
  refine precompile_byteEff_while_guard_inv
    (fun t => t.locals.lookup (ofString "out") = some (.val (.word out)) ∧
      ∃ i : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ 8)
    _ _ _ (by intro t ht; exact ht) ?_ s hc hi ⟨hout,hindex⟩
  intro t hct hgt ht hactive
  obtain ⟨hto, i, hti, hib⟩ := ht
  have hib' := precompile_sha256_finish_guard t i hti (by omega) hactive
  let call : ProgHOL 64 := .call (some (none, none)) (ofString "st_be32")
    [.op .add [.var .local (ofString "out"),
      .panop .mul [.var .local (ofString "i"), .const 4]], value]
  let inc : ProgHOL 64 := .assign .local (ofString "i")
    (.op .add [.var .local (ofString "i"), .const 1])
  have he : R10Shards.P26_P28.ByteEff t
      (evaluateHOLFiniteState t call).2 [(out.toNat,32)] :=
    precompile_sha256_finish_store_total t out i value hct hgt hto hti hib' hob
  refine ⟨R10Shards.P26_P28.byteEff_seq he
    (fun m hm => R10Shards.P26_P28.byteEff_assign_local m _ _ _), ?_⟩
  intro hflow
  change (evaluateHOLFiniteState t (.seq call inc)).1 = none ∨
    (evaluateHOLFiniteState t (.seq call inc)).1 = some .continue at hflow
  rw [evaluateHOLFiniteState_seq_line780] at hflow ⊢
  rcases run : evaluateHOLFiniteState t call with ⟨r,m⟩
  cases r with
  | some r =>
    have hn := precompile_call0_ne_continue t (ofString "st_be32")
      [.op .add [.var .local (ofString "out"),
        .panop .mul [.var .local (ofString "i"), .const 4]], value]
    change (evaluateHOLFiniteState t call).1 ≠ some .continue at hn
    rw [run] at hn
    cases r <;> simp_all
  | none =>
    rw [run] at hflow
    dsimp only at hflow ⊢
    have hl := precompile_call0_locals_on_flow t _ _
      (by change (evaluateHOLFiniteState t call).1 = none; rw [run])
    change (evaluateHOLFiniteState t call).2.locals = t.locals at hl
    rw [run] at hl
    have hmo : m.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hl]; exact hto
    have hmi : m.locals.lookup (ofString "i") = some (.val (.word i)) := by rw [hl]; exact hti
    have hival : (i + (1 : BitVec 64)).toNat ≤ 8 := by
      rw [BitVec.toNat_add]
      change (i.toNat + 1) % 2^64 ≤ 8
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [inc, evaluateHOLFiniteState_assign] at hflow ⊢
    simp [evalHOLExact, evalListHOLExact, hmi, valueIsWord, valueWord, wordOpHOL, wordOp] at hflow ⊢
    by_cases hvalid : isValidValueHOLExact m.toExact .local (ofString "i")
        (.val (.word (i+1#64))) = true
    · simp [hvalid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update,
        FUPDATE, hmo, show ofString "i" ≠ ofString "out" by decide]
      exact hival
    · simp [hvalid] at hflow

theorem precompile_sha256_finish_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hob : out.toNat + 32 < 2^64) :
    R10Shards.P26_P28.ByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256_finish)).2
      [(out.toNat,32)] := by
  change R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
    (.dec (ofString "i") .one (.const 0) _)).2 _
  apply R10Shards.P26_P28.byteEff_dec
  intro v hv
  simp only [evalHOLExact] at hv
  injection hv with hv
  subst v
  apply R10Shards.P26_P28.byteEff_seq
  · apply precompile_sha256_finish_loop_effect
      (setVarHOLFinite (ofString "i") (.val (.word 0)) s) out _ hc
      (guestInv_congr (s := s) (t := setVarHOLFinite (ofString "i") (.val (.word 0)) s)
        rfl rfl rfl rfl hi) ?_ ?_ hob
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout,
        show ofString "i" ≠ ofString "out" by decide]
    · refine ⟨0, ?_, by decide⟩
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · intro m hm
    exact R10Shards.P26_P28.byteEff_return m _ _

theorem precompile_call0_byteEff_at {F : Type} (fname : MlS)
    (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (ret : ShapeHOL)
    (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64)) (Rl : List Ivl)
    (hl : originalRuntimeCode.lookup fname = some (params, body, ret))
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hf : ∀ (entry : PanSemStateFiniteExact 64 F) vals,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      entry.code = originalRuntimeCode → GuestInv entry →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, entry.locals, ret) →
      R10Shards.P26_P28.ByteEff entry (evaluateHOLFiniteState entry body).2 Rl) :
    R10Shards.P26_P28.ByteEff s
      (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 Rl := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact R10Shards.P26_P28.ByteEff.refl s Rl
  · dsimp only
    rcases hlook : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact R10Shards.P26_P28.ByteEff.refl s Rl
    · dsimp only
      have heq := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hl) hlook
      subst heq
      have heq := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hl) hlook
      subst heq
      by_cases hz : s.clock = 0
      · simp only [hz, ↓reduceIte]
        exact (R10Shards.P26_P28.ByteEff.refl s Rl).locals_clock _ _
      · simp only [hz, ↓reduceIte]
        let entry := callEntryStateHOLFinite s callee
        have hge : GuestInv entry := guestInv_callEntry s callee hi
        have hle : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals =
            some (body', entry.locals, ret') := by
          simpa [hc, entry, callEntryStateHOLFinite] using hlook
        have he := hf entry vals hargs hc hge hle
        dsimp only [entry] at he
        rcases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        rw [run] at he
        have eff : R10Shards.P26_P28.ByteEff s post Rl :=
          ((R10Shards.P26_P28.ByteEff.refl s _).locals_clock _ _).trans he
        cases res with
        | none => exact eff.locals_clock _ _
        | some r =>
          cases r <;> dsimp only
          all_goals first
            | exact eff.locals_clock _ _
            | (split <;> exact eff.locals_clock _ _)

theorem precompile_sha256_finish_call_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out : BitVec 64) (ptr dest : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) dest =
      some (.val (.word out))) (hob : out.toNat + 32 < 2^64) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "sha256_finish") [ptr, dest])).2 [(out.toNat,32)] := by
  have hl : originalRuntimeCode.lookup (ofString "sha256_finish") =
      some ([(ofString "stp", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_sha256_finish, .one) :=
    lookup_of_guestAst_getElem 94 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_finish) rfl
  refine precompile_call0_byteEff_at _ _ _ _ s _ _ hl hc hi ?_
  intro entry vals hargs hce hge hle
  obtain ⟨p, b, hv, hpe, hbe⟩ := R10Shards.P26_P28.lookupCode_two_words (by decide) hl hle
  have hb : b = out := by
    rw [hv] at hargs
    change @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) dest = some (.val (.word out)) at hp
    simp [evalListHOLFinite, evalListHOLExact, hp] at hargs
    split at hargs <;> simp_all
  subst b
  exact precompile_sha256_finish_effect entry out hce hge hbe hob

theorem precompile_sha256_padding_byte_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad rem : BitVec 64)
    (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hr : s.locals.lookup (ofString "rem") = some (.val (.word rem)))
    (hrem : rem.toNat < 64) (hpad : pad.toNat + 128 ≤ heapEnd) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.storeByte (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")])
        (.const 128))).2 [(pad.toNat,128)] := by
  apply R10Shards.P26_P28.byteEff_storeByte_at hi _ _ pad rem.toNat 128 hpad
    (fun _ => ⟨(pad.toNat,128), List.mem_singleton.mpr rfl, le_rfl, le_rfl⟩) (by omega)
  simp [evalHOLExact, evalListHOLExact, hp, hr, valueIsWord, valueWord,
    wordOpHOL, wordOp]

theorem precompile_sha256_padding_zero_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memzero")
      [.var .global (ofString "sha_pad"), .const 128])).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memzero")
      [.var .global (ofString "sha_pad"), .const 128])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memzero")
      [.var .global (ofString "sha_pad"), .const 128])).1) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "sha_pad"), .const 128])).2 [(pad.toNat,128)] := by
  apply R10Shards.P26_P28.call0_byteEff R10Shards.P26_P28.funByteEff_memzero s _ _ hc hi ?_ hnt hr
  intro vals hv r hr hpos
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp] at hv
  subst vals
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    R10Shards.P26_P28.valWordNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, List.mem_singleton] at hr
  subst r
  exact ⟨(pad.toNat,128), List.mem_singleton.mpr rfl, le_rfl, le_rfl⟩

theorem precompile_sha256_padding_copy_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad rem : BitVec 64) (src : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hrem : s.locals.lookup (ofString "rem") = some (.val (.word rem)))
    (hb : rem.toNat < 64)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy")
      [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")])).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy")
      [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy")
      [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")])).1) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")])).2 [(pad.toNat,128)] := by
  apply R10Shards.P26_P28.call0_byteEff R10Shards.P26_P28.funByteEff_memcpy s _ _ hc hi ?_ hnt hr
  intro vals hv r hr hpos
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hrem] at hv
  split at hv
  · rename_i v vs hv1 hv2
    injection hv1 with hv1
    subst v
    injection hv with hv
    subst vals
    split at hv2
    · rename_i v vs hsrc htail
      injection hv2 with hv2
      injection htail with htail
      rw [← hv2, ← htail] at hr
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
        R10Shards.P26_P28.valWordNat, List.mem_singleton] at hr
      subst r
      refine ⟨(pad.toNat,128), List.mem_singleton.mpr rfl, le_rfl, ?_⟩
      omega
    · simp at hv2
  · simp at hv

theorem precompile_sha256_padding_length_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad total : BitVec 64) (value : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (ht : s.locals.lookup (ofString "total") = some (.val (.word total)))
    (hb : total.toNat = 64 ∨ total.toNat = 128)
    (hpad : pad.toNat + 128 < 2^64)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be64")
      [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")],
        .const 8], value])).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be64")
      [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")],
        .const 8], value])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be64")
      [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")],
        .const 8], value])).1) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "st_be64")
        [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")],
          .const 8], value])).2 [(pad.toNat,128)] := by
  have ha : (pad + total).toNat = pad.toNat + total.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by rcases hb with h|h <;> omega)]
  have hs : (pad + total - (8 : BitVec 64)).toNat = pad.toNat + total.toNat - 8 := by
    have hle : (8 : BitVec 64) ≤ pad+total := by
      change (8 : BitVec 64).toNat ≤ (pad+total).toNat
      change 8 ≤ (pad+total).toNat
      rw [ha]; rcases hb with h|h <;> omega
    rw [BitVec.toNat_sub_of_le hle, ha]
    rfl
  apply R10Shards.P26_P28.call0_byteEff R10Shards.P26_P28.funByteEff_st_be64 s _ _ hc hi ?_ hnt hr
  intro vals hv r hr hpos
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, ht,
    valueIsWord, valueWord, wordOpHOL, wordOp] at hv
  split at hv
  · rename_i v vs hv1 hv2
    injection hv1 with hv1
    subst v
    injection hv with hv
    subst vals
    simp only [List.getElem?_cons_zero, Option.getD_some, R10Shards.P26_P28.valWordNat,
      List.mem_singleton] at hr
    subst r
    refine ⟨(pad.toNat,128), List.mem_singleton.mpr rfl, ?_, ?_⟩
    · change pad.toNat ≤ (pad+total-(8 : BitVec 64)).toNat
      rw [hs]; rcases hb with h|h <;> omega
    · change (pad+total-(8 : BitVec 64)).toNat + 8 ≤ pad.toNat+128
      rw [hs]; rcases hb with h|h <;> omega
  · simp at hv

theorem precompile_sha256_final_blocks_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (stp : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_st") = some (.val (.word stp))) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"), .var .global (ofString "sha_pad")])
        (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128))
          (.call (some (none, none)) (ofString "sha256_block")
            [.var .global (ofString "sha_st"),
              .op .add [.var .global (ofString "sha_pad"), .const 64]]) .skip))).2
      [(stp.toNat,64)] := by
  have he := precompile_sha256_block_call_effect s stp
    (.var .global (ofString "sha_st")) (.var .global (ofString "sha_pad")) hc hi
    (by simp [evalHOLFinite, evalHOLExact, hp])
  apply R10Shards.P26_P28.byteEff_seq he
  intro m hm
  rw [hm] at he
  have hgm : GuestInv m := guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi
  have hpm : m.globals.lookup (ofString "sha_st") = some (.val (.word stp)) := by
    rw [he.globals]; exact hp
  apply R10Shards.P26_P28.byteEff_ite
  · exact precompile_sha256_block_call_effect m stp
      (.var .global (ofString "sha_st"))
      (.op .add [.var .global (ofString "sha_pad"), .const 64]) (he.code.trans hc) hgm
      (by simp [evalHOLFinite, evalHOLExact, hpm])
  · exact R10Shards.P26_P28.byteEff_skip m _

theorem precompile_sha256_padding_total_choice {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (ht : s.locals.lookup (ofString "total") = some (.val (.word 64)))
    (hv : isValidValueHOLExact s.toExact .local (ofString "total")
      (.val (.word 128)) = true) :
    let post := (evaluateHOLFiniteState s
      (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip)).2
    ∃ total : BitVec 64, post.locals.lookup (ofString "total") = some (.val (.word total)) ∧
      (total.toNat = 64 ∨ total.toNat = 128) := by
  change isValidValueHOLExact s.toExact .local (ofString "total")
    (.val (.word 128#64)) = true at hv
  dsimp only
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact ⟨64, by simpa [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext] using ht, Or.inl rfl⟩
    · refine ⟨128, ?_, Or.inr rfl⟩
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hv, setVarHOLFinite,
        setKvarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · exact ⟨64, ht, Or.inl rfl⟩

theorem precompile_sha256_finish_return_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hob : out.toNat + 32 < 2^64) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "sha256_finish")
        [.var .global (ofString "sha_st"), .var .local (ofString "out")])
        (.return (.const 0)))).2 [(out.toNat,32)] := by
  apply R10Shards.P26_P28.byteEff_seq (precompile_sha256_finish_call_effect s out
    (.var .global (ofString "sha_st")) (.var .local (ofString "out")) hc hi
    (by simp [evalHOLFinite, evalHOLExact, ho]) hob)
  intro m hm
  exact R10Shards.P26_P28.byteEff_return m _ _

theorem precompile_sha256_optional_block_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hr : (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128))
        (.call (some (none, none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .global (ofString "sha_pad"), .const 64]]) .skip)).1 = none) :
    (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128))
        (.call (some (none, none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .global (ofString "sha_pad"), .const 64]]) .skip)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_ite] at hr ⊢
  split
  · rename_i v he
    rw [he] at hr
    dsimp only at hr
    split
    · rename_i hz
      simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext]
    · rename_i hz
      simp only [hz, ↓reduceIte] at hr
      exact precompile_call0_locals_on_flow s _ _ hr
  · rfl

theorem precompile_sha256_final_tail_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (stp out : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hob : out.toNat + 32 < 2^64) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"), .var .global (ofString "sha_pad")])
        (.seq (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128))
          (.call (some (none, none)) (ofString "sha256_block")
            [.var .global (ofString "sha_st"),
              .op .add [.var .global (ofString "sha_pad"), .const 64]]) .skip)
          (.seq (.call (some (none, none)) (ofString "sha256_finish")
            [.var .global (ofString "sha_st"), .var .local (ofString "out")])
            (.return (.const 0)))))).2 [(stp.toNat,64),(out.toNat,32)] := by
  have he := precompile_sha256_block_call_effect s stp
    (.var .global (ofString "sha_st")) (.var .global (ofString "sha_pad")) hc hi
    (by simp [evalHOLFinite, evalHOLExact, hp])
  have he' := he.mono (R2 := [(stp.toNat,64),(out.toNat,32)]) (by
    intro i hi hpos; simp only [List.mem_singleton] at hi; subst i
    exact ⟨_, by simp, le_rfl, le_rfl⟩)
  apply R10Shards.P26_P28.byteEff_seq he'
  intro m hm
  have hl := precompile_call0_locals_on_flow s (ofString "sha256_block")
    [.var .global (ofString "sha_st"), .var .global (ofString "sha_pad")]
    (by rw [hm])
  rw [hm] at he hl
  have hgm : GuestInv m := guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi
  have hpm : m.globals.lookup (ofString "sha_st") = some (.val (.word stp)) := by
    rw [he.globals]; exact hp
  have he2 : R10Shards.P26_P28.ByteEff m (evaluateHOLFiniteState m
      (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128))
        (.call (some (none, none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .global (ofString "sha_pad"), .const 64]]) .skip)).2
      [(stp.toNat,64)] := by
    apply R10Shards.P26_P28.byteEff_ite
    · exact precompile_sha256_block_call_effect m stp
        (.var .global (ofString "sha_st"))
        (.op .add [.var .global (ofString "sha_pad"), .const 64]) (he.code.trans hc) hgm
        (by simp [evalHOLFinite, evalHOLExact, hpm])
    · exact R10Shards.P26_P28.byteEff_skip m _
  apply R10Shards.P26_P28.byteEff_seq (he2.mono (by
    intro i hi hpos; simp only [List.mem_singleton] at hi; subst i
    exact ⟨_, by simp, le_rfl, le_rfl⟩))
  intro n hn
  have hl2 := precompile_sha256_optional_block_locals m (by rw [hn])
  rw [hn] at he2 hl2
  have hgn : GuestInv n := guestInv_congr he2.code he2.memaddrs he2.shMemaddrs he2.baseAddr hgm
  have hon : n.locals.lookup (ofString "out") = some (.val (.word out)) := by
    rw [hl2, hl]; exact ho
  exact (precompile_sha256_finish_return_effect n out (he2.code.trans (he.code.trans hc)) hgn hon hob).mono (by
    intro i hi hpos; simp only [List.mem_singleton] at hi; subst i
    exact ⟨_, by simp, le_rfl, le_rfl⟩)

theorem precompile_byteEff_seq_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64) (Rl : List Ivl)
    (hnt : (evaluateHOLFiniteState s (.seq a b)).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.seq a b)).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.seq a b)).1)
    (ha : (evaluateHOLFiniteState s a).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s a).1 = none ∨ Resumes (evaluateHOLFiniteState s a).1) →
      R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s a).2 Rl)
    (hb : ∀ m, evaluateHOLFiniteState s a = (none,m) →
      (evaluateHOLFiniteState m b).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState m b).1 = none ∨ Resumes (evaluateHOLFiniteState m b).1) →
      R10Shards.P26_P28.ByteEff m (evaluateHOLFiniteState m b).2 Rl) :
    R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s (.seq a b)).2 Rl := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hr ⊢
  rcases run : evaluateHOLFiniteState s a with ⟨r,m⟩
  cases r with
  | none =>
    simp only [run] at hnt hr ⊢
    have he := ha (by simp [run]) (Or.inl (by simp [run]))
    rw [run] at he
    exact he.trans (hb m run hnt hr)
  | some r =>
    simp only [run] at hnt hr ⊢
    have he := ha (by simpa [run] using hnt) (by simpa [run] using hr)
    simpa only [run] using he

open R10Shards.P26_P28 in
theorem precompile_sha256_padding_prepare_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad rem : BitVec 64) (src : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hrm : s.locals.lookup (ofString "rem") = some (.val (.word rem)))
    (hb : rem.toNat < 64) (hpad : pad.toNat + 128 ≤ heapEnd)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "sha_pad"), .const 128])
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")])
          (.storeByte (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")])
            (.const 128))))).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "sha_pad"), .const 128])
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")])
          (.storeByte (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")])
            (.const 128))))).1 = none ∨ Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "sha_pad"), .const 128])
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")])
          (.storeByte (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")])
            (.const 128))))).1) :
    ByteEff s (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "sha_pad"), .const 128])
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")])
          (.storeByte (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")])
            (.const 128))))).2 [(pad.toNat,128)] := by
  refine precompile_byteEff_seq_resumes s _ _ _ hnt hr
    (precompile_sha256_padding_zero_effect s pad hc hi hp) ?_
  intro m hm hntm hrm'
  have he := precompile_sha256_padding_zero_effect s pad hc hi hp (by rw [hm]; simp)
    (Or.inl (by rw [hm]))
  have hl := precompile_call0_locals_on_flow s (ofString "memzero")
    [.var .global (ofString "sha_pad"), .const 128] (by rw [hm])
  rw [hm] at he hl
  have him : GuestInv m := guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi
  have hpm : m.globals.lookup (ofString "sha_pad") = some (.val (.word pad)) := by
    rw [he.globals]; exact hp
  have hrmm : m.locals.lookup (ofString "rem") = some (.val (.word rem)) := by
    rw [hl]; exact hrm
  refine precompile_byteEff_seq_resumes m _ _ _ hntm hrm'
    (precompile_sha256_padding_copy_effect m pad rem src (he.code.trans hc) him hpm hrmm hb) ?_
  intro n hn hntn hrn
  have he2 := precompile_sha256_padding_copy_effect m pad rem src (he.code.trans hc) him hpm hrmm hb
    (by rw [hn]; simp) (Or.inl (by rw [hn]))
  have hl2 := precompile_call0_locals_on_flow m (ofString "memcpy")
    [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")] (by rw [hn])
  rw [hn] at he2 hl2
  apply precompile_sha256_padding_byte_effect n pad rem
    (guestInv_congr he2.code he2.memaddrs he2.shMemaddrs he2.baseAddr him)
    (by rw [he2.globals]; exact hpm) (by rw [hl2]; exact hrmm) hb hpad

open R10Shards.P26_P28 in
theorem precompile_sha256_length_tail_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad total stp out : BitVec 64) (value : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (ht : s.locals.lookup (ofString "total") = some (.val (.word total)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hb : total.toNat = 64 ∨ total.toNat = 128)
    (hpad : pad.toNat + 128 < 2^64) (hob : out.toNat + 32 < 2^64) :
    let p := ProgHOL.seq
      (.call (some (none, none)) (ofString "st_be64")
        [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")],
          .const 8], value])
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"), .var .global (ofString "sha_pad")])
        (.seq (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128))
          (.call (some (none, none)) (ofString "sha256_block")
            [.var .global (ofString "sha_st"),
              .op .add [.var .global (ofString "sha_pad"), .const 64]]) .skip)
          (.seq (.call (some (none, none)) (ofString "sha256_finish")
            [.var .global (ofString "sha_st"), .var .local (ofString "out")])
            (.return (.const 0)))))
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2 [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)] := by
  dsimp only
  intro hnt hr
  refine precompile_byteEff_seq_resumes s _ _ _ hnt hr ?_ ?_
  · intro hnta hra
    exact (precompile_sha256_padding_length_effect s pad total value hc hi hp ht hb hpad hnta hra).mono (by
      intro i hi hpos; simp only [List.mem_singleton] at hi; subst i
      exact ⟨_, by simp, le_rfl, le_rfl⟩)
  · intro m hm hntm hrm
    have he := precompile_sha256_padding_length_effect s pad total value hc hi hp ht hb hpad
      (by rw [hm]; simp) (Or.inl (by rw [hm]))
    have hl := precompile_call0_locals_on_flow s (ofString "st_be64")
      [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")],
        .const 8], value] (by rw [hm])
    rw [hm] at he hl
    have him : GuestInv m := guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi
    have hsm : m.globals.lookup (ofString "sha_st") = some (.val (.word stp)) := by
      rw [he.globals]; exact hs
    have hom : m.locals.lookup (ofString "out") = some (.val (.word out)) := by
      rw [hl]; exact ho
    exact (precompile_sha256_final_tail_effect m stp out (he.code.trans hc) him hsm hom hob).mono (by
      intro i hi hpos
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl
      · exact ⟨_, by simp, le_rfl, le_rfl⟩
      · exact ⟨_, by simp, le_rfl, le_rfl⟩)

theorem precompile_sha256_padding_choice_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (name : MlS)
    (hne : name ≠ ofString "total") :
    (evaluateHOLFiniteState s
      (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip)).2.locals.lookup name =
      s.locals.lookup name := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · simp [evaluateHOLFiniteState, evaluateHOLFiniteStateWithDeciders,
        evalPanSemRecursiveCallFiniteContext]
    · simp only [evaluateHOLFiniteState_assign]
      simp [evalHOLExact, setKvarHOLFinite, setVarHOLFinite]
      split
      · simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
      · rfl
  · rfl

open R10Shards.P26_P28 in
theorem precompile_sha256_padding_choice_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteEff s (evaluateHOLFiniteState s
      (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip)).2 Rl := by
  apply byteEff_ite
  · exact byteEff_assign_local s _ _ _
  · exact byteEff_skip s _

open R10Shards.P26_P28 in
theorem precompile_sha256_padding_choice_then {F : Type}
    (s : PanSemStateFiniteExact 64 F) (body : ProgHOL 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (ht : s.locals.lookup (ofString "total") = some (.val (.word 64)))
    (hv : isValidValueHOLExact s.toExact .local (ofString "total")
      (.val (.word 128)) = true)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip) body)).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s
      (.seq (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip) body)).1 = none ∨
      Resumes (evaluateHOLFiniteState s
      (.seq (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip) body)).1)
    (hb : ∀ (m : PanSemStateFiniteExact 64 F), m.code = originalRuntimeCode → GuestInv m → m.globals = s.globals →
      (∀ name, name ≠ ofString "total" → m.locals.lookup name = s.locals.lookup name) →
      (∃ total : BitVec 64, m.locals.lookup (ofString "total") = some (.val (.word total)) ∧
        (total.toNat = 64 ∨ total.toNat = 128)) →
      (evaluateHOLFiniteState m body).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState m body).1 = none ∨ Resumes (evaluateHOLFiniteState m body).1) →
      ByteEff m (evaluateHOLFiniteState m body).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s
      (.seq (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip) body)).2 Rl := by
  refine precompile_byteEff_seq_resumes s _ _ _ hnt hr
    (fun _ _ => precompile_sha256_padding_choice_effect s Rl) ?_
  intro m hm hntm hrm
  have he := precompile_sha256_padding_choice_effect s Rl
  have htotal := precompile_sha256_padding_total_choice s ht hv
  rw [hm] at he htotal
  apply hb m (he.code.trans hc)
    (guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi) he.globals
  · intro name hne
    have hl := precompile_sha256_padding_choice_locals s name hne
    simpa only [hm] using hl
  · exact htotal
  · exact hntm
  · exact hrm

open R10Shards.P26_P28 in
theorem precompile_sha256_choice_tail_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (ht : s.locals.lookup (ofString "total") = some (.val (.word 64)))
    (hv : isValidValueHOLExact s.toExact .local (ofString "total") (.val (.word 128)) = true)
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hpad : pad.toNat + 128 < 2^64) (hob : out.toNat + 32 < 2^64) :
    let tail := ProgHOL.seq
      (.call (some (none, none)) (ofString "st_be64")
        [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")],
          .const 8], .shift .lsl (.var .local (ofString "len")) (.const 3)])
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"), .var .global (ofString "sha_pad")])
        (.seq (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128))
          (.call (some (none, none)) (ofString "sha256_block")
            [.var .global (ofString "sha_st"),
              .op .add [.var .global (ofString "sha_pad"), .const 64]]) .skip)
          (.seq (.call (some (none, none)) (ofString "sha256_finish")
            [.var .global (ofString "sha_st"), .var .local (ofString "out")])
            (.return (.const 0)))))
    let p := ProgHOL.seq
      (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip) tail
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2 [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)] := by
  dsimp only
  intro hnt hr
  refine precompile_sha256_padding_choice_then s _ _ hc hi ht hv hnt hr ?_
  intro m hcm him hgm hlm htotal hntm hrm
  obtain ⟨total, htm, htb⟩ := htotal
  exact precompile_sha256_length_tail_effect m pad total stp out _ hcm him
    (by rw [hgm]; exact hp) htm (by rw [hgm]; exact hs)
    (by rw [hlm (ofString "out") (by decide)]; exact ho) htb hpad hob hntm hrm

open R10Shards.P26_P28 in
theorem precompile_byteEff_dec_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (name : MlS) (sh : ShapeHOL)
    (init : ExpHOL 64) (body : ProgHOL 64) (Rl : List Ivl)
    (hnt : (evaluateHOLFiniteState s (.dec name sh init body)).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.dec name sh init body)).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.dec name sh init body)).1)
    (hb : ∀ val,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some val →
      (evaluateHOLFiniteState (setVarHOLFinite name val s) body).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState (setVarHOLFinite name val s) body).1 = none ∨
        Resumes (evaluateHOLFiniteState (setVarHOLFinite name val s) body).1) →
      ByteEff (setVarHOLFinite name val s)
        (evaluateHOLFiniteState (setVarHOLFinite name val s) body).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s (.dec name sh init body)).2 Rl := by
  rw [evaluateHOLFiniteState_dec_total] at hnt hr ⊢
  dsimp only at hnt hr ⊢
  split
  · exact ByteEff.refl s Rl
  · rename_i val hval
    rw [hval] at hnt hr
    dsimp only at hnt hr
    split
    · rename_i hshape
      simp only [hshape, ↓reduceIte] at hnt hr
      exact ((ByteEff.refl s Rl).locals_clock _ s.clock).trans
        (hb val hval hnt hr) |>.locals_clock _ _
    · exact ByteEff.refl s Rl

open R10Shards.P26_P28 in
theorem precompile_sha256_total_decl_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hpad : pad.toNat + 128 < 2^64) (hob : out.toNat + 32 < 2^64) :
    let tail := ProgHOL.seq
      (.call (some (none, none)) (ofString "st_be64")
        [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")],
          .const 8], .shift .lsl (.var .local (ofString "len")) (.const 3)])
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"), .var .global (ofString "sha_pad")])
        (.seq (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128))
          (.call (some (none, none)) (ofString "sha256_block")
            [.var .global (ofString "sha_st"),
              .op .add [.var .global (ofString "sha_pad"), .const 64]]) .skip)
          (.seq (.call (some (none, none)) (ofString "sha256_finish")
            [.var .global (ofString "sha_st"), .var .local (ofString "out")])
            (.return (.const 0)))))
    let p := ProgHOL.dec (ofString "total") .one (.const 64)
      (.seq (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip) tail)
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2 [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)] := by
  dsimp only
  intro hnt hr
  refine precompile_byteEff_dec_resumes s _ _ _ _ _ hnt hr ?_
  intro val hval hntb hrb
  simp only [evalHOLExact, Option.some.injEq] at hval
  subst val
  apply precompile_sha256_choice_tail_effect
    (setVarHOLFinite (ofString "total") (.val (.word 64#64)) s) pad stp out hc
    (guestInv_setVar _ _ s hi) hp
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · simp [isValidValueHOLExact, lookupKvarHOLExact, setVarHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE, shapeOfHOLExact, shapeEqHOL]
  · exact hs
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "total" ≠ ofString "out" by decide] using ho
  · exact hpad
  · exact hob
  · exact hntb
  · exact hrb

theorem precompile_storeByte_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst value : ExpHOL 64) :
    (evaluateHOLFiniteState s (.storeByte dst value)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_storeByte]
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

open R10Shards.P26_P28 in
theorem precompile_sha256_marker_then {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad rem : BitVec 64)
    (body : ProgHOL 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hr : s.locals.lookup (ofString "rem") = some (.val (.word rem)))
    (hb : rem.toNat < 64) (hpad : pad.toNat + 128 ≤ heapEnd)
    (hin : ∀ i ∈ [(pad.toNat,128)], 0 < i.2 →
      ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hbody : ∀ (m : PanSemStateFiniteExact 64 F), m.code = originalRuntimeCode → GuestInv m →
      m.globals = s.globals → m.locals = s.locals →
      ByteEff m (evaluateHOLFiniteState m body).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s
      (.seq (.storeByte (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")])
        (.const 128)) body)).2 Rl := by
  have he := precompile_sha256_padding_byte_effect s pad rem hi hp hr hb hpad
  apply byteEff_seq (he.mono hin)
  intro m hm
  have hl := precompile_storeByte_locals s
    (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")]) (.const 128)
  rw [hm] at he hl
  exact hbody m (he.code.trans hc)
    (guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi) he.globals hl

open R10Shards.P26_P28 in
theorem precompile_sha256_marker_then_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad rem : BitVec 64)
    (body : ProgHOL 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hr : s.locals.lookup (ofString "rem") = some (.val (.word rem)))
    (hb : rem.toNat < 64) (hpad : pad.toNat + 128 ≤ heapEnd)
    (hin : ∀ i ∈ [(pad.toNat,128)], 0 < i.2 →
      ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hbody : ∀ (m : PanSemStateFiniteExact 64 F), m.code = originalRuntimeCode → GuestInv m →
      m.globals = s.globals → m.locals = s.locals →
      (evaluateHOLFiniteState m body).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState m body).1 = none ∨ Resumes (evaluateHOLFiniteState m body).1) →
      ByteEff m (evaluateHOLFiniteState m body).2 Rl) :
    let p := ProgHOL.seq
      (.storeByte (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")])
        (.const 128)) body
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2 Rl := by
  dsimp only
  intro hnt hres
  have he := precompile_sha256_padding_byte_effect s pad rem hi hp hr hb hpad
  refine precompile_byteEff_seq_resumes s _ _ _ hnt hres (fun _ _ => he.mono hin) ?_
  intro m hm hntm hrm
  have hl := precompile_storeByte_locals s
    (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")]) (.const 128)
  rw [hm] at he hl
  exact hbody m (he.code.trans hc)
    (guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi) he.globals hl hntm hrm

open R10Shards.P26_P28 in
theorem precompile_sha256_marker_tail_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad rem stp out : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hr : s.locals.lookup (ofString "rem") = some (.val (.word rem)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hb : rem.toNat < 64) (hpad : pad.toNat + 128 ≤ heapEnd)
    (hob : out.toNat + 32 < 2^64) :
    let tail := ProgHOL.seq
      (.call (some (none, none)) (ofString "st_be64")
        [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")],
          .const 8], .shift .lsl (.var .local (ofString "len")) (.const 3)])
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"), .var .global (ofString "sha_pad")])
        (.seq (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128))
          (.call (some (none, none)) (ofString "sha256_block")
            [.var .global (ofString "sha_st"),
              .op .add [.var .global (ofString "sha_pad"), .const 64]]) .skip)
          (.seq (.call (some (none, none)) (ofString "sha256_finish")
            [.var .global (ofString "sha_st"), .var .local (ofString "out")])
            (.return (.const 0)))))
    let body := ProgHOL.dec (ofString "total") .one (.const 64)
      (.seq (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip) tail)
    let p := ProgHOL.seq
      (.storeByte (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")])
        (.const 128)) body
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2 [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)] := by
  dsimp only
  intro hnt hres
  refine precompile_sha256_marker_then_resumes s pad rem _ _ hc hi hp hr hb hpad ?_ ?_ hnt hres
  · intro i hi hpos; simp only [List.mem_singleton] at hi; subst i
    exact ⟨_, by simp, le_rfl, le_rfl⟩
  · intro m hcm him hgm hlm hntm hrm
    exact precompile_sha256_total_decl_effect m pad stp out hcm him
      (by rw [hgm]; exact hp) (by rw [hgm]; exact hs) (by rw [hlm]; exact ho)
      (lt_of_le_of_lt hpad (by decide : heapEnd < 2^64)) hob hntm hrm

open R10Shards.P26_P28 in
theorem precompile_sha256_padding_copy_then {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad rem : BitVec 64)
    (src : ExpHOL 64) (body : ProgHOL 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hr : s.locals.lookup (ofString "rem") = some (.val (.word rem)))
    (hb : rem.toNat < 64)
    (hin : ∀ i ∈ [(pad.toNat,128)], 0 < i.2 →
      ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hbody : ∀ (m : PanSemStateFiniteExact 64 F), m.code = originalRuntimeCode → GuestInv m →
      m.globals = s.globals → m.locals = s.locals →
      (evaluateHOLFiniteState m body).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState m body).1 = none ∨ Resumes (evaluateHOLFiniteState m body).1) →
      ByteEff m (evaluateHOLFiniteState m body).2 Rl) :
    let p := ProgHOL.seq
      (.call (some (none, none)) (ofString "memcpy")
        [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")]) body
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2 Rl := by
  dsimp only
  intro hnt hres
  refine precompile_byteEff_seq_resumes s _ _ _ hnt hres ?_ ?_
  · intro hnta hra
    exact (precompile_sha256_padding_copy_effect s pad rem src hc hi hp hr hb hnta hra).mono hin
  · intro m hm hntm hrm
    have he := precompile_sha256_padding_copy_effect s pad rem src hc hi hp hr hb
      (by rw [hm]; simp) (Or.inl (by rw [hm]))
    have hl := precompile_call0_locals_on_flow s (ofString "memcpy")
      [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")] (by rw [hm])
    rw [hm] at he hl
    exact hbody m (he.code.trans hc)
      (guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi) he.globals hl hntm hrm

open R10Shards.P26_P28 in
theorem precompile_sha256_padding_zero_then {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad : BitVec 64)
    (body : ProgHOL 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hin : ∀ i ∈ [(pad.toNat,128)], 0 < i.2 →
      ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hbody : ∀ (m : PanSemStateFiniteExact 64 F), m.code = originalRuntimeCode → GuestInv m →
      m.globals = s.globals → m.locals = s.locals →
      (evaluateHOLFiniteState m body).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState m body).1 = none ∨ Resumes (evaluateHOLFiniteState m body).1) →
      ByteEff m (evaluateHOLFiniteState m body).2 Rl) :
    let p := ProgHOL.seq
      (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "sha_pad"), .const 128]) body
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2 Rl := by
  dsimp only
  intro hnt hres
  refine precompile_byteEff_seq_resumes s _ _ _ hnt hres ?_ ?_
  · intro hnta hra
    exact (precompile_sha256_padding_zero_effect s pad hc hi hp hnta hra).mono hin
  · intro m hm hntm hrm
    have he := precompile_sha256_padding_zero_effect s pad hc hi hp
      (by rw [hm]; simp) (Or.inl (by rw [hm]))
    have hl := precompile_call0_locals_on_flow s (ofString "memzero")
      [.var .global (ofString "sha_pad"), .const 128] (by rw [hm])
    rw [hm] at he hl
    exact hbody m (he.code.trans hc)
      (guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi) he.globals hl hntm hrm

open R10Shards.P26_P28 in
theorem precompile_sha256_padding_path_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad rem stp out : BitVec 64) (src : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hr : s.locals.lookup (ofString "rem") = some (.val (.word rem)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hb : rem.toNat < 64) (hpad : pad.toNat + 128 ≤ heapEnd)
    (hob : out.toNat + 32 < 2^64) :
    let tail := ProgHOL.seq
      (.call (some (none, none)) (ofString "st_be64")
        [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")],
          .const 8], .shift .lsl (.var .local (ofString "len")) (.const 3)])
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"), .var .global (ofString "sha_pad")])
        (.seq (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128))
          (.call (some (none, none)) (ofString "sha256_block")
            [.var .global (ofString "sha_st"),
              .op .add [.var .global (ofString "sha_pad"), .const 64]]) .skip)
          (.seq (.call (some (none, none)) (ofString "sha256_finish")
            [.var .global (ofString "sha_st"), .var .local (ofString "out")])
            (.return (.const 0)))))
    let body := ProgHOL.dec (ofString "total") .one (.const 64)
      (.seq (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip) tail)
    let p := ProgHOL.seq
      (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "sha_pad"), .const 128])
      (.seq (.call (some (none, none)) (ofString "memcpy")
        [.var .global (ofString "sha_pad"), src, .var .local (ofString "rem")])
        (.seq (.storeByte (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")])
          (.const 128)) body))
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2 [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)] := by
  dsimp only
  intro hnt hres
  have hin : ∀ i ∈ [(pad.toNat,128)], 0 < i.2 →
      ∃ j ∈ [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)],
        j.1 ≤ i.1 ∧ i.1+i.2 ≤ j.1+j.2 := by
    intro i hi hpos; simp only [List.mem_singleton] at hi; subst i
    exact ⟨_, by simp, le_rfl, le_rfl⟩
  refine precompile_sha256_padding_zero_then s pad _ _ hc hi hp hin ?_ hnt hres
  intro m hcm him hgm hlm hntm hrm
  refine precompile_sha256_padding_copy_then m pad rem src _ _ hcm him
    (by rw [hgm]; exact hp) (by rw [hlm]; exact hr) hb hin ?_ hntm hrm
  intro n hcn hinv hgn hln hntn hrn
  exact precompile_sha256_marker_tail_effect n pad rem stp out hcn hinv
    (by rw [hgn, hgm]; exact hp) (by rw [hln, hlm]; exact hr)
    (by rw [hgn, hgm]; exact hs) (by rw [hln, hlm]; exact ho) hb hpad hob hntn hrn

open R10Shards.P26_P28 in
theorem precompile_sha256_remainder_then {F : Type}
    (s : PanSemStateFiniteExact 64 F) (len i : BitVec 64)
    (body : ProgHOL 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hx : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hle : i.toNat ≤ len.toNat) (hb : len.toNat - i.toNat < 64)
    (hbody : ∀ (m : PanSemStateFiniteExact 64 F), m.code = originalRuntimeCode → GuestInv m →
      m.globals = s.globals →
      (∀ name, name ≠ ofString "rem" → m.locals.lookup name = s.locals.lookup name) →
      m.locals.lookup (ofString "rem") = some (.val (.word (len-i))) →
      (len-i).toNat < 64 →
      (evaluateHOLFiniteState m body).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState m body).1 = none ∨ Resumes (evaluateHOLFiniteState m body).1) →
      ByteEff m (evaluateHOLFiniteState m body).2 Rl) :
    let p := ProgHOL.dec (ofString "rem") .one
      (.op .sub [.var .local (ofString "len"), .var .local (ofString "i")]) body
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2 Rl := by
  dsimp only
  intro hnt hr
  refine precompile_byteEff_dec_resumes s _ _ _ _ _ hnt hr ?_
  intro val hval hntb hrb
  simp [evalHOLExact, evalListHOLExact, hl, hx, valueIsWord, valueWord, wordOpHOL, wordOp] at hval
  subst val
  apply hbody (setVarHOLFinite (ofString "rem") (.val (.word (len-i))) s) hc
    (guestInv_setVar _ _ s hi) rfl
  · intro name hne
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [BitVec.toNat_sub_of_le (show i ≤ len from hle)]
    exact hb
  · exact hntb
  · exact hrb

theorem precompile_sha256_blocks_exit_remainder {F : Type}
    (s : PanSemStateFiniteExact 64 F) (len i : BitVec 64)
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hx : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hle : i.toNat ≤ len.toNat) (hbound : len.toNat + 64 < 2^64)
    (hexit : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"), .const 64])) = some (.val (.word 0))) :
    len.toNat - i.toNat < 64 := by
  have hadd : (i+(64 : BitVec 64)).toNat = i.toNat+64 := by
    rw [BitVec.toNat_add]
    change (i.toNat+64) % 2^64 = i.toNat+64
    exact Nat.mod_eq_of_lt (by omega)
  simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hl, hx, valueIsWord, valueWord,
    wordOpHOL, wordOp, Compiler.Encoders.Asm.wordCmpHOL] at hexit
  change len.toNat < (i+(64 : BitVec 64)).toNat at hexit
  rw [hadd] at hexit
  omega

theorem precompile_sha256_blocks_active_bound {F : Type}
    (s : PanSemStateFiniteExact 64 F) (len i : BitVec 64)
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hx : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hle : i.toNat ≤ len.toNat) (hbound : len.toNat + 64 < 2^64)
    (ha : LoopActive (.cmp .notLower (.var .local (ofString "len"))
      (.op .add [.var .local (ofString "i"), .const 64])) s) :
    i.toNat + 64 ≤ len.toNat := by
  have hadd : (i+(64 : BitVec 64)).toNat = i.toNat+64 := by
    rw [BitVec.toNat_add]
    change (i.toNat+64) % 2^64 = i.toNat+64
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨v, hv, hn⟩ := ha
  simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hl, hx, valueIsWord, valueWord,
    wordOpHOL, wordOp, Compiler.Encoders.Asm.wordCmpHOL] at hv
  by_cases h : i+(64 : BitVec 64) ≤ len
  · change (i+(64 : BitVec 64)).toNat ≤ len.toNat at h
    rw [hadd] at h
    exact h
  · change ¬ i+64#64 ≤ len at h
    simp [h] at hv
    exact False.elim (hn hv.symm)

theorem precompile_sha256_blocks_increment {F : Type}
    (s : PanSemStateFiniteExact 64 F) (len i : BitVec 64)
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hx : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hb : i.toNat + 64 ≤ len.toNat) :
    let post := (evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 64]))).2
    post.locals.lookup (ofString "len") = some (.val (.word len)) ∧
    post.locals.lookup (ofString "i") = some (.val (.word (i+64))) ∧
    (i+64).toNat ≤ len.toNat := by
  have hv : isValidValueHOLExact s.toExact .local (ofString "i")
      (.val (.word (i+64#64))) = true := by
    simp [isValidValueHOLExact, lookupKvarHOLExact, hx, shapeOfHOLExact, shapeEqHOL]
  have ha : (i+(64 : BitVec 64)).toNat = i.toNat+64 := by
    rw [BitVec.toNat_add]
    change (i.toNat+64) % 2^64 = i.toNat+64
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt hb len.isLt)
  dsimp only
  constructor
  · simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hx,
      valueIsWord, valueWord, wordOpHOL, wordOp, hv, setKvarHOLFinite, setVarHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE, hl,
      show ofString "i" ≠ ofString "len" by decide]
  · constructor
    · simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hx,
        valueIsWord, valueWord, wordOpHOL, wordOp, hv, setKvarHOLFinite, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE]
    · exact ha ▸ hb

theorem precompile_sha256_blocks_body_index {F : Type}
    (s : PanSemStateFiniteExact 64 F) (len i : BitVec 64)
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hx : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hb : i.toNat + 64 ≤ len.toNat) :
    let body := ProgHOL.seq
      (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 64]))
    (evaluateHOLFiniteState s body).1 = none →
    let post := (evaluateHOLFiniteState s body).2
    post.locals.lookup (ofString "len") = some (.val (.word len)) ∧
    post.locals.lookup (ofString "i") = some (.val (.word (i+64))) ∧
    (i+64).toNat ≤ len.toNat := by
  dsimp only
  intro hr
  rw [evaluateHOLFiniteState_seq_line780] at hr ⊢
  rcases run : evaluateHOLFiniteState s
    (.call (some (none, none)) (ofString "sha256_block")
      [.var .global (ofString "sha_st"),
        .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]) with ⟨r,m⟩
  cases r with
  | none =>
    simp only [run] at hr ⊢
    have hloc := precompile_call0_locals_on_flow s (ofString "sha256_block")
      [.var .global (ofString "sha_st"),
        .op .add [.var .local (ofString "p"), .var .local (ofString "i")]] (by rw [run])
    rw [run] at hloc
    exact precompile_sha256_blocks_increment m len i (by rw [hloc]; exact hl)
      (by rw [hloc]; exact hx) hb
  | some r => simp [run] at hr

theorem precompile_while_normal_exit {F : Type}
    (P : PanSemStateFiniteExact 64 F → Prop) (cond : ExpHOL 64) (body : ProgHOL 64)
    (hdec : ∀ s, P s → P (decClockHOLFinite s))
    (hb : ∀ s, P s → LoopActive cond s →
      (evaluateHOLFiniteState s body).1 ≠ some .break ∧
      ((evaluateHOLFiniteState s body).1 = none ∨
        (evaluateHOLFiniteState s body).1 = some .continue → P (evaluateHOLFiniteState s body).2))
    (s : PanSemStateFiniteExact 64 F) (hp : P s)
    (hr : (evaluateHOLFiniteState s (.while cond body)).1 = none) :
    let post := (evaluateHOLFiniteState s (.while cond body)).2
    P post ∧ @evalHOLFinite 64 F _ post
      (fun a => Classical.propDecidable (post.memaddrs a)) cond = some (.val (.word 0)) := by
  rw [evaluateHOLFiniteState_while_total] at hr ⊢
  split
  · rename_i v hv
    rw [hv] at hr
    dsimp only at hr
    split
    · rename_i hn
      change v ≠ 0#64 at hn
      have hn' : v ≠ (0 : BitVec 64) := hn
      rw [if_pos hn'] at hr
      split
      · rename_i hz
        simp [hz] at hr
      · dsimp only at hr ⊢
        rename_i hz
        rw [if_neg hz] at hr
        rw [fixClockHOLFinite_evaluateState] at hr ⊢
        have ha : LoopActive cond (decClockHOLFinite s) :=
          loopActive_decClock ⟨_, hv, hn⟩
        obtain ⟨hnb, hpres⟩ := hb (decClockHOLFinite s) (hdec s hp) ha
        have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        rcases run : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r,mid⟩
        rw [run] at hnb hpres rem
        have hlt : mid.clock < s.clock := by change mid.clock ≤ s.clock-1 at rem; omega
        cases r with
        | none =>
          simp only [run] at hr ⊢
          exact precompile_while_normal_exit P cond body hdec hb mid (hpres (Or.inl rfl)) hr
        | some r =>
          cases r <;> simp only [run] at hr ⊢
          all_goals first
            | exact precompile_while_normal_exit P cond body hdec hb mid (hpres (Or.inr rfl)) hr
            | exact False.elim (hnb rfl)
            | cases hr
    · rename_i hn
      have hz : v = 0 := by simpa only [not_not] using hn
      exact ⟨hp, hz ▸ hv⟩
  · rename_i hn
    split at hr <;> simp_all
termination_by s.clock

theorem precompile_call0_ne_break {F : Type} (u : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vals
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite u.code.lookup fn vals with _ | ⟨body, callee, ret⟩
    · simp
    · dsimp only
      by_cases hk : u.clock = 0
      · rw [if_pos hk]; simp
      · rw [if_neg hk]
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite u callee) body with ⟨r, st⟩
        cases r with
        | none => simp
        | some r1 =>
          cases r1 with
          | returned rv => dsimp only; split <;> simp
          | _ => simp

theorem precompile_sha256_blocks_body_control {F : Type}
    (s : PanSemStateFiniteExact 64 F) :
    let body := ProgHOL.seq
      (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 64]))
    (evaluateHOLFiniteState s body).1 ≠ some .break ∧
      (evaluateHOLFiniteState s body).1 ≠ some .continue := by
  dsimp only
  have hc := precompile_call0_ne_continue s (ofString "sha256_block")
    [.var .global (ofString "sha_st"),
      .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]
  rw [evaluateHOLFiniteState_seq_line780]
  rcases run : evaluateHOLFiniteState s
    (.call (some (none, none)) (ofString "sha256_block")
      [.var .global (ofString "sha_st"),
        .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]) with ⟨r,m⟩
  cases r with
  | none =>
    dsimp only
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | some r =>
    dsimp only
    rw [run] at hc
    constructor
    · have hn := precompile_call0_ne_break s (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]
      simpa only [run] using hn
    · exact hc

theorem precompile_sha256_blocks_normal_remainder {F : Type}
    (s : PanSemStateFiniteExact 64 F) (len : BitVec 64)
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hx : ∃ i : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ len.toNat)
    (hbound : len.toNat + 64 < 2^64) :
    let loop := ProgHOL.while
      (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"), .const 64]))
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 64])))
    (evaluateHOLFiniteState s loop).1 = none →
    let post := (evaluateHOLFiniteState s loop).2
    post.locals.lookup (ofString "len") = some (.val (.word len)) ∧
      ∃ i : BitVec 64, post.locals.lookup (ofString "i") = some (.val (.word i)) ∧
        i.toNat ≤ len.toNat ∧ len.toNat-i.toNat < 64 := by
  dsimp only
  intro hr
  let P := fun (t : PanSemStateFiniteExact 64 F) =>
    t.locals.lookup (ofString "len") = some (.val (.word len)) ∧
    ∃ i : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ len.toNat
  have he := precompile_while_normal_exit P _ _ ?_ ?_ s ⟨hl,hx⟩ hr
  · obtain ⟨⟨hlp,i,hip,hib⟩, hguard⟩ := he
    exact ⟨hlp, i, hip, hib, precompile_sha256_blocks_exit_remainder _ len i hlp hip hib hbound hguard⟩
  · intro t ht
    exact ht
  · intro t ht ha
    obtain ⟨hlt,i,hit,hib⟩ := ht
    refine ⟨(precompile_sha256_blocks_body_control t).1, ?_⟩
    intro hflow
    rcases hflow with hflow|hflow
    · have hb := precompile_sha256_blocks_active_bound t len i hlt hit hib hbound ha
      obtain ⟨hln,hin,hbn⟩ := precompile_sha256_blocks_body_index t len i hlt hit hb hflow
      exact ⟨hln,i+64,hin,hbn⟩
    · exact False.elim ((precompile_sha256_blocks_body_control t).2 hflow)

theorem precompile_sha256_blocks_body_local {F : Type}
    (s : PanSemStateFiniteExact 64 F) (name : MlS) (hne : name ≠ ofString "i") :
    let body := ProgHOL.seq
      (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 64]))
    (evaluateHOLFiniteState s body).1 = none →
    (evaluateHOLFiniteState s body).2.locals.lookup name = s.locals.lookup name := by
  dsimp only
  intro hr
  rw [evaluateHOLFiniteState_seq_line780] at hr ⊢
  rcases run : evaluateHOLFiniteState s
    (.call (some (none, none)) (ofString "sha256_block")
      [.var .global (ofString "sha_st"),
        .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]) with ⟨r,m⟩
  cases r with
  | none =>
    dsimp only
    have hloc := precompile_call0_locals_on_flow s (ofString "sha256_block")
      [.var .global (ofString "sha_st"),
        .op .add [.var .local (ofString "p"), .var .local (ofString "i")]] (by rw [run])
    rw [run] at hloc
    rw [evaluateHOLFiniteState_assign]
    split
    · exact congrArg (fun l => l.lookup name) hloc
    · simp only [setKvarHOLFinite, setVarHOLFinite]
      split
      · simpa [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne] using
          congrArg (fun l => l.lookup name) hloc
      · exact congrArg (fun l => l.lookup name) hloc
  | some r => simp [run] at hr

theorem precompile_sha256_blocks_normal_local {F : Type}
    (s : PanSemStateFiniteExact 64 F) (name : MlS) (hne : name ≠ ofString "i") :
    let loop := ProgHOL.while
      (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"), .const 64]))
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 64])))
    (evaluateHOLFiniteState s loop).1 = none →
    (evaluateHOLFiniteState s loop).2.locals.lookup name = s.locals.lookup name := by
  dsimp only
  intro hr
  have he := precompile_while_normal_exit
    (fun (t : PanSemStateFiniteExact 64 F) => t.locals.lookup name = s.locals.lookup name)
    _ _ (fun t ht => ht) ?_ s rfl hr
  · exact he.1
  · intro t ht ha
    refine ⟨(precompile_sha256_blocks_body_control t).1, ?_⟩
    intro hflow
    rcases hflow with hflow|hflow
    · exact (precompile_sha256_blocks_body_local t name hne hflow).trans ht
    · exact False.elim ((precompile_sha256_blocks_body_control t).2 hflow)

open R10Shards.P26_P28 in
theorem precompile_sha256_blocks_then {F : Type}
    (s : PanSemStateFiniteExact 64 F) (stp len : BitVec 64)
    (body : ProgHOL 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hx : ∃ i : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ len.toNat)
    (hbound : len.toNat + 64 < 2^64)
    (hin : ∀ i ∈ [(stp.toNat,64)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1+i.2 ≤ j.1+j.2)
    (hbody : ∀ (m : PanSemStateFiniteExact 64 F), m.code = originalRuntimeCode → GuestInv m →
      m.globals = s.globals →
      (∀ name, name ≠ ofString "i" → m.locals.lookup name = s.locals.lookup name) →
      m.locals.lookup (ofString "len") = some (.val (.word len)) →
      (∃ i : BitVec 64, m.locals.lookup (ofString "i") = some (.val (.word i)) ∧
        i.toNat ≤ len.toNat ∧ len.toNat-i.toNat < 64) →
      (evaluateHOLFiniteState m body).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState m body).1 = none ∨ Resumes (evaluateHOLFiniteState m body).1) →
      ByteEff m (evaluateHOLFiniteState m body).2 Rl) :
    let loop := ProgHOL.while
      (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"), .const 64]))
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 64])))
    (evaluateHOLFiniteState s (.seq loop body)).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s (.seq loop body)).1 = none ∨ Resumes (evaluateHOLFiniteState s (.seq loop body)).1) →
    ByteEff s (evaluateHOLFiniteState s (.seq loop body)).2 Rl := by
  dsimp only
  intro hnt hr
  have he := precompile_sha256_blocks_loop_effect s stp hc hi hs
  refine precompile_byteEff_seq_resumes s _ body Rl hnt hr
    (fun _ _ => he.mono hin) ?_
  intro m run hntm hrm
  have hn : (evaluateHOLFiniteState s _).1 = none := congrArg Prod.fst run
  obtain ⟨hlm,hxm⟩ := precompile_sha256_blocks_normal_remainder s len hl hx hbound hn
  have hloc := fun name hne => precompile_sha256_blocks_normal_local s name hne hn
  rw [run] at he hlm hxm
  apply hbody m (he.code.trans hc)
    (guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi) he.globals
  · intro name hne
    simpa only [run] using hloc name hne
  · exact hlm
  · exact hxm
  · exact hntm
  · exact hrm

open R10Shards.P26_P28 in
theorem precompile_sha256_blocks_padding_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hx : ∃ i : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ len.toNat)
    (hbound : len.toNat + 64 < 2^64) (hpad : pad.toNat + 128 ≤ heapEnd)
    (hob : out.toNat + 32 < 2^64) :
    let tail := ProgHOL.seq
      (.call (some (none, none)) (ofString "st_be64")
        [.op .sub [.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "total")],
          .const 8], .shift .lsl (.var .local (ofString "len")) (.const 3)])
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"), .var .global (ofString "sha_pad")])
        (.seq (.ite (.cmp .equal (.var .local (ofString "total")) (.const 128))
          (.call (some (none, none)) (ofString "sha256_block")
            [.var .global (ofString "sha_st"),
              .op .add [.var .global (ofString "sha_pad"), .const 64]]) .skip)
          (.seq (.call (some (none, none)) (ofString "sha256_finish")
            [.var .global (ofString "sha_st"), .var .local (ofString "out")])
            (.return (.const 0)))))
    let final := ProgHOL.dec (ofString "total") .one (.const 64)
      (.seq (.ite (.cmp .notLower (.var .local (ofString "rem")) (.const 56))
        (.assign .local (ofString "total") (.const 128)) .skip) tail)
    let padding := ProgHOL.seq
      (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "sha_pad"), .const 128])
      (.seq (.call (some (none, none)) (ofString "memcpy")
        [.var .global (ofString "sha_pad"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
          .var .local (ofString "rem")])
        (.seq (.storeByte (.op .add [.var .global (ofString "sha_pad"), .var .local (ofString "rem")])
          (.const 128)) final))
    let rest := ProgHOL.dec (ofString "rem") .one
      (.op .sub [.var .local (ofString "len"), .var .local (ofString "i")]) padding
    let loop := ProgHOL.while
      (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"), .const 64]))
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 64])))
    (evaluateHOLFiniteState s (.seq loop rest)).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s (.seq loop rest)).1 = none ∨ Resumes (evaluateHOLFiniteState s (.seq loop rest)).1) →
    ByteEff s (evaluateHOLFiniteState s (.seq loop rest)).2
      [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)] := by
  dsimp only
  intro hnt hr
  refine precompile_sha256_blocks_then s stp len _ _ hc hi hs hl hx hbound ?_ ?_ hnt hr
  · intro i hi hpos
    simp only [List.mem_singleton] at hi
    subst i
    exact ⟨_, by simp, le_rfl, le_rfl⟩
  · intro m hcm him hgm hlm hlen hindex hntm hrm
    obtain ⟨i, hxi, hile, hirem⟩ := hindex
    refine precompile_sha256_remainder_then m len i _ _ hcm him hlen hxi hile hirem ?_ hntm hrm
    intro n hcn hin hgn hln hrem hremb hntn hrn
    exact precompile_sha256_padding_path_effect n pad (len-i) stp out _ hcn hin
      (by rw [hgn,hgm]; exact hp) hrem (by rw [hgn,hgm]; exact hs)
      (by rw [hln _ (by decide),hlm _ (by decide)]; exact ho) hremb hpad hob hntn hrn

open R10Shards.P26_P28 in
theorem precompile_sha256_body_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hbound : len.toNat + 64 < 2^64) (hpad : pad.toNat + 128 ≤ heapEnd)
    (hob : out.toNat + 32 < 2^64)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256)).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256)).1 = none ∨
      Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256)).1) :
    ByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256)).2
      [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)] := by
  change ByteEff s (evaluateHOLFiniteState s (.seq
    (.call (some (none,none)) (ofString "sha256_state_init") [.var .global (ofString "sha_st")]) _)).2 _
  have he := precompile_sha256_init_call_effect s stp (.var .global (ofString "sha_st")) hc hi
    (by simp [evalHOLFinite, evalHOLExact, hs])
  refine precompile_byteEff_seq_resumes s _ _ _ hnt hr (fun _ _ => he.mono ?_) ?_
  · intro i hi hpos
    simp only [List.mem_singleton] at hi
    subst i
    exact ⟨_, by simp, le_rfl, le_rfl⟩
  · intro m run hntm hrm
    have hloc := precompile_call0_locals_on_flow s (ofString "sha256_state_init")
      [.var .global (ofString "sha_st")] (by rw [run])
    rw [run] at he hloc
    refine precompile_byteEff_dec_resumes m _ _ _ _ _ hntm hrm ?_
    intro val hval hntb hrb
    change some (.val (.word (0 : BitVec 64))) = some val at hval
    injection hval with hval
    subst val
    apply precompile_sha256_blocks_padding_effect
      (setVarHOLFinite (ofString "i") (.val (.word 0)) m) pad stp out len
    · exact he.code.trans hc
    · exact guestInv_setVar _ _ m (guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi)
    · change m.globals.lookup _ = _
      rw [he.globals]; exact hp
    · change m.globals.lookup _ = _
      rw [he.globals]; exact hs
    · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "out" by decide, if_false]
      rw [hloc]; exact ho
    · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "len" by decide, if_false]
      rw [hloc]; exact hl
    · exact ⟨0, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], by simp⟩
    · exact hbound
    · exact hpad
    · exact hob
    · exact hntb
    · exact hrb

open R10Shards.P26_P28 in
theorem precompile_call0_byteEff_resumes_at {F : Type} (fname : MlS)
    (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (ret : ShapeHOL)
    (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64)) (Rl : List Ivl)
    (hl : originalRuntimeCode.lookup fname = some (params, body, ret))
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hf : ∀ (entry : PanSemStateFiniteExact 64 F) vals,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      entry.code = originalRuntimeCode → GuestInv entry → entry.globals = s.globals →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, entry.locals, ret) →
      (evaluateHOLFiniteState entry body).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState entry body).1 = none ∨ Resumes (evaluateHOLFiniteState entry body).1) →
      ByteEff entry (evaluateHOLFiniteState entry body).2 Rl)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    ByteEff s (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 Rl := by
  rw [evaluateHOLFiniteState_call] at hnt hr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact ByteEff.refl s Rl
  · dsimp only at hnt hr ⊢
    rw [hargs] at hnt hr
    dsimp only at hnt hr
    rcases hlook : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact ByteEff.refl s Rl
    · dsimp only at hnt hr ⊢
      rw [hlook] at hnt hr
      dsimp only at hnt hr
      have heq := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hl) hlook
      subst heq
      have heq := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hl) hlook
      subst heq
      by_cases hz : s.clock = 0
      · simp only [hz, ↓reduceIte]
        exact (ByteEff.refl s Rl).locals_clock _ _
      · simp only [hz, ↓reduceIte] at hnt hr ⊢
        let entry := callEntryStateHOLFinite s callee
        have hge : GuestInv entry := guestInv_callEntry s callee hi
        have hle : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals =
            some (body', entry.locals, ret') := by
          simpa [hc, entry, callEntryStateHOLFinite] using hlook
        have hn : (evaluateHOLFiniteState entry body').1 ≠ some .timeOut := by
          intro h
          rcases run : evaluateHOLFiniteState entry body' with ⟨r,m⟩
          rw [run] at h
          dsimp only at h
          subst r
          exact hnt (by simp [entry] at run; rw [run])
        have hres : (evaluateHOLFiniteState entry body').1 = none ∨
            Resumes (evaluateHOLFiniteState entry body').1 := by
          rcases run : evaluateHOLFiniteState entry body' with ⟨r,m⟩
          cases r with
          | none => exact Or.inl rfl
          | some r =>
            cases r <;> simp_all [entry, Resumes]
        have he := hf entry vals hargs hc hge rfl hle hn hres
        dsimp only [entry] at he
        rcases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        rw [run] at he
        have eff : ByteEff s post Rl := ((ByteEff.refl s _).locals_clock _ _).trans he
        cases res with
        | none => exact eff.locals_clock _ _
        | some r =>
          cases r <;> dsimp only
          all_goals first
            | exact eff.locals_clock _ _
            | (split <;> exact eff.locals_clock _ _)

open R10Shards.P26_P28 in
theorem precompile_sha256_call_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len : BitVec 64)
    (ptr count dest : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hlength : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) count =
      some (.val (.word len)))
    (hout : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) dest =
      some (.val (.word out)))
    (hbound : len.toNat + 64 < 2^64) (hpad : pad.toNat + 128 ≤ heapEnd)
    (hob : out.toNat + 32 < 2^64)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "sha256") [ptr,count,dest])).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "sha256") [ptr,count,dest])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "sha256") [ptr,count,dest])).1) :
    ByteEff s (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "sha256") [ptr,count,dest])).2
      [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)] := by
  have hl : originalRuntimeCode.lookup (ofString "sha256") =
      some ([(ofString "p",.one),(ofString "len",.one),(ofString "out",.one)],
        sourceFnBody Guest.Software.guestFn_sha256,.one) :=
    lookup_of_guestAst_getElem 95 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256) rfl
  refine precompile_call0_byteEff_resumes_at _ _ _ _ s _ _ hl hc hi ?_ hnt hr
  intro entry vals hargs hce hie hge hle hnte hre
  obtain ⟨p,n,o,hvals,hpl,hnl,hol⟩ := lookupCode_three_words (by decide) (by decide) (by decide) hl hle
  have heq : n = len ∧ o = out := by
    rw [hvals] at hargs
    change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) count = some (.val (.word len)) at hlength
    change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dest = some (.val (.word out)) at hout
    simp [evalListHOLFinite, evalListHOLExact, hlength, hout] at hargs
    split at hargs <;> simp_all
  rcases heq with ⟨hen,heo⟩
  subst n
  subst o
  exact precompile_sha256_body_effect entry pad stp out len hce hie
    (by rw [hge]; exact hp) (by rw [hge]; exact hs) hol hnl hbound hpad hob hnte hre

open R10Shards.P26_P28 in
theorem precompile_sha256_call_then {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len : BitVec 64)
    (ptr count dest : ExpHOL 64) (body : ProgHOL 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hlength : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) count =
      some (.val (.word len)))
    (hout : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) dest =
      some (.val (.word out)))
    (hbound : len.toNat + 64 < 2^64) (hpad : pad.toNat + 128 ≤ heapEnd)
    (hob : out.toNat + 32 < 2^64)
    (hin : ∀ i ∈ [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)], 0 < i.2 →
      ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1+i.2 ≤ j.1+j.2)
    (hbody : ∀ (m : PanSemStateFiniteExact 64 F), m.code = originalRuntimeCode → GuestInv m →
      m.globals = s.globals → m.locals = s.locals →
      ByteEff s m [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)] →
      (evaluateHOLFiniteState m body).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState m body).1 = none ∨ Resumes (evaluateHOLFiniteState m body).1) →
      ByteEff m (evaluateHOLFiniteState m body).2 Rl) :
    let p := ProgHOL.seq (.call (some (none,none)) (ofString "sha256") [ptr,count,dest]) body
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2 Rl := by
  dsimp only
  intro hnt hr
  have he := precompile_sha256_call_effect s pad stp out len ptr count dest hc hi hp hs
    hlength hout hbound hpad hob
  refine precompile_byteEff_seq_resumes s _ body Rl hnt hr
    (fun hntc hrc => (he hntc hrc).mono hin) ?_
  intro m run hntm hrm
  have hn : (evaluateHOLFiniteState s _).1 = none := congrArg Prod.fst run
  have heff := he (by rw [hn]; simp) (Or.inl hn)
  have hl := precompile_call0_locals_on_flow s (ofString "sha256") [ptr,count,dest] hn
  rw [run] at heff hl
  exact hbody m (heff.code.trans hc)
    (guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hi)
    heff.globals hl heff hntm hrm

open R10Shards.P26_P28 in
theorem precompile_output_tail_byteEff {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ev out size : BitVec 64) (name : MlS)
    (hi : GuestInv s)
    (hev : s.globals.lookup (ofString "ev") = some (.val (.word ev)))
    (hout : s.locals.lookup name = some (.val (.word out)))
    (hb : ev.toNat+136 ≤ heapEnd) :
    let p := ProgHOL.seq
      (.store (.op .add [.var .global (ofString "ev"), .const 120]) (.var .local name))
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const 128]) (.const size))
        (.return (.const 0)))
    ByteEff s (evaluateHOLFiniteState s p).2 [(ev.toNat,136)] := by
  dsimp only
  have he : ByteEff s (evaluateHOLFiniteState s (.store
      (.op .add [.var .global (ofString "ev"), .const 120]) (.var .local name))).2
      [(ev.toNat,136)] := by
    refine byteEff_store_at hi _ _ ev 120 136 hb
      (fun _ => ⟨(ev.toNat,136), by simp, le_rfl, le_rfl⟩) ?_ (by decide) ?_
    · intro v hv
      simp [evalHOLExact, hout] at hv
      exact ⟨out,hv.symm⟩
    · simp [evalHOLExact, evalListHOLExact, hev, valueIsWord, valueWord, wordOpHOL, wordOp]
  refine byteEff_seq he ?_
  intro m run
  have hem := he
  rw [run] at hem
  have him : GuestInv m := guestInv_congr hem.code hem.memaddrs hem.shMemaddrs hem.baseAddr hi
  have hev' : m.globals.lookup (ofString "ev") = some (.val (.word ev)) := by
    rw [hem.globals]; exact hev
  have he2 : ByteEff m (evaluateHOLFiniteState m (.store
      (.op .add [.var .global (ofString "ev"), .const 128]) (.const size))).2
      [(ev.toNat,136)] := by
    refine byteEff_store_at him _ _ ev 128 136 hb
      (fun _ => ⟨(ev.toNat,136), by simp, le_rfl, le_rfl⟩) ?_ (by decide) ?_
    · intro v hv
      simp only [evalHOLExact, Option.some.injEq] at hv
      exact ⟨size,hv.symm⟩
    · simp [evalHOLExact, evalListHOLExact, hev', valueIsWord, valueWord, wordOpHOL, wordOp]
  exact byteEff_seq he2 (fun n _ => byteEff_return n _ _)

open R10Shards.P26_P28 in
theorem precompile_sha256_output_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len ev : BitVec 64) (ptr : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hev : s.globals.lookup (ofString "ev") = some (.val (.word ev)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word len)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hbound : len.toNat+64 < 2^64) (hpad : pad.toNat+128 ≤ heapEnd)
    (hob : out.toNat+32 < 2^64) (hevbound : ev.toNat+136 ≤ heapEnd) :
    let p := ProgHOL.seq
      (.call (some (none,none)) (ofString "sha256")
        [ptr,.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local (ofString "out")))
        (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const 32))
          (.return (.const 0))))
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2
      [(pad.toNat,128),(stp.toNat,64),(out.toNat,32),(ev.toNat,136)] := by
  dsimp only
  intro hnt hr
  refine precompile_sha256_call_then s pad stp out len ptr _ _ _ _ hc hi hp hs
    (by simp [evalHOLFinite,evalHOLExact,hn]) (by simp [evalHOLFinite,evalHOLExact,ho])
    hbound hpad hob ?_ ?_ hnt hr
  · intro i hi hpos
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> exact ⟨_,by simp,le_rfl,le_rfl⟩
  · intro m hcm him hgm hlm he hntm hrm
    exact (precompile_output_tail_byteEff m ev out 32 (ofString "out") him
      (by rw [hgm]; exact hev) (by rw [hlm]; exact ho) hevbound).mono (by
        intro i hi hpos
        simp only [List.mem_singleton] at hi
        subst i
        exact ⟨(ev.toNat,136),by simp,le_rfl,le_rfl⟩)

open R10Shards.P26_P28 in
theorem precompile_output_store_precise {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ev : BitVec 64) (off : Nat) (value : ExpHOL 64)
    (hi : GuestInv s)
    (hev : s.globals.lookup (ofString "ev") = some (.val (.word ev)))
    (hoff : off = 120 ∨ off = 128) (hb : ev.toNat+136 < 2^64)
    (hv : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) value =
      some v → ∃ w : BitVec 64, v = .val (.word w)) :
    ByteEff s (evaluateHOLFiniteState s (.store
      (.op .add [.var .global (ofString "ev"),.const (BitVec.ofNat 64 off)]) value)).2
      [(ev.toNat+120,16)] := by
  refine (byteEff_store_one hi _ _ hv ?_).1
  intro x hx hmem
  have ho : off < 2^64 := by rcases hoff with rfl|rfl <;> decide
  have heval : x = ev+BitVec.ofNat 64 off := by
    simp [evalHOLExact,evalListHOLExact,hev,valueIsWord,valueWord,wordOpHOL,wordOp] at hx
    exact hx.symm
  subst x
  have hnat : (ev+BitVec.ofNat 64 off).toNat = ev.toNat+off := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ho,Nat.mod_eq_of_lt (by
      rcases hoff with rfl|rfl <;> omega)]
  exact ⟨(ev.toNat+120,16),by simp,by rw [hnat]; rcases hoff with rfl|rfl <;> omega,
    by rw [hnat]; rcases hoff with rfl|rfl <;> omega⟩

open R10Shards.P26_P28 in
theorem precompile_output_tail_precise_byteEff {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ev out size : BitVec 64) (name : MlS)
    (hi : GuestInv s)
    (hev : s.globals.lookup (ofString "ev") = some (.val (.word ev)))
    (hout : s.locals.lookup name = some (.val (.word out)))
    (hb : ev.toNat+136 < 2^64) :
    let p := ProgHOL.seq
      (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local name))
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const size))
        (.return (.const 0)))
    ByteEff s (evaluateHOLFiniteState s p).2 [(ev.toNat+120,16)] := by
  dsimp only
  have he := precompile_output_store_precise s ev 120 (.var .local name) hi hev (Or.inl rfl) hb (by
    intro v hv
    simp [evalHOLExact,hout] at hv
    exact ⟨out,hv.symm⟩)
  refine byteEff_seq he ?_
  intro m run
  change evaluateHOLFiniteState s (.store
    (.op .add [.var .global (ofString "ev"),.const 120#64]) (.var .local name)) = (none,m) at run
  rw [run] at he
  have him : GuestInv m := guestInv_congr he.code he.memaddrs he.shMemaddrs he.baseAddr hi
  have he2 := precompile_output_store_precise m ev 128 (.const size) him
    (by rw [he.globals]; exact hev) (Or.inr rfl) hb (by
      intro v hv
      simp only [evalHOLExact,Option.some.injEq] at hv
      exact ⟨size,hv.symm⟩)
  exact byteEff_seq he2 (fun n _ => byteEff_return n _ _)

open R10Shards.P26_P28 in
theorem precompile_sha256_output_precise_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len ev : BitVec 64) (ptr : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hev : s.globals.lookup (ofString "ev") = some (.val (.word ev)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word len)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hbound : len.toNat+64 < 2^64) (hpad : pad.toNat+128 ≤ heapEnd)
    (hob : out.toNat+32 < 2^64) (hevbound : ev.toNat+136 < 2^64) :
    let p := ProgHOL.seq
      (.call (some (none,none)) (ofString "sha256")
        [ptr,.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local (ofString "out")))
        (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const 32))
          (.return (.const 0))))
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) →
    ByteEff s (evaluateHOLFiniteState s p).2
      [(pad.toNat,128),(stp.toNat,64),(out.toNat,32),(ev.toNat+120,16)] := by
  dsimp only
  intro hnt hr
  refine precompile_sha256_call_then s pad stp out len ptr _ _ _ _ hc hi hp hs
    (by simp [evalHOLFinite,evalHOLExact,hn]) (by simp [evalHOLFinite,evalHOLExact,ho])
    hbound hpad hob ?_ ?_ hnt hr
  · intro i hi hpos
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> exact ⟨_,by simp,le_rfl,le_rfl⟩
  · intro m hcm him hgm hlm he hntm hrm
    exact (precompile_output_tail_precise_byteEff m ev out 32 (ofString "out") him
      (by rw [hgm]; exact hev) (by rw [hlm]; exact ho) hevbound).mono (by
        intro i hi hpos
        simp only [List.mem_singleton] at hi
        subst i
        exact ⟨(ev.toNat+120,16),by simp,le_rfl,le_rfl⟩)

open R10Shards.P26_P28 in
theorem precompile_chain_cells_of_disjoint_byteEff {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {rl : List Ivl}
    (hi : Wave8Contracts.M23.EvmInvAt s S) (he : ByteEff s post rl)
    (hd : ∀ i ∈ rl, ∀ j ∈ ((evmChain s).map (frameObjects s)).flatten, Disj i j) :
    ChainCellsAgree s post := by
  have word : ∀ ec ∈ evmChain s, ∀ base sz k : Nat,
      (base,sz) ∈ frameScratch s ec → k % 8 = 0 → k+8 < sz →
      memW post (base+k) = memW s (base+k) := by
    intro ec hec base sz k hj hk8 hk
    have hf := hi.2.2.2.2.1 ec hec
    have hb : base+sz ≤ 2^64 := le_trans (hf.1 (base,sz) hj).1.2 (by
      rw [R11Shards.scratchEnd_val]; decide)
    have hbase8 := (hf.1 (base,sz) hj).2.1
    have hj' : (base,sz) ∈ frameObjects s ec := by
      simp only [frameScratch,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with h|h|h|h <;> simp [frameObjects,←h]
    refine (InitECandidate.Solver.Wave8GuestInv.SoloHtabSet.memW_eq_iff_memB he.be
      (by omega) (by omega) (by omega) (by omega)).mpr ?_
    intro r hr
    by_contra hn
    obtain ⟨i,hir,hib⟩ := he.byte_frame (base+k+r) (by omega) hn
    have hdis := hd i hir (base,sz) (List.mem_flatten.mpr
      ⟨frameObjects s ec,List.mem_map.mpr ⟨ec,hec,rfl⟩,hj'⟩)
    rcases i with ⟨a,n⟩
    simp only [InIvl,Disj] at hib hdis
    rcases hdis with h|h|h|h <;> omega
  intro ec hec
  exact ⟨word ec hec ec.1 280 24 (by simp [frameScratch]) (by omega) (by omega),
    word ec hec ec.1 280 32 (by simp [frameScratch]) (by omega) (by omega),
    word ec hec ec.1 280 40 (by simp [frameScratch]) (by omega) (by omega),
    word ec hec ec.2 104 56 (by simp [frameScratch]) (by omega) (by omega)⟩

theorem precompile_sha256_call_evmStep {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len : BitVec 64)
    (ptr count dest : ExpHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hav : Wave8Contracts.M23.EvmAvoids
      (fun {_} _ => [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)]) s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hlength : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) count =
      some (.val (.word len)))
    (hout : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) dest =
      some (.val (.word out)))
    (hbound : len.toNat+64 < 2^64) (hpad : pad.toNat+128 ≤ heapEnd)
    (hob : out.toNat+32 < 2^64)
    (hnt : (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "sha256") [ptr,count,dest])).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "sha256") [ptr,count,dest])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "sha256") [ptr,count,dest])).1) :
    Wave8Contracts.M23.EvmStep [] s
      (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "sha256") [ptr,count,dest])).2 := by
  exact Wave8Contracts.M23.ByteRegionEffect.to_evmStep_avoids hav
    (precompile_byteEff_to_region (precompile_sha256_call_effect s pad stp out len ptr count dest hc
      hav.1.1 hp hs hlength hout hbound hpad hob hnt hr))

theorem precompile_sha256_call_evmStepCC {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len : BitVec 64)
    (ptr count dest : ExpHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hav : Wave8Contracts.M23.EvmAvoids
      (fun {_} _ => [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)]) s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hlength : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) count =
      some (.val (.word len)))
    (hout : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) dest =
      some (.val (.word out)))
    (hbound : len.toNat+64 < 2^64) (hpad : pad.toNat+128 ≤ heapEnd)
    (hob : out.toNat+32 < 2^64)
    (hnt : (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "sha256") [ptr,count,dest])).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "sha256") [ptr,count,dest])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "sha256") [ptr,count,dest])).1) :
    EvmStepCC [] s
      (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "sha256") [ptr,count,dest])).2 := by
  have he := precompile_sha256_call_effect s pad stp out len ptr count dest hc
    hav.1.1 hp hs hlength hout hbound hpad hob hnt hr
  refine ⟨Wave8Contracts.M23.ByteRegionEffect.to_evmStep_avoids hav
    (precompile_byteEff_to_region he),?_⟩
  obtain ⟨ha,S,hat,Nd,htr,hd⟩ := hav
  exact precompile_chain_cells_of_disjoint_byteEff hat he
    (fun i hi j hj => hd i hi j (List.mem_append_right _ hj))

theorem precompile_global_buffer_bound {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hi : EvmInv s)
    (gn : String × Nat) (hg : gn ∈ globalBuffers)
    (p : BitVec 64) (hp : s.globals.lookup (ofString gn.1) = some (.val (.word p)))
    (hnz : p.toNat ≠ 0) (hn : gn.2 ≠ 0) :
    p.toNat + gn.2 ≤ heapEnd := by
  obtain ⟨ha,S,hat⟩ := (evmInv_iff_at s).1 hi
  have hf : bufferRegion s gn ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append.mpr; left
    apply List.mem_append.mpr; left
    apply List.mem_append.mpr; left
    exact List.mem_map.mpr ⟨gn,hg,rfl⟩
  have hfix := hat.1.2.2.1.1 _ hf
  have heq : bufferRegion s gn = (p.toNat,gn.2) := by
    simp [bufferRegion,globN,hp,hnz]
  rw [heq] at hfix
  rcases hfix with hz|⟨ha',_⟩
  · exact absurd hz hn
  · rcases ha' with hh|hs
    · have lim := ha.2.2.1
      have hlim : heapLimit ≤ heapEnd := by decide
      exact le_trans hh.2 (le_trans lim hlim)
    · have hlim : scratchEnd ≤ heapEnd := by decide
      exact le_trans hs.2 hlim

theorem precompile_sha256_globals_of_evmInv {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hi : EvmInv s)
    (hpad : globN s "sha_pad" ≠ 0) (hst : globN s "sha_st" ≠ 0) :
    ∃ pad stp heap : BitVec 64,
      s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)) ∧
      s.globals.lookup (ofString "sha_st") = some (.val (.word stp)) ∧
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      pad.toNat ≠ 0 ∧ stp.toNat ≠ 0 ∧ pad.toNat+128 ≤ heapEnd ∧
      heap.toNat+32 < 2^64 := by
  have words := hi.1.2.2.2.2.2.2.2.2.2
  obtain ⟨pad,hp⟩ := words "sha_pad" (by decide)
  obtain ⟨stp,hs⟩ := words "sha_st" (by decide)
  obtain ⟨heap,hh⟩ := words "heap_ptr" (by decide)
  change s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)) at hp
  change s.globals.lookup (ofString "sha_st") = some (.val (.word stp)) at hs
  change s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) at hh
  have hpv : pad.toNat = globN s "sha_pad" := by simp [globN,hp]
  have hsv : stp.toNat = globN s "sha_st" := by simp [globN,hs]
  have hhv : heap.toNat = globN s "heap_ptr" := by simp [globN,hh]
  have hpz : pad.toNat ≠ 0 := by rw [hpv]; exact hpad
  have hsz : stp.toNat ≠ 0 := by rw [hsv]; exact hst
  refine ⟨pad,stp,heap,hp,hs,hh,hpz,hsz,
    precompile_global_buffer_bound hi ("sha_pad",128) (by decide) pad hp hpz (by decide),?_⟩
  have hb := hi.1.2.2.1
  have hc : heapLimit+32 < 2^64 := by decide
  rw [hhv]
  omega

theorem precompile_sha256_buffers_avoid {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp : BitVec 64)
    (hi : EvmInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hpad : pad.toNat ≠ 0) (hst : stp.toNat ≠ 0) :
    Wave8Contracts.M23.EvmAvoids (fun {_} _ => [(pad.toNat,128),(stp.toNat,64)]) s := by
  have hav := evmAvoids_frameStart_of_evmInv s hi
  obtain ⟨ha,S,hin,Nd,htr,hdj⟩ := hav
  refine ⟨ha,S,hin,Nd,htr,?_⟩
  intro i him j hjm
  apply hdj i ?_ j hjm
  change i ∈ [bufferRegion s ("b2_v",128),bufferRegion s ("bn_expw",352),
    bufferRegion s ("bn_gamma",384),bufferRegion s ("keccak_pad",136),
    bufferRegion s ("keccak_st",200),bufferRegion s ("mpt_nib_scratch",64),
    bufferRegion s ("pre_hdr_buf",96),bufferRegion s ("rmd_h",40),
    bufferRegion s ("rmd_pad",128),bufferRegion s ("rmd_x",128),
    bufferRegion s ("sha_pad",128),bufferRegion s ("sha_st",64),
    bufferRegion s ("sk_buf",52),bufferRegion s ("u256_ws",640)]
  have hp' : bufferRegion s ("sha_pad",128) = (pad.toNat,128) := by
    simp [bufferRegion,globN,hp,hpad]
  have hs' : bufferRegion s ("sha_st",64) = (stp.toNat,64) := by
    simp [bufferRegion,globN,hs,hst]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at him
  rcases him with rfl|rfl
  · rw [←hp']; simp
  · rw [←hs']; simp

theorem precompile_fresh_output_avoid {F : Type}
    {s allocated : PanSemStateFiniteExact 64 F} (out : BitVec 64)
    (hi : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s allocated)
    (hm : allocated.memory = s.memory) (hb : allocated.be = s.be)
    (hfresh : Inside (out.toNat,32) (globN s "heap_ptr") (globN allocated "heap_ptr")) :
    Wave8Contracts.M23.EvmAvoids (fun {_} _ => [(out.toNat,32)]) allocated := by
  obtain ⟨ha,S,hat⟩ := (evmInv_iff_at s).1 hi
  obtain ⟨Nd,htr,hatn⟩ := hat.2.2.2.2.2.2.2.2.2.1
  have hout : ∀ a : BitVec 64, ¬ s.memaddrs a → allocated.memory a = s.memory a := by
    intro a _; rw [hm]
  have hbyte : ∀ b : Nat, b < 2^64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN allocated "heap_ptr") → memB allocated b = memB s b := by
    intro b _ _; unfold memB; rw [hm,hb]
  obtain ⟨hat',htr',hatn'⟩ := transfer_fixed_witness_of_accumulated_frame hi hat htr hatn hstep hb hout hbyte
  have hwt : WorldTypedWith s S Nd := ⟨hat.1.1,hat.1.2.1,hat.1.2.2.1,htr⟩
  obtain ⟨hw,hf,_⟩ := transfer_fresh_disjoint_of_accumulated_frame hi hstep hwt hb hout hbyte (Or.inr hfresh)
  refine ⟨hstep.1.1.1,S,hat',Nd,htr',?_⟩
  intro i him j hjm
  simp only [List.mem_singleton] at him
  subst i
  rcases List.mem_append.mp hjm with hj|hj
  · exact hw j (worldTypedIvls_sub_worldOwned allocated S Nd j hj)
  · obtain ⟨l,hl,hjl⟩ := List.mem_flatten.mp hj
    obtain ⟨ec,hec,rfl⟩ := List.mem_map.mp hl
    exact hf ec hec j hjl

theorem precompile_sha256_allocated_avoid {F : Type}
    {s allocated : PanSemStateFiniteExact 64 F} (pad stp out : BitVec 64)
    (hi : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s allocated)
    (hm : allocated.memory = s.memory) (hb : allocated.be = s.be)
    (hfresh : Inside (out.toNat,32) (globN s "heap_ptr") (globN allocated "heap_ptr"))
    (hp : allocated.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : allocated.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hpad : pad.toNat ≠ 0) (hst : stp.toNat ≠ 0) :
    Wave8Contracts.M23.EvmAvoids
      (fun {_} _ => [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)]) allocated := by
  obtain ⟨ha,S,hat⟩ := (evmInv_iff_at s).1 hi
  obtain ⟨Nd,htr,hatn⟩ := hat.2.2.2.2.2.2.2.2.2.1
  have hout : ∀ a : BitVec 64, ¬ s.memaddrs a → allocated.memory a = s.memory a := by
    intro a _; rw [hm]
  have hbyte : ∀ b : Nat, b < 2^64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN allocated "heap_ptr") → memB allocated b = memB s b := by
    intro b _ _; unfold memB; rw [hm,hb]
  obtain ⟨hat',htr',hatn'⟩ := transfer_fixed_witness_of_accumulated_frame hi hat htr hatn hstep hb hout hbyte
  have hwt : WorldTypedWith s S Nd := ⟨hat.1.1,hat.1.2.1,hat.1.2.2.1,htr⟩
  obtain ⟨hw,hf,_⟩ := transfer_fresh_disjoint_of_accumulated_frame hi hstep hwt hb hout hbyte (Or.inr hfresh)
  have wt' : WorldTypedWith allocated S Nd := ⟨hat'.1.1,hat'.1.2.1,hat'.1.2.2.1,htr'⟩
  have hbuf : ∀ gn : String × Nat, gn ∈ globalBuffers →
      gn.1 ∉ typedRecords.map Prod.fst →
      ∀ j ∈ worldTypedIvls allocated S Nd ++ ((evmChain allocated).map (frameObjects allocated)).flatten,
      Disj (bufferRegion allocated gn) j := by
    intro gn hg hu j hj
    rcases List.mem_append.mp hj with hj|hj
    · exact bufferRegion_disj_le wt' gn hg hu gn.2 le_rfl j hj
    · obtain ⟨l,hl,hjl⟩ := List.mem_flatten.mp hj
      obtain ⟨ec,hec,rfl⟩ := List.mem_map.mp hl
      have hfix : bufferRegion allocated gn ∈ fixedObjects allocated := by
        unfold fixedObjects
        apply List.mem_append.mpr; left
        apply List.mem_append.mpr; left
        apply List.mem_append.mpr; left
        exact List.mem_map.mpr ⟨gn,hg,rfl⟩
      exact ((hat'.2.2.2.2.2.2.2.2.1 ec hec j hjl).2 _ hfix).flip
  have hp' : bufferRegion allocated ("sha_pad",128) = (pad.toNat,128) := by
    simp [bufferRegion,globN,hp,hpad]
  have hs' : bufferRegion allocated ("sha_st",64) = (stp.toNat,64) := by
    simp [bufferRegion,globN,hs,hst]
  refine ⟨hstep.1.1.1,S,hat',Nd,htr',?_⟩
  intro i him j hjm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at him
  rcases him with rfl|rfl|rfl
  · rw [←hp']; exact hbuf ("sha_pad",128) (by decide) (by decide) j hjm
  · rw [←hs']; exact hbuf ("sha_st",64) (by decide) (by decide) j hjm
  · rcases List.mem_append.mp hjm with hj|hj
    · exact hw j (worldTypedIvls_sub_worldOwned allocated S Nd j hj)
    · obtain ⟨l,hl,hjl⟩ := List.mem_flatten.mp hj
      obtain ⟨ec,hec,rfl⟩ := List.mem_map.mp hl
      exact hf ec hec j hjl

theorem precompile_output_tail_at {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (out size : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hi : EvmInv s)
    (hout : s.locals.lookup name = some (.val (.word out))) :
    let p : ProgHOL 64 := .seq
      (.store (.op .add [.var .global (ofString "ev"), .const 120]) (.var .local name))
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const 128]) (.const size))
        (.return (.const 0)))
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    R13.FlowsOrResumes (evaluateHOLFiniteState s p).1 →
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s p).2 := by
  dsimp only
  intro hnt hfr
  apply precompile_step_seq_at s _ _ _ _ hnt hfr
  · intro _ hfr
    exact precompile_store_output_local_at s 120 (Or.inl rfl) name out hi hout hfr
  · intro hflow hnt hfr
    let mid := (evaluateHOLFiniteState s (.store
      (.op .add [.var .global (ofString "ev"), .const 120]) (.var .local name))).2
    have hs := precompile_store_output_local_at s 120 (Or.inl rfl) name out hi hout (Or.inl hflow)
    have hc : mid.code = originalRuntimeCode := ((evaluateHOLFiniteState_metadata s _).1).trans hcode
    apply precompile_step_seq_at mid _ _ _ _ hnt hfr
    · exact precompile_store_output_step 128 (Or.inr rfl) (.const size)
        (by intro F s v hv; simp only [evalHOLExact, Option.some.injEq] at hv; exact ⟨size, hv.symm⟩)
        mid hc hs.1.1
    · intro hflow hnt hfr
      change (evaluateHOLFiniteState mid (.store
        (.op .add [.var .global (ofString "ev"), .const 128#64]) (.const size))).1 = none at hflow
      have ht := precompile_store_output_step 128 (Or.inr rfl) (.const size)
        (by intro F s v hv; simp only [evalHOLExact, Option.some.injEq] at hv; exact ⟨size, hv.symm⟩)
        mid hc hs.1.1 (by rw [hflow]; simp) (Or.inl hflow)
      exact dispatch_step_ro (ReadOnlyProg.ret _) _
        (((evaluateHOLFiniteState_metadata mid _).1).trans hc) ht.1.1 hnt hfr

theorem precompile_sha256_tail_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len : BitVec 64) (ptr : ExpHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hav : Wave8Contracts.M23.EvmAvoids
      (fun {_} _ => [(pad.toNat,128),(stp.toNat,64),(out.toNat,32)]) s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word len)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hbound : len.toNat+64 < 2^64) (hpad : pad.toNat+128 ≤ heapEnd)
    (hob : out.toNat+32 < 2^64) :
    let p : ProgHOL 64 := .seq
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local (ofString "out")))
        (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const 32)) (.return (.const 0))))
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    R13.FlowsOrResumes (evaluateHOLFiniteState s p).1 →
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s p).2 := by
  dsimp only
  intro hnt hfr
  have callstep : (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])).1 ≠ some .timeOut → R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])).1 →
      EvmStepCC frameStartGw s (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])).2 := by
    intro hnt hfr
    have hr : (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])).1 = none ∨
      Resumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])).1 := by
      rcases hfr with h|h|h|h
      · exact Or.inl h
      · exact absurd h (precompile_call0_ne_break s _ _)
      · exact absurd h (precompile_call0_ne_continue s _ _)
      · exact Or.inr h
    exact precompile_step_weaken (by simp)
      (precompile_sha256_call_evmStepCC s pad stp out len ptr _ _ hc hav hp hs hn ho
        hbound hpad hob hnt hr)
  apply precompile_step_seq_at s _ _ _ _ hnt hfr
  · exact callstep
  · intro hflow hnt hfr
    have hi := callstep (by rw [hflow]; simp) (Or.inl hflow)
    apply precompile_output_tail_at _ (ofString "out") out 32
      (((evaluateHOLFiniteState_metadata s _).1).trans hc) hi.1.1
      ?_ hnt hfr
    rw [precompile_call0_locals_on_flow s _ _ hflow]
    exact ho

theorem precompile_sha256_allocated_tail {F : Type}
    {s next : PanSemStateFiniteExact 64 F} (pad stp out len : BitVec 64) (ptr : ExpHOL 64)
    (hi : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s next)
    (hm : next.memory = s.memory) (hb : next.be = s.be)
    (hfresh : Inside (out.toNat,32) (globN s "heap_ptr") (globN next "heap_ptr"))
    (hc : next.code = originalRuntimeCode)
    (hp : next.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : next.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hn : next.locals.lookup (ofString "n") = some (.val (.word len)))
    (ho : next.locals.lookup (ofString "out") = some (.val (.word out)))
    (hbound : len.toNat+64 < 2^64) :
    let p : ProgHOL 64 := .seq
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local (ofString "out")))
        (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const 32)) (.return (.const 0))))
    (evaluateHOLFiniteState next p).1 ≠ some .timeOut →
    R13.FlowsOrResumes (evaluateHOLFiniteState next p).1 →
    EvmStepCC frameStartGw next (evaluateHOLFiniteState next p).2 := by
  intro p hnt hflow
  have hpad : pad.toNat ≠ 0 :=
    precompile_sha256_call_padding_nonzero next pad stp _ hstep.1.1.1.1 hp hs
      (precompile_seq_flows_left next _ _ hflow)
  have hst : stp.toNat ≠ 0 :=
    precompile_sha256_call_state_nonzero next stp _ hstep.1.1.1.1 hs
      (precompile_seq_flows_left next _ _ hflow)
  have hav := precompile_sha256_allocated_avoid pad stp out hi hstep hm hb hfresh hp hs hpad hst
  have hpb := precompile_global_buffer_bound hstep.1.1 ("sha_pad",128) (by decide) pad hp hpad (by decide)
  have hob : out.toNat+32 < 2^64 := by
    have hl := hstep.1.1.1.2.2.1
    have hc64 : heapLimit < 2^64 := by decide
    exact lt_of_le_of_lt (le_trans hfresh.2 hl) hc64
  exact precompile_sha256_tail_step next pad stp out len ptr hc hav hp hs hn ho hbound hpb hob hnt hflow

theorem precompile_sha256_alloc_tail_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len : BitVec 64) (ptr : ExpHOL 64)
    (hi : EvmInv s)
    (hhp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word out)))
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word len)))
    (hbound : len.toNat+64 < 2^64) :
    let tail : ProgHOL 64 := .seq
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local (ofString "out")))
        (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const 32)) (.return (.const 0))))
    Resumes (evaluateHOLFiniteState s (.decCall (ofString "out") .one (ofString "alloc") [.const 32] tail)).1 →
    EvmStepCC frameStartGw s
      (evaluateHOLFiniteState s (.decCall (ofString "out") .one (ofString "alloc") [.const 32] tail)).2 := by
  intro tail hr
  obtain ⟨next,ho,hh,hwords,hstep,hres,hstate,hm,hb,hl⟩ :=
    transfer_decCall_alloc_exact_spec s (ofString "out") tail out 32 (by simp) hi hhp hr
  have hpn : next.globals.lookup (ofString "sha_pad") = some (.val (.word pad)) := by
    rw [←hstep.1.2.2.1 _ (by decide)]; exact hp
  have hsn : next.globals.lookup (ofString "sha_st") = some (.val (.word stp)) := by
    rw [←hstep.1.2.2.1 _ (by decide)]; exact hs
  have hnn : next.locals.lookup (ofString "n") = some (.val (.word len)) := by
    rw [hl _ (by decide)]; exact hn
  have fresh : Inside (out.toNat,32) (globN s "heap_ptr") (globN next "heap_ptr") := by
    change globN s "heap_ptr" ≤ out.toNat ∧ out.toNat+32 ≤ globN next "heap_ptr"
    rw [hh]
    simp [globN,hhp]
  have hrn : Resumes (evaluateHOLFiniteState next tail).1 := hres ▸ hr
  have hc := precompile_sha256_allocated_tail pad stp out len ptr hi hstep hm hb fresh
    hstep.1.1.1.1.code hpn hsn hnn ho hbound
    (by intro ht; exact EvmFrameSpecs.not_resumes_timeOut (ht ▸ hrn))
    (Or.inr (Or.inr (Or.inr hrn)))
  have hs' : EvmStepCC frameStartGw s next := precompile_step_weaken
    (by intro k hk; simp only [List.map_cons,List.map_nil,List.mem_singleton] at hk
        subst k; simp [frameStartGw]) hstep
  have both : EvmStepCC frameStartGw s (evaluateHOLFiniteState next tail).2 :=
    ⟨⟨hc.1.1,le_trans hs'.1.2.1 hc.1.2.1,
      fun k hk => (hs'.1.2.2.1 k hk).trans (hc.1.2.2.1 k hk),
      hc.1.2.2.2.trans hs'.1.2.2.2⟩,
      by
        intro ec hec
        obtain ⟨a,b,c,d⟩ := hs'.2 ec hec
        obtain ⟨a',b',c',d'⟩ := hc.2 ec (hs'.1.2.2.2.symm ▸ hec)
        exact ⟨a'.trans a,b'.trans b,c'.trans c,d'.trans d⟩⟩
  change EvmStepCC frameStartGw s (evaluateHOLFiniteState s
    (.decCall (ofString "out") .one (ofString "alloc") [.const (BitVec.ofNat 64 32)] tail)).2
  rw [hstate]
  exact ⟨⟨localsFree_evmInv _ _ _ both.1.1,both.1.2.1,both.1.2.2.1,
    (evmChain_with_locals _ _ _).trans both.1.2.2.2⟩,both.2⟩

theorem precompile_sha256_gas_alloc_tail_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (len : BitVec 64) (ptr : ExpHOL 64)
    (args : List (ExpHOL 64)) (hi : EvmInv s)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word len)))
    (hbound : len.toNat+64 < 2^64) :
    let tail : ProgHOL 64 := .seq
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local (ofString "out")))
        (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const 32)) (.return (.const 0))))
    let p : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "charge_gas") args)
      (.decCall (ofString "out") .one (ofString "alloc") [.const 32] tail)
    Resumes (evaluateHOLFiniteState s p).1 →
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s p).2 := by
  intro tail p hr
  change Resumes (evaluateHOLFiniteState s (.seq _ _)).1 at hr
  change EvmStepCC frameStartGw s (evaluateHOLFiniteState s (.seq _ _)).2
  rw [evaluateHOLFiniteState_seq_line780] at hr ⊢
  rcases heval : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "charge_gas") args) with ⟨r,mid⟩
  simp only [heval] at hr ⊢
  cases r with
  | some r =>
    simp only at hr ⊢
    have hg := precompile_charge_gas_call_step args s hi.1.1.code hi
      (by rw [heval]; exact fun ht => EvmFrameSpecs.not_resumes_timeOut (ht ▸ hr))
      (by rw [heval]; exact Or.inr (Or.inr (Or.inr hr)))
    simpa only [heval] using hg
  | none =>
    simp only at hr ⊢
    have hg := precompile_charge_gas_call_step args s hi.1.1.code hi
      (by rw [heval]; simp) (by rw [heval]; exact Or.inl rfl)
    rw [heval] at hg
    have words := hg.1.1.1.2.2.2.2.2.2.2.2.2
    obtain ⟨pad,hp⟩ := words "sha_pad" (by decide)
    obtain ⟨stp,hs⟩ := words "sha_st" (by decide)
    obtain ⟨out,hh⟩ := words "heap_ptr" (by decide)
    change mid.globals.lookup (ofString "sha_pad") = some (.val (.word pad)) at hp
    change mid.globals.lookup (ofString "sha_st") = some (.val (.word stp)) at hs
    change mid.globals.lookup (ofString "heap_ptr") = some (.val (.word out)) at hh
    have hflow : (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "charge_gas") args)).1 = none := by rw [heval]
    have hlocals := precompile_call0_locals_on_flow s _ _ hflow
    rw [heval] at hlocals
    have hc := precompile_sha256_alloc_tail_step mid pad stp out len ptr hg.1.1 hh hp hs
      (by rw [hlocals]; exact hn) hbound hr
    exact ⟨⟨hc.1.1,le_trans hg.1.2.1 hc.1.2.1,
      fun k hk => (hg.1.2.2.1 k hk).trans (hc.1.2.2.1 k hk),
      hc.1.2.2.2.trans hg.1.2.2.2⟩,by
        intro ec hec
        obtain ⟨a,b,c,d⟩ := hg.2 ec hec
        obtain ⟨a',b',c',d'⟩ := hc.2 ec (hg.1.2.2.2.symm ▸ hec)
        exact ⟨a'.trans a,b'.trans b,c'.trans c,d'.trans d⟩⟩

theorem precompile_seq_call0_flows_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hc : ∀ t : PanSemStateFiniteExact 64 F,
      R13.FlowsOrResumes (evaluateHOLFiniteState t cont).1 → Resumes (evaluateHOLFiniteState t cont).1)
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s (.seq (.call (some (none,none)) fn args) cont)).1) :
    Resumes (evaluateHOLFiniteState s (.seq (.call (some (none,none)) fn args) cont)).1 := by
  rw [evaluateHOLFiniteState_seq_line780] at hr ⊢
  rcases he : evaluateHOLFiniteState s (.call (some (none,none)) fn args) with ⟨r,t⟩
  simp only [he] at hr ⊢
  cases r with
  | none => exact hc t hr
  | some r =>
    rcases hr with h|h|h|h
    · cases h
    · exact False.elim (precompile_call0_ne_break s fn args (by rw [he]; exact h))
    · exact False.elim (precompile_call0_ne_continue s fn args (by rw [he]; exact h))
    · exact h

theorem precompile_decCall_flows_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hc : ∀ t : PanSemStateFiniteExact 64 F,
      R13.FlowsOrResumes (evaluateHOLFiniteState t cont).1 → Resumes (evaluateHOLFiniteState t cont).1)
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s (.decCall name shape fn args cont)).1) :
    Resumes (evaluateHOLFiniteState s (.decCall name shape fn args cont)).1 := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr ⊢
  have bad : ¬ R13.FlowsOrResumes (some (.error : PanSemResultExact 64)) := by
    rintro (h|h|h|⟨⟨_,h⟩|⟨_,_,h,_⟩⟩) <;> cases h
  cases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => simp only [ha] at hr; exact False.elim (bad hr)
  | some vals =>
    simp only [ha] at hr ⊢
    cases hl : lookupCodeHOLFinite s.code.lookup fn vals with
    | none => simp only [hl] at hr; exact False.elim (bad hr)
    | some entry =>
      obtain ⟨body,locals,ret⟩ := entry
      simp only [hl] at hr ⊢
      by_cases hz : s.clock = 0
      · simp only [hz,↓reduceIte] at hr
        rcases hr with h|h|h|⟨⟨_,h⟩|⟨_,_,h,_⟩⟩ <;> cases h
      · simp only [hz,↓reduceIte] at hr ⊢
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s locals) body with ⟨r,post⟩
        simp only [hb] at hr ⊢
        cases r with
        | none => exact False.elim (bad hr)
        | some r =>
          cases r with
          | error | «break» | «continue» => exact False.elim (bad hr)
          | returned v =>
            dsimp only at hr ⊢
            split
            · rename_i hsh
              simp only [hsh,↓reduceIte] at hr
              exact hc _ hr
            · rename_i hsh
              simp only [hsh] at hr
              exact False.elim (bad hr)
          | exception e v =>
            rcases hr with h|h|h|h
            · cases h
            · cases h
            · cases h
            · exact h
          | timeOut | finalFfi _ =>
            rcases hr with h|h|h|⟨⟨_,h⟩|⟨_,_,h,_⟩⟩ <;> cases h

theorem precompile_seq_store_flows_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addr val : ExpHOL 64) (cont : ProgHOL 64)
    (hc : ∀ t : PanSemStateFiniteExact 64 F,
      R13.FlowsOrResumes (evaluateHOLFiniteState t cont).1 → Resumes (evaluateHOLFiniteState t cont).1)
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s (.seq (.store addr val) cont)).1) :
    Resumes (evaluateHOLFiniteState s (.seq (.store addr val) cont)).1 := by
  have bad : ¬ R13.FlowsOrResumes (some (.error : PanSemResultExact 64)) := by
    rintro (h|h|h|⟨⟨_,h⟩|⟨_,_,h,_⟩⟩) <;> cases h
  have hs : (evaluateHOLFiniteState s (.store addr val)).1 = none ∨
      (evaluateHOLFiniteState s (.store addr val)).1 = some .error := by
    rw [evaluateHOLFiniteState_store]
    split <;> (try split) <;> (try split) <;> simp
  rw [evaluateHOLFiniteState_seq_line780] at hr ⊢
  rcases he : evaluateHOLFiniteState s (.store addr val) with ⟨r,t⟩
  simp only [he] at hs hr ⊢
  rcases hs with rfl|rfl
  · exact hc t hr
  · exact False.elim (bad hr)

theorem precompile_return_flows_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (val : ExpHOL 64)
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s (.return val)).1) :
    Resumes (evaluateHOLFiniteState s (.return val)).1 := by
  rw [evaluateHOLFiniteState_return] at hr ⊢
  cases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with
  | none =>
    simp only [hv] at hr
    rcases hr with h|h|h|⟨⟨_,h⟩|⟨_,_,h,_⟩⟩ <;> cases h
  | some v =>
    simp only [hv] at hr ⊢
    split
    · exact Or.inl ⟨v,rfl⟩
    · rename_i hsz
      simp only [hsz,↓reduceIte] at hr
      rcases hr with h|h|h|⟨⟨_,h⟩|⟨_,_,h,_⟩⟩ <;> cases h

theorem precompile_sha256_words_gas_tail_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (len : BitVec 64) (ptr : ExpHOL 64)
    (hi : EvmInv s)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word len)))
    (hbound : len.toNat+64 < 2^64) :
    let tail : ProgHOL 64 := .seq
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local (ofString "out")))
        (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const 32)) (.return (.const 0))))
    let gas : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "charge_gas")
      [.op .add [.const 60,.panop .mul [.const 12,.var .local (ofString "w")]]])
      (.decCall (ofString "out") .one (ofString "alloc") [.const 32] tail)
    let p : ProgHOL 64 := .decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "n")] gas
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    R13.FlowsOrResumes (evaluateHOLFiniteState s p).1 →
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s p).2 := by
  intro tail gas p hnt hfr
  apply precompile_step_decCall_ro_at precompile_ro_words_of _ _ _ _ s hi.1.1.code hi ?_ hnt hfr
  intro v k mid hnt hfr
  have hinv := localsFree_evmInv s (setVarHOLFinite (ofString "w") v s).locals k hi
  apply precompile_sha256_gas_alloc_tail_step _ len ptr _ hinv ?_ hbound ?_
  · change (setVarHOLFinite (ofString "w") v s).locals.lookup (ofString "n") = _
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hn,show ofString "w" ≠ ofString "n" by decide]
  · exact precompile_seq_call0_flows_resumes mid _ _ _ (fun t ht =>
      precompile_decCall_flows_resumes t _ _ _ _ _ (fun t ht =>
        precompile_seq_call0_flows_resumes t _ _ _ (fun t ht =>
          precompile_seq_store_flows_resumes t _ _ _ (fun t ht =>
            precompile_seq_store_flows_resumes t _ _ _ (fun t ht =>
              precompile_return_flows_resumes t _ ht) ht) ht) ht) ht) hfr

theorem precompile_step_dec_at {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) (body : ProgHOL 64)
    (hb : ∀ v, @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) init = some v →
      shapeEqHOL shape (shapeOfHOLExact v) = true →
      (evaluateHOLFiniteState (setVarHOLFinite name v s) body).1 ≠ some .timeOut →
      R13.FlowsOrResumes (evaluateHOLFiniteState (setVarHOLFinite name v s) body).1 →
      EvmStepCC frameStartGw (setVarHOLFinite name v s)
        (evaluateHOLFiniteState (setVarHOLFinite name v s) body).2)
    (hnt : (evaluateHOLFiniteState s (.dec name shape init body)).1 ≠ some .timeOut)
    (hfr : R13.FlowsOrResumes (evaluateHOLFiniteState s (.dec name shape init body)).1) :
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s (.dec name shape init body)).2 := by
  have bad : ¬ R13.FlowsOrResumes (some (.error : PanSemResultExact 64)) := by
    rintro (h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩) <;> cases h
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · exact absurd hfr bad
  · rename_i v hv
    by_cases hsh : shapeEqHOL shape (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
      have hh := hb v hv hsh hnt hfr
      have hset : setVarHOLFinite name v s =
          {s with locals := (setVarHOLFinite name v s).locals, clock := s.clock} := by cases s; rfl
      rw [hset] at hh
      exact precompile_step_locals_right _ _ (precompile_step_locals_left _ _ hh)
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
      exact absurd hfr bad

theorem precompile_dec_flows_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) (body : ProgHOL 64)
    (hc : ∀ t : PanSemStateFiniteExact 64 F,
      R13.FlowsOrResumes (evaluateHOLFiniteState t body).1 → Resumes (evaluateHOLFiniteState t body).1)
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s (.dec name shape init body)).1) :
    Resumes (evaluateHOLFiniteState s (.dec name shape init body)).1 := by
  have bad : ¬ R13.FlowsOrResumes (some (.error : PanSemResultExact 64)) := by
    rintro (h|h|h|⟨⟨_,h⟩|⟨_,_,h,_⟩⟩) <;> cases h
  rw [evaluateHOLFiniteState_dec_total] at hr ⊢
  dsimp only at hr ⊢
  revert hr
  split
  · intro hr; exact False.elim (bad hr)
  · split
    · intro hr; exact hc _ hr
    · intro hr; exact False.elim (bad hr)

/-! ## SHA-256 callee lookups and no-catchable-raise clearance -/

private theorem lookup_sha256_state_init_local :
    originalRuntimeCode.lookup (ofString "sha256_state_init") =
      some ([(ofString "stp", .one)],
        sourceFnBody Guest.Software.guestFn_sha256_state_init, .one) :=
  lookup_of_guestAst_getElem 92 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sha256_state_init) rfl

private theorem lookup_sha256_block_local :
    originalRuntimeCode.lookup (ofString "sha256_block") =
      some ([(ofString "stp", .one), (ofString "blk", .one)],
        sourceFnBody Guest.Software.guestFn_sha256_block, .one) :=
  lookup_of_guestAst_getElem 93 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sha256_block) rfl

private theorem lookup_sha256_finish_local :
    originalRuntimeCode.lookup (ofString "sha256_finish") =
      some ([(ofString "stp", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_sha256_finish, .one) :=
  lookup_of_guestAst_getElem 94 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sha256_finish) rfl

private theorem lookup_sha256_local :
    originalRuntimeCode.lookup (ofString "sha256") =
      some ([(ofString "p", .one), (ofString "len", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_sha256, .one) :=
  lookup_of_guestAst_getElem 95 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sha256) rfl

private def shaNcrCallees (f : MlS) : Bool :=
  f == ofString "trap_with" || f == ofString "alloc" || f == ofString "memcpy" ||
  f == ofString "memzero" || f == ofString "bswap64" || f == ofString "st_be32" ||
  f == ofString "st_be64" || f == ofString "sha256" ||
  f == ofString "sha256_state_init" || f == ofString "sha256_block" ||
  f == ofString "sha256_finish"

open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
  (noCatchableRaise evaluate_noCatchableRaise)

private theorem shaNcrCallees_good :
    ∀ f, shaNcrCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise shaNcrCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
  simp only [shaNcrCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · rw [lookup_trap_with_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [R13Shards.lookup_alloc_r13] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [EvmFrameSpecs.lookup_memcpy] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_memzero_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [EvmFrameSpecs.lookup_bswap64] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [EvmFrameSpecs.lookup_st_be32] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [EvmFrameSpecs.lookup_st_be64] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_sha256_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_sha256_state_init_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_sha256_block_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_sha256_finish_local] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

private theorem sha_ncr_sha256_body :
    noCatchableRaise shaNcrCallees (sourceFnBody Guest.Software.guestFn_sha256) = true :=
  rfl

/-- A zero-argument-result (`some (none, none)`) call never produces a plain
`returned` result: the callee's shape-checked return maps the call to a flow
(`none`), and every other callee outcome maps to a non-`returned` result. -/
theorem precompile_call0_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s
      (.call (some (none, none)) fn args : ProgHOL 64)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) args with _ | vals
  · simp
  · dsimp only
    rcases hlook : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn vals with _ | ⟨body, callee, ret⟩
    · simp
    · dsimp only
      by_cases hz : s.clock = 0
      · rw [if_pos hz]; simp
      · rw [if_neg hz]
        split
        · simp
        · simp
        · simp
        · split <;> simp
        · simp
        · intro h; simp_all

/-! ## SHA-256 blocks-loop exit bound (mod-64 index invariant) -/

private theorem precompile_sha256_blocks_body_i_wrap {F : Type} (s : PanSemStateFiniteExact 64 F)
    (i : BitVec 64) (hx : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hflow : (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 64])))).1 = none) :
    (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 64])))).2.locals.lookup (ofString "i")
      = some (.val (.word (i + 64))) := by
  rw [evaluateHOLFiniteState_seq_line780] at hflow ⊢
  rcases run : evaluateHOLFiniteState s
    (.call (some (none, none)) (ofString "sha256_block")
      [.var .global (ofString "sha_st"),
        .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]) with ⟨r, m⟩
  rw [run] at hflow
  cases r with
  | none =>
    dsimp only
    have hl := precompile_call0_locals_on_flow s (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]] (by rw [run])
    rw [run] at hl
    have hl' : m.locals.lookup (ofString "i") = some (.val (.word i)) :=
      hl.symm ▸ hx
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hl', valueIsWord, valueWord,
      wordOpHOL, wordOp, isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL,
      setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | some r => simp [run] at hflow

private theorem precompile_sha256_blocks_body_i_wrap_mod {F : Type} (s : PanSemStateFiniteExact 64 F)
    (i : BitVec 64) (hx : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hi0 : i.toNat % 64 = 0)
    (hflow : (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 64])))).1 = none) :
    ∃ j : BitVec 64,
      (evaluateHOLFiniteState s
        (.seq (.call (some (none, none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 64])))).2.locals.lookup (ofString "i")
        = some (.val (.word j)) ∧ j.toNat % 64 = 0 := by
  refine ⟨i + 64, precompile_sha256_blocks_body_i_wrap s i hx hflow, ?_⟩
  have hdvd : (64 : Nat) ∣ 2^64 := ⟨2^58, by ring⟩
  have hadd : (i + 64).toNat = (i.toNat + 64) % 2^64 := by
    rw [BitVec.toNat_add]
    simp [BitVec.toNat_ofNat]
  rw [hadd, Nat.mod_mod_of_dvd (i.toNat + 64) hdvd, Nat.add_mod_right]
  exact hi0

private theorem precompile_sha256_blocks_exit_len_lt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (len : BitVec 64)
    (hP : s.locals.lookup (ofString "len") = some (.val (.word len)) ∧
      ∃ j : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word j)) ∧
        j.toNat % 64 = 0)
    (hr : (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"), .const 64]))
        (.seq (.call (some (none, none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 64]))))).1 = none) :
    len.toNat < 2^64 - 64 := by
  let P : PanSemStateFiniteExact 64 F → Prop := fun t =>
    t.locals.lookup (ofString "len") = some (.val (.word len)) ∧
    ∃ j : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word j)) ∧ j.toNat % 64 = 0
  have he := precompile_while_normal_exit P _ _ (fun t ht => ht) ?_ s hP hr
  · generalize hpost : (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "len"))
          (.op .add [.var .local (ofString "i"), .const 64]))
        (.seq (.call (some (none, none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 64]))))).2 = wp at he
    obtain ⟨⟨hlp, j, hj, hj0⟩, hguard⟩ := he
    have hdvd : (64 : Nat) ∣ 2^64 := ⟨2^58, by ring⟩
    have hmod : (j.toNat + 64) % 2^64 ≤ 2^64 - 64 := by
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hj0
      rw [hk, show (2^64 : Nat) = 64 * 2^58 from by ring,
        show (64 : Nat) * k + 64 = 64 * (k + 1) from by ring, Nat.mul_mod_mul_left]
      have h1 : (k + 1) % 2^58 < 2^58 := Nat.mod_lt _ (by norm_num)
      omega
    simp [evalListHOLExact, evalHOLExact, hlp, hj, valueIsWord, valueWord,
      wordOpHOL, wordOp, Compiler.Encoders.Asm.wordCmpHOL] at hguard
    have hlt : len.toNat < (j + (64 : BitVec 64)).toNat := BitVec.lt_def.mp hguard
    rw [show (j + (64 : BitVec 64)).toNat = (j.toNat + 64) % 2^64 from by
      rw [BitVec.toNat_add]; simp [BitVec.toNat_ofNat]] at hlt
    omega
  · intro t ht ha
    obtain ⟨hlt, j, hj, hj0⟩ := ht
    refine ⟨(precompile_sha256_blocks_body_control t).1, ?_⟩
    rintro (hflow | hflow)
    · refine ⟨(precompile_sha256_blocks_body_local t (ofString "len") (by decide) hflow).trans hlt, ?_⟩
      exact precompile_sha256_blocks_body_i_wrap_mod t j hj hj0 hflow
    · exact absurd hflow ((precompile_sha256_blocks_body_control t).2)

theorem precompile_sha256_tail_not_resumes_st0 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len d : BitVec 64) (ptr : ExpHOL 64)
    (hi : GuestInv s)
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word 0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word len)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hd : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) ptr =
      some (.val (.word d))) :
    let tail : ProgHOL 64 := .seq
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local (ofString "out")))
        (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const 32)) (.return (.const 0))))
    ¬ Resumes (evaluateHOLFiniteState s tail).1 := by
  intro tail hr
  change Resumes (evaluateHOLFiniteState s (.seq _ _)).1 at hr
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rw [evaluateHOLFiniteState_call] at hr
  have hd' : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) ptr =
      some (.val (.word d)) := hd
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [ptr, .var .local (ofString "n"), .var .local (ofString "out")] =
      some [.val (.word d), .val (.word len), .val (.word out)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hd', hn, ho]
  rw [hargs] at hr
  dsimp only at hr
  rcases hlook : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup
      (ofString "sha256") [.val (.word d), .val (.word len), .val (.word out)] with _ | ⟨body, callee, ret⟩
  · rw [hlook] at hr; simp [Resumes] at hr
  · rw [hlook] at hr
    dsimp only at hr
    have heqb := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ ret _ callee
      (by rw [hi.code]; exact lookup_sha256_local) hlook
    subst heqb
    have heqr := lookupCodeHOLFinite_installed_return s _ _ _ _ .one ret _ callee
      (by rw [hi.code]; exact lookup_sha256_local) hlook
    subst heqr
    by_cases hz : s.clock = 0
    · rw [if_pos hz] at hr; simp [Resumes] at hr
    · rw [if_neg hz] at hr
      dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_sha256,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural] at hr
      rw [evaluateHOLFiniteState_seq_line780] at hr
      rw [evaluateHOLFiniteState_call] at hr
      have hargs1 : evalListHOLFinite (callEntryStateHOLFinite s callee)
          (h := fun a => Classical.propDecidable ((callEntryStateHOLFinite s callee).memaddrs a))
          [.var .global (ofString "sha_st")] = some [.val (.word 0)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLFinite, evalHOLExact,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          hs, callEntryStateHOLFinite]
      simp only [List.map_cons, List.map_nil,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural] at hr
      rw [hargs1] at hr
      dsimp only at hr
      rcases hlook1 : PanSemStateFiniteExact.lookupCodeHOLFinite
          (callEntryStateHOLFinite s callee).code.lookup
          (ofString "sha256_state_init") [.val (.word 0)] with _ | ⟨body1, callee1, ret1⟩
      · rw [hlook1] at hr; simp [Resumes] at hr
      · rw [hlook1] at hr
        dsimp only at hr
        have hcode1 : (callEntryStateHOLFinite s callee).code = s.code := by
          cases s; rfl
        have heqb1 := lookupCodeHOLFinite_installed_body
            (callEntryStateHOLFinite s callee).code.lookup _ _ _ body1 _ ret1 _ callee1
          (by rw [hcode1, hi.code]; exact lookup_sha256_state_init_local) hlook1
        subst heqb1
        have heqr1 := lookupCodeHOLFinite_installed_return
            (callEntryStateHOLFinite s callee) _ _ _ _ .one ret1 _ callee1
          (by rw [hcode1, hi.code]; exact lookup_sha256_state_init_local) hlook1
        subst heqr1
        by_cases hz1 : (callEntryStateHOLFinite s callee).clock = 0
        · rw [if_pos hz1] at hr; simp [Resumes] at hr
        · rw [if_neg hz1] at hr
          obtain ⟨p, hvals, hpe⟩ := R10Shards.P26_P28.lookupCode_one_word
            lookup_sha256_state_init_local
            (by rw [← hi.code]; exact hlook1)
          have hp0 : p = 0 := by simpa using hvals.symm
          subst hp0
          rw [precompile_sha256_state_init_null
            (callEntryStateHOLFinite (callEntryStateHOLFinite s callee) callee1)
            (guestInv_callEntry (callEntryStateHOLFinite s callee) callee1
              (guestInv_callEntry s callee hi)) hpe] at hr
          simp [Resumes] at hr

theorem pre_sha256_body_flows_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hr : R13.FlowsOrResumes
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_pre_sha256)).1) :
    Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_pre_sha256)).1 := by
  dsimp only [sourceFnBody,sourceFunctionEntry,Guest.Software.guestFn_pre_sha256,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural] at hr ⊢
  exact precompile_dec_flows_resumes s _ _ _ _ (fun t ht =>
    precompile_dec_flows_resumes t _ _ _ _ (fun t ht =>
      precompile_decCall_flows_resumes t _ _ _ _ _ (fun t ht =>
        precompile_seq_call0_flows_resumes t _ _ _ (fun t ht =>
          precompile_decCall_flows_resumes t _ _ _ _ _ (fun t ht =>
            precompile_seq_call0_flows_resumes t _ _ _ (fun t ht =>
              precompile_seq_store_flows_resumes t _ _ _ (fun t ht =>
                precompile_seq_store_flows_resumes t _ _ _ (fun t ht =>
                  precompile_return_flows_resumes t _ ht) ht) ht) ht) ht) ht) ht) ht) hr

theorem precompile_while_invariant_no_normal_exit {F : Type}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (hguard : ∀ t, P t → @evalHOLFinite 64 F _ t
      (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 1)))
    (hdec : ∀ t, P t → P (decClockHOLFinite t))
    (hbody : ∀ t, P t →
      (evaluateHOLFiniteState t body).1 ≠ some .break ∧
      ((evaluateHOLFiniteState t body).1 = none ∨
        (evaluateHOLFiniteState t body).1 = some .continue →
        P (evaluateHOLFiniteState t body).2))
    (s : PanSemStateFiniteExact 64 F) (hs : P s) :
    (evaluateHOLFiniteState s (.while cond body)).1 ≠ none := by
  rw [evaluateHOLFiniteState_while_total]
  rw [hguard s hs]
  dsimp only
  split <;> try (rename_i h; exact False.elim (h (by decide)))
  split
  · simp
  · rw [fixClockHOLFinite_evaluateState]
    have hb := hbody (decClockHOLFinite s) (hdec s hs)
    have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
    rcases run : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r,m⟩
    rw [run] at hb hle
    have hlt : m.clock < s.clock := by
      change m.clock ≤ s.clock - 1 at hle
      omega
    cases r with
    | none =>
      exact precompile_while_invariant_no_normal_exit cond body P hguard hdec hbody m
        (hb.2 (Or.inl rfl))
    | some r =>
      cases r with
      | «continue» =>
        exact precompile_while_invariant_no_normal_exit cond body P hguard hdec hbody m
          (hb.2 (Or.inr rfl))
      | «break» => exact False.elim (hb.1 rfl)
      | _ => simp
termination_by s.clock

theorem precompile_sha256_block_index_add_bound (i : BitVec 64)
    (halign : i.toNat % 64 = 0) :
    (i + 64).toNat % 64 = 0 ∧ (i + 64).toNat ≤ 2^64 - 64 := by
  have hi := i.isLt
  have hadd : (i + 64).toNat = (i.toNat + 64) % 2^64 := by
    simp [BitVec.toNat_add]
  rw [hadd]
  constructor <;> omega

theorem precompile_sha256_block_guard_of_large_length (i len : BitVec 64)
    (halign : i.toNat % 64 = 0) (hlen : ¬ len.toNat + 64 < 2^64) :
    (i + 64).toNat ≤ len.toNat := by
  have hb := (precompile_sha256_block_index_add_bound i halign).2
  omega

theorem precompile_sha256_block_guard_true {F : Type}
    (s : PanSemStateFiniteExact 64 F) (i len : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (halign : i.toNat % 64 = 0) (hlen : ¬ len.toNat + 64 < 2^64) :
    @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"),.const 64])) = some (.val (.word 1)) := by
  have hb := precompile_sha256_block_guard_of_large_length i len halign hlen
  simp [BitVec.toNat_add] at hb
  simpa [evalHOLFinite,evalHOLExact,evalListHOLExact,hi,hl,Compiler.Encoders.Asm.wordCmpHOL,
    wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.le_def,hb]
    using hb

theorem precompile_call0_no_loop_control {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (none,none)) fn args)).1 ≠ some .break ∧
    (evaluateHOLFiniteState s (.call (some (none,none)) fn args)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · dsimp only
    split
    · simp
    · split
      · simp
      · split <;> try simp_all
        split <;> simp_all

theorem precompile_sha256_blocks_body_locals_on_flow {F : Type}
    (s : PanSemStateFiniteExact 64 F) (i len : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hr : (evaluateHOLFiniteState s
      (.seq (.call (some (none,none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"),.var .local (ofString "i")]])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"),.const 64])))).1 = none) :
    let post := (evaluateHOLFiniteState s
      (.seq (.call (some (none,none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"),.var .local (ofString "i")]])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"),.const 64])))).2
    post.locals.lookup (ofString "i") = some (.val (.word (i+64))) ∧
      post.locals.lookup (ofString "len") = some (.val (.word len)) := by
  rw [evaluateHOLFiniteState_seq_line780] at hr ⊢
  dsimp only at hr ⊢
  rcases run : evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256_block")
        [.var .global (ofString "sha_st"),
          .op .add [.var .local (ofString "p"),.var .local (ofString "i")]]) with ⟨r,m⟩
  cases r with
  | some r => simp [run] at hr
  | none =>
    have hm := precompile_call0_locals_on_flow s _ _ (by rw [run])
    rw [run] at hm
    dsimp only at hm hr ⊢
    rw [evaluateHOLFiniteState_assign]
    have hne : ofString "i" ≠ ofString "len" := by decide
    simp [evalHOLFinite,evalHOLExact,evalListHOLExact,hm,hi,hl,
      wordOpHOL,wordOp,valueIsWord,valueWord,isValidValueHOLExact,
      lookupKvarHOLExact,shapeEqHOL,shapeOfHOLExact,
      setKvarHOLFinite,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,hne]

theorem precompile_seq_call0_assign_no_loop_control {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64))
    (name : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.seq (.call (some (none,none)) fn args)
      (.assign .local name e))).1 ≠ some .break ∧
    (evaluateHOLFiniteState s (.seq (.call (some (none,none)) fn args)
      (.assign .local name e))).1 ≠ some .continue := by
  have hc := precompile_call0_no_loop_control s fn args
  rw [evaluateHOLFiniteState_seq_line780]
  rcases run : evaluateHOLFiniteState s (.call (some (none,none)) fn args) with ⟨r,m⟩
  cases r with
  | some r => simpa only [run] using hc
  | none =>
    dsimp only
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp

theorem precompile_sha256_blocks_large_no_normal_exit {F : Type}
    (s : PanSemStateFiniteExact 64 F) (i len : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (halign : i.toNat % 64 = 0) (hlen : ¬ len.toNat + 64 < 2^64) :
    (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"),.const 64]))
        (.seq (.call (some (none,none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .local (ofString "p"),.var .local (ofString "i")]])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"),.const 64]))))).1 ≠ none := by
  let P := fun t : PanSemStateFiniteExact 64 F =>
    t.locals.lookup (ofString "len") = some (.val (.word len)) ∧
    ∃ j : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word j)) ∧
      j.toNat % 64 = 0
  apply precompile_while_invariant_no_normal_exit _ _ P ?_ ?_ ?_ s ⟨hl,i,hi,halign⟩
  · intro t ht
    obtain ⟨hlt,j,hj,hja⟩ := ht
    exact precompile_sha256_block_guard_true t j len hj hlt hja hlen
  · intro t ht; exact ht
  · intro t ht
    have hc := precompile_seq_call0_assign_no_loop_control t (ofString "sha256_block")
      [.var .global (ofString "sha_st"),
        .op .add [.var .local (ofString "p"),.var .local (ofString "i")]]
      (ofString "i") (.op .add [.var .local (ofString "i"),.const 64])
    refine ⟨hc.1,?_⟩
    intro hr
    rcases hr with hr | hr
    · obtain ⟨hlt,j,hj,hja⟩ := ht
      have he := precompile_sha256_blocks_body_locals_on_flow t j len hj hlt hr
      exact ⟨he.2,j+64,he.1,(precompile_sha256_block_index_add_bound j hja).1⟩
    · exact False.elim (hc.2 hr)

theorem precompile_sha256_blocks_input_bound_of_normal_exit {F : Type}
    (s : PanSemStateFiniteExact 64 F) (i len : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (halign : i.toNat % 64 = 0)
    (hr : (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"),.const 64]))
        (.seq (.call (some (none,none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .local (ofString "p"),.var .local (ofString "i")]])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"),.const 64]))))).1 = none) :
    len.toNat + 64 < 2^64 := by
  by_contra hlen
  exact precompile_sha256_blocks_large_no_normal_exit s i len hi hl halign hlen hr

theorem precompile_sha256_blocks_input_bound_of_flow {F : Type}
    (s : PanSemStateFiniteExact 64 F) (i len : BitVec 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (halign : i.toNat % 64 = 0)
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.seq (.while (.cmp .notLower (.var .local (ofString "len"))
        (.op .add [.var .local (ofString "i"),.const 64]))
        (.seq (.call (some (none,none)) (ofString "sha256_block")
          [.var .global (ofString "sha_st"),
            .op .add [.var .local (ofString "p"),.var .local (ofString "i")]])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"),.const 64])))) cont)).1) :
    len.toNat + 64 < 2^64 := by
  rcases precompile_seq_flow_cases s _ _ hr with h | h
  · exact precompile_sha256_blocks_input_bound_of_normal_exit s i len hi hl halign h.1
  · rcases h with h | h | h
    · exact False.elim ((precompile_while_no_loop_control s _ _).1 h)
    · exact False.elim ((precompile_while_no_loop_control s _ _).2 h)
    · exact False.elim (precompile_while_not_resumes_code _ _
        (fun t ht => precompile_sha256_blocks_body_not_resumes t ht) s hc h)

theorem precompile_sha256_body_input_bound {F : Type}
    (s : PanSemStateFiniteExact 64 F) (len : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hr : R13.FlowsOrResumes
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sha256)).1) :
    len.toNat + 64 < 2^64 := by
  change R13.FlowsOrResumes (evaluateHOLFiniteState s (.seq
    (.call (some (none,none)) (ofString "sha256_state_init")
      [.var .global (ofString "sha_st")]) _)).1 at hr
  rcases precompile_seq_flow_cases s _ _ hr with ⟨hn,hflow⟩ | hctrl
  · have hm := precompile_call0_locals_on_flow s _ _ hn
    have hmeta := (evaluateHOLFiniteState_metadata s
      (.call (some (none,none)) (ofString "sha256_state_init")
        [.var .global (ofString "sha_st")])).1
    change R13.FlowsOrResumes (evaluateHOLFiniteState _ (.dec (ofString "i") .one (.const 0) _)).1 at hflow
    rw [evaluateHOLFiniteState_dec_total] at hflow
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,Bool.true_eq,ite_true] at hflow
    let m := setVarHOLFinite (ofString "i") (.val (.word 0))
      (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "sha256_state_init")
        [.var .global (ofString "sha_st")])).2
    have hmc : m.code = originalRuntimeCode := hmeta.trans hc
    apply precompile_sha256_blocks_input_bound_of_flow m 0 len _ hmc ?_ ?_ (by decide) hflow
    · simp [m,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · have hne : ofString "i" ≠ ofString "len" := by decide
      simpa [m,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hne,hm] using hl
  · rcases hctrl with h | h | h
    · exact False.elim ((precompile_call0_no_loop_control s _ _).1 h)
    · exact False.elim ((precompile_call0_no_loop_control s _ _).2 h)
    · exact False.elim (precompile_sha256_init_call_not_resumes s _ hc h)

theorem precompile_sha256_call_input_bound {F : Type}
    (s : PanSemStateFiniteExact 64 F) (len : BitVec 64)
    (ptr count dest : ExpHOL 64) (hc : s.code = originalRuntimeCode)
    (hlength : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) count =
      some (.val (.word len)))
    (hr : R13.FlowsOrResumes (evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "sha256") [ptr,count,dest])).1) :
    len.toNat + 64 < 2^64 := by
  have hl : originalRuntimeCode.lookup (ofString "sha256") =
      some ([(ofString "p",.one),(ofString "len",.one),(ofString "out",.one)],
        sourceFnBody Guest.Software.guestFn_sha256,.one) :=
    lookup_of_guestAst_getElem 95 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256) rfl
  rw [evaluateHOLFiniteState_call] at hr
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [ptr,count,dest] with _ | vals
  · rw [ha] at hr
    simp [R13.FlowsOrResumes,Resumes] at hr
  · rw [ha] at hr
    dsimp only at hr
    rcases hlook : lookupCodeHOLFinite s.code.lookup (ofString "sha256") vals with _ | ⟨body,callee,ret⟩
    · simp [hlook,R13.FlowsOrResumes,Resumes] at hr
    · rw [hlook] at hr
      dsimp only at hr
      have heq := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ ret _ callee
        (by rw [hc]; exact hl) hlook
      subst heq
      have hret := lookupCodeHOLFinite_installed_return s _ _ _ _ .one ret _ callee
        (by rw [hc]; exact hl) hlook
      subst hret
      obtain ⟨p,n,o,hvals,hpl,hnl,hol⟩ := R10Shards.P26_P28.lookupCode_three_words
        (by decide) (by decide) (by decide) hl (by simpa only [hc] using hlook)
      have he : n = len := by
        rw [hvals] at ha
        change @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a)) count = some (.val (.word len)) at hlength
        cases hpv : @evalHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a)) ptr <;>
          cases hov : @evalHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a)) dest <;>
          simp [evalListHOLFinite,evalListHOLExact,hlength,hpv,hov] at ha
        exact ha.2.1.symm
      subst n
      by_cases hz : s.clock = 0
      · simp [hz,R13.FlowsOrResumes,Resumes] at hr
      · rw [if_neg hz] at hr
        have hbody : R13.FlowsOrResumes (evaluateHOLFiniteState
            (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_sha256)).1 := by
          rcases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
              (sourceFnBody Guest.Software.guestFn_sha256) with ⟨r,post⟩
          cases r with
          | none => exact Or.inl rfl
          | some r => cases r <;> simp_all [R13.FlowsOrResumes,Resumes]
        exact precompile_sha256_body_input_bound (callEntryStateHOLFinite s callee) len hc hnl hbody

theorem precompile_sha256_allocated_tail_unconditional {F : Type}
    {s next : PanSemStateFiniteExact 64 F} (pad stp out len : BitVec 64) (ptr : ExpHOL 64)
    (hi : EvmInv s) (hstep : EvmStepCC ["heap_ptr"] s next)
    (hm : next.memory = s.memory) (hb : next.be = s.be)
    (hfresh : Inside (out.toNat,32) (globN s "heap_ptr") (globN next "heap_ptr"))
    (hc : next.code = originalRuntimeCode)
    (hp : next.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : next.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hn : next.locals.lookup (ofString "n") = some (.val (.word len)))
    (ho : next.locals.lookup (ofString "out") = some (.val (.word out))) :
    let p : ProgHOL 64 := .seq
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local (ofString "out")))
        (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const 32)) (.return (.const 0))))
    (evaluateHOLFiniteState next p).1 ≠ some .timeOut →
    R13.FlowsOrResumes (evaluateHOLFiniteState next p).1 →
    EvmStepCC frameStartGw next (evaluateHOLFiniteState next p).2 := by
  intro p hnt hflow
  have hbound := precompile_sha256_call_input_bound next len ptr
    (.var .local (ofString "n")) (.var .local (ofString "out")) hc
    (by simp [evalHOLFinite,evalHOLExact,hn])
    (precompile_seq_flows_left next _ _ hflow)
  exact precompile_sha256_allocated_tail pad stp out len ptr hi hstep hm hb hfresh hc
    hp hs hn ho hbound hnt hflow

theorem precompile_sha256_alloc_tail_step_unconditional {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pad stp out len : BitVec 64) (ptr : ExpHOL 64)
    (hi : EvmInv s)
    (hhp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word out)))
    (hp : s.globals.lookup (ofString "sha_pad") = some (.val (.word pad)))
    (hs : s.globals.lookup (ofString "sha_st") = some (.val (.word stp)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word len))) :
    let tail : ProgHOL 64 := .seq
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local (ofString "out")))
        (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const 32)) (.return (.const 0))))
    Resumes (evaluateHOLFiniteState s (.decCall (ofString "out") .one (ofString "alloc") [.const 32] tail)).1 →
    EvmStepCC frameStartGw s
      (evaluateHOLFiniteState s (.decCall (ofString "out") .one (ofString "alloc") [.const 32] tail)).2 := by
  intro tail hr
  obtain ⟨next,ho,hh,hwords,hstep,hres,hstate,hm,hb,hl⟩ :=
    transfer_decCall_alloc_exact_spec s (ofString "out") tail out 32 (by simp) hi hhp hr
  have hnn : next.locals.lookup (ofString "n") = some (.val (.word len)) := by
    rw [hl _ (by decide)]; exact hn
  have hrn : Resumes (evaluateHOLFiniteState next tail).1 := hres ▸ hr
  have hbound := precompile_sha256_call_input_bound next len ptr
    (.var .local (ofString "n")) (.var .local (ofString "out")) hstep.1.1.1.1.code
    (by simp [evalHOLFinite,evalHOLExact,hnn])
    (precompile_seq_flows_left next _ _ (Or.inr (Or.inr (Or.inr hrn))))
  exact precompile_sha256_alloc_tail_step s pad stp out len ptr hi hhp hp hs hn hbound hr

theorem precompile_sha256_gas_alloc_tail_step_unconditional {F : Type}
    (s : PanSemStateFiniteExact 64 F) (len : BitVec 64) (ptr : ExpHOL 64)
    (args : List (ExpHOL 64)) (hi : EvmInv s)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word len))) :
    let tail : ProgHOL 64 := .seq
      (.call (some (none,none)) (ofString "sha256") [ptr,.var .local (ofString "n"),.var .local (ofString "out")])
      (.seq (.store (.op .add [.var .global (ofString "ev"),.const 120]) (.var .local (ofString "out")))
        (.seq (.store (.op .add [.var .global (ofString "ev"),.const 128]) (.const 32)) (.return (.const 0))))
    let p : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "charge_gas") args)
      (.decCall (ofString "out") .one (ofString "alloc") [.const 32] tail)
    Resumes (evaluateHOLFiniteState s p).1 →
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s p).2 := by
  intro tail p hr
  change Resumes (evaluateHOLFiniteState s (.seq _ _)).1 at hr
  change EvmStepCC frameStartGw s (evaluateHOLFiniteState s (.seq _ _)).2
  rw [evaluateHOLFiniteState_seq_line780] at hr ⊢
  rcases heval : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "charge_gas") args) with ⟨r,mid⟩
  simp only [heval] at hr ⊢
  cases r with
  | some r =>
    simp only at hr ⊢
    have hg := precompile_charge_gas_call_step args s hi.1.1.code hi
      (by rw [heval]; exact fun ht => EvmFrameSpecs.not_resumes_timeOut (ht ▸ hr))
      (by rw [heval]; exact Or.inr (Or.inr (Or.inr hr)))
    simpa only [heval] using hg
  | none =>
    simp only at hr ⊢
    have hg := precompile_charge_gas_call_step args s hi.1.1.code hi
      (by rw [heval]; simp) (by rw [heval]; exact Or.inl rfl)
    rw [heval] at hg
    have words := hg.1.1.1.2.2.2.2.2.2.2.2.2
    obtain ⟨pad,hp⟩ := words "sha_pad" (by decide)
    obtain ⟨stp,hs⟩ := words "sha_st" (by decide)
    obtain ⟨out,hh⟩ := words "heap_ptr" (by decide)
    change mid.globals.lookup (ofString "sha_pad") = some (.val (.word pad)) at hp
    change mid.globals.lookup (ofString "sha_st") = some (.val (.word stp)) at hs
    change mid.globals.lookup (ofString "heap_ptr") = some (.val (.word out)) at hh
    have hflow : (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "charge_gas") args)).1 = none := by rw [heval]
    have hlocals := precompile_call0_locals_on_flow s _ _ hflow
    rw [heval] at hlocals
    have hc := precompile_sha256_alloc_tail_step_unconditional mid pad stp out len ptr hg.1.1 hh hp hs
      (by rw [hlocals]; exact hn) hr
    exact ⟨⟨hc.1.1,le_trans hg.1.2.1 hc.1.2.1,
      fun k hk => (hg.1.2.2.1 k hk).trans (hc.1.2.2.1 k hk),
      hc.1.2.2.2.trans hg.1.2.2.2⟩,by
        intro ec hec
        obtain ⟨a,b,c,d⟩ := hg.2 ec hec
        obtain ⟨a',b',c',d'⟩ := hc.2 ec (hg.1.2.2.2.symm ▸ hec)
        exact ⟨a'.trans a,b'.trans b,c'.trans c,d'.trans d⟩⟩

theorem pre_sha256_body_step_of_input_bound {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hi : EvmInv s)
    (hbound : ∀ msg : ValueHOL 64, @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ev"),.const 112])) = some msg →
      let t := setVarHOLFinite (ofString "msg") msg s
      ∀ v : ValueHOL 64, @evalHOLExact 64 F _ t.toExact
        (fun a => Classical.propDecidable (t.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "msg"),.const 96])) = some v →
        ∃ n : BitVec 64, v = .val (.word n) ∧ n.toNat+64 < 2^64)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_pre_sha256)).1 ≠ some .timeOut)
    (hfr : R13.FlowsOrResumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_pre_sha256)).1) :
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_pre_sha256)).2 := by
  dsimp only [sourceFnBody,sourceFunctionEntry,Guest.Software.guestFn_pre_sha256,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural] at hnt hfr ⊢
  apply precompile_step_dec_at s _ _ _ _ ?_ hnt hfr
  intro msg hmsg hshape hnt hfr
  let t := setVarHOLFinite (ofString "msg") msg s
  have hit : EvmInv t := by
    exact localsFree_evmInv s t.locals s.clock hi
  apply precompile_step_dec_at t _ _ _ _ ?_ hnt hfr
  intro v hv hshape hnt hfr
  obtain ⟨n,rfl,hnb⟩ := hbound msg hmsg v hv
  let u := setVarHOLFinite (ofString "n") (.val (.word n)) t
  have hiu : EvmInv u := by
    exact localsFree_evmInv t u.locals t.clock hit
  apply precompile_sha256_words_gas_tail_step u n _ hiu ?_ hnb hnt hfr
  simp [u,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

theorem precompile_identity_tail_at {F : Type} (s : PanSemStateFiniteExact 64 F)
    (args : List (ExpHOL 64)) (n : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hi : EvmInv s)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n))) :
    let p : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "charge_gas") args)
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const 120])
        (.load .one (.op .add [.var .local (ofString "msg"), .const 88])))
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const 128])
        (.var .local (ofString "n"))) (.return (.const 0))))
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    R13.FlowsOrResumes (evaluateHOLFiniteState s p).1 →
    EvmStepCC frameStartGw s (evaluateHOLFiniteState s p).2 := by
  dsimp only
  intro hnt hfr
  apply precompile_step_seq_at s _ _ _ _ hnt hfr
  · exact precompile_charge_gas_call_step args s hcode hi
  · intro hflow hnt hfr
    let mid := (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).2
    have hs := precompile_charge_gas_call_step args s hcode hi
      (by rw [hflow]; simp) (Or.inl hflow)
    have hmcode : mid.code = originalRuntimeCode :=
      ((evaluateHOLFiniteState_metadata s _).1).trans hcode
    have hmn : mid.locals.lookup (ofString "n") = some (.val (.word n)) := by
      dsimp only [mid]
      rw [precompile_call0_locals_on_flow s _ _ hflow]
      exact hn
    apply precompile_step_seq_at mid _ _ _ _ hnt hfr
    · exact precompile_store_output_step 120 (Or.inl rfl) _
        (fun s v hv => EvmFrameSpecs.word_of_load_one s _ v hv) mid hmcode hs.1.1
    · intro hstore hnt hfr
      change (evaluateHOLFiniteState mid (.store
        (.op .add [.var .global (ofString "ev"), .const 120#64])
        (.load .one (.op .add [.var .local (ofString "msg"), .const 88])))).1 = none at hstore
      let post := (evaluateHOLFiniteState mid (.store
        (.op .add [.var .global (ofString "ev"), .const 120])
        (.load .one (.op .add [.var .local (ofString "msg"), .const 88])))).2
      have ht := precompile_store_output_step 120 (Or.inl rfl) _
        (fun s v hv => EvmFrameSpecs.word_of_load_one s _ v hv) mid hmcode hs.1.1
        (by rw [hstore]; simp) (Or.inl hstore)
      have hpcode : post.code = originalRuntimeCode :=
        ((evaluateHOLFiniteState_metadata mid _).1).trans hmcode
      have hpn : post.locals.lookup (ofString "n") = some (.val (.word n)) := by
        dsimp only [post]; rw [precompile_store_locals]; exact hmn
      apply precompile_step_seq_at post _ _ _ _ hnt hfr
      · intro _ hfr
        exact precompile_store_output_local_at post 128 (Or.inr rfl) _ n ht.1.1 hpn hfr
      · intro hstore hnt hfr
        have hu := precompile_store_output_local_at post 128 (Or.inr rfl) _ n ht.1.1 hpn
          (Or.inl hstore)
        exact dispatch_step_ro (ReadOnlyProg.ret _) _
          (((evaluateHOLFiniteState_metadata post _).1).trans hpcode) hu.1.1 hnt hfr

private theorem dispatch_step_ite (cond : ExpHOL 64) {a b : ProgHOL 64}
    (ha : EvmProgStep frameStartGw a) (hb : EvmProgStep frameStartGw b) :
    EvmProgStep frameStartGw (.ite cond a b) := by
  intro F s hcode hInv hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · split at hnt
    · rename_i hz
      simp only [hz, ↓reduceIte] at hfr ⊢
      exact hb s hcode hInv hnt hfr
    · rename_i hz
      simp only [hz, ↓reduceIte] at hfr ⊢
      exact ha s hcode hInv hnt hfr
  · rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h

theorem pre_identity_body_step :
    EvmProgStep frameStartGw (sourceFnBody Guest.Software.guestFn_pre_identity) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_pre_identity,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  apply precompile_step_dec
  intro F s hcode hInv hnt hfr
  apply precompile_step_dec_at s _ _ _ _ _ hnt hfr
  intro v hv hshape hnt hfr
  obtain ⟨n, rfl⟩ := EvmFrameSpecs.word_of_load_one s _ v hv
  let mid := setVarHOLFinite (ofString "n") (.val (.word n)) s
  have hmid : mid = {s with locals := mid.locals, clock := s.clock} := by cases s; rfl
  have hi : EvmInv mid := by rw [hmid]; exact localsFree_evmInv s _ _ hInv
  have hn : mid.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  apply precompile_step_decCall_ro_at precompile_ro_words_of _ _ _ _ mid hcode hi _ hnt hfr
  intro v k
  dsimp only
  apply precompile_identity_tail_at
    {mid with locals := (setVarHOLFinite (ofString "w") v mid).locals, clock := k}
    _ n hcode (localsFree_evmInv mid _ k hi)
  change (setVarHOLFinite (ofString "w") v mid).locals.lookup (ofString "n") = _
  simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    show ofString "w" ≠ ofString "n" by decide] using hn

theorem lookup_pre_identity :
    originalRuntimeCode.lookup (ofString "pre_identity") =
      some ([], sourceFnBody Guest.Software.guestFn_pre_identity, .one) :=
  lookup_of_guestAst_getElem 823 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_identity) rfl

theorem ek_cc_pre_identity :
    EvmKeeps EvmInv frameStartGw (ofString "pre_identity") ∧
      ChainCellsKept EvmInv (ofString "pre_identity") := by
  constructor
  · refine ⟨_, _, _, lookup_pre_identity, ?_⟩
    intro F s hcode hi hex hnt hres
    exact (pre_identity_body_step s hcode hi hnt (Or.inr (Or.inr (Or.inr hres)))).1
  · refine ⟨_, _, _, lookup_pre_identity, ?_⟩
    intro F s hcode hi hex hnt hres
    exact (pre_identity_body_step s hcode hi hnt (Or.inr (Or.inr (Or.inr hres)))).2

theorem pre_identity_call_step :
    EvmProgStep frameStartGw (.call (some (none, none)) (ofString "pre_identity") []) :=
  precompile_step_call0 ek_cc_pre_identity.1 ek_cc_pre_identity.2 []

theorem run_precompile_body_step_of_dispatch (h : PrecompileDispatchSpecs) :
    EvmProgStep frameStartGw (sourceFnBody Guest.Software.guestFn_run_precompile) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_run_precompile,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  repeat first
    | apply dispatch_step_seq
    | apply dispatch_step_ite
    | exact dispatch_step_ro (ReadOnlyProg.ret _)
    | exact dispatch_step_ro ReadOnlyProg.skip
    | exact dispatch_step_ro (ReadOnlyProg.raise _ _)
    | exact h _ (by simp)

theorem lookup_run_precompile :
    originalRuntimeCode.lookup (ofString "run_precompile") =
      some ([(ofString "idx", .one)],
        sourceFnBody Guest.Software.guestFn_run_precompile, .one) :=
  lookup_of_guestAst_getElem 830 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_run_precompile) rfl

theorem run_precompile_zero_index {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hz : s.locals.lookup (ofString "idx") = some (.val (.word 0))) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_run_precompile) =
      evaluateHOLFiniteState s (.raise (ofString "BlockErr") (.const 99)) := by
  have hb : sourceFnBody Guest.Software.guestFn_run_precompile =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_run_precompile).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_run_precompile,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
    evaluateHOLFiniteState_skip, evalHOLExact, hz,
    Compiler.Encoders.Asm.wordCmpHOL]
  split <;> simp_all
  split <;> simp_all
  split_ifs at * <;> simp_all

theorem run_precompile_invalid_index {F : Type} (s : PanSemStateFiniteExact 64 F)
    (idx : BitVec 64)
    (hidx : s.locals.lookup (ofString "idx") = some (.val (.word idx)))
    (hinvalid : idx ∉ ([1, 2, 3, 4, 6, 7, 8, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] :
      List (BitVec 64))) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_run_precompile) =
      evaluateHOLFiniteState s (.raise (ofString "BlockErr") (.const 99)) := by
  have hb : sourceFnBody Guest.Software.guestFn_run_precompile =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_run_precompile).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_run_precompile,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hinvalid
  rcases hinvalid with ⟨h1, h2, h3, h4, h6, h7, h8, h5, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18⟩
  change idx ≠ 1#64 at h1
  change idx ≠ 2#64 at h2
  change idx ≠ 3#64 at h3
  change idx ≠ 4#64 at h4
  change idx ≠ 5#64 at h5
  change idx ≠ 6#64 at h6
  change idx ≠ 7#64 at h7
  change idx ≠ 8#64 at h8
  change idx ≠ 9#64 at h9
  change idx ≠ 10#64 at h10
  change idx ≠ 11#64 at h11
  change idx ≠ 12#64 at h12
  change idx ≠ 13#64 at h13
  change idx ≠ 14#64 at h14
  change idx ≠ 15#64 at h15
  change idx ≠ 16#64 at h16
  change idx ≠ 17#64 at h17
  change idx ≠ 18#64 at h18
  simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
    evaluateHOLFiniteState_skip, evalHOLExact, hidx,
    Compiler.Encoders.Asm.wordCmpHOL, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18]
  split <;> simp_all
  split <;> simp_all
  split_ifs at * <;> simp_all

theorem run_precompile_invalid_no_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (idx : BitVec 64)
    (hidx : s.locals.lookup (ofString "idx") = some (.val (.word idx)))
    (hinvalid : idx ∉ ([1, 2, 3, 4, 6, 7, 8, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] :
      List (BitVec 64))) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_run_precompile)).1 ≠
      some (.returned v) := by
  rw [run_precompile_invalid_index s idx hidx hinvalid]
  simp [evaluateHOLFiniteState_raise, evalHOLExact]
  split <;> simp_all
  split_ifs <;> simp

theorem run_precompile_index_mem_of_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (idx : BitVec 64)
    (hidx : s.locals.lookup (ofString "idx") = some (.val (.word idx)))
    (hreturn : ∃ v, (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_run_precompile)).1 = some (.returned v)) :
    idx ∈ ([1, 2, 3, 4, 6, 7, 8, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] :
      List (BitVec 64)) := by
  by_contra hinvalid
  obtain ⟨v, hv⟩ := hreturn
  exact run_precompile_invalid_no_return s idx hidx hinvalid v hv

theorem ek_cc_run_precompile_of_dispatch (h : PrecompileDispatchSpecs) :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "run_precompile") ∧
      ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "run_precompile") := by
  have hInv {F : Type} {s : PanSemStateFiniteExact 64 F}
      (hP : EvmAvoids FrameStartAvoids s) : EvmInv s := by
    obtain ⟨hA, S, hI, _⟩ := hP
    exact (evmInv_iff_at s).2 ⟨hA, S, hI⟩
  constructor
  · refine ⟨_, _, _, lookup_run_precompile, ?_⟩
    intro F s hcode hP hex hnt hres
    exact (run_precompile_body_step_of_dispatch h s hcode (hInv hP) hnt
      (Or.inr (Or.inr (Or.inr hres)))).1
  · refine ⟨_, _, _, lookup_run_precompile, ?_⟩
    intro F s hcode hP hex hnt hres
    exact (run_precompile_body_step_of_dispatch h s hcode (hInv hP) hnt
      (Or.inr (Or.inr (Or.inr hres)))).2

theorem framePrologueCalleeSpecs_of_dispatch
    (hemit : EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw
      (ofString "emit_transfer_log"))
    (hemit_cc : ChainCellsKept (EvmAvoids FrameStartAvoids)
      (ofString "emit_transfer_log"))
    (hdispatch : PrecompileDispatchSpecs) : FramePrologueCalleeSpecs :=
  ⟨ek_move_ether, cc_move_ether, hemit, hemit_cc,
    (ek_cc_run_precompile_of_dispatch hdispatch).1,
    (ek_cc_run_precompile_of_dispatch hdispatch).2⟩

theorem frame_prologue_start_of_dispatch
    (hemit : EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw
      (ofString "emit_transfer_log"))
    (hemit_cc : ChainCellsKept (EvmAvoids FrameStartAvoids)
      (ofString "emit_transfer_log"))
    (hdispatch : PrecompileDispatchSpecs) :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "frame_prologue") ∧
      ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_prologue") ∧
      EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "frame_start") ∧
      ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_start") := by
  have h := framePrologueCalleeSpecs_of_dispatch hemit hemit_cc hdispatch
  exact ⟨ek_frame_prologue_of_callees h, frame_prologue_chainCellsKept_of_callees h,
    ek_frame_start_of_callees h, frame_start_chainCellsKept_of_callees h⟩

theorem framePrologueCalleeSpecs_of_system_heap_and_dispatch
    (hready : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmAvoids FrameStartAvoids s →
      Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (hdispatch : PrecompileDispatchSpecs) : FramePrologueCalleeSpecs := by
  obtain ⟨hemit, hcells⟩ := ek_cc_emit_transfer_log_of_system_heap hready
  exact framePrologueCalleeSpecs_of_dispatch hemit hcells hdispatch

theorem frame_prologue_start_of_system_heap_and_dispatch
    (hready : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmAvoids FrameStartAvoids s →
      Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (hdispatch : PrecompileDispatchSpecs) :
    EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "frame_prologue") ∧
      ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_prologue") ∧
      EvmKeeps (EvmAvoids FrameStartAvoids) frameStartGw (ofString "frame_start") ∧
      ChainCellsKept (EvmAvoids FrameStartAvoids) (ofString "frame_start") := by
  obtain ⟨hemit, hcells⟩ := ek_cc_emit_transfer_log_of_system_heap hready
  exact frame_prologue_start_of_dispatch hemit hcells hdispatch

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
