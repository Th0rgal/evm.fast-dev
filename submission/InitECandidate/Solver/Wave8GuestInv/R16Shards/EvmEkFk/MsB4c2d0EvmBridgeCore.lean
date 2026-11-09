import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2bWorldStepCode

/-!
# Scratch Rung B4c2d0: `WorldStepSc` (with extra `Q`) → `EvmStepCC` + `MsgOwned` Core Bridge

Bridges any `WorldStepCodeSc B gw s r post` (`PosBufList B`, `SafeStepGlobals gw`) directly to
`EvmMsgReadyMsgBounded post ∧ EvmStepCC gw_out s post ∧ memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112)`,
and lifts `WorldKeepsCodeSc` and bounded-return (`get_code`, `ext_code_of`) callees to `FunSpec`
and `Hoare` wrappers on `D0PreB`.
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
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
  (IvlUnhit not_cellHits_of_disj memW_eq_of_ivlUnhit worldOwned_zero_or_allocated
   worldOwned_zero_aligned worldTypedWith_erase_local adjoin_local_table
   htabValues_eq_of_unhit ivl_allocated_bound zero_not_mem_S worldTypedIvls_sub_worldOwned)
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-! ## 1. `AllocatedEvm` & Frame-Table Stripping Helpers -/

theorem wordsOK_transfer_b4d {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {i : Ivl} (hw : WordsOK s i) :
    WordsOK post i := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨_, hdom, _⟩ := hw.2.2 k hk
  rcases hm : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with ⟨w⟩
  exact ⟨w, hgP.memaddrs.trans hgS.memaddrs.symm ▸ hdom, hm⟩

def AllocatedEvmB4d {F : Type} (s : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  Inside i sourceBase (globN s "heap_ptr") ∨
    Inside i scratchStart (globN s "frame_mem_ptr") ∨
    Inside i (globN s "scratch_ptr") scratchEnd

theorem allocatedEvm_of_allocated_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} {i : Ivl} (hi : Allocated s i) :
    AllocatedEvmB4d s i := by
  rcases hi with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem allocatedEvm_disj_freeGap_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hAs : ArenaOK s) {i : Ivl}
    (hi : i.2 = 0 ∨ AllocatedEvmB4d s i) :
    Disj i (freeGap s) := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  unfold freeGap
  rcases hi with hz | h | h | h
  · exact Or.inl hz
  · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp; omega)))

theorem allocatedEvm_disj_heapFree_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hAs : ArenaOK s) {i : Ivl}
    (hi : i.2 = 0 ∨ AllocatedEvmB4d s i) :
    Disj i (heapFree s) := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  unfold heapFree
  rcases hi with hz | h | h | h
  · exact Or.inl hz
  · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp; omega)))

theorem allocatedEvm_disj_freshHeap_b4d {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {i j : Ivl} (hi : i.2 = 0 ∨ AllocatedEvmB4d s i)
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

theorem allocatedEvm_disj_ownedGrows_b4d {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {o : Ivl} {old new : List Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : o.2 = 0 ∨ AllocatedEvmB4d s o)
    (hold : ∀ i ∈ old, Disj o i)
    (hgrow : OwnedGrows s post old new) :
    ∀ j ∈ new, Disj o j := by
  intro j hj
  rcases hgrow j hj with rfl | ⟨i, hi, hin⟩ | hfresh
  · exact disj_zero_right o
  · exact disj_of_inside_right hin (hold i hi)
  · exact allocatedEvm_disj_freshHeap_b4d hAs hAp hhp ho hfresh

theorem allocatedEvm_bound_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hAs : ArenaOK s) {i : Ivl}
    (hi : AllocatedEvmB4d s i) :
    i.1 + i.2 ≤ 2 ^ 64 := by
  have hlim1 : heapLimit ≤ 2 ^ 64 := by decide
  have hlim2 : scratchEnd ≤ 2 ^ 64 := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, hs_se, _⟩ := hAs
  rcases hi with h | h | h <;> unfold Inside at h <;> omega

theorem frameObject_zero_or_allocatedEvm_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat} {ec o : Ivl}
    (hAs : ArenaOK s) (hFW : FrameWF s S ec) (ho : o ∈ frameObjects s ec) :
    o.2 = 0 ∨ AllocatedEvmB4d s o := by
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

theorem ivlUnhit_of_worldStep_frameOutside_b4d {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old R : List Ivl} {i : Ivl}
    (hAs : ArenaOK s)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (hold_z : ∀ j ∈ old, j.2 = 0 → j.1 % 8 = 0)
    (hR_z : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hi1 : i.1 % 8 = 0) (hi2 : i.2 % 8 = 0)
    (hi_al : i.2 = 0 ∨ AllocatedEvmB4d s i)
    (hi_old : ∀ j ∈ old, Disj i j)
    (hi_R : ∀ j ∈ R, Disj i j) :
    IvlUnhit s post i := by
  have hfg_z : (freeGap s).2 = 0 → (freeGap s).1 % 8 = 0 := fun _ => hAs.2.2.2.2.2.2.1
  have hhf_z : (heapFree s).2 = 0 → (heapFree s).1 % 8 = 0 := fun _ => hAs.2.2.2.2.2.1
  have hi_fg := allocatedEvm_disj_freeGap_b4d hAs hi_al
  have hi_hf := allocatedEvm_disj_heapFree_b4d hAs hi_al
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

theorem worldTypedWith_strip_frame_tables_b4d {F : Type}
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

theorem adjoin_local_table_list_b4d {F : Type}
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

theorem frameRole_ne_worldOrJournal_b4d {F : Type}
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

theorem worldTableRefs_in_worldOrJournalRoleSlots_b4d {F : Type}
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

theorem disj_comm_b4d {i j : Ivl} (h : Disj i j) : Disj j i := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem avoidsTries_join_msgs_b4d {F : Type}
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

theorem globalBuffers_sz_pos_b4d {gn : String × Nat} (h : gn ∈ globalBuffers) :
    0 < gn.2 := by
  revert gn h; decide

theorem bufRegions_zero_aligned_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} {B : BufList}
    (hB : ValidBufList B) (hF : FixedTyped s) :
    ∀ j ∈ bufRegions B s, j.2 = 0 → j.1 % 8 = 0 := by
  intro j hj _
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
  obtain ⟨sz, hgb, _, _⟩ := hB p hp
  by_cases hz : globN s p.1 = 0
  · simp [Wave8GuestInv.bufferRegion, hz]
  · have hfix : Wave8GuestInv.bufferRegion s (p.1, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
    have hpos : 0 < sz := globalBuffers_sz_pos_b4d hgb
    rcases hF.1 _ hfix with h0 | ⟨_, hw⟩
    · simp [Wave8GuestInv.bufferRegion, hz] at h0; omega
    · have h1 := hw.1
      simp only [Wave8GuestInv.bufferRegion, hz, ↓reduceIte] at h1 ⊢
      exact h1

theorem bufRegions_disj_of_disj_fixedObjects_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} {B : BufList} {i : Ivl}
    (hB : ValidBufList B) (hfix_dj : ∀ j ∈ fixedObjects s, Disj i j) :
    ∀ j ∈ bufRegions B s, Disj i j := by
  intro j hj
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
  obtain ⟨sz, hgb, _, hle⟩ := hB p hp
  by_cases hz : globN s p.1 = 0
  · exact Or.inr (Or.inl (by simp [Wave8GuestInv.bufferRegion, hz]))
  · have hfix : Wave8GuestInv.bufferRegion s (p.1, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
    have hd := hfix_dj _ hfix
    have hin : Inside (Wave8GuestInv.bufferRegion s p) (Wave8GuestInv.bufferRegion s (p.1, sz)).1
        ((Wave8GuestInv.bufferRegion s (p.1, sz)).1 + (Wave8GuestInv.bufferRegion s (p.1, sz)).2) := by
      simp only [Wave8GuestInv.bufferRegion, hz, ↓reduceIte, Inside]
      exact ⟨le_rfl, by omega⟩
    exact disj_of_inside_right hin hd

theorem htabFootprint_len_pos_b4d {F : Type}
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

theorem worldOwned_inside_heap_or_mark_of_ownedGrows_b4d {F : Type}
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


theorem evmStepCC_full_of_worldStepSc_gen {F : Type}
    {B : BufList} {gw gw_out : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {Extra : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F →
      List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S : List Nat}
    (hB : ValidBufList B)
    (hgw : SafeStepGlobals gw)
    (hgw_sub : ∀ g ∈ gw, g ∈ gw_out)
    (hAs : ArenaReady s)
    (hInvAt : EvmInvAt s S)
    (hMO : MsgOwned s S (memW s (globN s "ev" + 112)))
    (hstep : WorldStepSc (bufRegions B) gw keep Q s r post)
    (hextra : ∀ {F : Type} (s1 post1 : PanSemStateFiniteExact 64 F) (S_w1 Nd1 : List Nat),
      WorldTypedWith s1 S_w1 Nd1 →
      IvlsDisj (bufRegions B s1) (worldTypedIvls s1 S_w1 Nd1) →
      Extra s1 post1 S_w1 Nd1) :
    ∃ S_w F_rem S_w' Nd Nd' : List Nat,
      let S' := S_w' ++ F_rem
      ArenaReady post ∧
      S.Perm (S_w ++ F_rem) ∧
      (∀ t ∈ S_w, t ∈ S_w') ∧
      WorldTypedWith s S Nd ∧
      WorldTypedWith s S_w Nd ∧
      WorldTypedWith post S_w' Nd' ∧
      WorldTypedWith post S' Nd' ∧
      OwnedGrows s post (worldOwned s S_w Nd) (worldOwned post S_w' Nd') ∧
      FrameOutside s post (worldOwned s S_w Nd ++ bufRegions B s ++ [freeGap s]) (heapFree s) ∧
      (∀ t ∈ F_rem, htabFootprint post t = htabFootprint s t) ∧
      Q s r post S_w' Nd' ∧
      Extra s post S_w Nd ∧
      EvmInvAt post S' ∧
      MsgOwned post S' (memW post (globN post "ev" + 112)) ∧
      EvmStepCC gw_out s post ∧
      memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) ∧
      (∀ t ∈ F_rem, ∀ i ∈ htabFootprint s t, IvlUnhit s post i) := by
  obtain ⟨⟨hAp, hhp, hG, _, htyped⟩, hsc⟩ := hstep
  have hag : AllocatorGrows s post := ⟨hhp, hsc⟩
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW,
    hFO_pw, hFO_disj, hAT_fo, hMarks, hRoles, hGas⟩ := hInvAt
  obtain ⟨hT, hJ, hF, _⟩ := hW
  set ch := evmChain s
  obtain ⟨Nd_m, hTr_m, hAT_fo_m, hAT_msg_m⟩ :=
    avoidsTries_join_msgs_b4d hAT_fo (fun ec hec => (hFW_all ec hec).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  obtain ⟨Nd_mo, hTr_mo, hAT_mo⟩ := hMO.2.2.2.2.2
  obtain ⟨hTr, hsub_nd⟩ := EvmStepLemmas.triesTypedWith_inter hTr_m hTr_mo
  set Nd := Nd_m.filter (fun n => decide (n ∈ Nd_mo))
  have hAT_fo_Nd : ∀ o ∈ (ch.map (frameObjects s)).flatten, ∀ j ∈ nodeExtents s Nd, Disj o j :=
    fun o ho j hj => hAT_fo_m o ho j (hsub_nd j hj).1
  have hAT_msg_Nd : ∀ ec ∈ ch, ∀ j ∈ nodeExtents s Nd, Disj (memW s (ec.1 + 112), 176) j :=
    fun ec hec j hj => hAT_msg_m ec hec j (hsub_nd j hj).1
  have hAT_cur_Nd : ∀ j ∈ nodeExtents s Nd, Disj (memW s (globN s "ev" + 112), 176) j :=
    fun j hj => hAT_mo _ (List.mem_singleton.2 rfl) j (hsub_nd j hj).2
  have hWT_S : WorldTypedWith s S Nd := ⟨hT, hJ, hF, hTr⟩
  let L : List Nat := ch.flatMap fun ec =>
    [memW s (ec.1 + 136), memW s (ec.1 + 168), memW s (ec.1 + 176)]
  have hL_local : ∀ t ∈ L, ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t := by
    intro t ht
    obtain ⟨ec, hec, ht_ec⟩ := List.mem_flatMap.1 ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht_ec
    rcases ht_ec with rfl | rfl | rfl
    · exact frameRole_ne_worldOrJournal_b4d hRoles (rf := "frame.del")
        (List.mem_flatMap.2 ⟨ec, hec, by simp⟩) (by decide)
    · exact frameRole_ne_worldOrJournal_b4d hRoles (rf := "frame.addr")
        (List.mem_flatMap.2 ⟨ec, hec, by simp⟩) (by decide)
    · exact frameRole_ne_worldOrJournal_b4d hRoles (rf := "frame.key")
        (List.mem_flatMap.2 ⟨ec, hec, by simp⟩) (by decide)
  obtain ⟨S_w, F_rem, hnd_F, hF_in, hL_not_Sw, hperm_S, hWT_Sw⟩ :=
    worldTypedWith_strip_frame_tables_b4d hWT_S L hL_local
  have hSw_sub_S : ∀ t ∈ S_w, t ∈ S :=
    fun t ht => hperm_S.symm.subset (List.mem_append_left _ ht)
  have hF_sub_S : ∀ t ∈ F_rem, t ∈ S :=
    fun t ht => hperm_S.symm.subset (List.mem_append_right _ ht)
  have hR_disj : IvlsDisj (bufRegions B s) (worldTypedIvls s S_w Nd) :=
    validBufList_disj hB hWT_Sw
  obtain ⟨S_w', Nd', hSw_sub_Sw', hWT_Sw', hgrow, hfr, hQ⟩ := htyped S_w Nd hWT_Sw hR_disj
  have hold_z : ∀ j ∈ worldOwned s S_w Nd, j.2 = 0 → j.1 % 8 = 0 :=
    worldOwned_zero_aligned hWT_Sw
  have hR_z : ∀ j ∈ bufRegions B s, j.2 = 0 → j.1 % 8 = 0 :=
    bufRegions_zero_aligned_b4d hB hF
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
    fun ec hec o ho => allocatedEvm_disj_ownedGrows_b4d hAs.2 hAp.2 hhp
      (frameObject_zero_or_allocatedEvm_b4d hAs.2 (hFW_all ec hec) ho)
      (hfo_disj_old ec hec o ho) hgrow
  have hfo_unhit : ∀ ec ∈ ch, ∀ o ∈ frameObjects s ec, WordsOK s o → IvlUnhit s post o := by
    intro ec hec o ho hwo
    exact ivlUnhit_of_worldStep_frameOutside_b4d hAs.2 hfr hold_z hR_z hwo.1 hwo.2.1
      (frameObject_zero_or_allocatedEvm_b4d hAs.2 (hFW_all ec hec) ho)
      (hfo_disj_old ec hec o ho)
      (bufRegions_disj_of_disj_fixedObjects_b4d hB (hFO_disj ec hec o ho).2)
  have hfo_bound : ∀ ec ∈ ch, ∀ o ∈ frameObjects s ec, o.2 = 0 ∨ o.1 + o.2 ≤ 2 ^ 64 := by
    intro ec hec o ho
    rcases frameObject_zero_or_allocatedEvm_b4d hAs.2 (hFW_all ec hec) ho with hz | hal
    · exact Or.inl hz
    · exact Or.inr (allocatedEvm_bound_b4d hAs.2 hal)
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
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ ch := by
    simp [ch, evmChain, evmChainFrom]
  have h112_eq : memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) :=
    (hrec_eq _ hhead_mem).1 112 (by omega) (by omega)
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
        refine ⟨wordsOK_transfer_b4d hAs.1 hAp.1 hw_l, hag.allocated hal_l,
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
        exact ⟨wordsOK_transfer_b4d hAs.1 hAp.1 hle.1,
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
    · exact disj_comm_b4d ((hTr.2.1 j hj_nd).1 t htS i hi)
  have hF_unhit : ∀ t ∈ F_rem, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
    intro t ht i hi
    have htS := hF_sub_S t ht
    have hwo := ((hT.2.1 t htS).1.1 i hi).2
    have hal := ((hT.2.1 t htS).2 i hi).1
    exact ivlUnhit_of_worldStep_frameOutside_b4d hAs.2 hfr hold_z hR_z hwo.1 hwo.2.1
      (Or.inr (allocatedEvm_of_allocated_b4d hal))
      (hF_disj_old t ht i hi)
      (bufRegions_disj_of_disj_fixedObjects_b4d hB ((hT.2.1 t htS).2 i hi).2)
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
    exact allocatedEvm_disj_ownedGrows_b4d hAs.2 hAp.2 hhp
      (Or.inr (allocatedEvm_of_allocated_b4d hal))
      (hF_disj_old t ht i hi) hgrow
  have hdj_FF_post : ∀ t ∈ F_rem, ∀ u ∈ F_rem, t ≠ u →
      ∀ i ∈ htabFootprint post t, ∀ j ∈ htabFootprint post u, Disj i j := by
    intro t ht u hu hne i hi j hj
    rw [(hF_hdr_fp t ht).2] at hi
    rw [(hF_hdr_fp u hu).2] at hj
    exact hT.2.2.1 t (hF_sub_S t ht) u (hF_sub_S u hu) hne i hi j hj
  set S' := S_w' ++ F_rem
  have hWT_S' : WorldTypedWith post S' Nd' :=
    adjoin_local_table_list_b4d hWT_Sw' F_rem hnd_F hwf_F_post hall_F_post hdj_F_Sw' hdj_FF_post
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
  have hdelEx_F : ∀ (i : Nat) (hi : i + 1 < ch.length) (u : Nat),
      u ∈ F_rem → DelExclusive s S ch i u → DelExclusive post S' ch i u := by
    intro i hi u huF ⟨_, hu_frames⟩
    have huS' : u ∈ S' := List.mem_append_right _ huF
    have hu_nz : u ≠ 0 := fun h0 => zero_not_mem_S hWT_S'.1 (h0 ▸ huS')
    refine ⟨?_, ?_⟩
    · intro hw_post
      obtain ⟨r_u, hru⟩ := worldTableRefs_in_worldOrJournalRoleSlots_b4d hWT_S'.1 hu_nz hw_post
      have huSw' : u ∈ S_w' := (hRoles_Sw'.1 (u, r_u) hru).1
      exact hSw'_disj_F u huSw' u huF rfl
    · intro j hj k hk hmem_eq
      have hj_mem : ch[j] ∈ ch := List.getElem_mem _
      have hk_le : k + 8 ≤ 280 ∧ k % 8 = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [(hrec_eq _ hj_mem).1 k hk_le.1 hk_le.2] at hmem_eq
      exact hu_frames j hj k hk hmem_eq
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
  have hmsg_transfer : ∀ m, MsgOwned s S m →
      (∀ j ∈ nodeExtents s Nd, Disj (m, 176) j) →
      MsgOwned post S' m := by
    intro m ⟨hal_m, hw_m, hdt, hdf, hdfo, _⟩ hm_nd
    have hm_disj_old : ∀ j ∈ worldOwned s S_w Nd, Disj (m, 176) j := by
      intro j hj
      unfold worldOwned at hj
      rcases List.mem_append.1 hj with hj1 | hj_nd
      · rcases List.mem_append.1 hj1 with hj_tab | hj_fix
        · obtain ⟨u, hu, hju⟩ := List.mem_flatMap.1 hj_tab
          exact hdt u (hSw_sub_S u hu) j hju
        · exact hdf j hj_fix
      · exact hm_nd j hj_nd
    have hm_disj_new : ∀ j ∈ worldOwned post S_w' Nd', Disj (m, 176) j :=
      allocatedEvm_disj_ownedGrows_b4d hAs.2 hAp.2 hhp
        (Or.inr (allocatedEvm_of_allocated_b4d hal_m)) hm_disj_old hgrow
    refine ⟨hag.allocated hal_m, wordsOK_transfer_b4d hAs.1 hAp.1 hw_m, ?_, ?_, ?_,
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
  have hInvAt_post : EvmInvAt post S' := by
    refine ⟨hW_post, ?_⟩
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
        exact hmsg_transfer _ c17 (hAT_msg_Nd ec hec)
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
                wordsOK_transfer_b4d hAs.1 hAp.1 (c1 i hi).2⟩,
        c2, wordsOK_transfer_b4d hAs.1 hAp.1 c3, c4, c5, c6, c7,
        hS_sub_S' _ c8, hS_sub_S' _ c9, hS_sub_S' _ c10, c11, c12,
        ?_, wordsOK_transfer_b4d hAs.1 hAp.1 c14, ?_, hlo_ok, hmsg_ok⟩
      · rcases c13 with h | h
        · exact Or.inl ⟨h.1, le_trans h.2 hhp⟩
        · exact Or.inr ⟨le_trans hsc h.1, h.2⟩
      · rcases c15 with h0 | ⟨hin, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨⟨hin.1, le_trans hin.2 hhp⟩, wordsOK_transfer_b4d hAs.1 hAp.1 hw⟩
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
      have howned_loc := worldOwned_inside_heap_or_mark_of_ownedGrows_b4d
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
          have hpos := htabFootprint_len_pos_b4d (hWT_Sw'.1.2.1 u huw).1 o ho
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
  have hMO_post : MsgOwned post S' (memW post (globN post "ev" + 112)) := by
    rw [hev_eq, h112_eq]
    exact hmsg_transfer _ hMO hAT_cur_Nd
  have hStepCC : EvmStepCC gw_out s post :=
    ⟨⟨(evmInv_iff_at post).2 ⟨hAp, S', hInvAt_post⟩, hhp, hG_out, hchain_eq⟩, hcc_agree⟩
  exact ⟨S_w, F_rem, S_w', Nd, Nd', hAp, hperm_S, hSw_sub_Sw', hWT_S, hWT_Sw, hWT_Sw', hWT_S',
    hgrow, hfr, fun t ht => (hF_hdr_fp t ht).2, hQ,
    hextra s post S_w Nd hWT_Sw hR_disj, hInvAt_post, hMO_post, hStepCC, h112_eq,
    hF_unhit⟩

/-! ## 2. Master Bridge: `WorldStepSc` (with extra `Q`) → `EvmMsgReadyMsgBounded` + `EvmStepCC` -/

/-- Generalizes `worldStepSc_to_evmStepCC` to arbitrary extra world-step relation `Q` while keeping
the exact table-set witness `S' := S_w' ++ F_rem` exposed so code-DB boundedness (`CodeRootsValsEq`
or `set_code`'s `ts+48` insertion) and `MsgDisjCodeStrong` transfer cleanly. -/
theorem evmStepCC_full_of_worldStepSc {F : Type}
    {B : BufList} {gw gw_out : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S : List Nat}
    (hB : ValidBufList B)
    (hgw : SafeStepGlobals gw)
    (hgw_sub : ∀ g ∈ gw, g ∈ gw_out)
    (hAs : ArenaReady s)
    (hInvAt : EvmInvAt s S)
    (hMO : MsgOwned s S (memW s (globN s "ev" + 112)))
    (hstep : WorldStepSc (bufRegions B) gw keep Q s r post) :
    ∃ S_w F_rem S_w' Nd Nd' : List Nat,
      let S' := S_w' ++ F_rem
      ArenaReady post ∧
      S.Perm (S_w ++ F_rem) ∧
      (∀ t ∈ S_w, t ∈ S_w') ∧
      WorldTypedWith s S Nd ∧
      WorldTypedWith s S_w Nd ∧
      WorldTypedWith post S_w' Nd' ∧
      WorldTypedWith post S' Nd' ∧
      OwnedGrows s post (worldOwned s S_w Nd) (worldOwned post S_w' Nd') ∧
      FrameOutside s post (worldOwned s S_w Nd ++ bufRegions B s ++ [freeGap s]) (heapFree s) ∧
      (∀ t ∈ F_rem, htabFootprint post t = htabFootprint s t) ∧
      Q s r post S_w' Nd' ∧
      EvmInvAt post S' ∧
      MsgOwned post S' (memW post (globN post "ev" + 112)) ∧
      EvmStepCC gw_out s post ∧
      memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) ∧
      (∀ t ∈ F_rem, ∀ i ∈ htabFootprint s t, IvlUnhit s post i) := by
  obtain ⟨S_w, F_rem, S_w', Nd, Nd', hAp, hperm_S, hSw_sub_Sw', hWT_S, hWT_Sw, hWT_Sw', hWT_S',
    hgrow, hfr, hfp_eq, hQ, hExtra, hInvAt_post, hMO_post, hStepCC, h112_eq, hF_unhit⟩ :=
    evmStepCC_full_of_worldStepSc_gen (Extra := @fun _ _ _ _ _ => True) hB hgw hgw_sub hAs hInvAt
      hMO hstep (fun _ _ _ _ _ _ => trivial)
  exact ⟨S_w, F_rem, S_w', Nd, Nd', hAp, hperm_S, hSw_sub_Sw', hWT_S, hWT_Sw, hWT_Sw', hWT_S',
    hgrow, hfr, hfp_eq, hQ, hInvAt_post, hMO_post, hStepCC, h112_eq, hF_unhit⟩
end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
