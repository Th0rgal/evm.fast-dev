import InitECandidate.Solver.Wave8GuestInv.R16Shards.HtabValuesSub
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.Base
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.EvmLemmas
import InitECandidate.Solver.Wave8GuestInv.R11Shards.FrameException

/-! `EvmHtabStep`: general EVM-frame preservation lemma across an `HtabExit` step on a table
`t0 ∈ S` (supporting both non-value-role tables and `ts+32` inner-table restoration, plus optional
`journal_n` decrement). Cycle-free pre-`C00` module (uses `HtabC00Ports`, never `Deliveries.M19`). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports (ExitR)
open InitECandidate.Solver.Wave8Contracts.M08 (WorldGlobalsSame worldGlobalsSame_of_kept
  globN_eq_of_lookup ivl_allocated_bound wordsOK_transfer typedRecords typedRecord_mem_fixedObjects
  rec_word_eq_of_unhit blockOutObjects_eq_of_bo_unhit balRecords_eq_of_unhit
  fixedObjects_eq_of_parts fixedTyped_transfer nodeHeap_congr_bytes
  htabFootprint_eq_of_hdr_unhit htabValues_eq_of_unhit htabValuesIn_congr_unhit
  htabWF_congr_unhit disj_of_inside_left disj_of_inside_right)
open InitECandidate.Solver.Wave8Contracts.M23 (EvmInvAt EvmStep EvmKeeps EvmAvoids Resumes
  GlobalsKept frameWF_bounds triesTypedWith_inter)

private abbrev M08IvlUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i

def IvlUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat i → post.memory a = s.memory a

theorem memW_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) {a : Nat}
    (ha8 : a % 8 = 0) (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  have hmem := hu (BitVec.ofNat 64 a)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact ha8)
    (by unfold CellHits; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega)
  unfold memW; rw [hmem]

theorem ivlUnhit_of_frameOutside {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hi_al : i.1 % 8 = 0 ∧ i.2 % 8 = 0)
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0 ∧ j.2 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    IvlUnhit s post i := by
  obtain ⟨hia1, hia2⟩ := hi_al
  intro a ha8 ⟨hh1, hh2⟩
  apply hfr a
  · intro j hj ⟨hc1, hc2⟩
    obtain ⟨hja1, hja2⟩ := hk_al j hj
    rcases hk j hj with hd | hd | hd | hd <;> omega
  · intro ⟨hcf1, hcf2⟩
    rcases hf with hd | hd | hd | hd <;> omega

theorem disj_fresh_of_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp
  rcases hj with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))

def evmR {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum

private theorem disj_fresh_of_zero_or_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : j.2 = 0 ∨ Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  rcases hj with h0 | hal
  · exact Or.inl h0
  · exact disj_fresh_of_allocated hAs hAp hhp hal

private theorem disj_symm {i j : Ivl} (h : Disj i j) : Disj j i :=
  R11Shards.Disj.symm h

private theorem disj_fresh_of_frameObject {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S : List Nat} {ec o : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hFW : FrameWF s S ec) (ho : o ∈ frameObjects s ec) :
    Disj o (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhp_lim : globN post "heap_ptr" ≤ heapLimit := hAp.2.1
  have hss_fm : scratchStart ≤ globN s "frame_mem_ptr" := hAs.2.2.1
  have hfm_sc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.1
  obtain ⟨hscr, hmem_in, _, _, _, _, _, _, _, _, _, _, hlogs_in, _, hret_in, hll_ok, _⟩ := hFW
  unfold frameObjects at ho
  rcases List.mem_append.1 ho with ho7 | holog
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
    rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := (hscr (ec.1, 280) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · have h := (hscr (ec.2, 104) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · have h := (hscr (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hmem_in; dsimp at hmem_in ⊢; omega)))
    · have h := (hscr (memW s (ec.1 + 88), 24) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · rcases hlogs_in with h | h
      · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp at h ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · rcases hret_in with ⟨hz, _⟩ | ⟨h, _⟩
      · unfold frameRet; simp [hz]; exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp at h ⊢; omega)))
  · unfold frameLogObjects at holog; dsimp only at holog
    obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
    rw [List.mem_range] at hidx_mem
    rcases hll_ok with hz | ⟨_, _, _, _, hent⟩
    · have hlo := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      have hss0 : 0 < scratchStart := by decide
      dsimp at hlo; omega
    · have hle := (hent idx hidx_mem).2
      have ho_rec := (List.mem_filter.1 ho_own).1
      simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
      rcases ho_rec with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.1.2; dsimp at this ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.2.2.2.1.2; dsimp at this ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.2.2.2.2.1.2; dsimp at this ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.2.2.2.2.2.2; dsimp at this ⊢; omega)))

private theorem m08_ivlUnhit_of_frameOutside {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    M08IvlUnhit s post i := by
  intro a ha8 h1 h2
  apply hfr a
  · intro j hj ⟨hc1, hc2⟩
    have hj1 := hk_al j hj
    rcases hk j hj with hd | hd | hd | hd <;> omega
  · intro ⟨hcf1, hcf2⟩
    rcases hf with hd | hd | hd | hd <;> omega

private theorem balObjects_eq_of_unhit_except {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    {t0 : Nat}
    (hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i)
    (ht0_not_bal : globN s "bal_accounts" ≠ t0 ∧ ∀ ad ∈ balRecords s, memW s ad ≠ t0)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s post i)
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    balObjects post = balObjects s ∧
    (∀ ad ∈ balRecords post, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  have hrecs : balRecords post = balRecords s :=
    balRecords_eq_of_unhit hT hbal_eq (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_other _ hm ht0_not_bal.1)
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi => by
    unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
  have had_props : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      htabValues post (memW s ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat),
        memW post (memW s (ad + k)) = memW s (memW s (ad + k)) ∧
        memW post (memW s (ad + k) + 8) = memW s (memW s (ad + k) + 8) ∧
        memW post (memW s (ad + k) + 16) = memW s (memW s (ad + k) + 16)) ∧
      (∀ l ∈ htabValues s (memW s ad),
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16)) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s := by
      unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (ivl_allocated_bound hA hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
          (hu_bal _ had_bal (by simp)) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 (ht0_not_bal.2 ad had))
    have hlst_eq : ∀ l, (l, 24) ∈ balObjects s →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
      intro l hl_bal
      rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      have hhi_l := (ivl_allocated_bound hA hal_l).2
      have hl8 : l % 8 = 0 := hw_l.1
      have hul := hu_bal _ hl_bal (by simp)
      exact ⟨by simpa using InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩,
             InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩,
             InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩⟩
    refine ⟨hoff_eq, hvals_ad, ?_, ?_⟩
    · intro k hk
      by_cases hk0 : memW s (ad + k) = 0
      · simp [hk0, hm0.1, hm0.2.1, hm0.2.2]
      · apply hlst_eq; unfold balObjects; refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hk0]
    · intro l hl
      by_cases hl0 : l = 0
      · subst hl0; simp [hm0.1, hm0.2.1, hm0.2.2]
      · apply hlst_eq; unfold balObjects; refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        apply List.mem_cons_of_mem; apply List.mem_append.2; right
        exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hl0]⟩
  constructor
  · unfold balObjects; rw [hrecs]
    apply List.flatMap_congr; intro ad had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h16 := hoff_eq 16 (by simp); have h24 := hoff_eq 24 (by simp); have h32 := hoff_eq 32 (by simp)
    obtain ⟨hk16_0, _, hk16_16⟩ := hklst 16 (by simp)
    obtain ⟨hk24_0, _, hk24_16⟩ := hklst 24 (by simp)
    obtain ⟨hk32_0, _, hk32_16⟩ := hklst 32 (by simp)
    have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      rw [h0, hvals_ad]; apply List.flatMap_congr; intro l hl
      obtain ⟨hl0, _, hl16⟩ := hllst l hl; simp [lstObjects, hl0, hl16]
    rw [htail, h16, h24, h32]
    simp [lstObjects, hk16_0, hk16_16, hk24_0, hk24_16, hk32_0, hk32_16]
  · intro ad had
    rw [hrecs] at had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    refine ⟨h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]; obtain ⟨_, hk8, hk16⟩ := hklst k hk
      unfold LstOK; rw [hk8, hk16]; exact had_T.2.2.1 k hk
    · intro l hl; rw [h0, hvals_ad] at hl; obtain ⟨_, hl8, hl16⟩ := hllst l hl
      unfold LstOK; rw [hl8, hl16]; exact had_T.2.2.2 l hl

private theorem rolesOK_of_ts_nest_sub {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S : List Nat} {ch : List Ivl}
    (hRoles : RolesOK s S (worldRoleSlots s ++ frameRoleSlots s ch) (journalRoleSlots s))
    (hhdr0 : ∀ u ∈ S, hdr post u 0 = hdr s u 0)
    (hfrs_eq : frameRoleSlots post ch = frameRoleSlots s ch)
    (hjrs_sub : ∀ a ∈ journalRoleSlots post, a ∈ journalRoleSlots s)
    (hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] = recRoles s "ws" [(16, "ws+16"), (32, "ws+32")])
    (hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")])
    (hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")])
    (hba : globN post "bal_accounts" = globN s "bal_accounts")
    (hbia : globN post "bal_idx_accts" = globN s "bal_idx_accts")
    (hbis : globN post "bal_idx_stor" = globN s "bal_idx_stor")
    (hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner")
    (hbal_slots : (balRecords post).flatMap (fun ad => [(memW post ad, "bal.stor"), (memW post (ad + 8), "bal.reads")]) =
      (balRecords s).flatMap (fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]))
    (hnest_ts_sub : ∀ a ∈ nestRoles post "ts" "ts.inner",
      a ∈ nestRoles s "ts" "ts.inner" ∨ (a.2 = "ts.inner" ∧ a ∈ journalRoleSlots s)) :
    RolesOK post S (worldRoleSlots post ++ frameRoleSlots post ch) (journalRoleSlots post) ∧
    RolesOK post S (worldRoleSlots post) (journalRoleSlots post) := by
  let P_pre := recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
    recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
      (48, "bs+48"), (72, "bs+72")] ++
    recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
      (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] ++
    [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"),
      (globN s "bal_idx_stor", "bal_idx_stor")] ++
    nestRoles s "bs" "bs.inner"
  let P_suf := (balRecords s).flatMap fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]
  have hwrs_s : worldRoleSlots s =
      (P_pre.filter (fun a => a.1 != 0)) ++
      ((nestRoles s "ts" "ts.inner").filter (fun a => a.1 != 0)) ++
      (P_suf.filter (fun a => a.1 != 0)) := by
    unfold worldRoleSlots P_pre P_suf
    simp only [List.filter_append, List.append_assoc]
  have hwrs_post : worldRoleSlots post =
      (P_pre.filter (fun a => a.1 != 0)) ++
      ((nestRoles post "ts" "ts.inner").filter (fun a => a.1 != 0)) ++
      (P_suf.filter (fun a => a.1 != 0)) := by
    unfold worldRoleSlots P_pre P_suf
    rw [hrec_ws, hrec_bs, hrec_ts, hba, hbia, hbis, hnest_bs, hbal_slots]
    simp only [List.filter_append, List.append_assoc]
  have hsub_sl_jr : ∀ a ∈ worldRoleSlots post ++ frameRoleSlots post ch,
      a ∈ worldRoleSlots s ++ frameRoleSlots s ch ∨ (a.2 = "ts.inner" ∧ a ∈ journalRoleSlots s) := by
    intro a ha
    rw [hwrs_post, hfrs_eq] at ha
    rcases List.mem_append.1 ha with hw | hf
    · rcases List.mem_append.1 hw with hw12 | hw3
      · rcases List.mem_append.1 hw12 with hw1 | hw2
        · left; rw [hwrs_s]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw1))
        · obtain ⟨hmem_nt, hnz⟩ := List.mem_filter.1 hw2
          rcases hnest_ts_sub a hmem_nt with hold | hnew
          · left; rw [hwrs_s]
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_filter.2 ⟨hold, hnz⟩)))
          · exact Or.inr hnew
      · left; rw [hwrs_s]; exact List.mem_append_left _ (List.mem_append_right _ hw3)
    · exact Or.inl (List.mem_append_right _ hf)
  have hts_sh : "ts.inner" ∈ sharedRoles := by decide
  have hR_full : RolesOK post S (worldRoleSlots post ++ frameRoleSlots post ch) (journalRoleSlots post) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have ha_old : a ∈ (worldRoleSlots s ++ frameRoleSlots s ch) ++ journalRoleSlots s := by
        rcases List.mem_append.1 ha with hsl | hjr
        · rcases hsub_sl_jr a hsl with h1 | ⟨_, h2⟩
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ h2
        · exact List.mem_append_right _ (hjrs_sub a hjr)
      obtain ⟨haS, hkl⟩ := hRoles.1 a ha_old
      exact ⟨haS, (hhdr0 a.1 haS).trans hkl⟩
    · set A := P_pre.filter (fun a => a.1 != 0)
      set Ns := (nestRoles s "ts" "ts.inner").filter (fun a => a.1 != 0)
      set Np := (nestRoles post "ts" "ts.inner").filter (fun a => a.1 != 0)
      set B := P_suf.filter (fun a => a.1 != 0)
      set Fr := frameRoleSlots s ch
      let rel : (Nat × String) → (Nat × String) → Prop :=
        fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles
      have hpw_s := hRoles.2.1
      rw [hwrs_s, List.append_assoc, List.append_assoc] at hpw_s
      rw [hwrs_post, hfrs_eq, List.append_assoc, List.append_assoc]
      obtain ⟨hpw_A, hpw_NsBF, hA_rest⟩ := List.pairwise_append.1 hpw_s
      obtain ⟨hpw_Ns, hpw_BF, hNs_BF⟩ := List.pairwise_append.1 hpw_NsBF
      have hNp_role : ∀ x ∈ Np, x.2 = "ts.inner" ∧ (x ∈ Ns ∨ x ∈ journalRoleSlots s) := by
        intro x hx
        obtain ⟨hm, hnz⟩ := List.mem_filter.1 hx
        have hr2 : x.2 = "ts.inner" := by
          unfold nestRoles at hm
          split_ifs at hm with h1 h2
          · cases hm
          · cases hm
          · obtain ⟨v, _, rfl⟩ := List.mem_map.1 hm; rfl
        rcases hnest_ts_sub x hm with hold | ⟨_, hjr⟩
        · exact ⟨hr2, Or.inl (List.mem_filter.2 ⟨hold, hnz⟩)⟩
        · exact ⟨hr2, Or.inr hjr⟩
      have hNp_pw : Np.Pairwise rel := by
        refine List.pairwise_iff_getElem.2 (fun i j hi hj _ heq => ?_)
        have hi_m : Np[i] ∈ Np := List.getElem_mem hi
        have hj_m : Np[j] ∈ Np := List.getElem_mem hj
        rw [(hNp_role _ hi_m).1, (hNp_role _ hj_m).1]
        exact ⟨rfl, hts_sh⟩
      have hA_in_old : ∀ a ∈ A, a ∈ (worldRoleSlots s ++ frameRoleSlots s ch) ++ journalRoleSlots s := by
        intro a ha; apply List.mem_append_left; rw [hwrs_s]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha))
      have hBF_in_old : ∀ b ∈ B ++ Fr, b ∈ (worldRoleSlots s ++ frameRoleSlots s ch) ++ journalRoleSlots s := by
        intro b hb; apply List.mem_append_left; rw [hwrs_s]
        rcases List.mem_append.1 hb with hbB | hbF
        · exact List.mem_append_left _ (List.mem_append_right _ hbB)
        · exact List.mem_append_right _ hbF
      refine List.pairwise_append.2 ⟨hpw_A, List.pairwise_append.2 ⟨hNp_pw, hpw_BF, ?_⟩, ?_⟩
      · intro x hx b hb heq
        rcases hNp_role x hx with ⟨hx2, hx_old | hx_jr⟩
        · exact hNs_BF x hx_old b hb heq
        · have heq2 := hRoles.2.2 x hx_jr b (hBF_in_old b hb) heq
          exact ⟨heq2, hx2 ▸ hts_sh⟩
      · intro a ha y hy heq
        rcases List.mem_append.1 hy with hyNp | hyBF
        · rcases hNp_role y hyNp with ⟨hy2, hy_old | hy_jr⟩
          · exact hA_rest a ha y (List.mem_append_left _ hy_old) heq
          · have heq2 := hRoles.2.2 y hy_jr a (hA_in_old a ha) heq.symm
            exact ⟨heq2.symm, (heq2.symm.trans hy2) ▸ hts_sh⟩
        · exact hA_rest a ha y (List.mem_append_right _ hyBF) heq
    · intro a ha b hb heq
      have ha_jr : a ∈ journalRoleSlots s := hjrs_sub a ha
      rcases List.mem_append.1 hb with hbsl | hbjr
      · rcases hsub_sl_jr b hbsl with hb1 | ⟨_, hb2⟩
        · exact hRoles.2.2 a ha_jr b (List.mem_append_left _ hb1) heq
        · exact hRoles.2.2 a ha_jr b (List.mem_append_right _ hb2) heq
      · exact hRoles.2.2 a ha_jr b (List.mem_append_right _ (hjrs_sub b hbjr)) heq
  refine ⟨hR_full, ?_⟩
  refine ⟨fun a ha => hR_full.1 a ?_,
          (List.pairwise_append.1 hR_full.2.1).1,
          fun a ha b hb => hR_full.2.2 a ha b ?_⟩
  · rcases List.mem_append.1 ha with hw | hjr
    · exact List.mem_append_left _ (List.mem_append_left _ hw)
    · exact List.mem_append_right _ hjr
  · rcases List.mem_append.1 hb with hw | hjr
    · exact List.mem_append_left _ (List.mem_append_left _ hw)
    · exact List.mem_append_right _ hjr

theorem evmInvAt_of_htab_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {t0 : Nat}
    (hAs : ArenaReady s) (hInv : EvmInvAt s S)
    (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hwf_t0 : HtabWF post t0)
    (hhdr0_t0 : hdr post t0 0 = hdr s t0 0)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfp_t0 : ∀ i ∈ htabFootprint post t0, Allocated post i ∧
      ((∃ j ∈ htabFootprint s t0, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))))
    (hfr : FrameOutside s post (htabFootprint s t0) (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hg_kept : GlobalsKept ["heap_ptr", "journal_n"] s post)
    (hjn_le : globN post "journal_n" ≤ globN s "journal_n")
    (ht0_S : t0 ∈ S)
    (ht0_not_delEx : ∀ (i : Nat) (hi : i + 1 < (evmChain s).length),
      ¬ DelExclusive s S (evmChain s) i t0)
    (ht0_no_ws32 : globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0)
    (ht0_no_bs32 : globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0)
    (ht0_no_ba : globN s "bal_accounts" ≠ t0)
    (ht0_no_ad : ∀ ad ∈ balRecords s, memW s ad ≠ t0)
    (ht0_ts32 : (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∨
      (globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) = t0 ∧
        ∀ v ∈ htabValues post t0, v ∈ htabValues s t0 ∨ (v, "ts.inner") ∈ journalRoleSlots s)) :
    EvmInvAt post S ∧
    evmChain post = evmChain s ∧
    evmR post = evmR s ∧
    (∀ ec ∈ evmChain s, IvlUnhit s post (ec.1, 280) ∧ IvlUnhit s post (ec.2, 104)) := by
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨hT, hJ, hF, _⟩ := hW
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hdom_eq : post.memaddrs = s.memaddrs := hAp.1.memaddrs.trans hAs.1.memaddrs.symm
  have hg_nonHeapJn : ∀ name, ofString name ≠ ofString "heap_ptr" →
      ofString name ≠ ofString "journal_n" → globN post name = globN s name := by
    intro name h1 h2
    exact globN_eq_of_lookup (hg_kept (ofString name) (by
      simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
      rintro ⟨w, rfl | rfl, heq⟩
      · exact h1 heq.symm
      · exact h2 heq.symm))
  have hsc_eq : globN post "scratch_ptr" = globN s "scratch_ptr" := hg_nonHeapJn "scratch_ptr" (by decide) (by decide)
  have hfm_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := hg_nonHeapJn "frame_mem_ptr" (by decide) (by decide)
  have hev_eq : globN post "ev" = globN s "ev" := hg_nonHeapJn "ev" (by decide) (by decide)
  have hcc_eq : globN post "cur_cont" = globN s "cur_cont" := hg_nonHeapJn "cur_cont" (by decide) (by decide)
  have hevm_empty_eq : globN post "evm_empty" = globN s "evm_empty" := hg_nonHeapJn "evm_empty" (by decide) (by decide)
  have hvmsa_eq : globN post "vm_system_address" = globN s "vm_system_address" := hg_nonHeapJn "vm_system_address" (by decide) (by decide)
  have hws_g : globN post "ws" = globN s "ws" := hg_nonHeapJn "ws" (by decide) (by decide)
  have hbs_g : globN post "bs" = globN s "bs" := hg_nonHeapJn "bs" (by decide) (by decide)
  have hts_g : globN post "ts" = globN s "ts" := hg_nonHeapJn "ts" (by decide) (by decide)
  have hbo_g : globN post "bo" = globN s "bo" := hg_nonHeapJn "bo" (by decide) (by decide)
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hg_nonHeapJn "bal_accounts" (by decide) (by decide)
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" := hg_nonHeapJn "bal_idx_accts" (by decide) (by decide)
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" := hg_nonHeapJn "bal_idx_stor" (by decide) (by decide)
  have hj_g : globN post "journal" = globN s "journal" := hg_nonHeapJn "journal" (by decide) (by decide)
  have hjc_g : globN post "journal_cap" = globN s "journal_cap" := hg_nonHeapJn "journal_cap" (by decide) (by decide)
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsc_eq]⟩
  have hf_al1 : (globN s "heap_ptr") % 8 = 0 := hAs.2.2.2.2.2.2.1
  have hf_al2 : (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have := hAs.2.2.2.2.2.2.1; have := hAp.2.2.2.2.2.2.1; omega
  have ht0_al : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hT.2.1 t0 ht0_S).1.1 j hj).2; exact ⟨hw.1, hw.2.1⟩
  have ht0_al1 : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 := fun j hj => (ht0_al j hj).1
  have hunhit_m08 : ∀ i : Ivl, (∀ j ∈ htabFootprint s t0, Disj i j) →
      (i.2 = 0 ∨ Allocated s i) → M08IvlUnhit s post i := fun i hdi hal =>
    m08_ivlUnhit_of_frameOutside hfr ht0_al1 hf_al1 hdi
      (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp hal)
  have hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i := fun u hu hne i hi =>
    hunhit_m08 i (fun j hj => hT.2.2.1 u hu t0 ht0_S hne i hi j hj)
      (Or.inr ((hT.2.1 u hu).2 i hi).1)
  have hu_fix : ∀ i ∈ fixedObjects s, M08IvlUnhit s post i := fun i hi =>
    hunhit_m08 i (fun j hj => disj_symm (((hT.2.1 t0 ht0_S).2 j hj).2 i hi))
      (by rcases hF.1 i hi with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal)
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj ⟨h1, _⟩ => by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := ((hT.2.1 t0 ht0_S).1.1 j hj).1.1; omega)
        (fun ⟨h1, _⟩ => by
          dsimp at h1; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := hAs.2.1; omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
  have hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s post (globN s "ws", 40) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s post (globN s "bs", 80) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s post (globN s "ts", 72) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_bo : globN s "bo" ≠ 0 → M08IvlUnhit s post (globN s "bo", 88) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_jr : globN s "journal_cap" ≠ 0 → M08IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz => by
    apply hu_fix; unfold fixedObjects
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hnz]
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → M08IvlUnhit s post i := fun i hi _ =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi))))
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s post i := fun i hi _ =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using rec_word_eq_of_unhit hAs.2 hF "bo" 88 (by simp [typedRecords]) hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_eq := blockOutObjects_eq_of_bo_unhit hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun h h40 => hu_bo_lst (memW s (globN s "bo" + 40), 24) (by simp [blockOutObjects, h, h40]) rfl)
    (fun h h72 => hu_bo_lst (memW s (globN s "bo" + 72), 24) (by simp [blockOutObjects, h, h72]) rfl)
  have hbal_eq := balObjects_eq_of_unhit_except hAs.2 hT hF hba_g hu_other
    ⟨ht0_no_ba, ht0_no_ad⟩ hu_bal hm0
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_eq.1, hbal_eq.1, hj_g, hjc_g]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" ∧ ofString gn.1 ≠ ofString "journal_n" := by
      revert gn hgn; decide
    rw [hg_nonHeapJn gn.1 hne.1 hne.2]
  have hF_post := fixedTyped_transfer hAs.1 hAp.1 hag hF hfix_eq
  have hrole_eq : ∀ t, journalRole post t = journalRole s t := fun t => by
    unfold journalRole
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw16 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 16) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      have hw48 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 48) (by omega) (by omega)
      have hw64 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 64) (by omega) (by omega)
      simp only [hts_g] at hw16 hw32 hw48 hw64 ⊢
      rw [hw16, hw32, hw48, hw64]
  have hj_cells : ∀ i, i < globN s "journal_n" →
      memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) ∧
      memW post (globN s "journal" + 32 * i + 16) = memW s (globN s "journal" + 32 * i + 16) ∧
      memW post (globN s "journal" + 32 * i + 24) = memW s (globN s "journal" + 32 * i + 24) := by
    intro i hi
    have hcnz : globN s "journal_cap" ≠ 0 := by have := hJ.1; omega
    rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
    · exact absurd h0 hcnz
    · have hhi := (ivl_allocated_bound hAs.2 hal).2
      have hj8 : (globN s "journal") % 8 = 0 := hwords.1
      have huj := hu_jr hcnz
      have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ.1
      exact ⟨InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩,
             InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩,
             InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩⟩
  have hJ_post : JournalTyped post S := by
    unfold JournalTyped
    rw [hjc_g, hj_g]
    refine ⟨le_trans hjn_le hJ.1, hJ.2.1, ?_, fun i hi => ?_⟩
    · rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hwords⟩
    · rw [(hj_cells i (lt_of_lt_of_le hi hjn_le)).1]
      exact hJ.2.2.2 i (lt_of_lt_of_le hi hjn_le)
  have hjrs_sub : ∀ a ∈ journalRoleSlots post, a ∈ journalRoleSlots s := by
    intro a ha
    unfold journalRoleSlots at ha ⊢
    rw [hj_g] at ha
    obtain ⟨i, hi_mem, hai⟩ := List.mem_flatMap.1 ha
    have hi_lt : i < globN post "journal_n" := List.mem_range.1 hi_mem
    have hi_s : i < globN s "journal_n" := lt_of_lt_of_le hi_lt hjn_le
    obtain ⟨hc0, hc16, hc24⟩ := hj_cells i hi_s
    dsimp only at hai
    rw [hc0, hc16, hc24, hrole_eq] at hai
    exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi_s, hai⟩
  have hother_fp : ∀ u ∈ S, u ≠ t0 →
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu hne
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    exact htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
      (by have := (hfp _ ht_fp).1.2; dsimp at this; omega) (hu_other u hu hne _ ht_fp)
  have hhdr0_all : ∀ u ∈ S, hdr post u 0 = hdr s u 0 := fun u hu => by
    by_cases heq : u = t0
    · subst heq; exact hhdr0_t0
    · exact (hother_fp u hu heq).1 0 (by omega)
  have transfer_tries : ∀ Nd, TriesTypedWith s S Nd →
      TriesTypedWith post S Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
    intro Nd hTr
    have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s post (nodeIvl s n) := fun n hn => by
      have hmem : nodeIvl s n ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
      exact hunhit_m08 _ (fun j hj => (hTr.2.1 _ hmem).1 t0 ht0_S j hj)
        (Or.inr (hTr.1.1 n hn).2.1)
    have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
        ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
      intro n hn h12 hlen0 k hk
      have h264 : heapLimit ≤ 2 ^ 64 := by decide
      rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
      · exact absurd h0 hlen0
      · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
          unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
        have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; omega
        let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
        have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
          rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
        have hmem := hfr c
          (fun j hj ⟨h1, h2⟩ => by
            rw [hc_nat] at h1 h2
            have hj_al := ht0_al j hj
            have hdj := (hTr.2.1 _ hp_ne).1 t0 ht0_S j hj
            rcases hdj with d | d | d | d <;> omega)
          (fun ⟨h1, h2⟩ => by
            dsimp at h1 h2; rw [hc_nat] at h1 h2
            have hp_hp8 : (globN post "heap_ptr") % 8 = 0 := hAp.2.2.2.2.2.2.1
            have hdj := disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr hal_p)
            rcases hdj with d | d | d | d <;> dsimp at d <;> omega)
        unfold memB
        change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v post.be).toNat) =
               (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
        rw [hmem, hbe]
    obtain ⟨hNH_post, hne_eq⟩ := nodeHeap_congr_bytes hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
    refine ⟨⟨hNH_post, ?_, ?_⟩, hne_eq⟩
    · rw [hne_eq, hfix_eq]
      intro o ho
      have ho_alloc : o.2 = 0 ∨ Allocated s o := by
        unfold nodeExtents at ho
        obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
        rcases hno with rfl | rfl
        · exact Or.inr (hTr.1.1 n hn).2.1
        · unfold nodePath; split_ifs with hc
          · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
            · exact absurd h0 hc.2
            · exact Or.inr hal
          · exact Or.inl rfl
      refine ⟨fun u hu i hi => ?_, (hTr.2.1 o ho).2⟩
      by_cases hu0 : u = t0
      · subst hu0
        rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
        · exact disj_symm (disj_of_inside_left hin (disj_symm ((hTr.2.1 o ho).1 u ht0_S k hk)))
        · exact disj_of_inside_right hfresh (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp ho_alloc)
      · rw [(hother_fp u hu hu0).2] at hi
        exact (hTr.2.1 o ho).1 u hu i hi
    · intro hws_nz
      rw [hws_g] at hws_nz
      have e24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hne32 := ht0_no_ws32 hws_nz
      have hu32 := hu_other _ htS hne32
      have hwf32 := (hT.2.1 _ htS).1
      have hvals_eq := htabValues_eq_of_unhit hwf32 hu32
      obtain ⟨hhdr32, _⟩ := hother_fp _ htS hne32
      rw [hhdr32 3 (by omega)] at hi
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]; exact hr32 htS i hi
  obtain ⟨hTr_at_post, hne_at_eq⟩ := transfer_tries Nd_at hTr_at
  -- Every frame object `o ∈ frameObjects s ec` is `M08IvlUnhit`:
  have hu_fo_m08 : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, M08IvlUnhit s post o := by
    intro ec hec o ho
    exact m08_ivlUnhit_of_frameOutside hfr ht0_al1 hf_al1
      (fun j hj => (hFO_disj ec hec o ho).1 t0 ht0_S j hj)
      (disj_fresh_of_frameObject hAs.2 hAp.2 hhp (hFW_all ec hec) ho)
  have hu_ec_r11 : ∀ ec ∈ evmChain s, IvlUnhit s post (ec.1, 280) ∧ IvlUnhit s post (ec.2, 104) := by
    intro ec hec
    have hFW := hFW_all ec hec
    have h1 := hFW.1 (ec.1, 280) (by simp)
    have h2 := hFW.1 (ec.2, 104) (by simp)
    exact ⟨ivlUnhit_of_frameOutside ⟨h1.2.1, h1.2.2.1⟩ hfr ht0_al ⟨hf_al1, hf_al2⟩
             (fun j hj => (hFO_disj ec hec (ec.1, 280) (by simp [frameObjects])).1 t0 ht0_S j hj)
             (disj_fresh_of_allocated hAs.2 hAp.2 hhp (Or.inr h1.1)),
           ivlUnhit_of_frameOutside ⟨h2.2.1, h2.2.2.1⟩ hfr ht0_al ⟨hf_al1, hf_al2⟩
             (fun j hj => (hFO_disj ec hec (ec.2, 104) (by simp [frameObjects])).1 t0 ht0_S j hj)
             (disj_fresh_of_allocated hAs.2 hAp.2 hhp (Or.inr h2.1))⟩
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := frameWF_bounds hAs.2 hFW
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    refine ⟨fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (ec.1, 280) (by simp [frameObjects])) (by omega) hb1 ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (ec.2, 104) (by simp [frameObjects])) (by omega) hb2 ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects])) (by omega) hb88 ⟨by omega, by omega⟩⟩
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain; rw [hev_eq, hcc_eq]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
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
      have hfl_b : memW s logs + 8 * memW s (logs + 16) ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only [logs] at h0 hi hlen_le; omega
        · simpa [frameLogs, logs] using hb
      have hfl_8 : (memW s logs) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      have hfl_u : M08IvlUnhit s post (memW s logs, 8 * memW s (logs + 16)) :=
        hu_fo_m08 ec hec (frameLogs s ec) hfl_in
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
        hfl_u (by omega) hfl_b ⟨by dsimp only; omega, by dsimp only; omega⟩
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
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s logs + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (logs, 24) (by simp [logs])).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          have hss0 : 0 < scratchStart := by decide
          dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
        (hu_fo_m08 ec hec _ hlr_in) (by omega) hlr_b ⟨by omega, by omega⟩
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
        refine ⟨wordsOK_transfer hAs.1 hAp.1 hw_l, hag.allocated hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        have hwa_post : WordAt post (memW s logs + 8 * i) := by
          obtain ⟨_, hdom, _⟩ := hwa
          rcases hm : post.memory (BitVec.ofNat 64 (memW s logs + 8 * i)) with ⟨w⟩
          exact ⟨w, hdom_eq ▸ hdom, hm⟩
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
        exact ⟨wordsOK_transfer hAs.1 hAp.1 hle.1,
          ⟨hle.2.1.1, le_trans hle.2.1.2 hhp⟩,
          hle.2.2.1, hle.2.2.2.1,
          ⟨hle.2.2.2.2.1.1, le_trans hle.2.2.2.2.1.2 hhp⟩,
          ⟨hle.2.2.2.2.2.1.1, le_trans hle.2.2.2.2.2.1.2 hhp⟩,
          ⟨hle.2.2.2.2.2.2.1, le_trans hle.2.2.2.2.2.2.2 hhp⟩⟩
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec,
        (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hfrs_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega)]
  -- Role & table-typing assembly via `rolesOK_of_ts_nest_sub`:
  have hrec_ws_eq : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] = recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
    unfold recRoles
    by_cases h : globN s "ws" = 0
    · simp [hws_g, h]
    · have hw16 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
      simp only [hws_g] at hw16 hw32 ⊢; simp [h, hw16, hw32]
  have hrec_bs_eq : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
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
      have hw := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
      simp only [hbs_g] at hw; simp [hw]
  have hrec_ts_eq : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
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
      have hw := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) hk.1 hk.2
      simp only [hts_g] at hw; simp [hw]
  have hnest_bs_eq : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    unfold nestRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · have hw32 := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
      simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "bs" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "bs" + 32) ∈ S := by
          rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_no_bs32 h))]
  have hrecs_bal := balRecords_eq_of_unhit hT hba_g (fun hnz => by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hu_other _ hm ht0_no_ba)
  have hbal_slots_eq : (balRecords post).flatMap (fun ad => [(memW post ad, "bal.stor"), (memW post (ad + 8), "bal.reads")]) =
      (balRecords s).flatMap (fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]) := by
    rw [hrecs_bal]; apply List.flatMap_congr; intro ad had
    have had_p : ad ∈ balRecords post := by rwa [hrecs_bal]
    obtain ⟨e0, e8, _⟩ := hbal_eq.2 ad had_p
    rw [e0, e8]
  have hnest_ts_sub : ∀ a ∈ nestRoles post "ts" "ts.inner",
      a ∈ nestRoles s "ts" "ts.inner" ∨ (a.2 = "ts.inner" ∧ a ∈ journalRoleSlots s) := by
    intro a ha
    unfold nestRoles at ha ⊢
    rw [hts_g] at ha
    by_cases h : globN s "ts" = 0
    · simp [h] at ha
    · have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      simp only [hts_g] at hw32
      rw [if_neg h, hw32] at ha
      rw [if_neg h]
      by_cases h32 : memW s (globN s "ts" + 32) = 0
      · rw [if_pos h32] at ha; cases ha
      · rw [if_neg h32] at ha ⊢
        have hmS : memW s (globN s "ts" + 32) ∈ S := by
          rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rcases ht0_ts32 with hne_ts | ⟨_, heq_ts, hval_sub⟩
        · rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (hne_ts h))] at ha
          exact Or.inl ha
        · rw [heq_ts] at ha ⊢
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ha
          rcases hval_sub v hv with hv_old | hv_jr
          · exact Or.inl (List.mem_map.2 ⟨v, hv_old, rfl⟩)
          · exact Or.inr ⟨rfl, hv_jr⟩
  obtain ⟨hRoles_evm_post, hRoles_world_post⟩ := rolesOK_of_ts_nest_sub
    hRoles hhdr0_all hfrs_eq hjrs_sub hrec_ws_eq hrec_bs_eq hrec_ts_eq
    hba_g hbia_g hbis_g hnest_bs_eq hbal_slots_eq hnest_ts_sub
  -- `TablesTyped post S`:
  have ht0_disj_other : ∀ i ∈ htabFootprint post t0,
      (∀ u ∈ S, u ≠ t0 → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects s, Disj i j) := by
    intro i hi
    rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
    · exact ⟨fun u hu hne j hj => disj_of_inside_left hin (hT.2.2.1 t0 ht0_S u hu hne.symm k hk j hj),
             fun j hj => disj_of_inside_left hin (((hT.2.1 t0 ht0_S).2 k hk).2 j hj)⟩
    · exact ⟨fun u hu _ j hj => disj_symm (disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr ((hT.2.1 u hu).2 j hj).1))),
             fun j hj => disj_symm (disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp
                  (by rcases hF.1 j hj with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal)))⟩
  have hT_post : TablesTyped post S := by
    have hT0 := hT
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq.2, hRoles_world_post⟩
    · intro u hu
      by_cases heq : u = t0
      · subst heq; rw [hfix_eq]
        exact ⟨hwf_t0, fun i hi => ⟨(hfp_t0 i hi).1, (ht0_disj_other i hi).2⟩⟩
      · rw [(hother_fp u hu heq).2, hfix_eq]
        exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_other u hu heq),
          fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, ((htwf u hu).2 i hi).2⟩⟩
    · intro u hu v hv hne i hi j hj
      by_cases hu0 : u = t0
      · subst hu0; rw [(hother_fp v hv hne.symm).2] at hj
        exact (ht0_disj_other i hi).1 v hv hne.symm j hj
      · by_cases hv0 : v = t0
        · subst hv0; rw [(hother_fp u hu hu0).2] at hi
          exact disj_symm ((ht0_disj_other j hj).1 u hu hu0 i hi)
        · rw [(hother_fp u hu hu0).2] at hi; rw [(hother_fp v hv hv0).2] at hj
          exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz
      rw [hws_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) hk8.1 hk8.2]
      exact htsR k hk hnz
    · intro g hg_mem
      have hne : ofString g ≠ ofString "heap_ptr" ∧ ofString g ≠ ofString "journal_n" := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg_mem
        rcases hg_mem with rfl | rfl | rfl <;> decide
      rw [hg_nonHeapJn g hne.1 hne.2]; exact hgR g hg_mem
    · intro hnz hmem
      rw [hbs_g] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (ht0_no_bs32 hnz)) (fun _ hx => hx) (hbsN hnz hmem)
    · intro hnz hmem
      rw [hts_g] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      rcases ht0_ts32 with hne_ts | ⟨_, heq_ts, hval_sub⟩
      · exact htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hne_ts hnz)) (fun _ hx => hx) (htsN hnz hmem)
      · rw [heq_ts] at hmem ⊢
        intro idx hidx
        have hmem_vals : nodeF post (hdr post t0 5) (memW post (hdr post t0 6 + 8 * idx)) 8 ∈ htabValues post t0 :=
          List.mem_map.2 ⟨idx, List.mem_range.2 hidx, rfl⟩
        rcases hval_sub _ hmem_vals with hv_old | hv_jr
        · obtain ⟨j, hj_mem, hvj⟩ := List.mem_map.1 hv_old
          rw [← hvj]
          have hts_in := htsN hnz (heq_ts ▸ ht0_S)
          rw [heq_ts] at hts_in
          exact hts_in j (List.mem_range.1 hj_mem)
        · exact (hRoles.1 _ (List.mem_append_right _ hv_jr)).1
    · intro ad had
      have had_s : ad ∈ balRecords s := by rwa [← hrecs_bal]
      obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq.2 ad had
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
  have hW_post : WorldTyped post S := ⟨hT_post, hJ_post, hF_post, Nd_at, hTr_at_post⟩
  -- `DelExclusive post S (evmChain s) i u → DelExclusive s S (evmChain s) i u`:
  -- Every world table ref of `s` EXCEPT possibly the popped journal entries (`journal_n post .. journal_n s`)
  -- and any deleted `ts+32` entry... WAIT!
  -- Look at `MarksOK`: for ANY `u ∈ S`, `hMarks i hi` in `s` says:
  -- `(u ∈ (ch.take (i+1)).map (+136) ∧ DelExclusive s S ch i u) ∨ (∀ o ∈ htabFootprint s u, Inside o sourceBase heapLimit ∨ Inside o m scratchEnd)`.
  -- If `u = t0`: `ht0_not_delEx i hi` rules out the left disjunct in `s`! So `t0`'s old footprint was in heap or `[m, scratchEnd]`, and its fresh allocations are in `[heap_ptr, post.heap_ptr] ⊆ [sourceBase, heapLimit]`, so `t0` satisfies the RIGHT disjunct in `post`!
  -- What if `u ≠ t0` and `u` satisfied `DelExclusive s S ch i u` in `s`?!
  -- Then `u` is a `"frame.del"` table of frame `j ≤ i` (`u = memW s (ch[j].1 + 136)` AND `u ∉ worldTableRefs s S`)!
  -- Could `u` suddenly ENTER `worldTableRefs post S`?!
  -- Check `worldTableRefs post S`:
  -- - `ws`, `bs`, `ts` slots: unchanged!
  -- - `globalTableRoots`: unchanged!
  -- - `nest "bs"`: unchanged!
  -- - `balRecords`: unchanged!
  -- - `journal` `0 .. post.journal_n`: SUBSET of `0 .. s.journal_n`!
  -- - `nest "ts"`: if `t0 = ts+32`, any NEW element `v` of `htabValues post t0` has `(v, "ts.inner") ∈ journalRoleSlots s`!
  --   Could `u` have `(u, "ts.inner") ∈ journalRoleSlots s` AND `u = memW s (ch[j].1 + 136)`?!
  --   If `u = 0`: `0 ∉ S` (every `u ∈ S` has `sourceBase ≤ u` by `HtabWF`), so `u ≠ 0`!
  --   Since `u = memW s (ch[j].1 + 136)` with `j < ch.length`, `(u, "frame.del") ∈ frameRoleSlots s ch`!
  --   By `hRoles.2.2` (`RolesOK`), `(u, "ts.inner") ∈ journalRoleSlots s` and `(u, "frame.del") ∈ frameRoleSlots s ch` would force `"ts.inner" = "frame.del"`, IMPOSSIBLE!
  --   SO `u ∉ worldTableRefs post S`, AND `DelExclusive post S ch i u` HOLDS!!
  have hdelEx_imp : ∀ (i : Nat) (hi : i + 1 < (evmChain s).length) (u : Nat),
      u ∈ S → u ∈ ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) →
      DelExclusive s S (evmChain s) i u →
      DelExclusive post S (evmChain s) i u := by
    intro i hi u huS hu_take ⟨hu_not_wref, hu_frames⟩
    have hu_pos : 0 < u := by
      have := ((hT.2.1 u huS).1.1 (u, 88) (by simp [htabFootprint])).1.1
      have hsb : 0 < sourceBase := by decide
      dsimp at this; omega
    obtain ⟨ec_u, hec_take, hu_eq136⟩ := List.mem_map.1 hu_take
    have hec_mem : ec_u ∈ evmChain s := List.mem_of_mem_take hec_take
    have hu_frs : (u, "frame.del") ∈ frameRoleSlots s (evmChain s) := by
      unfold frameRoleSlots; rw [← hu_eq136]
      exact List.mem_flatMap.2 ⟨ec_u, hec_mem, by simp⟩
    refine ⟨?_, ?_⟩
    · intro hw_post
      apply hu_not_wref
      unfold worldTableRefs recordSlots at hw_post ⊢
      rw [hws_g, hbs_g, hts_g,
          show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
            simp only [globalTableRoots, List.map, hba_g, hbia_g, hbis_g],
          hrecs_bal, hj_g] at hw_post
      have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
          (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
          simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega
        simpa [hws_g] using rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) hk8.1 hk8.2
      have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
          (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
          simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        simpa [hbs_g] using rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) hk8.1 hk8.2
      have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
          (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        simpa [hts_g] using rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) hk8.1 hk8.2
      have hnest_bs_w : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
          (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
        by_cases hnz : globN s "bs" = 0
        · simp [hnz]
        · have ew := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
          simp only [hbs_g] at ew; rw [ew]
          by_cases hmS : memW s (globN s "bs" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_no_bs32 hnz))]
          · simp [hnz, hmS]
      have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
          (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
        apply List.flatMap_congr; intro ad had
        have had_p : ad ∈ balRecords post := by rwa [hrecs_bal]
        obtain ⟨e0, e8, _⟩ := hbal_eq.2 ad had_p
        rw [e0, e8]
      dsimp only at hw_post ⊢
      rw [hbs_g, hts_g, hws_sl, hbs_sl, hts_sl, hnest_bs_w, hbal_fl] at hw_post
      -- Split `hw_post` into the 7 pieces:
      rcases List.mem_append.1 hw_post with hw16 | hw_jr
      · rcases List.mem_append.1 hw16 with hw15 | hw_bal
        · rcases List.mem_append.1 hw15 with hw14 | hw_nts
          · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw14))
          · -- `u ∈ nest "ts"` in `post`:
            by_cases hts0 : globN s "ts" = 0
            · simp [hts0] at hw_nts
            · have ew := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hts0 (hu_ts hts0) (k := 32) (by omega) (by omega)
              simp only [hts_g] at ew; rw [ew] at hw_nts
              by_cases hmS : memW s (globN s "ts" + 32) ∈ S
              · simp only [hts0, ne_eq, not_false_eq_true, hmS, and_self, ↓reduceIte] at hw_nts ⊢
                rcases ht0_ts32 with hne_ts | ⟨_, heq_ts, hval_sub⟩
                · rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (hne_ts hts0))] at hw_nts
                  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp [hts0, hmS, hw_nts])))
                · rw [heq_ts] at hw_nts
                  rcases hval_sub u hw_nts with hu_old | hu_jr
                  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp [hts0, hmS, heq_ts, hu_old])))
                  · exfalso
                    have heq_r : ("ts.inner" : String) = "frame.del" :=
                      hRoles.2.2 (u, "ts.inner") hu_jr (u, "frame.del")
                        (List.mem_append_left _ (List.mem_append_right _ hu_frs)) rfl
                    exact absurd heq_r (by decide)
              · simp [hts0, hmS] at hw_nts
        · exact List.mem_append_left _ (List.mem_append_right _ hw_bal)
      · obtain ⟨k, hk_mem, huk⟩ := List.mem_map.1 hw_jr
        have hk_s : k < globN s "journal_n" := lt_of_lt_of_le (List.mem_range.1 hk_mem) hjn_le
        rw [(hj_cells k hk_s).1] at huk
        exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk_s, huk⟩)
    · intro j hj k hk hmem_eq
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_le : k + 8 ≤ 280 ∧ k % 8 = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [(hrec_eq _ hj_mem).1 k hk_le.1 hk_le.2] at hmem_eq
      exact hu_frames j hj k hk hmem_eq
  -- Assemble `evmR post = evmR s`:
  have hR_eq : evmR post = evmR s := by
    unfold evmR; rw [hchain_eq]
    congr 1; apply List.map_congr_left; intro ec hec
    rw [(hrec_eq ec hec).1 64 (by omega) (by omega), (hrec_eq ec hec).1 192 (by omega) (by omega)]
  have hmap_gas : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
      apply List.map_congr_left; intro ec hec
      rw [(hrec_eq ec hec).1 64 (by decide) (by decide), (hrec_eq ec hec).1 192 (by decide) (by decide)]
  refine ⟨⟨hW_post, ?_⟩, hchain_eq, hR_eq, hu_ec_r11⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, hmap_fo_eq ▸ hFO_pw, ?_, ?_, ?_, hRoles_evm_post, hmap_gas ▸ hGas⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega)]
      obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
      obtain ⟨hTr_m_post, hne_m_eq⟩ := transfer_tries Nd_m hTr_m
      refine ⟨hag.allocated hal_m, wordsOK_transfer hAs.1 hAp.1 hw_m, ?_, ?_, ?_, Nd_m, hTr_m_post, ?_⟩
      · intro u hu i hi
        by_cases hu0 : u = t0
        · subst hu0
          rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
          · exact disj_symm (disj_of_inside_left hin (disj_symm (hdt u ht0_S k hk)))
          · exact disj_of_inside_right hfresh (disj_fresh_of_allocated hAs.2 hAp.2 hhp hal_m)
        · rw [(hother_fp u hu hu0).2] at hi; exact hdt u hu i hi
      · rw [hfix_eq]; exact hdf
      · rw [hchain_eq]; intro ec' hec' o ho; rw [hframeObjects_eq ec' hec'] at ho; exact hdfo ec' hec' o ho
      · intro o ho j hj; rw [hne_m_eq] at hj; exact hdj_m o ho j hj
    unfold FrameWF; dsimp only
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
        he_eq 40 (by omega) (by omega), he_eq 16 (by omega) (by omega),
        he_eq 32 (by omega) (by omega), he_eq 136 (by omega) (by omega),
        he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec, he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
        hframeRet_eq ec hec, hsc_eq, hfm_eq, hevm_empty_eq]
    rw [he_eq 88 (by omega) (by omega)] at hlo_ok
    refine ⟨fun i hi => ⟨(c1 i hi).1, wordsOK_transfer hAs.1 hAp.1 (c1 i hi).2⟩,
      c2, wordsOK_transfer hAs.1 hAp.1 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
      ?_, wordsOK_transfer hAs.1 hAp.1 c14, ?_, hlo_ok, hmsg_ok⟩
    · rcases c13 with h | h
      · exact Or.inl ⟨h.1, le_trans h.2 hhp⟩
      · exact Or.inr h
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨⟨hin.1, le_trans hin.2 hhp⟩, wordsOK_transfer hAs.1 hAp.1 hw⟩
  · intro ec hec
    have hec_mem := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_eq ec hec_mem).1 16 (by omega) (by omega), (hrec_eq ec hec_mem).1 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_eq _ hi0).2.1 80 (by decide) (by decide),
        (hrec_eq _ hi0).2.1 72 (by decide) (by decide),
        (hrec_eq _ hi1).1 40 (by decide) (by decide)]
    exact hRW i hi
  · intro ec hec o ho
    have ho_s : o ∈ frameObjects s ec := by rwa [← hframeObjects_eq ec hec]
    rw [hfix_eq]
    refine ⟨fun u hu i hi => ?_, (hFO_disj ec hec o ho_s).2⟩
    by_cases hu0 : u = t0
    · subst hu0
      rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
      · exact disj_symm (disj_of_inside_left hin (disj_symm ((hFO_disj ec hec o ho_s).1 u ht0_S k hk)))
      · exact disj_of_inside_right hfresh (disj_fresh_of_frameObject hAs.2 hAp.2 hhp (hFW_all ec hec) ho_s)
    · rw [(hother_fp u hu hu0).2] at hi; exact (hFO_disj ec hec o ho_s).1 u hu i hi
  · rw [hmap_fo_eq]
    refine ⟨Nd_at, hTr_at_post, fun o ho j hj => ?_⟩
    rw [hne_at_eq] at hj; exact hAT_at o ho j hj
  · intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
    have hM := hMarks i hi
    dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfix_eq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by omega)]
      exact m5 j hj hij
    · intro u hu
      by_cases hu0 : u = t0
      · subst hu0; right
        rcases m8 u ht0_S with ⟨_, hdel⟩ | hloc
        · exact absurd hdel (ht0_not_delEx i hi)
        · intro o ho
          rcases (hfp_t0 o ho).2 with ⟨k, hk, hin⟩ | hfresh
          · rcases hloc k hk with hh | hm
            · exact Or.inl ⟨le_trans hh.1 hin.1, le_trans hin.2 hh.2⟩
            · exact Or.inr ⟨le_trans hm.1 hin.1, le_trans hin.2 hm.2⟩
          · exact Or.inl ⟨le_trans hAs.2.1 hfresh.1,
              le_trans hfresh.2 (by rw [Nat.add_sub_of_le hhp]; exact hAp.2.2.1)⟩
      · rw [(hother_fp u hu hu0).2]
        rcases m8 u hu with ⟨htake, hdel⟩ | hloc
        · exact Or.inl ⟨htake, hdelEx_imp i hi u hu htake hdel⟩
        · exact Or.inr hloc

end InitECandidate.Solver.Wave8GuestInv.R16Shards
