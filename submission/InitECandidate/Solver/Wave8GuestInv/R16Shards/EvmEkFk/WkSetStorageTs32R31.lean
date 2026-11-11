import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockAuxLeaves
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2c1JournalAppend

/-!
# R31 Helper 1/2: `ts+32` Fresh `ts.inner` Outer Insertion & `WorldStepIn` Composition

Provides:
1. `ts32_world_typed_r31`, `ts32_owned_grows_r31`, `ts32_worldStepIn_r31`, `ts32_outer_kept_r31`,
   `ts32_nestRoles_provenance_r31`
2. `worldStepIn_mono_bufs_r31`, `worldStepIn_with_locals_clock_r31`, `worldStepIn_of_pre_locals_clock_r31`,
   `worldStepSc_trans_owned_r31`, `worldStepIn_trans_stepSc_r31`, `worldStepIn_trans_owned_r31`
3. `nonTrieStep_preserves_fresh_slot_r31`, `journal_append_wrs_and_hdr_r31`
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
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

/-! ## 1. `ts+32` Fresh `ts.inner` Outer-Table Insertion -/

theorem ts32_outer_kept_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (hts : globN s "ts" ≠ 0) :
    globN post "ts" = globN s "ts" ∧
    memW post (globN post "ts" + 32) = memW s (globN s "ts" + 32) := by
  have hg : globN post "ts" = globN s "ts" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "ts") (by decide))
  have hm := typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords])
  simp only [hts, ↓reduceIte] at hm
  have hu := merge_set_fixed_unhit hA hW ht he _ hm (by simp)
  exact ⟨hg, rec_word_eq_of_unhit hA.2 hW.2.2.1 "ts" 72
    (by simp [typedRecords]) hg hts hu (by decide) (by decide)⟩

theorem ts32_nestRoles_provenance_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {t inner : Nat}
    (hts : globN s "ts" ≠ 0) (ht : t = memW s (globN s "ts" + 32))
    (ht0 : t ≠ 0) (hg : globN post "ts" = globN s "ts")
    (hp : memW post (globN post "ts" + 32) = t)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    (inner, "ts.inner") ∈ nestRoles post "ts" "ts.inner" ∧
    ∀ a ∈ nestRoles post "ts" "ts.inner",
      a ∈ nestRoles s "ts" "ts.inner" ∨ a = (inner, "ts.inner") := by
  have hpost : nestRoles post "ts" "ts.inner" =
      (htabValues post t).map (fun v => (v, "ts.inner")) := by
    have htpost : globN post "ts" ≠ 0 := by rwa [hg]
    simp [nestRoles, htpost, hp, ht0]
  have hpre : nestRoles s "ts" "ts.inner" =
      (htabValues s t).map (fun v => (v, "ts.inner")) := by
    simp [nestRoles, hts, ← ht, ht0]
  rw [hpost, hpre]
  refine ⟨List.mem_map.2 ⟨inner, (merge_set_values_membership hv).1, rfl⟩, ?_⟩
  intro a ha
  obtain ⟨v, hv', rfl⟩ := List.mem_map.1 ha
  rcases (merge_set_values_membership hv).2 v hv' with hold | heq
  · exact Or.inl (List.mem_map.2 ⟨v, hold, rfl⟩)
  · exact Or.inr (by rw [heq])

theorem ts32_roles_replace_inner_r31 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} {pre old new suf jr : List (Nat × String)} {inner : Nat}
    (h : RolesOK s S (pre ++ old ++ suf) jr)
    (hi : inner ∈ S) (hk : hdr s inner 0 = roleKeyLen "ts.inner")
    (hf : ∀ a ∈ (pre ++ old ++ suf) ++ jr, a.1 ≠ inner)
    (hp : ∀ a ∈ new, a ∈ old ∨ a = (inner, "ts.inner"))
    (hr : ∀ a ∈ new, a.2 = "ts.inner") :
    RolesOK s S (pre ++ new ++ suf) jr := by
  have hold : ∀ a ∈ old, a ∈ pre ++ old ++ suf := by
    intro a ha; simp only [List.mem_append]; exact Or.inl (Or.inr ha)
  have hpre : ∀ a ∈ pre, a ∈ pre ++ old ++ suf := by
    intro a ha; simp only [List.mem_append]; exact Or.inl (Or.inl ha)
  have hsuf : ∀ a ∈ suf, a ∈ pre ++ old ++ suf := by
    intro a ha; exact List.mem_append_right _ ha
  have hprov : ∀ a ∈ pre ++ new ++ suf,
      a ∈ pre ++ old ++ suf ∨ a = (inner, "ts.inner") := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact Or.inl (hpre a ha)
      · exact (hp a ha).imp (hold a) id
    · exact Or.inl (hsuf a ha)
  have hpair := List.pairwise_append.1 h.2.1
  have hleft := List.pairwise_append.1 hpair.1
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases hprov a ha with ha | rfl
      · exact h.1 a (List.mem_append_left _ ha)
      · exact ⟨hi, hk⟩
    · exact h.1 a (List.mem_append_right _ ha)
  · apply List.pairwise_append.2
    refine ⟨List.pairwise_append.2 ⟨hleft.1, ?_, ?_⟩, hpair.2.1, ?_⟩
    · have hall : ∀ l : List (Nat × String), (∀ a ∈ l, a.2 = "ts.inner") →
          l.Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := by
        intro l
        induction l with
        | nil => simp
        | cons a l ih =>
          intro hh
          apply List.pairwise_cons.2
          refine ⟨?_, ih (fun b hb => hh b (List.mem_cons_of_mem _ hb))⟩
          intro b hb heq
          have ha := hh a List.mem_cons_self
          have hb' := hh b (List.mem_cons_of_mem _ hb)
          exact ⟨ha.trans hb'.symm, by rw [ha]; simp [sharedRoles]⟩
      exact hall new hr
    · intro a ha b hb heq
      rcases hp b hb with hb | rfl
      · exact hleft.2.2 a ha b hb heq
      · exact False.elim (hf a (List.mem_append_left _ (hpre a ha)) heq)
    · intro a ha b hb heq
      rcases List.mem_append.1 ha with ha | ha
      · exact hpair.2.2 a (List.mem_append_left _ ha) b hb heq
      · rcases hp a ha with ha | rfl
        · exact hpair.2.2 a (List.mem_append_right _ ha) b hb heq
        · exact False.elim (hf b (List.mem_append_left _ (hsuf b hb)) heq.symm)
  · intro a ha b hb heq
    rcases List.mem_append.1 hb with hb | hb
    · rcases hprov b hb with hb | rfl
      · exact h.2.2 a ha b (List.mem_append_left _ hb) heq
      · exact False.elim (hf a (List.mem_append_right _ ha) heq)
    · exact h.2.2 a ha b (List.mem_append_right _ hb) heq

theorem ts32_roles_transport_inner_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {pre suf jr : List (Nat × String)} {t inner : Nat}
    (h : RolesOK s S (pre ++ (nestRoles s "ts" "ts.inner").filter
      (fun a => a.1 != 0) ++ suf) jr)
    (hi : inner ∈ S) (hk : hdr s inner 0 = roleKeyLen "ts.inner")
    (hf : ∀ a ∈ (pre ++ (nestRoles s "ts" "ts.inner").filter
      (fun a => a.1 != 0) ++ suf) ++ jr, a.1 ≠ inner)
    (hh : ∀ u ∈ S, hdr post u 0 = hdr s u 0)
    (hts : globN s "ts" ≠ 0) (ht : t = memW s (globN s "ts" + 32))
    (ht0 : t ≠ 0) (hg : globN post "ts" = globN s "ts")
    (hp : memW post (globN post "ts" + 32) = t)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    RolesOK post S (pre ++ (nestRoles post "ts" "ts.inner").filter
      (fun a => a.1 != 0) ++ suf) jr := by
  have hprov := (ts32_nestRoles_provenance_r31 hts ht ht0 hg hp hv).2
  have hnew := ts32_roles_replace_inner_r31 h hi hk hf
    (new := (nestRoles post "ts" "ts.inner").filter (fun a => a.1 != 0))
    (by
      intro a ha
      obtain ⟨ha, hn⟩ := List.mem_filter.1 ha
      rcases hprov a ha with ha | ha
      · exact Or.inl (List.mem_filter.2 ⟨ha, hn⟩)
      · exact Or.inr ha)
    (by
      intro a ha
      have ha := (List.mem_filter.1 ha).1
      unfold nestRoles at ha
      split at ha
      · simp at ha
      · split at ha
        · simp at ha
        · obtain ⟨v, _, rfl⟩ := List.mem_map.1 ha
          rfl)
  refine ⟨?_, hnew.2⟩
  intro a ha
  obtain ⟨hm, hk'⟩ := hnew.1 a ha
  exact ⟨hm, (hh a.1 hm).trans hk'⟩

theorem ts32_bs_nestRoles_kept_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hts : globN s "ts" ≠ 0) (ht0 : t ≠ 0)
    (htts : t = memW s (globN s "ts" + 32)) :
    nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
  have hdisj := ts32Slot_disj s S hW.1 hts (htts ▸ ht0)
  apply merge_set_other_nestRoles_kept hA hW ht he "bs" "bs.inner" 80
    (by simp [typedRecords]) (by decide) (by decide)
  · exact hW.1.2.2.2.2.1 32 (by simp [bsTableSlots])
  · intro hbs _
    rw [htts]
    exact hdisj.2.1 hbs

theorem ts32_balRecords_kept_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hts : globN s "ts" ≠ 0) (ht0 : t ≠ 0)
    (htts : t = memW s (globN s "ts" + 32)) :
    balRecords post = balRecords s := by
  have hdisj := ts32Slot_disj s S hW.1 hts (htts ▸ ht0)
  apply merge_set_balRecords_kept hA hW ht he
  rw [htts]
  exact hdisj.2.2.1

theorem ts32_bal_roles_kept_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hts : globN s "ts" ≠ 0) (ht0 : t ≠ 0)
    (htts : t = memW s (globN s "ts" + 32)) :
    (balRecords post).flatMap (fun ad =>
      [(memW post ad, "bal.stor"), (memW post (ad + 8), "bal.reads")]) =
    (balRecords s).flatMap (fun ad =>
      [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]) := by
  rw [ts32_balRecords_kept_r31 hA hW ht he hts ht0 htts]
  apply List.flatMap_congr
  intro ad had
  have h0 := merge_set_bal_record_fields_kept hA hW ht he had 0 (by decide) (by decide)
  have h8 := merge_set_bal_record_fields_kept hA hW ht he had 8 (by decide) (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0, h8]

theorem ts32_bal_objects_kept_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hts : globN s "ts" ≠ 0) (ht0 : t ≠ 0)
    (htts : t = memW s (globN s "ts" + 32)) :
    balObjects post = balObjects s ∧
    (∀ ad ∈ balRecords post, memW post ad = memW s ad ∧
      memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  have hdisj := ts32Slot_disj s S hW.1 hts (htts ▸ ht0)
  apply R16WkMarkAccountCreated.balObjects_eq_of_unhit_except hA.2 hW.1 hW.2.2.1
    (globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bal_accounts") (by decide)))
    (merge_set_other_table_unhit hA hW ht he)
  · rw [htts]
    exact ⟨hdisj.2.2.1, hdisj.2.2.2.1⟩
  · intro i hi _
    have hm : i ∈ fixedObjects s := List.mem_append_right _ hi
    exact merge_set_fixed_word_unhit hA hW ht he i hm
  · exact merge_set_low_words_kept hA hW ht he

theorem ts32_fixed_typed_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hts : globN s "ts" ≠ 0) (ht0 : t ≠ 0)
    (htts : t = memW s (globN s "ts" + 32)) :
    fixedObjects post = fixedObjects s ∧ FixedTyped post := by
  have hgs := InitECandidate.Solver.Wave8Contracts.M08.worldGlobalsSame_of_kept
    (gw := ["heap_ptr"]) he.2.2.2.2.2.2.2 (fun _ h => Or.inl (by simpa using h))
  have hb := (merge_set_blockOutObjects_kept hA hW ht he).1
  have hbal := (ts32_bal_objects_kept_r31 hA hW ht he hts ht0 htts).1
  have hf := InitECandidate.Solver.Wave8Contracts.M08.fixedObjects_eq_of_parts hgs hb hbal
  have hag : AllocatorGrows s post := by
    refine ⟨he.2.2.2.2.1, ?_⟩
    rw [globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "scratch_ptr") (by decide))]
  exact ⟨hf, InitECandidate.Solver.Wave8Contracts.M08.fixedTyped_transfer
    hA.1 he.1.1 hag hW.2.2.1 hf⟩

theorem ts32_world_roles_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t inner : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hts : globN s "ts" ≠ 0) (ht0 : t ≠ 0)
    (htts : t = memW s (globN s "ts" + 32))
    (hi : inner ∈ S) (hk : hdr s inner 0 = roleKeyLen "ts.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ inner)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    RolesOK post S (worldRoleSlots post) (journalRoleSlots post) := by
  have hj := (merge_set_journal_kept hA hW ht he).1
  have hws := merge_set_recRoles_kept hA hW ht he "ws" 40
    [(16, "ws+16"), (32, "ws+32")] (by simp [typedRecords]) (by decide)
    (by decide) (by decide)
  have hbr := merge_set_recRoles_kept hA hW ht he "bs" 80
    [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")]
    (by simp [typedRecords]) (by decide) (by decide) (by decide)
  have htr := merge_set_recRoles_kept hA hW ht he "ts" 72
    [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]
    (by simp [typedRecords]) (by decide) (by decide) (by decide)
  have hba : globN post "bal_accounts" = globN s "bal_accounts" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bal_accounts") (by decide))
  have hbi : globN post "bal_idx_accts" = globN s "bal_idx_accts" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bal_idx_accts") (by decide))
  have hbj : globN post "bal_idx_stor" = globN s "bal_idx_stor" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bal_idx_stor") (by decide))
  have hbn := ts32_bs_nestRoles_kept_r31 hA hW ht he hts ht0 htts
  have hbal := ts32_bal_roles_kept_r31 hA hW ht he hts ht0 htts
  have hp := ts32_outer_kept_r31 hA hW ht he hts
  let pre := (recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
    recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] ++
    recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] ++
    [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"),
      (globN s "bal_idx_stor", "bal_idx_stor")] ++
    nestRoles s "bs" "bs.inner").filter (fun a => a.1 != 0)
  let suf := ((balRecords s).flatMap
    (fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")])).filter
    (fun a => a.1 != 0)
  have hpre : worldRoleSlots s = pre ++
      (nestRoles s "ts" "ts.inner").filter (fun a => a.1 != 0) ++ suf := by
    simp only [worldRoleSlots, pre, suf, List.filter_append, List.append_assoc]
  have hpost : worldRoleSlots post = pre ++
      (nestRoles post "ts" "ts.inner").filter (fun a => a.1 != 0) ++ suf := by
    simp only [worldRoleSlots, hws, hbr, htr, hba, hbi, hbj, hbn, hbal,
      pre, suf, List.filter_append, List.append_assoc]
  rw [hpost, hj]
  apply ts32_roles_transport_inner_r31 (s := s) (t := t) (inner := inner)
  · rw [← hpre]; exact hW.1.2.2.2.2.2.2.2.2.2.2.2
  · exact hi
  · exact hk
  · rwa [← hpre]
  · exact merge_set_key_lengths_kept hA hW ht he
  · exact hts
  · exact htts
  · exact ht0
  · exact hp.1
  · exact hp.2.trans htts.symm
  · exact hv

theorem ts32_tables_typed_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t inner : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hts : globN s "ts" ≠ 0) (ht0 : t ≠ 0)
    (htts : t = memW s (globN s "ts" + 32))
    (hi : inner ∈ S) (hk : hdr s inner 0 = roleKeyLen "ts.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ inner)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    TablesTyped post S := by
  have hfix := (ts32_fixed_typed_r31 hA hW ht he hts ht0 htts).1
  have hgeom := merge_set_tables_geometry hA hW ht he hfix
  have hroots := merge_set_direct_roots hA hW ht he
  have hbal := ts32_bal_objects_kept_r31 hA hW ht he hts ht0 htts
  have hdisj := ts32Slot_disj s S hW.1 hts (htts ▸ ht0)
  refine ⟨hW.1.1, hgeom.1, hgeom.2, hroots.1, hroots.2.1, hroots.2.2.1,
    hroots.2.2.2, ?_, ?_, ?_, (merge_set_blockOutObjects_kept hA hW ht he).2,
    ts32_world_roles_r31 hA hW ht he hts ht0 htts hi hk hf hv⟩
  · intro hn hu
    have hg : globN post "bs" = globN s "bs" :=
      globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bs") (by decide))
    rw [hg] at hn
    have hp := merge_set_record_word_kept hA hW ht he "bs" 80 32
      (by decide) (by decide) hn (by decide) (by decide)
    rw [hp] at hu ⊢
    have hne : memW s (globN s "bs" + 32) ≠ t := by
      rw [htts]; exact hdisj.2.1 hn
    exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit
      (hW.1.2.1 _ hu).1 (merge_set_other_table_unhit hA hW ht he _ hu hne)
      (fun _ hm => hm) (hW.1.2.2.2.2.2.2.2.1 hn hu)
  · intro _ _
    have hp := (ts32_outer_kept_r31 hA hW ht he hts).2
    rw [hp, ← htts]
    apply merge_set_values_owned hv _ hi
    rw [htts]
    exact hW.1.2.2.2.2.2.2.2.2.1 hts (htts ▸ ht)
  · intro ad had
    have hads : ad ∈ balRecords s := by
      rwa [ts32_balRecords_kept_r31 hA hW ht he hts ht0 htts] at had
    obtain ⟨e0, e8, _, hl, hll⟩ := hbal.2 ad had
    have h := hW.1.2.2.2.2.2.2.2.2.2.1 ad hads
    exact ⟨e0 ▸ h.1, e8 ▸ h.2.1, hl, hll⟩

theorem ts32_tries_typed_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (hbe : post.be = s.be)
    (hts : globN s "ts" ≠ 0) (ht0 : t ≠ 0)
    (htts : t = memW s (globN s "ts" + 32)) :
    TriesTypedWith post S Nd := by
  obtain ⟨hN, hne⟩ := merge_set_nodes_kept hA hW ht he hbe
  have hfix := (ts32_fixed_typed_r31 hA hW ht he hts ht0 htts).1
  have hdisj := ts32Slot_disj s S hW.1 hts (htts ▸ ht0)
  refine ⟨hN, ?_, ?_⟩
  · rw [hne, hfix]
    intro o ho
    refine ⟨?_, (hW.2.2.2.2.1 o ho).2⟩
    intro u hu i hi
    by_cases hut : u = t
    · subst u
      exact ((merge_set_footprint_disjoint hA hW ht he i hi).2.2 o ho).flip
    · rw [(merge_set_other_table_frame hA hW ht hu hut he).2.1] at hi
      exact (hW.2.2.2.2.1 o ho).1 u hu i hi
  · intro hn
    have hg : globN post "ws" = globN s "ws" :=
      globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "ws") (by decide))
    rw [hg] at hn
    have e24 : memW post (globN post "ws" + 24) = memW s (globN s "ws" + 24) :=
      merge_set_record_word_kept hA hW ht he "ws" 40 24
        (by decide) (by decide) hn (by decide) (by decide)
    have e32 : memW post (globN post "ws" + 32) = memW s (globN s "ws" + 32) :=
      merge_set_record_word_kept hA hW ht he "ws" 40 32
        (by decide) (by decide) hn (by decide) (by decide)
    rw [e24, e32]
    refine ⟨(hW.2.2.2.2.2 hn).1, ?_⟩
    intro hu i hi
    have hut : memW s (globN s "ws" + 32) ≠ t := by
      rw [htts]; exact hdisj.2.2.2.2.1 hn
    have hh := (merge_set_other_table_frame hA hW ht hu hut he).2.2
    have hv := merge_set_other_values_kept hA hW ht hu hut he
    rw [hh 3 (by decide)] at hi
    have hget := congrArg (fun l : List Nat => l[i]?) hv
    simp only [htabValues, List.getElem?_map, List.getElem?_range,
      hh 3 (by decide), hi, Option.map_some, Option.some.injEq] at hget
    rw [hget]
    exact (hW.2.2.2.2.2 hn).2 hu i hi

theorem ts32_world_typed_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t inner : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (hbe : post.be = s.be)
    (hts : globN s "ts" ≠ 0) (ht0 : t ≠ 0)
    (htts : t = memW s (globN s "ts" + 32))
    (hi : inner ∈ S) (hk : hdr s inner 0 = roleKeyLen "ts.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ inner)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    WorldTypedWith post S Nd :=
  ⟨ts32_tables_typed_r31 hA hW ht he hts ht0 htts hi hk hf hv,
   (merge_set_journal_kept hA hW ht he).2,
   (ts32_fixed_typed_r31 hA hW ht he hts ht0 htts).2,
   ts32_tries_typed_r31 hA hW ht he hbe hts ht0 htts⟩

theorem ts32_owned_grows_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (hbe : post.be = s.be)
    (hts : globN s "ts" ≠ 0) (ht0 : t ≠ 0)
    (htts : t = memW s (globN s "ts" + 32)) :
    OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) := by
  have hfix := (ts32_fixed_typed_r31 hA hW ht he hts ht0 htts).1
  have hnodes := (merge_set_nodes_kept hA hW ht he hbe).2
  intro o ho
  unfold worldOwned at ho
  rcases List.mem_append.1 ho with ho | ho
  · rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨u, hu, hi⟩ := List.mem_flatMap.1 ho
      by_cases hut : u = t
      · subst u
        rcases (he.2.2.2.2.2.1 o hi).2 with ⟨j, hj, hin⟩ | hin
        · exact Or.inr (Or.inl ⟨j, List.mem_append_left _
            (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hj⟩)), hin⟩)
        · exact Or.inr (Or.inr ⟨hin.1, by
            have hh := he.2.2.2.2.1
            dsimp [Inside] at hin ⊢
            omega⟩)
      · rw [(merge_set_other_table_frame hA hW ht hu hut he).2.1] at hi
        exact Or.inr (Or.inl ⟨o, List.mem_append_left _
          (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hi⟩)), le_rfl, le_rfl⟩)
    · rw [hfix] at ho
      exact Or.inr (Or.inl ⟨o, List.mem_append_left _
        (List.mem_append_right _ ho), le_rfl, le_rfl⟩)
  · rw [hnodes] at ho
    exact Or.inr (Or.inl ⟨o, List.mem_append_right _ ho, le_rfl, le_rfl⟩)

theorem ts32_worldStepIn_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {t inner : Nat} {S Nd : List Nat}
    (hA : ArenaReady s) (hw : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (hbe : post.be = s.be)
    (hts : globN s "ts" ≠ 0) (ht0 : t ≠ 0)
    (htts : t = memW s (globN s "ts" + 32))
    (hk : hdr s inner 0 = roleKeyLen "ts.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ inner)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    WorldStepIn (fun _ => [t, inner]) (bufRegions []) ["heap_ptr"] stdKeep NoExtra s r post ∧
      globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
      (inner ≠ 0 → (inner, "ts.inner") ∈ worldRoleSlots post) := by
  have hsp : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "scratch_ptr") (by decide))
  have hp := ts32_outer_kept_r31 hA hw ht he hts
  have hmem_nest := (ts32_nestRoles_provenance_r31 hts htts ht0 hp.1
    (hp.2.trans htts.symm) hv).1
  refine ⟨⟨he.1, he.2.2.2.2.1, he.2.2.2.2.2.2.2, ?_, ?_⟩, by rw [hsp], ?_⟩
  · intro rec hrec hn k hks _
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧
        ofString rec.1 ≠ ofString "heap_ptr" ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, by decide, ?_⟩; simp at hks; omega
      · refine ⟨80, by decide, by decide, ?_⟩; simp at hks; omega
      · refine ⟨72, by decide, by decide, ?_⟩; simp at hks; omega
      · refine ⟨88, by decide, by decide, ?_⟩; simp at hks; omega
    obtain ⟨sz, hrec, hg, hk8, hbound⟩ := hrec_sz
    have hh := merge_set_record_word_kept hA hw ht he rec.1 sz k hrec hg hn hk8 hbound
    rwa [globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString rec.1)
      (by simpa using hg))] at hh
  · intro S' Nd' hw' howned _
    have ht' : t ∈ S' := howned t (by simp)
    have hi' : inner ∈ S' := howned inner (by simp)
    refine ⟨S', Nd', fun _ h => h,
      ts32_world_typed_r31 hA hw' ht' he hbe hts ht0 htts hi' hk hf hv,
      ts32_owned_grows_r31 hA hw' ht' he hbe hts ht0 htts, ?_, trivial⟩
    intro a hkeep hfree
    apply he.2.2.2.2.2.2.1 a
    · intro j hj hh
      apply hkeep j _ hh
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.2 ⟨t, ht', hj⟩))
    · intro hh
      apply hfree
      have hpmax := he.1.2.2.1
      obtain ⟨h1, h2⟩ := hh
      unfold heapFree CellHits at *
      dsimp at h1 h2 ⊢
      omega
  · intro hnz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [hnz]⟩
    exact List.mem_append_left _ (List.mem_append_right _ hmem_nest)

/-! ## 2. `WorldStepSc` Composition with Guarded `WorldStepIn` -/

theorem worldStepIn_mono_bufs_r31
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {F : Type} {B1 B2 : BufList} {gw1 gw2 : List String}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : ∀ p ∈ B1, p ∈ B2) (hgw : ∀ g ∈ gw1, g ∈ gw2)
    (h : WorldStepIn T (bufRegions B1) gw1 stdKeep NoExtra s r post) :
    WorldStepIn T (bufRegions B2) gw2 stdKeep NoExtra s r post := by
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := h
  have hsubR : ∀ i ∈ bufRegions B1 s, i ∈ bufRegions B2 s := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
    exact List.mem_map.2 ⟨p, hB p hp, rfl⟩
  refine ⟨hAp, hhp, ?_, ?_, ?_⟩
  · intro k hk
    apply hG k
    intro hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk (List.mem_map.2 ⟨g, hgw g hg, rfl⟩)
  · intro rec hrec hnz k hk hno
    exact hK rec hrec hnz k hk (fun i hi => hno i (hsubR i hi))
  · intro S Nd hWT hT hD
    have hD1 : IvlsDisj (bufRegions B1 s) (worldTypedIvls s S Nd) :=
      fun i hi j hj => hD i (hsubR i hi) j hj
    obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hW S Nd hWT hT hD1
    refine ⟨S', Nd', hsub, hWT', hOG, ?_, trivial⟩
    intro a ha hhf
    apply hFO a _ hhf
    intro i hi
    rcases List.mem_append.1 hi with hi1 | hfg
    · rcases List.mem_append.1 hi1 with hwo | hR1
      · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo))
      · exact ha i (List.mem_append_left _ (List.mem_append_right _ (hsubR i hR1)))
    · exact ha i (List.mem_append_right _ hfg)

theorem worldStepIn_with_locals_clock_r31
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {F : Type} {B : BufList} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : WorldStepIn T (bufRegions B) gw stdKeep NoExtra s r post) :
    WorldStepIn T (bufRegions B) gw stdKeep NoExtra s r' { post with locals := L, clock := k } := by
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := h
  refine ⟨(arenaReady_with_locals post L k).2 hAp, hhp, hG, hK, ?_⟩
  intro S Nd hWT hT hD
  obtain ⟨S', Nd', hsub, ⟨hT', hJ', hF', hNH', hndisj', hws'⟩, hOG, hFO, _⟩ := hW S Nd hWT hT hD
  have hWT'' : WorldTypedWith { post with locals := L, clock := k } S' Nd' :=
    ⟨(tablesTyped_with_locals post L k S').2 hT', hJ', hF', hNH', hndisj', hws'⟩
  exact ⟨S', Nd', hsub, hWT'', hOG, hFO, trivial⟩

theorem worldStepIn_of_pre_locals_clock_r31
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {F : Type} {B : BufList} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (hT_eq : @T F { s with locals := L, clock := k } = @T F s)
    (h : WorldStepIn T (bufRegions B) gw stdKeep NoExtra { s with locals := L, clock := k } r post) :
    WorldStepIn T (bufRegions B) gw stdKeep NoExtra s r post := by
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := h
  refine ⟨hAp, hhp, hG, hK, fun S Nd hWT hTs hD => ?_⟩
  obtain ⟨hTab, hJ, hF, hNH, hndisj, hws⟩ := hWT
  have hWT' : WorldTypedWith { s with locals := L, clock := k } S Nd :=
    ⟨(tablesTyped_with_locals s L k S).2 hTab, hJ, hF, hNH, hndisj, hws⟩
  exact hW S Nd hWT' (fun t ht => hTs t (by dsimp only at ht ⊢; rwa [← hT_eq])) hD

theorem worldStepSc_trans_owned_r31
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {F : Type} {B : BufList} {gw : List String}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (h12 : WorldStepSc (bufRegions B) gw stdKeep NoExtra s1 r1 s2)
    (howned : ∀ S Nd, WorldTypedWith s1 S Nd →
      ∃ S2 Nd2, (∀ t ∈ S, t ∈ S2) ∧ WorldTypedWith s2 S2 Nd2 ∧
        OwnedGrows s1 s2 (worldOwned s1 S Nd) (worldOwned s2 S2 Nd2) ∧
        (∀ t ∈ T s2, t ∈ S2) ∧
        (∀ a : BitVec 64,
          (∀ i ∈ worldOwned s1 S Nd ++ bufRegions B s1 ++ [freeGap s1], ¬ CellHits a.toNat i) →
          ¬ CellHits a.toNat (heapFree s1) →
          s2.memory a = s1.memory a))
    (h23 : WorldStepIn T (bufRegions B) gw stdKeep NoExtra s2 r2 s3)
    (hsc23 : globN s3 "scratch_ptr" ≤ globN s2 "scratch_ptr") :
    WorldStepSc (bufRegions B) gw stdKeep NoExtra s1 r2 s3 := by
  obtain ⟨⟨hA2, hhp12, hG12, hK12, _⟩, hsc12⟩ := h12
  obtain ⟨hA3, hhp23, hG23, hK23, hW23⟩ := h23
  have hbuf21 : bufRegions B s2 = bufRegions B s1 := bufRegions_eq_of_safeGlobals hB hgw hG12
  have hfmp21 : globN s2 "frame_mem_ptr" = globN s1 "frame_mem_ptr" :=
    globN_eq_of_lookup (hG12 (ofString "frame_mem_ptr") (hgw.not_mem_map (by decide)))
  refine ⟨⟨hA3, le_trans hhp12 hhp23,
    fun k hk => (hG12 k hk).trans (hG23 k hk), ?_, ?_⟩, le_trans hsc23 hsc12⟩
  · intro rec hrec hnz k hk hno
    have hrec_not : ofString rec.1 ∉ (["heap_ptr", "scratch_ptr", "journal_n"] : List String).map ofString := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl <;> decide
    have hg_rec : globN s2 rec.1 = globN s1 rec.1 :=
      globN_eq_of_lookup (hG12 (ofString rec.1) (hgw.not_mem_map hrec_not))
    have h2 : memW s3 (globN s2 rec.1 + k) = memW s2 (globN s2 rec.1 + k) :=
      hK23 rec hrec (by rw [hg_rec]; exact hnz) k hk
        (by change ∀ i ∈ bufRegions B s2, ¬ CellHits (globN s2 rec.1 + k) i
            rw [hbuf21, hg_rec]; exact hno)
    rw [hg_rec] at h2
    exact h2.trans (hK12 rec hrec hnz k hk hno)
  · intro S Nd hWT1 _
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hT2, hFO12⟩ := howned S Nd hWT1
    have hD2 : IvlsDisj (bufRegions B s2) (worldTypedIvls s2 S2 Nd2) := validBufList_disj hB hWT2
    obtain ⟨S3, Nd3, hsub23, hWT3, hOG23, hFO23, _⟩ := hW23 S2 Nd2 hWT2 hT2 hD2
    refine ⟨S3, Nd3, fun t ht => hsub23 t (hsub12 t ht), hWT3, ?_, ?_, trivial⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          have ho1 : o1 = 0 := by omega
          have ho2 : o2 = 0 := by omega
          rw [ho1, ho2]
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
            · change i ∈ bufRegions B s2 at hR2
              rw [hbuf21] at hR2
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hR2)) ⟨hc1, hc2⟩
          · simp only [List.mem_singleton] at hfg2
            subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by unfold freeGap at hc1 ⊢; dsimp only at hc1 ⊢; omega,
               by unfold freeGap at hc2 ⊢; dsimp only at hc2 ⊢; omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12

theorem worldStepIn_trans_stepSc_r31
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {F : Type} {B : BufList} {gw : List String}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (h12 : WorldStepIn T (bufRegions B) gw stdKeep NoExtra s1 r1 s2)
    (hsc12 : globN s2 "scratch_ptr" ≤ globN s1 "scratch_ptr")
    (h23 : WorldStepSc (bufRegions B) gw stdKeep NoExtra s2 r2 s3) :
    WorldStepIn T (bufRegions B) gw stdKeep NoExtra s1 r2 s3 ∧
      globN s3 "scratch_ptr" ≤ globN s1 "scratch_ptr" := by
  obtain ⟨hA2, hhp12, hG12, hK12, hW12⟩ := h12
  obtain ⟨⟨hA3, hhp23, hG23, hK23, hW23⟩, hsc23⟩ := h23
  have hbuf21 : bufRegions B s2 = bufRegions B s1 := bufRegions_eq_of_safeGlobals hB hgw hG12
  have hfmp21 : globN s2 "frame_mem_ptr" = globN s1 "frame_mem_ptr" :=
    globN_eq_of_lookup (hG12 (ofString "frame_mem_ptr") (hgw.not_mem_map (by decide)))
  refine ⟨⟨hA3, le_trans hhp12 hhp23,
    fun k hk => (hG12 k hk).trans (hG23 k hk), ?_, ?_⟩, le_trans hsc23 hsc12⟩
  · intro rec hrec hnz k hk hno
    have hrec_not : ofString rec.1 ∉ (["heap_ptr", "scratch_ptr", "journal_n"] : List String).map ofString := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl <;> decide
    have hg_rec : globN s2 rec.1 = globN s1 rec.1 :=
      globN_eq_of_lookup (hG12 (ofString rec.1) (hgw.not_mem_map hrec_not))
    have h2 : memW s3 (globN s2 rec.1 + k) = memW s2 (globN s2 rec.1 + k) :=
      hK23 rec hrec (by rw [hg_rec]; exact hnz) k hk
        (by change ∀ i ∈ bufRegions B s2, ¬ CellHits (globN s2 rec.1 + k) i
            rw [hbuf21, hg_rec]; exact hno)
    rw [hg_rec] at h2
    exact h2.trans (hK12 rec hrec hnz k hk hno)
  · intro S Nd hWT1 hT1 hD1
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, _⟩ := hW12 S Nd hWT1 hT1 hD1
    have hD2 : IvlsDisj (bufRegions B s2) (worldTypedIvls s2 S2 Nd2) := validBufList_disj hB hWT2
    obtain ⟨S3, Nd3, hsub23, hWT3, hOG23, hFO23, _⟩ := hW23 S2 Nd2 hWT2 hD2
    refine ⟨S3, Nd3, fun t ht => hsub23 t (hsub12 t ht), hWT3, ?_, ?_, trivial⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          have ho1 : o1 = 0 := by omega
          have ho2 : o2 = 0 := by omega
          rw [ho1, ho2]
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
            · change i ∈ bufRegions B s2 at hR2
              rw [hbuf21] at hR2
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hR2)) ⟨hc1, hc2⟩
          · simp only [List.mem_singleton] at hfg2
            subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by unfold freeGap at hc1 ⊢; dsimp only at hc1 ⊢; omega,
               by unfold freeGap at hc2 ⊢; dsimp only at hc2 ⊢; omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12

/-! ## 3. Journal-Append Consequences & `jset` on `ts.inner` / Fresh `ts+32` -/

theorem nonTrieStep_preserves_fresh_slot_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hNT : NonTrieStep [] s post)
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd)
    {iw : Nat} (hiw_not : iw ∉ S) :
    ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ iw := by
  obtain ⟨⟨Nd', hWT'⟩, _, _⟩ := hNT S Nd hWT (fun _ h => by cases h)
  have hroles : RolesOK post S (worldRoleSlots post) (journalRoleSlots post) :=
    hWT'.1.2.2.2.2.2.2.2.2.2.2.2
  intro a ha heq
  exact hiw_not (heq ▸ (hroles.1 a ha).1)

theorem journal_append_wrs_and_hdr_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (jnw : BitVec 64)
    (hW0 : WorldOK s) (_hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg_kept : GlobalsKept ["heap_ptr", "journal_n"] s post)
    (hjn_s : globN s "journal_n" = jnw.toNat)
    (hjn_lt : globN s "journal_n" < globN s "journal_cap")
    (hdom_wr : ∀ x : BitVec 64, post.memory x ≠ s.memory x → s.memaddrs x)
    (hcell : ∀ x : BitVec 64, post.memory x ≠ s.memory x →
      CellHitsPos x.toNat (globN s "journal" + 32 * jnw.toNat, 32) ∨
      CellHitsPos x.toNat (freeGap s) ∨
      CellHitsPos x.toNat (heapFree s)) :
    worldRoleSlots post = worldRoleSlots s ∧
    (∀ S, TablesTyped s S → ∀ u ∈ S, hdr post u 0 = hdr s u 0) ∧
    (∀ tw_val : Nat,
      globN post "journal_n" = globN s "journal_n" + 1 →
      memW post (globN s "journal" + 32 * jnw.toNat) = tw_val →
      (let j := globN s "journal" + 32 * jnw.toNat
       ∀ p ∈ (tw_val, journalRole s tw_val) ::
         (if memW post (j + 16) ≠ 0 ∧ journalRole s tw_val = "ts+32" then
           [(memW post (j + 24), "ts.inner")] else []),
         p ∈ worldRoleSlots s) →
      ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post,
        a ∈ worldRoleSlots s ++ journalRoleSlots s) := by
  have hAs := hW0.1
  have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hg_kept (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsp_eq]⟩
  have hcore_no_jn : ∀ g ∈ (["ws", "bs", "ts", "bo", "bal_accounts", "bal_idx_accts",
      "bal_idx_stor", "journal", "journal_cap"] : List String), globN post g = globN s g := fun g hg => by
    have hne : ofString g ∉ (["heap_ptr", "journal_n"] : List String).map ofString := by revert g hg; decide
    exact globN_eq_of_lookup (hg_kept (ofString g) hne)
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega),
     mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega)⟩
  set jrec : Ivl := (globN s "journal" + 32 * jnw.toNat, 32)
  have hjcap_nz : globN s "journal_cap" ≠ 0 := by omega
  have hj_fo : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
    unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; right; simp [hjcap_nz]
  obtain ⟨_, S0, hWT0⟩ := hW0
  have hJ0 := hWT0.2.1
  have hF0 := hWT0.2.2.1
  have hjrec_in : Inside jrec (globN s "journal") (globN s "journal" + 32 * globN s "journal_cap") := by
    dsimp [Inside, jrec]; omega
  have hunhit_disj_jr : ∀ i : Ivl, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 →
      Disj i (globN s "journal", 32 * globN s "journal_cap") → IvlUnhit s post i := by
    intro i hal hi1 hi2 hdj x hx8 hhit
    by_contra hne
    have hdj_rec : Disj i jrec := (disj_of_inside_left hjrec_in hdj.flip).flip
    have hdj_fg : Disj i (freeGap s) := disj_allocated_freeGap hAs.2 hal
    have hdj_hf : Disj i (heapFree s) := disj_allocated_heapFree hAs.2 hal
    have hin_i : i.1 ≤ x.toNat ∧ x.toNat + 8 ≤ i.1 + i.2 := by
      unfold CellHits at hhit; omega
    rcases hcell x hne with hrec_hit | hfg_hit | hhf_hit
    · exact not_cellHitsPos_of_disj hin_i hdj_rec hrec_hit
    · exact not_cellHitsPos_of_disj hin_i hdj_fg hfg_hit
    · exact not_cellHitsPos_of_disj hin_i hdj_hf hhf_hit
  have hu_tab_any : ∀ S, TablesTyped s S → ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i :=
    fun S hT t ht i hi =>
      hunhit_disj_jr i ((hT.2.1 t ht).2 i hi).1
        ((hT.2.1 t ht).1.1 i hi).2.1 ((hT.2.1 t ht).1.1 i hi).2.2.1
        (((hT.2.1 t ht).2 i hi).2 _ hj_fo)
  have hhdr_any : ∀ S, TablesTyped s S → ∀ u ∈ S, hdr post u 0 = hdr s u 0 := by
    intro S hT u hu
    have hwf := (hT.2.1 u hu).1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    have ht8 : u % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : u + 88 ≤ 2 ^ 64 := by
      have h1 := (hwf.1 _ ht_fp).1.2
      have h2 : heapEnd ≤ 2 ^ 64 := by decide
      dsimp at h1; omega
    exact (htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab_any S hT u hu _ ht_fp)).1 0 (by omega)
  have hfo_split : fixedObjects s = (globalBuffers.map (bufferRegion s)) ++
      ([(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s ++ balObjects s) := by
    unfold fixedObjects
    have hmap : (List.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) globalBuffers) =
        globalBuffers.map (bufferRegion s) := rfl
    rw [hmap]; simp [List.append_assoc]
  have hpw_fo := hF0.2
  rw [hfo_split] at hpw_fo
  obtain ⟨_, hpw_right, hcross_gb⟩ := List.pairwise_append.1 hpw_fo
  have hpw_jr_rest : (([(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
      blockOutObjects s ++ balObjects s)).Pairwise Disj := hpw_right
  rw [List.append_assoc] at hpw_jr_rest
  have hcross_jr_rest := (List.pairwise_cons.1 hpw_jr_rest).1
  have hu_gb_rec : ∀ r : String × Nat, r ∈ typedRecords → globN s r.1 ≠ 0 →
      IvlUnhit s post (globN s r.1, r.2) := fun r hr hnz => by
    have hmf := typedRecord_mem_fixedObjects s hr
    simp only [hnz, ↓reduceIte] at hmf
    rcases hF0.1 _ hmf with h0 | ⟨hal, hw⟩
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
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hpos => by
    have hmf : i ∈ fixedObjects s := by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
    rcases hF0.1 i hmf with h0 | ⟨hal, hw⟩
    · exact absurd h0 hpos
    · have hdj : Disj (globN s "journal", 32 * globN s "journal_cap") i := by
        simpa [hjcap_nz] using hcross_jr_rest i (List.mem_append_right (blockOutObjects s) hi)
      exact hunhit_disj_jr i hal hw.1 hw.2.1 hdj.flip
  have hT := hWT0.1
  have hbal_part := R10Shards.P26_P28.balObjects_eq_of_unhit hAs.2 hT hF0 (hcore_no_jn "bal_accounts" (by decide))
    (hu_tab_any S0 hT) hu_bal hlow
  have hws_g : globN post "ws" = globN s "ws" := hcore_no_jn "ws" (by decide)
  have hbs_g : globN post "bs" = globN s "bs" := hcore_no_jn "bs" (by decide)
  have hts_g : globN post "ts" = globN s "ts" := hcore_no_jn "ts" (by decide)
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
      have hw := rec_word_eq_of_unhit hAs.2 hF0 "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) hk.1 hk.2
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
      have hw := rec_word_eq_of_unhit hAs.2 hF0 "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
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
      have hw := rec_word_eq_of_unhit hAs.2 hF0 "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) hk.1 hk.2
      simp only [hts_g] at hw; simp [hw]
  have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    unfold nestRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · have hw32 := rec_word_eq_of_unhit hAs.2 hF0 "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
      simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "bs" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "bs" + 32) ∈ S0 := by
          rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm; exact absurd h0 h32; exact hm
        rw [R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab_any S0 hT _ hmS)]
  have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
    unfold nestRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw32 := rec_word_eq_of_unhit hAs.2 hF0 "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "ts" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "ts" + 32) ∈ S0 := by
          rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm; exact absurd h0 h32; exact hm
        rw [R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab_any S0 hT _ hmS)]
  have hrecs_bal := balRecords_eq_of_unhit hT hba_g (fun hnz => by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hu_tab_any S0 hT _ hm)
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s := by
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
    congr 1; congr 1
    apply List.flatMap_congr
    intro ad had
    rw [← hrecs_bal] at had
    obtain ⟨h0, h8, _⟩ := hbal_part.2 ad had
    rw [h0, h8]
  refine ⟨hwrs_eq, hhdr_any, fun tw_val hjn_post hm_r0 hjrNew_sub => ?_⟩
  rcases hJ0.2.2.1 with hjc0 | ⟨hal_jr, hw_jr⟩
  · exact absurd hjc0 hjcap_nz
  have hj_hi := (ivl_allocated_bound hAs.2 hal_jr).2
  have hj8 : (globN s "journal") % 8 = 0 := hw_jr.1
  have hu_jr_old : ∀ i, i < globN s "journal_n" →
      IvlUnhit s post (globN s "journal" + 32 * i, 32) := fun i hi => by
    intro x hx8 hhit
    by_contra hne
    have hdj_rec : Disj (globN s "journal" + 32 * i, 32) jrec := by
      right; right; left; dsimp [jrec]; omega
    have hal_i : Allocated s (globN s "journal" + 32 * i, 32) := by
      have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ0.1
      rcases hal_jr with ⟨hlo, hhi_hp⟩ | ⟨hlo, hhi_sc⟩
      · exact Or.inl ⟨by dsimp at hlo ⊢; omega, by dsimp at hhi_hp ⊢; omega⟩
      · exact Or.inr ⟨by dsimp at hlo ⊢; omega, by dsimp at hhi_sc ⊢; omega⟩
    have hdj_fg : Disj (globN s "journal" + 32 * i, 32) (freeGap s) :=
      disj_allocated_heapFree hAs.2 hal_i |> fun _ => disj_allocated_freeGap hAs.2 hal_i
    have hdj_hf : Disj (globN s "journal" + 32 * i, 32) (heapFree s) :=
      disj_allocated_heapFree hAs.2 hal_i
    have hin_i : globN s "journal" + 32 * i ≤ x.toNat ∧ x.toNat + 8 ≤ globN s "journal" + 32 * i + 32 := by
      unfold CellHits at hhit; omega
    rcases hcell x hne with hrec_hit | hfg_hit | hhf_hit
    · exact not_cellHitsPos_of_disj hin_i hdj_rec hrec_hit
    · exact not_cellHitsPos_of_disj hin_i hdj_fg hfg_hit
    · exact not_cellHitsPos_of_disj hin_i hdj_hf hhf_hit
  have hj_old_words : ∀ i, i < globN s "journal_n" →
      memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) ∧
      memW post (globN s "journal" + 32 * i + 16) = memW s (globN s "journal" + 32 * i + 16) ∧
      memW post (globN s "journal" + 32 * i + 24) = memW s (globN s "journal" + 32 * i + 24) := by
    intro i hi
    have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ0.1
    have hhi_i : globN s "journal" + 32 * i + 32 ≤ 2 ^ 64 := by dsimp at hj_hi; omega
    have hui := hu_jr_old i hi
    exact ⟨memW_eq_of_ivlUnhit hui (by omega) hhi_i ⟨by omega, by omega⟩,
           memW_eq_of_ivlUnhit hui (by omega) hhi_i ⟨by omega, by omega⟩,
           memW_eq_of_ivlUnhit hui (by omega) hhi_i ⟨by omega, by omega⟩⟩
  have hj_g : globN post "journal" = globN s "journal" := hcore_no_jn "journal" (by decide)
  have hrole_eq : ∀ t, journalRole post t = journalRole s t := fun t => by
    unfold journalRole
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw16 := rec_word_eq_of_unhit hAs.2 hF0 "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 16) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF0 "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      have hw48 := rec_word_eq_of_unhit hAs.2 hF0 "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 48) (by omega) (by omega)
      have hw64 := rec_word_eq_of_unhit hAs.2 hF0 "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 64) (by omega) (by omega)
      simp only [hts_g] at hw16 hw32 hw48 hw64 ⊢
      rw [hw16, hw32, hw48, hw64]
  let jrNew :=
    let j := globN s "journal" + 32 * jnw.toNat
    (tw_val, journalRole s tw_val) ::
      (if memW post (j + 16) ≠ 0 ∧ journalRole s tw_val = "ts+32" then
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
  intro a ha
  rw [hwrs_eq, hjrs_post] at ha
  rcases List.mem_append.1 ha with hw | hjr
  · exact List.mem_append_left _ hw
  · rcases List.mem_append.1 hjr with hjr_old | hjr_new
    · exact List.mem_append_right _ hjr_old
    · exact List.mem_append_left _ (hjrNew_sub a hjr_new)


theorem worldStepIn_trans_owned_r31
    {T1 T2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {F : Type} {B : BufList} {gw : List String}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (h12 : WorldStepIn T1 (bufRegions B) gw stdKeep NoExtra s1 r1 s2)
    (hsc12 : globN s2 "scratch_ptr" ≤ globN s1 "scratch_ptr")
    (howned : ∀ S Nd, WorldTypedWith s1 S Nd → (∀ t ∈ T1 s1, t ∈ S) →
      ∃ S2 Nd2, (∀ t ∈ S, t ∈ S2) ∧ WorldTypedWith s2 S2 Nd2 ∧
        OwnedGrows s1 s2 (worldOwned s1 S Nd) (worldOwned s2 S2 Nd2) ∧
        (∀ t ∈ T2 s2, t ∈ S2) ∧
        (∀ a : BitVec 64,
          (∀ i ∈ worldOwned s1 S Nd ++ bufRegions B s1 ++ [freeGap s1], ¬ CellHits a.toNat i) →
          ¬ CellHits a.toNat (heapFree s1) →
          s2.memory a = s1.memory a))
    (h23 : WorldStepIn T2 (bufRegions B) gw stdKeep NoExtra s2 r2 s3)
    (hsc23 : globN s3 "scratch_ptr" ≤ globN s2 "scratch_ptr") :
    WorldStepIn T1 (bufRegions B) gw stdKeep NoExtra s1 r2 s3 ∧
      globN s3 "scratch_ptr" ≤ globN s1 "scratch_ptr" := by
  obtain ⟨hA2, hhp12, hG12, hK12, _⟩ := h12
  obtain ⟨hA3, hhp23, hG23, hK23, hW23⟩ := h23
  have hbuf21 : bufRegions B s2 = bufRegions B s1 := bufRegions_eq_of_safeGlobals hB hgw hG12
  have hfmp21 : globN s2 "frame_mem_ptr" = globN s1 "frame_mem_ptr" :=
    globN_eq_of_lookup (hG12 (ofString "frame_mem_ptr") (hgw.not_mem_map (by decide)))
  refine ⟨⟨hA3, le_trans hhp12 hhp23,
    fun k hk => (hG12 k hk).trans (hG23 k hk), ?_, ?_⟩, le_trans hsc23 hsc12⟩
  · intro rec hrec hnz k hk hno
    have hrec_not : ofString rec.1 ∉ (["heap_ptr", "scratch_ptr", "journal_n"] : List String).map ofString := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl <;> decide
    have hg_rec : globN s2 rec.1 = globN s1 rec.1 :=
      globN_eq_of_lookup (hG12 (ofString rec.1) (hgw.not_mem_map hrec_not))
    have h2 : memW s3 (globN s2 rec.1 + k) = memW s2 (globN s2 rec.1 + k) :=
      hK23 rec hrec (by rw [hg_rec]; exact hnz) k hk
        (by change ∀ i ∈ bufRegions B s2, ¬ CellHits (globN s2 rec.1 + k) i
            rw [hbuf21, hg_rec]; exact hno)
    rw [hg_rec] at h2
    exact h2.trans (hK12 rec hrec hnz k hk hno)
  · intro S Nd hWT1 hT1 hD1
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hT2, hFO12⟩ := howned S Nd hWT1 hT1
    have hD2 : IvlsDisj (bufRegions B s2) (worldTypedIvls s2 S2 Nd2) := validBufList_disj hB hWT2
    obtain ⟨S3, Nd3, hsub23, hWT3, hOG23, hFO23, _⟩ := hW23 S2 Nd2 hWT2 hT2 hD2
    refine ⟨S3, Nd3, fun t ht => hsub23 t (hsub12 t ht), hWT3, ?_, ?_, trivial⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          have ho1 : o1 = 0 := by omega
          have ho2 : o2 = 0 := by omega
          rw [ho1, ho2]
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
            · change i ∈ bufRegions B s2 at hR2
              rw [hbuf21] at hR2
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hR2)) ⟨hc1, hc2⟩
          · simp only [List.mem_singleton] at hfg2
            subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by unfold freeGap at hc1 ⊢; dsimp only at hc1 ⊢; omega,
               by unfold freeGap at hc2 ⊢; dsimp only at hc2 ⊢; omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12


end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
