import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HtabValuesSub
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalBase
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Common

/-!
# R16 Shard `AccountWk`: Account & Storage WorldKeeps Contracts

Standalone 0-`sorry` proofs of C08 `WorldKeeps` contracts:
- `«wk_destroy_storage»`
- `«wk_clear_account_preserving_balance»`
- `«wk_create_ether»`
- `«wk_set_account_balance»`
- `«wk_increment_nonce»`
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

def acctMutBufs : List (String × Nat) :=
  [("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64), ("sk_buf", 52)]

theorem validBufList_acctMutBufs : ValidBufList acctMutBufs := by
  intro p hp
  simp only [acctMutBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨136, by decide, by decide, by decide⟩
  · exact ⟨200, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩

/-! ## 1. Runtime Code Lookups -/

theorem lookup_trap_with_r16 :
    originalRuntimeCode.lookup (ofString "trap_with") =
      some ((sourceFunctionEntry Guest.Software.guestFn_trap_with).2) :=
  lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_trap_with) rfl

theorem lookup_alloc_r16 :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ((sourceFunctionEntry Guest.Software.guestFn_alloc).2) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem lookup_memcpy_r16 :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ((sourceFunctionEntry Guest.Software.guestFn_memcpy).2) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem lookup_u256_add :
    originalRuntimeCode.lookup (ofString "u256_add") =
      some ((sourceFunctionEntry Guest.Software.guestFn_u256_add).2) :=
  lookup_of_guestAst_getElem 56 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_add) rfl

theorem lookup_htab_del_r16 :
    originalRuntimeCode.lookup (ofString "htab_del") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_del, .one) :=
  lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_del) rfl

theorem lookup_htab_item_r16 :
    originalRuntimeCode.lookup (ofString "htab_item") =
      some ((sourceFunctionEntry Guest.Software.guestFn_htab_item).2) :=
  lookup_of_guestAst_getElem 143 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_item) rfl

theorem lookup_jset :
    originalRuntimeCode.lookup (ofString "jset") =
      some ((sourceFunctionEntry Guest.Software.guestFn_jset).2) :=
  lookup_of_guestAst_getElem 356 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_jset) rfl

theorem lookup_jdel :
    originalRuntimeCode.lookup (ofString "jdel") =
      some ((sourceFunctionEntry Guest.Software.guestFn_jdel).2) :=
  lookup_of_guestAst_getElem 357 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_jdel) rfl

theorem lookup_acct_copy :
    originalRuntimeCode.lookup (ofString "acct_copy") =
      some ((sourceFunctionEntry Guest.Software.guestFn_acct_copy).2) :=
  lookup_of_guestAst_getElem 363 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_acct_copy) rfl

theorem lookup_acct_is_empty :
    originalRuntimeCode.lookup (ofString "acct_is_empty") =
      some ((sourceFunctionEntry Guest.Software.guestFn_acct_is_empty).2) :=
  lookup_of_guestAst_getElem 384 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_acct_is_empty) rfl

theorem lookup_set_account :
    originalRuntimeCode.lookup (ofString "set_account") =
      some ((sourceFunctionEntry Guest.Software.guestFn_set_account).2) :=
  lookup_of_guestAst_getElem 387 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_set_account) rfl

theorem lookup_destroy_storage :
    originalRuntimeCode.lookup (ofString "destroy_storage") =
      some ((sourceFunctionEntry Guest.Software.guestFn_destroy_storage).2) :=
  lookup_of_guestAst_getElem 389 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_destroy_storage) rfl

theorem lookup_destroy_account :
    originalRuntimeCode.lookup (ofString "destroy_account") =
      some ((sourceFunctionEntry Guest.Software.guestFn_destroy_account).2) :=
  lookup_of_guestAst_getElem 390 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_destroy_account) rfl

theorem lookup_modify_state_commit :
    originalRuntimeCode.lookup (ofString "modify_state_commit") =
      some ((sourceFunctionEntry Guest.Software.guestFn_modify_state_commit).2) :=
  lookup_of_guestAst_getElem 391 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_modify_state_commit) rfl

theorem lookup_clear_account_preserving_balance :
    originalRuntimeCode.lookup (ofString "clear_account_preserving_balance") =
      some ((sourceFunctionEntry Guest.Software.guestFn_clear_account_preserving_balance).2) :=
  lookup_of_guestAst_getElem 392 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_clear_account_preserving_balance) rfl

theorem lookup_create_ether :
    originalRuntimeCode.lookup (ofString "create_ether") =
      some ((sourceFunctionEntry Guest.Software.guestFn_create_ether).2) :=
  lookup_of_guestAst_getElem 396 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_create_ether) rfl

theorem lookup_set_account_balance :
    originalRuntimeCode.lookup (ofString "set_account_balance") =
      some ([(ofString "addr", .one), (ofString "amount", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_set_account_balance, .one) :=
  lookup_of_guestAst_getElem 397 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_set_account_balance) rfl

theorem lookup_increment_nonce :
    originalRuntimeCode.lookup (ofString "increment_nonce") =
      some ((sourceFunctionEntry Guest.Software.guestFn_increment_nonce).2) :=
  lookup_of_guestAst_getElem 398 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_increment_nonce) rfl

/-! ## 2. Read-Only Helpers (`u256_add`, `acct_is_empty`) -/

theorem ro_u256_add : ReadOnlyFn (ofString "u256_add") :=
  InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst
    56 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_add rfl (fun _ => false) (by intro _ h; cases h) (by decide)

def acctIsEmptyCallees (f : MlS) : Bool :=
  f == ofString "memeq" || f == ofString "u256_is_zero"

theorem ro_acct_is_empty : ReadOnlyFn (ofString "acct_is_empty") :=
  readOnlyFn_of_roProgR16 384 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_acct_is_empty rfl acctIsEmptyCallees
    (fun f hf values body callee rs hfound => by
      obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
      simp only [acctIsEmptyCallees, Bool.or_eq_true, beq_iff_eq] at hf
      rcases hf with rfl | rfl
      · have hl := lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_memeq) rfl
        change originalRuntimeCode.lookup (ofString "memeq") = _ at hl
        rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
      · have hl := lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_u256_is_zero) rfl
        change originalRuntimeCode.lookup (ofString "u256_is_zero") = _ at hl
        rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide)
    (by decide)

theorem ro_htab_item : ReadOnlyFn (ofString "htab_item") :=
  readOnlyFn_of_roProgR16 143 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_item rfl (fun _ => false) (by intro _ h; cases h) (by decide)

/-! ## 3. Role-Slot Preservation Lemmas -/

theorem rolesOK_append_journal_sub_wrs {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {sl jr newEntries : List (Nat × String)}
    (hroles : RolesOK s S sl jr)
    (hhdr : ∀ u ∈ S, hdr post u 0 = hdr s u 0)
    (hnew : ∀ p ∈ newEntries, p ∈ sl) :
    RolesOK post S sl (jr ++ newEntries) := by
  have hmem_old : ∀ a ∈ sl ++ (jr ++ newEntries), a ∈ sl ++ jr := by
    intro a ha
    rcases List.mem_append.1 ha with hsl | hjrn
    · exact List.mem_append_left _ hsl
    · rcases List.mem_append.1 hjrn with hjr | hne
      · exact List.mem_append_right _ hjr
      · exact List.mem_append_left _ (hnew a hne)
  have hsl_same : ∀ a ∈ sl, ∀ b ∈ sl, a.1 = b.1 → a.2 = b.2 := by
    intro a ha b hb heq
    obtain ⟨ia, hia, rfl⟩ := List.mem_iff_getElem.1 ha
    obtain ⟨ib, hib, rfl⟩ := List.mem_iff_getElem.1 hb
    rcases Nat.lt_trichotomy ia ib with hlt | rfl | hgt
    · exact ((List.pairwise_iff_getElem.1 hroles.2.1) ia ib hia hib hlt heq).1
    · rfl
    · exact (((List.pairwise_iff_getElem.1 hroles.2.1) ib ia hib hia hgt heq.symm).1).symm
  refine ⟨fun a ha => ?_, hroles.2.1, fun a ha b hb heq => ?_⟩
  · obtain ⟨haS, hkl⟩ := hroles.1 a (hmem_old a ha)
    exact ⟨haS, (hhdr a.1 haS).trans hkl⟩
  · rcases List.mem_append.1 ha with hajr | hane
    · exact hroles.2.2 a hajr b (hmem_old b hb) heq
    · have hasl : a ∈ sl := hnew a hane
      rcases List.mem_append.1 (hmem_old b hb) with hbsl | hbjr
      · exact hsl_same a hasl b hbsl heq
      · exact (hroles.2.2 b hbjr a (List.mem_append_left _ hasl) heq.symm).symm

theorem rolesOK_nest_sub {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {A Ns Np B jr : List (Nat × String)}
    (hroles : RolesOK s S (A ++ Ns ++ B) jr)
    (hhdr : ∀ u ∈ S, hdr post u 0 = hdr s u 0)
    (hNp : ∀ x ∈ Np, x ∈ Ns ∧ x.2 = "ts.inner") :
    RolesOK post S (A ++ Np ++ B) jr := by
  have hsub_sl : ∀ x ∈ A ++ Np ++ B, x ∈ A ++ Ns ++ B := by
    intro x hx
    rcases List.mem_append.1 hx with hANp | hB
    · rcases List.mem_append.1 hANp with hA | hxNp
      · exact List.mem_append_left _ (List.mem_append_left _ hA)
      · exact List.mem_append_left _ (List.mem_append_right _ (hNp x hxNp).1)
    · exact List.mem_append_right _ hB
  have hsub_all : ∀ x ∈ (A ++ Np ++ B) ++ jr, x ∈ (A ++ Ns ++ B) ++ jr := by
    intro x hx
    rcases List.mem_append.1 hx with hsl | hjr
    · exact List.mem_append_left _ (hsub_sl x hsl)
    · exact List.mem_append_right _ hjr
  have hts_sh : "ts.inner" ∈ sharedRoles := by decide
  have hpw0 : (A ++ (Ns ++ B)).Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := by
    simpa [List.append_assoc] using hroles.2.1
  obtain ⟨hpwA, hpwNsB, hcrossA⟩ := List.pairwise_append.1 hpw0
  obtain ⟨hpwNs, hpwB, hcrossNsB⟩ := List.pairwise_append.1 hpwNsB
  have hpwNp : Np.Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := by
    refine List.pairwise_iff_getElem.2 (fun i j hi hj _ heq => ?_)
    have hi_role := (hNp Np[i] (List.getElem_mem hi)).2
    have hj_role := (hNp Np[j] (List.getElem_mem hj)).2
    exact ⟨hi_role.trans hj_role.symm, hi_role ▸ hts_sh⟩
  have hpwNpB : (Np ++ B).Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) :=
    List.pairwise_append.2 ⟨hpwNp, hpwB, fun x hx b hb => hcrossNsB x (hNp x hx).1 b hb⟩
  have hpw_new : (A ++ (Np ++ B)).Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) :=
    List.pairwise_append.2 ⟨hpwA, hpwNpB, fun a ha c hc => by
      rcases List.mem_append.1 hc with hcNp | hcB
      · exact hcrossA a ha c (List.mem_append_left _ (hNp c hcNp).1)
      · exact hcrossA a ha c (List.mem_append_right _ hcB)⟩
  refine ⟨fun a ha => ?_, by simpa [List.append_assoc] using hpw_new, fun a ha b hb heq => ?_⟩
  · obtain ⟨haS, hkl⟩ := hroles.1 a (hsub_all a ha)
    exact ⟨haS, (hhdr a.1 haS).trans hkl⟩
  · exact hroles.2.2 a ha b (hsub_all b hb) heq

/-! ## 4. Multi-Word Store Infrastructure (`wkSc_get_account`, `worldEff_store_multi` imported from `WkGetAccount`) -/

private theorem flattenHOL_shape_u256 {v : ValueHOL 64}
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

theorem safeStepGlobals_hp_jn : SafeStepGlobals ["heap_ptr", "journal_n"] := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

theorem safeStepGlobals_hp_jn_sp : SafeStepGlobals ["heap_ptr", "journal_n", "scratch_ptr"] := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem nonValueSlot_ts16 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + (16 : BitVec 64).toNat) ≠ 0) :
    let t0 := memW s (globN s "ts" + (16 : BitVec 64).toNat)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have hc : (16 : BitVec 64).toNat = 16 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S : memW s (globN s "ts" + 16) ∈ S := by
    rcases hT.2.2.2.2.2.1 16 (by simp [tsTableSlots]) hts_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (memW s (globN s "ts" + 16), "ts+16") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 16 "ts+16" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact nonValueSlot_of_wrs s S _ "ts+16" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem ts32Slot_disj {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + 32) ≠ 0) :
    let t0 := memW s (globN s "ts" + 32)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) ∧
    memW s (globN s "ts" + 16) ≠ t0 := by
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  have ht0_S : memW s (globN s "ts" + 32) ∈ S := by
    rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) hts_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (memW s (globN s "ts" + 32), "ts+32") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 32 "ts+32" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  refine ⟨ht0_S, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbs h32
    have h32_nz : memW s (globN s "bs" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
    have hm : (memW s (globN s "bs" + 32), "bs+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "bs" 32 "bs+32" hbs h32_nz
      apply List.mem_append.2; left; apply List.mem_append.2; right
      unfold recRoles; simp [hbs]
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) h32
  · intro hba
    have hba_nz : globN s "bal_accounts" ≠ 0 := by rw [hba]; exact ht0_nz
    have hm : (globN s "bal_accounts", "bal_accounts") ∈ worldRoleSlots s := by
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [hba_nz]⟩
      apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right; simp
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) hba
  · intro ad had had0
    have had0_nz : memW s ad ≠ 0 := by rw [had0]; exact ht0_nz
    have hm : (memW s ad, "bal.stor") ∈ worldRoleSlots s := by
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [had0_nz]⟩
      apply List.mem_append.2; right
      exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) had0
  · intro hws h32
    have h32_nz : memW s (globN s "ws" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
    have hm : (memW s (globN s "ws" + 32), "ws+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ws" 32 "ws+32" hws h32_nz
      apply List.mem_append.2; left; apply List.mem_append.2; left
      unfold recRoles; simp [hws]
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) h32
  · intro h16
    have h16_nz : memW s (globN s "ts" + 16) ≠ 0 := by rw [h16]; exact ht0_nz
    have hm : (memW s (globN s "ts" + 16), "ts+16") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ts" 16 "ts+16" hts_nz h16_nz
      apply List.mem_append.2; right
      unfold recRoles; simp [hts_nz]
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) h16

theorem worldStepSc_of_htabDel_ts32 {F : Type} {s post : PanSemStateFiniteExact 64 F}
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
    WorldStepSc (bufRegions []) gw stdKeep NoExtra s r post := by
  set t0 := memW s (globN s "ts" + 32)
  have hAs := hW0.1
  have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hg_nonHeap (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsp_eq]⟩
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g hg => by
    have hne : ofString g ∉ (["heap_ptr"] : List String).map ofString := by revert g hg; decide
    exact globN_eq_of_lookup (hg_nonHeap (ofString g) hne)
  have hbuf_same : FreshBufsOK s post := by
    refine ⟨fun gn hgn => Or.inl ?_, List.pairwise_iff_getElem.2 fun i j _ _ _ ha _ => absurd ?_ ha.1⟩
    · have hne : ofString gn.1 ∉ (["heap_ptr"] : List String).map ofString := by revert gn hgn; decide
      exact globN_eq_of_lookup (hg_nonHeap (ofString gn.1) hne)
    · have hgm := List.getElem_mem ‹i < globalBuffers.length›
      have hne : ofString globalBuffers[i].1 ∉ (["heap_ptr"] : List String).map ofString := by
        revert hgm; generalize globalBuffers[i] = gp; intro hgm; revert gp hgm; decide
      exact globN_eq_of_lookup (hg_nonHeap (ofString globalBuffers[i].1) hne)
  obtain ⟨S0, hWT0_ex⟩ := hW0.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have ht0_S0 : t0 ∈ S0 := (ts32Slot_disj s S0 hWT0.1 hts_nz ht0_nz).1
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have h1 := hAs.2.2.2.2.2.2.1; have h2 := hAp.2.2.2.2.2.2.1; omega
  have ht0_al0 : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hWT0.1.2.1 t0 ht0_S0).1.1 j hj).2; exact ⟨hw.1, hw.2.1⟩
  have hrk : RecordsKept (bufRegions []) stdKeep s post := by
    intro rec hrec hgnz k hk _
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
    have hmf := typedRecord_mem_fixedObjects s htr
    simp only [hgnz, ↓reduceIte] at hmf
    rcases hWT0.2.2.1.1 _ hmf with h0 | ⟨hal, hwords⟩
    · omega
    · have hhi := (ivl_allocated_bound hAs.2 hal).2
      have hg8 : (globN s rec.1) % 8 = 0 := hwords.1
      have hu_rec : IvlUnhit s post (globN s rec.1, sz) :=
        ivlUnhit_of_frameOutside_aligned hsz_nz hfr ht0_al0 hf_al
          (fun j hj => (((hWT0.1.2.1 t0 ht0_S0).2 j hj).2 _ hmf).flip)
          (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr hal))
      exact memW_eq_of_ivlUnhit hu_rec (by omega) hhi ⟨by omega, by omega⟩
  refine ⟨⟨hAp, hhp, hg_kept, hrk, fun S Nd hWT _ => ?_⟩, by rw [hsp_eq]⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨ht0_S, hno_bs32, hno_ba, hno_ad, hno_ws32, _⟩ := ts32Slot_disj s S hT hts_nz ht0_nz
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
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; omega
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
    apply hu_fix _ _ (by dsimp only; omega)
    unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; right; simp [hnz]
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi h24 =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))) (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hipos =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)) hipos
  have hbo_eq := blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst
  have hbal_eq := balObjects_eq_of_unhit_except hAs.2 hT hF
    (hcore "bal_accounts" (by decide)) hu_other ⟨hno_ba, hno_ad⟩ hu_bal hm0
  obtain ⟨hF_post, _⟩ := fixedTyped_of_freshBufsOK hAs hAp hag hF
    (hcore "journal" (by decide)) (hcore "journal_cap" (by decide)) hbo_eq.1 hbal_eq.1 hbuf_same
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_eq.1, hbal_eq.1, hcore "journal" (by decide), hcore "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ∉ (["heap_ptr"] : List String).map ofString := by revert gn hgn; decide
    have hg_eq : globN post gn.1 = globN s gn.1 := globN_eq_of_lookup (hg_nonHeap (ofString gn.1) hne)
    simp [hg_eq]
  obtain ⟨hjr_eq, hJ_post⟩ := journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hcore hu_ts hu_jr
  obtain ⟨hNH_post, hne_eq⟩ := nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hother_fp : ∀ u ∈ S, u ≠ t0 →
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu hne
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    exact htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
      (by have := (hfp _ ht_fp).1.2; dsimp at this; omega) (hu_other u hu hne _ ht_fp)
  have ht0_disj_other : ∀ i ∈ htabFootprint post t0,
      (∀ u ∈ S, u ≠ t0 → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects s, Disj i j) ∧
      (∀ o ∈ nodeExtents s Nd, Disj i o) := by
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
                  unfold nodeExtents at ho
                  obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
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
    have ews := hcore "ws" (by decide)
    have ebs := hcore "bs" (by decide)
    have ets := hcore "ts" (by decide)
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq.2, ?_⟩
    · intro u hu
      by_cases heq : u = t0
      · subst heq; rw [hfix_eq]
        exact ⟨hwf_t0, fun i hi => ⟨(hfp_t0 i hi).1, (ht0_disj_other i hi).2.1⟩⟩
      · rw [(hother_fp u hu heq).2, hfix_eq]
        exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_other u hu heq),
          fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, ((htwf u hu).2 i hi).2⟩⟩
    · intro u hu v hv hne i hi j hj
      by_cases hu0 : u = t0
      · subst hu0; rw [(hother_fp v hv hne.symm).2] at hj
        exact (ht0_disj_other i hi).1 v hv hne.symm j hj
      · by_cases hv0 : v = t0
        · subst hv0; rw [(hother_fp u hu hu0).2] at hi
          exact ((ht0_disj_other j hj).1 u hu hu0 i hi).flip
        · rw [(hother_fp u hu hu0).2] at hi; rw [(hother_fp v hv hv0).2] at hj
          exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz
      rw [ews] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [ebs] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [ets] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) hk8.1 hk8.2]
      exact htsR k hk hnz
    · intro g hg_mem; rw [hcore g (by simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg_mem; rcases hg_mem with rfl | rfl | rfl <;> decide)]; exact hgR g hg_mem
    · intro hnz hmem
      rw [ebs] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_bs32 hnz)) (fun _ hx => hx) (hbsN hnz hmem)
    · intro hnz hmem
      rw [ets] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      intro i hi
      have hmem_v : nodeF post (hdr post t0 5) (memW post (hdr post t0 6 + 8 * i)) 8 ∈ htabValues post t0 := by
        unfold htabValues
        exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
      have hmem_s := hvals_sub _ hmem_v
      unfold htabValues at hmem_s
      obtain ⟨j, hj, heq⟩ := List.mem_map.1 hmem_s
      rw [← heq]
      exact htsN hnz hmem j (List.mem_range.1 hj)
    · intro ad had
      have had_s : ad ∈ balRecords s := by
        rwa [balRecords_eq_of_unhit hT0 (hcore "bal_accounts" (by decide)) (fun hnz => by
          rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
          · exact absurd h0 hnz
          · exact hu_other _ hm hno_ba)] at had
      obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq.2 ad had
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
    · -- RolesOK via `rolesOK_nest_sub`!
      have hws_g : globN post "ws" = globN s "ws" := hcore "ws" (by decide)
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
        · simp only [hws_g, h, ↓reduceIte]
          apply List.map_congr_left
          intro ⟨k, r⟩ hkr
          have hk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
            rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
          have hw := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) hk.1 hk.2
          simp only [hws_g] at hw; simp [hw]
      have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
          (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
          recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
          (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
        unfold recRoles
        by_cases h : globN s "bs" = 0
        · simp [hbs_g, h]
        · simp only [hbs_g, h, ↓reduceIte]
          apply List.map_congr_left
          intro ⟨k, r⟩ hkr
          have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
            rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
          have hw := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
          simp only [hbs_g] at hw; simp [hw]
      have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
          (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
          recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
          (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
        unfold recRoles
        simp only [hts_g, hts_nz, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hts_nz (hu_ts hts_nz) hk.1 hk.2
        simp only [hts_g] at hw; simp [hw]
      have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
        unfold nestRoles
        by_cases h : globN s "bs" = 0
        · simp [hbs_g, h]
        · have hw32 := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
          simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
          by_cases h32 : memW s (globN s "bs" + 32) = 0
          · simp [h32]
          · simp only [h32, ↓reduceIte]
            have hmS : memW s (globN s "bs" + 32) ∈ S := by
              rcases hbsR 32 (by simp [bsTableSlots]) h with h0 | hm; exact absurd h0 h32; exact hm
            rw [htabValues_eq_of_unhit (htwf _ hmS).1 (hu_other _ hmS (hno_bs32 h))]
      have hnest_ts_sub : ∀ p ∈ (nestRoles post "ts" "ts.inner").filter (fun a => a.1 != 0),
          p ∈ (nestRoles s "ts" "ts.inner").filter (fun a => a.1 != 0) := by
        intro p hp
        rw [List.mem_filter] at hp ⊢
        refine ⟨?_, hp.2⟩
        unfold nestRoles at hp ⊢
        have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hts_nz (hu_ts hts_nz) (k := 32) (by omega) (by omega)
        simp only [hts_g] at hw32
        have ht0_nz' : memW s (globN s "ts" + 32) ≠ 0 := ht0_nz
        simp only [hts_g, hts_nz, ↓reduceIte, hw32, ht0_nz'] at hp ⊢
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hp.1
        exact List.mem_map.2 ⟨v, hvals_sub v hv, rfl⟩
      have hrecs_bal := balRecords_eq_of_unhit hT0 hba_g (fun hnz => by
        rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
        · exact absurd h0 hnz
        · exact hu_other _ hm hno_ba)
      have hbal_part_eq : ((balRecords post).flatMap fun ad => [(memW post ad, "bal.stor"), (memW post (ad + 8), "bal.reads")]) =
          ((balRecords s).flatMap fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]) := by
        rw [hrecs_bal]
        apply List.flatMap_congr
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
        unfold worldRoleSlots
        dsimp only [preList, sufList]
        simp only [List.filter_append, List.append_assoc]
      have hwrs_p : worldRoleSlots post = preList ++ (nestRoles post "ts" "ts.inner").filter (fun a => a.1 != 0) ++ sufList := by
        unfold worldRoleSlots
        rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hbal_part_eq]
        dsimp only [preList, sufList]
        simp only [List.filter_append, List.append_assoc]
      rw [hwrs_p, hjr_eq]
      rw [hwrs_s] at hroles
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
    · rw [hne_eq, hfix_eq]
      intro o ho
      refine ⟨fun u hu i hi => ?_, (hTr.2.1 o ho).2⟩
      by_cases hu0 : u = t0
      · subst hu0; exact ((ht0_disj_other i hi).2.2 o ho).flip
      · rw [(hother_fp u hu hu0).2] at hi; exact (hTr.2.1 o ho).1 u hu i hi
    · intro hws_nz
      rw [ews] at hws_nz
      have e24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hne32 := hno_ws32 hws_nz
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
  refine ⟨S, Nd, fun _ h => h, ⟨hT_post, hJ_post, hF_post, hTr_post⟩, ?_, ?_, trivial⟩
  · intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with ho12 | ho_nd
    · rcases List.mem_append.1 ho12 with ho_tab | ho_fix
      · obtain ⟨u, hu, hi⟩ := List.mem_flatMap.1 ho_tab
        by_cases hu0 : u = t0
        · subst hu0
          rcases (hfp_t0 o hi).2 with ⟨j, hj, hin⟩ | hfresh
          · refine Or.inr (Or.inl ⟨j, ?_, hin⟩)
            unfold worldOwned
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t0, hu, hj⟩))
          · exact Or.inr (Or.inr ⟨hfresh.1, by have := hfresh.2; omega⟩)
        · rw [(hother_fp u hu hu0).2] at hi
          refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
          unfold worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hi⟩))
      · rw [hfix_eq] at ho_fix
        refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ ho_fix)
    · rw [hne_eq] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned
      exact List.mem_append_right _ ho_nd
  · intro a hkeep hnot_hf
    apply hfr a
    · intro j hj
      apply hkeep j
      apply List.mem_append_left; apply List.mem_append_left
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t0, ht0_S, hj⟩))
    · intro hcf
      apply hnot_hf
      obtain ⟨h1, h2⟩ := hcf
      unfold heapFree CellHits at *
      dsimp at h1 h2 ⊢
      have := hAs.2.2.1
      have := hAp.2.2.1
      omega

theorem worldStepSc_of_journal_append {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {tw : BitVec 64} (jnw : BitVec 64)
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
    WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra s r post := by
  have hAs := hW0.1
  have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hg_kept (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsp_eq]⟩
  have hcore_no_jn : ∀ g ∈ (["ws", "bs", "ts", "bo", "bal_accounts", "bal_idx_accts",
      "bal_idx_stor", "journal", "journal_cap"] : List String), globN post g = globN s g := fun g hg => by
    have hne : ofString g ∉ (["heap_ptr", "journal_n"] : List String).map ofString := by revert g hg; decide
    exact globN_eq_of_lookup (hg_kept (ofString g) hne)
  have hbuf_same : FreshBufsOK s post := by
    refine ⟨fun gn hgn => Or.inl ?_, List.pairwise_iff_getElem.2 fun i j _ _ _ ha _ => absurd ?_ ha.1⟩
    · have hne : ofString gn.1 ∉ (["heap_ptr", "journal_n"] : List String).map ofString := by revert gn hgn; decide
      exact globN_eq_of_lookup (hg_kept (ofString gn.1) hne)
    · have hgm := List.getElem_mem ‹i < globalBuffers.length›
      have hne : ofString globalBuffers[i].1 ∉ (["heap_ptr", "journal_n"] : List String).map ofString := by
        revert hgm; generalize globalBuffers[i] = gp; intro hgm; revert gp hgm; decide
      exact globN_eq_of_lookup (hg_kept (ofString globalBuffers[i].1) hne)
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega),
     mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega)⟩
  set jrec : Ivl := (globN s "journal" + 32 * jnw.toNat, 32)
  have hjcap_nz : globN s "journal_cap" ≠ 0 := by omega
  have hj_fo : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
    unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; right; simp [hjcap_nz]
  have hjrec_in : Inside jrec (globN s "journal") (globN s "journal" + 32 * globN s "journal_cap") := by
    dsimp [Inside, jrec]; omega
  -- Helper: any aligned allocated interval disjoint from `(journal, 32 * journal_cap)` is `IvlUnhit`!
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
  -- `RecordsKept`:
  have hrk : RecordsKept (bufRegions []) stdKeep s post := by
    obtain ⟨_, S0, hWT0⟩ := hW0
    obtain ⟨Nd0, hWTW0⟩ := (worldTyped_iff_with s S0).1 hWT0
    have hF0 := hWTW0.2.2.1
    intro rec hrec hgnz k hk _
    have hrec_info : ∃ sz, (rec.1, sz) ∈ globalBuffers ∧
        (rec.1, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, hgb_mem, htr, hsz_nz, hk8, hksz⟩ := hrec_info
    have hmf := typedRecord_mem_fixedObjects s htr
    simp only [hgnz, ↓reduceIte] at hmf
    rcases hF0.1 _ hmf with h0 | ⟨hal, hwords⟩
    · omega
    · have hhi := (ivl_allocated_bound hAs.2 hal).2
      have hg8 : (globN s rec.1) % 8 = 0 := hwords.1
      -- Disjointness between `(rec.1, sz)` in `globalBuffers` and the journal entry in `fixedObjects s`:
      have hfo_split : fixedObjects s = (globalBuffers.map (bufferRegion s)) ++
          ([(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
            blockOutObjects s ++ balObjects s) := by
        unfold fixedObjects
        have hmap : (List.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) globalBuffers) =
            globalBuffers.map (bufferRegion s) := rfl
        rw [hmap]; simp [List.append_assoc]
      have hpw0 := hF0.2
      rw [hfo_split] at hpw0
      have hcross := (List.pairwise_append.1 hpw0).2.2
      have hmem_left : (globN s rec.1, sz) ∈ globalBuffers.map (bufferRegion s) := by
        have hm0 : bufferRegion s (rec.1, sz) ∈ globalBuffers.map (bufferRegion s) :=
          List.mem_map.2 ⟨(rec.1, sz), hgb_mem, rfl⟩
        simpa [bufferRegion, hgnz] using hm0
      have hmem_right : (globN s "journal", 32 * globN s "journal_cap") ∈
          [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
            blockOutObjects s ++ balObjects s := by
        simp [hjcap_nz]
      have hdj_jr : Disj (globN s rec.1, sz) (globN s "journal", 32 * globN s "journal_cap") :=
        hcross _ hmem_left _ hmem_right
      have hu_rec := hunhit_disj_jr (globN s rec.1, sz) hal hg8 hwords.2.1 hdj_jr
      exact memW_eq_of_ivlUnhit hu_rec (by omega) hhi ⟨by omega, by omega⟩
  refine ⟨⟨hAp, hhp, hg_kept, hrk, fun S Nd hWT _ => ?_⟩, by rw [hsp_eq]⟩
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
      have hdj_fg : Disj (memW s (n + 32), memW s (n + 40)) (freeGap s) :=
        disj_allocated_freeGap hAs.2 hal_p
      have hdj_hf : Disj (memW s (n + 32), memW s (n + 40)) (heapFree s) :=
        disj_allocated_heapFree hAs.2 hal_p
      rcases hbyte _ ha_lt hne_b with hin_rec | hin_fg | hin_hf
      · unfold InIvl at hin_rec; rcases hdj_jr with h0 | h0 | h1 | h2 <;> (dsimp [jrec] at *; omega)
      · unfold InIvl at hin_fg; rcases hdj_fg with h0 | h0 | h1 | h2 <;> (dsimp [freeGap] at *; omega)
      · unfold InIvl at hin_hf; rcases hdj_hf with h0 | h0 | h1 | h2 <;> (dsimp [heapFree] at *; omega)
  have hbo_part := blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore_no_jn "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst
  have hbal_part := balObjects_eq_of_unhit hAs.2 hT hF (hcore_no_jn "bal_accounts" (by decide))
    hu_tab hu_bal hlow
  obtain ⟨hF_post, _⟩ := fixedTyped_of_freshBufsOK hAs hAp hag hF
    (hcore_no_jn "journal" (by decide)) (hcore_no_jn "journal_cap" (by decide))
    hbo_part.1 hbal_part.1 hbuf_same
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_part.1, hbal_part.1, hcore_no_jn "journal" (by decide), hcore_no_jn "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ∉ (["heap_ptr", "journal_n"] : List String).map ofString := by revert gn hgn; decide
    have hg_eq : globN post gn.1 = globN s gn.1 := globN_eq_of_lookup (hg_kept (ofString gn.1) hne)
    simp [hg_eq]
  obtain ⟨hNH_post, hne_eq⟩ := nodeHeap_congr_bytes hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
    have h264_he : heapEnd ≤ 2 ^ 64 := by decide
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab t ht _ ht_fp)
  -- Prefix journal records `i < jnw.toNat` are untouched!
  rcases hJ.2.2.1 with hjc0 | ⟨hal_jr, hw_jr⟩
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
      have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ.1
      rcases hal_jr with ⟨hlo, hhi_hp⟩ | ⟨hlo, hhi_sc⟩
      · exact Or.inl ⟨by dsimp at hlo ⊢; omega, by dsimp at hhi_hp ⊢; omega⟩
      · exact Or.inr ⟨by dsimp at hlo ⊢; omega, by dsimp at hhi_sc ⊢; omega⟩
    have hdj_fg : Disj (globN s "journal" + 32 * i, 32) (freeGap s) :=
      disj_allocated_freeGap hAs.2 hal_i
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
    have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ.1
    have hhi_i : globN s "journal" + 32 * i + 32 ≤ 2 ^ 64 := by dsimp at hj_hi; omega
    have hui := hu_jr_old i hi
    exact ⟨memW_eq_of_ivlUnhit hui (by omega) hhi_i ⟨by omega, by omega⟩,
           memW_eq_of_ivlUnhit hui (by omega) hhi_i ⟨by omega, by omega⟩,
           memW_eq_of_ivlUnhit hui (by omega) hhi_i ⟨by omega, by omega⟩⟩
  have hts_g : globN post "ts" = globN s "ts" := hcore_no_jn "ts" (by decide)
  have hj_g : globN post "journal" = globN s "journal" := hcore_no_jn "journal" (by decide)
  have hjc_g : globN post "journal_cap" = globN s "journal_cap" := hcore_no_jn "journal_cap" (by decide)
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
  obtain ⟨htw_S, hjrNew_sub⟩ := htw_ok S hT
  have hJ_post : JournalTyped post S := by
    unfold JournalTyped
    rw [hjn_post, hjc_g, hj_g]
    refine ⟨by omega, hJ.2.1, Or.inr ⟨hag.allocated hal_jr, wordsOK_transfer hAs.1 hAp.1 hw_jr⟩, ?_⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
    · rw [(hj_old_words i hlt).1]; exact hJ.2.2.2 i hlt
    · rw [hjn_s, hm_r0]; exact htw_S
  -- `worldRoleSlots post = worldRoleSlots s`:
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
        have hw := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) hk.1 hk.2
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
        have hw := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
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
        have hw := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) hk.1 hk.2
        simp only [hts_g] at hw; simp [hw]
    have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
      unfold nestRoles
      by_cases h : globN s "bs" = 0
      · simp [hbs_g, h]
      · have hw32 := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
        simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "bs" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s (globN s "bs" + 32) ∈ S := by
            rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm; exact absurd h0 h32; exact hm
          rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
      unfold nestRoles
      by_cases h : globN s "ts" = 0
      · simp [hts_g, h]
      · have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
        simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "ts" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s (globN s "ts" + 32) ∈ S := by
            rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm; exact absurd h0 h32; exact hm
          rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    have hrecs_bal := balRecords_eq_of_unhit hT hba_g (fun hnz => by
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
  -- `journalRoleSlots post = journalRoleSlots s ++ jrNew`:
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
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩ := hT
    have hws_g : globN post "ws" = globN s "ws" := hcore_no_jn "ws" (by decide)
    have hbs_g : globN post "bs" = globN s "bs" := hcore_no_jn "bs" (by decide)
    have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hcore_no_jn "bal_accounts" (by decide)
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2, hfix_eq]
      exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, ((hTt t ht).2 i hi).2⟩⟩
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp t ht u hu_mem hne
    · intro k hk hnz
      rw [hws_g] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) htk.1 htk.2]
      exact htsR k hk hnz
    · intro g hg
      have hg_eq : globN post g = globN s g := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> exact hcore_no_jn _ (by decide)
      rw [hg_eq]; exact hgR g hg
    · intro hnz hm
      rw [hbs_g] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (hbsN hnz hm)
    · intro hnz hm
      rw [hts_g] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (htsN hnz hm)
    · intro ad had
      obtain ⟨h0, h8, _, hkl, hll⟩ := hbal_part.2 ad had
      have hrecs := balRecords_eq_of_unhit hT0 hba_g (fun hnz => by
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
    · intro hnz
      rw [hws_g] at hnz
      have hw24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hwf32 := (hT.2.1 _ hm).1
      have hu32 := hu_tab _ hm
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := htabValues_eq_of_unhit hwf32 hu32
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]; exact hr32 hm i hi
  have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    rw [hfix_eq, hne_eq]
    congr 2
    apply List.flatMap_congr
    intro t ht; exact (htab_fp_hdr t ht).2
  refine ⟨S, Nd, fun _ h => h, ⟨hT_post, hJ_post, hF_post, hTr_post⟩, ?_, ?_, trivial⟩
  · intro o ho; rw [hwo_eq] at ho; exact Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩)
  · intro a hkeep hnot_hf
    by_contra hne
    rcases hcell a hne with ⟨_, hhit_rec⟩ | ⟨_, hhit_fg⟩ | ⟨_, hhit_hf⟩
    · have hhit_jr : CellHits a.toNat (globN s "journal", 32 * globN s "journal_cap") := by
        unfold CellHits at hhit_rec ⊢; dsimp [jrec] at hhit_rec; omega
      have hwo_jr : (globN s "journal", 32 * globN s "journal_cap") ∈ worldOwned s S Nd := by
        unfold worldOwned; exact List.mem_append_left _ (List.mem_append_right _ hj_fo)
      exact hkeep _ (List.mem_append_left _ (List.mem_append_left _ hwo_jr)) hhit_jr
    · exact hkeep (freeGap s) (List.mem_append_right _ List.mem_cons_self) hhit_fg
    · apply hnot_hf
      unfold heapFree CellHits at hhit_hf ⊢
      have := hAp.2.2.2.1
      omega

/-! ## 7. Journaled Mutation Combinators (`jset` on `ts+16`, `jdel` on `ts+32`) -/

private theorem worldEff_call0_memcpy {F : Type} {s cur : PanSemStateFiniteExact 64 F}
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

/-! ## 7. Journal Append Core & `progWStep_call0_jset_ts16` / `progWStep_call0_jdel_ts32` -/

private theorem callee_param_two_r16 {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 : MlS)
    (s1 s2 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2)], body, ret))
    (e1 e2 : ExpHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · simp [he1] at hargs
  · rcases he2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
    · simp [he1, he2] at hargs
    · simp only [he1, he2, Option.some.injEq] at hargs
      subst hargs
      unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
      split at hlook
      · cases hlook
      · rename_i exactBody exactLocals exactShape raw
        have heq := Option.some.inj hlook
        rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, _⟩
        unfold lookupCodeHOLExact at raw
        rw [hl] at raw
        dsimp only at raw
        split at raw
        · rename_i hcond
          have rawEq := Option.some.inj raw
          rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
          rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
          subst hloc
          obtain ⟨hnd, -, -⟩ := hcond
          have hne : p1 ≠ p2 := by simp [List.nodup_cons] at hnd; exact hnd
          refine ⟨v1, v2, he1, he2, ?_, ?_⟩
          · simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE, hne]
          · simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE]
        · cases raw

private theorem trap_with_call_no_none_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 ≠ none ∧
    ¬ Resumes (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 := by
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.const codeVal] = some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal
    (by rw [hcode]; exact lookup_trap_with)
  rw [evaluateHOLFiniteState_call, hargs]; dsimp only; rw [hlk]; dsimp only
  split
  · exact ⟨by simp, by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hrun : evaluateHOLFiniteState
        (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
        (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hrun] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | exception eid v =>
        refine ⟨by simp, ?_⟩
        rintro (⟨_, h⟩ | ⟨_, _, h, hne⟩)
        · simp at h
        · injection h with h'; injection h' with he hw; subst he hw
          exact hout.2.2 eid v hne rfl
      | _ => exact ⟨by simp, by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩

/-- The journal-append statement block shared by `jset` (`e16 = old.0`, `trapCode = 4`)
and `jdel` (`e16 = const 1`, `trapCode = 5`), parameterized over the trailing continuation `tail`
because `dec "klen"`, `decCall "kc"`, and `dec "r"` scope over `tail` in both functions. -/
private def journalAppendTailProg (trapCode : BitVec 64) (e16 : ExpHOL 64) (tail : ProgHOL 64) : ProgHOL 64 :=
  .seq
    (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
      (.call (some (none, none)) (ofString "trap_with") [.const trapCode])
      .skip)
    (.dec (ofString "klen") .one (.load .one (.op .add [.var .local (ofString "t"), .const 0#64]))
      (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")]
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
          (.dec (ofString "r") .one
            (.op .add [.var .global (ofString "journal"),
              .panop .mul [.var .global (ofString "journal_n"), .const 32#64]])
            (.seq
              (.store (.var .local (ofString "r")) (.var .local (ofString "t")))
              (.seq
                (.store (.op .add [.var .local (ofString "r"), .const 8#64]) (.var .local (ofString "kc")))
                (.seq
                  (.store (.op .add [.var .local (ofString "r"), .const 16#64]) e16)
                  (.seq
                    (.store (.op .add [.var .local (ofString "r"), .const 24#64])
                      (.rfield 1 (.var .local (ofString "old"))))
                    (.seq
                      (.assign .global (ofString "journal_n")
                        (.op .add [.var .global (ofString "journal_n"), .const 1#64]))
                      tail)))))))))

private theorem dec_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nm : MlS} {init : ExpHOL 64} {bd : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.dec nm .one init bd) = (some (.returned rv), post)) :
    ∃ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some (.val (.word w)) ∧
      ∃ mid, evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) bd = (some (.returned rv), mid) ∧
        post = { mid with locals := HolFiniteMapExact.resVarEq mid.locals (nm, s.locals.lookup nm) } := by
  rw [evaluateHOLFiniteState_dec_total] at h; dsimp only at h
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | val
  · rw [hev] at h; simp at h
  · rw [hev] at h; dsimp only at h
    rcases val with ⟨⟨w⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at h; done)
    have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh] at h
    rcases hb : evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) bd with ⟨rb, mid⟩
    rw [hb] at h
    cases rb with
    | none => simp at h
    | some r0 =>
      cases r0 with
      | returned u =>
        dsimp only at h
        injection h with hr hso; injection hr with hr'; injection hr' with hu; subst hu
        exact ⟨w, rfl, mid, hb, hso.symm⟩
      | _ => simp at h

private theorem seq_store_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.store dst val) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.store dst val) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.store dst val) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some _ =>
    have hcf := (PanRunBounded.evaluate_store_control_frame s dst val).1
    rw [ha] at hcf; rcases hcf with h0 | h0 <;> cases h0; simp at h

private theorem seq_assign_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {vk : VarKind} {nm : MlS} {val : ExpHOL 64} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.assign vk nm val) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.assign vk nm val) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.assign vk nm val) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some _ =>
    exfalso
    rw [evaluateHOLFiniteState_assign] at ha
    split at ha
    · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
    · split at ha
      · simp at ha
      · injection ha with hr _; injection hr with hr'; subst hr'; simp at h

private theorem seq_call0_ret_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {fn : MlS} {args : List (ExpHOL 64)} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.call (some (none, none)) fn args) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.call (some (none, none)) fn args) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.call (some (none, none)) fn args) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some _ =>
    exfalso
    rw [evaluateHOLFiniteState_call] at ha
    rcases hev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
    · rw [hev] at ha; dsimp only at ha
      injection ha with hr _; injection hr with hr'; subst hr'; simp at h
    · rw [hev] at ha; dsimp only at ha
      rcases hlk : lookupCodeHOLFinite s.code.lookup fn vals with _ | ⟨body0, cal0, ret0⟩
      · rw [hlk] at ha; dsimp only at ha
        injection ha with hr _; injection hr with hr'; subst hr'; simp at h
      · rw [hlk] at ha; dsimp only at ha
        split at ha
        · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
        · rcases hrb : evaluateHOLFiniteState (callEntryStateHOLFinite s cal0) body0 with ⟨rb, mb⟩
          rw [hrb] at ha
          cases rb with
          | none =>
            dsimp only at ha
            injection ha with hr _; injection hr with hr'; subst hr'; simp at h
          | some rb0 =>
            cases rb0 <;> simp only at ha
            case returned =>
              split at ha
              · simp at ha
              · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
            all_goals (injection ha with hr _; injection hr with hr'; subst hr'; simp at h)

private theorem store_word_none_inv {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dstExp valExp : ExpHOL 64}
    (hrun : evaluateHOLFiniteState s (.store dstExp valExp) = (none, post))
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w)) :
    ∃ (dw vw : BitVec 64),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word dw)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
        some (.val (.word vw)) ∧
      s.memaddrs dw ∧
      post = { s with memory := fun a => if a = dw then .word vw else s.memory a } := by
  rw [evaluateHOLFiniteState_store] at hrun
  rcases hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp with _ | dv
  · rw [hx] at hrun; simp at hrun
  · rw [hx] at hrun
    rcases dv with ⟨⟨dw⟩⟩ | _ | _ <;> try (simp at hrun; done)
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp with _ | val
    · rw [hv] at hrun; simp at hrun
    · obtain ⟨vw, rfl⟩ := hval_one val hv
      rw [hv] at hrun
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hrun
      by_cases hdom : s.memaddrs dw
      · simp only [hdom, ↓reduceIte] at hrun
        injection hrun with _ hp
        exact ⟨dw, vw, rfl, rfl, hdom, hp.symm⟩
      · simp [hdom] at hrun

private theorem journal_append_block_step {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F)
    (trapCode : BitVec 64) (e16 : ExpHOL 64) (tw kw f0 f1 w16 : BitVec 64)
    (hW0 : WorldOK s0)
    (heff0 : WorldEff s0 cur [] [] ["heap_ptr"])
    (hg_all_cur : ∀ k : MlS, cur.globals.lookup k = s0.globals.lookup k)
    (hloc_t : cur.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hloc_k : cur.locals.lookup (ofString "key") = some (.val (.word kw)))
    (hloc_old : cur.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]))
    (he16 : ∀ st : PanSemStateFiniteExact 64 F,
      st.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]) →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) e16 =
        some (.val (.word w16)))
    (htw_ok : ∀ S, TablesTyped s0 S → tw.toNat ∈ S ∧
      let jrNew :=
        (tw.toNat, journalRole s0 tw.toNat) ::
          (if w16.toNat ≠ 0 ∧ journalRole s0 tw.toNat = "ts+32" then
            [(f1.toNat, "ts.inner")] else [])
      ∀ p ∈ jrNew, p ∈ worldRoleSlots s0)
    {tail : ProgHOL 64} {rv : ValueHOL 64} {out : PanSemStateFiniteExact 64 F}
    (hflow : evaluateHOLFiniteState cur (journalAppendTailProg trapCode e16 tail) =
      (some (.returned rv), out)) :
    ∃ mid tailPost,
      WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra s0 none mid ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      mid.locals.lookup (ofString "key") = some (.val (.word kw)) ∧
      mid.locals.lookup (ofString "value") = cur.locals.lookup (ofString "value") ∧
      evaluateHOLFiniteState mid tail = (some (.returned rv), tailPost) ∧
      out = { tailPost with locals := out.locals } := by
  have hAs0 := hW0.1
  have hcode : cur.code = originalRuntimeCode := heff0.code
  obtain ⟨_, S0, hWT0⟩ := hW0
  have hW0_full : WorldOK s0 := ⟨hAs0, S0, hWT0⟩
  have hJ0 := hWT0.2.1
  -- Extract `jnw` and `jcw` from `ArenaOK s0`:
  obtain ⟨jnw, hjn_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal_n" (by decide)
  obtain ⟨jcw, hjc_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal_cap" (by decide)
  obtain ⟨jw, hj_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal" (by decide)
  have hjn_cur : cur.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
    rw [hg_all_cur]; exact hjn_lk0
  have hjc_cur : cur.globals.lookup (ofString "journal_cap") = some (.val (.word jcw)) := by
    rw [hg_all_cur]; exact hjc_lk0
  have hjn_nat : globN s0 "journal_n" = jnw.toNat := by unfold GlobalWord at hjn_lk0; simp [globN, hjn_lk0]
  have hjc_nat : globN s0 "journal_cap" = jcw.toNat := by unfold GlobalWord at hjc_lk0; simp [globN, hjc_lk0]
  have hj_nat : globN s0 "journal" = jw.toNat := by unfold GlobalWord at hj_lk0; simp [globN, hj_lk0]
  unfold journalAppendTailProg at hflow
  rw [evaluateHOLFiniteState_seq_line780] at hflow
  -- 1. Capacity guard `ite (journal_n >= journal_cap) (trap_with trapCode) skip`:
  have hjn_lt_jc : jnw.toNat < jcw.toNat := by
    by_contra hge
    have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = true := by
      simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      have hnotlt : ¬ jnw.toNat < jcw.toNat := by omega
      simp [hnotlt]
    have hev_cmp1 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
        (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
        some (.val (.word 1#64)) := by
      simp [evalHOLExact, toExact, hjn_cur, hjc_cur, hnl]
    have hite_tr : evaluateHOLFiniteState cur
        (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
          (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) .skip) =
        evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) := by
      rw [evaluateHOLFiniteState_ite, hev_cmp1]
      simp [show (1#64 : BitVec 64) ≠ 0 by decide]
    rw [hite_tr] at hflow
    obtain ⟨_, htr_none, _⟩ := seq_call0_ret_inv (by rw [evaluateHOLFiniteState_seq_line780]; exact hflow)
    have ⟨hno_none, _⟩ := trap_with_call_no_none_resumes cur trapCode hcode
    exact hno_none (congrArg Prod.fst htr_none)
  have hite_ok : evaluateHOLFiniteState cur
      (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
        (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) .skip) = (none, cur) := by
    have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = false := by
      simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      simp [hjn_lt_jc]
    have hev_cmp0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
        (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
        some (.val (.word 0#64)) := by
      simp [evalHOLExact, toExact, hjn_cur, hjc_cur, hnl]
    rw [evaluateHOLFiniteState_ite, hev_cmp0]
    simp [evaluateHOLFiniteState_skip]
  rw [hite_ok] at hflow; dsimp only at hflow
  have hjn_lt0 : globN s0 "journal_n" < globN s0 "journal_cap" := by omega
  have hjcap_nz : globN s0 "journal_cap" ≠ 0 := by omega
  rcases hJ0.2.2.1 with hjc0 | ⟨hal_jr0, hw_jr0⟩
  · exact absurd hjc0 hjcap_nz
  have hj_hi0 := (ivl_allocated_bound hAs0.2 hal_jr0).2
  set jrec : Ivl := (globN s0 "journal" + 32 * jnw.toNat, 32)
  have hjrec_hi : jrec.1 + 32 ≤ heapEnd := by
    have hhl_he : heapLimit ≤ heapEnd := by decide
    have hse_he : scratchEnd ≤ heapEnd := by decide
    rcases hal_jr0 with ⟨_, hhi⟩ | ⟨_, hhi⟩ <;> (have := hAs0.2.2.1; have := hAs0.2.2.2.2.1; dsimp [jrec] at *; omega)
  -- 2. Unpack `dec klen`:
  obtain ⟨klw, hkl_ev, m_kl, hflow_kl, hout_eq1⟩ := dec_ret_inv hflow
  set s_kl := setVarHOLFinite (ofString "klen") (.val (.word klw)) cur
  have heff_kl : WorldEff s0 s_kl [jrec] [] ["heap_ptr"] :=
    (heff0.mono (by intro _ h; cases h) (by intro _ h; cases h) (by intro _ h; exact h)).locals_clock _ _
  -- 3. Unpack `decCall kc := alloc(klen)` directly to get `s_kc` with `WorldEff` and globals preserved:
  change evaluateHOLFiniteState s_kl _ = (some (.returned rv), m_kl) at hflow_kl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hflow_kl
  have hkl_loc : s_kl.locals.lookup (ofString "klen") = some (.val (.word klw)) := by
    simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hargs_al : evalListHOLFinite s_kl (h := fun a => Classical.propDecidable (s_kl.memaddrs a))
      [.var .local (ofString "klen")] = some [.val (.word klw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hkl_loc]
  have hlk_al := pan_one_word_lookup s_kl.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) klw (by rw [heff_kl.code]; exact lookup_alloc_r16)
  rw [hargs_al] at hflow_kl; dsimp only at hflow_kl; rw [hlk_al] at hflow_kl; dsimp only at hflow_kl
  by_cases hcz_kl : s_kl.clock = 0
  · simp [hcz_kl] at hflow_kl
  rw [if_neg hcz_kl] at hflow_kl
  obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, s_kl.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
    globalWord_of_globN_pos s_kl "heap_ptr"
      (by have := heff_kl.arena.2.1; have hsb : sourceBase = 2701131776 := rfl; omega)
  let ent_al := callEntryStateHOLFinite s_kl (HolFiniteMapExact.empty.update (ofString "n", .val (.word klw)))
  rcases hrun_al : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res_al, pa_al⟩
  dsimp only [ent_al] at hrun_al
  rw [hrun_al] at hflow_kl
  have hres_al : Resumes res_al := by
    cases res_al with
    | none => simp at hflow_kl
    | some cra =>
      cases cra with
      | returned _ => exact Or.inl ⟨_, rfl⟩
      | exception eid _ =>
        dsimp only at hflow_kl; injection hflow_kl with hr_eq _; cases hr_eq
      | _ => simp at hflow_kl
  have hal_spec := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes ent_al pw heff_kl.code hpw_lk
    (by dsimp only [ent_al]; rw [hrun_al]; exact hres_al)
  dsimp only [ent_al] at hal_spec; rw [hrun_al] at hal_spec
  obtain ⟨klw', hklw'_lk, hrv_al, hcmp1, hcmp2, hpa_al⟩ := hal_spec
  have hklw_eq : klw = klw' := by
    have : ent_al.locals.lookup (ofString "n") = some (.val (.word klw)) := by
      simp [ent_al, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [this] at hklw'_lk; injection hklw'_lk with h'; injection h' with h'; injection h'
  subst hklw_eq
  dsimp only at hrv_al hpa_al; subst hrv_al
  have hsh_pw_al : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hflow_kl
  rw [if_pos hsh_pw_al] at hflow_kl
  set s_kc := setVarHOLFinite (ofString "kc") (.val (.word pw)) { pa_al with locals := s_kl.locals }
  have hs_kc_next : s_kc = { s_kl with
      globals := s_kl.globals.update (ofString "heap_ptr", .val (.word ((pw + (klw + 7)) &&& ((0 : BitVec 64) - 8)))),
      locals := s_kc.locals, clock := s_kc.clock } := by
    dsimp only [s_kc, setVarHOLFinite]; rw [hpa_al]; rfl
  obtain ⟨heff_kc, _, _, _, hpw_lo_s0, hpw_add, hhp_kc_lim, _⟩ :=
    R16Shards.worldEff_alloc_step heff_kl (by simp) hpw_lk hcmp1 hcmp2 hs_kc_next
  rcases hcont_kc : evaluateHOLFiniteState s_kc
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
        (.dec (ofString "r") .one
          (.op .add [.var .global (ofString "journal"),
            .panop .mul [.var .global (ofString "journal_n"), .const 32#64]])
          (.seq
            (.store (.var .local (ofString "r")) (.var .local (ofString "t")))
            (.seq
              (.store (.op .add [.var .local (ofString "r"), .const 8#64]) (.var .local (ofString "kc")))
              (.seq
                (.store (.op .add [.var .local (ofString "r"), .const 16#64]) e16)
                (.seq
                  (.store (.op .add [.var .local (ofString "r"), .const 24#64])
                    (.rfield 1 (.var .local (ofString "old"))))
                  (.seq
                    (.assign .global (ofString "journal_n")
                      (.op .add [.var .global (ofString "journal_n"), .const 1#64]))
                    tail))))))) with ⟨rkc, m_kc⟩
  rw [hcont_kc] at hflow_kl
  dsimp only at hflow_kl
  have hrv_kc_eq : rkc = some (.returned rv) := (Prod.mk.inj hflow_kl).1
  have hm_kl_eq : m_kl = { m_kc with locals := (HolFiniteMapExact.resVarEq m_kc.locals
      (ofString "kc", s_kl.locals.lookup (ofString "kc"))) } := ((Prod.mk.inj hflow_kl).2).symm
  cases rkc with
  | none => simp at hrv_kc_eq
  | some cr_kc =>
    cases cr_kc with
    | returned rv_kc =>
      injection hrv_kc_eq with hrv_kc'; injection hrv_kc' with hrv_kc''; subst hrv_kc''
      -- 4. Unpack `seq (call memcpy [kc, key, klen]) (dec r ...)`:
      obtain ⟨s_mc, hmc, hcont_mc⟩ := seq_call0_ret_inv hcont_kc
      have hkc_loc : s_kc.locals.lookup (ofString "kc") = some (.val (.word pw)) := by
        simp [s_kc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hk_loc_kc : s_kc.locals.lookup (ofString "key") = some (.val (.word kw)) := by
        simp [s_kc, s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hloc_k,
          show ofString "kc" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide]
      have hkl_loc_kc : s_kc.locals.lookup (ofString "klen") = some (.val (.word klw)) := by
        simp [s_kc, s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "kc" ≠ ofString "klen" by decide]
      have heff_mc : WorldEff s0 s_mc [jrec] [] ["heap_ptr"] := by
        have hm := worldEff_call0_memcpy heff_kc
          (.var .local (ofString "kc")) (.var .local (ofString "key")) (.var .local (ofString "klen"))
          (by rw [hmc]; simp) (by rw [hmc]; exact Or.inl rfl)
          (fun dw sw nw hd _ hn _ => by
            simp [evalHOLExact, toExact, hkc_loc] at hd; subst hd
            simp [evalHOLExact, toExact, hkl_loc_kc] at hn; subst hn
            exact Or.inr (Or.inr (Or.inr ⟨hpw_lo_s0, by omega⟩)))
        rw [hmc] at hm; exact hm
      have hmc_g : s_mc.globals = s_kc.globals := by
        have hargs_mc : evalListHOLFinite s_kc (h := fun a => Classical.propDecidable (s_kc.memaddrs a))
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")] =
            some [.val (.word pw), .val (.word kw), .val (.word klw)] := by
          rw [evalListHOLFinite_eq_toExact]
          simp [evalListHOLExact, evalHOLExact, toExact, hkc_loc, hk_loc_kc, hkl_loc_kc]
        have hb_mc := Fast_C08WkShard03.call0_byteEff Fast_C08WkShard03.funByteEff_memcpy s_kc
          [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")]
          [(pw.toNat, klw.toNat)] heff_kc.code heff_kc.arena.1
          (fun vals hvs i hi _ => by
            rw [hargs_mc] at hvs; injection hvs with hvs_eq; subst hvs_eq
            simp only [List.mem_singleton, Fast_C08WkShard03.valWordNat] at hi
            subst hi
            exact ⟨(pw.toNat, klw.toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
          (by rw [hmc]; simp) (by rw [hmc]; exact Or.inl rfl)
        rw [hmc] at hb_mc
        exact hb_mc.globals
      have hmc_loc : s_mc.locals = s_kc.locals := by
        have hk := fun k => evaluate_avoidsLocal_flowing k
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
          rfl s_kc (by rw [hmc]; exact Or.inl rfl)
        apply HolFiniteMapExact.ext; funext k; simpa [hmc] using hk k
      -- 5. Unpack `dec r := journal + journal_n * 32`:
      obtain ⟨rw, hr_ev, m_r, hflow_r, hm_kc_eq⟩ := dec_ret_inv hcont_mc
      have hs_mc_g_no_hp : ∀ k : MlS, k ≠ ofString "heap_ptr" → s_mc.globals.lookup k = s0.globals.lookup k := by
        intro k hk
        rw [hmc_g, hs_kc_next]
        simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk.symm, hg_all_cur]
      have hrw_eq : rw = jw + jnw * 32#64 := by
        have hj_mc : s_mc.globals.lookup (ofString "journal") = some (.val (.word jw)) := by
          rw [hs_mc_g_no_hp _ (by decide)]; exact hj_lk0
        have hjn_mc : s_mc.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
          rw [hs_mc_g_no_hp _ (by decide)]; exact hjn_lk0
        simp only [evalHOLExact, evalListHOLExact, toExact, hj_mc, hjn_mc, List.all, List.map,
          Option.map, Bool.and_self, ↓reduceIte, List.foldr, valueIsWord, valueWord,
          wordOpHOL, wordOp, panOpHOL] at hr_ev
        have hz : jnw * 32#64 + (0 : BitVec 64) = jnw * 32#64 := BitVec.add_zero _
        rw [hz] at hr_ev
        injection hr_ev with hr'; injection hr' with hr'; injection hr' with hr'; exact hr'.symm
      have hrw_nat : rw.toNat = globN s0 "journal" + 32 * jnw.toNat := by
        subst hrw_eq
        have hmul : (jnw * 32#64).toNat = 32 * jnw.toNat := by
          rw [BitVec.toNat_mul, show (32#64 : BitVec 64).toNat = 32 from rfl]
          change (jnw.toNat * 32) % 2 ^ 64 = 32 * jnw.toNat
          rw [Nat.mul_comm, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        rw [BitVec.toNat_add, hj_nat, hmul, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
      set s_r := setVarHOLFinite (ofString "r") (.val (.word rw)) s_mc
      have heff_r : WorldEff s0 s_r [jrec] [] ["heap_ptr"] := heff_mc.locals_clock _ _
      have hr_loc : s_r.locals.lookup (ofString "r") = some (.val (.word rw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have ht_loc_r : s_r.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, s_kc, s_kl, hloc_t,
          show ofString "r" ≠ ofString "t" by decide,
          show ofString "kc" ≠ ofString "t" by decide,
          show ofString "klen" ≠ ofString "t" by decide]
      have hkc_loc_r : s_r.locals.lookup (ofString "kc") = some (.val (.word pw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, hkc_loc,
          show ofString "r" ≠ ofString "kc" by decide]
      have hold_loc_r : s_r.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, s_kc, s_kl, hloc_old,
          show ofString "r" ≠ ofString "old" by decide,
          show ofString "kc" ≠ ofString "old" by decide,
          show ofString "klen" ≠ ofString "old" by decide]
      -- 6. Unpack the 4 word stores + `assign journal_n`:
      obtain ⟨s_st0, hst0, hflow_st0⟩ := seq_store_ret_inv hflow_r
      obtain ⟨dw0, vw0, hdw0, hvw0, _, hs_st0_eq⟩ := store_word_none_inv hst0
        (fun v hv => by simp [evalHOLExact, toExact, ht_loc_r] at hv; exact ⟨tw, hv.symm⟩)
      have hdw0_eq : dw0 = rw := by simp [evalHOLExact, toExact, hr_loc] at hdw0; exact hdw0.symm
      have hvw0_eq : vw0 = tw := by simp [evalHOLExact, toExact, ht_loc_r] at hvw0; exact hvw0.symm
      rw [hdw0_eq, hvw0_eq] at hs_st0_eq
      have heff_st0 : WorldEff s0 s_st0 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_r (.var .local (ofString "r")) (.var .local (ofString "t"))
          (fun v hv => by simp [evalHOLExact, toExact, ht_loc_r] at hv; exact ⟨tw, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, toExact, hr_loc] at hx; subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst0] at hw; exact hw
      obtain ⟨s_st8, hst8, hflow_st8⟩ := seq_store_ret_inv hflow_st0
      have hst0_loc : s_st0.locals = s_r.locals := by rw [hs_st0_eq]
      obtain ⟨dw8, vw8, hdw8, hvw8, _, hs_st8_eq⟩ := store_word_none_inv hst8
        (fun v hv => by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hv; exact ⟨pw, hv.symm⟩)
      have hdw8_eq : dw8 = rw + 8#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst0_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw8
        exact hdw8.symm
      have hvw8_eq : vw8 = pw := by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hvw8; exact hvw8.symm
      rw [hdw8_eq, hvw8_eq] at hs_st8_eq
      have hrw8_nat : (rw + 8#64).toNat = rw.toNat + 8 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 8 < 2 ^ 64; dsimp at hj_hi0; omega
      have heff_st8 : WorldEff s0 s_st8 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st0
          (.op .add [.var .local (ofString "r"), .const 8#64]) (.var .local (ofString "kc"))
          (fun v hv => by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hv; exact ⟨pw, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst0_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst8] at hw; exact hw
      obtain ⟨s_st16, hst16, hflow_st16⟩ := seq_store_ret_inv hflow_st8
      have hst8_loc : s_st8.locals = s_r.locals := by rw [hs_st8_eq, hst0_loc]
      have he16_st8 := he16 s_st8 (by rw [hst8_loc]; exact hold_loc_r)
      obtain ⟨dw16, vw16, hdw16, hvw16, _, hs_st16_eq⟩ := store_word_none_inv hst16
        (fun v hv => by rw [he16_st8] at hv; injection hv with hv'; exact ⟨w16, hv'.symm⟩)
      have hdw16_eq : dw16 = rw + 16#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst8_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw16
        exact hdw16.symm
      have hvw16_eq : vw16 = w16 := by
        rw [he16_st8] at hvw16; injection hvw16 with h'; injection h' with h'; injection h' with h'; exact h'.symm
      rw [hdw16_eq, hvw16_eq] at hs_st16_eq
      have hrw16_nat : (rw + 16#64).toNat = rw.toNat + 16 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 16 < 2 ^ 64; dsimp at hj_hi0; omega
      have heff_st16 : WorldEff s0 s_st16 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st8
          (.op .add [.var .local (ofString "r"), .const 16#64]) e16
          (fun v hv => by rw [he16_st8] at hv; injection hv with hv'; exact ⟨w16, hv'.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst8_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst16] at hw; exact hw
      obtain ⟨s_st24, hst24, hflow_st24⟩ := seq_store_ret_inv hflow_st16
      have hst16_loc : s_st16.locals = s_r.locals := by rw [hs_st16_eq, hst8_loc]
      have he24 : @evalHOLExact 64 F _ s_st16.toExact (fun a => Classical.propDecidable (s_st16.memaddrs a))
          (.rfield 1 (.var .local (ofString "old"))) = some (.val (.word f1)) := by
        simp [evalHOLExact, toExact, hst16_loc, hold_loc_r]
      obtain ⟨dw24, vw24, hdw24, hvw24, _, hs_st24_eq⟩ := store_word_none_inv hst24
        (fun v hv => by rw [he24] at hv; injection hv with hv'; exact ⟨f1, hv'.symm⟩)
      have hdw24_eq : dw24 = rw + 24#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst16_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw24
        exact hdw24.symm
      have hvw24_eq : vw24 = f1 := by
        rw [he24] at hvw24; injection hvw24 with h'; injection h' with h'; injection h' with h'; exact h'.symm
      rw [hdw24_eq, hvw24_eq] at hs_st24_eq
      have hrw24_nat : (rw + 24#64).toNat = rw.toNat + 24 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 24 < 2 ^ 64; dsimp at hj_hi0; omega
      have heff_st24 : WorldEff s0 s_st24 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st16
          (.op .add [.var .local (ofString "r"), .const 24#64]) (.rfield 1 (.var .local (ofString "old")))
          (fun v hv => by rw [he24] at hv; injection hv with hv'; exact ⟨f1, hv'.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst16_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst24] at hw; exact hw
      -- 7. Unpack `seq (assign .global "journal_n" (journal_n + 1)) tail`:
      obtain ⟨mid, hass_step, htail_run⟩ := seq_assign_ret_inv hflow_st24
      have hst24_g : s_st24.globals = s_mc.globals := by
        rw [hs_st24_eq, hs_st16_eq, hs_st8_eq, hs_st0_eq]; rfl
      have hjn_st24 : s_st24.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
        rw [hst24_g, hs_mc_g_no_hp _ (by decide)]; exact hjn_lk0
      have hass : evaluateHOLFiniteState s_st24
          (.assign .global (ofString "journal_n")
            (.op .add [.var .global (ofString "journal_n"), .const 1#64])) =
          (none, setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw + 1#64))) s_st24) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, toExact,
          hjn_st24, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
          isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      rw [hass] at hass_step
      have hmid_eq : mid = setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw + 1#64))) s_st24 :=
        ((Prod.mk.inj hass_step).2).symm
      -- Relate `mid` to `s_st24`:
      have hmid_mem : mid.memory = s_st24.memory := by rw [hmid_eq]; rfl
      have hmid_g : mid.globals = s_st24.globals.update (ofString "journal_n", .val (.word (jnw + 1#64))) := by
        rw [hmid_eq]; rfl
      have hmid_be : mid.be = s0.be := by rw [hmid_eq]; exact heff_st24.be
      -- Check memory words at `rw`, `rw + 16#64`, `rw + 24#64`:
      have hne_0_8 : rw ≠ rw + 8#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_0_16 : rw ≠ rw + 16#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_0_24 : rw ≠ rw + 24#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_16_24 : rw + 16#64 ≠ rw + 24#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hm_r0 : memW mid (globN s0 "journal" + 32 * jnw.toNat) = tw.toNat := by
        have hbv0 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat) = rw := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv0, hmid_mem, hs_st24_eq, hs_st16_eq, hs_st8_eq, hs_st0_eq]
        simp [hne_0_24, hne_0_16, hne_0_8]
      have hm_r16 : memW mid (globN s0 "journal" + 32 * jnw.toNat + 16) = w16.toNat := by
        have hbv16 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat + 16) = rw + 16#64 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw16_nat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv16, hmid_mem, hs_st24_eq, hs_st16_eq]
        simp [hne_16_24]
      have hm_r24 : memW mid (globN s0 "journal" + 32 * jnw.toNat + 24) = f1.toNat := by
        have hbv24 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat + 24) = rw + 24#64 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw24_nat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv24, hmid_mem, hs_st24_eq]
        simp
      -- `ArenaReady mid`:
      have hhp_mid_eq : globN mid "heap_ptr" = globN s_st24 "heap_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "heap_ptr" by decide]
      have hfmp_mid_eq : globN mid "frame_mem_ptr" = globN s_st24 "frame_mem_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "frame_mem_ptr" by decide]
      have hsp_mid_eq : globN mid "scratch_ptr" = globN s_st24 "scratch_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "scratch_ptr" by decide]
      have hA_mid : ArenaReady mid := by
        have hG_mid : GuestInv mid := by
          have hG24 := heff_st24.arena.1
          rw [hmid_eq]
          exact ⟨hG24.code, hG24.memaddrs, hG24.shMemaddrs, hG24.baseAddr⟩
        refine ⟨hG_mid, ?_⟩
        unfold ArenaOK
        have hA24 := heff_st24.arena.2
        rw [hhp_mid_eq, hfmp_mid_eq, hsp_mid_eq]
        refine ⟨hA24.1, hA24.2.1, hA24.2.2.1, hA24.2.2.2.1, hA24.2.2.2.2.1,
          hA24.2.2.2.2.2.1, hA24.2.2.2.2.2.2.1, hA24.2.2.2.2.2.2.2.1, ?_⟩
        intro g hg
        by_cases hgj : ofString g = ofString "journal_n"
        · refine ⟨jnw + 1#64, ?_⟩
          unfold GlobalWord; rw [hmid_g, hgj]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        · obtain ⟨w, hw⟩ := hA24.2.2.2.2.2.2.2.2 g hg
          refine ⟨w, ?_⟩
          unfold GlobalWord at hw ⊢
          rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hgj, hw]
      have hjn_mid : globN mid "journal_n" = globN s0 "journal_n" + 1 := by
        have hjc_max : globN s0 "journal_cap" ≤ journalCapMax := hJ0.2.1
        have hjcm_val : journalCapMax = 524288 := rfl
        have hadd1 : (jnw + 1#64).toNat = jnw.toNat + 1 := by
          apply BitVec.toNat_add_of_lt
          change jnw.toNat + 1 < 2 ^ 64; omega
        have hlk_mid : mid.globals.lookup (ofString "journal_n") = some (.val (.word (jnw + 1#64))) := by
          rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        rw [hjn_nat]
        unfold globN; simp [hlk_mid, hadd1]
      have hg_kept_mid : GlobalsKept ["heap_ptr", "journal_n"] s0 mid := by
        intro k hk
        have hne_hp : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
        have hne_jn : k ≠ ofString "journal_n" := fun h => hk (by simp [h])
        rw [hmid_g]
        have hlk_k : (s_st24.globals.update (ofString "journal_n", .val (.word (jnw + 1#64)))).lookup k =
            s_st24.globals.lookup k := by
          simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne_jn]
        rw [hlk_k]
        exact heff_st24.gw_kept k (by simp [hne_hp])
      have hstep : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra s0 none mid :=
        worldStepSc_of_journal_append jnw hW0_full hA_mid hmid_be
          (by rw [hhp_mid_eq]; exact heff_st24.hp_lo) hg_kept_mid hjn_nat hjn_lt0 hjn_mid
          (fun x hx => heff_st24.out_dom x (by rwa [← hmid_mem]))
          (fun x hx => by
            rcases heff_st24.cell_frame x (by rwa [← hmid_mem]) with ⟨iv, hiv, hhit⟩ | ⟨_, h, _⟩ | hfg | hhf
            · simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inl hhit
            · cases h
            · exact Or.inr (Or.inl hfg)
            · exact Or.inr (Or.inr hhf))
          (fun a ha hne => by
            have hmb_mid : memB mid a = memB s_st24 a := by
              unfold memB; rw [hmid_mem, hmid_be, heff_st24.be]
            rcases heff_st24.byte_frame a ha (by rwa [← hmb_mid]) with ⟨iv, hiv, hin⟩ | ⟨_, h, _⟩ | hfg | hhf
            · simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inl hin
            · cases h
            · exact Or.inr (Or.inl hfg)
            · exact Or.inr (Or.inr hhf))
          hm_r0
          (fun S hTS => by
            dsimp only
            rw [hm_r16, hm_r24]
            exact htw_ok S hTS)
      have hs_st24_loc : s_st24.locals = s_r.locals := by rw [hs_st24_eq, hst16_loc]
      have hmid_loc : mid.locals = s_r.locals := by rw [hmid_eq]; exact hs_st24_loc
      have hmid_loc_other : ∀ x : MlS, x ≠ ofString "klen" → x ≠ ofString "kc" → x ≠ ofString "r" →
          mid.locals.lookup x = cur.locals.lookup x := by
        intro x hx_kl hx_kc hx_r
        rw [hmid_loc]
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm hx_r, hmc_loc, s_kc, Ne.symm hx_kc, s_kl, Ne.symm hx_kl]
      have hout_tp : out = { m_r with locals := out.locals } := by
        rw [hout_eq1, hm_kl_eq, hm_kc_eq]
      exact ⟨mid, m_r, hstep,
        (hmid_loc_other _ (by decide) (by decide) (by decide)).trans hloc_t,
        (hmid_loc_other _ (by decide) (by decide) (by decide)).trans hloc_k,
        hmid_loc_other _ (by decide) (by decide) (by decide),
        htail_run, hout_tp⟩
    | _ => simp at hflow_kl

theorem progWStep_call0_jset_ts16 (B : BufList) (gw : List String)
    (hhp_in : "heap_ptr" ∈ gw) (hjn_in : "journal_n" ∈ gw)
    (kExp vExp : ExpHOL 64) :
    ProgWStep B gw
      (.call (some (none, none)) (ofString "jset")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 16#64]), kExp, vExp]) := by
  intro F s hcode hW hnt hfr
  set argsL : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .global (ofString "ts"), .const 16#64]), kExp, vExp]
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "jset") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hbody_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "jset")
          _ _ body' _ ret' values callee lookup_jset (by rwa [← hcode])
        obtain ⟨v1, v2, v3, he1, _, _, hc_t, hc_k, hc_v⟩ := callee_param_three s (ofString "jset")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact lookup_jset) _ _ _ values body' callee ret' hargs_fin hl
        obtain ⟨tw, rfl, htw_nat, hts_nz⟩ := evalAt_loadG_nz s hW.1.1 "ts" 16#64 (by decide) v1 he1
        -- `v2` and `v3` must be words because `jset` params have `.one` shape:
        obtain ⟨_, kw, vlw, hvals_eq, _, hc_k', hc_v'⟩ := Fast_C08WkShard03.lookupCode_three_words
          (by decide) (by decide) (by decide) lookup_jset
          (by
            have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "jset")
              _ _ _ _ ret' values callee (by rw [hcode]; exact lookup_jset) hl
            subst hbody_eq hret_eq; rwa [← hcode])
        have hv23 : v2 = .val (.word kw) ∧ v3 = .val (.word vlw) := by
          rw [hc_k] at hc_k'; rw [hc_v] at hc_v'
          exact ⟨Option.some.inj hc_k', Option.some.inj hc_v'⟩
        rcases hv23 with ⟨rfl, rfl⟩
        let ent := callEntryStateHOLFinite s callee
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, post⟩
        simp only [ent, hrun] at hnt hfr ⊢
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            exfalso
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : noCatchableRaise trapOnlyCallees body' = true :=
              trapOnlyCallees_good (ofString "jset") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
              body' hbody_ok ent hcode eid ev hne
            dsimp only [ent] at hno; rw [hrun] at hno; exact hno rfl
          | returned rv =>
            dsimp only at hfr ⊢
            split
            · -- Unpack `jset` body on `ent` (`WorldOK ent`):
              have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
              subst hbody_eq
              have hbody_fold : sourceFnBody Guest.Software.guestFn_jset =
                  .decCall (ofString "old") (.comb [.one, .one]) (ofString "htab_get")
                    [.var .local (ofString "t"), .var .local (ofString "key")]
                    (journalAppendTailProg 4#64 (.rfield 0 (.var .local (ofString "old")))
                      (.seq
                        (.call (some (none, none)) (ofString "htab_set")
                          [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                        (.return (.const 0#64)))) := rfl
              change evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_jset) = (some (.returned rv), post) at hrun
              rw [hbody_fold] at hrun
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
              have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word tw)) := hc_t
              have hent_k : ent.locals.lookup (ofString "key") = some (.val (.word kw)) := hc_k
              have hent_v : ent.locals.lookup (ofString "value") = some (.val (.word vlw)) := hc_v
              have hargs_hg : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
                  [.var .local (ofString "t"), .var .local (ofString "key")] =
                  some [.val (.word tw), .val (.word kw)] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hent_t, hent_k]
              rw [hargs_hg] at hrun; dsimp only at hrun
              rcases hlk_hg : lookupCodeHOLFinite ent.code.lookup (ofString "htab_get")
                  [.val (.word tw), .val (.word kw)] with _ | ⟨bhg, chg, rhg⟩
              · rw [hlk_hg] at hrun; simp at hrun
              · rw [hlk_hg] at hrun; dsimp only at hrun
                by_cases hcz_ent : ent.clock = 0
                · simp [hcz_ent] at hrun
                rw [if_neg hcz_ent] at hrun
                have hbhg_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "htab_get")
                  _ _ bhg _ rhg _ chg EvmFrameSpecs.lookup_htab_get (by rwa [← show ent.code = originalRuntimeCode from hcode])
                subst hbhg_eq
                obtain ⟨_, _, _, _, hchg_t, hchg_k⟩ := callee_param_two_r16 ent (ofString "htab_get")
                  (ofString "t") (ofString "key") .one .one _ _
                  (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                  (.var .local (ofString "t")) (.var .local (ofString "key"))
                  _ _ chg rhg hargs_hg hlk_hg
                have hchg_t' : chg.lookup (ofString "t") = some (.val (.word tw)) := by
                  have ht_ev : evalAt ent (.var .local (ofString "t")) = some (.val (.word tw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_t]
                  have ⟨v1', _, he1', _, hc1', _⟩ := callee_param_two_r16 ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [ht_ev] at he1'; injection he1' with h'; subst h'; exact hc1'
                have hchg_k' : chg.lookup (ofString "key") = some (.val (.word kw)) := by
                  have hk_ev : evalAt ent (.var .local (ofString "key")) = some (.val (.word kw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_k]
                  have ⟨_, v2', _, he2', _, hc2'⟩ := callee_param_two_r16 ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [hk_ev] at he2'; injection he2' with h'; subst h'; exact hc2'
                let ent_hg := callEntryStateHOLFinite ent chg
                rcases hrun_hg : evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get) with ⟨res_hg, p_hg⟩
                dsimp only [ent_hg] at hrun_hg
                rw [hrun_hg] at hrun
                cases res_hg with
                | none => simp at hrun
                | some cr_hg =>
                  cases cr_hg with
                  | exception eid_hg ev_hg =>
                    exfalso
                    dsimp only at hrun; injection hrun with hr_eq _
                    cases hr_eq
                  | timeOut | error | «break» | «continue» | finalFfi _ => simp at hrun
                  | returned v_old =>
                    dsimp only at hrun
                    split at hrun <;> try simp at hrun
                    have htw_nz : tw ≠ 0 := WkBal.htab_get_t_nonzero ent_hg tw kw
                      (guestInv_callEntry ent chg hWent.1.1) hchg_t' hchg_k' v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have ht0_nz : memW s (globN s "ts" + 16) ≠ 0 := by
                      intro h0; apply htw_nz; apply BitVec.eq_of_toNat_eq
                      change tw.toNat = 0; simpa [htw_nat] using h0
                    obtain ⟨_, S0, hWT0⟩ := hW
                    have htw_S0 : tw.toNat ∈ S0 := by
                      rw [htw_nat]; exact (nonValueSlot_ts16 s S0 hWT0.1 hts_nz ht0_nz).1
                    have hwf_hg : HtabWF ent_hg tw.toNat :=
                      (htabWF_with_locals s chg (ent.clock - 1) tw.toNat).2 (hWT0.1.2.1 _ htw_S0).1
                    obtain ⟨f0, f1, rfl, _⟩ := WkBal.htab_get_ret_in_values ent_hg tw kw
                      hcode hchg_t' hchg_k' hwf_hg v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have hro_hg := FunSpec.at_lookup EvmFrameSpecs.ro_htab_get ent hcode
                      _ (sourceFnBody Guest.Software.guestFn_htab_get) chg rhg hlk_hg
                      (guestInv_callEntry ent chg hWent.1.1) (by rw [hrun_hg]; simp)
                    have hro_hg' : ((evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get)).2) = _ :=
                      hro_hg (by rw [hrun_hg]; exact Or.inl ⟨_, rfl⟩)
                    dsimp only [ent_hg] at hro_hg'
                    rw [hrun_hg] at hro_hg'
                    dsimp only at hro_hg'
                    set s_old := setVarHOLFinite (ofString "old") (.rStruct [.val (.word f0), .val (.word f1)])
                      { p_hg with locals := ent.locals }
                    have heff_old : WorldEff ent s_old [] [] ["heap_ptr"] :=
                      ((WorldEff.refl ent [] [] ["heap_ptr"] hWent.1 hcode).of_readOnly hro_hg').locals_clock _ _
                    have hg_all_old : ∀ k : MlS, s_old.globals.lookup k = ent.globals.lookup k := by
                      intro k; dsimp only [s_old, setVarHOLFinite]; rw [hro_hg']; rfl
                    have hold_t : s_old.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_t,
                        show ofString "old" ≠ ofString "t" by decide]
                    have hold_k : s_old.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_k,
                        show ofString "old" ≠ ofString "key" by decide]
                    have hold_v : s_old.locals.lookup (ofString "value") = some (.val (.word vlw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_v,
                        show ofString "old" ≠ ofString "value" by decide]
                    have hold_old : s_old.locals.lookup (ofString "old") =
                        some (.rStruct [.val (.word f0), .val (.word f1)]) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    rcases htail_old : evaluateHOLFiniteState s_old
                        (journalAppendTailProg 4#64 (.rfield 0 (.var .local (ofString "old")))
                          (.seq
                            (.call (some (none, none)) (ofString "htab_set")
                              [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                            (.return (.const 0#64)))) with ⟨rtail, ptail⟩
                    rw [htail_old] at hrun; dsimp only at hrun
                    have hrtail_eq : rtail = some (.returned rv) := hrun.1
                    have hpost_ptail : post = { ptail with locals := (HolFiniteMapExact.resVarEq ptail.locals
                        (ofString "old", ent.locals.lookup (ofString "old"))) } := hrun.2.symm
                    obtain ⟨mid, tailPost, hstep_j, hmid_t, hmid_k, hmid_v_eq, hmid_tail, hptail_tp⟩ :=
                      journal_append_block_step ent s_old
                        4#64 (.rfield 0 (.var .local (ofString "old"))) tw kw f0 f1 f0 hWent heff_old hg_all_old
                        hold_t hold_k hold_old
                        (fun st hst => by simp [evalHOLExact, toExact, hst])
                        (fun S hTS => by
                          have htw_nat' : tw.toNat = memW s (globN s "ts" + 16) := htw_nat
                          have hts_ent : globN ent "ts" = globN s "ts" := rfl
                          have hm16_ent : memW ent (globN ent "ts" + 16) = memW s (globN s "ts" + 16) := rfl
                          have htw_S : tw.toNat ∈ S := by
                            rw [htw_nat']
                            exact (nonValueSlot_ts16 ent S hTS hts_nz (by change memW ent (globN ent "ts" + 16) ≠ 0; rw [hm16_ent]; exact ht0_nz)).1
                          have hjr_16 : journalRole ent tw.toNat = "ts+16" := by
                            unfold journalRole
                            rw [if_pos ⟨hts_nz, by rw [hm16_ent]; exact htw_nat'⟩]
                          refine ⟨htw_S, ?_⟩
                          dsimp only
                          rw [hjr_16]
                          simp only [show ("ts+16" = "ts+32") ↔ False by decide, and_false, ↓reduceIte,
                            List.mem_singleton]
                          rintro p rfl
                          have hm16_wrs : (memW ent (globN ent "ts" + 16), "ts+16") ∈ worldRoleSlots ent := by
                            apply mem_worldRoleSlots_recRole ent "ts" 16 "ts+16" (by rwa [hts_ent])
                              (by rw [hm16_ent]; exact ht0_nz)
                            apply List.mem_append.2; right
                            unfold recRoles; simp [hts_ent, hts_nz]
                          rwa [hm16_ent, ← htw_nat'] at hm16_wrs)
                        (by rw [htail_old, hrtail_eq])
                    have hmid_v : mid.locals.lookup (ofString "value") = some (.val (.word vlw)) :=
                      hmid_v_eq.trans hold_v
                    have hW_mid : WorldOK mid := hstep_j.worldOK_bufs (fun _ h => by cases h) hWent
                    have hmid_code : mid.code = originalRuntimeCode := hW_mid.1.1.code
                    -- `mid` preserves `ts` and `memW mid (globN mid "ts" + 16) = tw.toNat`:
                    have hts_mid : globN mid "ts" = globN ent "ts" :=
                      globN_eq_of_lookup (hstep_j.1.2.2.1 (ofString "ts") (by decide))
                    have hm16_mid : memW mid (globN mid "ts" + 16) = tw.toNat := by
                      rw [hts_mid]
                      have hrk16 := hstep_j.1.2.2.2.1
                        ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]) (by simp [stdKeep]) hts_nz
                        16 (by simp) (fun _ h => by cases h)
                      exact hrk16.trans htw_nat.symm
                    -- Unpack `seq (call htab_set [t, key, value]) (return 0)` on `mid`:
                    obtain ⟨s_hs, hhs, hret_hs⟩ := seq_call0_ret_inv hmid_tail
                    rw [evaluateHOLFiniteState_return] at hret_hs
                    simp only [evalHOLExact, toExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                      show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hret_hs
                    have htp_eq : tailPost = { s_hs with locals := HolFiniteMapExact.empty } :=
                      ((Prod.mk.inj hret_hs).2).symm
                    -- Unpack `call htab_set` on `mid`:
                    rw [evaluateHOLFiniteState_call] at hhs
                    have hargs_hs : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a))
                        [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")] =
                        some [.val (.word tw), .val (.word kw), .val (.word vlw)] := by
                      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hmid_t, hmid_k, hmid_v]
                    rw [hargs_hs] at hhs; dsimp only at hhs
                    rcases hlk_hs : lookupCodeHOLFinite mid.code.lookup (ofString "htab_set")
                        [.val (.word tw), .val (.word kw), .val (.word vlw)] with _ | ⟨bhs, chs, rhs'⟩
                    · rw [hlk_hs] at hhs; simp at hhs
                    · rw [hlk_hs] at hhs; dsimp only at hhs
                      by_cases hcz_mid : mid.clock = 0
                      · simp [hcz_mid] at hhs
                      rw [if_neg hcz_mid] at hhs
                      obtain ⟨v1_hs, _, _, he1_hs, _, _, hchs_t, _, _⟩ := callee_param_three mid (ofString "htab_set")
                        (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
                        (by rw [hmid_code]; exact EvmFrameSpecs.lookup_htab_set)
                        (.var .local (ofString "t")) (.var .local (ofString "key")) (.var .local (ofString "value"))
                        _ bhs chs rhs' hargs_hs hlk_hs
                      have hv1_hs_eq : v1_hs = .val (.word tw) := by
                        simp [evalAt, evalHOLExact, toExact, hmid_t] at he1_hs; exact he1_hs.symm
                      subst hv1_hs_eq
                      let ent_hs := callEntryStateHOLFinite mid chs
                      have hloc_t_hs : locN ent_hs "t" = memW mid (globN mid "ts" + (16#64 : BitVec 64).toNat) := by
                        change locN ent_hs "t" = memW mid (globN mid "ts" + 16)
                        simp [locN, ent_hs, callEntryStateHOLFinite, hchs_t, hm16_mid]
                      rcases hrun_hs : evaluateHOLFiniteState ent_hs bhs with ⟨res_hs, p_hs⟩
                      dsimp only [ent_hs] at hrun_hs
                      rw [hrun_hs] at hhs
                      cases res_hs with
                      | none => simp at hhs
                      | some cr_hs2 =>
                        cases cr_hs2 with
                        | returned v_hs =>
                          dsimp only at hhs
                          split at hhs <;> try simp at hhs
                          have hs_hs_eq : s_hs = { p_hs with locals := mid.locals } := hhs.symm
                          have hts_mid_nz : globN mid "ts" ≠ 0 := by rwa [hts_mid]
                          have ht0_mid_nz : memW mid (globN mid "ts" + (16#64 : BitVec 64).toNat) ≠ 0 := by
                            change memW mid (globN mid "ts" + 16) ≠ 0
                            rw [hm16_mid]; intro h0; apply htw_nz; exact BitVec.eq_of_toNat_eq h0
                          have hArg_hs : HtabArgWF ent_hs := by
                            obtain ⟨hAm, Sm, hTm, _⟩ := hW_mid
                            have ht0_Sm := (nonValueSlot_ts16 mid Sm hTm hts_mid_nz ht0_mid_nz).1
                            refine ⟨localsFree_arenaReady mid _ _ hAm, ?_, ?_⟩
                            · rw [hloc_t_hs]; exact (htabWF_with_locals mid chs (mid.clock - 1) _).2 (hTm.2.1 _ ht0_Sm).1
                            · rw [hloc_t_hs]; exact fun i hi => ((hTm.2.1 _ ht0_Sm).2 i hi).1
                          have hexit := FunSpec.at_lookup htab_set_spec mid hmid_code
                            _ bhs chs rhs' hlk_hs hArg_hs (by rw [hrun_hs]; simp)
                          rw [hrun_hs] at hexit
                          have hex := hexit v_hs rfl
                          dsimp only [HtabExit] at hex
                          rw [hloc_t_hs] at hex
                          obtain ⟨hAp_hs, hwf_hs, hh0_hs, _, hhp_hs, hfp_hs, hfr_hs, hg_hs⟩ := hex
                          have hbe_hs : p_hs.be = mid.be := by
                            have inv := (PanRunBounded.evaluateHOLFiniteState_metadata ent_hs bhs).2.2.1
                            dsimp only [ent_hs] at inv; rw [hrun_hs] at inv; exact inv
                          have hstep_hs0 : WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra mid none p_hs :=
                            worldStepSc_of_htabExit_nonValue hW_mid hbe_hs hg_hs hg_hs
                              (fun Sm hTm => nonValueSlot_ts16 mid Sm hTm hts_mid_nz ht0_mid_nz)
                              hAp_hs hwf_hs hh0_hs hhp_hs hfp_hs hfr_hs
                          have hstep_hs : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra mid none post := by
                            have hp_post : post = { p_hs with locals := post.locals, clock := post.clock } := by
                              rw [hpost_ptail, hptail_tp, htp_eq, hs_hs_eq]
                            rw [hp_post]
                            exact (hstep_hs0.with_locals_clock post.locals post.clock).mono_bufs
                              (fun _ h => by cases h) (by simp)
                          have hstep_ent : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra ent none post :=
                            WorldStepSc.trans (fun _ h => by cases h) (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
                              hstep_j hstep_hs
                          exact (hstep_ent.from_entry).mono_bufs
                            (fun _ h => by cases h)
                            (fun g hg => by
                              simp at hg
                              rcases hg with rfl | rfl
                              · exact hhp_in
                              · exact hjn_in)
                        | _ => simp at hhs
            · rename_i hbad; simp only [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem jdel_ts32_step {F : Type} (B : BufList) (gw : List String)
    (hhp_in : "heap_ptr" ∈ gw) (hjn_in : "journal_n" ∈ gw)
    (tExp kExp : ExpHOL 64)
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hW : WorldOK s)
    (tw : BitVec 64)
    (ht_ev : evalAt s tExp = some (.val (.word tw)))
    (htw_nat : tw.toNat = memW s (globN s "ts" + 32))
    (hts_nz : globN s "ts" ≠ 0)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "jdel") [tExp, kExp])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "jdel") [tExp, kExp])).1) :
    WorldStepSc (bufRegions B) gw stdKeep NoExtra
      s (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "jdel") [tExp, kExp])).1
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "jdel") [tExp, kExp])).2 := by
  set argsL : List (ExpHOL 64) := [tExp, kExp]
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "jdel") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hbody_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "jdel")
          _ _ body' _ ret' values callee lookup_jdel (by rwa [← hcode])
        obtain ⟨v1, v2, he1, he2, hc_t, hc_k⟩ := callee_param_two_r16 s (ofString "jdel")
          (ofString "t") (ofString "key") .one .one _ _
          (by rw [hcode]; exact lookup_jdel) _ _ values body' callee ret' hargs_fin hl
        have hv1_eq : v1 = .val (.word tw) := by
          rw [ht_ev] at he1; exact (Option.some.inj he1).symm
        subst hv1_eq
        obtain ⟨_, kw, hvals_eq, _, hc_k'⟩ := Fast_C08WkShard03.lookupCode_two_words
          (by decide) lookup_jdel
          (by
            have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "jdel")
              _ _ _ _ ret' values callee (by rw [hcode]; exact lookup_jdel) hl
            subst hbody_eq hret_eq; rwa [← hcode])
        have hv2_eq : v2 = .val (.word kw) := by
          rw [hc_k] at hc_k'; exact Option.some.inj hc_k'
        subst hv2_eq
        let ent := callEntryStateHOLFinite s callee
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, post⟩
        simp only [ent, hrun] at hnt hfr ⊢
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            exfalso
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : noCatchableRaise trapOnlyCallees body' = true :=
              trapOnlyCallees_good (ofString "jdel") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
              body' hbody_ok ent hcode eid ev hne
            dsimp only [ent] at hno; rw [hrun] at hno; exact hno rfl
          | returned rv =>
            dsimp only at hfr ⊢
            split
            · have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
              subst hbody_eq
              have hbody_fold : sourceFnBody Guest.Software.guestFn_jdel =
                  .decCall (ofString "old") (.comb [.one, .one]) (ofString "htab_get")
                    [.var .local (ofString "t"), .var .local (ofString "key")]
                    (.seq
                      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0#64))
                        (.return (.const 0#64))
                        .skip)
                      (journalAppendTailProg 5#64 (.const 1#64)
                        (.seq
                          (.call (some (none, none)) (ofString "htab_del")
                            [.var .local (ofString "t"), .var .local (ofString "key")])
                          (.return (.const 0#64))))) := rfl
              change evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_jdel) = (some (.returned rv), post) at hrun
              rw [hbody_fold] at hrun
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
              have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word tw)) := hc_t
              have hent_k : ent.locals.lookup (ofString "key") = some (.val (.word kw)) := hc_k
              have hargs_hg : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
                  [.var .local (ofString "t"), .var .local (ofString "key")] =
                  some [.val (.word tw), .val (.word kw)] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hent_t, hent_k]
              rw [hargs_hg] at hrun; dsimp only at hrun
              rcases hlk_hg : lookupCodeHOLFinite ent.code.lookup (ofString "htab_get")
                  [.val (.word tw), .val (.word kw)] with _ | ⟨bhg, chg, rhg⟩
              · rw [hlk_hg] at hrun; simp at hrun
              · rw [hlk_hg] at hrun; dsimp only at hrun
                by_cases hcz_ent : ent.clock = 0
                · simp [hcz_ent] at hrun
                rw [if_neg hcz_ent] at hrun
                have hbhg_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "htab_get")
                  _ _ bhg _ rhg _ chg EvmFrameSpecs.lookup_htab_get (by rwa [← show ent.code = originalRuntimeCode from hcode])
                subst hbhg_eq
                have hchg_t' : chg.lookup (ofString "t") = some (.val (.word tw)) := by
                  have ht_ev : evalAt ent (.var .local (ofString "t")) = some (.val (.word tw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_t]
                  have ⟨v1', _, he1', _, hc1', _⟩ := callee_param_two_r16 ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [ht_ev] at he1'; injection he1' with h'; subst h'; exact hc1'
                have hchg_k' : chg.lookup (ofString "key") = some (.val (.word kw)) := by
                  have hk_ev : evalAt ent (.var .local (ofString "key")) = some (.val (.word kw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_k]
                  have ⟨_, v2', _, he2', _, hc2'⟩ := callee_param_two_r16 ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [hk_ev] at he2'; injection he2' with h'; subst h'; exact hc2'
                let ent_hg := callEntryStateHOLFinite ent chg
                rcases hrun_hg : evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get) with ⟨res_hg, p_hg⟩
                dsimp only [ent_hg] at hrun_hg
                rw [hrun_hg] at hrun
                cases res_hg with
                | none => simp at hrun
                | some cr_hg =>
                  cases cr_hg with
                  | exception eid_hg ev_hg =>
                    exfalso
                    dsimp only at hrun; injection hrun with hr_eq _
                    cases hr_eq
                  | timeOut | error | «break» | «continue» | finalFfi _ => simp at hrun
                  | returned v_old =>
                    dsimp only at hrun
                    split at hrun <;> try simp at hrun
                    have htw_nz : tw ≠ 0 := WkBal.htab_get_t_nonzero ent_hg tw kw
                      (guestInv_callEntry ent chg hWent.1.1) hchg_t' hchg_k' v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have ht0_nz : memW s (globN s "ts" + 32) ≠ 0 := by
                      intro h0; apply htw_nz; apply BitVec.eq_of_toNat_eq
                      change tw.toNat = 0; simpa [htw_nat] using h0
                    obtain ⟨_, S0, hWT0⟩ := hW
                    have htw_S0 : tw.toNat ∈ S0 := by
                      rw [htw_nat]; exact (ts32Slot_disj s S0 hWT0.1 hts_nz ht0_nz).1
                    have hwf_hg : HtabWF ent_hg tw.toNat :=
                      (htabWF_with_locals s chg (ent.clock - 1) tw.toNat).2 (hWT0.1.2.1 _ htw_S0).1
                    obtain ⟨f0, f1, rfl, hf1_in⟩ := WkBal.htab_get_ret_in_values ent_hg tw kw
                      hcode hchg_t' hchg_k' hwf_hg v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have hro_hg := FunSpec.at_lookup EvmFrameSpecs.ro_htab_get ent hcode
                      _ (sourceFnBody Guest.Software.guestFn_htab_get) chg rhg hlk_hg
                      (guestInv_callEntry ent chg hWent.1.1) (by rw [hrun_hg]; simp)
                    have hro_hg' : ((evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get)).2) = _ :=
                      hro_hg (by rw [hrun_hg]; exact Or.inl ⟨_, rfl⟩)
                    dsimp only [ent_hg] at hro_hg'
                    rw [hrun_hg] at hro_hg'
                    dsimp only at hro_hg'
                    set s_old := setVarHOLFinite (ofString "old") (.rStruct [.val (.word f0), .val (.word f1)])
                      { p_hg with locals := ent.locals }
                    have heff_old : WorldEff ent s_old [] [] ["heap_ptr"] :=
                      ((WorldEff.refl ent [] [] ["heap_ptr"] hWent.1 hcode).of_readOnly hro_hg').locals_clock _ _
                    have hg_all_old : ∀ k : MlS, s_old.globals.lookup k = ent.globals.lookup k := by
                      intro k; dsimp only [s_old, setVarHOLFinite]; rw [hro_hg']; rfl
                    have hold_t : s_old.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_t,
                        show ofString "old" ≠ ofString "t" by decide]
                    have hold_k : s_old.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_k,
                        show ofString "old" ≠ ofString "key" by decide]
                    have hold_old : s_old.locals.lookup (ofString "old") =
                        some (.rStruct [.val (.word f0), .val (.word f1)]) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    -- First statement in seq: `ite (old.0 == 0) (return 0) skip`
                    rcases hs1_run : evaluateHOLFiniteState s_old
                        (.seq
                          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0#64))
                            (.return (.const 0#64))
                            .skip)
                          (journalAppendTailProg 5#64 (.const 1#64)
                            (.seq
                              (.call (some (none, none)) (ofString "htab_del")
                                [.var .local (ofString "t"), .var .local (ofString "key")])
                              (.return (.const 0#64))))) with ⟨rs1_res, ms1⟩
                    rw [hs1_run] at hrun; dsimp only at hrun
                    have hrs1_eq : rs1_res = some (.returned rv) := hrun.1
                    have hpost_ms1 : post = { ms1 with locals := post.locals } := by
                      have hp2 := hrun.2.symm
                      rw [hp2]
                    subst hrs1_eq
                    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hs1_run
                    by_cases hf0_z : f0 = 0#64
                    · -- Early return 0:
                      subst hf0_z
                      have hev_cmp1 : @evalHOLExact 64 F _ s_old.toExact (fun a => Classical.propDecidable (s_old.memaddrs a))
                          (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0#64)) =
                          some (.val (.word 1#64)) := by
                        simp [evalHOLExact, toExact, hold_old, Compiler.Encoders.Asm.wordCmpHOL]
                      rw [hev_cmp1] at hs1_run; dsimp only at hs1_run
                      rw [if_neg (show (1#64 : BitVec 64) ≠ 0 by decide), evaluateHOLFiniteState_return] at hs1_run
                      simp only [evalHOLExact, toExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                        show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hs1_run
                      have hpost_eq : post = { ent with locals := post.locals, clock := post.clock } := by
                        have hp2 := ((Prod.mk.inj hs1_run).2).symm
                        rw [hpost_ms1, hp2]; dsimp only [s_old, setVarHOLFinite]
                        rw [hro_hg']; rfl
                      rw [hpost_eq]
                      have hstep_ent : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra
                          ent none { ent with locals := post.locals, clock := post.clock } :=
                        (WorldStepSc.refl (R := bufRegions []) (gw := ["heap_ptr", "journal_n"]) (keep := stdKeep)
                          ent none hWent.1).with_locals_clock (r' := none) post.locals post.clock
                      exact (hstep_ent.from_entry).mono_bufs
                        (fun _ h => by cases h)
                        (fun g hg => by simp at hg; rcases hg with rfl | rfl <;> assumption)
                    · -- `f0 ≠ 0#64`: `skip` flows into `journalAppendTailProg 5#64 (.const 1#64)` + `htab_del` + `return 0`!
                      have hnl0 : Compiler.Encoders.Asm.wordCmpHOL .equal f0 0#64 = false := by
                        simp [Compiler.Encoders.Asm.wordCmpHOL, hf0_z]
                      have hev_cmp0 : @evalHOLExact 64 F _ s_old.toExact (fun a => Classical.propDecidable (s_old.memaddrs a))
                          (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0#64)) =
                          some (.val (.word 0#64)) := by
                        simp [evalHOLExact, toExact, hold_old, hnl0]
                      rw [hev_cmp0] at hs1_run; dsimp only at hs1_run
                      simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hs1_run
                      have hf1_in_ent : f1.toNat ∈ htabValues ent tw.toNat := hf1_in hf0_z
                      obtain ⟨mid, tailPost, hstep_j, hmid_t, hmid_k, _, hmid_tail, hms1_tp⟩ :=
                        journal_append_block_step ent s_old
                          5#64 (.const 1#64) tw kw f0 f1 1#64 hWent heff_old hg_all_old
                          hold_t hold_k hold_old
                          (fun st _ => by simp [evalHOLExact, toExact])
                          (fun S hTS => by
                            have hts_ent : globN ent "ts" = globN s "ts" := rfl
                            have hm32_ent : memW ent (globN ent "ts" + 32) = memW s (globN s "ts" + 32) := rfl
                            obtain ⟨ht0_S, _, _, _, _, hne_16⟩ := ts32Slot_disj ent S hTS hts_nz (by rw [hm32_ent]; exact ht0_nz)
                            have htw_S : tw.toNat ∈ S := by rwa [htw_nat, ← hm32_ent]
                            have hjr_32 : journalRole ent tw.toNat = "ts+32" := by
                              unfold journalRole
                              rw [if_neg (fun ⟨_, h16⟩ => hne_16 (by rw [hm32_ent, ← htw_nat]; exact h16.symm))]
                              rw [if_pos ⟨hts_nz, by rw [hm32_ent]; exact htw_nat⟩]
                            -- Show `f1.toNat ∈ S`, hence `f1.toNat ≠ 0`, and `(f1.toNat, "ts.inner") ∈ worldRoleSlots ent`:
                            have hf1_S : f1.toNat ∈ S := by
                              have hv_in : HtabValuesIn ent (memW ent (globN ent "ts" + 32)) S :=
                                hTS.2.2.2.2.2.2.2.2.1 hts_nz ht0_S
                              have hf1_vals : f1.toNat ∈ htabValues ent (memW ent (globN ent "ts" + 32)) := by
                                rwa [hm32_ent, ← htw_nat]
                              obtain ⟨idx, hidx_mem, hidx_eq⟩ := List.mem_map.1 hf1_vals
                              rw [← hidx_eq]
                              exact hv_in idx (List.mem_range.1 hidx_mem)
                            have hf1_nz : f1.toNat ≠ 0 := by
                              intro h0
                              have hwf0 : HtabWF ent 0 := h0 ▸ (hTS.2.1 _ hf1_S).1
                              have hin0 := (hwf0.1 (0, 88) (by unfold htabFootprint; simp)).1
                              unfold Inside sourceBase at hin0
                              omega
                            have hts_ent_nz : globN ent "ts" ≠ 0 := by rwa [hts_ent]
                            have hf1_wrs : (f1.toNat, "ts.inner") ∈ worldRoleSlots ent := by
                              unfold worldRoleSlots
                              rw [List.mem_filter]
                              refine ⟨?_, by simp [hf1_nz]⟩
                              -- `nestRoles ent "ts" "ts.inner"` is inside `worldRoleSlots`:
                              have hnr : (f1.toNat, "ts.inner") ∈ nestRoles ent "ts" "ts.inner" := by
                                unfold nestRoles
                                rw [if_neg hts_ent_nz, if_neg (by rw [hm32_ent]; exact ht0_nz)]
                                refine List.mem_map.2 ⟨f1.toNat, ?_, rfl⟩
                                rwa [hm32_ent, ← htw_nat]
                              exact List.mem_append_left _ (List.mem_append_right _ hnr)
                            have htw_wrs : (tw.toNat, "ts+32") ∈ worldRoleSlots ent := by
                              have hm32_wrs : (memW ent (globN ent "ts" + 32), "ts+32") ∈ worldRoleSlots ent := by
                                apply mem_worldRoleSlots_recRole ent "ts" 32 "ts+32" hts_ent_nz
                                  (by rw [hm32_ent]; exact ht0_nz)
                                apply List.mem_append.2; right
                                unfold recRoles; simp [hts_ent_nz]
                              rwa [hm32_ent, ← htw_nat] at hm32_wrs
                            refine ⟨htw_S, ?_⟩
                            dsimp only
                            rw [hjr_32]
                            have h1nz : (1#64 : BitVec 64).toNat ≠ 0 ∧ "ts+32" = "ts+32" := ⟨by decide, rfl⟩
                            rw [if_pos h1nz]
                            rintro p hp
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                            rcases hp with rfl | rfl
                            · exact htw_wrs
                            · exact hf1_wrs)
                          hs1_run
                      have hW_mid : WorldOK mid := hstep_j.worldOK_bufs (fun _ h => by cases h) hWent
                      have hmid_code : mid.code = originalRuntimeCode := hW_mid.1.1.code
                      have hts_mid : globN mid "ts" = globN ent "ts" :=
                        globN_eq_of_lookup (hstep_j.1.2.2.1 (ofString "ts") (by decide))
                      have hm32_mid : memW mid (globN mid "ts" + 32) = tw.toNat := by
                        rw [hts_mid]
                        have hrk32 := hstep_j.1.2.2.2.1
                          ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]) (by simp [stdKeep]) hts_nz
                          32 (by simp) (fun _ h => by cases h)
                        exact hrk32.trans htw_nat.symm
                      -- Unpack `seq (call htab_del [t, key]) (return 0)` on `mid`:
                      obtain ⟨s_hd, hhd, hret_hd⟩ := seq_call0_ret_inv hmid_tail
                      rw [evaluateHOLFiniteState_return] at hret_hd
                      simp only [evalHOLExact, toExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                        show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hret_hd
                      have htp_eq : tailPost = { s_hd with locals := HolFiniteMapExact.empty } :=
                        ((Prod.mk.inj hret_hd).2).symm
                      rw [evaluateHOLFiniteState_call] at hhd
                      have hargs_hd : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a))
                          [.var .local (ofString "t"), .var .local (ofString "key")] =
                          some [.val (.word tw), .val (.word kw)] := by
                        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hmid_t, hmid_k]
                      rw [hargs_hd] at hhd; dsimp only at hhd
                      rcases hlk_hd : lookupCodeHOLFinite mid.code.lookup (ofString "htab_del")
                          [.val (.word tw), .val (.word kw)] with _ | ⟨bhd, chd, rhd'⟩
                      · rw [hlk_hd] at hhd; simp at hhd
                      · rw [hlk_hd] at hhd; dsimp only at hhd
                        by_cases hcz_mid : mid.clock = 0
                        · simp [hcz_mid] at hhd
                        rw [if_neg hcz_mid] at hhd
                        have hbhd_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "htab_del")
                          _ _ bhd _ rhd' _ chd lookup_htab_del_r16 (by rwa [← hmid_code])
                        subst hbhd_eq
                        obtain ⟨v1_hd, _, he1_hd, _, hchd_t, _⟩ := callee_param_two_r16 mid (ofString "htab_del")
                          (ofString "t") (ofString "key") .one .one _ _
                          (by rw [hmid_code]; exact lookup_htab_del_r16)
                          (.var .local (ofString "t")) (.var .local (ofString "key"))
                          _ _ chd rhd' hargs_hd hlk_hd
                        have hv1_hd_eq : v1_hd = .val (.word tw) := by
                          simp [evalAt, evalHOLExact, toExact, hmid_t] at he1_hd; exact he1_hd.symm
                        subst hv1_hd_eq
                        let ent_hd := callEntryStateHOLFinite mid chd
                        have hloc_t_hd : locN ent_hd "t" = memW mid (globN mid "ts" + 32) := by
                          simp [locN, ent_hd, callEntryStateHOLFinite, hchd_t, hm32_mid]
                        rcases hrun_hd : evaluateHOLFiniteState ent_hd (sourceFnBody Guest.Software.guestFn_htab_del) with ⟨res_hd, p_hd⟩
                        dsimp only [ent_hd] at hrun_hd
                        rw [hrun_hd] at hhd
                        cases res_hd with
                        | none => simp at hhd
                        | some cr_hd2 =>
                          cases cr_hd2 with
                          | returned v_hd =>
                            dsimp only at hhd
                            split at hhd <;> try simp at hhd
                            have hs_hd_eq : s_hd = { p_hd with locals := mid.locals } := hhd.symm
                            have hts_mid_nz : globN mid "ts" ≠ 0 := by rwa [hts_mid]
                            have ht0_mid_nz : memW mid (globN mid "ts" + 32) ≠ 0 := by
                              rw [hm32_mid]; intro h0; apply htw_nz; exact BitVec.eq_of_toNat_eq h0
                            have hArg_hd : HtabArgWF ent_hd := by
                              obtain ⟨hAm, Sm, hTm, _⟩ := hW_mid
                              have ht0_Sm := (ts32Slot_disj mid Sm hTm hts_mid_nz ht0_mid_nz).1
                              refine ⟨localsFree_arenaReady mid _ _ hAm, ?_, ?_⟩
                              · rw [hloc_t_hd]; exact (htabWF_with_locals mid chd (mid.clock - 1) _).2 (hTm.2.1 _ ht0_Sm).1
                              · rw [hloc_t_hd]; exact fun i hi => ((hTm.2.1 _ ht0_Sm).2 i hi).1
                            have hd_sub := htab_del_values_sub ent_hd hmid_code hArg_hd v_hd
                              (by dsimp only [ent_hd]; rw [hrun_hd])
                            dsimp only [ent_hd] at hd_sub
                            have hd_p_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite mid chd)
                                (sourceFnBody Guest.Software.guestFn_htab_del)).2 = p_hd := by
                              rw [hrun_hd]
                            rw [hd_p_eq] at hd_sub
                            obtain ⟨hex_hd, hbe_hd, hvals_sub⟩ := hd_sub
                            dsimp only [HtabExit] at hex_hd
                            rw [hloc_t_hd] at hex_hd hvals_sub
                            obtain ⟨hAp_hd, hwf_hd, hh0_hd, _, hhp_hd, hfp_hd, hfr_hd, hg_hd⟩ := hex_hd
                            have hstep_hd0 : WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra mid none p_hd :=
                              worldStepSc_of_htabDel_ts32 hW_mid hbe_hd hg_hd hg_hd hts_mid_nz ht0_mid_nz
                                hAp_hd hwf_hd hh0_hd hvals_sub hhp_hd hfp_hd hfr_hd
                            have hstep_hd : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra mid none post := by
                              have hp_post : post = { p_hd with locals := post.locals, clock := post.clock } := by
                                rw [hpost_ms1, hms1_tp, htp_eq, hs_hd_eq]
                              rw [hp_post]
                              exact (hstep_hd0.with_locals_clock post.locals post.clock).mono_bufs
                                (fun _ h => by cases h) (by simp)
                            have hstep_ent : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra ent none post :=
                              WorldStepSc.trans (fun _ h => by cases h) (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
                                hstep_j hstep_hd
                            exact (hstep_ent.from_entry).mono_bufs
                              (fun _ h => by cases h)
                              (fun g hg => by simp at hg; rcases hg with rfl | rfl <;> assumption)
                          | _ => simp at hhd
            · rename_i hbad; simp only [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem wkSc_set_account :
    WorldKeepsSc WorldOK (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra
      (ofString "set_account") := by
  have hB : ValidBufList [] := by intro p hp; cases hp
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp
  refine worldKeepsSc_of_progWStep lookup_set_account ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_set_account,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_seq hB hgw ?_ (progWStep_return _ _ _)
  exact progWStep_call0_jset_ts16 [] ["heap_ptr", "journal_n"] (by simp) (by simp) _ _

private def ProgWStepOuter (tw : BitVec 64) (B : BufList) (gw : List String) (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → WorldOK s →
    s.locals.lookup (ofString "outer") = some (.val (.word tw)) →
    tw.toNat = memW s (globN s "ts" + 32) → globN s "ts" ≠ 0 →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowingOrResumes (evaluateHOLFiniteState s prog).1 →
    WorldStepSc (bufRegions B) gw stdKeep NoExtra
      s (evaluateHOLFiniteState s prog).1 (evaluateHOLFiniteState s prog).2

private theorem progWStepOuter_of_progWStep (tw : BitVec 64) {B : BufList} {gw : List String}
    {prog : ProgHOL 64} (h : ProgWStep B gw prog) : ProgWStepOuter tw B gw prog :=
  fun s hc hW _ _ _ hnt hfr => h s hc hW hnt hfr

private theorem worldStepSc_preserves_ts32 {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    {B : BufList} {gw : List String} {r} {tw : BitVec 64}
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw) (hW : WorldOK s)
    (hstep : WorldStepSc (bufRegions B) gw stdKeep NoExtra s r mid)
    (htw : tw.toNat = memW s (globN s "ts" + 32)) (hts : globN s "ts" ≠ 0) :
    tw.toNat = memW mid (globN mid "ts" + 32) ∧ globN mid "ts" ≠ 0 := by
  have hk_ts : ofString "ts" ∉ gw.map ofString := hgw.not_mem_map (by decide)
  have hts_eq : globN mid "ts" = globN s "ts" := globN_eq_of_lookup (hstep.1.2.2.1 _ hk_ts)
  refine ⟨?_, by rwa [hts_eq]⟩
  rw [hts_eq]
  obtain ⟨_, S, hWT⟩ := hW
  obtain ⟨Nd, hWTn⟩ := (worldTyped_iff_with s S).1 hWT
  have hts_wti : (globN s "ts", 72) ∈ worldTypedIvls s S Nd := by
    change (globN s "ts", 72) ∈ M13.worldTypedIvls s S Nd
    unfold M13.worldTypedIvls
    have hts_tr : (globN s "ts", 72) ∈ M13.typedRecords.map (fun r => (globN s r.1, if globN s r.1 = 0 then 0 else r.2)) := by
      refine List.mem_map.2 ⟨("ts", 72), by simp [M13.typedRecords], ?_⟩
      simp [hts]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hts_tr))))
  have hrk := hstep.1.2.2.2.1 ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]) (by simp [stdKeep]) hts
    32 (by simp) (fun b hb hhit => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
      obtain ⟨sz, hgb, hun, hle⟩ := hB p hp
      have hsz_pos : 0 < sz := (by decide : ∀ gp ∈ globalBuffers, 0 < gp.2) (p.1, sz) hgb
      by_cases hgp0 : globN s p.1 = 0
      · dsimp only [bufferRegion, CellHits] at hhit
        simp only [hgp0, ↓reduceIte] at hhit
        omega
      · have hun' : (p.1, sz).1 ∉ typedRecords.map Prod.fst := by
          dsimp only; simpa [typedRecords] using hun
        have hdj := bufferRegion_disj hWTn (p.1, sz) hgb hun' (globN s "ts", 72) hts_wti
        dsimp only [bufferRegion, CellHits, Disj] at hhit hdj
        simp only [hgp0, ↓reduceIte] at hhit hdj
        rcases hdj with h0 | h72 | h1 | h2 <;> omega)
  exact htw.trans hrk.symm

private theorem progWStepOuter_dec {tw : BitVec 64} {B : BufList} {gw : List String}
    {x : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {body : ProgHOL 64}
    (hne : x ≠ ofString "outer") (hb : ProgWStepOuter tw B gw body) :
    ProgWStepOuter tw B gw (.dec x sh e body) := by
  intro F s hc hW hout htw hts hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hnt hfr ⊢
    by_cases hok : shapeEqHOL sh (shapeOfHOLExact val) = true
    · simp only [hok, ↓reduceIte] at hnt hfr ⊢
      set s1 := setVarHOLFinite x val s
      have hW1 : WorldOK s1 := localsFree_worldOK s _ s.clock hW
      have hout1 : s1.locals.lookup (ofString "outer") = some (.val (.word tw)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hout]
      have hstep := hb s1 hc hW1 hout1 htw hts hnt hfr
      exact (WorldStepSc.of_pre_locals_clock hstep).with_locals_clock _ (evaluateHOLFiniteState s1 body).2.clock
    · simp [hok] at hfr; exact absurd hfr not_flowingOrResumes_error

private theorem progWStepOuter_decCall {tw : BitVec 64} {B Bf : BufList} {gw gwf : List String}
    {x : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hne : x ≠ ofString "outer")
    (hBvalid : ValidBufList B) (hgwSafe : SafeStepGlobals gw)
    (hB : ∀ p ∈ Bf, p ∈ B) (hgw : ∀ g ∈ gwf, g ∈ gw)
    (hf : WorldKeepsSc WorldOK (bufRegions Bf) gwf stdKeep NoExtra fname)
    (hcont : ProgWStepOuter tw B gw cont) :
    ProgWStepOuter tw B gw (.decCall x sh fname args cont) := by
  intro F s hc hW hout htw hts hnt hfr
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
          simp only [ent, hrun]; rintro rfl; exact hnt (by simp)
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
              have hstep1 := (hspec (Or.inl ⟨v, rfl⟩)).mono_bufs hB hgw
              set s1 := setVarHOLFinite x v { cpost with locals := s.locals }
              have hs1_step : WorldStepSc (bufRegions B) gw stdKeep NoExtra s none s1 := hstep1.from_entry
              have hWs1 : WorldOK s1 := hs1_step.worldOK_bufs hBvalid hW
              have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hc
              have hout1 : s1.locals.lookup (ofString "outer") = some (.val (.word tw)) := by
                simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hout]
              obtain ⟨htw1, hts1⟩ := worldStepSc_preserves_ts32 hBvalid hgwSafe hW hs1_step htw hts
              have hstep2 := hcont s1 hs1_code hWs1 hout1 htw1 hts1 hnt hfr
              have hstep2' := hstep2.with_locals_clock (r' := (evaluateHOLFiniteState s1 cont).1)
                (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x))
                (evaluateHOLFiniteState s1 cont).2.clock
              exact WorldStepSc.trans hBvalid hgwSafe hs1_step hstep2'
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact ((hspec hres_ex).mono_bufs hB hgw).from_entry

private theorem progWStepOuter_seq {tw : BitVec 64} {B : BufList} {gw : List String} {p1 p2 : ProgHOL 64}
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw) (hp1_no : avoidsLocal (ofString "outer") p1 = true)
    (h1 : ProgWStep B gw p1) (h2 : ProgWStepOuter tw B gw p2) :
    ProgWStepOuter tw B gw (.seq p1 p2) := by
  intro F s hc hW hout htw hts hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p1).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hfr ⊢
  cases r1 with
  | none =>
    have hs1 := h1 s hc hW (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hs1; dsimp only at hs1
    have hW_mid : WorldOK mid := hs1.worldOK_bufs hB hW
    have hout_mid : mid.locals.lookup (ofString "outer") = some (.val (.word tw)) := by
      have hp := evaluate_avoidsLocal_flowing (ofString "outer") p1 hp1_no s (by rw [hr1]; exact Or.inl rfl)
      rw [hr1] at hp; exact hp.trans hout
    obtain ⟨htw_m, hts_m⟩ := worldStepSc_preserves_ts32 hB hgw hW hs1 htw hts
    have hs2 := h2 mid (hmeta.trans hc) hW_mid hout_mid htw_m hts_m hnt hfr
    exact WorldStepSc.trans hB hgw hs1 hs2
  | some r =>
    have hs1 := h1 s hc hW (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hs1
    exact hs1

private theorem progWStepOuter_of_dec_ts32 {B : BufList} {gw : List String} {body : ProgHOL 64}
    (hb : ∀ tw : BitVec 64, ProgWStepOuter tw B gw body) :
    ProgWStep B gw (.dec (ofString "outer") .one
      (.load .one (.op .add [.var .global (ofString "ts"), .const 32#64])) body) := by
  intro F s0 hc0 hW0 hnt0 hfr0
  rw [evaluateHOLFiniteState_dec_total] at hnt0 hfr0 ⊢
  rcases hev_o : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ts"), .const 32#64])) with _ | vo
  · simp [hev_o] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
  · simp only [hev_o] at hnt0 hfr0 ⊢
    obtain ⟨tw, rfl, htw_nat, hts_nz⟩ := evalAt_loadG_nz s0 hW0.1.1 "ts" 32#64 (by decide) vo hev_o
    have hsh_ok : shapeEqHOL .one (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hsh_ok, ↓reduceIte] at hnt0 hfr0 ⊢
    set s1 := setVarHOLFinite (ofString "outer") (.val (.word tw)) s0
    have hW1 : WorldOK s1 := localsFree_worldOK s0 _ s0.clock hW0
    have hs1_outer : s1.locals.lookup (ofString "outer") = some (.val (.word tw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hstep := hb tw s1 hc0 hW1 hs1_outer htw_nat hts_nz hnt0 hfr0
    exact (WorldStepSc.of_pre_locals_clock hstep).with_locals_clock
      (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 body).2.locals
        (ofString "outer", s0.locals.lookup (ofString "outer")))
      (evaluateHOLFiniteState s1 body).2.clock

theorem wkSc_destroy_storage :
    WorldKeepsSc WorldOK (bufRegions [("sk_buf", 52)]) ["heap_ptr", "journal_n"] stdKeep NoExtra
      (ofString "destroy_storage") := by
  have hB : ValidBufList [("sk_buf", 52)] := by
    intro p hp; simp at hp; subst hp
    exact ⟨64, by decide, by decide, by decide⟩
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp
  refine worldKeepsSc_of_progWStep lookup_destroy_storage ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_destroy_storage,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepOuter_of_dec_ts32 (fun tw => ?_)
  refine progWStepOuter_decCall (by decide) hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStepOuter_seq hB hgw (by decide)
    (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStepOuter_dec (by decide) ?_
  refine progWStepOuter_dec (by decide) ?_
  refine progWStepOuter_dec (by decide) ?_
  refine progWStepOuter_seq hB hgw (by decide) ?_ ?_
  · refine progWStep_while hB hgw ?_
    refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
      (worldKeepsSc_of_readOnly ro_htab_item) ?_
    refine progWStep_seq hB hgw ?_ (progWStep_assign_local _ _ _ _)
    refine progWStep_ite ?_ (progWStep_skip _ _)
    refine progWStep_decCall hB hgw (by intro p hp; exact hp) (by intro g hg; cases hg)
      worldKeepsSc_sk_make ?_
    exact progWStep_call0_htab_set_recSlot "ts" "ts+24" 24 _ _ (by simp) (by decide)
      (fun s S hT hts ht0 => nonValueSlot_ts24 s S hT hts ht0)
  · -- `.seq (.call (some (none, none)) "jdel" [.var .local "outer", .var .local "addr"]) (.return 0)`
    intro F' s' hc' hW' hout' htw' hts' hnt' hfr'
    have hmeta' := (PanRunBounded.evaluateHOLFiniteState_metadata s'
      (.call (some (none, none)) (ofString "jdel") [.var .local (ofString "outer"), .var .local (ofString "addr")])).1
    rw [evaluateHOLFiniteState_seq_line780] at hnt' hfr' ⊢
    rcases hr1 : evaluateHOLFiniteState s'
      (.call (some (none, none)) (ofString "jdel") [.var .local (ofString "outer"), .var .local (ofString "addr")]) with ⟨r1, mid⟩
    simp only [hr1] at hmeta' hnt' hfr' ⊢
    have ht_ev : evalAt s' (.var .local (ofString "outer")) = some (.val (.word tw)) := by
      simp [evalAt, evalHOLExact, toExact, hout']
    cases r1 with
    | none =>
      have hs1 := jdel_ts32_step [("sk_buf", 52)] ["heap_ptr", "journal_n"] (by simp) (by simp)
        (.var .local (ofString "outer")) (.var .local (ofString "addr"))
        s' hc' hW' tw ht_ev htw' hts' (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
      rw [hr1] at hs1; dsimp only at hs1
      have hW_mid : WorldOK mid := hs1.worldOK_bufs hB hW'
      have hs2 := progWStep_return [("sk_buf", 52)] ["heap_ptr", "journal_n"] (.const 0#64)
        mid (hmeta'.trans hc') hW_mid hnt' hfr'
      exact WorldStepSc.trans hB hgw hs1 hs2
    | some r =>
      have hs1 := jdel_ts32_step [("sk_buf", 52)] ["heap_ptr", "journal_n"] (by simp) (by simp)
        (.var .local (ofString "outer")) (.var .local (ofString "addr"))
        s' hc' hW' tw ht_ev htw' hts' (by rw [hr1]; exact hnt') (by rw [hr1]; exact hfr')
      rw [hr1] at hs1
      exact hs1

theorem wkSc_destroy_account :
    WorldKeepsSc WorldOK (bufRegions [("sk_buf", 52)]) ["heap_ptr", "journal_n"] stdKeep NoExtra
      (ofString "destroy_account") := by
  have hB : ValidBufList [("sk_buf", 52)] := by
    intro p hp; simp at hp; subst hp
    exact ⟨64, by decide, by decide, by decide⟩
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp
  refine worldKeepsSc_of_progWStep lookup_destroy_account ?_
  simp only [sourceFunctionEntry,
    Guest.Software.guestFn_set_account,
    Guest.Software.guestFn_destroy_account,
    Guest.Software.guestFn_modify_state_commit,
    Guest.Software.guestFn_clear_account_preserving_balance,
    Guest.Software.guestFn_create_ether,
    Guest.Software.guestFn_increment_nonce,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_seq hB hgw
    (progWStep_call0 (by intro p hp; exact hp) (by intro g hg; exact hg) wkSc_destroy_storage) ?_
  refine progWStep_seq hB hgw
    (progWStep_call0 (by intro p hp; cases hp) (by intro g hg; exact hg) wkSc_set_account) ?_
  exact progWStep_return _ _ _

theorem wkSc_modify_state_commit :
    WorldKeepsSc WorldOK (bufRegions [("sk_buf", 52)]) ["heap_ptr", "journal_n"] stdKeep NoExtra
      (ofString "modify_state_commit") := by
  have hB : ValidBufList [("sk_buf", 52)] := by
    intro p hp; simp at hp; subst hp
    exact ⟨64, by decide, by decide, by decide⟩
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp
  refine worldKeepsSc_of_progWStep lookup_modify_state_commit ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_modify_state_commit,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_seq hB hgw
    (progWStep_call0 (by intro p hp; cases hp) (by intro g hg; exact hg) wkSc_set_account) ?_
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly ro_acct_is_empty) ?_
  refine progWStep_seq hB hgw ?_ (progWStep_return _ _ _)
  exact progWStep_ite
    (progWStep_call0 (by intro p hp; exact hp) (by intro g hg; exact hg) wkSc_destroy_account)
    (progWStep_skip _ _)

/-! ## 9. `acct_copy` + Local Account Mutation Helper & Target Theorems -/

private theorem acct_copy_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).1) :
    let res := (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).1
    let post := (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).2
    WorldEff s post [] [] ["heap_ptr"] ∧
    (res = none → ∃ bw : BitVec 64,
      post.locals = s.locals.update (ofString "a", .val (.word bw)) ∧
      globN s "heap_ptr" ≤ bw.toNat ∧ bw.toNat + 56 ≤ heapLimit) := by
  dsimp only
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  have heff0 : WorldEff s s [] [] ["heap_ptr"] := WorldEff.refl s [] [] ["heap_ptr"] hA hcode
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "a")] with _ | vals
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
        have hent_a : ent.locals.lookup (ofString "a") = some (.val (.word aw)) := haw_c
        have heff_ent : WorldEff s ent [] [] ["heap_ptr"] := heff0.locals_clock _ _
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_acct_copy) with ⟨rc, pc⟩
        have hrun_ent : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy) = (rc, pc) := hrun
        have hnt_ent : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy)).1 ≠ some .timeOut := by
          rw [hrun_ent]; rintro rfl; simp [hrun] at hnt
        simp only [hrun] at hnt hfr ⊢
        cases rc with
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
            -- Unpack `acct_copy` on `ent` for exception:
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
                (fun hnt_mc hcr_mc => worldEff_call0_memcpy heff_m1 _ _ _ hnt_mc
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
              · -- `acct_copy` returned `rv` and assigned `.local "a" := rv`!
                -- Unpack `acct_copy` body on `ent` to get `rv = .val (.word bw)` AND `WorldEff s pc`:
                have hbody_eq2 : sourceFnBody Guest.Software.guestFn_acct_copy =
                    .decCall (ofString "b") .one (ofString "alloc") [.const 56#64]
                      (.seq
                        (.call (some (none, none)) (ofString "memcpy")
                          [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                        (.return (.var .local (ofString "b")))) := rfl
                rw [hbody_eq2] at hrun_ent
                -- Use `worldEff_decCall_alloc` for `WorldEff s pc`, AND inspect `hrun_ent` directly for `rv = .val (.word bw)`!
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
                -- Now `seq (call memcpy [b, a, 56]) (return b)` on `m1`:
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
                    have hw := worldEff_call0_memcpy heff_m1
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
                  have heff_out : WorldEff s (setVarHOLFinite (ofString "a") (.val (.word pw)) { pc with locals := s.locals })
                      [] [] ["heap_ptr"] := by
                    rw [hpc_m2]; exact heff_m2.locals_clock _ _
                  exact ⟨heff_out, fun _ => ⟨pw, rfl, hp_lo_s, hpw_hi⟩⟩
              · rename_i hbad; simp only [hsh_rv, hbad, ↓reduceIte] at hfr; exact absurd hfr not_flowingOrResumes_error
            · rename_i hbad; simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hfr; exact absurd hfr not_flowingOrResumes_error

private theorem progWStep_acctCopy_mut {B : BufList} {gw : List String}
    (hhp_in : "heap_ptr" ∈ gw) (mutProg : ProgHOL 64)
    (hmut : ∀ {F : Type} (s s1 : PanSemStateFiniteExact 64 F) (bw : BitVec 64),
      WorldEff s s1 [] [] ["heap_ptr"] →
      s1.locals = s.locals.update (ofString "a", .val (.word bw)) →
      s1.locals.lookup (ofString "a") = some (.val (.word bw)) →
      globN s "heap_ptr" ≤ bw.toNat → bw.toNat + 56 ≤ heapLimit →
      (evaluateHOLFiniteState s1 mutProg).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState s1 mutProg).1 →
      WorldEff s (evaluateHOLFiniteState s1 mutProg).2 [] [] ["heap_ptr"]) :
    ProgWStep B gw
      (.seq
        (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
          [.var .local (ofString "a")])
        mutProg) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases h1 : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")]) with ⟨r1, s1⟩
  simp only [h1] at hnt hfr ⊢
  cases r1 with
  | some cr1 =>
    have hac := acct_copy_step s hc hW.1 (by rw [h1]; exact hnt) (by rw [h1]; exact hfr)
    rw [h1] at hac
    have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s (some cr1) s1 :=
      hac.1.to_worldStep_Q hW (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
    exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp [hhp_in]) ⟨hws0, hac.1.sp_hi⟩
  | none =>
    dsimp only at hnt hfr ⊢
    have hac := acct_copy_step s hc hW.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    rw [h1] at hac; dsimp only at hac
    obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
    have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word bw)) := by
      rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hcr : ContOrRes (evaluateHOLFiniteState s1 mutProg).1 := by
      rcases hfr with h | h | h | hr
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr hr))
    have heff2 := hmut s s1 bw hac.1 hs1_loc hs1_a hbw_lo hbw_hi hnt hcr
    have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s
        (evaluateHOLFiniteState s1 mutProg).1 (evaluateHOLFiniteState s1 mutProg).2 :=
      heff2.to_worldStep_Q hW (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
    exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp [hhp_in]) ⟨hws0, heff2.sp_hi⟩

private theorem evaluateHOLFiniteState_seq_assoc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p1 p2 p3 : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq p1 (.seq p2 p3)) =
      evaluateHOLFiniteState s (.seq (.seq p1 p2) p3) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 <;> rfl

private theorem progWStep_acctCopy_mut_tail {B : BufList} {gw : List String}
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (hhp_in : "heap_ptr" ∈ gw) (mutProg tailProg : ProgHOL 64)
    (hmut : ∀ {F : Type} (s s1 : PanSemStateFiniteExact 64 F) (bw : BitVec 64),
      WorldEff s s1 [] [] ["heap_ptr"] →
      s1.locals = s.locals.update (ofString "a", .val (.word bw)) →
      s1.locals.lookup (ofString "a") = some (.val (.word bw)) →
      globN s "heap_ptr" ≤ bw.toNat → bw.toNat + 56 ≤ heapLimit →
      (evaluateHOLFiniteState s1 mutProg).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState s1 mutProg).1 →
      WorldEff s (evaluateHOLFiniteState s1 mutProg).2 [] [] ["heap_ptr"])
    (htail : ProgWStep B gw tailProg) :
    ProgWStep B gw
      (.seq
        (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
          [.var .local (ofString "a")])
        (.seq mutProg tailProg)) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_seq_assoc] at hnt hfr ⊢
  exact progWStep_seq hB hgw (progWStep_acctCopy_mut hhp_in mutProg hmut) htail s hc hW hnt hfr

private theorem safeStepGlobals_acctMut : SafeStepGlobals ["heap_ptr", "journal_n", "scratch_ptr"] := by
  intro g hg; simp at hg; rcases hg with rfl | rfl | rfl <;> simp

theorem wkSc_clear_account_preserving_balance :
    WorldKeepsSc WorldOK (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      (ofString "clear_account_preserving_balance") := by
  have hB := validBufList_acctMutBufs
  have hgw := safeStepGlobals_acctMut
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  refine worldKeepsSc_of_progWStep lookup_clear_account_preserving_balance ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_clear_account_preserving_balance,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_seq hB hgw
    (progWStep_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
      (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkSc_destroy_storage) ?_
  refine progWStep_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
    wkSc_get_account ?_
  intro F s0 hc0 hW0 hnt0 hfr0
  have hassoc : evaluateHOLFiniteState s0
      (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
        (.seq (.store (.op .add [.var .local (ofString "a"), .const 0#64]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "a"), .const 48#64]) (.var .global (ofString "empty_code_hash")))
            (.seq (.call (some (none, none)) (ofString "modify_state_commit") [.var .local (ofString "addr"), .var .local (ofString "a")])
              (.return (.const 0#64)))))) =
      evaluateHOLFiniteState s0
      (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
        (.seq
          (.seq (.store (.op .add [.var .local (ofString "a"), .const 0#64]) (.const 0#64))
            (.store (.op .add [.var .local (ofString "a"), .const 48#64]) (.var .global (ofString "empty_code_hash"))))
          (.seq (.call (some (none, none)) (ofString "modify_state_commit") [.var .local (ofString "addr"), .var .local (ofString "a")])
            (.return (.const 0#64))))) := by
    simp only [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState s0 _ with ⟨r1, s1⟩
    cases r1 with
    | some _ => rfl
    | none =>
      dsimp only
      rcases evaluateHOLFiniteState s1 _ with ⟨r2, _⟩
      cases r2 <;> rfl
  rw [hassoc] at hnt0 hfr0 ⊢
  refine progWStep_acctCopy_mut_tail hB hgw (by simp) _ _
    (fun s s1 bw heff1 _ hs1_a hbw_lo hbw_hi hnt1 hcr1 => ?_)
    (progWStep_seq hB hgw
      (progWStep_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
        (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkSc_modify_state_commit)
      (progWStep_return _ _ _))
    s0 hc0 hW0 hnt0 hfr0
  refine worldEff_seq hnt1 hcr1
    (fun _ _ => worldEff_store_word heff1 _ _
      (fun v hv => by simp [evalHOLExact] at hv; exact ⟨0#64, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, toExact, hs1_a, panOpHOL, wordOpHOL, wordOp,
          valueIsWord, valueWord] at hx
        subst hx
        have hx0 : (bw + 0#64).toNat = bw.toNat := by simp
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
    (fun m2 hm2 heff_m2 _ _ => ?_)
  have hm2_loc : m2.locals = s1.locals := by
    have hk := fun k => evaluate_avoidsLocal_flowing k
      (.store (.op .add [.var .local (ofString "a"), .const 0#64]) (.const 0#64))
      rfl s1 (by rw [hm2]; exact Or.inl rfl)
    apply HolFiniteMapExact.ext; funext k; simpa [hm2] using hk k
  exact worldEff_store_word heff_m2 _ _
    (fun v hv => by
      simp only [evalHOLExact, toExact] at hv
      obtain ⟨wech, hwech⟩ := heff_m2.arena.2.2.2.2.2.2.2.2.2 "empty_code_hash" (by decide)
      unfold GlobalWord at hwech
      rw [hwech] at hv; injection hv with hv'; exact ⟨wech, hv'.symm⟩)
    (fun x hx _ => by
      simp [evalHOLExact, evalListHOLExact, toExact, hm2_loc, hs1_a, panOpHOL, wordOpHOL, wordOp,
        valueIsWord, valueWord] at hx
      subst hx
      have hx48 : (bw + 48#64).toNat = bw.toNat + 48 := by
        apply BitVec.toNat_add_of_lt; change bw.toNat + 48 < 2 ^ 64; omega
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))

theorem wkSc_create_ether :
    WorldKeepsSc WorldOK (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      (ofString "create_ether") := by
  have hB := validBufList_acctMutBufs
  have hgw := safeStepGlobals_acctMut
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  refine worldKeepsSc_of_progWStep lookup_create_ether ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_create_ether,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
    wkSc_get_account ?_
  intro F s0 hc0 hW0 hnt0 hfr0
  rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
  rcases h1 : evaluateHOLFiniteState s0
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")]) with ⟨r1, s1⟩
  simp only [h1] at hnt0 hfr0 ⊢
  cases r1 with
  | some cr1 =>
    have hac := acct_copy_step s0 hc0 hW0.1 (by rw [h1]; exact hnt0) (by rw [h1]; exact hfr0)
    rw [h1] at hac
    have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s0 (some cr1) s1 :=
      hac.1.to_worldStep_Q hW0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
    exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, hac.1.sp_hi⟩
  | none =>
    have hac := acct_copy_step s0 hc0 hW0.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    rw [h1] at hac; dsimp only at hac
    obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
    have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word bw)) := by
      rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt0 hfr0 ⊢
    rcases hargs_nb : @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        [.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 8#64]),
         .var .local (ofString "amount")] with _ | vnb_args
    · simp [evalListHOLFinite, hargs_nb] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
    · simp only [evalListHOLFinite, hargs_nb] at hnt0 hfr0 ⊢
      rcases hl_nb : lookupCodeHOLFinite s1.code.lookup (ofString "u256_add") vnb_args with _ | ⟨bnb, cnb, rnb⟩
      · simp [hl_nb] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
      · simp only [hl_nb] at hnt0 hfr0 ⊢
        by_cases hcz1 : s1.clock = 0
        · simp [hcz1] at hnt0
        rw [if_neg hcz1] at hnt0 hfr0 ⊢
        let ent_nb := callEntryStateHOLFinite s1 cnb
        rcases hrun_nb : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb with ⟨res_nb, p_nb⟩
        have hrun_nb' : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb = (res_nb, p_nb) := hrun_nb
        simp only [hrun_nb] at hnt0 hfr0 ⊢
        cases res_nb with
        | none => exact absurd hfr0 not_flowingOrResumes_error
        | some cr_nb =>
          cases cr_nb with
          | timeOut => simp at hnt0
          | error | «break» | «continue» => exact absurd hfr0 not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr0 not_flowingOrResumes_finalFfi
          | exception eid ev =>
            dsimp only at hfr0 ⊢
            have hres_ex : Wave8Contracts.M18.Resumes (some (.exception eid ev)) := by
              rcases hfr0 with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, rfl⟩ := h
              exact Or.inr ⟨eid, ev, rfl, hne⟩
            have hro := FunSpec.at_lookup ro_u256_add s1 hac.1.code vnb_args bnb cnb rnb hl_nb
              (guestInv_callEntry s1 cnb hac.1.arena.1) (by rw [hrun_nb']; simp)
            have hro' : ((evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb).2) = _ :=
              hro (by rw [hrun_nb']; exact hres_ex)
            rw [hrun_nb'] at hro'; dsimp only at hro'
            have heff_ex : WorldEff s0 (emptyLocalsHOLFinite p_nb) [] [] ["heap_ptr"] :=
              (hac.1.of_readOnly hro').locals_clock _ p_nb.clock
            have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s0 (some (.exception eid ev))
                (emptyLocalsHOLFinite p_nb) :=
              heff_ex.to_worldStep_Q hW0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
            exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, heff_ex.sp_hi⟩
          | returned vnb =>
            dsimp only at hnt0 hfr0 ⊢
            by_cases hsh_nb : (shapeEqHOL (shapeOfHOLExact vnb) (.comb [.one, .one, .one, .one]) &&
                shapeEqHOL (shapeOfHOLExact vnb) rnb) = true
            · simp only [hsh_nb, ↓reduceIte] at hnt0 hfr0 ⊢
              have hsh_u256 : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vnb) = true := by
                have h12 : shapeEqHOL (shapeOfHOLExact vnb) (.comb [.one, .one, .one, .one]) = true := by
                  revert hsh_nb
                  cases shapeEqHOL (shapeOfHOLExact vnb) (.comb [.one, .one, .one, .one]) <;> simp
                rcases vnb with _ | fs | _
                · simp [shapeOfHOLExact, shapeEqHOL] at h12
                · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
                    try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h12; done)
                  rcases v0 with ⟨⟨_⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨_⟩⟩ | _ | _ <;>
                    rcases v2 with ⟨⟨_⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨_⟩⟩ | _ | _ <;>
                    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h12 ⊢
                · simp [shapeOfHOLExact, shapeEqHOL] at h12
              have hro := FunSpec.at_lookup ro_u256_add s1 hac.1.code vnb_args bnb cnb rnb hl_nb
                (guestInv_callEntry s1 cnb hac.1.arena.1) (by rw [hrun_nb']; simp)
              have hro' : ((evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb).2) = _ :=
                hro (by rw [hrun_nb']; exact Or.inl ⟨vnb, rfl⟩)
              rw [hrun_nb'] at hro'; dsimp only at hro'
              set s2 := setVarHOLFinite (ofString "nb") vnb { p_nb with locals := s1.locals }
              have heff2 : WorldEff s0 s2 [] [] ["heap_ptr"] :=
                (hac.1.of_readOnly hro').locals_clock _ _
              have hs2_a : s2.locals.lookup (ofString "a") = some (.val (.word bw)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_a,
                  show ofString "nb" ≠ ofString "a" by decide]
              have hs2_nb : s2.locals.lookup (ofString "nb") = some vnb := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
              rcases hst : evaluateHOLFiniteState s2
                  (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "nb"))) with ⟨rst, s3⟩
              simp only [hst] at hnt0 hfr0 ⊢
              have heff3 : WorldEff s0 s3 [] [] ["heap_ptr"] := by
                have hs3_eq : s3 = (evaluateHOLFiniteState s2
                    (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "nb")))).2 := by
                  rw [hst]
                rw [hs3_eq]
                exact worldEff_store_multi heff2 _ _ 4 (by decide)
                  (fun v hv => by
                    simp [evalHOLExact, toExact, hs2_nb] at hv
                    subst hv
                    exact flattenHOL_shape_u256 hsh_u256)
                  (fun x hx => by
                    simp [evalHOLExact, evalListHOLExact, toExact, hs2_a, panOpHOL, wordOpHOL, wordOp,
                      valueIsWord, valueWord] at hx
                    subst hx
                    have hx8 : (bw + 8#64).toNat = bw.toNat + 8 := by
                      apply BitVec.toNat_add_of_lt; change bw.toNat + 8 < 2 ^ 64; omega
                    exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩)
              have hstep03 : WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra s0 rst s3 := by
                have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s0 rst s3 :=
                  heff3.to_worldStep_Q hW0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
                exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, heff3.sp_hi⟩
              cases rst with
              | some cr_st =>
                exact hstep03.with_locals_clock _ _
              | none =>
                dsimp only at hnt0 hfr0 ⊢
                have hWs3 : WorldOK s3 := hstep03.worldOK_bufs hB hW0
                have htail_step := progWStep_seq hB hgw
                  (progWStep_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
                    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkSc_modify_state_commit)
                  (progWStep_return _ _ _)
                  s3 heff3.code hWs3 hnt0 hfr0
                exact WorldStepSc.trans hB hgw hstep03 (htail_step.with_locals_clock _ _)
            · simp [hsh_nb] at hfr0; exact absurd hfr0 not_flowingOrResumes_error

theorem wkSc_set_account_balance :
    WorldKeepsSc WorldOK (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      (ofString "set_account_balance") := by
  have hB := validBufList_acctMutBufs
  have hgw := safeStepGlobals_acctMut
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  refine ⟨_, _, _, lookup_set_account_balance, fun {F} s0 hc0 hW0 ⟨vals, hl⟩ hnt0 hres0 => ?_⟩
  have hamt_ok : ∃ vamt : ValueHOL 64,
      s0.locals.lookup (ofString "amount") = some vamt ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vamt) = true := by
    have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "set_account_balance")
      vals _ s0.locals _ hl
    simp only [lookupCodeHOLExact, lookup_set_account_balance] at hx
    rcases vals with _ | ⟨va, _ | ⟨vamt, _ | _⟩⟩
    · simp at hx
    · simp at hx
    · rcases va with ⟨⟨wa⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hx; done)
      simp [shapeOfHOLExact, shapeEqHOL, show ofString "addr" ≠ ofString "amount" by decide] at hx
      obtain ⟨hsh_amt, hL⟩ := hx
      refine ⟨vamt, ?_, hsh_amt⟩
      have := congrFun hL (ofString "amount")
      simpa [FUPDATE, show ofString "amount" ≠ ofString "addr" by decide,
        show ofString "addr" ≠ ofString "amount" by decide] using this.symm
    · simp at hx
  obtain ⟨vamt, hs0_amt, hsh_amt⟩ := hamt_ok
  have hfr0 : FlowingOrResumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_set_account_balance)).1 :=
    Or.inr (Or.inr (Or.inr hres0))
  simp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_set_account_balance,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil] at hnt0 hfr0 ⊢
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt0 hfr0 ⊢
  rcases hargs : @evalListHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      [.var .local (ofString "addr")] with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr0
    exact absurd hfr0 not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt0 hfr0 ⊢
    rcases hlk : lookupCodeHOLFinite s0.code.lookup (ofString "get_account") vs with _ | ⟨bga, cga, rga⟩
    · simp [hlk] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
    · simp only [hlk] at hnt0 hfr0 ⊢
      by_cases hcz0 : s0.clock = 0
      · simp [hcz0] at hnt0
      rw [if_neg hcz0] at hnt0 hfr0 ⊢
      let ent_ga := callEntryStateHOLFinite s0 cga
      have hWent_ga : WorldOK ent_ga := localsFree_worldOK s0 cga (s0.clock - 1) hW0
      have hmeta_ga := (PanRunBounded.evaluateHOLFiniteState_metadata ent_ga bga).1
      rcases hrun_ga : evaluateHOLFiniteState ent_ga bga with ⟨res_ga, p_ga⟩
      simp only [ent_ga] at hrun_ga hmeta_ga
      simp only [hrun_ga] at hmeta_ga hnt0 hfr0 ⊢
      have hnt_ga : (evaluateHOLFiniteState ent_ga bga).1 ≠ some .timeOut := by
        simp only [ent_ga, hrun_ga]; rintro rfl; simp at hnt0
      cases res_ga with
      | none => exact absurd hfr0 not_flowingOrResumes_error
      | some cr_ga =>
        cases cr_ga with
        | timeOut => simp at hnt0
        | error | «break» | «continue» => exact absurd hfr0 not_flowingOrResumes_error
        | finalFfi _ => exact absurd hfr0 not_flowingOrResumes_finalFfi
        | exception eid ev =>
          dsimp only at hfr0 ⊢
          have hres_ex : Resumes (some (.exception eid ev)) := by
            rcases hfr0 with h | h | h | hr <;> try simp at h
            exact hr
          have hspec := FunSpec.at_lookup wkSc_get_account s0 hc0 vs bga cga rga hlk hWent_ga hnt_ga
          simp only [ent_ga, hrun_ga] at hspec
          exact ((hspec hres_ex).mono_bufs
            (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
            (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)).from_entry
        | returned vga =>
          dsimp only at hnt0 hfr0 ⊢
          by_cases hsh_ga : (shapeEqHOL (shapeOfHOLExact vga) .one && shapeEqHOL (shapeOfHOLExact vga) rga) = true
          · simp only [hsh_ga, ↓reduceIte] at hnt0 hfr0 ⊢
            have hspec := FunSpec.at_lookup wkSc_get_account s0 hc0 vs bga cga rga hlk hWent_ga hnt_ga
            simp only [ent_ga, hrun_ga] at hspec
            set sa := setVarHOLFinite (ofString "a") vga { p_ga with locals := s0.locals }
            have hstep_ga : WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                stdKeep NoExtra s0 none sa :=
              ((hspec (Or.inl ⟨vga, rfl⟩)).mono_bufs
                (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
                (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)).from_entry
            have hWsa : WorldOK sa := hstep_ga.worldOK_bufs hB hW0
            have hsa_code : sa.code = originalRuntimeCode := hmeta_ga.trans hc0
            have hsa_amt : sa.locals.lookup (ofString "amount") = some vamt := by
              simp [sa, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_amt,
                show ofString "a" ≠ ofString "amount" by decide]
            let sabTail : ProgHOL 64 :=
              .seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                (.seq (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))
                  (.seq (.call (some (none, none)) (ofString "modify_state_commit")
                    [.var .local (ofString "addr"), .var .local (ofString "a")])
                    (.return (.const 0#64))))
            have hcont_step : WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                stdKeep NoExtra sa (evaluateHOLFiniteState sa sabTail).1 (evaluateHOLFiniteState sa sabTail).2 := by
              dsimp only [sabTail] at hnt0 hfr0 ⊢
              rw [evaluateHOLFiniteState_seq_assoc] at hnt0 hfr0 ⊢
              rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
              have hm_step : WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                  stdKeep NoExtra sa
                  (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1
                  (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).2 := by
                have hnt_m : (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1 ≠ some .timeOut := by
                  rcases hm : evaluateHOLFiniteState sa _ with ⟨rm, sm⟩
                  rw [hm] at hnt0; cases rm with | none => simp | some cm => cases cm <;> simp at hnt0 ⊢
                have hfr_m : FlowingOrResumes (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1 := by
                  rcases hm : evaluateHOLFiniteState sa _ with ⟨rm, sm⟩
                  rw [hm] at hfr0; cases rm with | none => exact Or.inl rfl | some cm => exact hfr0
                rw [evaluateHOLFiniteState_seq_line780] at hnt_m hfr_m ⊢
                rcases h1 : evaluateHOLFiniteState sa
                    (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
                      [.var .local (ofString "a")]) with ⟨r1, s1⟩
                simp only [h1] at hnt_m hfr_m ⊢
                cases r1 with
                | some cr1 =>
                  have hac := acct_copy_step sa hsa_code hWsa.1 (by rw [h1]; exact hnt_m) (by rw [h1]; exact hfr_m)
                  rw [h1] at hac
                  have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra sa (some cr1) s1 :=
                    hac.1.to_worldStep_Q hWsa (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
                  exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, hac.1.sp_hi⟩
                | none =>
                  dsimp only at hnt_m hfr_m ⊢
                  have hac := acct_copy_step sa hsa_code hWsa.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
                  rw [h1] at hac; dsimp only at hac
                  obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
                  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word bw)) := by
                    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                  have hs1_amt : s1.locals.lookup (ofString "amount") = some vamt := by
                    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsa_amt,
                      show ofString "a" ≠ ofString "amount" by decide]
                  have heff2 : WorldEff sa
                      (evaluateHOLFiniteState s1
                        (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))).2
                      [] [] ["heap_ptr"] :=
                    worldEff_store_multi hac.1 _ _ 4 (by decide)
                      (fun v hv => by
                        simp [evalHOLExact, toExact, hs1_amt] at hv
                        subst hv
                        exact flattenHOL_shape_u256 hsh_amt)
                      (fun x hx => by
                        simp [evalHOLExact, evalListHOLExact, toExact, hs1_a, panOpHOL, wordOpHOL, wordOp,
                          valueIsWord, valueWord] at hx
                        subst hx
                        have hx8 : (bw + 8#64).toNat = bw.toNat + 8 := by
                          apply BitVec.toNat_add_of_lt; change bw.toNat + 8 < 2 ^ 64; omega
                        exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩)
                  have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra sa
                      (evaluateHOLFiniteState s1
                        (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))).1
                      (evaluateHOLFiniteState s1
                        (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))).2 :=
                    heff2.to_worldStep_Q hWsa (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
                  exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, heff2.sp_hi⟩
              have hm_code := (PanRunBounded.evaluateHOLFiniteState_metadata sa
                (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                  (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1
              rcases hm : evaluateHOLFiniteState sa
                  (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                    (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))) with ⟨rm, sm⟩
              simp only [hm] at hm_step hm_code hnt0 hfr0 ⊢
              cases rm with
              | some crm => exact hm_step
              | none =>
                dsimp only at hnt0 hfr0 ⊢
                have hWsm : WorldOK sm := hm_step.worldOK_bufs hB hWsa
                have htail := progWStep_seq hB hgw
                  (progWStep_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
                    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkSc_modify_state_commit)
                  (progWStep_return _ _ _)
                  sm (hm_code.trans hsa_code) hWsm hnt0 hfr0
                exact WorldStepSc.trans hB hgw hm_step htail
            exact WorldStepSc.trans hB hgw hstep_ga (hcont_step.with_locals_clock _ _)
          · simp [hsh_ga] at hfr0; exact absurd hfr0 not_flowingOrResumes_error

theorem wkSc_increment_nonce :
    WorldKeepsSc WorldOK (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      (ofString "increment_nonce") := by
  have hB := validBufList_acctMutBufs
  have hgw := safeStepGlobals_acctMut
  refine worldKeepsSc_of_progWStep lookup_increment_nonce ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_increment_nonce,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
    wkSc_get_account ?_
  exact progWStep_acctCopy_mut_tail hB hgw (by simp) _ _
    (fun {F} s s1 bw heff1 _ hs1_a hbw_lo hbw_hi _ _ =>
      worldEff_store_word heff1 _ _
        (fun v hv => by
          rcases hld : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.load .one (.op .add [.var .local (ofString "a"), .const 0#64])) with _ | vl
          · simp [evalHOLExact, evalListHOLExact] at hv hld; rw [hld] at hv; simp at hv
          · simp [evalHOLExact, evalListHOLExact] at hv hld; rw [hld] at hv
            rcases vl with ⟨⟨wl⟩⟩ | _ | _ <;> simp [panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
            exact ⟨wl + 1#64, hv.symm⟩)
        (fun x hx _ => by
          simp [evalHOLExact, evalListHOLExact, toExact, hs1_a, panOpHOL, wordOpHOL, wordOp,
            valueIsWord, valueWord] at hx
          subst hx
          have hx0 : (bw + 0#64).toNat = bw.toNat := by simp
          exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
    (progWStep_seq hB hgw
      (progWStep_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
        (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkSc_modify_state_commit)
      (progWStep_return _ _ _))

/-! ## 10. Exported C08 Target Theorems -/

/-- `destroy_storage` (AST line 13480): relational world step with output region. -/
theorem «wk_destroy_storage» :
    WorldKeeps WorldOK (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "destroy_storage") :=
  wkSc_destroy_storage.to_worldKeeps

/-- `clear_account_preserving_balance` (AST line 13541): relational world step with output region. -/
theorem «wk_clear_account_preserving_balance» :
    WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "clear_account_preserving_balance") :=
  wkSc_clear_account_preserving_balance.to_worldKeeps

/-- `create_ether` (AST line 13629): relational world step with output region. -/
theorem «wk_create_ether» :
    WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "create_ether") :=
  wkSc_create_ether.to_worldKeeps

/-- `set_account_balance` (AST line 13647): relational world step with output region. -/
theorem «wk_set_account_balance» :
    WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "set_account_balance") :=
  wkSc_set_account_balance.to_worldKeeps

/-- `increment_nonce` (AST line 13664): relational world step with output region. -/
theorem «wk_increment_nonce» :
    WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "increment_nonce") :=
  wkSc_increment_nonce.to_worldKeeps

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
