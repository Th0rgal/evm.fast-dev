import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2b0WorldStepCodeBase

/-!
# Scratch Rung B4c2b: Read/Lookup World Callees (`WorldKeepsCodeSc`)

Derives `WorldKeepsCodeSc` (including `CodeRootsValsEq` and `NonTrieStep`) for all
read/lookup world callees (`acct_new`, `acct_empty`, `ws_get_account_optional`,
`ws_storage_root_of`, `get_pre_state_account`, `account_exists`, `is_account_alive`,
`account_deployable`, `ext_code_of`, etc.).
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
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28


/-! ## 4. Non-Code Value-Slot `htab_set` & Read/Lookup World Callees (`WorldKeepsCodeSc`) -/

/-- Role-slot disjointness from both value tables AND code-DB roots (`ws+16`, `bs+48`, `ts+48`). -/
def NonCodeValueSlot {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (t0 : Nat) : Prop :=
  (t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0)) ∧
  (globN s "ws" ≠ 0 → memW s (globN s "ws" + 16) ≠ t0) ∧
  (globN s "bs" ≠ 0 → memW s (globN s "bs" + 48) ≠ t0) ∧
  (globN s "ts" ≠ 0 → memW s (globN s "ts" + 48) ≠ t0)

theorem nonCodeValueSlot_of_wrs {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (t0 : Nat) (roleName : String)
    (hT : TablesTyped s S) (ht0_nz : t0 ≠ 0) (ht0_S : t0 ∈ S)
    (ht0_wrs : (t0, roleName) ∈ worldRoleSlots s)
    (hne_bs32 : "bs+32" ≠ roleName) (hne_ts32 : "ts+32" ≠ roleName)
    (hne_ba : "bal_accounts" ≠ roleName) (hne_bstor : "bal.stor" ≠ roleName)
    (hne_ws32 : "ws+32" ≠ roleName)
    (hne_ws16 : "ws+16" ≠ roleName) (hne_bs48 : "bs+48" ≠ roleName)
    (hne_ts48 : "ts+48" ≠ roleName) :
    NonCodeValueSlot s S t0 := by
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨nonValueSlot_of_wrs s S t0 roleName hT ht0_nz ht0_S ht0_wrs
    hne_bs32 hne_ts32 hne_ba hne_bstor hne_ws32, ?_, ?_, ?_⟩
  · intro hws heq
    have h16_nz : memW s (globN s "ws" + 16) ≠ 0 := by rw [heq]; exact ht0_nz
    have hm : (memW s (globN s "ws" + 16), "ws+16") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ws" 16 "ws+16" hws h16_nz
      apply List.mem_append.2; left; apply List.mem_append.2; left
      unfold recRoles; simp [hws]
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs hne_ws16 heq
  · intro hbs heq
    have h48_nz : memW s (globN s "bs" + 48) ≠ 0 := by rw [heq]; exact ht0_nz
    have hm : (memW s (globN s "bs" + 48), "bs+48") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "bs" 48 "bs+48" hbs h48_nz
      apply List.mem_append.2; left; apply List.mem_append.2; right
      unfold recRoles; simp [hbs]
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs hne_bs48 heq
  · intro hts heq
    have h48_nz : memW s (globN s "ts" + 48) ≠ 0 := by rw [heq]; exact ht0_nz
    have hm : (memW s (globN s "ts" + 48), "ts+48") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ts" 48 "ts+48" hts h48_nz
      apply List.mem_append.2; right
      unfold recRoles; simp [hts]
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs hne_ts48 heq

theorem nonCodeValueSlot_bs72 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hbs_nz : globN s "bs" ≠ 0)
    (ht0_nz : memW s (globN s "bs" + (72 : BitVec 64).toNat) ≠ 0) :
    NonCodeValueSlot s S (memW s (globN s "bs" + (72 : BitVec 64).toNat)) := by
  have hc : (72 : BitVec 64).toNat = 72 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S := (nonValueSlot_bs72 s S hT hbs_nz (by rwa [hc])).1
  have ht0_wrs : (memW s (globN s "bs" + 72), "bs+72") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "bs" 72 "bs+72" hbs_nz ht0_nz
    apply List.mem_append.2; left; apply List.mem_append.2; right
    unfold recRoles; simp [hbs_nz]
  exact nonCodeValueSlot_of_wrs s S _ "bs+72" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem nonCodeValueSlot_ts8 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + (8 : BitVec 64).toNat) ≠ 0) :
    NonCodeValueSlot s S (memW s (globN s "ts" + (8 : BitVec 64).toNat)) := by
  have hc : (8 : BitVec 64).toNat = 8 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S := (nonValueSlot_ts8 s S hT hts_nz (by rwa [hc])).1
  have ht0_wrs : (memW s (globN s "ts" + 8), "ts+8") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 8 "ts+8" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact nonCodeValueSlot_of_wrs s S _ "ts+8" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem nonCodeValueSlot_ts16 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + (16 : BitVec 64).toNat) ≠ 0) :
    NonCodeValueSlot s S (memW s (globN s "ts" + (16 : BitVec 64).toNat)) := by
  have hc : (16 : BitVec 64).toNat = 16 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S := (nonValueSlot_ts16 s S hT hts_nz (by rwa [hc])).1
  have ht0_wrs : (memW s (globN s "ts" + 16), "ts+16") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 16 "ts+16" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact nonCodeValueSlot_of_wrs s S _ "ts+16" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem nonCodeValueSlot_ts24 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + (24 : BitVec 64).toNat) ≠ 0) :
    NonCodeValueSlot s S (memW s (globN s "ts" + (24 : BitVec 64).toNat)) := by
  have hc : (24 : BitVec 64).toNat = 24 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S := (nonValueSlot_ts24 s S hT hts_nz (by rwa [hc])).1
  have ht0_wrs : (memW s (globN s "ts" + 24), "ts+24") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 24 "ts+24" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact nonCodeValueSlot_of_wrs s S _ "ts+24" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem nonCodeValueSlot_ts40 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + (40 : BitVec 64).toNat) ≠ 0) :
    NonCodeValueSlot s S (memW s (globN s "ts" + (40 : BitVec 64).toNat)) := by
  have hc : (40 : BitVec 64).toNat = 40 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S := (nonValueSlot_ts40 s S hT hts_nz (by rwa [hc])).1
  have ht0_wrs : (memW s (globN s "ts" + 40), "ts+40") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 40 "ts+40" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact nonCodeValueSlot_of_wrs s S _ "ts+40" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem nonCodeValueSlot_ts56 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + (56 : BitVec 64).toNat) ≠ 0) :
    NonCodeValueSlot s S (memW s (globN s "ts" + (56 : BitVec 64).toNat)) := by
  have hc : (56 : BitVec 64).toNat = 56 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S : memW s (globN s "ts" + 56) ∈ S := by
    rcases hT.2.2.2.2.2.1 56 (by simp [tsTableSlots]) hts_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (memW s (globN s "ts" + 56), "ts+56") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 56 "ts+56" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact nonCodeValueSlot_of_wrs s S _ "ts+56" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem worldStepCodeSc_of_htabExit_nonCodeValue {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {gw : List String}
    (hW0 : WorldOK s) (hbe : post.be = s.be)
    (hg_kept : GlobalsKept gw s post)
    (hg_nonHeap : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k)
    {t0 : Nat}
    (ht0_mem : ∀ S, TablesTyped s S → NonCodeValueSlot s S t0)
    (hAp : ArenaReady post) (hwf_t0 : HtabWF post t0)
    (hhdr0_t0 : hdr post t0 0 = hdr s t0 0)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfp_t0 : ∀ i ∈ htabFootprint post t0, Allocated post i ∧
      ((∃ j ∈ htabFootprint s t0, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))))
    (hfr : FrameOutside s post (htabFootprint s t0) (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    WorldStepCodeSc [] gw s r post := by
  have hbase := worldStepSc_of_htabExit_nonValue (r := r) hW0 hbe hg_kept hg_nonHeap
    (fun S hT => (ht0_mem S hT).1) hAp hwf_t0 hhdr0_t0 hhp hfp_t0 hfr
  obtain ⟨⟨hAp', hhp', hG', hK', hWs⟩, hsc⟩ := hbase
  have hAs := hW0.1
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have h1 := hAs.2.2.2.2.2.2.1; have h2 := hAp.2.2.2.2.2.2.1; omega
  have hcode : ∀ S Nd, WorldTypedWith s S Nd →
      CodeRootsValsEq s r post S Nd := by
    intro S Nd hWT g k hm hgnz htnz
    obtain ⟨⟨ht0_S, _⟩, hne_ws16, hne_bs48, hne_ts48⟩ := ht0_mem S hWT.1
    have ht0_al : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
      have hw := ((hWT.1.2.1 t0 ht0_S).1.1 j hj).2
      exact ⟨hw.1, hw.2.1⟩
    have htS := codeRoot_mem_S hWT.1 hm hgnz htnz
    have hne_t0 : memW s (globN s g + k) ≠ t0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne_ws16 hgnz
      · exact hne_bs48 hgnz
      · exact hne_ts48 hgnz
    apply R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit (hWT.1.2.1 _ htS).1
    intro i hi
    exact ivlUnhit_of_frameOutside_aligned
      (htabFootprint_len_pos (hWT.1.2.1 _ htS).1 hi) hfr ht0_al hf_al
      (fun j hj => hWT.1.2.2.1 _ htS t0 ht0_S hne_t0 i hi j hj)
      (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr ((hWT.1.2.1 _ htS).2 i hi).1))
  refine ⟨⟨⟨hAp', hhp', hG', hK', fun S Nd hWT hD => ?_⟩, hsc⟩, ?_⟩
  · obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hWs S Nd hWT hD
    exact ⟨S', Nd', hsub, hWT', hOG, hFO, hcode S Nd hWT⟩
  · intro S Nd hWT _
    have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
      globN_eq_of_lookup (hg_nonHeap (ofString "scratch_ptr") (by decide))
    have hag : AllocatorGrows s post := ⟨hhp, by rw [hsp_eq]⟩
    have hcore : ∀ g ∈ R10Shards.P26_P28.coreWorldGlobals, globN post g = globN s g := fun g hg => by
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
    obtain ⟨hT, hJ, hF, hTr⟩ := hWT
    obtain ⟨⟨ht0_S, hno_bs32, hno_ts32, hno_ba, hno_ad, hno_ws32⟩, _⟩ := ht0_mem S hT
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
      have hne : ofString gn.1 ∉ (["heap_ptr"] : List String).map ofString := by revert gn hgn; decide
      simp [globN_eq_of_lookup (hg_nonHeap (ofString gn.1) hne)]
    obtain ⟨hjr_eq, hJ_post⟩ := Fast_C08WkShard03.journalRoleSlots_eq_of_unhit
      hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hcore hu_ts hu_jr
    have hwrs_eq := worldRoleSlots_eq_of_unhit_except hAs.2 hT hF hcore hu_other
      ⟨hno_bs32, hno_ts32, hno_ba, hno_ad⟩ hu_ws hu_bs hu_ts hu_bal hm0
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
        exact Fast_C08WkShard03.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_ts32 hnz)) (fun _ hx => hx) (htsN hnz hmem)
      · intro ad had
        have had_s : ad ∈ balRecords s := by
          rwa [Fast_C08WkShard03.balRecords_eq_of_unhit hT0 (hcore "bal_accounts" (by decide)) (fun hnz => by
            rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0 | hm; exact absurd h0 hnz; exact hu_other _ hm hno_ba)] at had
        obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq.2 ad had
        exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
      · unfold RolesOK at hroles ⊢; rw [hwrs_eq, hjr_eq]
        refine ⟨fun a ha => ?_, hroles.2⟩
        obtain ⟨haS, hkl⟩ := hroles.1 a ha
        by_cases ha0 : a.1 = t0
        · rw [ha0] at hkl ⊢; exact ⟨ht0_S, hhdr0_t0.trans hkl⟩
        · exact ⟨haS, ((hother_fp a.1 haS ha0).1 0 (by omega)).trans hkl⟩
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
    refine ⟨⟨Nd, ⟨hT_post, hJ_post, hF_post, hTr_post⟩⟩, ?_, ?_⟩
    · intro o ho; unfold nonTrieOwned at ho
      rcases List.mem_append.1 ho with ho_tab | ho_fix
      · obtain ⟨u, hu, hi⟩ := List.mem_flatMap.1 ho_tab
        by_cases hu0 : u = t0
        · subst hu0
          rcases (hfp_t0 o hi).2 with ⟨j, hj, hin⟩ | hfresh
          · refine Or.inr (Or.inl ⟨j, ?_, hin⟩); unfold nonTrieOwned
            exact List.mem_append_left _ (List.mem_flatMap.2 ⟨u, ht0_S, hj⟩)
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

theorem progWStepCode_call0_htab_set_recSlot {B : BufList} {gw : List String}
    (recName roleName : String) (off : BitVec 64)
    (kExp vExp : ExpHOL 64)
    (hhp_in : "heap_ptr" ∈ gw)
    (hoff_lt : off.toNat < sourceBase)
    (hslot_nonVal : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat),
      TablesTyped s S → globN s recName ≠ 0 → memW s (globN s recName + off.toNat) ≠ 0 →
      NonCodeValueSlot s S (memW s (globN s recName + off.toNat))) :
    ProgWStepCode B gw
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString recName), .const off]), kExp, vExp]) := by
  have _ := roleName
  intro F s hcode hW hnt hfr
  set argsL : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .global (ofString recName), .const off]), kExp, vExp]
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        obtain ⟨v1, _, _, he1, _, _, hc_t, _, _⟩ := callee_param_three s (ofString "htab_set")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact EvmFrameSpecs.lookup_htab_set) _ _ _ values body' callee ret' hargs_fin hl
        obtain ⟨tw, rfl, htw_nat, hrec_nz⟩ := evalAt_loadG_nz s hW.1.1 recName off hoff_lt v1 he1
        have hloc_t : locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s recName + off.toNat) := by
          simp [locN, callEntryStateHOLFinite, hc_t, htw_nat]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        have hbe_post : post.be = s.be := by
          have inv := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').2.2.1
          rw [hrun] at inv; exact inv
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
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨e', v', h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : noCatchableRaise trapOnlyCallees body' = true :=
              trapOnlyCallees_good (ofString "htab_set") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
              body' hbody_ok (callEntryStateHOLFinite s callee) hcode eid ev hne
            rw [hrun] at hno; exact hno rfl
          | returned v =>
            dsimp only at hfr ⊢
            split
            · have hnz_at := FunSpec.at_lookup EvmFrameSpecs.nz_htab_set s hcode values body' callee ret' hl
                (guestInv_callEntry s callee hW.1.1) (by rw [hrun]; simp)
              rw [hrun] at hnz_at
              have ht0_nz : memW s (globN s recName + off.toNat) ≠ 0 := by
                rw [← hloc_t]; exact hnz_at (Or.inl ⟨v, rfl⟩)
              have hArgWF : HtabArgWF (callEntryStateHOLFinite s callee) := by
                obtain ⟨hAs, S, hT, _⟩ := hW
                have ht0_S := (hslot_nonVal s S hT hrec_nz ht0_nz).1.1
                refine ⟨localsFree_arenaReady s _ _ hAs, ?_, ?_⟩
                · rw [hloc_t]; exact (htabWF_with_locals s callee (s.clock - 1) _).2 (hT.2.1 _ ht0_S).1
                · rw [hloc_t]; exact fun i hi => ((hT.2.1 _ ht0_S).2 i hi).1
              have hexit := FunSpec.at_lookup htab_set_spec s hcode values body' callee ret' hl
                hArgWF (by rw [hrun]; simp)
              rw [hrun] at hexit
              have hex := hexit v rfl
              dsimp only [HtabExit] at hex
              rw [hloc_t] at hex
              change let t := memW s (globN s recName + off.toNat)
                let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
                ArenaReady post ∧ HtabWF post t ∧ hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
                globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
                (∀ i ∈ htabFootprint post t, Allocated post i ∧
                  ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
                FrameOutside s post (htabFootprint s t) fresh ∧
                (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
                  s.globals.lookup k = post.globals.lookup k) at hex
              obtain ⟨hAp, hwf_t0, hh0, _, hhp, hfp_t0, hfr_t0, hg_t0⟩ := hex
              have hstep0 : WorldStepCodeSc [] ["heap_ptr"] s none post :=
                worldStepCodeSc_of_htabExit_nonCodeValue hW hbe_post hg_t0 hg_t0
                  (fun S hT => hslot_nonVal s S hT hrec_nz ht0_nz)
                  hAp hwf_t0 hh0 hhp hfp_t0 hfr_t0
              exact worldStepCodeSc_mono_bufs
                (fun _ h => by cases h)
                (fun g hg => by simp at hg; subst hg; exact hhp_in)
                (worldStepCodeSc_with_locals_clock hstep0 s.locals post.clock)
            · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem lookup_get_pre_state_account :
    originalRuntimeCode.lookup (ofString "get_pre_state_account") =
      some ((sourceFunctionEntry Guest.Software.guestFn_get_pre_state_account).2) :=
  lookup_of_guestAst_getElem 373 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_pre_state_account) rfl

theorem lookup_account_exists :
    originalRuntimeCode.lookup (ofString "account_exists") =
      some ((sourceFunctionEntry Guest.Software.guestFn_account_exists).2) :=
  lookup_of_guestAst_getElem 381 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_account_exists) rfl

theorem lookup_is_account_alive :
    originalRuntimeCode.lookup (ofString "is_account_alive") =
      some ((sourceFunctionEntry Guest.Software.guestFn_is_account_alive).2) :=
  lookup_of_guestAst_getElem 386 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_is_account_alive) rfl

private theorem acct_new_params_code {vals : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "acct_new") vals =
      some (body, callee, rs)) :
    ∃ (wn wc : BitVec 64) (vb : ValueHOL 64),
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vb) = true ∧
      callee.lookup (ofString "nonce") = some (.val (.word wn)) ∧
      callee.lookup (ofString "balance") = some vb ∧
      callee.lookup (ofString "code_hash") = some (.val (.word wc)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "acct_new")
    vals body callee rs hl
  simp only [lookupCodeHOLExact, lookup_acct_new] at hx
  rcases vals with _ | ⟨vn, _ | ⟨vb, _ | ⟨vc, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases vn with ⟨⟨wn⟩⟩ | _ | _ <;> rcases vc with ⟨⟨wc⟩⟩ | _ | _ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL] at hx)
    simp [shapeOfHOLExact, shapeEqHOL,
      show ofString "nonce" ≠ ofString "balance" by decide,
      show ofString "nonce" ≠ ofString "code_hash" by decide,
      show ofString "balance" ≠ ofString "code_hash" by decide] at hx
    obtain ⟨hsh_b, _, hL, _⟩ := hx
    refine ⟨wn, wc, vb, hsh_b, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [show ofString "nonce" ≠ ofString "balance" by decide,
        show ofString "nonce" ≠ ofString "code_hash" by decide,
        show ofString "balance" ≠ ofString "nonce" by decide,
        show ofString "balance" ≠ ofString "code_hash" by decide,
        show ofString "code_hash" ≠ ofString "nonce" by decide,
        show ofString "code_hash" ≠ ofString "balance" by decide])
  · simp at hx

theorem wkCodeSc_acct_new :
    WorldKeepsCodeSc [] ["heap_ptr"] (ofString "acct_new") := by
  refine ⟨_, _, _, lookup_acct_new, ?_⟩
  intro F s hc hWOK ⟨vals, hl⟩ hnt hres
  obtain ⟨wn, wc, vb, hsh_b, hlk_n, hlk_b, hlk_c⟩ := acct_new_params_code hl
  have heff := worldEff_acct_new s s (Rl := bufRegions [] s) (B := []) (gw := ["heap_ptr"])
    (by decide) (WorldEff.refl s (bufRegions [] s) [] ["heap_ptr"] hWOK.1 hc)
    hsh_b hlk_n hlk_b hlk_c hnt hres
  exact worldEff_to_worldStepCodeSc hWOK (by decide) (by intro p hp; cases hp) (by decide) heff

theorem wkCodeSc_acct_empty :
    WorldKeepsCodeSc [] ["heap_ptr"] (ofString "acct_empty") := by
  have hB := posBufList_nil
  have hgw : SafeStepGlobals ["heap_ptr"] := by intro g hg; simp at hg; subst hg; simp
  refine worldKeepsCodeSc_of_progWStepCode lookup_acct_empty ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_acct_empty,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; exact hg)
    wkCodeSc_acct_new ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_ws_get_account_optional :
    WorldKeepsCodeSc wsAcctBufs ["heap_ptr", "scratch_ptr"]
      (ofString "ws_get_account_optional") := by
  refine ⟨_, _, _, lookup_ws_get_account_optional_top, ?_⟩
  intro F s hc hWOK _ hnt hres
  have heff := worldEff_ws_get_account_optional s s hWOK.1.2
    (WorldEff.refl s [] wsBufs wsGw hWOK.1 hc) hnt hres
  have heff' : WorldEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2
      (bufRegions wsAcctBufs s) wsBufs wsGw :=
    heff.mono (fun _ hiv => by cases hiv) (fun _ h => h) (fun _ h => h)
  exact worldEff_to_worldStepCodeSc hWOK (by decide) validBufList_wsAcctBufs (by decide) heff'

theorem wkCodeSc_ws_storage_root_of :
    WorldKeepsCodeSc wsAcctBufs ["heap_ptr", "scratch_ptr"]
      (ofString "ws_storage_root_of") := by
  refine ⟨_, _, _, lookup_ws_storage_root_of_top, ?_⟩
  intro F s hc hWOK _ hnt hres
  have heff := worldEff_ws_storage_root_of s s hWOK.1.2
    (WorldEff.refl s [] wsBufs wsGw hWOK.1 hc) hnt hres
  have heff' : WorldEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_storage_root_of)).2
      (bufRegions wsAcctBufs s) wsBufs wsGw :=
    heff.mono (fun _ hiv => by cases hiv) (fun _ h => h) (fun _ h => h)
  exact worldEff_to_worldStepCodeSc hWOK (by decide) validBufList_wsAcctBufs (by decide) heff'

theorem wkCodeSc_record_pre_state_read :
    WorldKeepsCodeSc [] ["heap_ptr"] (ofString "record_pre_state_read") := by
  have hB := posBufList_nil
  have hgw : SafeStepGlobals ["heap_ptr"] := by intro g hg; simp at hg; subst hg; simp
  refine worldKeepsCodeSc_of_progWStepCode lookup_record_pre_state_read ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_record_pre_state_read,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_seq hB hgw ?_ (progWStepCode_return _ _ _)
  exact progWStepCode_call0_htab_set_recSlot "bs" "bs+72" 72 _ _ (by simp) (by decide)
    (fun s S hT hbs ht0 => nonCodeValueSlot_bs72 s S hT hbs ht0)

theorem wkCodeSc_mark_account_created :
    WorldKeepsCodeSc [] ["heap_ptr"] (ofString "mark_account_created") := by
  have hB := posBufList_nil
  have hgw : SafeStepGlobals ["heap_ptr"] := by intro g hg; simp at hg; subst hg; simp
  refine worldKeepsCodeSc_of_progWStepCode lookup_mark_account_created ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_mark_account_created,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_seq hB hgw ?_ (progWStepCode_return _ _ _)
  exact progWStepCode_call0_htab_set_recSlot "ts" "ts+56" 56 _ _ (by simp) (by decide)
    (fun s S hT hts ht0 => nonCodeValueSlot_ts56 s S hT hts ht0)

theorem wkCodeSc_get_code :
    WorldKeepsCodeSc [("sk_buf", 52)] ["heap_ptr"] (ofString "get_code") := by
  have hB := posBufList_sk
  have hgw : SafeStepGlobals ["heap_ptr"] := by intro g hg; simp at hg; subst hg; simp
  refine worldKeepsCodeSc_of_progWStepCode lookup_get_code ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_code,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsCodeSc_of_readOnly EvmFrameSpecs.ro_memeq) ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsCodeSc_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  refine progWStepCode_seq hB hgw
    (progWStepCode_call_local (by intro p hp; cases hp) (by intro g hg; cases hg)
      (worldKeepsCodeSc_of_readOnly EvmFrameSpecs.ro_htab_get)) ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  refine progWStepCode_decCall hB hgw (by intro p hp; exact hp) (by intro g hg; cases hg)
    wkCodeSc_sk_make ?_
  refine progWStepCode_seq hB hgw
    (progWStepCode_call0_htab_set_recSlot "ts" "ts+40" 40 _ _ (by simp) (by decide)
      (fun s S hT hts ht0 => nonCodeValueSlot_ts40 s S hT hts ht0)) ?_
  refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsCodeSc_of_readOnly ro_ws_get_code) ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_ws_account_has_storage :
    WorldKeepsCodeSc wsAcctBufs ["heap_ptr", "scratch_ptr"]
      (ofString "ws_account_has_storage") := by
  have hB := posBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsCodeSc_of_progWStepCode lookup_ws_account_has_storage ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_ws_account_has_storage,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkCodeSc_ws_storage_root_of ?_
  refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsCodeSc_of_readOnly EvmFrameSpecs.ro_memeq) ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_get_pre_state_account_optional :
    WorldKeepsCodeSc wsAcctBufs ["heap_ptr", "scratch_ptr"]
      (ofString "get_pre_state_account_optional") := by
  have hB := posBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsCodeSc_of_progWStepCode lookup_get_pre_state_account_optional ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_pre_state_account_optional,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_seq hB hgw
    (progWStepCode_call0_htab_set_recSlot "ts" "ts+8" 8 _ _ (by simp) (by decide)
      (fun s S hT hts ht0 => nonCodeValueSlot_ts8 s S hT hts ht0)) ?_
  refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsCodeSc_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  refine progWStepCode_seq hB hgw
    (progWStepCode_call0 (by intro p hp; cases hp) (by intro g hg; simp at hg; subst hg; simp)
      wkCodeSc_record_pre_state_read) ?_
  refine progWStepCode_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkCodeSc_ws_get_account_optional ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_get_pre_state_account :
    WorldKeepsCodeSc wsAcctBufs ["heap_ptr", "scratch_ptr"]
      (ofString "get_pre_state_account") := by
  have hB := posBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsCodeSc_of_progWStepCode lookup_get_pre_state_account ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_pre_state_account,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkCodeSc_get_pre_state_account_optional ?_
  refine progWStepCode_seq hB hgw
    (progWStepCode_ite
      (progWStepCode_call_local (by intro p hp; cases hp) (by intro g hg; simp at hg; subst hg; simp)
        wkCodeSc_acct_empty)
      (progWStepCode_skip _ _)) ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_get_account_optional :
    WorldKeepsCodeSc wsAcctBufs ["heap_ptr", "scratch_ptr"]
      (ofString "get_account_optional") := by
  have hB := posBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsCodeSc_of_progWStepCode lookup_get_account_optional ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_account_optional,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_seq hB hgw
    (progWStepCode_call0_htab_set_recSlot "ts" "ts+8" 8 _ _ (by simp) (by decide)
      (fun s S hT hts ht0 => nonCodeValueSlot_ts8 s S hT hts ht0)) ?_
  refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsCodeSc_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  refine progWStepCode_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkCodeSc_get_pre_state_account_optional ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_get_account :
    WorldKeepsCodeSc wsAcctBufs ["heap_ptr", "scratch_ptr"]
      (ofString "get_account") := by
  have hB := posBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsCodeSc_of_progWStepCode lookup_get_account ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_account,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkCodeSc_get_account_optional ?_
  refine progWStepCode_seq hB hgw
    (progWStepCode_ite
      (progWStepCode_call_local (by intro p hp; cases hp) (by intro g hg; simp at hg; subst hg; simp)
        wkCodeSc_acct_empty)
      (progWStepCode_skip _ _)) ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_account_exists :
    WorldKeepsCodeSc wsAcctBufs ["heap_ptr", "scratch_ptr"]
      (ofString "account_exists") := by
  have hB := posBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsCodeSc_of_progWStepCode lookup_account_exists ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_account_exists,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkCodeSc_get_account_optional ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_is_account_alive :
    WorldKeepsCodeSc wsAcctBufs ["heap_ptr", "scratch_ptr"]
      (ofString "is_account_alive") := by
  have hB := posBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsCodeSc_of_progWStepCode lookup_is_account_alive ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_is_account_alive,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkCodeSc_get_account_optional ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsCodeSc_of_readOnly ro_acct_is_empty) ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_account_has_storage :
    WorldKeepsCodeSc wsAcctBufs ["heap_ptr", "scratch_ptr"]
      (ofString "account_has_storage") := by
  have hB := posBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsCodeSc_of_progWStepCode lookup_account_has_storage ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_account_has_storage,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsCodeSc_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStepCode_seq hB hgw
    (progWStepCode_ite (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) (progWStepCode_skip _ _)) ?_
  refine progWStepCode_seq hB hgw
    (progWStepCode_call_local (by intro p hp; cases hp) (by intro g hg; cases hg)
      (worldKeepsCodeSc_of_readOnly EvmFrameSpecs.ro_htab_get)) ?_
  refine progWStepCode_seq hB hgw
    (progWStepCode_ite (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) (progWStepCode_skip _ _)) ?_
  refine progWStepCode_seq hB hgw
    (progWStepCode_call0 (by intro p hp; cases hp) (by intro g hg; simp at hg; subst hg; simp)
      wkCodeSc_record_pre_state_read) ?_
  refine progWStepCode_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkCodeSc_ws_account_has_storage ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_account_deployable :
    WorldKeepsCodeSc wsAcctBufs ["heap_ptr", "scratch_ptr"]
      (ofString "account_deployable") := by
  have hB := posBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsCodeSc_of_progWStepCode lookup_account_deployable ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_account_deployable,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkCodeSc_get_account ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsCodeSc_of_readOnly EvmFrameSpecs.ro_memeq) ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  refine progWStepCode_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkCodeSc_account_has_storage ?_
  refine progWStepCode_seq hB hgw (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_ext_code_of :
    WorldKeepsCodeSc extCodeBufs ["heap_ptr", "scratch_ptr"]
      (ofString "ext_code_of") := by
  have hB := posBufList_extCodeBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsCodeSc_of_progWStepCode lookup_ext_code_of ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_ext_code_of,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs, extCodeBufs] at hp ⊢; exact hp.imp_right (fun h => h.imp_right Or.inl))
    (fun _ h => h)
    wkCodeSc_get_account ?_
  refine progWStepCode_decCall hB hgw
    (by intro p hp; simp at hp; subst hp; simp [extCodeBufs])
    (by intro g hg; simp at hg; subst hg; simp)
    wkCodeSc_get_code ?_
  exact progWStepCode_return _ _ _

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
