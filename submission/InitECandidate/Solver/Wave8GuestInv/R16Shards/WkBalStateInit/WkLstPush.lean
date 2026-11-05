import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.SetLstNew

/-! Zero-sorry proof of `wk_lst_push_strong` (`lst_push` on `bo+40` / `bo+72` with `memW s l ≠ 0`). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Contracts.M08
open InitECandidate.Solver.Wave8GuestInv.M11

abbrev RetListSlot := @M13.RetListSlot
abbrev BoListArg := @M13.BoListArg

def BoListArgStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ BoListArg s ∧ memW s (locN s "l") ≠ 0

theorem lookup_lst_push :
    originalRuntimeCode.lookup (ofString "lst_push") =
      some ([(ofString "l", .one), (ofString "esz", .one)],
        sourceFnBody Guest.Software.guestFn_lst_push, .one) :=
  lookup_of_guestAst_getElem 410 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_push) rfl

private def lstPushCallees (f : MlS) : Bool :=
  f == ofString "trap_with" ||
  f == ofString "alloc" ||
  f == ofString "memcpy" ||
  f == ofString "lst_push"

private theorem lstPushCallees_noCatchableRaise :
    ∀ f, lstPushCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise lstPushCallees body = true := by
  intro f hf values body callee rs hfound
  simp only [lstPushCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((rfl | rfl) | rfl) | rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [R13Shards.lookup_alloc_r13] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [M11.lookup_memcpy] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_lst_push] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

private theorem lst_push_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_push)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise lstPushCallees lstPushCallees_noCatchableRaise
    (sourceFnBody Guest.Software.guestFn_lst_push) rfl s hcode e v hne

private theorem not_disj_self_24 (l : Nat) : ¬ Disj (l, 24) (l, 24) := by
  rintro (h | h | h | h) <;> dsimp only at h <;> omega

private def boBaseObjs {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  let bo := globN s "bo"
  let obj (p len : Nat) : Ivl := if bo = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)
  [obj (memW s (bo + 24)) (16 * memW s (bo + 80) + 16),
   obj (memW s (bo + 32)) (16 * memW s (bo + 80) + 16),
   obj (memW s (bo + 56)) 128]

private def boLstObjs {F : Type} (s : PanSemStateFiniteExact 64 F) (k : Nat) : List Ivl :=
  let bo := globN s "bo"
  let obj (p len : Nat) : Ivl := if bo = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)
  let l := memW s (bo + k)
  if bo = 0 ∨ l = 0 then [(0, 0), (0, 0)]
  else [obj l 24, obj (memW s l) (8 * memW s (l + 16))]

private theorem blockOutObjects_eq_parts {F : Type} (s : PanSemStateFiniteExact 64 F) :
    blockOutObjects s = boBaseObjs s ++ boLstObjs s 40 ++ boLstObjs s 72 := rfl

private theorem boLstObjs_eq_of_active {F : Type} (s : PanSemStateFiniteExact 64 F)
    {k l : Nat} (hbo : globN s "bo" ≠ 0) (hl_eq : memW s (globN s "bo" + k) = l)
    (hl_nz : l ≠ 0) (hp_nz : memW s l ≠ 0) (hlst : LstOK s l) :
    boLstObjs s k = [(l, 24), (memW s l, 8 * memW s (l + 16))] := by
  have hlen_nz : 8 * memW s (l + 16) ≠ 0 := by have := hlst.1; omega
  unfold boLstObjs
  simp [hbo, hl_eq, hl_nz, hp_nz, hlen_nz]

theorem bo_list_slice_props {F : Type} {s : PanSemStateFiniteExact 64 F} {l : Nat}
    (hF : FixedTyped s) (hbo_nz : globN s "bo" ≠ 0)
    (hbo_slot : l = memW s (globN s "bo" + 40) ∨ l = memW s (globN s "bo" + 72))
    (hl_nz : l ≠ 0) (hp_nz : memW s l ≠ 0) (hlst : LstOK s l) :
    (l, 24) ∈ blockOutObjects s ∧
    (memW s l, 8 * memW s (l + 16)) ∈ blockOutObjects s ∧
    (l, 24) ∈ fixedObjects s ∧
    (memW s l, 8 * memW s (l + 16)) ∈ fixedObjects s ∧
    Disj (l, 24) (memW s l, 8 * memW s (l + 16)) ∧
    (∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
      memW s (globN s "bo" + k) ≠ l →
      Disj (memW s (globN s "bo" + k), 24) (l, 24) ∧
      Disj (memW s (globN s "bo" + k), 24) (memW s l, 8 * memW s (l + 16))) := by
  have hpw_bo : (blockOutObjects s).Pairwise Disj := by
    have h1 := (List.pairwise_append.1 hF.2).1
    exact (List.pairwise_append.1 h1).2.1
  rcases hbo_slot with hl40 | hl72
  · have h40_eq := boLstObjs_eq_of_active s hbo_nz hl40.symm hl_nz hp_nz hlst
    have hbo_split : blockOutObjects s =
        boBaseObjs s ++ [(l, 24), (memW s l, 8 * memW s (l + 16))] ++ boLstObjs s 72 := by
      rw [blockOutObjects_eq_parts, h40_eq]
    have hl_bo : (l, 24) ∈ blockOutObjects s := by rw [hbo_split]; simp
    have hp_bo : (memW s l, 8 * memW s (l + 16)) ∈ blockOutObjects s := by rw [hbo_split]; simp
    have hl_fix : (l, 24) ∈ fixedObjects s :=
      List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hl_bo)))
    have hp_fix : (memW s l, 8 * memW s (l + 16)) ∈ fixedObjects s :=
      List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hp_bo)))
    rw [hbo_split] at hpw_bo
    have hpw_mid : ([(l, 24), (memW s l, 8 * memW s (l + 16))]).Pairwise Disj :=
      (List.pairwise_append.1 (List.pairwise_append.1 hpw_bo).1).2.1
    refine ⟨hl_bo, hp_bo, hl_fix, hp_fix,
      (List.pairwise_cons.1 hpw_mid).1 _ (List.mem_singleton.2 rfl), ?_⟩
    intro k hk hknz hkne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact absurd hl40.symm hkne
    · have h72_mem : (memW s (globN s "bo" + 72), 24) ∈ boLstObjs s 72 := by
        unfold boLstObjs; simp [hbo_nz, hknz]
      exact ⟨pairwise_disj_outside_slice hpw_bo (Or.inr h72_mem) (by simp),
             pairwise_disj_outside_slice hpw_bo (Or.inr h72_mem) (by simp)⟩
  · have h72_eq := boLstObjs_eq_of_active s hbo_nz hl72.symm hl_nz hp_nz hlst
    have hbo_split : blockOutObjects s =
        (boBaseObjs s ++ boLstObjs s 40) ++ [(l, 24), (memW s l, 8 * memW s (l + 16))] ++ [] := by
      rw [blockOutObjects_eq_parts, h72_eq]; simp [List.append_assoc]
    have hl_bo : (l, 24) ∈ blockOutObjects s := by rw [hbo_split]; simp
    have hp_bo : (memW s l, 8 * memW s (l + 16)) ∈ blockOutObjects s := by rw [hbo_split]; simp
    have hl_fix : (l, 24) ∈ fixedObjects s :=
      List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hl_bo)))
    have hp_fix : (memW s l, 8 * memW s (l + 16)) ∈ fixedObjects s :=
      List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hp_bo)))
    rw [hbo_split] at hpw_bo
    have hpw_mid : ([(l, 24), (memW s l, 8 * memW s (l + 16))]).Pairwise Disj :=
      (List.pairwise_append.1 (List.pairwise_append.1 hpw_bo).1).2.1
    refine ⟨hl_bo, hp_bo, hl_fix, hp_fix,
      (List.pairwise_cons.1 hpw_mid).1 _ (List.mem_singleton.2 rfl), ?_⟩
    intro k hk hknz hkne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · have h40_mem : (memW s (globN s "bo" + 40), 24) ∈ boBaseObjs s ++ boLstObjs s 40 := by
        apply List.mem_append_right
        unfold boLstObjs; simp [hbo_nz, hknz]
      exact ⟨pairwise_disj_outside_slice hpw_bo (Or.inl h40_mem) (by simp),
             pairwise_disj_outside_slice hpw_bo (Or.inl h40_mem) (by simp)⟩
    · exact absurd hl72.symm hkne

theorem bo_list_nogrow_worldStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {l n' : Nat} {ew : BitVec 64}
    (hW : WorldOK s)
    (hbo_nz : globN s "bo" ≠ 0)
    (hl_eq_loc : locN s "l" = l)
    (hbo_slot : l = memW s (globN s "bo" + 40) ∨ l = memW s (globN s "bo" + 72))
    (hl_nz : l ≠ 0)
    (hp_nz : memW s l ≠ 0)
    (heff : M11.ByteRegionEffect s post [(l + 8, 8)])
    (hn'_le : n' ≤ memW s (l + 16))
    (hl8_post : memW post (l + 8) = n')
    (hret_slot : ∀ v, r = some (.returned v) → v = .val (.word ew) ∧
      ew.toNat % 8 = 0 ∧
      Inside (ew.toNat, 8) (memW s l) (memW s l + 8 * memW s (l + 16))) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep RetListSlot s r post := by
  have hAs := hW.1
  have hinv_post : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1
  have hAp : ArenaReady post := ⟨hinv_post, arenaOK_congr heff.globals hAs.2⟩
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hag : AllocatorGrows s post := ⟨hhp, hsp⟩
  have hG : GlobalsKept ["heap_ptr"] s post := fun _ _ => by rw [heff.globals]
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s post :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hG (by decide)
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have hlst0 : LstOK s l := by
    rcases hbo_slot with hl40 | hl72
    · rw [hl40] at hl_nz ⊢
      exact hWT0.1.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 40 (by simp) hl_nz
    · rw [hl72] at hl_nz ⊢
      exact hWT0.1.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 72 (by simp) hl_nz
  obtain ⟨hl_bo0, _, hl_fix0, _, _, _⟩ :=
    bo_list_slice_props hWT0.2.2.1 hbo_nz hbo_slot hl_nz hp_nz hlst0
  rcases hWT0.2.2.1.1 _ hl_fix0 with h0 | ⟨hal_l0, hw_l0⟩
  · simp at h0
  have hl_hi : l + 24 ≤ 2 ^ 64 :=
    (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_l0).2
  have hunhit_of_disj : ∀ i : Ivl, Disj i (l, 24) → M08IvlUnhit s post i := by
    intro i hdj a ha8 hi1 hi2
    apply heff.cell_frame a
    intro x hx hch
    simp only [List.mem_singleton] at hx
    subst hx
    obtain ⟨hc1, hc2⟩ := hch
    dsimp only at hc1 hc2
    rcases hdj with d | d | d | d <;> omega
  have hl_w0 : memW post l = memW s l := by
    have hl_lt : l < 2 ^ 64 := by omega
    have hm := heff.cell_frame (BitVec.ofNat 64 l) (fun x hx hch => by
      simp only [List.mem_singleton] at hx; subst hx
      obtain ⟨hc1, hc2⟩ := hch
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl_lt] at hc1 hc2
      dsimp only at hc1 hc2; omega)
    unfold memW; rw [hm]
  have hl_w16 : memW post (l + 16) = memW s (l + 16) := by
    have hl_lt : l + 16 < 2 ^ 64 := by omega
    have hm := heff.cell_frame (BitVec.ofNat 64 (l + 16)) (fun x hx hch => by
      simp only [List.mem_singleton] at hx; subst hx
      obtain ⟨hc1, hc2⟩ := hch
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl_lt] at hc1 hc2
      dsimp only at hc1 hc2; omega)
    unfold memW; rw [hm]
  have hRK : RecordsKept (fun _ => []) stdKeep s post := by
    intro ⟨rec_nm, rec_ks⟩ hrec hgnz k hk _
    have hrec_sz : ∃ sz, (rec_nm, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, M13.stdKeep, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨40, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
    have hmf := M11.typedRec_in_fixedObjects s htr
    simp only [hgnz, ↓reduceIte] at hmf
    have hgb_mem : (globN s rec_nm, sz) ∈
        (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] := by
      apply List.mem_append_left
      have hr_gb : (rec_nm, sz) ∈ globalBuffers :=
        Wave8Contracts.M08.typedRecord_mem_globalBuffers htr
      have hm : (globN s rec_nm, if globN s rec_nm = 0 then 0 else sz) ∈
          globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) :=
        List.mem_map.2 ⟨(rec_nm, sz), hr_gb, rfl⟩
      rwa [if_neg hgnz] at hm
    have hpw_pre := List.pairwise_append.1 (List.pairwise_append.1 hWT0.2.2.1.2).1
    have hdj_l : Disj (globN s rec_nm, sz) (l, 24) := hpw_pre.2.2 _ hgb_mem _ hl_bo0
    rcases hWT0.2.2.1.1 _ hmf with h0 | ⟨hal_r, hw_r⟩
    · exact absurd h0 hsz_nz
    have hhi_r := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_r).2
    have hg8 : (globN s rec_nm) % 8 = 0 := hw_r.1
    change memW post (globN s rec_nm + k) = memW s (globN s rec_nm + k)
    exact Wave8Contracts.M08.memW_eq_of_ivlUnhit
      (hunhit_of_disj _ hdj_l) (by omega) hhi_r ⟨by omega, by omega⟩
  refine ⟨hAp, hhp, hG, hRK, fun S Nd hWT _ => ?_⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hlst : LstOK s l := by
    rcases hbo_slot with hl40 | hl72
    · rw [hl40] at hl_nz ⊢
      exact hT.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 40 (by simp) hl_nz
    · rw [hl72] at hl_nz ⊢
      exact hT.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 72 (by simp) hl_nz
  obtain ⟨hl_bo, hp_bo, hl_fix, hp_fix, hdj_lp, hbo_other_dj⟩ :=
    bo_list_slice_props hF hbo_nz hbo_slot hl_nz hp_nz hlst
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, M08IvlUnhit s post i := fun t ht i hi =>
    hunhit_of_disj i (((hT.2.1 t ht).2 i hi).2 _ hl_fix)
  have hpw_top := List.pairwise_append.1 hF.2
  have hpw_pre := List.pairwise_append.1 hpw_top.1
  have hu_gb_jr : ∀ i ∈
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
      [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")],
      M08IvlUnhit s post i := fun i hi =>
    hunhit_of_disj i (hpw_pre.2.2 i hi _ hl_bo)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s post i := fun i hi _ =>
    hunhit_of_disj i (disj_flip (hpw_top.2.2 _ (List.mem_append_right _ hl_bo) i hi))
  have hmem_gb : ∀ (nm : String) (sz : Nat), (nm, sz) ∈ globalBuffers → globN s nm ≠ 0 →
      (globN s nm, sz) ∈
        (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] :=
    fun nm sz hgb hnz => by
      apply List.mem_append_left
      have hm : (globN s nm, if globN s nm = 0 then 0 else sz) ∈
          globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) :=
        List.mem_map.2 ⟨(nm, sz), hgb, rfl⟩
      rwa [if_neg hnz] at hm
  have hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s post (globN s "ws", 40) := fun hnz =>
    hu_gb_jr _ (hmem_gb "ws" 40 (by decide) hnz)
  have hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s post (globN s "bs", 80) := fun hnz =>
    hu_gb_jr _ (hmem_gb "bs" 80 (by decide) hnz)
  have hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s post (globN s "ts", 72) := fun hnz =>
    hu_gb_jr _ (hmem_gb "ts" 72 (by decide) hnz)
  have hu_bo : globN s "bo" ≠ 0 → M08IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hu_gb_jr _ (hmem_gb "bo" 88 (by decide) hnz)
  have hu_jr : globN s "journal_cap" ≠ 0 →
      M08IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz =>
    hu_gb_jr _ (List.mem_append_right _ (by simp [hnz]))
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    Wave8Contracts.M08.mem0_8_16_eq_of_domain_writes
      (fun a hne => Classical.byContradiction fun hna => hne (heff.out_dom a hna)) hAs.1
  have hlst_l_post : LstOK post l := by
    unfold LstOK
    rw [hl8_post, hl_w16]
    exact ⟨hlst.1, hn'_le⟩
  have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hws_g : globN post "ws" = globN s "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have htr_ws : ("ws", 40) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_bs : ("bs", 80) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_ts : ("ts", 72) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_bo : ("bo", 88) ∈ Wave8Contracts.M08.typedRecords := by decide
  have hbo_words : ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using Wave8Contracts.M08.rec_word_eq_of_unhit
      hAs.2 hF "bo" 88 htr_bo hbo_g hbo_nz (hu_bo hbo_nz) hk_in.1 hk_in.2
  have hbo_lst_hdr_other : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
      memW s (globN s "bo" + k) ≠ l →
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) ∧
      memW post (memW s (globN s "bo" + k) + 8) = memW s (memW s (globN s "bo" + k) + 8) ∧
      memW post (memW s (globN s "bo" + k) + 16) = memW s (memW s (globN s "bo" + k) + 16) := by
    intro k hk hknz hkne
    have hk_bo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> simp [blockOutObjects, hbo_nz, hknz]
    have hk_fix : (memW s (globN s "bo" + k), 24) ∈ fixedObjects s :=
      List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hk_bo)))
    rcases hF.1 _ hk_fix with h0 | ⟨hal_k, hw_k⟩
    · simp at h0
    have hhi_k := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_k).2
    have hk8 : (memW s (globN s "bo" + k)) % 8 = 0 := hw_k.1
    have huk := hunhit_of_disj _ (hbo_other_dj k hk hknz hkne).1
    refine ⟨?_, ?_, ?_⟩
    · simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit huk (by omega) hhi_k ⟨by omega, by omega⟩
    · exact Wave8Contracts.M08.memW_eq_of_ivlUnhit huk (by omega) hhi_k ⟨by omega, by omega⟩
    · exact Wave8Contracts.M08.memW_eq_of_ivlUnhit huk (by omega) hhi_k ⟨by omega, by omega⟩
  have hbo_eq : blockOutObjects post = blockOutObjects s := by
    unfold blockOutObjects
    simp only [hbo_g, hbo_nz, false_or,
      hbo_words 24 (by simp), hbo_words 32 (by simp), hbo_words 40 (by simp),
      hbo_words 56 (by simp), hbo_words 72 (by simp), hbo_words 80 (by simp)]
    congr 1; congr 1
    · by_cases h40z : memW s (globN s "bo" + 40) = 0
      · simp [h40z]
      · by_cases h40l : memW s (globN s "bo" + 40) = l
        · simp [h40z, h40l, hl_w0, hl_w16]
        · obtain ⟨e0, _, e16⟩ := hbo_lst_hdr_other 40 (by simp) h40z h40l
          simp [h40z, e0, e16]
    · by_cases h72z : memW s (globN s "bo" + 72) = 0
      · simp [h72z]
      · by_cases h72l : memW s (globN s "bo" + 72) = l
        · simp [h72z, h72l, hl_w0, hl_w16]
        · obtain ⟨e0, _, e16⟩ := hbo_lst_hdr_other 72 (by simp) h72z h72l
          simp [h72z, e0, e16]
  have hbo_ok_post : globN post "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat),
      memW post (globN post "bo" + k) ≠ 0 → LstOK post (memW post (globN post "bo" + k)) := by
    intro _ k hk hknz
    have hk_eq : memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact hbo_words 40 (by simp)
      · exact hbo_words 72 (by simp)
    rw [hbo_g, hk_eq] at hknz ⊢
    by_cases hkl : memW s (globN s "bo" + k) = l
    · rw [hkl]; exact hlst_l_post
    · obtain ⟨_, e8, e16⟩ := hbo_lst_hdr_other k hk hknz hkl
      have hold := hT.2.2.2.2.2.2.2.2.2.2.1 hbo_nz k hk hknz
      unfold LstOK at hold ⊢; rw [e8, e16]; exact hold
  have hbal_part := Wave8Contracts.M08.balObjects_eq_of_unhit
    hAs.2 hT hF hba_g hu_tab hu_bal hm0
  have hfix_eq := Wave8Contracts.M08.fixedObjects_eq_of_parts
    hgs hbo_eq hbal_part.1
  have hF_post := Wave8Contracts.M08.fixedTyped_transfer
    hAs.1 hAp.1 hag hF hfix_eq
  have hjr_part := Wave8Contracts.M08.journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hgs hu_ts hu_jr
  have hwrs_eq := Wave8Contracts.M08.worldRoleSlots_eq_of_unhit
    hAs.2 hT hF hgs hu_tab hu_ws hu_bs hu_ts hu_bal hm0
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hne_mem : nodeIvl s n ∈ nodeExtents s Nd :=
      List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
    exact hunhit_of_disj _ ((hTr.2.1 _ hne_mem).2 _ hl_fix)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have hnp_mem : nodePath s n ∈ nodeExtents s Nd :=
      List.mem_flatMap.2 ⟨n, hn, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)⟩
    have hnp_eq : nodePath s n = (memW s (n + 32), memW s (n + 40)) := by
      simp [nodePath, h12, hlen0]
    have hdj_l : Disj (memW s (n + 32), memW s (n + 40)) (l, 24) := by
      rw [← hnp_eq]; exact (hTr.2.1 _ hnp_mem).2 _ hl_fix
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, _, hin_p, _⟩
    · exact absurd h0 hlen0
    have hlim264 : heapLimit ≤ 2 ^ 64 := by decide
    have hbk_lt : memW s (n + 32) + k < 2 ^ 64 := by
      have := hin_p.2; dsimp at this; omega
    exact heff.byte_frame (memW s (n + 32) + k) hbk_lt (fun x hx hbi => by
      simp only [List.mem_singleton] at hx; subst hx
      obtain ⟨hb1, hb2⟩ := hbi
      dsimp only at hb1 hb2
      rcases hdj_l with d | d | d | d <;> omega)
  have hnd_part := Wave8Contracts.M08.nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧
      htabFootprint post t = htabFootprint s t := by
    have h264_he : heapEnd ≤ 2 ^ 64 := by decide
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit
      ht8 hhi (hu_tab t ht _ ht_fp)
  have hflat_fp : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) :=
    List.flatMap_congr fun t ht => (htab_fp_hdr t ht).2
  have howned_eq : M13.worldOwned post S Nd = M13.worldOwned s S Nd := by
    change S.flatMap (htabFootprint post) ++ fixedObjects post ++ nodeExtents post Nd =
      S.flatMap (htabFootprint s) ++ fixedObjects s ++ nodeExtents s Nd
    rw [hflat_fp, hfix_eq, hnd_part.2]
  have hrecs_eq : balRecords post = balRecords s :=
    Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_ok_post, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2, hfix_eq]
      exact ⟨Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, ((hTt t ht).2 i hi).2⟩⟩
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp t ht u hu_mem hne
    · intro k hk hnz
      rw [hws_g] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g hnz (hu_ts hnz) htk.1 htk.2]
      exact htsR k hk hnz
    · intro g hg; rw [hgs.2.1 g hg]; exact hgR g hg
    · intro hnz hm
      rw [hbs_g] at hnz
      have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "bs" 80 htr_bs hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact Wave8Contracts.M08.htabValuesIn_congr_unhit
        (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (hbsN hnz hm)
    · intro hnz hm
      rw [hts_g] at hnz
      have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ts" 72 htr_ts hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact Wave8Contracts.M08.htabValuesIn_congr_unhit
        (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (htsN hnz hm)
    · intro ad had
      obtain ⟨e0, e8, _, hk_ok, hl_ok⟩ := hbal_part.2 ad had
      rw [hrecs_eq] at had
      have had_old := hbalT ad had
      exact ⟨by rw [e0]; exact had_old.1, by rw [e8]; exact had_old.2.1, hk_ok, hl_ok⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_part.1]
      refine ⟨fun a ha => ?_, hroles.2.1, hroles.2.2⟩
      obtain ⟨haS, hak⟩ := hroles.1 a ha
      rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
      exact ⟨haS, hak⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hnd_part.1, ?_, ?_⟩
    · intro o ho
      rw [hnd_part.2] at ho
      refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rw [(htab_fp_hdr t ht).2] at hi
        exact (hTr.2.1 o ho).1 t ht i hi
      · rw [hfix_eq] at hj
        exact (hTr.2.1 o ho).2 j hj
    · intro hnz
      rw [hws_g] at hnz
      have hw24 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hwf32 := (hT.2.1 _ hm).1
      have hu32 := hu_tab _ hm
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := Wave8Contracts.M08.htabValues_eq_of_unhit hwf32 hu32
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 hm i hi
  have hfr : FrameOutside s post (worldOwned s S Nd ++ ([] : List Ivl) ++ [freeGap s]) (heapFree s) := by
    intro a ha _
    apply heff.cell_frame a
    intro x hx hch
    simp only [List.mem_singleton] at hx; subst hx
    obtain ⟨hc1, hc2⟩ := hch
    dsimp only at hc1 hc2
    have hl_ow : (l, 24) ∈ worldOwned s S Nd ++ ([] : List Ivl) ++ [freeGap s] := by
      apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_append_left _ (List.mem_append_right _ hl_fix)
    exact ha (l, 24) hl_ow ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hQ_post : RetListSlot s r post S Nd := by
    intro v hv
    obtain ⟨rfl, hal8, hin⟩ := hret_slot v hv
    refine ⟨ew, rfl, hal8, ?_⟩
    rw [hl_eq_loc, hl_w0, hl_w16]
    exact hin
  exact ⟨S, Nd, fun _ hx => hx, ⟨hT_post, hjr_part.2, hF_post, hTr_post⟩,
    fun o ho => Or.inr (Or.inl ⟨o, by rw [howned_eq] at ho; exact ho, le_rfl, le_rfl⟩),
    hfr, hQ_post⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal
