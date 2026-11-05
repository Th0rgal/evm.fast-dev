import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.SetLstNew

/-! Complete proof of `wk_lst_push_strong` (`lst_push` on `bo+40` / `bo+72` with `memW s l ≠ 0`). -/

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

theorem bo_list_grow_worldStep {F : Type}
    {s0 m post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {l np cap : Nat} {ew : BitVec 64}
    (hW : WorldOK s0)
    (hbo_nz : globN s0 "bo" ≠ 0)
    (hl_eq_loc : locN s0 "l" = l)
    (hbo_slot : l = memW s0 (globN s0 "bo" + 40) ∨ l = memW s0 (globN s0 "bo" + 72))
    (hl_nz : l ≠ 0)
    (hp_nz : memW s0 l ≠ 0)
    (hcap_eq : memW s0 (l + 16) = cap)
    (hAm : ArenaReady m)
    (hm_mem : m.memory = s0.memory)
    (hm_be : m.be = s0.be)
    (hm_gl : ∀ k : MlS, k ≠ ofString "heap_ptr" → s0.globals.lookup k = m.globals.lookup k)
    (hnp_eq : np = globN s0 "heap_ptr")
    (hhp_m : globN m "heap_ptr" = np + 2 * 8 * cap)
    (heff : M11.ByteRegionEffect m post [(np, 2 * 8 * cap), (l, 24)])
    (hl0_post : memW post l = np)
    (hl8_post : memW post (l + 8) ≤ 2 * cap)
    (hl16_post : memW post (l + 16) = 2 * cap)
    (hret_slot : ∀ v, r = some (.returned v) → v = .val (.word ew) ∧
      ew.toNat % 8 = 0 ∧
      Inside (ew.toNat, 8) np (np + 8 * (2 * cap))) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep RetListSlot s0 r post := by
  have hAs := hW.1
  have hinv_post : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAm.1
  have hAp : ArenaReady post := ⟨hinv_post, arenaOK_congr heff.globals hAm.2⟩
  have hglob_mp : ∀ nm, globN post nm = globN m nm := fun nm => by simp [globN, heff.globals]
  have hhp_post : globN post "heap_ptr" = np + 2 * 8 * cap := by rw [hglob_mp, hhp_m]
  have hhp_le : globN s0 "heap_ptr" ≤ globN post "heap_ptr" := by omega
  have hsp_eq : globN post "scratch_ptr" = globN s0 "scratch_ptr" := by
    rw [hglob_mp]
    exact Wave8Contracts.M08.globN_eq_of_lookup (hm_gl (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s0 post := ⟨hhp_le, by rw [hsp_eq]⟩
  have hG : GlobalsKept ["heap_ptr"] s0 post := by
    intro g hg
    have hg_ne : g ≠ ofString "heap_ptr" := by
      intro rfl; exact hg (List.mem_singleton.2 rfl)
    rw [heff.globals]
    exact hm_gl g hg_ne
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s0 post :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hG (by decide)
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s0 S0).1 hWT0_ex
  have hlst0 : LstOK s0 l := by
    rcases hbo_slot with hl40 | hl72
    · rw [hl40] at hl_nz ⊢
      exact hWT0.1.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 40 (by simp) hl_nz
    · rw [hl72] at hl_nz ⊢
      exact hWT0.1.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 72 (by simp) hl_nz
  obtain ⟨hl_bo0, _, hl_fix0, _, _, _⟩ :=
    bo_list_slice_props hWT0.2.2.1 hbo_nz hbo_slot hl_nz hp_nz hlst0
  have hcap_pos : 1 ≤ cap := by rw [← hcap_eq]; exact hlst0.1
  have hsb_pos : 0 < sourceBase := by decide
  have hnp_nz : np ≠ 0 := by rw [hnp_eq]; have := hAs.2.1; omega
  rcases hWT0.2.2.1.1 _ hl_fix0 with h0 | ⟨hal_l0, _⟩
  · simp at h0
  have hnew_sz_eq : 2 * 8 * cap = 8 * (2 * cap) := by ring
  have hin_new : Inside (np, 8 * (2 * cap)) (globN s0 "heap_ptr") (globN post "heap_ptr") :=
    ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hal_new : Allocated post (np, 8 * (2 * cap)) := by
    left
    exact ⟨le_trans hAs.2.1 (by dsimp only; omega), by dsimp only; omega⟩
  have hnp8 : np % 8 = 0 := by rw [hnp_eq]; exact hAs.2.2.2.2.2.2.1
  have hsz8 : (8 * (2 * cap)) % 8 = 0 := by omega
  have hw_new : WordsOK post (np, 8 * (2 * cap)) :=
    M13.wordsOK_of_allocated hAp hal_new hnp8 hsz8
  have hdj_new_l : Disj (l, 24) (np, 8 * (2 * cap)) :=
    disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_l0 hin_new)
  have hunhit_of_disj : ∀ i : Ivl, Allocated s0 i → Disj i (l, 24) →
      M08IvlUnhit s0 post i := by
    intro i hal_i hdj_l a ha8 hi1 hi2
    have hdj_n : Disj i (np, 2 * 8 * cap) := by
      rw [hnew_sz_eq]
      exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_i hin_new)
    have hm_a := heff.cell_frame a (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2; rcases hdj_n with d | d | d | d <;> omega
      · dsimp only at hc1 hc2; rcases hdj_l with d | d | d | d <;> omega)
    rw [hm_a, hm_mem]
  have hRK : RecordsKept (fun _ => []) stdKeep s0 post := by
    intro ⟨rec_nm, rec_ks⟩ hrec hgnz k hk _
    have hrec_sz : ∃ sz, (rec_nm, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, M13.stdKeep, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨40, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
    have hmf := M11.typedRec_in_fixedObjects s0 htr
    simp only [hgnz, ↓reduceIte] at hmf
    have hgb_mem : (globN s0 rec_nm, sz) ∈
        (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")] := by
      apply List.mem_append_left
      have hr_gb : (rec_nm, sz) ∈ globalBuffers :=
        Wave8Contracts.M08.typedRecord_mem_globalBuffers htr
      have hm : (globN s0 rec_nm, if globN s0 rec_nm = 0 then 0 else sz) ∈
          globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2) :=
        List.mem_map.2 ⟨(rec_nm, sz), hr_gb, rfl⟩
      rwa [if_neg hgnz] at hm
    have hpw_pre := List.pairwise_append.1 (List.pairwise_append.1 hWT0.2.2.1.2).1
    have hdj_l : Disj (globN s0 rec_nm, sz) (l, 24) := hpw_pre.2.2 _ hgb_mem _ hl_bo0
    rcases hWT0.2.2.1.1 _ hmf with h0 | ⟨hal_r, hw_r⟩
    · exact absurd h0 hsz_nz
    have hhi_r := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_r).2
    have hg8 : (globN s0 rec_nm) % 8 = 0 := hw_r.1
    change memW post (globN s0 rec_nm + k) = memW s0 (globN s0 rec_nm + k)
    exact Wave8Contracts.M08.memW_eq_of_ivlUnhit
      (hunhit_of_disj _ hal_r hdj_l) (by omega) hhi_r ⟨by omega, by omega⟩
  refine ⟨hAp, hhp_le, hG, hRK, fun S Nd hWT _ => ?_⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hlst : LstOK s0 l := by
    rcases hbo_slot with hl40 | hl72
    · rw [hl40] at hl_nz ⊢
      exact hT.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 40 (by simp) hl_nz
    · rw [hl72] at hl_nz ⊢
      exact hT.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 72 (by simp) hl_nz
  obtain ⟨hl_bo, _, hl_fix, _, _, hbo_other_dj⟩ :=
    bo_list_slice_props hF hbo_nz hbo_slot hl_nz hp_nz hlst
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s0 t, M08IvlUnhit s0 post i := fun t ht i hi =>
    hunhit_of_disj i ((hT.2.1 t ht).2 i hi).1 (((hT.2.1 t ht).2 i hi).2 _ hl_fix)
  have hpw_top := List.pairwise_append.1 hF.2
  have hpw_pre := List.pairwise_append.1 hpw_top.1
  have hu_gb_jr : ∀ i ∈
      (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
      [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")],
      M08IvlUnhit s0 post i := by
    intro i hi
    have hi_fix : i ∈ fixedObjects s0 :=
      List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hi)))
    rcases hF.1 i hi_fix with h0 | ⟨hal_i, _⟩
    · intro a _ ha1 ha2; omega
    · exact hunhit_of_disj i hal_i (hpw_pre.2.2 i hi _ hl_bo)
  have hu_bal : ∀ i ∈ balObjects s0, i.2 ≠ 0 → M08IvlUnhit s0 post i := by
    intro i hi hnz_sz
    have hi_fix : i ∈ fixedObjects s0 := List.mem_append.2 (Or.inr hi)
    rcases hF.1 i hi_fix with h0 | ⟨hal_i, _⟩
    · exact absurd h0 hnz_sz
    · exact hunhit_of_disj i hal_i (disj_flip (hpw_top.2.2 _ (List.mem_append_right _ hl_bo) i hi))
  have hmem_gb : ∀ (nm : String) (sz : Nat), (nm, sz) ∈ globalBuffers → globN s0 nm ≠ 0 →
      (globN s0 nm, sz) ∈
        (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")] :=
    fun nm sz hgb hnz => by
      apply List.mem_append_left
      have hm : (globN s0 nm, if globN s0 nm = 0 then 0 else sz) ∈
          globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2) :=
        List.mem_map.2 ⟨(nm, sz), hgb, rfl⟩
      rwa [if_neg hnz] at hm
  have hu_ws : globN s0 "ws" ≠ 0 → M08IvlUnhit s0 post (globN s0 "ws", 40) := fun hnz =>
    hu_gb_jr _ (hmem_gb "ws" 40 (by decide) hnz)
  have hu_bs : globN s0 "bs" ≠ 0 → M08IvlUnhit s0 post (globN s0 "bs", 80) := fun hnz =>
    hu_gb_jr _ (hmem_gb "bs" 80 (by decide) hnz)
  have hu_ts : globN s0 "ts" ≠ 0 → M08IvlUnhit s0 post (globN s0 "ts", 72) := fun hnz =>
    hu_gb_jr _ (hmem_gb "ts" 72 (by decide) hnz)
  have hu_bo : globN s0 "bo" ≠ 0 → M08IvlUnhit s0 post (globN s0 "bo", 88) := fun hnz =>
    hu_gb_jr _ (hmem_gb "bo" 88 (by decide) hnz)
  have hu_jr : globN s0 "journal_cap" ≠ 0 →
      M08IvlUnhit s0 post (globN s0 "journal", 32 * globN s0 "journal_cap") := fun hnz =>
    hu_gb_jr _ (List.mem_append_right _ (by simp [hnz]))
  have hm0 : memW post 0 = memW s0 0 ∧ memW post 8 = memW s0 8 ∧ memW post 16 = memW s0 16 := by
    have hdom_writes : ∀ a : BitVec 64, post.memory a ≠ s0.memory a → s0.memaddrs a := by
      intro a hne
      apply Classical.byContradiction
      intro hna
      have hna_m : ¬ m.memaddrs a := by
        rw [hAm.1.memaddrs, ← hAs.1.memaddrs]
        exact hna
      have heq := heff.out_dom a hna_m
      rw [hm_mem] at heq
      exact hne heq
    exact Wave8Contracts.M08.mem0_8_16_eq_of_domain_writes hdom_writes hAs.1
  have hlst_l_post : LstOK post l := by
    unfold LstOK
    rw [hl16_post]
    exact ⟨by omega, hl8_post⟩
  have hbo_g : globN post "bo" = globN s0 "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hws_g : globN post "ws" = globN s0 "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s0 "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s0 "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hba_g : globN post "bal_accounts" = globN s0 "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have htr_ws : ("ws", 40) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_bs : ("bs", 80) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_ts : ("ts", 72) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_bo : ("bo", 88) ∈ Wave8Contracts.M08.typedRecords := by decide
  have hbo_words : ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s0 "bo" + k) = memW s0 (globN s0 "bo" + k) := fun k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using Wave8Contracts.M08.rec_word_eq_of_unhit
      hAs.2 hF "bo" 88 htr_bo hbo_g hbo_nz (hu_bo hbo_nz) hk_in.1 hk_in.2
  have hbo_lst_hdr_other : ∀ k ∈ ([40, 72] : List Nat), memW s0 (globN s0 "bo" + k) ≠ 0 →
      memW s0 (globN s0 "bo" + k) ≠ l →
      memW post (memW s0 (globN s0 "bo" + k)) = memW s0 (memW s0 (globN s0 "bo" + k)) ∧
      memW post (memW s0 (globN s0 "bo" + k) + 8) = memW s0 (memW s0 (globN s0 "bo" + k) + 8) ∧
      memW post (memW s0 (globN s0 "bo" + k) + 16) = memW s0 (memW s0 (globN s0 "bo" + k) + 16) := by
    intro k hk hknz hkne
    have hk_bo : (memW s0 (globN s0 "bo" + k), 24) ∈ blockOutObjects s0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> simp [blockOutObjects, hbo_nz, hknz]
    have hk_fix : (memW s0 (globN s0 "bo" + k), 24) ∈ fixedObjects s0 :=
      List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hk_bo)))
    rcases hF.1 _ hk_fix with h0 | ⟨hal_k, hw_k⟩
    · simp at h0
    have hhi_k := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_k).2
    have hk8 : (memW s0 (globN s0 "bo" + k)) % 8 = 0 := hw_k.1
    have huk := hunhit_of_disj _ hal_k (hbo_other_dj k hk hknz hkne).1
    refine ⟨?_, ?_, ?_⟩
    · simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit huk (by omega) hhi_k ⟨by omega, by omega⟩
    · exact Wave8Contracts.M08.memW_eq_of_ivlUnhit huk (by omega) hhi_k ⟨by omega, by omega⟩
    · exact Wave8Contracts.M08.memW_eq_of_ivlUnhit huk (by omega) hhi_k ⟨by omega, by omega⟩
  have hbo_base_eq : boBaseObjs post = boBaseObjs s0 := by
    unfold boBaseObjs
    simp only [hbo_g, hbo_words 24 (by simp), hbo_words 32 (by simp),
      hbo_words 56 (by simp), hbo_words 80 (by simp)]
  have hbo_ok_post : globN post "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat),
      memW post (globN post "bo" + k) ≠ 0 → LstOK post (memW post (globN post "bo" + k)) := by
    intro _ k hk hknz
    have hk_eq : memW post (globN s0 "bo" + k) = memW s0 (globN s0 "bo" + k) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact hbo_words 40 (by simp)
      · exact hbo_words 72 (by simp)
    rw [hbo_g, hk_eq] at hknz ⊢
    by_cases hkl : memW s0 (globN s0 "bo" + k) = l
    · rw [hkl]; exact hlst_l_post
    · obtain ⟨_, e8, e16⟩ := hbo_lst_hdr_other k hk hknz hkl
      have hold := hT.2.2.2.2.2.2.2.2.2.2.1 hbo_nz k hk hknz
      unfold LstOK at hold ⊢; rw [e8, e16]; exact hold
  have hbal_part := Wave8Contracts.M08.balObjects_eq_of_unhit
    hAs.2 hT hF hba_g hu_tab hu_bal hm0
  have hgb_map_eq : (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) =
      (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) :=
    List.map_congr_left fun gn hgn => by rw [hgs.1 gn hgn]
  have hjr_ivl_eq : (if globN post "journal_cap" = 0 then 0 else globN post "journal", 32 * globN post "journal_cap") =
      (if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap") := by
    rw [hgs.2.2.1, hgs.2.2.2.1]
  have hslice_fix : ∃ L1 L2 : List Ivl,
      fixedObjects s0 = L1 ++ [(l, 24), (memW s0 l, 8 * cap)] ++ L2 ∧
      fixedObjects post = L1 ++ [(l, 24), (np, 8 * (2 * cap))] ++ L2 := by
    have hpw_bo : (blockOutObjects s0).Pairwise Disj := hpw_pre.2.1
    let gb_jr := (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
      [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")]
    rcases hbo_slot with hl40 | hl72
    · have h40_s0 := boLstObjs_eq_of_active s0 hbo_nz hl40.symm hl_nz hp_nz hlst
      have h40_post : boLstObjs post 40 = [(l, 24), (np, 8 * (2 * cap))] := by
        have h40_eq_p : memW post (globN post "bo" + 40) = l := by
          rw [hbo_g, hbo_words 40 (by simp), ← hl40]
        have hp_post_nz : memW post l ≠ 0 := by rw [hl0_post]; exact hnp_nz
        have h := boLstObjs_eq_of_active post (by rw [hbo_g]; exact hbo_nz)
          h40_eq_p hl_nz hp_post_nz hlst_l_post
        rwa [hl0_post, hl16_post] at h
      have h72_ne_l : memW s0 (globN s0 "bo" + 72) ≠ l := by
        intro h72l
        have hbo_split : blockOutObjects s0 =
            boBaseObjs s0 ++ [(l, 24), (memW s0 l, 8 * memW s0 (l + 16))] ++ boLstObjs s0 72 := by
          rw [blockOutObjects_eq_parts, h40_s0]
        rw [hbo_split] at hpw_bo
        have h72_mem : (l, 24) ∈ boLstObjs s0 72 := by
          unfold boLstObjs; simp [hbo_nz, h72l, hl_nz]
        exact not_disj_self_24 l (pairwise_disj_outside_slice hpw_bo (Or.inr h72_mem) (by simp))
      have h72_post : boLstObjs post 72 = boLstObjs s0 72 := by
        unfold boLstObjs; dsimp only
        rw [hbo_g, hbo_words 72 (by simp)]
        by_cases h72z : memW s0 (globN s0 "bo" + 72) = 0
        · simp [h72z]
        · obtain ⟨e0, _, e16⟩ := hbo_lst_hdr_other 72 (by simp) h72z h72_ne_l
          simp [hbo_nz, h72z, e0, e16]
      refine ⟨gb_jr ++ boBaseObjs s0, boLstObjs s0 72 ++ balObjects s0, ?_, ?_⟩
      · unfold fixedObjects
        rw [blockOutObjects_eq_parts, h40_s0, hcap_eq]
        simp [gb_jr, List.append_assoc]
      · unfold fixedObjects
        rw [hgb_map_eq, hjr_ivl_eq, blockOutObjects_eq_parts, hbo_base_eq, h40_post, h72_post, hbal_part.1]
        simp [gb_jr, List.append_assoc]
    · have h72_s0 := boLstObjs_eq_of_active s0 hbo_nz hl72.symm hl_nz hp_nz hlst
      have h72_post : boLstObjs post 72 = [(l, 24), (np, 8 * (2 * cap))] := by
        have h72_eq_p : memW post (globN post "bo" + 72) = l := by
          rw [hbo_g, hbo_words 72 (by simp), ← hl72]
        have hp_post_nz : memW post l ≠ 0 := by rw [hl0_post]; exact hnp_nz
        have h := boLstObjs_eq_of_active post (by rw [hbo_g]; exact hbo_nz)
          h72_eq_p hl_nz hp_post_nz hlst_l_post
        rwa [hl0_post, hl16_post] at h
      have h40_ne_l : memW s0 (globN s0 "bo" + 40) ≠ l := by
        intro h40l
        have hbo_split : blockOutObjects s0 =
            (boBaseObjs s0 ++ boLstObjs s0 40) ++ [(l, 24), (memW s0 l, 8 * memW s0 (l + 16))] ++ [] := by
          rw [blockOutObjects_eq_parts, h72_s0]; simp [List.append_assoc]
        rw [hbo_split] at hpw_bo
        have h40_mem : (l, 24) ∈ boBaseObjs s0 ++ boLstObjs s0 40 := by
          apply List.mem_append_right
          unfold boLstObjs; simp [hbo_nz, h40l, hl_nz]
        exact not_disj_self_24 l (pairwise_disj_outside_slice hpw_bo (Or.inl h40_mem) (by simp))
      have h40_post : boLstObjs post 40 = boLstObjs s0 40 := by
        unfold boLstObjs; dsimp only
        rw [hbo_g, hbo_words 40 (by simp)]
        by_cases h40z : memW s0 (globN s0 "bo" + 40) = 0
        · simp [h40z]
        · obtain ⟨e0, _, e16⟩ := hbo_lst_hdr_other 40 (by simp) h40z h40_ne_l
          simp [hbo_nz, h40z, e0, e16]
      refine ⟨gb_jr ++ boBaseObjs s0 ++ boLstObjs s0 40, balObjects s0, ?_, ?_⟩
      · unfold fixedObjects
        rw [blockOutObjects_eq_parts, h72_s0, hcap_eq]
        simp [gb_jr, List.append_assoc]
      · unfold fixedObjects
        rw [hgb_map_eq, hjr_ivl_eq, blockOutObjects_eq_parts, hbo_base_eq, h40_post, h72_post, hbal_part.1]
        simp [gb_jr, List.append_assoc]
  obtain ⟨L1, L2, hfix_s0_eq, hfix_post_eq⟩ := hslice_fix
  have hfix_from : ∀ x ∈ fixedObjects post,
      x ∈ fixedObjects s0 ∨ x = (np, 8 * (2 * cap)) := by
    intro x hx
    rw [hfix_post_eq] at hx
    rcases List.mem_append.1 hx with hxl | hx2
    · rcases List.mem_append.1 hxl with hx1 | hxm
      · exact Or.inl (by rw [hfix_s0_eq]; exact List.mem_append_left _ (List.mem_append_left _ hx1))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxm
        rcases hxm with rfl | rfl
        · exact Or.inl hl_fix
        · exact Or.inr rfl
    · exact Or.inl (by rw [hfix_s0_eq]; exact List.mem_append_right _ hx2)
  have hdisj_old_new : ∀ x ∈ fixedObjects s0, Disj x (np, 8 * (2 * cap)) := by
    intro x hx
    rcases hF.1 x hx with h0 | ⟨hal_x, _⟩
    · exact Or.inl h0
    · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_x hin_new)
  have hF_post : FixedTyped post := by
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases hfix_from x hx with hx_s | rfl
      · rcases hF.1 x hx_s with h0 | ⟨hal_x, hw_x⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hag.allocated hal_x, Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw_x⟩
      · exact Or.inr ⟨hal_new, hw_new⟩
    · rw [hfix_post_eq]
      have hpw_f0 : (L1 ++ [(l, 24), (memW s0 l, 8 * cap)] ++ L2).Pairwise Disj :=
        hfix_s0_eq ▸ hF.2
      exact pairwise_disj_replace_slice hpw_f0
        (List.pairwise_cons.2 ⟨fun y hy => by simp at hy; subst hy; exact hdj_new_l, List.pairwise_singleton _ _⟩)
        (fun x hx y hy => by
          have hx_f0 : x ∈ fixedObjects s0 := by
            rw [hfix_s0_eq]; exact List.mem_append_left _ (List.mem_append_left _ hx)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact pairwise_disj_outside_slice hpw_f0 (Or.inl hx) (by simp)
          · exact hdisj_old_new x hx_f0)
        (fun x hx y hy => by
          have hy_f0 : y ∈ fixedObjects s0 := by
            rw [hfix_s0_eq]; exact List.mem_append_right _ hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact disj_flip (pairwise_disj_outside_slice hpw_f0 (Or.inr hy) (by simp))
          · exact disj_flip (hdisj_old_new y hy_f0))
  have hjr_part := Wave8Contracts.M08.journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hgs hu_ts hu_jr
  have hwrs_eq := Wave8Contracts.M08.worldRoleSlots_eq_of_unhit
    hAs.2 hT hF hgs hu_tab hu_ws hu_bs hu_ts hu_bal hm0
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s0 post (nodeIvl s0 n) := fun n hn => by
    have hne_mem : nodeIvl s0 n ∈ nodeExtents s0 Nd :=
      List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
    exact hunhit_of_disj _ (hTr.1.1 n hn).2.1 ((hTr.2.1 _ hne_mem).2 _ hl_fix)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s0 n = 1 ∨ memW s0 n = 2) → memW s0 (n + 40) ≠ 0 →
      ∀ k, k < memW s0 (n + 40) → memB post (memW s0 (n + 32) + k) = memB s0 (memW s0 (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have hnp_mem : nodePath s0 n ∈ nodeExtents s0 Nd :=
      List.mem_flatMap.2 ⟨n, hn, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)⟩
    have hnp_eq_nd : nodePath s0 n = (memW s0 (n + 32), memW s0 (n + 40)) := by
      simp [nodePath, h12, hlen0]
    have hdj_l : Disj (memW s0 (n + 32), memW s0 (n + 40)) (l, 24) := by
      rw [← hnp_eq_nd]; exact (hTr.2.1 _ hnp_mem).2 _ hl_fix
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_np, hin_p, _⟩
    · exact absurd h0 hlen0
    have hdj_n : Disj (memW s0 (n + 32), memW s0 (n + 40)) (np, 2 * 8 * cap) := by
      rw [hnew_sz_eq]
      exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_np hin_new)
    have hlim264 : heapLimit ≤ 2 ^ 64 := by decide
    have hbk_lt : memW s0 (n + 32) + k < 2 ^ 64 := by
      have := hin_p.2; dsimp at this; omega
    have hb_eq := heff.byte_frame (memW s0 (n + 32) + k) hbk_lt (fun x hx hbi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hb1, hb2⟩ := hbi
      rcases hx with rfl | rfl
      · dsimp only at hb1 hb2; rcases hdj_n with d | d | d | d <;> omega
      · dsimp only at hb1 hb2; rcases hdj_l with d | d | d | d <;> omega)
    rw [hb_eq]
    unfold memB
    rw [hm_mem, hm_be]
  have hnd_part := Wave8Contracts.M08.nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s0 t k) ∧
      htabFootprint post t = htabFootprint s0 t := by
    have h264_he : heapEnd ≤ 2 ^ 64 := by decide
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s0 t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit
      ht8 hhi (hu_tab t ht _ ht_fp)
  have hflat_fp : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s0) :=
    List.flatMap_congr fun t ht => (htab_fp_hdr t ht).2
  have hrecs_eq : balRecords post = balRecords s0 :=
    Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_ok_post, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2]
      refine ⟨Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, fun j hj => ?_⟩⟩
      rcases hfix_from j hj with hj_s | rfl
      · exact ((hTt t ht).2 i hi).2 j hj_s
      · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 ((hTt t ht).2 i hi).1 hin_new)
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
      have ho_alloc : o = (0, 0) ∨ Allocated s0 o := by
        unfold nodeExtents at ho
        obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
        rcases hno with rfl | rfl
        · exact Or.inr (hTr.1.1 n hn).2.1
        · unfold nodePath
          split
          · rename_i hcond
            rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
            · exact absurd h0 hcond.2
            · exact Or.inr hal
          · exact Or.inl rfl
      refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rw [(htab_fp_hdr t ht).2] at hi
        exact (hTr.2.1 o ho).1 t ht i hi
      · rcases hfix_from j hj with hj_s | rfl
        · exact (hTr.2.1 o ho).2 j hj_s
        · rcases ho_alloc with rfl | hal_o
          · exact Or.inl rfl
          · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_o hin_new)
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
      have hget : (htabValues post (memW s0 (globN s0 "ws" + 32)))[i]? =
          (htabValues s0 (memW s0 (globN s0 "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 hm i hi
  have hfr : FrameOutside s0 post (worldOwned s0 S Nd ++ ([] : List Ivl) ++ [freeGap s0]) (heapFree s0) := by
    intro a ha hnhf
    have hm_a := heff.cell_frame a (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      have hl_ow : (l, 24) ∈ worldOwned s0 S Nd ++ ([] : List Ivl) ++ [freeGap s0] := by
        apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_append_left _ (List.mem_append_right _ hl_fix)
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2
        have hlim : np + 2 * 8 * cap ≤ heapLimit := by
          have := hAp.2.2.1; omega
        exact hnhf ⟨by unfold heapFree M13.heapFree; dsimp only; omega,
                    by unfold heapFree M13.heapFree; dsimp only; omega⟩
      · exact ha (l, 24) hl_ow ⟨hc1, hc2⟩)
    rw [hm_a, hm_mem]
  have hOG : OwnedGrows s0 post (worldOwned s0 S Nd) (worldOwned post S Nd) := by
    intro o ho
    unfold worldOwned M13.worldOwned at ho
    simp only [List.mem_append] at ho
    rcases ho with (ho_tab | ho_fix) | ho_nd
    · rw [hflat_fp] at ho_tab
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned M13.worldOwned
      exact List.mem_append_left _ (List.mem_append_left _ ho_tab)
    · rcases hfix_from o ho_fix with ho_s | rfl
      · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned M13.worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ ho_s)
      · exact Or.inr (Or.inr hin_new)
    · rw [hnd_part.2] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned M13.worldOwned
      exact List.mem_append_right _ ho_nd
  have hQ_post : RetListSlot s0 r post S Nd := by
    intro v hv
    obtain ⟨rfl, hal8, hin⟩ := hret_slot v hv
    refine ⟨ew, rfl, hal8, ?_⟩
    rw [hl_eq_loc, hl0_post, hl16_post]
    exact hin
  exact ⟨S, Nd, fun _ hx => hx, ⟨hT_post, hjr_part.2, hF_post, hTr_post⟩, hOG, hfr, hQ_post⟩

theorem wk_lst_push_strong :
    WorldKeeps BoListArgStrong (fun _ => []) ["heap_ptr"] stdKeep
      RetListSlot (ofString "lst_push") := by
  refine ⟨_, _, _, lookup_lst_push, ?_⟩
  intro F s hcode hArg hvalid hnt hres
  obtain ⟨hW, ⟨_, hbo_nz, hbo_slot_loc, hesz_loc_eq⟩, hp_nz_loc⟩ := hArg
  have hAs : ArenaReady s := hW.1
  have hG : GuestInv s := hAs.1
  obtain ⟨values, hlook_fn⟩ := hvalid
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "lst_push")
    values _ s.locals _ hlook_fn
  simp only [lookupCodeHOLExact, lookup_lst_push] at hx
  rcases values with _ | ⟨vl, _ | ⟨ve, _ | ⟨_, _⟩⟩⟩
  · simp at hx
  · simp at hx
  swap
  · simp at hx
  · rcases vl with ⟨⟨lw⟩⟩ | _ | _; swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases ve with ⟨⟨eszw⟩⟩ | _ | _; swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hs_locals_eq⟩ := hx
    have hs_l : s.locals.lookup (ofString "l") = some (.val (.word lw)) := by
      have := congrFun hs_locals_eq (ofString "l")
      simpa [FUPDATE, show ofString "esz" ≠ ofString "l" by decide,
        show ofString "l" ≠ ofString "esz" by decide] using this.symm
    have hs_e : s.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
      have := congrFun hs_locals_eq (ofString "esz")
      simpa [FUPDATE] using this.symm
    have hl_loc : locN s "l" = lw.toNat := by simp [locN, hs_l]
    have hesz_loc : locN s "esz" = eszw.toNat := by simp [locN, hs_e]
    have heszw_toNat : eszw.toNat = 8 := by rw [← hesz_loc, hesz_loc_eq]
    have heszw_eq : eszw = 8#64 := BitVec.eq_of_toNat_eq (by rw [heszw_toNat]; rfl)
    by_cases hlw0 : lw = 0
    · have hnot8 : ¬ s.memaddrs 8#64 := by
        rw [hG.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff]
        have hsb : sourceBase = 2701131776 := rfl
        simp [hsb]
      have hbody_err : (evaluateHOLFiniteState s
          (sourceFnBody Guest.Software.guestFn_lst_push)).1 = some .error := by
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_lst_push,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
        rw [evaluateHOLFiniteState_dec_total]; dsimp only
        have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
        have hl0 : s.locals.lookup (ofString "l") = some (.val (.word 0#64)) := by
          subst hlw0; exact hs_l
        have hev8 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) = none := by
          simp [evalHOLExact, evalListHOLExact, hl0, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.foldr, hz_8, memLoadHOLExact, hnot8]
        rw [hev8]
      rw [hbody_err] at hres
      exact absurd hres not_resumes_error
    · have hlw_nz_nat : lw.toNat ≠ 0 := fun h => hlw0 (BitVec.eq_of_toNat_eq (by simpa using h))
      have hbo_slot : lw.toNat = memW s (globN s "bo" + 40) ∨ lw.toNat = memW s (globN s "bo" + 72) := by
        rwa [← hl_loc]
      have hp_nz : memW s lw.toNat ≠ 0 := by rwa [← hl_loc]
      obtain ⟨S0, hWT0_ex⟩ := hW.2
      obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
      have hlst0 : LstOK s lw.toNat := by
        rcases hbo_slot with hl40 | hl72
        · rw [hl40] at hlw_nz_nat ⊢
          exact hWT0.1.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 40 (by simp) hlw_nz_nat
        · rw [hl72] at hlw_nz_nat ⊢
          exact hWT0.1.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 72 (by simp) hlw_nz_nat
      obtain ⟨_, _, hl_fix0, hp_fix0, _, _⟩ :=
        bo_list_slice_props hWT0.2.2.1 hbo_nz hbo_slot hlw_nz_nat hp_nz hlst0
      have hpos_arr : 8 * memW s (lw.toNat + 16) ≠ 0 := by have := hlst0.1; omega
      rcases hWT0.2.2.1.1 _ hl_fix0 with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      rcases hWT0.2.2.1.1 _ hp_fix0 with h0 | ⟨hal_p, hw_p⟩
      · exact absurd h0 hpos_arr
      have hhe_264 : heapEnd < 2 ^ 64 := by decide
      have hlim_he : heapLimit ≤ heapEnd := by decide
      have hsb_ss : sourceBase ≤ scratchStart := by decide
      have hl_bnd : sourceBase ≤ lw.toNat ∧ lw.toNat + 24 ≤ heapEnd := by
        have hup := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_l).1
        rcases hal_l with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      have hp_bnd : sourceBase ≤ memW s lw.toNat ∧
          memW s lw.toNat + 8 * memW s (lw.toNat + 16) ≤ heapEnd := by
        have hup := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_p).1
        rcases hal_p with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      let nw : BitVec 64 := BitVec.ofNat 64 (memW s (lw.toNat + 8))
      let capw : BitVec 64 := BitVec.ofNat 64 (memW s (lw.toNat + 16))
      let pw0 : BitVec 64 := BitVec.ofNat 64 (memW s lw.toNat)
      have hnw_toNat : nw.toNat = memW s (lw.toNat + 8) := by
        dsimp [nw]; rw [BitVec.toNat_ofNat]
        have := hlst0.2
        exact Nat.mod_eq_of_lt (by omega)
      have hcapw_toNat : capw.toNat = memW s (lw.toNat + 16) := by
        dsimp [capw]; rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      have hpw0_toNat : pw0.toNat = memW s lw.toNat := by
        dsimp [pw0]; rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      have hl0_bv : lw + 0#64 = BitVec.ofNat 64 lw.toNat := by simp
      have hl8_bv : lw + 8#64 = BitVec.ofNat 64 (lw.toNat + 8) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        rfl
      have hl16_bv : lw + 16#64 = BitVec.ofNat 64 (lw.toNat + 16) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        rfl
      have hl8_toNat : (lw + 8#64).toNat = lw.toNat + 8 := by
        rw [hl8_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hl16_toNat : (lw + 16#64).toNat = lw.toNat + 16 := by
        rw [hl16_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hdom_l0 : s.memaddrs (lw + 0#64) := by
        rw [hG.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff]
        have : (lw + 0#64).toNat = lw.toNat := by simp
        rw [this]; exact ⟨hw_l.1, by omega, by omega⟩
      have hdom_l8 : s.memaddrs (lw + 8#64) := by
        rw [hG.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, hl8_toNat]
        exact ⟨by have := hw_l.1; omega, by omega, by omega⟩
      have hdom_l16 : s.memaddrs (lw + 16#64) := by
        rw [hG.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, hl16_toNat]
        exact ⟨by have := hw_l.1; omega, by omega, by omega⟩
      have hm_l0 : s.memory (lw + 0#64) = .word pw0 := by
        rw [hl0_bv]; dsimp [pw0]; unfold memW
        rcases s.memory (BitVec.ofNat 64 lw.toNat) with ⟨w⟩; simp
      have hm_l8 : s.memory (lw + 8#64) = .word nw := by
        rw [hl8_bv]; dsimp [nw]; unfold memW
        rcases s.memory (BitVec.ofNat 64 (lw.toNat + 8)) with ⟨w⟩; simp
      have hm_l16 : s.memory (lw + 16#64) = .word capw := by
        rw [hl16_bv]; dsimp [capw]; unfold memW
        rcases s.memory (BitVec.ofNat 64 (lw.toNat + 16)) with ⟨w⟩; simp
      rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_push) with ⟨rb, post⟩
      rw [hrun] at hnt hres
      dsimp only at hnt hres ⊢
      cases rb with
      | none =>
        exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | some rb' =>
        cases rb' with
        | timeOut => exact absurd rfl hnt
        | «break» | «continue» | error | finalFfi _ =>
          exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | exception e ev =>
          exfalso
          rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
          · simp at h
          · injection h with h'; injection h' with he1 he2; subst he1 he2
            exact lst_push_no_catchable_exn s hcode e ev hne (congrArg Prod.fst hrun)
        | returned vb =>
          let e1 := setVarHOLFinite (ofString "n") (.val (.word nw)) s
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
          have hbody_e2 : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_push) =
              (let out := evaluateHOLFiniteState e2
                (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
                        growProg .skip)
                      tailProg);
               (out.1, { out.2 with
                 locals := HolFiniteMapExact.resVarEq
                   (HolFiniteMapExact.resVarEq out.2.locals (ofString "cap", e1.locals.lookup (ofString "cap")))
                   (ofString "n", s.locals.lookup (ofString "n")) })) := by
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
            have hev1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
                (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) =
                some (.val (.word nw)) := by
              simp only [evalHOLExact, evalListHOLExact, hs_l, valueIsWord, valueWord,
                wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_8,
                memLoadHOLExact, isWfShapeExactHOL, hdom_l8, hm_l8, ↓reduceIte]
            rw [hev1]; dsimp only
            rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
            have he1_def : setVarHOLFinite (ofString "n") (.val (.word nw)) s = e1 := rfl
            rw [he1_def, evaluateHOLFiniteState_dec_total]; dsimp only
            have he1_l : e1.locals.lookup (ofString "l") = some (.val (.word lw)) := by
              simp [e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "n" ≠ ofString "l" by decide, hs_l]
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
          rw [hbody_e2] at hrun
          dsimp only at hrun
          rcases hout_e2 : evaluateHOLFiniteState e2
              (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
                      growProg .skip)
                    tailProg) with ⟨ro2, so2⟩
          rw [hout_e2] at hrun
          injection hrun with hro2 hpost_eq
          subst hro2
          have he2_eq : e2 = { s with locals := e2.locals, clock := s.clock } := rfl
          have he2_AR : ArenaReady e2 := (arenaReady_with_locals s e2.locals s.clock).2 hAs
          have he2_l : e2.locals.lookup (ofString "l") = some (.val (.word lw)) := by
            simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cap" ≠ ofString "l" by decide,
              show ofString "n" ≠ ofString "l" by decide, hs_l]
          have he2_e : e2.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
            simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cap" ≠ ofString "esz" by decide,
              show ofString "n" ≠ ofString "esz" by decide, hs_e]
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
            · have hlt_f : ¬ (nw < capw) := fun h => by
                have := (BitVec.lt_def).1 h; omega
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
            rw [evaluateHOLFiniteState_ite, hcmp_nl] at hite_out
            dsimp only at hite_out
            by_cases hgrow_cond : capw.toNat ≤ nw.toNat
            · rw [if_pos hgrow_cond, if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hite_out
              have hgrow_nret : (evaluateHOLFiniteState e2 growProg).1 ≠ some (.returned vb) := by
                intro hgr
                have hgr_nt : (evaluateHOLFiniteState e2 growProg).1 ≠ some .timeOut := by
                  rw [hgr]; simp
                have hgr_res : Resumes (evaluateHOLFiniteState e2 growProg).1 :=
                  Or.inl ⟨vb, hgr⟩
                have hmul2_ev : @evalHOLExact 64 F _ e2.toExact
                    (fun a => Classical.propDecidable (e2.memaddrs a))
                    (.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]) =
                    some (.val (.word (eszw * capw * 2#64))) := by
                  simp [evalHOLExact, evalListHOLExact, he2_e, he2_c, valueIsWord, valueWord, panOpHOL]
                obtain ⟨_, _, mid_a, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hg_eq1, _⟩ :=
                  decCall_alloc_resumes e2 (ofString "np") _ (eszw * capw * 2#64) _ he2_AR hmul2_ev hgr_nt hgr_res
                rw [hg_eq1] at hgr
                rw [evaluateHOLFiniteState_seq_line780] at hgr
                rcases hmc_o : evaluateHOLFiniteState mid_a
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
              exact hgrow_nret (by rw [hite_out, hri])
            · rw [if_neg hgrow_cond, if_pos (by decide : (0#64 : BitVec 64) = 0), evaluateHOLFiniteState_skip] at hite_out
              simp at hite_out
          | none =>
            dsimp only at hout_e2
            rw [evaluateHOLFiniteState_ite, hcmp_nl] at hite_out
            dsimp only at hite_out
            by_cases hgrow_cond : capw.toNat ≤ nw.toNat
            · have hn_eq_cap : nw.toNat = capw.toNat := by
                have := hlst0.2; omega
              have hnw_eq_capw : nw = capw := BitVec.eq_of_toNat_eq hn_eq_cap
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
                  some [.val (.word (eszw * capw * 2#64))] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, he2_e, he2_c,
                  valueIsWord, valueWord, panOpHOL]
              have hlk_alloc := pan_one_word_lookup e2.code.lookup (ofString "alloc") (ofString "n")
                (sourceFnBody Guest.Software.guestFn_alloc) (eszw * capw * 2#64)
                (by rw [he2_AR.1.code]; exact R13Shards.lookup_alloc_r13)
              rw [hev_alloc] at hite_out; dsimp only at hite_out
              rw [hlk_alloc] at hite_out; dsimp only at hite_out
              by_cases hc_e2 : e2.clock = 0
              · rw [if_pos hc_e2] at hite_out; simp at hite_out
              · rw [if_neg hc_e2] at hite_out
                let cmap_a := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (eszw * capw * 2#64)))
                let ent_a := callEntryStateHOLFinite e2 cmap_a
                have hent_a_AR : ArenaReady ent_a := (arenaReady_with_locals e2 cmap_a (e2.clock - 1)).2 he2_AR
                have hent_a_n : locN ent_a "n" = (eszw * capw * 2#64).toNat := by
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
                    have hma_m : ma.memory = s.memory := hsa_m
                    have hma_be : ma.be = s.be := hsa_be
                    have hma_ma : ma.memaddrs = ordinaryDomain := hsa_ma.trans hG.memaddrs
                    have hma_code : ma.code = originalRuntimeCode := hma_AR.1.code
                    have hma_gl : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = ma.globals.lookup k := by
                      intro k hk1
                      change s.globals.lookup k = sa.globals.lookup k
                      have hent_a_gl : ent_a.globals = s.globals := rfl
                      rw [hsa_g, hent_a_gl]
                      simp [HolFiniteMapExact.lookup_update, FUPDATE, hk1, Ne.symm hk1]
                    have hnpw_eq_s : npw.toNat = globN s "heap_ptr" := hnpw_eq
                    have hnpw8 : npw.toNat % 8 = 0 := by rw [hnpw_eq_s]; exact hAs.2.2.2.2.2.2.1
                    have hmul_ec_lt : eszw.toNat * capw.toNat < 2 ^ 64 := by
                      rw [heszw_toNat, hcapw_toNat]; omega
                    have hec_bv : (eszw * capw).toNat = 8 * capw.toNat := by
                      rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hmul_ec_lt, heszw_toNat]
                    have hmul2_lt : 8 * capw.toNat * 2 < 2 ^ 64 := by
                      rw [hcapw_toNat]
                      have hhe_val : heapEnd = 33806089704 := by decide
                      omega
                    have hmul2_toNat : (eszw * capw * 2#64).toNat = 2 * 8 * capw.toNat := by
                      rw [BitVec.toNat_mul, hec_bv]
                      have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
                      rw [h2, Nat.mod_eq_of_lt hmul2_lt]
                      ring
                    have hmul2_div : (2 * 8 * capw.toNat + 7) / 8 * 8 = 2 * 8 * capw.toNat := by omega
                    have hma_hp : globN ma "heap_ptr" = npw.toNat + 2 * 8 * capw.toNat := by
                      change globN sa "heap_ptr" = _
                      rw [hsa_hp, hqw_eq, hmul2_toNat, hmul2_div]
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
                    rw [hma_cont] at hite_out
                    dsimp only at hite_out
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
                      have hma_e : ma.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "np" ≠ ofString "esz" by decide, he2_e]
                      have hma_n : ma.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "np" ≠ ofString "n" by decide, he2_n]
                      have hma_c : ma.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "np" ≠ ofString "cap" by decide, he2_c]
                      have hma_dom0 : ma.memaddrs (lw + 0#64) := by rw [hma_ma, ← hG.memaddrs]; exact hdom_l0
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
                          some (.val (.word (eszw * nw))) := by
                        simp [evalHOLExact, evalListHOLExact, hma_e, hma_n, valueIsWord, valueWord, panOpHOL]
                      let Rg : List Ivl := [(npw.toNat, 2 * 8 * capw.toNat), (lw.toNat, 24)]
                      have hmc_nt : (evaluateHOLFiniteState ma
                          (.call (some (none, none)) (ofString "memcpy")
                            [.var .local (ofString "np"),
                             .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                             .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])).1 ≠
                          some .timeOut := by
                        rw [hmc_out]; simp
                      have hmc_bre_all := M11.eval_call_memcpy_bre ma _ _ _ npw pw0 (eszw * nw) Rg
                        hma_code hma_ma hev_mc_dst hev_mc_src hev_mc_n
                        (fun _ => by
                          refine ⟨(npw.toNat, 2 * 8 * capw.toNat), by simp [Rg], le_refl _, ?_⟩
                          dsimp only
                          rw [hnw_eq_capw, hec_bv]
                          omega)
                        hmc_nt
                      obtain ⟨heff_mc, hsmc_loc⟩ := hmc_bre_all.1 (by rw [hmc_out])
                      rw [hmc_out] at heff_mc hsmc_loc
                      dsimp only at heff_mc hsmc_loc
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
                        have hsmc_dom0 : smc.memaddrs (lw + 0#64) := by rw [hsmc_ma, ← hG.memaddrs]; exact hdom_l0
                        have hsmc_dom0' : smc.memaddrs lw := by simpa using hsmc_dom0
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
                        obtain ⟨heff_st0, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rg) hsmc_ma hst0_out
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
                        have hsst0_dom16 : sst0.memaddrs (lw + 16#64) := by rw [hsst0_ma, ← hG.memaddrs]; exact hdom_l16
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
                        obtain ⟨heff_st16, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rg) hsst0_ma hma_cont
                          (fun v hv => by rw [hev_st16_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                          (fun addr hdst _ => by
                            rw [hev_st16_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                            subst hd3
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
                        have hsi_e : si.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
                          rw [← hsi_eq]; dsimp only
                          rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq, hsst0_loc]; exact hma_e
                        have hsi_dom8 : si.memaddrs (lw + 8#64) := by rw [hsi_ma, ← hG.memaddrs]; exact hdom_l8
                        have hsi_dom0 : si.memaddrs (lw + 0#64) := by rw [hsi_ma, ← hG.memaddrs]; exact hdom_l0
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
                        rw [hst8_eq] at hout_e2
                        dsimp only at hout_e2
                        obtain ⟨heff_st8, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rg) hsi_ma hst8_eq
                          (fun v hv => by rw [hev_st8_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                          (fun addr hdst _ => by
                            rw [hev_st8_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                            subst hd3
                            exact ⟨(lw.toNat, 24), by simp [Rg], by dsimp only; omega, by dsimp only; omega⟩)
                        let st8 : PanSemStateFiniteExact 64 F :=
                          { si with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else si.memory a }
                        have hne_0_16 : lw + 0#64 ≠ lw + 16#64 := by
                          intro h; have := congrArg BitVec.toNat h
                          have h0 : (lw + 0#64).toNat = lw.toNat := by simp
                          omega
                        have hne_0_8 : lw + 0#64 ≠ lw + 8#64 := by
                          intro h; have := congrArg BitVec.toNat h
                          have h0 : (lw + 0#64).toNat = lw.toNat := by simp
                          omega
                        have hne_16_8 : lw + 16#64 ≠ lw + 8#64 := by
                          intro h; have := congrArg BitVec.toNat h; omega
                        have hst8_m0 : st8.memory (lw + 0#64) = .word npw := by
                          dsimp [st8]; rw [if_neg hne_0_8, ← hsi_eq]; dsimp only
                          rw [hsg1_eq]; dsimp only; rw [if_neg hne_0_16, hsst0_eq]; simp
                        have hst8_m8 : st8.memory (lw + 8#64) = .word (nw + 1#64) := by
                          dsimp [st8]; simp
                        have hst8_m16 : st8.memory (lw + 16#64) = .word (capw * 2#64) := by
                          dsimp [st8]; rw [if_neg hne_16_8, ← hsi_eq]; dsimp only
                          rw [hsg1_eq]; simp
                        have hst8_dom0 : st8.memaddrs (lw + 0#64) := hsi_dom0
                        have hev_ret : @evalHOLExact 64 F _ st8.toExact (fun a => Classical.propDecidable (st8.memaddrs a))
                            (.op .add
                              [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                               .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
                            some (.val (.word (npw + nw * eszw))) := by
                          have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
                          have hst8_l : st8.locals.lookup (ofString "l") = some (.val (.word lw)) := hsi_l
                          have hst8_n : st8.locals.lookup (ofString "n") = some (.val (.word nw)) := hsi_n
                          have hst8_e : st8.locals.lookup (ofString "esz") = some (.val (.word eszw)) := hsi_e
                          simp only [evalHOLExact, evalListHOLExact, hst8_l, hst8_n, hst8_e,
                            valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                            List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
                            memLoadHOLExact, isWfShapeExactHOL, hst8_dom0, hst8_m0, ↓reduceIte]
                          simp
                        rw [evaluateHOLFiniteState_return, hev_ret] at hout_e2
                        dsimp only at hout_e2
                        rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])] at hout_e2
                        injection hout_e2 with hvb_eq hso2_eq
                        injection hvb_eq with hvb_ret
                        injection hvb_ret with hvb_val
                        subst hvb_val
                        let ew := npw + nw * eszw
                        have heff_si : M11.ByteRegionEffect ma si Rg := by
                          rw [← hsi_eq]
                          exact ((heff_mc.trans heff_st0).trans heff_st16).with_locals_clock _ sg1.clock
                        have hm_post_st8 : post.memory = st8.memory := by
                          rw [← hpost_eq, ← hso2_eq]; rfl
                        have heff_post : M11.ByteRegionEffect ma post Rg := by
                          have hpost_mem : post = { st8 with locals := post.locals, clock := post.clock } := by
                            rw [← hpost_eq, ← hso2_eq]; rfl
                          rw [hpost_mem]
                          exact (heff_si.trans heff_st8).with_locals_clock post.locals post.clock
                        have hpost_m0 : memW post lw.toNat = npw.toNat := by
                          unfold memW; rw [← hl0_bv, hm_post_st8, hst8_m0]
                        have hcap2_toNat : (capw * 2#64).toNat = 2 * capw.toNat := by
                          have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
                          have hc2_lt : capw.toNat * 2 < 2 ^ 64 := by omega
                          rw [BitVec.toNat_mul, h2, Nat.mod_eq_of_lt hc2_lt]; omega
                        have hnp1_toNat : (nw + 1#64).toNat = nw.toNat + 1 := by
                          have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
                          have hn1_lt : nw.toNat + 1 < 2 ^ 64 := by omega
                          rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt hn1_lt]
                        have hpost_m8 : memW post (lw.toNat + 8) = nw.toNat + 1 := by
                          unfold memW; rw [← hl8_bv, hm_post_st8, hst8_m8]; exact hnp1_toNat
                        have hpost_m16 : memW post (lw.toNat + 16) = 2 * capw.toNat := by
                          unfold memW; rw [← hl16_bv, hm_post_st8, hst8_m16]; exact hcap2_toNat
                        have hcap_pos0 : 1 ≤ capw.toNat := by rw [hcapw_toNat]; exact hlst0.1
                        have hne_mul_toNat : (nw * eszw).toNat = nw.toNat * 8 := by
                          rw [BitVec.toNat_mul, hn_eq_cap, Nat.mul_comm,
                            Nat.mod_eq_of_lt hmul_ec_lt, heszw_toNat]; ring
                        have hnpw_hi_lim : npw.toNat + 2 * 8 * capw.toNat ≤ heapLimit := by
                          rw [← hma_hp]; exact hma_AR.2.2.1
                        have hew_toNat : ew.toNat = npw.toNat + nw.toNat * 8 := by
                          change (npw + nw * eszw).toNat = _
                          rw [BitVec.toNat_add, hne_mul_toNat, Nat.mod_eq_of_lt (by rw [hn_eq_cap]; omega)]
                        have hew8 : ew.toNat % 8 = 0 := by rw [hew_toNat]; omega
                        have hew_in : Inside (ew.toNat, 8) npw.toNat (npw.toNat + 8 * (2 * capw.toNat)) := by
                          refine ⟨by dsimp only; rw [hew_toNat]; omega, ?_⟩
                          dsimp only; rw [hew_toNat, hn_eq_cap]; omega
                        exact bo_list_grow_worldStep hW hbo_nz hl_loc hbo_slot hlw_nz_nat hp_nz
                          hcapw_toNat.symm hma_AR hma_m hma_be hma_gl hnpw_eq_s hma_hp heff_post
                          hpost_m0 (by rw [hpost_m8, hn_eq_cap]; omega) hpost_m16
                          (fun v hv => by
                            injection hv with hv'; injection hv' with hv''
                            exact ⟨hv''.symm, hew8, hew_in⟩)
            · have hn_lt_cap : nw.toNat < capw.toNat := by omega
              rw [if_neg hgrow_cond, if_pos (by decide : (0#64 : BitVec 64) = 0), evaluateHOLFiniteState_skip] at hite_out
              injection hite_out with _ hsi_eq
              subst hsi_eq
              let Rn : List Ivl := [(lw.toNat + 8, 8)]
              have he2_ma : e2.memaddrs = ordinaryDomain := hG.memaddrs
              have he2_dom8 : e2.memaddrs (lw + 8#64) := hdom_l8
              have he2_dom0 : e2.memaddrs (lw + 0#64) := hdom_l0
              dsimp only [tailProg] at hout_e2
              rw [evaluateHOLFiniteState_seq_line780] at hout_e2
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
              rw [hst8_eq] at hout_e2
              dsimp only at hout_e2
              obtain ⟨heff_st8, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rn) he2_ma hst8_eq
                (fun v hv => by rw [hev_st8_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                (fun addr hdst _ => by
                  rw [hev_st8_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                  subst hd3
                  exact ⟨(lw.toNat + 8, 8), by simp [Rn], by dsimp only; omega, by dsimp only; omega⟩)
              let st8 : PanSemStateFiniteExact 64 F :=
                { e2 with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else e2.memory a }
              have hne_0_8 : lw + 0#64 ≠ lw + 8#64 := by
                intro h; have := congrArg BitVec.toNat h
                have h0 : (lw + 0#64).toNat = lw.toNat := by simp
                omega
              have hst8_m0 : st8.memory (lw + 0#64) = .word pw0 := by
                dsimp [st8]; rw [if_neg hne_0_8]; exact hm_l0
              have hst8_m8 : st8.memory (lw + 8#64) = .word (nw + 1#64) := by
                dsimp [st8]; simp
              have hst8_dom0 : st8.memaddrs (lw + 0#64) := he2_dom0
              have hev_ret : @evalHOLExact 64 F _ st8.toExact (fun a => Classical.propDecidable (st8.memaddrs a))
                  (.op .add
                    [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                     .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
                  some (.val (.word (pw0 + nw * eszw))) := by
                have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
                have hst8_l : st8.locals.lookup (ofString "l") = some (.val (.word lw)) := he2_l
                have hst8_n : st8.locals.lookup (ofString "n") = some (.val (.word nw)) := he2_n
                have hst8_e : st8.locals.lookup (ofString "esz") = some (.val (.word eszw)) := he2_e
                simp only [evalHOLExact, evalListHOLExact, hst8_l, hst8_n, hst8_e,
                  valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                  List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
                  memLoadHOLExact, isWfShapeExactHOL, hst8_dom0, hst8_m0, ↓reduceIte]
                simp
              rw [evaluateHOLFiniteState_return, hev_ret] at hout_e2
              dsimp only at hout_e2
              rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])] at hout_e2
              injection hout_e2 with hvb_eq hso2_eq
              injection hvb_eq with hvb_ret
              injection hvb_ret with hvb_val
              subst hvb_val
              let ew := pw0 + nw * eszw
              have hm_post_st8 : post.memory = st8.memory := by
                rw [← hpost_eq, ← hso2_eq]; rfl
              have heff_e2_post : M11.ByteRegionEffect e2 post Rn := by
                have hpost_mem : post = { st8 with locals := post.locals, clock := post.clock } := by
                  rw [← hpost_eq, ← hso2_eq]; rfl
                rw [hpost_mem]
                exact heff_st8.with_locals_clock post.locals post.clock
              have heff_s_e2 : M11.ByteRegionEffect s e2 Rn := by
                rw [he2_eq]
                exact (M11.ByteRegionEffect.refl s Rn).with_locals_clock e2.locals s.clock
              have heff_post : M11.ByteRegionEffect s post Rn := heff_s_e2.trans heff_e2_post
              have hnp1_toNat : (nw + 1#64).toNat = nw.toNat + 1 := by
                have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
                have hn1_lt : nw.toNat + 1 < 2 ^ 64 := by omega
                rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt hn1_lt]
              have hpost_m8 : memW post (lw.toNat + 8) = nw.toNat + 1 := by
                unfold memW; rw [← hl8_bv, hm_post_st8, hst8_m8]; exact hnp1_toNat
              have hne_mul_lt : nw.toNat * 8 < 8 * memW s (lw.toNat + 16) := by
                rw [← hcapw_toNat]; omega
              have hne_mul_toNat : (nw * eszw).toNat = nw.toNat * 8 := by
                rw [BitVec.toNat_mul, heszw_toNat, Nat.mod_eq_of_lt (by omega)]
              have hew_toNat : ew.toNat = memW s lw.toNat + nw.toNat * 8 := by
                change (pw0 + nw * eszw).toNat = _
                rw [BitVec.toNat_add, hpw0_toNat, hne_mul_toNat, Nat.mod_eq_of_lt (by omega)]
              have hew8 : ew.toNat % 8 = 0 := by
                rw [hew_toNat]
                have hp8 : (memW s lw.toNat) % 8 = 0 := hw_p.1
                omega
              have hew_in : Inside (ew.toNat, 8) (memW s lw.toNat)
                  (memW s lw.toNat + 8 * memW s (lw.toNat + 16)) := by
                refine ⟨by dsimp only; rw [hew_toNat]; omega, ?_⟩
                dsimp only; rw [hew_toNat]; omega
              exact bo_list_nogrow_worldStep hW hbo_nz hl_loc hbo_slot hlw_nz_nat hp_nz
                heff_post (by rw [← hcapw_toNat]; omega) hpost_m8
                (fun v hv => by
                  injection hv with hv'; injection hv' with hv''
                  exact ⟨hv''.symm, hew8, hew_in⟩)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal
