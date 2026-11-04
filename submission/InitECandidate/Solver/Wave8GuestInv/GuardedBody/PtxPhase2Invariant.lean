import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Set
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Stores
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Entries
import InitECandidate.Solver.GuestGlobalKeep

/-! Heap-buffer and local-table invariants (`HeapBuf`, `LocalTab`, `HeapLocalTab`)
and step preservation theorems for Phase 2 of `process_transaction`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1

structure HeapBuf {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat)
    (p sz : Nat) : Prop where
  p8 : p % 8 = 0
  sz8 : sz % 8 = 0
  inside : Inside (p, sz) sourceBase (globN s "heap_ptr")
  disj : ∀ o ∈ worldOwned s S Nd, Disj (p, sz) o

theorem heapBuf_with_locals {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {p sz : Nat} (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hb : HeapBuf s S Nd p sz) :
    HeapBuf { s with locals := locals, clock := k } S Nd p sz :=
  ⟨hb.p8, hb.sz8, hb.inside, hb.disj⟩

theorem heapBuf_disj_typed {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {p sz : Nat} (hb : HeapBuf s S Nd p sz) :
    ∀ j ∈ worldTypedIvls s S Nd, Disj j (p, sz) :=
  fun j hj => disj_symm (typed_disj_of_owned hb.disj j hj)

theorem heapBuf_sub_disj_typed {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {p sz q len : Nat} (hb : HeapBuf s S Nd p sz)
    (hin : Inside (q, len) p (p + sz)) :
    ∀ j ∈ worldTypedIvls s S Nd, Disj (q, len) j :=
  fun j hj => disj_of_inside_left hin (typed_disj_of_owned hb.disj j hj)

theorem heapBuf_of_freshBlock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) {S' Nd' : List Nat} {p n : Nat}
    (hfb : FreshBlock s post p n)
    (hav : IvlsDisj [(p, (n + 7) / 8 * 8)] (worldOwned post S' Nd')) :
    HeapBuf post S' Nd' p ((n + 7) / 8 * 8) := by
  refine ⟨hfb.1, by omega, ⟨Nat.le_trans hAs.1 hfb.2.1.1, hfb.2.1.2⟩, ?_⟩
  intro o ho
  exact hav (p, (n + 7) / 8 * 8) (by simp) o ho

theorem heapBuf_survives_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {S Nd S' Nd' : List Nat} {R : List Ivl}
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    {p sz : Nat} (hb : HeapBuf s S Nd p sz)
    (hb_R : ∀ r ∈ R, Disj (p, sz) r) :
    HeapBuf post S' Nd' p sz ∧ IvlUnhit s post (p, sz) := by
  obtain ⟨hin, hd, hu⟩ := heap_ivl_survives_step hAs hhp hold0 hR0
    hog hfr hb.p8 hb.sz8 hb.inside hb.disj hb_R
  exact ⟨⟨hb.p8, hb.sz8, hin, hd⟩, hu⟩

structure LocalTab {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (t klen : Nat) : Prop where
  mem_S : t ∈ S
  nz : t ≠ 0
  hdr0 : hdr s t 0 = klen
  unassigned : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t

theorem localTab_with_locals {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {t klen : Nat} (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (ht : LocalTab s S t klen) :
    LocalTab { s with locals := locals, clock := k } S t klen :=
  ⟨ht.mem_S, ht.nz, ht.hdr0, ht.unassigned⟩

theorem localTab_congr {F : Type} {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {t klen : Nat} (ht : LocalTab s S t klen)
    (hwrs : worldRoleSlots post = worldRoleSlots s)
    (hjrs : journalRoleSlots post = journalRoleSlots s)
    (hhdr : ∀ u ∈ S, hdr post u 0 = hdr s u 0) :
    LocalTab post S t klen := by
  refine ⟨ht.mem_S, ht.nz, (hhdr t ht.mem_S).trans ht.hdr0, ?_⟩
  rw [hwrs, hjrs]
  exact ht.unassigned

theorem localTab_ext {F : Type} {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {t klen u : Nat} (ht : LocalTab s S t klen)
    (hwrs : worldRoleSlots post = worldRoleSlots s)
    (hjrs : journalRoleSlots post = journalRoleSlots s)
    (hhdr : ∀ x ∈ S, hdr post x 0 = hdr s x 0) :
    LocalTab post (S ++ [u]) t klen := by
  refine ⟨List.mem_append.2 (Or.inl ht.mem_S), ht.nz, (hhdr t ht.mem_S).trans ht.hdr0, ?_⟩
  rw [hwrs, hjrs]
  exact ht.unassigned

def htabNewCalleeGood (fn : MlS) : Bool :=
  (fn == ofString "alloc") || (fn == ofString "trap_with")

theorem lookup_trap_with_fn :
    originalRuntimeCode.lookup (ofString "trap_with") =
      some ((sourceFunctionEntry Guest.Software.guestFn_trap_with).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_trap_with) rfl

theorem lookup_htab_new_fn :
    originalRuntimeCode.lookup (ofString "htab_new") =
      some ((sourceFunctionEntry Guest.Software.guestFn_htab_new).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 128 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new) rfl

theorem htab_new_scratch_unchanged {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) :
    ∀ values body' callee ret' v post,
      lookupCodeHOLFinite s.code.lookup (ofString "htab_new") values = some (body', callee, ret') →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' = (some (.returned v), post) →
      globN post "scratch_ptr" = globN s "scratch_ptr" := by
  intro values body' callee ret' v post hlook hrun
  have hgood : ∀ fn, htabNewCalleeGood fn = true → ∀ vals b c rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup fn vals = some (b, c, rs) →
      InitECandidate.Solver.GuestGlobalKeep.keepsG (ofString "scratch_ptr") htabNewCalleeGood b = true := by
    intro fn hfn vals b c rs hl
    unfold htabNewCalleeGood at hfn
    rcases Bool.or_eq_true_iff.1 hfn with h1 | h2
    · have heq : fn = ofString "alloc" := by simpa using h1
      subst heq
      have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
        (ofString "alloc") _ _ b _ _ vals c lookup_alloc hl
      subst hsame
      decide
    · have heq : fn = ofString "trap_with" := by simpa using h2
      subst heq
      have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
        (ofString "trap_with") _ _ b _ _ vals c lookup_trap_with_fn hl
      subst hsame
      decide
  have hb_eq := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "htab_new")
    _ _ body' _ ret' values callee (by rw [hcode]; exact lookup_htab_new_fn) hlook
  have hkeep := InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG
    (ofString "scratch_ptr") htabNewCalleeGood hgood
    body' (by rw [hb_eq]; decide) (callEntryStateHOLFinite s callee) hcode
  rw [hrun] at hkeep
  exact globN_eq_of_lookup hkeep.symm

structure HeapLocalTab {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (t klen : Nat) : Prop extends LocalTab s S t klen where
  fp_heap : ∀ i ∈ htabFootprint s t, Inside i sourceBase (globN s "heap_ptr")

theorem heapLocalTab_with_locals {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {t klen : Nat} (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (ht : HeapLocalTab s S t klen) :
    HeapLocalTab { s with locals := locals, clock := k } S t klen :=
  ⟨localTab_with_locals locals k ht.toLocalTab, ht.fp_heap⟩

theorem worldStep_preserves_two_heapLocalTabs {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {aa ak : Nat} (haa : HeapLocalTab s S aa 20) (hak : HeapLocalTab s S ak 52)
    (haa_ne_ak : aa ≠ ak)
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hstep : WorldStep R gw keep Q s r post)
    (hR0 : ∀ x ∈ R s, x.2 = 0 → x.1 % 8 = 0)
    (hR_disj : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hR_aa : ∀ x ∈ R s, ∀ i ∈ htabFootprint s aa, Disj x i)
    (hR_ak : ∀ x ∈ R s, ∀ i ∈ htabFootprint s ak, Disj x i) :
    ∃ S' Nd',
      WorldTypedWith post (S' ++ [aa, ak]) Nd' ∧
      HeapLocalTab post (S' ++ [aa, ak]) aa 20 ∧
      HeapLocalTab post (S' ++ [aa, ak]) ak 52 ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post (S' ++ [aa, ak]) Nd') ∧
      Q s r post S' Nd' ∧
      (∀ {p sz : Nat}, HeapBuf s S Nd p sz → (∀ x ∈ R s, Disj (p, sz) x) →
        HeapBuf post (S' ++ [aa, ak]) Nd' p sz ∧ IvlUnhit s post (p, sz)) := by
  let S1 := S.erase aa
  let S0 := S1.erase ak
  have hW1 : WorldTypedWith s S1 Nd := worldTypedWith_erase_local hW haa.unassigned
  have hW0 : WorldTypedWith s S0 Nd := worldTypedWith_erase_local hW1 hak.unassigned
  have hsub1 : ∀ u ∈ S1, u ∈ S := fun u hu => List.mem_of_mem_erase hu
  have hsub0 : ∀ u ∈ S0, u ∈ S := fun u hu => hsub1 u (List.mem_of_mem_erase hu)
  have hsub_ti : ∀ i ∈ worldTypedIvls s S0 Nd, i ∈ worldTypedIvls s S Nd := by
    intro i hi
    unfold worldTypedIvls at hi ⊢
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    refine List.mem_map.2 ⟨j, ?_, rfl⟩
    simp only [List.mem_append] at hj ⊢
    rcases hj with ((((htab | hrec) | hjr) | hbo) | hbal) | hnd
    · obtain ⟨u, hu0, hj_fp⟩ := List.mem_flatMap.1 htab
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_flatMap.2 ⟨u, hsub0 u hu0, hj_fp⟩)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hrec))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr hjr)))
    · exact Or.inl (Or.inl (Or.inr hbo))
    · exact Or.inl (Or.inr hbal)
    · exact Or.inr hnd
  have hsub_ow0 : ∀ j ∈ worldOwned s S0 Nd, j ∈ worldOwned s S Nd := by
    intro j hj; unfold worldOwned at hj ⊢
    rcases List.mem_append.1 hj with h1 | hnd
    · apply List.mem_append.2; left
      rcases List.mem_append.1 h1 with htab | hfix
      · apply List.mem_append.2; left
        obtain ⟨u, hu0, hj_fp⟩ := List.mem_flatMap.1 htab
        exact List.mem_flatMap.2 ⟨u, hsub0 u hu0, hj_fp⟩
      · exact List.mem_append.2 (Or.inr hfix)
    · exact List.mem_append.2 (Or.inr hnd)
  have hR_disj0 : IvlsDisj (R s) (worldTypedIvls s S0 Nd) :=
    fun x hx i hi => hR_disj x hx i (hsub_ti i hi)
  obtain ⟨hAp, hhp, _, _, hWS⟩ := hstep
  obtain ⟨S', Nd', _, hW_S', hog0, hfr0, hQ0⟩ := hWS S0 Nd hW0 hR_disj0
  have hW_zero : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0 := worldOwned_zero_aligned hW
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have haa_not_S0 : aa ∉ S0 := by
    intro hm
    have hm1 : aa ∈ S1 := List.mem_of_mem_erase hm
    exact ((List.Nodup.mem_erase_iff hT.1).1 hm1).1 rfl
  have hak_not_S0 : ak ∉ S0 := by
    intro hm
    exact ((List.Nodup.mem_erase_iff (hT.1.erase aa)).1 hm).1 rfl
  have hdisj_tab_ow0 : ∀ {t : Nat}, t ∈ S → t ∉ S0 →
      ∀ i ∈ htabFootprint s t, ∀ j ∈ worldOwned s S0 Nd, Disj i j := by
    intro t htS ht_not i hi j hj
    unfold worldOwned at hj
    rcases List.mem_append.1 hj with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · obtain ⟨u, hu0, hj_fp⟩ := List.mem_flatMap.1 htab
        have hne : t ≠ u := fun heq => ht_not (heq ▸ hu0)
        exact hT.2.2.1 t htS u (hsub0 u hu0) hne i hi j hj_fp
      · exact ((hT.2.1 t htS).2 i hi).2 j hfix
    · exact disj_symm ((hTr.2.1 j hnd).1 t htS i hi)
  have htab_surv : ∀ {t : Nat} (htS : t ∈ S) (ht0 : t ∉ S0)
      (hfp_in : ∀ i ∈ htabFootprint s t, Inside i sourceBase (globN s "heap_ptr"))
      (hR_t : ∀ x ∈ R s, ∀ i ∈ htabFootprint s t, Disj x i),
      HtabWF post t ∧ htabFootprint post t = htabFootprint s t ∧
      hdr post t 0 = hdr s t 0 ∧
      (∀ i ∈ htabFootprint post t, Inside i sourceBase (globN post "heap_ptr") ∧
        ∀ o ∈ worldOwned post S' Nd', Disj i o) := by
    intro t htS ht0 hfp_in hR_t
    have hwf_s := (hT.2.1 t htS).1
    have hsurv_i : ∀ i ∈ htabFootprint s t,
        Inside i sourceBase (globN post "heap_ptr") ∧
        (∀ o ∈ worldOwned post S' Nd', Disj i o) ∧
        IvlUnhit s post i := by
      intro i hi
      have hw := (hwf_s.1 i hi).2
      exact heap_ivl_survives_step hAs.2 hhp (worldOwned_zero_aligned hW0) hR0
        hog0 hfr0 hw.1 hw.2.1
        (hfp_in i hi) (hdisj_tab_ow0 htS ht0 i hi)
        (fun x hx => disj_symm (hR_t x hx i hi))
    have hwf_post : HtabWF post t :=
      htabWF_congr_unhit hAs.1 hAp.1 hwf_s (fun i hi => (hsurv_i i hi).2.2)
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf_s.1 _ ht_fp).2.1
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf_s.1 _ ht_fp).1.2; omega
    obtain ⟨hhdr_eq, hfp_eq⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhi (hsurv_i _ ht_fp).2.2
    refine ⟨hwf_post, hfp_eq, hhdr_eq 0 (by omega), fun i hi => ?_⟩
    rw [hfp_eq] at hi
    exact ⟨(hsurv_i i hi).1, (hsurv_i i hi).2.1⟩
  obtain ⟨hwf_aa, hfp_aa, hhdr_aa, hsurv_aa⟩ := htab_surv haa.mem_S haa_not_S0 haa.fp_heap hR_aa
  obtain ⟨hwf_ak, hfp_ak, hhdr_ak, hsurv_ak⟩ := htab_surv hak.mem_S hak_not_S0 hak.fp_heap hR_ak
  have hadjoin : ∀ {U : List Nat} {t klen : Nat},
      WorldTypedWith post U Nd' →
      HtabWF post t → t ≠ 0 → hdr post t 0 = klen →
      (∀ i ∈ htabFootprint post t, Inside i sourceBase (globN post "heap_ptr") ∧
        ∀ o ∈ worldOwned post U Nd', Disj i o) →
      WorldTypedWith post (U ++ [t]) Nd' ∧ HeapLocalTab post (U ++ [t]) t klen := by
    intro U t klen hWU hwf_t ht_nz hklen hfp_t
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
          refine ⟨hwf_t, fun i hi => ⟨Or.inl (hfp_t i hi).1, fun j hj => ?_⟩⟩
          apply (hfp_t i hi).2 j
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
      · intro u hu v hv hne i hi j hj
        rcases List.mem_append.1 hu with huU | hut <;> rcases List.mem_append.1 hv with hvU | hvt
        · exact hTpU u huU v hvU hne i hi j hj
        · simp only [List.mem_singleton] at hvt; subst hvt
          apply disj_symm; apply (hfp_t j hj).2 i
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
          apply disj_symm; apply (hfp_t i hi).2 o
          unfold worldOwned; exact List.mem_append.2 (Or.inr ho)
      · intro hnz
        refine ⟨(hTrU.2.2 hnz).1, fun hm => ?_⟩
        rcases List.mem_append.1 hm with hmU | hmt
        · exact (hTrU.2.2 hnz).2 hmU
        · simp only [List.mem_singleton] at hmt
          rcases hwsU 32 (by simp [wsTableSlots]) hnz with h0 | hmU
          · exact absurd (h0.symm.trans hmt).symm ht_nz
          · exact absurd (hmt ▸ hmU) ht_not_U
    refine ⟨⟨hTU', hJU', hFU, hTrU'⟩,
      ⟨⟨List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)), ht_nz, hklen, ht_unass⟩,
        fun i hi => (hfp_t i hi).1⟩⟩
  obtain ⟨hW_aa, haa_post1⟩ := hadjoin hW_S' hwf_aa haa.nz (hhdr_aa.trans haa.hdr0) hsurv_aa
  have hsurv_ak2 : ∀ i ∈ htabFootprint post ak, Inside i sourceBase (globN post "heap_ptr") ∧
      ∀ o ∈ worldOwned post (S' ++ [aa]) Nd', Disj i o := by
    intro i hi
    refine ⟨(hsurv_ak i hi).1, fun o ho => ?_⟩
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htab' | htab_aa
        · apply (hsurv_ak i hi).2 o
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab')))
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htab_aa
          rw [hfp_ak] at hi; rw [hfp_aa] at htab_aa
          exact hT.2.2.1 ak hak.mem_S aa haa.mem_S haa_ne_ak.symm i hi o htab_aa
      · apply (hsurv_ak i hi).2 o
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    · apply (hsurv_ak i hi).2 o
      unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
  obtain ⟨hW_both, hak_post2⟩ := hadjoin hW_aa hwf_ak hak.nz (hhdr_ak.trans hak.hdr0) hsurv_ak2
  have hassoc_S : (S' ++ [aa]) ++ [ak] = S' ++ [aa, ak] := by simp
  rw [hassoc_S] at hW_both hak_post2
  have haa_post2 : HeapLocalTab post (S' ++ [aa, ak]) aa 20 :=
    ⟨⟨by simp, haa_post1.nz, haa_post1.hdr0, haa_post1.unassigned⟩, haa_post1.fp_heap⟩
  have hog_full : OwnedGrows s post (worldOwned s S Nd) (worldOwned post (S' ++ [aa, ak]) Nd') := by
    intro o ho
    have hog0_sub : ∀ x ∈ worldOwned post S' Nd',
        x = (0, 0) ∨ (∃ j ∈ worldOwned s S Nd, Inside x j.1 (j.1 + j.2)) ∨
        Inside x (globN s "heap_ptr") (globN post "heap_ptr") := by
      intro x hx
      rcases hog0 x hx with rfl | ⟨j, hj0, hin⟩ | hfr
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨j, hsub_ow0 j hj0, hin⟩)
      · exact Or.inr (Or.inr hfr)
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htab' | htab_loc
        · apply hog0_sub o
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab')))
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at htab_loc
          rcases htab_loc with haa_fp | hak_fp
          · rw [hfp_aa] at haa_fp
            refine Or.inr (Or.inl ⟨o, ?_, ⟨le_rfl, le_rfl⟩⟩)
            unfold worldOwned
            exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨aa, haa.mem_S, haa_fp⟩))))
          · rw [hfp_ak] at hak_fp
            refine Or.inr (Or.inl ⟨o, ?_, ⟨le_rfl, le_rfl⟩⟩)
            unfold worldOwned
            exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨ak, hak.mem_S, hak_fp⟩))))
      · apply hog0_sub o
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    · apply hog0_sub o
      unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
  refine ⟨S', Nd', hW_both, haa_post2, hak_post2, hog_full, hQ0, ?_⟩
  intro p sz hb hb_R
  have hfr_sub : FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) := by
    intro a hkeep hfresh
    apply hfr0 a
    · intro j hj hcj
      apply hkeep j ?_ hcj
      rcases List.mem_append.1 hj with hj12 | hfg
      · apply List.mem_append.2; left
        rcases List.mem_append.1 hj12 with hj0 | hjR
        · exact List.mem_append.2 (Or.inl (hsub_ow0 j hj0))
        · exact List.mem_append.2 (Or.inr hjR)
      · exact List.mem_append.2 (Or.inr hfg)
    · exact hfresh
  exact heapBuf_survives_step hAs.2 hhp hW_zero hR0 hog_full hfr_sub hb hb_R

theorem panMemStoresHOL_frame {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
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
    have ih := panMemStoresHOL_frame ws (x + panBytesInWord 64)
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

theorem panMemStoresHOL_nonempty_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom}
    {w : HolWordLab 64} {ws : List (HolWordLab 64)} {x : BitVec 64}
    {mem mem' : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ x (w :: ws) dom dec mem = some mem') :
    dom x := by
  unfold panMemStoresHOL panMemStoreHOL at hst
  split_ifs at hst with hdom
  exact hdom

theorem ivlUnhit_words {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {x : BitVec 64} {n : Nat} {i : Ivl}
    (hx_hi : x.toNat + 8 * n ≤ 2 ^ 64)
    (hm : ∀ a : BitVec 64, (∀ k, k < n → a ≠ x + BitVec.ofNat 64 (8 * k)) → post.memory a = s.memory a)
    (hi0 : i.2 = 0 → i.1 % 8 = 0)
    (hd : Disj i (x.toNat, 8 * n)) : IvlUnhit s post i := by
  intro a ha8 hch
  apply hm a
  intro k hk heq
  subst heq
  have h8k : 8 * k < 2 ^ 64 := by omega
  have hadd : (x + BitVec.ofNat 64 (8 * k)).toNat = x.toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h8k,
      Nat.mod_eq_of_lt (by omega)]
  exact not_cellHits_of_disj ha8 hi0 ⟨by rw [hadd]; omega, by rw [hadd]; omega⟩ (disj_symm hd) hch

theorem store_heapBuf_world {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {p sz : Nat} (hb : HeapBuf s S Nd p sz)
    {x : BitVec 64} {n : Nat} (hn : 0 < n)
    (hin : Inside (x.toNat, 8 * n) p (p + sz))
    {mem' : BitVec 64 → HolWordLab 64}
    (hm : ∀ a : BitVec 64, (∀ k, k < n → a ≠ x + BitVec.ofNat 64 (8 * k)) → mem' a = s.memory a) :
    let post : PanSemStateFiniteExact 64 F := { s with memory := mem' }
    ArenaReady post ∧
    WorldTypedWith post S Nd ∧
    worldOwned post S Nd = worldOwned s S Nd ∧
    worldRoleSlots post = worldRoleSlots s ∧
    journalRoleSlots post = journalRoleSlots s ∧
    (∀ t ∈ S, hdr post t 0 = hdr s t 0) ∧
    TxEnv post ∧
    (∀ {q qsz : Nat}, HeapBuf s S Nd q qsz → Disj (q, qsz) (p, sz) →
      HeapBuf post S Nd q qsz ∧ IvlUnhit s post (q, qsz)) := by
  let post : PanSemStateFiniteExact 64 F := { s with memory := mem' }
  have hAp : ArenaReady post := ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩
  have hp_hi := (ivl_allocated_bound hA.2 (Or.inl hb.inside)).2
  have hx_hi : x.toNat + 8 * n ≤ 2 ^ 64 := by
    unfold Inside at hin; dsimp at hin hp_hi; omega
  have unhit_ow (i : Ivl) (hi : i ∈ worldOwned s S Nd) : IvlUnhit s post i :=
    ivlUnhit_words hx_hi hm (worldOwned_zero_aligned hW i hi)
      (disj_of_inside_right hin (disj_symm (hb.disj i hi)))
  have fixedOwned (i : Ivl) (hi : i ∈ fixedObjects s) : i ∈ worldOwned s S Nd :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hi)))
  have recUnhit (r : String × Nat) (hr : r ∈ typedRecords) (hnz : globN s r.1 ≠ 0) :
      IvlUnhit s post (globN s r.1, r.2) :=
    unhit_ow _ (fixedOwned _ (by simpa only [hnz, if_false] using typedRecord_mem_fixedObjects s hr))
  have hboU := recUnhit ("bo", 88) (by simp [typedRecords]) hE.bo_nz
  have hboW : ∀ k, k % 8 = 0 → k + 8 ≤ 88 →
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk hkle
    have hw := bo_words hW.2.2.1 hE.bo_nz
    have hhi := (ivl_allocated_bound hA.2 hw.1).2
    exact memW_eq_of_ivlUnhit hboU (by have := hw.2.1; omega) hhi ⟨by dsimp; omega, by dsimp; omega⟩
  have hm0 : memW post 0 = memW s 0 ∧ memW post 16 = memW s 16 := by
    have hlo : sourceBase ≤ x.toNat := Nat.le_trans hb.inside.1 hin.1
    have hsb : 16 < sourceBase := by decide
    have hne_small : ∀ (c : Nat), c ≤ 16 → ∀ k, k < n → BitVec.ofNat 64 c ≠ x + BitVec.ofNat 64 (8 * k) := by
      intro c hc k hk heq
      have h8k : 8 * k < 2 ^ 64 := by omega
      have h1 := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h8k,
        Nat.mod_eq_of_lt (by omega)] at h1
      omega
    exact ⟨by unfold memW; dsimp only [post]; rw [hm _ (hne_small 0 (by omega))],
      by unfold memW; dsimp only [post]; rw [hm _ (hne_small 16 (by omega))]⟩
  obtain ⟨hW', how_eq, hwrs_eq, hjrs_eq, hhdr_eq⟩ :=
    worldTypedWith_congr_bo hA hAp rfl ⟨le_rfl, le_rfl⟩
      (worldGlobalsSame_of_globals_eq (s := s) (post := post) rfl) hW
      (fun t ht i hi => unhit_ow i
        (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨t, ht, hi⟩))))))
      (recUnhit ("ws", 40) (by simp [typedRecords]))
      (recUnhit ("bs", 80) (by simp [typedRecords]))
      (recUnhit ("ts", 72) (by simp [typedRecords]))
      (fun hnz => unhit_ow _ (fixedOwned _ (fixed_mem_raw
        (by simp only [fixedRaw, List.mem_append]; exact Or.inl (Or.inl (Or.inr (by simp))))
        (by dsimp; omega))))
      (fun i hi h24 => unhit_ow i (fixedOwned i (fixed_mem_raw (block_mem_raw hi) (by omega))))
      (fun i hi => unhit_ow i (fixedOwned i (mem_normalized (List.mem_append.2 (Or.inr hi)) (normalized_mem_zero hi))))
      (fun o ho => unhit_ow o (List.mem_append.mpr (Or.inr ho)))
      (fun _ k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hboW _ (by omega) (by omega))
      hm0
  have hE' : TxEnv post := by
    refine ⟨hE.bo_nz, ?_, ?_, ?_, ?_, ?_, hE.jcap_nz⟩
    · change memW post (globN s "bo" + 24) ≠ 0; rw [hboW 24 (by omega) (by omega)]; exact hE.bo24
    · change memW post (globN s "bo" + 32) ≠ 0; rw [hboW 32 (by omega) (by omega)]; exact hE.bo32
    · change memW post (globN s "bo" + 40) ≠ 0; rw [hboW 40 (by omega) (by omega)]; exact hE.bo40
    · change memW post (globN s "bo" + 72) ≠ 0; rw [hboW 72 (by omega) (by omega)]; exact hE.bo72
    · change locN s "index" < memW post (globN s "bo" + 80); rw [hboW 80 (by omega) (by omega)]; exact hE.idx_lt
  refine ⟨hAp, hW', how_eq, hwrs_eq, hjrs_eq, hhdr_eq, hE', ?_⟩
  intro q qsz hq hdq
  have hq' : HeapBuf post S Nd q qsz := ⟨hq.p8, hq.sz8, hq.inside, by rw [how_eq]; exact hq.disj⟩
  refine ⟨hq', ivlUnhit_words hx_hi hm (fun _ => hq.p8) (disj_of_inside_right hin hdq)⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2
