import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2BackingPre

/-!
# Phase 2 backing replay, region B (guest spine 44..48)

The address-array allocation, the beneficiary store, and the counting loop,
with the auxiliary conjunct `PtxPhase2X` carried throughout. The frozen
region-B machinery of `PtxPhase2Strong` supplies the joint address invariant,
the counting invariant and the loop bounds; this file threads `PtxPhase2X`
alongside them so the far-side bridge can consume both.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards

/-! ## Separation helpers for the address block -/

/-- A cell of an interval separated from a block never coincides with a cell
of the block. -/
private theorem ptxPhase2B_cell_ne {p L b0 sz x : Nat} (k : Nat)
    (hn : p + L ≤ b0 ∨ b0 + sz ≤ p) (hb : b0 + k < 2 ^ 64) (hk : k < sz)
    (hxin : p ≤ x) (hxlt : x < p + L) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 (b0 + k) ≠ BitVec.ofNat 64 x := by
  intro he
  have h1 : (BitVec.ofNat 64 (b0 + k)).toNat = b0 + k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  have h2 : (BitVec.ofNat 64 x).toNat = x := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  have he' := congrArg BitVec.toNat he
  rw [h1, h2] at he'
  rcases hn with h | h <;> omega

/-- Every nonempty world-owned interval starts past the address block or ends
before it. -/
private theorem ptxPhase2B_disj_of_world {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {p L a sz : Nat}
    (hd : IvlsDisj [(p, L)] (worldOwned s S Nd))
    (hmem : (a, sz) ∈ worldOwned s S Nd) (hsz : 0 < sz) (hL : 0 < L) :
    p + L ≤ a ∨ a + sz ≤ p := by
  rcases hd (p, L) (by simp) (a, sz) hmem with h | h | h | h
  · exact absurd h (by omega)
  · exact absurd h (by omega)
  · exact Or.inl h
  · exact Or.inr h

/-- The block-out record cells and the two list data pointers never coincide
with a cell inside the address array. -/
theorem ptxPhase2B_joint_miss {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressJoint s) (hx : PtxPhase2X s) {p : Nat}
    (hxin : locN s "al_addrs" ≤ p)
    (hxlt : p < locN s "al_addrs" + (locN s "nal" + 1) * 8) :
    (∀ c ∈ ([24, 32, 40, 72, 80] : List Nat),
      BitVec.ofNat 64 (globN s "bo" + c) ≠ BitVec.ofNat 64 p) ∧
    (∀ c ∈ ([40, 72] : List Nat),
      BitVec.ofNat 64 (memW s (globN s "bo" + c)) ≠ BitVec.ofNat 64 p) := by
  obtain ⟨S, Nd, hW, hT, hd, -⟩ := hp.2
  have hAR : ArenaReady s := hp.1.1.1.1.1.1.1.1.1.1
  have hAO : ArenaOK s := hAR.2
  have hF : FixedTyped s := hW.2.2.1
  have hnz : globN s "bo" ≠ 0 := hx.2.2.1.bo_nz
  have hbo_al := bo_words hF hnz
  have hbo_mem : (globN s "bo", 88) ∈ worldOwned s S Nd := by
    have hm := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    simp only [hnz, ↓reduceIte] at hm
    simp only [worldOwned, List.mem_append]
    exact Or.inl (Or.inr hm)
  have hlst_mem : ∀ c ∈ ([40, 72] : List Nat),
      (memW s (globN s "bo" + c), 24) ∈ worldOwned s S Nd := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · have hm : (memW s (globN s "bo" + 40), 24) ∈ fixedObjects s := by
        simp [fixedObjects, blockOutObjects, hnz, hx.2.2.1.bo40]
      simp only [worldOwned, List.mem_append]
      exact Or.inl (Or.inr hm)
    · have hm : (memW s (globN s "bo" + 72), 24) ∈ fixedObjects s := by
        simp [fixedObjects, blockOutObjects, hnz, hx.2.2.1.bo72]
      simp only [worldOwned, List.mem_append]
      exact Or.inl (Or.inr hm)
  have hl40 : memW s (globN s "bo" + 40) < 2 ^ 64 := by
    obtain ⟨w, -, hw⟩ := hbo_al.2.2.2 5 (by show 5 < 88 / 8; decide)
    have hw' : s.memory (BitVec.ofNat 64 (globN s "bo" + 40)) = .word w := hw
    have hw64 : w.toNat < 2 ^ 64 := w.isLt
    simp only [memW, hw'] at *
    exact hw64
  have hl72 : memW s (globN s "bo" + 72) < 2 ^ 64 := by
    obtain ⟨w, -, hw⟩ := hbo_al.2.2.2 9 (by show 9 < 88 / 8; decide)
    have hw' : s.memory (BitVec.ofNat 64 (globN s "bo" + 72)) = .word w := hw
    have hw64 : w.toNat < 2 ^ 64 := w.isLt
    simp only [memW, hw'] at *
    exact hw64
  have hbo_bound : globN s "bo" + 88 ≤ 2 ^ 64 := (ivl_allocated_bound hAO hbo_al.1).2
  have hp64 : p < 2 ^ 64 := by
    have h2 : globN s "heap_ptr" ≤ 2 ^ 64 := Nat.le_trans hAO.2.1 (by decide)
    have hins := hp.1.2.2.1
    have h1 := hins.1
    have h2' := hins.2
    omega
  have hbo_disj := ptxPhase2B_disj_of_world hd hbo_mem (by decide) (by omega)
  refine ⟨?_, ?_⟩
  · intro c hc
    have hc88 : c < 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega
    have hb : globN s "bo" + c < 2 ^ 64 := by omega
    exact ptxPhase2B_cell_ne c hbo_disj hb hc88 hxin hxlt hp64
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · have hd := ptxPhase2B_disj_of_world hd (hlst_mem 40 (by simp)) (by decide) (by omega)
      exact ptxPhase2B_cell_ne 0 hd hl40 (by decide) hxin hxlt hp64
    · have hd := ptxPhase2B_disj_of_world hd (hlst_mem 72 (by simp)) (by decide) (by omega)
      exact ptxPhase2B_cell_ne 0 hd hl72 (by decide) hxin hxlt hp64

/-! ## Allocation of the address array (guest spine 44) -/

/-- Resuming after the address-array allocation with the full auxiliary
conjunct: the callee leaves memory and every non-`heap_ptr` global untouched,
so all four components transfer wholesale. -/
theorem ptxPhase2B_alAddrs_X_resume (h : PtxCallees) :
    DecCallResumeOn (fun s => PtxAccessCountReady s ∧ PtxPhase2X s)
      (fun s => PtxAddressJoint s ∧ PtxPhase2X s) (ofString "al_addrs") (ofString "alloc")
      [.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hb0 := hb
  have hbody : body = InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
      Guest.Software.guestFn_alloc :=
    InitECandidate.Solver.PanRunBounded.lookupCodeHOLFinite_installed_body s.code.lookup
      (ofString "alloc") [(ofString "n", .one)]
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_alloc) body
      .one ret vs callee
      (by rw [hc]; exact InitECandidate.Solver.GuestTrapAndLookup.lookup_alloc) hl
  rw [hbody] at hb
  obtain ⟨w_nal, hlu_nal⟩ := hp.1.2.1
  have harg_ev : evalAt s
      (.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]) =
      some (.val (.word ((w_nal + 1#64) * 8#64))) := by
    simp only [evalAt, evalHOLExact, evalListHOLExact, hlu_nal, valueIsWord, valueWord, panOpHOL,
      wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, if_true,
      Option.some.injEq]
    simp [List.foldr]
  have hpc := R16Shards.callee_param_one_exp s (ofString "alloc") (ofString "n") .one
    (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_alloc) .one
    (by rw [hc]; exact InitECandidate.Solver.GuestTrapAndLookup.lookup_alloc)
    (.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8])
    (.val (.word ((w_nal + 1#64) * 8#64))) vs body callee ret harg_ev ha hl
  have hnloc : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n") =
      some (.val (.word ((w_nal + 1#64) * 8#64))) := hpc.2
  have hA' : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1.1.1.1.1.1.1.1.1
  obtain ⟨hpw, hhp⟩ := hA'.2.2.2.2.2.2.2.2.2 "heap_ptr" (by simp [guestGlobalNames])
  have hcode' : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hc
  have hout1 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
        Guest.Software.guestFn_alloc)).1 = some (.returned v) := by rw [hb]
  obtain ⟨-, -, -, hEq⟩ := InitECandidate.Solver.Wave8Contracts.M27.alloc_body_run
    (callEntryStateHOLFinite s callee) hpw ((w_nal + 1#64) * 8#64) hcode' hhp hnloc v hout1
  have hpost : post = (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
        Guest.Software.guestFn_alloc)).2 := by rw [hb]
  have hmemF : ∀ a, post.memory a = s.memory a := by
    intro a
    rw [hpost, hEq]
    rfl
  have hgl (m : MlS) (hm : m ≠ ofString "heap_ptr") :
      post.globals.lookup m = s.globals.lookup m := by
    rw [hpost, hEq]
    have hentry : (callEntryStateHOLFinite s callee).globals = s.globals := rfl
    rw [hentry]
    show (s.globals.update (ofString "heap_ptr", _)).lookup m = s.globals.lookup m
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hm.symm]
  have hboG : globN post "bo" = globN s "bo" := by
    unfold globN
    rw [hgl (ofString "bo") (by decide)]
  have hjcG : globN post "journal_cap" = globN s "journal_cap" := by
    unfold globN
    rw [hgl (ofString "journal_cap") (by decide)]
  have htxPost : TxBacking {post with locals := s.locals} :=
    ptxPhase2_txBacking_of_mem_eq hp.2.2.1 hboG hmemF
  have hX : PtxPhase2X {post with locals := s.locals} := by
    refine ptxPhase2X_of_cells hp.2 htxPost rfl hboG hjcG rfl ?_
    intro k hk
    unfold memW
    rw [hmemF]
  refine ⟨phase2_address_alloc_joint h s vs body callee ret v post hc hp.1 ha hl hb0,
    ptxPhase2X_setVar_other _ v ?_ hX⟩
  intro n hn
  simp only [ptxPhase2XNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## The beneficiary store (guest spine 45) -/

/-- Storing the beneficiary address into the first array slot preserves both
the joint invariant and the auxiliary conjunct. -/
theorem ptxPhase2B_beneficiaryX_hoare :
    Hoare (fun s => PtxAddressJoint s ∧ PtxPhase2X s)
      (.store (.var .local (ofString "al_addrs"))
        (.load .one (.op .add [.var .global (ofString "be"), .const 32])))
      (fun r s => r = none → PtxAddressJoint s ∧ PtxPhase2X s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  have hlen := phase2_load_one_length s _ v hv
  have hex : ∃ w, flattenHOL v = [w] := by
    cases hs : flattenHOL v with
    | nil => simp [hs] at hlen
    | cons w ws =>
      cases ws with
      | nil => exact ⟨w, rfl⟩
      | cons a rest => simp [hs] at hlen
  obtain ⟨w, hw⟩ := hex
  rw [hw] at hst
  obtain ⟨hdom, -, hmem⟩ := panMemStoresHOL_word_spec hst
  obtain ⟨a, ha⟩ := hp.1.1.2.1
  have he : x = a := by simpa [evalAt, evalHOLExact, ha] using hx.symm
  subst x
  have hl : locN s "al_addrs" = a.toNat := by simp [locN, ha]
  have ha64 : a.toNat < 2 ^ 64 := a.isLt
  have hxe : a = BitVec.ofNat 64 a.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64]
  have hmiss := ptxPhase2B_joint_miss hp.1 hp.2 (p := a.toNat)
    (by rw [hl]) (by rw [hl]; omega)
  refine ⟨?_, ?_⟩
  · apply phase2_address_joint_store hp.1 hdom _ hmem
    rw [hl]
    constructor <;> dsimp <;> omega
  · refine ptxPhase2X_store hp.2 hmem ?_ ?_
    · intro k hk
      rw [hxe]
      exact hmiss.1 k hk
    · intro k hk
      rw [hxe]
      exact hmiss.2 k hk

/-! ## The counting loop with the auxiliary conjunct (guest spine 46..48) -/

/-- The fresh counting locals leave the auxiliary conjunct untouched. -/
theorem ptxPhase2X_setVar_nkeys {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hp : PtxPhase2X s) : PtxPhase2X (setVarHOLFinite (ofString "nkeys") v s) :=
  ptxPhase2X_setVar_other s v (by
    intro n hn
    simp only [ptxPhase2XNames, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hp

theorem ptxPhase2X_setVar_i {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hp : PtxPhase2X s) : PtxPhase2X (setVarHOLFinite (ofString "i") v s) :=
  ptxPhase2X_setVar_other s v (by
    intro n hn
    simp only [ptxPhase2XNames, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hp

theorem ptxPhase2X_setVar_acc {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hp : PtxPhase2X s) : PtxPhase2X (setVarHOLFinite (ofString "acc") v s) :=
  ptxPhase2X_setVar_other s v (by
    intro n hn
    simp only [ptxPhase2XNames, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hp

/-- The array-slot store of the counting loop, with the auxiliary conjunct. -/
theorem ptxPhase2B_count_store_recordX_hoare :
    Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
      locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i" ∧ PtxPhase2X s)
      (.store (.op .add [.var .local (ofString "al_addrs"),
        .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
        (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
      (fun r s => r = none → PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
        locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i" ∧ PtxPhase2X s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  have hlen := phase2_load_one_length s _ v hv
  have hex : ∃ w, flattenHOL v = [w] := by
    cases hs : flattenHOL v with
    | nil => simp [hs] at hlen
    | cons w ws =>
      cases ws with
      | nil => exact ⟨w, rfl⟩
      | cons a rest => simp [hs] at hlen
  obtain ⟨w, hw⟩ := hex
  rw [hw] at hst
  obtain ⟨a, ha⟩ := hp.1.1.1.1.2.1
  obtain ⟨i, hi⟩ := hp.1.1.2.1
  have he : x = a + (i + 1) * 8 := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, ha, hi,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] using hx.symm
  have hslot := (phase2_address_copy_slot hp.1.1.1 (locN s "i") hp.2.1).2
  rw [← phase2_address_copy_word_addr hp.1.1 a i ha hi, ← he] at hslot
  obtain ⟨hdom, -, hmem⟩ := panMemStoresHOL_word_spec hst
  have hxe : x = BitVec.ofNat 64 x.toNat := by
    apply BitVec.eq_of_toNat_eq
    have hlt : x.toNat < 2 ^ 64 := by
      have hAR : ArenaReady s := hp.1.1.1.1.1.1.1.1.1.1.1.1.1
      have h2 : globN s "heap_ptr" ≤ 2 ^ 64 := Nat.le_trans hAR.2.2.1 (by decide)
      have hins := hp.1.1.1.1.2.2.1
      have h1 := hins.1
      have h2' := hins.2
      have h3 := hslot.1
      have h4 := hslot.2
      omega
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hmiss := ptxPhase2B_joint_miss hp.1.1.1 hp.2.2.2 (p := x.toNat)
    (by have h3 := hslot.1; omega) (by have h4 := hslot.2; omega)
  refine ⟨phase2_address_count_store hp.1 hdom hslot hmem, hp.2.1,
    phase2_address_count_store_acc hp.1 hslot hmem hp.2.2.1, ?_⟩
  refine ptxPhase2X_store hp.2.2.2 hmem ?_ ?_
  · intro k hk
    rw [hxe]
    exact hmiss.1 k hk
  · intro k hk
    rw [hxe]
    exact hmiss.2 k hk

/-- The key-count assignment with the auxiliary conjunct. -/
theorem ptxPhase2B_count_nkeysX_hoare :
    Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
      locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i" ∧ PtxPhase2X s)
      (.assign .local (ofString "nkeys")
        (.op .add [.var .local (ofString "nkeys"),
          .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
      (fun r s => r = none → PtxAddressCopyInv s ∧ locN s "i" < locN s "nal" ∧
        locN s "nal" = memW s (locN s "tx" + 216) ∧
        locN s "nkeys" = phase2_key_prefix s (locN s "i" + 1) ∧ PtxPhase2X s) := by
  apply Hoare.assign
  · intro F s v hp he
    rw [phase2_count_add_eval s hp.1 v hp.2.2.1 he]
    have hca := phase2_address_count_add s hp.1 hp.2.1
    exact fun _ => ⟨hca.1, hca.2.1, hca.2.2.1, hca.2.2.2,
      ptxPhase2X_setVar_nkeys s _ hp.2.2.2⟩
  · exact fun _ _ hr => by cases hr

/-- The index increment with the auxiliary conjunct. -/
theorem ptxPhase2B_count_incrementX_hoare :
    Hoare (fun s => PtxAddressCopyInv s ∧ locN s "i" < locN s "nal" ∧
      locN s "nal" = memW s (locN s "tx" + 216) ∧
      locN s "nkeys" = phase2_key_prefix s (locN s "i" + 1) ∧ PtxPhase2X s)
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r s => r = none → PtxAddressCountInv s ∧ PtxPhase2X s) := by
  apply Hoare.assign
  · intro F s v hp he
    obtain ⟨w, hw⟩ := hp.1.2.1
    have hv : v = .val (.word (w + 1)) := by
      simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord,
        valueWord, wordOpHOL, wordOp] using he.symm
    subst v
    have hwN : locN s "i" = w.toNat := by simp [locN, hw]
    have hadd : w + 1 = BitVec.ofNat 64 (locN s "i" + 1) := by
      rw [hwN]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [hadd]
    exact fun _ => ⟨phase2_address_count_advance s hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1,
      ptxPhase2X_setVar_i s _ hp.2.2.2.2⟩
  · exact fun _ _ hr => by cases hr

/-- The store and both counter updates preserve the cumulative count and the
auxiliary conjunct. -/
theorem ptxPhase2B_count_innerX_hoare :
    Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
      locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i" ∧ PtxPhase2X s)
      (.seq
        (.store (.op .add [.var .local (ofString "al_addrs"),
          .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
          (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
        (.seq
          (.assign .local (ofString "nkeys")
            (.op .add [.var .local (ofString "nkeys"),
              .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 1]))))
      (fun r s => r = none → PtxAddressCountInv s ∧ PtxPhase2X s) := by
  refine Hoare.seq_fall ptxPhase2B_count_store_recordX_hoare ?_
  refine Hoare.seq_fall ptxPhase2B_count_nkeysX_hoare ?_
  exact ptxPhase2B_count_incrementX_hoare

/-- The complete counting/address-copy body preserves the strengthened
invariant and the auxiliary conjunct. -/
theorem ptxPhase2B_count_bodyX_hoare :
    Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧ PtxPhase2X s)
      (.dec (ofString "acc") .one
        (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
          .panop .mul [.var .local (ofString "i"), .const 24]])
        (.seq
          (.store (.op .add [.var .local (ofString "al_addrs"),
            .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
            (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
          (.seq
            (.assign .local (ofString "nkeys")
              (.op .add [.var .local (ofString "nkeys"),
                .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1])))))
      (fun r s => r = none → PtxAddressCountInv s ∧ PtxPhase2X s) := by
  apply Hoare.dec (names := ["i", "nkeys", "al_addrs", "nal", "te", "tx", "index", "sender",
    "mgas", "reservoir", "gas", "tx_blob_gas_used", "price", "enc", "intrinsic"])
    (P' := fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
      locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i" ∧ PtxPhase2X s) (by decide)
  · intro F s v hp he
    have hda := phase2_address_count_declare_acc s hp.1 hp.2.1 v he
    exact ⟨hda.1, hda.2.1, hda.2.2, ptxPhase2X_setVar_acc s _ hp.2.2⟩
  · exact ptxPhase2B_count_innerX_hoare
  · intro F r s locals hl hp hr
    exact ⟨phase2_address_count_with_locals s locals s.clock (hp hr).1 hl,
      ptxPhase2X_with_locals s locals s.clock (fun n hn => hl n (by
        simp only [ptxPhase2XNames, List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
        (hp hr).2⟩
  · exact fun _ _ hr => by cases hr

/-- The guarded counting loop preserves the auxiliary conjunct alongside the
strengthened invariant, exiting with the index equal to the record count. -/
theorem ptxPhase2B_while_countX_hoare {body : ProgHOL 64}
    (hb : Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
      PtxPhase2X s) body
      (fun r s => r = none → PtxAddressCountInv s ∧ PtxPhase2X s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare (fun s => PtxAddressCountInv s ∧ PtxPhase2X s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body)
      (fun r s => r = none →
        (PtxAddressCountInv s ∧ locN s "i" = locN s "nal") ∧ PtxPhase2X s) := by
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s
    (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body)
    = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → PtxAddressCountInv st ∧ PtxPhase2X st →
      evaluateHOLFiniteState st
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body) =
          (none, post) →
      (PtxAddressCountInv post ∧ locN post "i" = locN post "nal") ∧ PtxPhase2X post from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd : PtxAddressCountInv (decClockHOLFinite st) :=
            phase2_address_count_with_locals st st.locals (st.clock - 1) hp.1 (by intros; rfl)
          have hXd : PtxPhase2X (decClockHOLFinite st) :=
            ptxPhase2X_with_locals st st.locals (st.clock - 1) (by intros; rfl) hp.2
          have hg := phase2_address_copy_guard hp.1.1 w hw hnz
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body
            hnb (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body
            hnc (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc
              ⟨hd, hg, hXd⟩ (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        have hwz : w = 0 := by simpa using hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨⟨hp.1, phase2_address_copy_exit hp.1.1 (by simpa [evalAt, hwz] using hw)⟩, hp.2⟩
    · simp at he

/-- Both counting cases exit with the full invariant and the conjunct. -/
theorem ptxPhase2B_countCases_whileX_hoare :
    Hoare (fun s => PtxAddressCountCases s ∧ PtxPhase2X s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        (.dec (ofString "acc") .one
          (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
            .panop .mul [.var .local (ofString "i"), .const 24]])
          (.seq
            (.store (.op .add [.var .local (ofString "al_addrs"),
              .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
              (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
            (.seq
              (.assign .local (ofString "nkeys")
                (.op .add [.var .local (ofString "nkeys"),
                  .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1]))))))
      (fun r s => r = none → PtxAddressCountExit s ∧ PtxPhase2X s) := by
  refine ⟨fun {F} s hc hp hnt hr => ?_⟩
  rcases hp.1 with hinv | hzero
  · have hwx := (ptxPhase2B_while_countX_hoare ptxPhase2B_count_bodyX_hoare (by decide)
      (by decide)).run s hc ⟨hinv, hp.2⟩ hnt hr
    exact ⟨Or.inl hwx.1, hwx.2⟩
  · rw [phase2_address_zero_loop s _ hzero.1 hzero.2.1] at hr ⊢
    exact ⟨Or.inr hzero, hp.2⟩

/-! ## Region B segment bound (guest spine 44..48) -/

/-- The allocation, beneficiary store and counting loop compose with the
auxiliary conjunct carried along. -/
theorem ptxPhase2B_addressLoopX_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => PtxAddressCountExit s ∧ PtxPhase2X s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxAccessCountReady s ∧ PtxPhase2X s)
      (spinePlug 5 (spineAt 44 ptxCode) tail)
      (K.alloc + ((2 ^ 63 + 1) + b) + 1) := by
  have he : spinePlug 5 (spineAt 44 ptxCode) tail =
      .decCall (ofString "al_addrs") .one (ofString "alloc")
        [.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]]
        (.seq (.store (.var .local (ofString "al_addrs"))
          (.load .one (.op .add [.var .global (ofString "be"), .const 32])))
          (.dec (ofString "nkeys") .one (.const 0)
            (.dec (ofString "i") .one (.const 0)
              (.seq
                (.while (.cmp .less (.var .local (ofString "i"))
                  (.var .local (ofString "nal")))
                  (.dec (ofString "acc") .one
                    (.op .add [.load .one (.op .add [.var .local (ofString "tx"),
                      .const 208]),
                      .panop .mul [.var .local (ofString "i"), .const 24]])
                    (.seq
                      (.store (.op .add [.var .local (ofString "al_addrs"),
                        .panop .mul [.op .add [.var .local (ofString "i"), .const 1],
                          .const 8]])
                        (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
                      (.seq
                        (.assign .local (ofString "nkeys")
                          (.op .add [.var .local (ofString "nkeys"),
                            .load .one (.op .add [.var .local (ofString "acc"),
                              .const 16])]))
                        (.assign .local (ofString "i")
                          (.op .add [.var .local (ofString "i"), .const 1]))))))
                tail)))) := by
    simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
      spineAt, spinePlug]
    rfl
  rw [he]
  apply TerminatingProgBoundedOn.decCall_on
    (Q := fun s => PtxAddressJoint s ∧ PtxPhase2X s) h.fb_alloc
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1.1.1
  · exact ptxPhase2B_alAddrs_X_resume h
  · intro F s hc hp
    have hs0 : TerminatingProgBoundedOn (fun s => PtxAddressJoint s ∧ PtxPhase2X s)
        (.store (.var .local (ofString "al_addrs"))
          (.load .one (.op .add [.var .global (ofString "be"), .const 32]))) 0 := by
      intro F s hc hp hn
      rw [clock_store]
      exact ⟨by omega, le_rfl⟩
    have hrest : TerminatingProgBoundedOn (fun s => PtxAddressJoint s ∧ PtxPhase2X s)
        (.dec (ofString "nkeys") .one (.const 0)
          (.dec (ofString "i") .one (.const 0)
            (.seq
              (.while (.cmp .less (.var .local (ofString "i"))
                (.var .local (ofString "nal")))
                (.dec (ofString "acc") .one
                  (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
                    .panop .mul [.var .local (ofString "i"), .const 24]])
                  (.seq
                    (.store (.op .add [.var .local (ofString "al_addrs"),
                      .panop .mul [.op .add [.var .local (ofString "i"), .const 1],
                        .const 8]])
                      (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
                    (.seq
                      (.assign .local (ofString "nkeys")
                        (.op .add [.var .local (ofString "nkeys"),
                          .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
                      (.assign .local (ofString "i")
                        (.op .add [.var .local (ofString "i"), .const 1]))))))
              tail))) ((2 ^ 63 + 1) + b) := by
      apply dec_bound_trans (Q := fun s => ∃ before, (PtxAddressJoint before ∧
        PtxPhase2X before) ∧ s = setVarHOLFinite (ofString "nkeys") (.val (.word 0)) before)
      · intro F s v hp hev
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hev.symm
        subst v
        exact ⟨s, hp, rfl⟩
      · apply dec_bound_trans (Q := fun s => PtxAddressCountCases s ∧ PtxPhase2X s)
        · intro F s v hp hev
          have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hev.symm
          subst v
          obtain ⟨before, ⟨hj, hx⟩, rfl⟩ := hp
          exact ⟨phase2_address_count_cases_init before hj,
            ptxPhase2X_setVar_i _ _ (ptxPhase2X_setVar_nkeys before _ hx)⟩
        · intro F s hc hp
          have hwl : TerminatingProgBoundedOn PtxAddressCountCases
              (.while (.cmp .less (.var .local (ofString "i"))
                (.var .local (ofString "nal")))
                (.dec (ofString "acc") .one
                  (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
                    .panop .mul [.var .local (ofString "i"), .const 24]])
                  (.seq
                    (.store (.op .add [.var .local (ofString "al_addrs"),
                      .panop .mul [.op .add [.var .local (ofString "i"), .const 1],
                        .const 8]])
                      (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
                    (.seq
                      (.assign .local (ofString "nkeys")
                        (.op .add [.var .local (ofString "nkeys"),
                          .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
                      (.assign .local (ofString "i")
                        (.op .add [.var .local (ofString "i"), .const 1])))))) (2 ^ 63 + 1) :=
            phase2_count_cases_while_bound phase2_address_count_loop_bound
          exact seq_bound_trans (fun t hct hpt => hwl t hct hpt.1)
            ptxPhase2B_countCases_whileX_hoare ht s hc hp
    simpa only [Nat.zero_add] using seq_bound_trans hs0 ptxPhase2B_beneficiaryX_hoare hrest s hc hp

/-! ## Section 5: packed keys allocation and packing loop (guest spine 49..52) -/

/-- Locals that the packing-region frame keeps in sync: the two buffer
parameters plus every local read by the auxiliary conjunct. -/
def ptxPhase2BXNames : List String := ["al_keys", "nkeys"] ++ ptxPhase2XNames

/-- The glue conjunct threaded through the packing region: the auxiliary
conjunct plus the block-out record's nonzero base and its separation from the
packed access-list buffer. -/
def ptxPhase2BX {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPhase2X s ∧ globN s "bo" ≠ 0 ∧
    Disj (globN s "bo", 88)
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)

theorem ptxPhase2BX_mem_al_keys {n : String} (hn : n ∈ ptxPhase2BXNames) :
    n ∈ ptxPhase2BXNames := hn

/-- The glue conjunct transfers along a locals substitution. -/
theorem ptxPhase2BX_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ n ∈ ptxPhase2BXNames, locals.lookup (ofString n) =
      s.locals.lookup (ofString n))
    (hp : ptxPhase2BX s) :
    ptxPhase2BX {s with locals := locals, clock := clock} := by
  refine ⟨ptxPhase2X_with_locals s locals clock (fun n hn => hl n (by
      simp only [ptxPhase2BXNames, List.mem_append]; exact Or.inr hn)) hp.1, ?_, ?_⟩
  · exact hp.2.1
  · have halk : locN {s with locals := locals, clock := clock} "al_keys" =
        locN s "al_keys" :=
      locN_congr s locals clock "al_keys" (hl "al_keys" (by simp [ptxPhase2BXNames]))
    have hnk : locN {s with locals := locals, clock := clock} "nkeys" =
        locN s "nkeys" :=
      locN_congr s locals clock "nkeys" (hl "nkeys" (by simp [ptxPhase2BXNames]))
    rw [halk, hnk]
    exact hp.2.2

/-- The glue conjunct survives a clock decrement. -/
theorem ptxPhase2BX_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : ptxPhase2BX s) : ptxPhase2BX (decClockHOLFinite s) :=
  ptxPhase2BX_with_locals s (decClockHOLFinite s).locals (s.clock - 1) (by intros; rfl) hp

/-- The glue conjunct survives a local assignment it does not mention. -/
theorem ptxPhase2BX_setVar_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (name : MlS)
    (hne : ∀ n ∈ ptxPhase2BXNames, ofString n ≠ name) (hp : ptxPhase2BX s) :
    ptxPhase2BX (setVarHOLFinite name v s) := by
  refine ⟨ptxPhase2X_setVar_other s v (fun n hn => hne n (by
      simp only [ptxPhase2BXNames, List.mem_append]; exact Or.inr hn)) hp.1, hp.2.1, ?_⟩
  have halk : locN (setVarHOLFinite name v s) "al_keys" = locN s "al_keys" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show name ≠ ofString "al_keys" from (hne "al_keys"
        (by simp [ptxPhase2BXNames])).symm]
  have hnk : locN (setVarHOLFinite name v s) "nkeys" = locN s "nkeys" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show name ≠ ofString "nkeys" from (hne "nkeys"
        (by simp [ptxPhase2BXNames])).symm]
  rw [halk, hnk]
  exact hp.2.2

/-- Two postconditions of the same hoare proof can be paired. -/
theorem ptxPhase2B_hoare_pair {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q1 Q2 : ∀ {F : Type}, Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {prog : ProgHOL 64}
    (h1 : Hoare P prog Q1) (h2 : Hoare P prog Q2) :
    Hoare P prog (fun r s => Q1 r s ∧ Q2 r s) :=
  ⟨fun s hc hp hnt => ⟨h1.run s hc hp hnt, h2.run s hc hp hnt⟩⟩

/-- A hoare postcondition can be weakened. -/
theorem ptxPhase2B_hoare_post {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q Q' : ∀ {F : Type}, Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {prog : ProgHOL 64}
    (h : Hoare P prog Q) (hQ : ∀ {F : Type} (r : Option (PanSemResultExact 64))
      (s : PanSemStateFiniteExact 64 F), Q r s → Q' r s) :
    Hoare P prog Q' :=
  ⟨fun s hc hp hnt => hQ _ _ (h.run s hc hp hnt)⟩

/-- A generic local assignment preserves the glue conjunct. -/
theorem ptxPhase2BX_assign_hoare {name : MlS} {source : ExpHOL 64}
    (hne : ∀ n ∈ ptxPhase2BXNames, ofString n ≠ name) :
    Hoare ptxPhase2BX (.assign .local name source)
      (fun r s => r = none → ptxPhase2BX s) := by
  apply Hoare.assign
  · intro F s v hp _
    exact fun _ => ptxPhase2BX_setVar_other s v name hne hp
  · exact fun _ _ hr => by cases hr

/-! ### Fine-frame word preservation for the packing copies -/

/-- A word cell inside a region allocated at `s` (heap or scratch side) is
preserved by a `FrameOutside` frame whose keep-set misses it: the region lies
below the old heap top or above the scratch start, so the fresh gap never
covers the cell. -/
theorem ptxPhase2BX_frame_word {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {K : List Ivl}
    (hAO : ArenaOK s)
    (hhp' : globN post "heap_ptr" ≤ heapLimit)
    (hfr : FrameOutside s post K
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    {i : Ivl} (hai : Allocated s i) {a : Nat}
    (hkeep : ∀ j ∈ K, ¬ CellHits a j)
    (hin : Inside (a, 8) i.1 (i.1 + i.2)) :
    memW post a = memW s a := by
  have hhl : heapLimit = 2952790016 := rfl
  have hss : InitE.scratchStart = 2952790016 := rfl
  have hsep : heapLimit ≤ InitE.scratchStart := by decide
  have hsb : InitE.sourceBase ≤ globN s "heap_ptr" := hAO.1
  have hhp : globN s "heap_ptr" ≤ heapLimit := hAO.2.1
  have hsc : InitE.scratchStart ≤ globN s "scratch_ptr" :=
    Nat.le_trans hAO.2.2.1 hAO.2.2.2.1
  have hi2 : i.1 + i.2 ≤ 2 ^ 64 := (ivl_allocated_bound hAO hai).2
  obtain ⟨hin1, hin2⟩ := hin
  have ha_lt : a < 2 ^ 64 := by omega
  have haddr : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hm : post.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a) := by
    refine hfr _ (fun j hj hci => ?_) (fun hcf => ?_)
    · rw [haddr] at hci; exact hkeep j hj hci
    · rw [haddr] at hcf
      unfold CellHits at hcf
      rcases hai with hheap | hscr
      · obtain ⟨he1, he2⟩ := hheap; omega
      · obtain ⟨hs1, hs2⟩ := hscr; omega
  unfold memW
  rw [hm]

/-- The glue conjunct is preserved by a packed copy whose only memory writes
hit the copied interval inside the packed buffer: the block-out record and the
two list headers are allocated regions separated from that interval, so their
cells are untouched, and the copy keeps every global. -/
theorem ptxPhase2BX_copy_preserved {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dst len : Nat}
    (hp : ptxPhase2BX s) (hnc : PtxPackedNsNalCopy s)
    (hloc : post.locals = s.locals)
    (hgl : post.globals = s.globals)
    (hcell : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      ∃ i ∈ [(dst, len)], R13Shards.Keccak256.CellHitsPos a.toNat i)
    (hdst : Inside (dst, len) (locN s "al_keys")
      (locN s "al_keys" + (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)) :
    ptxPhase2BX post := by
  obtain ⟨hX, hbo_nz, hdisj⟩ := hp
  have hs := hnc.1
  have hci : PtxPackedCopyIndex s := hs.1.2.1.1
  obtain ⟨S, Nd, hWT, hT, hIvls⟩ := hci.1.2.2.2.2
  have hA : ArenaReady s := hs.1.1.1
  have hAO : ArenaOK s := hA.2
  have hF : FixedTyped s := hWT.2.2.1
  have hbo_al := bo_words hF hbo_nz
  have htb : TxBacking s := hX.2.1
  have hlst : ∀ k ∈ ([40, 72] : List Nat),
      (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [fixedObjects, blockOutObjects, hbo_nz, hX.2.2.1.bo40]
    · simp [fixedObjects, blockOutObjects, hbo_nz, hX.2.2.1.bo72]
  have hown : ∀ k ∈ ([40, 72] : List Nat),
      (memW s (globN s "bo" + k), 24) ∈ worldOwned s S Nd := by
    intro k hk
    have h1 := hlst k hk
    simp only [worldOwned, List.mem_append, List.not_mem_nil, or_false]
    exact Or.inl (Or.inr h1)
  -- the copied interval misses the block-out record cells and both headers
  have hmiss_bo : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      ¬ CellHits (globN s "bo" + k) (dst, len) := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    obtain ⟨hd1, hd2⟩ := hdst
    unfold CellHits
    rcases hdisj with h | h
    · rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    · rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
  have hmiss_hd : ∀ k ∈ ([40, 72] : List Nat),
      ¬ CellHits (memW s (globN s "bo" + k)) (dst, len) := by
    intro k hk
    have hmem : (memW s (globN s "bo" + k), 24) ∈ worldOwned s S Nd := hown k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    obtain ⟨hd1, hd2⟩ := hdst
    unfold CellHits
    rcases hIvls (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)
      (by simp) (memW s (globN s "bo" + k), 24) hmem with h | h
    · rcases hk with rfl | rfl <;> omega
    · rcases hk with rfl | rfl <;> omega
  -- the frame
  have hfr : FrameOutside s post [(dst, len)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a hkeep _
    by_contra hm
    obtain ⟨i, hi, hpos⟩ := hcell a hm
    exact hkeep i hi hpos.2
  have hbo' : globN post "bo" = globN s "bo" := by unfold globN; rw [hgl]
  have hjc' : globN post "journal_cap" = globN s "journal_cap" := by
    unfold globN; rw [hgl]
  have hhp' : globN post "heap_ptr" ≤ heapLimit := by
    rw [show globN post "heap_ptr" = globN s "heap_ptr" from by
      unfold globN; rw [hgl]]
    exact hAO.2.1
  -- preserved cells
  have hcells : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      exact ptxPhase2BX_frame_word hAO hhp' hfr hbo_al.1
        (fun j hj hci => by
          simp only [List.mem_singleton] at hj
          subst hj
          exact hmiss_bo _ (by simp) hci)
        ⟨by omega, by omega⟩
  have hhd : ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) := by
    intro k hk
    rcases hF.1 _ (hlst k hk) with h0 | ⟨hal, hwd⟩
    · simp at h0
    · refine ptxPhase2BX_frame_word hAO hhp' hfr hal ?_ ?_
      · intro j hj hci
        simp only [List.mem_singleton] at hj
        subst hj
        exact hmiss_hd k hk hci
      · exact ⟨Nat.le_refl _, by omega⟩
  -- TxBacking
  have htb' : TxBacking post := by
    refine ⟨?_, ?_⟩
    · rw [hbo', hcells 40 (by simp), hhd 40 (by simp)]; exact htb.1
    · rw [hbo', hcells 72 (by simp), hhd 72 (by simp)]; exact htb.2
  have hidx : locN post "index" = locN s "index" := by unfold locN; rw [hloc]
  refine ⟨ptxPhase2X_of_cells hX htb' hloc hbo' hjc' hidx hcells, ?_, ?_⟩
  · rw [hbo']; exact hbo_nz
  · rw [hbo']
    rw [show locN post "al_keys" = locN s "al_keys" from by unfold locN; rw [hloc],
        show locN post "nkeys" = locN s "nkeys" from by unfold locN; rw [hloc]]
    exact hdisj

/-! ### The two packed copies keep the backing conjunct -/

/-- A three-element evaluated argument list splits into its values. -/
theorem ptxPhase2B_evalList_three {F : Type} (s : PanSemStateFiniteExact 64 F)
    {e1 e2 e3 : ExpHOL 64} {values : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [e1, e2, e3] = some values) :
    ∃ v1 v2 v3, values = [v1, v2, v3] ∧ evalAt s e1 = some v1 ∧
      evalAt s e2 = some v2 ∧ evalAt s e3 = some v3 := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp only [evalListHOLExact] at h
  revert h
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1
    with _ | v1
  · simp
  · rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2
      with _ | v2
    · simp
    · rcases h3 : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
      · simp
      · simp only [Option.some.injEq]
        intro h
        exact ⟨v1, v2, v3, h.symm, h1, h2, h3⟩

/-- The first packed copy keeps the backing conjunct. -/
theorem ptxPhase2BX_packed_address_copy_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → ptxPhase2BX t ∧ PtxPackedNsNalCopy t) := by
  have hfrozen : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → PtxPackedNsNalCopy t) :=
    Hoare.mono (P := fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (P' := PtxPackedNsNalCopy) (phase2_packed_address_copy_ns_nal_hoare h src)
      (fun _ hs => hs.2)
  have hbx : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
    (.call (some (none, none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "al_keys"),
        .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
    (fun r t => r = none → ptxPhase2BX t) := by
    refine ⟨fun {F} s hc hp hnt hr => ?_⟩
    have hnt0 := hnt
    have hs : PtxPackedNsCopy s := hp.2.1
    have hAR : ArenaReady s := hs.1.1.1
    have hG : GuestInv s := hAR.1
    have hci : PtxPackedCopyIndex s := hs.1.2.1.1
    obtain ⟨base, hbase⟩ := hs.1.2.1.1.1.1
    obtain ⟨kk, hkk⟩ := hs.1.2.2.1
    have hbound := hs.1.2.2.2
    have hdst := (phase2_packed_copy_index_destinations hci).1
    have hdsteq : (base + kk * 52).toNat = locN s "al_keys" + 52 * locN s "k" :=
      phase2_packed_destination_toNat s hci base kk hbase hkk hbound
    have hd : evalAt s (.op .add [.var .local (ofString "al_keys"),
        .panop .mul [.var .local (ofString "k"), .const 52]]) =
        some (.val (.word (base + kk * 52))) :=
      phase2_packed_destination_eval s base kk hbase hkk
    have hlen : evalAt s (.const 20) = some (.val (.word (20 : BitVec 64))) := by
      simp [evalAt, evalHOLExact]
    rw [evaluateHOLFiniteState_call] at hr
    rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20] with _ | vs
    · rw [ha] at hr; simp at hr
    · simp only [ha] at hr
      rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs with
        _ | ⟨body, callee, ret⟩
      · simp [hl] at hr
      · simp only [hl] at hr
        by_cases hz : s.clock = 0
        · simp [hz] at hr
        · simp only [hz, ↓reduceIte] at hr
          rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
            ⟨res, post⟩
          simp only [hb] at hr
          cases res with
          | none => simp at hr
          | some r =>
            cases r with
            | returned v =>
              dsimp only at hr
              split at hr
              · rename_i hsh
                have hpost_eq : (evaluateHOLFiniteState s
                    (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])).2 =
                    {post with locals := s.locals} := by
                  rw [evaluateHOLFiniteState_call]
                  simp only [ha]
                  simp only [hl]
                  simp only [hz, ↓reduceIte]
                  rw [hb]; dsimp only; rw [if_pos hsh]
                have hor : (evaluateHOLFiniteState s
                    (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])).1 = none ∨
                    Resumes (evaluateHOLFiniteState s
                      (.call (some (none, none)) (ofString "memcpy")
                        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])).1 := by
                  rw [evaluateHOLFiniteState_call]
                  simp only [ha]
                  simp only [hl]
                  simp only [hz, ↓reduceIte]
                  rw [hb]; dsimp only; rw [if_pos hsh]
                  exact Or.inl rfl
                obtain ⟨v1, v2, v3, hvs, hv1, hv2, hv3⟩ := ptxPhase2B_evalList_three s ha
                subst hvs
                have hv1' : v1 = .val (.word (base + kk * 52)) :=
                  Option.some.inj (by rw [← hv1]; exact hd)
                subst hv1'
                have hv3' : v3 = .val (.word (20 : BitVec 64)) :=
                  Option.some.inj (by rw [← hv3]; exact hlen)
                subst hv3'
                obtain ⟨-, -, -, -, -, hgl, -, -, hcell, -⟩ :=
                  R13Shards.Keccak256.call0_byteEff R13Shards.Keccak256.funByteEff_memcpy s
                    [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20]
                    [((base + kk * 52).toNat, 20)] hc hG
                    (fun vals hvs' i hi _ => by
                      rw [ha] at hvs'
                      injection hvs' with hvs'
                      subst hvs'
                      exact ⟨i, hi, Nat.le_refl _, Nat.le_refl _⟩)
                    hnt0 hor
                rw [hpost_eq] at hgl hcell
                rw [← hdsteq] at hdst
                rw [hpost_eq]
                exact ptxPhase2BX_copy_preserved hp.1 hp.2 rfl hgl hcell hdst
              · simp at hr
            | _ => simp at hr

  exact ptxPhase2B_hoare_post (ptxPhase2B_hoare_pair hbx hfrozen)
    (fun r t hpair hr => ⟨hpair.1 hr, hpair.2 hr⟩)

/-- The second packed copy keeps the backing conjunct. -/
theorem ptxPhase2BX_packed_storage_copy_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → ptxPhase2BX t ∧ PtxPackedNsNalCopy t) := by
  have hfrozen : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → PtxPackedNsNalCopy t) :=
    Hoare.mono (P := fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (P' := PtxPackedNsNalCopy) (phase2_packed_storage_copy_ns_nal_hoare h src)
      (fun _ hs => hs.2)
  have hbx : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
    (.call (some (none, none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "al_keys"),
        .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
    (fun r t => r = none → ptxPhase2BX t) := by
    refine ⟨fun {F} s hc hp hnt hr => ?_⟩
    have hnt0 := hnt
    have hs : PtxPackedNsCopy s := hp.2.1
    have hAR : ArenaReady s := hs.1.1.1
    have hG : GuestInv s := hAR.1
    have hci : PtxPackedCopyIndex s := hs.1.2.1.1
    obtain ⟨base, hbase⟩ := hs.1.2.1.1.1.1
    obtain ⟨kk, hkk⟩ := hs.1.2.2.1
    have hbound := hs.1.2.2.2
    have hdst := (phase2_packed_copy_index_destinations hci).2
    have hdsteq : (base + kk * 52 + 20).toNat = locN s "al_keys" + 52 * locN s "k" + 20 :=
      phase2_packed_key_destination_toNat s hci base kk hbase hkk hbound
    have hd : evalAt s (.op .add [.var .local (ofString "al_keys"),
        .panop .mul [.var .local (ofString "k"), .const 52], .const 20]) =
        some (.val (.word (base + kk * 52 + 20))) :=
      phase2_packed_key_destination_eval s base kk hbase hkk
    have hlen : evalAt s (.const 32) = some (.val (.word (32 : BitVec 64))) := by
      simp [evalAt, evalHOLExact]
    rw [evaluateHOLFiniteState_call] at hr
    rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32] with _ | vs
    · rw [ha] at hr; simp at hr
    · simp only [ha] at hr
      rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs with
        _ | ⟨body, callee, ret⟩
      · simp [hl] at hr
      · simp only [hl] at hr
        by_cases hz : s.clock = 0
        · simp [hz] at hr
        · simp only [hz, ↓reduceIte] at hr
          rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
            ⟨res, post⟩
          simp only [hb] at hr
          cases res with
          | none => simp at hr
          | some r =>
            cases r with
            | returned v =>
              dsimp only at hr
              split at hr
              · rename_i hsh
                have hpost_eq : (evaluateHOLFiniteState s
                    (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])).2 =
                    {post with locals := s.locals} := by
                  rw [evaluateHOLFiniteState_call]
                  simp only [ha]
                  simp only [hl]
                  simp only [hz, ↓reduceIte]
                  rw [hb]; dsimp only; rw [if_pos hsh]
                have hor : (evaluateHOLFiniteState s
                    (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])).1 = none ∨
                    Resumes (evaluateHOLFiniteState s
                      (.call (some (none, none)) (ofString "memcpy")
                        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])).1 := by
                  rw [evaluateHOLFiniteState_call]
                  simp only [ha]
                  simp only [hl]
                  simp only [hz, ↓reduceIte]
                  rw [hb]; dsimp only; rw [if_pos hsh]
                  exact Or.inl rfl
                obtain ⟨v1, v2, v3, hvs, hv1, hv2, hv3⟩ := ptxPhase2B_evalList_three s ha
                subst hvs
                have hv1' : v1 = .val (.word (base + kk * 52 + 20)) :=
                  Option.some.inj (by rw [← hv1]; exact hd)
                subst hv1'
                have hv3' : v3 = .val (.word (32 : BitVec 64)) :=
                  Option.some.inj (by rw [← hv3]; exact hlen)
                subst hv3'
                obtain ⟨-, -, -, -, -, hgl, -, -, hcell, -⟩ :=
                  R13Shards.Keccak256.call0_byteEff R13Shards.Keccak256.funByteEff_memcpy s
                    [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32]
                    [((base + kk * 52 + 20).toNat, 32)] hc hG
                    (fun vals hvs' i hi _ => by
                      rw [ha] at hvs'
                      injection hvs' with hvs'
                      subst hvs'
                      exact ⟨i, hi, Nat.le_refl _, Nat.le_refl _⟩)
                    hnt0 hor
                rw [hpost_eq] at hgl hcell
                rw [← hdsteq] at hdst
                rw [hpost_eq]
                exact ptxPhase2BX_copy_preserved hp.1 hp.2 rfl hgl hcell hdst
              · simp at hr
            | _ => simp at hr

  exact ptxPhase2B_hoare_post (ptxPhase2B_hoare_pair hbx hfrozen)
    (fun r t hpair hr => ⟨hpair.1 hr, hpair.2 hr⟩)

/-! ### The packed copies plus the counter updates -/

/-- Neither packing counter local is read by the glue conjunct, so the
counter pair preserves it. -/
theorem ptxPhase2BX_setVar_counters {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v v' : ValueHOL 64) (hp : ptxPhase2BX s) :
    ptxPhase2BX (setVarHOLFinite (ofString "j") v
      (setVarHOLFinite (ofString "k") v' s)) := by
  have hbxk : ptxPhase2BX (setVarHOLFinite (ofString "k") v' s) :=
    ptxPhase2BX_setVar_other s _ (ofString "k") (by
      intro n hn
      simp [ptxPhase2BXNames, ptxPhase2XNames] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hp
  exact ptxPhase2BX_setVar_other _ _ (ofString "j") (by
      intro n hn
      simp [ptxPhase2BXNames, ptxPhase2XNames] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hbxk

/-- Counter updates preserve the glue conjunct and both cached bounds. -/
theorem ptxPhase2B_countersBX_hoare :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNsNalIteration s) := by
  apply Hoare.seq_fall (R := fun s => ∃ before, ptxPhase2BX before ∧
    PtxPackedNsNalCopy before ∧
    s = setVarHOLFinite (ofString "k")
      (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before)
  · apply Hoare.assign
    · intro F s v hp he
      have hb := (phase2_packed_copy_counter_bounds hp.2.1.1.2.1.1).1
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "k" v hb he
      have heq : w = BitVec.ofNat 64 (locN s "k" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => ⟨s, hp.1, hp.2, rfl⟩
    · exact fun _ _ hr => by cases hr
  · apply Hoare.assign
    · intro F s v hp he
      obtain ⟨before, hbx, hnc, rfl⟩ := hp
      have hj : locN (setVarHOLFinite (ofString "k")
          (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before) "j" =
          locN before "j" := by
        simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          show ofString "k" ≠ ofString "j" by decide]
      have hb := (phase2_packed_copy_counter_bounds hnc.1.1.2.1.1).2
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval _ "j" v (by rw [hj]; exact hb) he
      have heq : w = BitVec.ofNat 64 (locN before "j" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => ⟨ptxPhase2BX_setVar_counters before _ _ hbx,
        ⟨⟨phase2_packed_counters_iteration_state before hnc.1.1.1 hnc.1.1.2.1
          hnc.1.1.2.2.2, phase2_packed_ns_counters before hnc.1 _ _⟩,
        phase2_packed_nal_counters before hnc _ _⟩⟩
    · exact fun _ _ hr => by cases hr

/-- Both copies and both counters preserve the glue conjunct together with
the actual source-loop invariant. -/
theorem ptxPhase2B_bodyBX_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNsNalIteration s) := by
  exact Hoare.seq_fall (ptxPhase2BX_packed_address_copy_hoare h addressSrc)
    (Hoare.seq_fall (ptxPhase2BX_packed_storage_copy_hoare h keySrc)
      ptxPhase2B_countersBX_hoare)

/-! ### The inner packing loop -/

/-- Clock induction for the source guard `j < ns`, carrying the glue
conjunct alongside the cached-count invariant. -/
theorem ptxPhase2B_innerWhileBX_hoare {body : ProgHOL 64}
    (hb : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s) body
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNsNalIteration s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s)
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))) body)
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1)) := by
  let guard : ExpHOL 64 := .cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → ptxPhase2BX st ∧ PtxPackedNsNalIteration st →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      ptxPhase2BX post ∧ PtxPackedNsNalIteration post ∧
        locN post "k" = phase2_key_prefix post (locN post "i" + 1) from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := phase2_packed_ns_guard_eval st w hp.2.1
        (by simpa [evalAt, guard] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hdBX := ptxPhase2BX_decClock st hp.1
          have hd := phase2_packed_ns_iteration_decClock st hp.2.1
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb
            (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc
            (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc
              ⟨hdBX, ⟨⟨phase2_packed_iteration_guard_pre _ hd.1 (hguard.mp hnz), hd.2⟩,
                hp.2.2⟩⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp.1, hp.2, (phase2_packed_separated_inner_exit hp.2.1.1.2.1
          (fun hlt => hz (hguard.mpr hlt))).1⟩
    · simp at he

/-! ### The record increment and the outer body -/

/-- The outer increment retains the glue conjunct and the cached record bound. -/
theorem ptxPhase2B_outerIncrementBX_hoare :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
      locN s "k" = phase2_key_prefix s (locN s "i" + 1))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s) := by
  apply Hoare.assign
  · intro F s v hp he
    have hbx := hp.1
    have hiter := hp.2.1
    have hkpre := hp.2.2
    have hb := phase2_packed_outer_successor_bound hiter.1.1.2.1.1
    obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "i" v hb he
    have heq : w = BitVec.ofNat 64 (locN s "i" + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    subst w
    refine fun _ => ⟨ptxPhase2BX_setVar_other s _ (ofString "i") (by
      intro n hn
      simp [ptxPhase2BXNames, ptxPhase2XNames] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hbx,
      ⟨phase2_packed_ns_outer_advance s hiter.1 hkpre, ?_⟩⟩
    simpa [locN, memW, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nal" by decide,
      show ofString "i" ≠ ofString "tx" by decide] using hiter.2
  · exact fun _ _ hr => by cases hr

/-- The concrete inner loop and record increment retain the glue conjunct
together with the outer cached bound. -/
theorem ptxPhase2B_innerTailBX_hoare (h : PtxCallees) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s) phase2_packed_source_inner_tail
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s) := by
  exact Hoare.seq_fall
    (ptxPhase2B_innerWhileBX_hoare (ptxPhase2B_bodyBX_hoare h _ _) rfl rfl)
    ptxPhase2B_outerIncrementBX_hoare

/-- Locals the packing-region declarations must preserve in their frame. -/
def ptxPhase2BDecNames : List String := ptxPhase2BXNames ++ ["i", "k", "nal"]

theorem ptxPhase2BXNames_sub_DecNames {n : String} (hn : n ∈ ptxPhase2BXNames) :
    n ∈ ptxPhase2BDecNames := by
  simp only [ptxPhase2BDecNames, List.mem_append]
  exact Or.inl hn

theorem nalNames_sub_DecNames {n : String}
    (hn : n ∈ (["al_keys", "nkeys", "tx", "i", "k", "nal"] : List String)) :
    n ∈ ptxPhase2BDecNames := by
  simp at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ptxPhase2BDecNames, ptxPhase2BXNames, ptxPhase2XNames]

theorem ptxPhase2BDecNames_ne (name : MlS)
    (hne : name = ofString "acc2" ∨ name = ofString "ns" ∨ name = ofString "j") :
    ∀ n ∈ ptxPhase2BDecNames, ofString n ≠ name := by
  intro n hn h'
  simp [ptxPhase2BDecNames, ptxPhase2BXNames, ptxPhase2XNames] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hne with rfl | rfl | rfl <;> exact absurd h' (by decide)

/-- None of the packing-region scratch locals is read by the glue conjunct. -/
theorem ptxPhase2BX_setVar_scratch {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (name : MlS) (hp : ptxPhase2BX s)
    (hne : name = ofString "k" ∨ name = ofString "j" ∨ name = ofString "i" ∨
      name = ofString "acc2" ∨ name = ofString "ns") :
    ptxPhase2BX (setVarHOLFinite name v s) := by
  refine ptxPhase2BX_setVar_other s v name ?_ hp
  intro n hn h'
  simp [ptxPhase2BXNames, ptxPhase2XNames] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hne with rfl | rfl | rfl | rfl | rfl <;> exact absurd h' (by decide)

/-- The actual nested declarations and copy loop preserve the glue conjunct
together with the source outer-loop invariant. -/
theorem ptxPhase2B_outerBodyBX_hoare (h : PtxCallees) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216)) phase2_packed_source_outer_body
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s) := by
  unfold phase2_packed_source_outer_body
  apply Hoare.dec (names := ptxPhase2BDecNames)
    (P' := fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216) ∧
      locN s "acc2" = memW s (locN s "tx" + 208) + 24 * locN s "i")
    (ptxPhase2BDecNames_ne (ofString "acc2") (Or.inl rfl))
  · intro F s v hp he
    have hd := phase2_packed_outer_declare_acc2 s hp.2.1.1 hp.2.2 v he
    exact ⟨ptxPhase2BX_setVar_scratch s v (ofString "acc2") hp.1
          (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      phase2_packed_nal_set_other s hp.2.1 _ _ (by decide), hd.2⟩
  · apply Hoare.dec (names := ptxPhase2BDecNames)
      (P' := fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
        locN s "i" < memW s (locN s "tx" + 216) ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
        locN s "ns" = memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16))
      (ptxPhase2BDecNames_ne (ofString "ns") (Or.inr (Or.inl rfl)))
    · intro F s v hp he
      have hd := phase2_packed_outer_declare_ns s hp.2.1.1 hp.2.2.1 hp.2.2.2 v he
      exact ⟨ptxPhase2BX_setVar_scratch s v (ofString "ns") hp.1
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
        phase2_packed_nal_set_other s hp.2.1 _ _ (by decide), hd.2⟩
    · apply Hoare.dec (names := ptxPhase2BDecNames)
        (P' := fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s)
        (ptxPhase2BDecNames_ne (ofString "j") (Or.inr (Or.inr rfl)))
      · intro F s v hp he
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        refine ⟨ptxPhase2BX_setVar_scratch s (.val (.word 0)) (ofString "j") hp.1
            (Or.inr (Or.inl rfl)),
          ⟨phase2_packed_ns_reset s hp.2.1.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2, ?_⟩⟩
        exact (phase2_packed_nal_set_other s hp.2.1 (ofString "j") (.val (.word 0))
          (by decide)).2
      · exact ptxPhase2B_innerTailBX_hoare h
      · intro F r s locals hl hp hr
        exact ⟨ptxPhase2BX_with_locals s locals s.clock
            (fun n hn => hl n (ptxPhase2BXNames_sub_DecNames hn)) (hp hr).1,
          phase2_packed_nal_iteration_with_locals s locals s.clock (hp hr).2
            (fun n hn => hl n (nalNames_sub_DecNames hn))⟩
      · exact fun _ _ hr => by cases hr
    · intro F r s locals hl hp hr
      exact ⟨ptxPhase2BX_with_locals s locals s.clock
          (fun n hn => hl n (ptxPhase2BXNames_sub_DecNames hn)) (hp hr).1,
        phase2_packed_nal_iteration_with_locals s locals s.clock (hp hr).2
          (fun n hn => hl n (nalNames_sub_DecNames hn))⟩
    · exact fun _ _ hr => by cases hr
  · intro F r s locals hl hp hr
    exact ⟨ptxPhase2BX_with_locals s locals s.clock
        (fun n hn => hl n (ptxPhase2BXNames_sub_DecNames hn)) (hp hr).1,
      phase2_packed_nal_iteration_with_locals s locals s.clock (hp hr).2
        (fun n hn => hl n (nalNames_sub_DecNames hn))⟩
  · exact fun _ _ hr => by cases hr


/-! ### The outer packing loop -/

/-- The outer packing loop over `nal` retains the glue conjunct and finishes
with the cached count equal to the packed record count. -/
theorem ptxPhase2B_nalWhileBX_hoare {body : ProgHOL 64}
    (hb : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216)) body
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body)
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
        locN s "k" = locN s "nkeys") := by
  let guard : ExpHOL 64 := .cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))
  change Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s) (.while guard body) _
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → ptxPhase2BX st ∧ PtxPackedNalIteration st →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      ptxPhase2BX post ∧ PtxPackedNalIteration post ∧ locN post "k" = locN post "nkeys" from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := phase2_packed_outer_nal_guard st w hp.2.1 hp.2.2.1 hp.2.2.2
        (by simpa [evalAt, guard] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd := phase2_packed_nal_iteration_decClock st hp.2
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb
            (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc
            (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc
              ⟨ptxPhase2BX_decClock st hp.1, ⟨hd, hguard.mp hnz⟩⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp.1, hp.2, (phase2_packed_outer_exit hp.2.1.2.1
          (fun hlt => hz (hguard.mpr hlt))).2⟩
    · simp at he

/-- The concrete outer packing loop completes all records while retaining the
glue conjunct. -/
theorem ptxPhase2B_outerWhileBX_hoare (h : PtxCallees) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        phase2_packed_source_outer_body)
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
        locN s "k" = locN s "nkeys") :=
  ptxPhase2B_nalWhileBX_hoare (ptxPhase2B_outerBodyBX_hoare h) rfl rfl

end InitECandidate.Solver.Wave8GuestInv.R13Shards
