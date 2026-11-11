import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4B

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase (stdKeep)
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-! # Phase 4C: store engines and instruction steps

The phase-4 body writes only three kinds of cells: untyped `bo` words
(insts 16-19), `bo`-array slots (insts 26/27, the inst-31 loop, inst 40) and
fresh stable-log cells (insts 35, 38). This file provides the corresponding
`P4Data` step engines, built on the `WorldStep` assembly of `Phase4B`. -/

/-! ## The transaction environment at every phase-4 intermediate state -/

/-- Every phase-4 intermediate state satisfies `TxEnv`: the `bo` fields and
`journal_cap` are kept from the entry by `PtxRelBase`, and `index` is kept by
`P4Data.idx_local`. -/
theorem txEnv_of_p4Data {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out) : TxEnv s := by
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, hjcap_e, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
  have hbo24 := ptx_entry_bo_field_eq (off := 24) hWT_e h.base.globals h.base.records hbo_nz_e (by simp) (by omega)
  have hbo32 := ptx_entry_bo_field_eq (off := 32) hWT_e h.base.globals h.base.records hbo_nz_e (by simp) (by omega)
  have hbo40 := ptx_entry_bo_field_eq (off := 40) hWT_e h.base.globals h.base.records hbo_nz_e (by simp) (by omega)
  have hbo72 := ptx_entry_bo_field_eq (off := 72) hWT_e h.base.globals h.base.records hbo_nz_e (by simp) (by omega)
  have hbo80 := ptx_entry_bo_field_eq (off := 80) hWT_e h.base.globals h.base.records hbo_nz_e (by simp) (by omega)
  have hbo_s : globN s "bo" = globN entry "bo" :=
    globN_eq_of_lookup (h.base.globals (ofString "bo") (by decide))
  have hidx : locN s "index" = locN entry "index" := by
    simp only [locN, h.idx_local]
  exact ⟨
    by rw [hbo_s]; exact hbo_nz_e,
    by rw [hbo24]; exact hbo24_nz_e,
    by rw [hbo32]; exact hbo32_nz_e,
    by rw [hbo40]; exact hbo40_nz_e,
    by rw [hbo72]; exact hbo72_nz_e,
    by rw [hidx, hbo80]; exact hidx_lt_e,
    by rw [globN_eq_of_lookup (h.base.globals (ofString "journal_cap") (by decide))]; exact hjcap_e⟩

/-! ## Store engine for untyped `bo` words (insts 16-19) -/

/-- A single store to an untyped `bo` word (`off ∈ [0, 8, 16, 48]`) transports
`P4Data` to the post state. The store address must be in the memory domain
(what a successful `store` evaluation provides). -/
theorem p4Data_of_bo_word_store {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    {off : Nat} (hoff : off ∈ ([0, 8, 16, 48] : List Nat))
    {x : BitVec 64} (hx_mem : s.memaddrs x) (hx_eq : x.toNat = globN s "bo" + off)
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    P4Data entry {s with memory := mem'} s_pmc w_out := by
  have hA : ArenaReady s := h.base.world.1
  have hE : TxEnv s := txEnv_of_p4Data h
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, hjcap_e, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨S_c, N_c, _, hWT_s, _, _⟩ := h.base.typing S_e Nd_e hWT_e hD_e
  obtain ⟨hgbs, _, hgb_rest, _, _⟩ := fixedObjects_disj_parts hWT_s.2.2.1
  have hbo_fix : (globN s "bo", 88) ∈ fixedObjects s := by
    simpa [hE.bo_nz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
  have hbo_hi : globN s "bo" + 88 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hA.2 (bo_words hWT_s.2.2.1 hE.bo_nz).1).2
  have hin_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp only
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  have hbo_gbs : (globN s "bo", 88) ∈
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
  have hrec_disj : ∀ (g : String) (sz : Nat), (g, sz) ∈ globalBuffers → g ≠ "bo" →
      globN s g ≠ 0 → Disj (globN s g, sz) (globN s "bo", 88) := by
    intro g sz hgb hne hgnz
    obtain ⟨i1, hi1, eq1⟩ := List.mem_iff_getElem.1 hgb
    obtain ⟨i2, hi2, eq2⟩ := List.mem_iff_getElem.1 (show ("bo", 88) ∈ globalBuffers by decide)
    have hne_idx : i1 ≠ i2 := by intro h; subst h; rw [eq1] at eq2; exact hne (congrArg Prod.fst eq2)
    have hget := List.pairwise_iff_getElem.1 hgbs
    rcases Nat.lt_or_gt_of_ne hne_idx with hlt | hgt
    · have hd := hget i1 i2 (by simp; exact hi1) (by simp; exact hi2) hlt
      simpa only [List.getElem_map, eq1, eq2, hgnz, hE.bo_nz, ↓reduceIte] using hd
    · have hd := hget i2 i1 (by simp; exact hi2) (by simp; exact hi1) hgt
      exact disj_symm (by simpa only [List.getElem_map, eq1, eq2, hgnz, hE.bo_nz, ↓reduceIte] using hd)
  -- keep-cell disequalities: bo cells vs the stored untyped word.
  have hbo_cell_ne : ∀ k ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat),
      BitVec.ofNat 64 (globN s "bo" + k) ≠ x := by
    intro k hk heq
    have htonat := congrArg BitVec.toNat heq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff hk
    have hk_lt : globN s "bo" + k < 2 ^ 64 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt, hx_eq] at htonat
    rcases hoff with rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  -- keep-cell disequalities: typed-record cells vs the stored word.
  have hcell_ne : ∀ (g : String) (sz : Nat), (g, sz) ∈ typedRecords → g ≠ "bo" →
      globN s g ≠ 0 → ∀ k, k + 8 ≤ sz → BitVec.ofNat 64 (globN s g + k) ≠ x := by
    intro g sz htr hne hgnz k hk8 heq
    have hd : Disj (globN s g, sz) (x.toNat, 8) :=
      disj_of_inside_right hin_bo (hrec_disj g sz (typedRecord_mem_globalBuffers htr) hne hgnz)
    have hg_fix : (globN s g, sz) ∈ fixedObjects s := by
      simpa [hgnz] using typedRecord_mem_fixedObjects s (r := (g, sz)) htr
    have hsz_nz : (g, sz).2 ≠ 0 := by simp; omega
    obtain ⟨halloc, _⟩ := (hWT_s.2.2.1.1 _ hg_fix).resolve_left hsz_nz
    have hg_hi := (ivl_allocated_bound hA.2 halloc).2
    have htonat := congrArg BitVec.toNat heq
    have hk_lt : globN s g + k < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt, hx_eq] at htonat
    rcases hd with h0 | h0 | h1 | h1 <;> omega
  have hstep : WorldStep (bufRegions ([] : BufList)) [] ptxKeep NoExtra s none
      {s with memory := mem'} := by
    refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩,
      Nat.le_of_eq rfl, fun k _ => rfl, ?_, ?_⟩
    · intro rec hrec hgnz k hk _
      simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · dsimp only at hgnz hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        have hk8 : k + 8 ≤ 40 := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
        have hne := hcell_ne "ws" 40 (by decide) (by decide) hgnz k hk8
        unfold memW
        dsimp only
        rw [hm _ hne]
      · dsimp only at hgnz hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        have hk8 : k + 8 ≤ 80 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        have hne := hcell_ne "bs" 80 (by decide) (by decide) hgnz k hk8
        unfold memW
        dsimp only
        rw [hm _ hne]
      · simp at hk
      · dsimp only at hgnz hk
        unfold memW
        dsimp only
        rw [hm _ (hbo_cell_ne k hk)]
    · intro S Nd hWT _
      have htyp := store_bo_untyped_world hA hE hWT hoff hx_mem hx_eq hm
      refine ⟨S, Nd, fun t ht => ht, htyp.1, ?_, ?_, trivial⟩
      · rw [htyp.2.1]
        exact fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩)
      · intro a hno_keep _
        by_cases hax : a = x
        · subst hax
          have hbo_keep_mem : (globN s "bo", 88) ∈
              worldOwned s S Nd ++ bufRegions ([] : BufList) s ++ [freeGap s] := by
            apply List.mem_append.2; left
            unfold worldOwned
            apply List.mem_append.2; left
            apply List.mem_append.2; left
            apply List.mem_append.2; right
            exact hbo_fix
          have hx_cell : CellHits a.toNat (globN s "bo", 88) :=
            ⟨by have := hin_bo.1; omega, by have := hin_bo.2; omega⟩
          exact absurd hx_cell (hno_keep _ hbo_keep_mem)
        · exact hm a hax
  have hbo_unhit : PtxBlockOutUnhit s {s with memory := mem'} := by
    intro i hi
    apply ivlUnhit_single hm ?_ ?_
    · intro hz
      have h0 := fixedObjects_zero_aligned i (List.mem_append_left _ (List.mem_append_right _ hi)) hz
      simp [h0]
    · refine disj_of_inside_right hin_bo (disj_symm (hgb_rest _ hbo_gbs _ ?_))
      apply List.mem_append.2; left
      apply List.mem_append.2; right
      exact hi
  have hcells := ptxBoCells_of_blockOutUnhit h.base
    (B := ([] : BufList)) (gw := []) (keep := ptxKeep)
    (fun p hp => absurd hp (by simp))
    (fun p hp => absurd hp (by simp))
    (fun g hg => absurd hg (by simp))
    (by intro rec hrec; exact ⟨rec.2, hrec, fun off hoff => hoff⟩)
    (by simp)
    (Or.inl (by simp [ptxKeep]))
    hstep hbo_unhit
  exact p4Data_step_of_worldStep_cells h
    (B := ([] : BufList)) (gw := []) (keep := ptxKeep)
    (fun p hp => absurd hp (by simp))
    (fun p hp => absurd hp (by simp))
    (fun g hg => absurd hg (by simp))
    (by simp) (by simp)
    (by intro rec hrec; exact ⟨rec.2, hrec, fun off hoff => hoff⟩)
    hstep (Nat.le_of_eq rfl) hcells

/-! ## Fresh-region frame composition -/

/-- `ptx_frameOutside_trans` for write regions lying in the heap gap allocated
between `entry` and `s` (no subsumption into the entry's regions needed). -/
theorem ptx_frameOutside_trans_fresh {F : Type}
    {entry s post : PanSemStateFiniteExact 64 F} {old cur R0 R : List Ivl}
    (hA0 : ArenaReady entry) (hAs : ArenaReady s)
    (hhp : globN entry "heap_ptr" ≤ globN s "heap_ptr")
    (hfp : globN entry "frame_mem_ptr" ≤ globN s "frame_mem_ptr")
    (hsp : globN s "scratch_ptr" ≤ globN entry "scratch_ptr")
    (hog : OwnedGrows entry s old cur)
    (hR : ∀ i ∈ R, Inside i (globN entry "heap_ptr") (globN s "heap_ptr"))
    (h01 : FrameOutside entry s (old ++ R0 ++ [freeGap entry]) (heapFree entry))
    (h12 : FrameOutside s post (cur ++ R ++ [freeGap s]) (heapFree s)) :
    FrameOutside entry post (old ++ R0 ++ [freeGap entry]) (heapFree entry) := by
  intro a ha hhf
  apply Eq.trans (h12 a ?_ ?_) (h01 a ha hhf)
  · intro i hi ⟨hc1, hc2⟩
    rcases List.mem_append.1 hi with hi | hi
    · rcases List.mem_append.1 hi with hi | hi
      · rcases hog i hi with rfl | ⟨j, hj, hin⟩ | hin
        · dsimp at hc2; omega
        · exact ha j (List.mem_append_left _ (List.mem_append_left _ hj))
            ⟨by dsimp [Inside] at hin; omega, by dsimp [Inside] at hin; omega⟩
        · have hlim := hAs.2.2.1
          exact hhf ⟨by dsimp [heapFree, Inside] at hin ⊢; omega,
            by dsimp [heapFree, Inside] at hin ⊢; omega⟩
      · have hin := hR i hi
        have hlim := hAs.2.2.1
        exact hhf ⟨by dsimp [heapFree, Inside] at hin ⊢; omega,
          by dsimp [heapFree, Inside] at hin ⊢; omega⟩
    · simp only [List.mem_singleton] at hi
      subst i
      have h0 := hA0.2.2.2.2.1
      have h1 := hAs.2.2.2.2.1
      exact ha (freeGap entry) (List.mem_append_right _ (by simp))
        ⟨by dsimp [freeGap] at hc1 ⊢; omega, by dsimp [freeGap] at hc2 ⊢; omega⟩
  · intro ⟨hc1, hc2⟩
    have hlim := hAs.2.2.1
    exact hhf ⟨by dsimp [heapFree] at hc1 ⊢; omega, by dsimp [heapFree] at hc2 ⊢; omega⟩

/-! ## Generalized-region step engines -/

/-- `ptxRelBase_step_worldStep` for an arbitrary write-region family `R` whose
cells are fresh (inside the heap gap allocated since `entry`), disjoint from the
typed records, and disjoint from the `ptxKeep` record words. -/
theorem ptxRelBase_step_worldStep_R {F : Type} {txDone : Bool}
    {entry s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (h : PtxRelBase txDone entry s)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hkeep : PtxKeepSub keep)
    (hstep : WorldStep R gw keep Q s r post)
    (hR_keepcells : ∀ i ∈ R s, ∀ rec ∈ ptxKeep, globN s rec.1 ≠ 0 →
      ∀ off ∈ rec.2, ¬ CellHits (globN s rec.1 + off) i)
    (hR_disj : ∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hR_fresh : ∀ i ∈ R s, Inside i (globN entry "heap_ptr") (globN s "heap_ptr")) :
    WorldStep ptxRegions ptxGlobals ptxKeep NoExtra entry r post := by
  refine ⟨hstep.1, le_trans h.heap_entry hstep.2.1, ?_, ?_, ?_⟩
  · intro k hk
    have hkg : k ∉ gw.map ofString := by
      intro hm
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
      exact hk (List.mem_map.2 ⟨g, hgw g hg, rfl⟩)
    exact (h.globals k hk).trans (hstep.2.2.1 k hkg)
  · intro rec hr hn off hoff hno
    obtain ⟨offs, hkr, hko⟩ := hkeep rec hr
    have heq : globN s rec.1 = globN entry rec.1 := by
      have hni : ofString rec.1 ∉ ptxGlobals.map ofString := by
        simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · decide
        · decide
        · simp at hoff
        · decide
      exact globN_eq_of_lookup (h.globals (ofString rec.1) hni)
    have hks := hstep.2.2.2.1 (rec.1, offs) hkr (by rw [heq]; exact hn)
      off (hko off hoff)
      (fun i hi => hR_keepcells i hi rec hr (by rw [heq]; exact hn) off hoff)
    rw [heq] at hks
    exact hks.trans (h.records rec hr hn off hoff hno)
  · intro S Nd hWT hD
    obtain ⟨Sc, Nc, hsub, hWc, hOG, hFO⟩ := h.typing S Nd hWT hD
    obtain ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn, _⟩ :=
      hstep.2.2.2.2 Sc Nc hWc (hR_disj Sc Nc hWc)
    refine ⟨Sn, Nn, fun t ht => hsubn t (hsub t ht), hWn,
      ptx_ownedGrows_trans h.heap_entry hstep.2.1 hOG hOGn, ?_, trivial⟩
    exact ptx_frameOutside_trans_fresh h.arena_entry h.world.1 h.heap_entry h.frame_entry
      h.scratch_entry hOG hR_fresh hFO hFOn

/-! ## The `PtxRelBase` cells step over a general region family -/

theorem ptxRelBase_step_cells_R {F : Type} {txDone : Bool}
    {entry s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (h : PtxRelBase txDone entry s)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hkeep : PtxKeepSub keep)
        (hstep : WorldStep R gw keep Q s r post)
    (hR_keepcells : ∀ i ∈ R s, ∀ rec ∈ ptxKeep, globN s rec.1 ≠ 0 →
      ∀ off ∈ rec.2, ¬ CellHits (globN s rec.1 + off) i)
    (hR_disj : ∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hR_fresh : ∀ i ∈ R s, Inside i (globN entry "heap_ptr") (globN s "heap_ptr"))
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hfmp : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr")
    (hcells : PtxBoCells txDone entry s post) :
    PtxRelBase txDone entry post := by
  have hws_entry := ptxRelBase_step_worldStep_R h hgw hkeep hstep hR_keepcells hR_disj hR_fresh
  obtain ⟨⟨_, hbo_nz_e, _, _, _⟩, _, _, _, S_e, Nd_e, hWT_e, _⟩ := h.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨Sc, Nc, _, hWT_w, _, _⟩ := h.typing S_e Nd_e hWT_e hD_e
  obtain ⟨S_wp, Nd_wp, _, hWT_wp, _, _, _⟩ :=
    hstep.2.2.2.2 Sc Nc hWT_w (hR_disj Sc Nc hWT_w)
  have hworld_post : WorldOK post :=
    ⟨hstep.1, S_wp, (worldTyped_iff_with post S_wp).2 ⟨Nd_wp, hWT_wp⟩⟩
  refine ⟨h.ready_entry, h.arena_entry, le_trans h.frame_entry hfmp,
    le_trans hsp h.scratch_entry, hworld_post, hws_entry.2.1, hws_entry.2.2.1,
    hws_entry.2.2.2.1, hcells.rcpt_backing, hcells.log_backing,
    hcells.rcpt_len_eq.trans h.rcpt_len_eq,
    fun off hoff k hk => (hcells.slices_prev off hoff k hk).trans
      (h.slices_prev off hoff k hk),
    hcells.tx_slice_cur, ?_⟩
  intro S0 Nd0 hWT0 hD0
  obtain ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn, _⟩ := hws_entry.2.2.2.2 S0 Nd0 hWT0 hD0
  exact ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn⟩
/-! ## The `P4Data` engine over a general region family -/


/-- Transport `P4Data` across any step given as a `WorldStep` at `s` plus
cell-level block-out facts.  The caller frame is restored (locals of `s`,
clock of the step's exit). -/
theorem p4Data_step_of_worldStep_R {F : Type}
    {entry s s_pmc post : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (h : P4Data entry s s_pmc w_out)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hsys_gw : ofString "vm_system_address" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hstep : WorldStep R gw keep Q s r post)
    (hR_keepcells : ∀ i ∈ R s, ∀ rec ∈ ptxKeep, globN s rec.1 ≠ 0 →
      ∀ off ∈ rec.2, ¬ CellHits (globN s rec.1 + off) i)
    (hR_disj : ∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hR_fresh : ∀ i ∈ R s, Inside i (globN entry "heap_ptr") (globN s "heap_ptr"))
    (hR_zero : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR_out : ∀ j ∈ R s, Disj (w_out.toNat, 96) j)
    (hR_logs : ∀ {logs : Nat} {S Nd : List Nat}, logs ≠ 0 →
      PmcLogsLiveOwned s S Nd logs →
      (∀ j ∈ R s, Disj (logs, 24) j) ∧
      (∀ j ∈ R s, Disj (memW s logs, 8 * memW s (logs + 8)) j) ∧
      (∀ i < memW s (logs + 8), ∀ j ∈ R s,
        Disj (memW s (memW s logs + 8 * i), 40) j))
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hcells : PtxBoCells true entry s post) :
    P4Data entry {post with locals := s.locals, clock := post.clock} s_pmc w_out := by
  have hfmp : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" :=
    Nat.le_of_eq (globN_eq_of_lookup (hstep.2.2.1 _ hfmp_gw)).symm
  have hsys : globN post "vm_system_address" = globN s "vm_system_address" :=
    globN_eq_of_lookup (hstep.2.2.1 _ hsys_gw)
  have hgrow : AllocatorGrows s post := ⟨hstep.2.1, hsp⟩
  have hAs : ArenaOK s := h.base.world.1.2
  have hAp : ArenaOK post := hstep.1.2
  have hgS : GuestInv s := h.base.world.1.1
  have hgP : GuestInv post := hstep.1.1
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e, S_e, Nd_e, hWT_e, _⟩ :=
    h.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨logs, hll, hl_ok, hl_dj, hty⟩ := h.logs_facts
  obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hty1, hty2, hWT_s, hty4, hty5, hty6, hty7, hty8, hty9⟩ :=
    hty S_e Nd_e hWT_e hD_e
  obtain ⟨S_n, N_n, hsub_n, hWT_n, hOG_n, hFO_n, hQ_n⟩ :=
    hstep.2.2.2.2 S_cur Nd_cur hWT_s (hR_disj S_cur Nd_cur hWT_s)
  have hold0 : ∀ j ∈ worldOwned s S_cur Nd_cur, j.2 = 0 → j.1 % 8 = 0 :=
    R13Shards.worldOwned_zero_aligned hWT_s
  have hR0 : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0 := hR_zero
  have hout_u : R13Shards.IvlUnhit s post (w_out.toNat, 96) :=
    (R13Shards.heap_ivl_survives_step hAs hstep.2.1 hold0 hR0 hOG_n hFO_n
      h.out_words.1 h.out_words.2.1 h.out_inside hty7
      (hR_out)).2.2
  have hout_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (R13Shards.ivl_allocated_bound hAs (Or.inl h.out_inside)).2
  have hout_mem : ∀ off ∈ ([80, 88] : List Nat),
      memW post (w_out.toNat + off) = memW s (w_out.toNat + off) := by
    intro off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl
    · apply R13Shards.memW_eq_of_ivlUnhit hout_u
      · have := h.out_words.1; omega
      · exact hout_hi
      · constructor <;> omega
    · apply R13Shards.memW_eq_of_ivlUnhit hout_u
      · have := h.out_words.1; omega
      · exact hout_hi
      · constructor <;> omega
  have hout_list : memW post (w_out.toNat + 16) = memW s (w_out.toNat + 16) := by
    apply R13Shards.memW_eq_of_ivlUnhit hout_u
    · have := h.out_words.1; omega
    · exact hout_hi
    · constructor <;> omega
  have hout_list_surv : memW s (w_out.toNat + 16) ≠ 0 →
      LogsListOK post (memW s (w_out.toNat + 16)) ∧
      PmcLogsLiveOwned post S_n N_n (memW s (w_out.toNat + 16)) := by
    intro hnz
    obtain ⟨hRh, hRa, hRe⟩ := hR_logs hnz hty8
    exact ⟨PtxP34.logsLiveOwned_list_survives hAs hAp hgS hgP hgrow h.logs_ok hty8
      hold0 hR0 hOG_n hFO_n hRh hRa hRe,
      PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow h.logs_ok hty8 hsys
      hold0 hR0 hOG_n hFO_n hRh hRa hRe⟩
  have hlogs_surv : logs ≠ 0 → LogsListOK post logs ∧ PmcLogsLiveOwned post S_n N_n logs := by
    intro hnz
    obtain ⟨hRh, hRa, hRe⟩ := hR_logs hnz hty9
    exact ⟨PtxP34.logsLiveOwned_list_survives hAs hAp hgS hgP hgrow hl_ok hty9
      hold0 hR0 hOG_n hFO_n hRh hRa hRe,
      PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow hl_ok hty9 hsys
      hold0 hR0 hOG_n hFO_n hRh hRa hRe⟩
  refine ⟨ptxRelBase_with_locals
      (ptxRelBase_step_cells_R h.base hgw hkeep hstep hR_keepcells hR_disj hR_fresh hsp hfmp hcells) s.locals post.clock,
    h.arena_pmc, le_trans h.heap_pmc hstep.2.1, h.out_local,
    R13Shards.wordsOK_transfer hgS hgP h.out_words,
    (R13Shards.heap_ivl_survives_step hAs hstep.2.1 hold0 hR0 hOG_n hFO_n
      h.out_words.1 h.out_words.2.1 h.out_inside hty7
      (hR_out)).1,
    ?_, ?_, h.shapes, h.tx_local, h.idx_local, ?_⟩
  · intro h80_nz
    have h80_nz' : memW s (w_out.toNat + 80) ≠ 0 := by
      rw [← hout_mem 80 (by simp)]; exact h80_nz
    obtain ⟨h80_8, h88_8, h88_le, h80_8b, h80_sc⟩ := h.marks h80_nz'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show memW post (w_out.toNat + 80) % 8 = 0
      rw [hout_mem 80 (by simp)]; exact h80_8
    · show memW post (w_out.toNat + 88) % 8 = 0
      rw [hout_mem 88 (by simp)]; exact h88_8
    · show globN s_pmc "frame_mem_ptr" ≤ memW post (w_out.toNat + 88)
      rw [hout_mem 88 (by simp)]; exact h88_le
    · show memW post (w_out.toNat + 88) ≤ memW post (w_out.toNat + 80)
      rw [hout_mem 88 (by simp), hout_mem 80 (by simp)]; exact h80_8b
    · show memW post (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr"
      rw [hout_mem 80 (by simp)]; exact h80_sc
  · show LogsListOK post (memW post (w_out.toNat + 16))
    rw [hout_list]
    by_cases hnz : memW s (w_out.toNat + 16) = 0
    · rw [hnz]; exact Or.inl rfl
    · exact (hout_list_surv hnz).1
  · refine ⟨logs, ?_, ?_, ?_, ?_⟩
    · rcases hll with hll | hll
      · exact Or.inl hll
      · exact Or.inr hll
    · by_cases hnz : logs = 0
      · exact Or.inl hnz
      · have h1 := (hlogs_surv hnz).1
        exact (R13Shards.logsListOK_with_locals post s.locals post.clock logs).2 h1
    · by_cases hnz : logs = 0
      · exact Or.inl hnz
      · exact pmcLogsLiveOwned_disjFixed (hlogs_surv hnz).2
    · intro S0 Nd0 hWT0 hD0
      obtain ⟨S_pmc', Nd_pmc', S_cur', Nd_cur', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        hty S0 Nd0 hWT0 hD0
      obtain ⟨S_n', N_n', hsub', hWT_n', hOG_n', hFO_n', hQ_n'⟩ :=
        hstep.2.2.2.2 S_cur' Nd_cur' h3 (hR_disj S_cur' Nd_cur' h3)
      have hold0' : ∀ j ∈ worldOwned s S_cur' Nd_cur', j.2 = 0 → j.1 % 8 = 0 :=
        R13Shards.worldOwned_zero_aligned h3
      have hR0' : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0 := hR_zero
      have hout_u' : R13Shards.IvlUnhit s post (w_out.toNat, 96) :=
        (R13Shards.heap_ivl_survives_step hAs hstep.2.1 hold0' hR0' hOG_n' hFO_n'
          h.out_words.1 h.out_words.2.1 h.out_inside h7
          (hR_out)).2.2
      have hout_list' : memW post (w_out.toNat + 16) = memW s (w_out.toNat + 16) := by
        apply R13Shards.memW_eq_of_ivlUnhit hout_u'
        · have := h.out_words.1; omega
        · exact hout_hi
        · constructor <;> omega
      have hout_list_surv' : memW s (w_out.toNat + 16) ≠ 0 →
          PmcLogsLiveOwned post S_n' N_n' (memW s (w_out.toNat + 16)) := by
        intro hnz
        obtain ⟨hRh, hRa, hRe⟩ := hR_logs hnz h8
        exact PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow h.logs_ok h8 hsys
          hold0' hR0' hOG_n' hFO_n' hRh hRa hRe
      have hlogs_surv' : logs ≠ 0 → PmcLogsLiveOwned post S_n' N_n' logs := by
        intro hnz
        obtain ⟨hRh, hRa, hRe⟩ := hR_logs hnz h9
        exact PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow hl_ok h9 hsys
          hold0' hR0' hOG_n' hFO_n' hRh hRa hRe
      refine ⟨S_pmc', Nd_pmc', S_n', N_n', h1, fun t ht => hsub' t (h2 t ht),
        (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals post s.locals post.clock S_n' N_n').2 hWT_n',
        ptx_ownedGrows_trans h.heap_pmc hstep.2.1 h4 hOG_n',
        ptx_ownedGrows_trans h.base.heap_entry hstep.2.1 h5 hOG_n',
        ptx_frameOutside_trans_fresh h.base.arena_entry ⟨hgS, hAs⟩ h.base.heap_entry
          h.base.frame_entry h.base.scratch_entry h5 hR_fresh h6 hFO_n',
        (R13Shards.heap_ivl_survives_step hAs hstep.2.1 hold0' hR0' hOG_n' hFO_n'
          h.out_words.1 h.out_words.2.1 h.out_inside h7
          (hR_out)).2.1, ?_, ?_⟩
      · show PmcLogsLiveOwned post S_n' N_n' (memW post (w_out.toNat + 16))
        rw [hout_list']
        by_cases hnz : memW s (w_out.toNat + 16) = 0
        · rw [hnz]; exact pmcLogsLiveOwned_zero _ _ _
        · exact hout_list_surv' hnz
      · show PmcLogsLiveOwned post S_n' N_n' logs
        by_cases hnz : logs = 0
        · rw [hnz]; exact pmcLogsLiveOwned_zero _ _ _
        · exact hlogs_surv' hnz
/-! ## The `bo+32` receipt-slice store engine (insts 26-27) -/

/-- A word store into the `bo+32` receipt-slices array (block-out element 1) at
the current receipt index.  All `PtxBoCells` facts survive: the kept record
words, the list headers (block-out elements 3/5), the previous slice words, and
the current `bo+24` slice word. -/
theorem p4Data_of_bo_slice_store {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    {j : Nat} (hj : j = 0 ∨ j = 8)
    {x : BitVec 64} (hx_mem : s.memaddrs x)
    (hx_eq : x.toNat = memW s (globN s "bo" + 32) + 16 * locN s "index" + j)
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    P4Data entry {s with memory := mem'} s_pmc w_out := by
  have hA : ArenaReady s := h.base.world.1
  have hE : TxEnv s := txEnv_of_p4Data h
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, hjcap_e, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨S_c, N_c, _, hWT_s, _, _⟩ := h.base.typing S_e Nd_e hWT_e hD_e
  obtain ⟨hgbs, hbo_pw, hgb_rest, hjr_rest, hbo_bal⟩ := fixedObjects_disj_parts hWT_s.2.2.1
  have hbo_nz_s : globN s "bo" ≠ 0 := by
    rw [globN_eq_of_lookup (h.base.globals (ofString "bo") (by decide))]; exact hbo_nz_e
  have hbo24_s : memW s (globN s "bo" + 24) = memW entry (globN entry "bo" + 24) :=
    ptx_entry_bo_field_eq hWT_e h.base.globals h.base.records hbo_nz_e (by simp) (by omega)
  have hbo32_s : memW s (globN s "bo" + 32) = memW entry (globN entry "bo" + 32) :=
    ptx_entry_bo_field_eq hWT_e h.base.globals h.base.records hbo_nz_e (by simp) (by omega)
  have hbo40_s : memW s (globN s "bo" + 40) = memW entry (globN entry "bo" + 40) :=
    ptx_entry_bo_field_eq hWT_e h.base.globals h.base.records hbo_nz_e (by simp) (by omega)
  have hbo72_s : memW s (globN s "bo" + 72) = memW entry (globN entry "bo" + 72) :=
    ptx_entry_bo_field_eq hWT_e h.base.globals h.base.records hbo_nz_e (by simp) (by omega)
  have hbo80_s : memW s (globN s "bo" + 80) = memW entry (globN entry "bo" + 80) :=
    ptx_entry_bo_field_eq hWT_e h.base.globals h.base.records hbo_nz_e (by simp) (by omega)
  have hidx_s : locN s "index" = locN entry "index" := by simp only [locN, h.idx_local]
  have hidx_lt : locN s "index" < memW s (globN s "bo" + 80) := by
    rw [hidx_s, hbo80_s]; exact hidx_lt_e
  have hbo24_nz_s : memW s (globN s "bo" + 24) ≠ 0 := by rw [hbo24_s]; exact hbo24_nz_e
  have hbo32_nz_s : memW s (globN s "bo" + 32) ≠ 0 := by rw [hbo32_s]; exact hbo32_nz_e
  have hbo40_nz_s : memW s (globN s "bo" + 40) ≠ 0 := by rw [hbo40_s]; exact hbo40_nz_e
  have hbo72_nz_s : memW s (globN s "bo" + 72) ≠ 0 := by rw [hbo72_s]; exact hbo72_nz_e
  -- element 1 (the bo+32 receipt-slices array) and the store position
  have hin : Inside (x.toNat, 8) (memW s (globN s "bo" + 32))
      (memW s (globN s "bo" + 32) + (16 * memW s (globN s "bo" + 80) + 16)) := by
    refine ⟨?_, ?_⟩ <;> [skip; skip]
    · omega
    · rcases hj with rfl | rfl <;> omega
  have hbo_gbs : (globN s "bo", 88) ∈
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
  obtain ⟨hc40, hc72, hbo_eq⟩ := blockOutObjects_eq_list hE hWT_s.1
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo_eq]; rfl
  have hget1 : (blockOutObjects s)[1] =
      (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) := by
    simp [hbo_eq]
  have hget3 : (blockOutObjects s)[3] = (memW s (globN s "bo" + 40), 24) := by
    simp [hbo_eq]
  have hget5 : (blockOutObjects s)[5] = (memW s (globN s "bo" + 72), 24) := by
    simp [hbo_eq]
  have hget0 : (blockOutObjects s)[0] =
      (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16) := by
    simp [hbo_eq, hbo_nz_s, hbo24_nz_s,
      (by omega : 16 * memW s (globN s "bo" + 80) + 16 ≠ 0)]
  have he1_mem : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) ∈
      blockOutObjects s := hget1 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have hpair := List.pairwise_iff_getElem.1 hbo_pw
  have hd01 : Disj (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16)
      (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) := by
    have h := hpair 0 1 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget0, hget1] at h
    exact h
  have hd31 : Disj (memW s (globN s "bo" + 40), 24)
      (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) := by
    have h := hpair 1 3 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget1, hget3] at h
    exact disj_symm h
  have hd51 : Disj (memW s (globN s "bo" + 72), 24)
      (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) := by
    have h := hpair 1 5 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget1, hget5] at h
    exact disj_symm h
  have hbo_disj_e1 : Disj (globN s "bo", 88)
      (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) :=
    hgb_rest _ hbo_gbs _
      (List.mem_append_left _ (List.mem_append_right _ he1_mem))
  -- allocation bounds for the block-out elements
  have hel_bound : ∀ ek ∈ blockOutObjects s, ek.2 ≠ 0 → ek.1 + ek.2 ≤ 2 ^ 64 := by
    intro ek hek hnz
    have hfix : ek ∈ fixedObjects s :=
      List.mem_append_left _ (List.mem_append_right _ hek)
    obtain ⟨halloc, _⟩ := (hWT_s.2.2.1.1 _ hfix).resolve_left hnz
    exact (ivl_allocated_bound hA.2 halloc).2
  -- keep-cell disequalities: bo cells vs the stored slice word.
  have hbo_cell_ne : ∀ k ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat),
      BitVec.ofNat 64 (globN s "bo" + k) ≠ x := by
    intro k hk heq
    have hbo_hi : globN s "bo" + 88 ≤ 2 ^ 64 :=
      (ivl_allocated_bound hA.2 (bo_words hWT_s.2.2.1 hE.bo_nz).1).2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      have htonat := congrArg BitVec.toNat heq <;>
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at htonat <;>
      have hd : Disj (globN s "bo", 88) (x.toNat, 8) := disj_of_inside_right hin hbo_disj_e1 <;>
      rcases hd with h0 | h0 | h1 | h1 <;> omega
  -- keep-cell disequalities: typed-record cells vs the stored slice word.
  have hrec_disj : ∀ (g : String) (sz : Nat), (g, sz) ∈ globalBuffers → g ≠ "bo" →
      globN s g ≠ 0 → Disj (globN s g, sz)
        (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) := by
    intro g sz hgb hne hgnz
    exact hgb_rest _ (List.mem_map.2 ⟨(g, sz), hgb, by simp [hgnz]⟩) _
      (List.mem_append_left _ (List.mem_append_right _ he1_mem))
  have hcell_ne : ∀ (g : String) (sz : Nat), (g, sz) ∈ typedRecords → g ≠ "bo" →
      globN s g ≠ 0 → ∀ k, k + 8 ≤ sz → BitVec.ofNat 64 (globN s g + k) ≠ x := by
    intro g sz htr hne hgnz k hk8 heq
    have hd : Disj (globN s g, sz) (x.toNat, 8) :=
      disj_of_inside_right hin (hrec_disj g sz (typedRecord_mem_globalBuffers htr) hne hgnz)
    have hg_fix : (globN s g, sz) ∈ fixedObjects s := by
      simpa [hgnz] using typedRecord_mem_fixedObjects s (r := (g, sz)) htr
    have hsz_nz : (g, sz).2 ≠ 0 := by simp; omega
    obtain ⟨halloc, _⟩ := (hWT_s.2.2.1.1 _ hg_fix).resolve_left hsz_nz
    have hg_hi := (ivl_allocated_bound hA.2 halloc).2
    have htonat := congrArg BitVec.toNat heq
    have hk_lt : globN s g + k < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt] at htonat
    rcases hd with h0 | h0 | h1 | h1 <;> omega
  -- word cells inside other block-out elements are not the stored word
  have hword_ne : ∀ (a : Nat) (ek : Ivl), Disj ek
      (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) →
      Inside (a, 8) ek.1 (ek.1 + ek.2) → a < 2 ^ 64 → BitVec.ofNat 64 a ≠ x := by
    intro a ek hd hin_k ha_lt heq
    have htonat := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at htonat
    have hx_lt := x.isLt
    have hdx : Disj ek (x.toNat, 8) := disj_of_inside_right hin hd
    rw [← htonat] at hdx
    have hk1 := hin_k.1
    have hk2 := hin_k.2
    rcases hdx with h0 | h0 | h1 | h1 <;> omega
  have hstep : WorldStep (bufRegions ([] : BufList)) [] ptxKeep NoExtra s none
      {s with memory := mem'} := by
    refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩,
      Nat.le_of_eq rfl, fun k _ => rfl, ?_, ?_⟩
    · intro rec hrec hgnz k hk _
      simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · dsimp only at hgnz hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        have hk8 : k + 8 ≤ 40 := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
        have hne := hcell_ne "ws" 40 (by decide) (by decide) hgnz k hk8
        unfold memW
        dsimp only
        rw [hm _ hne]
      · dsimp only at hgnz hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        have hk8 : k + 8 ≤ 80 := by
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        have hne := hcell_ne "bs" 80 (by decide) (by decide) hgnz k hk8
        unfold memW
        dsimp only
        rw [hm _ hne]
      · simp at hk
      · dsimp only at hgnz hk
        unfold memW
        dsimp only
        rw [hm _ (hbo_cell_ne k hk)]
    · intro S Nd hWT _
      have htyp := store_bo_array_world (idx := 1)
        (arr := (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16))
        hA hE hWT (Or.inl ⟨rfl, rfl⟩) hx_mem hin hm
      refine ⟨S, Nd, fun t ht => ht, htyp.1, ?_, ?_, trivial⟩
      · rw [htyp.2.1]
        exact fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩)
      · intro a hno_keep _
        by_cases hax : a = x
        · subst hax
          have he1_fix : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) ∈
              worldOwned s S Nd ++ bufRegions ([] : BufList) s ++ [freeGap s] := by
            apply List.mem_append.2; left
            unfold worldOwned
            apply List.mem_append.2; left
            apply List.mem_append.2; left
            apply List.mem_append.2; right
            exact List.mem_append_left _ (List.mem_append_right _ he1_mem)
          have hx_cell : CellHits a.toNat
              (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) :=
            ⟨by have := hin.1; omega, by have := hin.2; omega⟩
          exact absurd hx_cell (hno_keep _ he1_fix)
        · exact hm a hax
  -- the direct `PtxBoCells` proof for a store inside element 1
  have hk_post : ∀ off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat),
      memW {s with memory := mem'} (globN s "bo" + off) = memW s (globN s "bo" + off) := by
    intro off hoff
    have hne : BitVec.ofNat 64 (globN s "bo" + off) ≠ x := hbo_cell_ne off hoff
    unfold memW
    dsimp only
    rw [hm _ hne]
  have h0_mem : (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16) ∈
      blockOutObjects s := hget0 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have hb0 := hel_bound _ h0_mem (by dsimp only; omega)
  have h3_mem : (memW s (globN s "bo" + 40), 24) ∈ blockOutObjects s :=
    hget3 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have hb3 := hel_bound _ h3_mem (by simp)
  have h5_mem : (memW s (globN s "bo" + 72), 24) ∈ blockOutObjects s :=
    hget5 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have hb5 := hel_bound _ h5_mem (by simp)
  have hb1 := hel_bound _ he1_mem (by dsimp only; omega)
  -- the outer memory of a post-store word at a raw address
  have hmem_post : ∀ n : Nat, BitVec.ofNat 64 n ≠ x →
      memW {s with memory := mem'} n = memW s n := by
    intro n hne
    unfold memW
    dsimp only
    rw [hm (BitVec.ofNat 64 n) hne]
  have hcells : PtxBoCells true entry s {s with memory := mem'} := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · show memW {s with memory := mem'} (memW {s with memory := mem'} (globN s "bo" + 72)) ≠ 0
      rw [hk_post 72 (by simp)]
      have hne := hword_ne (memW s (globN s "bo" + 72)) (memW s (globN s "bo" + 72), 24) hd51
        ⟨le_rfl, by omega⟩ (by omega)
      rw [hmem_post (memW s (globN s "bo" + 72)) hne]
      exact h.base.rcpt_backing
    · show memW {s with memory := mem'} (memW {s with memory := mem'} (globN s "bo" + 40)) ≠ 0
      rw [hk_post 40 (by simp)]
      have hne := hword_ne (memW s (globN s "bo" + 40)) (memW s (globN s "bo" + 40), 24) hd31
        ⟨le_rfl, by omega⟩ (by omega)
      rw [hmem_post (memW s (globN s "bo" + 40)) hne]
      exact h.base.log_backing
    · show memW {s with memory := mem'}
          (memW {s with memory := mem'} (globN s "bo" + 72) + 8) =
        memW s (memW s (globN s "bo" + 72) + 8)
      rw [hk_post 72 (by simp)]
      have hne := hword_ne (memW s (globN s "bo" + 72) + 8) (memW s (globN s "bo" + 72), 24)
        hd51 ⟨by omega, by omega⟩ (by omega)
      rw [hmem_post (memW s (globN s "bo" + 72) + 8) hne]
    · intro off hoff i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl
      · show memW {s with memory := mem'}
            (memW {s with memory := mem'} (globN s "bo" + 24) + 16 * i + 8) =
          memW s (memW s (globN s "bo" + 24) + 16 * i + 8)
        rw [hk_post 24 (by simp)]
        have hne := hword_ne (memW s (globN s "bo" + 24) + 16 * i + 8)
          (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16) hd01
          ⟨by omega, by omega⟩ (by omega)
        rw [hmem_post (memW s (globN s "bo" + 24) + 16 * i + 8) hne]
      · show memW {s with memory := mem'}
            (memW {s with memory := mem'} (globN s "bo" + 32) + 16 * i + 8) =
          memW s (memW s (globN s "bo" + 32) + 16 * i + 8)
        rw [hk_post 32 (by simp)]
        have hne : BitVec.ofNat 64 (memW s (globN s "bo" + 32) + 16 * i + 8) ≠ x := by
          intro heq
          have htonat := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at htonat
          rcases hj with rfl | rfl <;> omega
        rw [hmem_post (memW s (globN s "bo" + 32) + 16 * i + 8) hne]
    · intro _
      show memW {s with memory := mem'}
        (memW {s with memory := mem'} (globN s "bo" + 24) + 16 * locN entry "index" + 8) < 2 ^ 40
      rw [hk_post 24 (by simp)]
      have hne := hword_ne (memW s (globN s "bo" + 24) + 16 * locN entry "index" + 8)
        (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16) hd01
        ⟨by omega, by omega⟩ (by omega)
      rw [hmem_post (memW s (globN s "bo" + 24) + 16 * locN entry "index" + 8) hne]
      exact h.base.tx_slice_cur rfl
  exact p4Data_step_of_worldStep_cells h
    (B := ([] : BufList)) (gw := []) (keep := ptxKeep)
    (fun p hp => absurd hp (by simp))
    (fun p hp => absurd hp (by simp))
    (fun g hg => absurd hg (by simp))
    (by simp) (by simp)
    (by intro rec hrec; exact ⟨rec.2, hrec, fun off hoff => hoff⟩)
    hstep (Nat.le_of_eq rfl) hcells

/-! ### The `lst_new` unhit bridge (instruction 34) -/

/-- An `lst_new` call writes only inside the fresh heap interval below the new
`heap_ptr`, so every (allocated, hence below the old `heap_ptr`) block-out
object survives untouched. -/
theorem ptxBlockOutUnhit_of_fresh_heap {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hWT : WorldTypedWith s S Nd)
    (hAR : ArenaReady s) (hARp : ArenaReady post)
    (hfr : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    PtxBlockOutUnhit s post := by
  apply ptxBlockOutUnhit_of_nonempty
  intro i hi hne
  obtain ⟨_, hal, _, _⟩ := blockOut_allocated_words hWT hi hne
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hAR.2
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩ := hARp.2
  have hsep : heapLimit ≤ scratchStart := by decide
  have hdisj : Disj i (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    rcases hal with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
  exact R10Shards.Fast_GbodyC17ToC21.ivlUnhit_of_frameOutside_aligned hfr
    (fun hz => absurd hz hne)
    (fun j hj => by obtain rfl := List.mem_singleton.1 hj; exact ⟨h8, by omega⟩)
    ⟨h6, by omega⟩
    (fun j hj => by obtain rfl := List.mem_singleton.1 hj; exact Or.inr (Or.inl rfl))
    hdisj

/-! ### The `lst_new` `decCall` runner (instruction 34) -/

/-- The `lst_new` decCall engine.  The typing clause comes from `«wk_lst_new»`,
the returned-word and fresh-heap facts from `WkBal.lst_new_heap_props`, and the
block-out unhit from the fresh-heap frame via `ptxBlockOutUnhit_of_fresh_heap`. -/
theorem p4Run_decCall_lst_new {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (name : MlS) (args : List (ExpHOL 64)) (eszw capw : BitVec 64) (tail : ProgHOL 64)
    (hnout : name ≠ ofString "out") (hntx : name ≠ ofString "tx")
    (hnidx : name ≠ ofString "index") (hnlogs : name ≠ ofString "logs")
    (hshn : ∀ nm ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used",
      "price", "intrinsic"] : List String), ofString nm ≠ name)
    (hesz_pos : 1 ≤ eszw.toNat) (hcap_pos : 1 ≤ capw.toNat)
    (hmul_lt : eszw.toNat * capw.toNat < 2 ^ 64)
    (hmul_al : (eszw.toNat * capw.toNat) % 8 = 0)
    (harg : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [.val (.word eszw), .val (.word capw)])
    (htail : ∀ (lw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw.toNat = globN s "heap_ptr" →
      lw.toNat % 8 = 0 →
      lw.toNat ≠ 0 →
      memW mid lw.toNat = lw.toNat + 24 →
      memW mid (lw.toNat + 8) = 0 →
      memW mid (lw.toNat + 16) = capw.toNat →
      globN mid "heap_ptr" = lw.toNat + 24 + eszw.toNat * capw.toNat →
      globN s "heap_ptr" < globN mid "heap_ptr" →
      ArenaReady mid →
      globN mid "scratch_ptr" = globN s "scratch_ptr" →
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" →
      LstOK mid lw.toNat →
      lstObjects mid lw.toNat eszw.toNat =
        [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] →
      Disj (lw.toNat, 24) (lw.toNat + 24, eszw.toNat * capw.toNat) →
      (∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
        Allocated mid i ∧ WordsOK mid i ∧
        Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) →
      FrameOutside s mid [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") →
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) →
      mid.locals.lookup name = some (.val (.word lw)) →
      (∀ y, y ≠ name → mid.locals.lookup y = s.locals.lookup y) →
      (∀ S0 Nd0 : List Nat, WorldTypedWith entry S0 Nd0 →
        IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
        ∃ S_pmc' Nd_pmc' S_new Nd_new : List Nat,
          WorldTypedWith s_pmc S_pmc' Nd_pmc' ∧
          (∀ t' ∈ S0, t' ∈ S_new) ∧
          WorldTypedWith mid S_new Nd_new ∧
          OwnedGrows s_pmc mid (worldOwned s_pmc S_pmc' Nd_pmc')
            (worldOwned mid S_new Nd_new) ∧
          OwnedGrows entry mid (worldOwned entry S0 Nd0) (worldOwned mid S_new Nd_new) ∧
          FrameOutside entry mid
            (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry) ∧
          (∀ o ∈ worldOwned mid S_new Nd_new, Disj (w_out.toNat, 96) o) ∧
          IvlsDisj [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)]
            (worldOwned mid S_new Nd_new) ∧
          PmcLogsLiveOwned mid S_new Nd_new (memW mid (w_out.toNat + 16)) ∧
          PmcLogsLiveOwned mid S_new Nd_new lw.toNat) →
      P4Data entry mid s_pmc w_out →
      mid.code = originalRuntimeCode →
      PtxRelRunStrong entry tail mid) :
    PtxRelRunStrong entry (.decCall name .one (ofString "lst_new") args tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  rw [harg] at hres ⊢
  dsimp only at hres ⊢
  have hlk := pan_two_word_lookup s.code.lookup (ofString "lst_new") (ofString "esz")
    (ofString "cap") (sourceFnBody Guest.Software.guestFn_lst_new) eszw capw
    (by decide) (by rw [hc]; exact WkBal.lookup_lst_new_wk)
  rw [hlk] at hres ⊢
  dsimp only at hres ⊢
  by_cases hcz : s.clock = 0
  · simp only [hcz, ↓reduceIte] at hres
    exact absurd hres (by rintro (⟨_, hh⟩ | ⟨_, _, hh, _⟩) <;> simp at hh)
  · simp only [hcz, ↓reduceIte] at hres ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "esz", ValueHOL.val (.word eszw))).update
      (ofString "cap", ValueHOL.val (.word capw)) with hcmap_def
    have hAR_ent : ArenaReady (callEntryStateHOLFinite s cmap) :=
      (arenaReady_with_locals s cmap (s.clock - 1)).2 h.base.world.1
    have hent_e : (callEntryStateHOLFinite s cmap).locals.lookup (ofString "esz") =
        some (.val (.word eszw)) := by
      simp [callEntryStateHOLFinite, hcmap_def, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "cap" ≠ ofString "esz" by decide]
    have hent_c : (callEntryStateHOLFinite s cmap).locals.lookup (ofString "cap") =
        some (.val (.word capw)) := by
      simp [callEntryStateHOLFinite, hcmap_def, HolFiniteMapExact.lookup_update, FUPDATE]
    have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite s cmap) (sourceFnBody Guest.Software.guestFn_lst_new)).1
    rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_lst_new) with ⟨rb, sb⟩
    have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_lst_new) = (rb, sb) := hb
    rw [hb] at hmeta
    simp only [hb] at hres ⊢
    cases rb with
    | none => exact absurd hres (by rintro (⟨_, hh⟩ | ⟨_, _, hh, _⟩) <;> simp at hh)
    | some cr =>
      cases cr with
      | timeOut | error | «break» | «continue» | finalFfi _ =>
        exact absurd hres (by rintro (⟨_, hh⟩ | ⟨_, _, hh, _⟩) <;> simp at hh)
      | exception eid ev =>
        exfalso
        rcases hres with ⟨v', hv⟩ | ⟨e', ev', hv, hne⟩
        · simp at hv
        · exact WkBal.lst_new_no_catchable_exn (callEntryStateHOLFinite s cmap) hAR_ent.1.code
            e' ev' hne (by rw [hb']; exact hv)
      | returned v =>
        dsimp only at hres ⊢
        have hprops := WkBal.lst_new_heap_props (callEntryStateHOLFinite s cmap) eszw capw
          hAR_ent hesz_pos hmul_lt hmul_al hcap_pos hent_e hent_c v (congrArg Prod.fst hb')
        have hrun_snd : (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
            (sourceFnBody Guest.Software.guestFn_lst_new)).2 = sb := congrArg Prod.snd hb'
        dsimp only at hprops
        rw [hrun_snd] at hprops
        obtain ⟨lw, rfl, hlw_eq, hlw_al, hlw_nz, hm0, hm8, hm16, hhp_sb, hhp_lt, hAsb, hbe_sb,
          hsp_sb, hfmp_sb, hlst_sb, hobjs_sb, hdisj_sb, hobjs_props, hfr_sb, hgl_sb⟩ := hprops
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word lw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word lw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hres ⊢
        have hspec := PtxP1.funSpec_at_lookup R13Wk06b.«wk_lst_new» s hc
          [.val (.word eszw), .val (.word capw)] (sourceFnBody Guest.Software.guestFn_lst_new)
          cmap .one hlk (PtxP1.worldOK_callEntry h.base.world cmap)
          (by rw [hb']; simp)
        rw [hb'] at hspec
        have hstep_ent := hspec (Or.inl ⟨(.val (.word lw) : ValueHOL 64), rfl⟩)
        have hstep_s : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra
            s (some (.returned (.val (.word lw)))) sb :=
          R13Shards.worldStep_with_locals hstep_ent s.locals s.clock
        have hsp : globN sb "scratch_ptr" ≤ globN s "scratch_ptr" := Nat.le_of_eq hsp_sb
        obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
          S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
        have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
          rw [ptxRegions_eq_bufRegions]
          exact validBufList_disj validBufList_ptxBufs hWT_e
        obtain ⟨logs, hll, hl_ok, hl_dj, hty⟩ := h.logs_facts
        obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hty1, hty2, hWT_s, hty4, hty5, hty6, hty7, hty8,
          hty9⟩ := hty S_e Nd_e hWT_e hD_e
        have hunhit : PtxBlockOutUnhit s sb :=
          ptxBlockOutUnhit_of_fresh_heap hWT_s h.base.world.1 hAsb hfr_sb
        have hcells : PtxBoCells true entry s sb :=
          ptxBoCells_of_blockOutUnhit h.base (B := ([] : BufList)) (gw := ["heap_ptr"])
            (keep := stdKeep)
            (fun p hp => absurd hp (by simp))
            (fun p hp => absurd hp (by simp))
            (fun g hg => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
              subst hg
              decide)
            ptxKeepSub_stdKeep
            (by decide)
            (Or.inr (by simp [stdKeep]))
            hstep_s hunhit
        have hdata_sb : P4Data entry { sb with locals := s.locals, clock := sb.clock } s_pmc w_out :=
          p4Data_step_of_worldStep_cells h (B := ([] : BufList)) (gw := ["heap_ptr"])
            (keep := stdKeep)
            (fun p hp => absurd hp (by simp))
            (fun p hp => absurd hp (by simp))
            (fun g hg => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
              subst hg
              decide)
            (by decide) (by decide) ptxKeepSub_stdKeep
            hstep_s hsp hcells
        have hdata_mid : P4Data entry
            (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals }) s_pmc w_out :=
          p4Data_setVar hnout hntx hnidx hnlogs hshn hdata_sb
        have hAR_mid : ArenaReady
            (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals }) :=
          (arenaReady_with_locals sb _ sb.clock).2 hAsb
        have hloc_name : (setVarHOLFinite name (.val (.word lw))
            { sb with locals := s.locals }).locals.lookup name = some (.val (.word lw)) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hloc_rest : ∀ y, y ≠ name → (setVarHOLFinite name (.val (.word lw))
            { sb with locals := s.locals }).locals.lookup y = s.locals.lookup y := by
          intro y hy
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy]
        have hgS : GuestInv s := h.base.world.1.1
        have hAs : ArenaOK s := h.base.world.1.2
        have hAp : ArenaOK sb := hAsb.2
        have hgrow : AllocatorGrows s sb := ⟨Nat.le_of_lt hhp_lt, hsp⟩
        have hsys : globN sb "vm_system_address" = globN s "vm_system_address" :=
          globN_eq_of_lookup (hgl_sb (ofString "vm_system_address") (by decide))
        have hR0 : ∀ j ∈ ([] : List Ivl), j.2 = 0 → j.1 % 8 = 0 := fun j hj =>
          absurd hj (by simp)
        have hBnil : ValidBufList ([] : BufList) := fun p hp => absurd hp (by simp)
        have hgrow_le : globN s "heap_ptr" ≤ globN sb "heap_ptr" := Nat.le_of_lt hhp_lt
        have hC : locN (callEntryStateHOLFinite s cmap) "esz" *
            locN (callEntryStateHOLFinite s cmap) "cap" < 2 ^ 64 := by
          simp only [locN, hent_e, hent_c]
          exact hmul_lt
        have htychain : ∀ S0 Nd0 : List Nat, WorldTypedWith entry S0 Nd0 →
            IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
          ∃ S_pmc' Nd_pmc' S_new Nd_new : List Nat,
            WorldTypedWith s_pmc S_pmc' Nd_pmc' ∧
            (∀ t' ∈ S0, t' ∈ S_new) ∧
            WorldTypedWith
              (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
              S_new Nd_new ∧
            OwnedGrows s_pmc
              (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
              (worldOwned s_pmc S_pmc' Nd_pmc')
              (worldOwned
                (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
                S_new Nd_new) ∧
            OwnedGrows entry
              (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
              (worldOwned entry S0 Nd0)
              (worldOwned
                (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
                S_new Nd_new) ∧
            FrameOutside entry
              (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
              (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry])
              (heapFree entry) ∧
            (∀ o ∈ worldOwned
                (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
                S_new Nd_new, Disj (w_out.toNat, 96) o) ∧
            IvlsDisj [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)]
              (worldOwned
                (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
                S_new Nd_new) ∧
            PmcLogsLiveOwned
              (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
              S_new Nd_new (memW
                (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
                (w_out.toNat + 16)) ∧
            PmcLogsLiveOwned
              (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
              S_new Nd_new lw.toNat := by
          set mid := setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals }
            with hmid_def
          intro S0 Nd0 hWT0 hD0
          obtain ⟨S_pmc', Nd_pmc', S_cur', Nd_cur', c1, c2, hWT_s', c4, c5, c6, c7, c8, c9⟩ :=
            hty S0 Nd0 hWT0 hD0
          have hWT_ent' : WorldTypedWith (callEntryStateHOLFinite s cmap) S_cur' Nd_cur' :=
            (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s cmap (s.clock - 1)
              S_cur' Nd_cur').2 hWT_s'
          obtain ⟨S2', N2', hs2', hWT_sb2', hOG2', hFO2', hQ2'⟩ :=
            hstep_ent.2.2.2.2 S_cur' Nd_cur' hWT_ent'
              (by intro o ho j hj; exact absurd ho (by simp))
          obtain ⟨w', hw', hdisj_w'⟩ := hQ2' hC (.val (.word lw)) rfl
          have hwl' : w' = lw := by
            injection hw' with h1
            injection h1 with h2
            exact h2.symm
          rw [hwl'] at hdisj_w'
          have hold0' : ∀ j ∈ worldOwned s S_cur' Nd_cur', j.2 = 0 → j.1 % 8 = 0 :=
            R13Shards.worldOwned_zero_aligned hWT_s'
          have hout_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
            (R13Shards.ivl_allocated_bound hAs (Or.inl h.out_inside)).2
          have hout_u' : R13Shards.IvlUnhit s sb (w_out.toNat, 96) :=
            (R13Shards.heap_ivl_survives_step hAs hgrow_le hold0' hR0 hOG2' hFO2'
              h.out_words.1 h.out_words.2.1 h.out_inside c7
              (ptx_disj_bufRegions_of_disj_worldOwned hBnil c7)).2.2
          have hout_list' : memW sb (w_out.toNat + 16) = memW s (w_out.toNat + 16) := by
            apply R13Shards.memW_eq_of_ivlUnhit hout_u'
            · have := h.out_words.1; omega
            · exact hout_hi
            · constructor <;> omega
          have hout_list_surv' : memW s (w_out.toNat + 16) ≠ 0 →
              PmcLogsLiveOwned sb S2' N2' (memW s (w_out.toNat + 16)) := by
            intro hnz
            obtain ⟨hRh, hRa, hRe⟩ := pmcLogs_bufDisj hBnil c8 hnz
            exact PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow h.logs_ok c8 hsys
              hold0' hR0 hOG2' hFO2' hRh hRa hRe
          have hdisj_fresh_full : IvlsDisj
              [(lw.toNat, 24), (memW mid lw.toNat, eszw.toNat * capw.toNat)]
              (worldOwned mid S2' N2') := by
            simp only [locN, hent_e, hent_c] at hdisj_w'
            exact hdisj_w'
          have hm0m : memW mid lw.toNat = lw.toNat + 24 := hm0
          have hm8m : memW mid (lw.toNat + 8) = 0 := hm8
          have hobjs_sb' : lstObjects mid lw.toNat eszw.toNat =
              [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] := hobjs_sb
          have hobjs_props' : ∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
              Allocated mid i ∧ WordsOK mid i ∧
              Inside i (globN s "heap_ptr") (globN mid "heap_ptr") := hobjs_props
          have hsz8 : 8 ≤ eszw.toNat * capw.toNat := by
            have h1 : 1 * 1 ≤ eszw.toNat * capw.toNat := Nat.mul_le_mul hesz_pos hcap_pos
            have := hmul_al
            omega
          have hh : FreshBlock s mid lw.toNat 24 :=
            ⟨hlw_al, (hobjs_props' (lw.toNat, 24) (by rw [hobjs_sb']; simp)).2.2,
             (hobjs_props' (lw.toNat, 24) (by rw [hobjs_sb']; simp)).2.1⟩
          have harr := hobjs_props' (lw.toNat + 24, eszw.toNat * capw.toNat)
            (by rw [hobjs_sb']; simp)
          have hb8 : FreshBlock s mid (memW mid lw.toNat) 8 := by
            refine ⟨?_, ?_, ?_⟩
            · rw [hm0m]; omega
            · rw [hm0m]
              exact ⟨harr.2.2.1, by have := harr.2.2.2; omega⟩
            · rw [hm0m]
              obtain ⟨ha1, ha2, ha3⟩ := harr.2.1
              refine ⟨ha1, by omega, ?_⟩
              intro k hk
              have hk0 : k = 0 := by omega
              subst hk0
              exact ha3 0 (by have := hsz8; omega)
          have hd8 : IvlsDisj [(lw.toNat, 24), (memW mid lw.toNat, 8)]
              (worldOwned mid S2' N2') := by
            intro o ho j hj
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
            rcases ho with rfl | rfl
            · exact hdisj_fresh_full (lw.toNat, 24) (by simp) j hj
            · have hd := hdisj_fresh_full (memW mid lw.toNat, eszw.toNat * capw.toNat)
                (by simp) j hj
              dsimp only [Disj] at hd ⊢
              rcases hd with h | h | h | h
              · exact absurd h (by have := hsz8; omega)
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inl (by have := hsz8; omega)))
              · exact Or.inr (Or.inr (Or.inr h))
          have hfl' := PtxP34.fresh_empty_logs (s := s) (post := mid) (S := S2') (Nd := N2')
            (logs := lw.toNat) hAs hh hb8 hd8 hm8m
          refine ⟨S_pmc', Nd_pmc', S2', N2', c1, fun t ht => hs2' t (c2 t ht),
            (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals sb mid.locals mid.clock
              S2' N2').2 hWT_sb2', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact ptx_ownedGrows_trans h.heap_pmc hgrow_le c4 hOG2'
          · exact ptx_ownedGrows_trans h.base.heap_entry hgrow_le c5 hOG2'
          · exact ptx_frameOutside_trans h.base.arena_entry ⟨hgS, hAs⟩ h.base.heap_entry
              h.base.frame_entry h.base.scratch_entry c5
              (fun i hi => absurd hi (by simp)) c6 hFO2'
          · exact (R13Shards.heap_ivl_survives_step hAs hgrow_le hold0' hR0 hOG2' hFO2'
              h.out_words.1 h.out_words.2.1 h.out_inside c7
              (ptx_disj_bufRegions_of_disj_worldOwned hBnil c7)).2.1
          · rw [← hm0m]; exact hdisj_fresh_full
          · show PmcLogsLiveOwned sb S2' N2' (memW sb (w_out.toNat + 16))
            rw [hout_list']
            by_cases hnz : memW s (w_out.toNat + 16) = 0
            · rw [hnz]; exact pmcLogsLiveOwned_zero _ _ _
            · exact hout_list_surv' hnz
          · exact hfl'.2.1
        have hmid := htail lw
          (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals })
          hlw_eq hlw_al hlw_nz hm0 hm8 hm16 hhp_sb hhp_lt hAR_mid
          hsp_sb hfmp_sb hlst_sb hobjs_sb hdisj_sb hobjs_props hfr_sb hgl_sb hloc_name
          hloc_rest htychain hdata_mid (hmeta.trans hc) hres
        exact ptxWorldStep_strong_with_locals_right'
          (HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState
              (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals }) tail).2.locals
            (name, s.locals.lookup name))
          (evaluateHOLFiniteState
            (setVarHOLFinite name (.val (.word lw)) { sb with locals := s.locals }) tail).2.clock hmid

/-! ### The inst-22 engine: `call` binding the `logs` local from `lst_new(8,1)` -/

/-- The `.call` form of instruction 22 (`logs := lst_new(8, 1)`).  The fresh
list becomes the new `logs_facts` witness; the typing component is rebuilt
from the callee's `WorldStep` typing clause, whose `RetAvoidsIf` part
supplies disjointness of the fresh blocks from the new ownership witnesses. -/
theorem p4Run_call_local_lst_new {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (tail : ProgHOL 64)
    (htail : ∀ (lw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw.toNat = globN s "heap_ptr" →
      lw.toNat % 8 = 0 →
      lw.toNat ≠ 0 →
      memW mid lw.toNat = lw.toNat + 24 →
      memW mid (lw.toNat + 8) = 0 →
      memW mid (lw.toNat + 16) = 1 →
      globN mid "heap_ptr" = lw.toNat + 24 + 8 →
      globN s "heap_ptr" < globN mid "heap_ptr" →
      ArenaReady mid →
      globN mid "scratch_ptr" = globN s "scratch_ptr" →
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" →
      LstOK mid lw.toNat →
      lstObjects mid lw.toNat 8 = [(lw.toNat, 24), (lw.toNat + 24, 8)] →
      Disj (lw.toNat, 24) (lw.toNat + 24, 8) →
      (∀ i ∈ lstObjects mid lw.toNat 8,
        Allocated mid i ∧ WordsOK mid i ∧
        Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) →
      FrameOutside s mid [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") →
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) →
      mid.locals.lookup (ofString "logs") = some (.val (.word lw)) →
      (∀ y, y ≠ ofString "logs" → mid.locals.lookup y = s.locals.lookup y) →
      LogsListOK mid lw.toNat →
      LogsDisjFixed mid lw.toNat →
      P4Data entry mid s_pmc w_out →
      mid.code = originalRuntimeCode →
      PtxRelRunStrong entry tail mid) :
    PtxRelRunStrong entry
      (.seq (.call (some (some (.local, ofString "logs"), none)) (ofString "lst_new")
        [(.const 0x0000000000000008#64), (.const 0x0000000000000001#64)]) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hres ⊢
  have harg : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [(.const 0x0000000000000008#64), (.const 0x0000000000000001#64)] =
      some [.val (.word 0x0000000000000008#64), .val (.word 0x0000000000000001#64)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  rw [harg] at hres ⊢
  dsimp only at hres ⊢
  have hlk := pan_two_word_lookup s.code.lookup (ofString "lst_new") (ofString "esz")
    (ofString "cap") (sourceFnBody Guest.Software.guestFn_lst_new)
    0x0000000000000008#64 0x0000000000000001#64
    (by decide) (by rw [hc]; exact WkBal.lookup_lst_new_wk)
  rw [hlk] at hres ⊢
  dsimp only at hres ⊢
  by_cases hcz : s.clock = 0
  · simp only [hcz, ↓reduceIte] at hres
    exact absurd hres (by rintro (⟨_, hh⟩ | ⟨_, _, hh, _⟩) <;> simp at hh)
  · simp only [hcz, ↓reduceIte] at hres ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "esz", ValueHOL.val (.word 0x0000000000000008#64))).update
      (ofString "cap", ValueHOL.val (.word 0x0000000000000001#64)) with hcmap_def
    have hAR_ent : ArenaReady (callEntryStateHOLFinite s cmap) :=
      (arenaReady_with_locals s cmap (s.clock - 1)).2 h.base.world.1
    have hent_e : (callEntryStateHOLFinite s cmap).locals.lookup (ofString "esz") =
        some (.val (.word 0x0000000000000008#64)) := by
      simp [callEntryStateHOLFinite, hcmap_def, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "cap" ≠ ofString "esz" by decide]
    have hent_c : (callEntryStateHOLFinite s cmap).locals.lookup (ofString "cap") =
        some (.val (.word 0x0000000000000001#64)) := by
      simp [callEntryStateHOLFinite, hcmap_def, HolFiniteMapExact.lookup_update, FUPDATE]
    have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite s cmap) (sourceFnBody Guest.Software.guestFn_lst_new)).1
    rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_lst_new) with ⟨rb, sb⟩
    have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_lst_new) = (rb, sb) := hb
    rw [hb] at hmeta
    simp only [hb] at hres ⊢
    cases rb with
    | none => exact absurd hres (by rintro (⟨_, hh⟩ | ⟨_, _, hh, _⟩) <;> simp at hh)
    | some cr =>
      cases cr with
      | timeOut | error | «break» | «continue» | finalFfi _ =>
        exact absurd hres (by rintro (⟨_, hh⟩ | ⟨_, _, hh, _⟩) <;> simp at hh)
      | exception eid ev =>
        exfalso
        rcases hres with ⟨v', hv⟩ | ⟨e', ev', hv, hne⟩
        · simp at hv
        · exact WkBal.lst_new_no_catchable_exn (callEntryStateHOLFinite s cmap) hAR_ent.1.code
            e' ev' hne (by rw [hb']; exact hv)
      | returned v =>
        dsimp only at hres ⊢
        have hprops := WkBal.lst_new_heap_props (callEntryStateHOLFinite s cmap)
          0x0000000000000008#64 0x0000000000000001#64
          hAR_ent (by decide) (by decide) (by decide) (by decide)
          hent_e hent_c v (congrArg Prod.fst hb')
        have hrun_snd : (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
            (sourceFnBody Guest.Software.guestFn_lst_new)).2 = sb := congrArg Prod.snd hb'
        dsimp only at hprops
        rw [hrun_snd] at hprops
        obtain ⟨lw, rfl, hlw_eq, hlw_al, hlw_nz, hm0, hm8, hm16, hhp_sb, hhp_lt, hAsb, hbe_sb,
          hsp_sb, hfmp_sb, hlst_sb, hobjs_sb, hdisj_sb, hobjs_props, hfr_sb, hgl_sb⟩ := hprops
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word lw) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hres ⊢
        by_cases hvalid : isValidValueHOLExact s.toExact VarKind.local (ofString "logs")
            (.val (.word lw)) = true
        · simp only [hvalid, ↓reduceIte] at hres ⊢
          have hspec := PtxP1.funSpec_at_lookup R13Wk06b.«wk_lst_new» s hc
            [.val (.word 0x0000000000000008#64), .val (.word 0x0000000000000001#64)]
            (sourceFnBody Guest.Software.guestFn_lst_new)
            cmap .one hlk (PtxP1.worldOK_callEntry h.base.world cmap)
            (by rw [hb']; simp)
          rw [hb'] at hspec
          have hstep_ent := hspec (Or.inl ⟨(.val (.word lw) : ValueHOL 64), rfl⟩)
          have hstep_s : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra
              s (some (.returned (.val (.word lw)))) sb :=
            R13Shards.worldStep_with_locals hstep_ent s.locals s.clock
          have hsp : globN sb "scratch_ptr" ≤ globN s "scratch_ptr" := Nat.le_of_eq hsp_sb
          have hgS : GuestInv s := h.base.world.1.1
          have hAs : ArenaOK s := h.base.world.1.2
          have hAp : ArenaOK sb := hAsb.2
          have hgrow : AllocatorGrows s sb := ⟨Nat.le_of_lt hhp_lt, hsp⟩
          have hsys : globN sb "vm_system_address" = globN s "vm_system_address" :=
            globN_eq_of_lookup (hgl_sb (ofString "vm_system_address") (by decide))
          obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
            S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
          have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
            rw [ptxRegions_eq_bufRegions]
            exact validBufList_disj validBufList_ptxBufs hWT_e
          obtain ⟨logs, hll, hl_ok, hl_dj, hty⟩ := h.logs_facts
          obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hty1, hty2, hWT_s, hty4, hty5, hty6, hty7, hty8,
            hty9⟩ := hty S_e Nd_e hWT_e hD_e
          have hunhit : PtxBlockOutUnhit s sb :=
            ptxBlockOutUnhit_of_fresh_heap hWT_s h.base.world.1 hAsb hfr_sb
          have hBnil : ValidBufList ([] : BufList) := fun p hp => absurd hp (by simp)
          have hcells : PtxBoCells true entry s sb :=
            ptxBoCells_of_blockOutUnhit h.base (B := ([] : BufList)) (gw := ["heap_ptr"])
              (keep := stdKeep)
              (fun p hp => absurd hp (by simp))
              (fun p hp => absurd hp (by simp))
              (fun g hg => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
                subst hg
                decide)
              ptxKeepSub_stdKeep
              (by decide)
              (Or.inr (by simp [stdKeep]))
              hstep_s hunhit
          have hdata_sb : P4Data entry { sb with locals := s.locals, clock := sb.clock } s_pmc w_out :=
            p4Data_step_of_worldStep_cells h (B := ([] : BufList)) (gw := ["heap_ptr"])
              (keep := stdKeep)
              (fun p hp => absurd hp (by simp))
              (fun p hp => absurd hp (by simp))
              (fun g hg => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
                subst hg
                decide)
              (by decide) (by decide) ptxKeepSub_stdKeep
              hstep_s hsp hcells
          have hWT_ent : WorldTypedWith (callEntryStateHOLFinite s cmap) S_cur Nd_cur :=
            (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s cmap (s.clock - 1)
              S_cur Nd_cur).2 hWT_s
          have hC : locN (callEntryStateHOLFinite s cmap) "esz" *
              locN (callEntryStateHOLFinite s cmap) "cap" < 2 ^ 64 := by
            simp only [locN, hent_e, hent_c]
            decide
          have hold0 : ∀ j ∈ worldOwned s S_cur Nd_cur, j.2 = 0 → j.1 % 8 = 0 :=
            R13Shards.worldOwned_zero_aligned hWT_s
          have hR0 : ∀ j ∈ ([] : List Ivl), j.2 = 0 → j.1 % 8 = 0 := fun j hj =>
            absurd hj (by simp)
          have hgrow_le : globN s "heap_ptr" ≤ globN sb "heap_ptr" := Nat.le_of_lt hhp_lt
          set mid := setVarHOLFinite (ofString "logs") (.val (.word lw))
            { sb with locals := s.locals } with hmid_def
          have hloc_name : mid.locals.lookup (ofString "logs") = some (.val (.word lw)) := by
            rw [hmid_def]
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hloc_rest : ∀ y, y ≠ ofString "logs" → mid.locals.lookup y = s.locals.lookup y := by
            intro y hy
            rw [hmid_def]
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy]
          have hAR_mid : ArenaReady mid := (arenaReady_with_locals sb _ sb.clock).2 hAsb
          have hm0' : memW mid lw.toNat = lw.toNat + 24 := hm0
          have hobjs_sb' : lstObjects mid lw.toNat 8 =
              [(lw.toNat, 24), (lw.toNat + 24, 8)] := hobjs_sb
          have hobjs_props' : ∀ i ∈ lstObjects mid lw.toNat 8,
              Allocated mid i ∧ WordsOK mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr") :=
            hobjs_props
          have hh : FreshBlock s mid lw.toNat 24 :=
            ⟨hlw_al,
             (hobjs_props' (lw.toNat, 24) (by rw [hobjs_sb']; simp)).2.2,
             (hobjs_props' (lw.toNat, 24) (by rw [hobjs_sb']; simp)).2.1⟩
          have hb : FreshBlock s mid (memW mid lw.toNat) 8 :=
            ⟨by rw [hm0']; omega,
             by rw [hm0']; exact (hobjs_props' (lw.toNat + 24, 8) (by rw [hobjs_sb']; simp)).2.2,
             by rw [hm0']; exact (hobjs_props' (lw.toNat + 24, 8) (by rw [hobjs_sb']; simp)).2.1⟩
          -- canonical RetAvoids instantiation
          obtain ⟨S2, N2, hsub2, hWT_sb2, hOG2, hFO2, hQ2⟩ :=
            hstep_ent.2.2.2.2 S_cur Nd_cur hWT_ent
              (by intro o ho j hj; exact absurd ho (by simp))
          obtain ⟨w, hw, hdisj_w⟩ := hQ2 hC (.val (.word lw)) rfl
          have hwl : w = lw := by
            injection hw with h1
            injection h1 with h2
            exact h2.symm
          rw [hwl] at hdisj_w
          have hdisj_fresh : IvlsDisj [(lw.toNat, 24), (memW mid lw.toNat, 8)]
              (worldOwned mid S2 N2) := by
            simp only [locN, hent_e, hent_c] at hdisj_w
            exact hdisj_w
          have hfl := PtxP34.fresh_empty_logs (s := s) (post := mid) (S := S2) (Nd := N2)
            (logs := lw.toNat) hAs hh hb hdisj_fresh hm8
          -- the rebuilt typing component (arbitrary entry witnesses)
          have hout_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
            (R13Shards.ivl_allocated_bound hAs (Or.inl h.out_inside)).2
          have htyComp : ∀ S0 Nd0, WorldTypedWith entry S0 Nd0 →
              IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
              ∃ S_pmc' Nd_pmc' S_new Nd_new,
                WorldTypedWith s_pmc S_pmc' Nd_pmc' ∧
                (∀ t ∈ S0, t ∈ S_new) ∧
                WorldTypedWith mid S_new Nd_new ∧
                OwnedGrows s_pmc mid (worldOwned s_pmc S_pmc' Nd_pmc')
                  (worldOwned mid S_new Nd_new) ∧
                OwnedGrows entry mid (worldOwned entry S0 Nd0)
                  (worldOwned mid S_new Nd_new) ∧
                FrameOutside entry mid
                  (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry])
                  (heapFree entry) ∧
                (∀ o ∈ worldOwned mid S_new Nd_new, Disj (w_out.toNat, 96) o) ∧
                PmcLogsLiveOwned mid S_new Nd_new (memW mid (w_out.toNat + 16)) ∧
                PmcLogsLiveOwned mid S_new Nd_new lw.toNat := by
            intro S0 Nd0 hWT0 hD0
            obtain ⟨S_pmc', Nd_pmc', S_cur', Nd_cur', c1, c2, hWT_s', c4, c5, c6, c7, c8, c9⟩ :=
              hty S0 Nd0 hWT0 hD0
            obtain ⟨S2', N2', hs2', hWT_sb2', hOG2', hFO2', hQ2'⟩ :=
              hstep_ent.2.2.2.2 S_cur' Nd_cur'
                ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s cmap (s.clock - 1)
                  S_cur' Nd_cur').2 hWT_s')
                (by intro o ho j hj; exact absurd ho (by simp))
            have hold0' : ∀ j ∈ worldOwned s S_cur' Nd_cur', j.2 = 0 → j.1 % 8 = 0 :=
              R13Shards.worldOwned_zero_aligned hWT_s'
            have hout_u' : R13Shards.IvlUnhit s sb (w_out.toNat, 96) :=
              (R13Shards.heap_ivl_survives_step hAs hgrow_le hold0' hR0 hOG2' hFO2'
                h.out_words.1 h.out_words.2.1 h.out_inside c7
                (ptx_disj_bufRegions_of_disj_worldOwned hBnil c7)).2.2
            have hout_list' : memW sb (w_out.toNat + 16) = memW s (w_out.toNat + 16) := by
              apply R13Shards.memW_eq_of_ivlUnhit hout_u'
              · have := h.out_words.1; omega
              · exact hout_hi
              · constructor <;> omega
            have hout_list_surv' : memW s (w_out.toNat + 16) ≠ 0 →
                PmcLogsLiveOwned sb S2' N2' (memW s (w_out.toNat + 16)) := by
              intro hnz
              obtain ⟨hRh, hRa, hRe⟩ := pmcLogs_bufDisj hBnil c8 hnz
              exact PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow h.logs_ok c8 hsys
                hold0' hR0 hOG2' hFO2' hRh hRa hRe
            obtain ⟨w', hw', hdisj_w'⟩ := hQ2' hC (.val (.word lw)) rfl
            have hwl' : w' = lw := by
              injection hw' with h1
              injection h1 with h2
              exact h2.symm
            rw [hwl'] at hdisj_w'
            have hdisj_fresh' : IvlsDisj [(lw.toNat, 24), (memW mid lw.toNat, 8)]
                (worldOwned mid S2' N2') := by
              simp only [locN, hent_e, hent_c] at hdisj_w'
              exact hdisj_w'
            have hfl' := PtxP34.fresh_empty_logs (s := s) (post := mid) (S := S2') (Nd := N2')
              (logs := lw.toNat) hAs hh hb hdisj_fresh' hm8
            refine ⟨S_pmc', Nd_pmc', S2', N2', c1, fun t ht => hs2' t (c2 t ht), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals sb mid.locals mid.clock
                S2' N2').2 hWT_sb2'
            · exact ptx_ownedGrows_trans h.heap_pmc hgrow_le c4 hOG2'
            · exact ptx_ownedGrows_trans h.base.heap_entry hgrow_le c5 hOG2'
            · exact ptx_frameOutside_trans h.base.arena_entry ⟨hgS, hAs⟩ h.base.heap_entry
                h.base.frame_entry h.base.scratch_entry c5
                (fun i hi => absurd hi (by simp)) c6 hFO2'
            · exact (R13Shards.heap_ivl_survives_step hAs hgrow_le hold0' hR0 hOG2' hFO2'
                h.out_words.1 h.out_words.2.1 h.out_inside c7
                (ptx_disj_bufRegions_of_disj_worldOwned hBnil c7)).2.1
            · show PmcLogsLiveOwned sb S2' N2' (memW sb (w_out.toNat + 16))
              rw [hout_list']
              by_cases hnz : memW s (w_out.toNat + 16) = 0
              · rw [hnz]; exact pmcLogsLiveOwned_zero _ _ _
              · exact hout_list_surv' hnz
            · exact hfl'.2.1
          have hdata_mid : P4Data entry mid s_pmc w_out :=
            ⟨ptxRelBase_with_locals hdata_sb.base mid.locals mid.clock,
             hdata_sb.arena_pmc, hdata_sb.heap_pmc,
             (by rw [hmid_def]
                 simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                   show ofString "out" ≠ ofString "logs" by decide]
                 exact hdata_sb.out_local),
             hdata_sb.out_words, hdata_sb.out_inside, hdata_sb.marks, hdata_sb.logs_ok,
             ptxPhase4LocalShapes_setVar
               (by intro nm' hnm'
                   simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm'
                   rcases hnm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
               hdata_sb.shapes,
             (by rw [hmid_def]
                 simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                   show ofString "tx" ≠ ofString "logs" by decide]
                 exact hdata_sb.tx_local),
             (by rw [hmid_def]
                 simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                   show ofString "index" ≠ ofString "logs" by decide]
                 exact hdata_sb.idx_local),
              ⟨lw.toNat, Or.inl (by simp [locN, hloc_name]),
                hfl.1, hfl.2.2, htyComp⟩⟩
          exact htail lw mid hlw_eq hlw_al hlw_nz hm0 hm8 hm16 hhp_sb hhp_lt hAR_mid
            hsp_sb hfmp_sb hlst_sb hobjs_sb' hdisj_sb hobjs_props' hfr_sb hgl_sb hloc_name
            hloc_rest hfl.1 hfl.2.2 hdata_mid (hmeta.trans hc) hres
        · simp only [hvalid, Bool.false_eq_true, ↓reduceIte] at hres
          exact absurd hres (by rintro (⟨_, hh⟩ | ⟨_, _, hh, _⟩) <;> simp at hh)
