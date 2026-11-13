import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q6T2

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

/-! # Phase 4Q6T: the g8 tail — receipt-list push and slot store

Instructions 39–40 of the g8 epilogue: `rl := lst_push(load (bo + 72), 8)`
followed by `store rl := stable_logs`.  From the loop-exit bundle
`P4Q8Exit` the two instructions establish `PtxAfterPhase4`, the entry
invariant of the remaining program.

`PtxRelBase` does not survive the push (the receipt-list length grows), so
the state between the two instructions is described by the dedicated
invariant `P4Q8TMid`. -/

/-- The state invariant between the receipt-list push and the slot store:
`l` is the receipt-list header, `w` the freshly pushed slot. -/
structure P4Q8TMid {F : Type} (entry s_pmc : PanSemStateFiniteExact 64 F)
    (w_out lw w : BitVec 64) (l : Nat) (u : PanSemStateFiniteExact 64 F) : Prop where
  ready_entry : TxReadyStrong entry
  arena_entry : ArenaReady entry
  arena_pmc : ArenaReady s_pmc
  frame_entry : globN entry "frame_mem_ptr" ≤ globN u "frame_mem_ptr"
  scratch_entry : globN u "scratch_ptr" ≤ globN entry "scratch_ptr"
  world : WorldOK u
  heap_entry : globN entry "heap_ptr" ≤ globN u "heap_ptr"
  heap_pmc : globN s_pmc "heap_ptr" ≤ globN u "heap_ptr"
  globals : GlobalsKept ptxGlobals entry u
  records : RecordsKept ptxRegions ptxKeep entry u
  chain : p4Q8ChainX entry s_pmc w_out lw u
  out_words : WordsOK u (w_out.toNat, 96)
  out_inside : Inside (w_out.toNat, 96) sourceBase (globN u "heap_ptr")
  out_hi : w_out.toNat + 96 ≤ 2 ^ 64
  marks : memW u (w_out.toNat + 80) ≠ 0 →
    memW u (w_out.toNat + 80) % 8 = 0 ∧
      memW u (w_out.toNat + 88) % 8 = 0 ∧
        globN s_pmc "frame_mem_ptr" ≤ memW u (w_out.toNat + 88) ∧
          memW u (w_out.toNat + 88) ≤ memW u (w_out.toNat + 80) ∧
            memW u (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr"
  l_eq : l = memW u (globN u "bo" + 72)
  backing : memW u l ≠ 0
  len_eq : memW u (l + 8) = memW entry (memW entry (globN entry "bo" + 72) + 8) + 1
  slot_in : Inside (w.toNat, 8) (memW u l) (memW u l + 8 * memW u (l + 16))
  slot_eq : w.toNat = memW u l + 8 * memW entry (memW entry (globN entry "bo" + 72) + 8)
  slices_prev : ∀ off ∈ ([24, 32] : List Nat), ∀ i < locN entry "index",
    memW u (memW u (globN u "bo" + off) + 16 * i + 8) =
      memW entry (memW entry (globN entry "bo" + off) + 16 * i + 8)
  slices_cur : ∀ off ∈ ([24, 32] : List Nat),
    memW u (memW u (globN u "bo" + off) + 16 * locN entry "index" + 8) < 2 ^ 40

/-- The mid invariant does not mention the locals or the clock. -/
theorem p4Q8TMid_with_locals {F : Type}
    {entry s_pmc u : PanSemStateFiniteExact 64 F} {w_out lw w : BitVec 64} {l : Nat}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : P4Q8TMid entry s_pmc w_out lw w l u) :
    P4Q8TMid entry s_pmc w_out lw w l {u with locals := L, clock := k} :=
  { ready_entry := h.ready_entry
    arena_entry := h.arena_entry
    arena_pmc := h.arena_pmc
    frame_entry := h.frame_entry
    scratch_entry := h.scratch_entry
    world := localsFree_worldOK u L k h.world
    heap_entry := h.heap_entry
    heap_pmc := h.heap_pmc
    globals := h.globals
    records := h.records
    chain := p4Q8ChainX_with_locals L k h.chain
    out_words := h.out_words
    out_inside := h.out_inside
    out_hi := h.out_hi
    marks := h.marks
    l_eq := h.l_eq
    backing := h.backing
    len_eq := h.len_eq
    slot_in := h.slot_in
    slot_eq := h.slot_eq
    slices_prev := h.slices_prev
    slices_cur := h.slices_cur }

/-- The receipt-list push establishes the mid invariant at the callee's
post state. -/
theorem p4Q8T_mid_of_push {F : Type}
    {entry s_pmc t post : PanSemStateFiniteExact 64 F}
    {w_out lw capw nl_w w w_l : BitVec 64}
    (h : P4Q8Exit entry s_pmc w_out lw capw nl_w t)
    (hl : w_l.toNat = memW t (globN t "bo" + 72))
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (w_l.toNat, 24) →
      ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree t) →
      post.memory a = t.memory a)
    (hin : Inside (w.toNat, 8) (memW post w_l.toNat)
      (memW post w_l.toNat + 8 * memW post (w_l.toNat + 16)))
    (hlen : memW post (w_l.toNat + 8) = memW t (w_l.toNat + 8) + 1)
    (hslot : w.toNat = memW post w_l.toNat + 8 * memW t (w_l.toNat + 8))
    (hback : memW post w_l.toNat ≠ 0)
    (hstep : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra t
      (some (.returned (.val (.word w)))) post) :
    P4Q8TMid entry s_pmc w_out lw w w_l.toNat post := by
  obtain ⟨⟨_, hbo_nz_e, _, _, _⟩, _, _, _, S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  have hEt : TxEnv t := p4Q8_txEnv_of_base h.base h.idx_local
  have hX_t : p4Q8ChainX entry s_pmc w_out lw t := p4Q8ChainX_of_exit h
  obtain ⟨S_t, N_t, _, _, _, hWT_t, _⟩ := hX_t S_e Nd_e hWT_e hD_e
  have hAR_t : ArenaReady t := h.base.world.1
  obtain ⟨hg_p, hr_p⟩ := p4Q8T_keep_step h.base.globals h.base.records
    (by intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        subst hg; decide) hstep
  obtain ⟨S_p, N_p, _, hWT_p, _, _, _⟩ :=
    hstep.2.2.2.2 S_t N_t hWT_t (by intro i hi; cases hi)
  have hW_p : WorldOK post := ⟨hstep.1, S_p, (worldTyped_iff_with _ S_p).2 ⟨N_p, hWT_p⟩⟩
  have hw8 : w_out.toNat % 8 = 0 := h.out_words.1
  have hX_p : p4Q8ChainX entry s_pmc w_out lw post :=
    p4Q8ChainX_worldStep hX_t h.base.world h.heap_pmc h.base.heap_entry h.base.frame_entry
      h.base.scratch_entry h.base.arena_entry hw8 h.out_inside hstep (Or.inr rfl)
  have hfp : globN post "frame_mem_ptr" = globN t "frame_mem_ptr" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "frame_mem_ptr") (by decide))
  have hsp : globN post "scratch_ptr" = globN t "scratch_ptr" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "scratch_ptr") (by decide))
  have hout_hi : w_out.toNat + 96 ≤ 2 ^ 64 := by
    have h1 := h.out_below
    have h2 := h.lim64
    omega
  have hunhit : R13Shards.IvlUnhit t post (w_out.toNat, 96) :=
    p4Q8T_out_unhit hX_t hWT_e hD_e hAR_t.2 hw8 h.out_inside hstep
  have hm80 : memW post (w_out.toNat + 80) = memW t (w_out.toNat + 80) :=
    R13Shards.memW_eq_of_ivlUnhit hunhit (by omega) hout_hi
      ⟨by show w_out.toNat ≤ w_out.toNat + 80; omega,
       by show w_out.toNat + 80 + 8 ≤ w_out.toNat + 96; omega⟩
  have hm88 : memW post (w_out.toNat + 88) = memW t (w_out.toNat + 88) :=
    R13Shards.memW_eq_of_ivlUnhit hunhit (by omega) hout_hi
      ⟨by show w_out.toNat ≤ w_out.toNat + 88; omega,
       by show w_out.toNat + 88 + 8 ≤ w_out.toNat + 96; omega⟩
  have hbo_f : ∀ off ∈ ([24, 32, 72] : List Nat),
      memW post (globN post "bo" + off) = memW t (globN t "bo" + off) := by
    intro off hoff
    have hoff' : off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat) ∧ off + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl <;> decide
    exact (ptx_entry_bo_field_eq hWT_e hg_p hr_p hbo_nz_e hoff'.1 hoff'.2).trans
      (ptx_entry_bo_field_eq hWT_e h.base.globals h.base.records hbo_nz_e
        hoff'.1 hoff'.2).symm
  have hsub : ∀ off ∈ ([24, 32] : List Nat), off ∈ ([24, 32, 72] : List Nat) := by
    intro off ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  have hidx_t : locN t "index" = locN entry "index" := by simp only [locN, h.idx_local]
  have hsl := p4Q8T_calleeSlices (entry := entry) hAR_t hEt hWT_t hidx_t hl hmem
  have hslice : ∀ off ∈ ([24, 32] : List Nat), ∀ i ≤ locN entry "index",
      memW post (memW post (globN post "bo" + off) + 16 * i + 8) =
        memW t (memW t (globN t "bo" + off) + 16 * i + 8) := by
    intro off hoff i hi
    rw [hbo_f off (hsub off hoff)]
    exact hsl off hoff i hi
  have hlen_t : memW t (w_l.toNat + 8) =
      memW entry (memW entry (globN entry "bo" + 72) + 8) := by
    rw [hl]; exact h.base.rcpt_len_eq
  exact
    { ready_entry := h.base.ready_entry
      arena_entry := h.base.arena_entry
      arena_pmc := h.arena_pmc
      frame_entry := by rw [hfp]; exact h.base.frame_entry
      scratch_entry := by rw [hsp]; exact h.base.scratch_entry
      world := hW_p
      heap_entry := Nat.le_trans h.base.heap_entry hstep.2.1
      heap_pmc := Nat.le_trans h.heap_pmc hstep.2.1
      globals := hg_p
      records := hr_p
      chain := hX_p
      out_words := R13Shards.wordsOK_transfer hAR_t.1 hstep.1.1 h.out_words
      out_inside := ⟨h.out_inside.1, Nat.le_trans h.out_inside.2 hstep.2.1⟩
      out_hi := hout_hi
      marks := by
        intro hne
        rw [hm80] at hne ⊢
        rw [hm88]
        exact h.marks hne
      l_eq := hl.trans (hbo_f 72 (by decide)).symm
      backing := hback
      len_eq := by rw [hlen, hlen_t]
      slot_in := hin
      slot_eq := by rw [← hlen_t]; exact hslot
      slices_prev := fun off hoff i hi =>
        (hslice off hoff i (Nat.le_of_lt hi)).trans (h.base.slices_prev off hoff i hi)
      slices_cur := by
        intro off hoff
        refine lt_of_eq_of_lt (hslice off hoff _ (Nat.le_refl _)) ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl
        · exact h.base.tx_slice_cur rfl
        · exact h.rcpt_cur }

/-- The slot store from a mid state is a typed, empty-region `stdKeep`
step. -/
theorem p4Q8T_storeStep {F : Type}
    {entry s_pmc u : PanSemStateFiniteExact 64 F} {w_out lw w : BitVec 64} {l : Nat}
    {mem' : RiscV.Word 64 → HolWordLab 64}
    (hmid : P4Q8TMid entry s_pmc w_out lw w l u)
    (hidx_u : u.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index"))
    (hx : u.memaddrs w)
    (hm : ∀ a, a ≠ w → mem' a = u.memory a) :
    WorldStep (fun _ => []) [] stdKeep NoExtra u none {u with memory := mem'} := by
  obtain ⟨_, _, _, _, S_e, Nd_e, hWT_e, _⟩ := hmid.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  have hE : TxEnv u := p4Q8T_txEnv hmid.ready_entry hmid.globals hmid.records hidx_u
  obtain ⟨S_u, N_u, _, _, _, hWT_u, _⟩ := hmid.chain S_e Nd_e hWT_e hD_e
  exact p4Loop31_storeWorldStep (p4Loop31_arenaStored hmid.world.1) hm
    (fun S Nd hWT _ =>
      p4Q8T_hty hmid.world.1 hE hmid.l_eq hmid.backing hmid.slot_in hx hm S Nd hWT)
    (p4Q8T_hrecStd hmid.world.1 hE hWT_u hmid.l_eq hmid.backing hmid.slot_in hm)

/-- The slot store of the fresh `stable_logs` list turns the mid invariant
into `PtxAfterPhase4`. -/
theorem p4Q8T_after_store {F : Type}
    {entry s_pmc u s5 : PanSemStateFiniteExact 64 F} {w_out lw w : BitVec 64} {l : Nat}
    (hmid : P4Q8TMid entry s_pmc w_out lw w l u)
    (hidx_u : u.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index"))
    (hout5 : s5.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hi5 : ∃ wi : BitVec 64, s5.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hstep : WorldStep (fun _ => []) [] stdKeep NoExtra u none s5)
    (hmw : ∀ k : Nat, BitVec.ofNat 64 k ≠ w → memW s5 k = memW u k)
    (hw5 : memW s5 w.toNat = lw.toNat) :
    PtxAfterPhase4 entry s5 := by
  obtain ⟨⟨_, hbo_nz_e, _, _, _⟩, _, _, _, S_e, Nd_e, hWT_e, _⟩ := hmid.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  have hE : TxEnv u := p4Q8T_txEnv hmid.ready_entry hmid.globals hmid.records hidx_u
  have hAR : ArenaReady u := hmid.world.1
  obtain ⟨S_u, N_u, _, _, _, hWT_u, _⟩ := hmid.chain S_e Nd_e hWT_e hD_e
  obtain ⟨hg5, hr5⟩ := p4Q8T_keep_step hmid.globals hmid.records
    (by intro g hg; cases hg) hstep
  have hw8 : w_out.toNat % 8 = 0 := hmid.out_words.1
  have hX5 : p4Q8ChainX entry s_pmc w_out lw s5 :=
    p4Q8ChainX_worldStep hmid.chain hmid.world hmid.heap_pmc hmid.heap_entry
      hmid.frame_entry hmid.scratch_entry hmid.arena_entry hw8 hmid.out_inside hstep
      (Or.inl rfl)
  obtain ⟨S5, N5, _, _, _, hWT5, _⟩ := hX5 S_e Nd_e hWT_e hD_e
  have hW5 : WorldOK s5 := ⟨hstep.1, S5, (worldTyped_iff_with _ S5).2 ⟨N5, hWT5⟩⟩
  have hfp : globN s5 "frame_mem_ptr" = globN u "frame_mem_ptr" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "frame_mem_ptr") (by simp))
  have hsp : globN s5 "scratch_ptr" = globN u "scratch_ptr" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "scratch_ptr") (by simp))
  have hunhit : R13Shards.IvlUnhit u s5 (w_out.toNat, 96) :=
    p4Q8T_out_unhit hmid.chain hWT_e hD_e hAR.2 hw8 hmid.out_inside hstep
  have hout_hi := hmid.out_hi
  have hm80 : memW s5 (w_out.toNat + 80) = memW u (w_out.toNat + 80) :=
    R13Shards.memW_eq_of_ivlUnhit hunhit (by omega) hout_hi
      ⟨by show w_out.toNat ≤ w_out.toNat + 80; omega,
       by show w_out.toNat + 80 + 8 ≤ w_out.toNat + 96; omega⟩
  have hm88 : memW s5 (w_out.toNat + 88) = memW u (w_out.toNat + 88) :=
    R13Shards.memW_eq_of_ivlUnhit hunhit (by omega) hout_hi
      ⟨by show w_out.toNat ≤ w_out.toNat + 88; omega,
       by show w_out.toNat + 88 + 8 ≤ w_out.toNat + 96; omega⟩
  have hidx : locN u "index" = locN entry "index" := by simp only [locN, hidx_u]
  have hientry : locN entry "index" < memW u (globN u "bo" + 80) := by
    rw [← hidx]; exact hE.idx_lt
  obtain ⟨⟨hmiss_l, hmiss_l8⟩, hmiss_sl⟩ :=
    p4Q8T_storeMisses (entry := entry) hAR hE hWT_u hmid.l_eq hmid.backing hientry
      hmid.slot_in
  have hbo_f : ∀ off ∈ ([24, 32, 72] : List Nat),
      memW s5 (globN s5 "bo" + off) = memW u (globN u "bo" + off) := by
    intro off hoff
    have hoff' : off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat) ∧ off + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl <;> decide
    exact (ptx_entry_bo_field_eq hWT_e hg5 hr5 hbo_nz_e hoff'.1 hoff'.2).trans
      (ptx_entry_bo_field_eq hWT_e hmid.globals hmid.records hbo_nz_e
        hoff'.1 hoff'.2).symm
  have hsub : ∀ off ∈ ([24, 32] : List Nat), off ∈ ([24, 32, 72] : List Nat) := by
    intro off ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  have h72 : memW s5 (globN s5 "bo" + 72) = l :=
    (hbo_f 72 (by decide)).trans hmid.l_eq.symm
  have hl5 : memW s5 l = memW u l := hmw l hmiss_l
  have hl8_5 : memW s5 (l + 8) = memW u (l + 8) := hmw (l + 8) hmiss_l8
  have hslice : ∀ off ∈ ([24, 32] : List Nat), ∀ i ≤ locN entry "index",
      memW s5 (memW s5 (globN s5 "bo" + off) + 16 * i + 8) =
        memW u (memW u (globN u "bo" + off) + 16 * i + 8) := by
    intro off hoff i hi
    rw [hbo_f off (hsub off hoff)]
    exact hmw _ (hmiss_sl off hoff i hi)
  refine ⟨hmid.ready_entry, s_pmc, w_out, ?_⟩
  refine
    { arena_pmc := hmid.arena_pmc
      arena_entry := hmid.arena_entry
      frame_entry := by rw [hfp]; exact hmid.frame_entry
      scratch_entry := by rw [hsp]; exact hmid.scratch_entry
      world := hW5
      heap_entry := Nat.le_trans hmid.heap_entry hstep.2.1
      heap_pmc := Nat.le_trans hmid.heap_pmc hstep.2.1
      globals := hg5
      records := hr5
      out_local := hout5
      out_words := R13Shards.wordsOK_transfer hAR.1 hstep.1.1 hmid.out_words
      out_inside := ⟨hmid.out_inside.1, Nat.le_trans hmid.out_inside.2 hstep.2.1⟩
      marks := ?_
      index_word := hi5
      rcpt_backing := ?_
      typing := ?_ }
  · intro hne
    rw [hm80] at hne ⊢
    rw [hm88]
    exact hmid.marks hne
  · rw [h72, hl5]
    exact hmid.backing
  · intro S0 Nd0 hWT0 hD0
    obtain ⟨S, N, Sp, Np, hsub', hWT, hWTp, hOGp, hOGe, hFO, hout, hlogs⟩ :=
      hX5 S0 Nd0 hWT0 hD0
    refine ⟨Sp, Np, S, N, hWTp, hsub', hWT, hOGp, hOGe, hFO, hout, ?_, ?_⟩
    · intro i hi1 hi2
      rw [h72] at hi2 ⊢
      rw [hl8_5, hmid.len_eq] at hi2
      have hi : i = memW entry (memW entry (globN entry "bo" + 72) + 8) := by omega
      rw [hi, hl5, ← hmid.slot_eq, hw5]
      exact hlogs
    · intro v _
      refine ⟨fun off hoff i hi => ?_, fun off hoff => ?_⟩
      · exact (hslice off hoff i (Nat.le_of_lt hi)).trans (hmid.slices_prev off hoff i hi)
      · exact lt_of_eq_of_lt (hslice off hoff _ (Nat.le_refl _)) (hmid.slices_cur off hoff)

/-- The g8 tail: the receipt-list push and the slot store take the loop-exit
bundle to `PtxAfterPhase4`, where the remaining program takes over. -/
theorem p4Q8_tail {F : Type}
    {entry s_pmc t : PanSemStateFiniteExact 64 F} {w_out lw capw nl_w : BitVec 64}
    (h : P4Q8Exit entry s_pmc w_out lw capw nl_w t)
    (rest : ProgHOL 64)
    (htail : ∀ s' : PanSemStateFiniteExact 64 F,
      s'.code = originalRuntimeCode → PtxAfterPhase4 entry s' → PtxRelRunStrong entry rest s') :
    PtxRelRunStrong entry
      (.decCall (ofString "rl") .one (ofString "lst_push")
        [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000048#64)])),
         (.const 0x0000000000000008#64)]
        (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) rest)) t := by
  obtain ⟨_, _, _, _, S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  have hEt : TxEnv t := p4Q8_txEnv_of_base h.base h.idx_local
  obtain ⟨S_t, N_t, _, _, _, hWT_t, _⟩ := (p4Q8ChainX_of_exit h) S_e Nd_e hWT_e hD_e
  have hw_l : (BitVec.ofNat 64 (memW t (globN t "bo" + 72))).toNat =
      memW t (globN t "bo" + 72) := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (p4Q8T_memW_lt _ _)
  have harg := p4Q8T_harg h.base.world.1 hWT_t hEt hw_l
  have hlist_nz : memW t (BitVec.ofNat 64 (memW t (globN t "bo" + 72))).toNat ≠ 0 := by
    rw [hw_l]; exact h.base.rcpt_backing
  refine p4Q8T_decCall_lst_push h.base h.code
    (BitVec.ofNat 64 (memW t (globN t "bo" + 72))) (Or.inr hw_l) hlist_nz _ _ _ harg ?_
  intro w post hmem hpush hback hstep0 hcode
  obtain ⟨_, hin, hlen, hslot, _⟩ := hpush
  have hstepT : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra t
      (some (.returned (.val (.word w)))) post :=
    worldStep_congr_R rfl (p4Loop31_calleeStepAtU hstep0)
  have hmid_p := p4Q8T_mid_of_push h hw_l hmem hin hlen hslot hback hstepT
  have key : ∀ u1 : PanSemStateFiniteExact 64 F,
      u1 = setVarHOLFinite (ofString "rl") (.val (.word w)) { post with locals := t.locals } →
      PtxRelRunStrong entry
        (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs")))
          rest) u1 := by
    intro u1 hu1
    have hu1_mid : P4Q8TMid entry s_pmc w_out lw w
        (BitVec.ofNat 64 (memW t (globN t "bo" + 72))).toNat u1 := by
      subst hu1
      exact p4Q8TMid_with_locals (u := post)
        (t.locals.update (ofString "rl", .val (.word w))) post.clock hmid_p
    have hu1_code : u1.code = originalRuntimeCode := by
      subst hu1
      exact hcode
    have hu1_rl : u1.locals.lookup (ofString "rl") = some (.val (.word w)) := by
      subst hu1
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hu1_sl : u1.locals.lookup (ofString "stable_logs") = some (.val (.word lw)) := by
      subst hu1
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "rl" ≠ ofString "stable_logs" by decide, h.sl_local]
    have hu1_out : u1.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
      subst hu1
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "rl" ≠ ofString "out" by decide, h.out_local]
    have hu1_idx : u1.locals.lookup (ofString "index") =
        entry.locals.lookup (ofString "index") := by
      subst hu1
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "rl" ≠ ofString "index" by decide, h.idx_local]
    have hu1_i : ∃ wi : BitVec 64,
        u1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
      obtain ⟨wi, hwi⟩ := h.i_local
      refine ⟨wi, ?_⟩
      subst hu1
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "rl" ≠ ofString "i" by decide, hwi]
    refine p4Run_store _ _ _ ?_
    intro a v mem' hdst hsrc hst
    have ha : a = w := by
      simp only [evalAt, evalHOLExact, toExact, hu1_rl] at hdst
      have h1 := Option.some.inj hdst
      injection h1 with h2
      injection h2 with h3
      exact h3.symm
    have hv : v = .val (.word lw) := by
      simp only [evalAt, evalHOLExact, toExact, hu1_sl] at hsrc
      exact (Option.some.inj hsrc).symm
    subst ha
    subst hv
    have hflat : flattenHOL (.val (.word lw) : ValueHOL 64) = [HolWordLab.word lw] := by
      simp [flattenHOL]
    rw [hflat] at hst
    obtain ⟨hdom_w, hmemform⟩ := p4Loop31_storeWordEff hst
    have hm : ∀ x, x ≠ a → mem' x = u1.memory x := by
      intro x hx
      rw [hmemform]
      simp [hx]
    have hw : mem' a = HolWordLab.word lw := by
      rw [hmemform]
      simp
    have hstep5 := p4Q8T_storeStep hu1_mid hu1_idx hdom_w hm
    have hmw : ∀ k : Nat, BitVec.ofNat 64 k ≠ a →
        memW {u1 with memory := mem'} k = memW u1 k :=
      fun k hk => p4Loop31_memW_of_storeMiss hm hk
    have hw5 : memW {u1 with memory := mem'} a.toNat = lw.toNat := by
      have hround : BitVec.ofNat 64 a.toNat = a := by simp
      have hcell : ({u1 with memory := mem'} : PanSemStateFiniteExact 64 F).memory
          (BitVec.ofNat 64 a.toNat) = HolWordLab.word lw := by
        show mem' (BitVec.ofNat 64 a.toNat) = HolWordLab.word lw
        rw [hround]
        exact hw
      unfold memW
      rw [hcell]
    exact htail _ hu1_code
      (p4Q8T_after_store hu1_mid hu1_idx hu1_out hu1_i hstep5 hmw hw5)
  exact key _ rfl

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
