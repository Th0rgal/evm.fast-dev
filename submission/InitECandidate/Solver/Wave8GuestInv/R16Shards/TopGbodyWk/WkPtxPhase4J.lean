import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4I

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

/-! # Phase 4J: the loop-31 eval facts

The load-eval for the first `lst_push` argument (the logs-list header word
at `bo + 40`), assembled from the bo-global word, the bo-record's `WordsOK`
cells and the forward load-evaluation lemma. -/

/-- Every global is either a word (and then `globN` reads that word back) or
`globN` is zero: case analysis on the definition of `globN`. -/
theorem p4Loop31_globN_cases {F : Type} (u : PanSemStateFiniteExact 64 F) (name : String) :
    u.globals.lookup (ofString name) =
        some (.val (.word (BitVec.ofNat 64 (globN u name)))) ∨
    globN u name = 0 := by
  unfold globN
  rcases hv : u.globals.lookup (ofString name) with _ | v
  · exact Or.inr rfl
  · rcases hvv : v with @⟨wl⟩ | _ | _
    · rcases hwl : wl with @⟨w⟩
      · exact Or.inl (by simp)
    · exact Or.inr rfl
    · exact Or.inr rfl

/-- The `bo` global is a word whose value reads back as `globN u "bo"`. -/
theorem p4Loop31_boWord {F : Type} {u : PanSemStateFiniteExact 64 F}
    (hbnz : globN u "bo" ≠ 0) (hb : globN u "bo" < 2 ^ 64) :
    ∃ bw : BitVec 64, u.globals.lookup (ofString "bo") = some (.val (.word bw)) ∧
      bw.toNat = globN u "bo" := by
  rcases p4Loop31_globN_cases u "bo" with hgl | h0
  · refine ⟨BitVec.ofNat 64 (globN u "bo"), hgl, ?_⟩
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hb
  · exact absurd h0 hbnz

/-- The loop-31 argument evaluation: the first `lst_push` argument loads the
logs-list header word at `bo + 40` (the bo global is a word, the bo-record's
word-cells are in domain, so the forward load-evaluation applies), the second
is the constant `8`. -/
theorem p4Loop31_harg {F : Type} {u : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady u) {S Nd : List Nat} (hWT : WorldTypedWith u S Nd) (hE : TxEnv u)
    {w_l : BitVec 64} (hl40 : w_l.toNat = memW u (globN u "bo" + 40)) :
    evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a))
        p4Loop31Args = some [.val (.word w_l), .val (.word 8)] := by
  have ⟨halloc, hwords⟩ := bo_words hWT.2.2.1 hE.bo_nz
  have hbo264 : globN u "bo" + 88 ≤ 2 ^ 64 := (ivl_allocated_bound hAR.2 halloc).2
  obtain ⟨bw, hgl, hbwn⟩ := p4Loop31_boWord hE.bo_nz (by omega)
  have h28 : (0x0000000000000028#64 : BitVec 64).toNat = 40 := rfl
  have hb40 : BitVec.ofNat 64 (globN u "bo" + 40) = bw + 0x0000000000000028#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hadd : (bw + 0x0000000000000028#64).toNat = bw.toNat + 40 := by
      rw [BitVec.toNat_add, h28]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hadd, hbwn]
    exact Nat.mod_eq_of_lt (by omega)
  have hw40 : WordAt u (globN u "bo" + 40) := by
    have h5 : WordAt u (globN u "bo" + 8 * 5) := hwords.2.2 5 (show 5 < 88 / 8 by decide)
    have heq : globN u "bo" + 8 * 5 = globN u "bo" + 40 := by ring
    rwa [heq] at h5
  obtain ⟨w', hdom', hcell'⟩ := hw40
  rw [hb40] at hdom' hcell'
  have hload0 : @evalHOLExact 64 F _ u.toExact
      (fun x => Classical.propDecidable (u.memaddrs x))
      (.load .one (.op .add [.var .global (ofString "bo"), (.const 0x0000000000000028#64)])) =
      some (.val (.word w')) := by
    have hz : (0x0000000000000028#64 : BitVec 64) + 0 = 0x0000000000000028#64 :=
      BitVec.add_zero _
    simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hgl, valueIsWord, valueWord,
      wordOpHOL, wordOp, List.all, List.map, Option.map, ↓reduceIte, List.foldr, Bool.and_self,
      memLoadHOLExact, isWfShapeExactHOL, hz, hdom', hcell']
  have hm : memW u (bw + 0x0000000000000028#64).toNat = w_l.toNat := by
    have h1 : (bw + 0x0000000000000028#64).toNat = globN u "bo" + 40 := by
      rw [BitVec.toNat_add, h28, ← hbwn]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, hl40]
  have hw'w : w' = w_l := by
    apply BitVec.eq_of_toNat_eq
    have hmem : memW u (bw + 0x0000000000000028#64).toNat = w'.toNat := by
      have hround : ∀ x : BitVec 64, BitVec.ofNat 64 x.toNat = x := fun x => by simp
      unfold memW
      rw [hround (bw + 0x0000000000000028#64), hcell']
    rw [← hm, hmem]
  rw [hw'w] at hload0
  have hconst : @evalHOLExact 64 F _ u.toExact
      (fun x => Classical.propDecidable (u.memaddrs x))
      (.const 0x0000000000000008#64) = some (.val (.word 0x0000000000000008#64)) := rfl
  rw [evalListHOLFinite_eq_toExact]
  simp only [p4Loop31Args, evalListHOLExact, hload0, hconst]
  rfl

/-! ## The miss facts

An 8-byte cell that lies fully inside an allocated fixed object is not hit
by the pushed list header (disjoint objects) nor by the free heap (allocated
objects live below `heap_ptr` or above `heapLimit = scratchStart`). -/

/-- A cell inside an object disjoint from a nonempty target interval misses it. -/
theorem p4Loop31_noHit {k : Nat} {obj tgt : Ivl}
    (hkin : obj.1 ≤ k ∧ k + 8 ≤ obj.1 + obj.2) (h2nz : tgt.2 ≠ 0) (hdisj : Disj obj tgt) :
    ¬ CellHits k tgt := by
  intro hc
  unfold CellHits at hc
  obtain ⟨hc1, hc2⟩ := hc
  rcases hdisj with h0 | h0 | h | h <;> omega

/-- A cell inside an allocated object misses the free heap. -/
theorem p4Loop31_noFreeHit {F : Type} {u : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK u) {k : Nat} {obj : Ivl} (hal : Allocated u obj)
    (hkin : obj.1 ≤ k ∧ k + 8 ≤ obj.1 + obj.2) :
    ¬ CellHits k (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) := by
  have hlim : heapLimit = scratchStart := rfl
  have hhp := hA.2.1
  have hss := hA.2.2.1
  have hfs := hA.2.2.2.1
  intro hc
  unfold CellHits at hc
  simp only [InitECandidate.Solver.Wave8Contracts.M08.heapFree] at hc
  rcases hal with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- The loop-31 preserved cells: across the `lst_push` callee (whose write
set is contained in the pushed list header plus the free heap), every
bo-record cell, every receipt-list header cell and every written slice cell
survives unchanged. -/
theorem p4Loop31_preservedCells {F : Type}
    {entry u post : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady u) {S Nd : List Nat} (hWT : WorldTypedWith u S Nd) (hE : TxEnv u)
    (hidx : locN u "index" = locN entry "index")
    {w_l : BitVec 64} (hl40 : w_l.toNat = memW u (globN u "bo" + 40))
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (w_l.toNat, 24) →
      ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) →
      post.memory a = u.memory a) :
    (∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN u "bo" + off) = memW u (globN u "bo" + off)) ∧
    (memW post (memW u (globN u "bo" + 72)) = memW u (memW u (globN u "bo" + 72))) ∧
    (memW post (memW u (globN u "bo" + 72) + 8) =
      memW u (memW u (globN u "bo" + 72) + 8)) ∧
    (∀ off ∈ ([24, 32] : List Nat), ∀ i ≤ locN entry "index",
      memW post (memW u (globN u "bo" + off) + 16 * i + 8) =
        memW u (memW u (globN u "bo" + off) + 16 * i + 8)) := by
  obtain ⟨hgbs, hbo_pw, hgb_rest, hjr_rest, hbo_bal⟩ := fixedObjects_disj_parts hWT.2.2.1
  obtain ⟨hc40, hc72, hbo_eq⟩ := blockOutObjects_eq_list hE hWT.1
  have hbo_len : (blockOutObjects u).length = 7 := by rw [hbo_eq]; rfl
  have hfix : ∀ o ∈ fixedObjects u, o.2 = 0 ∨ (Allocated u o ∧ WordsOK u o) :=
    hWT.2.2.1.1
  have hfixOf : ∀ o ∈ blockOutObjects u, o ∈ fixedObjects u := by
    intro o ho
    unfold fixedObjects
    exact List.mem_append_left _ (List.mem_append_right _ ho)
  have hallocOf : ∀ o ∈ blockOutObjects u, o.2 ≠ 0 → Allocated u o := by
    intro o ho hne
    rcases hfix o (hfixOf o ho) with h0 | ⟨hal, hw⟩
    · exact absurd h0 hne
    · exact hal
  -- the element equations
  have hlen_nz : 16 * memW u (globN u "bo" + 80) + 16 ≠ 0 := by omega
  have h0_eq : (blockOutObjects u)[0] =
      (memW u (globN u "bo" + 24), 16 * memW u (globN u "bo" + 80) + 16) := by
    simp [hbo_eq, hE.bo_nz, hE.bo24, hlen_nz]
  have h1_eq : (blockOutObjects u)[1] =
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) := by
    simp [hbo_eq, hE.bo_nz, hE.bo32, hlen_nz]
  have h3_eq : (blockOutObjects u)[3] = (memW u (globN u "bo" + 40), 24) := by
    simp [hbo_eq]
  have h5_eq : (blockOutObjects u)[5] = (memW u (globN u "bo" + 72), 24) := by
    simp [hbo_eq]
  have h3l40 : (blockOutObjects u)[3] = (w_l.toNat, 24) := by rw [hl40, h3_eq]
  have hl40_bo : (w_l.toNat, 24) ∈ blockOutObjects u :=
    h3l40 ▸ List.getElem_mem (by rw [hbo_len]; omega)
  have hl72_bo : (memW u (globN u "bo" + 72), 24) ∈ blockOutObjects u := by
    rw [← h5_eq]; exact List.getElem_mem (by rw [hbo_len]; omega)
  have hs24_bo : (memW u (globN u "bo" + 24), 16 * memW u (globN u "bo" + 80) + 16) ∈
      blockOutObjects u := by
    rw [← h0_eq]; exact List.getElem_mem (by rw [hbo_len]; omega)
  have hs32_bo : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) ∈
      blockOutObjects u := by
    rw [← h1_eq]; exact List.getElem_mem (by rw [hbo_len]; omega)
  -- the allocations and bounds
  have ⟨halloc_bo, hwords_bo⟩ := bo_words hWT.2.2.1 hE.bo_nz
  have hbo_hi : globN u "bo" + 88 ≤ 2 ^ 64 := (ivl_allocated_bound hAR.2 halloc_bo).2
  have halloc_l72 : Allocated u (memW u (globN u "bo" + 72), 24) :=
    hallocOf _ hl72_bo (by simp)
  have hl72_hi : memW u (globN u "bo" + 72) + 24 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAR.2 halloc_l72).2
  have halloc_s24 : Allocated u
      (memW u (globN u "bo" + 24), 16 * memW u (globN u "bo" + 80) + 16) :=
    hallocOf _ hs24_bo hlen_nz
  have hs24_hi : memW u (globN u "bo" + 24) + (16 * memW u (globN u "bo" + 80) + 16) ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAR.2 halloc_s24).2
  have halloc_s32 : Allocated u
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) :=
    hallocOf _ hs32_bo hlen_nz
  have hs32_hi : memW u (globN u "bo" + 32) + (16 * memW u (globN u "bo" + 80) + 16) ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAR.2 halloc_s32).2
  -- the disjointness facts
  have hbo_gbs : (globN u "bo", 88) ∈ (globalBuffers.map fun gn =>
      (globN u gn.1, if globN u gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
  have hdisj_bo : Disj (globN u "bo", 88) (w_l.toNat, 24) :=
    hgb_rest _ hbo_gbs (w_l.toNat, 24)
      (by simp only [List.mem_append]; first
        | exact Or.inr (Or.inl hl40_bo)
        | exact Or.inl (Or.inr hl40_bo))
  have hget := List.pairwise_iff_getElem.1 hbo_pw
  have hlen : 3 < (blockOutObjects u).length ∧ 5 < (blockOutObjects u).length ∧
      0 < (blockOutObjects u).length ∧ 1 < (blockOutObjects u).length := by
    rw [hbo_len]; omega
  obtain ⟨hli3, hli5, hli0, hli1⟩ := hlen
  have hd_l72 : Disj (memW u (globN u "bo" + 72), 24) (w_l.toNat, 24) := by
    rw [← h5_eq, ← h3l40]
    exact disj_symm (hget 3 5 hli3 hli5 (by omega))
  have hd_s24 : Disj (memW u (globN u "bo" + 24), 16 * memW u (globN u "bo" + 80) + 16)
      (w_l.toNat, 24) := by
    rw [← h0_eq, ← h3l40]
    exact hget 0 3 hli0 hli3 (by omega)
  have hd_s32 : Disj (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16)
      (w_l.toNat, 24) := by
    rw [← h1_eq, ← h3l40]
    exact hget 1 3 hli1 hli3 (by omega)
  -- component 1: the bo-record cells
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro off hoff
    have hoffb : off ≤ 80 ∧ 24 ≤ off := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hk64 : globN u "bo" + off < 2 ^ 64 := by omega
    have hkin : globN u "bo" ≤ globN u "bo" + off ∧
        globN u "bo" + off + 8 ≤ globN u "bo" + 88 := by omega
    exact p4Loop31_memW_of_miss hmem hk64
      (p4Loop31_noHit hkin (by simp) hdisj_bo) (p4Loop31_noFreeHit hAR.2 halloc_bo hkin)
  · exact p4Loop31_memW_of_miss hmem (by omega)
      (p4Loop31_noHit ⟨Nat.le_refl _, by omega⟩ (by simp) hd_l72)
      (p4Loop31_noFreeHit hAR.2 halloc_l72 ⟨Nat.le_refl _, by omega⟩)
  · exact p4Loop31_memW_of_miss hmem (by omega)
      (p4Loop31_noHit ⟨by omega, by omega⟩ (by simp) hd_l72)
      (p4Loop31_noFreeHit hAR.2 halloc_l72 ⟨by omega, by omega⟩)
  · intro off hoff i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl
    · have hk64 : memW u (globN u "bo" + 24) + 16 * i + 8 < 2 ^ 64 := by
        have hidx' := hidx
        have := hE.idx_lt
        omega
      have hkin : memW u (globN u "bo" + 24) ≤ memW u (globN u "bo" + 24) + 16 * i + 8 ∧
          memW u (globN u "bo" + 24) + 16 * i + 8 + 8 ≤
            memW u (globN u "bo" + 24) + (16 * memW u (globN u "bo" + 80) + 16) := by
        have hidx' := hidx
        have := hE.idx_lt
        omega
      exact p4Loop31_memW_of_miss hmem hk64
        (p4Loop31_noHit hkin (by simp) hd_s24) (p4Loop31_noFreeHit hAR.2 halloc_s24 hkin)
    · have hk64 : memW u (globN u "bo" + 32) + 16 * i + 8 < 2 ^ 64 := by
        have hidx' := hidx
        have := hE.idx_lt
        omega
      have hkin : memW u (globN u "bo" + 32) ≤ memW u (globN u "bo" + 32) + 16 * i + 8 ∧
          memW u (globN u "bo" + 32) + 16 * i + 8 + 8 ≤
            memW u (globN u "bo" + 32) + (16 * memW u (globN u "bo" + 80) + 16) := by
        have hidx' := hidx
        have := hE.idx_lt
        omega
      exact p4Loop31_memW_of_miss hmem hk64
        (p4Loop31_noHit hkin (by simp) hd_s32) (p4Loop31_noFreeHit hAR.2 halloc_s32 hkin)

/-! ## The store-step eval facts

The continuation `C = store slot src; i := i + 1` runs at
`s₁ = setVar slot w {post with locals := u.locals}`.  These lemmas evaluate
its three expressions: the store target (the local `slot`), the source (the
log entry word at `lp + 8*i`) and the index bump. -/

/-- The store target: after the call, the local `slot` holds the pushed
slot address `w`. -/
theorem p4Loop31_slotEval {F : Type}
    {u post : PanSemStateFiniteExact 64 F} {w : BitVec 64} :
    evalAt (setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals})
        (.var .local (ofString "slot")) = some (.val (.word w)) := by
  simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

/-- The store source: the log entry word at `lp + 8*i`, read from the
callee's memory at the in-domain word cell. -/
theorem p4Loop31_srcEval {F : Type}
    {u post : PanSemStateFiniteExact 64 F} {w lp_w i_w v_src : BitVec 64}
    (hlp : u.locals.lookup (ofString "lp") = some (.val (.word lp_w)))
    (hi : u.locals.lookup (ofString "i") = some (.val (.word i_w)))
    (hdom : post.memaddrs (lp_w + i_w * 0x0000000000000008#64))
    (hcell : post.memory (lp_w + i_w * 0x0000000000000008#64) = .word v_src) :
    evalAt (setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals})
        p4Loop31Src = some (.val (.word v_src)) := by
  have hma : (setVarHOLFinite (ofString "slot") (.val (.word w))
      {post with locals := u.locals}).memaddrs = post.memaddrs := rfl
  have hmo : (setVarHOLFinite (ofString "slot") (.val (.word w))
      {post with locals := u.locals}).memory = post.memory := rfl
  have hslot_lp : (setVarHOLFinite (ofString "slot") (.val (.word w))
      {post with locals := u.locals}).locals.lookup (ofString "lp")
      = some (.val (.word lp_w)) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "slot" ≠ ofString "lp" by decide, hlp]
  have hslot_i : (setVarHOLFinite (ofString "slot") (.val (.word w))
      {post with locals := u.locals}).locals.lookup (ofString "i")
      = some (.val (.word i_w)) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "slot" ≠ ofString "i" by decide, hi]
  have hz : i_w * 0x0000000000000008#64 + (0 : BitVec 64) = i_w * 0x0000000000000008#64 :=
    BitVec.add_zero _
  simp only [p4Loop31Src, evalAt, evalHOLExact, evalListHOLExact, toExact, hslot_lp, hslot_i,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map,
    ↓reduceIte, List.foldr, Bool.and_self, memLoadHOLExact, isWfShapeExactHOL, hz, hdom,
    hcell, hma, hmo]

/-- The index bump: `i + 1` reads the caller's `i` local (the memory update
of the store step does not touch locals). -/
theorem p4Loop31_iEval {F : Type}
    {u post : PanSemStateFiniteExact 64 F} {w i_w : BitVec 64}
    {mem' : RiscV.Word 64 → HolWordLab 64}
    (hi : u.locals.lookup (ofString "i") = some (.val (.word i_w))) :
    evalAt {setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}
        with memory := mem'} p4Loop31I
        = some (.val (.word (i_w + 0x0000000000000001#64))) := by
  have hlm : ({setVarHOLFinite (ofString "slot") (.val (.word w))
      {post with locals := u.locals} with memory := mem'} : PanSemStateFiniteExact 64 F).locals
      = (setVarHOLFinite (ofString "slot") (.val (.word w))
          {post with locals := u.locals}).locals := rfl
  have hlu : (setVarHOLFinite (ofString "slot") (.val (.word w))
      {post with locals := u.locals}).locals.lookup (ofString "i")
      = some (.val (.word i_w)) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "slot" ≠ ofString "i" by decide, hi]
  have hz : (0x0000000000000001#64 : BitVec 64) + 0 = 0x0000000000000001#64 :=
    BitVec.add_zero _
  simp only [p4Loop31I, evalAt, evalHOLExact, evalListHOLExact, toExact, hlm, hlu, valueIsWord,
    valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, ↓reduceIte, List.foldr,
    Bool.and_self, hz]

/-! ## The post-store `TxEnv`

The next loop-31 iteration's `TxEnv` at the bumped state: the bo-record
cells survive both the callee (via `hbo_pres`) and the single-cell slot store
(via the address-misses `hw_miss`), and the `index` local is untouched by the
`slot`/`i` updates. -/

theorem p4Loop31_txEnvPost {F : Type}
    {u post : PanSemStateFiniteExact 64 F} {w i_w : BitVec 64}
    {mem' : RiscV.Word 64 → HolWordLab 64}
    (hE : TxEnv u)
    (hbo_eq : globN post "bo" = globN u "bo")
    (hjcap_eq : globN post "journal_cap" = globN u "journal_cap")
    (hmem' : ∀ a, a ≠ w → mem' a = post.memory a)
    (hbo_pres : ∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN u "bo" + off) = memW u (globN u "bo" + off))
    (hw_miss : ∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      BitVec.ofNat 64 (globN u "bo" + off) ≠ w) :
    TxEnv (setVarHOLFinite (ofString "i") (.val (.word (i_w + 0x0000000000000001#64)))
      {setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}
        with memory := mem'}) := by
  have hgbo : globN (setVarHOLFinite (ofString "i")
      (.val (.word (i_w + 0x0000000000000001#64)))
      {setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}
        with memory := mem'}) "bo" = globN u "bo" := by
    show globN post "bo" = globN u "bo"
    rw [hbo_eq]
  have hgjc : globN (setVarHOLFinite (ofString "i")
      (.val (.word (i_w + 0x0000000000000001#64)))
      {setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}
        with memory := mem'}) "journal_cap" = globN u "journal_cap" := by
    show globN post "journal_cap" = globN u "journal_cap"
    rw [hjcap_eq]
  have hmemW : ∀ k, BitVec.ofNat 64 k ≠ w →
      memW (setVarHOLFinite (ofString "i") (.val (.word (i_w + 0x0000000000000001#64)))
        {setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}
          with memory := mem'}) k = memW post k := by
    intro k hk
    have e1 : (setVarHOLFinite (ofString "i") (.val (.word (i_w + 0x0000000000000001#64)))
        {setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}
          with memory := mem'}).memory (BitVec.ofNat 64 k) = mem' (BitVec.ofNat 64 k) := rfl
    have e2 : mem' (BitVec.ofNat 64 k) = post.memory (BitVec.ofNat 64 k) := hmem' _ hk
    unfold memW
    rw [e1, e2]
  have hloc : locN (setVarHOLFinite (ofString "i") (.val (.word (i_w + 0x0000000000000001#64)))
      {setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}
        with memory := mem'}) "index" = locN u "index" := by
    have hlu : (setVarHOLFinite (ofString "i") (.val (.word (i_w + 0x0000000000000001#64)))
        {setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}
          with memory := mem'}).locals.lookup (ofString "index")
        = u.locals.lookup (ofString "index") := by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "index" by decide,
        show ofString "slot" ≠ ofString "index" by decide]
    simp only [locN, hlu]
  refine ⟨by rw [hgbo]; exact hE.bo_nz, ?_, ?_, ?_, ?_, ?_, by rw [hgjc]; exact hE.jcap_nz⟩
  · rw [hgbo, hmemW (globN u "bo" + 24) (hw_miss 24 (by decide)),
      hbo_pres 24 (by decide)]
    exact hE.bo24
  · rw [hgbo, hmemW (globN u "bo" + 32) (hw_miss 32 (by decide)),
      hbo_pres 32 (by decide)]
    exact hE.bo32
  · rw [hgbo, hmemW (globN u "bo" + 40) (hw_miss 40 (by decide)),
      hbo_pres 40 (by decide)]
    exact hE.bo40
  · rw [hgbo, hmemW (globN u "bo" + 72) (hw_miss 72 (by decide)),
      hbo_pres 72 (by decide)]
    exact hE.bo72
  · rw [hgbo, hmemW (globN u "bo" + 80) (hw_miss 80 (by decide)),
      hbo_pres 80 (by decide), hloc]
    exact hE.idx_lt

/-! ## The `hty`/`hrec` cores for the slot-store

The pushed slot `w` lies inside the bo+40 block-logs backing array, so the
single-cell store is a `store_bo_array_world` (idx = 4) step: typing, the
owned set and the `TxEnv` survive, and every `stdKeep` record cell misses the
stored address. -/

/-- The bo+40 backing array is a block-out object with positive capacity. -/
theorem p4Loop31_arrFacts {F : Type} {s : PanSemStateFiniteExact 64 F} {l : Nat}
    (hE : TxEnv s) {S : List Nat} (hT : TablesTyped s S)
    (hl : l = memW s (globN s "bo" + 40))
    (hdata_nz : memW s l ≠ 0) :
    (memW s l, 8 * memW s (l + 16)) ∈ blockOutObjects s ∧ 1 ≤ memW s (l + 16) := by
  obtain ⟨hc40, _, hbo_eq⟩ := blockOutObjects_eq_list hE hT
  have hcap : 1 ≤ memW s (l + 16) := by rw [hl]; exact hc40
  have hlen_nz : 8 * memW s (l + 16) ≠ 0 := by omega
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo_eq]; rfl
  have hget4 : (blockOutObjects s)[4] = (memW s l, 8 * memW s (l + 16)) := by
    simp [hbo_eq, ← hl, hE.bo_nz, hdata_nz, hlen_nz]
  exact ⟨hget4 ▸ List.getElem_mem (by rw [hbo_len]; decide), hcap⟩

/-- The `TxEnv` at the slot-composite state: the callee kept `bo` and
`journal_cap` and preserved the bo-record cells. -/
theorem p4Loop31_txEnvSlot {F : Type}
    {u post : PanSemStateFiniteExact 64 F} {w : BitVec 64}
    (hE : TxEnv u)
    (hbo_eq : globN post "bo" = globN u "bo")
    (hjcap_eq : globN post "journal_cap" = globN u "journal_cap")
    (hbo_pres : ∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN u "bo" + off) = memW u (globN u "bo" + off)) :
    TxEnv (setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}) := by
  have hgbo : globN (setVarHOLFinite (ofString "slot") (.val (.word w))
      {post with locals := u.locals}) "bo" = globN u "bo" := by
    show globN post "bo" = globN u "bo"
    rw [hbo_eq]
  have hgjc : globN (setVarHOLFinite (ofString "slot") (.val (.word w))
      {post with locals := u.locals}) "journal_cap" = globN u "journal_cap" := by
    show globN post "journal_cap" = globN u "journal_cap"
    rw [hjcap_eq]
  have hmemW : ∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW (setVarHOLFinite (ofString "slot") (.val (.word w))
        {post with locals := u.locals}) (globN u "bo" + off) = memW u (globN u "bo" + off) := by
    intro off hoff
    show memW post (globN u "bo" + off) = memW u (globN u "bo" + off)
    exact hbo_pres off hoff
  have hloc : locN (setVarHOLFinite (ofString "slot") (.val (.word w))
      {post with locals := u.locals}) "index" = locN u "index" := by
    have hlu : (setVarHOLFinite (ofString "slot") (.val (.word w))
        {post with locals := u.locals}).locals.lookup (ofString "index")
        = u.locals.lookup (ofString "index") := by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "slot" ≠ ofString "index" by decide]
    simp only [locN, hlu]
  refine ⟨by rw [hgbo]; exact hE.bo_nz, ?_, ?_, ?_, ?_, ?_, by rw [hgjc]; exact hE.jcap_nz⟩
  · rw [hgbo, hmemW 24 (by decide)]; exact hE.bo24
  · rw [hgbo, hmemW 32 (by decide)]; exact hE.bo32
  · rw [hgbo, hmemW 40 (by decide)]; exact hE.bo40
  · rw [hgbo, hmemW 72 (by decide)]; exact hE.bo72
  · rw [hgbo, hmemW 80 (by decide), hloc]; exact hE.idx_lt

/-- The loop-31 `hty` core: the single-cell slot-store inside the bo+40
backing array preserves typing, the owned set and the `TxEnv`, and the
stored cell lies inside an owned object (the backing array itself). -/
theorem p4Loop31_hty {F : Type} {s : PanSemStateFiniteExact 64 F} {w : BitVec 64}
    {mem' : RiscV.Word 64 → HolWordLab 64} {l : Nat}
    (hAR : ArenaReady s) (hE : TxEnv s)
    (hl : l = memW s (globN s "bo" + 40))
    (hdata_nz : memW s l ≠ 0)
    (hin : Inside (w.toNat, 8) (memW s l) (memW s l + 8 * memW s (l + 16)))
    (hx : s.memaddrs w)
    (hm : ∀ a, a ≠ w → mem' a = s.memory a) :
    ∀ S Nd, WorldTypedWith s S Nd →
      (WorldTypedWith {s with memory := mem'} S Nd ∧
        worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
        TxEnv {s with memory := mem'}) ∧
      (∃ o ∈ worldOwned s S Nd, Inside (w.toNat, 8) o.1 (o.1 + o.2)) := by
  intro S Nd hWT
  obtain ⟨harr_mem, -⟩ := p4Loop31_arrFacts hE hWT.1 hl hdata_nz
  have harr_fix : (memW s l, 8 * memW s (l + 16)) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    exact harr_mem
  have harr_own : (memW s l, 8 * memW s (l + 16)) ∈ worldOwned s S Nd := by
    unfold worldOwned
    apply List.mem_append_left
    apply List.mem_append_right
    exact harr_fix
  refine ⟨?_, ⟨(memW s l, 8 * memW s (l + 16)), harr_own, hin⟩⟩
  rw [hl] at hdata_nz hin
  exact store_bo_array_world (idx := 4)
    (arr := (memW s (memW s (globN s "bo" + 40)),
      8 * memW s (memW s (globN s "bo" + 40) + 16)))
    hAR hE hWT (Or.inr (Or.inl ⟨rfl, hdata_nz, rfl⟩)) hx hin hm

/-- The loop-31 `hrec` core: every `stdKeep` record cell (ws, bs, ts, bo)
misses the stored slot address, so all kept cells survive the store. -/
theorem p4Loop31_hrecStd {F : Type} {s : PanSemStateFiniteExact 64 F} {w : BitVec 64}
    {mem' : RiscV.Word 64 → HolWordLab 64}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {l : Nat} (hl : l = memW s (globN s "bo" + 40))
    (hdata_nz : memW s l ≠ 0)
    (hin : Inside (w.toNat, 8) (memW s l) (memW s l + 8 * memW s (l + 16)))
    (hm : ∀ a, a ≠ w → mem' a = s.memory a) :
    ∀ r ∈ stdKeep, globN s r.1 ≠ 0 → ∀ k ∈ r.2,
      memW {s with memory := mem'} (globN s r.1 + k) = memW s (globN s r.1 + k) := by
  obtain ⟨-, -, hgb_rest, -, -⟩ := fixedObjects_disj_parts hW.2.2.1
  obtain ⟨harr_mem, -⟩ := p4Loop31_arrFacts hE hW.1 hl hdata_nz
  have hrec_disj : ∀ (g : String) (sz : Nat), (g, sz) ∈ globalBuffers →
      globN s g ≠ 0 → Disj (globN s g, sz) (memW s l, 8 * memW s (l + 16)) := by
    intro g sz hgb hgnz
    have hmem : (memW s l, 8 * memW s (l + 16)) ∈
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s := by
      apply List.mem_append_left
      apply List.mem_append_right
      exact harr_mem
    exact hgb_rest _ (List.mem_map.2 ⟨(g, sz), hgb, by simp [hgnz]⟩) _ hmem
  have hcell_miss : ∀ (g : String) (sz : Nat), (g, sz) ∈ typedRecords →
      globN s g ≠ 0 → ∀ k, k + 8 ≤ sz → BitVec.ofNat 64 (globN s g + k) ≠ w := by
    intro g sz htr hgnz k hk8
    have hd : Disj (globN s g, sz) (w.toNat, 8) :=
      disj_of_inside_right hin (hrec_disj g sz (typedRecord_mem_globalBuffers htr) hgnz)
    have hg_fix : (globN s g, sz) ∈ fixedObjects s := by
      simpa [hgnz] using typedRecord_mem_fixedObjects s (r := (g, sz)) htr
    have hsz_nz : (g, sz).2 ≠ 0 := by simp; omega
    obtain ⟨halloc, -⟩ := (hW.2.2.1.1 _ hg_fix).resolve_left hsz_nz
    have hg_hi := (ivl_allocated_bound hA.2 halloc).2
    intro heq
    have htonat := congrArg BitVec.toNat heq
    have hk_lt : globN s g + k < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt] at htonat
    rcases hd with h0 | h0 | h1 | h1 <;> omega
  intro r hr hgnz k hk
  simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hne : BitVec.ofNat 64 (globN s r.1 + k) ≠ w := by
    rcases hr with rfl | rfl | rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      have hk8 : k + 8 ≤ 40 := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
      exact hcell_miss "ws" 40 (by decide) hgnz k hk8
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      have hk8 : k + 8 ≤ 80 := by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact hcell_miss "bs" 80 (by decide) hgnz k hk8
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      have hk8 : k + 8 ≤ 72 := by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact hcell_miss "ts" 72 (by decide) hgnz k hk8
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      have hk8 : k + 8 ≤ 88 := by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact hcell_miss "bo" 88 (by decide) hgnz k hk8
  exact p4Loop31_memW_of_storeMiss hm hne

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
