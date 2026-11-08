import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexedWalkWip
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRoot

/-!
# `wk_build_mpt_indexed`: the world-keeping bridge for `build_mpt_indexed`

R12 of the R16k shard family. This file completes the R11 WIP (`BuildMptIndexedWalkWip.lean`,
chunks A-D): the eval-level chain for the `while` walk, the entry construction, the per-step
invariant preservation, and the final `WorldStep` packaging.

Exports:
* `wk_build_mpt_indexed_strong` : the C08-shaped `WorldKeeps` at the strengthened guard
  `BuildMptIndexedReadyStrong`, with region list matching `Primitives.«wk_build_mpt_indexed»`.
* `gbody_build_mpt_indexed_strong` : the C11-shaped terminating bound at the strengthened guard.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

/-! ## Section 1: state congruences under locals/clock changes -/

theorem allocated_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (i : Ivl) :
    Allocated { s with locals := locals, clock := k } i ↔ Allocated s i := by
  simp only [Allocated, globN]

theorem mptObjInWith_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nm : List Nat) (m : Nat)
    (h : MptObjInWith s S Nm m) :
    MptObjInWith { s with locals := locals, clock := k } S Nm m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨(allocated_with_locals s locals k (m, 16)).2 h1, h2, h3, h4, h5, h6, h7⟩

theorem nodeHeapValuePtrOK_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (Nm : List Nat)
    (h : NodeHeapValuePtrOK s Nm) :
    NodeHeapValuePtrOK { s with locals := locals, clock := k } Nm := by
  unfold NodeHeapValuePtrOK at h ⊢
  exact fun n hn => h n hn

theorem mptObjInWithStrong_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nm : List Nat) (m : Nat)
    (h : MptObjInWithStrong s S Nm m) :
    MptObjInWithStrong { s with locals := locals, clock := k } S Nm m := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨mptObjInWith_with_locals s locals k S Nm m h1,
    nodeHeapValuePtrOK_with_locals s locals k Nm h2⟩

theorem worldOwned_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) :
    worldOwned { s with locals := locals, clock := k } S Nd = worldOwned s S Nd := rfl

theorem nodeExtents_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (Nd : List Nat) :
    nodeExtents { s with locals := locals, clock := k } Nd = nodeExtents s Nd := rfl

theorem mptObjIvls_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (Nm : List Nat) (m : Nat) :
    mptObjIvls { s with locals := locals, clock := k } Nm m = mptObjIvls s Nm m := rfl

theorem worldTypedIvls_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) :
    worldTypedIvls { s with locals := locals, clock := k } S Nd = worldTypedIvls s S Nd := rfl

theorem keccakBufIvls_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    keccakBufIvls { s with locals := locals, clock := k } = keccakBufIvls s := rfl

theorem bufferRegion_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (gs : String × Nat) :
    bufferRegion { s with locals := locals, clock := k } gs = bufferRegion s gs := rfl

theorem memW_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (x : Nat) :
    memW { s with locals := locals, clock := k } x = memW s x := rfl

/-! ## Section 2: the `WorldEff` walk foundation

The walk threads the public `R16Shards.WorldEff` (from `WkCacheGetRoot`) with `B = []` and
`gw = ["heap_ptr", "scratch_ptr"]`, anchored at the loop-entry state `s0`, with the fixed region
list `bmiWkRti s0` (the five keep buffers of the exported contract).  The buffer addresses are
stable across the whole walk because `GlobalsKept ["heap_ptr", "scratch_ptr"]` keeps every global
*outside* that list, and `WorldEff.sp_hi`/`fmp_eq` are anchored at `s0`, so `freeGap t ⊆ freeGap s0`
for every later state `t`. -/

/-- The ambient `gw` of the walk, as `MlS` list for `GlobalsKept` side conditions. -/
def bmiWkGw : List String := ["heap_ptr", "scratch_ptr"]

theorem bmiWkGw_map : bmiWkGw.map ofString = ["heap_ptr", "scratch_ptr"].map ofString := rfl

theorem bmiWkGw_no_gb : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ ["heap_ptr", "scratch_ptr"].map ofString := by
  decide

/-- A `HeapByteEff` step (evaluated decCall of `heap_mark`/`mpt_new`/`rlp_encode_word`) lifted to
the ambient `WorldEff` for the step's own source state, given the evaluation-side metadata facts
(`HeapByteEff` already carries `memaddrs`, `be`, `out_dom` and the byte frame). -/
theorem bmiWk_we_of_heapByteEff {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Sub Rl : List Ivl}
    (h : HeapByteEff s post Sub (bmiWkGw : List String))
    (hc : post.code = originalRuntimeCode)
    (hes : post.eshapes = s.eshapes)
    (hRl : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit)) :
    R16Shards.WorldEff s post Rl [] (bmiWkGw : List String) := by
  refine ⟨h.arena, hc, h.memaddrs, h.be, hes, h.hp_le, h.fp_eq, h.sp_le, h.globals,
    freshBufsOK_of_no_globalBuf_writes h.globals bmiWkGw_no_gb, h.out_dom, ?_, ?_⟩
  · intro a hne
    rcases h.cell_frame a hne with ⟨ivl, hivl, hcp⟩ | hfg | hhf
    · obtain ⟨h0, hc1, hc2⟩ := hcp
      rcases hRl ivl hivl h0 with ⟨j, hj, hj1, hj2⟩ | hg | hh
      · refine Or.inl ⟨j, hj, ?_, ?_⟩
        · omega
        · simp only [CellHits] at ⊢
          omega
      · refine Or.inr (Or.inr (Or.inl ?_))
        simp only [Fast_C08WkShard03.CellHitsPos, CellHits, freeGap] at ⊢
        omega
      · refine Or.inr (Or.inr (Or.inr ?_))
        simp only [Fast_C08WkShard03.CellHitsPos, CellHits, heapFree] at ⊢
        omega
    · exact Or.inr (Or.inr (Or.inl hfg))
    · exact Or.inr (Or.inr (Or.inr hhf))
  · intro b hb64 hne
    rcases h.byte_frame b hb64 hne with ⟨ivl, hivl, hiv⟩ | hfg | hhf
    · obtain ⟨h1, h2⟩ := hiv
      rcases hRl ivl hivl (by omega) with ⟨j, hj, hj1, hj2⟩ | hg | hh
      · refine Or.inl ⟨j, hj, ?_⟩
        simp only [InIvl] at ⊢
        omega
      · refine Or.inr (Or.inr (Or.inl ?_))
        simp only [InIvl, freeGap] at ⊢
        omega
      · refine Or.inr (Or.inr (Or.inr ?_))
        simp only [InIvl, heapFree] at ⊢
        omega
    · exact Or.inr (Or.inr (Or.inl hfg))
    · exact Or.inr (Or.inr (Or.inr hhf))

/-- Composing the anchored `WorldEff` with a lifted `HeapByteEff` step: the step's own `hRl`
contract is stated at the step source `t`, verbatim; `WorldEff.trans` performs the `s0`-narrowing
of `freeGap`/`heapFree` internally via `fmp_eq`/`sp_hi`/`hp_lo`. -/
theorem bmiWk_we_trans_heapByteEff {F : Type} {s0 t mid : PanSemStateFiniteExact 64 F}
    {Sub Rl : List Ivl}
    (h : R16Shards.WorldEff s0 t Rl [] (bmiWkGw : List String))
    (hb : HeapByteEff t mid Sub (bmiWkGw : List String))
    (hc : mid.code = originalRuntimeCode)
    (hes : mid.eshapes = t.eshapes)
    (hRl : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (globN t "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN t "scratch_ptr") ∨
      (globN t "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit)) :
    R16Shards.WorldEff s0 mid Rl [] (bmiWkGw : List String) := by
  have hstep := bmiWk_we_of_heapByteEff hb hc hes hRl
  exact R16Shards.WorldEff.trans h hstep (fun gs hgs => absurd hgs (by simp))
    (freshBufsOK_of_no_globalBuf_writes
      (fun k hk => (h.gw_kept k hk).trans (hstep.gw_kept k hk)) bmiWkGw_no_gb)

/-! ## Section 3: the two mpt callees (`mpt_set`, `mpt_root`)

The walk's frame contract for an mpt callee is `BmiWkMptWW`: resuming outcomes keep the arena,
never lower `heap_ptr`, never raise `scratch_ptr`, keep every global except `heap_ptr`/
`scratch_ptr`, and write only inside `Rm s` (the allocated tree span `[m, heap_ptr)` plus the
three keccak/mpt-hash scratch buffers), the frame gap `[fmp, sp)` and fresh heap
`[hp, heapLimit)` — cell- and byte-level.  It is discharged from the public `MptEffStrong`-level
producer `mk_mpt_set_eff_strong` (a five-way cell *and* byte frame over `R ∪ B ∪ mptObjIvls ∪
[freeGap] ∪ heapFree` with no `worldOwned` case): the `R`/`B` disjuncts are the keccak buffers of
`Rm`, and the `mptObjIvls` disjunct lands inside the `Rm` head `[m, hp)` via the span clause of
the `BmiWkMptReady` bundle the caller supplies. -/

/-- The keccak/mpt-hash buffer regions: exactly the `R` of `mk_mpt_set_eff_strong`. -/
def bmiWkKeccakR (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
   bufferRegion s ("mpt_hash_scratch", 40)]

/-- The mpt-callee write regions: the allocated tree span `[m, hp)` plus the three
keccak/mpt-hash scratch buffers. -/
def bmiWkMptRm (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  (locN s "m", globN s "heap_ptr" - locN s "m") :: bmiWkKeccakR s

theorem bmiWkKeccakR_eq_mptSetR_sc {F : Type} (s : PanSemStateFiniteExact 64 F) :
    bmiWkKeccakR s = mptSetR_sc s := rfl

/-- Dischargeable bundle for one mpt callee at its entry state `s`: the `MptSetReadyStrong`
contract, the object `Nm0` whose node extents the callee preserves, the two buffer-disjointness
clauses and the `mptObjIvls` disjointness the callee's `MptEffStrong` write/obj frames take as
premises, and the span bound pinning every `mptObjIvls` member into `[m, heap_ptr)` (so the
frames' `mptObjIvls` disjunct lands inside the `Rm` head). -/
def BmiWkMptReady {F : Type} (s : PanSemStateFiniteExact 64 F) (Nm0 : List Nat) : Prop :=
  MptSetReadyStrong s ∧
  ∃ S : List Nat,
    MptObjInWithStrong s S Nm0 (locN s "m") ∧
    (∀ o ∈ nodeExtents s Nm0, ∀ gs ∈ mptSetB_sc, Disj o (bufferRegion s gs)) ∧
    (∀ gs ∈ mptSetB_sc, Disj (locN s "m", 16) (bufferRegion s gs)) ∧
    IvlsDisj (mptSetR_sc s) (mptObjIvls s Nm0 (locN s "m")) ∧
    (∀ o ∈ mptObjIvls s Nm0 (locN s "m"), locN s "m" ≤ o.1 ∧ o.1 + o.2 ≤ globN s "heap_ptr") ∧
    locN s "m" + 16 ≤ globN s "heap_ptr"

/-- Byte-level write frame for an mpt callee: resuming outcomes keep the arena, never lower
`heap_ptr`, never raise `scratch_ptr`, keep every global except `heap_ptr`, and write only inside
`Rm s`, the frame gap `[fmp, sp)` and fresh heap `[hp, heapLimit)` (cell- and byte-level). -/
def BmiWkMptWW {F : Type} (Rm : PanSemStateFiniteExact 64 F → List Ivl)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      (fun s r post => Resumes r →
        ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
        globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
        (∀ a : BitVec 64, post.memory a ≠ s.memory a →
          (∃ i ∈ Rm s, 0 < i.2 ∧ i.1 < a.toNat + 8 ∧ a.toNat < i.1 + i.2) ∨
          (0 < globN s "scratch_ptr" - globN s "frame_mem_ptr" ∧
            globN s "frame_mem_ptr" < a.toNat + 8 ∧ a.toNat < globN s "scratch_ptr") ∨
          (0 < heapLimit - globN s "heap_ptr" ∧
            globN s "heap_ptr" < a.toNat + 8 ∧ a.toNat < heapLimit)) ∧
        (∀ b : Nat, b < 2 ^ 64 → memB post b ≠ memB s b →
          (∃ i ∈ Rm s, 0 < i.2 ∧ i.1 ≤ b ∧ b < i.1 + i.2) ∨
          (0 < globN s "scratch_ptr" - globN s "frame_mem_ptr" ∧
            globN s "frame_mem_ptr" ≤ b ∧ b < globN s "scratch_ptr") ∨
          (0 < heapLimit - globN s "heap_ptr" ∧
            globN s "heap_ptr" ≤ b ∧ b < heapLimit)) ∧
        ∀ k : MlS, k ∉ [ofString "heap_ptr", ofString "scratch_ptr"] →
          s.globals.lookup k = post.globals.lookup k)
        s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

/-- Lifting one mpt-callee step (given by its flattened `BmiWkMptWW` conclusion at the call's own
source state `t`, plus the evaluation metadata) to the anchored `WorldEff`. -/
theorem bmiWk_we_callee_mpt {F : Type} {s0 t post : PanSemStateFiniteExact 64 F}
    {Rm : PanSemStateFiniteExact 64 F → List Ivl}
    {Wown : List Ivl} {Rl : List Ivl}
    (h : R16Shards.WorldEff s0 t Rl [] (bmiWkGw : List String))
    (hRl : ∀ i ∈ Rm t, 0 < i.2 → ∃ j ∈ Rl, 0 < j.2 ∧ j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hRlW : ∀ j ∈ Wown, j ∈ Rl)
    (hAp : ArenaReady post)
    (hhp : globN t "heap_ptr" ≤ globN post "heap_ptr")
    (hspc : globN post "scratch_ptr" ≤ globN t "scratch_ptr")
    (hcell : ∀ a : BitVec 64, post.memory a ≠ t.memory a →
      (∃ i ∈ Rm t, 0 < i.2 ∧ i.1 < a.toNat + 8 ∧ a.toNat < i.1 + i.2) ∨
      (∃ j ∈ Wown, 0 < j.2 ∧ j.1 < a.toNat + 8 ∧ a.toNat < j.1 + j.2) ∨
      (0 < globN t "scratch_ptr" - globN t "frame_mem_ptr" ∧
        globN t "frame_mem_ptr" < a.toNat + 8 ∧ a.toNat < globN t "scratch_ptr") ∨
      (0 < heapLimit - globN t "heap_ptr" ∧
        globN t "heap_ptr" < a.toNat + 8 ∧ a.toNat < heapLimit))
    (hbyte : ∀ b : Nat, b < 2 ^ 64 → memB post b ≠ memB t b →
      (∃ i ∈ Rm t, 0 < i.2 ∧ i.1 ≤ b ∧ b < i.1 + i.2) ∨
      (∃ j ∈ Wown, 0 < j.2 ∧ j.1 ≤ b ∧ b < j.1 + j.2) ∨
      (0 < globN t "scratch_ptr" - globN t "frame_mem_ptr" ∧
        globN t "frame_mem_ptr" ≤ b ∧ b < globN t "scratch_ptr") ∨
      (0 < heapLimit - globN t "heap_ptr" ∧
        globN t "heap_ptr" ≤ b ∧ b < heapLimit))
    (hgw : ∀ k : MlS, k ∉ [ofString "heap_ptr", ofString "scratch_ptr"] →
      t.globals.lookup k = post.globals.lookup k)
    (hc : post.code = originalRuntimeCode)
    (hmd : post.memaddrs = t.memaddrs ∧ post.be = t.be ∧ post.eshapes = t.eshapes)
    (hout : ∀ a : BitVec 64, post.memory a ≠ t.memory a → t.memaddrs a) :
    R16Shards.WorldEff s0 post Rl [] (bmiWkGw : List String) := by
  obtain ⟨hmd_ma, hmd_be, hmd_es⟩ := hmd
  have hfmp_t : globN t "frame_mem_ptr" = globN s0 "frame_mem_ptr" := h.fmp_eq
  have hfmp_p : globN post "frame_mem_ptr" = globN t "frame_mem_ptr" :=
    globN_eq_of_lookup (hgw (ofString "frame_mem_ptr") (by decide))
  have hsp_t : globN t "scratch_ptr" ≤ globN s0 "scratch_ptr" := h.sp_hi
  have hhp_t : globN s0 "heap_ptr" ≤ globN t "heap_ptr" := h.hp_lo
  have hgw_c : GlobalsKept (bmiWkGw : List String) s0 post := by
    intro k hk
    rw [bmiWkGw_map] at hk
    have h1 : k ∉ [ofString "heap_ptr", ofString "scratch_ptr"] := by
      intro hm
      exact hk (by simpa using hm)
    exact (h.gw_kept k hk).trans (hgw k h1)
  refine ⟨hAp, hc, hmd_ma.trans h.memaddrs, hmd_be.trans h.be, hmd_es.trans h.eshapes,
    le_trans hhp_t hhp, hfmp_p.trans hfmp_t, le_trans hspc hsp_t, hgw_c,
    freshBufsOK_of_no_globalBuf_writes hgw_c bmiWkGw_no_gb, fun a hne => ?_, ?_, ?_⟩
  · by_cases hct : post.memory a = t.memory a
    · rw [hct] at hne; exact h.out_dom a hne
    · exact h.memaddrs ▸ hout a hct
  · intro a hne
    by_cases hct : post.memory a = t.memory a
    · rw [hct] at hne; exact h.cell_frame a hne
    · rcases hcell a hct with ⟨i, hi, h0, hc1, hc2⟩ | ⟨j, hj, hj0, hj1, hj2⟩ | hfg |
        ⟨h0, hc1, hc2⟩
      · obtain ⟨j', hj', hj0', hj1', hj2'⟩ := hRl i hi h0
        exact Or.inl ⟨j', hj', hj0', ⟨by omega, by omega⟩⟩
      · exact Or.inl ⟨j, hRlW j hj, hj0, hj1, hj2⟩
      · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
        all_goals (dsimp only [freeGap]; omega)
      · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
        all_goals dsimp only [Fast_C08WkShard03.CellHitsPos, CellHits, heapFree]
        all_goals omega
  · intro b hb64 hne
    by_cases hct : memB post b = memB t b
    · rw [hct] at hne; exact h.byte_frame b hb64 hne
    · rcases hbyte b hb64 hct with ⟨i, hi, h0, h1, h2⟩ | ⟨j, hj, hj0, hj1, hj2⟩ | hfg |
        ⟨h0, h1, h2⟩
      · obtain ⟨j', hj', hj0', hj1', hj2'⟩ := hRl i hi h0
        exact Or.inl ⟨j', hj', ⟨by omega, by omega⟩⟩
      · exact Or.inl ⟨j, hRlW j hj, hj1, hj2⟩
      · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
        all_goals (dsimp only [freeGap]; omega)
      · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
        all_goals dsimp only [InIvl, heapFree]
        all_goals omega

/-! ## Section 3b: call-site plumbing

`bmiWk_we_call_mpt_callee` turns `BmiWkMptWW` into the `hcallee` callback of
`worldEff_call0_eff`; `bmiWk_we_decCall_rlp` lifts one `rlp_encode_word` decCall
(whose `HeapByteEff` step has `Sub := Rl`, i.e. trivial coverage). -/

/-- The entry state of a guest callee keeps `ArenaReady`. -/
theorem bmiWk_arenaReady_callEntry {F : Type} (t : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (hA : ArenaReady t) :
    ArenaReady (callEntryStateHOLFinite t callee) :=
  ⟨guestInv_callEntry t callee hA.1, hA.2⟩

/-- The walk loop invariant.  Components:
1. `ArenaReady` and the pinned locals (`mark`/`m` at the fresh-heap base `mark`,
   `n`/`slice_arr`/`out` at their entry values);
2. the heap-pointer window (`mark ≤ hp ≤ heapLimit`) and the pinned global
   addresses (`keccak_pad`, `keccak_st`, `frame_mem_ptr`, `scratch_ptr` monotone);
3. the typed world `S Nd` with the mpt object `Nm` at `mark`, the disjointness
   facts, the extent/ownership bounds and the kept-word clauses (the standard-keep
   record words and the slice words);
4. the layout extras: the keep buffers all end at or before `mark`, the
   `mpt_key_scratch` address is constant, and the root node fits in fresh heap. -/
def BmiWkInv (s0 : PanSemStateFiniteExact 64 F) (S0 Nd0 : List Nat) (mark : Nat)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady t ∧
  locN t "mark" = mark ∧ locN t "m" = mark ∧
  (∃ w : BitVec 64, t.locals.lookup (ofString "m") = some (.val (.word w))) ∧
  (∃ w : BitVec 64, t.locals.lookup (ofString "slice_arr") = some (.val (.word w))) ∧
  locN t "n" = locN s0 "n" ∧ locN t "slice_arr" = locN s0 "slice_arr" ∧
    locN t "out" = locN s0 "out" ∧
  mark ≤ globN t "heap_ptr" ∧
  globN t "heap_ptr" ≤ heapLimit ∧
  globN t "keccak_pad" = globN s0 "keccak_pad" ∧
    globN t "keccak_st" = globN s0 "keccak_st" ∧
  globN t "frame_mem_ptr" = globN s0 "frame_mem_ptr" ∧
  globN t "mpt_hash_scratch" = globN s0 "mpt_hash_scratch" ∧
  globN t "scratch_ptr" ≤ globN s0 "scratch_ptr" ∧
  (∃ S Nd Nm,
    WorldTypedWith t S Nd ∧
    MptObjInWith t S Nm mark ∧ NodeHeapValuePtrOK t Nm ∧
    IvlsDisj ((mark, 16) :: nodeExtents t Nm) (nodeExtents t Nd) ∧
    IvlsDisj (bmiWkRti s0) (worldTypedIvls t S Nd ++ mptObjIvls t Nm mark) ∧
    IvlsDisj [(locN s0 "slice_arr", 16 * locN s0 "n")]
      (worldOwned t S Nd ++ mptObjIvls t Nm mark) ∧
    (∀ o ∈ nodeExtents t Nm, mark ≤ o.1 ∧ o.1 + o.2 ≤ globN t "heap_ptr") ∧
    (∀ o ∈ worldOwned t S Nd, o = (0, 0) ∨
      (∃ j ∈ worldOwned s0 S0 Nd0, j.1 ≤ o.1 ∧ o.1 + o.2 ≤ j.1 + j.2) ∨
      (mark ≤ o.1 ∧ o.1 + o.2 ≤ globN t "heap_ptr")) ∧
    (∀ o ∈ worldOwned t S Nd, o = (0, 0) ∨
      Inside o sourceBase mark ∨ Inside o (globN t "scratch_ptr") scratchEnd) ∧
    (∀ r ∈ R10Shards.P26_P28.stdKeep, globN s0 r.1 ≠ 0 → ∀ k ∈ r.2,
      (∀ i ∈ bmiWkRti s0, ¬ CellHits (globN s0 r.1 + k) i) →
      memW t (globN s0 r.1 + k) = memW s0 (globN s0 r.1 + k)) ∧
    (∀ i, i < locN s0 "n" →
      memW t (locN s0 "slice_arr" + 16 * i) = memW s0 (locN s0 "slice_arr" + 16 * i) ∧
      memW t (locN s0 "slice_arr" + 16 * i + 8) = memW s0 (locN s0 "slice_arr" + 16 * i + 8))) ∧
  locN s0 "slice_arr" + 16 * locN s0 "n" ≤ mark ∧
  (∀ iv ∈ bmiWkRti s0, iv.1 + iv.2 ≤ mark) ∧
  globN t "mpt_key_scratch" = globN s0 "mpt_key_scratch" ∧
  globN t "mpt_key_scratch" ≠ 0 ∧
  (Inside (locN s0 "slice_arr", 16 * locN s0 "n") sourceBase (globN t "heap_ptr") ∧
    WordsOK t (locN s0 "slice_arr", 16 * locN s0 "n")) ∧
  IvlsDisj [(locN s0 "slice_arr", 16 * locN s0 "n")]
    (bmiWkRti s0 ++ worldOwned s0 S0 Nd0) ∧
  (∀ i, i < locN s0 "n" → memW s0 (locN s0 "slice_arr" + 16 * i) + 8 ≤ mark) ∧
  (∀ i, i < locN s0 "n" → ∀ iv ∈ keccakBufIvls s0, 0 < iv.2 →
    ¬ InIvl (memW s0 (locN s0 "slice_arr" + 16 * i)) iv) ∧
  mark + 16 ≤ globN t "heap_ptr"

/-- One plain call to an mpt callee covered by `BmiWkMptWW` extends the anchored chain. -/
theorem callee_locals_five_lookup {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 p4 p5 : MlS) (s1 s2 s3 s4 s5 : ShapeHOL)
    (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname =
      some ([(p1, s1), (p2, s2), (p3, s3), (p4, s4), (p5, s5)], body, ret))
    (values : List (ValueHOL 64)) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret' : ShapeHOL)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, ret)) :
    ∃ v1 v2 v3 v4 v5,
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧
      callee.lookup p3 = some v3 ∧ callee.lookup p4 = some v4 ∧ callee.lookup p5 = some v5 := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · exact absurd hlook (by simp)
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
      obtain ⟨hnd, hlen, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      rcases values with _ | ⟨v1, values⟩
      · simp at hlen
      rcases values with _ | ⟨v2, values⟩
      · simp at hlen
      rcases values with _ | ⟨v3, values⟩
      · simp at hlen
      rcases values with _ | ⟨v4, values⟩
      · simp at hlen
      rcases values with _ | ⟨v5, values⟩
      · simp at hlen
      refine ⟨v1, v2, v3, v4, v5, ?_, ?_, ?_, ?_, ?_⟩
      · simp [List.zip, List.zipWith, List.foldl, hnd.1.1, hnd.1.2.1, hnd.1.2.2.1, hnd.1.2.2.2]
      · simp [List.zip, List.zipWith, List.foldl, hnd.2.1.1, hnd.2.1.2.1, hnd.2.1.2.2]
      · simp [List.zip, List.zipWith, List.foldl, hnd.2.2.1.1, hnd.2.2.1.2]
      · simp [List.zip, List.zipWith, List.foldl, hnd.2.2.2.1]
      · simp [List.zip, List.zipWith, List.foldl]
    · exact absurd raw (by simp)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem bmiWkWW_mpt_set {F : Type} (Nm0 : List Nat) :
    BmiWkMptWW (F := F) bmiWkMptRm (fun s => BmiWkMptReady s Nm0) (ofString "mpt_set") := by
  refine ⟨_, _, _, P3MptSet.lookup_mpt_set, ?_⟩
  intro s hcode hP hlook hnt hres
  obtain ⟨vals, hlook⟩ := hlook
  obtain ⟨params, body, retSh, hreg, hspec⟩ := mk_mpt_set_eff_strong
  -- Pin the `mk_mpt_set_eff_strong` existentials to the `P3MptSet.lookup_mpt_set` triple that
  -- `hlook`/`hnt`/`hres` are stated at.
  have htup : some (params, body, retSh) =
      some ((sourceFunctionEntry Guest.Software.guestFn_mpt_set).2) :=
    hreg.symm.trans P3MptSet.lookup_mpt_set
  have htri : (params, body, retSh) =
      (sourceFunctionEntry Guest.Software.guestFn_mpt_set).2 := Option.some.inj htup
  have hp0 : params = (sourceFunctionEntry Guest.Software.guestFn_mpt_set).2.1 := by
    rw [← htri]
  have hb0 : body = (sourceFunctionEntry Guest.Software.guestFn_mpt_set).2.2.1 := by
    rw [← htri]
  have hr0 : retSh = (sourceFunctionEntry Guest.Software.guestFn_mpt_set).2.2.2 := by
    rw [← htri]
  subst hp0; subst hb0; subst hr0
  -- The `BmiWkMptReady` bundle supplies exactly the `write_frame` premises at `Nm0`.
  obtain ⟨hmsr, S, ⟨⟨hm_al, hm_w, -, -, hm_nh, hm_root, hm_ext⟩, hm_nhOK⟩, hextbuf, hmbuf,
    -, hspan, hm16⟩ := hP
  obtain ⟨hAr, hag, hgwK, -, hframe, -⟩ :=
    hspec s hcode hmsr ⟨vals, hlook⟩ hnt hres
  obtain ⟨hcell5, hbyte5⟩ := hframe Nm0 hm_al hm_w hm_nh hm_nhOK hm_root
    (fun o ho => ⟨(hm_ext o ho).1, hextbuf o ho⟩) hmbuf
  have hmemKeccak : ∀ ivl ∈ mptSetR_sc s, ivl ∈ bmiWkMptRm s := by
    intro ivl hivl
    simp only [bmiWkMptRm, bmiWkKeccakR_eq_mptSetR_sc]
    exact List.mem_cons_of_mem _ hivl
  have hmemB : ∀ gs ∈ mptSetB_sc, bufferRegion s gs ∈ bmiWkMptRm s := by
    intro gs hgs
    simp only [mptSetB_sc, List.mem_cons, List.mem_nil_iff, or_false] at hgs
    rcases hgs with rfl | rfl | rfl <;> simp [bmiWkMptRm, bmiWkKeccakR]
  refine ⟨hAr, hag.1, hag.2, ?_, ?_, hgwK⟩
  · intro a hne
    rcases hcell5 a hne with ⟨ivl, hivl, hcp0, hcp1, hcp2⟩ |
        ⟨gs, hgs, hcp0, hcp1, hcp2⟩ | ⟨o, ho, hcp0, hcp1, hcp2⟩ | hfg | hhf
    · exact Or.inl ⟨ivl, hmemKeccak ivl hivl, hcp0, hcp1, hcp2⟩
    · exact Or.inl ⟨bufferRegion s gs, hmemB gs hgs, hcp0, hcp1, hcp2⟩
    · obtain ⟨hm_lo, hm_hi⟩ := hspan o ho
      refine Or.inl ⟨(locN s "m", globN s "heap_ptr" - locN s "m"), ?_, ?_, ?_, ?_⟩
      · simp only [bmiWkMptRm]; exact List.mem_cons_self
      · show 0 < globN s "heap_ptr" - locN s "m"; omega
      · show locN s "m" < a.toNat + 8; omega
      · show a.toNat < locN s "m" + (globN s "heap_ptr" - locN s "m"); omega
    · simp only [Fast_C08WkShard03.CellHitsPos, CellHits, freeGap] at hfg
      obtain ⟨hfg1, hfg2, hfg3⟩ := hfg
      exact Or.inr (Or.inl ⟨hfg1, hfg2, by omega⟩)
    · simp only [Fast_C08WkShard03.CellHitsPos, CellHits, heapFree] at hhf
      obtain ⟨hhf1, hhf2, hhf3⟩ := hhf
      exact Or.inr (Or.inr ⟨hhf1, hhf2, by omega⟩)
  · intro b hb64 hne
    rcases hbyte5 b hb64 hne with ⟨ivl, hivl, hiv⟩ | ⟨gs, hgs, hiv⟩ | ⟨o, ho, hiv⟩ | hfg | hhf
    · simp only [InIvl] at hiv
      refine Or.inl ⟨ivl, hmemKeccak ivl hivl, ?_, hiv.1, hiv.2⟩
      omega
    · simp only [InIvl] at hiv
      refine Or.inl ⟨bufferRegion s gs, hmemB gs hgs, ?_, hiv.1, hiv.2⟩
      omega
    · obtain ⟨hm_lo, hm_hi⟩ := hspan o ho
      simp only [InIvl] at hiv
      refine Or.inl ⟨(locN s "m", globN s "heap_ptr" - locN s "m"), ?_, ?_, ?_, ?_⟩
      · simp only [bmiWkMptRm]; exact List.mem_cons_self
      · show 0 < globN s "heap_ptr" - locN s "m"; omega
      · show locN s "m" ≤ b; omega
      · show b < locN s "m" + (globN s "heap_ptr" - locN s "m"); omega
    · simp only [InIvl, freeGap] at hfg
      exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
    · simp only [InIvl, heapFree] at hhf
      exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)

theorem bmiWk_we_call_mpt_callee {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {Nm0 : List Nat} {Rl : List Ivl} {fname : MlS} {args : List (ExpHOL 64)}
    (h : R16Shards.WorldEff s0 t Rl [] (bmiWkGw : List String))
    (hRl : ∀ i ∈ bmiWkMptRm t, 0 < i.2 → ∃ j ∈ Rl, 0 < j.2 ∧ j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hww : BmiWkMptWW (F := F) bmiWkMptRm (fun s => BmiWkMptReady s Nm0) fname)
    (hPentry : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64)),
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some vals →
      BmiWkMptReady (callEntryStateHOLFinite t callee) Nm0)
    (hRmE : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64)),
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some vals →
      bmiWkMptRm (callEntryStateHOLFinite t callee) = bmiWkMptRm t)
    (hnt : (evaluateHOLFiniteState t (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState t (.call (some (none, none)) fname args)).1) :
    R16Shards.WorldEff s0
      (evaluateHOLFiniteState t (.call (some (none, none)) fname args)).2 Rl []
      (bmiWkGw : List String) := by
  obtain ⟨params, fbody, retSh, hlook, hspec⟩ := hww
  refine worldEff_call0_eff h fname args params fbody retSh hlook ?_ hnt hcr
  intro callee vals hvals hl
  dsimp only
  intro hnt' hres'
  have hRm' : bmiWkMptRm (callEntryStateHOLFinite t callee) = bmiWkMptRm t :=
    hRmE callee vals hvals
  have hcode_e : (callEntryStateHOLFinite t callee).code = originalRuntimeCode := h.code
  have hglob : ∀ k, globN (callEntryStateHOLFinite t callee) k = globN t k := fun _ => rfl
  -- The `BmiWkMptReady` bundle supplies exactly the `write_frame` premises at `Nm0`: feed the
  -- intact bundle to `hspec` and destructure a copy for the `write_frame` premises.
  have hbundle := hPentry callee vals hvals
  have hspec' := hspec (callEntryStateHOLFinite t callee) hcode_e hbundle
    ⟨vals, by rw [h.code] at hl; exact hl⟩ hnt' hres'
  obtain ⟨hAp', hhp', hspc', hcellWW, hbyteWW, hgwK'⟩ := hspec'
  set post' := (evaluateHOLFiniteState (callEntryStateHOLFinite t callee) fbody).2 with hpost'
  have hcell'' : ∀ a : BitVec 64, post'.memory a ≠ (callEntryStateHOLFinite t callee).memory a →
      (∃ i ∈ bmiWkMptRm t, 0 < i.2 ∧ i.1 < a.toNat + 8 ∧ a.toNat < i.1 + i.2) ∨
      (∃ j ∈ ([] : List Ivl), 0 < j.2 ∧ j.1 < a.toNat + 8 ∧ a.toNat < j.1 + j.2) ∨
      (0 < globN t "scratch_ptr" - globN t "frame_mem_ptr" ∧
        globN t "frame_mem_ptr" < a.toNat + 8 ∧ a.toNat < globN t "scratch_ptr") ∨
      (0 < heapLimit - globN t "heap_ptr" ∧
        globN t "heap_ptr" < a.toNat + 8 ∧ a.toNat < heapLimit) := by
    intro a hne
    have hc := hcellWW a hne
    simp only [hRm', hglob] at hc
    rcases hc with hR | hgap | hheap
    · exact Or.inl hR
    · exact Or.inr (Or.inr (Or.inl hgap))
    · exact Or.inr (Or.inr (Or.inr hheap))
  have hbyte'' : ∀ b : Nat, b < 2 ^ 64 → memB post' b ≠ memB (callEntryStateHOLFinite t callee) b →
      (∃ i ∈ bmiWkMptRm t, 0 < i.2 ∧ i.1 ≤ b ∧ b < i.1 + i.2) ∨
      (∃ j ∈ ([] : List Ivl), 0 < j.2 ∧ j.1 ≤ b ∧ b < j.1 + j.2) ∨
      (0 < globN t "scratch_ptr" - globN t "frame_mem_ptr" ∧
        globN t "frame_mem_ptr" ≤ b ∧ b < globN t "scratch_ptr") ∨
      (0 < heapLimit - globN t "heap_ptr" ∧
        globN t "heap_ptr" ≤ b ∧ b < heapLimit) := by
    intro b hb64 hne
    have hc := hbyteWW b hb64 hne
    simp only [hRm', hglob] at hc
    rcases hc with hR | hgap | hheap
    · exact Or.inl hR
    · exact Or.inr (Or.inr (Or.inl hgap))
    · exact Or.inr (Or.inr (Or.inr hheap))
  have hmeta := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) fbody
  refine bmiWk_we_callee_mpt (Wown := []) h hRl (by simp) hAp' hhp' hspc' hcell'' hbyte''
    (fun k hk => hgwK' k hk) ?_
    ⟨?_, ?_, ?_⟩ ?_
  · exact hmeta.1.trans hcode_e
  · exact hmeta.2.1
  · exact hmeta.2.2.1
  · exact hmeta.2.2.2.2
  · intro a hne
    by_contra h0
    rw [hpost'] at hne
    rw [evaluate_memory_eq_of_not_memaddrs (callEntryStateHOLFinite t callee) fbody a h0] at hne
    exact hne rfl

/-- One `rlp_encode_word` decCall extends the anchored chain: its `HeapByteEff` step has
`Sub := Rl` (trivial coverage), and the caller runs the continuation through `hcont`. -/
theorem bmiWk_we_decCall_rlp {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {cont : ProgHOL 64} {Rl : List Ivl} {dstExp wExp : ExpHOL 64}
    {dst0 w0 : BitVec 64} {lname : String}
    (h : R16Shards.WorldEff s0 t Rl [] (bmiWkGw : List String))
    (hdst : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hw : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) wExp =
      some (.val (.word w0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState t
      (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState t
      (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)).1)
    (hcont : ∀ (len : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      1 ≤ len.toNat → len.toNat ≤ 9 → dst0.toNat < heapEnd →
      mid.globals = t.globals →
      mid.locals = t.locals.update (ofString lname, .val (.word len)) →
      R16Shards.WorldEff s0 (evaluateHOLFiniteState mid cont).2 Rl [] (bmiWkGw : List String)) :
    R16Shards.WorldEff s0 (evaluateHOLFiniteState t
      (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)).2
      Rl [] (bmiWkGw : List String) := by
  obtain ⟨len, mid, hlen1, hlen9, hdst_lt, hmid_g, hmid_l, heff, hcr', hres', hrun⟩ :=
    eval_decCall_rlp_encode_word t lname dstExp wExp dst0 w0 cont Rl (bmiWkGw : List String)
      h.code h.arena hdst hw hin_ivl hnt hres
  have hmeta := evaluateHOLFiniteState_metadata t
    (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)
  have hes : mid.eshapes = t.eshapes := by
    have h1 := hmeta.2.2.2.2
    rw [hrun] at h1
    dsimp only at h1
    exact (evaluateHOLFiniteState_metadata mid cont).2.2.2.2.symm.trans h1
  have hwe := bmiWk_we_trans_heapByteEff h heff heff.arena.1.code hes
    (fun iv hiv _ => Or.inl ⟨iv, hiv, Nat.le_refl _, by omega⟩)
  have hwe' := hcont len mid hlen1 hlen9 hdst_lt hmid_g hmid_l
  rw [hrun]
  dsimp only
  exact hwe'.locals_clock _ _

/-! ## Section 4: the `while` loop

The loop runs on `R16Shards.WorldEff` with `Rl := bmiWkLoopRl s0 mark` (keep buffers
plus the whole fresh-heap tail) and the WIP typing invariant `BmiWkLoopInv`, augmented
with the root-allocation fact. -/


/-- The clock-decrement step of the loop invariant (record update keeps everything). -/
theorem BmiWkInv.dec {F : Type} {s0 : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    {mark : Nat} {t : PanSemStateFiniteExact 64 F} (h : BmiWkInv s0 S0 Nd0 mark t) :
    BmiWkInv s0 S0 Nd0 mark (decClockHOLFinite t) := by
  obtain ⟨hA, hmark, hm, hmlk, hsalk, hn, hsa, hout, hmark_hp, hhp_lim, hk1, hk2, hfmp,
    hhs, hsp, htyping, hsl_mark, hrti, hkey, hkey0, hslbuf, hc4, hc5, h16⟩ := h
  obtain ⟨S, Nd, Nm, hWT, hmpt, hnh, hdj1, hdj2, hdj3, hext, hown, hown2, hkeep,
    hslicew⟩ := htyping
  refine ⟨localsFree_arenaReady t t.locals (t.clock - 1) hA, hmark, hm, hmlk, hsalk, hn,
    hsa, hout, hmark_hp, hhp_lim, hk1, hk2, hfmp, hhs, hsp, ?_, hsl_mark, hrti, hkey,
    hkey0, hslbuf, hc4, hc5, h16⟩
  refine ⟨S, Nd, Nm, ?_, ?_, ?_, hdj1, hdj2, hdj3, hext, hown, hown2, hkeep, hslicew⟩
  · exact (worldTypedWith_build_locals t t.locals (t.clock - 1) S Nd).2 hWT
  · exact hmpt
  · exact hnh

/-- Locals/clock changes keep the invariant, given the five pinned locals. -/
theorem BmiWkInv.locals {F : Type} {s0 : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    {mark : Nat} {t : PanSemStateFiniteExact 64 F}
    (h : BmiWkInv s0 S0 Nd0 mark t)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hmark : locN {t with locals := locals, clock := k} "mark" = mark)
    (hmlk : {t with locals := locals, clock := k}.locals.lookup (ofString "m") =
      t.locals.lookup (ofString "m"))
    (hsalk : {t with locals := locals, clock := k}.locals.lookup (ofString "slice_arr") =
      t.locals.lookup (ofString "slice_arr"))
    (hn : locN {t with locals := locals, clock := k} "n" = locN s0 "n")
    (hsa : locN {t with locals := locals, clock := k} "slice_arr" = locN s0 "slice_arr")
    (hout : locN {t with locals := locals, clock := k} "out" = locN s0 "out") :
    BmiWkInv s0 S0 Nd0 mark {t with locals := locals, clock := k} := by
  obtain ⟨hA, hmark0, hm0, hmlk0, hsalk0, hn0, hsa0, hout0, hmark_hp, hhp_lim, hk1, hk2,
    hfmp, hhs, hsp, htyping, hsl_mark, hrti, hkey, hkey0, hslbuf, hc4, hc5, h16⟩ := h
  obtain ⟨S, Nd, Nm, hWT, hmpt, hnh, hdj1, hdj2, hdj3, hext, hown, hown2, hkeep,
    hslicew⟩ := htyping
  refine ⟨localsFree_arenaReady t locals k hA, hmark,
    (by unfold locN; rw [hmlk]; exact hm0), (by rw [hmlk]; exact hmlk0),
    (by rw [hsalk]; exact hsalk0), hn, hsa, hout,
    hmark_hp, hhp_lim, hk1, hk2, hfmp, hhs, hsp, ?_, hsl_mark, hrti, hkey, hkey0,
    hslbuf, hc4, hc5, h16⟩
  refine ⟨S, Nd, Nm, ?_, ?_, ?_, hdj1, hdj2, hdj3, hext, hown, hown2, hkeep, hslicew⟩
  · exact (worldTypedWith_build_locals t locals k S Nd).2 hWT
  · exact hmpt
  · exact hnh



/-! ## Section 4b: the loop body's eval-level chain -/

/-- One `HeapByteEff` step with the loop's `Rl` keeps every slice word in
`[slice_arr, slice_arr + 16 * n)` (their cells are below `mark`, hence outside
every write region of the step). -/
theorem bmiWk_slice_word_kept {F : Type} {s0 t mid : PanSemStateFiniteExact 64 F}
    {S0 Nd0 : List Nat} (hinv : BmiWkInv s0 S0 Nd0 (locN s0 "mark") t)
    (hbe : HeapByteEff t mid (bmiWkRl s0 (locN s0 "mark") S0 Nd0) (bmiWkGw : List String))
    (i : Nat) (hlt : i < locN s0 "n") :
    memW mid (locN s0 "slice_arr" + 16 * i) = memW t (locN s0 "slice_arr" + 16 * i) ∧
    memW mid (locN s0 "slice_arr" + 16 * i + 8) = memW t (locN s0 "slice_arr" + 16 * i + 8) := by
  obtain ⟨hA, hmark, hm, hmlk, hsalk, hn, hsa, hout, hmark_hp, hhp_lim, hk1, hk2, hfmp,
    hhs, hsp, htyping, hsl_mark, hrti, hkey, hkey0, hslin, hslbuf, hc4, hc5, h16⟩ := hinv
  have hss : scratchStart = heapLimit := rfl
  have hcell_of : ∀ x : Nat, locN s0 "slice_arr" ≤ x →
      x + 8 ≤ locN s0 "slice_arr" + 16 * locN s0 "n" →
      mid.memory (BitVec.ofNat 64 x) = t.memory (BitVec.ofNat 64 x) := by
    intro x hlo hxb
    have hlim : heapLimit < 18446744073709551616 := by decide
    have hx64 : x < 18446744073709551616 := by omega
    by_contra hne
    have htn : (BitVec.ofNat 64 x).toNat = x := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hx64
    rcases hbe.cell_frame _ hne with ⟨ivl, hivl, h0, hc1, hc2⟩ | hfg | hhf
    · rw [htn] at hc1 hc2
      rcases List.mem_append.mp hivl with hj1 | hj
      · rcases List.mem_append.mp hj1 with hj | hj
        · have hd := hslbuf (locN s0 "slice_arr", 16 * locN s0 "n") List.mem_cons_self
            ivl (List.mem_append.2 (Or.inl hj))
          rcases hd with h | h | h | h
          · omega
          · omega
          · omega
          · omega
        · have hv : ivl = (locN s0 "mark", heapLimit - locN s0 "mark") :=
            List.mem_singleton.mp hj
          have h1' : ivl.1 = locN s0 "mark" := by rw [hv]
          have h2' : ivl.2 = heapLimit - locN s0 "mark" := by rw [hv]
          rw [h1'] at hc1
          rw [h2'] at hc2
          omega
      · have hd := hslbuf (locN s0 "slice_arr", 16 * locN s0 "n") List.mem_cons_self
          ivl (List.mem_append.2 (Or.inr hj))
        rcases hd with h | h | h | h
        · omega
        · omega
        · omega
        · omega
    · unfold freeGap at hfg
      rw [htn] at hfg
      unfold InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.CellHitsPos
        InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.CellHitsPos CellHits at hfg
      rw [show (globN t "frame_mem_ptr", globN t "scratch_ptr" - globN t "frame_mem_ptr").1 =
          globN t "frame_mem_ptr" from rfl,
        show (globN t "frame_mem_ptr", globN t "scratch_ptr" - globN t "frame_mem_ptr").2 =
          globN t "scratch_ptr" - globN t "frame_mem_ptr" from rfl] at hfg
      have e1 : x + 8 ≤ locN s0 "mark" := by omega
      have e2 : locN s0 "mark" + 16 ≤ globN t "heap_ptr" := by omega
      have e3 : globN t "heap_ptr" ≤ heapLimit := hhp_lim
      have e4 : scratchStart ≤ globN t "frame_mem_ptr" := hA.2.2.2.1
      have e5 : x + 8 ≤ scratchStart := by omega
      omega
    · unfold heapFree at hhf
      rw [htn] at hhf
      unfold InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.CellHitsPos
        InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.CellHitsPos CellHits at hhf
      rw [show (globN t "heap_ptr", heapLimit - globN t "heap_ptr").1 =
          globN t "heap_ptr" from rfl,
        show (globN t "heap_ptr", heapLimit - globN t "heap_ptr").2 =
          heapLimit - globN t "heap_ptr" from rfl] at hhf
      omega
  refine ⟨by simp only [memW, hcell_of (locN s0 "slice_arr" + 16 * i) (by omega) (by omega)],
    by simp only [memW,
      hcell_of (locN s0 "slice_arr" + 16 * i + 8) (by omega) (by omega)]⟩

/-- The loop's coverage fact: every region the mpt callees may touch (`Rm`) is
covered by a positive-length region of the loop's region list. -/
theorem bmiWkLoop_hRl {F : Type} {s0 : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    {mark : Nat} {t : PanSemStateFiniteExact 64 F} (hinv : BmiWkInv s0 S0 Nd0 mark t) :
    ∀ i ∈ bmiWkMptRm t, 0 < i.2 →
      ∃ j ∈ bmiWkRl s0 mark S0 Nd0, 0 < j.2 ∧ j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
  obtain ⟨hA, hmark, hm, hmlk, hsalk, hn, hsa, hout, hmark_hp, hhp_lim, hk1, hk2, hfmp,
    hhs, hsp, htyping, hsl_mark, hrti, hkey, hkey0, hslbuf, hc4, hc5, h16⟩ := hinv
  intro i hi hi2
  obtain ⟨a, b⟩ := i
  simp only [bmiWkMptRm, bmiWkKeccakR, bufferRegion] at hi
  rcases List.mem_cons.mp hi with heq | hi
  · -- the m-span: covered by the fresh-heap tail
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine ⟨(mark, heapLimit - mark),
      List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))),
      ?_, ?_, ?_⟩
    all_goals omega
  · rcases List.mem_cons.mp hi with heq | hi
    · -- keccak_pad
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hne : globN t "keccak_pad" ≠ 0 := by
        intro h0; rw [h0] at hi2; simp at hi2
      have hs0ne : globN s0 "keccak_pad" ≠ 0 := by
        intro h0; apply hne; rw [hk1]; exact h0
      refine ⟨(globN s0 "keccak_pad", if globN s0 "keccak_pad" = 0 then 0 else 136),
        List.mem_append.2 (Or.inl ?_), ?_, ?_, ?_⟩
      · simp only [bmiWkRti]
        exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
      · rw [if_neg hs0ne]; omega
      · omega
      · rw [if_neg hne, if_neg hs0ne]; omega
    · rcases List.mem_cons.mp hi with heq | hi
      · -- keccak_st
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hne : globN t "keccak_st" ≠ 0 := by
          intro h0; rw [h0] at hi2; simp at hi2
        have hs0ne : globN s0 "keccak_st" ≠ 0 := by
          intro h0; apply hne; rw [hk2]; exact h0
        refine ⟨(globN s0 "keccak_st", if globN s0 "keccak_st" = 0 then 0 else 200),
          List.mem_append.2 (Or.inl ?_), ?_, ?_, ?_⟩
        · simp only [bmiWkRti]
          exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))
        · rw [if_neg hs0ne]; omega
        · omega
        · rw [if_neg hne, if_neg hs0ne]; omega
      · rcases List.mem_cons.mp hi with heq | hi
        · -- mpt_hash_scratch
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          have hne : globN t "mpt_hash_scratch" ≠ 0 := by
            intro h0; rw [h0] at hi2; simp at hi2
          have hs0ne : globN s0 "mpt_hash_scratch" ≠ 0 := by
            intro h0; apply hne; rw [hhs]; exact h0
          refine ⟨(globN s0 "mpt_hash_scratch", if globN s0 "mpt_hash_scratch" = 0 then 0 else 40),
            List.mem_append.2 (Or.inl ?_), ?_, ?_, ?_⟩
          · simp only [bmiWkRti]
            exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2
              (Or.inr (List.mem_cons.2 (Or.inl rfl)))))))
          · rw [if_neg hs0ne]; omega
          · omega
          · rw [if_neg hne, if_neg hs0ne]; omega
        · cases hi

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
