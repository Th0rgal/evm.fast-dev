import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongTail4
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongDelta

/-!
# Phase 2 backing replay, pre-`msg_new` part (guest spine 34..69)

This module threads the auxiliary conjunct `PtxPhase2X` through the Phase 2
segment bounds of `PtxPhase2Strong` (regions 34..44, 44..53 and 53..69),
so that the pre-`msg_new` backing bridge documented in the header of
`PtxPhase2StrongTail4` can be closed: at guest spine 69 the state satisfies
`PtxMsgPreBInv` for the degenerate buffer family, which requires
`PtxTeSufInv` (from the segment chain), `TxEnv`, `TxBacking` and
`PtxPhase4LocalShapes` (threaded here), and a live degenerate buffer.

`PtxPhase2X` bundles exactly the four caller-frame facts that are lost by
the fixed segment-exit guards and reappear in `PtxMsgPreBInv`:

* `PtxPhase2MgasW` — the `mgas` caller local is a word below `2 ^ 27 + 1`;
  this is the value stored at message offset 40 (guest spine 73) and is the
  source of the `memW s (locN s "m" + 40) < 2 ^ 63` bound demanded by the
  Phase 2 backing cut.
* `R16Shards.TxBacking` — the two block-out list data pointers stay live.
* `TxEnv` — the block-out record cells stay valid.
* `R16Shards.PtxPhase4LocalShapes` — the Phase 4 caller-local shapes.

All four are either pure caller-local facts or facts about the block-out
record cells, which are fixed objects disjoint from every buffer the
Phase 2 segments write. The per-step preservation lemmas below make this
precise; they are then used to replay the segment chains of
`PtxPhase2Strong` with the conjunct carried along.
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

/-! ## The auxiliary conjunct -/

/-- The `mgas` caller local is a word below the protocol gas bound. The
value is stored at message offset 40 at guest spine 73; the bound is the
source of the `2 ^ 63` message-gas bound of the Phase 2 backing cut. -/
def PtxPhase2MgasW {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w : BitVec 64, s.locals.lookup (ofString "mgas") = some (.val (.word w)) ∧
    w.toNat ≤ 16777216

/-- The auxiliary caller-frame conjunct threaded through the 34..69 replay:
message-gas word bound, block-out backing pointers, block-out record cells,
and the Phase 4 local shapes. -/
def PtxPhase2X {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPhase2MgasW s ∧ TxBacking s ∧ TxEnv s ∧ R16Shards.PtxPhase4LocalShapes s

/-- The caller locals the auxiliary conjunct reads. -/
def ptxPhase2XNames : List String :=
  ["mgas", "index", "tx", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"]

/-- The Phase 4 local shapes follow from the Phase 2 local shapes: the five
Phase 4 scalar names are among the Phase 2 scalar names, and the `price`
and `intrinsic` struct shapes agree with the record layouts. -/
theorem ptxPhase4LocalShapes_of_phase2 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : PtxPhase2LocalShapes s) : R16Shards.PtxPhase4LocalShapes s := by
  refine ⟨fun name hn => h.scalar name (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> simp), ?_, ?_⟩
  · obtain ⟨a, b, c, d, hprice⟩ := h.price
    exact ⟨.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)],
      hprice, by simp [shapeOfHOLExact]⟩
  · obtain ⟨a, b, c, hintr⟩ := h.intrinsic
    exact ⟨.rStruct [.val (.word a), .val (.word b), .val (.word c)], hintr, by simp [shapeOfHOLExact]⟩

/-- The auxiliary conjunct holds at the Phase 2 entry: the gas word bound is
`ptxValidatedStrong_mgas`, the backing conjunct is the entry guard's own,
the environment record cells come from the ready state, and the Phase 4
shapes are a projection of the Phase 2 shapes. -/
theorem ptxPhase2X_of_entry {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxValidatedBackingStrong s) : PtxPhase2X s :=
  ⟨ptxValidatedStrong_mgas hp.1, hp.2, PtxP1.txEnv_of_ready hp.1.1.1,
    ptxPhase4LocalShapes_of_phase2 hp.1.2⟩

/-! ## Locals- and clock-insensitivity -/

/-- The auxiliary conjunct only reads the listed caller locals. -/
theorem ptxPhase2X_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ n ∈ ptxPhase2XNames, locals.lookup (ofString n) =
      s.locals.lookup (ofString n))
    (hp : PtxPhase2X s) : PtxPhase2X {s with locals := locals, clock := clock} := by
  have hmgas := hl "mgas" (by simp [ptxPhase2XNames])
  have hidx := hl "index" (by simp [ptxPhase2XNames])
  have htx := hl "tx" (by simp [ptxPhase2XNames])
  have hsender := hl "sender" (by simp [ptxPhase2XNames])
  have hgas := hl "gas" (by simp [ptxPhase2XNames])
  have hblob := hl "tx_blob_gas_used" (by simp [ptxPhase2XNames])
  have hprice := hl "price" (by simp [ptxPhase2XNames])
  have hintr := hl "intrinsic" (by simp [ptxPhase2XNames])
  obtain ⟨⟨w, hw, hwb⟩, hback, henv, hshapes⟩ := hp
  refine ⟨⟨w, hmgas ▸ hw, hwb⟩, (R16Shards.txBacking_with_locals s locals clock).mp hback,
    ⟨henv.bo_nz, henv.bo24, henv.bo32, henv.bo40, henv.bo72, ?_, henv.jcap_nz⟩, ?_⟩
  · rw [locN_congr s locals clock "index" hidx]
    exact henv.idx_lt
  · refine ⟨fun name hn => ?_, ?_, ?_⟩
    · obtain ⟨w', hw'⟩ := hshapes.1 name hn
      refine ⟨w', ?_⟩
      show locals.lookup (ofString name) = _
      rw [hl name (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl <;> simp [ptxPhase2XNames])]
      exact hw'
    · obtain ⟨v, hv, hshape⟩ := hshapes.2.1
      refine ⟨v, ?_, hshape⟩
      show locals.lookup (ofString "price") = _
      rw [hprice]
      exact hv
    · obtain ⟨v, hv, hshape⟩ := hshapes.2.2
      refine ⟨v, ?_, hshape⟩
      show locals.lookup (ofString "intrinsic") = _
      rw [hintr]
      exact hv

/-! ## Cell-preservation helpers -/

/-- The gas-word bound transfers along a locals substitution. -/
theorem ptxPhase2MgasW_with_locals {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hloc : post.locals = s.locals) (h : PtxPhase2MgasW s) : PtxPhase2MgasW post := by
  obtain ⟨w, hw, hb⟩ := h
  refine ⟨w, ?_, hb⟩
  rw [hloc]
  exact hw

/-- The Phase 4 local shapes transfer along a locals substitution. -/
theorem ptxPhase4LocalShapes_with_locals {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hloc : post.locals = s.locals)
    (h : R16Shards.PtxPhase4LocalShapes s) : R16Shards.PtxPhase4LocalShapes post := by
  refine ⟨fun name hn => ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := h.1 name hn
    refine ⟨w, ?_⟩
    rw [hloc]
    exact hw
  · obtain ⟨v, hv, hshape⟩ := h.2.1
    refine ⟨v, ?_, hshape⟩
    rw [hloc]
    exact hv
  · obtain ⟨v, hv, hshape⟩ := h.2.2
    refine ⟨v, ?_, hshape⟩
    rw [hloc]
    exact hv

/-- The environment record transfers to a state whose `bo` and `journal_cap`
globals, `index` local and five record cells agree with the original. -/
theorem ptxPhase2_txEnv_of_cells {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : TxEnv s)
    (hbo : globN post "bo" = globN s "bo")
    (hjc : globN post "journal_cap" = globN s "journal_cap")
    (hidx : locN post "index" = locN s "index")
    (hcells : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k)) :
    TxEnv post := by
  refine ⟨by rw [hbo]; exact h.bo_nz, ?_, ?_, ?_, ?_, ?_, by rw [hjc]; exact h.jcap_nz⟩
  · rw [hbo, hcells 24 (by simp)]; exact h.bo24
  · rw [hbo, hcells 32 (by simp)]; exact h.bo32
  · rw [hbo, hcells 40 (by simp)]; exact h.bo40
  · rw [hbo, hcells 72 (by simp)]; exact h.bo72
  · rw [hbo, hcells 80 (by simp), hidx]; exact h.idx_lt

/-- The auxiliary conjunct transfers to a state that agrees with the original
on the caller locals, the two `bo`/`journal_cap` globals, the `index` local
and the five block-out record cells. -/
theorem ptxPhase2X_of_cells {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hp : PtxPhase2X s)
    (hback : TxBacking post)
    (hloc : post.locals = s.locals)
    (hbo : globN post "bo" = globN s "bo")
    (hjc : globN post "journal_cap" = globN s "journal_cap")
    (hidx : locN post "index" = locN s "index")
    (hcells : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k)) :
    PtxPhase2X post :=
  ⟨ptxPhase2MgasW_with_locals hloc hp.1, hback, ptxPhase2_txEnv_of_cells hp.2.2.1 hbo hjc hidx
    hcells, ptxPhase4LocalShapes_with_locals hloc hp.2.2.2⟩

/-! ## Single-store preservation -/

/-- A memory change at one cell outside every block-out record cell (and the
two list-header data words) preserves the auxiliary conjunct: the gas word,
backing pointers, environment record and Phase 4 shapes are caller-local or
block-out facts, and the stored cell misses all of them. -/
theorem ptxPhase2X_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x : BitVec 64} {mem : BitVec 64 → HolWordLab 64}
    (hp : PtxPhase2X s)
    (hm : ∀ a, a ≠ x → mem a = s.memory a)
    (hcells : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      BitVec.ofNat 64 (globN s "bo" + k) ≠ x)
    (hptrs : ∀ k ∈ ([40, 72] : List Nat),
      BitVec.ofNat 64 (memW s (globN s "bo" + k)) ≠ x) :
    PtxPhase2X {s with memory := mem} := by
  have hmemW : ∀ p : Nat, BitVec.ofNat 64 p ≠ x →
      memW {s with memory := mem} p = memW s p := by
    intro p hpx
    unfold memW
    dsimp only
    rw [hm _ hpx]
  have hslots : ∀ k ∈ ([40, 72] : List Nat),
      BitVec.ofNat 64 (globN s "bo" + k) ≠ x := fun k hk => hcells k (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> simp)
  refine ptxPhase2X_of_cells hp (R16Shards.txBacking_store hp.2.1 hm hslots hptrs) rfl rfl rfl
    rfl ?_
  intro k hk
  exact hmemW (globN s "bo" + k) (hcells k hk)

/-! ## Fine-frame preservation across callee steps -/

/-- Any word whose 8-byte cell lies below the old heap top and outside the
callee's keep-set is preserved by a fine `FrameOutside` frame. Public
companion of the private `Tail4.memW_eq_of_fine_frame`. -/
theorem ptxPhase2_memW_eq_of_frameOutside {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {K : List Ivl} {a : Nat}
    (hA : ArenaReady s)
    (hfr : FrameOutside s post K
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hkeep : ∀ i ∈ K, ¬ CellHits a i) (halt : a + 8 ≤ globN s "heap_ptr") :
    memW post a = memW s a := by
  obtain ⟨-, hs_hp, -, -, -, -, -, -, -⟩ := hA.2
  have hlim : heapLimit ≤ 2 ^ 64 := by decide
  have ha_lt : a < 2 ^ 64 := by omega
  have haddr : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hm : post.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a) :=
    hfr _ (fun i hi hci => by rw [haddr] at hci; exact hkeep i hi hci) (fun hcf => by
      rw [haddr] at hcf
      unfold CellHits at hcf
      obtain ⟨h1, h2⟩ := hcf
      omega)
  unfold memW
  rw [hm]

/-- The auxiliary conjunct is preserved by a callee step whose memory writes
a `FrameOutside` frame confines to the keep-set plus fresh heap growth, whose
globals keep `bo` and `journal_cap`, and whose locals are the caller's: the
five block-out record cells and the two list-header data words all lie below
the old heap top and outside the keep-set. -/
theorem ptxPhase2X_of_fine_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {K : List Ivl}
    (hp : PtxPhase2X s) (hA : ArenaReady s)
    (hloc : post.locals = s.locals)
    (hbo : globN post "bo" = globN s "bo")
    (hjc : globN post "journal_cap" = globN s "journal_cap")
    (hfr : FrameOutside s post K
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hboHeap : globN s "bo" + 88 ≤ globN s "heap_ptr")
    (hp40 : memW s (globN s "bo" + 40) + 8 ≤ globN s "heap_ptr")
    (hp72 : memW s (globN s "bo" + 72) + 8 ≤ globN s "heap_ptr")
    (hK : ∀ i ∈ K, ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      ¬ CellHits (globN s "bo" + k) i ∧ ¬ CellHits (memW s (globN s "bo" + 40)) i ∧
      ¬ CellHits (memW s (globN s "bo" + 72)) i) :
    PtxPhase2X post := by
  have hmemW : ∀ a : Nat, a + 8 ≤ globN s "heap_ptr" → (∀ i ∈ K, ¬ CellHits a i) →
      memW post a = memW s a := fun a halt hk =>
    ptxPhase2_memW_eq_of_frameOutside hA hfr hk halt
  have hidx : locN post "index" = locN s "index" := by
    unfold locN
    rw [hloc]
  refine ptxPhase2X_of_cells hp
    (phase2_txBacking_of_fine_frame hA hp.2.1 hbo hfr (by omega) hp40 hp72
      (fun i hi => ⟨fun hc => (hK i hi 40 (by simp)).1 hc,
        fun hc => (hK i hi 72 (by simp)).1 hc,
        fun hc => (hK i hi 40 (by simp)).2.1 hc,
        fun hc => (hK i hi 72 (by simp)).2.2 hc⟩))
    hloc hbo hjc hidx ?_
  intro k hk
  have hcell : globN s "bo" + k + 8 ≤ globN s "heap_ptr" := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
  exact hmemW (globN s "bo" + k) hcell (fun i hi => (hK i hi k hk).1)

/-! ## Section 3: region A (guest spine 34..44) -/

/-- Every address strictly below `p` or at/above `p + 200` reads the same
word through `zeroBlock25 m p` as through `m`: the 25 zeroed words all sit
in `[p, p + 200)`, and each of them is `p + c` with `c ≤ 192`. Copy of the
private `zeroBlock25_keep` (`PtxPhase2StrongTail4`), which cannot be
imported. -/
private theorem ptxPhase2_zeroBlock25_keep (m : BitVec 64 → HolWordLab 64)
    (p a : BitVec 64) (hple : p.toNat ≤ 2952790016)
    (ha : a.toNat + 8 ≤ p.toNat ∨ p.toNat + 200 ≤ a.toNat) :
    InitECandidate.Solver.Wave8Contracts.M27.zeroBlock25 m p a = m a := by
  have key : ∀ c : BitVec 64, c.toNat ≤ 192 → a = p + c → False := by
    intro c hcle hc
    have hc1 : a.toNat = p.toNat + c.toNat := by
      rw [hc, BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    rcases ha with ha | ha
    · omega
    · omega
  have ifneg : ∀ {α : Type} (x y : α) (c : BitVec 64), c.toNat ≤ 192 →
      (if a = p + c then x else y) = y := fun x y c hcle =>
    if_neg (fun hc => key c hcle hc)
  have ifneg2 : ∀ {α : Type} (x y : α) (c d : BitVec 64), c.toNat + d.toNat ≤ 192 →
      (if a = p + c + d then x else y) = y := fun x y c d hcd =>
    if_neg (fun hc => key (c + d) (by
        rw [BitVec.toNat_add]
        exact Nat.le_trans (Nat.mod_le _ _) hcd)
      (hc.trans (BitVec.add_assoc p c d)))
  unfold InitECandidate.Solver.Wave8Contracts.M27.zeroBlock25
    InitECandidate.Solver.Wave8Contracts.M27.updW_te
  simp (discharger := decide) only [ifneg, ifneg2]

/-- Any region allocated at `s` — heap or scratch — is untouched by an
empty-keep frame whose only memory writes sit inside the fresh heap gap
`[heap_ptr, post-heap_ptr)`. Modeled on the side-agnostic
`phase2_htab_new_frame_unhit` (`PtxPhase2StrongDelta`), which needs the full
`ArenaReady post`; here only the post heap bound is available (the callee
keeps every other global). -/
theorem ptxPhase2_fresh_frame_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) (hhp' : globN post "heap_ptr" ≤ heapLimit)
    (hfr : FrameOutside s post []
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    {i : Ivl} (hai : Allocated s i) : IvlUnhit s post i := by
  have hhl : heapLimit = 2952790016 := rfl
  have hss : InitE.scratchStart = 2952790016 := rfl
  have hsep : heapLimit ≤ InitE.scratchStart := by decide
  have hsb : InitE.sourceBase ≤ globN s "heap_ptr" := hs.2.1
  have hhp : globN s "heap_ptr" ≤ heapLimit := hs.2.2.1
  have hp8 : globN s "heap_ptr" % 8 = 0 := hs.2.2.2.2.2.2.1
  have hsc : InitE.scratchStart ≤ globN s "scratch_ptr" :=
    Nat.le_trans hs.2.2.2.1 hs.2.2.2.2.1
  intro a ha8 hh
  unfold CellHits at hh
  obtain ⟨hh1, hh2⟩ := hh
  rcases hai with hheap | hscr
  · unfold Inside at hheap
    obtain ⟨he1, he2⟩ := hheap
    apply hfr a
    · intro j hj
      exact absurd hj (by simp)
    · unfold CellHits
      intro hcon
      obtain ⟨hc1, _⟩ := hcon
      dsimp only at hc1
      omega
  · unfold Inside at hscr
    obtain ⟨hs1, hs2⟩ := hscr
    apply hfr a
    · intro j hj
      exact absurd hj (by simp)
    · unfold CellHits
      intro hcon
      obtain ⟨_, hc2⟩ := hcon
      dsimp only at hc2
      omega

/-- The raw `te_new` body run (`M27.te_new_body_run`) yields: the post heap
top stays under `heapLimit`, every global but `heap_ptr` is preserved, and
the only memory writes are the 200 zeroed bytes of the fresh block, i.e. an
empty-keep `FrameOutside` frame over the fresh heap gap. -/
theorem ptxPhase2_te_new_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {retVal : ValueHOL 64}
    (hA : ArenaReady s)
    (hrun : evaluateHOLFiniteState s
        (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1 =
      (some (.returned retVal), post)) :
    globN post "heap_ptr" ≤ heapLimit ∧
    (∀ n : MlS, n ≠ ofString "heap_ptr" →
      post.globals.lookup n = s.globals.lookup n) ∧
    FrameOutside s post []
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  obtain ⟨hGI, hAO⟩ := hA
  have hcode : s.code = originalRuntimeCode := hGI.1
  obtain ⟨hp, hhp⟩ := hAO.2.2.2.2.2.2.2.2 "heap_ptr" (by simp [guestGlobalNames])
  have hhp' : s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) := hhp
  have hgs : globN s "heap_ptr" = hp.toNat := by unfold globN; rw [hhp]
  have hp_align : hp.toNat % 8 = 0 := by rw [← hgs]; exact hAO.2.2.2.2.2.1
  have hp_le_lim : hp.toNat ≤ 2952790016 := by
    have hhl : heapLimit = 2952790016 := rfl
    rw [← hgs, ← hhl]
    exact hAO.2.1
  have hdom_fn : ∀ (q : BitVec 64), q.toNat ≤ 2952790016 → q.toNat = hp.toNat + 200 →
      ∀ off : Nat, off < 200 → off % 8 = 0 → s.memaddrs (hp + BitVec.ofNat 64 off) := by
    intro q hq_le hq_nat off hoff hmod
    rw [hGI.2, InitECandidate.Solver.Wave8Contracts.M28.ordinaryDomain_iff]
    have hlo_hp : InitE.sourceBase ≤ hp.toNat := by rw [← hgs]; exact hAO.1
    have hadd_nat : (hp + BitVec.ofNat 64 off).toNat = hp.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have hhe : InitE.heapEnd = 33806089704 := by decide
    rw [hadd_nat]
    exact ⟨by omega, by omega, by omega⟩
  obtain ⟨-, hq_nat, hq_le, hpost_mem, hpost_glob, -, -, -, -⟩ :=
    InitECandidate.Solver.Wave8Contracts.M27.te_new_body_run s post hp retVal hcode hhp'
      hp_align hp_le_lim hdom_fn hrun
  have hgp : globN post "heap_ptr" = hp.toNat + 200 := by
    unfold globN
    rw [hpost_glob]
    simp only [HolFiniteMapExact.lookup_update, FUPDATE]
    exact hq_nat
  have hq2 : hp.toNat + 200 ≤ heapLimit := hq_nat ▸ hq_le
  refine ⟨by rw [hgp]; exact hq2, ?_, ?_⟩
  · intro n hn
    rw [hpost_glob]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]
  · intro a _ hcf
    have hreg : a.toNat + 8 ≤ hp.toNat ∨ hp.toNat + 200 ≤ a.toNat := by
      unfold CellHits at hcf
      rw [hgs, hgp] at hcf
      omega
    have hkeep := ptxPhase2_zeroBlock25_keep s.memory hp a hp_le_lim hreg
    rw [hpost_mem, hkeep]

/-- `PtxPhase4LocalShapes` survives storing the returned `te` pointer: none
of the Phase 4 local names is `te`. -/
theorem ptxPhase4LocalShapes_setVar_te {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (h : R16Shards.PtxPhase4LocalShapes s) :
    R16Shards.PtxPhase4LocalShapes
      (setVarHOLFinite (ofString "te") v { post with locals := s.locals }) := by
  have hlu : ∀ name : String, ofString name ≠ ofString "te" →
      (setVarHOLFinite (ofString "te") v { post with locals := s.locals }).locals.lookup
        (ofString name) = s.locals.lookup (ofString name) := by
    intro name hn
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hn]
  refine ⟨?_, ?_, ?_⟩
  · intro name hn
    have hne : ofString name ≠ ofString "te" := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hlu name hne]
    exact h.1 name hn
  · rw [hlu "price" (by decide)]; exact h.2.1
  · rw [hlu "intrinsic" (by decide)]; exact h.2.2

/-- Side-agnostic preservation of the block-out record cells and of the two
pointed list headers across an empty-keep fresh-heap frame: the `bo` record
and the `lst`-40/72 headers are fixed objects (`FixedTyped`), hence
allocated on either side of the arena, and every allocated region is
untouched by the frame. -/
theorem ptxPhase2_fresh_cells {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat}
    (hA : ArenaReady s) (hw : WorldTypedWith s S Nd)
    (hnz : globN s "bo" ≠ 0)
    (h40 : memW s (globN s "bo" + 40) ≠ 0) (h72 : memW s (globN s "bo" + 72) ≠ 0)
    (hhp' : globN post "heap_ptr" ≤ heapLimit)
    (hbo : globN post "bo" = globN s "bo")
    (hfr : FrameOutside s post []
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    (∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k)) ∧
    memW post (memW s (globN s "bo" + 40)) = memW s (memW s (globN s "bo" + 40)) ∧
    memW post (memW s (globN s "bo" + 72)) = memW s (memW s (globN s "bo" + 72)) := by
  obtain ⟨hGI, hAO⟩ := hA
  have hF : FixedTyped s := hw.2.2.1
  have hbo_al := bo_words hF hnz
  have hu : IvlUnhit s post (globN s "bo", 88) :=
    ptxPhase2_fresh_frame_unhit ⟨hGI, hAO⟩ hhp' hfr hbo_al.1
  have hlst : ∀ k ∈ ([40, 72] : List Nat),
      (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [fixedObjects, blockOutObjects, hnz, h40]
    · simp [fixedObjects, blockOutObjects, hnz, h72]
  have hlst_word : ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) := by
    intro k hk
    have hmem := hlst k hk
    rcases hF.1 _ hmem with h0 | ⟨hal, hwd⟩
    · dsimp only at h0; omega
    · exact memW_eq_of_ivlUnhit
        (ptxPhase2_fresh_frame_unhit ⟨hGI, hAO⟩ hhp' hfr hal)
        hwd.1 (ivl_allocated_bound hAO hal).2 ⟨by dsimp only; omega, by dsimp only; omega⟩
  refine ⟨?_, hlst_word 40 (by simp), hlst_word 72 (by simp)⟩
  intro k hk
  have hk8 : k % 8 = 0 ∧ k + 8 ≤ 88 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
  have hcell := rec_word_eq_of_unhit hAO hF "bo" 88 (by decide) hbo hnz hu hk8.1 hk8.2
  rw [hbo] at hcell
  exact hcell

/-- Resuming after the `te_new` constructor call (guest spine 34) with the
auxiliary conjunct carried along: the callee's only memory writes are the
200 zeroed bytes of the fresh block (`M27.te_new_body_run`), every global
but `heap_ptr` is kept, and the caller locals are restored, so every
component of `PtxPhase2X` survives. The `PtxTeStoreReady` part is the
frozen `phase2_resume_te_storeReady`. -/
theorem ptxPhase2_te_new_resume_X (h : PtxCallees) :
    R16Shards.PtxP1.DecCallResumeShapeOn (fun s => PtxValidatedStrong s ∧ PtxPhase2X s)
      (fun s => PtxTeStoreReady s ∧ PtxPhase2X s)
      (ofString "te") .one (ofString "te_new") [] := by
  intro F st vs body callee ret v post hc hp ha hl hb hsh
  have hb0 := hb
  have hbody : body = (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1 :=
    InitECandidate.Solver.PanRunBounded.lookupCodeHOLFinite_installed_body st.code.lookup (ofString "te_new")
      (sourceFunctionEntry Guest.Software.guestFn_te_new).2.1
      (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1 body
      (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.2 ret vs callee
      (by rw [hc]; exact InitECandidate.Solver.Wave8Contracts.M27.lookup_te_new) hl
  rw [hbody] at hb
  obtain ⟨S, Nd, hW, -⟩ := hp.1.1.1.2.2.2.2
  have hA' : ArenaReady (callEntryStateHOLFinite st callee) :=
    (arenaReady_with_locals st callee (st.clock - 1)).mpr hp.1.1.1.1.1.1
  have hW' : WorldTypedWith (callEntryStateHOLFinite st callee) S Nd :=
    (worldTypedWith_with_locals st callee (st.clock - 1) S Nd).mpr hW
  obtain ⟨hhp', hglob, hfr⟩ := ptxPhase2_te_new_frame hA' hb
  obtain ⟨hcell, hd40, hd72⟩ :=
    ptxPhase2_fresh_cells hA' hW' hp.1.1.1.1.2.1 hp.1.1.1.2.2.1 hp.1.1.1.2.2.2.1 hhp'
      (by unfold globN; rw [hglob (ofString "bo") (by decide)]) hfr
  have hcell_st : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN st "bo" + k) = memW st (globN st "bo" + k) := hcell
  have hd40_st : memW post (memW st (globN st "bo" + 40)) = memW st (memW st (globN st "bo" + 40)) :=
    hd40
  have hd72_st : memW post (memW st (globN st "bo" + 72)) = memW st (memW st (globN st "bo" + 72)) :=
    hd72
  have hbo_st : globN post "bo" = globN st "bo" := by
    unfold globN; rw [hglob (ofString "bo") (by decide)]; rfl
  have hjc_st : globN post "journal_cap" = globN st "journal_cap" := by
    unfold globN; rw [hglob (ofString "journal_cap") (by decide)]; rfl
  have htb0 : TxBacking post := by
    refine ⟨?_, ?_⟩
    · rw [hbo_st, hcell_st 40 (by simp), hd40_st]; exact hp.2.2.1.1
    · rw [hbo_st, hcell_st 72 (by simp), hd72_st]; exact hp.2.2.1.2
  have hidx' : locN (setVarHOLFinite (ofString "te") v { post with locals := st.locals })
      "index" = locN st "index" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "te" ≠ ofString "index" from by decide]
  obtain ⟨w, hw, hwb⟩ := hp.2.1
  have hmg : PtxPhase2MgasW (setVarHOLFinite (ofString "te") v { post with locals := st.locals }) :=
    ⟨w, by
      simp only [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "te" ≠ ofString "mgas" from by decide]
      exact hw, hwb⟩
  refine ⟨phase2_resume_te_storeReady h st vs body callee ret v post hc hp.1 ha hl hb0 hsh,
    ⟨hmg, htb0,
      ptxPhase2_txEnv_of_cells hp.2.2.2.1 hbo_st hjc_st hidx' hcell_st,
      ptxPhase4LocalShapes_setVar_te st post v hp.2.2.2.2⟩⟩
/-! ### Te-environment stores with the auxiliary conjunct (guest spine 36..41)

The six environment stores only write inside the fresh 200-byte block
returned by `te_new`, which the store-ready invariant separates from every
world-owned interval. The block-out record cells and the two list headers
are world-owned, so none of the addresses read by `PtxPhase2X` is hit. -/

/-- From the store-ready separation: every nonempty world-owned interval
starts past the whole environment or ends before it. -/
private theorem ptxPhase2_te_disj_of_world {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {a sz : Nat}
    (hd : IvlsDisj [(locN s "te", 200)] (worldOwned s S Nd))
    (hmem : (a, sz) ∈ worldOwned s S Nd) (hsz : 0 < sz) :
    locN s "te" + 200 ≤ a ∨ a + sz ≤ locN s "te" := by
  rcases hd (locN s "te", 200) (by simp) (a, sz) hmem with h | h | h | h
  · exact absurd h (by simp)
  · exact absurd h (by omega)
  · exact Or.inl h
  · exact Or.inr h

/-- No aligned environment slot coincides with an address that the
store-ready separation keeps outside the environment. -/
private theorem ptxPhase2_te_addr_miss {F : Type}
    {s : PanSemStateFiniteExact 64 F} {a sz : Nat}
    (hn : locN s "te" + 200 ≤ a ∨ a + sz ≤ locN s "te")
    {k : Nat} (hk : k < 25) (ha : a < 2 ^ 64)
    (hte : locN s "te" + 200 ≤ 2 ^ 64) (hsz : 0 < sz) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 (locN s "te" + 8 * k) := by
  intro he
  have ha' : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have hx' : (BitVec.ofNat 64 (locN s "te" + 8 * k)).toNat
      = locN s "te" + 8 * k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have he' := congrArg BitVec.toNat he
  rw [ha', hx'] at he'
  rcases hn with h1 | h1
  · omega
  · omega

/-- A cell inside an interval separated from the environment never coincides
with an aligned environment slot. -/
private theorem ptxPhase2_te_cell_miss {F : Type}
    {s : PanSemStateFiniteExact 64 F} {b0 sz c : Nat}
    (hn : locN s "te" + 200 ≤ b0 ∨ b0 + sz ≤ locN s "te")
    (hc : c < sz) {k : Nat} (hk : k < 25)
    (ha : b0 + c < 2 ^ 64) (hte : locN s "te" + 200 ≤ 2 ^ 64) :
    BitVec.ofNat 64 (b0 + c) ≠ BitVec.ofNat 64 (locN s "te" + 8 * k) := by
  intro he
  have ha' : (BitVec.ofNat 64 (b0 + c)).toNat = b0 + c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have hx' : (BitVec.ofNat 64 (locN s "te" + 8 * k)).toNat
      = locN s "te" + 8 * k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have he' := congrArg BitVec.toNat he
  rw [ha', hx'] at he'
  rcases hn with h1 | h1
  · omega
  · omega

/-- The block-out record cells and the two list data pointers are separated
from every aligned slot of the fresh environment, so a store into the
environment cannot disturb any address read by `PtxPhase2X`. -/
theorem ptxPhase2_te_miss_facts {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeStoreReady s) (hx : PtxPhase2X s) {k : Nat} (hk : k < 25) :
    (∀ c ∈ ([24, 32, 40, 72, 80] : List Nat),
      BitVec.ofNat 64 (globN s "bo" + c) ≠ BitVec.ofNat 64 (locN s "te" + 8 * k)) ∧
    (∀ c ∈ ([40, 72] : List Nat),
      BitVec.ofNat 64 (memW s (globN s "bo" + c)) ≠ BitVec.ofNat 64 (locN s "te" + 8 * k)) := by
  obtain ⟨hlive, S, Nd, hW, -, hd, -, -⟩ := hp
  have hAO : ArenaOK s := hlive.1.1.1.1.1.1.2
  have hF : FixedTyped s := hW.2.2.1
  have hnz : globN s "bo" ≠ 0 := hx.2.2.1.bo_nz
  have hbo_al := bo_words hF hnz
  have hte_ptr : locN s "te" + 200 ≤ 2 ^ 64 := by
    rcases hlive.2.2.1 with ⟨-, h1⟩
    have h2 : globN s "heap_ptr" ≤ 2 ^ 64 := Nat.le_trans hAO.2.1 (by decide)
    omega
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
  refine ⟨?_, ?_⟩
  · intro c hc
    have hc88 : c < 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega
    exact ptxPhase2_te_cell_miss (ptxPhase2_te_disj_of_world hd hbo_mem (by decide))
      hc88 hk (by have := ivl_allocated_bound hAO hbo_al.1; omega) hte_ptr
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ptxPhase2_te_addr_miss (ptxPhase2_te_disj_of_world hd (hlst_mem 40 (by simp))
        (by decide)) hk hl40 hte_ptr (by decide)
    · exact ptxPhase2_te_addr_miss (ptxPhase2_te_disj_of_world hd (hlst_mem 72 (by simp))
        (by decide)) hk hl72 hte_ptr (by decide)

/-- Consecutive word writes into the environment preserve both the
store-ready invariant and the auxiliary conjunct. -/
theorem ptxPhase2_teStoreX_words {F : Type} (ws : List (HolWordLab 64))
    {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeStoreReady s ∧ PtxPhase2X s)
    (k : Nat) (hk : k + ws.length ≤ 25)
    {mem : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ (BitVec.ofNat 64 (locN s "te" + 8 * k)) ws
      s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem) :
    PtxTeStoreReady { s with memory := mem } ∧ PtxPhase2X { s with memory := mem } := by
  induction ws generalizing s k mem with
  | nil =>
    simp only [panMemStoresHOL, Option.some.injEq] at hst
    subst mem
    exact hp
  | cons w ws ih =>
    have hk' : k < 25 := by simp only [List.length_cons] at hk; omega
    obtain ⟨hcells, hptrs⟩ := ptxPhase2_te_miss_facts hp.1 hp.2 hk'
    have hslot := phase2_teLive_slot hp.1.1 k hk'
    let x := BitVec.ofNat 64 (locN s "te" + 8 * k)
    let mem1 := fun a => if a = x then w else s.memory a
    have hp1 : PtxTeStoreReady { s with memory := mem1 } ∧
        PtxPhase2X { s with memory := mem1 } :=
      ⟨phase2_teStoreReady_slot_store hp.1 k hk' (fun a ha => if_neg ha),
        ptxPhase2X_store hp.2 (fun a ha => if_neg ha) hcells hptrs⟩
    have he : x + BitVec.ofNat 64 8 = BitVec.ofNat 64 (locN s "te" + 8 * (k + 1)) := by
      simp only [x, ← BitVec.ofNat_add]
      congr 1
    simp only [panMemStoresHOL, panMemStoreHOL, hslot.2.1, ↓reduceIte] at hst
    apply ih hp1 (k + 1) (by simp only [List.length_cons] at hk; omega)
    change @panMemStoresHOL 64 _ (BitVec.ofNat 64 (locN s "te" + 8 * (k + 1))) ws
      s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) mem1 = some mem
    change @panMemStoresHOL 64 _ (x + BitVec.ofNat 64 8) ws
      s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) mem1 = some mem at hst
    rw [he] at hst
    exact hst

/-- Store any fixed-width expression at an aligned environment offset,
carrying the auxiliary conjunct along. -/
theorem ptxPhase2_teStoreX_expr_store (src : ExpHOL 64) (k n : Nat)
    (hk : k + n ≤ 25)
    (hlen : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v,
      PtxTeStoreReady s → evalAt s src = some v → (flattenHOL v).length = n) :
    Hoare (fun s => PtxTeStoreReady s ∧ PtxPhase2X s)
      (.store (.op .add [.var .local (ofString "te"), .const (8 * k)]) src)
      (fun r s => r = none → PtxTeStoreReady s ∧ PtxPhase2X s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  obtain ⟨w, hw⟩ := hp.1.1.2.1
  have hl : locN s "te" = w.toNat := by simp [locN, hw]
  have he : x = w + BitVec.ofNat 64 (8 * k) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr, BitVec.ofNat_mul] using hx.symm
  have hx' : x = BitVec.ofNat 64 (locN s "te" + 8 * k) := by
    simp [he, hl, BitVec.ofNat_add]
  rw [hx'] at hst
  exact ptxPhase2_teStoreX_words (flattenHOL v) hp k (by rw [hlen s v hp.1 hv]; exact hk) hst

/-- The six environment stores of guest spine 36..41, replayed with the
auxiliary conjunct carried along. -/
theorem ptxPhase2_teStoresX_bound {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => PtxTeStoreReady s ∧ PtxPhase2X s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxTeStoreReady s ∧ PtxPhase2X s)
      (phase2_teStores tail) b := by
  have hs (addr src : ExpHOL 64) :
      TerminatingProgBoundedOn (fun s => PtxTeStoreReady s ∧ PtxPhase2X s)
        (.store addr src) 0 := by
    intro F s hc hp hn
    rw [clock_store]
    exact ⟨by omega, le_rfl⟩
  have seq0 {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {a t : ProgHOL 64}
      (ha : TerminatingProgBoundedOn P a 0)
      (hh : Hoare P a (fun r s => r = none → P s))
      (ht : TerminatingProgBoundedOn P t b) :
      TerminatingProgBoundedOn P (.seq a t) b := by
    intro F s hc hp
    simpa only [Nat.zero_add] using seq_bound_trans ha hh ht s hc hp
  unfold phase2_teStores
  simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
  change TerminatingProgBoundedOn (fun s => PtxTeStoreReady s ∧ PtxPhase2X s)
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 0]) (.var .local (ofString "sender")))
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 8])
      (.load .one (.op .add [.var .local (ofString "tx"), .const 152])))
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 16])
      (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "tx"), .const 160])))
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 48]) (.var .local (ofString "price")))
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 80]) (.var .local (ofString "mgas")))
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 88]) (.var .local (ofString "reservoir"))) tail)))))) b
  apply seq0 (hs _ _) (ptxPhase2_teStoreX_expr_store _ 0 1 (by decide) (fun s v hp hv => by
    obtain ⟨w, hw⟩ := hp.1.1.2.scalar "sender" (by simp)
    have he : v = .val (.word w) := by simpa [evalAt, evalHOLExact, hw] using hv.symm
    rw [he]; simp [flattenHOL]))
  apply seq0 (hs _ _) (ptxPhase2_teStoreX_expr_store _ 1 1 (by decide)
    (fun s v _ hv => phase2_load_one_length s _ v hv))
  apply seq0 (hs _ _) (ptxPhase2_teStoreX_expr_store _ 2 4 (by decide)
    (fun s v _ hv => phase2_load_quad_length s _ v hv))
  apply seq0 (hs _ _) (ptxPhase2_teStoreX_expr_store _ 6 4 (by decide) (fun s v hp hv => by
    obtain ⟨a, b, c, d, hw⟩ := hp.1.1.2.price
    have he : v = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] := by
      simpa [evalAt, evalHOLExact, hw] using hv.symm
    rw [he]; simp [flattenHOL]))
  apply seq0 (hs _ _) (ptxPhase2_teStoreX_expr_store _ 10 1 (by decide) (fun s v hp hv => by
    obtain ⟨w, hw⟩ := hp.1.1.2.scalar "mgas" (by simp)
    have he : v = .val (.word w) := by simpa [evalAt, evalHOLExact, hw] using hv.symm
    rw [he]; simp [flattenHOL]))
  apply seq0 (hs _ _) (ptxPhase2_teStoreX_expr_store _ 11 1 (by decide) (fun s v hp hv => by
    obtain ⟨w, hw⟩ := hp.1.1.2.scalar "reservoir" (by simp)
    have he : v = .val (.word w) := by simpa [evalAt, evalHOLExact, hw] using hv.symm
    rw [he]; simp [flattenHOL]))
  exact ht

/-- Bounded constructor and six-store prefix of Phase 2 (guest spine 34..41)
with the auxiliary conjunct carried along. -/
theorem ptxPhase2_tePrefixX_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => PtxTeStoreReady s ∧ PtxPhase2X s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxValidatedStrong s ∧ PtxPhase2X s)
      (spinePlug 7 (spineAt 34 ptxCode) tail) (K.te_new + b + 1) := by
  have he : spinePlug 7 (spineAt 34 ptxCode) tail =
      .decCall (ofString "te") .one (ofString "te_new") [] (phase2_teStores tail) := by
    simp only [phase2_teStores, ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
      spineAt, spinePlug]
    rfl
  rw [he]
  apply @R16Shards.PtxP1.decCall_shape_bound _ _
    (fun {F} s => PtxTeStoreReady s ∧ PtxPhase2X s) _ _ _ h.fb_te_new
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1
  · intro F st vs body callee ret v post hc hp ha hl hrun hshape
    exact ptxPhase2_te_new_resume_X h st vs body callee ret v post hc hp ha hl hrun hshape
  · exact ptxPhase2_teStoresX_bound ht

/-! ### Access-list count setup with the auxiliary conjunct -/

/-- The auxiliary conjunct ignores the fresh bookkeeping locals. -/
theorem ptxPhase2X_setVar_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    {name : MlS} (v : ValueHOL 64)
    (hne : ∀ n ∈ ptxPhase2XNames, ofString n ≠ name)
    (hp : PtxPhase2X s) :
    PtxPhase2X (setVarHOLFinite name v s) := by
  show PtxPhase2X {s with locals := s.locals.update (name, v), clock := s.clock}
  refine ptxPhase2X_with_locals s _ s.clock (fun n hn => ?_) hp
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]

theorem ptxPhase2X_setVar_nal {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hp : PtxPhase2X s) : PtxPhase2X (setVarHOLFinite (ofString "nal") v s) :=
  ptxPhase2X_setVar_other s v (by
    intro n hn
    simp only [ptxPhase2XNames, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hp

theorem ptxPhase2X_setVar_hal {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hp : PtxPhase2X s) : PtxPhase2X (setVarHOLFinite (ofString "hal") v s) :=
  ptxPhase2X_setVar_other s v (by
    intro n hn
    simp only [ptxPhase2XNames, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hp

theorem ptxPhase2_resume_has_access_list_X (h : PtxCallees) :
    DecCallResumeOn (fun s => PtxAccessCountReady s ∧ PtxPhase2X s)
      (fun s => PtxAccessCountReady s ∧ PtxPhase2X s) (ofString "hal")
      (ofString "tx_has_access_list") [.var .local (ofString "tx")] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hr := R16Shards.PtxP1.funSpec_at_lookup h.ro_tx_has_access_list
    s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hr
  have he := hr (Or.inl ⟨v, rfl⟩)
  dsimp only at he
  have hrestore : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with locals := s.locals, clock := post.clock } := by rw [he]; rfl
  have hp' : PtxAccessCountReady { post with locals := s.locals } ∧
      PtxPhase2X { post with locals := s.locals } := by
    rw [hrestore]
    exact ⟨phase2_accessCountReady_with_locals s s.locals post.clock (fun _ _ => rfl) hp.1,
      ptxPhase2X_with_locals s s.locals post.clock (fun _ _ => rfl) hp.2⟩
  refine ⟨phase2_accessCountReady_with_locals _ _ _ ?_ hp'.1, ptxPhase2X_setVar_hal _ _ hp'.2⟩
  intro name hn
  have hne : ofString name ≠ ofString "hal" := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst name <;> decide
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm hne]

theorem ptxPhase2_count_assignX_hoare (e : ExpHOL 64)
    (he : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PtxAccessCountReady s → evalAt s e = some v →
      ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memW s (locN s "tx" + 216)) :
    Hoare (fun s => PtxAccessCountReady s ∧ PtxPhase2X s)
      (.assign .local (ofString "nal") e)
      (fun r t => r = none → PtxAccessCountReady t ∧ PtxPhase2X t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    obtain ⟨w, rfl, hw⟩ := he s v hp.1 hv
    exact ⟨phase2_accessCountReady_loaded s hp.1.1 w hw, ptxPhase2X_setVar_nal s _ hp.2⟩
  · intro F s hp hr
    simp at hr

theorem ptxPhase2_count_condX_hoare (cond e : ExpHOL 64)
    (he : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PtxAccessCountReady s → evalAt s e = some v →
      ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memW s (locN s "tx" + 216)) :
    Hoare (fun s => PtxAccessCountReady s ∧ PtxPhase2X s)
      (.ite cond (.assign .local (ofString "nal") e) .skip)
      (fun r t => r = none → PtxAccessCountReady t ∧ PtxPhase2X t) := by
  apply Hoare.ite
  · refine ⟨fun s hc hp hn => ?_⟩
    exact (ptxPhase2_count_assignX_hoare e he).run s hc hp.1 hn
  · exact Hoare.skip (fun s hp _ => hp.1)
  · intro F s hp hr
    simp at hr

theorem ptxPhase2_countPrefixX_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => PtxAccessCountReady s ∧ PtxPhase2X s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxTeStoreReady s ∧ PtxPhase2X s)
      (spinePlug 3 (spineAt 41 ptxCode) tail) (K.tx_has_access_list + b + 1) := by
  simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
  change TerminatingProgBoundedOn (fun s => PtxTeStoreReady s ∧ PtxPhase2X s)
    (.dec (ofString "nal") .one (.const 0)
      (.decCall (ofString "hal") .one (ofString "tx_has_access_list")
        [.var .local (ofString "tx")]
        (.seq (.ite (.cmp .notEqual (.var .local (ofString "hal")) (.const 0))
          (.assign .local (ofString "nal")
            (.load .one (.op .add [.var .local (ofString "tx"), .const 216]))) .skip) tail))) _
  apply dec_bound_trans (Q := fun s => PtxAccessCountReady s ∧ PtxPhase2X s)
  · intro F s v hp he
    have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
    subst v
    exact ⟨phase2_accessCountReady_zero s hp.1, ptxPhase2X_setVar_nal s _ hp.2⟩
  apply TerminatingProgBoundedOn.decCall_on (Q := fun s => PtxAccessCountReady s ∧ PtxPhase2X s)
    h.fb_tx_has_access_list
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1.1.1
  · exact ptxPhase2_resume_has_access_list_X h
  · have hi := ptxPhase2_count_condX_hoare
      (.cmp .notEqual (.var .local (ofString "hal")) (.const 0))
      (.load .one (.op .add [.var .local (ofString "tx"), .const 216]))
      (fun s v _ he => phase2_count_load s v he)
    have hb0 : TerminatingProgBoundedOn (fun s => PtxAccessCountReady s ∧ PtxPhase2X s)
        (.ite (.cmp .notEqual (.var .local (ofString "hal")) (.const 0))
          (.assign .local (ofString "nal")
            (.load .one (.op .add [.var .local (ofString "tx"), .const 216]))) .skip) 0 := by
      intro F s hc hp hn
      simp only [evaluateHOLFiniteState_ite]
      split
      · split <;> simp only [clock_assign, clock_skip, Nat.zero_add] <;> exact ⟨le_rfl, le_rfl⟩
      · exact ⟨le_rfl, le_rfl⟩
    intro F s hc hp
    simpa only [Nat.zero_add] using seq_bound_trans hb0 hi ht s hc hp

/-- Constructor, initialization stores, and count setup compose at the first
access-list allocation, with the auxiliary conjunct retained throughout. -/
theorem ptxPhase2_allocationEntryX_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => PtxAccessCountReady s ∧ PtxPhase2X s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxValidatedStrong s ∧ PtxPhase2X s)
      (spinePlug 10 (spineAt 34 ptxCode) tail)
      (K.te_new + (K.tx_has_access_list + b + 1) + 1) := by
  have he : spinePlug 10 (spineAt 34 ptxCode) tail =
      spinePlug 7 (spineAt 34 ptxCode) (spinePlug 3 (spineAt 41 ptxCode) tail) := by
    simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
    rfl
  rw [he]
  apply ptxPhase2_tePrefixX_bound h
  exact ptxPhase2_countPrefixX_bound h ht


/-! ### Region B: addresses and packing with `TxBacking` (guest spine 44..53)

Only `TxBacking` needs threading through regions B and C: the remaining
components of `PtxPhase2X` are re-derived at the far side from the validated
part. The `alloc` callee writes no memory and keeps every global but
`heap_ptr` (`M27.alloc_body_run`), so `TxBacking` survives both allocation
calls wholesale. -/

/-- Pointwise memory equality and the `bo` global transfer `TxBacking`. -/
theorem ptxPhase2_txBacking_of_mem_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (htx : TxBacking s) (hbo : globN post "bo" = globN s "bo")
    (hmem : ∀ a, post.memory a = s.memory a) : TxBacking post := by
  have hm (p : Nat) : memW post p = memW s p := by
    unfold memW; rw [hmem (BitVec.ofNat 64 p)]
  refine ⟨?_, ?_⟩
  · have h1 : memW post (globN post "bo" + 40) = memW s (globN s "bo" + 40) := by
      rw [hbo]; exact hm _
    rw [h1, hm _]; exact htx.1
  · have h1 : memW post (globN post "bo" + 72) = memW s (globN s "bo" + 72) := by
      rw [hbo]; exact hm _
    rw [h1, hm _]; exact htx.2

/-- Resuming after the first address-array allocation (guest spine 44) with
`TxBacking` carried along: the joint address invariant is frozen, and the
callee leaves memory and every non-`heap_ptr` global untouched. -/
theorem ptxPhase2_alloc_joint_tx_resume (h : PtxCallees) :
    DecCallResumeOn (fun s => PtxAccessCountReady s ∧ TxBacking s)
      (fun s => PtxAddressJoint s ∧ TxBacking s) (ofString "al_addrs") (ofString "alloc")
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
  have htxPost : TxBacking post := ptxPhase2_txBacking_of_mem_eq hp.2 hboG hmemF
  exact ⟨phase2_address_alloc_joint h s vs body callee ret v post hc hp.1 ha hl hb0,
    txBacking_set_local (ofString "al_addrs") v
      ((txBacking_with_locals post s.locals post.clock).mp htxPost)⟩

end InitECandidate.Solver.Wave8GuestInv.R13Shards
