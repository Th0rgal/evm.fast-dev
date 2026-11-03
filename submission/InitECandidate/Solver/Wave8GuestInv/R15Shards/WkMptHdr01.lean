import InitECandidate.Solver.Wave8GuestInv.Primitives
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_C08WkShard03
import InitECandidate.Solver.Wave8GuestInv.R13Shards.Common
import InitECandidate.Solver.GuestGlobalKeep
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.zv_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_memeq

/-!
# R15 Shard `WkMptHdr01`: `wk_mpt_from_witness` & `wk_decode_host_input`

Self-contained `WorldEff` combinator framework + 0-sorry proofs of:
1. `wk_mpt_from_witness`
2. `wk_decode_host_input`
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R15Shards

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
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

/-! ## Section 1: Composable `WorldEff` Relation (Heap + Scratch + Byte-Exact Frame) -/

structure WorldEff {F : Type} (s cur : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (B : List (String × Nat)) (gw : List String) : Prop where
  arena      : ArenaReady cur
  code       : cur.code = originalRuntimeCode
  memaddrs   : cur.memaddrs = s.memaddrs
  be         : cur.be = s.be
  eshapes    : cur.eshapes = s.eshapes
  hp_lo      : globN s "heap_ptr" ≤ globN cur "heap_ptr"
  fmp_eq     : globN cur "frame_mem_ptr" = globN s "frame_mem_ptr"
  sp_hi      : globN cur "scratch_ptr" ≤ globN s "scratch_ptr"
  gw_kept    : GlobalsKept gw s cur
  fresh_bufs : FreshBufsOK s cur
  out_dom    : ∀ a : BitVec 64, cur.memory a ≠ s.memory a → s.memaddrs a
  cell_frame : ∀ a : BitVec 64, cur.memory a ≠ s.memory a →
                 (∃ ivl ∈ Rl, CellHitsPos a.toNat ivl) ∨
                 (∃ gs ∈ B, CellHitsPos a.toNat (bufferRegion s gs)) ∨
                 CellHitsPos a.toNat (freeGap s) ∨
                 CellHitsPos a.toNat (heapFree s)
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → memB cur b ≠ memB s b →
                 (∃ ivl ∈ Rl, InIvl b ivl) ∨
                 (∃ gs ∈ B, InIvl b (bufferRegion s gs)) ∨
                 InIvl b (freeGap s) ∨
                 InIvl b (heapFree s)

theorem WorldEff.refl {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (B : List (String × Nat)) (gw : List String)
    (hA : ArenaReady s) (hc : s.code = originalRuntimeCode) :
    WorldEff s s Rl B gw := by
  refine ⟨hA, hc, rfl, rfl, rfl, le_rfl, rfl, le_rfl, fun _ _ => rfl, ?_,
    fun _ h => absurd rfl h, fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩
  refine ⟨fun _ _ => Or.inl rfl, ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j _ _ _ h1 _; exact absurd rfl h1.1

theorem WorldEff.locals_clock {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldEff s { cur with locals := L, clock := k } Rl B gw :=
  ⟨⟨guestInv_with_locals_clock cur L k h.arena.1, h.arena.2⟩,
   h.code, h.memaddrs, h.be, h.eshapes, h.hp_lo, h.fmp_eq, h.sp_hi,
   h.gw_kept, h.fresh_bufs, h.out_dom, h.cell_frame, h.byte_frame⟩

theorem WorldEff.mono {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {R1 R2 : List Ivl} {B1 B2 : List (String × Nat)} {gw1 gw2 : List String}
    (h : WorldEff s cur R1 B1 gw1)
    (hR : ∀ iv ∈ R1, 0 < iv.2 →
      (∃ j ∈ R2, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B2, (bufferRegion s gs).1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit))
    (hB : ∀ gs ∈ B1, gs ∈ B2)
    (hgw : ∀ g ∈ gw1, g ∈ gw2) :
    WorldEff s cur R2 B2 gw2 := by
  refine ⟨h.arena, h.code, h.memaddrs, h.be, h.eshapes, h.hp_lo, h.fmp_eq, h.sp_hi,
    fun k hk => h.gw_kept k (fun hm => hk (by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
      exact List.mem_map.2 ⟨g, hgw g hg, rfl⟩)),
    h.fresh_bufs, h.out_dom, ?_, ?_⟩
  · intro a hne
    rcases h.cell_frame a hne with ⟨iv, hiv, hpos, hc1, hc2⟩ | ⟨gs, hgs, hhit⟩ | hfg | hhf
    · rcases hR iv hiv hpos with ⟨j, hj, h1, h2⟩ | ⟨gs, hgs, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨j, hj, by omega, by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨gs, hgs, by omega, by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by dsimp [freeGap]; omega, by dsimp [freeGap]; omega, by dsimp [freeGap]; omega⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩))
    · exact Or.inr (Or.inl ⟨gs, hB gs hgs, hhit⟩)
    · exact Or.inr (Or.inr (Or.inl hfg))
    · exact Or.inr (Or.inr (Or.inr hhf))
  · intro b hb64 hne
    rcases h.byte_frame b hb64 hne with ⟨iv, hiv, hb1, hb2⟩ | ⟨gs, hgs, hin⟩ | hfg | hhf
    · rcases hR iv hiv (by omega) with ⟨j, hj, h1, h2⟩ | ⟨gs, hgs, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨j, hj, by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨gs, hgs, by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by dsimp [freeGap]; omega, by dsimp [freeGap]; omega⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩))
    · exact Or.inr (Or.inl ⟨gs, hB gs hgs, hin⟩)
    · exact Or.inr (Or.inr (Or.inl hfg))
    · exact Or.inr (Or.inr (Or.inr hhf))

theorem WorldEff.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h1 : WorldEff a b Rl B gw) (h2 : WorldEff b c Rl B gw)
    (hB_same : ∀ gs ∈ B, globN b gs.1 = globN a gs.1)
    (hbuf_ac : FreshBufsOK a c) :
    WorldEff a c Rl B gw := by
  refine ⟨h2.arena, h2.code, h2.memaddrs.trans h1.memaddrs, h2.be.trans h1.be,
    h2.eshapes.trans h1.eshapes, le_trans h1.hp_lo h2.hp_lo,
    h2.fmp_eq.trans h1.fmp_eq, le_trans h2.sp_hi h1.sp_hi,
    fun k hk => (h1.gw_kept k hk).trans (h2.gw_kept k hk),
    hbuf_ac, ?_, ?_, ?_⟩
  · intro x hne
    by_cases hcb : c.memory x = b.memory x
    · rw [hcb] at hne; exact h1.out_dom x hne
    · rw [← h1.memaddrs]; exact h2.out_dom x hcb
  · intro x hne
    by_cases hcb : c.memory x = b.memory x
    · rw [hcb] at hne; exact h1.cell_frame x hne
    · rcases h2.cell_frame x hcb with hR | ⟨gs, hgs, hhit⟩ | ⟨hp0, hc1, hc2⟩ | ⟨hp0, hc1, hc2⟩
      · exact Or.inl hR
      · refine Or.inr (Or.inl ⟨gs, hgs, ?_⟩)
        simpa only [bufferRegion, hB_same gs hgs] using hhit
      · refine Or.inr (Or.inr (Or.inl ?_))
        dsimp only [CellHitsPos, CellHits, freeGap] at hp0 hc1 hc2 ⊢
        have := h1.fmp_eq; have := h1.sp_hi
        exact ⟨by omega, by omega, by omega⟩
      · refine Or.inr (Or.inr (Or.inr ?_))
        dsimp only [CellHitsPos, CellHits, heapFree] at hp0 hc1 hc2 ⊢
        have := h1.hp_lo
        exact ⟨by omega, by omega, by omega⟩
  · intro x hx64 hne
    by_cases hcb : memB c x = memB b x
    · rw [hcb] at hne; exact h1.byte_frame x hx64 hne
    · rcases h2.byte_frame x hx64 hcb with hR | ⟨gs, hgs, hin⟩ | ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · exact Or.inl hR
      · refine Or.inr (Or.inl ⟨gs, hgs, ?_⟩)
        simpa only [bufferRegion, hB_same gs hgs] using hin
      · refine Or.inr (Or.inr (Or.inl ?_))
        dsimp only [InIvl, freeGap] at hc1 hc2 ⊢
        have := h1.fmp_eq; have := h1.sp_hi
        exact ⟨by omega, by omega⟩
      · refine Or.inr (Or.inr (Or.inr ?_))
        dsimp only [InIvl, heapFree] at hc1 hc2 ⊢
        have := h1.hp_lo
        exact ⟨by omega, by omega⟩

theorem freshBufsOK_of_no_globalBuf_writes {F : Type} {a c : PanSemStateFiniteExact 64 F}
    {gw : List String}
    (hgw : GlobalsKept gw a c)
    (hno_gb : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ gw.map ofString) :
    FreshBufsOK a c := by
  have heq : ∀ gs ∈ globalBuffers, globN c gs.1 = globN a gs.1 :=
    fun gs hgs => globN_eq_of_lookup (hgw (ofString gs.1) (hno_gb gs hgs))
  refine ⟨fun gs hgs => Or.inl (heq gs hgs), ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi _ _ h1 _
  exact absurd (heq _ (List.getElem_mem hi)) h1.1

theorem WorldEff.trans_noBuf {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h1 : WorldEff a b Rl B gw) (h2 : WorldEff b c Rl B gw)
    (hB_sub : ∀ gs ∈ B, gs ∈ globalBuffers)
    (hno_gb : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ gw.map ofString) :
    WorldEff a c Rl B gw :=
  h1.trans h2
    (fun gs hgs => globN_eq_of_lookup (h1.gw_kept (ofString gs.1) (hno_gb gs (hB_sub gs hgs))))
    (freshBufsOK_of_no_globalBuf_writes (fun k hk => (h1.gw_kept k hk).trans (h2.gw_kept k hk)) hno_gb)

theorem WorldEff.of_byteEff {F : Type} {s cur next : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String} {Sub : List Ivl}
    (h : WorldEff s cur Rl B gw) (hb : ByteEff cur next Sub)
    (hsub : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit)) :
    WorldEff s next Rl B gw := by
  have hGn : GuestInv next :=
    guestInv_congr hb.code hb.memaddrs hb.shMemaddrs hb.baseAddr h.arena.1
  have hAn : ArenaReady next := ⟨hGn, arenaOK_congr hb.globals h.arena.2⟩
  refine ⟨hAn, hb.code.trans h.code, hb.memaddrs.trans h.memaddrs, hb.be.trans h.be, hb.eshapes.trans h.eshapes,
    by simpa [globN, hb.globals] using h.hp_lo,
    by simpa [globN, hb.globals] using h.fmp_eq,
    by simpa [globN, hb.globals] using h.sp_hi,
    fun k hk => (h.gw_kept k hk).trans (by rw [hb.globals]),
    by simpa [FreshBufsOK, globN, hb.globals] using h.fresh_bufs, ?_, ?_, ?_⟩
  · intro a hne
    by_cases hnc : next.memory a = cur.memory a
    · rw [hnc] at hne; exact h.out_dom a hne
    · rw [← h.memaddrs]; exact hb.out_dom a hnc
  · intro a hne
    by_cases hnc : next.memory a = cur.memory a
    · rw [hnc] at hne; exact h.cell_frame a hne
    · obtain ⟨iv, hiv, hpos, hc1, hc2⟩ := hb.cell_frame a hnc
      rcases hsub iv hiv hpos with ⟨j, hj, h1, h2⟩ | ⟨gs, hgs, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨j, hj, by omega, by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨gs, hgs, by omega, by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by dsimp [freeGap]; omega, by dsimp [freeGap]; omega, by dsimp [freeGap]; omega⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩))
  · intro b hb64 hne
    by_cases hnc : memB next b = memB cur b
    · rw [hnc] at hne; exact h.byte_frame b hb64 hne
    · obtain ⟨iv, hiv, hb1, hb2⟩ := hb.byte_frame b hb64 hnc
      rcases hsub iv hiv (by omega) with ⟨j, hj, h1, h2⟩ | ⟨gs, hgs, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨j, hj, by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨gs, hgs, by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by dsimp [freeGap]; omega, by dsimp [freeGap]; omega⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩))

theorem WorldEff.to_worldStep_Q {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {B : List (String × Nat)} {gw : List String}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hWOK : WorldOK s)
    (hB_ok : ∀ gs ∈ B, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hcore_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ gw.map ofString)
    (heff : WorldEff s post (R s) B gw)
    (hQ : ∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (R s) (worldTypedIvls s S Nd) →
      WorldTypedWith post S Nd →
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) →
      nodeExtents post Nd = nodeExtents s Nd →
      (∀ t ∈ S, htabFootprint post t = htabFootprint s t) →
      Q s r post S Nd) :
    WorldStep R gw stdKeep Q s r post :=
  worldStep_master B hB_ok hWOK heff.arena ⟨heff.hp_lo, heff.sp_hi⟩
    heff.gw_kept hcore_out heff.fresh_bufs
    (fun a hne => ⟨heff.out_dom a hne, heff.cell_frame a hne⟩)
    heff.byte_frame hQ

theorem WorldEff.of_readOnly {F : Type} {s cur next : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (hro : next = { cur with locals := next.locals, clock := next.clock }) :
    WorldEff s next Rl B gw := by
  have h1 := h.locals_clock next.locals next.clock
  rwa [← hro] at h1

/-! ## Section 2: `alloc` & `scratch_alloc` & `scratch_release` `WorldEff` Steps -/

theorem worldEff_alloc_step {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    {p n : BitVec 64}
    (hp_lk : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hcmp1 : ¬ ((cMax - p).toNat < n.toNat))
    (hcmp2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat))
    {next : PanSemStateFiniteExact 64 F}
    (hnext : next = { cur with
      globals := cur.globals.update (ofString "heap_ptr", .val (.word ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)))),
      locals := next.locals, clock := next.clock }) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    WorldEff s next Rl B gw ∧
    q.toNat = p.toNat + (n.toNat + 7) / 8 * 8 ∧
    p.toNat % 8 = 0 ∧
    sourceBase ≤ p.toNat ∧
    globN s "heap_ptr" ≤ p.toNat ∧
    p.toNat + (n.toNat + 7) / 8 * 8 = globN next "heap_ptr" ∧
    globN next "heap_ptr" ≤ heapLimit ∧
    WordsOK next (p.toNat, (n.toNat + 7) / 8 * 8) := by
  intro q
  rcases h.arena.2 with ⟨hc_hp_lo, hc_hp_hi, hc_fm_lo, hc_fm_hi, hc_sp_hi, hc_hp_al, hc_fm_al, hc_sp_al, hc_gw⟩
  have hp_glob : globN cur "heap_ptr" = p.toNat := by simp [globN, hp_lk]
  have hp_hi : p.toNat ≤ heapLimit := by rw [← hp_glob]; exact hc_hp_hi
  have hp_al : p.toNat % 8 = 0 := by rw [← hp_glob]; exact hc_hp_al
  have hp_lo_sb : sourceBase ≤ p.toNat := by rw [← hp_glob]; exact hc_hp_lo
  have hp_lo_s : globN s "heap_ptr" ≤ p.toNat := by rw [← hp_glob]; exact h.hp_lo
  obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q, _⟩ :=
    InitECandidate.Solver.Wave8GuestInv.R13.alloc_arith p n hp_hi hp_al hcmp1 hcmp2
  change q.toNat = _ at hq_eq
  change q.toNat ≤ heapLimit at hq_hi
  change q.toNat % 8 = 0 at hq_al
  change p.toNat ≤ q.toNat at hp_le_q
  have hn_globs : next.globals = cur.globals.update (ofString "heap_ptr", .val (.word q)) := by
    rw [hnext]
  have hn_hp : globN next "heap_ptr" = q.toNat := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]; simp [FUPDATE]
  have hn_fmp : globN next "frame_mem_ptr" = globN cur "frame_mem_ptr" := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hn_sp : globN next "scratch_ptr" = globN cur "scratch_ptr" := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have hn_G : GuestInv next :=
    guestInv_congr (by rw [hnext]) (by rw [hnext]) (by rw [hnext]) (by rw [hnext]) h.arena.1
  have hn_gw : GlobalsWord next :=
    globalsWord_update (ofString "heap_ptr") q hn_globs hc_gw
  have hn_A : ArenaOK next := by
    unfold ArenaOK; rw [hn_hp, hn_fmp, hn_sp]
    exact ⟨le_trans hp_lo_sb hp_le_q, hq_hi, hc_fm_lo, hc_fm_hi, hc_sp_hi,
      hq_al, hc_fm_al, hc_sp_al, hn_gw⟩
  have hn_kept : GlobalsKept gw s next := by
    intro k hk
    have hne : k ≠ ofString "heap_ptr" := fun heq => hk (heq ▸ hgw_hp)
    rw [h.gw_kept k hk, hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, Ne.symm hne]
  have hn_bufs : FreshBufsOK s next := by
    have hgb_eq : ∀ gn ∈ globalBuffers, globN next gn.1 = globN cur gn.1 := by
      intro gn hgn
      have hne : ofString gn.1 ≠ ofString "heap_ptr" :=
        (by decide : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "heap_ptr") gn hgn
      unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]
      simp [FUPDATE, hne, Ne.symm hne]
    refine ⟨fun gn hgn => ?_, ?_⟩
    · rw [hgb_eq gn hgn]
      rcases h.fresh_bufs.1 gn hgn with h1 | h2 | ⟨ha, hin⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨ha, hin.1, le_trans hin.2 (by rw [hn_hp, hp_glob]; exact hp_le_q)⟩)
    · rw [List.pairwise_iff_getElem]
      have hpw := List.pairwise_iff_getElem.1 h.fresh_bufs.2
      intro i j hi hj hlt ha hb
      rw [hgb_eq _ (List.getElem_mem hi)] at ha ⊢
      rw [hgb_eq _ (List.getElem_mem hj)] at hb ⊢
      exact hpw i j hi hj hlt ha hb
  have hn_mem : next.memory = cur.memory := by rw [hnext]
  have hn_be : next.be = cur.be := by rw [hnext]
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hwok : WordsOK next (p.toNat, (n.toNat + 7) / 8 * 8) :=
    wordsOK_of_inside_heap hn_G hp_al (by omega) hp_lo_sb (by omega)
  refine ⟨⟨⟨hn_G, hn_A⟩, by rw [hnext]; exact h.code, by rw [hnext]; exact h.memaddrs,
    hn_be.trans h.be, by rw [hnext]; exact h.eshapes,
    by rw [hn_hp]; omega, hn_fmp.trans h.fmp_eq, by rw [hn_sp]; exact h.sp_hi,
    hn_kept, hn_bufs,
    fun a hne => h.out_dom a (by rwa [hn_mem] at hne),
    fun a hne => h.cell_frame a (by rwa [hn_mem] at hne),
    fun b hb64 hne => h.byte_frame b hb64 (by unfold memB at hne ⊢; rwa [hn_mem, hn_be] at hne)⟩,
    hq_eq, hp_al, hp_lo_sb, hp_lo_s, by rw [hn_hp]; exact hq_eq.symm,
    by rw [hn_hp]; exact hq_hi, hwok⟩

theorem worldEff_scratch_alloc_step {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (hgw_sp : ofString "scratch_ptr" ∈ gw.map ofString)
    {sp fp n : BitVec 64}
    (hsp_lk : cur.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)))
    (hfp_lk : cur.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)))
    (hcmp1 : ¬ ((sp - fp).toNat < n.toNat))
    (hcmp2 : ¬ (((sp - n) &&& ((0 : BitVec 64) - 8)).toNat < fp.toNat))
    {next : PanSemStateFiniteExact 64 F}
    (hnext : next = { cur with
      globals := cur.globals.update (ofString "scratch_ptr", .val (.word ((sp - n) &&& ((0 : BitVec 64) - 8)))),
      locals := next.locals, clock := next.clock }) :
    let q := (sp - n) &&& ((0 : BitVec 64) - 8)
    WorldEff s next Rl B gw ∧
    q.toNat % 8 = 0 ∧
    globN s "frame_mem_ptr" ≤ q.toNat ∧
    q.toNat + (n.toNat + 7) / 8 * 8 = sp.toNat ∧
    sp.toNat ≤ globN s "scratch_ptr" ∧
    globN next "scratch_ptr" = q.toNat ∧
    WordsOK next (q.toNat, (n.toNat + 7) / 8 * 8) := by
  intro q
  rcases h.arena.2 with ⟨hc_hp_lo, hc_hp_hi, hc_fm_lo, hc_fm_hi, hc_sp_hi, hc_hp_al, hc_fm_al, hc_sp_al, hc_gw⟩
  have hsp_glob : globN cur "scratch_ptr" = sp.toNat := by simp [globN, hsp_lk]
  have hfp_glob : globN cur "frame_mem_ptr" = fp.toNat := by simp [globN, hfp_lk]
  have hfp_le_sp : fp.toNat ≤ sp.toNat := by rw [← hfp_glob, ← hsp_glob]; exact hc_fm_hi
  have hsp_al : sp.toNat % 8 = 0 := by rw [← hsp_glob]; exact hc_sp_al
  obtain ⟨hq_al, hfp_le_q, hq_le_sp, hq_add, _⟩ :=
    InitECandidate.Solver.Wave8GuestInv.R13.scratch_alloc_arith sp fp n hfp_le_sp hsp_al hcmp1 hcmp2
  change q.toNat % 8 = 0 at hq_al
  change fp.toNat ≤ q.toNat at hfp_le_q
  change q.toNat ≤ sp.toNat at hq_le_sp
  change q.toNat + _ = sp.toNat at hq_add
  have hn_globs : next.globals = cur.globals.update (ofString "scratch_ptr", .val (.word q)) := by
    rw [hnext]
  have hn_hp : globN next "heap_ptr" = globN cur "heap_ptr" := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide]
  have hn_fmp : globN next "frame_mem_ptr" = globN cur "frame_mem_ptr" := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, show ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hn_sp : globN next "scratch_ptr" = q.toNat := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]; simp [FUPDATE]
  have hn_G : GuestInv next :=
    guestInv_congr (by rw [hnext]) (by rw [hnext]) (by rw [hnext]) (by rw [hnext]) h.arena.1
  have hn_gw : GlobalsWord next :=
    globalsWord_update (ofString "scratch_ptr") q hn_globs hc_gw
  have hn_A : ArenaOK next := by
    unfold ArenaOK; rw [hn_hp, hn_fmp, hn_sp]
    exact ⟨hc_hp_lo, hc_hp_hi, hc_fm_lo, by rw [hfp_glob]; exact hfp_le_q,
      le_trans hq_le_sp (by rw [← hsp_glob]; exact hc_sp_hi),
      hc_hp_al, hc_fm_al, hq_al, hn_gw⟩
  have hn_kept : GlobalsKept gw s next := by
    intro k hk
    have hne : k ≠ ofString "scratch_ptr" := fun heq => hk (heq ▸ hgw_sp)
    rw [h.gw_kept k hk, hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, Ne.symm hne]
  have hn_bufs : FreshBufsOK s next := by
    have hgb_eq : ∀ gn ∈ globalBuffers, globN next gn.1 = globN cur gn.1 := by
      intro gn hgn
      have hne : ofString gn.1 ≠ ofString "scratch_ptr" :=
        (by decide : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "scratch_ptr") gn hgn
      unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]
      simp [FUPDATE, hne, Ne.symm hne]
    refine ⟨fun gn hgn => ?_, ?_⟩
    · rw [hgb_eq gn hgn, hn_hp]; exact h.fresh_bufs.1 gn hgn
    · rw [List.pairwise_iff_getElem]
      have hpw := List.pairwise_iff_getElem.1 h.fresh_bufs.2
      intro i j hi hj hlt ha hb
      rw [hgb_eq _ (List.getElem_mem hi)] at ha ⊢
      rw [hgb_eq _ (List.getElem_mem hj)] at hb ⊢
      exact hpw i j hi hj hlt ha hb
  have hn_mem : next.memory = cur.memory := by rw [hnext]
  have hn_be : next.be = cur.be := by rw [hnext]
  have hsb_ss : sourceBase ≤ scratchStart := by decide
  have hse_he : scratchEnd ≤ heapEnd := by decide
  have hq_lo_sb : sourceBase ≤ q.toNat :=
    le_trans hsb_ss (le_trans hc_fm_lo (by rw [hfp_glob]; exact hfp_le_q))
  have hq_hi_he : q.toNat + (n.toNat + 7) / 8 * 8 ≤ heapEnd := by
    rw [hq_add]; exact le_trans (by rw [← hsp_glob]; exact hc_sp_hi) hse_he
  have hwok : WordsOK next (q.toNat, (n.toNat + 7) / 8 * 8) :=
    wordsOK_of_inside_heap hn_G hq_al (by omega) hq_lo_sb hq_hi_he
  refine ⟨⟨⟨hn_G, hn_A⟩, by rw [hnext]; exact h.code, by rw [hnext]; exact h.memaddrs,
    hn_be.trans h.be, by rw [hnext]; exact h.eshapes,
    by rw [hn_hp]; exact h.hp_lo, hn_fmp.trans h.fmp_eq,
    by rw [hn_sp]; exact le_trans hq_le_sp (by rw [← hsp_glob]; exact h.sp_hi),
    hn_kept, hn_bufs,
    fun a hne => h.out_dom a (by rwa [hn_mem] at hne),
    fun a hne => h.cell_frame a (by rwa [hn_mem] at hne),
    fun b hb64 hne => h.byte_frame b hb64 (by unfold memB at hne ⊢; rwa [hn_mem, hn_be] at hne)⟩,
    hq_al, by rw [← h.fmp_eq, hfp_glob]; exact hfp_le_q, hq_add,
    by rw [← hsp_glob]; exact h.sp_hi, hn_sp, hwok⟩

/-! ## Section 3: Statement & Call Combinators for `WorldEff` -/

abbrev ContOrRes (r : Option (PanSemResultExact 64)) : Prop :=
  r = none ∨ r = some .break ∨ r = some .continue ∨ Resumes r

theorem worldEff_scratch_release_step {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (hAs : ArenaOK s)
    (h : WorldEff s cur Rl B gw)
    (hgw_sp : ofString "scratch_ptr" ∈ gw.map ofString)
    {mw : BitVec 64}
    (hm_lo : globN s "frame_mem_ptr" ≤ mw.toNat)
    (hm_hi : mw.toNat ≤ globN s "scratch_ptr")
    (hm_al : mw.toNat % 8 = 0)
    {next : PanSemStateFiniteExact 64 F}
    (hnext : next = { cur with
      globals := cur.globals.update (ofString "scratch_ptr", .val (.word mw)),
      locals := next.locals, clock := next.clock }) :
    WorldEff s next Rl B gw ∧ globN next "scratch_ptr" = mw.toNat := by
  rcases h.arena.2 with ⟨hc_hp_lo, hc_hp_hi, hc_fm_lo, _, _, hc_hp_al, hc_fm_al, _, hc_gw⟩
  have hn_globs : next.globals = cur.globals.update (ofString "scratch_ptr", .val (.word mw)) := by
    rw [hnext]
  have hn_hp : globN next "heap_ptr" = globN cur "heap_ptr" := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide]
  have hn_fmp : globN next "frame_mem_ptr" = globN cur "frame_mem_ptr" := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, show ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hn_sp : globN next "scratch_ptr" = mw.toNat := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]; simp [FUPDATE]
  have hn_G : GuestInv next :=
    guestInv_congr (by rw [hnext]) (by rw [hnext]) (by rw [hnext]) (by rw [hnext]) h.arena.1
  have hn_gw : GlobalsWord next :=
    globalsWord_update (ofString "scratch_ptr") mw hn_globs hc_gw
  have hn_A : ArenaOK next := by
    unfold ArenaOK; rw [hn_hp, hn_fmp, hn_sp]
    exact ⟨hc_hp_lo, hc_hp_hi, hc_fm_lo, by rw [h.fmp_eq]; exact hm_lo,
      le_trans hm_hi hAs.2.2.2.2.1, hc_hp_al, hc_fm_al, hm_al, hn_gw⟩
  have hn_kept : GlobalsKept gw s next := by
    intro k hk
    have hne : k ≠ ofString "scratch_ptr" := fun heq => hk (heq ▸ hgw_sp)
    rw [h.gw_kept k hk, hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, Ne.symm hne]
  have hn_bufs : FreshBufsOK s next := by
    have hgb_eq : ∀ gn ∈ globalBuffers, globN next gn.1 = globN cur gn.1 := by
      intro gn hgn
      have hne : ofString gn.1 ≠ ofString "scratch_ptr" :=
        (by decide : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "scratch_ptr") gn hgn
      unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]
      simp [FUPDATE, hne, Ne.symm hne]
    refine ⟨fun gn hgn => ?_, ?_⟩
    · rw [hgb_eq gn hgn, hn_hp]; exact h.fresh_bufs.1 gn hgn
    · rw [List.pairwise_iff_getElem]
      have hpw := List.pairwise_iff_getElem.1 h.fresh_bufs.2
      intro i j hi hj hlt ha hb
      rw [hgb_eq _ (List.getElem_mem hi)] at ha ⊢
      rw [hgb_eq _ (List.getElem_mem hj)] at hb ⊢
      exact hpw i j hi hj hlt ha hb
  have hn_mem : next.memory = cur.memory := by rw [hnext]
  have hn_be : next.be = cur.be := by rw [hnext]
  refine ⟨⟨⟨hn_G, hn_A⟩, by rw [hnext]; exact h.code, by rw [hnext]; exact h.memaddrs,
    hn_be.trans h.be, by rw [hnext]; exact h.eshapes,
    by rw [hn_hp]; exact h.hp_lo, hn_fmp.trans h.fmp_eq,
    by rw [hn_sp]; exact hm_hi,
    hn_kept, hn_bufs,
    fun a hne => h.out_dom a (by rwa [hn_mem] at hne),
    fun a hne => h.cell_frame a (by rwa [hn_mem] at hne),
    fun b hb64 hne => h.byte_frame b hb64 (by unfold memB at hne ⊢; rwa [hn_mem, hn_be] at hne)⟩,
    hn_sp⟩

theorem byteEff_shMemLoad_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (op : OpSize) (name : MlS) (addr : ExpHOL 64) (Rl : List Ivl) :
    ByteEff s (evaluateHOLFiniteState s (.shMemLoad op .local name addr)).2 Rl := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source]
  split
  · split
    · unfold shMemLoadHOLFiniteExact
      dsimp only
      split <;> split <;> (try split) <;>
        (refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          fun _ h => absurd rfl h, fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩)
    · exact ByteEff.refl s Rl
  · exact ByteEff.refl s Rl

theorem shMemLoad_local_none_inv {F : Type}
    (s : PanSemStateFiniteExact 64 F) (op : OpSize) (name : MlS) (addr : ExpHOL 64)
    {post : PanSemStateFiniteExact 64 F}
    (hrun : evaluateHOLFiniteState s (.shMemLoad op .local name addr) = (none, post)) :
    ∃ val : BitVec 64,
      post = { s with locals := s.locals.update (name, .val (.word val)), ffi := post.ffi } := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source] at hrun
  split at hrun
  · split at hrun
    · unfold shMemLoadHOLFiniteExact at hrun
      split at hrun
      · split at hrun
        · split at hrun
          · simp at hrun
          · obtain ⟨_, rfl⟩ := Prod.mk.inj hrun
            exact ⟨_, rfl⟩
        · simp at hrun
      · split at hrun
        · split at hrun
          · simp at hrun
          · obtain ⟨_, rfl⟩ := Prod.mk.inj hrun
            exact ⟨_, rfl⟩
        · simp at hrun
    · simp at hrun
  · simp at hrun

theorem shMemLoad_local_not_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (op : OpSize) (name : MlS) (addr : ExpHOL 64) :
    ¬ Resumes (evaluateHOLFiniteState s (.shMemLoad op .local name addr)).1 := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source]
  split
  · split
    · unfold shMemLoadHOLFiniteExact
      dsimp only
      split <;> split <;> (try split) <;>
        (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

theorem worldEff_shMemLoad_local {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw) (op : OpSize) (name : MlS) (addr : ExpHOL 64) :
    WorldEff s (evaluateHOLFiniteState cur (.shMemLoad op .local name addr)).2 Rl B gw :=
  h.of_byteEff (byteEff_shMemLoad_local cur op name addr []) (fun _ hiv => by cases hiv)

theorem worldEff_skip {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw) :
    WorldEff s (evaluateHOLFiniteState cur .skip).2 Rl B gw := by
  rw [evaluateHOLFiniteState_skip]; exact h

theorem worldEff_return {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw) (e : ExpHOL 64) :
    WorldEff s (evaluateHOLFiniteState cur (.return e)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_return]
  split
  · exact h
  · split <;> [exact h.locals_clock _ cur.clock; exact h]

theorem worldEff_raise {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw) (eid : MlS) (e : ExpHOL 64) :
    WorldEff s (evaluateHOLFiniteState cur (.raise eid e)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only; split <;> [exact h.locals_clock _ cur.clock; exact h]
  · exact h

theorem worldEff_assign_local {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw) (name : MlS) (e : ExpHOL 64) :
    WorldEff s (evaluateHOLFiniteState cur (.assign .local name e)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_assign]
  split
  · exact h
  · split <;> [exact h.locals_clock _ cur.clock; exact h]

theorem worldEff_dec {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.dec name sh init body)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.dec name sh init body)).1)
    (hb : ∀ val,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) init = some val →
      shapeEqHOL sh (shapeOfHOLExact val) = true →
      (evaluateHOLFiniteState (setVarHOLFinite name val cur) body).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (setVarHOLFinite name val cur) body).1 →
      WorldEff s (evaluateHOLFiniteState (setVarHOLFinite name val cur) body).2 Rl B gw) :
    WorldEff s (evaluateHOLFiniteState cur (.dec name sh init body)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_dec_total] at hnt hcr ⊢
  dsimp only at hnt hcr ⊢
  rcases hval : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) init with _ | val
  · exact h
  · rw [hval] at hnt hcr
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact val) = true
    · simp only [hsh, ↓reduceIte] at hnt hcr ⊢
      exact (hb val hval hsh hnt hcr).locals_clock _ _
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte]; exact h

theorem worldEff_seq {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    {a b : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.seq a b)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.seq a b)).1)
    (ha : (evaluateHOLFiniteState cur a).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur a).1 →
      WorldEff s (evaluateHOLFiniteState cur a).2 Rl B gw)
    (hb : ∀ mid, evaluateHOLFiniteState cur a = (none, mid) →
      WorldEff s mid Rl B gw →
      (evaluateHOLFiniteState mid b).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid b).1 →
      WorldEff s (evaluateHOLFiniteState mid b).2 Rl B gw) :
    WorldEff s (evaluateHOLFiniteState cur (.seq a b)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hcr ⊢
  rcases hra : evaluateHOLFiniteState cur a with ⟨ra, mid⟩
  rw [hra] at hnt hcr
  have hnt_a : ra ≠ some .timeOut := fun h => by subst h; exact hnt rfl
  cases ra with
  | none =>
    have effa := ha (by rw [hra]; exact hnt_a) (by rw [hra]; exact Or.inl rfl)
    rw [hra] at effa
    exact hb mid hra effa hnt hcr
  | some r1 =>
    have hcr_a : ContOrRes (some r1) := by
      rcases hcr with h | h | h | hr
      · cases h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr hr))
    have effa := ha (by rw [hra]; exact hnt_a) (by rw [hra]; exact hcr_a)
    rw [hra] at effa
    exact effa

theorem worldEff_ite {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.ite cond yes no)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.ite cond yes no)).1)
    (hy : ∀ cw : BitVec 64,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond = some (.val (.word cw)) →
      cw ≠ 0 →
      (evaluateHOLFiniteState cur yes).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur yes).1 →
      WorldEff s (evaluateHOLFiniteState cur yes).2 Rl B gw)
    (hn : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond = some (.val (.word 0)) →
      (evaluateHOLFiniteState cur no).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur no).1 →
      WorldEff s (evaluateHOLFiniteState cur no).2 Rl B gw) :
    WorldEff s (evaluateHOLFiniteState cur (.ite cond yes no)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_ite] at hnt hcr ⊢
  rcases hc : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
  · exact h
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try exact h
    rw [hc] at hnt hcr
    dsimp only at hnt hcr ⊢
    by_cases h0 : cw = 0
    · subst h0; rw [if_pos rfl] at hnt hcr ⊢; exact hn hc hnt hcr
    · rw [if_neg h0] at hnt hcr ⊢; exact hy cw hc h0 hnt hcr

theorem worldEff_while {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (cond : ExpHOL 64) {body : ProgHOL 64}
    (Inv : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, Inv t → Inv (decClockHOLFinite t))
    (hb : ∀ t, WorldEff s t Rl B gw → Inv t →
      (evaluateHOLFiniteState t body).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState t body).1 →
      WorldEff s (evaluateHOLFiniteState t body).2 Rl B gw ∧
      (((evaluateHOLFiniteState t body).1 = none ∨
        (evaluateHOLFiniteState t body).1 = some .continue) →
        Inv (evaluateHOLFiniteState t body).2)) :
    ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F), cur.clock = k →
      WorldEff s cur Rl B gw → Inv cur →
      (evaluateHOLFiniteState cur (.while cond body)).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur (.while cond body)).1 →
      WorldEff s (evaluateHOLFiniteState cur (.while cond body)).2 Rl B gw := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro cur hclk heff hinv hnt hcr
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hcr ⊢
    rcases hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
    · exact heff
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try exact heff
      rw [hc] at hnt hcr; dsimp only at hnt hcr ⊢
      by_cases hw0 : cw = 0
      · subst hw0; simp; exact heff
      · rw [if_pos hw0] at hnt hcr ⊢
        by_cases hk0 : cur.clock = 0
        · rw [if_pos hk0] at hnt; exact absurd rfl hnt
        · rw [if_neg hk0] at hnt hcr ⊢
          have heff_d : WorldEff s (decClockHOLFinite cur) Rl B gw := heff.locals_clock cur.locals (cur.clock - 1)
          have hinv_d : Inv (decClockHOLFinite cur) := hdec cur hinv
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) body
          rcases hbo : evaluateHOLFiniteState (decClockHOLFinite cur) body with ⟨rb, sb⟩
          simp only [hbo] at hnt hcr hrem ⊢
          have hlt : sb.clock < k := by
            change sb.clock ≤ cur.clock - 1 at hrem; omega
          cases rb with
          | none =>
            obtain ⟨heff_b, hinv_b⟩ := hb (decClockHOLFinite cur) heff_d hinv_d
              (by rw [hbo]; simp) (by rw [hbo]; exact Or.inl rfl)
            rw [hbo] at heff_b hinv_b
            exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inl rfl)) hnt hcr
          | some r1 =>
            cases r1 with
            | «continue» =>
              obtain ⟨heff_b, hinv_b⟩ := hb (decClockHOLFinite cur) heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hbo] at heff_b hinv_b
              exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inr rfl)) hnt hcr
            | «break» =>
              obtain ⟨heff_b, _⟩ := hb (decClockHOLFinite cur) heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inl rfl))
              rw [hbo] at heff_b; exact heff_b
            | timeOut => exact absurd rfl hnt
            | returned v =>
              obtain ⟨heff_b, _⟩ := hb (decClockHOLFinite cur) heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hbo] at heff_b; exact heff_b
            | exception eid ev =>
              have hres_e : Resumes (some (.exception eid ev)) := by
                rcases hcr with h | h | h | hr <;> [cases h; cases h; cases h; exact hr]
              obtain ⟨heff_b, _⟩ := hb (decClockHOLFinite cur) heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr hres_e)))
              rw [hbo] at heff_b; exact heff_b
            | error =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h
            | finalFfi _ =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h

theorem worldEff_store_word {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (dstExp valExp : ExpHOL 64)
    (hval_one : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
        some (.val (.word x)) →
      cur.memaddrs x →
      (∃ j ∈ Rl, j.1 ≤ x.toNat ∧ x.toNat + 8 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ x.toNat ∧ x.toNat + 8 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ x.toNat ∧ x.toNat + 8 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ x.toNat ∧ x.toNat + 8 ≤ heapLimit)) :
    WorldEff s (evaluateHOLFiniteState cur (.store dstExp valExp)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_store]
  rcases hx : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp with _ | dv
  · exact h
  · rcases dv with ⟨⟨x⟩⟩ | _ | _ <;> try exact h
    rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp with _ | val
    · exact h
    · obtain ⟨w, rfl⟩ := hval_one val hv
      have hb := (byteEff_store_one h.arena.1 dstExp valExp hval_one (Rl := [(x.toNat, 8)])
        (fun x' hx' _ => by
          rw [hx] at hx'; injection hx' with hx'; injection hx' with hx'; injection hx' with hx'; subst hx'
          exact ⟨(x.toNat, 8), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)).1
      rw [evaluateHOLFiniteState_store, hx, hv] at hb
      by_cases hdom : cur.memaddrs x
      · exact h.of_byteEff hb (fun iv hiv _ => by
          simp at hiv; subst hiv
          exact hin x hx hdom)
      · dsimp only
        split
        · rename_i mem' hmem
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte] at hmem
          cases hmem
        · exact h

theorem worldEff_storeByte {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (dstExp valExp : ExpHOL 64)
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
        some (.val (.word x)) →
      cur.memaddrs (panByteAlignHOL x) →
      (∃ j ∈ Rl, j.1 ≤ x.toNat ∧ x.toNat + 1 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ x.toNat ∧ x.toNat + 1 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ x.toNat ∧ x.toNat + 1 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ x.toNat ∧ x.toNat + 1 ≤ heapLimit)) :
    WorldEff s (evaluateHOLFiniteState cur (.storeByte dstExp valExp)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_storeByte]
  rcases hx : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp with _ | dv
  · exact h
  · rcases dv with ⟨⟨x⟩⟩ | _ | _ <;> try exact h
    rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp with _ | val
    · exact h
    · rcases val with ⟨⟨vw⟩⟩ | _ | _ <;> try exact h
      by_cases hdom : cur.memaddrs (panByteAlignHOL x)
      · have hb := (byteEff_storeByte h.arena.1 dstExp valExp (Rl := [(x.toNat, 1)])
          (fun x' hx' _ => by
            rw [hx] at hx'; injection hx' with hx'; injection hx' with hx'; injection hx' with hx'; subst hx'
            exact ⟨(x.toNat, 1), List.mem_singleton.2 rfl, le_rfl, by omega⟩)).1
        rw [evaluateHOLFiniteState_storeByte, hx, hv] at hb
        exact h.of_byteEff hb (fun iv hiv _ => by
          simp at hiv; subst hiv
          exact hin x hx hdom)
      · dsimp only
        split
        · rename_i mem' hmem
          unfold panMemStoreByteWord8HOL at hmem
          cases cur.memory (panByteAlignHOL x) with
          | word _ => simp [hdom] at hmem
        · exact h

/-! ## Section 4: Call Combinators for `WorldEff` -/

theorem worldEff_call0_ro {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    {fname : MlS} (hf : ReadOnlyFn fname) (args : List (ExpHOL 64))
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).2 Rl B gw :=
  h.of_readOnly (InitECandidate.Solver.Wave8GuestInv.R13.ReadOnlyProg.call0 hf args cur h.code h.arena.1 hnt hcr)

theorem worldEff_decCall_ro {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    {fname : MlS} (hf : ReadOnlyFn fname)
    (name : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).1)
    (hcont : ∀ (rv : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F),
      shapeEqHOL (shapeOfHOLExact rv) sh = true →
      cpost = { cur with locals := cpost.locals, clock := cpost.clock } →
      (evaluateHOLFiniteState (setVarHOLFinite name rv { cpost with locals := cur.locals }) cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (setVarHOLFinite name rv { cpost with locals := cur.locals }) cont).1 →
      WorldEff s (evaluateHOLFiniteState (setVarHOLFinite name rv { cpost with locals := cur.locals }) cont).2 Rl B gw) :
    WorldEff s (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).2 Rl B gw := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | values
  · exact h
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact h
    · simp only [hl] at hnt hcr ⊢
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt hcr ⊢
        have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup fname params body body'
          ret ret' values callee (by rw [h.code]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return cur fname params body' body'
          ret ret' values callee (by rw [h.code]; exact hlook) hl
        subst hret_eq
        have hentryEq : callEntryStateHOLFinite cur callee =
            { cur with locals := callee, clock := (callEntryStateHOLFinite cur callee).clock } := by
          cases cur; rfl
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', (callEntryStateHOLFinite cur callee).locals, ret') :=
          ⟨values, by simpa only [h.code, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) body' with ⟨res, cpost⟩
        simp only [hrun] at hnt hcr ⊢
        cases res with
        | none => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | returned rv =>
            dsimp only at hnt hcr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hcr ⊢
              have hsh1 : shapeEqHOL (shapeOfHOLExact rv) sh = true := (Bool.and_eq_true _ _ ▸ hsh).1
              have hro := hspec (callEntryStateHOLFinite cur callee) h.code
                (guestInv_callEntry cur callee h.arena.1) hex
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
              rw [hrun] at hro; dsimp only at hro
              have hcpost : cpost = { cur with locals := cpost.locals, clock := cpost.clock } :=
                InitECandidate.Solver.Wave8GuestInv.R13.state_trans_locals_clock hentryEq hro
              exact (hcont rv cpost hsh1 hcpost hnt hcr).locals_clock _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hcr
              rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | exception eid ev =>
            have hres_e : Resumes (some (.exception eid ev)) := by
              rcases hcr with hc0 | hc0 | hc0 | hr <;> [simp at hc0; simp at hc0; simp at hc0; exact hr]
            have hro := hspec (callEntryStateHOLFinite cur callee) h.code
              (guestInv_callEntry cur callee h.arena.1) hex
              (by rw [hrun]; simp) (by rw [hrun]; exact hres_e)
            rw [hrun] at hro; dsimp only at hro
            have hcpost : cpost = { cur with locals := cpost.locals, clock := cpost.clock } :=
              InitECandidate.Solver.Wave8GuestInv.R13.state_trans_locals_clock hentryEq hro
            exact (h.of_readOnly hcpost).locals_clock _ _
          | timeOut => simp at hnt
          | _ => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0

theorem worldEff_decCall_alloc {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (name : MlS) (szExp : ExpHOL 64) {cont : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.decCall name .one (ofString "alloc") [szExp] cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.decCall name .one (ofString "alloc") [szExp] cont)).1)
    (hcont : ∀ (pw nw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp = some (.val (.word nw)) →
      mid.memory = cur.memory →
      mid.locals = cur.locals.update (name, .val (.word pw)) →
      (∀ k : MlS, k ≠ ofString "heap_ptr" → mid.globals.lookup k = cur.globals.lookup k) →
      WorldEff s mid Rl B gw →
      pw.toNat % 8 = 0 →
      sourceBase ≤ pw.toNat →
      globN s "heap_ptr" ≤ pw.toNat →
      pw.toNat + (nw.toNat + 7) / 8 * 8 = globN mid "heap_ptr" →
      globN mid "heap_ptr" ≤ heapLimit →
      WordsOK mid (pw.toNat, (nw.toNat + 7) / 8 * 8) →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B gw) :
    WorldEff s (evaluateHOLFiniteState cur (.decCall name .one (ofString "alloc") [szExp] cont)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [szExp] with _ | values
  · exact h
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "alloc") values with _ | ⟨body', callee, ret'⟩
    · exact h
    · simp only [hl] at hnt hcr ⊢
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt hcr ⊢
        have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup (ofString "alloc") _ _ body'
          _ ret' values callee (by rw [h.code]; exact lookup_alloc) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return cur (ofString "alloc") _ _ _
          _ ret' values callee (by rw [h.code]; exact lookup_alloc) hl
        subst hret_eq
        obtain ⟨nw, rfl, hnw_callee⟩ := lookupCode_one_word lookup_alloc (by rwa [← h.code])
        have hsz_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp =
            some (.val (.word nw)) := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          split at hargs <;> simp at hargs
          rename_i v hv _; rw [hargs.1] at hv; exact hv
        obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, cur.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
          globalWord_of_globN_pos cur "heap_ptr" (by have := h.arena.2.1; rw [sourceBase_val] at this; omega)
        let entry := callEntryStateHOLFinite cur callee
        rcases hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res, pa⟩
        dsimp only [entry] at hrun
        simp only [hrun] at hnt hcr ⊢
        have hres_a : Resumes res := by
          cases res with
          | none => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | some r1 =>
            cases r1 with
            | returned rv => exact Or.inl ⟨rv, rfl⟩
            | exception eid ev =>
              rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨e', v', hc0, hne⟩⟩
              · simp at hc0
              · simp at hc0
              · simp at hc0
              · simp at hc0
              · change some (PanSemResultExact.exception eid ev) = some (PanSemResultExact.exception e' v') at hc0
                injection hc0 with hc0'; injection hc0' with he1 he2; subst he1 he2
                exact Or.inr ⟨eid, ev, rfl, hne⟩
            | timeOut => exact absurd rfl hnt
            | _ => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        have hal := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes entry pw h.code hpw_lk
          (by dsimp only [entry]; rw [hrun]; exact hres_a)
        dsimp only [entry] at hal
        rw [hrun] at hal
        obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
        have hnw_eq : nw = nw' := by
          have : entry.locals.lookup (ofString "n") = some (.val (.word nw)) := hnw_callee
          rw [this] at hnw'_lk; injection hnw'_lk with h'; injection h' with h'; injection h'
        subst hnw_eq
        dsimp only at hrv_eq hpa_eq
        subst hrv_eq
        dsimp only at hnt hcr ⊢
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at hnt hcr ⊢
        dsimp only at hnt hcr ⊢
        let mid := setVarHOLFinite name (.val (.word pw)) { pa with locals := cur.locals }
        have hmid_next : mid = { cur with
            globals := cur.globals.update (ofString "heap_ptr", .val (.word ((pw + (nw + 7)) &&& ((0 : BitVec 64) - 8)))),
            locals := mid.locals, clock := mid.clock } := by
          dsimp only [mid, setVarHOLFinite]; rw [hpa_eq]; rfl
        obtain ⟨heff_m, _, hp_al, hp_lo_sb, hp_lo_s, hp_add, hp_hi, hwok⟩ :=
          worldEff_alloc_step h hgw_hp hpw_lk hcmp1 hcmp2 hmid_next
        have hmid_mem : mid.memory = cur.memory := by rw [hmid_next]
        have hmid_loc : mid.locals = cur.locals.update (name, .val (.word pw)) := rfl
        have hmid_g : ∀ k : MlS, k ≠ ofString "heap_ptr" → mid.globals.lookup k = cur.globals.lookup k := by
          intro k hk; rw [hmid_next]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        exact (hcont pw nw mid hsz_ev hmid_mem hmid_loc hmid_g heff_m hp_al hp_lo_sb hp_lo_s
          hp_add hp_hi hwok hnt hcr).locals_clock _ _

theorem worldEff_decCall_scratch_alloc {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (hgw_sp : ofString "scratch_ptr" ∈ gw.map ofString)
    (name : MlS) (szExp : ExpHOL 64) {cont : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.decCall name .one (ofString "scratch_alloc") [szExp] cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.decCall name .one (ofString "scratch_alloc") [szExp] cont)).1)
    (hcont : ∀ (qw nw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp = some (.val (.word nw)) →
      mid.memory = cur.memory →
      mid.locals = cur.locals.update (name, .val (.word qw)) →
      (∀ k : MlS, k ≠ ofString "scratch_ptr" → mid.globals.lookup k = cur.globals.lookup k) →
      WorldEff s mid Rl B gw →
      qw.toNat % 8 = 0 →
      globN s "frame_mem_ptr" ≤ qw.toNat →
      qw.toNat + (nw.toNat + 7) / 8 * 8 = globN cur "scratch_ptr" →
      globN cur "scratch_ptr" ≤ globN s "scratch_ptr" →
      globN mid "scratch_ptr" = qw.toNat →
      WordsOK mid (qw.toNat, (nw.toNat + 7) / 8 * 8) →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B gw) :
    WorldEff s (evaluateHOLFiniteState cur (.decCall name .one (ofString "scratch_alloc") [szExp] cont)).2 Rl B gw := by
  have hlook_sa : originalRuntimeCode.lookup (ofString "scratch_alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_scratch_alloc, .one) :=
    lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_scratch_alloc) rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [szExp] with _ | values
  · exact h
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "scratch_alloc") values with _ | ⟨body', callee, ret'⟩
    · exact h
    · simp only [hl] at hnt hcr ⊢
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt hcr ⊢
        have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup (ofString "scratch_alloc") _ _ body'
          _ ret' values callee (by rw [h.code]; exact hlook_sa) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return cur (ofString "scratch_alloc") _ _ _
          _ ret' values callee (by rw [h.code]; exact hlook_sa) hl
        subst hret_eq
        obtain ⟨nw, rfl, hnw_callee⟩ := lookupCode_one_word hlook_sa (by rwa [← h.code])
        have hsz_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp =
            some (.val (.word nw)) := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          split at hargs <;> simp at hargs
          rename_i v hv _; rw [hargs.1] at hv; exact hv
        obtain ⟨sp, hsp_lk⟩ : ∃ sp : BitVec 64, cur.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) :=
          globalWord_of_globN_pos cur "scratch_ptr"
            (by have := h.arena.2.2.2.1; have := h.arena.2.2.2.2.1; rw [scratchStart_val] at *; omega)
        obtain ⟨fp, hfp_lk⟩ : ∃ fp : BitVec 64, cur.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)) :=
          globalWord_of_globN_pos cur "frame_mem_ptr"
            (by have := h.arena.2.2.2.1; rw [scratchStart_val] at this; omega)
        let entry := callEntryStateHOLFinite cur callee
        rcases hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_scratch_alloc) with ⟨res, pa⟩
        dsimp only [entry] at hrun
        simp only [hrun] at hnt hcr ⊢
        have hres_sa : Resumes res := by
          cases res with
          | none => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | some r1 =>
            cases r1 with
            | returned rv => exact Or.inl ⟨rv, rfl⟩
            | exception eid ev =>
              rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨e', v', hc0, hne⟩⟩
              · simp at hc0
              · simp at hc0
              · simp at hc0
              · simp at hc0
              · change some (PanSemResultExact.exception eid ev) = some (PanSemResultExact.exception e' v') at hc0
                injection hc0 with hc0'; injection hc0' with he1 he2; subst he1 he2
                exact Or.inr ⟨eid, ev, rfl, hne⟩
            | timeOut => exact absurd rfl hnt
            | _ => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        have hsa := InitECandidate.Solver.Wave8GuestInv.R13.scratch_alloc_body_resumes entry sp fp h.code
          hsp_lk hfp_lk (by dsimp only [entry]; rw [hrun]; exact hres_sa)
        dsimp only [entry] at hsa
        rw [hrun] at hsa
        obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hsa
        have hnw_eq : nw = nw' := by
          have : entry.locals.lookup (ofString "n") = some (.val (.word nw)) := hnw_callee
          rw [this] at hnw'_lk; injection hnw'_lk with h'; injection h' with h'; injection h'
        subst hnw_eq
        dsimp only at hrv_eq hpa_eq
        subst hrv_eq
        dsimp only at hnt hcr ⊢
        let qw := (sp - nw) &&& ((0 : BitVec 64) - 8)
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word qw))) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word qw))) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at hnt hcr ⊢
        dsimp only at hnt hcr ⊢
        let mid := setVarHOLFinite name (.val (.word qw)) { pa with locals := cur.locals }
        have hmid_next : mid = { cur with
            globals := cur.globals.update (ofString "scratch_ptr", .val (.word qw)),
            locals := mid.locals, clock := mid.clock } := by
          dsimp only [mid, setVarHOLFinite]; rw [hpa_eq]; rfl
        obtain ⟨heff_m, hq_al, hq_lo, hq_add, hsp_le, hn_sp, hwok⟩ :=
          worldEff_scratch_alloc_step h hgw_sp hsp_lk hfp_lk hcmp1 hcmp2 hmid_next
        have hsp_glob : globN cur "scratch_ptr" = sp.toNat := by simp [globN, hsp_lk]
        have hmid_mem : mid.memory = cur.memory := by rw [hmid_next]
        have hmid_loc : mid.locals = cur.locals.update (name, .val (.word qw)) := rfl
        have hmid_g : ∀ k : MlS, k ≠ ofString "scratch_ptr" → mid.globals.lookup k = cur.globals.lookup k := by
          intro k hk; rw [hmid_next]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        exact (hcont qw nw mid hsz_ev hmid_mem hmid_loc hmid_g heff_m hq_al hq_lo
          (by rw [hsp_glob]; exact hq_add) (by rw [hsp_glob]; exact hsp_le) hn_sp hwok hnt hcr).locals_clock _ _

/-! ## Section 5: Scratch Mark/Release, Handled Calls, and `wsafe` Word-Local Preservation -/

theorem resVarEq_lookup_local {V : Type} (m : HolFiniteMapExact MlS V) (k x : MlS) (ov : Option V) :
    (HolFiniteMapExact.resVarEq m (k, ov)).lookup x = if x = k then ov else m.lookup x := by
  unfold HolFiniteMapExact.resVarEq
  cases ov with
  | none =>
    by_cases h : x = k <;> simp [FDOMSUB_HOL, h, Ne.symm]
  | some v =>
    by_cases h : x = k <;> simp [HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL, h, Ne.symm]

def wsafe : ProgHOL 64 → Bool
  | .dec _ _ _ body => wsafe body
  | .seq first second => wsafe first && wsafe second
  | .ite _ yes no => wsafe yes && wsafe no
  | .while _ body => wsafe body
  | .assign _ _ _ => true
  | .store _ _ | .storeByte _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .decCall _ _ _ _ continuation => wsafe continuation
  | .call none _ _ => true
  | .call (some (_, none)) _ _ => true
  | .call (some (_, some (_, _, handler))) _ _ => wsafe handler
  | .shMemLoad _ .local _ _ => true
  | _ => false

theorem evaluate_wordLocal {F : Type} (x : MlS)
    (program : ProgHOL 64) (supported : wsafe program = true)
    (state : PanSemStateFiniteExact 64 F)
    (hx : ∃ w : BitVec 64, state.locals.lookup x = some (.val (.word w)))
    (hflow : Flowing (evaluateHOLFiniteState state program).1) :
    ∃ w : BitVec 64, (evaluateHOLFiniteState state program).2.locals.lookup x = some (.val (.word w)) := by
  cases shape : program with
  | skip => subst shape; rw [evaluateHOLFiniteState_skip]; exact hx
  | «break» => subst shape; rw [evaluateHOLFiniteState_break]; exact hx
  | «continue» => subst shape; rw [evaluateHOLFiniteState_continue]; exact hx
  | annot _ _ => subst shape; rw [evaluateHOLFiniteState_annot]; exact hx
  | raise _ _ =>
    subst shape; revert hflow; rw [evaluateHOLFiniteState_raise]
    split <;> [ (dsimp only; split <;> simp [Flowing]); simp [Flowing] ]
  | «return» _ =>
    subst shape; revert hflow; rw [evaluateHOLFiniteState_return]
    split <;> [ simp [Flowing]; (split <;> simp [Flowing]) ]
  | store _ _ =>
    subst shape; revert hflow; rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> [ (intro _; exact hx); simp [Flowing] ]
      · simp [Flowing]
    · simp [Flowing]
  | storeByte _ _ =>
    subst shape; revert hflow; rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> [ (intro _; exact hx); simp [Flowing] ]
      · simp [Flowing]
    · simp [Flowing]
  | assign kind name _ =>
    subst shape; revert hflow; rw [evaluateHOLFiniteState_assign]
    split
    · simp [Flowing]
    · rename_i v _
      split
      · rename_i hvalid
        intro _
        obtain ⟨w, hw⟩ := hx
        cases kind with
        | global => exact ⟨w, by simpa [setKvarHOLFinite, setGlobalHOLFinite] using hw⟩
        | «local» =>
          by_cases hxn : x = name
          · subst hxn
            have hsh : shapeEqHOL (shapeOfHOLExact v) .one = true := by
              simpa [isValidValueHOLFinite, lookupKvarHOLFinite, hw, shapeOfHOLExact] using hvalid
            rcases v with ⟨⟨w'⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh)
            exact ⟨w', by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
          · exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn, hw]⟩
      · simp [Flowing]
  | dec name _ _ body =>
    have child : wsafe body = true := by simpa only [shape, wsafe] using supported
    subst shape; revert hflow; rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp [Flowing]
    · split
      · rename_i v _ _
        intro hflow
        obtain ⟨w, hw⟩ := hx
        by_cases hxn : x = name
        · subst hxn; exact ⟨w, by dsimp only; rw [resVarEq_lookup_local, if_pos rfl]; exact hw⟩
        · obtain ⟨w', hw'⟩ := evaluate_wordLocal x body child (setVarHOLFinite name v state)
            ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn, hw]⟩ hflow
          exact ⟨w', by dsimp only; rw [resVarEq_lookup_local, if_neg hxn]; exact hw'⟩
      · simp [Flowing]
  | seq first second =>
    have children : wsafe first = true ∧ wsafe second = true := by
      simpa only [shape, wsafe, Bool.and_eq_true] using supported
    subst shape
    have remaining := evaluateHOLFiniteState_clock_le state first
    revert hflow; rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at remaining; dsimp only at remaining
      cases result with
      | none =>
        intro hflow
        have mclock : middle.clock ≤ state.clock := remaining
        have hm := evaluate_wordLocal x first children.1 state hx (by rw [firstRun]; exact Or.inl rfl)
        rw [firstRun] at hm
        exact evaluate_wordLocal x second children.2 middle hm hflow
      | some _ =>
        intro hflow
        have hm := evaluate_wordLocal x first children.1 state hx (by rw [firstRun]; exact hflow)
        rw [firstRun] at hm; exact hm
  | ite _ yes no =>
    have children : wsafe yes = true ∧ wsafe no = true := by
      simpa only [shape, wsafe, Bool.and_eq_true] using supported
    subst shape; revert hflow; rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_wordLocal x no children.2 state hx
      · exact evaluate_wordLocal x yes children.1 state hx
    · simp [Flowing]
  | «while» condition body =>
    have child : wsafe body = true := by simpa only [shape, wsafe] using supported
    subst shape; revert hflow; rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp [Flowing]
        · dsimp only; rw [fixClockHOLFinite_evaluateState]
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at remaining; dsimp only at remaining
            have small : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining; omega
            have hmid (hf : Flowing result) : ∃ w, middle.locals.lookup x = some (.val (.word w)) := by
              have := evaluate_wordLocal x body child (decClockHOLFinite state) hx (by rw [bodyRun]; exact hf)
              rw [bodyRun] at this; exact this
            cases result with
            | none =>
              intro hflow
              exact evaluate_wordLocal x (.while condition body) (by simpa [wsafe] using child) middle (hmid (Or.inl rfl)) hflow
            | some result =>
              cases result with
              | «continue» =>
                intro hflow
                exact evaluate_wordLocal x (.while condition body) (by simpa [wsafe] using child) middle (hmid (Or.inr (Or.inr rfl))) hflow
              | «break» => intro _; exact hmid (Or.inr (Or.inl rfl))
              | _ => simp [Flowing]
      · intro _; exact hx
    · simp [Flowing]
  | decCall name _ _ _ continuation =>
    have child : wsafe continuation = true := by simpa only [shape, wsafe] using supported
    subst shape; revert hflow; rw [evaluateHOLFiniteState_decCall_total]
    split
    · simp [Flowing]
    · split
      · simp [Flowing]
      · rename_i body callee _ _
        split
        · simp [Flowing]
        · dsimp only
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at cl ⊢
          obtain ⟨r, st⟩ := out
          dsimp only at cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try simp [Flowing])
          split
          · intro hflow
            have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            obtain ⟨w, hw⟩ := hx
            by_cases hxn : x = name
            · subst hxn; exact ⟨w, by dsimp only; rw [resVarEq_lookup_local, if_pos rfl]; exact hw⟩
            · obtain ⟨w', hw'⟩ := evaluate_wordLocal x continuation child _
                ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn, hw]⟩ hflow
              exact ⟨w', by dsimp only; rw [resVarEq_lookup_local, if_neg hxn]; exact hw'⟩
          · intro h; rcases h with h | h | h <;> simp at h
  | call info _ _ =>
    subst shape; revert hflow; rw [evaluateHOLFiniteState_call]
    split
    · simp [Flowing]
    · split
      · simp [Flowing]
      · rename_i body callee _ _
        split
        · simp [Flowing]
        · have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at cl ⊢
          obtain ⟨r, st⟩ := out
          dsimp only at cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have small : st.clock < state.clock := by omega
          obtain ⟨w, hw⟩ := hx
          have hnf : ∀ (o : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
              o ≠ none → o ≠ some .break → o ≠ some .continue → Flowing (o, t).1 →
              ∃ w', (o, t).2.locals.lookup x = some (.val (.word w')) := by
            intro o _ h1 h2 h3 hf; rcases hf with hf | hf | hf <;> [exact absurd hf h1; exact absurd hf h2; exact absurd hf h3]
          cases r with
          | none => exact hnf _ _ (by simp) (by simp) (by simp)
          | some r =>
            cases r with
            | returned v =>
              dsimp only; split
              · rcases info with _ | ⟨_ | ⟨kind, nm⟩, _⟩
                · exact hnf _ _ (by simp) (by simp) (by simp)
                · intro _; exact ⟨w, hw⟩
                · dsimp only; split
                  · rename_i hvalid; intro _
                    cases kind with
                    | global => exact ⟨w, by simpa [setKvarHOLFinite, setGlobalHOLFinite] using hw⟩
                    | «local» =>
                      by_cases hxn : x = nm
                      · subst hxn
                        have hsh : shapeEqHOL (shapeOfHOLExact v) .one = true := by
                          simpa [isValidValueHOLExact, lookupKvarHOLExact, toExact, hw, shapeOfHOLExact] using hvalid
                        rcases v with ⟨⟨w'⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh)
                        exact ⟨w', by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
                      · exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn, hw]⟩
                  · exact hnf _ _ (by simp) (by simp) (by simp)
              · exact hnf _ _ (by simp) (by simp) (by simp)
            | exception _ v =>
              dsimp only
              rcases info with _ | ⟨dest, _ | ⟨_, hv, hp⟩⟩
              · exact hnf _ _ (by simp) (by simp) (by simp)
              · exact hnf _ _ (by simp) (by simp) (by simp)
              · have hhp : wsafe hp = true := by rcases dest with _ | ⟨_, _⟩ <;> simpa [wsafe] using supported
                dsimp only; split
                · split
                  · split
                    · rename_i hc; intro hflow
                      simp only [Bool.and_eq_true] at hc
                      refine evaluate_wordLocal x hp hhp _ ?_ hflow
                      by_cases hxn : x = hv
                      · subst hxn
                        have hsh : shapeEqHOL (shapeOfHOLExact v) .one = true := by
                          simpa [isValidValueHOLExact, lookupKvarHOLExact, toExact, hw, shapeOfHOLExact] using hc.2
                        rcases v with ⟨⟨w'⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh)
                        exact ⟨w', by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
                      · exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn, hw]⟩
                    · exact hnf _ _ (by simp) (by simp) (by simp)
                  · exact hnf _ _ (by simp) (by simp) (by simp)
                · exact hnf _ _ (by simp) (by simp) (by simp)
            | _ => exact hnf _ _ (by simp) (by simp) (by simp)
  | shMemLoad op kind name addr =>
    cases kind with
    | global => simp [shape, wsafe] at supported
    | «local» =>
      subst shape
      rcases h : evaluateHOLFiniteState state (.shMemLoad op .local name addr) with ⟨r, post⟩
      simp only [h] at hflow ⊢
      cases r with
      | none =>
        obtain ⟨val, hpost⟩ := shMemLoad_local_none_inv state op name addr h
        rw [hpost]
        obtain ⟨w, hw⟩ := hx
        by_cases hxn : x = name
        · subst hxn; exact ⟨val, by simp [HolFiniteMapExact.lookup_update, FUPDATE]⟩
        · exact ⟨w, by simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn, hw]⟩
      | some r1 =>
        exfalso
        have hr1 : r1 = .break ∨ r1 = .continue := by
          rcases hflow with h0 | h0 | h0
          · cases h0
          · injection h0 with h0'; exact Or.inl h0'
          · injection h0 with h0'; exact Or.inr h0'
        classical
        rw [evaluateHOLFiniteState_shMemLoad_source] at h
        revert h; split
        · split
          · unfold shMemLoadHOLFiniteExact; dsimp only
            split <;> split <;> (try split) <;>
              (intro h; rcases hr1 with rfl | rfl <;> simp at h)
          · intro h; rcases hr1 with rfl | rfl <;> simp at h
        · intro h; rcases hr1 with rfl | rfl <;> simp at h
  | _ => simp [shape, wsafe] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | (simp only [callEntryStateHOLFinite] at small; exact Or.inl small)
      | omega
      | (by_cases hc : state.clock = 0
         · right; refine ⟨by omega, ?_⟩; simp +arith
         · left; omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · right; refine ⟨h, ?_⟩; simp +arith)
      | (right; refine ⟨rfl, ?_⟩; simp +arith)

def WordLocals {F : Type} (names : List String) (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ n ∈ names, ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))

theorem wordLocals_flowing {F : Type} {names : List String} {p : ProgHOL 64}
    (hws : wsafe p = true) {s : PanSemStateFiniteExact 64 F}
    (hw : WordLocals names s)
    (hf : Flowing (evaluateHOLFiniteState s p).1) :
    WordLocals names (evaluateHOLFiniteState s p).2 :=
  fun n hn => evaluate_wordLocal (ofString n) p hws s (hw n hn) hf

theorem worldEff_decCall_scratch_mark {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (name : MlS) {cont : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.decCall name .one (ofString "scratch_mark") [] cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.decCall name .one (ofString "scratch_mark") [] cont)).1)
    (hcont : ∀ (sp : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      cur.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) →
      sp.toNat = globN cur "scratch_ptr" →
      sp.toNat % 8 = 0 →
      globN s "frame_mem_ptr" ≤ sp.toNat →
      sp.toNat ≤ globN s "scratch_ptr" →
      mid = { cur with locals := cur.locals.update (name, .val (.word sp)), clock := cur.clock - 1 } →
      WorldEff s mid Rl B gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B gw) :
    WorldEff s (evaluateHOLFiniteState cur (.decCall name .one (ofString "scratch_mark") [] cont)).2 Rl B gw := by
  have hlook_sm : originalRuntimeCode.lookup (ofString "scratch_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_scratch_mark, .one) :=
    lookup_of_guestAst_getElem 14 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_scratch_mark) rfl
  have hl_sm : lookupCodeHOLFinite cur.code.lookup (ofString "scratch_mark") [] =
      some (sourceFnBody Guest.Software.guestFn_scratch_mark, HolFiniteMapExact.empty, .one) := by
    rw [h.code]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "scratch_mark") [] =
        some (sourceFnBody Guest.Software.guestFn_scratch_mark, FEMPTY, .one) := by
      simp only [lookupCodeHOLExact, hlook_sm, List.length_nil, List.zip_nil_left, List.all_nil]
      rfl
    split
    · rename_i hnone; rw [hraw] at hnone; cases hnone
    · rename_i b' l' r' hsome
      have heq := Option.some.inj (hsome.symm.trans hraw)
      obtain ⟨rfl, hrest⟩ := Prod.mk.inj heq
      obtain ⟨hl_eq, rfl⟩ := Prod.mk.inj hrest
      refine congrArg some (Prod.ext rfl (Prod.ext ?_ rfl))
      apply HolFiniteMapExact.ext; funext k
      simp [HolFiniteMapExact.empty, hl_eq]; rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hcr ⊢
  have hargs_sm : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [] = some [] := rfl
  simp only [hargs_sm, hl_sm] at hnt hcr ⊢
  by_cases hz : cur.clock = 0
  · rw [if_pos hz] at hnt; exact absurd rfl hnt
  · rw [if_neg hz] at hnt hcr ⊢
    obtain ⟨sp, hsp_lk⟩ : ∃ sp : BitVec 64, cur.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) :=
      globalWord_of_globN_pos cur "scratch_ptr"
        (by have := h.arena.2.2.2.1; have := h.arena.2.2.2.2.1; rw [scratchStart_val] at *; omega)
    have hsm_run : evaluateHOLFiniteState (callEntryStateHOLFinite cur HolFiniteMapExact.empty)
        (sourceFnBody Guest.Software.guestFn_scratch_mark) =
        (some (.returned (.val (.word sp))), emptyLocalsHOLFinite (callEntryStateHOLFinite cur HolFiniteMapExact.empty)) := by
      have hbsm : sourceFnBody Guest.Software.guestFn_scratch_mark = .return (.var .global (ofString "scratch_ptr")) := rfl
      rw [hbsm, evaluateHOLFiniteState_return]
      have hg_sp : (callEntryStateHOLFinite cur HolFiniteMapExact.empty).globals.lookup (ofString "scratch_ptr") =
          some (.val (.word sp)) := hsp_lk
      simp [evalHOLExact, hg_sp, shapeOfHOLExact]
    simp only [hsm_run] at hnt hcr ⊢
    have hsh_sp : (shapeEqHOL (shapeOfHOLExact (.val (.word sp) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word sp) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hsh_sp, ↓reduceIte] at hnt hcr ⊢
    let mid := setVarHOLFinite name (.val (.word sp))
      { (emptyLocalsHOLFinite (callEntryStateHOLFinite cur HolFiniteMapExact.empty)) with locals := cur.locals }
    have hmid_eq : mid = { cur with locals := cur.locals.update (name, .val (.word sp)), clock := cur.clock - 1 } := rfl
    have hsp_glob : sp.toNat = globN cur "scratch_ptr" := by simp [globN, hsp_lk]
    have hsp_al : sp.toNat % 8 = 0 := by rw [hsp_glob]; exact h.arena.2.2.2.2.2.2.2.2.1
    have hsp_lo : globN s "frame_mem_ptr" ≤ sp.toNat := by
      rw [hsp_glob, ← h.fmp_eq]; exact h.arena.2.2.2.2.1
    have hsp_hi : sp.toNat ≤ globN s "scratch_ptr" := by rw [hsp_glob]; exact h.sp_hi
    have heff_mid : WorldEff s mid Rl B gw := by rw [hmid_eq]; exact h.locals_clock _ _
    exact (hcont sp mid hsp_lk hsp_glob hsp_al hsp_lo hsp_hi hmid_eq heff_mid hnt hcr).locals_clock _ _

theorem worldEff_call0_scratch_release {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (hAs : ArenaOK s)
    (h : WorldEff s cur Rl B gw)
    (hgw_sp : ofString "scratch_ptr" ∈ gw.map ofString)
    (mExp : ExpHOL 64) (mw : BitVec 64)
    (hm : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hm_lo : globN s "frame_mem_ptr" ≤ mw.toNat)
    (hm_hi : mw.toNat ≤ globN s "scratch_ptr")
    (hm_al : mw.toNat % 8 = 0)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "scratch_release") [mExp])).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "scratch_release") [mExp])).1 = none ∧
    ∃ ck, (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "scratch_release") [mExp])).2 =
      { cur with globals := cur.globals.update (ofString "scratch_ptr", .val (.word mw)), clock := ck } ∧
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "scratch_release") [mExp])).2 Rl B gw := by
  by_cases hz : cur.clock = 0
  · exfalso; rw [evaluateHOLFiniteState_call] at hnt
    have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [mExp] =
        some [.val (.word mw)] := by simp [evalListHOLFinite, evalListHOLExact, hm]
    have hlook_sr : originalRuntimeCode.lookup (ofString "scratch_release") =
        some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_scratch_release, .one) :=
      lookup_of_guestAst_getElem 15 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_scratch_release) rfl
    have hl := pan_one_word_lookup cur.code.lookup (ofString "scratch_release") (ofString "m")
      (sourceFnBody Guest.Software.guestFn_scratch_release) mw (by rw [h.code]; exact hlook_sr)
    rw [hargs] at hnt; dsimp only at hnt; rw [hl] at hnt; dsimp only at hnt; rw [if_pos hz] at hnt
    exact hnt rfl
  · obtain ⟨spw, hsp⟩ : ∃ spw : BitVec 64, cur.globals.lookup (ofString "scratch_ptr") = some (.val (.word spw)) :=
      globalWord_of_globN_pos cur "scratch_ptr"
        (by have := h.arena.2.2.2.1; have := h.arena.2.2.2.2.1; rw [scratchStart_val] at *; omega)
    have heval : evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "scratch_release") [mExp]) =
        (none, { cur with globals := cur.globals.update (ofString "scratch_ptr", .val (.word mw)), clock := cur.clock - 1 }) := by
      rw [evaluateHOLFiniteState_call]
      have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [mExp] =
          some [.val (.word mw)] := by simp [evalListHOLFinite, evalListHOLExact, hm]
      have hlook_sr : originalRuntimeCode.lookup (ofString "scratch_release") =
          some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_scratch_release, .one) :=
        lookup_of_guestAst_getElem 15 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_scratch_release) rfl
      have hl := pan_one_word_lookup cur.code.lookup (ofString "scratch_release") (ofString "m")
        (sourceFnBody Guest.Software.guestFn_scratch_release) mw (by rw [h.code]; exact hlook_sr)
      rw [hargs]; dsimp only; rw [hl]; dsimp only; rw [if_neg hz]
      let entry := callEntryStateHOLFinite cur (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw)))
      have hb : sourceFnBody Guest.Software.guestFn_scratch_release =
          .seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := rfl
      have hev_b : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_scratch_release) =
          (some (.returned (.val (.word 0))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mw)) entry)) := by
        rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        have hm_ent : entry.locals.lookup (ofString "m") = some (.val (.word mw)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hsp_ent : entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word spw)) := hsp
        simp [evalHOLExact, hm_ent, isValidValueHOLFinite, lookupKvarHOLFinite,
          hsp_ent, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return]
      have hev_b' : evaluateHOLFiniteState
          (callEntryStateHOLFinite cur (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw))))
          (sourceFnBody Guest.Software.guestFn_scratch_release) =
          (some (.returned (.val (.word 0))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mw)) entry)) := hev_b
      rw [hev_b']; dsimp only
      have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh]; rfl
    rw [heval]; dsimp only
    refine ⟨rfl, cur.clock - 1, rfl, ?_⟩
    exact (worldEff_scratch_release_step hAs h hgw_sp hm_lo hm_hi hm_al rfl).1

theorem worldEff_handledCall {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (dest : Option (VarKind × MlS)) (eid evar : MlS) (handler : ProgHOL 64)
    (fname : MlS) (args : List (ExpHOL 64))
    (hdest_local : ∀ k nm, dest = some (k, nm) → k = .local)
    (hntrap : eid ≠ ofString "TrapErr")
    (params : List (MlS × ShapeHOL)) (fbody : ProgHOL 64) (retSh : ShapeHOL)
    (hlook : originalRuntimeCode.lookup fname = some (params, fbody, retSh))
    (hcallee : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64)),
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      lookupCodeHOLFinite cur.code.lookup fname vals = some (fbody, callee, retSh) →
      let entry := callEntryStateHOLFinite cur callee
      (evaluateHOLFiniteState entry fbody).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState entry fbody).1 →
      WorldEff s (evaluateHOLFiniteState entry fbody).2 Rl B gw)
    (hhand : ∀ (exVal : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F),
      WorldEff s cpost Rl B gw →
      let hst := setVarHOLFinite evar exVal { cpost with locals := cur.locals }
      (evaluateHOLFiniteState hst handler).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState hst handler).1 →
      WorldEff s (evaluateHOLFiniteState hst handler).2 Rl B gw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (dest, some (eid, evar, handler))) fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (dest, some (eid, evar, handler))) fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (dest, some (eid, evar, handler))) fname args)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_call] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · exact h
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact h
    · simp only [hl] at hnt hcr ⊢
      have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup fname params fbody body'
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hsame
      have hret_eq := lookupCodeHOLFinite_installed_return cur fname params fbody fbody
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hret_eq
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt hcr ⊢
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody with ⟨res, cpost⟩
        simp only [hrun] at hnt hcr ⊢
        cases res with
        | none => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | timeOut => exact absurd rfl hnt
          | «break» | «continue» | error | finalFfi _ =>
            rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | returned rv =>
            dsimp only at hnt hcr ⊢
            split
            · have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
                (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
              rw [hrun] at heff_c
              cases dest with
              | none => exact heff_c.locals_clock _ _
              | some d =>
                rcases d with ⟨kind, nm⟩
                have hk := hdest_local kind nm rfl; subst hk
                dsimp only at hcr ⊢
                split
                · exact heff_c.locals_clock _ _
                · rename_i hbad; rw [if_neg hbad] at hcr
                  rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
            · rename_i hbad; rw [if_neg hbad] at hcr
              rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | exception exId exVal =>
            dsimp only at hnt hcr ⊢
            by_cases heq : exId = eid
            · subst exId; rw [if_pos rfl] at hnt hcr ⊢
              rcases hes : cur.eshapes.lookup eid with _ | declSh
              · simp [hes] at hcr
                rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
              · simp only [hes] at hnt hcr ⊢
                by_cases hsh : (shapeEqHOL (shapeOfHOLExact exVal) declSh &&
                    isValidValueHOLExact cur.toExact .local evar exVal) = true
                · simp only [hsh, ↓reduceIte] at hnt hcr ⊢
                  have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
                    (by rw [hrun]; exact Or.inr ⟨eid, exVal, rfl, hntrap⟩)
                  rw [hrun] at heff_c
                  exact (hhand exVal cpost heff_c hnt hcr).locals_clock _ _
                · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hcr
                  rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
            · rw [if_neg heq] at hnt hcr ⊢
              have hres_e : Resumes (some (.exception exId exVal)) := by
                rcases hcr with hc0 | hc0 | hc0 | hr <;> [simp at hc0; simp at hc0; simp at hc0; exact hr]
              have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
                (by rw [hrun]; exact hres_e)
              rw [hrun] at heff_c
              exact heff_c.locals_clock _ _

theorem worldEff_call0_eff {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (fname : MlS) (args : List (ExpHOL 64))
    (params : List (MlS × ShapeHOL)) (fbody : ProgHOL 64) (retSh : ShapeHOL)
    (hlook : originalRuntimeCode.lookup fname = some (params, fbody, retSh))
    (hcallee : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64)),
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      lookupCodeHOLFinite cur.code.lookup fname vals = some (fbody, callee, retSh) →
      let entry := callEntryStateHOLFinite cur callee
      (evaluateHOLFiniteState entry fbody).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState entry fbody).1 →
      WorldEff s (evaluateHOLFiniteState entry fbody).2 Rl B gw)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_call] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · exact h
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact h
    · simp only [hl] at hnt hcr ⊢
      have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup fname params fbody body'
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hsame
      have hret_eq := lookupCodeHOLFinite_installed_return cur fname params fbody fbody
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hret_eq
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt hcr ⊢
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody with ⟨res, cpost⟩
        simp only [hrun] at hnt hcr ⊢
        cases res with
        | none => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | timeOut => exact absurd rfl hnt
          | «break» | «continue» | error | finalFfi _ =>
            rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | returned rv =>
            dsimp only at hcr ⊢
            split
            · have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
                (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
              rw [hrun] at heff_c
              exact heff_c.locals_clock _ _
            · rename_i hbad; rw [if_neg hbad] at hcr
              rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | exception exId exVal =>
            have hres_e : Resumes (some (.exception exId exVal)) := by
              rcases hcr with hc0 | hc0 | hc0 | hr <;> [simp at hc0; simp at hc0; simp at hc0; exact hr]
            have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
              (by rw [hrun]; exact hres_e)
            rw [hrun] at heff_c
            exact heff_c.locals_clock _ _

theorem worldEff_tailCall_eff {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (fname : MlS) (args : List (ExpHOL 64))
    (params : List (MlS × ShapeHOL)) (fbody : ProgHOL 64) (retSh : ShapeHOL)
    (hlook : originalRuntimeCode.lookup fname = some (params, fbody, retSh))
    (hcallee : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64)),
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      lookupCodeHOLFinite cur.code.lookup fname vals = some (fbody, callee, retSh) →
      let entry := callEntryStateHOLFinite cur callee
      (evaluateHOLFiniteState entry fbody).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState entry fbody).1 →
      WorldEff s (evaluateHOLFiniteState entry fbody).2 Rl B gw)
    (hnt : (evaluateHOLFiniteState cur (.call none fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call none fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call none fname args)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_call] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · exact h
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact h
    · simp only [hl] at hnt hcr ⊢
      have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup fname params fbody body'
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hsame
      have hret_eq := lookupCodeHOLFinite_installed_return cur fname params fbody fbody
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hret_eq
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt hcr ⊢
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody with ⟨res, cpost⟩
        simp only [hrun] at hnt hcr ⊢
        cases res with
        | none => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | timeOut => exact absurd rfl hnt
          | «break» | «continue» | error | finalFfi _ =>
            rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | returned rv =>
            dsimp only at hcr ⊢
            split
            · have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
                (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
              rw [hrun] at heff_c
              exact heff_c.locals_clock _ _
            · rename_i hbad; rw [if_neg hbad] at hcr
              rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | exception exId exVal =>
            have hres_e : Resumes (some (.exception exId exVal)) := by
              rcases hcr with hc0 | hc0 | hc0 | hr <;> [simp at hc0; simp at hc0; simp at hc0; exact hr]
            have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
              (by rw [hrun]; exact hres_e)
            rw [hrun] at heff_c
            exact heff_c.locals_clock _ _

theorem worldEff_decCall_eff {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (name : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (params : List (MlS × ShapeHOL)) (fbody : ProgHOL 64) (retSh : ShapeHOL)
    (hlook : originalRuntimeCode.lookup fname = some (params, fbody, retSh))
    (hcallee : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64)),
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      lookupCodeHOLFinite cur.code.lookup fname vals = some (fbody, callee, retSh) →
      let entry := callEntryStateHOLFinite cur callee
      (evaluateHOLFiniteState entry fbody).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState entry fbody).1 →
      WorldEff s (evaluateHOLFiniteState entry fbody).2 Rl B gw)
    (hcont : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64))
        (rv : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F),
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      lookupCodeHOLFinite cur.code.lookup fname vals = some (fbody, callee, retSh) →
      evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody = (some (.returned rv), cpost) →
      shapeEqHOL (shapeOfHOLExact rv) sh = true →
      WorldEff s cpost Rl B gw →
      let mid := setVarHOLFinite name rv { cpost with locals := cur.locals }
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B gw)
    (hnt : (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hcr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · exact h
  · simp only [hargs] at hnt hcr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact h
    · simp only [hl] at hnt hcr ⊢
      have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup fname params fbody body'
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hsame
      have hret_eq := lookupCodeHOLFinite_installed_return cur fname params fbody fbody
        retSh ret' vals callee (by rw [h.code]; exact hlook) hl
      cases hret_eq
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt hcr ⊢
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody with ⟨res, cpost⟩
        simp only [hrun] at hnt hcr ⊢
        cases res with
        | none => rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | timeOut => exact absurd rfl hnt
          | «break» | «continue» | error | finalFfi _ =>
            rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | returned rv =>
            dsimp only at hnt hcr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) retSh) = true
            · simp only [hsh, ↓reduceIte] at hnt hcr ⊢
              have hsh1 : shapeEqHOL (shapeOfHOLExact rv) sh = true := (Bool.and_eq_true _ _ ▸ hsh).1
              have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
                (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
              rw [hrun] at heff_c
              exact (hcont callee vals rv cpost hargs hl hrun hsh1 heff_c hnt hcr).locals_clock _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hcr
              rcases hcr with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | exception exId exVal =>
            have hres_e : Resumes (some (.exception exId exVal)) := by
              rcases hcr with hc0 | hc0 | hc0 | hr <;> [simp at hc0; simp at hc0; simp at hc0; exact hr]
            have heff_c := hcallee callee vals hargs hl (by rw [hrun]; simp)
              (by rw [hrun]; exact hres_e)
            rw [hrun] at heff_c
            exact heff_c.locals_clock _ _

end InitECandidate.Solver.Wave8GuestInv.R15Shards
