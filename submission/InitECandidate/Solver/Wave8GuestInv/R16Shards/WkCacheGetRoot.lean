import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_C08WkShard03
import InitECandidate.Solver.Wave8GuestInv.R13Shards.Common
import InitECandidate.Solver.GuestGlobalKeep
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.zv_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_memeq
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_has

/-!
# R16 Shard `WkCacheGetRoot`: `wk_cache_get_root`, `wk_ws_get_account_optional`, `wk_ws_storage_root_of`

Self-contained `WorldEff` combinator framework + 0-sorry proofs of:
1. `wk_ws_get_account_optional`
2. `wk_ws_storage_root_of`
3. `wk_cache_get_root`
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

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

/-! ## Section 6: Heap Mark/Release & RLP/Trie/Witness Account Callees for `wk_cache_get_root` -/

theorem worldEff_heap_release_step {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (hAs : ArenaOK s)
    (h : WorldEff s cur Rl B gw)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (hno_gb : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ gw.map ofString)
    {mw : BitVec 64}
    (hm_lo : globN s "heap_ptr" ≤ mw.toNat)
    (hm_hi : mw.toNat ≤ heapLimit)
    (hm_al : mw.toNat % 8 = 0)
    {next : PanSemStateFiniteExact 64 F}
    (hnext : next = { cur with
      globals := cur.globals.update (ofString "heap_ptr", .val (.word mw)),
      locals := next.locals, clock := next.clock }) :
    WorldEff s next Rl B gw ∧ globN next "heap_ptr" = mw.toNat := by
  rcases h.arena.2 with ⟨_, _, hc_fm_lo, hc_fm_hi, hc_sp_hi, _, hc_fm_al, hc_sp_al, hc_gw⟩
  have hn_globs : next.globals = cur.globals.update (ofString "heap_ptr", .val (.word mw)) := by
    rw [hnext]
  have hn_hp : globN next "heap_ptr" = mw.toNat := by
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
    globalsWord_update (ofString "heap_ptr") mw hn_globs hc_gw
  have hn_A : ArenaOK next := by
    unfold ArenaOK; rw [hn_hp, hn_fmp, hn_sp]
    exact ⟨le_trans hAs.1 hm_lo, hm_hi, hc_fm_lo, hc_fm_hi, hc_sp_hi,
      hm_al, hc_fm_al, hc_sp_al, hn_gw⟩
  have hn_kept : GlobalsKept gw s next := by
    intro k hk
    have hne : k ≠ ofString "heap_ptr" := fun heq => hk (heq ▸ hgw_hp)
    rw [h.gw_kept k hk, hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, Ne.symm hne]
  have hn_bufs : FreshBufsOK s next :=
    freshBufsOK_of_no_globalBuf_writes hn_kept hno_gb
  have hn_mem : next.memory = cur.memory := by rw [hnext]
  have hn_be : next.be = cur.be := by rw [hnext]
  refine ⟨⟨⟨hn_G, hn_A⟩, by rw [hnext]; exact h.code, by rw [hnext]; exact h.memaddrs,
    hn_be.trans h.be, by rw [hnext]; exact h.eshapes,
    by rw [hn_hp]; exact hm_lo, hn_fmp.trans h.fmp_eq,
    by rw [hn_sp]; exact h.sp_hi,
    hn_kept, hn_bufs,
    fun a hne => h.out_dom a (by rwa [hn_mem] at hne),
    fun a hne => h.cell_frame a (by rwa [hn_mem] at hne),
    fun b hb64 hne => h.byte_frame b hb64 (by unfold memB at hne ⊢; rwa [hn_mem, hn_be] at hne)⟩,
    hn_hp⟩

theorem worldEff_decCall_heap_mark {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (name : MlS) {cont : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.decCall name .one (ofString "heap_mark") [] cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.decCall name .one (ofString "heap_mark") [] cont)).1)
    (hcont : ∀ (hp : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      cur.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) →
      hp.toNat = globN cur "heap_ptr" →
      hp.toNat % 8 = 0 →
      globN s "heap_ptr" ≤ hp.toNat →
      hp.toNat ≤ heapLimit →
      mid = { cur with locals := cur.locals.update (name, .val (.word hp)), clock := cur.clock - 1 } →
      WorldEff s mid Rl B gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B gw) :
    WorldEff s (evaluateHOLFiniteState cur (.decCall name .one (ofString "heap_mark") [] cont)).2 Rl B gw := by
  have hl_hm : lookupCodeHOLFinite cur.code.lookup (ofString "heap_mark") [] =
      some (sourceFnBody Guest.Software.guestFn_heap_mark, HolFiniteMapExact.empty, .one) := by
    rw [h.code]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "heap_mark") [] =
        some (sourceFnBody Guest.Software.guestFn_heap_mark, FEMPTY, .one) := by
      simp only [lookupCodeHOLExact, lookup_heap_mark, List.length_nil, List.zip_nil_left, List.all_nil]
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
  have hargs_hm : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [] = some [] := rfl
  simp only [hargs_hm, hl_hm] at hnt hcr ⊢
  by_cases hz : cur.clock = 0
  · rw [if_pos hz] at hnt; exact absurd rfl hnt
  · rw [if_neg hz] at hnt hcr ⊢
    obtain ⟨hp, hhp_lk⟩ : ∃ hp : BitVec 64, cur.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) :=
      globalWord_of_globN_pos cur "heap_ptr"
        (by have := h.arena.2.1; rw [sourceBase_val] at this; omega)
    have hhm_run : evaluateHOLFiniteState (callEntryStateHOLFinite cur HolFiniteMapExact.empty)
        (sourceFnBody Guest.Software.guestFn_heap_mark) =
        (some (.returned (.val (.word hp))), emptyLocalsHOLFinite (callEntryStateHOLFinite cur HolFiniteMapExact.empty)) := by
      have hbhm : sourceFnBody Guest.Software.guestFn_heap_mark = .return (.var .global (ofString "heap_ptr")) := rfl
      rw [hbhm, evaluateHOLFiniteState_return]
      have hg_hp : (callEntryStateHOLFinite cur HolFiniteMapExact.empty).globals.lookup (ofString "heap_ptr") =
          some (.val (.word hp)) := hhp_lk
      simp [evalHOLExact, hg_hp, shapeOfHOLExact]
    simp only [hhm_run] at hnt hcr ⊢
    have hsh_hp : (shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hsh_hp, ↓reduceIte] at hnt hcr ⊢
    let mid := setVarHOLFinite name (.val (.word hp))
      { (emptyLocalsHOLFinite (callEntryStateHOLFinite cur HolFiniteMapExact.empty)) with locals := cur.locals }
    have hmid_eq : mid = { cur with locals := cur.locals.update (name, .val (.word hp)), clock := cur.clock - 1 } := rfl
    have hhp_glob : hp.toNat = globN cur "heap_ptr" := by simp [globN, hhp_lk]
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_glob]; exact h.arena.2.2.2.2.2.2.1
    have hhp_lo : globN s "heap_ptr" ≤ hp.toNat := by rw [hhp_glob]; exact h.hp_lo
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_glob]; exact h.arena.2.2.1
    have heff_mid : WorldEff s mid Rl B gw := by rw [hmid_eq]; exact h.locals_clock _ _
    exact (hcont hp mid hhp_lk hhp_glob hhp_al hhp_lo hhp_hi hmid_eq heff_mid hnt hcr).locals_clock _ _

theorem worldEff_call0_heap_release {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (hAs : ArenaOK s)
    (h : WorldEff s cur Rl B gw)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (hno_gb : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ gw.map ofString)
    (mExp : ExpHOL 64) (mw : BitVec 64)
    (hm : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hm_lo : globN s "heap_ptr" ≤ mw.toNat)
    (hm_hi : mw.toNat ≤ heapLimit)
    (hm_al : mw.toNat % 8 = 0)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "heap_release") [mExp])).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "heap_release") [mExp])).1 = none ∧
    ∃ ck, (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "heap_release") [mExp])).2 =
      { cur with globals := cur.globals.update (ofString "heap_ptr", .val (.word mw)), clock := ck } ∧
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "heap_release") [mExp])).2 Rl B gw := by
  by_cases hz : cur.clock = 0
  · exfalso; rw [evaluateHOLFiniteState_call] at hnt
    have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [mExp] =
        some [.val (.word mw)] := by simp [evalListHOLFinite, evalListHOLExact, hm]
    have hl := pan_one_word_lookup cur.code.lookup (ofString "heap_release") (ofString "m")
      (sourceFnBody Guest.Software.guestFn_heap_release) mw (by rw [h.code]; exact lookup_heap_release)
    rw [hargs] at hnt; dsimp only at hnt; rw [hl] at hnt; dsimp only at hnt; rw [if_pos hz] at hnt
    exact hnt rfl
  · obtain ⟨hpw, hhp⟩ : ∃ hpw : BitVec 64, cur.globals.lookup (ofString "heap_ptr") = some (.val (.word hpw)) :=
      globalWord_of_globN_pos cur "heap_ptr"
        (by have := h.arena.2.1; rw [sourceBase_val] at this; omega)
    have heval : evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "heap_release") [mExp]) =
        (none, { cur with globals := cur.globals.update (ofString "heap_ptr", .val (.word mw)), clock := cur.clock - 1 }) := by
      rw [evaluateHOLFiniteState_call]
      have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [mExp] =
          some [.val (.word mw)] := by simp [evalListHOLFinite, evalListHOLExact, hm]
      have hl := pan_one_word_lookup cur.code.lookup (ofString "heap_release") (ofString "m")
        (sourceFnBody Guest.Software.guestFn_heap_release) mw (by rw [h.code]; exact lookup_heap_release)
      rw [hargs]; dsimp only; rw [hl]; dsimp only; rw [if_neg hz]
      let entry := callEntryStateHOLFinite cur (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw)))
      have hb : sourceFnBody Guest.Software.guestFn_heap_release =
          .seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := rfl
      have hev_b : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_heap_release) =
          (some (.returned (.val (.word 0))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mw)) entry)) := by
        rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        have hm_ent : entry.locals.lookup (ofString "m") = some (.val (.word mw)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hhp_ent : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word hpw)) := hhp
        simp [evalHOLExact, hm_ent, isValidValueHOLFinite, lookupKvarHOLFinite,
          hhp_ent, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return]
      have hev_b' : evaluateHOLFiniteState
          (callEntryStateHOLFinite cur (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw))))
          (sourceFnBody Guest.Software.guestFn_heap_release) =
          (some (.returned (.val (.word 0))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mw)) entry)) := hev_b
      rw [hev_b']; dsimp only
      have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh]; rfl
    rw [heval]; dsimp only
    refine ⟨rfl, cur.clock - 1, rfl, ?_⟩
    exact (worldEff_heap_release_step hAs h hgw_hp hno_gb hm_lo hm_hi hm_al rfl).1

/-! ## Section 7: `ReadOnlyProg` for `trie_walk` and `WorldEff` for RLP Scratch Walkers -/

theorem ro_trie_walk : ReadOnlyFn (ofString "trie_walk") := by
  refine InitECandidate.Solver.Wave8GuestInv.R13.readOnlyFn_of_guestAst 266
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_trie_walk rfl ?_
  dsimp only [Guest.Software.guestFn_trie_walk, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, Option.map]
  have hmemeq : ReadOnlyFn (ofString "memeq") := InitECandidate.Solver.Wave8Contracts.M15.ro_memeq
  intro F
  open InitECandidate.Solver.Wave8GuestInv.R13 in
  exact ReadOnlyProg.dec _ _ _
    (ReadOnlyProg.seq
      (ReadOnlyProg.while_loop _
        (ReadOnlyProg.dec _ _ _
          (ReadOnlyProg.seq
            (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_mpt_fail _) ReadOnlyProg.skip)
            (ReadOnlyProg.seq
              (ReadOnlyProg.ite _
                (ReadOnlyProg.dec _ _ _
                  (ReadOnlyProg.seq
                    (ReadOnlyProg.ite _
                      (ReadOnlyProg.decCall hmemeq _ _ _
                        (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip))
                      ReadOnlyProg.skip)
                    (ReadOnlyProg.ret _)))
                ReadOnlyProg.skip)
              (ReadOnlyProg.ite _
                (ReadOnlyProg.dec _ _ _
                  (ReadOnlyProg.seq
                    (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                    (ReadOnlyProg.decCall hmemeq _ _ _
                      (ReadOnlyProg.seq
                        (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                        (ReadOnlyProg.seq
                          (ReadOnlyProg.assign_local _ _)
                          (ReadOnlyProg.assign_local _ _))))))
                (ReadOnlyProg.seq
                  (ReadOnlyProg.ite _
                    (ReadOnlyProg.dec _ _ _
                      (ReadOnlyProg.seq
                        (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
                        (ReadOnlyProg.ret _)))
                    ReadOnlyProg.skip)
                  (ReadOnlyProg.seq
                    (ReadOnlyProg.assign_local _ _)
                    (ReadOnlyProg.assign_local _ _))))))))
      (ReadOnlyProg.ret _))

/-! ## Section 8: `key_to_nibbles` `ByteEff` + `trie_lookup` `WorldEff` -/

private def KeyNibInv {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (key0 n0 out0 : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  ByteEff s0 s [(out0.toNat, 2 * n0.toNat)] ∧
  s.locals.lookup (ofString "key") = some (.val (.word key0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  s.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ out0.toNat ∧ out0.toNat + 2 * iw.toNat ≤ heapEnd)

private theorem noRetOrRaise_seq {F : Type} {a b : ProgHOL 64} {s : PanSemStateFiniteExact 64 F}
    (ha : ¬ Resumes (evaluateHOLFiniteState s a).1)
    (hb : ∀ m, (evaluateHOLFiniteState s a) = (none, m) → ¬ Resumes (evaluateHOLFiniteState m b).1) :
    ¬ Resumes (evaluateHOLFiniteState s (.seq a b)).1 := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s a with ⟨r1, m⟩
  rw [hr] at ha
  cases r1 with
  | none => exact hb m hr
  | some _ => exact ha

private theorem noRetOrRaise_storeByte {F : Type} (s : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) :
    ¬ Resumes (evaluateHOLFiniteState s (.storeByte d e)).1 := by
  rw [evaluateHOLFiniteState_storeByte]
  repeat' split
  all_goals (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

private theorem noRetOrRaise_assign {F : Type} (s : PanSemStateFiniteExact 64 F) (k : VarKind) (nm : MlS) (e : ExpHOL 64) :
    ¬ Resumes (evaluateHOLFiniteState s (.assign k nm e)).1 := by
  rw [evaluateHOLFiniteState_assign]
  repeat' split
  all_goals (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

private theorem noRetOrRaise_dec {F : Type} (s : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL) (e : ExpHOL 64)
    {b : ProgHOL 64} (hb : ∀ v, ¬ Resumes (evaluateHOLFiniteState (setVarHOLFinite nm v s) b).1) :
    ¬ Resumes (evaluateHOLFiniteState s (.dec nm sh e b)).1 := by
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  split
  · exact not_resumes_error
  · rename_i v _; split
    · exact hb v
    · exact not_resumes_error

private theorem noRetOrRaise_while {F : Type} (cond : ExpHOL 64) (body : ProgHOL 64)
    (hb : ∀ t : PanSemStateFiniteExact 64 F, ¬ Resumes (evaluateHOLFiniteState t body).1)
    (k : Nat) (s : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k) :
    ¬ Resumes (evaluateHOLFiniteState s (.while cond body)).1 := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total]
    repeat' split
    all_goals (try omega)
    all_goals (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · dsimp only; rw [fixClockHOLFinite_evaluateState]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hnb := hb (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at rem hnb
          have hlt : mid.clock ≤ k := by change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none => exact ih mid hlt
          | some res =>
            cases res with
            | «continue» => exact ih mid hlt
            | «break» => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | _ => exact hnb
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
    · exact not_resumes_error

private theorem while_keyNibInv {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {key0 n0 out0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnobc : ∀ t : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState t body).1 ≠ some .break ∧
      (evaluateHOLFiniteState t body).1 ≠ some .continue)
    (hstep : ∀ (s : PanSemStateFiniteExact 64 F) (cw : BitVec 64),
      KeyNibInv s0 key0 n0 out0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word cw)) → cw ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      KeyNibInv s0 key0 n0 out0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : KeyNibInv s0 key0 n0 out0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    KeyNibInv s0 key0 n0 out0 post ∧
    @evalHOLExact 64 F _ post.toExact (fun a => Classical.propDecidable (post.memaddrs a)) cond =
      some (.val (.word 0)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hbc := hnobc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem hbc
          cases r1 with
          | none =>
            have hmid : KeyNibInv s0 key0 n0 out0 mid := by
              have hb := hstep s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl hbc.2
            | «break» => exact absurd rfl hbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem dec_none_inv_ktn {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nm : MlS} {e : ExpHOL 64} {b : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.dec nm .one e b) = (none, post)) :
    ∃ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
        some (.val (.word w)) ∧
      (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) b).1 = none ∧
      post = { (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) b).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) b).2.locals
          (nm, s.locals.lookup nm) } := by
  rw [evaluateHOLFiniteState_dec_total] at h; dsimp only at h
  split at h
  · simp at h
  · rename_i v hv
    split at h
    · rename_i hsh
      rcases v with ⟨⟨w⟩⟩ | _ | _ <;> simp [shapeEqHOL, shapeOfHOLExact] at hsh
      refine ⟨w, hv, ?_, ?_⟩
      · injection h
      · injection h with _ hp; exact hp.symm
    · simp at h

private theorem seq_storeByte_none_inv_ktn {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {d e : ExpHOL 64} {b : ProgHOL 64}
    (hG : GuestInv s) (addr : BitVec 64)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) d =
      some (.val (.word addr)))
    (hin : sourceBase ≤ addr.toNat → addr.toNat + 1 ≤ heapEnd → ∃ iv ∈ Rl, InIvl addr.toNat iv)
    (h : evaluateHOLFiniteState s (.seq (.storeByte d e) b) = (none, post)) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      sourceBase ≤ addr.toNat ∧ addr.toNat + 1 ≤ heapEnd ∧
      ByteEff s mid Rl ∧ mid.locals = s.locals ∧ mid.code = s.code ∧ GuestInv mid ∧
      evaluateHOLFiniteState mid b = (none, post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  have hbs := byteEff_storeByte (Rl := Rl) hG d e (fun x hx hdom => by
    rw [hd] at hx; cases hx
    have hord : (panByteAlignHOL addr).toNat % 8 = 0 ∧
        sourceBase ≤ (panByteAlignHOL addr).toNat ∧ (panByteAlignHOL addr).toNat < heapEnd := by
      rwa [hG.memaddrs, ordinaryDomain_iff] at hdom
    have hhe8 : heapEnd % 8 = 0 := by decide
    have hsb8 : sourceBase % 8 = 0 := by decide
    have hal := panByteAlign_toNat64 addr
    exact hin (by omega) (by omega))
  rcases h1 : evaluateHOLFiniteState s (.storeByte d e) with ⟨r1, mid⟩
  rw [h1] at h hbs
  cases r1 with
  | some _ => simp at h
  | none =>
    obtain ⟨x, hx, hlo, hhi⟩ := hbs.2 rfl
    rw [hd] at hx; cases hx
    have hloc : mid.locals = s.locals := by
      rw [evaluateHOLFiniteState_storeByte] at h1
      revert h1; repeat' split
      all_goals (intro h1; injection h1 with _ hm; subst hm; rfl)
    exact ⟨mid, hlo, hhi, hbs.1, hloc, hbs.1.code,
      guestInv_congr hbs.1.code hbs.1.memaddrs hbs.1.shMemaddrs hbs.1.baseAddr hG, h⟩

private theorem one_byte_nibbles_step {F : Type} {s0 s post : PanSemStateFiniteExact 64 F}
    {key0 n0 out0 iw : BitVec 64} (bnm : MlS) (kOff : ExpHOL 64)
    (outOff0 outOff1 : ExpHOL 64) (d0 : Nat) {rest : ProgHOL 64}
    (hb_ne_out : bnm ≠ ofString "out") (hb_ne_i : bnm ≠ ofString "i")
    (hb_ne_key : bnm ≠ ofString "key") (hb_ne_n : bnm ≠ ofString "n")
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (heff : ByteEff s0 s [(out0.toNat, 2 * n0.toNat)])
    (hk : s.locals.lookup (ofString "key") = some (.val (.word key0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (ho0 : ∀ bw : BitVec 64,
      let sb := setVarHOLFinite bnm (.val (.word bw)) s
      @evalHOLExact 64 F _ sb.toExact (fun a => Classical.propDecidable (sb.memaddrs a)) outOff0 =
        some (.val (.word (out0 + 2#64 * iw + BitVec.ofNat 64 d0))))
    (ho1 : ∀ (bw : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      m.locals = (setVarHOLFinite bnm (.val (.word bw)) s).locals →
      @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a)) outOff1 =
        some (.val (.word (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)))))
    (hin0 : sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat →
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat + 1 ≤ heapEnd →
      InIvl (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat (out0.toNat, 2 * n0.toNat))
    (hin1 : sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat →
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat + 1 ≤ heapEnd →
      sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat →
      (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat + 1 ≤ heapEnd →
      InIvl (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat (out0.toNat, 2 * n0.toNat))
    (hrun : evaluateHOLFiniteState s
      (.dec bnm .one (.loadByte kOff)
        (.seq (.storeByte outOff0 (.shift .lsr (.var .local bnm) (.const 4)))
          (.seq (.storeByte outOff1 (.op .and [.var .local bnm, .const 15]))
            rest))) = (none, post)) :
    ∃ m2 : PanSemStateFiniteExact 64 F,
      sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat ∧
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat + 1 ≤ heapEnd ∧
      sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat ∧
      (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat + 1 ≤ heapEnd ∧
      m2.code = originalRuntimeCode ∧ GuestInv m2 ∧
      ByteEff s0 m2 [(out0.toNat, 2 * n0.toNat)] ∧
      m2.locals.lookup (ofString "key") = some (.val (.word key0)) ∧
      m2.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
      m2.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
      m2.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
      (evaluateHOLFiniteState m2 rest).1 = none ∧
      post = { (evaluateHOLFiniteState m2 rest).2 with
        locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState m2 rest).2.locals
          (bnm, s.locals.lookup bnm) } := by
  obtain ⟨bw, _, hrest1, hpost_eq⟩ := dec_none_inv_ktn hrun
  set sb := setVarHOLFinite bnm (.val (.word bw)) s
  have hG_sb : GuestInv sb := guestInv_setVar _ _ s hG
  have heff_sb : ByteEff s0 sb [(out0.toNat, 2 * n0.toNat)] := heff.locals_clock _ s.clock
  rcases h_eq : evaluateHOLFiniteState sb
      (.seq (.storeByte outOff0 (.shift .lsr (.var .local bnm) (.const 4)))
        (.seq (.storeByte outOff1 (.op .and [.var .local bnm, .const 15])) rest)) with ⟨r_end, p_end⟩
  have hr_none : r_end = none := by rw [h_eq] at hrest1; exact hrest1
  subst hr_none
  obtain ⟨m1, hlo0, hhi0, heff1, hloc1, hc1, hG1, hseq2⟩ :=
    seq_storeByte_none_inv_ktn (Rl := [(out0.toNat, 2 * n0.toNat)]) hG_sb
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0) (ho0 bw)
      (fun h1 h2 => ⟨_, List.mem_singleton.mpr rfl, hin0 h1 h2⟩) h_eq
  obtain ⟨m2, hlo1, hhi1, heff2, hloc2, hc2, hG2, hrest2⟩ :=
    seq_storeByte_none_inv_ktn (Rl := [(out0.toNat, 2 * n0.toNat)]) hG1
      (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)) (ho1 bw m1 hloc1)
      (fun h1 h2 => ⟨_, List.mem_singleton.mpr rfl, hin1 hlo0 hhi0 h1 h2⟩) hseq2
  have hloc_m2 : m2.locals = sb.locals := hloc2.trans hloc1
  refine ⟨m2, hlo0, hhi0, hlo1, hhi1, hc2.trans (hc1.trans hc), hG2,
    (heff_sb.trans heff1).trans heff2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk, hb_ne_key]
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, hb_ne_n]
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ho, hb_ne_out]
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi, hb_ne_i]
  · rw [hrest2]
  · rw [hpost_eq, h_eq, hrest2]

private theorem nib_addr_nowrap (out0 iw n0 : BitVec 64) (step : Nat)
    (hprev : 0 < iw.toNat → sourceBase ≤ out0.toNat ∧ out0.toNat + 2 * iw.toNat ≤ heapEnd)
    (hstep_cond : iw.toNat + step ≤ n0.toNat ∨ ¬ (n0 < iw + BitVec.ofNat 64 step))
    (hstep_le : step ≤ 4) (hstep_pos : 0 < step)
    (h0_lo : sourceBase ≤ (out0 + 2#64 * iw + 0#64).toNat)
    (h0_hi : (out0 + 2#64 * iw + 0#64).toNat + 1 ≤ heapEnd) :
    (2#64 * iw).toNat = 2 * iw.toNat ∧
    (out0 + 2#64 * iw).toNat = out0.toNat + 2 * iw.toNat ∧
    (iw + BitVec.ofNat 64 step).toNat = iw.toNat + step ∧
    iw.toNat + step ≤ n0.toNat ∧
    sourceBase ≤ out0.toNat ∧
    ∀ d : Nat, d < 2 * step →
      (out0 + 2#64 * iw + BitVec.ofNat 64 d).toNat = out0.toNat + 2 * iw.toNat + d ∧
      InIvl (out0 + 2#64 * iw + BitVec.ofNat 64 d).toNat (out0.toNat, 2 * n0.toNat) := by
  have hsb : sourceBase = 2701131776 := rfl
  have hhe : heapEnd = 33806089704 := by decide
  rw [BitVec.add_zero] at h0_lo h0_hi
  have holt := out0.isLt; have hilt := iw.isLt; have hnlt := n0.isLt
  by_cases hiz : iw.toNat = 0
  · have hi0 : iw = 0 := BitVec.eq_of_toNat_eq hiz
    subst hi0
    have hz : 2#64 * (0 : BitVec 64) = (0 : BitVec 64) := rfl
    have hao : out0 + (0 : BitVec 64) = out0 := BitVec.add_zero out0
    rw [hz, hao] at h0_lo h0_hi ⊢
    have h0_nat : (0 : BitVec 64).toNat = 0 := rfl
    have hstep_bv : ((0 : BitVec 64) + BitVec.ofNat 64 step).toNat = step := by
      rw [zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hle_n : step ≤ n0.toNat := by
      rcases hstep_cond with h | h
      · omega
      · rw [BitVec.lt_def, hstep_bv] at h; omega
    refine ⟨rfl, by simp [h0_nat], by omega, by omega, h0_lo, fun d hd => ?_⟩
    have hd_nat : (BitVec.ofNat 64 d).toNat = d := Nat.mod_eq_of_lt (by omega)
    have hadd_d : (out0 + BitVec.ofNat 64 d).toNat = out0.toNat + d := by
      rw [BitVec.toNat_add, hd_nat, Nat.mod_eq_of_lt (by omega)]
    rw [hadd_d, h0_nat]
    exact ⟨by omega, ⟨by omega, by omega⟩⟩
  · obtain ⟨hdlo, hdhi⟩ := hprev (by omega)
    have h2i : (2#64 * iw).toNat = 2 * iw.toNat := by
      rw [BitVec.toNat_mul]
      have h2_nat : (2#64).toNat = 2 := rfl
      rw [h2_nat, Nat.mod_eq_of_lt (by omega)]
    have ho2i : (out0 + 2#64 * iw).toNat = out0.toNat + 2 * iw.toNat := by
      rw [BitVec.toNat_add, h2i, Nat.mod_eq_of_lt (by omega)]
    have his : (iw + BitVec.ofNat 64 step).toNat = iw.toNat + step := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hle_n : iw.toNat + step ≤ n0.toNat := by
      rcases hstep_cond with h | h
      · exact h
      · rw [BitVec.lt_def, his] at h; omega
    refine ⟨h2i, ho2i, his, hle_n, hdlo, fun d hd => ?_⟩
    have hadd_d : (out0 + 2#64 * iw + BitVec.ofNat 64 d).toNat = out0.toNat + 2 * iw.toNat + d := by
      rw [BitVec.toNat_add, ho2i, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hadd_d]
    exact ⟨rfl, ⟨by omega, by omega⟩⟩

private theorem eval_out_2i {F : Type} (s : PanSemStateFiniteExact 64 F) (out0 iw : BitVec 64)
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")]]) =
      some (.val (.word (out0 + 2#64 * iw + 0#64))) := by
  simp [evalHOLExact, evalListHOLExact, ho, hi, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]

private theorem eval_out_2i_c {F : Type} (s : PanSemStateFiniteExact 64 F) (out0 iw : BitVec 64) (d : Nat)
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")], .const (BitVec.ofNat 64 d)]) =
      some (.val (.word (out0 + 2#64 * iw + BitVec.ofNat 64 d))) := by
  simp [evalHOLExact, evalListHOLExact, ho, hi, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp, BitVec.add_assoc]

private theorem lookup_resVarEq_ne_ktn (m : HolFiniteMapExact MlS (ValueHOL 64))
    (x k : MlS) (ox : Option (ValueHOL 64)) (hne : k ≠ x) :
    (m.resVarEq (x, ox)).lookup k = m.lookup k := by
  simp only [HolFiniteMapExact.resVarEq]
  cases ox <;> simp [FDOMSUB_HOL, FUPDATE_HOL, hne, Ne.symm hne]

theorem key_to_nibbles_body_eff {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (key0 n0 out0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hk0 : s0.locals.lookup (ofString "key") = some (.val (.word key0)))
    (hn0 : s0.locals.lookup (ofString "n") = some (.val (.word n0)))
    (ho0 : s0.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_key_to_nibbles)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_key_to_nibbles)).2
      [(out0.toNat, 2 * n0.toNat)] ∧
    (0 < n0.toNat → sourceBase ≤ out0.toNat ∧ out0.toNat + 2 * n0.toNat ≤ heapEnd) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_key_to_nibbles,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hres ⊢
  rw [evaluateHOLFiniteState_dec_total] at hres ⊢; dsimp only at hres ⊢
  have hev0 : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word (BitVec.ofNat 64 0))) := rfl
  rw [hev0] at hres ⊢; dsimp only at hres ⊢
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 0)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hres ⊢; dsimp only at hres ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 0))) s0
  have hinv1 : KeyNibInv s0 key0 n0 out0 s1 := by
    refine ⟨hc, guestInv_setVar _ _ s0 hG, (ByteEff.refl s0 _).locals_clock _ s0.clock, ?_, ?_, ?_, BitVec.ofNat 64 0, ?_, Nat.zero_le _, fun h => by simp at h⟩
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk0, show ofString "i" ≠ ofString "key" by decide]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn0, show ofString "i" ≠ ofString "n" by decide]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ho0, show ofString "i" ≠ ofString "out" by decide]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  set w4 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 4)])) _
  have hw4_nrr : ¬ Resumes (evaluateHOLFiniteState s1 w4).1 := by
    refine noRetOrRaise_while _ _ (fun t => ?_) s1.clock s1 le_rfl
    exact noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_assign _ _ _ _
  rcases hr4 : evaluateHOLFiniteState s1 w4 with ⟨r4, s2⟩
  cases r4 with
  | some _ => rw [hr4] at hres hw4_nrr; exact absurd hres hw4_nrr
  | none =>
    dsimp only at hres ⊢
    have hnbc_dec : ∀ {p : ProgHOL 64},
        (∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t p).1 ≠ some .break ∧ (evaluateHOLFiniteState t p).1 ≠ some .continue) →
        ∀ nm e (t : PanSemStateFiniteExact 64 F),
          (evaluateHOLFiniteState t (.dec nm .one e p)).1 ≠ some .break ∧
          (evaluateHOLFiniteState t (.dec nm .one e p)).1 ≠ some .continue := by
      intro p hp nm e t
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      split
      · simp
      · rename_i v _; split
        · exact hp (setVarHOLFinite nm v t)
        · simp
    have hnbc_seq_sb : ∀ {p : ProgHOL 64},
        (∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t p).1 ≠ some .break ∧ (evaluateHOLFiniteState t p).1 ≠ some .continue) →
        ∀ d e (t : PanSemStateFiniteExact 64 F),
          (evaluateHOLFiniteState t (.seq (.storeByte d e) p)).1 ≠ some .break ∧
          (evaluateHOLFiniteState t (.seq (.storeByte d e) p)).1 ≠ some .continue := by
      intro p hp d e t
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hs : evaluateHOLFiniteState t (.storeByte d e) with ⟨rs, ms⟩
      cases rs with
      | none => exact hp ms
      | some _ =>
        rw [evaluateHOLFiniteState_storeByte] at hs
        revert hs; repeat' split
        all_goals (intro hs; cases hs; try simp)
    have hnbc_asgn : ∀ nm e (t : PanSemStateFiniteExact 64 F),
        (evaluateHOLFiniteState t (.assign .local nm e)).1 ≠ some .break ∧
        (evaluateHOLFiniteState t (.assign .local nm e)).1 ≠ some .continue := by
      intro nm e t; rw [evaluateHOLFiniteState_assign]
      repeat' split
      all_goals simp
    have hinv2_pair := while_keyNibInv _ _
      (by
        intro t
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        exact hnbc_asgn _ _)
      (by
        intro st cw hinv hcond hnz hbody_none
        obtain ⟨hst_c, hst_G, hst_eff, hst_k, hst_n, hst_o, iw, hst_i, hiw_le, hprev⟩ := hinv
        have hnotlt : ¬ (n0 < iw + 4#64) := by
          simp only [evalHOLExact, evalListHOLExact, hst_n, hst_i, wordOpHOL, wordOp, valueIsWord, valueWord,
            List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, add_zero,
            Compiler.Encoders.Asm.wordCmpHOL] at hcond
          intro hlt
          have hnotle : ¬ (iw + 4#64 ≤ n0) := BitVec.not_le.mpr hlt
          simp [hnotle] at hcond
          exact hnz hcond.symm
        let st' := decClockHOLFinite st
        have hst'_c : st'.code = originalRuntimeCode := hst_c
        have hG' : GuestInv st' := guestInv_congr (s := st) rfl rfl rfl rfl hst_G
        have heff' : ByteEff s0 st' [(out0.toNat, 2 * n0.toNat)] := hst_eff.locals_clock _ _
        rcases hpst : evaluateHOLFiniteState st' _ with ⟨pst_r, pst⟩
        rw [hpst] at hbody_none; dsimp only at hbody_none; subst hbody_none
        obtain ⟨u1, h0lo, h0hi, h1lo, h1hi, hu1c, hu1G, hu1eff, hu1k, hu1n, hu1o, hu1i, hu1r, hpst1⟩ :=
          one_byte_nibbles_step (s := st') (ofString "b0") _ _ _ 0
            (by decide) (by decide) (by decide) (by decide)
            hst'_c hG' heff' hst_k hst_n hst_o hst_i
            (fun bw => eval_out_2i _ out0 iw
              (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b0" ≠ ofString "out" by decide])
              (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b0" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 1
              (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b0" ≠ ofString "out" by decide])
              (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b0" ≠ ofString "i" by decide]))
            (fun hlo hhi => (nib_addr_nowrap out0 iw n0 4 hprev (Or.inr hnotlt) (by omega) (by omega) hlo hhi).2.2.2.2.2 0 (by omega) |>.2)
            (fun hlo hhi _ _ => (nib_addr_nowrap out0 iw n0 4 hprev (Or.inr hnotlt) (by omega) (by omega) hlo hhi).2.2.2.2.2 1 (by omega) |>.2)
            hpst
        have hnw := nib_addr_nowrap out0 iw n0 4 hprev (Or.inr hnotlt) (by omega) (by omega) h0lo h0hi
        rcases h_u1 : evaluateHOLFiniteState u1 _ with ⟨r_u1, p_u1⟩
        rw [h_u1] at hu1r; dsimp only at hu1r; subst hu1r
        obtain ⟨u2, _, _, _, _, hu2c, hu2G, hu2eff, hu2k, hu2n, hu2o, hu2i, hu2r, hpst2⟩ :=
          one_byte_nibbles_step (ofString "b1") _ _ _ 2
            (by decide) (by decide) (by decide) (by decide)
            hu1c hu1G hu1eff hu1k hu1n hu1o hu1i
            (fun bw => eval_out_2i_c _ out0 iw 2
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1o, show ofString "b1" ≠ ofString "out" by decide])
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1i, show ofString "b1" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 3
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1o, show ofString "b1" ≠ ofString "out" by decide])
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1i, show ofString "b1" ≠ ofString "i" by decide]))
            (fun _ _ => (hnw.2.2.2.2.2 2 (by omega)).2)
            (fun _ _ _ _ => (hnw.2.2.2.2.2 3 (by omega)).2)
            h_u1
        rcases h_u2 : evaluateHOLFiniteState u2 _ with ⟨r_u2, p_u2⟩
        rw [h_u2] at hu2r; dsimp only at hu2r; subst hu2r
        obtain ⟨u3, _, _, _, _, hu3c, hu3G, hu3eff, hu3k, hu3n, hu3o, hu3i, hu3r, hpst3⟩ :=
          one_byte_nibbles_step (ofString "b2") _ _ _ 4
            (by decide) (by decide) (by decide) (by decide)
            hu2c hu2G hu2eff hu2k hu2n hu2o hu2i
            (fun bw => eval_out_2i_c _ out0 iw 4
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2o, show ofString "b2" ≠ ofString "out" by decide])
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2i, show ofString "b2" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 5
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2o, show ofString "b2" ≠ ofString "out" by decide])
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2i, show ofString "b2" ≠ ofString "i" by decide]))
            (fun _ _ => (hnw.2.2.2.2.2 4 (by omega)).2)
            (fun _ _ _ _ => (hnw.2.2.2.2.2 5 (by omega)).2)
            h_u2
        rcases h_u3 : evaluateHOLFiniteState u3 _ with ⟨r_u3, p_u3⟩
        rw [h_u3] at hu3r; dsimp only at hu3r; subst hu3r
        obtain ⟨u4, _, _, _, h7hi, hu4c, hu4G, hu4eff, hu4k, hu4n, hu4o, hu4i, hu4r, hpst4⟩ :=
          one_byte_nibbles_step (ofString "b3") _ _ _ 6
            (by decide) (by decide) (by decide) (by decide)
            hu3c hu3G hu3eff hu3k hu3n hu3o hu3i
            (fun bw => eval_out_2i_c _ out0 iw 6
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3o, show ofString "b3" ≠ ofString "out" by decide])
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3i, show ofString "b3" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 7
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3o, show ofString "b3" ≠ ofString "out" by decide])
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3i, show ofString "b3" ≠ ofString "i" by decide]))
            (fun _ _ => (hnw.2.2.2.2.2 6 (by omega)).2)
            (fun _ _ _ _ => (hnw.2.2.2.2.2 7 (by omega)).2)
            h_u3
        have hasgn : evaluateHOLFiniteState u4
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 4)])) =
            (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 4#64))) u4) := by
          simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hu4i, wordOpHOL, wordOp,
            valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
            shapeOfHOLExact, shapeEqHOL]
        have h7_eq := (hnw.2.2.2.2.2 7 (by omega)).1
        rw [h7_eq] at h7hi
        set L_new :=
          HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq
            (setVarHOLFinite (ofString "i") (.val (.word (iw + 4#64))) u4).locals
            (ofString "b3", u3.locals.lookup (ofString "b3")))
            (ofString "b2", u2.locals.lookup (ofString "b2")))
            (ofString "b1", u1.locals.lookup (ofString "b1")))
            (ofString "b0", st'.locals.lookup (ofString "b0"))
        have hpst_all : pst = { u4 with locals := L_new } := by
          rw [hpst1, h_u1, hpst2, h_u2, hpst3, h_u3, hpst4, hasgn]; rfl
        dsimp only
        rw [hpst_all]
        refine ⟨hu4c, guestInv_congr (s := u4) rfl rfl rfl rfl hu4G, hu4eff.locals_clock _ _, ?_, ?_, ?_,
          iw + 4#64, ?_, by rw [hnw.2.2.1]; exact hnw.2.2.2.1,
          fun _ => ⟨hnw.2.2.2.2.1, by rw [hnw.2.2.1]; omega⟩⟩
        · simp [L_new, lookup_resVarEq_ne_ktn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu4k,
            show ofString "key" ≠ ofString "b0" by decide, show ofString "key" ≠ ofString "b1" by decide,
            show ofString "key" ≠ ofString "b2" by decide, show ofString "key" ≠ ofString "b3" by decide,
            show ofString "i" ≠ ofString "key" by decide]
        · simp [L_new, lookup_resVarEq_ne_ktn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu4n,
            show ofString "n" ≠ ofString "b0" by decide, show ofString "n" ≠ ofString "b1" by decide,
            show ofString "n" ≠ ofString "b2" by decide, show ofString "n" ≠ ofString "b3" by decide,
            show ofString "i" ≠ ofString "n" by decide]
        · simp [L_new, lookup_resVarEq_ne_ktn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu4o,
            show ofString "out" ≠ ofString "b0" by decide, show ofString "out" ≠ ofString "b1" by decide,
            show ofString "out" ≠ ofString "b2" by decide, show ofString "out" ≠ ofString "b3" by decide,
            show ofString "i" ≠ ofString "out" by decide]
        · simp [L_new, lookup_resVarEq_ne_ktn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "b0" by decide, show ofString "i" ≠ ofString "b1" by decide,
            show ofString "i" ≠ ofString "b2" by decide, show ofString "i" ≠ ofString "b3" by decide])
      s1.clock s1 s2 le_rfl hinv1 hr4
    rw [hr4] at hres; dsimp only at hres
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    set w1 : ProgHOL 64 := .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) _
    have hw1_nrr : ¬ Resumes (evaluateHOLFiniteState s2 w1).1 := by
      refine noRetOrRaise_while _ _ (fun t => ?_) s2.clock s2 le_rfl
      exact noRetOrRaise_dec _ _ _ _ fun _ =>
        noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
        noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
        noRetOrRaise_assign _ _ _ _
    rcases hr1 : evaluateHOLFiniteState s2 w1 with ⟨r1, s3⟩
    cases r1 with
    | some _ => rw [hr1] at hres hw1_nrr; exact absurd hres hw1_nrr
    | none =>
      dsimp only at ⊢
      obtain ⟨hinv3, hcond3⟩ := while_keyNibInv _ _
        (by
          intro t
          apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
          exact hnbc_asgn _ _)
        (by
          intro st cw hinv hcond hnz hbody_none
          obtain ⟨hst_c, hst_G, hst_eff, hst_k, hst_n, hst_o, iw, hst_i, hiw_le, hprev⟩ := hinv
          have hlt : iw.toNat < n0.toNat := by
            simp [evalHOLExact, hst_n, hst_i, Compiler.Encoders.Asm.wordCmpHOL] at hcond
            by_contra hge; have hge' : ¬ (iw < n0) := by rw [BitVec.lt_def]; omega
            simp [hge'] at hcond; exact hnz hcond.symm
          let st' := decClockHOLFinite st
          have hst'_c : st'.code = originalRuntimeCode := hst_c
          have hG' : GuestInv st' := guestInv_congr (s := st) rfl rfl rfl rfl hst_G
          have heff' : ByteEff s0 st' [(out0.toNat, 2 * n0.toNat)] := hst_eff.locals_clock _ _
          rcases hpst : evaluateHOLFiniteState st' _ with ⟨pst_r, pst⟩
          rw [hpst] at hbody_none; dsimp only at hbody_none; subst hbody_none
          obtain ⟨u1, h0lo, h0hi, _, h1hi, hu1c, hu1G, hu1eff, hu1k, hu1n, hu1o, hu1i, hu1r, hpst1⟩ :=
            one_byte_nibbles_step (s := st') (ofString "b") _ _ _ 0
              (by decide) (by decide) (by decide) (by decide)
              hst'_c hG' heff' hst_k hst_n hst_o hst_i
              (fun bw => eval_out_2i _ out0 iw
                (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b" ≠ ofString "out" by decide])
                (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b" ≠ ofString "i" by decide]))
              (fun bw m hm => eval_out_2i_c _ out0 iw 1
                (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b" ≠ ofString "out" by decide])
                (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b" ≠ ofString "i" by decide]))
              (fun hlo hhi => (nib_addr_nowrap out0 iw n0 1 hprev (Or.inl (by omega)) (by omega) (by omega) hlo hhi).2.2.2.2.2 0 (by omega) |>.2)
              (fun hlo hhi _ _ => (nib_addr_nowrap out0 iw n0 1 hprev (Or.inl (by omega)) (by omega) (by omega) hlo hhi).2.2.2.2.2 1 (by omega) |>.2)
              hpst
          have hnw := nib_addr_nowrap out0 iw n0 1 hprev (Or.inl (by omega)) (by omega) (by omega) h0lo h0hi
          have hasgn : evaluateHOLFiniteState u1
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])) =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) u1) := by
            simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hu1i, wordOpHOL, wordOp,
              valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
              shapeOfHOLExact, shapeEqHOL]
          have h1_eq := (hnw.2.2.2.2.2 1 (by omega)).1
          rw [h1_eq] at h1hi
          dsimp only
          rw [hpst1, hasgn]
          refine ⟨hu1c, guestInv_congr (s := u1) rfl rfl rfl rfl hu1G, hu1eff.locals_clock _ _, ?_, ?_, ?_,
            iw + 1#64, ?_, by rw [hnw.2.2.1]; exact hnw.2.2.2.1,
            fun _ => ⟨hnw.2.2.2.2.1, by rw [hnw.2.2.1]; omega⟩⟩
          · simp [lookup_resVarEq_ne_ktn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1k,
              show ofString "key" ≠ ofString "b" by decide, show ofString "i" ≠ ofString "key" by decide]
          · simp [lookup_resVarEq_ne_ktn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1n,
              show ofString "n" ≠ ofString "b" by decide, show ofString "i" ≠ ofString "n" by decide]
          · simp [lookup_resVarEq_ne_ktn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1o,
              show ofString "out" ≠ ofString "b" by decide, show ofString "i" ≠ ofString "out" by decide]
          · simp [lookup_resVarEq_ne_ktn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "b" by decide])
        s2.clock s2 s3 le_rfl hinv2_pair.1 hr1
      obtain ⟨_, _, heff3, _, hst3_n, _, iw3, hst3_i, hiw3_le, hdom3⟩ := hinv3
      have hge3 : ¬ (iw3 < n0) := by
        intro hlt
        simp [evalHOLExact, hst3_n, hst3_i, Compiler.Encoders.Asm.wordCmpHOL, hlt] at hcond3
      rw [BitVec.lt_def] at hge3
      have hiw3_eq : iw3.toNat = n0.toNat := by omega
      have hret_run : (evaluateHOLFiniteState s3 (.return (.const (BitVec.ofNat 64 0)))).2 = emptyLocalsHOLFinite s3 := by
        rw [evaluateHOLFiniteState_return]
        simp [evalHOLExact, isValidValueHOLExact, shapeEqHOL, shapeOfHOLExact]
      rw [hret_run]
      refine ⟨heff3.locals_clock _ s3.clock, fun hpos => ?_⟩
      rw [← hiw3_eq] at hpos ⊢
      exact hdom3 hpos

theorem funByteEff_key_to_nibbles :
    FunByteEff (ofString "key_to_nibbles")
      (fun vals _ =>
        [(valWordNat (vals[2]?.getD (.rStruct [])),
          2 * valWordNat (vals[1]?.getD (.rStruct [])))]) := by
  have hlook : originalRuntimeCode.lookup (ofString "key_to_nibbles") =
      some ([(ofString "key", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_key_to_nibbles, .one) :=
    lookup_of_guestAst_getElem 248 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_key_to_nibbles) rfl
  refine ⟨_, _, _, hlook, fun {F} entry vals hc hG hl _hnt hres => ?_⟩
  obtain ⟨kw, nw, ow, rfl, hkw, hnw, how⟩ :=
    lookupCode_three_words (by decide) (by decide) (by decide) hlook hl
  exact (key_to_nibbles_body_eff entry kw nw ow hc hG hkw hnw how hres).1

/-! ## Section 9: `WorldEff` for RLP Scratch Walkers (`_rlp_validate_items_body`, `rlp_validate_items`, `rlp_item_total`, `rlp_list_count`, `rlp_item`, `rlp_decode_fully`, `rlp_list_to_slices`) -/

abbrev wsBufs : List (String × Nat) :=
  [("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)]

abbrev wsGw : List String := ["heap_ptr", "scratch_ptr"]

private theorem ws_no_gb : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ wsGw.map ofString := by
  decide

private theorem ws_B_sub : ∀ gs ∈ wsBufs, gs ∈ globalBuffers := by
  decide

private theorem lookup__rlp_validate_items_body :
    originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn__rlp_validate_items_body, .one) :=
  lookup_of_guestAst_getElem 110 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__rlp_validate_items_body) rfl

private theorem lookup_rlp_validate_items :
    originalRuntimeCode.lookup (ofString "rlp_validate_items") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_validate_items, .one) :=
  lookup_of_guestAst_getElem 111 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_validate_items) rfl

private theorem lookup_rlp_item_total :
    originalRuntimeCode.lookup (ofString "rlp_item_total") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item_total, .one) :=
  lookup_of_guestAst_getElem 112 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_total) rfl

private theorem lookup_rlp_list_count :
    originalRuntimeCode.lookup (ofString "rlp_list_count") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_list_count, .one) :=
  lookup_of_guestAst_getElem 113 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_count) rfl

private theorem lookup_rlp_item :
    originalRuntimeCode.lookup (ofString "rlp_item") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 107 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item) rfl

private theorem lookup_rlp_decode_fully :
    originalRuntimeCode.lookup (ofString "rlp_decode_fully") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_decode_fully, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 108 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_decode_fully) rfl

private theorem lookup_rlp_list_to_slices :
    originalRuntimeCode.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_list_to_slices, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 115 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_to_slices) rfl

private def vibPushProg : ProgHOL 64 :=
  .decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
    (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
      (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
        (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
          (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
            (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
              (.assign .local (ofString "end") (.var .local (ofString "after"))))))))

private theorem worldEff_vibPush {F : Type}
    {s t3 : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff_t3 : WorldEff s t3 [] wsBufs wsGw)
    (w_top w_end w_aft : BitVec 64)
    (ht3_aft : t3.locals.lookup (ofString "after") = some (.val (.word w_aft)))
    (ht3_end : t3.locals.lookup (ofString "end") = some (.val (.word w_end)))
    (ht3_top : t3.locals.lookup (ofString "top") = some (.val (.word w_top)))
    (hnt_push : (evaluateHOLFiniteState t3 vibPushProg).1 ≠ some .timeOut)
    (hcr_push : ContOrRes (evaluateHOLFiniteState t3 vibPushProg).1) :
    WorldEff s (evaluateHOLFiniteState t3 vibPushProg).2 [] wsBufs wsGw := by
  dsimp only [vibPushProg] at hnt_push hcr_push ⊢
  refine worldEff_decCall_scratch_alloc heff_t3 (by decide) _ _ hnt_push hcr_push
    (fun qw nw mid hsz_ev _ hmid_loc _ heff_mid _ hqw_lo hqw_add hsp_le _ _ hnt_ps hcr_ps => ?_)
  have hnw_eq : nw = 24 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hnw_eq
  have h24 : ((24 : BitVec 64).toNat + 7) / 8 * 8 = 24 := by decide
  rw [h24] at hqw_add
  have hse_lt : scratchEnd < 2 ^ 64 := by decide
  have hsp_s_hi : globN s "scratch_ptr" ≤ scratchEnd := hAR.2.2.2.2.2.1
  have hqw8 : (qw + 8#64).toNat = qw.toNat + 8 := BitVec.toNat_add_of_lt (by change qw.toNat + 8 < 2 ^ 64; omega)
  have hqw16 : (qw + 16#64).toNat = qw.toNat + 16 := BitVec.toNat_add_of_lt (by change qw.toNat + 16 < 2 ^ 64; omega)
  have hmid_rec : mid.locals.lookup (ofString "rec") = some (.val (.word qw)) := by
    rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hmid_aft : mid.locals.lookup (ofString "after") = some (.val (.word w_aft)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_aft, show ofString "rec" ≠ ofString "after" by decide]
  have hmid_end : mid.locals.lookup (ofString "end") = some (.val (.word w_end)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_end, show ofString "rec" ≠ ofString "end" by decide]
  have hmid_top : mid.locals.lookup (ofString "top") = some (.val (.word w_top)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_top, show ofString "rec" ≠ ofString "top" by decide]
  refine worldEff_seq hnt_ps hcr_ps
    (fun _ _ => worldEff_store_word heff_mid _ _
      (fun v hv => by simp [evalHOLExact, hmid_aft] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, hmid_rec] at hx; subst hx
        exact Or.inr (Or.inr (Or.inl ⟨hqw_lo, by omega⟩))))
    (fun u1 hu1 heff_u1 hnt_u1 hcr_u1 => ?_)
  have hu1_loc : u1.locals = mid.locals := by
    have hcf := (evaluate_store_control_frame mid (.var .local (ofString "rec")) (.var .local (ofString "after"))).2.1
    rwa [hu1] at hcf
  refine worldEff_seq hnt_u1 hcr_u1
    (fun _ _ => worldEff_store_word heff_u1 _ _
      (fun v hv => by simp [evalHOLExact, hu1_loc, hmid_end] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, hu1_loc, hmid_rec, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
        subst hx
        exact Or.inr (Or.inr (Or.inl ⟨by rw [hqw8]; omega, by rw [hqw8]; omega⟩))))
    (fun u2 hu2 heff_u2 hnt_u2 hcr_u2 => ?_)
  have hu2_loc : u2.locals = mid.locals := by
    have hcf := (evaluate_store_control_frame u1 (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end"))).2.1
    rw [hu2] at hcf; exact hcf.trans hu1_loc
  refine worldEff_seq hnt_u2 hcr_u2
    (fun _ _ => worldEff_store_word heff_u2 _ _
      (fun v hv => by simp [evalHOLExact, hu2_loc, hmid_top] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, hu2_loc, hmid_rec, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
        subst hx
        exact Or.inr (Or.inr (Or.inl ⟨by rw [hqw16]; omega, by rw [hqw16]; omega⟩))))
    (fun u3 _ heff_u3 hnt_u3 hcr_u3 =>
      worldEff_seq hnt_u3 hcr_u3
        (fun _ _ => worldEff_assign_local heff_u3 _ _)
        (fun u4 _ heff_u4 hnt_u4 hcr_u4 =>
          worldEff_seq hnt_u4 hcr_u4
            (fun _ _ => worldEff_assign_local heff_u4 _ _)
            (fun u5 _ heff_u5 _ _ => worldEff_assign_local heff_u5 _ _)))

private def vibLoopBody : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end")))
    (.ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
      (.assign .local (ofString "go") (.const 0))
      (.seq
        (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
        (.seq
          (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
          (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16]))))))
    (.decCall (ofString "h") (.comb [.one, .one, .one]) (ofString "rlp_item_header")
      [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]]
      (.dec (ofString "payload") .one (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
        (.dec (ofString "after") .one (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))])
          (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
            vibPushProg
            (.assign .local (ofString "pos") (.var .local (ofString "after")))))))

private theorem worldEff_vibLoopBody {F : Type}
    {s t : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff_t : WorldEff s t [] wsBufs wsGw)
    (hinv_t : WordLocals ["top", "pos", "end", "go"] t)
    (hnt_b : (evaluateHOLFiniteState t vibLoopBody).1 ≠ some .timeOut)
    (hcr_b : ContOrRes (evaluateHOLFiniteState t vibLoopBody).1) :
    WorldEff s (evaluateHOLFiniteState t vibLoopBody).2 [] wsBufs wsGw := by
  dsimp only [vibLoopBody] at hnt_b hcr_b ⊢
  refine worldEff_ite heff_t _ hnt_b hcr_b
    (fun _ _ _ hnt_eq hcr_eq =>
      worldEff_ite heff_t _ hnt_eq hcr_eq
        (fun _ _ _ _ _ => worldEff_assign_local heff_t _ _)
        (fun _ hnt_pop hcr_pop =>
          worldEff_seq hnt_pop hcr_pop
            (fun _ _ => worldEff_assign_local heff_t _ _)
            (fun m1 _ heff_m1 hnt_p2 hcr_p2 =>
              worldEff_seq hnt_p2 hcr_p2
                (fun _ _ => worldEff_assign_local heff_m1 _ _)
                (fun m2 _ heff_m2 _ _ => worldEff_assign_local heff_m2 _ _))))
    (fun _ hnt_neq hcr_neq => ?_)
  refine worldEff_decCall_ro heff_t InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_item_header
    (ofString "h") (.comb [.one, .one, .one]) _ hnt_neq hcr_neq (fun rvh cpost _ hcpost hnt_c1 hcr_c1 => ?_)
  let t1 := setVarHOLFinite (ofString "h") rvh { cpost with locals := t.locals }
  have heff_t1 : WorldEff s t1 [] wsBufs wsGw := (heff_t.of_readOnly hcpost).locals_clock _ _
  obtain ⟨w_top, htop_t⟩ := hinv_t "top" (by simp)
  obtain ⟨w_end, hend_t⟩ := hinv_t "end" (by simp)
  refine worldEff_dec heff_t1 _ _ _ hnt_c1 hcr_c1 (fun vpay _ hsh_pay hnt_c2 hcr_c2 => ?_)
  rcases vpay with ⟨⟨wpay⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_pay
  let t2 := setVarHOLFinite (ofString "payload") (.val (.word wpay)) t1
  have heff_t2 : WorldEff s t2 [] wsBufs wsGw := heff_t1.locals_clock _ _
  refine worldEff_dec heff_t2 _ _ _ hnt_c2 hcr_c2 (fun vaft _ hsh_aft hnt_c3 hcr_c3 => ?_)
  rcases vaft with ⟨⟨waft⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_aft
  let t3 := setVarHOLFinite (ofString "after") (.val (.word waft)) t2
  have heff_t3 : WorldEff s t3 [] wsBufs wsGw := heff_t2.locals_clock _ _
  refine worldEff_ite heff_t3 _ hnt_c3 hcr_c3
    (fun _ _ _ hnt_push hcr_push =>
      worldEff_vibPush hAR heff_t3 w_top w_end waft
        (by simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by simp [t3, t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hend_t,
              show ofString "after" ≠ ofString "end" by decide,
              show ofString "payload" ≠ ofString "end" by decide,
              show ofString "h" ≠ ofString "end" by decide])
        (by simp [t3, t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htop_t,
              show ofString "after" ≠ ofString "top" by decide,
              show ofString "payload" ≠ ofString "top" by decide,
              show ofString "h" ≠ ofString "top" by decide])
        hnt_push hcr_push)
    (fun _ _ _ => worldEff_assign_local heff_t3 _ _)

theorem worldEff__rlp_validate_items_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") vals =
      some (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).2
      [] wsBufs wsGw := by
  obtain ⟨wp, wlen, rfl, hp_lk, hlen_lk⟩ :=
    lookupCode_two_words (by decide) lookup__rlp_validate_items_body hl
  have heff0 : WorldEff s s [] wsBufs wsGw := WorldEff.refl s [] wsBufs wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn__rlp_validate_items_body =
      .dec (ofString "top") .one (.const 0)
        (.dec (ofString "pos") .one (.var .local (ofString "p"))
          (.dec (ofString "end") .one (.op .add [.var .local (ofString "p"), .var .local (ofString "len")])
            (.dec (ofString "go") .one (.const 1)
              (.seq
                (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) vibLoopBody)
                (.return (.const 0)))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_dec heff0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vtop hvtop _ hnt1 hcr1 => ?_)
  have hvtop_eq : vtop = .val (.word 0) := by simp [evalHOLExact] at hvtop; exact hvtop.symm
  subst hvtop_eq
  let s1 := setVarHOLFinite (ofString "top") (.val (.word 0)) s
  have heff1 : WorldEff s s1 [] wsBufs wsGw := heff0.locals_clock _ _
  refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun vpos hvpos _ hnt2 hcr2 => ?_)
  have hvpos_eq : vpos = .val (.word wp) := by
    simp [s1, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hp_lk,
      show ofString "top" ≠ ofString "p" by decide] at hvpos
    exact hvpos.symm
  subst hvpos_eq
  let s2 := setVarHOLFinite (ofString "pos") (.val (.word wp)) s1
  have heff2 : WorldEff s s2 [] wsBufs wsGw := heff1.locals_clock _ _
  refine worldEff_dec heff2 _ _ _ hnt2 hcr2 (fun vend hvend _ hnt3 hcr3 => ?_)
  have hvend_eq : vend = .val (.word (wp + wlen)) := by
    simp [s2, s1, setVarHOLFinite, evalHOLExact, evalListHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
      hp_lk, hlen_lk, valueIsWord, valueWord, wordOpHOL, wordOp,
      show ofString "pos" ≠ ofString "p" by decide, show ofString "top" ≠ ofString "p" by decide,
      show ofString "pos" ≠ ofString "len" by decide, show ofString "top" ≠ ofString "len" by decide] at hvend
    exact hvend.symm
  subst hvend_eq
  let s3 := setVarHOLFinite (ofString "end") (.val (.word (wp + wlen))) s2
  have heff3 : WorldEff s s3 [] wsBufs wsGw := heff2.locals_clock _ _
  refine worldEff_dec heff3 _ _ _ hnt3 hcr3 (fun vgo hvgo _ hnt4 hcr4 => ?_)
  have hvgo_eq : vgo = .val (.word 1) := by simp [evalHOLExact] at hvgo; exact hvgo.symm
  subst hvgo_eq
  let s4 := setVarHOLFinite (ofString "go") (.val (.word 1)) s3
  have heff4 : WorldEff s s4 [] wsBufs wsGw := heff3.locals_clock _ _
  have hw4 : WordLocals ["top", "pos", "end", "go"] s4 := by
    intro nm hnm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
    rcases hnm with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "top" by decide, show ofString "end" ≠ ofString "top" by decide,
        show ofString "pos" ≠ ofString "top" by decide]⟩
    · exact ⟨wp, by simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "pos" by decide, show ofString "end" ≠ ofString "pos" by decide]⟩
    · exact ⟨wp + wlen, by simp [s4, s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "end" by decide]⟩
    · exact ⟨1, by simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  have hws_vib : wsafe vibLoopBody = true := by decide
  refine worldEff_seq hnt4 hcr4
    (fun hnt_w hcr_w =>
      worldEff_while _ (WordLocals ["top", "pos", "end", "go"])
        (fun _ hinv => hinv)
        (fun t heff_t hinv_t hnt_b hcr_b =>
          ⟨worldEff_vibLoopBody hAR heff_t hinv_t hnt_b hcr_b,
           fun hf => wordLocals_flowing hws_vib hinv_t
             (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩)
        s4.clock s4 rfl heff4 hw4 hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)

theorem WorldEff.from_locals_clock {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff { s with locals := L, clock := k } cur Rl B gw) :
    WorldEff s cur Rl B gw :=
  ⟨h.arena, h.code, h.memaddrs, h.be, h.eshapes, h.hp_lo, h.fmp_eq, h.sp_hi,
   h.gw_kept, h.fresh_bufs, h.out_dom, h.cell_frame, h.byte_frame⟩

private theorem handledCall_raise_keeps_local {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F)
    (eid evar fname : MlS) (preProg : ProgHOL 64) (rexp : ExpHOL 64) (args : List (ExpHOL 64))
    (key : MlS) (hrun : evaluateHOLFiniteState cur
      (.call (some (none, some (eid, evar, .seq preProg (.raise eid rexp)))) fname args) = (none, mid)) :
    mid.locals.lookup key = cur.locals.lookup key := by
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vs
  · rw [hargs] at hrun; cases hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hlk : lookupCodeHOLFinite cur.code.lookup fname vs with _ | ⟨b', c', r'⟩
    · rw [hlk] at hrun; cases hrun
    · rw [hlk] at hrun; dsimp only at hrun
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hrun; cases hrun
      · rw [if_neg hz] at hrun
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite cur c') b' with ⟨res_b, pb⟩
        rw [hb] at hrun
        cases res_b with
        | none => cases hrun
        | some rb =>
          cases rb with
          | returned rv =>
            dsimp only at hrun
            by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) r' = true
            · rw [if_pos hsh] at hrun; injection hrun with _ hm; rw [← hm]
            · rw [if_neg hsh] at hrun; cases hrun
          | exception exId exVal =>
            dsimp only at hrun
            by_cases he : exId = eid
            · subst exId; rw [if_pos rfl] at hrun
              rcases hes : cur.eshapes.lookup eid with _ | esh
              · rw [hes] at hrun; cases hrun
              · rw [hes] at hrun; dsimp only at hrun
                by_cases hok : (shapeEqHOL (shapeOfHOLExact exVal) esh &&
                    isValidValueHOLExact cur.toExact .local evar exVal) = true
                · rw [if_pos hok, evaluateHOLFiniteState_seq_line780] at hrun
                  rcases hp : evaluateHOLFiniteState _ preProg with ⟨rp, mp⟩
                  rw [hp] at hrun
                  cases rp with
                  | some _ => cases hrun
                  | none =>
                    dsimp only at hrun
                    rw [evaluateHOLFiniteState_raise] at hrun
                    rcases hes2 : mp.eshapes.lookup eid with _ | esh2
                    · rw [hes2] at hrun; cases hrun
                    · rw [hes2] at hrun
                      rcases hrv : @evalHOLExact 64 F _ mp.toExact
                          (fun a => Classical.propDecidable (mp.memaddrs a)) rexp with _ | rval
                      · rw [hrv] at hrun; cases hrun
                      · rw [hrv] at hrun; dsimp only at hrun
                        split at hrun <;> cases hrun
                · rw [if_neg hok] at hrun; cases hrun
            · rw [if_neg he] at hrun; cases hrun
          | _ => cases hrun

theorem worldEff_rlp_validate_items {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_validate_items") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_validate_items, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).2
      [] wsBufs wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] wsBufs wsGw := WorldEff.refl s [] wsBufs wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_validate_items =
      .decCall (ofString "mark") .one (ofString "scratch_mark") []
        (.dec (ofString "e") .one (.const 0)
          (.seq
            (.call (some (none, some (ofString "RlpErr", ofString "e",
                .seq
                  (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
                  (.raise (ofString "RlpErr") (.var .local (ofString "e"))))))
              (ofString "_rlp_validate_items_body") [.var .local (ofString "p"), .var .local (ofString "len")])
            (.seq
              (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
              (.return (.const 0))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_decCall_scratch_mark heff0 _ hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun sp mid1 _ _ hsp_al hsp_lo hsp_hi hmid1_eq heff1 hnt1 hcr1 => ?_)
  refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun ve hve _ hnt2 hcr2 => ?_)
  have hve_eq : ve = .val (.word (0 : BitVec 64)) := by simp [evalHOLExact] at hve; exact hve.symm
  subst hve_eq
  let mid2 := setVarHOLFinite (ofString "e") (.val (.word (0 : BitVec 64))) mid1
  have heff2 : WorldEff s mid2 [] wsBufs wsGw := heff1.locals_clock _ _
  have hmark_m2 : mid2.locals.lookup (ofString "mark") = some (.val (.word sp)) := by
    simp [mid2, setVarHOLFinite, hmid1_eq, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "e" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_c hcr_c =>
      worldEff_handledCall heff2 none (ofString "RlpErr") (ofString "e") _
        (ofString "_rlp_validate_items_body") _
        (fun _ _ h => by cases h) (by decide) _ _ _ lookup__rlp_validate_items_body
        (fun callee cvals _ hlc hnt_cb hres_cb =>
          heff2.trans_noBuf
            (WorldEff.from_locals_clock
              (worldEff__rlp_validate_items_body (callEntryStateHOLFinite mid2 callee) cvals
                heff2.code (localsFree_arenaReady mid2 callee _ heff2.arena)
                (by simpa [heff2.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
            ws_B_sub ws_no_gb)
        (fun exVal cpost heff_cp hnt_h hcr_h => by
          let hst := setVarHOLFinite (ofString "e") exVal { cpost with locals := mid2.locals }
          have heff_hst : WorldEff s hst [] wsBufs wsGw := heff_cp.locals_clock _ _
          have hmark_hst : @evalHOLExact 64 F _ hst.toExact (fun a => Classical.propDecidable (hst.memaddrs a))
              (.var .local (ofString "mark")) = some (.val (.word sp)) := by
            simp [hst, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hmark_m2,
              show ofString "e" ≠ ofString "mark" by decide]
          exact worldEff_seq hnt_h hcr_h
            (fun hnt_sr _ => (worldEff_call0_scratch_release hAR.2 heff_hst (by decide) _ sp hmark_hst hsp_lo hsp_hi hsp_al hnt_sr).2.choose_spec.2)
            (fun m_sr _ heff_sr _ _ => worldEff_raise heff_sr _ _))
        hnt_c hcr_c)
    (fun mid3 hmid3 heff3 hnt3 hcr3 => ?_)
  have hmark_m3 : mid3.locals.lookup (ofString "mark") = some (.val (.word sp)) := by
    rw [handledCall_raise_keeps_local mid2 mid3 _ _ _ _ _ _ _ hmid3]
    exact hmark_m2
  have hmark_ev3 : @evalHOLExact 64 F _ mid3.toExact (fun a => Classical.propDecidable (mid3.memaddrs a))
      (.var .local (ofString "mark")) = some (.val (.word sp)) := hmark_m3
  exact worldEff_seq hnt3 hcr3
    (fun hnt_sr _ => (worldEff_call0_scratch_release hAR.2 heff3 (by decide) _ sp hmark_ev3 hsp_lo hsp_hi hsp_al hnt_sr).2.choose_spec.2)
    (fun m_sr _ heff_sr _ _ => worldEff_return heff_sr _)

theorem worldEff_rlp_item_total {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_item_total") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_item_total, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).2
      [] wsBufs wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] wsBufs wsGw := WorldEff.refl s [] wsBufs wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_ro heff0 InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_item_header
    _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun rvh cpost _ hcpost hnt1 hcr1 => ?_)
  let s1 := setVarHOLFinite (ofString "h") rvh { cpost with locals := s.locals }
  have heff1 : WorldEff s s1 [] wsBufs wsGw := (heff0.of_readOnly hcpost).locals_clock _ _
  refine worldEff_seq hnt1 hcr1
    (fun hnt_i hcr_i =>
      worldEff_ite heff1 _ hnt_i hcr_i
        (fun _ _ _ hnt_c hcr_c =>
          worldEff_call0_eff heff1 (ofString "rlp_validate_items") _ _ _ _ lookup_rlp_validate_items
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff1.trans_noBuf
                (WorldEff.from_locals_clock
                  (worldEff_rlp_validate_items (callEntryStateHOLFinite s1 callee) cvals
                    heff1.code (localsFree_arenaReady s1 callee _ heff1.arena)
                    (by simpa [heff1.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                ws_B_sub ws_no_gb)
            hnt_c hcr_c)
        (fun _ _ _ => worldEff_skip heff1))
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)

theorem worldEff_rlp_list_count {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_count") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_count, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).2
      [] wsBufs wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] wsBufs wsGw := WorldEff.refl s [] wsBufs wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_list_count,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_dec heff0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vcnt _ _ hnt1 hcr1 => ?_)
  let s1 := setVarHOLFinite (ofString "count") vcnt s
  have heff1 : WorldEff s s1 [] wsBufs wsGw := heff0.locals_clock _ _
  refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun voff _ _ hnt2 hcr2 => ?_)
  let s2 := setVarHOLFinite (ofString "off") voff s1
  have heff2 : WorldEff s s2 [] wsBufs wsGw := heff1.locals_clock _ _
  refine worldEff_seq hnt2 hcr2
    (fun hnt_w hcr_w =>
      worldEff_while _ (fun _ => True) (fun _ _ => trivial)
        (fun t heff_t _ hnt_b hcr_b =>
          ⟨worldEff_decCall_eff heff_t (ofString "total") .one (ofString "rlp_item_total") _ _ _ _ lookup_rlp_item_total
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff_t.trans_noBuf
                (WorldEff.from_locals_clock
                  (worldEff_rlp_item_total (callEntryStateHOLFinite t callee) cvals
                    heff_t.code (localsFree_arenaReady t callee _ heff_t.arena)
                    (by simpa [heff_t.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                ws_B_sub ws_no_gb)
            (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
              worldEff_seq hnt_k hcr_k
                (fun _ _ => worldEff_assign_local (heff_cp.locals_clock _ _) _ _)
                (fun m2 _ heff_m2 _ _ => worldEff_assign_local heff_m2 _ _))
            hnt_b hcr_b,
           fun _ => trivial⟩)
        s2.clock s2 rfl heff2 trivial hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)

theorem worldEff_rlp_item {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_item") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_item, s.locals, .comb [.one, .one, .one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item)).2
      [] wsBufs wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] wsBufs wsGw := WorldEff.refl s [] wsBufs wsGw hAR hc
  have hrf := InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_fail
  have hrrl := InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_read_length
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_seq hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun hnt_0 hcr_0 =>
      worldEff_ite heff0 _ hnt_0 hcr_0
        (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff0 hrf _ hnt_f hcr_f)
        (fun _ _ _ => worldEff_skip heff0))
    (fun m0 _ heff_m0 hnt_m0 hcr_m0 => ?_)
  refine worldEff_dec heff_m0 _ _ _ hnt_m0 hcr_m0 (fun vb _ _ hnt_b hcr_b => ?_)
  let sb := setVarHOLFinite (ofString "b") vb m0
  have heff_sb : WorldEff s sb [] wsBufs wsGw := heff_m0.locals_clock _ _
  -- Branch 1: `b < 128`
  refine worldEff_seq hnt_b hcr_b
    (fun hnt_1 hcr_1 =>
      worldEff_ite heff_sb _ hnt_1 hcr_1
        (fun _ _ _ _ _ => worldEff_return heff_sb _)
        (fun _ _ _ => worldEff_skip heff_sb))
    (fun m1 _ heff_m1 hnt_m1 hcr_m1 => ?_)
  -- Branch 2: `183 >= b`
  refine worldEff_seq hnt_m1 hcr_m1
    (fun hnt_2 hcr_2 =>
      worldEff_ite heff_m1 _ hnt_2 hcr_2
        (fun _ _ _ hnt_t2 hcr_t2 =>
          worldEff_dec heff_m1 _ _ _ hnt_t2 hcr_t2 (fun vn _ _ hnt_n hcr_n =>
            let sn := setVarHOLFinite (ofString "n") vn m1
            have heff_sn : WorldEff s sn [] wsBufs wsGw := heff_m1.locals_clock _ _
            worldEff_seq hnt_n hcr_n
              (fun hnt_c1 hcr_c1 =>
                worldEff_ite heff_sn _ hnt_c1 hcr_c1
                  (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_sn hrf _ hnt_f hcr_f)
                  (fun _ _ _ => worldEff_skip heff_sn))
              (fun mn1 _ heff_mn1 hnt_c2 hcr_c2 =>
                worldEff_seq hnt_c2 hcr_c2
                  (fun hnt_c3 hcr_c3 =>
                    worldEff_ite heff_mn1 _ hnt_c3 hcr_c3
                      (fun _ _ _ hnt_c4 hcr_c4 =>
                        worldEff_ite heff_mn1 _ hnt_c4 hcr_c4
                          (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_mn1 hrf _ hnt_f hcr_f)
                          (fun _ _ _ => worldEff_skip heff_mn1))
                      (fun _ _ _ => worldEff_skip heff_mn1))
                  (fun mn2 _ heff_mn2 _ _ => worldEff_return heff_mn2 _))))
        (fun _ _ _ => worldEff_skip heff_m1))
    (fun m2 _ heff_m2 hnt_m2 hcr_m2 => ?_)
  -- Branch 3: `191 >= b`
  refine worldEff_seq hnt_m2 hcr_m2
    (fun hnt_3 hcr_3 =>
      worldEff_ite heff_m2 _ hnt_3 hcr_3
        (fun _ _ _ hnt_t3 hcr_t3 =>
          worldEff_dec heff_m2 _ _ _ hnt_t3 hcr_t3 (fun vll _ _ hnt_ll hcr_ll =>
            let sll := setVarHOLFinite (ofString "ll") vll m2
            have heff_sll : WorldEff s sll [] wsBufs wsGw := heff_m2.locals_clock _ _
            worldEff_seq hnt_ll hcr_ll
              (fun hnt_c1 hcr_c1 =>
                worldEff_ite heff_sll _ hnt_c1 hcr_c1
                  (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_sll hrf _ hnt_f hcr_f)
                  (fun _ _ _ => worldEff_skip heff_sll))
              (fun mll1 _ heff_mll1 hnt_dc hcr_dc =>
                worldEff_decCall_ro heff_mll1 hrrl _ _ _ hnt_dc hcr_dc (fun rvn cpost _ hcpost hnt_k hcr_k =>
                  let mll2 := setVarHOLFinite (ofString "n") rvn { cpost with locals := mll1.locals }
                  have heff_mll2 : WorldEff s mll2 [] wsBufs wsGw := (heff_mll1.of_readOnly hcpost).locals_clock _ _
                  worldEff_seq hnt_k hcr_k
                    (fun hnt_k1 hcr_k1 =>
                      worldEff_ite heff_mll2 _ hnt_k1 hcr_k1
                        (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_mll2 hrf _ hnt_f hcr_f)
                        (fun _ _ _ => worldEff_skip heff_mll2))
                    (fun mll3 _ heff_mll3 hnt_k2 hcr_k2 =>
                      worldEff_seq hnt_k2 hcr_k2
                        (fun hnt_k3 hcr_k3 =>
                          worldEff_ite heff_mll3 _ hnt_k3 hcr_k3
                            (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_mll3 hrf _ hnt_f hcr_f)
                            (fun _ _ _ => worldEff_skip heff_mll3))
                        (fun mll4 _ heff_mll4 _ _ => worldEff_return heff_mll4 _))))))
        (fun _ _ _ => worldEff_skip heff_m2))
    (fun m3 _ heff_m3 hnt_m3 hcr_m3 => ?_)
  -- Branch 4: `247 >= b` vs `> 247`
  refine worldEff_seq hnt_m3 hcr_m3
    (fun hnt_4 hcr_4 =>
      worldEff_ite heff_m3 _ hnt_4 hcr_4
        (fun _ _ _ hnt_t4 hcr_t4 =>
          worldEff_dec heff_m3 _ _ _ hnt_t4 hcr_t4 (fun vn _ _ hnt_n hcr_n =>
            let sn := setVarHOLFinite (ofString "n") vn m3
            have heff_sn : WorldEff s sn [] wsBufs wsGw := heff_m3.locals_clock _ _
            worldEff_seq hnt_n hcr_n
              (fun hnt_c1 hcr_c1 =>
                worldEff_ite heff_sn _ hnt_c1 hcr_c1
                  (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_sn hrf _ hnt_f hcr_f)
                  (fun _ _ _ => worldEff_skip heff_sn))
              (fun mn1 _ heff_mn1 hnt_c2 hcr_c2 =>
                worldEff_seq hnt_c2 hcr_c2
                  (fun hnt_lc hcr_lc =>
                    worldEff_call0_eff heff_mn1 (ofString "rlp_list_count") _ _ _ _ lookup_rlp_list_count
                      (fun callee cvals _ hlc hnt_cb hres_cb =>
                        heff_mn1.trans_noBuf
                          (WorldEff.from_locals_clock
                            (worldEff_rlp_list_count (callEntryStateHOLFinite mn1 callee) cvals
                              heff_mn1.code (localsFree_arenaReady mn1 callee _ heff_mn1.arena)
                              (by simpa [heff_mn1.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                          ws_B_sub ws_no_gb)
                      hnt_lc hcr_lc)
                  (fun mn2 _ heff_mn2 _ _ => worldEff_return heff_mn2 _))))
        (fun _ _ _ => worldEff_skip heff_m3))
    (fun m4 _ heff_m4 hnt_m4 hcr_m4 => ?_)
  -- Branch 5 (`> 247`):
  refine worldEff_dec heff_m4 _ _ _ hnt_m4 hcr_m4 (fun vll _ _ hnt_ll hcr_ll => ?_)
  let sll := setVarHOLFinite (ofString "ll") vll m4
  have heff_sll : WorldEff s sll [] wsBufs wsGw := heff_m4.locals_clock _ _
  refine worldEff_seq hnt_ll hcr_ll
    (fun hnt_c1 hcr_c1 =>
      worldEff_ite heff_sll _ hnt_c1 hcr_c1
        (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_sll hrf _ hnt_f hcr_f)
        (fun _ _ _ => worldEff_skip heff_sll))
    (fun mll1 _ heff_mll1 hnt_dc hcr_dc =>
      worldEff_decCall_ro heff_mll1 hrrl _ _ _ hnt_dc hcr_dc (fun rvn cpost _ hcpost hnt_k hcr_k =>
        let mll2 := setVarHOLFinite (ofString "n") rvn { cpost with locals := mll1.locals }
        have heff_mll2 : WorldEff s mll2 [] wsBufs wsGw := (heff_mll1.of_readOnly hcpost).locals_clock _ _
        worldEff_seq hnt_k hcr_k
          (fun hnt_k1 hcr_k1 =>
            worldEff_ite heff_mll2 _ hnt_k1 hcr_k1
              (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_mll2 hrf _ hnt_f hcr_f)
              (fun _ _ _ => worldEff_skip heff_mll2))
          (fun mll3 _ heff_mll3 hnt_k2 hcr_k2 =>
            worldEff_seq hnt_k2 hcr_k2
              (fun hnt_k3 hcr_k3 =>
                worldEff_ite heff_mll3 _ hnt_k3 hcr_k3
                  (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_mll3 hrf _ hnt_f hcr_f)
                  (fun _ _ _ => worldEff_skip heff_mll3))
              (fun mll4 _ heff_mll4 hnt_k4 hcr_k4 =>
                worldEff_seq hnt_k4 hcr_k4
                  (fun hnt_lc hcr_lc =>
                    worldEff_call0_eff heff_mll4 (ofString "rlp_list_count") _ _ _ _ lookup_rlp_list_count
                      (fun callee cvals _ hlc hnt_cb hres_cb =>
                        heff_mll4.trans_noBuf
                          (WorldEff.from_locals_clock
                            (worldEff_rlp_list_count (callEntryStateHOLFinite mll4 callee) cvals
                              heff_mll4.code (localsFree_arenaReady mll4 callee _ heff_mll4.arena)
                              (by simpa [heff_mll4.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                          ws_B_sub ws_no_gb)
                      hnt_lc hcr_lc)
                  (fun mll5 _ heff_mll5 _ _ => worldEff_return heff_mll5 _)))))

theorem worldEff_rlp_decode_fully {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_decode_fully") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_decode_fully, s.locals, .comb [.one, .one, .one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_decode_fully)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_decode_fully)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_decode_fully)).2
      [] wsBufs wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] wsBufs wsGw := WorldEff.refl s [] wsBufs wsGw hAR hc
  have hrf := InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_fail
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_decode_fully,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "it") (.comb [.one, .one, .one, .one])
    (ofString "rlp_item") _ _ _ _ lookup_rlp_item
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_item (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_B_sub ws_no_gb)
    (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
      let m1 := setVarHOLFinite (ofString "it") rv { cpost with locals := s.locals }
      have heff_m1 : WorldEff s m1 [] wsBufs wsGw := heff_cp.locals_clock _ _
      worldEff_seq hnt_k hcr_k
        (fun hnt_i hcr_i =>
          worldEff_ite heff_m1 _ hnt_i hcr_i
            (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_m1 hrf _ hnt_f hcr_f)
            (fun _ _ _ => worldEff_skip heff_m1))
        (fun m2 _ heff_m2 _ _ => worldEff_return heff_m2 _))
    hnt (Or.inr (Or.inr (Or.inr hres)))

/-! ### `rlp_list_count` Return Bound (`wcnt.toNat ≤ domainBytes`) & `worldEff_rlp_list_to_slices` -/

private def RetOK (Q : ValueHOL 64 → Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) :
    Prop :=
  ∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) → Q v

private theorem R_seq {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (ha : RetOK Q s a) (hb : ∀ mid, evaluateHOLFiniteState s a = (none, mid) → RetOK Q mid b) :
    RetOK Q s (.seq a b) := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780] at hv
  rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
  rw [hr] at hv
  cases r with
  | none => exact hb mid hr v hv
  | some _ => apply ha v; rw [hr]; simpa using hv

private theorem R_ite {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {yes no : ProgHOL 64}
    (h : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → (w ≠ 0 → RetOK Q s yes) ∧ (w = 0 → RetOK Q s no)) :
    RetOK Q s (.ite c yes no) := by
  intro v hv
  rw [evaluateHOLFiniteState_ite] at hv
  split at hv
  · rename_i w hw
    split at hv
    · exact (h w hw).2 (by assumption) v hv
    · exact (h w hw).1 (by assumption) v hv
  · simp at hv

private theorem R_dec {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (h : ∀ v, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) init =
      some v → shapeEqHOL sh (shapeOfHOLExact v) = true → RetOK Q (setVarHOLFinite n v s) body) :
    RetOK Q s (.dec n sh init body) := by
  intro v hv
  rw [evaluateHOLFiniteState_dec_total] at hv
  dsimp only at hv
  split at hv
  · simp at hv
  · rename_i val hval
    split at hv
    · rename_i hsh; exact h val hval hsh v hv
    · simp at hv

private theorem R_ret {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    (h : ∀ v, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
      some v → Q v) :
    RetOK Q s (.return e) := by
  intro v hv
  rw [evaluateHOLFiniteState_return] at hv
  split at hv
  · simp at hv
  · rename_i val hval
    split at hv
    · simp at hv; subst hv; exact h val hval
    · simp at hv

private theorem R_skip {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} :
    RetOK Q s .skip := by
  intro v hv; rw [evaluateHOLFiniteState_skip] at hv; simp at hv

private theorem rlp_fail_noret {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_fail)).1 ≠ some (.returned v) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_fail =
      .seq (.raise (ofString "RlpErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
  have hraise : ∀ w, (evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ some (.returned w) ∧
      (evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ none := by
    intro w
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  rw [hb, evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
    ProgHOL 64) with ⟨r, mid⟩
  rw [hr] at hraise
  cases r with
  | none => exact absurd rfl (hraise v).2
  | some _ => dsimp only; exact (hraise v).1

private theorem lookup_rlp_fail_cgr : originalRuntimeCode.lookup (ofString "rlp_fail") =
    some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_rlp_fail, .one) :=
  lookup_of_guestAst_getElem 105 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_fail) rfl

private theorem lookup_rlp_item_header_cgr : originalRuntimeCode.lookup (ofString "rlp_item_header") =
    some ([(ofString "p", .one), (ofString "len", .one)],
      sourceFnBody Guest.Software.guestFn_rlp_item_header, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 109 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_header) rfl

private theorem call_noret_cgr {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64))
    (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) f args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, st⟩
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> simp

private theorem call_fail_nonone_cgr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "rlp_fail") args)).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · rename_i values _
    split
    · simp
    · rename_i body callee rs hl
      have hb := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ rs values callee
        (by rw [hcode]; exact lookup_rlp_fail_cgr) hl
      subst hb
      split
      · simp
      · have hnr := fun w => rlp_fail_noret (callEntryStateHOLFinite s callee) w
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_rlp_fail) with ⟨r, st⟩
        rw [hrun] at hnr
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> try simp
        exact absurd rfl (hnr w)

private theorem R_guard {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {c : ExpHOL 64} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (h : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w = 0 → RetOK Q s rest) :
    RetOK Q s (.seq (.ite c (.call (some (none, none)) (ofString "rlp_fail") args) .skip) rest) := by
  apply R_seq
  · apply R_ite
    intro w _
    exact ⟨fun _ v hv => absurd hv (call_noret_cgr s _ args v), fun _ => R_skip⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · rename_i w hw
      split at hmid
      · rename_i hw0
        rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact h w hw hw0
      · exact absurd (by rw [hmid]) (call_fail_nonone_cgr s hcode args)
    · simp at hmid

private theorem R_decCall {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {f : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : ∀ (u : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), shapeEqHOL (shapeOfHOLExact v) sh = true →
      u.code = s.code → (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) →
      u.locals.lookup n = some v → RetOK Q u cont) :
    RetOK Q s (.decCall n sh f args cont) := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv
  split at hv
  · simp at hv
  · split at hv
    · simp at hv
    · rename_i body callee rs _
      split at hv
      · simp at hv
      · have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
        rw [hrun] at hmeta
        change st.code = s.code at hmeta
        simp only [hrun] at hv
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only at hv <;> try simp at hv
        split at hv
        · rename_i hsh
          try simp only [Bool.and_eq_true] at hsh
          refine h _ w hsh.1 (by simp [setVarHOLFinite, fixClockHOLFinite, hmeta]) ?_ ?_ v hv
          · intro k hk
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp at hv

private theorem R_decCall' {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {f : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : ∀ (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (v : ValueHOL 64),
      evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) args =
        some values →
      lookupCodeHOLFinite s.code.lookup f values = some (body, callee, rs) →
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned v) →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      ∀ (u : PanSemStateFiniteExact 64 F), u.code = s.code →
        (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) → u.locals.lookup n = some v →
        RetOK Q u cont) :
    RetOK Q s (.decCall n sh f args cont) := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv
  split at hv
  · simp at hv
  · rename_i values hargs
    split at hv
    · simp at hv
    · rename_i body callee rs hl
      split at hv
      · simp at hv
      · have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
        rw [hrun] at hmeta
        change st.code = s.code at hmeta
        simp only [hrun] at hv
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only at hv <;> try simp at hv
        split at hv
        · rename_i hsh
          try simp only [Bool.and_eq_true] at hsh
          refine h values body callee rs w hargs hl (by rw [hrun]) hsh.1 _
            (by simp [setVarHOLFinite, fixClockHOLFinite, hmeta]) ?_ ?_ v hv
          · intro k hk
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp at hv

private def abrupt_cgr : ProgHOL 64 → Bool
  | .return _ => true
  | .raise _ _ => true
  | .seq _ b => abrupt_cgr b
  | .dec _ _ _ b => abrupt_cgr b
  | .decCall _ _ _ _ c => abrupt_cgr c
  | .ite _ y n => abrupt_cgr y && abrupt_cgr n
  | _ => false

private theorem abrupt_nonone_cgr {F : Type} (p : ProgHOL 64) (h : abrupt_cgr p = true) (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ none := by
  match p, h with
  | .return e, _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | .raise n e, _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | .seq a b, h =>
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
    cases r with
    | none => exact abrupt_nonone_cgr b (by simpa [abrupt_cgr] using h) mid
    | some _ => simp
  | .dec n sh e b, h =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact abrupt_nonone_cgr b (by simpa [abrupt_cgr] using h) _
      · simp
  | .decCall n sh f args c, h =>
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · simp
    · split
      · simp
      · rename_i body callee rs _
        split
        · simp
        · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
          simp only [hrun]
          rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
          split
          · exact abrupt_nonone_cgr c (by simpa [abrupt_cgr] using h) _
          · simp
  | .ite c y n, h =>
    have hh : abrupt_cgr y = true ∧ abrupt_cgr n = true := by simpa [abrupt_cgr] using h
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact abrupt_nonone_cgr n hh.2 s
      · exact abrupt_nonone_cgr y hh.1 s
    · simp

private theorem R_branch {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {yes rest : ProgHOL 64} (hab : abrupt_cgr yes = true)
    (hy : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w ≠ 0 → RetOK Q s yes)
    (hr : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w = 0 → RetOK Q s rest) :
    RetOK Q s (.seq (.ite c yes .skip) rest) := by
  apply R_seq
  · apply R_ite
    intro w hw
    exact ⟨hy w hw, fun _ => R_skip⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · rename_i w hw
      split at hmid
      · rename_i hw0
        rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact hr w hw hw0
      · exact absurd (by rw [hmid]) (abrupt_nonone_cgr yes hab s)
    · simp at hmid

private theorem R_check2 {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {c c' : ExpHOL 64} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (hr : RetOK Q s rest) :
    RetOK Q s (.seq (.ite c (.ite c' (.call (some (none, none)) (ofString "rlp_fail") args) .skip) .skip)
      rest) := by
  apply R_seq
  · apply R_ite
    intro w _
    refine ⟨fun _ => ?_, fun _ => R_skip⟩
    apply R_ite
    intro w' _
    exact ⟨fun _ v hv => absurd hv (call_noret_cgr s _ args v), fun _ => R_skip⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · split at hmid
      · rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact hr
      · rw [evaluateHOLFiniteState_ite] at hmid
        split at hmid
        · split at hmid
          · rw [evaluateHOLFiniteState_skip] at hmid
            simp only [Prod.mk.injEq] at hmid
            obtain ⟨-, rfl⟩ := hmid
            exact hr
          · exact absurd (by rw [hmid]) (call_fail_nonone_cgr s hcode args)
        · simp at hmid
    · simp at hmid

private def hval_cgr (a b c : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word a), .val (.word b), .val (.word c)]

private def HdrQ_cgr (L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ a b c : BitVec 64, v = hval_cgr a b c ∧ 1 ≤ a.toNat + b.toNat ∧ a.toNat + b.toNat ≤ L.toNat

private theorem loadByte_word_dom_cgr {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.loadByte e) =
      some v) :
    ∃ a B : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
        some (.val (.word a)) ∧
      s.memaddrs (panByteAlignHOL (width := 64) a) ∧
      v = .val (.word B) := by
  simp only [evalHOLExact] at hv
  split at hv
  · rename_i a ha
    dsimp only [panMemLoadByteHOL] at hv
    split at hv
    · rename_i hdom
      simp only [Option.map_some, Option.some.injEq] at hv
      exact ⟨a, _, ha, hdom, hv.symm⟩
    · simp at hv
  · simp at hv

private theorem lk_set_cgr {F : Type} (st : PanSemStateFiniteExact 64 F) (k : MlS) (x : ValueHOL 64) (k' : MlS)
    (hk : k ≠ k') : (setVarHOLFinite k x st).locals.lookup k' = st.locals.lookup k' := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk]

private theorem lk_set'_cgr {F : Type} (st : PanSemStateFiniteExact 64 F) (k : MlS) (x : ValueHOL 64) :
    (setVarHOLFinite k x st).locals.lookup k = some x := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem toNat_sub_one_cgr (L : BitVec 64) (hL : L ≠ 0) : (L - 1#64).toNat = L.toNat - 1 := by
  have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [BitVec.toNat_sub]; simp; omega

private theorem short_branch_cgr {F : Type} (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (L B off flag : BitVec 64) (hL : L ≠ 0)
    (hl : st.locals.lookup (ofString "len") = some (.val (.word L)))
    (hb : st.locals.lookup (ofString "b") = some (.val (.word B))) :
    RetOK (HdrQ_cgr L) st
      (.dec (ofString "n") .one (.op .sub [.var .local (ofString "b"), .const off])
        (.seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"), .const 1#64])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
          (.return (.rstruct [.const 1#64, .var .local (ofString "n"), .const flag])))) := by
  refine R_dec (fun v hv _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  refine R_guard (by exact hcode) (fun w hw hw0 => R_ret (fun v hv => ?_))
  have hL1 := toNat_sub_one_cgr L hL
  have hne_nlen : ofString "n" ≠ ofString "len" := by decide
  have hN : (B - off).toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, lk_set_cgr, lk_set'_cgr, hne_nlen, hl, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 < B - off := by rw [BitVec.lt_def, hL1]; omega
    simp [this] at hw
  simp [evalHOLExact, evalListHOLExact, lk_set_cgr, lk_set'_cgr] at hv
  subst hv
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  refine ⟨1, B - off, flag, rfl, by simp, ?_⟩
  rw [h1]
  have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

private theorem long_branch_cgr {F : Type} (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (L B off flag : BitVec 64) (hL : L ≠ 0)
    (hl : st.locals.lookup (ofString "len") = some (.val (.word L)))
    (hb : st.locals.lookup (ofString "b") = some (.val (.word B))) :
    RetOK (HdrQ_cgr L) st
      (.dec (ofString "ll") .one (.op .sub [.var .local (ofString "b"), .const off])
        (.seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"), .const 1#64])
              (.var .local (ofString "ll")))
            (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
          (.decCall (ofString "n") .one (ofString "rlp_read_length")
            [.op .add [.var .local (ofString "p"), .const 1#64], .var .local (ofString "ll")]
            (.seq (.ite (.cmp .notLower (.const 55#64) (.var .local (ofString "n")))
                (.call (some (none, none)) (ofString "rlp_fail") [.const 5#64]) .skip)
              (.seq (.ite (.cmp .lower (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64],
                    .var .local (ofString "ll")]) (.var .local (ofString "n")))
                  (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
                (.return (.rstruct [.op .add [.const 1#64, .var .local (ofString "ll")],
                  .var .local (ofString "n"), .const flag]))))))) := by
  refine R_dec (fun v hv _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have hL1 := toNat_sub_one_cgr L hL
  have hne_ll_len : ofString "ll" ≠ ofString "len" := by decide
  refine R_guard (by exact hcode) (fun w hw hw0 => ?_)
  have hLL : (B - off).toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, lk_set_cgr, lk_set'_cgr, hne_ll_len, hl, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 < B - off := by rw [BitVec.lt_def, hL1]; omega
    simp [this] at hw
  refine R_decCall (fun u v hsh hcu hloc hn => ?_)
  have hvw : ∃ N : BitVec 64, v = .val (.word N) := by
    rcases v with ⟨⟨N⟩⟩ | fs | ⟨nm, fs⟩ <;> simp_all [shapeEqHOL, shapeOfHOLExact]
  obtain ⟨N, rfl⟩ := hvw
  have hul : u.locals.lookup (ofString "len") = some (.val (.word L)) := by
    rw [hloc _ (by decide), lk_set_cgr _ _ _ _ (by decide)]; exact hl
  have hull : u.locals.lookup (ofString "ll") = some (.val (.word (B - off))) := by
    rw [hloc _ (by decide), lk_set'_cgr]
  have hcu' : u.code = originalRuntimeCode := hcu.trans hcode
  refine R_guard hcu' (fun w _ _ => ?_)
  refine R_guard hcu' (fun w hw hw0 => R_ret (fun v hv => ?_))
  have hsub : (L - 1#64 - (B - off)).toNat = L.toNat - 1 - (B - off).toNat := by
    rw [BitVec.toNat_sub, hL1]; have := (B - off).isLt; omega
  have hNle : N.toNat ≤ L.toNat - 1 - (B - off).toNat := by
    simp [evalHOLExact, evalListHOLExact, hul, hull, hn, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 - (B - off) < N := by rw [BitVec.lt_def, hsub]; omega
    simp [this] at hw
  simp [evalHOLExact, evalListHOLExact, hull, hn, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hadd : (1#64 + (B - off)).toNat = 1 + (B - off).toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [h1]; have := L.isLt; omega), h1]
  refine ⟨1#64 + (B - off), N, flag, rfl, ?_, ?_⟩
  · rw [hadd]; omega
  · rw [hadd]
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    omega

private theorem hdr_post_dom_cgr {F : Type} (e : PanSemStateFiniteExact 64 F)
    (hcode : e.code = originalRuntimeCode) (hP : GuestInv e)
    (P L : BitVec 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState e (sourceFnBody Guest.Software.guestFn_rlp_item_header)).1 =
      some (.returned v)) :
    HdrQ_cgr L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd := by
  revert v hret
  change RetOK (fun v => HdrQ_cgr L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd) e
    (sourceFnBody Guest.Software.guestFn_rlp_item_header)
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_guard hcode (fun w hw hw0 => ?_)
  have hL : L ≠ 0 := by
    intro h; subst h; simp [evalHOLExact, hl, Compiler.Encoders.Asm.wordCmpHOL] at hw; subst hw0
    simp at hw
  refine R_dec (fun v hv _ => ?_)
  obtain ⟨P', B, ha, hdom, rfl⟩ := loadByte_word_dom_cgr e _ v hv
  simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq] at ha
  subst ha
  rw [hP.memaddrs, ordinaryDomain_iff] at hdom
  have hhe8 : heapEnd % 8 = 0 := by decide
  have hsb8 : sourceBase % 8 = 0 := by decide
  have hal := panByteAlign_toNat64 P
  have hp_in : sourceBase ≤ P.toNat ∧ P.toNat < heapEnd := ⟨by omega, by omega⟩
  have liftQ : ∀ {st : PanSemStateFiniteExact 64 F} {pr : ProgHOL 64},
      RetOK (HdrQ_cgr L) st pr →
      RetOK (fun v => HdrQ_cgr L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd) st pr :=
    fun h v hv => ⟨h v hv, hp_in⟩
  apply liftQ
  set e1 := setVarHOLFinite (ofString "b") (.val (.word B)) e with he1
  have hb1 : e1.locals.lookup (ofString "b") = some (.val (.word B)) := by
    simp [he1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hl1 : e1.locals.lookup (ofString "len") = some (.val (.word L)) := by
    simp [he1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "len" by decide, hl]
  have hc1 : e1.code = originalRuntimeCode := hcode
  refine R_branch (by rfl) (fun w _ _ => R_ret (fun v hv => ?_)) (fun w _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact] at hv
    subst hv
    refine ⟨0, 1, 0, rfl, by simp, ?_⟩
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    simp; omega
  have hL1 := toNat_sub_one_cgr L hL
  refine R_branch (by rfl) (fun w _ _ => R_dec (fun v hv _ => ?_)) (fun w _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact, hb1, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    set e2 := setVarHOLFinite (ofString "n") (.val (.word (B - 128#64))) e1 with he2
    have hc2 : e2.code = originalRuntimeCode := hcode
    refine R_guard hc2 (fun w hw hw0 => ?_)
    have hN : (B - 128#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, he2, lk_set_cgr, lk_set'_cgr,
        show ofString "n" ≠ ofString "len" by decide, hl1, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
      subst hw0
      by_contra hc
      have : L - 1#64 < B - 128#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hw
    refine R_check2 hc2 (R_ret (fun v hv => ?_))
    simp [evalHOLExact, evalListHOLExact, he2, lk_set_cgr, lk_set'_cgr] at hv
    subst hv
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    refine ⟨1, B - 128#64, 0, rfl, by simp, ?_⟩
    rw [h1]
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  refine R_branch (by rfl) (fun w _ _ => long_branch_cgr e1 hc1 L B 183#64 0#64 hL hl1 hb1) (fun w _ _ => ?_)
  refine R_branch (by rfl) (fun w _ _ => short_branch_cgr e1 hc1 L B 192#64 1#64 hL hl1 hb1) (fun w _ _ => ?_)
  exact long_branch_cgr e1 hc1 L B 247#64 1#64 hL hl1 hb1

private theorem call_flow_locals_cgr {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64))
    (mid : PanSemStateFiniteExact 64 F)
    (h : evaluateHOLFiniteState s (.call (some (none, none)) f args) = (none, mid)) :
    mid.locals = s.locals ∧ mid.code = s.code := by
  have hmeta := (evaluateHOLFiniteState_metadata s (.call (some (none, none)) f args)).1
  rw [h] at hmeta
  refine ⟨?_, hmeta⟩
  revert h
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, st⟩
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
        intro h; rw [← h]

private theorem callee_p_len_cgr {fname : MlS} {body0 : ProgHOL 64} {rs0 : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname =
      some ([(ofString "p", .one), (ofString "len", .one)], body0, rs0))
    (v1 v2 : ValueHOL 64) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup fname [v1, v2] =
      some (body, callee, rs)) :
    body = body0 ∧ callee.lookup (ofString "p") = some v1 ∧ callee.lookup (ofString "len") = some v2 := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · simp at hl
  · rename_i b cl r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    simp only [lookupCodeHOLExact, hlook] at heq
    split at heq
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine ⟨rfl, ?_, by simp⟩
      simp [List.zip, List.foldl, show ofString "p" ≠ ofString "len" by decide]
    · simp at heq

private def TotQDom_cgr (P L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ t : BitVec 64, v = .val (.word t) ∧ 1 ≤ t.toNat ∧ t.toNat ≤ L.toNat ∧
    sourceBase ≤ P.toNat ∧ P.toNat < heapEnd

private theorem total_post_dom_cgr {F : Type} (e : PanSemStateFiniteExact 64 F)
    (hcode : e.code = originalRuntimeCode) (hP : GuestInv e)
    (P L : BitVec 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L))) :
    RetOK (TotQDom_cgr P L) e (sourceFnBody Guest.Software.guestFn_rlp_item_total) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_decCall' (fun values body callee rs v hargs hlk hret _ u _ _ hu => ?_)
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp, hl, Option.some.injEq] at hargs
  subst hargs
  rw [hcode] at hlk
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_cgr lookup_rlp_item_header_cgr _ _ body callee rs hlk
  obtain ⟨⟨a, b, c, rfl, h1, h2⟩, hp_lo, hp_hi⟩ :=
    hdr_post_dom_cgr (callEntryStateHOLFinite e callee) hcode (guestInv_callEntry e callee hP) P L hcp hcl v hret
  refine R_seq (R_ite (fun w _ => ⟨fun _ v hv => absurd hv (call_noret_cgr u _ _ v), fun _ => R_skip⟩))
    (fun mid hmid => ?_)
  have hmid_h : mid.locals.lookup (ofString "h") = some (hval_cgr a b c) := by
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · split at hmid
      · rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        rw [← hmid.2]; exact hu
      · rw [(call_flow_locals_cgr u _ _ mid hmid).1]; exact hu
    · simp at hmid
  refine R_ret (fun v hv => ?_)
  simp [evalHOLExact, evalListHOLExact, hmid_h, hval_cgr, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  refine ⟨a + b, rfl, ?_, ?_, hp_lo, hp_hi⟩
  · rw [BitVec.toNat_add_of_lt (by have := L.isLt; omega)]; omega
  · rw [BitVec.toNat_add_of_lt (by have := L.isLt; omega)]; omega

private theorem decCall_flow_cgr {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS} {sh : ShapeHOL} {f : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hflow : (evaluateHOLFiniteState s (.decCall n sh f args cont)).1 = none) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (v : ValueHOL 64),
      evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) args =
        some values ∧
      lookupCodeHOLFinite s.code.lookup f values = some (body, callee, rs) ∧
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned v) ∧
      ∃ u : PanSemStateFiniteExact 64 F, u.code = s.code ∧
        (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) ∧ u.locals.lookup n = some v ∧
        (evaluateHOLFiniteState u cont).1 = none ∧
        ∀ k, k ≠ n → (evaluateHOLFiniteState s (.decCall n sh f args cont)).2.locals.lookup k =
          (evaluateHOLFiniteState u cont).2.locals.lookup k := by
  revert hflow
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · simp
  rename_i values hargs
  split
  · simp
  rename_i body callee rs hl
  split
  · simp
  have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
  rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
  rw [hrun] at hmeta
  change st.code = s.code at hmeta
  simp only [hrun]
  cases r with
  | none => simp
  | some r =>
    cases r with
    | returned w =>
      dsimp only
      split
      · intro hflow
        refine ⟨values, body, callee, rs, w, hargs, hl, by rw [hrun], _,
          by simp [setVarHOLFinite, fixClockHOLFinite, hmeta], ?_, ?_, hflow, ?_⟩
        · intro k hk
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · intro k hk
          simp only
          rw [resVarEq_lookup_local, if_neg hk]
      · simp
    | _ => simp

private def countCond_cgr : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))

private def countBody_cgr : ProgHOL 64 :=
  .decCall (ofString "total") .one (ofString "rlp_item_total")
    [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
      .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]]
    (.seq (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
      (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1])))

private theorem countBody_step_cgr {F : Type} (s : PanSemStateFiniteExact 64 F) (P y m c : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hP : GuestInv s)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hy : s.locals.lookup (ofString "off") = some (.val (.word y)))
    (hm : s.locals.lookup (ofString "len") = some (.val (.word m)))
    (hc : s.locals.lookup (ofString "count") = some (.val (.word c)))
    (hlt : y.toNat < m.toNat)
    (hflow : (evaluateHOLFiniteState s countBody_cgr).1 = none) :
    ∃ T : BitVec 64,
      1 ≤ T.toNat ∧ y.toNat + T.toNat ≤ m.toNat ∧
      sourceBase ≤ (P + y).toNat ∧ (P + y).toNat < heapEnd ∧
      (evaluateHOLFiniteState s countBody_cgr).2.locals.lookup (ofString "off") = some (.val (.word (y + T))) ∧
      (evaluateHOLFiniteState s countBody_cgr).2.locals.lookup (ofString "count") = some (.val (.word (c + 1#64))) ∧
      (evaluateHOLFiniteState s countBody_cgr).2.locals.lookup (ofString "p") = some (.val (.word P)) ∧
      (evaluateHOLFiniteState s countBody_cgr).2.locals.lookup (ofString "len") = some (.val (.word m)) := by
  unfold countBody_cgr at hflow ⊢
  obtain ⟨values, body, callee, rs, v, hargs, hl, hret, u, hcu, hloc, hu, hcont, hfin⟩ := decCall_flow_cgr hflow
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp, hy, hm,
    wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
    ↓reduceIte, List.foldr, add_zero, Option.some.injEq] at hargs
  subst hargs
  rw [hcode] at hl
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_cgr lookup_rlp_item_total _ _ body callee rs hl
  have hsub : (m - y).toNat = m.toNat - y.toNat := by rw [BitVec.toNat_sub]; omega
  obtain ⟨T, rfl, hT1, hT2, hpy_lo, hpy_hi⟩ :=
    total_post_dom_cgr (callEntryStateHOLFinite s callee) hcode (guestInv_callEntry s callee hP)
      (P + y) (m - y) hcp hcl v hret
  rw [hsub] at hT2
  have huoff : u.locals.lookup (ofString "off") = some (.val (.word y)) := by
    rw [hloc _ (by decide)]; exact hy
  have hucnt : u.locals.lookup (ofString "count") = some (.val (.word c)) := by
    rw [hloc _ (by decide)]; exact hc
  have hup : u.locals.lookup (ofString "p") = some (.val (.word P)) := by
    rw [hloc _ (by decide)]; exact hp
  have hulen : u.locals.lookup (ofString "len") = some (.val (.word m)) := by
    rw [hloc _ (by decide)]; exact hm
  have hfirst : evaluateHOLFiniteState u
      (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) =
      (none, setKvarHOLFinite .local (ofString "off") (.val (.word (y + T))) u) := by
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, evalListHOLExact, huoff, hu, wordOpHOL, wordOp, valueIsWord, valueWord,
      isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
  let u1 := setKvarHOLFinite .local (ofString "off") (.val (.word (y + T))) u
  have hu1_cnt : u1.locals.lookup (ofString "count") = some (.val (.word c)) := by
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hucnt,
      show ofString "off" ≠ ofString "count" by decide]
  have hsecond : evaluateHOLFiniteState u1
      (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1])) =
      (none, setKvarHOLFinite .local (ofString "count") (.val (.word (c + 1#64))) u1) := by
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, evalListHOLExact, hu1_cnt, wordOpHOL, wordOp, valueIsWord, valueWord,
      isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
  refine ⟨T, hT1, by omega, hpy_lo, hpy_hi, ?_, ?_, ?_, ?_⟩
  · rw [hfin (ofString "off") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "count" ≠ ofString "off" by decide]
  · rw [hfin (ofString "count") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [hfin (ofString "p") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hup,
      show ofString "count" ≠ ofString "p" by decide, show ofString "off" ≠ ofString "p" by decide]
  · rw [hfin (ofString "len") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hulen,
      show ofString "count" ≠ ofString "len" by decide, show ofString "off" ≠ ofString "len" by decide]

private def CountRetInv {F : Type} (P m : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  ∃ (vis : Finset (Fin domainBytes)) (y c : BitVec 64),
    s.locals.lookup (ofString "p") = some (.val (.word P)) ∧
    s.locals.lookup (ofString "off") = some (.val (.word y)) ∧
    s.locals.lookup (ofString "len") = some (.val (.word m)) ∧
    s.locals.lookup (ofString "count") = some (.val (.word c)) ∧
    c.toNat = vis.card ∧
    ∀ k ∈ vis, ∃ d : BitVec 64, d.toNat < y.toNat ∧
      sourceBase ≤ (P + d).toNat ∧ (P + d).toNat < heapEnd ∧
      k.val = (P + d).toNat - sourceBase

private theorem countBody_no_bc {F : Type} (t : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState t countBody_cgr).1 ≠ some .break ∧
    (evaluateHOLFiniteState t countBody_cgr).1 ≠ some .continue := by
  unfold countBody_cgr
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rename_i body callee _ _ _
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨r, st⟩
        simp only [hrun]
        cases r with
        | none => simp
        | some r =>
          cases r with
          | returned w =>
            dsimp only
            split
            · dsimp only
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
              split
              · simp
              · split
                · dsimp only
                  rw [evaluateHOLFiniteState_assign]
                  split <;> [simp; (split <;> simp)]
                · simp
            · simp
          | _ => simp

private theorem while_countRetInv {F : Type} (P m : BitVec 64)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F)
    (hclk : s.clock ≤ k) (hinv : CountRetInv P m s)
    (hrun : evaluateHOLFiniteState s (.while countCond_cgr countBody_cgr) = (none, post)) :
    CountRetInv P m post := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact hinv
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) countBody_cgr
          have hbc := countBody_no_bc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) countBody_cgr with ⟨r1, mid⟩
          rw [hbr] at hrun rem hbc
          cases r1 with
          | none =>
            obtain ⟨hc_s, hG_s, vis, y, c, hp, hy, hm, hc_cnt, hcard, hvis⟩ := hinv
            have hlt : y.toNat < m.toNat := by
              simp [countCond_cgr, evalHOLExact, hy, hm, Compiler.Encoders.Asm.wordCmpHOL] at hcond
              by_contra hge
              have hge' : ¬ (y < m) := by rw [BitVec.lt_def]; omega
              simp [hge'] at hcond
              exact hnz hcond.symm
            let sd := decClockHOLFinite s
            have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG_s
            have hmeta := (evaluateHOLFiniteState_metadata sd countBody_cgr).1
            have hG_mid : GuestInv mid := by
              have hg := guestInv_evaluate sd countBody_cgr hGd
              rwa [hbr] at hg
            obtain ⟨T, hT1, hyT_le, hpy_lo, hpy_hi, hm_off, hm_cnt, hm_p, hm_len⟩ :=
              countBody_step_cgr sd P y m c hc_s hGd hp hy hm hc_cnt hlt (by rw [hbr])
            rw [hbr] at hm_off hm_cnt hm_p hm_len hmeta
            dsimp only at hm_off hm_cnt hm_p hm_len
            change mid.code = s.code at hmeta
            have hk_lt : (P + y).toNat - sourceBase < domainBytes := by
              have eD : domainBytes = heapEnd - sourceBase := rfl; omega
            let k_now : Fin domainBytes := ⟨(P + y).toNat - sourceBase, hk_lt⟩
            have hfresh : k_now ∉ vis := by
              intro hmem
              obtain ⟨d, hd_lt, _, _, hk_eq⟩ := hvis k_now hmem
              have hbv : P + d = P + y := BitVec.eq_of_toNat_eq (by change (P + y).toNat - sourceBase = _ at hk_eq; omega)
              have hdy : d = y := by
                have hsub := congrArg (fun x => -P + x) hbv
                simpa [← BitVec.add_assoc] using hsub
              subst hdy; omega
            have hle_ins : (insert k_now vis).card ≤ domainBytes := by
              simpa using Finset.card_le_univ (insert k_now vis)
            have hcard_ins := Finset.card_insert_of_notMem hfresh
            have hdb_lt : domainBytes < 2 ^ 64 := by decide
            have hc1_nat : (c + 1#64).toNat = c.toNat + 1 :=
              BitVec.toNat_add_of_lt (by change c.toNat + 1 < 2 ^ 64; omega)
            have hyT_nat : (y + T).toNat = y.toNat + T.toNat :=
              BitVec.toNat_add_of_lt (by have := m.isLt; omega)
            have hinv_mid : CountRetInv P m mid := by
              refine ⟨hmeta.trans hc_s, hG_mid, insert k_now vis, y + T, c + 1#64,
                hm_p, hm_off, hm_len, hm_cnt, by omega, ?_⟩
              intro k' hk'
              rcases Finset.mem_insert.mp hk' with rfl | hk'
              · exact ⟨y, by omega, hpy_lo, hpy_hi, rfl⟩
              · obtain ⟨d, hd, h1, h2, h3⟩ := hvis k' hk'
                exact ⟨d, by omega, h1, h2, h3⟩
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hinv_mid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl hbc.2
            | «break» => exact absurd rfl hbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact hinv
    · simp at hrun

private theorem countBody_no_return {F : Type} (st : PanSemStateFiniteExact 64 F) (rv : ValueHOL 64) :
    (evaluateHOLFiniteState st countBody_cgr).1 ≠ some (.returned rv) := by
  unfold countBody_cgr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
       .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]] with _ | vs
  · simp
  · simp only [hargs]
    rcases hlk : lookupCodeHOLFinite st.code.lookup (ofString "rlp_item_total") vs with _ | ⟨b', c', r'⟩
    · simp
    · simp only [hlk]
      by_cases hz : st.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite st c') b' with ⟨rc, cst⟩
        simp only [hcal]
        rcases rc with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
        split
        · dsimp only
          let u0 := setVarHOLFinite (ofString "total") w { cst with locals := st.locals }
          change (evaluateHOLFiniteState u0 _).1 ≠ some (.returned rv)
          rw [evaluateHOLFiniteState_seq_line780]
          have ha1 : ∀ x : Option (PanSemResultExact 64),
              (evaluateHOLFiniteState u0 (.assign .local (ofString "off")
                (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))).1 = x →
              x = none ∨ x = some .error := by
            intro x hx; rw [← hx, evaluateHOLFiniteState_assign]
            rcases @evalHOLExact 64 F _ u0.toExact (fun a => Classical.propDecidable (u0.memaddrs a))
                (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]) with _ | v1
            · exact Or.inr rfl
            · dsimp only
              by_cases hv : isValidValueHOLFinite u0 .local (ofString "off") v1 = true
              · rw [if_pos hv]; exact Or.inl rfl
              · rw [if_neg hv]; exact Or.inr rfl
          rcases h1 : evaluateHOLFiniteState u0 (.assign .local (ofString "off")
              (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) with ⟨r1, u1⟩
          rcases ha1 r1 (by rw [h1]) with rfl | rfl
          · dsimp only
            rw [evaluateHOLFiniteState_assign]
            rcases @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                (.op .add [.var .local (ofString "count"), .const 1]) with _ | v2
            · simp
            · dsimp only
              by_cases hv2 : isValidValueHOLFinite u1 .local (ofString "count") v2 = true
              · rw [if_pos hv2]; simp
              · rw [if_neg hv2]; simp
          · simp
        · simp

private theorem while_count_no_return {F : Type} (rv : ValueHOL 64) :
    ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
      (evaluateHOLFiniteState st (.while countCond_cgr countBody_cgr)).1 ≠ some (.returned rv) := by
  intro k
  induction k with
  | zero =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) countCond_cgr with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        have hk0 : st.clock = 0 := by omega
        rw [if_pos hk0]; simp
  | succ k ih =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) countCond_cgr with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        by_cases hk0 : st.clock = 0
        · rw [if_pos hk0]; simp
        · rw [if_neg hk0]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) countBody_cgr
          have hb_nr := countBody_no_return (decClockHOLFinite st) rv
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) countBody_cgr with ⟨r1, m1⟩
          simp only [hbr] at rem hb_nr ⊢
          cases r1 with
          | none => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
          | some r1 =>
            cases r1 with
            | «continue» => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
            | «break» => simp
            | returned v' =>
              intro heq; injection heq with heq'; injection heq' with heq''; subst heq''
              exact hb_nr rfl
            | _ => simp

private theorem rlp_list_count_ret_bound {F : Type}
    (s cpost : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64)) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_count") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_count, s.locals, .one))
    (hret : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count) =
      (some (.returned rv), cpost)) :
    ∃ wcnt : BitVec 64, rv = .val (.word wcnt) ∧ wcnt.toNat ≤ domainBytes := by
  obtain ⟨P, m, rfl, hp, hm⟩ := lookupCode_two_words (by decide) lookup_rlp_list_count hl
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_list_count =
      .dec (ofString "count") .one (.const 0)
        (.dec (ofString "off") .one (.const 0)
          (.seq (.while countCond_cgr countBody_cgr)
            (.return (.var .local (ofString "count"))))) := rfl
  have hret1 : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1 =
      some (.returned rv) := by rw [hret]
  clear hret
  rw [hbody] at hret1
  revert rv hret1
  change RetOK (fun rv => ∃ wcnt : BitVec 64, rv = .val (.word wcnt) ∧ wcnt.toNat ≤ domainBytes) s _
  refine R_dec (fun vcnt hvcnt _ => ?_)
  have hvcnt_eq : vcnt = .val (.word 0) := by simp [evalHOLExact] at hvcnt; exact hvcnt.symm
  subst hvcnt_eq
  refine R_dec (fun voff hvoff _ => ?_)
  have hvoff_eq : voff = .val (.word 0) := by simp [evalHOLExact] at hvoff; exact hvoff.symm
  subst hvoff_eq
  let s2 := setVarHOLFinite (ofString "off") (.val (.word 0))
    (setVarHOLFinite (ofString "count") (.val (.word 0)) s)
  have hinv2 : CountRetInv P m s2 := by
    refine ⟨hc, guestInv_setVar _ _ _ (guestInv_setVar _ _ _ hG), ∅, 0, 0, ?_, ?_, ?_, ?_, by simp, by simp⟩
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
        show ofString "off" ≠ ofString "p" by decide, show ofString "count" ≠ ofString "p" by decide]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm,
        show ofString "off" ≠ ofString "len" by decide, show ofString "count" ≠ ofString "len" by decide]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "off" ≠ ofString "count" by decide]
  refine R_seq ?_ (fun mid hmid => ?_)
  · intro rv hwhile_ret
    exact absurd hwhile_ret (while_count_no_return rv s2.clock s2 le_rfl)
  · obtain ⟨_, _, vis, _, c, _, _, _, hm_cnt, hcard, _⟩ := while_countRetInv P m s2.clock s2 mid le_rfl hinv2 hmid
    refine R_ret (fun v hv => ?_)
    simp [evalHOLExact, hm_cnt] at hv; subst hv
    have hle : vis.card ≤ domainBytes := by simpa using Finset.card_le_univ vis
    exact ⟨c, rfl, by omega⟩

private def ltsLoopBody : ProgHOL 64 :=
  .decCall (ofString "total") .one (ofString "rlp_item_total_unchecked")
    [.op .add [.var .local (ofString "p"), .var .local (ofString "off")]]
    (.seq
      (.store (.op .add [.var .local (ofString "arr"),
          .panop .mul [.var .local (ofString "i"), .const 16]])
        (.op .add [.var .local (ofString "p"), .var .local (ofString "off")]))
      (.seq
        (.store (.op .add [.var .local (ofString "arr"),
            .panop .mul [.var .local (ofString "i"), .const 16], .const 8])
          (.var .local (ofString "total")))
        (.seq
          (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))))

private def LtsInv {F : Type} (pw wcnt : BitVec 64) (t : PanSemStateFiniteExact 64 F) : Prop :=
  t.locals.lookup (ofString "arr") = some (.val (.word pw)) ∧
  t.locals.lookup (ofString "count") = some (.val (.word wcnt)) ∧
  WordLocals ["p", "off", "i"] t

private theorem lts_addr_in_heap {globN_hp : Nat} (pw wcnt wi : BitVec 64)
    (hcnt_dom : wcnt.toNat ≤ domainBytes)
    (hp_lo : globN_hp ≤ pw.toNat)
    (halloc_hi : pw.toNat + ((wcnt * 16#64).toNat + 7) / 8 * 8 ≤ heapLimit)
    (hlt : wi < wcnt) :
    globN_hp ≤ (pw + wi * 16#64).toNat ∧
    (pw + wi * 16#64).toNat + 8 ≤ heapLimit ∧
    globN_hp ≤ (pw + (wi * 16#64) + 8#64).toNat ∧
    (pw + (wi * 16#64) + 8#64).toNat + 8 ≤ heapLimit := by
  have hdb : domainBytes = 31104957928 := by decide
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hlt_nat : wi.toNat < wcnt.toNat := BitVec.lt_def.mp hlt
  have hcnt16 : (wcnt * 16#64).toNat = wcnt.toNat * 16 :=
    BitVec.toNat_mul_of_lt (by change wcnt.toNat * 16 < 2 ^ 64; omega)
  have hwi16 : (wi * 16#64).toNat = wi.toNat * 16 :=
    BitVec.toNat_mul_of_lt (by change wi.toNat * 16 < 2 ^ 64; omega)
  have halign : ((wcnt * 16#64).toNat + 7) / 8 * 8 = wcnt.toNat * 16 := by
    rw [hcnt16]; omega
  rw [halign] at halloc_hi
  have hp_wi16 : (pw + wi * 16#64).toNat = pw.toNat + wi.toNat * 16 := by
    rw [BitVec.toNat_add_of_lt (by rw [hwi16]; omega), hwi16]
  have hp_wi16_8 : (pw + (wi * 16#64) + 8#64).toNat = pw.toNat + wi.toNat * 16 + 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [hp_wi16]; change pw.toNat + wi.toNat * 16 + 8 < 2 ^ 64; omega), hp_wi16]
    rfl
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem worldEff_while_cond {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (cond : ExpHOL 64) {body : ProgHOL 64}
    (Inv : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, Inv t → Inv (decClockHOLFinite t))
    (hb : ∀ t (cw : BitVec 64),
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s (decClockHOLFinite t) Rl B gw → Inv (decClockHOLFinite t) →
      (evaluateHOLFiniteState (decClockHOLFinite t) body).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite t) body).1 →
      WorldEff s (evaluateHOLFiniteState (decClockHOLFinite t) body).2 Rl B gw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite t) body).1 = some .continue) →
        Inv (evaluateHOLFiniteState (decClockHOLFinite t) body).2)) :
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
            obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
              (by rw [hbo]; simp) (by rw [hbo]; exact Or.inl rfl)
            rw [hbo] at heff_b hinv_b
            exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inl rfl)) hnt hcr
          | some r1 =>
            cases r1 with
            | «continue» =>
              obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hbo] at heff_b hinv_b
              exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inr rfl)) hnt hcr
            | «break» =>
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inl rfl))
              rw [hbo] at heff_b; exact heff_b
            | timeOut => exact absurd rfl hnt
            | returned v =>
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hbo] at heff_b; exact heff_b
            | exception eid ev =>
              have hres_e : Resumes (some (.exception eid ev)) := by
                rcases hcr with h | h | h | hr <;> [cases h; cases h; cases h; exact hr]
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr hres_e)))
              rw [hbo] at heff_b; exact heff_b
            | error =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h
            | finalFfi _ =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h

private theorem eval_assign_flowing_keeps {F : Type}
    (u : PanSemStateFiniteExact 64 F) (nm : MlS) (e : ExpHOL 64) (key : MlS)
    (hk : key ≠ nm)
    (hf : (evaluateHOLFiniteState u (.assign .local nm e)).1 = none ∨
      (evaluateHOLFiniteState u (.assign .local nm e)).1 = some .continue) :
    (evaluateHOLFiniteState u (.assign .local nm e)).2.locals.lookup key = u.locals.lookup key := by
  revert hf
  rw [evaluateHOLFiniteState_assign]
  rcases hv : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e with _ | val
  · simp
  · dsimp only
    by_cases hval : isValidValueHOLFinite u .local nm val = true
    · rw [if_pos hval]
      intro _
      simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
    · rw [if_neg hval]; simp

private theorem eval_store_flowing_inv {F : Type}
    (u : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) {rest : ProgHOL 64}
    (hf : (evaluateHOLFiniteState u (.seq (.store d e) rest)).1 = none ∨
      (evaluateHOLFiniteState u (.seq (.store d e) rest)).1 = some .continue) :
    ∃ u1, evaluateHOLFiniteState u (.store d e) = (none, u1) ∧ u1.locals = u.locals ∧
      ((evaluateHOLFiniteState u1 rest).1 = none ∨ (evaluateHOLFiniteState u1 rest).1 = some .continue) ∧
      (evaluateHOLFiniteState u (.seq (.store d e) rest)).2 = (evaluateHOLFiniteState u1 rest).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hf ⊢
  rcases hs : evaluateHOLFiniteState u (.store d e) with ⟨r, u1⟩
  rw [hs] at hf
  cases r with
  | none =>
    have hloc : u1.locals = u.locals := by
      have hcf := (evaluate_store_control_frame u d e).2.1
      rwa [hs] at hcf
    exact ⟨u1, rfl, hloc, hf, rfl⟩
  | some r =>
    exfalso
    have hse : r = .error := by
      rw [evaluateHOLFiniteState_store] at hs
      revert hs; repeat' split
      all_goals (intro hs; injection hs with hs1 _; cases hs1 <;> rfl)
    subst hse
    rcases hf with hf | hf <;> simp at hf

private theorem ltsLoopBody_keeps_arr_count {F : Type}
    (t : PanSemStateFiniteExact 64 F) (pw wcnt : BitVec 64)
    (harr : t.locals.lookup (ofString "arr") = some (.val (.word pw)))
    (hcnt : t.locals.lookup (ofString "count") = some (.val (.word wcnt)))
    (hf : (evaluateHOLFiniteState t ltsLoopBody).1 = none ∨
      (evaluateHOLFiniteState t ltsLoopBody).1 = some .continue) :
    (evaluateHOLFiniteState t ltsLoopBody).2.locals.lookup (ofString "arr") = some (.val (.word pw)) ∧
    (evaluateHOLFiniteState t ltsLoopBody).2.locals.lookup (ofString "count") = some (.val (.word wcnt)) := by
  have heq : ∀ key : MlS, key ≠ ofString "total" → key ≠ ofString "off" → key ≠ ofString "i" →
      (evaluateHOLFiniteState t ltsLoopBody).2.locals.lookup key = t.locals.lookup key := by
    intro key hk1 hk2 hk3
    revert hf
    unfold ltsLoopBody
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.op .add [.var .local (ofString "p"), .var .local (ofString "off")]] with _ | vs
    · simp
    · simp only [hargs]
      rcases hlk : lookupCodeHOLFinite t.code.lookup (ofString "rlp_item_total_unchecked") vs with _ | ⟨b', c', r'⟩
      · simp
      · simp only [hlk]
        by_cases hz : t.clock = 0
        · simp [hz]
        · simp only [hz, ↓reduceIte]
          rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite t c') b' with ⟨rc, st⟩
          simp only [hcal]
          rcases rc with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
          split
          · intro hf
            dsimp only
            rw [resVarEq_lookup_local, if_neg hk1]
            let u0 := setVarHOLFinite (ofString "total") w { st with locals := t.locals }
            have hu0_k : u0.locals.lookup key = t.locals.lookup key := by
              simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk1]
            change (evaluateHOLFiniteState u0 _).1 = _ ∨ (evaluateHOLFiniteState u0 _).1 = _ at hf
            change (evaluateHOLFiniteState u0 _).2.locals.lookup key = t.locals.lookup key
            obtain ⟨u1, _, hu1_loc, hf1, heq1⟩ := eval_store_flowing_inv u0 _ _ hf
            rw [heq1]
            obtain ⟨u2, _, hu2_loc, hf2, heq2⟩ := eval_store_flowing_inv u1 _ _ hf1
            rw [heq2]
            rw [evaluateHOLFiniteState_seq_line780] at hf2 ⊢
            rcases ha1 : evaluateHOLFiniteState u2 (.assign .local (ofString "off")
                (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) with ⟨ra1, u3⟩
            rw [ha1] at hf2
            cases ra1 with
            | some _ =>
              exfalso
              have hbad : (evaluateHOLFiniteState u2 (.assign .local (ofString "off")
                  (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))).1 ≠ some .continue := by
                rw [evaluateHOLFiniteState_assign]; split <;> [simp; (split <;> simp)]
              rw [ha1] at hbad
              rcases hf2 with hf2 | hf2 <;> [cases hf2; exact hbad hf2]
            | none =>
              have hu3_k : u3.locals.lookup key = u2.locals.lookup key := by
                have := eval_assign_flowing_keeps u2 (ofString "off")
                  (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]) key hk2
                  (by rw [ha1]; exact Or.inl rfl)
                rwa [ha1] at this
              have hu4_k := eval_assign_flowing_keeps u3 (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1#64]) key hk3 hf2
              dsimp only
              rw [hu4_k, hu3_k, hu2_loc, hu1_loc, hu0_k]
          · simp
  exact ⟨(heq (ofString "arr") (by decide) (by decide) (by decide)).trans harr,
         (heq (ofString "count") (by decide) (by decide) (by decide)).trans hcnt⟩

private theorem lookupCode_two_words_any {fname p1 p2 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, retShape))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, retShape)) :
    ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, rfl, ?_, ?_⟩ <;> (rw [← hL]; simp [hne, Ne.symm hne])
  · simp at hx

theorem worldEff_rlp_list_to_slices {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_to_slices") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices, s.locals, .comb [.one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices)).2
      [] wsBufs wsGw := by
  obtain ⟨wp, wlen, rfl, hp_lk, _⟩ := lookupCode_two_words_any (by decide) lookup_rlp_list_to_slices hl
  have heff0 : WorldEff s s [] wsBufs wsGw := WorldEff.refl s [] wsBufs wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_list_to_slices =
      .decCall (ofString "count") .one (ofString "rlp_list_count")
        [.var .local (ofString "p"), .var .local (ofString "len")]
        (.decCall (ofString "arr") .one (ofString "alloc")
          [.panop .mul [.var .local (ofString "count"), .const 16]]
          (.dec (ofString "i") .one (.const 0)
            (.dec (ofString "off") .one (.const 0)
              (.seq
                (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count")))
                  ltsLoopBody)
                (.return (.rstruct [.var .local (ofString "arr"), .var .local (ofString "count")])))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "count") .one (ofString "rlp_list_count") _ _ _ _ lookup_rlp_list_count
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_list_count (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_B_sub ws_no_gb)
    (fun callee cvals rv cpost _ hlc hrun_c _ heff_cp hnt_k1 hcr_k1 => ?_)
    hnt (Or.inr (Or.inr (Or.inr hres)))
  obtain ⟨wcnt, rfl, hcnt_dom⟩ :=
    rlp_list_count_ret_bound (callEntryStateHOLFinite s callee) cpost cvals rv
      heff0.code (guestInv_callEntry s callee heff0.arena.1)
      (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hrun_c
  let m1 := setVarHOLFinite (ofString "count") (.val (.word wcnt)) { cpost with locals := s.locals }
  have heff_m1 : WorldEff s m1 [] wsBufs wsGw := heff_cp.locals_clock _ _
  have hm1_cnt : m1.locals.lookup (ofString "count") = some (.val (.word wcnt)) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_lk,
      show ofString "count" ≠ ofString "p" by decide]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "arr") _ hnt_k1 hcr_k1
    (fun pw nw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hpw_lo_s hpw_add hhp_m2_hi _ hnt_k2 hcr_k2 => ?_)
  have hnw_eq : nw = wcnt * 16#64 := by
    simp [evalHOLExact, evalListHOLExact, hm1_cnt, panOpHOL, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have halloc_hi : pw.toNat + ((wcnt * 16#64).toNat + 7) / 8 * 8 ≤ heapLimit := by omega
  refine worldEff_dec heff_m2 _ _ _ hnt_k2 hcr_k2 (fun vi hvi _ hnt_k3 hcr_k3 => ?_)
  have hvi_eq : vi = .val (.word 0) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  let m3 := setVarHOLFinite (ofString "i") (.val (.word 0)) m2
  have heff_m3 : WorldEff s m3 [] wsBufs wsGw := heff_m2.locals_clock _ _
  refine worldEff_dec heff_m3 _ _ _ hnt_k3 hcr_k3 (fun voff hvoff _ hnt_k4 hcr_k4 => ?_)
  have hvoff_eq : voff = .val (.word 0) := by simp [evalHOLExact] at hvoff; exact hvoff.symm
  subst hvoff_eq
  let m4 := setVarHOLFinite (ofString "off") (.val (.word 0)) m3
  have heff_m4 : WorldEff s m4 [] wsBufs wsGw := heff_m3.locals_clock _ _
  have hinv_m4 : LtsInv pw wcnt m4 := by
    refine ⟨?_, ?_, ?_⟩
    · simp [m4, m3, setVarHOLFinite, hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "off" ≠ ofString "arr" by decide, show ofString "i" ≠ ofString "arr" by decide]
    · simp [m4, m3, setVarHOLFinite, hm2_loc, hm1_cnt, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "off" ≠ ofString "count" by decide, show ofString "i" ≠ ofString "count" by decide,
        show ofString "arr" ≠ ofString "count" by decide]
    · intro nm hnm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
      rcases hnm with rfl | rfl | rfl
      · exact ⟨wp, by simp [m4, m3, setVarHOLFinite, hm2_loc, hm1_p, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "off" ≠ ofString "p" by decide, show ofString "i" ≠ ofString "p" by decide,
          show ofString "arr" ≠ ofString "p" by decide]⟩
      · exact ⟨0, by simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
      · exact ⟨0, by simp [m4, m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "off" ≠ ofString "i" by decide]⟩
  have hws_lts : wsafe ltsLoopBody = true := by decide
  refine worldEff_seq hnt_k4 hcr_k4
    (fun hnt_w hcr_w =>
      worldEff_while_cond _ (LtsInv pw wcnt)
        (fun _ hinv => hinv)
        (fun t0 cw hcond hnz heff_t hinv_t hnt_b hcr_b => ?_)
        m4.clock m4 rfl heff_m4 hinv_m4 hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)
  set t := decClockHOLFinite t0
  obtain ⟨ht_arr, ht_cnt, ht_wloc⟩ := hinv_t
  obtain ⟨wp_t, htp⟩ := ht_wloc "p" (by simp)
  obtain ⟨woff_t, htoff⟩ := ht_wloc "off" (by simp)
  obtain ⟨wi_t, hti⟩ := ht_wloc "i" (by simp)
  have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi_t)) := hti
  have ht0_cnt : t0.locals.lookup (ofString "count") = some (.val (.word wcnt)) := ht_cnt
  have hlt_i : wi_t < wcnt := by
    rw [evalHOLFinite_eq_toExact] at hcond
    simp [evalHOLExact, ht0_i, ht0_cnt, Compiler.Encoders.Asm.wordCmpHOL] at hcond
    by_contra hge
    simp [hge] at hcond
    exact hnz hcond.symm
  obtain ⟨ha0_lo, ha0_hi, ha8_lo, ha8_hi⟩ :=
    lts_addr_in_heap pw wcnt wi_t hcnt_dom hpw_lo_s halloc_hi hlt_i
  refine ⟨?_, fun hf => ?_⟩
  · dsimp only [ltsLoopBody] at hnt_b hcr_b ⊢
    refine worldEff_decCall_ro heff_t InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_item_total_unchecked
      (ofString "total") .one _ hnt_b hcr_b (fun rvt cpost hsh_rvt hcpost hnt_s1 hcr_s1 => ?_)
    have hrvt_w : ∃ wt : BitVec 64, rvt = .val (.word wt) := by
      rcases rvt with ⟨⟨wt⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_rvt
      exact ⟨wt, rfl⟩
    obtain ⟨wt, rfl⟩ := hrvt_w
    let u0 := setVarHOLFinite (ofString "total") (.val (.word wt)) { cpost with locals := t.locals }
    have heff_u0 : WorldEff s u0 [] wsBufs wsGw := (heff_t.of_readOnly hcpost).locals_clock _ _
    have hu0_arr : u0.locals.lookup (ofString "arr") = some (.val (.word pw)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_arr,
        show ofString "total" ≠ ofString "arr" by decide]
    have hu0_i : u0.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hti,
        show ofString "total" ≠ ofString "i" by decide]
    have hu0_p : u0.locals.lookup (ofString "p") = some (.val (.word wp_t)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htp,
        show ofString "total" ≠ ofString "p" by decide]
    have hu0_off : u0.locals.lookup (ofString "off") = some (.val (.word woff_t)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htoff,
        show ofString "total" ≠ ofString "off" by decide]
    have hu0_tot : u0.locals.lookup (ofString "total") = some (.val (.word wt)) := by
      simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_seq hnt_s1 hcr_s1
      (fun _ _ => worldEff_store_word heff_u0 _ _
        (fun v hv => by
          simp [evalHOLExact, evalListHOLExact, hu0_p, hu0_off, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
          exact ⟨_, hv.symm⟩)
        (fun x hx _ => by
          simp [evalHOLExact, evalListHOLExact, hu0_arr, hu0_i, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
          subst hx
          exact Or.inr (Or.inr (Or.inr ⟨ha0_lo, ha0_hi⟩))))
      (fun u1 hu1 heff_u1 hnt_s2 hcr_s2 => ?_)
    have hu1_loc : u1.locals = u0.locals := by
      have hcf := (evaluate_store_control_frame u0
        (.op .add [.var .local (ofString "arr"), .panop .mul [.var .local (ofString "i"), .const 16]])
        (.op .add [.var .local (ofString "p"), .var .local (ofString "off")])).2.1
      rwa [hu1] at hcf
    refine worldEff_seq hnt_s2 hcr_s2
      (fun _ _ => worldEff_store_word heff_u1 _ _
        (fun v hv => by
          simp [evalHOLExact, hu1_loc, hu0_tot] at hv
          exact ⟨_, hv.symm⟩)
        (fun x hx _ => by
          simp [evalHOLExact, evalListHOLExact, hu1_loc, hu0_arr, hu0_i, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
          subst hx
          have hadd_assoc : pw + (wi_t * 16#64 + 8#64) = pw + wi_t * 16#64 + 8#64 :=
            (BitVec.add_assoc pw (wi_t * 16#64) 8#64).symm
          rw [hadd_assoc]
          exact Or.inr (Or.inr (Or.inr ⟨ha8_lo, ha8_hi⟩))))
      (fun u2 _ heff_u2 hnt_s3 hcr_s3 =>
        worldEff_seq hnt_s3 hcr_s3
          (fun _ _ => worldEff_assign_local heff_u2 _ _)
          (fun u3 _ heff_u3 _ _ => worldEff_assign_local heff_u3 _ _))
  · obtain ⟨hkeep_arr, hkeep_cnt⟩ := ltsLoopBody_keeps_arr_count t pw wcnt ht_arr ht_cnt hf
    exact ⟨hkeep_arr, hkeep_cnt,
      wordLocals_flowing hws_lts ht_wloc (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩

private theorem call0_or_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname : MlS) (args : List (ExpHOL 64))
    (hcr : ContOrRes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
    Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 := by
  rcases hcr with h | h | h | hr
  · exact Or.inl h
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exact Or.inr hr

private theorem worldEff_call0_funByteEff {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    {fname : MlS} {argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl}
    (hf : FunByteEff fname argR)
    (args : List (ExpHOL 64)) (Sub : List Ivl)
    (hsub_args : ∀ vals,
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      ∀ i ∈ argR vals cur.globals, 0 < i.2 → ∃ j ∈ Sub, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hsub_world : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit))
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).2 Rl B gw :=
  h.of_byteEff (call0_byteEff hf cur args Sub h.code h.arena.1 hsub_args hnt (call0_or_resumes cur fname args hcr))
    hsub_world

private def dafBalLoopBody : ProgHOL 64 :=
  .dec (ofString "pos") .one
    (.op .sub [.op .sub [.rfield 2 (.var .local (ofString "f1")), .const 1#64], .var .local (ofString "i")])
    (.dec (ofString "lp") .one
      (.op .add [.var .local (ofString "acct_out"), .const 8#64,
        .panop .mul [.shift .lsr (.var .local (ofString "pos")) (.const 3#64), .const 8#64]])
      (.seq
        (.store (.var .local (ofString "lp"))
          (.op .or [.load .one (.var .local (ofString "lp")),
            .shift .lsl
              (.loadByte (.op .add [.rfield 1 (.var .local (ofString "f1")), .var .local (ofString "i")]))
              (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64])]))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))

private def DafBalInv {F : Type} (wa f1_0 f1_1 f1_2 f1_3 : BitVec 64)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  t.locals.lookup (ofString "acct_out") = some (.val (.word wa)) ∧
  t.locals.lookup (ofString "f1") =
    some (.rStruct [.val (.word f1_0), .val (.word f1_1), .val (.word f1_2), .val (.word f1_3)]) ∧
  (∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)))

private theorem dafBalLoopBody_keeps {F : Type}
    (t : PanSemStateFiniteExact 64 F) (key : MlS)
    (hk_pos : key ≠ ofString "pos") (hk_lp : key ≠ ofString "lp") (hk_i : key ≠ ofString "i")
    (hf : (evaluateHOLFiniteState t dafBalLoopBody).1 = none ∨
      (evaluateHOLFiniteState t dafBalLoopBody).1 = some .continue) :
    (evaluateHOLFiniteState t dafBalLoopBody).2.locals.lookup key = t.locals.lookup key := by
  have hav : avoidsLocal key dafBalLoopBody = true := by
    simp [dafBalLoopBody, avoidsLocal, beq_iff_eq, Ne.symm hk_pos, Ne.symm hk_lp, Ne.symm hk_i]
  exact evaluate_avoidsLocal_flowing key dafBalLoopBody hav t
    (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))

private theorem daf_store_val_one {F : Type} (cur : PanSemStateFiniteExact 64 F) (e : ExpHOL 64)
    (hform : (∃ c, e = .const c) ∨ (∃ nm, e = .var .local nm ∧ ∃ w, cur.locals.lookup nm = some (.val (.word w))) ∨
      (∃ gnm : String, gnm ∈ guestGlobalNames ∧ e = .var .global (ofString gnm) ∧ GlobalsWord cur) ∨
      (∃ a b, e = .op .or [a, b])) :
    ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  rcases hform with ⟨c, rfl⟩ | ⟨nm, rfl, w, hw⟩ | ⟨gnm, hgnm, rfl, hgw⟩ | ⟨a, b, rfl⟩
  · simp [evalHOLExact] at hv; exact ⟨_, hv.symm⟩
  · simp [evalHOLExact, hw] at hv; exact ⟨_, hv.symm⟩
  · simp only [evalHOLExact, toExact] at hv
    obtain ⟨w, hw⟩ := hgw gnm hgnm
    unfold GlobalWord at hw
    rw [hw] at hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
  · simp only [evalHOLExact, evalListHOLExact] at hv
    rcases ha : @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) a with _ | va
    · rw [ha] at hv; simp at hv
    · rw [ha] at hv
      rcases hb : @evalHOLExact 64 F _ cur.toExact (fun x => Classical.propDecidable (cur.memaddrs x)) b with _ | vb
      · rw [hb] at hv; simp at hv
      · rw [hb] at hv; dsimp only at hv
        split at hv <;> simp [wordOpHOL] at hv
        obtain ⟨w, _, hw⟩ := hv
        exact ⟨w, hw.symm⟩

private theorem mpt_fail_noret_cgr {F : Type} (st : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_mpt_fail)).1 ≠ some (.returned v) := by
  have hb : sourceFnBody Guest.Software.guestFn_mpt_fail =
      .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
  have hraise : ∀ w, (evaluateHOLFiniteState st (.raise (ofString "MptErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ some (.returned w) ∧
      (evaluateHOLFiniteState st (.raise (ofString "MptErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ none := by
    intro w
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  rw [hb, evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState st (.raise (ofString "MptErr") (.var .local (ofString "code")) :
    ProgHOL 64) with ⟨r, mid⟩
  rw [hr] at hraise
  cases r with
  | none => exact absurd rfl (hraise v).2
  | some _ => dsimp only; exact (hraise v).1

private theorem handledCall_mpt_fail_keeps_local {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F)
    (hc : cur.code = originalRuntimeCode)
    (destVar eid evar fname : MlS) (fargs args : List (ExpHOL 64))
    (key : MlS) (hne_dest : key ≠ destVar)
    (hrun : evaluateHOLFiniteState cur
      (.call (some (some (.local, destVar),
        some (eid, evar, .call (some (none, none)) (ofString "mpt_fail") fargs))) fname args) = (none, mid)) :
    mid.locals.lookup key = cur.locals.lookup key := by
  have hlook_mf : originalRuntimeCode.lookup (ofString "mpt_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
    lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_mpt_fail) rfl
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vs
  · rw [hargs] at hrun; cases hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hlk : lookupCodeHOLFinite cur.code.lookup fname vs with _ | ⟨b', c', r'⟩
    · rw [hlk] at hrun; cases hrun
    · rw [hlk] at hrun; dsimp only at hrun
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hrun; cases hrun
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite cur c') b').1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite cur c') b' with ⟨res_b, pb⟩
        rw [hb] at hrun hmeta
        change pb.code = cur.code at hmeta
        cases res_b with
        | none => cases hrun
        | some rb =>
          cases rb with
          | returned rv =>
            dsimp only at hrun
            by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) r' = true
            · rw [if_pos hsh] at hrun
              by_cases hv : isValidValueHOLExact cur.toExact .local destVar rv = true
              · rw [if_pos hv] at hrun
                injection hrun with _ hm; rw [← hm]
                simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne_dest]
              · rw [if_neg hv] at hrun; cases hrun
            · rw [if_neg hsh] at hrun; cases hrun
          | exception exId exVal =>
            dsimp only at hrun
            by_cases he : exId = eid
            · subst exId; rw [if_pos rfl] at hrun
              rcases hes : cur.eshapes.lookup eid with _ | esh
              · rw [hes] at hrun; cases hrun
              · rw [hes] at hrun; dsimp only at hrun
                by_cases hok : (shapeEqHOL (shapeOfHOLExact exVal) esh &&
                    isValidValueHOLExact cur.toExact .local evar exVal) = true
                · simp only [hok, ↓reduceIte] at hrun
                  let hst := setVarHOLFinite evar exVal { pb with locals := cur.locals }
                  have hhst_code : hst.code = originalRuntimeCode := hmeta.trans hc
                  have hfst : (evaluateHOLFiniteState hst (.call (some (none, none)) (ofString "mpt_fail") fargs)).1 = none :=
                    congrArg Prod.fst hrun
                  exfalso
                  rw [evaluateHOLFiniteState_call] at hfst
                  rcases hf_a : evalListHOLFinite hst (h := fun a => Classical.propDecidable (hst.memaddrs a)) fargs with _ | fvs
                  · rw [hf_a] at hfst; simp at hfst
                  · rw [hf_a] at hfst; dsimp only at hfst
                    rcases hf_l : lookupCodeHOLFinite hst.code.lookup (ofString "mpt_fail") fvs with _ | ⟨fb, fc, fr⟩
                    · rw [hf_l] at hfst; simp at hfst
                    · rw [hf_l] at hfst; dsimp only at hfst
                      have hfb := lookupCodeHOLFinite_installed_body hst.code.lookup _ _ _ fb _ fr fvs fc
                        (by rw [hhst_code]; exact hlook_mf) hf_l
                      subst hfb
                      by_cases hfz : hst.clock = 0
                      · rw [if_pos hfz] at hfst; simp at hfst
                      · rw [if_neg hfz] at hfst
                        have hnr := mpt_fail_noret_cgr (callEntryStateHOLFinite hst fc)
                        rcases hfrun : evaluateHOLFiniteState (callEntryStateHOLFinite hst fc)
                            (sourceFnBody Guest.Software.guestFn_mpt_fail) with ⟨fr_r, _⟩
                        rw [hfrun] at hfst hnr
                        cases fr_r with
                        | none => simp at hfst
                        | some fr1 =>
                          cases fr1 with
                          | returned fv => exact hnr fv rfl
                          | _ => simp at hfst
                · simp only [hok, Bool.false_eq_true, ↓reduceIte] at hrun; cases hrun
            · rw [if_neg he] at hrun; cases hrun
          | _ => cases hrun

private theorem daf_ite_mpt_fail_keeps {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F)
    (hc : cur.code = originalRuntimeCode)
    (cond : ExpHOL 64) (codeExp : ExpHOL 64)
    (hrun : evaluateHOLFiniteState cur
      (.ite cond (.call (some (none, none)) (ofString "mpt_fail") [codeExp]) .skip) = (none, mid)) :
    mid.locals = cur.locals ∧
    @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond =
      some (.val (.word 0)) := by
  have hlook_mf : originalRuntimeCode.lookup (ofString "mpt_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
    lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_mpt_fail) rfl
  rw [evaluateHOLFiniteState_ite] at hrun
  rcases hcv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
  · rw [hcv] at hrun; simp at hrun
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> (rw [hcv] at hrun; try simp at hrun)
    by_cases hw0 : cw = 0#64
    · subst hw0; rw [if_pos rfl] at hrun
      injection hrun with _ hm; subst hm; exact ⟨rfl, rfl⟩
    · rw [if_neg hw0] at hrun
      exfalso
      rw [evaluateHOLFiniteState_call] at hrun
      rcases ha : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [codeExp] with _ | fvs
      · rw [ha] at hrun; simp at hrun
      · rw [ha] at hrun; dsimp only at hrun
        rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "mpt_fail") fvs with _ | ⟨fb, fc, fr⟩
        · rw [hl] at hrun; simp at hrun
        · rw [hl] at hrun; dsimp only at hrun
          have hfb := lookupCodeHOLFinite_installed_body cur.code.lookup _ _ _ fb _ fr fvs fc
            (by rw [hc]; exact hlook_mf) hl
          subst hfb
          by_cases hz : cur.clock = 0
          · rw [if_pos hz] at hrun; simp at hrun
          · rw [if_neg hz] at hrun
            have hnr := mpt_fail_noret_cgr (callEntryStateHOLFinite cur fc)
            rcases hfrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur fc)
                (sourceFnBody Guest.Software.guestFn_mpt_fail) with ⟨fr_r, _⟩
            rw [hfrun] at hrun hnr
            cases fr_r with
            | none => simp at hrun
            | some fr1 =>
              cases fr1 with
              | returned fv => exact hnr fv rfl
              | _ => simp at hrun

private theorem shape_four_words (v : ValueHOL 64)
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true) :
    ∃ a b c d : BitVec 64,
      v = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at h
  · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h)
    rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;>
      rcases v2 with ⟨⟨c⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨d⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    exact ⟨a, b, c, d, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem shape_three_words (v : ValueHOL 64)
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one]) = true) :
    ∃ a b c : BitVec 64,
      v = .rStruct [.val (.word a), .val (.word b), .val (.word c)] := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at h
  · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩⟩ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h)
    rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;>
      rcases v2 with ⟨⟨c⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    exact ⟨a, b, c, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem shape_two_words (v : ValueHOL 64)
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one]) = true) :
    ∃ a b : BitVec 64,
      v = .rStruct [.val (.word a), .val (.word b)] := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at h
  · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h)
    rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    exact ⟨a, b, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem daf_balance_addr {globN_hp : Nat} (wa f1_2 wi : BitVec 64)
    (ha_lo : globN_hp ≤ wa.toNat) (ha_hi : wa.toNat + 56 ≤ heapLimit)
    (hf1_le : f1_2.toNat ≤ 32) (hlt : wi < f1_2) :
    let wpos := f1_2 - 1#64 - wi
    let wlp := wa + 8#64 + ((wpos >>> 3) * 8#64)
    globN_hp ≤ wlp.toNat ∧ wlp.toNat + 8 ≤ heapLimit := by
  intro wpos wlp
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hlt_nat : wi.toNat < f1_2.toNat := BitVec.lt_def.mp hlt
  have hf1_sub1 : (f1_2 - 1#64).toNat = f1_2.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ f1_2.toNat; omega)]
    rfl
  have hwpos_nat : wpos.toNat = f1_2.toNat - 1 - wi.toNat := by
    dsimp only [wpos]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hf1_sub1]; omega), hf1_sub1]
  have hwpos_lt : wpos.toNat < 32 := by omega
  have hlsr_nat : (wpos >>> 3).toNat = wpos.toNat / 8 := by
    change wpos.toNat >>> 3 = wpos.toNat / 8
    rw [Nat.shiftRight_eq_div_pow]
  have hmul_nat : ((wpos >>> 3) * 8#64).toNat = (wpos.toNat / 8) * 8 := by
    rw [BitVec.toNat_mul_of_lt (by rw [hlsr_nat]; change (wpos.toNat / 8) * 8 < 2 ^ 64; omega), hlsr_nat]
    rfl
  have hwa8 : (wa + 8#64).toNat = wa.toNat + 8 :=
    BitVec.toNat_add_of_lt (by change wa.toNat + 8 < 2 ^ 64; omega)
  have hwlp_nat : wlp.toNat = wa.toNat + 8 + (wpos.toNat / 8) * 8 := by
    dsimp only [wlp]
    rw [BitVec.toNat_add_of_lt (by rw [hwa8, hmul_nat]; omega), hwa8, hmul_nat]
  exact ⟨by omega, by omega⟩

theorem worldEff_decode_account_from_leaf {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64)) (wa : BitVec 64)
    (heff_cur : WorldEff s0 cur [] wsBufs wsGw)
    (hwa_lo : globN s0 "heap_ptr" ≤ wa.toNat)
    (hwa_hi : wa.toNat + 56 ≤ heapLimit)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "decode_account_from_leaf") vals =
      some (sourceFnBody Guest.Software.guestFn_decode_account_from_leaf, cur.locals, .one))
    (hwa_lk : cur.locals.lookup (ofString "acct_out") = some (.val (.word wa)))
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_decode_account_from_leaf)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_decode_account_from_leaf)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_decode_account_from_leaf)).2
      [] wsBufs wsGw := by
  have _ := hl
  have hAR0 := heff_cur.arena -- note: for `s0`, wait: do we need `ArenaReady s0`? No! `WorldEff` only uses `heff_cur`!
  have hmf := InitECandidate.Solver.Wave8GuestInv.R13.ro_mpt_fail
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hwa0 : (wa + 0#64).toNat = wa.toNat := by simp
  have hwa8 : (wa + 8#64).toNat = wa.toNat + 8 := BitVec.toNat_add_of_lt (by change wa.toNat + 8 < 2 ^ 64; omega)
  have hwa40 : (wa + 40#64).toNat = wa.toNat + 40 := BitVec.toNat_add_of_lt (by change wa.toNat + 40 < 2 ^ 64; omega)
  have hwa48 : (wa + 48#64).toNat = wa.toNat + 48 := BitVec.toNat_add_of_lt (by change wa.toNat + 48 < 2 ^ 64; omega)
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_decode_account_from_leaf,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  -- `dec it`
  refine worldEff_dec heff_cur _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vit _ _ hnt1 hcr1 => ?_)
  let m1 := setVarHOLFinite (ofString "it") vit cur
  have heff_m1 : WorldEff s0 m1 [] wsBufs wsGw := heff_cur.locals_clock _ _
  -- `dec e`
  refine worldEff_dec heff_m1 _ _ _ hnt1 hcr1 (fun ve _ _ hnt2 hcr2 => ?_)
  let m2 := setVarHOLFinite (ofString "e") ve m1
  have heff_m2 : WorldEff s0 m2 [] wsBufs wsGw := heff_m1.locals_clock _ _
  have hm2_ao : m2.locals.lookup (ofString "acct_out") = some (.val (.word wa)) := by
    simp [m2, m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwa_lk,
      show ofString "e" ≠ ofString "acct_out" by decide, show ofString "it" ≠ ofString "acct_out" by decide]
  -- `seq`: handled call to `rlp_decode_fully`
  refine worldEff_seq hnt2 hcr2
    (fun hnt_hc hcr_hc =>
      worldEff_handledCall heff_m2 (some (.local, ofString "it")) (ofString "RlpErr") (ofString "e") _
        (ofString "rlp_decode_fully") _
        (fun _ _ h => by injection h with h'; exact (Prod.mk.inj h').1.symm) (by decide)
        _ _ _ lookup_rlp_decode_fully
        (fun callee cvals _ hlc hnt_cb hres_cb =>
          heff_m2.trans_noBuf
            (WorldEff.from_locals_clock
              (worldEff_rlp_decode_fully (callEntryStateHOLFinite m2 callee) cvals
                heff_m2.code (localsFree_arenaReady m2 callee _ heff_m2.arena)
                (by simpa [heff_m2.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
            ws_B_sub ws_no_gb)
        (fun exVal cpost heff_cp hnt_h hcr_h =>
          worldEff_call0_ro (heff_cp.locals_clock _ _) hmf _ hnt_h hcr_h)
        hnt_hc hcr_hc)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_ao : m3.locals.lookup (ofString "acct_out") = some (.val (.word wa)) :=
    (handledCall_mpt_fail_keeps_local m2 m3 heff_m2.code _ _ _ _ _ _ _ (by decide) hm3).trans hm2_ao
  -- `ite (it.0 != 1) mpt_fail(20) skip`
  refine worldEff_seq hnt3 hcr3
    (fun hnt_i1 hcr_i1 =>
      worldEff_ite heff_m3 _ hnt_i1 hcr_i1
        (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_m3 hmf _ hnt_f hcr_f)
        (fun _ _ _ => worldEff_skip heff_m3))
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hm4_ao : m4.locals.lookup (ofString "acct_out") = some (.val (.word wa)) := by
    rw [(daf_ite_mpt_fail_keeps m3 m4 heff_m3.code _ _ hm4).1]; exact hm3_ao
  -- `decCall sl := rlp_list_to_slices(it.1, it.2)`
  refine worldEff_decCall_eff heff_m4 (ofString "sl") (.comb [.one, .one]) (ofString "rlp_list_to_slices")
    _ _ _ _ lookup_rlp_list_to_slices
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff_m4.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_list_to_slices (callEntryStateHOLFinite m4 callee) cvals
            heff_m4.code (localsFree_arenaReady m4 callee _ heff_m4.arena)
            (by simpa [heff_m4.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_B_sub ws_no_gb)
    (fun _ _ rvsl cpost _ _ _ _ heff_cp hnt5 hcr5 => ?_)
    hnt4 hcr4
  let m5 := setVarHOLFinite (ofString "sl") rvsl { cpost with locals := m4.locals }
  have heff_m5 : WorldEff s0 m5 [] wsBufs wsGw := heff_cp.locals_clock _ _
  have hm5_ao : m5.locals.lookup (ofString "acct_out") = some (.val (.word wa)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_ao,
      show ofString "sl" ≠ ofString "acct_out" by decide]
  -- `ite (sl.1 != 4) mpt_fail(20) skip`
  refine worldEff_seq hnt5 hcr5
    (fun hnt_i2 hcr_i2 =>
      worldEff_ite heff_m5 _ hnt_i2 hcr_i2
        (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_m5 hmf _ hnt_f hcr_f)
        (fun _ _ _ => worldEff_skip heff_m5))
    (fun m6 hm6 heff_m6 hnt6 hcr6 => ?_)
  have hm6_ao : m6.locals.lookup (ofString "acct_out") = some (.val (.word wa)) := by
    rw [(daf_ite_mpt_fail_keeps m5 m6 heff_m5.code _ _ hm6).1]; exact hm5_ao
  -- `dec arr := sl.0`
  refine worldEff_dec heff_m6 _ _ _ hnt6 hcr6 (fun varr _ _ hnt7 hcr7 => ?_)
  let m7 := setVarHOLFinite (ofString "arr") varr m6
  have heff_m7 : WorldEff s0 m7 [] wsBufs wsGw := heff_m6.locals_clock _ _
  have hm7_ao : m7.locals.lookup (ofString "acct_out") = some (.val (.word wa)) := by
    simp [m7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm6_ao,
      show ofString "arr" ≠ ofString "acct_out" by decide]
  -- `decCall f0 := rlp_item(...)`
  refine worldEff_decCall_eff heff_m7 (ofString "f0") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
    _ _ _ _ lookup_rlp_item
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff_m7.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_item (callEntryStateHOLFinite m7 callee) cvals
            heff_m7.code (localsFree_arenaReady m7 callee _ heff_m7.arena)
            (by simpa [heff_m7.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_B_sub ws_no_gb)
    (fun _ _ rvf0 cpost0 _ _ _ hsh_f0 heff_cp0 hnt8 hcr8 => ?_)
    hnt7 hcr7
  obtain ⟨f0_0, f0_1, f0_2, f0_3, rfl⟩ := shape_four_words rvf0 hsh_f0
  let m8 := setVarHOLFinite (ofString "f0")
    (.rStruct [.val (.word f0_0), .val (.word f0_1), .val (.word f0_2), .val (.word f0_3)])
    { cpost0 with locals := m7.locals }
  have heff_m8 : WorldEff s0 m8 [] wsBufs wsGw := heff_cp0.locals_clock _ _
  -- `decCall f1 := rlp_item(...)`
  refine worldEff_decCall_eff heff_m8 (ofString "f1") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
    _ _ _ _ lookup_rlp_item
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff_m8.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_item (callEntryStateHOLFinite m8 callee) cvals
            heff_m8.code (localsFree_arenaReady m8 callee _ heff_m8.arena)
            (by simpa [heff_m8.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_B_sub ws_no_gb)
    (fun _ _ rvf1 cpost1 _ _ _ hsh_f1 heff_cp1 hnt9 hcr9 => ?_)
    hnt8 hcr8
  obtain ⟨f1_0, f1_1, f1_2, f1_3, rfl⟩ := shape_four_words rvf1 hsh_f1
  let m9 := setVarHOLFinite (ofString "f1")
    (.rStruct [.val (.word f1_0), .val (.word f1_1), .val (.word f1_2), .val (.word f1_3)])
    { cpost1 with locals := m8.locals }
  have heff_m9 : WorldEff s0 m9 [] wsBufs wsGw := heff_cp1.locals_clock _ _
  -- `decCall f2 := rlp_item(...)`
  refine worldEff_decCall_eff heff_m9 (ofString "f2") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
    _ _ _ _ lookup_rlp_item
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff_m9.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_item (callEntryStateHOLFinite m9 callee) cvals
            heff_m9.code (localsFree_arenaReady m9 callee _ heff_m9.arena)
            (by simpa [heff_m9.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_B_sub ws_no_gb)
    (fun _ _ rvf2 cpost2 _ _ _ hsh_f2 heff_cp2 hnt10 hcr10 => ?_)
    hnt9 hcr9
  obtain ⟨f2_0, f2_1, f2_2, f2_3, rfl⟩ := shape_four_words rvf2 hsh_f2
  let m10 := setVarHOLFinite (ofString "f2")
    (.rStruct [.val (.word f2_0), .val (.word f2_1), .val (.word f2_2), .val (.word f2_3)])
    { cpost2 with locals := m9.locals }
  have heff_m10 : WorldEff s0 m10 [] wsBufs wsGw := heff_cp2.locals_clock _ _
  -- `decCall f3 := rlp_item(...)`
  refine worldEff_decCall_eff heff_m10 (ofString "f3") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
    _ _ _ _ lookup_rlp_item
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff_m10.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_item (callEntryStateHOLFinite m10 callee) cvals
            heff_m10.code (localsFree_arenaReady m10 callee _ heff_m10.arena)
            (by simpa [heff_m10.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        ws_B_sub ws_no_gb)
    (fun _ _ rvf3 cpost3 _ _ _ hsh_f3 heff_cp3 hnt11 hcr11 => ?_)
    hnt10 hcr10
  obtain ⟨f3_0, f3_1, f3_2, f3_3, rfl⟩ := shape_four_words rvf3 hsh_f3
  let m11 := setVarHOLFinite (ofString "f3")
    (.rStruct [.val (.word f3_0), .val (.word f3_1), .val (.word f3_2), .val (.word f3_3)])
    { cpost3 with locals := m10.locals }
  have heff_m11 : WorldEff s0 m11 [] wsBufs wsGw := heff_cp3.locals_clock _ _
  have hm11_ao : m11.locals.lookup (ofString "acct_out") = some (.val (.word wa)) := by
    simp [m11, m10, m9, m8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm7_ao,
      show ofString "f3" ≠ ofString "acct_out" by decide, show ofString "f2" ≠ ofString "acct_out" by decide,
      show ofString "f1" ≠ ofString "acct_out" by decide, show ofString "f0" ≠ ofString "acct_out" by decide]
  have hm11_f1 : m11.locals.lookup (ofString "f1") =
      some (.rStruct [.val (.word f1_0), .val (.word f1_1), .val (.word f1_2), .val (.word f1_3)]) := by
    simp [m11, m10, m9, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "f3" ≠ ofString "f1" by decide, show ofString "f2" ≠ ofString "f1" by decide]
  have hm11_f2 : m11.locals.lookup (ofString "f2") =
      some (.rStruct [.val (.word f2_0), .val (.word f2_1), .val (.word f2_2), .val (.word f2_3)]) := by
    simp [m11, m10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "f3" ≠ ofString "f2" by decide]
  have hm11_f3 : m11.locals.lookup (ofString "f3") =
      some (.rStruct [.val (.word f3_0), .val (.word f3_1), .val (.word f3_2), .val (.word f3_3)]) := by
    simp [m11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Two `ite ... mpt_fail` checks:
  refine worldEff_seq hnt11 hcr11
    (fun hnt_g1 hcr_g1 =>
      worldEff_ite heff_m11 _ hnt_g1 hcr_g1
        (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_m11 hmf _ hnt_f hcr_f)
        (fun _ _ _ => worldEff_skip heff_m11))
    (fun m12 hm12 heff_m12 hnt12 hcr12 => ?_)
  have hm12_loc : m12.locals = m11.locals := (daf_ite_mpt_fail_keeps m11 m12 heff_m11.code _ _ hm12).1
  refine worldEff_seq hnt12 hcr12
    (fun hnt_g2 hcr_g2 =>
      worldEff_ite heff_m12 _ hnt_g2 hcr_g2
        (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_m12 hmf _ hnt_f hcr_f)
        (fun _ _ _ => worldEff_skip heff_m12))
    (fun m13 hm13 heff_m13 hnt13 hcr13 => ?_)
  have hm13_loc : m13.locals = m11.locals :=
    (daf_ite_mpt_fail_keeps m12 m13 heff_m12.code _ _ hm13).1.trans hm12_loc
  -- `dec nonce := 0`, `dec i := 0`
  refine worldEff_dec heff_m13 _ _ _ hnt13 hcr13 (fun vnonce hvnonce _ hnt14 hcr14 => ?_)
  have hvn_eq : vnonce = .val (.word 0) := by simp [evalHOLExact] at hvnonce; exact hvnonce.symm
  subst hvn_eq
  let m14 := setVarHOLFinite (ofString "nonce") (.val (.word 0)) m13
  have heff_m14 : WorldEff s0 m14 [] wsBufs wsGw := heff_m13.locals_clock _ _
  refine worldEff_dec heff_m14 _ _ _ hnt14 hcr14 (fun vi hvi _ hnt15 hcr15 => ?_)
  have hvi_eq : vi = .val (.word 0) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  let m15 := setVarHOLFinite (ofString "i") (.val (.word 0)) m14
  have heff_m15 : WorldEff s0 m15 [] wsBufs wsGw := heff_m14.locals_clock _ _
  have hm15_ao : m15.locals.lookup (ofString "acct_out") = some (.val (.word wa)) := by
    simp [m15, m14, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm13_loc, hm11_ao,
      show ofString "i" ≠ ofString "acct_out" by decide, show ofString "nonce" ≠ ofString "acct_out" by decide]
  have hm15_f1 : m15.locals.lookup (ofString "f1") =
      some (.rStruct [.val (.word f1_0), .val (.word f1_1), .val (.word f1_2), .val (.word f1_3)]) := by
    simp [m15, m14, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm13_loc, hm11_f1,
      show ofString "i" ≠ ofString "f1" by decide, show ofString "nonce" ≠ ofString "f1" by decide]
  have hm15_f2 : m15.locals.lookup (ofString "f2") =
      some (.rStruct [.val (.word f2_0), .val (.word f2_1), .val (.word f2_2), .val (.word f2_3)]) := by
    simp [m15, m14, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm13_loc, hm11_f2,
      show ofString "i" ≠ ofString "f2" by decide, show ofString "nonce" ≠ ofString "f2" by decide]
  have hm15_f3 : m15.locals.lookup (ofString "f3") =
      some (.rStruct [.val (.word f3_0), .val (.word f3_1), .val (.word f3_2), .val (.word f3_3)]) := by
    simp [m15, m14, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm13_loc, hm11_f3,
      show ofString "i" ≠ ofString "f3" by decide, show ofString "nonce" ≠ ofString "f3" by decide]
  have hm15_wnonce : WordLocals ["nonce"] m15 := by
    intro nm hnm; simp at hnm; subst hnm
    exact ⟨0, by simp [m15, m14, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "nonce" by decide]⟩
  -- Loop 1 (`nonce` read-only loop!)
  let loop1 : ProgHOL 64 :=
    .while (.cmp .lower (.var .local (ofString "i")) (.rfield 2 (.var .local (ofString "f0"))))
      (.seq
        (.assign .local (ofString "nonce")
          (.op .or [.shift .lsl (.var .local (ofString "nonce")) (.const 8#64),
            .loadByte (.op .add [.rfield 1 (.var .local (ofString "f0")), .var .local (ofString "i")])]))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))
  have hws_l1 : wsafe loop1 = true := by decide
  refine worldEff_seq hnt15 hcr15
    (fun hnt_l1 hcr_l1 =>
      worldEff_while _ (fun _ => True) (fun _ _ => trivial)
        (fun t heff_t _ hnt_b hcr_b =>
          ⟨worldEff_seq hnt_b hcr_b
            (fun _ _ => worldEff_assign_local heff_t _ _)
            (fun t' _ heff_t' _ _ => worldEff_assign_local heff_t' _ _),
           fun _ => trivial⟩)
        m15.clock m15 rfl heff_m15 trivial hnt_l1 hcr_l1)
    (fun m16 hm16 heff_m16 hnt16 hcr16 => ?_)
  have hm16_wnonce : WordLocals ["nonce"] m16 := by
    have := wordLocals_flowing hws_l1 hm15_wnonce (by change Flowing (evaluateHOLFiniteState m15 loop1).1; rw [hm16]; exact Or.inl rfl)
    rwa [hm16] at this
  obtain ⟨wnonce, hm16_nonce⟩ := hm16_wnonce "nonce" (by simp)
  have hm16_keep : ∀ key : MlS, key ≠ ofString "nonce" → key ≠ ofString "i" →
      m16.locals.lookup key = m15.locals.lookup key := by
    intro key hk1 hk2
    have hav : avoidsLocal key loop1 = true := by
      simp [loop1, avoidsLocal, beq_iff_eq, Ne.symm hk1, Ne.symm hk2]
    have hk := evaluate_avoidsLocal_flowing key loop1 hav m15
      (by change Flowing (evaluateHOLFiniteState m15 loop1).1; rw [hm16]; exact Or.inl rfl)
    rwa [hm16] at hk
  have hm16_ao : m16.locals.lookup (ofString "acct_out") = some (.val (.word wa)) :=
    (hm16_keep _ (by decide) (by decide)).trans hm15_ao
  have hm16_f1 : m16.locals.lookup (ofString "f1") =
      some (.rStruct [.val (.word f1_0), .val (.word f1_1), .val (.word f1_2), .val (.word f1_3)]) :=
    (hm16_keep _ (by decide) (by decide)).trans hm15_f1
  have hm16_f2 : m16.locals.lookup (ofString "f2") =
      some (.rStruct [.val (.word f2_0), .val (.word f2_1), .val (.word f2_2), .val (.word f2_3)]) :=
    (hm16_keep _ (by decide) (by decide)).trans hm15_f2
  have hm16_f3 : m16.locals.lookup (ofString "f3") =
      some (.rStruct [.val (.word f3_0), .val (.word f3_1), .val (.word f3_2), .val (.word f3_3)]) :=
    (hm16_keep _ (by decide) (by decide)).trans hm15_f3
  -- `store (acct_out + 0) nonce`
  refine worldEff_seq hnt16 hcr16
    (fun _ _ => worldEff_store_word heff_m16 _ _
      (daf_store_val_one m16 _ (Or.inr (Or.inl ⟨_, rfl, wnonce, hm16_nonce⟩)))
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, hm16_ao, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
        subst hx
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
    (fun m17 hm17 heff_m17 hnt17 hcr17 => ?_)
  have hm17_loc : m17.locals = m16.locals := by
    have hcf := (evaluate_store_control_frame m16
      (.op .add [.var .local (ofString "acct_out"), .const 0#64])
      (.var .local (ofString "nonce"))).2.1
    rwa [hm17] at hcf
  -- `ite (32 < f1.2) mpt_fail(22) skip`
  refine worldEff_seq hnt17 hcr17
    (fun hnt_g3 hcr_g3 =>
      worldEff_ite heff_m17 _ hnt_g3 hcr_g3
        (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_m17 hmf _ hnt_f hcr_f)
        (fun _ _ _ => worldEff_skip heff_m17))
    (fun m18 hm18 heff_m18 hnt18 hcr18 => ?_)
  obtain ⟨hm18_loc_m17, hcond_f1_32⟩ := daf_ite_mpt_fail_keeps m17 m18 heff_m17.code _ _ hm18
  have hm18_loc : m18.locals = m16.locals := hm18_loc_m17.trans hm17_loc
  have hf1_2_le32 : f1_2.toNat ≤ 32 := by
    simp [evalHOLExact, hm17_loc, hm16_f1, Compiler.Encoders.Asm.wordCmpHOL] at hcond_f1_32
    rw [BitVec.le_def] at hcond_f1_32
    exact hcond_f1_32
  -- `memzero(acct_out + 8, 32)`
  have hm18_ao : m18.locals.lookup (ofString "acct_out") = some (.val (.word wa)) := by
    rw [hm18_loc]; exact hm16_ao
  refine worldEff_seq hnt18 hcr18
    (fun hnt_mz hcr_mz =>
      worldEff_call0_funByteEff heff_m18 funByteEff_memzero _ [(wa.toNat + 8, 32)]
        (fun vs hvs iv hiv _ => by
          rw [evalListHOLFinite_eq_toExact] at hvs
          simp [evalListHOLExact, evalHOLExact, hm18_ao, wordOpHOL, wordOp, valueIsWord, valueWord] at hvs
          subst hvs
          simp [valWordNat] at hiv; subst hiv
          have hhl_lt : heapLimit < 2 ^ 64 := by decide
          exact ⟨(wa.toNat + 8, 32), List.mem_singleton.2 rfl, by omega, by omega⟩)
        (fun iv hiv _ => by
          simp at hiv; subst hiv
          exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
        hnt_mz hcr_mz)
    (fun m19 hm19 heff_m19 hnt19 hcr19 => ?_)
  have hm19_loc : m19.locals = m16.locals :=
    (call_flow_locals_cgr m18 _ _ m19 hm19).1.trans hm18_loc
  -- `assign i := 0`
  refine worldEff_seq hnt19 hcr19
    (fun _ _ => worldEff_assign_local heff_m19 _ _)
    (fun m20 hm20 heff_m20 hnt20 hcr20 => ?_)
  have hm20_i : m20.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    rw [evaluateHOLFiniteState_assign] at hm20
    simp only [evalHOLExact] at hm20
    split at hm20 <;> simp at hm20
    rw [← hm20]
    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm20_keep : ∀ key : MlS, key ≠ ofString "i" → m20.locals.lookup key = m16.locals.lookup key := by
    intro key hk
    have ha := eval_assign_flowing_keeps m19 (ofString "i") (.const 0#64) key hk
      (by rw [hm20]; exact Or.inl rfl)
    rw [hm20] at ha; dsimp only at ha
    exact ha.trans (by rw [hm19_loc])
  have hm20_inv : DafBalInv wa f1_0 f1_1 f1_2 f1_3 m20 :=
    ⟨(hm20_keep _ (by decide)).trans hm16_ao,
     (hm20_keep _ (by decide)).trans hm16_f1,
     ⟨0, hm20_i⟩⟩
  have hws_bal : wsafe dafBalLoopBody = true := by decide
  -- Loop 2 (`while (i < f1.2) dafBalLoopBody`)
  refine worldEff_seq hnt20 hcr20
    (fun hnt_l2 hcr_l2 =>
      worldEff_while_cond _ (DafBalInv wa f1_0 f1_1 f1_2 f1_3)
        (fun _ hinv => hinv)
        (fun t0 cw hcond hnz heff_t hinv_t hnt_b hcr_b => by
          set t := decClockHOLFinite t0
          obtain ⟨ht_ao, ht_f1, wi, ht_i⟩ := hinv_t
          have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
          have ht0_f1 : t0.locals.lookup (ofString "f1") =
              some (.rStruct [.val (.word f1_0), .val (.word f1_1), .val (.word f1_2), .val (.word f1_3)]) := ht_f1
          have hlt_wi : wi < f1_2 := by
            rw [evalHOLFinite_eq_toExact] at hcond
            simp [evalHOLExact, ht0_i, ht0_f1, Compiler.Encoders.Asm.wordCmpHOL] at hcond
            by_contra hge
            simp [hge] at hcond
            exact hnz hcond.symm
          obtain ⟨hwlp_lo, hwlp_hi⟩ := daf_balance_addr wa f1_2 wi hwa_lo hwa_hi hf1_2_le32 hlt_wi
          refine ⟨?_, fun hf => ?_⟩
          · refine worldEff_dec heff_t _ _ _ hnt_b hcr_b (fun vpos hvpos _ hnt_d1 hcr_d1 => ?_)
            have hvpos_eq : vpos = .val (.word (f1_2 - 1#64 - wi)) := by
              simp [evalHOLExact, evalListHOLExact, ht_f1, ht_i, wordOpHOL, wordOp, valueIsWord, valueWord] at hvpos
              exact hvpos.symm
            subst hvpos_eq
            let u1 := setVarHOLFinite (ofString "pos") (.val (.word (f1_2 - 1#64 - wi))) t
            have heff_u1 : WorldEff s0 u1 [] wsBufs wsGw := heff_t.locals_clock _ _
            have hu1_pos : u1.locals.lookup (ofString "pos") = some (.val (.word (f1_2 - 1#64 - wi))) := by
              simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hu1_ao : u1.locals.lookup (ofString "acct_out") = some (.val (.word wa)) := by
              simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_ao,
                show ofString "pos" ≠ ofString "acct_out" by decide]
            refine worldEff_dec heff_u1 _ _ _ hnt_d1 hcr_d1 (fun vlp hvlp _ hnt_d2 hcr_d2 => ?_)
            let wpos := f1_2 - 1#64 - wi
            let wlp := wa + 8#64 + ((wpos >>> 3) * 8#64)
            have hvlp_eq : vlp = .val (.word wlp) := by
              simp [evalHOLExact, evalListHOLExact, hu1_ao, hu1_pos, panOpHOL, wordShiftHOL,
                wordOpHOL, wordOp, valueIsWord, valueWord] at hvlp
              rw [← hvlp]
              congr 2
              exact (BitVec.add_assoc wa 8#64 ((wpos >>> 3) * 8#64)).symm
            subst hvlp_eq
            let u2 := setVarHOLFinite (ofString "lp") (.val (.word wlp)) u1
            have heff_u2 : WorldEff s0 u2 [] wsBufs wsGw := heff_u1.locals_clock _ _
            have hu2_lp : u2.locals.lookup (ofString "lp") = some (.val (.word wlp)) := by
              simp [u2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            refine worldEff_seq hnt_d2 hcr_d2
              (fun _ _ => worldEff_store_word heff_u2 _ _
                (daf_store_val_one u2 _ (Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))))
                (fun x hx _ => by
                  simp [evalHOLExact, hu2_lp] at hx; subst hx
                  exact Or.inr (Or.inr (Or.inr ⟨hwlp_lo, hwlp_hi⟩))))
              (fun u3 _ heff_u3 _ _ => worldEff_assign_local heff_u3 _ _)
          · exact ⟨(dafBalLoopBody_keeps t _ (by decide) (by decide) (by decide) hf).trans ht_ao,
                   (dafBalLoopBody_keeps t _ (by decide) (by decide) (by decide) hf).trans ht_f1,
                   evaluate_wordLocal (ofString "i") dafBalLoopBody hws_bal t ⟨wi, ht_i⟩
                     (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩)
        m20.clock m20 rfl heff_m20 hm20_inv hnt_l2 hcr_l2)
    (fun m21 hm21 heff_m21 hnt21 hcr21 => ?_)
  let loop2 : ProgHOL 64 :=
    .while (.cmp .lower (.var .local (ofString "i")) (.rfield 2 (.var .local (ofString "f1"))))
      dafBalLoopBody
  have hm21_keep : ∀ key : MlS, key ≠ ofString "pos" → key ≠ ofString "lp" → key ≠ ofString "i" →
      m21.locals.lookup key = m20.locals.lookup key := by
    intro key hk1 hk2 hk3
    have hav : avoidsLocal key loop2 = true := by
      simp [loop2, dafBalLoopBody, avoidsLocal, beq_iff_eq, Ne.symm hk1, Ne.symm hk2, Ne.symm hk3]
    have hm21_l2 : evaluateHOLFiniteState m20 loop2 = (none, m21) := hm21
    have hk := evaluate_avoidsLocal_flowing key loop2 hav m20
      (by rw [hm21_l2]; exact Or.inl rfl)
    rwa [hm21_l2] at hk
  have hm21_ao : m21.locals.lookup (ofString "acct_out") = some (.val (.word wa)) :=
    (hm21_keep _ (by decide) (by decide) (by decide)).trans ((hm20_keep _ (by decide)).trans hm16_ao)
  have hm21_f2 : m21.locals.lookup (ofString "f2") =
      some (.rStruct [.val (.word f2_0), .val (.word f2_1), .val (.word f2_2), .val (.word f2_3)]) :=
    (hm21_keep _ (by decide) (by decide) (by decide)).trans ((hm20_keep _ (by decide)).trans hm16_f2)
  have hm21_f3 : m21.locals.lookup (ofString "f3") =
      some (.rStruct [.val (.word f3_0), .val (.word f3_1), .val (.word f3_2), .val (.word f3_3)]) :=
    (hm21_keep _ (by decide) (by decide) (by decide)).trans ((hm20_keep _ (by decide)).trans hm16_f3)
  -- `ite (f2.2 == 0) (store (acct_out + 40) empty_trie_root) (ite (f2.2 != 32) mpt_fail(23) skip; store (acct_out + 40) f2.1)`
  refine worldEff_seq hnt21 hcr21
    (fun hnt_b2 hcr_b2 =>
      worldEff_ite heff_m21 _ hnt_b2 hcr_b2
        (fun _ _ _ _ _ => worldEff_store_word heff_m21 _ _
          (daf_store_val_one m21 _ (Or.inr (Or.inr (Or.inl ⟨"empty_trie_root", by decide, rfl, heff_m21.arena.2.2.2.2.2.2.2.2.2⟩))))
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hm21_ao, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
        (fun _ hnt_n2 hcr_n2 =>
          worldEff_seq hnt_n2 hcr_n2
            (fun hnt_g4 hcr_g4 =>
              worldEff_ite heff_m21 _ hnt_g4 hcr_g4
                (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_m21 hmf _ hnt_f hcr_f)
                (fun _ _ _ => worldEff_skip heff_m21))
            (fun m21a hm21a heff_m21a _ _ => by
              have hm21a_loc : m21a.locals = m21.locals :=
                (daf_ite_mpt_fail_keeps m21 m21a heff_m21.code _ _ hm21a).1
              exact worldEff_store_word heff_m21a _ _
                (fun v hv => by simp [evalHOLExact, hm21a_loc, hm21_f2] at hv; exact ⟨_, hv.symm⟩)
                (fun x hx _ => by
                  simp [evalHOLExact, evalListHOLExact, hm21a_loc, hm21_ao, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
                  subst hx
                  exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))))
    (fun m22 hm22 heff_m22 hnt22 hcr22 => ?_)
  have hm22_keep : ∀ key : MlS, m22.locals.lookup key = m21.locals.lookup key := by
    intro key
    let p22 : ProgHOL 64 :=
      .ite (.cmp .equal (.rfield 2 (.var .local (ofString "f2"))) (.const 0#64))
        (.store (.op .add [.var .local (ofString "acct_out"), .const 40#64]) (.var .global (ofString "empty_trie_root")))
        (.seq
          (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "f2"))) (.const 32#64))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 23#64])
            .skip)
          (.store (.op .add [.var .local (ofString "acct_out"), .const 40#64]) (.rfield 1 (.var .local (ofString "f2")))))
    have hav : avoidsLocal key p22 = true := by simp [p22, avoidsLocal]
    have hk := evaluate_avoidsLocal_flowing key p22 hav m21
      (by change Flowing (evaluateHOLFiniteState m21 p22).1; rw [hm22]; exact Or.inl rfl)
    rwa [hm22] at hk
  have hm22_ao : m22.locals.lookup (ofString "acct_out") = some (.val (.word wa)) :=
    (hm22_keep _).trans hm21_ao
  have hm22_f3 : m22.locals.lookup (ofString "f3") =
      some (.rStruct [.val (.word f3_0), .val (.word f3_1), .val (.word f3_2), .val (.word f3_3)]) :=
    (hm22_keep _).trans hm21_f3
  -- `ite (f3.2 == 0) (store (acct_out + 48) empty_code_hash) ... ; return 0`
  refine worldEff_seq hnt22 hcr22
    (fun hnt_b3 hcr_b3 =>
      worldEff_ite heff_m22 _ hnt_b3 hcr_b3
        (fun _ _ _ _ _ => worldEff_store_word heff_m22 _ _
          (daf_store_val_one m22 _ (Or.inr (Or.inr (Or.inl ⟨"empty_code_hash", by decide, rfl, heff_m22.arena.2.2.2.2.2.2.2.2.2⟩))))
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hm22_ao, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
        (fun _ hnt_n3 hcr_n3 =>
          worldEff_seq hnt_n3 hcr_n3
            (fun hnt_g5 hcr_g5 =>
              worldEff_ite heff_m22 _ hnt_g5 hcr_g5
                (fun _ _ _ hnt_f hcr_f => worldEff_call0_ro heff_m22 hmf _ hnt_f hcr_f)
                (fun _ _ _ => worldEff_skip heff_m22))
            (fun m22a hm22a heff_m22a _ _ => by
              have hm22a_loc : m22a.locals = m22.locals :=
                (daf_ite_mpt_fail_keeps m22 m22a heff_m22.code _ _ hm22a).1
              exact worldEff_store_word heff_m22a _ _
                (fun v hv => by simp [evalHOLExact, hm22a_loc, hm22_f3] at hv; exact ⟨_, hv.symm⟩)
                (fun x hx _ => by
                  simp [evalHOLExact, evalListHOLExact, hm22a_loc, hm22_ao, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
                  subst hx
                  exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))))
    (fun m23 _ heff_m23 _ _ => worldEff_return heff_m23 _)

private theorem lookup_decode_account_from_leaf :
    originalRuntimeCode.lookup (ofString "decode_account_from_leaf") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "acct_out", .one)],
        sourceFnBody Guest.Software.guestFn_decode_account_from_leaf, .one) :=
  lookup_of_guestAst_getElem 293 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_account_from_leaf) rfl

private theorem lookup_trie_lookup :
    originalRuntimeCode.lookup (ofString "trie_lookup") =
      some ([(ofString "root", .one), (ofString "key_hash32", .one)],
        sourceFnBody Guest.Software.guestFn_trie_lookup, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 267 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_trie_lookup) rfl

private theorem lookup_ws_account_leaf :
    originalRuntimeCode.lookup (ofString "ws_account_leaf") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_ws_account_leaf, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 365 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_account_leaf) rfl

private theorem lookup_ws_get_account_optional :
    originalRuntimeCode.lookup (ofString "ws_get_account_optional") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_ws_get_account_optional, .one) :=
  lookup_of_guestAst_getElem 366 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_get_account_optional) rfl

private theorem lookup_ws_storage_root_of :
    originalRuntimeCode.lookup (ofString "ws_storage_root_of") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_ws_storage_root_of, .one) :=
  lookup_of_guestAst_getElem 367 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_storage_root_of) rfl

private theorem lookup_cache_get_root :
    originalRuntimeCode.lookup (ofString "cache_get_root") =
      some ([(ofString "cache", .one), (ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_cache_get_root, .one) :=
  lookup_of_guestAst_getElem 842 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_cache_get_root) rfl

end InitECandidate.Solver.Wave8GuestInv.R16Shards
