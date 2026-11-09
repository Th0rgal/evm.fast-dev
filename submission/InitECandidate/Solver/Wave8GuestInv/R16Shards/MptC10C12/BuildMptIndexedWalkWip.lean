import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexed
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

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

/-! ### `wk_build_mpt_indexed`: the world-keeping bridge

The `WorldKeeps` for `build_mpt_indexed`. The walk mirrors the terminating walk
(`bmi_body_bound_entry`) but carries a `WorldEff` chain over a widened, fixed region
list `bmiWkRl` (the keep buffers, the trie object, the fresh heap tail and the
entry world's owned intervals), the composed `RecordsKept`, and the loop
invariant `BuildMptLoopInv2`. The final packaging assembles the `WorldStep`
directly: its `FrameOutside` permits `worldOwned` writes, so the widened regions
absorb without a table-unchangedness argument. The `mpt_root` contract is taken
as a hypothesis (the C08 `«mk_mpt_root»` stub's signature). -/

/-- The five keep-buffer regions of the exported contract. -/
def bmiWkRti (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(locN s "out", 32),
   (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
   (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
   (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
   (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)]

/-- The widened walk frame: the keep buffers, the whole fresh-heap tail from
`mark`, and the entry world's owned intervals. -/
def bmiWkRl (s : PanSemStateFiniteExact 64 F) (mark : Nat) (S Nd : List Nat) : List Ivl :=
  bmiWkRti s ++ [(mark, heapLimit - mark)] ++ worldOwned s S Nd

/-! ### Chunk B: the reduced cell-level effect structure -/

/-- The reduced, cell-level world effect for the walk: all fields the loop
threading needs, with `cell_frame` stated with the loose `CellHits` so that
sub-interval coverage never needs alignment. -/
structure BmiWkEff {F : Type} (s cur : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (gw : List String) : Prop where
  arena   : ArenaReady cur
  code    : cur.code = originalRuntimeCode
  hp_lo   : globN s "heap_ptr" ≤ globN cur "heap_ptr"
  fmp_eq  : globN cur "frame_mem_ptr" = globN s "frame_mem_ptr"
  sp_hi   : globN cur "scratch_ptr" ≤ globN s "scratch_ptr"
  gw_kept : GlobalsKept gw s cur
  cell_frame : ∀ a : BitVec 64, cur.memory a ≠ s.memory a →
    (∃ ivl ∈ Rl, CellHits a.toNat ivl) ∨
    CellHits a.toNat (freeGap s) ∨ CellHits a.toNat (heapFree s)

theorem BmiWkEff.refl {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (gw : List String) (hA : ArenaReady s)
    (hc : s.code = originalRuntimeCode) :
    BmiWkEff s s Rl gw := by
  refine ⟨hA, hc, le_rfl, rfl, le_rfl, fun _ _ => rfl, fun _ h => absurd rfl h⟩

theorem BmiWkEff.locals_clock {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (h : BmiWkEff s cur Rl gw) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    BmiWkEff s { cur with locals := L, clock := k } Rl gw := by
  refine ⟨⟨guestInv_with_locals_clock cur L k h.arena.1, h.arena.2⟩, h.code, h.hp_lo,
    h.fmp_eq, h.sp_hi, ?_, ?_⟩
  · intro k' hk'
    exact h.gw_kept k' hk'
  · intro a hne
    exact h.cell_frame a hne

theorem BmiWkEff.trans {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (h1 : BmiWkEff s mid Rl gw) (h2 : BmiWkEff mid post Rl gw) :
    BmiWkEff s post Rl gw := by
  have hfmp_mid : globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" := h1.fmp_eq
  have hsp_mid : globN mid "scratch_ptr" ≤ globN s "scratch_ptr" := h1.sp_hi
  have hhp_mid : globN s "heap_ptr" ≤ globN mid "heap_ptr" := h1.hp_lo
  have hhp_mid_lim : globN mid "heap_ptr" ≤ heapLimit := h1.arena.2.2.1
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" :=
    h1.hp_lo.trans h2.hp_lo
  refine ⟨h2.arena, h2.code, hhp, h2.fmp_eq.trans h1.fmp_eq,
    h2.sp_hi.trans h1.sp_hi, ?_, ?_⟩
  · intro k hk
    exact (h1.gw_kept k hk).trans (h2.gw_kept k hk)
  · intro a hne
    by_cases hmid : mid.memory a = s.memory a
    · rcases h2.cell_frame a (by rw [hmid]; exact hne) with ⟨ivl, hivl, hci⟩ | hci | hci
      · exact Or.inl ⟨ivl, hivl, hci⟩
      · refine Or.inr (Or.inl ?_)
        dsimp only [freeGap] at hci ⊢
        obtain ⟨hc1, hc2⟩ := hci
        exact ⟨by omega, by omega⟩
      · refine Or.inr (Or.inr ?_)
        dsimp only [heapFree] at hci ⊢
        obtain ⟨hc1, hc2⟩ := hci
        exact ⟨by omega, by omega⟩
    · exact h1.cell_frame a hmid

/-- Adapter: a `WorldStep` gives a `BmiWkEff`. Cell-level only: the frame
coverage is a pure sub-interval statement, so no alignment is required. -/
theorem bmiWkEff_of_worldStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    {Rl : List Ivl} {S Nd : List Nat}
    (hstep : WorldStep R gw keep Q s r post)
    (hW : WorldTypedWith s S Nd)
    (hR' : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hgw_map : gw.map ofString = ["heap_ptr", "scratch_ptr"].map ofString)
    (hsp_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hwiden : ∀ i ∈ worldOwned s S Nd ++ R s,
      i = (0, 0) ∨ (∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)) :
    BmiWkEff s post Rl gw := by
  have hmem_fmp : ofString "frame_mem_ptr" ∉ gw.map ofString := by
    rw [hgw_map]; decide
  obtain ⟨S', Nd', _, _, _, hfr, _⟩ :=
    hstep.2.2.2.2 S Nd hW hR'
  refine ⟨hstep.1, hstep.1.1.code, hstep.2.1,
    R10Shards.P26_P28.globN_eq_of_lookup (hstep.2.2.1 _ hmem_fmp), hsp_le,
    (fun k hk => hstep.2.2.1 k (by rw [hgw_map] at hk ⊢; exact hk)), ?_⟩
  intro a hne
  have hhit : (∃ i ∈ worldOwned s S Nd ++ R s, CellHits a.toNat i) ∨
      CellHits a.toNat (freeGap s) ∨ CellHits a.toNat (heapFree s) := by
    by_contra hall
    push Not at hall
    refine hne (hfr a (fun i hi => ?_) hall.2.2)
    rcases List.mem_append.mp hi with h | h
    · exact hall.1 i h
    · rcases List.mem_singleton.mp h with rfl
      exact hall.2.1
  rcases hhit with ⟨i, hi, hci⟩ | hfg | hhf
  · rcases hwiden i hi with hz | ⟨j, hj, hj1, hj2⟩
    · rw [hz] at hci
      simp [CellHits] at hci
    · obtain ⟨hc1, hc2⟩ := hci
      exact Or.inl ⟨j, hj, ⟨by omega, by omega⟩⟩
  · exact Or.inr (Or.inl hfg)
  · exact Or.inr (Or.inr hhf)

/-- The `while` CPS for `BmiWkEff` (copy of `worldEff_while`). -/
theorem bmiWk_while {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (cond : ExpHOL 64) {body : ProgHOL 64}
    (Inv : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, Inv t → Inv (decClockHOLFinite t))
    (hb : ∀ t, BmiWkEff s t Rl gw → Inv t →
      (evaluateHOLFiniteState t body).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState t body).1 →
      BmiWkEff s (evaluateHOLFiniteState t body).2 Rl gw ∧
      (((evaluateHOLFiniteState t body).1 = none ∨
        (evaluateHOLFiniteState t body).1 = some .continue) →
        Inv (evaluateHOLFiniteState t body).2)) :
    ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F), cur.clock = k →
      BmiWkEff s cur Rl gw → Inv cur →
      (evaluateHOLFiniteState cur (.while cond body)).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur (.while cond body)).1 →
      BmiWkEff s (evaluateHOLFiniteState cur (.while cond body)).2 Rl gw := by
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
          have heff_d : BmiWkEff s (decClockHOLFinite cur) Rl gw := heff.locals_clock cur.locals (cur.clock - 1)
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

/-- Word-cell persistence: a word cell disjoint from every walk frame and from
the fresh heap is preserved. -/
theorem bmiWk_memW_kept {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (heff : BmiWkEff s cur Rl gw)
    (x : Nat) (hx64 : x < 2 ^ 64)
    (hRl : ∀ ivl ∈ Rl, ¬ CellHits x ivl)
    (hfg : ¬ CellHits x (freeGap s)) (hhf : ¬ CellHits x (heapFree s)) :
    memW cur x = memW s x := by
  have htoNat : (BitVec.ofNat 64 x).toNat = x := by
    rw [BitVec.toNat_ofNat]; omega
  have hmem : cur.memory (BitVec.ofNat 64 x) = s.memory (BitVec.ofNat 64 x) := by
    by_contra hne
    rcases heff.cell_frame (BitVec.ofNat 64 x) hne with ⟨ivl, hivl, hci⟩ | hci | hci
    · rw [htoNat] at hci
      exact hRl ivl hivl hci
    · rw [htoNat] at hci
      exact hfg hci
    · rw [htoNat] at hci
      exact hhf hci
  simp only [memW, hmem]

/-! ### Chunk C: the strong entry guard and the walk invariant -/

/-- Strong entry guard for `build_mpt_indexed`: the ready guard plus the typed
world with the disjunctions the walk's steps and final packaging need. -/
def BuildMptIndexedReadyStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BuildMptIndexedReady s ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧
      IvlsDisj (bmiWkRti s) (worldTypedIvls s S Nd) ∧
      IvlsDisj [(locN s "slice_arr", 16 * locN s "n")] (worldOwned s S Nd) ∧
      IvlsDisj [(locN s "out", 32)]
        ((locN s "slice_arr", 16 * locN s "n") :: worldOwned s S Nd) ∧
      Inside (locN s "out", 32) sourceBase (globN s "heap_ptr") ∧
      globN s "mpt_key_scratch" ≠ 0 ∧
      (∀ i, i < locN s "n" → memW s (locN s "slice_arr" + 16 * i) + 8 ≤ globN s "heap_ptr") ∧
      (∀ i, i < locN s "n" → ∀ iv ∈ keccakBufIvls s, 0 < iv.2 →
        ¬ InIvl (memW s (locN s "slice_arr" + 16 * i)) iv)

/-- The walk invariant, threaded through the mpt steps' own `MptObjStepStrong`
witnesses. Everything is stated against the frozen entry `s0` (with its world
`S0 Nd0`) and the fresh-heap base `mark = globN s0 "heap_ptr"`. -/
def BmiWkLoopInv (s0 : PanSemStateFiniteExact 64 F) (S0 Nd0 : List Nat) (mark : Nat)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady t ∧
  locN t "mark" = mark ∧ locN t "m" = mark ∧
  locN t "n" = locN s0 "n" ∧ locN t "slice_arr" = locN s0 "slice_arr" ∧
    locN t "out" = locN s0 "out" ∧
  mark ≤ globN t "heap_ptr" ∧
  globN t "heap_ptr" ≤ heapLimit ∧
  globN t "keccak_pad" = globN s0 "keccak_pad" ∧
    globN t "keccak_st" = globN s0 "keccak_st" ∧
  globN t "frame_mem_ptr" = globN s0 "frame_mem_ptr" ∧
  globN t "scratch_ptr" ≤ globN s0 "scratch_ptr" ∧
  ∃ S Nd Nm,
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
    (∀ x, x + 8 ≤ locN s0 "slice_arr" + 16 * locN s0 "n" → memW t x = memW s0 x)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

/-! ### Chunk D: the eval-level chain (HeapByteEff-based) -/

/-- Bridge: a `HeapByteEff` plus the runtime code gives a `BmiWkEff`
(the loose `CellHits` only widens the frame disjunction). -/
theorem bmiWkEff_of_heapByteEff {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (h : HeapByteEff s post Rl gw) (hc : post.code = originalRuntimeCode) :
    BmiWkEff s post Rl gw := by
  refine ⟨h.arena, hc, h.hp_le, h.fp_eq, h.sp_le, h.globals, ?_⟩
  intro a hne
  rcases h.cell_frame a hne with ⟨ivl, hivl, hpos, hci⟩ | ⟨_, hci⟩ | ⟨_, hci⟩
  · exact Or.inl ⟨ivl, hivl, hci⟩
  · exact Or.inr (Or.inl hci)
  · exact Or.inr (Or.inr hci)

/-- The `heap_mark` decCall extends a `HeapByteEff` chain. -/
theorem heapByteEff_decCall_heap_mark {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {cont : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (heff : HeapByteEff s cur Rl gw) (hcode_cur : cur.code = originalRuntimeCode)
    (lname : String)
    (hnt : (evaluateHOLFiniteState cur
      (.decCall (ofString lname) .one (ofString "heap_mark") [] cont)).1 ≠ some .timeOut)
    (hcont : ∀ (hp : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      cur.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) →
      hp.toNat = globN cur "heap_ptr" →
      mid.globals = cur.globals → mid.memory = cur.memory →
      mid.locals = cur.locals.update (ofString lname, .val (.word hp)) →
      HeapByteEff s mid Rl gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      HeapByteEff s (evaluateHOLFiniteState mid cont).2 Rl gw) :
    HeapByteEff s (evaluateHOLFiniteState cur
      (.decCall (ofString lname) .one (ofString "heap_mark") [] cont)).2 Rl gw := by
  obtain ⟨hp, mid, hhp_lk, hhp_nat, hmid_g, hmid_m, hmid_l, heff_mid, hcont_run, heval⟩ :=
    eval_decCall_heap_mark cur lname cont Rl gw hcode_cur heff.arena hnt
  rw [heval]
  dsimp only
  exact (hcont hp mid hhp_lk hhp_nat hmid_g hmid_m hmid_l (heff.trans heff_mid)
    hcont_run).locals_clock
    (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
      (ofString lname, cur.locals.lookup (ofString lname)))
    (evaluateHOLFiniteState mid cont).2.clock

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

