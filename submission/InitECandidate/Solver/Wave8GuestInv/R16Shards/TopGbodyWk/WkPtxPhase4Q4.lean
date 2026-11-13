import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q3

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

/-! # Phase 4Q4: the loop-38 copy loop

This file continues `WkPtxPhase4Q3`.  After the tail setup, the program
runs the copy loop (loop 38): while `i < nl`, store the source log-entry
pointer at `stable_lp + 8 * i` (a cell of the fresh backing array) and
bump `i`.  The loop is run with a custom while-runner that exposes the
clock-positivity fact to the body obligation, and a loop invariant
(`P4Q8Loop`) carrying exactly the facts the post-loop tail needs:

* the entry-anchored `PtxRelBase` and the fresh-block chain,
* the out-record and its logs list (the copy source): the list header is
  the word at `w_out + 16`, the backing array of entry pointers is at
  `lp` (the header's first word), the length is the header's second
  word, and every involved region is either below the fresh frontier
  `lw` or on the scratch side above the whole heap arena,
* the fresh header cells and the copied prefix of the backing array.

The invariant deliberately does NOT carry a full `P4Data`: the world
witnesses of `P4Data.logs_facts` are replaced at final assembly by the
chain's witnesses, so only the fields `PtxAfterPhase4Data` actually
reads are transported. -/

/-! ## A while-runner that exposes the clock fact

`p4Run_loop38Body` (in `WkPtxPhase4G`) demands, inside its facts bundle,
either that the condition already evaluates to `0` at the post-body
state or that the pre-body clock is nonzero — but the plain runner's
body obligation receives neither fact.  The runner below is the loop-31
`p4Run_while_guard` pattern with the clock fact threaded into the body
obligation as a hypothesis. -/

/-- The loop-38 while-runner with the guard fact and the clock-positivity
fact both handed to the body obligation. -/
theorem p4Q8_while38 {F : Type} {entry : PanSemStateFiniteExact 64 F}
    {rest : ProgHOL 64} (INV : PanSemStateFiniteExact 64 F → Prop)
    (hexit : ∀ t, INV t → evalAt t p4Loop38Cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry rest t)
    (hbody : ∀ t, INV t →
      (∃ w : BitVec 64, evalAt t p4Loop38Cond = some (.val (.word w)) ∧ w ≠ 0#64) →
      t.clock ≠ 0 →
      (∀ mid, INV mid → mid.clock < t.clock →
        PtxRelRunStrong entry (.seq (.while p4Loop38Cond p4Loop38Body) rest) mid) →
      PtxRelRunStrong entry (.seq p4Loop38Body
        (.seq (.while p4Loop38Cond p4Loop38Body) rest)) (decClockHOLFinite t))
    (s : PanSemStateFiniteExact 64 F) (hINV : INV s) :
    PtxRelRunStrong entry (.seq (.while p4Loop38Cond p4Loop38Body) rest) s := by
  intro hres
  suffices H : ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → INV st →
      PtxRelRunStrong entry (.seq (.while p4Loop38Cond p4Loop38Body) rest) st from
    H s.clock s rfl hINV hres
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hINVst hres
    rcases hc : @evalHOLFinite 64 F _ st
        (fun address => Classical.propDecidable (st.memaddrs address)) p4Loop38Cond with _ | cval
    · -- condition evaluation fails: the loop traps with `.error`
      have herr : evaluateHOLFiniteState st (.seq (.while p4Loop38Cond p4Loop38Body) rest) =
          (some .error, st) := by
        rw [evaluateHOLFiniteState_seq_line780,
            evaluateHOLFiniteState_while_fixClockRewrite, hc]
      rw [herr] at hres ⊢
      dsimp only at hres ⊢
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · cases cval with
      | val wv =>
        cases wv with
        | word w =>
          by_cases hw : w = 0
          · -- loop exit
            subst hw
            have hrun : evaluateHOLFiniteState st (.seq (.while p4Loop38Cond p4Loop38Body) rest) =
                evaluateHOLFiniteState st rest := by
              rw [evaluateHOLFiniteState_seq_line780,
                  evaluateHOLFiniteState_while_fixClockRewrite, hc]
              dsimp only
              rw [if_neg (by decide)]
            rw [hrun] at hres ⊢
            exact hexit st hINVst hc hres
          · -- loop iterates
            by_cases hclk : st.clock = 0
            · -- clock exhausted: `.timeOut`
              have hto : evaluateHOLFiniteState st
                  (.seq (.while p4Loop38Cond p4Loop38Body) rest) =
                  (some .timeOut, emptyLocalsHOLFinite st) := by
                rw [evaluateHOLFiniteState_seq_line780,
                    evaluateHOLFiniteState_while_fixClockRewrite, hc]
                dsimp only
                rw [if_pos hw, if_pos hclk]
              rw [hto] at hres ⊢
              dsimp only at hres ⊢
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · -- run the body at the decremented clock, with the guard and clock facts
              rcases hbrun : evaluateHOLFiniteState (decClockHOLFinite st) p4Loop38Body
                with ⟨rb, mid⟩
              have hnb' := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
                p4Loop38Body p4Loop38Body_noTopBreak (decClockHOLFinite st)
              have hnc' := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue
                p4Loop38Body p4Loop38Body_noTopContinue (decClockHOLFinite st)
              rw [hbrun] at hnb' hnc'
              have hcomp : evaluateHOLFiniteState st
                  (.seq (.while p4Loop38Cond p4Loop38Body) rest) =
                  evaluateHOLFiniteState (decClockHOLFinite st)
                    (.seq p4Loop38Body (.seq (.while p4Loop38Cond p4Loop38Body) rest)) := by
                rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780,
                    evaluateHOLFiniteState_while_fixClockRewrite, hc]
                dsimp only
                rw [if_pos hw, if_neg hclk, hbrun]
                dsimp only
                cases rb with
                | none =>
                  rw [evaluateHOLFiniteState_seq_line780]
                | some r =>
                  cases r with
                  | «continue» => exact absurd rfl hnc'
                  | «break» => exact absurd rfl hnb'
                  | returned _ | exception _ | timeOut | error | finalFfi _ => rfl
              rw [hcomp] at hres ⊢
              have hclt : mid.clock < k := by
                have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st)
                  p4Loop38Body
                rw [hbrun] at hrem
                change mid.clock ≤ st.clock - 1 at hrem
                omega
              exact hbody st hINVst ⟨w, hc, hw⟩ hclk
                (fun mid' hINVmid hlt => ih mid'.clock (by omega) mid' rfl hINVmid)
                hres
      | rStruct _ | nStruct _ _ =>
        -- the condition is not a word: the loop traps with `.error`
        have herr : evaluateHOLFiniteState st (.seq (.while p4Loop38Cond p4Loop38Body) rest)
            = (some .error, st) := by
          rw [evaluateHOLFiniteState_seq_line780,
              evaluateHOLFiniteState_while_fixClockRewrite, hc]
        rw [herr] at hres ⊢
        dsimp only at hres ⊢
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-! ## Cell-stability helpers for `pmcUpdW` -/

theorem p4Q8_bv_ne_of_toNat_ne {a b : BitVec 64} (h : a.toNat ≠ b.toNat) : a ≠ b :=
  fun heq => h (congrArg BitVec.toNat heq)

/-- A cell different from the store address survives a `pmcUpdW` store. -/
theorem p4Q8_memW_updW_away {F : Type} {u : PanSemStateFiniteExact 64 F} {x v : BitVec 64}
    {k : Nat} (hk : BitVec.ofNat 64 k ≠ x) :
    memW {u with memory := pmcUpdW u.memory x v} k = memW u k := by
  unfold memW
  dsimp only
  simp only [pmcUpdW, if_neg hk]

/-- A word cell different from the store address survives a `pmcUpdW` store. -/
theorem p4Q8_wordAt_updW_away {F : Type} {u : PanSemStateFiniteExact 64 F} {x v : BitVec 64}
    {k : Nat} (hk : BitVec.ofNat 64 k ≠ x) (h : WordAt u k) :
    WordAt {u with memory := pmcUpdW u.memory x v} k := by
  obtain ⟨w, hd, hcell⟩ := h
  refine ⟨w, hd, ?_⟩
  show pmcUpdW u.memory x v (BitVec.ofNat 64 k) = HolWordLab.word w
  rw [pmcUpdW, if_neg hk]
  exact hcell

/-- The `toNat` of `i * 8#64`. -/
theorem p4Q8_mul8_toNat (i_w : BitVec 64) (h8 : i_w.toNat * 8 < 2 ^ 64) :
    (i_w * 0x0000000000000008#64).toNat = i_w.toNat * 8 := by
  rw [BitVec.toNat_mul]
  norm_num
  omega

/-! ## The current receipt slice across block-out-preserving steps -/

/-- The current receipt slice's length cell (written by instruction 27) is
a cell of the `bo + 32` slice array, a block-out object: it survives any
step between two base states that leaves the block-out objects unhit. -/
theorem p4Q8_rcptCur_of_unhit {F : Type}
    {entry t post : PanSemStateFiniteExact 64 F}
    (hbase : PtxRelBase true entry t) (hbase' : PtxRelBase true entry post)
    (hu : PtxBlockOutUnhit t post) :
    memW post (memW post (globN post "bo" + 32) + 16 * locN entry "index" + 8) =
      memW t (memW t (globN t "bo" + 32) + 16 * locN entry "index" + 8) := by
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := hbase.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨Sc, Nc, _, hWT_w, _, _⟩ := hbase.typing S_e Nd_e hWT_e hD_e
  have hbo_t : globN t "bo" = globN entry "bo" :=
    globN_eq_of_lookup (hbase.globals (ofString "bo") (by decide))
  have hbo_nz_t : globN t "bo" ≠ 0 := by rw [hbo_t]; exact hbo_nz_e
  have hbo32_t : memW t (globN t "bo" + 32) = memW entry (globN entry "bo" + 32) :=
    ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
  have hbo80_t : memW t (globN t "bo" + 80) = memW entry (globN entry "bo" + 80) :=
    ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
  have hbo32_p : memW post (globN post "bo" + 32) = memW entry (globN entry "bo" + 32) :=
    ptx_entry_bo_field_eq hWT_e hbase'.globals hbase'.records hbo_nz_e (by simp) (by omega)
  rw [hbo32_p, ← hbo32_t]
  exact ptx_slice_length_eq_of_blockOutUnhit (off := 32) (i := locN entry "index")
    hbase.world.1 hWT_w hu hbo_nz_t (by simp) (by rw [hbo32_t]; exact hbo32_nz_e)
    (by rw [hbo80_t]; omega)

/-- The current receipt slice's length cell survives a fresh-heap
allocation step (the `lst_new` callee). -/
theorem p4Q8_rcptCur_of_fresh_heap {F : Type}
    {entry t post : PanSemStateFiniteExact 64 F}
    (hbase : PtxRelBase true entry t) (hbase' : PtxRelBase true entry post)
    (hARp : ArenaReady post)
    (hfr : FrameOutside t post [(globN t "scratch_ptr", 0)]
      (globN t "heap_ptr", globN post "heap_ptr" - globN t "heap_ptr")) :
    memW post (memW post (globN post "bo" + 32) + 16 * locN entry "index" + 8) =
      memW t (memW t (globN t "bo" + 32) + 16 * locN entry "index" + 8) := by
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := hbase.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨Sc, Nc, _, hWT_w, _, _⟩ := hbase.typing S_e Nd_e hWT_e hD_e
  exact p4Q8_rcptCur_of_unhit hbase hbase'
    (ptxBlockOutUnhit_of_fresh_heap hWT_w hbase.world.1 hARp hfr)

/-! ## The loop-38 invariant -/

/-- The loop-38 invariant at state `t` with index `i_w`.  Everything the
post-loop tail needs: the base and chain anchors, the source-list facts
disjoint from the fresh blocks, the fresh header cells, and the copied
prefix of the backing array.  The out-record lies strictly below the
fresh frontier `lw` (it lives inside the heap); the source list's header,
backing array and entries may also live on the scratch side, in which
case they lie above the whole heap arena and are disjoint from the fresh
blocks that way.  The list header is the word at `w_out + 16`; `lp_w` is
the backing-array base (the header's first word) and `nl_w` the length
(the header's second word). -/
structure P4Q8Loop {F : Type} (entry s_pmc : PanSemStateFiniteExact 64 F)
    (w_out lw capw nl_w w_lp lp_w i_w : BitVec 64)
    (t : PanSemStateFiniteExact 64 F) : Prop where
  base : PtxRelBase true entry t
  chain : p4Q8Chain entry s_pmc w_out lw capw t
  world : WorldOK t
  code : t.code = originalRuntimeCode
  -- constant geometry
  lw_al : lw.toNat % 8 = 0
  lw_ge : sourceBase ≤ lw.toNat
  hp_ent : globN entry "heap_ptr" ≤ lw.toNat
  cap_pos : 1 ≤ capw.toNat
  nl_le_cap : nl_w.toNat ≤ capw.toNat
  nl_28 : nl_w.toNat < 2 ^ 28
  wlp_nat : w_lp.toNat = lw.toNat + 24
  lim64 : lw.toNat + 24 + 8 * capw.toNat ≤ 2 ^ 64
  heap_fr : globN t "heap_ptr" = lw.toNat + 24 + 8 * capw.toNat
  heap_pmc : globN s_pmc "heap_ptr" ≤ globN t "heap_ptr"
  -- locals
  out_local : t.locals.lookup (ofString "out") = some (.val (.word w_out))
  nl_local : t.locals.lookup (ofString "nl") = some (.val (.word nl_w))
  sl_local : t.locals.lookup (ofString "stable_logs") = some (.val (.word lw))
  slp_local : t.locals.lookup (ofString "stable_lp") = some (.val (.word w_lp))
  lp_local : t.locals.lookup (ofString "lp") = some (.val (.word lp_w))
  i_local : t.locals.lookup (ofString "i") = some (.val (.word i_w))
  -- the out-record (inside the heap, strictly below `lw`)
  out_words : WordsOK t (w_out.toNat, 96)
  out_inside : Inside (w_out.toNat, 96) sourceBase (globN t "heap_ptr")
  out_below : w_out.toNat + 96 ≤ lw.toNat
  marks : memW t (w_out.toNat + 80) ≠ 0 →
    memW t (w_out.toNat + 80) % 8 = 0 ∧
    memW t (w_out.toNat + 88) % 8 = 0 ∧
    globN s_pmc "frame_mem_ptr" ≤ memW t (w_out.toNat + 88) ∧
    memW t (w_out.toNat + 88) ≤ memW t (w_out.toNat + 80) ∧
    memW t (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr"
  -- the source logs list (the out-record's list)
  src_nz : memW t (w_out.toNat + 16) ≠ 0
  src_logs : LogsListOK t (memW t (w_out.toNat + 16))
  src_lp_eq : lp_w.toNat = memW t (memW t (w_out.toNat + 16))
  src_len : memW t (memW t (w_out.toNat + 16) + 8) = nl_w.toNat
  geo_out_hdr : p4Q8OldGeo lw.toNat (memW t (w_out.toNat + 16), 24)
  geo_out_arr : p4Q8OldGeo lw.toNat (lp_w.toNat, 8 * nl_w.toNat)
  src_ent : ∀ j, j < nl_w.toNat →
    WordAt t (lp_w.toNat + 8 * j) ∧ LogEntryOK t (memW t (lp_w.toNat + 8 * j)) ∧
    p4Q8OldGeo lw.toNat (memW t (lp_w.toNat + 8 * j), 40)
  -- the fresh blocks
  hdr_words : WordsOK t (lw.toNat, 24)
  arr_words : WordsOK t (lw.toNat + 24, 8 * capw.toNat)
  -- the loop progress
  i_le : i_w.toNat ≤ nl_w.toNat
  copied : ∀ j, j < i_w.toNat →
    memW t (lw.toNat + 24 + 8 * j) = memW t (lp_w.toNat + 8 * j)
  -- the facts the exit bundle (`P4Q8Exit`) reads beyond the loop's own needs
  arena_pmc : ArenaReady s_pmc
  idx_local : t.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index")
  hdr0 : memW t lw.toNat = lw.toNat + 24
  hdr8 : memW t (lw.toNat + 8) = nl_w.toNat
  hdr16 : memW t (lw.toNat + 16) = capw.toNat
  rcpt_cur : memW t (memW t (globN t "bo" + 32) + 16 * locN entry "index" + 8) < 2 ^ 40

/-- The invariant survives the loop's clock decrement. -/
theorem p4Q8Loop_decClock {F : Type} {entry s_pmc : PanSemStateFiniteExact 64 F}
    {w_out lw capw nl_w w_lp lp_w i_w : BitVec 64}
    {t : PanSemStateFiniteExact 64 F} (h : P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w t) :
    P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w (decClockHOLFinite t) :=
  ⟨ptxRelBase_with_locals h.base t.locals (t.clock - 1),
    p4Q8Chain_with_locals t.locals (t.clock - 1) h.chain,
    localsFree_worldOK t t.locals (t.clock - 1) h.world, h.code,
    h.lw_al, h.lw_ge, h.hp_ent, h.cap_pos, h.nl_le_cap, h.nl_28, h.wlp_nat, h.lim64,
    h.heap_fr, h.heap_pmc, h.out_local, h.nl_local, h.sl_local, h.slp_local, h.lp_local,
    h.i_local, h.out_words, h.out_inside, h.out_below, h.marks, h.src_nz, h.src_logs,
    h.src_lp_eq, h.src_len, h.geo_out_hdr, h.geo_out_arr, h.src_ent, h.hdr_words, h.arr_words,
    h.i_le, h.copied, h.arena_pmc, h.idx_local, h.hdr0, h.hdr8, h.hdr16, h.rcpt_cur⟩

/-! ## The body transport -/

/-- The loop-38 body transport, memory half: one iteration of the copy
loop.  At a state `u` satisfying the invariant with index `i_w < nl`,
storing the source word `v` (the log-entry pointer at index `i_w`) into
the array cell `w_lp + 8 * i_w` re-establishes the invariant at the SAME
index `i_w` at the post-store memory (the `i` local is still the old
word; the `setVar` wrapper below bumps it).  The second conjunct is the
copied-prefix extension: the new array cell equals its source cell. -/
theorem p4Q8Loop_store_mem {F : Type}
    {entry s_pmc u : PanSemStateFiniteExact 64 F}
    {w_out lw capw nl_w w_lp lp_w i_w : BitVec 64}
    (h : P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w u)
    (hi_lt : i_w.toNat < nl_w.toNat)
    (v : BitVec 64)
    (hv : u.memory (BitVec.ofNat 64 (lp_w.toNat + 8 * i_w.toNat)) = .word v) :
    P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w
      {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v} ∧
    memW {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}
        (lw.toNat + 24 + 8 * i_w.toNat) =
      memW {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}
        (lp_w.toNat + 8 * i_w.toNat) := by
  -- materialize the invariant's arithmetic facts (omega reads no projections)
  have hlim64 := h.lim64
  have hnlcap := h.nl_le_cap
  have hcapos := h.cap_pos
  have houtbelow := h.out_below
  have hge := h.lw_ge
  have hheapfr := h.heap_fr
  have hhppmc := h.heap_pmc
  have hi64 : i_w.toNat + 1 < 2 ^ 64 := by
    have hile := h.i_le
    have hnl28 := h.nl_28
    omega
  -- ===== 1. the store address =====
  have h3 : lw.toNat + 24 + 8 * i_w.toNat < 2 ^ 64 := by omega
  have hx64 : (w_lp + i_w * 0x0000000000000008#64).toNat < 2 ^ 64 := BitVec.isLt _
  have hx_nat : (w_lp + i_w * 0x0000000000000008#64).toNat =
      lw.toNat + 24 + 8 * i_w.toNat := by
    rw [BitVec.toNat_add, h.wlp_nat, p4Q8_mul8_toNat i_w (by omega)]
    omega
  have haddr_eq : w_lp + i_w * 0x0000000000000008#64 =
      BitVec.ofNat 64 (lw.toNat + 24 + 8 * i_w.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hx_nat, Nat.mod_eq_of_lt h3]
  -- the source cell
  have hsrc_lt64 : lp_w.toNat + 8 * i_w.toNat < 2 ^ 64 := by
    rcases h.geo_out_arr with hg | hg
    · unfold Inside at hg
      obtain ⟨hg1, hg2⟩ := hg
      omega
    · unfold Inside at hg
      obtain ⟨hg1, hg2⟩ := hg
      have hse64 : scratchEnd < 2 ^ 64 := by decide
      omega
  have hsrc_eq : lp_w + i_w * 0x0000000000000008#64 =
      BitVec.ofNat 64 (lp_w.toNat + 8 * i_w.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, p4Q8_mul8_toNat i_w (by omega), BitVec.toNat_ofNat]
    omega
  -- ===== 2. the WorldStep and the raw effects =====
  have hhp_lim : globN u "heap_ptr" ≤ heapLimit := h.world.1.2.2.1
  have hflen : (flattenHOL (.val (.word v) : ValueHOL 64)).length = 1 := by
    simp [flattenHOL]
  have hbase_lu : w_lp.toNat = lw.toNat + 24 := h.wlp_nat
  have hlwal := h.lw_al
  have hbase8 : (lw.toNat + 24) % 8 = 0 := by omega
  have hsz8 : (8 * capw.toNat) % 8 = 0 := by simp
  have hoff8 : (8 * i_w.toNat) % 8 = 0 := by simp
  have hbase_le : lw.toNat ≤ lw.toNat + 24 := by omega
  have hheap_lim : lw.toNat + 24 + 8 * capw.toNat ≤ heapLimit := by
    rw [← h.heap_fr]
    exact hhp_lim
  have hin_blk : Inside (lw.toNat + 24, 8 * capw.toNat) sourceBase (globN u "heap_ptr") := by
    unfold Inside
    dsimp only
    rw [h.heap_fr]
    omega
  have hx_off : w_lp + i_w * 0x0000000000000008#64 =
      w_lp + BitVec.ofNat 64 (8 * i_w.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, p4Q8_mul8_toNat i_w (by omega),
      BitVec.toNat_ofNat]
    omega
  have hdom_dst : u.memaddrs (w_lp + i_w * 0x0000000000000008#64) := by
    have hcellA := h.arr_words.2.2 i_w.toNat (by omega)
    obtain ⟨w9, hd9, _⟩ := hcellA
    rw [← haddr_eq] at hd9
    exact hd9
  have hst : @panMemStoresHOL 64 _ (w_lp + i_w * 0x0000000000000008#64)
      (flattenHOL (.val (.word v))) u.memaddrs
      (fun address => Classical.propDecidable (u.memaddrs address)) u.memory
      = some (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v) :=
    p4Q8_store_word_eq hdom_dst
  have hstep : WorldStep (fun _ => [(lw.toNat + 24, 8 * capw.toNat)]) [] stdKeep NoExtra u none
      {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v} :=
    worldStep_store_in_block h.world hbase_lu hbase8 hsz8 hoff8 hin_blk hx_off
      (by omega) hst
  -- ===== 3. the chain, base and raw effect at the post-store state =====
  have hR_fresh : Inside (lw.toNat + 24, 8 * capw.toNat) (globN entry "heap_ptr")
      (globN u "heap_ptr") :=
    ⟨Nat.le_trans h.hp_ent (Nat.le_add_right _ 24), by omega⟩
  have hRh : Disj (memW u (w_out.toNat + 16), 24) (lw.toNat + 24, 8 * capw.toNat) :=
    p4Q8OldGeo_disj h.geo_out_hdr hbase_le hheap_lim
  have harr_geo : p4Q8OldGeo lw.toNat
      (memW u (memW u (w_out.toNat + 16)), 8 * memW u (memW u (w_out.toNat + 16) + 8)) := by
    rw [h.src_len, ← h.src_lp_eq]
    exact h.geo_out_arr
  have hRa : memW u (w_out.toNat + 16) ≠ 0 →
      Disj (memW u (memW u (w_out.toNat + 16)),
        8 * memW u (memW u (w_out.toNat + 16) + 8)) (lw.toNat + 24, 8 * capw.toNat) := by
    intro _
    rw [h.src_len, ← h.src_lp_eq]
    exact p4Q8OldGeo_disj h.geo_out_arr hbase_le hheap_lim
  have hRe : memW u (w_out.toNat + 16) ≠ 0 → ∀ i, i < memW u (memW u (w_out.toNat + 16) + 8) →
      Disj (memW u (memW u (memW u (w_out.toNat + 16)) + 8 * i), 40)
        (lw.toNat + 24, 8 * capw.toNat) := by
    intro _ i hi
    rw [h.src_len] at hi
    rw [← h.src_lp_eq]
    exact p4Q8OldGeo_disj ((h.src_ent i hi).2.2) hbase_le hheap_lim
  have hw_out_blk : Disj (w_out.toNat, 96) (lw.toNat + 24, 8 * capw.toNat) := by
    refine Or.inr (Or.inr (Or.inl ?_))
    dsimp only
    omega
  have hlogs_list : LogsListOK u (memW u (w_out.toNat + 16)) := h.src_logs
  have hchain' : p4Q8Chain entry s_pmc w_out lw capw
      {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v} :=
    p4Q8Chain_store h.chain h.world hhppmc h.base.heap_entry h.base.frame_entry
      h.base.scratch_entry h.base.arena_entry hR_fresh hbase_lu hbase8 hsz8 hoff8 hin_blk
      hx_off (by omega) hst (Or.inr rfl)
      (by have := h.out_words.1; omega) h.out_words h.out_inside hw_out_blk hlogs_list
      hRh hRa hRe
  have hAR_u : ArenaReady u := ⟨h.world.1.1, h.world.1.2⟩
  have hAR_post : ArenaReady {u with memory :=
      (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)} := hstep.1
  have hcode_u' : {u with memory :=
      (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}.code = originalRuntimeCode :=
    h.code
  obtain ⟨hcell, hEff⟩ := p4Q8_store_effect (t := u) (base := lw.toNat + 24)
    (sz := 8 * capw.toNat) (off := 8 * i_w.toNat) (w_base := w_lp)
    (x := w_lp + i_w * 0x0000000000000008#64) (v := (.val (.word v) : ValueHOL 64))
    (mem' := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)
    h.world hAR_post hcode_u' hbase_lu hbase8 (by omega) hsz8 hin_blk hx_off (by omega)
    (by rw [hst])
  have hbo_unhit : PtxBlockOutUnhit u {u with memory :=
      (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)} :=
    p4Q8_blockOutUnhit_store h.chain h.base.ready_entry (Or.inr rfl) hAR_u hEff
  have hcells : PtxBoCells true entry u {u with memory :=
      (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)} :=
    p4Q8_boCells_store h.base h.chain (Or.inr rfl) (by omega) hstep hbo_unhit
  have hbase' : PtxRelBase true entry {u with memory :=
      (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)} :=
    p4Q8Base_store h.base h.chain hchain' (Or.inr rfl) (by omega) hstep hcells
  -- ===== 4. cell stability =====
  have hne_below : ∀ k : Nat, k + 8 ≤ lw.toNat + 24 →
      BitVec.ofNat 64 k ≠ (w_lp + i_w * 0x0000000000000008#64) := by
    intro k hk
    refine p4Q8_bv_ne_of_toNat_ne ?_
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hx_nat]
    omega
  have hse64 : scratchEnd < 2 ^ 64 := by decide
  have hgeo64 : ∀ a b : Nat, p4Q8OldGeo lw.toNat (a, b) → a + b < 2 ^ 64 := by
    intro a b hgeo
    rcases hgeo with hg | hg
    · unfold Inside at hg
      obtain ⟨hg1, hg2⟩ := hg
      omega
    · unfold Inside at hg
      obtain ⟨hg1, hg2⟩ := hg
      omega
  have hmemW_geo : ∀ a b : Nat, p4Q8OldGeo lw.toNat (a, b) → ∀ k : Nat,
      a ≤ k → k + 8 ≤ a + b →
      memW {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v} k =
      memW u k := by
    intro a b hgeo k hk1 hk2
    exact p4Q8MemW_store_of_geo hcell hgeo ⟨hk1, hk2⟩ hbase_le hheap_lim
      (by have := hgeo64 a b hgeo; omega)
  have hwordAt_geo : ∀ a b : Nat, p4Q8OldGeo lw.toNat (a, b) → ∀ k : Nat,
      a ≤ k → k + 8 ≤ a + b → WordAt u k →
      WordAt {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v} k := by
    intro a b hgeo k hk1 hk2 hwd
    exact p4Q8WordAt_store_of_geo hcell hwd hgeo ⟨hk1, hk2⟩ hbase_le hheap_lim
      (by have := hgeo64 a b hgeo; omega)
  -- below-`lw + 24` cells (out-record and fresh header)
  have hmemW_below : ∀ k : Nat, k + 8 ≤ lw.toNat + 24 →
      memW {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v} k =
      memW u k := fun k hk => p4Q8_memW_updW_away (hne_below k hk)
  have hout16 : memW {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}
      (w_out.toNat + 16) = memW u (w_out.toNat + 16) :=
    hmemW_below _ (by omega)
  -- source-list header cells
  have hhd0 : memW {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}
      (memW u (w_out.toNat + 16)) = memW u (memW u (w_out.toNat + 16)) :=
    hmemW_geo _ _ h.geo_out_hdr _ (by omega) (by omega)
  have hhd8 : memW {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}
      (memW u (w_out.toNat + 16) + 8) = memW u (memW u (w_out.toNat + 16) + 8) :=
    hmemW_geo _ _ h.geo_out_hdr _ (by omega) (by omega)
  -- ===== 5. the source-list transports =====
  have harr64 : memW u (memW u (w_out.toNat + 16)) +
      8 * memW u (memW u (w_out.toNat + 16) + 8) ≤ 2 ^ 64 := by
    rw [h.src_len, ← h.src_lp_eq]
    have := hgeo64 _ _ h.geo_out_arr
    omega
  have hent_geo : ∀ i, i < memW u (memW u (w_out.toNat + 16) + 8) →
      p4Q8OldGeo lw.toNat
        (memW u (memW u (memW u (w_out.toNat + 16)) + 8 * i), 40) := by
    intro i hi
    rw [h.src_len] at hi
    rw [← h.src_lp_eq]
    exact (h.src_ent i hi).2.2
  have hent64 : ∀ i, i < memW u (memW u (w_out.toNat + 16) + 8) →
      memW u (memW u (memW u (w_out.toNat + 16)) + 8 * i) + 40 ≤ 2 ^ 64 := by
    intro i hi
    have := hgeo64 _ _ (hent_geo i hi)
    omega
  have hh64 : memW u (w_out.toNat + 16) + 24 ≤ 2 ^ 64 := by
    have := hgeo64 _ _ h.geo_out_hdr
    omega
  have hsrc_logs' : LogsListOK {u with memory :=
      (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
      (memW u (w_out.toNat + 16)) :=
    p4Q8LogsListOK_store hcell h.src_nz h.src_logs h.geo_out_hdr harr_geo hent_geo
      hbase_le hheap_lim hh64 harr64 hent64
  have hsrc_ent' : ∀ j, j < nl_w.toNat →
      WordAt {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}
        (lp_w.toNat + 8 * j) ∧
      LogEntryOK {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}
        (memW {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}
          (lp_w.toNat + 8 * j)) ∧
      p4Q8OldGeo lw.toNat (memW {u with memory :=
        (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
        (lp_w.toNat + 8 * j), 40) := by
    intro j hj
    have hvalj : memW {u with memory :=
        (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)} (lp_w.toNat + 8 * j) =
        memW u (lp_w.toNat + 8 * j) :=
      hmemW_geo lp_w.toNat (8 * nl_w.toNat) h.geo_out_arr _ (by omega) (by omega)
    obtain ⟨hw1, hw2, hw3⟩ := h.src_ent j hj
    refine ⟨hwordAt_geo lp_w.toNat (8 * nl_w.toNat) h.geo_out_arr
        (lp_w.toNat + 8 * j) (by omega) (by omega) hw1, ?_, by rw [hvalj]; exact hw3⟩
    rw [hvalj]
    exact p4Q8LogEntryOK_store hcell hw2 hw3 hbase_le hheap_lim
      (by have := hgeo64 _ _ hw3; omega)
  -- ===== 6. the copied-cell extension =====
  have hcop : memW {u with memory :=
      (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
      (lw.toNat + 24 + 8 * i_w.toNat) =
      memW {u with memory := (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
      (lp_w.toNat + 8 * i_w.toNat) := by
    have hhit : memW {u with memory :=
        (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
        (lw.toNat + 24 + 8 * i_w.toNat) = v.toNat := by
      rw [haddr_eq]
      exact pmc_memW_updW_same u (lw.toNat + 24 + 8 * i_w.toNat) v
    have hsrcj : memW {u with memory :=
        (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
        (lp_w.toNat + 8 * i_w.toNat) = memW u (lp_w.toNat + 8 * i_w.toNat) :=
      hmemW_geo lp_w.toNat (8 * nl_w.toNat) h.geo_out_arr _ (by omega) (by omega)
    have hsrcv : memW u (lp_w.toNat + 8 * i_w.toNat) = v.toNat := by
      unfold memW
      rw [hv]
    rw [hhit, hsrcj, hsrcv]
  -- ===== 7. the marks transport =====
  have hmarks' : memW {u with memory :=
      (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)} (w_out.toNat + 80) ≠ 0 →
      memW {u with memory := (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
        (w_out.toNat + 80) % 8 = 0 ∧
      memW {u with memory := (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
        (w_out.toNat + 88) % 8 = 0 ∧
      globN s_pmc "frame_mem_ptr" ≤
        memW {u with memory := (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
          (w_out.toNat + 88) ∧
      memW {u with memory := (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
        (w_out.toNat + 88) ≤
        memW {u with memory := (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
          (w_out.toNat + 80) ∧
      memW {u with memory := (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
        (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr" := by
    intro hnz
    rw [hmemW_below (w_out.toNat + 80) (by omega)] at hnz
    obtain ⟨m1, m2, m3, m4, m5⟩ := h.marks hnz
    exact ⟨by rw [hmemW_below (w_out.toNat + 80) (by omega)]; exact m1,
      by rw [hmemW_below (w_out.toNat + 88) (by omega)]; exact m2,
      by rw [hmemW_below (w_out.toNat + 88) (by omega)]; exact m3,
      by rw [hmemW_below (w_out.toNat + 88) (by omega),
        hmemW_below (w_out.toNat + 80) (by omega)]; exact m4,
      by rw [hmemW_below (w_out.toNat + 80) (by omega)]; exact m5⟩
  -- ===== 8. the final assembly =====
  refine ⟨⟨hbase', hchain', hbase'.world, h.code, h.lw_al, h.lw_ge, h.hp_ent, h.cap_pos,
    h.nl_le_cap, h.nl_28, h.wlp_nat, h.lim64, h.heap_fr, h.heap_pmc,
    h.out_local, h.nl_local, h.sl_local, h.slp_local, h.lp_local, h.i_local,
    pmc_wordsOK_updW u (w_lp + i_w * 0x0000000000000008#64) v (w_out.toNat, 96) h.out_words,
    h.out_inside, h.out_below, hmarks', by rw [hout16]; exact h.src_nz,
    by rw [hout16]; exact hsrc_logs',
    by rw [hout16, hhd0]; exact h.src_lp_eq,
    by rw [hout16]; exact hhd8.trans h.src_len,
    by rw [hout16]; exact h.geo_out_hdr, h.geo_out_arr, hsrc_ent',
    pmc_wordsOK_updW u (w_lp + i_w * 0x0000000000000008#64) v (lw.toNat, 24) h.hdr_words,
    pmc_wordsOK_updW u (w_lp + i_w * 0x0000000000000008#64) v
      (lw.toNat + 24, 8 * capw.toNat) h.arr_words,
    h.i_le,
    fun j hj => by
      have harrj : memW {u with memory :=
          (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
          (lw.toNat + 24 + 8 * j) = memW u (lw.toNat + 24 + 8 * j) :=
        p4Q8_memW_updW_away (by
          refine p4Q8_bv_ne_of_toNat_ne ?_
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hx_nat]
          omega)
      have hsrcj : memW {u with memory :=
          (pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v)}
          (lp_w.toNat + 8 * j) = memW u (lp_w.toNat + 8 * j) :=
        hmemW_geo lp_w.toNat (8 * nl_w.toNat) h.geo_out_arr _ (by omega) (by omega)
      rw [harrj, hsrcj]
      exact h.copied j hj,
    h.arena_pmc, h.idx_local,
    (hmemW_below lw.toNat (by omega)).trans h.hdr0,
    (hmemW_below (lw.toNat + 8) (by omega)).trans h.hdr8,
    (hmemW_below (lw.toNat + 16) (by omega)).trans h.hdr16,
    lt_of_eq_of_lt (p4Q8_rcptCur_of_unhit h.base hbase' hbo_unhit) h.rcpt_cur⟩, hcop⟩

/-- The loop-38 body transport: one iteration of the copy loop.  At a
state `u` satisfying the invariant with index `i_w < nl`, storing the
source word `v` (the log-entry pointer at index `i_w`) into the array
cell `w_lp + 8 * i_w` and bumping `i` re-establishes the invariant with
index `i_w + 1`. -/
theorem p4Q8Loop_store {F : Type}
    {entry s_pmc u : PanSemStateFiniteExact 64 F}
    {w_out lw capw nl_w w_lp lp_w i_w : BitVec 64}
    (h : P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w u)
    (hi_lt : i_w.toNat < nl_w.toNat)
    (v : BitVec 64)
    (hv : u.memory (BitVec.ofNat 64 (lp_w.toNat + 8 * i_w.toNat)) = .word v) :
    P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w
      (BitVec.ofNat 64 (i_w.toNat + 1))
      (setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (i_w.toNat + 1))))
        {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}) := by
  obtain ⟨hmem, hcop⟩ := p4Q8Loop_store_mem h hi_lt v hv
  have hi64 : i_w.toNat + 1 < 2 ^ 64 := by
    have hile := hmem.i_le
    have hnl28 := hmem.nl_28
    omega
  have hlu_i : (setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (i_w.toNat + 1))))
      {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}).locals.lookup
      (ofString "i") = some (.val (.word (BitVec.ofNat 64 (i_w.toNat + 1)))) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hlu_others : ∀ name : String, ofString name ≠ ofString "i" →
      (setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (i_w.toNat + 1))))
        {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}).locals.lookup
        (ofString name) =
      {u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}.locals.lookup
        (ofString name) := by
    intro name hne
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    intro hcon
    exact absurd hcon.symm hne
  refine ⟨ptxRelBase_with_locals hmem.base
      (({u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}).locals.update
        (ofString "i", (.val (.word (BitVec.ofNat 64 (i_w.toNat + 1))) : ValueHOL 64)))
      u.clock,
    p4Q8Chain_with_locals
      (({u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}).locals.update
        (ofString "i", (.val (.word (BitVec.ofNat 64 (i_w.toNat + 1))) : ValueHOL 64)))
      u.clock hmem.chain,
    localsFree_worldOK
      ({u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v})
      (({u with memory := pmcUpdW u.memory (w_lp + i_w * 0x0000000000000008#64) v}).locals.update
        (ofString "i", (.val (.word (BitVec.ofNat 64 (i_w.toNat + 1))) : ValueHOL 64)))
      u.clock hmem.world,
    hmem.code, hmem.lw_al, hmem.lw_ge, hmem.hp_ent, hmem.cap_pos, hmem.nl_le_cap, hmem.nl_28,
    hmem.wlp_nat, hmem.lim64, hmem.heap_fr, hmem.heap_pmc,
    by rw [hlu_others "out" (by decide)]; exact hmem.out_local,
    by rw [hlu_others "nl" (by decide)]; exact hmem.nl_local,
    by rw [hlu_others "stable_logs" (by decide)]; exact hmem.sl_local,
    by rw [hlu_others "stable_lp" (by decide)]; exact hmem.slp_local,
    by rw [hlu_others "lp" (by decide)]; exact hmem.lp_local,
    hlu_i,
    hmem.out_words, hmem.out_inside, hmem.out_below, hmem.marks, hmem.src_nz, hmem.src_logs,
    hmem.src_lp_eq, hmem.src_len, hmem.geo_out_hdr, hmem.geo_out_arr, hmem.src_ent,
    hmem.hdr_words, hmem.arr_words,
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; have hile := hmem.i_le; omega,
    fun j hj => by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hj
      by_cases hjie : j < i_w.toNat
      · exact hmem.copied j hjie
      · have hj_eq : j = i_w.toNat := by omega
        subst hj_eq
        exact hcop,
    hmem.arena_pmc,
    by rw [hlu_others "index" (by decide)]; exact hmem.idx_local,
    hmem.hdr0, hmem.hdr8, hmem.hdr16, hmem.rcpt_cur⟩

/-! ## The loop-38 runner -/

/-- The full loop-38 lemma: from the invariant at the post-setup state
(with `i = 0`), the copy loop satisfies `PtxRelRunStrong`.  The exit
obligation is a hypothesis (discharged by the tail file). -/
theorem p4Q8_loop38 {F : Type}
    {entry s_pmc : PanSemStateFiniteExact 64 F}
    {w_out lw capw nl_w w_lp lp_w : BitVec 64} {rest : ProgHOL 64}
    {t : PanSemStateFiniteExact 64 F}
    (hINV : P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w 0x0000000000000000#64 t)
    (hexit : ∀ (t' : PanSemStateFiniteExact 64 F) (i_w : BitVec 64),
      P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w t' →
      evalAt t' p4Loop38Cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry rest t') :
    PtxRelRunStrong entry (.seq (.while p4Loop38Cond p4Loop38Body) rest) t := by
  refine p4Q8_while38 (fun st => ∃ i_w, P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w st)
    (fun st ⟨i_w, hst⟩ hcond => hexit st i_w hst hcond) ?_ t ⟨0x0000000000000000#64, hINV⟩
  intro st ⟨i_w, hINVst⟩ hguard hclk ih
  -- the guard conversion: `i_w < nl` as naturals
  obtain ⟨wg, hwg, hwne⟩ := hguard
  have hcond31 : evalAt st p4Loop31Cond = some (.val (.word wg)) := hwg
  have hi_lt : i_w.toNat < nl_w.toNat :=
    p4Loop31_guard_lt hINVst.i_local hINVst.nl_local hINVst.i_le hINVst.nl_28 wg hwne hcond31
  -- the invariant at the decremented-clock state
  have hINVu : P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w
      (decClockHOLFinite st) := p4Q8Loop_decClock hINVst
  -- the source word at index `i_w`
  obtain ⟨v, hvdom, hvcell⟩ := (hINVu.src_ent i_w.toNat hi_lt).1
  have hlim64 := hINVu.lim64
  have hsrc_lt64 : lp_w.toNat + 8 * i_w.toNat < 2 ^ 64 := by
    rcases hINVu.geo_out_arr with hg | hg
    · unfold Inside at hg
      obtain ⟨hg1, hg2⟩ := hg
      omega
    · unfold Inside at hg
      obtain ⟨hg1, hg2⟩ := hg
      have hse64 : scratchEnd < 2 ^ 64 := by decide
      omega
  have hsrc_addr : lp_w + i_w * 0x0000000000000008#64 =
      BitVec.ofNat 64 (lp_w.toNat + 8 * i_w.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, p4Q8_mul8_toNat i_w (by omega), BitVec.toNat_ofNat]
    omega
  have hx_nat : (w_lp + i_w * 0x0000000000000008#64).toNat =
      lw.toNat + 24 + 8 * i_w.toNat := by
    have hile := hINVu.i_le
    have hnlcap := hINVu.nl_le_cap
    rw [BitVec.toNat_add, hINVu.wlp_nat, p4Q8_mul8_toNat i_w (by omega)]
    omega
  have haddr_eq : w_lp + i_w * 0x0000000000000008#64 =
      BitVec.ofNat 64 (lw.toNat + 24 + 8 * i_w.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hx_nat]
    have h3 : lw.toNat + 24 + 8 * i_w.toNat < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h3]
  have hdom_src : (decClockHOLFinite st).memaddrs
      (lp_w + i_w * 0x0000000000000008#64) := by
    rw [hsrc_addr]
    exact hvdom
  have hdom_dst : (decClockHOLFinite st).memaddrs
      (w_lp + i_w * 0x0000000000000008#64) := by
    have hcellA := hINVu.arr_words.2.2 i_w.toNat (by
      have hile := hINVu.i_le
      have hnlcap := hINVu.nl_le_cap
      omega)
    obtain ⟨w9, hd9, _⟩ := hcellA
    rw [← haddr_eq] at hd9
    exact hd9
  have hed : evalAt (decClockHOLFinite st) p4L38Dst =
      some (.val (.word (w_lp + i_w * 0x0000000000000008#64))) :=
    p4Q8_eval_var_add_mul hINVu.slp_local hINVu.i_local
  have hcell_lp : (decClockHOLFinite st).memory (lp_w + i_w * 0x0000000000000008#64)
      = HolWordLab.word v := by
    rw [hsrc_addr]
    exact hvcell
  have hes : evalAt (decClockHOLFinite st) p4L38Src = some (.val (.word v)) :=
    p4Q8_eval_load_lp hINVu.lp_local hINVu.i_local hdom_src hcell_lp
  have hst : @panMemStoresHOL 64 _ (w_lp + i_w * 0x0000000000000008#64)
      (flattenHOL (.val (.word v))) (decClockHOLFinite st).memaddrs
      (fun address => Classical.propDecidable ((decClockHOLFinite st).memaddrs address))
      (decClockHOLFinite st).memory
      = some (pmcUpdW (decClockHOLFinite st).memory (w_lp + i_w * 0x0000000000000008#64) v) :=
    p4Q8_store_word_eq hdom_dst
  have hi64 : i_w.toNat + 1 < 2 ^ 64 := by
    have hile := hINVu.i_le
    have hnl28 := hINVu.nl_28
    omega
  have hea : evalAt {decClockHOLFinite st with memory :=
      (pmcUpdW (decClockHOLFinite st).memory (w_lp + i_w * 0x0000000000000008#64) v)} p4L38I =
      some (.val (.word (BitVec.ofNat 64 (i_w.toNat + 1)))) :=
    p4Q8_eval_var_add_const hINVu.i_local hi64
  exact p4Run_loop38Body
    (fun st' => ∃ i_w', P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w' st') rfl
    ih
    (fun st' ⟨i_w', hst'⟩ hcond => hexit st' i_w' hst' hcond)
    ⟨w_lp + i_w * 0x0000000000000008#64, v, BitVec.ofNat 64 (i_w.toNat + 1),
      pmcUpdW (decClockHOLFinite st).memory (w_lp + i_w * 0x0000000000000008#64) v,
      hed, hes, hst, hea,
      ⟨BitVec.ofNat 64 (i_w.toNat + 1),
        p4Q8Loop_store hINVu hi_lt v hvcell⟩,
      Or.inr hclk⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
