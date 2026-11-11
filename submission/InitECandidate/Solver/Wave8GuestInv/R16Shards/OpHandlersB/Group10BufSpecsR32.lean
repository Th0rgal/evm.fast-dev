import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreates
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.Common
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.RlpHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.Batch1
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkKeccak256
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChild
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.EvmLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M12.WorldLemmas
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group09LogReturnRevert
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Strong
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexed

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Group 10 fresh-buffer callee specs (R32 slot 4)

This file provides footprint-bounded "fresh-alloc buffer" specifications for the three
callees used by the `op_create` / `op_create2` handler tails:

* `bufSpec_u256_to_be32_r32`            (`u256_to_be32`)
* `bufSpec_compute_contract_address_r32` (`compute_contract_address`)
* `bufSpec_compute_create2_contract_address_r32` (`compute_create2_contract_address`)

**Deviation note.**  The slot asked for `EvmPreservingSpecA (fun _ => True) Q "<fname>"`.
That literal shape is *unsatisfiable* for all three callees: a callee entry state built by
`callEntryStateHOLFinite` has `clock = s.clock - 1` while the enclosing `EvmInv s` bounds the
gas sum `evmR s` from above using the caller's clock, and the entry states additionally break
`evmR` monotonicity; no post-state of the body can repair the invariant at the *entry* clock
(which `EvmInv post` quantifies over).  We therefore use the fresh-buffer precondition
`Pc`, documented per spec, which holds at the two real call sites (`salt = alloc(32)`,
`ca = alloc(24)` / `out = ca`), and supply adapter tails that consume these specs.
-/

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R16Shards (evmInvAt_of_htab_step evaluate_be_eq)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA

/-! ## Part A: shared machinery

`Part A` converts a `HeapByteEff` walk (plus the full globals equality that the
heap-release epilogue of the address functions restores) into an M23
`ByteRegionEffect`, assembles the `EvmAvoids` region bundle for a fresh out buffer
from the caller's out-region `EvmAvoids` plus the world invariant, and packages the
`EvmStep` / `HeadMemChainWF` / `evmR` conclusions shared by all three specs.
-/

/-- Evaluation preserves the shared-memory domain and the base address. -/
private theorem eval_meta_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) : (evaluateHOLFiniteState s p).2.shMemaddrs = s.shMemaddrs ∧ (evaluateHOLFiniteState s p).2.baseAddr = s.baseAddr := by
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata s p
  have invariant := evaluateInvariantsHOLFinite p (PanPropsEvalStateFiniteExact.ofPanSemFinite s) (evaluateHOLFiniteState s p).1 (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState s p).2) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact ⟨hm.2.2.2.1, invariant.2.2.2.2.1⟩

/-- An update of a global with its current value is the identity. -/
private theorem globals_update_self {F : Type} (s : PanSemStateFiniteExact 64 F) (nm : MlS) (v : ValueHOL 64) (hl : s.globals.lookup nm = some v) : s.globals.update (nm, v) = s.globals := by
  apply HolFiniteMapExact.ext
  funext k
  rw [HolFiniteMapExact.lookup_update]
  exact congrFun (FUPDATE_eq_self_of_lookup_some s.globals.lookup nm v hl) k

/-- M23 `ByteRegionEffect` from a `HeapByteEff` walk with full globals equality.
The effect regions are the walk regions plus the two free regions (all writes of
the walks below land inside `Rl ++ [freeGap s, heapFree s]`; note fresh allocations
sit inside `heapFree s` since `heap_ptr` only grows). -/
theorem bre_of_heapByteEff_glob {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String} (heff : R16Shards.WkBlockTxEnc.HeapByteEff s post Rl gw) (hglob : post.globals = s.globals) (hcode : post.code = s.code) (hsh : post.shMemaddrs = s.shMemaddrs) (hba : post.baseAddr = s.baseAddr) : ByteRegionEffect s post (Rl ++ [freeGap s, heapFree s]) where
  code := hcode
  memaddrs := heff.memaddrs
  shMemaddrs := hsh
  baseAddr := hba
  be := heff.be
  globals := hglob
  out_dom := fun a ha => by
    by_contra hne
    exact ha (heff.out_dom a hne)
  cell_frame := fun a ha => by
    by_contra hne
    rcases heff.cell_frame a hne with ⟨i, hi, hpos, hch⟩ | ⟨hpos, hch⟩ | ⟨hpos, hch⟩
    · exact ha i (List.mem_append.2 (Or.inl hi)) hch
    · exact ha (freeGap s) (List.mem_append.2 (Or.inr (by simp))) hch
    · exact ha (heapFree s) (List.mem_append.2 (Or.inr (by simp))) hch
  byte_frame := fun b hb ha => by
    by_contra hne
    rcases heff.byte_frame b hb hne with ⟨i, hi, hin⟩ | hin | hin
    · exact ha i (List.mem_append.2 (Or.inl hi)) hin
    · exact ha (freeGap s) (List.mem_append.2 (Or.inr (by simp))) hin
    · exact ha (heapFree s) (List.mem_append.2 (Or.inr (by simp))) hin

/-- Every frame object is disjoint from the free gap `(frame_mem_ptr, scratch_ptr)`. -/
private theorem allocated_disj_heapFree_r32 {F : Type} {s : PanSemStateFiniteExact 64 F} (hA : ArenaOK s) {i : Ivl} (hi : Allocated s i) : Disj i (heapFree s) := by
  rcases hi with ⟨_, hi2⟩ | ⟨hi1, _⟩
  · exact Or.inr (Or.inr (Or.inl (by unfold heapFree; dsimp only; omega)))
  · have hlim := hA.2.1
    have hfr := hA.2.2.1
    have hsep : heapLimit ≤ scratchStart := by
      rw [R11Shards.heapLimit_val, R11Shards.scratchStart_val]
    have hgap := hA.2.2.2.1
    exact Or.inr (Or.inr (Or.inr (by unfold heapFree; dsimp only; omega)))

private theorem frameObject_disj_freeGap_r32 {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat} {ec o : Ivl} (hA : ArenaOK s) (hFW : FrameWF s S ec) (ho : o ∈ frameObjects s ec) : Disj o (freeGap s) := by
  have hhl_ss : heapLimit ≤ scratchStart := by
    rw [R11Shards.heapLimit_val, R11Shards.scratchStart_val]
  have hfm_ge : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
  have hlim := hA.2.1
  have hgap : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hA.2.2.2.1
  have hhp_fm : globN s "heap_ptr" ≤ globN s "frame_mem_ptr" := by omega
  obtain ⟨hscr, hmem_in, _, _, _, _, _, _, _, _, _, _, hlogs_in, _, hret_in, hll_ok, _⟩ := hFW
  unfold frameObjects at ho
  rcases List.mem_append.1 ho with ho7 | holog
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
    rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := (hscr (ec.1, 280) (by simp)).1.1
      exact Or.inr (Or.inr (Or.inr (by unfold freeGap; dsimp only; omega)))
    · have h := (hscr (ec.2, 104) (by simp)).1.1
      exact Or.inr (Or.inr (Or.inr (by unfold freeGap; dsimp only; omega)))
    · have h := (hscr (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1.1
      exact Or.inr (Or.inr (Or.inr (by unfold freeGap; dsimp only; omega)))
    · have h := hmem_in.2
      exact Or.inr (Or.inr (Or.inl (by unfold freeGap; dsimp only; omega)))
    · have h := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      exact Or.inr (Or.inr (Or.inr (by unfold freeGap; dsimp only; omega)))
    · rcases hlogs_in with h | h
      · have h2 := h.2
        exact Or.inr (Or.inr (Or.inl (by unfold freeGap; dsimp only; omega)))
      · have h1 := h.1
        exact Or.inr (Or.inr (Or.inr (by unfold freeGap; dsimp only; omega)))
    · rcases hret_in with ⟨hz, _⟩ | ⟨h, _⟩
      · unfold frameRet; exact Or.inl (by simp [hz])
      · have h2 := h.2
        exact Or.inr (Or.inr (Or.inl (by unfold freeGap; dsimp only; omega)))
  · unfold frameLogObjects at holog
    dsimp only at holog
    obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
    rw [List.mem_range] at hidx_mem
    rcases hll_ok with hz | ⟨_, _, _, _, hent⟩
    · exfalso
      have hlo := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      dsimp only at hlo
      have hss : 0 < scratchStart := by rw [R11Shards.scratchStart_val]; decide
      omega
    · have hle := (hent idx hidx_mem).2
      have ho_rec : o ∈ logRecordIvls s (memW s (memW s (memW s (ec.1 + 88)) + 8 * idx)) := (List.mem_filter.1 ho_own).1
      simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
      rcases ho_rec with rfl | rfl | rfl | rfl
      · have h := hle.2.1.2
        exact Or.inr (Or.inr (Or.inl (by unfold freeGap; dsimp only; omega)))
      · have h := hle.2.2.2.2.1.2
        exact Or.inr (Or.inr (Or.inl (by unfold freeGap; dsimp only; omega)))
      · have h := hle.2.2.2.2.2.1.2
        exact Or.inr (Or.inr (Or.inl (by unfold freeGap; dsimp only; omega)))
      · have h := hle.2.2.2.2.2.2.2
        exact Or.inr (Or.inr (Or.inl (by unfold freeGap; dsimp only; omega)))

/-- The EvmAvoids region bundle used by all three specs: the caller's fresh out
region, the two keccak scratch buffers, and the two free regions.  The witness
`S`/`Nd` is inherited from the caller's out-region avoids. -/
theorem evmAvoids_buf_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) (hout : EvmAvoids (fun _ => [(locN s "out", n)]) s) : EvmAvoids (fun _ =>
      [(locN s "out", n), bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200), freeGap s, heapFree s]) s := by
  obtain ⟨hA, S, hInv, Nd, hTr, hd⟩ := hout
  have hFW_all := hInv.2.2.2.2.1
  have hWT : WorldTypedWith s S Nd := ⟨hInv.1.1, hInv.1.2.1, hInv.1.2.2.1, hTr⟩
  refine ⟨hA, S, hInv, Nd, hTr, ?_⟩
  intro i hi j hj
  have hi_mem : i ∈ [(locN s "out", n), bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200), freeGap s, heapFree s] := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi_mem
  rcases hi_mem with rfl | rfl | rfl | rfl | rfl
  · exact hd _ (by simp) j hj
  · rcases List.mem_append.1 hj with hj_w | hj_f
    · exact bufferRegion_disj_le hWT ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj_w
    · exact R10Shards.GbodyProcessMsg.bufferRegion_disj_frameObjects_le hInv ("keccak_pad", 136) (by decide) 136 le_rfl j hj_f
  · rcases List.mem_append.1 hj with hj_w | hj_f
    · exact bufferRegion_disj_le hWT ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj_w
    · exact R10Shards.GbodyProcessMsg.bufferRegion_disj_frameObjects_le hInv ("keccak_st", 200) (by decide) 200 le_rfl j hj_f
  · rcases List.mem_append.1 hj with hj_w | hj_f
    · rcases worldTypedIvls_allocated hWT hj_w with h0 | hal
      · exact Or.inr (Or.inl h0)
      · exact (allocated_disj_freeGap hA.2 hal).flip
    · obtain ⟨fo, hfo_map, hj_fo⟩ := List.mem_flatten.1 hj_f
      obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
      exact (frameObject_disj_freeGap_r32 hA.2 (hFW_all ec hec) hj_fo).flip
  · rcases List.mem_append.1 hj with hj_w | hj_f
    · rcases worldTypedIvls_allocated hWT hj_w with h0 | hal
      · exact Or.inr (Or.inl h0)
      · exact (allocated_disj_heapFree_r32 hA.2 hal).flip
    · obtain ⟨fo, hfo_map, hj_fo⟩ := List.mem_flatten.1 hj_f
      obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
      have hgo := frameObject_disj_fresh_heap_g09 hA.2 (le_refl heapLimit) (hFW_all ec hec) hj_fo
      have hlim := hA.2.2.1
      rcases hgo with h0 | hhi | hlo
      · exact Or.inr (Or.inl h0)
      · refine Or.inr (Or.inr (Or.inl ?_)); unfold heapFree; dsimp only; omega
      · refine Or.inr (Or.inr (Or.inr ?_)); unfold heapFree; dsimp only; omega

/-! ## Part B: `u256_to_be32` walk (aligned fast path; `Pc` pins `out % 8 = 0`)

The walk mirrors `Deliveries/M23/ek_u256_to_be32.lean` (whose helpers are private),
restricted to the aligned branch: `Pc` guarantees `locN s "out" % 8 = 0`, so the
`out &&& 7 = 0` test takes the `decCall bswap64` / store fast path. -/

private theorem lookup_bswap64_r32 : originalRuntimeCode.lookup (ofString "bswap64") = some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_bswap64, .one) := lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bswap64) rfl

private theorem lookup_u256_to_be32_r32 : originalRuntimeCode.lookup (ofString "u256_to_be32") = some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "out", .one)], sourceFnBody Guest.Software.guestFn_u256_to_be32, .one) := lookup_of_guestAst_getElem 87 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_to_be32) rfl

private theorem byteAlign_lt_heapEnd_r32 {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain) (addr : BitVec 64) (hdom : s_ma (panByteAlignHOL addr)) : addr.toNat < heapEnd := by
  rw [hma, Wave8Contracts.M23.ordinaryDomain_iff] at hdom
  have hal := panByteAlign_toNat64 addr
  rw [R11Shards.heapEnd_val]
  omega

private theorem word_dom_lt_heapEnd_r32 {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain) (addr : BitVec 64) (hdom : s_ma addr) : addr.toNat + 8 ≤ heapEnd := by
  rw [hma, Wave8Contracts.M23.ordinaryDomain_iff] at hdom
  rw [R11Shards.heapEnd_val]
  omega

private theorem bv_add_off_nat_r32 (base : BitVec 64) (off : Nat) (hbase : base.toNat < heapEnd) (hoff : off ≤ 32) : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  rw [R11Shards.heapEnd_val] at hbase
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  have ho_lt : off < 18446744073709551616 := by omega
  have hsum_lt : base.toNat + off < 18446744073709551616 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, h264, Nat.mod_eq_of_lt ho_lt, Nat.mod_eq_of_lt hsum_lt]

private theorem eval_var_local_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (nm : String) (w : BitVec 64) (hloc : s.locals.lookup (ofString nm) = some (.val (.word w))) : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local (ofString nm)) = some (.val (.word w)) := hloc

private theorem eval_var_local_zero_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (nm : String) (base : BitVec 64) (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local (ofString nm)) = some (.val (.word (base + BitVec.ofNat 64 0))) := by
  have hz : base + BitVec.ofNat 64 0 = base := BitVec.add_zero base
  rw [hz]
  exact hloc

private theorem eval_add_local_const_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (nm : String) (base : BitVec 64) (off : Nat) (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)]) = some (.val (.word (base + BitVec.ofNat 64 off))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (base + w)))) hz

private theorem eval_align8_eq0_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (nm : String) (base : BitVec 64) (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.cmp .equal (.op .and [.var .local (ofString nm), .const 7#64]) (.const 0#64)) = some (.val (.word (if (base &&& 7#64) = 0#64 then 1 else 0))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, Compiler.Encoders.Asm.wordCmpHOL]
  have h7 : (7#64 : BitVec 64) &&& 18446744073709551615#64 = 7#64 := by decide
  change some (ValueHOL.val (HolWordLab.word (if decide ((base &&& (7#64 &&& 18446744073709551615#64)) = 0#64) = true then 1 else 0))) = _
  rw [h7]
  by_cases hc : (base &&& 7#64) = 0#64 <;> simp [hc]

private theorem return_const0_step_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) : (evaluateHOLFiniteState s (.return (.const 0#64))).1 = some (.returned (.val (.word 0))) ∧ (evaluateHOLFiniteState s (.return (.const 0#64))).2 = emptyLocalsHOLFinite s := by
  rw [evaluateHOLFiniteState_return]
  have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0#64) = some (.val (.word 0)) := rfl
  rw [he]
  have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  dsimp only
  rw [if_pos hsz]
  exact ⟨rfl, rfl⟩

private theorem return_eff_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (ex : ExpHOL 64) (Rl : List Ivl) : ByteRegionEffect s (evaluateHOLFiniteState s (.return ex)).2 Rl := by
  have hret : (evaluateHOLFiniteState s (.return ex)).2 = { s with locals := (evaluateHOLFiniteState s (.return ex)).2.locals } := by
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  conv => arg 2; rw [hret]
  exact (ByteRegionEffect.refl s Rl).with_locals_clock _ s.clock

private theorem bre_of_mem_globals_eq_r32 {F : Type} {s post : PanSemStateFiniteExact 64 F} (Rl : List Ivl) (hg : post.globals = s.globals) (hm : post.memory = s.memory) (hc : post.code = s.code) (hma : post.memaddrs = s.memaddrs) (hsh : post.shMemaddrs = s.shMemaddrs) (hba : post.baseAddr = s.baseAddr) (hbe : post.be = s.be) : ByteRegionEffect s post Rl := ⟨hc, hma, hsh, hba, hbe, hg, fun _ _ => by rw [hm], fun _ _ => by rw [hm], fun _ _ _ => by simp [memB, hm, hbe]⟩

private theorem bswap64_body_ro_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).2 Rl := by
  have hb : sourceFnBody Guest.Software.guestFn_bswap64 = InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn Guest.Software.guestFn_bswap64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_bswap64, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  have hasgn : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64), (evaluateHOLFiniteState st (.assign .local nm ex)).2 = { st with locals := (evaluateHOLFiniteState st (.assign .local nm ex)).2.locals } := by
    intro st nm ex
    rw [evaluateHOLFiniteState_assign]
    split
    · rfl
    · split <;> rfl
  have hseq_ro : ∀ (st : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64), ByteRegionEffect st (evaluateHOLFiniteState st a).2 Rl → (∀ m, ByteRegionEffect st m Rl → ByteRegionEffect st (evaluateHOLFiniteState m b).2 Rl) → ByteRegionEffect st (evaluateHOLFiniteState st (.seq a b)).2 Rl := by
    intro st a b ha hb'
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState st a with ⟨r1, s1⟩
    rw [h1] at ha
    cases r1 with
    | none => exact hb' s1 ha
    | some _ => exact ha
  have hasgn_eff : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64), ByteRegionEffect st (evaluateHOLFiniteState st (.assign .local nm ex)).2 Rl := by
    intro st nm ex
    conv => arg 2; rw [hasgn st nm ex]
    exact (ByteRegionEffect.refl st Rl).with_locals_clock _ st.clock
  refine hseq_ro s _ _ (hasgn_eff s _ _) fun s1 hs1 => ?_
  exact hs1.trans (hseq_ro s1 _ _ (hasgn_eff s1 _ _) (fun s2 hs2 => hs2.trans (return_eff_r32 s2 _ Rl)))

private theorem decCall_bswap64_eff_r32 {F : Type} {s : PanSemStateFiniteExact 64 F} {argExp : ExpHOL 64} {cont : ProgHOL 64} {Rl : List Ivl} (hcode : s.code = originalRuntimeCode) (hcont : ∀ mid : PanSemStateFiniteExact 64 F, mid.code = originalRuntimeCode → mid.memaddrs = s.memaddrs → mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") → (∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv))) → ByteRegionEffect mid (evaluateHOLFiniteState mid cont).2 Rl) : ByteRegionEffect s (evaluateHOLFiniteState s (.decCall (ofString "w") .one (ofString "bswap64") [argExp] cont)).2 Rl := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] with _ | vals
  · exact ByteRegionEffect.refl s Rl
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨body', callee, ret'⟩
    · exact ByteRegionEffect.refl s Rl
    · dsimp only
      have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64") _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_bswap64_r32) hl
      subst hinst
      have hret_eq : ret' = .one := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
        split at hl
        · cases hl
        · rename_i eb el es hraw
          have hinj := Option.some.inj hl
          rcases Prod.mk.inj hinj with ⟨_, hr2⟩
          rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
          unfold lookupCodeHOLExact at hraw
          rw [hcode, lookup_bswap64_r32] at hraw
          dsimp only at hraw
          split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
      subst hret_eq
      split
      · exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl := (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro_r32 (callEntryStateHOLFinite s callee) Rl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
        rw [hb] at heff_b
        dsimp only at heff_b ⊢
        have heff_sb : ByteRegionEffect s sb Rl := heff_entry.trans heff_b
        cases rb with
        | none => exact heff_sb
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · rename_i hsh
              have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                rcases v with ⟨⟨wv⟩⟩ | _ | _
                · exact ⟨wv, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
              obtain ⟨wv, rfl⟩ := hvw
              let mid := setVarHOLFinite (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
              have heff_mid : ByteRegionEffect s mid Rl := heff_sb.with_locals_clock _ _
              have hc_mid : mid.code = originalRuntimeCode := heff_mid.code.trans hcode
              have hm_mid : mid.memaddrs = s.memaddrs := heff_mid.memaddrs
              have hout_mid : mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "w" ≠ ofString "out" by decide]
              have hw_mid : ∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv)) := ⟨wv, by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
              have heff_c := hcont mid hc_mid hm_mid hout_mid hw_mid
              exact (heff_mid.trans heff_c).with_locals_clock _ _
            · exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ => exact heff_sb.with_locals_clock _ _
          | «break» | «continue» => exact heff_sb

private theorem seq_call_bswap64_eff_r32 {F : Type} {s : PanSemStateFiniteExact 64 F} {argExp : ExpHOL 64} {cont : ProgHOL 64} {Rl : List Ivl} (hcode : s.code = originalRuntimeCode) (hcont : ∀ mid : PanSemStateFiniteExact 64 F, mid.code = originalRuntimeCode → mid.memaddrs = s.memaddrs → mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") → (∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv))) → ByteRegionEffect mid (evaluateHOLFiniteState mid cont).2 Rl) : ByteRegionEffect s (evaluateHOLFiniteState s (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [argExp]) cont)).2 Rl := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [argExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] with _ | vals
  · rw [hargs] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s Rl
  · rw [hargs] at hc; dsimp only at hc
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s Rl
    · rw [hl] at hc; dsimp only at hc
      have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64") _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_bswap64_r32) hl
      subst hinst
      have hret_eq : ret' = .one := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
        split at hl
        · cases hl
        · rename_i eb el es hraw
          have hinj := Option.some.inj hl
          rcases Prod.mk.inj hinj with ⟨_, hr2⟩
          rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
          unfold lookupCodeHOLExact at hraw
          rw [hcode, lookup_bswap64_r32] at hraw
          dsimp only at hraw
          split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
      subst hret_eq
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl := (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro_r32 (callEntryStateHOLFinite s callee) Rl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
        rw [hb] at hc heff_b
        dsimp only at heff_b
        have heff_sb : ByteRegionEffect s sb Rl := heff_entry.trans heff_b
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hc
            split at hc
            · rename_i hsh
              have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                rcases v with ⟨⟨wv⟩⟩ | _ | _
                · exact ⟨wv, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
              obtain ⟨wv, rfl⟩ := hvw
              split at hc
              · injection hc with hr hsc; subst hr hsc
                dsimp only
                let mid := setKvarHOLFinite .local (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
                have heff_mid : ByteRegionEffect s mid Rl := heff_sb.with_locals_clock _ _
                have hc_mid : mid.code = originalRuntimeCode := heff_mid.code.trans hcode
                have hm_mid : mid.memaddrs = s.memaddrs := heff_mid.memaddrs
                have hout_mid : mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                  simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "w" ≠ ofString "out" by decide]
                have hw_mid : ∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv)) := ⟨wv, by simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
                exact heff_mid.trans (hcont mid hc_mid hm_mid hout_mid hw_mid)
              · injection hc with hr hsc; subst hr hsc; exact heff_sb
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb

private theorem seq_store_word_eff_r32 {F : Type} {s : PanSemStateFiniteExact 64 F} {dstExp valExp : ExpHOL 64} {base w : BitVec 64} {off len : Nat} {cont : ProgHOL 64} (hma : s.memaddrs = ordinaryDomain) (hlen : len ≤ 32) (hoff : off + 8 ≤ len) (hprev : off > 0 → base.toNat < heapEnd) (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp = some (.val (.word (base + BitVec.ofNat 64 off)))) (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp = some (.val (.word w))) (hcont : ∀ s1 : PanSemStateFiniteExact 64 F, base.toNat < heapEnd → s1.code = s.code → s1.memaddrs = s.memaddrs → s1.locals = s.locals → ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) : ByteRegionEffect s (evaluateHOLFiniteState s (.seq (.store dstExp valExp) cont)).2 [(base.toNat, len)] := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s (.store dstExp valExp) with ⟨r1, s1⟩
  cases r1 with
  | some _ =>
    have h1' := h1
    rw [evaluateHOLFiniteState_store, hdst, hval] at h1'
    dsimp only at h1'
    split at h1'
    · cases h1'
    · injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
  | none =>
    have hbase_lt : base.toNat < heapEnd := by
      have hrun' := h1
      rw [evaluateHOLFiniteState_store, hdst, hval] at hrun'
      dsimp only at hrun'
      split at hrun'
      · rename_i m' hst
        unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
        by_cases hd : s.memaddrs (base + BitVec.ofNat 64 off)
        · by_cases hz : off = 0
          · subst hz; have h0 : base + BitVec.ofNat 64 0 = base := by simp
            rw [h0] at hd; have := word_dom_lt_heapEnd_r32 hma base hd; omega
          · exact hprev (by omega)
        · simp [hd] at hst
      · cases hrun'
    have heff1 := ByteRegionEffect.of_store_word (Rl := [(base.toNat, len)]) hma h1 (fun v hv => by rw [hval] at hv; injection hv with h; exact ⟨w, h.symm⟩) (fun addr ha hdom => by
        rw [hdst] at ha
        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
        have hnat := bv_add_off_nat_r32 base off hbase_lt (by omega)
        exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact heff1.1.trans (hcont s1 hbase_lt heff1.1.code heff1.1.memaddrs heff1.2)

/-- The `u256_to_be32` body has region effect `[(locN s "out", 32)]`, for any result. -/
theorem bre_u256_to_be32_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (out : BitVec 64) (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain) (hal : (out &&& 7#64) = 0#64) (hout_lu : s.locals.lookup (ofString "out") = some (.val (.word out))) : ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2 [(out.toNat, 32)] := by
  have hb : sourceFnBody Guest.Software.guestFn_u256_to_be32 = InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn Guest.Software.guestFn_u256_to_be32).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hcond := eval_align8_eq0_r32 s "out" out hout_lu
  have hdc_ne_none : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64)) (c : ProgHOL 64), (∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m c).1 ≠ none) → (evaluateHOLFiniteState st (.decCall nm sh fn args c)).1 ≠ none := by
    intro st nm sh fn args c hc_nn
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) args with _ | _
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite st.code.lookup fn _ with _ | ⟨b', cal', rs'⟩
      · simp
      · dsimp only; split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite st cal') b' with ⟨rb, sb⟩
          cases rb with
          | none => simp
          | some r =>
            cases r with
            | returned _ => dsimp only; split <;> [ exact hc_nn _; simp ]
            | _ => simp
  have hseq_ne_none : ∀ {p1 p2 : ProgHOL 64}, (∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m p2).1 ≠ none) → ∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m (.seq p1 p2)).1 ≠ none := by
    intro p1 p2 hp2 m
    rw [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState m p1 with ⟨r1, m1⟩
    cases r1 with
    | none => exact hp2 m1
    | some _ => simp
  have hret_ne_none : ∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m (.return (.const 0#64))).1 ≠ none := by
    intro m; rw [(return_const0_step_r32 m).1]; simp
  let yesProg256 : ProgHOL 64 := .decCall (ofString "w") .one (ofString "bswap64") [.rfield 3 (.var .local (ofString "a"))] (.seq (.store (.var .local (ofString "out")) (.var .local (ofString "w"))) (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 2 (.var .local (ofString "a"))]) (.seq (.store (.op .add [.var .local (ofString "out"), .const 8#64]) (.var .local (ofString "w"))) (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 1 (.var .local (ofString "a"))]) (.seq (.store (.op .add [.var .local (ofString "out"), .const 16#64]) (.var .local (ofString "w"))) (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 0 (.var .local (ofString "a"))]) (.seq (.store (.op .add [.var .local (ofString "out"), .const 24#64]) (.var .local (ofString "w"))) (.return (.const 0#64)))))))))
  have hyes256_nn : (evaluateHOLFiniteState s yesProg256).1 ≠ none := hdc_ne_none s _ _ _ _ _ (hseq_ne_none (hseq_ne_none (hseq_ne_none (hseq_ne_none (hseq_ne_none (hseq_ne_none (hseq_ne_none hret_ne_none)))))))
  have hgoal_yes256 : evaluateHOLFiniteState s (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7#64]) (.const 0#64)) yesProg256 .skip) (.seq (.call (some (none, none)) (ofString "st_be64") [.var .local (ofString "out"), .rfield 3 (.var .local (ofString "a"))]) (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 8#64], .rfield 2 (.var .local (ofString "a"))]) (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 16#64], .rfield 1 (.var .local (ofString "a"))]) (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 24#64], .rfield 0 (.var .local (ofString "a"))]) (.return (.const 0#64))))))) = evaluateHOLFiniteState s yesProg256 := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
    simp only [hal, ↓reduceIte]
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10]
    rcases hy : evaluateHOLFiniteState s yesProg256 with ⟨ry, sy⟩
    rw [hy] at hyes256_nn
    cases ry with
    | none => exact absurd rfl hyes256_nn
    | some _ => rfl
  rw [hgoal_yes256]
  exact decCall_bswap64_eff_r32 (s := s) (Rl := [(out.toNat, 32)]) hcode fun mid0 hc_m0 hm_m0 hout_m0 ⟨wv0, hw_m0⟩ => by
      have ho0 : mid0.locals.lookup (ofString "out") = some (.val (.word out)) := by
        rw [hout_m0]; exact hout_lu
      refine seq_store_word_eff_r32 (s := mid0) (base := out) (w := wv0) (off := 0) (len := 32) (hm_m0.trans hma) (by omega) (by omega) (fun h => by omega) (eval_var_local_zero_r32 mid0 "out" out ho0) (eval_var_local_r32 mid0 "w" wv0 hw_m0) fun s1 hout_lt hc_s1 hm_s1 hl_s1 => ?_
      refine seq_call_bswap64_eff_r32 (s := s1) (Rl := [(out.toNat, 32)]) (hc_s1.trans hc_m0) fun mid1 hc_m1 hm_m1 hout_m1 ⟨wv1, hw_m1⟩ => ?_
      have ho1 : mid1.locals.lookup (ofString "out") = some (.val (.word out)) := by
        rw [hout_m1, hl_s1]; exact ho0
      refine seq_store_word_eff_r32 (s := mid1) (base := out) (w := wv1) (off := 8) (len := 32) (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))) (by omega) (by omega) (fun _ => hout_lt) (eval_add_local_const_r32 mid1 "out" out 8 ho1) (eval_var_local_r32 mid1 "w" wv1 hw_m1) fun s2 _ hc_s2 hm_s2 hl_s2 => ?_
      refine seq_call_bswap64_eff_r32 (s := s2) (Rl := [(out.toNat, 32)]) (hc_s2.trans hc_m1) fun mid2 hc_m2 hm_m2 hout_m2 ⟨wv2, hw_m2⟩ => ?_
      have ho2 : mid2.locals.lookup (ofString "out") = some (.val (.word out)) := by
        rw [hout_m2, hl_s2]; exact ho1
      refine seq_store_word_eff_r32 (s := mid2) (base := out) (w := wv2) (off := 16) (len := 32) (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))))) (by omega) (by omega) (fun _ => hout_lt) (eval_add_local_const_r32 mid2 "out" out 16 ho2) (eval_var_local_r32 mid2 "w" wv2 hw_m2) fun s3 _ hc_s3 hm_s3 hl_s3 => ?_
      refine seq_call_bswap64_eff_r32 (s := s3) (Rl := [(out.toNat, 32)]) (hc_s3.trans hc_m2) fun mid3 _ hm_m3 hout_m3 ⟨wv3, hw_m3⟩ => ?_
      have ho3 : mid3.locals.lookup (ofString "out") = some (.val (.word out)) := by
        rw [hout_m3, hl_s3]; exact ho2
      refine seq_store_word_eff_r32 (s := mid3) (base := out) (w := wv3) (off := 24) (len := 32) (hm_m3.trans (hm_s3.trans (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))))))) (by omega) (by omega) (fun _ => hout_lt) (eval_add_local_const_r32 mid3 "out" out 24 ho3) (eval_var_local_r32 mid3 "w" wv3 hw_m3) fun s4 _ _ _ _ => return_eff_r32 s4 _ _

/-! ## Part B-2: the `u256_to_be32` preserving spec -/

/-- Fresh-buffer precondition for `u256_to_be32`: the callee's `out` parameter is a
word local denoting a 32-byte fresh region that the EVM frame objects avoid. -/
def PcU256ToBe32_r32 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s => ∃ out : BitVec 64, s.locals.lookup (ofString "out") = some (.val (.word out)) ∧ EvmAvoids (fun _ => [(out.toNat, 32)]) s ∧ out.toNat % 8 = 0 ∧ (out &&& 7#64) = 0#64 ∧ out.toNat + 32 ≤ heapLimit

/-- Footprint-bounded fresh-alloc buffer spec for `u256_to_be32`: the only memory the
body may touch is the fresh 32-byte `out` region, so the EVM invariants, the chain, and
the frame-cell reads (hence `evmR`) are all preserved.  Result-agnostic. -/
theorem bufSpec_u256_to_be32_r32 : EvmPreservingSpecA PcU256ToBe32_r32 (fun s _ post => post.globals = s.globals ∧ memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32)) (ofString "u256_to_be32") := by
  refine ⟨[(ofString "a", .comb [.one, .one, .one, .one]), (ofString "out", .one)], sourceFnBody Guest.Software.guestFn_u256_to_be32, .one, lookup_u256_to_be32_r32, ?_⟩
  intro F s hcode hInv hWF hPc _ _
  obtain ⟨out, hout_lu, hAv, hout8, hal, houtlim⟩ := hPc
  have hma : s.memaddrs = ordinaryDomain := hAv.1.1.memaddrs
  have heff : ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2 [(out.toNat, 32)] := bre_u256_to_be32_r32 s out hcode hma hal hout_lu
  have hAvM : Wave8Contracts.M23.EvmAvoids (fun _ => [(out.toNat, 32)]) s := hAv
  have hStep : Wave8Contracts.M23.EvmStep [] s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2 := ByteRegionEffect.to_evmStep_avoids hAvM heff
  have hWF' : Group10.HeadMemChainWF (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2 := by
    refine headMemChainWF_of_byteRegionEffect hInv hWF hStep.2.2.2 heff ?_ ?_
    · intro i hi
      simp only [List.mem_singleton] at hi
      subst hi
      exact hout8
    · intro ec hec i hi
      simp only [List.mem_singleton] at hi
      subst i
      obtain ⟨S, _, Nd, _, hdjAv⟩ := hAv.2
      have hmem280 : (ec.1, 280) ∈ worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten := List.mem_append_right _ (List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, by simp [frameObjects]⟩)
      have hmem104 : (ec.2, 104) ∈ worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten := List.mem_append_right _ (List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, by simp [frameObjects]⟩)
      have d280 := hdjAv (out.toNat, 32) (List.mem_singleton.2 rfl) (ec.1, 280) hmem280
      have d104 := hdjAv (out.toNat, 32) (List.mem_singleton.2 rfl) (ec.2, 104) hmem104
      exact ⟨Or.inr (by unfold Disj at d280 ⊢; omega), Or.inr (by unfold Disj at d104 ⊢; omega)⟩
  have hRe : R11Shards.OpDispatchSpec.evmR (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2 = R11Shards.OpDispatchSpec.evmR s := evmR_eq_of_bre_disj_g10 hInv hStep.2.2.2 heff houtlim
  have hout_locN : locN s "out" = out.toNat := by simp [locN, hout_lu]
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    simp [evmChain, evmChainFrom]
  obtain ⟨S', _, Nd', _, hdjAv⟩ := hAv.2
  have hmem280 : ((globN s "ev", globN s "cur_cont").1, 280) ∈ worldTypedIvls s S' Nd' ++ ((evmChain s).map (frameObjects s)).flatten := List.mem_append_right _ (List.mem_flatten.2 ⟨frameObjects s (globN s "ev", globN s "cur_cont"), List.mem_map.2 ⟨_, hhead, rfl⟩, by simp [frameObjects]⟩)
  have d280 := hdjAv (out.toNat, 32) (List.mem_singleton.2 rfl) (globN s "ev", 280) hmem280
  obtain ⟨_, _, _, _, _, _, hfw, _⟩ := hInv
  have hw0 := hfw (globN s "ev", globN s "cur_cont") hhead
  have he_lo : globN s "scratch_ptr" ≤ globN s "ev" := (hw0.1 (globN s "ev", 280) (by simp)).1.1
  have hscr_end := (hw0.1 (globN s "ev", 280) (by simp)).1.2
  have hse_val : scratchEnd = 2965299200 := R11Shards.scratchEnd_val
  have hbw : (BitVec.ofNat 64 (globN s "ev" + 32)).toNat = globN s "ev" + 32 := by
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    dsimp only at he_lo hscr_end
    omega
  have hcellEq : memW (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2 (globN s "ev" + 32) = memW s (globN s "ev" + 32) := by
    have hmem := heff.cell_frame (BitVec.ofNat 64 (globN s "ev" + 32)) ?_
    · unfold memW
      rw [hmem]
    · intro i hii hch
      simp only [List.mem_singleton] at hii
      subst i
      rw [hbw] at hch
      rcases hch with ⟨hc1, hc2⟩
      unfold Disj at d280
      dsimp only at d280
      omega
  refine ⟨fun v _ => ⟨⟨hStep.1, hWF'⟩, hStep.2.2.2, hRe.le, ⟨heff.globals, hcellEq⟩⟩, fun _ => ⟨⟨hStep.1, hWF'⟩, hStep.2.2.2, hRe.le⟩⟩

/-! ## Part C: the heap-grow bridge and the `compute_contract_address` spec

The address functions end with `heap_release`, but the keccak-raise exception path
leaves `heap_ptr` bumped, so a full globals equality between `s` and the final
`post` is false in general.  The `EvmPreservingSpecA` bullets, however, never ask
for globals equality: we factor the step through the mid state `{post with
globals := s.globals}` (region writes with globals restored, then a pure
heap-growth step), and each factor is discharged by existing machinery
(`to_evmStep_avoids` resp. `evmInvAt_of_fresh_heap_step`).
-/

/-- Globals at the mid state (post's memory, s's globals) match post wherever the
walk kept the global. -/
private theorem globN_mid_post_r32 {F : Type} {s post : PanSemStateFiniteExact 64 F} {gw : List String} (hk : GlobalsKept gw s post) {n : String} (hn : ofString n ∉ gw.map ofString) : globN { post with globals := s.globals } n = globN post n := by
  have h1 : globN { post with globals := s.globals } n = globN s n := rfl
  have h2 : globN s n = globN post n := by
    simp only [globN]
    rw [hk (ofString n) hn]
  exact h1.trans h2

/-- Every fixed object's base is 8-aligned (`bmi_fixed_base_al`). -/
private theorem fixedBase_al_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (hFT : FixedTyped s) : ∀ i ∈ fixedObjects s, i.1 % 8 = 0 := MptC10C12.bmi_fixed_base_al s hFT

/-- Fabricate the `HeapByteEff` of the mid state (post's memory, s's globals):
the region writes already happened there, but the globals are restored, so all
growth facts become trivial. -/
theorem heapByteEff_mid_r32 {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String} (hARs : ArenaReady s) (heff : R16Shards.WkBlockTxEnc.HeapByteEff s post Rl gw) : R16Shards.WkBlockTxEnc.HeapByteEff s { post with globals := s.globals } Rl gw := by
  refine ⟨⟨@guestInv_congr _ post _ rfl rfl rfl rfl heff.arena.1, @arenaOK_congr _ s _ rfl hARs.2⟩, heff.memaddrs, le_refl _, rfl, le_refl _, heff.be, fun k _ => rfl, heff.out_dom, heff.cell_frame, heff.byte_frame⟩

/-- `evmR` equality for a multi-region `ByteRegionEffect` whose regions are either
empty or avoid the 280-byte frame header (mirrors `evmR_eq_of_bre_disj_g10`). -/
theorem evmR_eq_of_bre_list_r32 {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} (hi : EvmInv s) (hch : evmChain post = evmChain s) (heff : ByteRegionEffect s post Rl) (hRl8 : ∀ i ∈ Rl, i.1 % 8 = 0) (hdj : ∀ ec ∈ evmChain s, ∀ i ∈ Rl, i.2 = 0 ∨ Disj (ec.1, 280) i) : R11Shards.OpDispatchSpec.evmR post = R11Shards.OpDispatchSpec.evmR s := by
  obtain ⟨ha, S, _, _, _, _, hfw, _⟩ := hi
  have hframe := ha.2.2.2.1
  have hscratch := ha.2.2.2.2.1
  have hlim : heapLimit = scratchStart := rfl
  have hse_val : scratchEnd = 2965299200 := R11Shards.scratchEnd_val
  unfold R11Shards.OpDispatchSpec.evmR
  rw [hch]
  congr 1
  apply List.map_congr_left
  intro ec hec
  have hw := hfw ec hec
  have he_lo : globN s "scratch_ptr" ≤ ec.1 := (hw.1 (ec.1, 280) (by simp)).1.1
  have hscr_end := (hw.1 (ec.1, 280) (by simp)).1.2
  have he8 : ec.1 % 8 = 0 := (hw.1 (ec.1, 280) (by simp)).2.1
  have hse := ha.2.2.2.2.2.2.1
  have hcell_eq : ∀ k : Nat, k % 8 = 0 → k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro k hk8 hk
    unfold memW
    have hm_eq : post.memory (BitVec.ofNat 64 (ec.1 + k)) = s.memory (BitVec.ofNat 64 (ec.1 + k)) := by
      have hbw : (BitVec.ofNat 64 (ec.1 + k)).toNat = ec.1 + k := by
        rw [BitVec.toNat_ofNat]
        apply Nat.mod_eq_of_lt
        dsimp only at he_lo hscr_end
        omega
      by_cases hdom : s.memaddrs (BitVec.ofNat 64 (ec.1 + k))
      · refine heff.cell_frame _ fun i hii hch => ?_
        rw [hbw] at hch
        rcases hch with ⟨hc1, hc2⟩
        have hi8 := hRl8 i hii
        rcases hdj ec hec i hii with hi0 | hd
        · omega
        · unfold Disj at hd
          dsimp only at hd
          omega
      · exact heff.out_dom _ hdom
    rw [hm_eq]
  rw [hcell_eq 64 (by omega) (by omega), hcell_eq 192 (by omega) (by omega)]

/-- The heap-grow bridge: from a `HeapByteEff` walk of a fresh-buffer callee whose
only global side effect is bumping `heap_ptr`, derive all the `EvmPreservingSpecA`
bullets.  The mid state carries post's memory with s's globals: the region writes
become an `EvmStep` via `to_evmStep_avoids`, and the pure heap-growth mid → post
step is covered by `evmInvAt_of_fresh_heap_step`. -/
theorem evmBullets_of_heapByteEff_r32 {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} (hInv : EvmInv s) (hs : Group10.HeadMemChainWF s) (hAv : EvmAvoids (fun _ => Rl ++ [freeGap s, heapFree s]) s) (heff : R16Shards.WkBlockTxEnc.HeapByteEff s post Rl ["heap_ptr"]) (hRl8 : ∀ i ∈ Rl, i.1 % 8 = 0) (hcode : post.code = s.code) (hsh : post.shMemaddrs = s.shMemaddrs) (hba : post.baseAddr = s.baseAddr) : EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmChain post = evmChain s ∧ R11Shards.OpDispatchSpec.evmR post = R11Shards.OpDispatchSpec.evmR s := by
  obtain ⟨hA, S, hInvAt, Nd, hTr, hdjAv⟩ := id hAv
  -- the full region list is base-aligned
  have hfm8 : globN s "frame_mem_ptr" % 8 = 0 := hA.2.2.2.2.2.2.2.1
  have hhp8 : globN s "heap_ptr" % 8 = 0 := hA.2.2.2.2.2.2.1
  have hRl8f : ∀ i ∈ Rl ++ [freeGap s, heapFree s], i.1 % 8 = 0 := by
    intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · exact hRl8 i hi
    · rcases List.mem_cons.1 hi with rfl | hi
      · exact hfm8
      · rcases List.mem_singleton.1 hi with rfl
        exact hhp8
  -- the region list avoids every frame object
  have hdj : ∀ ec ∈ evmChain s, ∀ i ∈ Rl ++ [freeGap s, heapFree s], (i.2 = 0 ∨ Disj (ec.1, 280) i) ∧ (i.2 = 0 ∨ Disj (ec.2, 104) i) := by
    intro ec hec i hi
    have hmem280 : (ec.1, 280) ∈ worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten := List.mem_append_right _ (List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, by simp [frameObjects]⟩)
    have hmem104 : (ec.2, 104) ∈ worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten := List.mem_append_right _ (List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, by simp [frameObjects]⟩)
    have d280 := hdjAv i hi (ec.1, 280) hmem280
    have d104 := hdjAv i hi (ec.2, 104) hmem104
    exact ⟨Or.inr (by unfold Disj at d280 ⊢; omega), Or.inr (by unfold Disj at d104 ⊢; omega)⟩
  -- step 1 (s → mid): region writes with the globals restored
  have heffm : R16Shards.WkBlockTxEnc.HeapByteEff s { post with globals := s.globals } Rl ["heap_ptr"] := heapByteEff_mid_r32 hA heff
  have hbreM : ByteRegionEffect s { post with globals := s.globals } (Rl ++ [freeGap s, heapFree s]) := bre_of_heapByteEff_glob heffm rfl hcode hsh hba
  have hAvM : Wave8Contracts.M23.EvmAvoids (fun _ => Rl ++ [freeGap s, heapFree s]) s := hAv
  have hStepM : Wave8Contracts.M23.EvmStep [] s { post with globals := s.globals } := ByteRegionEffect.to_evmStep_avoids hAvM hbreM
  have hWFm : Group10.HeadMemChainWF { post with globals := s.globals } := headMemChainWF_of_byteRegionEffect hInv hs hStepM.2.2.2 hbreM hRl8f hdj
  -- step 2 (mid → post): pure heap growth, no memory change
  obtain ⟨hARm, S2, hbody⟩ := hStepM.1
  have hInvAtM : Wave8Contracts.M23.EvmInvAt { post with globals := s.globals } S2 := hbody
  have hfresh := evmInvAt_of_fresh_heap_step hARm hInvAtM heff.arena rfl heff.hp_le heff.globals (fun a _ => rfl) (fun b _ _ => rfl)
  have hWFpost : Group10.HeadMemChainWF post := headMemChainWF_of_disj_bre hStepM.1 hWFm hfresh.2.1 (globN_mid_post_r32 heff.globals (by decide) |>.symm) (globN_mid_post_r32 heff.globals (by decide) |>.symm) (fun _ hi => (List.not_mem_nil hi).elim) (fun a _ => rfl) (fun _ _ _ hi => (List.not_mem_nil hi).elim)
  refine ⟨⟨heff.arena, S2, hfresh.1⟩, hWFpost, hfresh.2.1.trans hStepM.2.2.2, ?_⟩
  exact hfresh.2.2.trans (evmR_eq_of_bre_list_r32 hInv hStepM.2.2.2 hbreM hRl8f (fun ec hec i hi => (hdj ec hec i hi).1))

/-- Fresh-buffer precondition for `compute_contract_address`: the callee's `out`
parameter is a word local denoting a 20-byte fresh region that the EVM frame
objects avoid. -/
def PcCca_r32 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s => ∃ out addr nonce : BitVec 64, s.locals.lookup (ofString "addr") = some (.val (.word addr)) ∧ s.locals.lookup (ofString "nonce") = some (.val (.word nonce)) ∧ s.locals.lookup (ofString "out") = some (.val (.word out)) ∧ EvmAvoids (fun _ => [(out.toNat, 20)]) s ∧ out.toNat % 8 = 0

/-- Footprint-bounded fresh-alloc buffer spec for `compute_contract_address`:
the body's byte writes stay inside the fresh `out` region and the two keccak
scratch buffers, and its only global side effect is bumping `heap_ptr`, so all
the `EvmPreservingSpecA` bullets follow via the heap-grow bridge.  Result-agnostic
(both the returned and the `EvmErr` raise paths). -/
theorem bufSpec_compute_contract_address_r32 : EvmPreservingSpecA PcCca_r32 (fun _ _ _ => True) (ofString "compute_contract_address") := by
  refine ⟨[(ofString "addr", .one), (ofString "nonce", .one), (ofString "out", .one)], sourceFnBody Guest.Software.guestFn_compute_contract_address, .one, lookup_compute_contract_address, ?_⟩
  intro F s hcode hInv hWF hPc _ hnt
  obtain ⟨out, addr, nonce, haddr, hnonce, hout, hAv, hout8⟩ := hPc
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s (sourceFnBody Guest.Software.guestFn_compute_contract_address)
  have hshm := (eval_meta_r32 s (sourceFnBody Guest.Software.guestFn_compute_contract_address)).1
  have hba := (eval_meta_r32 s (sourceFnBody Guest.Software.guestFn_compute_contract_address)).2
  have hout_locN : locN s "out" = out.toNat := by simp [locN, hout]
  have houtL : EvmAvoids (fun _ => [(locN s "out", 20)]) s := by
    rw [hout_locN]; exact hAv
  obtain ⟨hARs, Sw, hWTw, _⟩ := id hInv
  have hfixal := fixedBase_al_r32 s hWTw.2.2.1
  have hpad_mem : (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append.2; left
    apply List.mem_append.2; left
    apply List.mem_append.2; left
    exact List.mem_map.2 ⟨("keccak_pad", 136), by simp [globalBuffers], rfl⟩
  have hst_mem : (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append.2; left
    apply List.mem_append.2; left
    apply List.mem_append.2; left
    exact List.mem_map.2 ⟨("keccak_st", 200), by simp [globalBuffers], rfl⟩
  have hRl8 : ∀ i ∈ [(locN s "out", 20), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)], i.1 % 8 = 0 := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · show locN s "out" % 8 = 0
      rw [hout_locN]; exact hout8
    · exact hfixal _ hpad_mem
    · exact hfixal _ hst_mem
  have hAvB : EvmAvoids (fun _ =>
      ([(locN s "out", 20), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]) ++
      [freeGap s, heapFree s]) s :=
    evmAvoids_buf_r32 s 20 houtL
  have core : InitECandidate.Solver.Wave8GuestInv.Resumes ((evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_contract_address)).1) → EvmInv (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_contract_address)).2 ∧ Group10.HeadMemChainWF (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_contract_address)).2 ∧ evmChain (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_contract_address)).2 = evmChain s ∧ R11Shards.OpDispatchSpec.evmR (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_contract_address)).2 = R11Shards.OpDispatchSpec.evmR s := fun hres =>
    evmBullets_of_heapByteEff_r32 hInv hWF hAvB (R13Shards.ContractAddressEffect.body_effect s hcode hARs addr nonce out haddr hnonce hout hnt hres) hRl8 hmeta.1 hshm hba
  refine ⟨fun v hv => ?_, fun he => ?_⟩
  · have hb := core (Or.inl ⟨v, hv⟩)
    exact ⟨⟨hb.1, hb.2.1⟩, hb.2.2.1, hb.2.2.2.le, trivial⟩
  · obtain ⟨v, hv⟩ := he
    have hb := core (Or.inr ⟨ofString "EvmErr", v, hv, by decide⟩)
    exact ⟨⟨hb.1, hb.2.1⟩, hb.2.2.1, hb.2.2.2.le⟩


/-! ## Part D: `compute_create2_contract_address` -/

private theorem storeByte_none_or_error_r32 {F : Type} (t : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) : (evaluateHOLFiniteState t (.storeByte dst val)).1 = none ∧ (evaluateHOLFiniteState t (.storeByte dst val)).2.locals = t.locals ∨ (evaluateHOLFiniteState t (.storeByte dst val)).1 = some .error := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · split
    · split
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

private theorem lift_seq_none_r32 {F : Type} {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl} {gw : List String} (ha : evaluateHOLFiniteState s a = (none, m)) (hb : R16Shards.WkBlockTxEnc.HeapByteEff s0 (evaluateHOLFiniteState m b).2 Rl gw) : R16Shards.WkBlockTxEnc.HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]; exact hb

private theorem lift_seq_some_r32 {F : Type} {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {r : PanSemResultExact 64} {Rl : List Ivl} {gw : List String} (ha : evaluateHOLFiniteState s a = (some r, m)) (hm : R16Shards.WkBlockTxEnc.HeapByteEff s0 m Rl gw) : R16Shards.WkBlockTxEnc.HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]; exact hm

private theorem lift_restore_r32 {F : Type} {s0 s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {q : PanSemStateFiniteExact 64 F} {L : HolFiniteMapExact MlS (ValueHOL 64)} {Rl : List Ivl} {gw : List String} (heq : evaluateHOLFiniteState s p = (r, {q with locals := L})) (hq : R16Shards.WkBlockTxEnc.HeapByteEff s0 q Rl gw) : R16Shards.WkBlockTxEnc.HeapByteEff s0 (evaluateHOLFiniteState s p).2 Rl gw := by
  rw [heq]; exact hq.locals_clock L q.clock

private theorem bv_add_off_nat96_r32 (base : BitVec 64) (off : Nat) (hbase : base.toNat < heapEnd) (hoff : off ≤ 96) : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  rw [R11Shards.heapEnd_val] at hbase
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  have ho_lt : off < 18446744073709551616 := by omega
  have hsum_lt : base.toNat + off < 18446744073709551616 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, h264, Nat.mod_eq_of_lt ho_lt, Nat.mod_eq_of_lt hsum_lt]

/-- The create2 contract-address implementation has a narrow byte-write footprint,
stronger than its exported world-growth contract: everything stays inside the fresh
96-byte buffer, the fresh 32-byte hash target, the caller's `out` region and the two
keccak scratch buffers. -/
private theorem body_effect_create2_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s) (addr0 salt0 code0 n0 out0 : BitVec 64) (haddr : s.locals.lookup (ofString "addr") = some (.val (.word addr0))) (hsalt : s.locals.lookup (ofString "salt") = some (.val (.word salt0))) (hcode_lk : s.locals.lookup (ofString "code") = some (.val (.word code0))) (hn_lk : s.locals.lookup (ofString "n") = some (.val (.word n0))) (hout : s.locals.lookup (ofString "out") = some (.val (.word out0))) (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_create2_contract_address)).1 ≠ some .timeOut) (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_create2_contract_address)).1) : R16Shards.WkBlockTxEnc.HeapByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_create2_contract_address)).2 [(locN s "out", 20), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)] ["heap_ptr"] := by
  have hhl_he : heapLimit ≤ heapEnd := by rw [R11Shards.heapLimit_val, R11Shards.heapEnd_val]; decide
  have hout_locN : locN s "out" = out0.toNat := by simp [locN, hout]
  let Rs : List Ivl := [(locN s "out", 20), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
  change R16Shards.WkBlockTxEnc.HeapByteEff s _ Rs ["heap_ptr"]
  have hb : sourceFnBody Guest.Software.guestFn_compute_create2_contract_address = .decCall (ofString "mark") .one (ofString "heap_mark") [] (.decCall (ofString "buf") .one (ofString "alloc") [.const 96] (.seq (.storeByte (ExpHOL.var VarKind.local (ofString "buf")) (.const 255)) (.seq (.call (some (none, none)) (ofString "memcpy") [.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 1], ExpHOL.var VarKind.local (ofString "addr"), .const 20]) (.seq (.call (some (none, none)) (ofString "memcpy") [.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 21], ExpHOL.var VarKind.local (ofString "salt"), .const 32]) (.seq (.call (some (none, none)) (ofString "keccak256") [ExpHOL.var VarKind.local (ofString "code"), ExpHOL.var VarKind.local (ofString "n"), .op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 53]]) (.decCall (ofString "h") .one (ofString "alloc") [.const 32] (.seq (.call (some (none, none)) (ofString "keccak256") [ExpHOL.var VarKind.local (ofString "buf"), .const 85, ExpHOL.var VarKind.local (ofString "h")]) (.seq (.call (some (none, none)) (ofString "memcpy") [ExpHOL.var VarKind.local (ofString "out"), .op .add [ExpHOL.var VarKind.local (ofString "h"), .const 12], .const 20]) (.seq (.call (some (none, none)) (ofString "heap_release") [ExpHOL.var VarKind.local (ofString "mark")]) (.return (.const 0))))))))))) := rfl
  rw [hb] at hnt hres ⊢
  obtain ⟨mark, s1, hhp_s, hmark_nat, hs1_g, hs1_m, hs1_loc, heff01, hnt1, heq1⟩ := WkBlockTxEnc.eval_decCall_heap_mark s "mark" _ Rs ["heap_ptr"] hcode hAR hnt
  rw [heq1] at hres; dsimp only at hres
  refine lift_restore_r32 heq1 ?_
  have hs1_mark : s1.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_addr : s1.locals.lookup (ofString "addr") = some (.val (.word addr0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, haddr, show ofString "mark" ≠ ofString "addr" by decide]
  have hs1_salt : s1.locals.lookup (ofString "salt") = some (.val (.word salt0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsalt, show ofString "mark" ≠ ofString "salt" by decide]
  have hs1_code : s1.locals.lookup (ofString "code") = some (.val (.word code0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hcode_lk, show ofString "mark" ≠ ofString "code" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hn_lk, show ofString "mark" ≠ ofString "n" by decide]
  have hs1_out : s1.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout, show ofString "mark" ≠ ofString "out" by decide]
  obtain ⟨buf, n96, q1, s2, h96_ev, hbuf_hp, hbuf8, hq1_nat, _, hq1_hi, hq1_8, hs2_hp, hs2_g, hs2_m, hs2_loc, heff12, hnt2, hres2, heq2⟩ := WkBlockTxEnc.eval_decCall_alloc_resumes s1 "buf" (.const 96) _ Rs ["heap_ptr"] heff01.arena.1.code heff01.arena (by simp) hnt1 hres
  have hn96 : n96 = 96 := by simp [evalHOLExact] at h96_ev; exact h96_ev.symm
  subst hn96
  have h96_val : (96 : BitVec 64).toNat = 96 := by decide
  rw [h96_val] at hq1_nat
  have hbuf_eq_mark : buf.toNat = mark.toNat := by
    rw [hbuf_hp, hmark_nat]; simp [globN, hs1_g]
  have hq1_eq : q1.toNat = buf.toNat + 96 := by omega
  refine lift_restore_r32 heq2 ?_
  let Rbuf : List Ivl := (buf.toNat, 96) :: Rs
  have hbuf_lt : buf.toNat < heapEnd := by omega
  have h20v : (20 : BitVec 64).toNat = 20 := by decide
  have h32v : (32 : BitVec 64).toNat = 32 := by decide
  have hbuf1 : (buf + 1).toNat = buf.toNat + 1 := bv_add_off_nat96_r32 buf 1 hbuf_lt (by omega)
  have hbuf21 : (buf + 21).toNat = buf.toNat + 21 := bv_add_off_nat96_r32 buf 21 hbuf_lt (by omega)
  have hbuf53 : (buf + 53).toNat = buf.toNat + 53 := bv_add_off_nat96_r32 buf 53 hbuf_lt (by omega)
  have hs2_buf : s2.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_mark : s2.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_mark, show ofString "buf" ≠ ofString "mark" by decide]
  have hs2_addr : s2.locals.lookup (ofString "addr") = some (.val (.word addr0)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_addr, show ofString "buf" ≠ ofString "addr" by decide]
  have hs2_salt : s2.locals.lookup (ofString "salt") = some (.val (.word salt0)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_salt, show ofString "buf" ≠ ofString "salt" by decide]
  have hs2_code : s2.locals.lookup (ofString "code") = some (.val (.word code0)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_code, show ofString "buf" ≠ ofString "code" by decide]
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_n, show ofString "buf" ≠ ofString "n" by decide]
  have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_out, show ofString "buf" ≠ ofString "out" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
  rcases hc3 : evaluateHOLFiniteState s2 (.storeByte (ExpHOL.var VarKind.local (ofString "buf")) (.const 255)) with ⟨r3, s3⟩
  have hsb := R13Shards.Keccak256.byteEff_storeByte (Rl := Rbuf) heff12.arena.1 (ExpHOL.var VarKind.local (ofString "buf")) (.const 255) (fun x hx _ => by
      simp [evalHOLExact, hs2_buf] at hx; subst hx
      exact ⟨(buf.toNat, 96), List.mem_cons_self, le_rfl, by omega⟩)
  rw [hc3] at hsb
  obtain ⟨heff3, _⟩ := hsb
  have hH3 : R16Shards.WkBlockTxEnc.HeapByteEff s2 s3 Rbuf [] := R16Shards.WkBlockTxEnc.HeapByteEff.of_byteEff heff12.arena heff3
  have m01 : R16Shards.WkBlockTxEnc.HeapByteEff s s1 Rbuf ["heap_ptr"] := heff01.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ hg => hg)
  have m12 : R16Shards.WkBlockTxEnc.HeapByteEff s1 s2 Rbuf ["heap_ptr"] := heff12.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ hg => hg)
  have heff_s_s3 : R16Shards.WkBlockTxEnc.HeapByteEff s s3 Rbuf ["heap_ptr"] := (m01.trans m12).trans (hH3.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
  rw [hc3] at hnt2 hres2
  cases r3 with
  | some _ =>
    refine lift_seq_some_r32 hc3 ?_
    exact heff_s_s3.mono (fun i hi _ => by
      simp only [Rbuf, List.mem_cons] at hi
      rcases hi with rfl | hi_rs
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      · exact Or.inl ⟨i, by simpa using hi_rs, le_rfl, le_rfl⟩) (fun _ hg => hg)
  | none =>
    have ho3 := storeByte_none_or_error_r32 s2 (ExpHOL.var VarKind.local (ofString "buf")) (.const 255)
    rw [hc3] at ho3; dsimp only at ho3
    rcases ho3 with ⟨_, hl3⟩ | he3
    · dsimp only at hnt2 hres2
      refine lift_seq_none_r32 hc3 ?_
      have hs3_buf : s3.locals.lookup (ofString "buf") = some (.val (.word buf)) := by rw [hl3]; exact hs2_buf
      have hs3_addr : s3.locals.lookup (ofString "addr") = some (.val (.word addr0)) := by rw [hl3]; exact hs2_addr
      have hs3_salt : s3.locals.lookup (ofString "salt") = some (.val (.word salt0)) := by rw [hl3]; exact hs2_salt
      have hs3_code : s3.locals.lookup (ofString "code") = some (.val (.word code0)) := by rw [hl3]; exact hs2_code
      have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [hl3]; exact hs2_n
      have hs3_mark : s3.locals.lookup (ofString "mark") = some (.val (.word mark)) := by rw [hl3]; exact hs2_mark
      have hs3_out : s3.locals.lookup (ofString "out") = some (.val (.word out0)) := by rw [hl3]; exact hs2_out
      rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
      rcases hc4 : evaluateHOLFiniteState s3 (.call (some (none, none)) (ofString "memcpy") [.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 1], ExpHOL.var VarKind.local (ofString "addr"), .const 20]) with ⟨r4, s4⟩
      have hnt_c4 : r4 ≠ some .timeOut := by rintro rfl; rw [hc4] at hnt2; exact hnt2 rfl
      have h4 := WkBlockTxEnc.eval_call_memcpy_heap s3 (.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 1]) (ExpHOL.var VarKind.local (ofString "addr")) (.const 20) (buf + 1) addr0 20 Rbuf [] heff_s_s3.arena.1.code heff_s_s3.arena (eval_add_local_const_r32 s3 "buf" buf 1 hs3_buf) hs3_addr rfl (fun _ => ⟨(buf.toNat, 96), List.mem_cons_self, by rw [hbuf1]; omega, by rw [hbuf1, h20v]; omega⟩) (by rw [hc4]; exact hnt_c4)
      dsimp only at h4; rw [hc4] at h4 hnt2 hres2
      cases r4 with
      | some _ => exfalso; exact h4.2 (by simp) hres2
      | none =>
        dsimp only at hnt2 hres2
        refine lift_seq_none_r32 hc4 ?_
        obtain ⟨heff34, hs4_loc, hs4_g⟩ := h4.1 rfl
        have heff_s_s4 : R16Shards.WkBlockTxEnc.HeapByteEff s s4 Rbuf ["heap_ptr"] := heff_s_s3.trans (heff34.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
        have hs4_buf : s4.locals.lookup (ofString "buf") = some (.val (.word buf)) := by rw [hs4_loc]; exact hs3_buf
        have hs4_salt : s4.locals.lookup (ofString "salt") = some (.val (.word salt0)) := by rw [hs4_loc]; exact hs3_salt
        have hs4_code : s4.locals.lookup (ofString "code") = some (.val (.word code0)) := by rw [hs4_loc]; exact hs3_code
        have hs4_n : s4.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [hs4_loc]; exact hs3_n
        have hs4_mark : s4.locals.lookup (ofString "mark") = some (.val (.word mark)) := by rw [hs4_loc]; exact hs3_mark
        have hs4_out : s4.locals.lookup (ofString "out") = some (.val (.word out0)) := by rw [hs4_loc]; exact hs3_out
        rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
        rcases hc5 : evaluateHOLFiniteState s4 (.call (some (none, none)) (ofString "memcpy") [.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 21], ExpHOL.var VarKind.local (ofString "salt"), .const 32]) with ⟨r5, s5⟩
        have hnt_c5 : r5 ≠ some .timeOut := by rintro rfl; rw [hc5] at hnt2; exact hnt2 rfl
        have h5 := WkBlockTxEnc.eval_call_memcpy_heap s4 (.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 21]) (ExpHOL.var VarKind.local (ofString "salt")) (.const 32) (buf + 21) salt0 32 Rbuf [] heff_s_s4.arena.1.code heff_s_s4.arena (eval_add_local_const_r32 s4 "buf" buf 21 hs4_buf) hs4_salt rfl (fun _ => ⟨(buf.toNat, 96), List.mem_cons_self, by rw [hbuf21]; omega, by rw [hbuf21, h32v]; omega⟩) (by rw [hc5]; exact hnt_c5)
        dsimp only at h5; rw [hc5] at h5 hnt2 hres2
        cases r5 with
        | some _ => exfalso; exact h5.2 (by simp) hres2
        | none =>
          dsimp only at hnt2 hres2
          refine lift_seq_none_r32 hc5 ?_
          obtain ⟨heff45, hs5_loc, hs5_g⟩ := h5.1 rfl
          have heff_s_s5 : R16Shards.WkBlockTxEnc.HeapByteEff s s5 Rbuf ["heap_ptr"] := heff_s_s4.trans (heff45.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
          have hs5_code : s5.locals.lookup (ofString "code") = some (.val (.word code0)) := by rw [hs5_loc]; exact hs4_code
          have hs5_n : s5.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [hs5_loc]; exact hs4_n
          have hs5_buf : s5.locals.lookup (ofString "buf") = some (.val (.word buf)) := by rw [hs5_loc]; exact hs4_buf
          have hs5_mark : s5.locals.lookup (ofString "mark") = some (.val (.word mark)) := by rw [hs5_loc]; exact hs4_mark
          have hs5_out : s5.locals.lookup (ofString "out") = some (.val (.word out0)) := by rw [hs5_loc]; exact hs4_out
          rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
          rcases hc6 : evaluateHOLFiniteState s5 (.call (some (none, none)) (ofString "keccak256") [ExpHOL.var VarKind.local (ofString "code"), ExpHOL.var VarKind.local (ofString "n"), .op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 53]]) with ⟨r6, s6⟩
          have hnt_c6 : r6 ≠ some .timeOut := by rintro rfl; rw [hc6] at hnt2; exact hnt2 rfl
          have hor_c6 : r6 = none ∨ Resumes r6 := by
            cases r6 with
            | none => exact Or.inl rfl
            | some rk => right; rw [hc6] at hres2; dsimp only at hres2; exact hres2
          have hkpad_eq : globN s5 "keccak_pad" = globN s "keccak_pad" := by
            unfold globN; rw [← heff_s_s5.globals (ofString "keccak_pad") (by decide)]
          have hkst_eq : globN s5 "keccak_st" = globN s "keccak_st" := by
            unfold globN; rw [← heff_s_s5.globals (ofString "keccak_st") (by decide)]
          have h6 := WkBlockTxEnc.eval_call_keccak256_heap s5 (ExpHOL.var VarKind.local (ofString "code")) (ExpHOL.var VarKind.local (ofString "n")) (.op .add [ExpHOL.var VarKind.local (ofString "buf"), .const 53]) code0 n0 (buf + 53) Rbuf [] heff_s_s5.arena.1.code heff_s_s5.arena hs5_code hs5_n (eval_add_local_const_r32 s5 "buf" buf 53 hs5_buf) ⟨(buf.toNat, 96), List.mem_cons_self, by rw [hbuf53]; omega, by rw [hbuf53]; omega⟩ (fun hnz => by
              rw [hkpad_eq] at hnz ⊢
              exact ⟨(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), by simp [Rbuf, Rs], le_rfl, by simp [hnz]⟩)
            (fun hnz => by
              rw [hkst_eq] at hnz ⊢
              exact ⟨(globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), by simp [Rbuf, Rs], le_rfl, by simp [hnz]⟩)
            (by rw [hc6]; exact hnt_c6) (by rw [hc6]; exact hor_c6)
          rw [hc6] at h6 hnt2 hres2
          cases r6 with
          | some _ =>
            have heff_fin : R16Shards.WkBlockTxEnc.HeapByteEff s s6 Rbuf ["heap_ptr"] := heff_s_s5.trans (h6.1.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
            refine lift_seq_some_r32 hc6 ?_
            exact heff_fin.mono (fun i hi _ => by
              simp only [Rbuf, List.mem_cons] at hi
              rcases hi with rfl | hi_rs
              · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
              · exact Or.inl ⟨i, by simpa using hi_rs, le_rfl, le_rfl⟩) (fun _ hg => hg)
          | none =>
            dsimp only at hnt2 hres2
            refine lift_seq_none_r32 hc6 ?_
            obtain ⟨hs6_loc, hs6_g⟩ := h6.2 rfl
            have heff_s_s6 : R16Shards.WkBlockTxEnc.HeapByteEff s s6 Rbuf ["heap_ptr"] := heff_s_s5.trans (h6.1.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
            have hs6_buf : s6.locals.lookup (ofString "buf") = some (.val (.word buf)) := by rw [hs6_loc]; exact hs5_buf
            have hs6_mark : s6.locals.lookup (ofString "mark") = some (.val (.word mark)) := by rw [hs6_loc]; exact hs5_mark
            have hhp6 := heff_s_s6.hp_le
            have hs6_out : s6.locals.lookup (ofString "out") = some (.val (.word out0)) := by rw [hs6_loc]; exact hs5_out
            obtain ⟨hw, n32, q2, s7, h32_ev, hhw_hp, hhw8, hq2_nat, _, hq2_hi, hq2_8, hs7_hp, hs7_g, hs7_m, hs7_loc, heff67, hnt7, hres7, heq7⟩ := WkBlockTxEnc.eval_decCall_alloc_resumes s6 "h" (.const 32) _ Rbuf ["heap_ptr"] heff_s_s6.arena.1.code heff_s_s6.arena (by simp) hnt2 hres2
            have hn32 : n32 = 32 := by simp [evalHOLExact] at h32_ev; exact h32_ev.symm
            subst hn32
            have h32_val : (32 : BitVec 64).toNat = 32 := by decide
            rw [h32_val] at hq2_nat
            have hq2_eq : q2.toNat = hw.toNat + 32 := by omega
            have hhw_lt : hw.toNat < heapEnd := by omega
            have hh12 : (hw + 12).toNat = hw.toNat + 12 := bv_add_off_nat96_r32 hw 12 hhw_lt (by omega)
            refine lift_restore_r32 heq7 ?_
            let Rall : List Ivl := (hw.toNat, 32) :: Rbuf
            have heff_s_s7 : R16Shards.WkBlockTxEnc.HeapByteEff s s7 Rall ["heap_ptr"] := (heff_s_s6.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ hg => hg)).trans (heff67.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ hg => hg))
            have hs7_h : s7.locals.lookup (ofString "h") = some (.val (.word hw)) := by
              rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            have hs7_buf : s7.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
              rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs6_buf, show ofString "h" ≠ ofString "buf" by decide]
            have hs7_mark : s7.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
              rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs6_mark, show ofString "h" ≠ ofString "mark" by decide]
            have hs7_out : s7.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs6_out, show ofString "h" ≠ ofString "out" by decide]
            rw [evaluateHOLFiniteState_seq_line780] at hnt7 hres7
            rcases hc8 : evaluateHOLFiniteState s7 (.call (some (none, none)) (ofString "keccak256") [ExpHOL.var VarKind.local (ofString "buf"), .const 85, ExpHOL.var VarKind.local (ofString "h")]) with ⟨r8, s8⟩
            have hnt_c8 : r8 ≠ some .timeOut := by rintro rfl; rw [hc8] at hnt7; exact hnt7 rfl
            have hor_c8 : r8 = none ∨ Resumes r8 := by
              cases r8 with
              | none => exact Or.inl rfl
              | some rk => right; rw [hc8] at hres7; dsimp only at hres7; exact hres7
            have hkpad_eq7 : globN s7 "keccak_pad" = globN s "keccak_pad" := by
              unfold globN; rw [← heff_s_s7.globals (ofString "keccak_pad") (by decide)]
            have hkst_eq7 : globN s7 "keccak_st" = globN s "keccak_st" := by
              unfold globN; rw [← heff_s_s7.globals (ofString "keccak_st") (by decide)]
            have h8 := WkBlockTxEnc.eval_call_keccak256_heap s7 (ExpHOL.var VarKind.local (ofString "buf")) (.const 85) (ExpHOL.var VarKind.local (ofString "h")) buf 85 hw Rall [] heff_s_s7.arena.1.code heff_s_s7.arena hs7_buf rfl hs7_h ⟨(hw.toNat, 32), List.mem_cons_self, le_rfl, le_rfl⟩ (fun hnz => by
                rw [hkpad_eq7] at hnz ⊢
                exact ⟨(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), by simp [Rall, Rbuf, Rs], le_rfl, by simp [hnz]⟩)
              (fun hnz => by
                rw [hkst_eq7] at hnz ⊢
                exact ⟨(globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), by simp [Rall, Rbuf, Rs], le_rfl, by simp [hnz]⟩)
              (by rw [hc8]; exact hnt_c8) (by rw [hc8]; exact hor_c8)
            rw [hc8] at h8 hnt7 hres7
            cases r8 with
            | some _ =>
              have heff_fin : R16Shards.WkBlockTxEnc.HeapByteEff s s8 Rall ["heap_ptr"] := heff_s_s7.trans (h8.1.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
              refine lift_seq_some_r32 hc8 ?_
              exact heff_fin.mono (fun i hi _ => by
                simp only [Rall, Rbuf, List.mem_cons] at hi
                rcases hi with rfl | rfl | hi_rs
                · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
                · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
                · exact Or.inl ⟨i, by simpa using hi_rs, le_rfl, le_rfl⟩) (fun _ hg => hg)
            | none =>
              dsimp only at hnt7 hres7
              refine lift_seq_none_r32 hc8 ?_
              obtain ⟨hs8_loc, hs8_g⟩ := h8.2 rfl
              have heff_s_s8 : R16Shards.WkBlockTxEnc.HeapByteEff s s8 Rall ["heap_ptr"] := heff_s_s7.trans (h8.1.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
              have hs8_out : s8.locals.lookup (ofString "out") = some (.val (.word out0)) := by rw [hs8_loc]; exact hs7_out
              have hs8_h : s8.locals.lookup (ofString "h") = some (.val (.word hw)) := by rw [hs8_loc]; exact hs7_h
              have hs8_mark : s8.locals.lookup (ofString "mark") = some (.val (.word mark)) := by rw [hs8_loc]; exact hs7_mark
              rw [evaluateHOLFiniteState_seq_line780] at hnt7 hres7
              rcases hc9 : evaluateHOLFiniteState s8 (.call (some (none, none)) (ofString "memcpy") [ExpHOL.var VarKind.local (ofString "out"), .op .add [ExpHOL.var VarKind.local (ofString "h"), .const 12], .const 20]) with ⟨r9, s9⟩
              have hnt_c9 : r9 ≠ some .timeOut := by rintro rfl; rw [hc9] at hnt7; exact hnt7 rfl
              have h9 := WkBlockTxEnc.eval_call_memcpy_heap s8 (ExpHOL.var VarKind.local (ofString "out")) (.op .add [ExpHOL.var VarKind.local (ofString "h"), .const 12]) (.const 20) out0 (hw + 12) 20 Rall [] heff_s_s8.arena.1.code heff_s_s8.arena hs8_out (eval_add_local_const_r32 s8 "h" hw 12 hs8_h) rfl (fun _ => ⟨(locN s "out", 20), by simp [Rall, Rbuf, Rs], by rw [hout_locN], by rw [hout_locN]; change out0.toNat + 20 ≤ out0.toNat + 20; omega⟩) (by rw [hc9]; exact hnt_c9)
              dsimp only at h9; rw [hc9] at h9 hnt7 hres7
              cases r9 with
              | some _ => exfalso; exact h9.2 (by simp) hres7
              | none =>
                dsimp only at hnt7 hres7
                refine lift_seq_none_r32 hc9 ?_
                obtain ⟨heff89, hs9_loc, hs9_g⟩ := h9.1 rfl
                have hs9_mark : s9.locals.lookup (ofString "mark") = some (.val (.word mark)) := by rw [hs9_loc]; exact hs8_mark
                have heff_s_s9 : R16Shards.WkBlockTxEnc.HeapByteEff s s9 Rall ["heap_ptr"] := heff_s_s8.trans (heff89.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
                rw [evaluateHOLFiniteState_seq_line780] at hnt7 hres7
                rcases hc10 : evaluateHOLFiniteState s9 (.call (some (none, none)) (ofString "heap_release") [ExpHOL.var VarKind.local (ofString "mark")]) with ⟨r10, s10⟩
                have hnt_c10 : r10 ≠ some .timeOut := by rintro rfl; rw [hc10] at hnt7; exact hnt7 rfl
                have h10 := WkBlockTxEnc.eval_call_heap_release s9 (ExpHOL.var VarKind.local (ofString "mark")) mark Rall ["heap_ptr"] heff89.arena.1.code heff_s_s9 (by simp) hs9_mark (by rw [hmark_nat]) (by rw [hmark_nat]; exact hAR.2.1) (by rw [hmark_nat]; exact hAR.2.2.1) (by rw [hmark_nat]; exact hAR.2.2.2.2.2.2.1) (by rw [hc10]; exact hnt_c10)
                dsimp only at h10; rw [hc10] at h10
                obtain ⟨rfl, _, _, _, heff_s_s10⟩ := h10
                refine lift_seq_none_r32 hc10 ?_
                have heff_ret : R16Shards.WkBlockTxEnc.HeapByteEff s10 (evaluateHOLFiniteState s10 (.return (.const 0))).2 Rall ["heap_ptr"] := R16Shards.WkBlockTxEnc.HeapByteEff.of_byteEff heff_s_s10.arena (R13Shards.Keccak256.byteEff_return s10 (.const 0) Rall)
                have heff_all : R16Shards.WkBlockTxEnc.HeapByteEff s (evaluateHOLFiniteState s10 (.return (.const 0))).2 Rall ["heap_ptr"] := heff_s_s10.trans heff_ret
                exact heff_all.mono (fun i hi _ => by
                  simp only [Rall, Rbuf, List.mem_cons] at hi
                  rcases hi with rfl | rfl | hi_rs
                  · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
                  · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
                  · exact Or.inl ⟨i, by simpa using hi_rs, le_rfl, le_rfl⟩) (fun _ hg => hg)
    · simp at he3

/-- Fresh-buffer precondition for `compute_create2_contract_address`: the callee's
`out` parameter is a word local denoting a 20-byte fresh region that the EVM frame
objects avoid. -/
def PcCc2_r32 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s => ∃ out addr salt code n : BitVec 64, s.locals.lookup (ofString "addr") = some (.val (.word addr)) ∧ s.locals.lookup (ofString "salt") = some (.val (.word salt)) ∧ s.locals.lookup (ofString "code") = some (.val (.word code)) ∧ s.locals.lookup (ofString "n") = some (.val (.word n)) ∧ s.locals.lookup (ofString "out") = some (.val (.word out)) ∧ EvmAvoids (fun _ => [(out.toNat, 20)]) s ∧ out.toNat % 8 = 0

/-- Footprint-bounded fresh-alloc buffer spec for `compute_create2_contract_address`:
the body's byte writes stay inside the fresh `out` region and the two keccak scratch
buffers, and its only global side effect is bumping `heap_ptr` (released back down at
the end), so all the `EvmPreservingSpecA` bullets follow via the heap-grow bridge.
Result-agnostic (both the returned and the `EvmErr` raise paths). -/
theorem bufSpec_compute_create2_contract_address_r32 : EvmPreservingSpecA PcCc2_r32 (fun _ _ _ => True) (ofString "compute_create2_contract_address") := by
  refine ⟨[(ofString "addr", .one), (ofString "salt", .one), (ofString "code", .one), (ofString "n", .one), (ofString "out", .one)], sourceFnBody Guest.Software.guestFn_compute_create2_contract_address, .one, lookup_compute_create2_contract_address, ?_⟩
  intro F s hcode hInv hWF hPc _ hnt
  obtain ⟨out, addr, salt, code, n, haddr, hsalt, hcode_lk, hn_lk, hout, hAv, hout8⟩ := hPc
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s (sourceFnBody Guest.Software.guestFn_compute_create2_contract_address)
  have hshm := (eval_meta_r32 s (sourceFnBody Guest.Software.guestFn_compute_create2_contract_address)).1
  have hba := (eval_meta_r32 s (sourceFnBody Guest.Software.guestFn_compute_create2_contract_address)).2
  have hout_locN : locN s "out" = out.toNat := by simp [locN, hout]
  have houtL : EvmAvoids (fun _ => [(locN s "out", 20)]) s := by
    rw [hout_locN]; exact hAv
  obtain ⟨hARs, Sw, hWTw, _⟩ := id hInv
  have hfixal := fixedBase_al_r32 s hWTw.2.2.1
  have hpad_mem : (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append.2; left
    apply List.mem_append.2; left
    apply List.mem_append.2; left
    exact List.mem_map.2 ⟨("keccak_pad", 136), by simp [globalBuffers], rfl⟩
  have hst_mem : (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append.2; left
    apply List.mem_append.2; left
    apply List.mem_append.2; left
    exact List.mem_map.2 ⟨("keccak_st", 200), by simp [globalBuffers], rfl⟩
  have hRl8 : ∀ i ∈ [(locN s "out", 20), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)], i.1 % 8 = 0 := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · show locN s "out" % 8 = 0
      rw [hout_locN]; exact hout8
    · exact hfixal _ hpad_mem
    · exact hfixal _ hst_mem
  have hAvB : EvmAvoids (fun _ =>
      ([(locN s "out", 20), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]) ++
      [freeGap s, heapFree s]) s :=
    evmAvoids_buf_r32 s 20 houtL
  have core : InitECandidate.Solver.Wave8GuestInv.Resumes ((evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_create2_contract_address)).1) → EvmInv (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_create2_contract_address)).2 ∧ Group10.HeadMemChainWF (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_create2_contract_address)).2 ∧ evmChain (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_create2_contract_address)).2 = evmChain s ∧ R11Shards.OpDispatchSpec.evmR (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_create2_contract_address)).2 = R11Shards.OpDispatchSpec.evmR s := fun hres =>
    evmBullets_of_heapByteEff_r32 hInv hWF hAvB (body_effect_create2_r32 s hcode hARs addr salt code n out haddr hsalt hcode_lk hn_lk hout hnt hres) hRl8 hmeta.1 hshm hba
  refine ⟨fun v hv => ?_, fun he => ?_⟩
  · have hb := core (Or.inl ⟨v, hv⟩)
    exact ⟨⟨hb.1, hb.2.1⟩, hb.2.2.1, hb.2.2.2.le, trivial⟩
  · obtain ⟨v, hv⟩ := he
    have hb := core (Or.inr ⟨ofString "EvmErr", v, hv, by decide⟩)
    exact ⟨⟨hb.1, hb.2.1⟩, hb.2.2.1, hb.2.2.2.le⟩



theorem epsA_allocFresh_r32 : EvmPreservingSpecA (fun _ => True) (fun s v post => post.memory = s.memory ∧ GlobalsKept ["heap_ptr"] s post ∧ ∃ p n : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word n)) ∧ v = .val (.word p) ∧ p.toNat = globN s "heap_ptr" ∧ p.toNat % 8 = 0 ∧ p.toNat + n.toNat ≤ globN post "heap_ptr" ∧ EvmAvoids (fun _ => [(p.toNat, n.toNat)]) post) (ofString "alloc") := by
  refine ⟨_, _, _, GuestTrapAndLookup.lookup_alloc, ?_⟩
  intro F s hc hi hw _ ⟨vals, hl⟩ _
  have hlen : ∃ v0, vals = [v0] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "alloc") vals _ _ _ hl
    simp only [Flapjack.lookupCodeHOLExact, GuestTrapAndLookup.lookup_alloc] at hx
    rcases vals with _ | ⟨v0, _ | _⟩ <;> simp at hx
    exact ⟨v0, rfl⟩
  obtain ⟨v0, rfl⟩ := hlen
  obtain ⟨_, _, n, rfl, hn⟩ := one_word_arg_lookup GuestTrapAndLookup.lookup_alloc hl
  obtain ⟨p, hp⟩ := hi.1.2.2.2.2.2.2.2.2.2 "heap_ptr" (by decide)
  change s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) at hp
  have hpn : p.toNat = globN s "heap_ptr" := by simp [globN, hp]
  have hple : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    rw [hpn]; exact hi.1.2.2.1
  dsimp only
  rcases hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) with ⟨r, post⟩
  refine ⟨fun v hv => ?_, fun herr => ?_⟩
  · have hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned v), post) := by rw [hr]; exact congrArg (fun r => (r, post)) hv
    obtain ⟨hiw, hwp, hch, hR⟩ := alloc_return_aligned_g10 s p n hi hw hc hp hn v post hrun
    obtain ⟨hvret, hm, _⟩ := alloc_return_frame_g10 s p n hc hple hp hn v post hrun
    obtain ⟨_, hpnB, hal8, hbnd, _, _⟩ := alloc_return_buffer_bounds_g10 s p n hi hc hp hn v post hrun
    have hAvP := alloc_return_avoids_g10 s p n hi hw hc hp hn v post hrun
    have hM := M13.evaluate_alloc_body_general s p n hc hple hp hn v
    rw [hr] at hM
    obtain ⟨_, hgg, _, _, _, _⟩ := hM hv
    have hgK : GlobalsKept ["heap_ptr"] s post := by
      intro k hk
      have hne : ofString "heap_ptr" ≠ k := by intro he; subst k; exact hk (by simp)
      rw [hgg]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
    refine ⟨⟨hiw, hwp⟩, hch, le_of_eq hR, hm, hgK, p, n, hn, hvret, hpn, hal8, hbnd, hAvP⟩
  · have hno := OpHandlers.alloc_body_no_evmErr s hc
    rw [hr] at hno
    exact False.elim (hno herr)

theorem evmAvoids_with_locals_clock_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) {os : List Ivl} (h : EvmAvoids (fun _ => os) s) : EvmAvoids (fun _ => os) { s with locals := locals, clock := k } := by
  obtain ⟨hA, S, hInv, Nd, hTr, hD⟩ := h
  have hA' : ArenaReady { s with locals := locals, clock := k } := localsFree_arenaReady s locals k hA
  have htr_eq : TriesTypedWith { s with locals := locals, clock := k } S Nd ↔ TriesTypedWith s S Nd := Iff.rfl
  have hinvAt_eq : EvmInvAt { s with locals := locals, clock := k } S ↔ EvmInvAt s S := by
    simp only [EvmInvAt, FrameWF, MsgOwned, worldTyped_with_locals, evmChain_with_locals]
    exact Iff.rfl
  refine ⟨hA', S, hinvAt_eq.2 hInv, Nd, htr_eq.2 hTr, ?_⟩
  change IvlsDisj os (worldTypedIvls { s with locals := locals, clock := k } S Nd ++ (List.map (frameObjects { s with locals := locals, clock := k }) (evmChain { s with locals := locals, clock := k })).flatten)
  rw [evmChain_with_locals s locals k]
  exact hD

theorem evmAvoids_shrink_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) {a m n : Nat} (h : EvmAvoids (fun _ => [(a, m)]) s) (hle : n ≤ m) : EvmAvoids (fun _ => [(a, n)]) s := by
  obtain ⟨hA, S, hInv, Nd, hTr, hD⟩ := h
  refine ⟨hA, S, hInv, Nd, hTr, ?_⟩
  intro i hi j hj
  have hi2 : i = (a, n) := by simp only [List.mem_singleton] at hi; exact hi
  subst hi2
  have hd : Disj (a, m) j := hD (a, m) (by simp) j hj
  rcases hd with h0 | h0 | h1 | h1
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr h1))

theorem bv_and7_zero_r32 {w : BitVec 64} (h : w.toNat % 8 = 0) : (w &&& 7#64) = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_and]
  simp only [BitVec.getLsbD, Nat.zero_testBit, Bool.and_eq_false_iff]
  by_cases h3 : i < 3
  · interval_cases i
    · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]; norm_num; omega
    · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]; norm_num; omega
    · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]; norm_num; omega
  · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have h8 : (8 : Nat) ≤ 2 ^ i := Nat.pow_le_pow_right (n := 2) (by decide) (i := 3) (j := i) (by omega)
    have hd : (7 : Nat) / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
    norm_num
    intro hcon
    simp [hd]

theorem lookup_u256_out_r32 {v0 v1 : ValueHOL 64} {body' : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL} (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_to_be32") [v0, v1] = some (body', callee, ret')) : ∃ out : BitVec 64, v1 = .val (.word out) ∧ callee.lookup (ofString "out") = some (.val (.word out)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "u256_to_be32") [v0, v1] body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_u256_to_be32_b] at hx
  split at hx
  · rename_i hcond
    have heq := Option.some.inj hx
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hloc, rfl⟩
    have hall : ¬ofString "a" = ofString "out" ∧ shapeEqHOL (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (shapeOfHOLExact v0) = true ∧ shapeEqHOL ShapeHOL.one (shapeOfHOLExact v1) = true := by simpa [List.map] using hcond
    have hsh1 := hall.2.2
    rcases v1 with ⟨⟨w⟩⟩ | _ | _
    · refine ⟨w, rfl, ?_⟩
      have hfn := congrFun hloc.symm (ofString "out")
      simpa [FUPDATE_LIST, FUPDATE, show ofString "out" ≠ ofString "a" from by decide] using hfn
    · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
    · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
  · cases hx

theorem lookup_cca_args_r32 {v0 v1 v2 : ValueHOL 64} {body' : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL} (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "compute_contract_address") [v0, v1, v2] = some (body', callee, ret')) : ∃ addr nonce out : BitVec 64, v0 = .val (.word addr) ∧ v1 = .val (.word nonce) ∧ v2 = .val (.word out) ∧ callee.lookup (ofString "addr") = some (.val (.word addr)) ∧ callee.lookup (ofString "nonce") = some (.val (.word nonce)) ∧ callee.lookup (ofString "out") = some (.val (.word out)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "compute_contract_address") [v0, v1, v2] body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_compute_contract_address] at hx
  rcases v0 with ⟨⟨w0⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
  rcases hx with ⟨_, hbody_eq, hloc, hret_eq⟩
  refine ⟨w0, w1, w2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · have hfn := congrFun hloc.symm (ofString "addr")
    simpa [FUPDATE_LIST, FUPDATE, show ofString "addr" ≠ ofString "nonce" from by decide, show ofString "addr" ≠ ofString "out" from by decide] using hfn
  · have hfn := congrFun hloc.symm (ofString "nonce")
    simpa [FUPDATE_LIST, FUPDATE, show ofString "nonce" ≠ ofString "addr" from by decide, show ofString "nonce" ≠ ofString "out" from by decide] using hfn
  · have hfn := congrFun hloc.symm (ofString "out")
    simpa [FUPDATE_LIST, FUPDATE, show ofString "out" ≠ ofString "addr" from by decide, show ofString "out" ≠ ofString "nonce" from by decide] using hfn

theorem lookup_cc2_args_r32 {v0 v1 v2 v3 v4 : ValueHOL 64} {body' : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL} (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "compute_create2_contract_address") [v0, v1, v2, v3, v4] = some (body', callee, ret')) : ∃ addr salt code n out : BitVec 64, v0 = .val (.word addr) ∧ v1 = .val (.word salt) ∧ v2 = .val (.word code) ∧ v3 = .val (.word n) ∧ v4 = .val (.word out) ∧ callee.lookup (ofString "addr") = some (.val (.word addr)) ∧ callee.lookup (ofString "salt") = some (.val (.word salt)) ∧ callee.lookup (ofString "code") = some (.val (.word code)) ∧ callee.lookup (ofString "n") = some (.val (.word n)) ∧ callee.lookup (ofString "out") = some (.val (.word out)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "compute_create2_contract_address") [v0, v1, v2, v3, v4] body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_compute_create2_contract_address] at hx
  rcases v0 with ⟨⟨w0⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> rcases v4 with ⟨⟨w4⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
  rcases hx with ⟨_, hbody_eq, hloc, hret_eq⟩
  refine ⟨w0, w1, w2, w3, w4, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have hfn := congrFun hloc.symm (ofString "addr")
    simpa [FUPDATE_LIST, FUPDATE, show ofString "addr" ≠ ofString "salt" from by decide, show ofString "addr" ≠ ofString "code" from by decide, show ofString "addr" ≠ ofString "n" from by decide, show ofString "addr" ≠ ofString "out" from by decide] using hfn
  · have hfn := congrFun hloc.symm (ofString "salt")
    simpa [FUPDATE_LIST, FUPDATE, show ofString "salt" ≠ ofString "addr" from by decide, show ofString "salt" ≠ ofString "code" from by decide, show ofString "salt" ≠ ofString "n" from by decide, show ofString "salt" ≠ ofString "out" from by decide] using hfn
  · have hfn := congrFun hloc.symm (ofString "code")
    simpa [FUPDATE_LIST, FUPDATE, show ofString "code" ≠ ofString "addr" from by decide, show ofString "code" ≠ ofString "salt" from by decide, show ofString "code" ≠ ofString "n" from by decide, show ofString "code" ≠ ofString "out" from by decide] using hfn
  · have hfn := congrFun hloc.symm (ofString "n")
    simpa [FUPDATE_LIST, FUPDATE, show ofString "n" ≠ ofString "addr" from by decide, show ofString "n" ≠ ofString "salt" from by decide, show ofString "n" ≠ ofString "code" from by decide, show ofString "n" ≠ ofString "out" from by decide] using hfn
  · have hfn := congrFun hloc.symm (ofString "out")
    simpa [FUPDATE_LIST, FUPDATE, show ofString "out" ≠ ofString "addr" from by decide, show ofString "out" ≠ ofString "salt" from by decide, show ofString "out" ≠ ofString "code" from by decide, show ofString "out" ≠ ofString "n" from by decide] using hfn

theorem evalList_var_last_r32 {F : Type} (t : PanSemStateFiniteExact 64 F) (es : List (ExpHOL 64)) (nm : MlS) {values : List (ValueHOL 64)} (ha : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) (es ++ [.var .local nm]) = some values) : ∃ (front : List (ValueHOL 64)) (w : ValueHOL 64), values = front ++ [w] ∧ t.locals.lookup nm = some w := by
  rw [evalListHOLFinite_eq_toExact] at ha
  induction es generalizing values with
  | nil =>
    cases hw : t.locals.lookup nm with
    | none =>
      simp [evalListHOLExact, evalHOLExact, hw] at ha
    | some w =>
      simp [evalListHOLExact, evalHOLExact, hw] at ha
      exact ⟨[], w, ha.symm, rfl⟩
  | cons e es ih =>
    simp only [List.cons_append, evalListHOLExact] at ha
    rcases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e with _ | x
    · simp [he] at ha
    · rcases hrest : @evalListHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (es ++ [.var .local nm]) with _ | vs
      · simp [he, hrest] at ha
      · simp only [he, hrest] at ha
        injection ha with ha'
        subst ha'
        obtain ⟨front, w, hvs, hw⟩ := ih (values := vs) hrest
        exact ⟨x :: front, w, by rw [hvs, List.cons_append], hw⟩

def CaFresh_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop := ∃ p : BitVec 64, s.locals.lookup (ofString "ca") = some (.val (.word p)) ∧ EvmAvoids (fun _ => [(p.toNat, 24)]) s ∧ p.toNat % 8 = 0

theorem createChargedSuffixTail_buf_r32 {F : Type} (hW : WorldAccountSpecsA) (hcc : EvmPreservingSpecA PcCca_r32 (fun _ _ _ => True) (ofString "compute_contract_address")) (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post) (ofString "generic_create")) : ChildContinuationA (F := F) (fun _ => True) (handlerSuffix_g10 1 createChargedSuffix_g10) := by
  apply ccA_dec_g10 (Q := fun _ => True) (fun t v hv hi hp => trivial)
  apply ccA_decCall_g10 (Q := fun _ => True) hW.epsA_get_account (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial) (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ _ _ => trivial)
  apply ccA_decCall_g10 (Q := CaFresh_r32) epsA_allocFresh_r32 (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial) (hstep := fun t values body callee rs v cpost hi hw hp ha hl hci hw2 hch hq => by
      have hvals : values = [.val (.word (24 : BitVec 64))] := by
        simpa [evalListHOLExact, evalHOLExact, FrontendCodecComputation.expToHOLStructural] using ha.symm
      subst values
      obtain ⟨_, _, n, hvn, hn⟩ := one_word_arg_lookup GuestTrapAndLookup.lookup_alloc hl
      have hn24 : n = (24 : BitVec 64) := by simpa using hvn.symm
      subst n
      obtain ⟨hm, hgK, p, n', hn'lu, hvret, hpn, hal8, hbnd, hAvP⟩ := hq
      have hn'24 : n' = (24 : BitVec 64) := by
        have h0 : (callEntryStateHOLFinite t callee).locals.lookup (ofString "n") = some (.val (.word 24)) := hn
        rw [h0] at hn'lu
        have h12 := Option.some.inj hn'lu
        injection h12 with h22
        injection h22 with h23
        exact h23.symm
      subst n'
      refine ⟨p, ?_, ?_, hal8⟩
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        exact hvret
      · have h24 : (24 : BitVec 64).toNat = 24 := by decide
        rw [h24] at hAvP
        exact evmAvoids_with_locals_clock_r32 cpost (t.locals.update (ofString "ca", v)) cpost.clock hAvP)
  apply ccA_seq_call_g10 (Q := fun _ => True) hcc (hentry := fun t values body callee rs hc hi hw hp ha hl => by
      rw [hc] at hl
      obtain ⟨front, w, hvals, hw2⟩ := evalList_var_last_r32 t [.load ShapeHOL.one (.op BinOp.add [.var VarKind.local (ofString "msg"), .const (BitVec.ofNat 64 32)]), .load ShapeHOL.one (.op BinOp.add [.var VarKind.local (ofString "a"), .const (BitVec.ofNat 64 0)])] (ofString "ca") ha
      have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "compute_contract_address") values body callee rs hl
      simp only [Flapjack.lookupCodeHOLExact, lookup_compute_contract_address] at hx
      rcases values with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩⟩
      · simp at hx
      · simp at hx
      · simp at hx
      · obtain ⟨addr, nonce, out, hv0w, hv1w, hv2w, hcaddr, hcnonce, hcout⟩ := lookup_cca_args_r32 hl
        rcases front with _ | ⟨x, tl⟩
        · simp at hvals
        · rcases tl with _ | ⟨y, tl2⟩
          · simp at hvals
          · rcases tl2 with _ | ⟨z, rest⟩
            · simp only [List.cons_append, List.nil_append] at hvals
              obtain ⟨rfl, rfl, rfl⟩ := hvals
              obtain ⟨p, hpca, hpAv, hp8⟩ := hp
              rw [hv2w] at hw2
              have houtp : out = p := by
                have h1 := hw2.symm.trans hpca
                have h2 := Option.some.inj h1
                simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at h2
                exact h2
              rw [houtp] at hcout
              refine ⟨p, addr, nonce, hcaddr, hcnonce, hcout, ?_, hp8⟩
              exact evmAvoids_with_locals_clock_r32 t callee (t.clock - 1) (evmAvoids_shrink_r32 t hpAv (by omega))
            · simp only [List.cons_append] at hvals
              injection hvals with _ h1
              injection h1 with _ h2
              injection h2 with _ h3
              cases rest <;> simp at h3
      · simp at hx)
    (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial)
  apply ccA_decCall_g10 (Q := fun _ => True) epsA_sat_word (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial) (hstep := by intros; trivial)
  apply ccA_decCall_g10 (Q := fun _ => True) hgc (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial) (hstep := by intros; trivial)
  apply ccA_seq_ite_g10
  · intro t w hcond hw0
    exact ccA_seq_call_g10 (Q := fun _ => True) epsA_pc_add (hentry := fun t values body callee rs hc hi hw hp ha hl => trivial) (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial) (ccA_ret_g10 (.const 0#64))
  · intro t hcond
    exact ccA_seq_skip_g10 (ccA_ret_g10 (.const 0#64))

theorem op_create_run_full_buf_r32 {F : Type} (s0 : PanSemStateFiniteExact 64 F) (hW : WorldAccountSpecsA) (hcc : EvmPreservingSpecA PcCca_r32 (fun _ _ _ => True) (ofString "compute_contract_address")) (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post) (ofString "generic_create")) : HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create) := create_prefix_through_extend_g10 s0 (handlerRunA_of_childContinuation_g10 s0 _ _ (createChargedSuffixTail_buf_r32 hW hcc hgc))

def SaltFresh_r32 {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop := ∃ p : BitVec 64, s.locals.lookup (ofString "salt") = some (.val (.word p)) ∧ EvmAvoids (fun _ => [(p.toNat, 32)]) s ∧ p.toNat % 8 = 0 ∧ p.toNat + 32 ≤ heapLimit

theorem create2ChargedSuffixTail_buf_r32 {F : Type} (hU : EvmPreservingSpecA PcU256ToBe32_r32 (fun s _ post => post.globals = s.globals ∧ memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32)) (ofString "u256_to_be32")) (hcc2 : EvmPreservingSpecA PcCc2_r32 (fun _ _ _ => True) (ofString "compute_create2_contract_address")) (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post) (ofString "generic_create")) : ChildContinuationA (F := F) (fun s => MemoryExpansionLocal_g10 s ∧ SaltFresh_r32 s) (handlerSuffix_g10 1 create2ChargedSuffix_g10) := by
  apply ccA_seq_call_g10 (Q := MemoryExpansionLocal_g10) hU (hentry := fun t values body callee rs hc hi hw hp ha hl => by
      rw [hc] at hl
      obtain ⟨front, w, hvals, hw2⟩ := evalList_var_last_r32 t [.var VarKind.local (ofString "saltv")] (ofString "salt") ha
      have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "u256_to_be32") values body callee rs hl
      simp only [Flapjack.lookupCodeHOLExact, lookup_u256_to_be32_b] at hx
      rcases values with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩
      · simp at hx
      · simp at hx
      · obtain ⟨out, hv1w, hcout⟩ := lookup_u256_out_r32 hl
        rcases front with _ | ⟨x, tl⟩
        · simp at hvals
        · rcases tl with _ | ⟨y, tl2⟩
          · simp only [List.cons_append, List.nil_append] at hvals
            obtain ⟨rfl, rfl⟩ := hvals
            obtain ⟨p, hpSl, hpAv, hp8, hpLim⟩ := hp.2
            rw [hv1w] at hw2
            have houtp : out = p := by
              have h1 := hw2.symm.trans hpSl
              have h2 := Option.some.inj h1
              simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at h2
              exact h2
            rw [houtp] at hcout
            exact ⟨p, hcout, evmAvoids_with_locals_clock_r32 t callee (t.clock - 1) hpAv, hp8, bv_and7_zero_r32 hp8, hpLim⟩
          · simp only [List.cons_append] at hvals
            injection hvals with _ h1
            cases tl2 <;> simp at h1
      · simp at hx)
    (hstep := fun t values body callee rs v cpost hi hw hp hci hw2 hch hq => by
      obtain ⟨hgg, hmm⟩ := hq
      have hev : globN cpost "ev" = globN t "ev" := by
        unfold globN
        rw [hgg]
        rfl
      have hmt : memW cpost (globN t "ev" + 32) = memW t (globN t "ev" + 32) := hmm
      refine memoryExpansionLocal_transport_g10 hp.1 rfl hev ?_
      show memW cpost (globN t "ev" + 32) = memW t (globN t "ev" + 32)
      exact hmt)
  apply ccA_seq_call_g10 (Q := fun _ => True) epsA_extend_memory (hentry := fun t values body callee rs hc hi hw hp ha hl =>
      memoryExpansionLocal_callee_pre_g10 t hc hw hp ha hl)
    (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial)
  apply ccA_dec_g10 (Q := fun _ => True) (fun t v hv hi hp => trivial)
  apply ccA_decCall_g10 (Q := fun _ => True) epsA_sat_word (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial) (hstep := by intros; trivial)
  apply ccA_decCall_g10 (Q := CaFresh_r32) epsA_allocFresh_r32 (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial) (hstep := fun t values body callee rs v cpost hi hw hp ha hl hci hw2 hch hq => by
      have hvals : values = [.val (.word (24 : BitVec 64))] := by
        simpa [evalListHOLExact, evalHOLExact, FrontendCodecComputation.expToHOLStructural] using ha.symm
      subst values
      obtain ⟨_, _, n, hvn, hn⟩ := one_word_arg_lookup GuestTrapAndLookup.lookup_alloc hl
      have hn24 : n = (24 : BitVec 64) := by simpa using hvn.symm
      subst n
      obtain ⟨hm, hgK, p, n', hn'lu, hvret, hpn, hal8, hbnd, hAvP⟩ := hq
      have hn'24 : n' = (24 : BitVec 64) := by
        have h0 : (callEntryStateHOLFinite t callee).locals.lookup (ofString "n") = some (.val (.word 24)) := hn
        rw [h0] at hn'lu
        have h12 := Option.some.inj hn'lu
        injection h12 with h22
        injection h22 with h23
        exact h23.symm
      subst n'
      refine ⟨p, ?_, ?_, hal8⟩
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        exact hvret
      · have h24 : (24 : BitVec 64).toNat = 24 := by decide
        rw [h24] at hAvP
        exact evmAvoids_with_locals_clock_r32 cpost (t.locals.update (ofString "ca", v)) cpost.clock hAvP)
  apply ccA_seq_call_g10 (Q := fun _ => True) hcc2 (hentry := fun t values body callee rs hc hi hw hp ha hl => by
      rw [hc] at hl
      obtain ⟨front, w, hvals, hw2⟩ := evalList_var_last_r32 t [.load ShapeHOL.one (.op BinOp.add [.var VarKind.local (ofString "msg"), .const (BitVec.ofNat 64 32)]), .var VarKind.local (ofString "salt"), .op BinOp.add [.load ShapeHOL.one (.op BinOp.add [.var VarKind.global (ofString "ev"), .const (BitVec.ofNat 64 24)]), .var VarKind.local (ofString "s")], .var VarKind.local (ofString "n")] (ofString "ca") ha
      have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "compute_create2_contract_address") values body callee rs hl
      simp only [Flapjack.lookupCodeHOLExact, lookup_compute_create2_contract_address] at hx
      rcases values with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | _⟩⟩⟩⟩⟩
      · simp at hx
      · simp at hx
      · simp at hx
      · simp at hx
      · simp at hx
      · obtain ⟨addr, salt, code, n, out, hv0w, hv1w, hv2w, hv3w, hv4w, hcaddr, hsalt, hcode, hn, hcout⟩ := lookup_cc2_args_r32 hl
        rcases front with _ | ⟨x, tl⟩
        · simp at hvals
        · rcases tl with _ | ⟨y, tl2⟩
          · simp at hvals
          · rcases tl2 with _ | ⟨z, tl3⟩
            · simp at hvals
            · rcases tl3 with _ | ⟨u, tl4⟩
              · simp at hvals
              · rcases tl4 with _ | ⟨q, rest⟩
                · simp only [List.cons_append, List.nil_append] at hvals
                  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hvals
                  obtain ⟨p, hpca, hpAv, hp8⟩ := hp
                  rw [hv4w] at hw2
                  have houtp : out = p := by
                    have h1 := hw2.symm.trans hpca
                    have h2 := Option.some.inj h1
                    simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at h2
                    exact h2
                  rw [houtp] at hcout
                  refine ⟨p, addr, salt, code, n, hcaddr, hsalt, hcode, hn, hcout, ?_, hp8⟩
                  exact evmAvoids_with_locals_clock_r32 t callee (t.clock - 1) (evmAvoids_shrink_r32 t hpAv (by omega))
                · simp only [List.cons_append] at hvals
                  injection hvals with _ h1
                  injection h1 with _ h2
                  injection h2 with _ h3
                  injection h3 with _ h4
                  injection h4 with _ h5
                  cases rest <;> simp at h5
      · simp at hx)
    (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial)
  apply ccA_decCall_g10 (Q := fun _ => True) hgc (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial) (hstep := by intros; trivial)
  apply ccA_seq_ite_g10
  · intro t w hcond hw0
    exact ccA_seq_call_g10 (Q := fun _ => True) epsA_pc_add (hentry := fun t values body callee rs hc hi hw hp ha hl => trivial) (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial) (ccA_ret_g10 (.const 0#64))
  · intro t hcond
    exact ccA_seq_skip_g10 (ccA_ret_g10 (.const 0#64))

theorem create2_prefix_through_alloc_buf_r32 {F : Type} (s0 : PanSemStateFiniteExact 64 F) (hcont : HandlerRunA s0 (fun s => MemoryExpansionLocal_g10 s ∧ SaltFresh_r32 s) true (handlerSuffix_g10 1 create2ChargedSuffix_g10)) : HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create2) := by
  apply create2_prefix_memory_run_g10
  apply HandlerRunA.weaken (Q := MemoryExpansionLocal_g10)
  · intro t hi hp; exact hp.2
  · apply HandlerRunA.decCall epsA_allocFresh_r32 (Q := fun s => MemoryExpansionLocal_g10 s ∧ SaltFresh_r32 s)
    · intros; trivial
    · intro t values body callee rs v cpost hi hw hp ha hl hpi hpw hch hq
      have hvals : values = [.val (.word (32 : BitVec 64))] := by
        simpa [evalListHOLExact, evalHOLExact, FrontendCodecComputation.expToHOLStructural] using ha.symm
      subst values
      obtain ⟨_, _, n, hvn, hn⟩ := one_word_arg_lookup GuestTrapAndLookup.lookup_alloc hl
      have hn32 : n = (32 : BitVec 64) := by simpa using hvn.symm
      subst n
      obtain ⟨hm, hgK, p, n', hn'lu, hvret, hpn, hal8, hbnd, hAvP⟩ := hq
      have hn'32 : n' = (32 : BitVec 64) := by
        have h0 : (callEntryStateHOLFinite t callee).locals.lookup (ofString "n") = some (.val (.word 32)) := hn
        rw [h0] at hn'lu
        have h12 := Option.some.inj hn'lu
        injection h12 with h22
        injection h22 with h23
        exact h23.symm
      subst n'
      have hev : globN cpost "ev" = globN t "ev" := by
        have he := congrArg (fun l => l.head?.map Prod.fst) hch
        simpa [evmChain, evmChainFrom, callEntryStateHOLFinite, globN] using he
      refine ⟨?_, p, ?_, ?_, hal8, ?_⟩
      · apply memoryExpansionLocal_transport_g10 hp
        · have hne : ofString "salt" ≠ ofString "x" := by decide
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
        · exact hev
        · change memW cpost _ = memW t _
          unfold memW
          rw [hm]
          rfl
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        exact hvret
      · have h32 : (32 : BitVec 64).toNat = 32 := by decide
        rw [h32] at hAvP
        exact evmAvoids_with_locals_clock_r32 cpost (t.locals.update (ofString "salt", v)) cpost.clock hAvP
      · have h32 : (32 : BitVec 64).toNat = 32 := by decide
        rw [h32] at hbnd
        have hpc : globN cpost "heap_ptr" ≤ heapLimit := hpi.1.2.2.1
        omega
    · exact hcont

theorem op_create2_run_full_buf_r32 {F : Type} (s0 : PanSemStateFiniteExact 64 F) (hU : EvmPreservingSpecA PcU256ToBe32_r32 (fun s _ post => post.globals = s.globals ∧ memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32)) (ofString "u256_to_be32")) (hcc2 : EvmPreservingSpecA PcCc2_r32 (fun _ _ _ => True) (ofString "compute_create2_contract_address")) (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post) (ofString "generic_create")) : HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create2) := create2_prefix_through_alloc_buf_r32 s0 (handlerRunA_of_childContinuation_g10 s0 _ _ (create2ChargedSuffixTail_buf_r32 hU hcc2 hgc))

theorem op_create_run_closed_buf_r32 {F : Type} (s0 : PanSemStateFiniteExact 64 F) (hW : WorldAccountSpecsA) (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post) (ofString "generic_create")) : HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create) := op_create_run_full_buf_r32 s0 hW bufSpec_compute_contract_address_r32 hgc

theorem op_create2_run_closed_buf_r32 {F : Type} (s0 : PanSemStateFiniteExact 64 F) (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post) (ofString "generic_create")) : HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create2) := op_create2_run_full_buf_r32 s0 bufSpec_u256_to_be32_r32 bufSpec_compute_create2_contract_address_r32 hgc

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
