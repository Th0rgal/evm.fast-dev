import InitECandidate.Solver.Wave8GuestInv.R13Shards.MptObjStepHelper
import InitECandidate.Solver.Wave8GuestInv.R13Shards.NodeRlpKeep
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptSet_Memory
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_Exec
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.RlpHelpers
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_scratch_alloc
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptInsertFinal
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptNibbleKeyWW
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfCollapseBranch
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfDeleteExtFinish
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete

/-! Standalone 0-`sorry`, axiom-clean proof shard for `mk_mpt_root` and `mk_mpt_set`
(`R16k-1File-MptSetRootKeeps`). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. `NodeHeap` cache-field (`+8`, `+16`, `+24`) preservation and `HeapByteEff` helpers -/

theorem nodeSize_ge32 (k : Nat) : 32 ≤ nodeSize k := by
  unfold nodeSize; split_ifs <;> omega

theorem nodeSize_mod8 (k : Nat) : nodeSize k % 8 = 0 := by
  unfold nodeSize; split_ifs <;> omega

theorem nodeIvl_aligned {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hN : NodeHeap s Nd) {n : Nat} (hn : n ∈ Nd) :
    (nodeIvl s n).1 % 8 = 0 ∧ (nodeIvl s n).2 % 8 = 0 :=
  ⟨(hN.1 n hn).2.2.2.1.1, nodeSize_mod8 (memW s n)⟩

theorem nodeIvl_in_heap {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hA : ArenaOK s) (hN : NodeHeap s Nd) {n : Nat} (hn : n ∈ Nd) :
    sourceBase ≤ n ∧ n + (nodeIvl s n).2 ≤ globN s "heap_ptr" := by
  obtain ⟨_, hal, hin, _, _⟩ := hN.1 n hn
  rcases hal with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact ⟨h1, h2⟩
  · have hsep : heapLimit ≤ scratchStart := by decide
    have hpos := nodeSize_ge32 (memW s n)
    have h2 := hin.2
    have hsp := hA.2.2.1
    have hfm := hA.2.2.2.1
    dsimp [nodeIvl] at h1 h2
    omega

theorem memW_eq_of_cell_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {a : Nat}
    (h : post.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a)) :
    memW post a = memW s a := by
  unfold memW; rw [h]

theorem memB_eq_of_align_cell_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {b : Nat}
    (hb : b < 2 ^ 64)
    (hcell : post.memory (BitVec.ofNat 64 (b / 8 * 8)) = s.memory (BitVec.ofNat 64 (b / 8 * 8)))
    (hbe : post.be = s.be) :
    memB post b = memB s b := by
  have hal_eq : panByteAlignHOL (BitVec.ofNat 64 b) = BitVec.ofNat 64 (b / 8 * 8) := by
    apply BitVec.eq_of_toNat_eq
    have hal : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
    change (BitVec.ofNat 64 ((BitVec.ofNat 64 b).toNat / 2 ^ ((64 : Nat) / 8).log2 *
      2 ^ ((64 : Nat) / 8).log2)).toNat = (BitVec.ofNat 64 (b / 8 * 8)).toNat
    rw [hal, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self b 8) hb)]
  unfold memB
  change (match post.memory (panByteAlignHOL (BitVec.ofNat 64 b)) with
      | .word v => (panGetByteHOL (BitVec.ofNat 64 b) v post.be).toNat) =
    (match s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) with
      | .word v => (panGetByteHOL (BitVec.ofNat 64 b) v s.be).toNat)
  rw [hal_eq, hcell, hbe]

/-- Preserves `NodeHeap Nd` and `nodeExtents` across any transition that only modifies
cache words `+8`, `+16`, `+24` of nodes `n ∈ Nd` (keeping `memW post (n + 16) < 2 ^ 40`),
leaves non-cache words of every `n ∈ Nd` unchanged, and leaves nibble-path bytes unchanged. -/
theorem nodeHeap_congr_cache {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) (hag : AllocatorGrows s post)
    {Nd : List Nat} (hN : NodeHeap s Nd)
    (hnonCache : ∀ n ∈ Nd, ∀ k, k < nodeSize (memW s n) / 8 →
      k ≠ 1 → k ≠ 2 → k ≠ 3 → memW post (n + 8 * k) = memW s (n + 8 * k))
    (hrlp_len : ∀ n ∈ Nd, memW post (n + 16) < 2 ^ 40)
    (hpath_bytes : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ j, j < memW s (n + 40) → memB post (memW s (n + 32) + j) = memB s (memW s (n + 32) + j)) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have hw0 : ∀ n ∈ Nd, memW post n = memW s n := by
    intro n hn
    have hsz := nodeSize_ge32 (memW s n)
    simpa using hnonCache n hn 0 (by omega) (by decide) (by decide) (by decide)
  have hivl : ∀ n ∈ Nd, nodeIvl post n = nodeIvl s n := by
    intro n hn; simp [nodeIvl, hw0 n hn]
  have hpath : ∀ n ∈ Nd, nodePath post n = nodePath s n := by
    intro n hn
    have hk_eq := hw0 n hn
    unfold nodePath
    by_cases h12 : memW s n = 1 ∨ memW s n = 2
    · have hsz : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize; rcases h12 with h1 | h2 <;> [simp [h1]; simp [h2]]
      have hw32 : memW post (n + 32) = memW s (n + 32) :=
        hnonCache n hn 4 (by omega) (by decide) (by decide) (by decide)
      have hw40 : memW post (n + 40) = memW s (n + 40) :=
        hnonCache n hn 5 (by omega) (by decide) (by decide) (by decide)
      simp [hk_eq, h12, hw32, hw40]
    · simp [hk_eq, h12]
  have hext_eq : nodeExtents post Nd = nodeExtents s Nd := by
    unfold nodeExtents
    apply List.flatMap_congr
    intro n hn
    rw [hivl n hn, hpath n hn]
  refine ⟨⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩, hext_eq⟩
  · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, hkey_n, _, hleaf, hbranch⟩ := hN.1 n hn
    rw [hw0 n hn, hivl n hn]
    refine ⟨hk3, hag.allocated hal_n, hin_n, P3MptSet.wordsOK_transfer hgS hgP hw_n,
      ?_, ?_, ?_, hrlp_len n hn, ?_, ?_⟩
    · intro h2
      have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
      have hw48 := hnonCache n hn 6 (by omega) (by decide) (by decide) (by decide)
      simpa only [Nat.mul_succ, Nat.mul_zero] using (by rw [hw48]; exact hext h2 : RootIn Nd (memW post (n + 48)))
    · intro h3 i hi
      have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
      have hw_ch := hnonCache n hn (4 + i) (by omega) (by omega) (by omega) (by omega)
      have hadd : n + 8 * (4 + i) = n + 32 + 8 * i := by omega
      rw [← hadd, hw_ch, hadd]
      exact hbr h3 i hi
    · intro h12
      have hsz : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize; rcases h12 with h1 | h2 <;> [simp [h1]; simp [h2]]
      have hw32 : memW post (n + 32) = memW s (n + 32) :=
        hnonCache n hn 4 (by omega) (by decide) (by decide) (by decide)
      have hw40 : memW post (n + 40) = memW s (n + 40) :=
        hnonCache n hn 5 (by omega) (by decide) (by decide) (by decide)
      rw [hw32, hw40]
      rcases hkey_n h12 with h0 | ⟨hnib, hal_p, hin_p, hdisj_p⟩
      · exact Or.inl h0
      · by_cases hlen0 : memW s (n + 40) = 0
        · exact Or.inl hlen0
        · right
          refine ⟨fun j hj => ?_, hag.allocated hal_p, hin_p, fun m hm => ?_⟩
          · rw [hpath_bytes n hn h12 hlen0 j hj]
            exact hnib j hj
          · rw [hivl m hm]
            exact hdisj_p m hm
    · intro h1
      have hsz : nodeSize (memW s n) = 64 := by unfold nodeSize; simp [h1]
      have hw56 := hnonCache n hn 7 (by omega) (by decide) (by decide) (by decide)
      simpa only [Nat.reduceMul, hw56] using hleaf h1
    · intro h3
      have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
      have hw168 := hnonCache n hn 21 (by omega) (by decide) (by decide) (by decide)
      simpa only [Nat.reduceMul, hw168] using hbranch h3
  · rw [hivl n hn, hivl m hm]
    exact hN.2 n hn m hm hne

/-- Cache-slice intervals `(n + 8, 24)` for `n ∈ Nd`. Every cache store (`+8`, `+16`, `+24`)
falls inside `(n + 8, 24)`, which is 8-byte aligned and disjoint from non-cache words and from
every `KeyIn` nibble path of `Nd`! -/
def nodeCacheIvls (Nd : List Nat) : List Ivl :=
  Nd.map fun n => (n + 8, 24)

theorem nodeHeap_of_heapByteEff_cache {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {extra : List Ivl} {gw : List String}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd)
    (heff : R16Shards.WkBlockTxEnc.HeapByteEff s post (nodeCacheIvls Nd ++ extra) gw)
    (hextra_disj : ∀ e ∈ extra, ∀ o ∈ nodeExtents s Nd, Disj e o)
    (hrlp_len : ∀ n ∈ Nd, memW post (n + 16) < 2 ^ 40) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hag : AllocatorGrows s post := ⟨heff.hp_le, heff.sp_le⟩
  apply nodeHeap_congr_cache hAs.1 heff.arena.1 hag hN ?_ hrlp_len ?_
  · intro n hn k hk hk1 hk2 hk3
    obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
    have hn8 : n % 8 = 0 := hw_n.1
    have hsz : 8 * k + 8 ≤ nodeSize (memW s n) := by
      have := nodeSize_mod8 (memW s n); omega
    have ha_lt : n + 8 * k < 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    apply memW_eq_of_cell_eq
    by_contra hne
    have ha_nat : (BitVec.ofNat 64 (n + 8 * k)).toNat = n + 8 * k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
    rcases heff.cell_frame (BitVec.ofNat 64 (n + 8 * k)) hne with ⟨iv, hiv, hpos, hc1, hc2⟩ | ⟨_, hfg1, hfg2⟩ | ⟨_, hhf1, hhf2⟩
    · rw [ha_nat] at hc1 hc2
      rcases List.mem_append.1 hiv with hcache | hex
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hcache
        by_cases hnm : n = m
        · subst hnm; dsimp only at hc1 hc2; omega
        · have hdj := hN.2 n hn m hm hnm
          have hsz_m := nodeSize_ge32 (memW s m)
          dsimp [nodeIvl] at hdj hc1 hc2
          rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
      · have ho_mem : nodeIvl s n ∈ nodeExtents s Nd := by
          unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
        have hdj := hextra_disj iv hex (nodeIvl s n) ho_mem
        dsimp [nodeIvl] at hdj
        rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
    · rw [ha_nat] at hfg1 hfg2
      have hfm8 : globN s "frame_mem_ptr" % 8 = 0 := hAs.2.2.2.2.2.2.2.1
      have hsp8 : globN s "scratch_ptr" % 8 = 0 := hAs.2.2.2.2.2.2.2.2.1
      have hdj := P3MptSet.disj_allocated_freeGap hAs.2 hal_n
      dsimp [nodeIvl, freeGap] at hdj hfg1 hfg2
      rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
    · rw [ha_nat] at hhf1 hhf2
      have hhp8 : globN s "heap_ptr" % 8 = 0 := hAs.2.2.2.2.2.2.1
      have hdj := P3MptSet.disj_allocated_heapFree hAs.2 hal_n
      dsimp [nodeIvl, heapFree] at hdj hhf1 hhf2
      rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  · intro n hn h12 hlen0 j hj
    obtain ⟨_, _, _, _, _, _, hkey_n, _⟩ := hN.1 n hn
    rcases hkey_n h12 with h0 | ⟨_, hal_p, hin_p, hdisj_p⟩
    · exact absurd h0 hlen0
    · have hb_lt : memW s (n + 32) + j < 2 ^ 64 := by
        have := hin_p.2; dsimp at this; omega
      by_contra hne
      rcases heff.byte_frame (memW s (n + 32) + j) hb_lt hne with ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
      · rcases List.mem_append.1 hiv with hcache | hex
        · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hcache
          have hdj := hdisj_p m hm
          have hsz_m := nodeSize_ge32 (memW s m)
          dsimp [nodeIvl] at hdj hb1 hb2
          rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
        · have hp_mem : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
            unfold nodeExtents
            exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
          have hdj := hextra_disj iv hex _ hp_mem
          rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
      · have hdj := P3MptSet.disj_allocated_freeGap hAs.2 hal_p
        dsimp [freeGap] at hdj hfg1 hfg2
        rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
      · have hdj := P3MptSet.disj_allocated_heapFree hAs.2 hal_p
        dsimp [heapFree] at hdj hhf1 hhf2
        rcases hdj with h0 | h0 | hd1 | hd2 <;> omega

/-! ## 2. Read-only RLP/node-reference evaluator (`roEncProg`) -/

private theorem lookup_rlp_be_len :
    originalRuntimeCode.lookup (ofString "rlp_be_len") =
      some ([(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_rlp_be_len, .one) :=
  lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_be_len) rfl

private theorem lookup_rlp_bytes_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len") =
      some ([(ofString "first_byte", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len, .one) :=
  lookup_of_guestAst_getElem 125 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_bytes_encoded_len) rfl

private theorem lookup_rlp_value_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_value_encoded_len") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len, .one) :=
  lookup_of_guestAst_getElem 286 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_value_encoded_len) rfl

private theorem lookup_node_ref_len :
    originalRuntimeCode.lookup (ofString "node_ref_len") =
      some ([(ofString "child", .one)], sourceFnBody Guest.Software.guestFn_node_ref_len, .one) :=
  lookup_of_guestAst_getElem 287 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_ref_len) rfl

private theorem lookup__node_needs_rlp :
    originalRuntimeCode.lookup (ofString "_node_needs_rlp") =
      some ([(ofString "child", .one)], sourceFnBody Guest.Software.guestFn__node_needs_rlp, .one) :=
  lookup_of_guestAst_getElem 283 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_needs_rlp) rfl

private def roEncGood (f : MlS) : Bool :=
  ((["rlp_be_len", "rlp_header_len", "rlp_list_header_len", "rlp_bytes_encoded_len",
    "rlp_value_encoded_len", "node_ref_len", "_node_needs_rlp", "mpt_fail"] : List String).map ofString).contains f

private def roEncProg : ProgHOL 64 → Bool
  | .dec _ _ _ body => roEncProg body
  | .seq first second => roEncProg first && roEncProg second
  | .ite _ yes no => roEncProg yes && roEncProg no
  | .while _ body => roEncProg body
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .decCall _ _ function _ continuation => roEncGood function && roEncProg continuation
  | .call none function _ => roEncGood function
  | .call (some (none, none)) function _ => roEncGood function
  | .call (some (some (.local, _), none)) function _ => roEncGood function
  | _ => false

private theorem roEnc_installed_body (f : MlS)
    (hf : roEncGood f = true)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs)) :
    roEncProg body = true := by
  simp only [roEncGood, List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_be_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee WkBlockTxEnc.lookup_rlp_header_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee WkBlockTxEnc.lookup_rlp_list_header_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_bytes_encoded_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_value_encoded_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_node_ref_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup__node_needs_rlp hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee R16Shards.lookup_mpt_fail hl; subst hb; rfl

theorem evaluate_roEncProg {F : Type} (program : ProgHOL 64)
    (supported : roEncProg program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2 =
      { state with locals := (evaluateHOLFiniteState state program).2.locals,
                   clock := (evaluateHOLFiniteState state program).2.clock } := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : roEncProg body = true := by simpa only [shape, roEncProg] using supported
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · rfl
    · rename_i val _
      split
      · have ih := evaluate_roEncProg body child (setVarHOLFinite name val state) code
        dsimp only [setVarHOLFinite] at ih ⊢
        rw [ih]
      · rfl
  | decCall name kind function arguments continuation =>
    have children : roEncGood function = true ∧ roEncProg continuation = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        rw [code] at found
        split
        · rfl
        · rename_i nonzero
          dsimp only
          have hsafe := roEnc_installed_body function children.1 values body callee rs found
          have hbody := evaluate_roEncProg body hsafe (callEntryStateHOLFinite state callee) code
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbody meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at hbody meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try (rw [hbody]; cases state; rfl))
          split
          · have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            let resumed : PanSemStateFiniteExact 64 F :=
              setVarHOLFinite name v
                { st with locals := state.locals,
                          clock := if (callEntryStateHOLFinite state callee).clock < st.clock
                                   then (callEntryStateHOLFinite state callee).clock else st.clock }
            have ih := evaluate_roEncProg continuation children.2 resumed stCode
            dsimp only [resumed, setVarHOLFinite] at ih ⊢
            conv_lhs => rw [ih]
            rw [hbody]; cases state; rfl
          · rw [hbody]; cases state; rfl
  | assign kind name value =>
    cases kind with
    | global => simp [shape, roEncProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split <;> (cases state; rfl)
  | seq first second =>
    have children : roEncProg first = true ∧ roEncProg second = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    have h1 := evaluate_roEncProg first children.1 state code
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at h1 remaining meta'
      dsimp only at h1 remaining meta'
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        have h2 := evaluate_roEncProg second children.2 middle (meta'.1.trans code)
        dsimp only
        rw [h2, h1]
      | some _ => exact h1
  | ite condition yes no =>
    have children : roEncProg yes = true ∧ roEncProg no = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_roEncProg no children.2 state code
      · exact evaluate_roEncProg yes children.1 state code
    · rfl
  | «while» condition body =>
    have child : roEncProg body = true := by simpa only [shape, roEncProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hb := evaluate_roEncProg body child (decClockHOLFinite state) code
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at hb remaining meta'
            dsimp only at hb remaining meta'
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining; omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none =>
              have hw := evaluate_roEncProg (.while condition body) (by simpa [roEncProg] using child) middle mCode
              rw [hw, hb]; cases state; rfl
            | some r =>
              cases r with
              | «continue» =>
                have hw := evaluate_roEncProg (.while condition body) (by simpa [roEncProg] using child) middle mCode
                rw [hw, hb]; cases state; rfl
              | _ => rw [hb]; cases state; rfl
      · rfl
    · rfl
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot tag text => rw [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> (cases state; rfl)
    · rfl
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> (cases state; rfl)
  | call info function arguments =>
    have hk : roEncGood function = true ∧
        (info = none ∨ info = some (none, none) ∨ ∃ nm, info = some (some (.local, nm), none)) := by
      rcases info with _ | ⟨_ | ⟨kind, nm⟩, _ | _⟩
      · exact ⟨by simpa [shape, roEncProg] using supported, Or.inl rfl⟩
      · exact ⟨by simpa [shape, roEncProg] using supported, Or.inr (Or.inl rfl)⟩
      · simp [shape, roEncProg] at supported
      · cases kind
        · exact ⟨by simpa [shape, roEncProg] using supported, Or.inr (Or.inr ⟨nm, rfl⟩)⟩
        · simp [shape, roEncProg] at supported
      · simp [shape, roEncProg] at supported
    rw [evaluateHOLFiniteState_call]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        rw [code] at found
        split
        · rfl
        · rename_i nonzero
          have hsafe := roEnc_installed_body function hk.1 values body callee rs found
          have hbody := evaluate_roEncProg body hsafe (callEntryStateHOLFinite state callee) code
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbody
          obtain ⟨r, st⟩ := out
          dsimp only at hbody ⊢
          rcases hk.2 with rfl | rfl | ⟨nm, rfl⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (rw [hbody]; cases state; rfl)
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (rw [hbody]; cases state; rfl)
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (try dsimp only [setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite]) <;>
              (rw [hbody]; cases state; rfl)
  | _ => simp [shape, roEncProg] at supported
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
      | omega

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
