import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChild
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep23

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23 (EvmStep EvmKeeps EvmAvoids GlobalsKept)
open InitECandidate.Solver.Wave8GuestInv.R11Shards

theorem lookup_incorporate_child_on_success_fc :
    originalRuntimeCode.lookup (ofString "incorporate_child_on_success") =
      some ([(ofString "child", .one)],
        sourceFnBody Guest.Software.guestFn_incorporate_child_on_success, .one) :=
  lookup_of_guestAst_getElem 592 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_incorporate_child_on_success) rfl

def incorpSuccCallees_fc (f : MlS) : Bool :=
  htabUnionCallees f || f == ofString "lst_push" || f == ofString "log_append" ||
    f == ofString "incorporate_child_on_error" || f == ofString "incorporate_child_on_success"

theorem incorpSuccCallees_fc_good :
    ∀ f, incorpSuccCallees_fc f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      StateRestoreEpilogue.noCatchableRaise incorpSuccCallees_fc body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [incorpSuccCallees_fc, htabUnionCallees,
    StateRestoreEpilogue.htabMutCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((((((((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_alloc) rfl
    change originalRuntimeCode.lookup (ofString "alloc") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memcpy) rfl
    change originalRuntimeCode.lookup (ofString "memcpy") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memeq) rfl
    change originalRuntimeCode.lookup (ofString "memeq") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 130 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_first_diff) rfl
    change originalRuntimeCode.lookup (ofString "htab_first_diff") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_find_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_find_leaf") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 134 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_node) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_node") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 135 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_leaf") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 136 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_internal) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_internal") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 137 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_grow) rfl
    change originalRuntimeCode.lookup (ofString "htab_grow") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_set) rfl
    change originalRuntimeCode.lookup (ofString "htab_set") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_del) rfl
    change originalRuntimeCode.lookup (ofString "htab_del") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 143 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_item) rfl
    change originalRuntimeCode.lookup (ofString "htab_item") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 400 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_union_into) rfl
    change originalRuntimeCode.lookup (ofString "htab_union_into") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_lst_push_fc] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_log_append_fc] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_incorporate_child_on_error] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [lookup_incorporate_child_on_success_fc] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

theorem wordsOK_updW_s5 {F : Type} (s : PanSemStateFiniteExact 64 F)
    {ivl : Ivl} (hw : WordsOK s ivl) (a w : BitVec 64) :
    WordsOK { s with memory := R14Shards.OpHandlersA.updW s.memory a w } ivl := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨wk, hdom, hm⟩ := hw.2.2 k hk
  dsimp only [WordAt, R14Shards.OpHandlersA.updW]
  by_cases heq : BitVec.ofNat 64 (ivl.1 + 8 * k) = a
  · exact ⟨w, hdom, if_pos heq⟩
  · exact ⟨wk, hdom, (if_neg heq).trans hm⟩

theorem ev_head_facts_s5 {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hA : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S) :
    globN s "ev" + 280 ≤ 2 ^ 64 ∧
    WordsOK s (globN s "ev", 280) ∧
    s.globals.lookup (ofString "ev") =
      some (.val (.word (BitVec.ofNat 64 (globN s "ev")))) ∧
    memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) ∧
    OpDispatchSpec.evmR s =
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hFW := hInv.2.2.2.2.1 _ hhead
  have hbnd := (InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hA.2 hFW).1
  dsimp only at hbnd
  have hwok : WordsOK s (globN s "ev", 280) := (hFW.1 (globN s "ev", 280) (by simp)).2
  obtain ⟨evw, hevw⟩ := hA.2.2.2.2.2.2.2.2.2 "ev" (by decide)
  have hevw_eq : evw = BitVec.ofNat 64 (globN s "ev") := by
    apply BitVec.eq_of_toNat_eq
    unfold GlobalWord at hevw
    have hgn : globN s "ev" = evw.toNat := by simp [globN, hevw]
    rw [BitVec.toNat_ofNat, hgn, Nat.mod_eq_of_lt evw.isLt]
  subst hevw_eq
  unfold GlobalWord at hevw
  have hsp : memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) := hFW.2.2.2.2.1
  have hR : OpDispatchSpec.evmR s =
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
    unfold OpDispatchSpec.evmR
    conv_lhs => rw [evmChain_cons]
    conv_rhs => rw [evmChain_cons]
    simp [Nat.add_assoc]
  exact ⟨hbnd, hwok, hevw, hsp, hR⟩

theorem eval_load_ev_off_s5 {F : Type} (s : PanSemStateFiniteExact 64 F)
    {base off : Nat}
    (hlk : s.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 base))))
    (hwok : WordsOK s (base, 280))
    (hbnd : base + 280 ≤ 2 ^ 64)
    (hoff : off + 8 ≤ 280) (hoff8 : off % 8 = 0) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW s (base + off))))) := by
  have hadd_eq : BitVec.ofNat 64 base + BitVec.ofNat 64 off = BitVec.ofNat 64 (base + off) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show base < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show base + off < 2 ^ 64 by omega)]
  have hwa : WordAt s (base + off) := hwok.2.2 (off / 8) (by omega)
    |> fun h => by rwa [show base + 8 * (off / 8) = base + off by omega] at h
  obtain ⟨w, hmem_dom, hmem_eq⟩ := hwa
  have hadd0 : BitVec.ofNat 64 base + (BitVec.ofNat 64 off + (0 : BitVec 64)) =
      BitVec.ofNat 64 (base + off) := by
    change BitVec.ofNat 64 base + (BitVec.ofNat 64 off + 0#64) = _
    rw [BitVec.add_zero, hadd_eq]
  simp only [evalHOLExact, evalListHOLExact, hlk, isWfShapeExactHOL, memLoadHOLExact, ↓reduceIte,
    valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr,
    Bool.and_self]
  rw [hadd0]
  simp only [hmem_dom, ↓reduceIte, hmem_eq, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq]
  unfold memW
  rw [hmem_eq]; simp

theorem eval_load_local_off_s5 {F : Type} (s : PanSemStateFiniteExact 64 F)
    {lname : String} {base sz off : Nat}
    (hlk : s.locals.lookup (ofString lname) = some (.val (.word (BitVec.ofNat 64 base))))
    (_hdom : s.memaddrs = ordinaryDomain)
    (hwok : WordsOK s (base, sz))
    (hbnd : base + sz ≤ 2 ^ 64)
    (hoff : off + 8 ≤ sz) (hoff8 : off % 8 = 0) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString lname), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW s (base + off))))) := by
  have hadd_eq : BitVec.ofNat 64 base + BitVec.ofNat 64 off = BitVec.ofNat 64 (base + off) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show base < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show base + off < 2 ^ 64 by omega)]
  have hwa : WordAt s (base + off) := hwok.2.2 (off / 8) (by omega)
    |> fun h => by rwa [show base + 8 * (off / 8) = base + off by omega] at h
  obtain ⟨w, hmem_dom, hmem_eq⟩ := hwa
  have hadd0 : BitVec.ofNat 64 base + (BitVec.ofNat 64 off + (0 : BitVec 64)) =
      BitVec.ofNat 64 (base + off) := by
    change BitVec.ofNat 64 base + (BitVec.ofNat 64 off + 0#64) = _
    rw [BitVec.add_zero, hadd_eq]
  simp only [evalHOLExact, evalListHOLExact, hlk, isWfShapeExactHOL, memLoadHOLExact, ↓reduceIte,
    valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr,
    Bool.and_self]
  rw [hadd0]
  simp only [hmem_dom, ↓reduceIte, hmem_eq, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
  unfold memW
  rw [hmem_eq]; simp

private theorem fc_eval_sub_words_s5 {F : Type} (s : PanSemStateFiniteExact 64 F)
    {a b : ExpHOL 64} {aw bw : BitVec 64}
    (ha : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a =
      some (.val (.word aw)))
    (hb : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) b =
      some (.val (.word bw))) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .sub [a, b]) = some (.val (.word (aw - bw))) := by
  simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp,
    valueIsWord, valueWord]

theorem fc_store_sub_words_s5 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {off : Nat} {ew aw bw : BitVec 64} {a b : ExpHOL 64}
    (he : s.globals.lookup (ofString "ev") = some (.val (.word ew)))
    (hen : ew.toNat = globN s "ev")
    (hbound : globN s "ev" + off < 2 ^ 64)
    (ha : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a =
      some (.val (.word aw)))
    (hb : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) b =
      some (.val (.word bw)))
    (hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)])
        (.op .sub [a, b])) = (none, post)) :
    post = { s with
      memory := R14Shards.OpHandlersA.updW s.memory
        (BitVec.ofNat 64 (globN s "ev" + off)) (aw - bw) } := by
  have hv := fc_eval_sub_words_s5 s ha hb
  obtain ⟨w, hw, hp⟩ := R14Shards.OpHandlersA.store_global_off_word
    he hen hbound (fun v h => by rw [hv] at h; exact ⟨aw - bw, (Option.some.inj h).symm⟩) hrun
  rw [hv] at hw
  have hw' : w = aw - bw := by simpa using hw.symm
  simpa only [hw'] using hp

private theorem disj_symm_s5 {i j : Ivl} (h : Disj i j) : Disj j i :=
  R11Shards.Disj.symm h

private theorem disj_fresh_of_allocated_s5 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp
  rcases hj with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))

private theorem disj_fresh_of_zero_or_allocated_s5 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : j.2 = 0 ∨ Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  rcases hj with h0 | hal
  · exact Or.inl h0
  · exact disj_fresh_of_allocated_s5 hAs hAp hhp hal

private theorem disj_fresh_of_frameObject_s5 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S : List Nat} {ec o : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hFW : FrameWF s S ec) (ho : o ∈ frameObjects s ec) :
    Disj o (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhp_lim : globN post "heap_ptr" ≤ heapLimit := hAp.2.1
  have hss_fm : scratchStart ≤ globN s "frame_mem_ptr" := hAs.2.2.1
  have hfm_sc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.1
  obtain ⟨hscr, hmem_in, _, _, _, _, _, _, _, _, _, _, hlogs_in, _, hret_in, hll_ok, _⟩ := hFW
  unfold frameObjects at ho
  rcases List.mem_append.1 ho with ho7 | holog
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
    rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := (hscr (ec.1, 280) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · have h := (hscr (ec.2, 104) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · have h := (hscr (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hmem_in; dsimp at hmem_in ⊢; omega)))
    · have h := (hscr (memW s (ec.1 + 88), 24) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · rcases hlogs_in with h | h
      · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp at h ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · rcases hret_in with ⟨hz, _⟩ | ⟨h, _⟩
      · unfold frameRet; simp [hz]; exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp at h ⊢; omega)))
  · unfold frameLogObjects at holog; dsimp only at holog
    obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
    rw [List.mem_range] at hidx_mem
    rcases hll_ok with hz | ⟨_, _, _, _, hent⟩
    · have hlo := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      have hss0 : 0 < scratchStart := by decide
      dsimp at hlo; omega
    · have hle := (hent idx hidx_mem).2
      have ho_rec := (List.mem_filter.1 ho_own).1
      simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
      rcases ho_rec with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.1.2; dsimp at this ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.2.2.2.1.2; dsimp at this ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.2.2.2.2.1.2; dsimp at this ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.2.2.2.2.2.2; dsimp at this ⊢; omega)))

private theorem avoidsTries_head_log_store_s5 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {p' cap' n0 : Nat}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (harr_cases : (p', 8 * cap') = frameLogs s (globN s "ev", globN s "cur_cont") ∨
      (Inside (p', 8 * cap') sourceBase (globN s "heap_ptr") ∧
        WordsOK s (p', 8 * cap') ∧
        (∀ t ∈ S, ∀ o ∈ htabFootprint s t, Disj (p', 8 * cap') o) ∧
        (∀ o ∈ fixedObjects s, Disj (p', 8 * cap') o) ∧
        AvoidsTries s S [(p', 8 * cap')]))
    (hn1_le_cap : n0 + 1 ≤ cap')
    (hmem_out : ∀ x : BitVec 64,
      x ≠ BitVec.ofNat 64 (memW s (globN s "ev" + 88)) →
      x ≠ BitVec.ofNat 64 (memW s (globN s "ev" + 88) + 8) →
      x ≠ BitVec.ofNat 64 (memW s (globN s "ev" + 88) + 16) →
      x ≠ BitVec.ofNat 64 (p' + 8 * n0) →
      post.memory x = s.memory x)
    {ivls : List Ivl} (hav : AvoidsTries s S ivls) :
    AvoidsTries post S ivls := by
  obtain ⟨Nd_v, hTr_v, hdj_v⟩ := hav
  obtain ⟨hW, _, _, _, hFW_all, _, _, _, hFO_disj, hAT, _, _, _⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  set l0 := memW s (e0 + 88)
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [evmChain_cons]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  have hl0_in_scr : Inside (l0, 24) (globN s "scratch_ptr") scratchEnd :=
    (hhead_FW.1 (l0, 24) (by simp [frameScratch, l0])).1
  have hl0_wok : WordsOK s (l0, 24) :=
    (hhead_FW.1 (l0, 24) (by simp [frameScratch, l0])).2
  have hl0_8 : l0 % 8 = 0 := hl0_wok.1
  have hl0_bnd : l0 + 24 ≤ 2 ^ 64 :=
    InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAs.2 (Or.inr hl0_in_scr)
  have hl0_fo : (l0, 24) ∈ frameObjects s (e0, c0) := by simp [frameObjects, l0]
  have hfl0_fo : frameLogs s (e0, c0) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
  have harr_alloc_wok : Allocated s (p', 8 * cap') ∧ WordsOK s (p', 8 * cap') := by
    rcases harr_cases with heq | ⟨hin, hw, _, _, _⟩
    · rw [heq]; exact ⟨hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.1, hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    · exact ⟨Or.inl hin, hw⟩
  have harr_wok : WordsOK s (p', 8 * cap') := harr_alloc_wok.2
  have hp'_8 : p' % 8 = 0 := harr_wok.1
  have harr_bnd : p' + 8 * cap' ≤ 2 ^ 64 :=
    InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAs.2 harr_alloc_wok.1
  have hdom_eq : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hAs.1.memaddrs.symm
  have hl0_dom0 : s.memaddrs (BitVec.ofNat 64 l0) := by
    obtain ⟨_, hdom, _⟩ := hl0_wok.2.2 0 (by omega); simpa using hdom
  have hl0_dom8 : s.memaddrs (BitVec.ofNat 64 (l0 + 8)) := by
    obtain ⟨_, hdom, _⟩ := hl0_wok.2.2 1 (by omega); simpa using hdom
  have hl0_dom16 : s.memaddrs (BitVec.ofNat 64 (l0 + 16)) := by
    obtain ⟨_, hdom, _⟩ := hl0_wok.2.2 2 (by omega); simpa using hdom
  have hslot_dom : s.memaddrs (BitVec.ofNat 64 (p' + 8 * n0)) := by
    obtain ⟨_, hdom, _⟩ := harr_wok.2.2 n0 (by dsimp only; omega); exact hdom
  have heff : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s post
      [(l0, 24), (p', 8 * cap')] := by
    refine ⟨hGp.code.trans hAs.1.code.symm, hdom_eq,
      hGp.shMemaddrs.trans hAs.1.shMemaddrs.symm,
      hGp.baseAddr.trans hAs.1.baseAddr.symm, hbe, hglob, ?_, ?_, ?_⟩
    · intro a hna
      exact hmem_out a (fun h => hna (h ▸ hl0_dom0)) (fun h => hna (h ▸ hl0_dom8))
        (fun h => hna (h ▸ hl0_dom16)) (fun h => hna (h ▸ hslot_dom))
    · intro a ha
      refine hmem_out a ?_ ?_ ?_ ?_
      · intro rfl
        have htn : (BitVec.ofNat 64 l0).toNat = l0 := Nat.mod_eq_of_lt (by omega)
        exact ha (l0, 24) (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
      · intro rfl
        have htn : (BitVec.ofNat 64 (l0 + 8)).toNat = l0 + 8 := Nat.mod_eq_of_lt (by omega)
        exact ha (l0, 24) (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
      · intro rfl
        have htn : (BitVec.ofNat 64 (l0 + 16)).toNat = l0 + 16 := Nat.mod_eq_of_lt (by omega)
        exact ha (l0, 24) (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
      · intro rfl
        have htn : (BitVec.ofNat 64 (p' + 8 * n0)).toNat = p' + 8 * n0 := Nat.mod_eq_of_lt (by omega)
        exact ha (p', 8 * cap') (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
    · intro b hb hno
      unfold memB
      have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      rw [hmem_out (panByteAlignHOL (BitVec.ofNat 64 b)) ?_ ?_ ?_ ?_, hbe]
      · intro heq
        have := congrArg BitVec.toNat heq
        rw [hal_b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact hno (l0, 24) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
      · intro heq
        have := congrArg BitVec.toNat heq
        rw [hal_b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact hno (l0, 24) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
      · intro heq
        have := congrArg BitVec.toNat heq
        rw [hal_b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact hno (l0, 24) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
      · intro heq
        have := congrArg BitVec.toNat heq
        rw [hal_b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact hno (p', 8 * cap') (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
  obtain ⟨Nd_arr, hTr_arr, harr_nodes_raw⟩ :
      ∃ Nd_arr, TriesTypedWith s S Nd_arr ∧ ∀ j ∈ nodeExtents s Nd_arr, Disj (p', 8 * cap') j := by
    rcases harr_cases with heq | ⟨_, _, _, _, Nd_p, hTr_p, hdj_p⟩
    · refine ⟨Nd_at, hTr_at, fun j hj => ?_⟩
      rw [heq]
      exact hAT_at _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hfl0_fo⟩) j hj
    · exact ⟨Nd_p, hTr_p, fun j hj => hdj_p _ (by simp) j hj⟩
  obtain ⟨hTr_1, hsub_1⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_arr
  obtain ⟨hTr_2, hsub_2⟩ := R11Shards.triesTypedWith_inter hTr_1 hTr_v
  set Nd2 := (Nd_at.filter (fun n => decide (n ∈ Nd_arr))).filter (fun n => decide (n ∈ Nd_v))
  have hWT2 : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd2 :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hTr_2⟩
  have hl0_disj_wti : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd2,
      i.2 = 0 ∨ Disj (l0, 24) i := by
    intro i hi
    unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem _ hl0_fo).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem _ hl0_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem _ hl0_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hl0_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hl0_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hl0_fo⟩)
        i (hsub_1 i (hsub_2 i h6).1).1)
  have harr_disj_wti : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd2,
      i.2 = 0 ∨ Disj (p', 8 * cap') i := by
    intro i hi
    unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      rcases harr_cases with heq | ⟨_, _, hd_ht, _, _⟩
      · rw [heq]; exact Or.inr ((hFO_disj _ hhead_mem _ hfl0_fo).1 t ht i hfp)
      · exact Or.inr (hd_ht t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      rcases harr_cases with heq | ⟨_, _, _, hd_fix, _⟩
      · rw [heq]; exact Or.inr ((hFO_disj _ hhead_mem _ hfl0_fo).2 _
          (InitECandidate.Solver.Wave8Contracts.M23.typedRec_in_fixedObjects s hr))
      · exact Or.inr (hd_fix _ (InitECandidate.Solver.Wave8Contracts.M23.typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      rcases harr_cases with heq | ⟨_, _, _, hd_fix, _⟩
      · rw [heq]; exact Or.inr ((hFO_disj _ hhead_mem _ hfl0_fo).2 _ hfix_j)
      · exact Or.inr (hd_fix _ hfix_j)
    · rcases harr_cases with heq | ⟨_, _, _, hd_fix, _⟩
      · rw [heq]; exact Or.inr ((hFO_disj _ hhead_mem _ hfl0_fo).2 _
          (InitECandidate.Solver.Wave8Contracts.M23.blockOut_in_fixedObjects h4))
      · exact Or.inr (hd_fix _ (InitECandidate.Solver.Wave8Contracts.M23.blockOut_in_fixedObjects h4))
    · rcases harr_cases with heq | ⟨_, _, _, hd_fix, _⟩
      · rw [heq]; exact Or.inr ((hFO_disj _ hhead_mem _ hfl0_fo).2 _
          (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects h5))
      · exact Or.inr (hd_fix _ (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects h5))
    · exact Or.inr (harr_nodes_raw i (hsub_1 i (hsub_2 i h6).1).2)
  have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd2 :=
    InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect.sameTypedCells
      (Rl := []) (extra := [(l0, 24), (p', 8 * cap')]) hAs.1.memaddrs hWT2
      (fun _ h => by simp at h)
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact hl0_disj_wti
        · exact harr_disj_wti)
      (by simpa using heff)
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hApost : ArenaReady post := ⟨hGp, arenaOK_congr hglob hAs.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hfeq := InitECandidate.Solver.Wave8Contracts.M23.fixedObjects_eq_of_nonHeapGlobalsKept
    hAs.2 hWT2.1 hWT2.2.2.1 hcell (fun name _ _ _ => by rw [hglob])
  have hFT_post := InitECandidate.Solver.Wave8Contracts.M23.fixedTyped_of_eq hApost hWT2.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
    hAs hApost hh hsc (fun g _ => hglob_eq g) hcell hWT2
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  refine ⟨Nd2, hWT_post.2.2.2, fun o ho j hj => ?_⟩
  rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_2.1 hcell] at hj
  exact hdj_v o ho j (hsub_2 j hj).2

/-- Call `log_append(ev, logExp)` from state `s` where `s` has `ArenaReady s` and `EvmInvAt s S`
and `log` is a valid, disjoint log entry. Preserves `EvmInvAt` and appends `logOwnedIvls s log`
to the head frame's `frameObjects`. -/
theorem call_log_append_step_fc {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {logExp : ExpHOL 64} {log : Nat}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hlog_arg : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      logExp = some (.val (.word (BitVec.ofNat 64 log))))
    (hlog_wa : WordAt s log)
    (hlog_ok : LogEntryOK s log)
    (hlog_pw : (logOwnedIvls s log).Pairwise Disj)
    (hlog_disj_fo : ∀ ec ∈ evmChain s, ∀ o1 ∈ logOwnedIvls s log,
      ∀ o2 ∈ frameObjects s ec, Disj o1 o2)
    (hlog_disj_ht : ∀ o ∈ logOwnedIvls s log, ∀ t ∈ S,
      ∀ j ∈ htabFootprint s t, Disj o j)
    (hlog_disj_fix : ∀ o ∈ logOwnedIvls s log,
      ∀ j ∈ fixedObjects s, Disj o j)
    (hlog_avoids : AvoidsTries s S (logOwnedIvls s log))
    (hlog_disj_msg : ∀ o ∈ logOwnedIvls s log,
      ∀ ec ∈ evmChain s, Disj (memW s (ec.1 + 112), 176) o)
    (hnone : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), logExp])).1 = none) :
    let post := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), logExp])).2
    ArenaReady post ∧
    InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
    post.locals = s.locals ∧
    post.be = s.be ∧
    GlobalsKept ["heap_ptr"] s post ∧
    globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    evmChain post = evmChain s ∧
    OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
    fixedObjects post = fixedObjects s ∧
    (∀ t ∈ S, htabFootprint post t = htabFootprint s t) ∧
    (∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec ∧
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.1 + 112) = memW s (ec.1 + 112) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56)) ∧
    (∀ ec ∈ evmChain s,
      frameLogs post ec = frameLogs s ec ∨
        Inside (frameLogs post ec) sourceBase (globN post "heap_ptr")) ∧
    (∀ ec ∈ (evmChain s).tail, frameObjects post ec = frameObjects s ec) ∧
    (∃ p' cap',
      frameLogs post (globN s "ev", globN s "cur_cont") = (p', 8 * cap') ∧
      ((p', 8 * cap') = frameLogs s (globN s "ev", globN s "cur_cont") ∨
        Inside (p', 8 * cap') (globN s "heap_ptr") (globN post "heap_ptr")) ∧
      frameObjects post (globN s "ev", globN s "cur_cont") =
        [(globN s "ev", 280), (globN s "cur_cont", 104),
         (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)),
         (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)),
         (memW s (globN s "ev" + 88), 24), (p', 8 * cap'),
         frameRet s (globN s "ev", globN s "cur_cont")] ++
        frameLogObjects s (globN s "ev", globN s "cur_cont") ++
        logOwnedIvls s log) ∧
    (∀ i : Ivl, i.1 + i.2 < 2 ^ 64 →
      Allocated s i →
      Disj i (memW s (globN s "ev" + 88), 24) →
      Disj i (frameLogs s (globN s "ev", globN s "cur_cont")) →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i) ∧
    (∀ ivls : List Ivl, AvoidsTries s S ivls → AvoidsTries post S ivls) ∧
    memW post (globN s "ev" + 16) = memW s (globN s "ev" + 16) := by
  dsimp only
  have hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), logExp])).1 ≠ some .timeOut := by
    rw [hnone]; simp
  obtain ⟨_, hcall_none, _⟩ := call0_outcome_fc (s := s)
    (fname := ofString "log_append")
    (args := [.var .global (ofString "ev"), logExp]) hnt
  obtain ⟨vals, body, cal, ret, rv, cpost, hargs, hl, hrun, hpost_eq⟩ := hcall_none hnone
  obtain ⟨he_bnd, he_wok, he_lk, _, _⟩ := ev_head_facts_s5 hAs hInv
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  set l0 := memW s (e0 + 88)
  set n0 := memW s (l0 + 8)
  set cap0 := memW s (l0 + 16)
  have hev_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "ev")) = some (.val (.word (BitVec.ofNat 64 e0))) := by
    simp [evalHOLExact, he_lk]
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, hev_ev, hlog_arg, Option.some.injEq] at hargs
  subst hargs
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "log_append")
      [.val (.word (BitVec.ofNat 64 e0)), .val (.word (BitVec.ofNat 64 log))] =
      some (body, cal, ret) := by rwa [← hAs.1.code]
  obtain ⟨rfl, rfl, wE, wL, hw_pair, hcal_e, hcal_l⟩ :=
    R14Shards.OpHandlersA.two_word_arg_lookup (by decide) lookup_log_append_fc hl_orig
  injection hw_pair with h1 h2
  injection h1 with h1'; injection h1' with hwE_eq; subst hwE_eq
  injection h2 with h2'; injection h2' with hwL_eq
  injection hwL_eq with hwL_eq'; subst hwL_eq'
  set ent := callEntryStateHOLFinite s cal
  have hbody_la : sourceFnBody Guest.Software.guestFn_log_append =
      .decCall (ofString "slot") .one (ofString "lst_push")
        [.load .one (.op .add [.var .local (ofString "e"), .const 88#64]), .const 8#64]
        (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
              (.return (.const 0#64))) := rfl
  change evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_log_append) =
    (some (.returned rv), cpost) at hrun
  rw [hbody_la, evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  have he88_eval := eval_load_local_off_s5 ent hcal_e hAs.1.memaddrs he_wok he_bnd
    (off := 88) (by omega) (by omega)
  have hargs_lp : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
      [.load .one (.op .add [.var .local (ofString "e"), .const 88#64]), .const 8#64] =
      some [.val (.word (BitVec.ofNat 64 l0)), .val (.word 8#64)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact, he88_eval]
    rfl
  have hlook_lp := pan_two_word_lookup ent.code.lookup (ofString "lst_push")
    (ofString "l") (ofString "esz")
    (sourceFnBody Guest.Software.guestFn_lst_push) (BitVec.ofNat 64 l0) 8#64
    (by decide) (by rw [show ent.code = originalRuntimeCode from hAs.1.code]; exact lookup_lst_push_fc)
  rw [hargs_lp] at hrun; dsimp only at hrun
  rw [hlook_lp] at hrun; dsimp only at hrun
  by_cases hclk_ent : ent.clock = 0
  · rw [if_pos hclk_ent] at hrun; simp at hrun
  · rw [if_neg hclk_ent] at hrun
    set cmap_lp : HolFiniteMapExact MlS (ValueHOL 64) :=
      (HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word (BitVec.ofNat 64 l0)))).update
        (ofString "esz", ValueHOL.val (.word 8#64))
    rcases hlp_run : evaluateHOLFiniteState (callEntryStateHOLFinite ent cmap_lp)
        (sourceFnBody Guest.Software.guestFn_lst_push) with ⟨rlp, sb⟩
    rw [hlp_run] at hrun
    cases rlp with
    | none => simp at hrun
    | some rlp0 =>
      cases rlp0 with
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ => simp at hrun
      | returned vb =>
        dsimp only at hrun
        have hhead_mem : (e0, c0) ∈ evmChain s := by
          rw [evmChain_cons]; exact List.mem_cons_self
        have hhead_FW := hInv.2.2.2.2.1 (e0, c0) hhead_mem
        have hl0_in_scr : Inside (l0, 24) (globN s "scratch_ptr") scratchEnd :=
          (hhead_FW.1 (l0, 24) (by simp [frameScratch, l0])).1
        have hl0_wok : WordsOK ent (l0, 24) :=
          (hhead_FW.1 (l0, 24) (by simp [frameScratch, l0])).2
        have hl0_bnd : l0 + 24 ≤ 2 ^ 64 :=
          InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAs.2 (Or.inr hl0_in_scr)
        have hl0_nat : (BitVec.ofNat 64 l0).toNat = l0 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hent_AR : ArenaReady ent := ⟨guestInv_with_locals_clock s cal _ hAs.1, hAs.2⟩
        have hcap_pos : 1 ≤ memW ent ((BitVec.ofNat 64 l0).toNat + 16) := by
          rw [hl0_nat]; exact hhead_FW.2.2.2.2.2.2.2.2.2.2.1
        have hlen_le : memW ent ((BitVec.ofNat 64 l0).toNat + 8) ≤
            memW ent ((BitVec.ofNat 64 l0).toNat + 16) := by
          rw [hl0_nat]; exact hhead_FW.2.2.2.2.2.2.2.2.2.2.2.1
        have harr_alloc : Inside (memW ent (BitVec.ofNat 64 l0).toNat,
            8 * memW ent ((BitVec.ofNat 64 l0).toNat + 16)) sourceBase (globN ent "heap_ptr") ∨
            Inside (memW ent (BitVec.ofNat 64 l0).toNat,
            8 * memW ent ((BitVec.ofNat 64 l0).toNat + 16)) (globN ent "scratch_ptr") scratchEnd := by
          rw [hl0_nat]; exact hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.1
        have harr_wok : WordsOK ent (memW ent (BitVec.ofNat 64 l0).toNat,
            8 * memW ent ((BitVec.ofNat 64 l0).toNat + 16)) := by
          rw [hl0_nat]; exact hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hl_disj_arr : Disj ((BitVec.ofNat 64 l0).toNat, 24)
            (memW ent (BitVec.ofNat 64 l0).toNat, 8 * memW ent ((BitVec.ofNat 64 l0).toNat + 16)) := by
          rw [hl0_nat]
          change Disj (l0, 24) (frameLogs s (e0, c0))
          have hpw := hInv.2.2.2.2.2.2.2.1
          change (((e0, c0) :: (evmChain s).tail).map (frameObjects s)).flatten.Pairwise Disj at hpw
          rw [List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
          have hpw0 := hpw.1
          unfold frameObjects at hpw0
          have hp0 := List.pairwise_cons.1 hpw0
          have hp1 := List.pairwise_cons.1 hp0.2
          have hp2 := List.pairwise_cons.1 hp1.2
          have hp3 := List.pairwise_cons.1 hp2.2
          have hp4 := List.pairwise_cons.1 hp3.2
          exact hp4.1 _ (by simp)
        have hspec := lst_push_body_logs_fc ent (BitVec.ofNat 64 l0) hent_AR
          (by rwa [hl0_nat]) (by rwa [hl0_nat]) hcap_pos hlen_le harr_alloc harr_wok hl_disj_arr
          vb (by rw [hlp_run])
        dsimp only at hspec
        rw [hlp_run] at hspec; dsimp only at hspec
        rw [hl0_nat] at hspec
        have hlog_lt264 : log < 2 ^ 64 := by
          have hh := hAs.2.2.1; have hl := hlog_ok.2.1.2
          rw [R11Shards.heapLimit_val] at hh; dsimp only at hl; omega
        set post := (evaluateHOLFiniteState s
          (.call (some (none, none)) (ofString "log_append")
            [.var .global (ofString "ev"), logExp])).2
        rcases hspec with
          ⟨hn_lt_cap, slotw, rfl, hslot_nat, hG_sb, hsb_glob, hsb_be, hsb_mem,
           hsb_m0, hsb_m8, hsb_m16⟩ |
          ⟨hn_eq_cap, s_mc, npw, slotw, rfl, hnpw_nat, hslot_nat, hAR_mc, hbe_mc, hhp_mc,
           hgk_mc, hout_mc, hbyte_mc, hwok_mc, hpref_mc, hG_sb, hsb_glob, hsb_be, hsb_mem,
           hsb_m0, hsb_m8, hsb_m16⟩
        · -- NO-GROW BRANCH (`n0 < cap0`)
          have hsh_ew : (shapeEqHOL (shapeOfHOLExact (ValueHOL.val (HolWordLab.word slotw))) .one &&
              shapeEqHOL (shapeOfHOLExact (ValueHOL.val (HolWordLab.word slotw))) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hsh_ew] at hrun
          set st_slot := setVarHOLFinite (ofString "slot") (.val (.word slotw)) { sb with locals := ent.locals }
          rcases hcont_out : evaluateHOLFiniteState st_slot
              (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                    (.return (.const 0#64))) with ⟨rcont, scont⟩
          rw [hcont_out] at hrun; dsimp only at hrun
          injection hrun with hrv_eq hcpost_eq
          rw [evaluateHOLFiniteState_seq_line780] at hcont_out
          have hslot_in_arr : slotw.toNat = memW s l0 + 8 * n0 := hslot_nat
          have hn_lt_cap_s : n0 < cap0 := hn_lt_cap
          have harr_wok_s : WordsOK s (memW s l0, 8 * cap0) :=
            hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have hslot_wa : WordAt s slotw.toNat := by
            rw [hslot_in_arr]; exact harr_wok_s.2.2 n0 (by change n0 < (8 * cap0) / 8; omega)
          obtain ⟨_, hslot_dom_s, _⟩ := hslot_wa
          have hslot_bv : BitVec.ofNat 64 slotw.toNat = slotw := by simp
          have hst_slot_dom : st_slot.memaddrs slotw := by
            change sb.memaddrs slotw
            rw [hG_sb.memaddrs, ← hAs.1.memaddrs, ← hslot_bv]
            exact hslot_dom_s
          have hst_slot_s : st_slot.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
            simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hst_slot_l : st_slot.locals.lookup (ofString "log") =
              some (.val (.word (BitVec.ofNat 64 log))) := by
            have hne : ofString "slot" ≠ ofString "log" := by decide
            simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne,
              ent, callEntryStateHOLFinite, hcal_l]
          have hev_st_d : @evalHOLExact 64 F _ st_slot.toExact
              (fun a => Classical.propDecidable (st_slot.memaddrs a))
              (.var .local (ofString "slot")) = some (.val (.word slotw)) := by
            simp [evalHOLExact, hst_slot_s]
          have hev_st_v : @evalHOLExact 64 F _ st_slot.toExact
              (fun a => Classical.propDecidable (st_slot.memaddrs a))
              (.var .local (ofString "log")) = some (.val (.word (BitVec.ofNat 64 log))) := by
            simp [evalHOLExact, hst_slot_l]
          have hst_eq : evaluateHOLFiniteState st_slot
              (.store (.var .local (ofString "slot")) (.var .local (ofString "log"))) =
              (none, { st_slot with memory := fun a =>
                if a = slotw then HolWordLab.word (BitVec.ofNat 64 log) else st_slot.memory a }) := by
            rw [evaluateHOLFiniteState_store, hev_st_d, hev_st_v]; dsimp only
            simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hst_slot_dom, FUPDATE]
          set st_after := { st_slot with memory := fun a =>
            if a = slotw then HolWordLab.word (BitVec.ofNat 64 log) else st_slot.memory a }
          rw [hst_eq] at hcont_out; dsimp only at hcont_out
          rw [evaluateHOLFiniteState_return] at hcont_out
          simp only [evalHOLExact, sizeOfShapeWithContextHOL, shapeOfHOLExact, ↓reduceIte] at hcont_out
          injection hcont_out with _ hscont_eq
          have hpost_mem : post.memory = st_after.memory := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; rfl
          have hpost_glob : post.globals = s.globals := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hsb_glob
          have hpost_be : post.be = s.be := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hsb_be
          have hpost_loc : post.locals = s.locals := by
            rw [hpost_eq]
          have hG_post : GuestInv post := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]
            exact ⟨hG_sb.code, hG_sb.memaddrs, hG_sb.shMemaddrs, hG_sb.baseAddr⟩
          have hslot_ne_hdr : ∀ k, k < 24 → slotw ≠ BitVec.ofNat 64 (l0 + k) := by
            intro k hk heq
            have htn := congrArg BitVec.toNat heq
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hslot_in_arr] at htn
            rcases hl_disj_arr with hd | hd | hd | hd
            · omega
            · dsimp only at hd; rw [hl0_nat] at hd; omega
            · dsimp only at hd; rw [hl0_nat] at hd; omega
            · dsimp only at hd; rw [hl0_nat] at hd; omega
          have hmem_out : ∀ x : BitVec 64,
              x ≠ BitVec.ofNat 64 l0 →
              x ≠ BitVec.ofNat 64 (l0 + 8) →
              x ≠ BitVec.ofNat 64 (l0 + 16) →
              x ≠ BitVec.ofNat 64 (memW s l0 + 8 * n0) →
              post.memory x = s.memory x := by
            intro x hx0 hx8 hx16 hxslot
            rw [hpost_mem]
            change (if x = slotw then .word (BitVec.ofNat 64 log) else sb.memory x) = s.memory x
            have hx_ne_slot : x ≠ slotw := by
              intro h; apply hxslot; rw [h, ← hslot_in_arr, hslot_bv]
            rw [if_neg hx_ne_slot]
            exact hsb_mem x hx8
          have hl0_post : memW post l0 = memW s l0 := by
            have hm : post.memory (BitVec.ofNat 64 l0) = sb.memory (BitVec.ofNat 64 l0) := by
              rw [hpost_mem]
              change (if BitVec.ofNat 64 l0 = slotw then HolWordLab.word (BitVec.ofNat 64 log)
                else sb.memory (BitVec.ofNat 64 l0)) = _
              exact if_neg (Ne.symm (by simpa using hslot_ne_hdr 0 (by omega)))
            exact (show memW post l0 = memW sb l0 by unfold memW; rw [hm]).trans hsb_m0
          have hl8_post : memW post (l0 + 8) = n0 + 1 := by
            have hm : post.memory (BitVec.ofNat 64 (l0 + 8)) = sb.memory (BitVec.ofNat 64 (l0 + 8)) := by
              rw [hpost_mem]
              change (if BitVec.ofNat 64 (l0 + 8) = slotw then HolWordLab.word (BitVec.ofNat 64 log)
                else sb.memory (BitVec.ofNat 64 (l0 + 8))) = _
              exact if_neg (Ne.symm (hslot_ne_hdr 8 (by omega)))
            exact (show memW post (l0 + 8) = memW sb (l0 + 8) by unfold memW; rw [hm]).trans hsb_m8
          have hl16_post : memW post (l0 + 16) = cap0 := by
            have hm : post.memory (BitVec.ofNat 64 (l0 + 16)) = sb.memory (BitVec.ofNat 64 (l0 + 16)) := by
              rw [hpost_mem]
              change (if BitVec.ofNat 64 (l0 + 16) = slotw then HolWordLab.word (BitVec.ofNat 64 log)
                else sb.memory (BitVec.ofNat 64 (l0 + 16))) = _
              exact if_neg (Ne.symm (hslot_ne_hdr 16 (by omega)))
            exact (show memW post (l0 + 16) = memW sb (l0 + 16) by unfold memW; rw [hm]).trans hsb_m16
          have hslot_post : memW post (memW s l0 + 8 * n0) = log := by
            rw [← hslot_in_arr]
            have hm : post.memory (BitVec.ofNat 64 slotw.toNat) = .word (BitVec.ofNat 64 log) := by
              rw [hslot_bv, hpost_mem]
              change (if slotw = slotw then HolWordLab.word (BitVec.ofNat 64 log) else sb.memory slotw) = _
              exact if_pos rfl
            unfold memW; rw [hm]; exact Nat.mod_eq_of_lt hlog_lt264
          have hcap_pos_s : 1 ≤ cap0 := hhead_FW.2.2.2.2.2.2.2.2.2.2.1
          obtain ⟨hAR_p, hInv_p, hch_p, hR_p, hfix_p, hfp_p, hsc_p, hfl0_p, htail_p, hfo0_p⟩ :=
            evmInvAt_of_head_log_store_fc hAs hInv hG_post hpost_glob hpost_be
              (p' := memW s l0) (cap' := cap0) (log := log)
              (Or.inl rfl)
              hcap_pos_s
              (by change n0 + 1 ≤ cap0; omega)
              hmem_out hl0_post hl8_post hl16_post hslot_post
              (fun i _ => rfl)
              hlog_wa hlog_ok hlog_pw hlog_disj_fo hlog_disj_ht hlog_disj_fix hlog_avoids hlog_disj_msg
          have hgk_p : GlobalsKept ["heap_ptr"] s post := fun g _ => by rw [hpost_glob]
          have hhp_p : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
            simp [globN, hpost_glob]
          have hui_no_grow : ∀ i : Ivl, i.1 + i.2 < 2 ^ 64 →
              Allocated s i →
              Disj i (l0, 24) →
              Disj i (frameLogs s (e0, c0)) →
              InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i := by
            intro i hi_bnd _ hdi_l0 hdi_fl a ha8 ha1 ha2
            have ha_lt : a.toNat < 2 ^ 64 := a.isLt
            have hne_hdr : ∀ k, k + 8 ≤ 24 → a ≠ BitVec.ofNat 64 (l0 + k) := by
              intro k hk heq
              have htn := congrArg BitVec.toNat heq
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at htn
              rcases hdi_l0 with hd | hd | hd | hd <;> (try dsimp only at hd) <;> omega
            have hne_slot : a ≠ BitVec.ofNat 64 (memW s l0 + 8 * n0) := by
              intro heq
              have harr_al_s : Allocated s (memW s l0, 8 * cap0) :=
                hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.1
              have hfl_b : memW s l0 + 8 * cap0 ≤ 2 ^ 64 :=
                InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAs.2 harr_al_s
              have htn := congrArg BitVec.toNat heq
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at htn
              have hfl_eq : frameLogs s (e0, c0) = (memW s l0, 8 * cap0) := rfl
              rw [hfl_eq] at hdi_fl
              rcases hdi_fl with hd | hd | hd | hd <;> (try dsimp only at hd) <;> omega
            exact hmem_out a (hne_hdr 0 (by omega)) (hne_hdr 8 (by omega))
              (hne_hdr 16 (by omega)) hne_slot
          have he16_p : memW post (e0 + 16) = memW s (e0 + 16) := by
            have hpw0 : (frameObjects s (e0, c0)).Pairwise Disj := by
              have hpw := hInv.2.2.2.2.2.2.2.1
              rw [evmChain_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
              exact hpw.1
            unfold frameObjects at hpw0
            have hrest := (List.pairwise_cons.1 hpw0).1
            have hd_l0 : Disj (e0, 280) (l0, 24) := hrest _ (by simp [l0])
            have hd_fl : Disj (e0, 280) (frameLogs s (e0, c0)) := hrest _ (by simp)
            have he_lt : e0 + 280 < 2 ^ 64 := by
              have hse : scratchEnd < 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
              exact lt_of_le_of_lt (hhead_FW.1 (e0, 280) (by simp)).1.2 hse
            exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hui_no_grow (e0, 280) he_lt (Or.inr (hhead_FW.1 (e0, 280) (by simp)).1) hd_l0 hd_fl)
              (by have := he_wok.1; omega) (by omega) ⟨by omega, by omega⟩
          refine ⟨hAR_p, hInv_p, hpost_loc, hpost_be, hgk_p, hhp_p, hch_p, hR_p, hfix_p, hfp_p,
            hsc_p, ?_, fun ec hec => (htail_p ec hec).2,
            ⟨memW s l0, cap0, hfl0_p, Or.inl rfl, hfo0_p⟩, hui_no_grow,
            fun ivls hav => avoidsTries_head_log_store_s5 hAs hInv hG_post hpost_glob hpost_be
              (Or.inl rfl) (by change n0 + 1 ≤ cap0; omega) hmem_out hav, he16_p⟩
          · intro ec hec
            rw [evmChain_cons] at hec
            rcases List.mem_cons.1 hec with rfl | htl
            · exact Or.inl hfl0_p
            · exact Or.inl (htail_p ec htl).1
        · -- GROW BRANCH (`n0 = cap0`)
          have hsh_ew : (shapeEqHOL (shapeOfHOLExact (ValueHOL.val (HolWordLab.word slotw))) .one &&
              shapeEqHOL (shapeOfHOLExact (ValueHOL.val (HolWordLab.word slotw))) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hsh_ew] at hrun
          set st_slot := setVarHOLFinite (ofString "slot") (.val (.word slotw)) { sb with locals := ent.locals }
          rcases hcont_out : evaluateHOLFiniteState st_slot
              (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                    (.return (.const 0#64))) with ⟨rcont, scont⟩
          rw [hcont_out] at hrun; dsimp only at hrun
          injection hrun with hrv_eq hcpost_eq
          rw [evaluateHOLFiniteState_seq_line780] at hcont_out
          have hn_eq_cap_s : n0 = cap0 := hn_eq_cap
          have hcap_pos_s : 1 ≤ cap0 := hhead_FW.2.2.2.2.2.2.2.2.2.2.1
          have hwok_mc' : WordsOK s_mc (npw.toNat, 16 * cap0) := hwok_mc
          have hslot_in_arr : slotw.toNat = npw.toNat + 8 * n0 := hslot_nat
          have hslot_wa_mc : WordAt s_mc slotw.toNat := by
            rw [hslot_in_arr]; exact hwok_mc'.2.2 n0 (by change n0 < (16 * cap0) / 8; omega)
          obtain ⟨_, hslot_dom_mc, _⟩ := hslot_wa_mc
          have hslot_bv : BitVec.ofNat 64 slotw.toNat = slotw := by simp
          have hst_slot_dom : st_slot.memaddrs slotw := by
            change sb.memaddrs slotw
            rw [hG_sb.memaddrs, ← hAR_mc.1.memaddrs, ← hslot_bv]
            exact hslot_dom_mc
          have hst_slot_s : st_slot.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
            simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hst_slot_l : st_slot.locals.lookup (ofString "log") =
              some (.val (.word (BitVec.ofNat 64 log))) := by
            have hne : ofString "slot" ≠ ofString "log" := by decide
            simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne,
              ent, callEntryStateHOLFinite, hcal_l]
          have hev_st_d : @evalHOLExact 64 F _ st_slot.toExact
              (fun a => Classical.propDecidable (st_slot.memaddrs a))
              (.var .local (ofString "slot")) = some (.val (.word slotw)) := by
            simp [evalHOLExact, hst_slot_s]
          have hev_st_v : @evalHOLExact 64 F _ st_slot.toExact
              (fun a => Classical.propDecidable (st_slot.memaddrs a))
              (.var .local (ofString "log")) = some (.val (.word (BitVec.ofNat 64 log))) := by
            simp [evalHOLExact, hst_slot_l]
          have hst_eq : evaluateHOLFiniteState st_slot
              (.store (.var .local (ofString "slot")) (.var .local (ofString "log"))) =
              (none, { st_slot with memory := fun a =>
                if a = slotw then HolWordLab.word (BitVec.ofNat 64 log) else st_slot.memory a }) := by
            rw [evaluateHOLFiniteState_store, hev_st_d, hev_st_v]; dsimp only
            simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hst_slot_dom, FUPDATE]
          set st_after := { st_slot with memory := fun a =>
            if a = slotw then HolWordLab.word (BitVec.ofNat 64 log) else st_slot.memory a }
          rw [hst_eq] at hcont_out; dsimp only at hcont_out
          rw [evaluateHOLFiniteState_return] at hcont_out
          simp only [evalHOLExact, sizeOfShapeWithContextHOL, shapeOfHOLExact, ↓reduceIte] at hcont_out
          injection hcont_out with _ hscont_eq
          have hpost_mem : post.memory = st_after.memory := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; rfl
          have hpost_glob_mc : post.globals = s_mc.globals := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hsb_glob
          have hpost_be_mc : post.be = s_mc.be := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hsb_be
          have hpost_loc : post.locals = s.locals := by
            rw [hpost_eq]
          have hG_post : GuestInv post := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]
            exact ⟨hG_sb.code, hG_sb.memaddrs, hG_sb.shMemaddrs, hG_sb.baseAddr⟩
          -- Transport `s -> s_mc` via fresh heap step:
          have hhp_s_mc : globN s "heap_ptr" ≤ globN s_mc "heap_ptr" := by
            have h : npw.toNat + 16 * cap0 ≤ globN s_mc "heap_ptr" := hhp_mc
            have hn : npw.toNat = globN s "heap_ptr" := hnpw_nat
            omega
          have hgk_s_mc : GlobalsKept ["heap_ptr"] s s_mc := hgk_mc
          have hbe_s_mc : s_mc.be = s.be := hbe_mc
          have hout_s_mc : ∀ a : BitVec 64, ¬ s.memaddrs a → s_mc.memory a = s.memory a := hout_mc
          have hbyte_s_mc : ∀ b : Nat, b < 2 ^ 64 →
              ¬ (globN s "heap_ptr" ≤ b ∧ b < globN s_mc "heap_ptr") → memB s_mc b = memB s b := hbyte_mc
          have hg_mc_nonHeap : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" →
              globN s_mc nm = globN s nm := by
            intro nm hne
            exact InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
              (hgk_s_mc (ofString nm) (by simp [hne]))
          have he0_mc : globN s_mc "ev" = e0 := hg_mc_nonHeap "ev" (by decide)
          have hc0_mc : globN s_mc "cur_cont" = c0 := hg_mc_nonHeap "cur_cont" (by decide)
          have hse_lt : scratchEnd < 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
          have he0_in_scr : Inside (e0, 280) (globN s "scratch_ptr") scratchEnd :=
            (hhead_FW.1 (e0, 280) (by simp)).1
          have he0_lt : e0 + 280 < 2 ^ 64 := lt_of_le_of_lt he0_in_scr.2 hse_lt
          have hl0_lt : l0 + 24 < 2 ^ 64 := lt_of_le_of_lt hl0_in_scr.2 hse_lt
          have he0_unhit_mc : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s s_mc (e0, 280) :=
            ivlUnhit_of_fresh_heap_bytes_fc hbe_s_mc hhp_s_mc hbyte_s_mc he0_lt
              (disj_fresh_of_allocated_s5 hAs.2 hAR_mc.2 hhp_s_mc (Or.inr he0_in_scr))
          have hl0_unhit_mc : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s s_mc (l0, 24) :=
            ivlUnhit_of_fresh_heap_bytes_fc hbe_s_mc hhp_s_mc hbyte_s_mc hl0_lt
              (disj_fresh_of_allocated_s5 hAs.2 hAR_mc.2 hhp_s_mc (Or.inr hl0_in_scr))
          have hl0_mc : memW s_mc (e0 + 88) = l0 :=
            InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit he0_unhit_mc
              (by have := he_wok.1; omega) (le_of_lt he0_lt) ⟨by omega, by omega⟩
          have hl0_p_mc : memW s_mc l0 = memW s l0 := by
            have := InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hl0_unhit_mc
              (a := l0 + 0) (by have := hl0_wok.1; omega) (le_of_lt hl0_lt) ⟨by omega, by omega⟩
            simpa using this
          have hn0_mc : memW s_mc (l0 + 8) = n0 :=
            InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hl0_unhit_mc
              (by have := hl0_wok.1; omega) (le_of_lt hl0_lt) ⟨by omega, by omega⟩
          have hcap0_mc : memW s_mc (l0 + 16) = cap0 :=
            InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hl0_unhit_mc
              (by have := hl0_wok.1; omega) (le_of_lt hl0_lt) ⟨by omega, by omega⟩
          obtain ⟨hInv_mc, hch_mc, hR_mc⟩ := OpHandlersB.evmInvAt_of_fresh_heap_step
            hAs hInv hAR_mc hbe_s_mc hhp_s_mc hgk_s_mc hout_s_mc hbyte_s_mc
          have hin_fresh : Inside (npw.toNat, 8 * (2 * cap0)) (globN s "heap_ptr") (globN s_mc "heap_ptr") := by
            have hn : npw.toNat = globN s "heap_ptr" := hnpw_nat
            have hh : npw.toNat + 16 * cap0 ≤ globN s_mc "heap_ptr" := hhp_mc
            exact ⟨by dsimp only; omega, by dsimp only; omega⟩
          obtain ⟨hnp_sb, hnp_fo, hnp_ht, hnp_fix, hnp_av, hnp_msg⟩ :=
            fresh_heap_ivl_props_fc hAs hInv hAR_mc hbe_s_mc hhp_s_mc hgk_s_mc hout_s_mc hbyte_s_mc hin_fresh
          obtain ⟨hlog_ok_mc, hlog_own_mc, _⟩ :=
            logEntry_fresh_heap_transport_fc hAs hAR_mc hbe_s_mc hhp_s_mc
              (hg_mc_nonHeap "vm_system_address" (by decide)) hbyte_s_mc hlog_ok
          have hlog_av_mc : AvoidsTries s_mc S (logOwnedIvls s_mc log) :=
            logOwnedIvls_avoidsTries_fresh_heap_fc hAs hInv hAR_mc hbe_s_mc hhp_s_mc
              hgk_s_mc hout_s_mc hbyte_s_mc hlog_ok hlog_avoids
          have hlog_wa_mc : WordAt s_mc log := hlog_ok_mc.1.2.2 0 (by omega) |> fun h => by simpa using h
          have hnp_disj_log : ∀ o ∈ logOwnedIvls s_mc log, Disj (npw.toNat, 8 * (2 * cap0)) o := by
            rw [hlog_own_mc]
            intro o ho
            have ho_rec := (List.mem_filter.1 ho).1
            have ho_al : Allocated s o := by
              simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
              rcases ho_rec with rfl | rfl | rfl | rfl
              · exact Or.inl hlog_ok.2.1
              · exact Or.inl hlog_ok.2.2.2.2.1
              · exact Or.inl hlog_ok.2.2.2.2.2.1
              · exact Or.inl hlog_ok.2.2.2.2.2.2
            exact disj_symm_s5 (InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right
              (by rw [Nat.add_sub_of_le hhp_s_mc]; exact hin_fresh)
              (disj_fresh_of_allocated_s5 hAs.2 hAR_mc.2 hhp_s_mc ho_al))
          -- Fresh-heap equality lemmas on `s -> s_mc`:
          have hdom_mc : s_mc.memaddrs = s.memaddrs := hAR_mc.1.memaddrs.trans hAs.1.memaddrs.symm
          have hsc_mc : globN s_mc "scratch_ptr" ≤ globN s "scratch_ptr" := by
            rw [hg_mc_nonHeap "scratch_ptr" (by decide)]
          obtain ⟨Nd_s, hTr_s, _⟩ := hInv.2.2.2.2.2.2.2.2.2.1
          have hWT_s : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd_s :=
            ⟨hInv.1.1, hInv.1.2.1, hInv.1.2.2.1, hTr_s⟩
          have hcell_mc : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s s_mc S Nd_s := by
            have hwti_disj : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_s,
                Disj i (globN s "heap_ptr", globN s_mc "heap_ptr" - globN s "heap_ptr") := fun i hi =>
              disj_fresh_of_zero_or_allocated_s5 hAs.2 hAR_mc.2 hhp_s_mc
                (InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls_allocated hWT_s hi)
            refine ⟨hbe_s_mc, hdom_mc, hAs.1.memaddrs, ?_, ?_, ?_⟩
            · intro a hna; apply hout_s_mc a; rwa [hAs.1.memaddrs]
            · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
              by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
              · have hord := (InitECandidate.Solver.Wave8Contracts.M23.ordinaryDomain_iff (BitVec.ofNat 64 a)).mp hdom
                have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
                have hhe : heapEnd < 2 ^ 64 := by rw [R11Shards.heapEnd_val]; decide
                have ha_bound : a + 8 < 2 ^ 64 := by rw [hbit] at hord; omega
                have hw : memW s_mc a = memW s a := by
                  apply (R13SoloHtabSet.memW_eq_iff_memB (a₁ := a) (a₂ := a) hbe_s_mc ha8 ha8 ha_bound ha_bound).2
                  intro k hk
                  apply hbyte_s_mc (a + k) (by omega)
                  intro ⟨hb1, hb2⟩
                  rcases hwti_disj i hi with hd | hd | hd | hd <;> (try dsimp only at hd) <;> omega
                cases hp : s_mc.memory (BitVec.ofNat 64 a) with
                | word wp =>
                  cases hs : s.memory (BitVec.ofNat 64 a) with
                  | word ws =>
                    simp only [memW, hp, hs] at hw
                    exact congrArg HolWordLab.word (BitVec.eq_of_toNat_eq hw)
              · apply hout_s_mc _ (by rwa [hAs.1.memaddrs])
            · intro b hb ⟨i, hi, hb1, hb2⟩
              apply hbyte_s_mc b hb
              intro ⟨h1, h2⟩
              rcases hwti_disj i hi with hd | hd | hd | hd <;> (try dsimp only at hd) <;> omega
          have hfeq_mc : fixedObjects s_mc = fixedObjects s := by
            unfold fixedObjects
            rw [InitECandidate.Solver.Wave8Contracts.M23.blockOutObjects_eq hAs.2 hWT_s.2.2.1 hcell_mc
                  (hg_mc_nonHeap "bo" (by decide)),
                InitECandidate.Solver.Wave8Contracts.M23.balObjects_eq hAs.2 hWT_s.1 hWT_s.2.2.1 hcell_mc
                  (hg_mc_nonHeap "bal_accounts" (by decide)),
                hg_mc_nonHeap "journal" (by decide),
                hg_mc_nonHeap "journal_cap" (by decide)]
            congr 3
            apply List.map_congr_left
            intro gn hgn
            have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
            rw [hg_mc_nonHeap gn.1 hne]
          have hfp_mc : ∀ t ∈ S, htabFootprint s_mc t = htabFootprint s t :=
            fun t ht => InitECandidate.Solver.Wave8Contracts.M23.htabFootprint_eq hcell_mc ht (hWT_s.1.2.1 t ht).1
          have hu_fo_mc : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, o.1 + o.2 < 2 ^ 64 →
              InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s s_mc o := fun ec hec o ho hob =>
            ivlUnhit_of_fresh_heap_bytes_fc hbe_s_mc hhp_s_mc hbyte_s_mc hob
              (disj_fresh_of_frameObject_s5 hAs.2 hAR_mc.2 hhp_s_mc (hInv.2.2.2.2.1 ec hec) ho)
          have hrec_mc : ∀ ec ∈ evmChain s,
              (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW s_mc (ec.1 + k) = memW s (ec.1 + k)) ∧
              (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW s_mc (ec.2 + k) = memW s (ec.2 + k)) ∧
              (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW s_mc (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
            intro ec hec
            have hFW := hInv.2.2.2.2.1 ec hec
            have hb1 : ec.1 + 280 < 2 ^ 64 := lt_of_le_of_lt (hFW.1 (ec.1, 280) (by simp)).1.2 hse_lt
            have hb2 : ec.2 + 104 < 2 ^ 64 := lt_of_le_of_lt (hFW.1 (ec.2, 104) (by simp)).1.2 hse_lt
            have hb88 : memW s (ec.1 + 88) + 24 < 2 ^ 64 :=
              lt_of_le_of_lt (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.2 hse_lt
            have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
            have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
            have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
            refine ⟨fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
                      (hu_fo_mc ec hec (ec.1, 280) (by simp [frameObjects]) hb1)
                      (by omega) (by omega) ⟨by omega, by omega⟩,
                    fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
                      (hu_fo_mc ec hec (ec.2, 104) (by simp [frameObjects]) hb2)
                      (by omega) (by omega) ⟨by omega, by omega⟩,
                    fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
                      (hu_fo_mc ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]) hb88)
                      (by omega) (by omega) ⟨by omega, by omega⟩⟩
          have hfo_mc : ∀ ec ∈ evmChain s, frameObjects s_mc ec = frameObjects s ec ∧
              frameScratch s_mc ec = frameScratch s ec ∧
              frameLogs s_mc ec = frameLogs s ec ∧
              frameRet s_mc ec = frameRet s ec ∧
              frameLogObjects s_mc ec = frameLogObjects s ec := by
            intro ec hec
            have hFW := hInv.2.2.2.2.1 ec hec
            obtain ⟨he_eq, _, h88_eq⟩ := hrec_mc ec hec
            have hl0_ec : memW s_mc (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
              simpa using h88_eq 0 (by omega) (by omega)
            have hl8_ec : memW s_mc (memW s (ec.1 + 88) + 8) = memW s (memW s (ec.1 + 88) + 8) :=
              h88_eq 8 (by omega) (by omega)
            have hl16_ec : memW s_mc (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16) :=
              h88_eq 16 (by omega) (by omega)
            have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
                memW s_mc (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
              intro i hi
              have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
              have hlen_le_ec := hFW.2.2.2.2.2.2.2.2.2.2.2.1
              have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 < 2 ^ 64 := by
                rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨_, h2⟩ | ⟨_, h2⟩
                · have hh := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hh; omega
                · omega
              have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
              exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
                (hu_fo_mc ec hec _ hfl_in hfl_b)
                (by unfold frameLogs at hfl_b; omega) (by omega)
                ⟨by unfold frameLogs; omega, by unfold frameLogs; omega⟩
            have hflo_eq : frameLogObjects s_mc ec = frameLogObjects s ec := by
              unfold frameLogObjects; dsimp only
              rw [he_eq 88 (by omega) (by omega), hl8_ec]
              apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
              rw [hl0_ec, harr_eq i hi]
              rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
              · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
                have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
                rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
              · exact (logEntry_fresh_heap_transport_fc hAs hAR_mc hbe_s_mc hhp_s_mc
                  (hg_mc_nonHeap "vm_system_address" (by decide)) hbyte_s_mc (hent i hi).2).2.1
            have hfl_eq_ec : frameLogs s_mc ec = frameLogs s ec := by
              unfold frameLogs; rw [he_eq 88 (by omega) (by omega), hl0_ec, hl16_ec]
            have hfr_eq_ec : frameRet s_mc ec = frameRet s ec := by
              unfold frameRet; rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
            have hsc_eq_ec : frameScratch s_mc ec = frameScratch s ec := by
              unfold frameScratch
              rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
            have hfo_eq_ec : frameObjects s_mc ec = frameObjects s ec := by
              unfold frameObjects
              rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
                  he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
                  he_eq 88 (by omega) (by omega), hfl_eq_ec, hfr_eq_ec, hflo_eq]
            exact ⟨hfo_eq_ec, hsc_eq_ec, hfl_eq_ec, hfr_eq_ec, hflo_eq⟩
          -- Now prove `s_mc -> post` via `evmInvAt_of_head_log_store_fc`:
          have hslot_ne_hdr : ∀ k, k + 8 ≤ 24 → slotw ≠ BitVec.ofNat 64 (l0 + k) := by
            intro k hk heq
            have htn := congrArg BitVec.toNat heq
            rw [hslot_in_arr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at htn
            have hl0_disj_np : Disj (l0, 24) (npw.toNat, 8 * (2 * cap0)) :=
              disj_symm_s5 (hnp_fo (e0, c0) (by rwa [hch_mc]) (l0, 24)
                (by rw [(hfo_mc (e0, c0) hhead_mem).1]; simp [frameObjects, l0]))
            rcases hl0_disj_np with hd | hd | hd | hd <;> (try dsimp only at hd) <;> omega
          have hmem_out_mc : ∀ x : BitVec 64,
              x ≠ BitVec.ofNat 64 (memW s_mc (globN s_mc "ev" + 88)) →
              x ≠ BitVec.ofNat 64 (memW s_mc (globN s_mc "ev" + 88) + 8) →
              x ≠ BitVec.ofNat 64 (memW s_mc (globN s_mc "ev" + 88) + 16) →
              x ≠ BitVec.ofNat 64 (npw.toNat + 8 * memW s_mc (memW s_mc (globN s_mc "ev" + 88) + 8)) →
              post.memory x = s_mc.memory x := by
            rw [he0_mc, hl0_mc, hn0_mc]
            intro x hx0 hx8 hx16 hxs
            rw [hpost_mem]
            have hne_sw : x ≠ slotw := by
              intro h; apply hxs; rw [← hslot_in_arr, hslot_bv]; exact h
            change (if x = slotw then HolWordLab.word (BitVec.ofNat 64 log) else sb.memory x) = s_mc.memory x
            rw [if_neg hne_sw]
            exact hsb_mem x hx0 hx8 hx16
          have hl0_post_mc : memW post (memW s_mc (globN s_mc "ev" + 88)) = npw.toNat := by
            rw [he0_mc, hl0_mc]
            have hm : post.memory (BitVec.ofNat 64 l0) = sb.memory (BitVec.ofNat 64 l0) := by
              rw [hpost_mem]
              change (if BitVec.ofNat 64 l0 = slotw then HolWordLab.word (BitVec.ofNat 64 log)
                else sb.memory (BitVec.ofNat 64 l0)) = _
              exact if_neg (Ne.symm (by simpa using hslot_ne_hdr 0 (by omega)))
            exact (show memW post l0 = memW sb l0 by unfold memW; rw [hm]).trans hsb_m0
          have hl8_post_mc : memW post (memW s_mc (globN s_mc "ev" + 88) + 8) =
              memW s_mc (memW s_mc (globN s_mc "ev" + 88) + 8) + 1 := by
            rw [he0_mc, hl0_mc, hn0_mc]
            have hm : post.memory (BitVec.ofNat 64 (l0 + 8)) = sb.memory (BitVec.ofNat 64 (l0 + 8)) := by
              rw [hpost_mem]
              change (if BitVec.ofNat 64 (l0 + 8) = slotw then HolWordLab.word (BitVec.ofNat 64 log)
                else sb.memory (BitVec.ofNat 64 (l0 + 8))) = _
              exact if_neg (Ne.symm (hslot_ne_hdr 8 (by omega)))
            exact (show memW post (l0 + 8) = memW sb (l0 + 8) by unfold memW; rw [hm]).trans hsb_m8
          have hl16_post_mc : memW post (memW s_mc (globN s_mc "ev" + 88) + 16) = 2 * cap0 := by
            rw [he0_mc, hl0_mc]
            have hm : post.memory (BitVec.ofNat 64 (l0 + 16)) = sb.memory (BitVec.ofNat 64 (l0 + 16)) := by
              rw [hpost_mem]
              change (if BitVec.ofNat 64 (l0 + 16) = slotw then HolWordLab.word (BitVec.ofNat 64 log)
                else sb.memory (BitVec.ofNat 64 (l0 + 16))) = _
              exact if_neg (Ne.symm (hslot_ne_hdr 16 (by omega)))
            exact (show memW post (l0 + 16) = memW sb (l0 + 16) by unfold memW; rw [hm]).trans hsb_m16
          have hslot_post_mc : memW post (npw.toNat + 8 * memW s_mc (memW s_mc (globN s_mc "ev" + 88) + 8)) = log := by
            rw [he0_mc, hl0_mc, hn0_mc]
            have hm : post.memory (BitVec.ofNat 64 (npw.toNat + 8 * n0)) = .word (BitVec.ofNat 64 log) := by
              rw [← hslot_in_arr, hslot_bv, hpost_mem]
              change (if slotw = slotw then HolWordLab.word (BitVec.ofNat 64 log) else sb.memory slotw) = _
              exact if_pos rfl
            unfold memW; rw [hm]; exact Nat.mod_eq_of_lt hlog_lt264
          have hpref_post_mc : ∀ i < memW s_mc (memW s_mc (globN s_mc "ev" + 88) + 8),
              memW s_mc (npw.toNat + 8 * i) = memW s_mc (memW s_mc (memW s_mc (globN s_mc "ev" + 88)) + 8 * i) := by
            rw [he0_mc, hl0_mc, hn0_mc, hl0_p_mc]
            intro i hi
            have hmc_eq : memW s_mc (npw.toNat + 8 * i) = memW s (memW s l0 + 8 * i) := hpref_mc i hi
            have hs_eq : memW s_mc (memW s l0 + 8 * i) = memW s (memW s l0 + 8 * i) := by
              have hfl_in : frameLogs s (e0, c0) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
              have hfl_def : frameLogs s (e0, c0) = (memW s l0, 8 * cap0) := rfl
              have hfl_b : (frameLogs s (e0, c0)).1 + (frameLogs s (e0, c0)).2 < 2 ^ 64 := by
                rcases hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨_, h2⟩ | ⟨_, h2⟩
                · have hh := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hh; omega
                · omega
              have hfl_b' : memW s l0 + 8 * cap0 < 2 ^ 64 := by simpa [hfl_def] using hfl_b
              have hfl_8 : (memW s l0) % 8 = 0 := hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
              have hn_le_cap : n0 ≤ cap0 := hhead_FW.2.2.2.2.2.2.2.2.2.2.2.1
              exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
                (hu_fo_mc (e0, c0) hhead_mem _ hfl_in hfl_b)
                (by omega) (by simpa [hfl_def] using le_of_lt hfl_b)
                ⟨by simp [hfl_def],
                 by simpa [hfl_def] using (show memW s l0 + 8 * i + 8 ≤ memW s l0 + 8 * cap0 by omega)⟩
            omega
          have hlog_pw_mc : (logOwnedIvls s_mc log).Pairwise Disj := by rwa [hlog_own_mc]
          have hlog_disj_fo_mc : ∀ ec ∈ evmChain s_mc, ∀ o1 ∈ logOwnedIvls s_mc log,
              ∀ o2 ∈ frameObjects s_mc ec, Disj o1 o2 := by
            intro ec hec o1 ho1 o2 ho2
            rw [hch_mc] at hec; rw [hlog_own_mc] at ho1; rw [(hfo_mc ec hec).1] at ho2
            exact hlog_disj_fo ec hec o1 ho1 o2 ho2
          have hlog_disj_ht_mc : ∀ o ∈ logOwnedIvls s_mc log, ∀ t ∈ S,
              ∀ j ∈ htabFootprint s_mc t, Disj o j := by
            intro o ho t ht j hj
            rw [hlog_own_mc] at ho; rw [hfp_mc t ht] at hj
            exact hlog_disj_ht o ho t ht j hj
          have hlog_disj_fix_mc : ∀ o ∈ logOwnedIvls s_mc log, ∀ j ∈ fixedObjects s_mc, Disj o j := by
            intro o ho j hj
            rw [hlog_own_mc] at ho; rw [hfeq_mc] at hj
            exact hlog_disj_fix o ho j hj
          have hlog_disj_msg_mc : ∀ o ∈ logOwnedIvls s_mc log,
              ∀ ec ∈ evmChain s_mc, Disj (memW s_mc (ec.1 + 112), 176) o := by
            intro o ho ec hec
            rw [hlog_own_mc] at ho; rw [hch_mc] at hec
            rw [(hrec_mc ec hec).1 112 (by omega) (by omega)]
            exact hlog_disj_msg o ho ec hec
          obtain ⟨hAR_p, hInv_p, hch_p, hR_p, hfix_p, hfp_p, hsc_p, hfl0_p, htail_p, hfo0_p⟩ :=
            evmInvAt_of_head_log_store_fc hAR_mc hInv_mc hG_post hpost_glob_mc hpost_be_mc
              (p' := npw.toNat) (cap' := 2 * cap0) (log := log)
              (Or.inr ⟨hnp_sb, by convert hwok_mc' using 2; omega, hnp_fo, hnp_ht, hnp_fix,
                hnp_av, hnp_msg, hnp_disj_log⟩)
              (by omega)
              (by rw [he0_mc, hl0_mc, hn0_mc]; omega)
              hmem_out_mc hl0_post_mc hl8_post_mc hl16_post_mc hslot_post_mc hpref_post_mc
              hlog_wa_mc hlog_ok_mc hlog_pw_mc hlog_disj_fo_mc hlog_disj_ht_mc
              hlog_disj_fix_mc hlog_av_mc hlog_disj_msg_mc
          have hgk_p : GlobalsKept ["heap_ptr"] s post := by
            intro g hg; rw [hpost_glob_mc]; exact hgk_s_mc g hg
          have hhp_p : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
            have hgp : globN post "heap_ptr" = globN s_mc "heap_ptr" := by
              simp [globN, hpost_glob_mc]
            omega
          have hui_grow : ∀ i : Ivl, i.1 + i.2 < 2 ^ 64 →
              Allocated s i →
              Disj i (l0, 24) →
              Disj i (frameLogs s (e0, c0)) →
              InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i := by
            intro i hi_bnd hi_al hdi_l0 _ a ha8 ha1 ha2
            have ha_lt : a.toNat < 2 ^ 64 := a.isLt
            have hu_mc : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s s_mc i :=
              ivlUnhit_of_fresh_heap_bytes_fc hbe_s_mc hhp_s_mc hbyte_s_mc hi_bnd
                (disj_fresh_of_allocated_s5 hAs.2 hAR_mc.2 hhp_s_mc hi_al)
            have hne_hdr : ∀ k, k + 8 ≤ 24 → a ≠ BitVec.ofNat 64 (l0 + k) := by
              intro k hk heq
              have htn := congrArg BitVec.toNat heq
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at htn
              rcases hdi_l0 with hd | hd | hd | hd <;> (try dsimp only at hd) <;> omega
            have hne_slot : a ≠ BitVec.ofNat 64 (npw.toNat + 8 * n0) := by
              intro heq
              have hnp_bnd' :=
                InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAR_mc.2 (Or.inl hnp_sb)
              have hnp_bnd : npw.toNat + 16 * cap0 ≤ 2 ^ 64 := by dsimp only at hnp_bnd'; omega
              have htn := congrArg BitVec.toNat heq
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at htn
              have hdi_np : Disj i (npw.toNat, 8 * (2 * cap0)) :=
                InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right
                  (by rw [Nat.add_sub_of_le hhp_s_mc]; exact hin_fresh)
                  (disj_fresh_of_allocated_s5 hAs.2 hAR_mc.2 hhp_s_mc hi_al)
              rcases hdi_np with hd | hd | hd | hd <;> (try dsimp only at hd) <;> omega
            have hm1 : post.memory a = s_mc.memory a := by
              have h := hmem_out_mc a
              rw [he0_mc, hl0_mc, hn0_mc] at h
              exact h (hne_hdr 0 (by omega)) (hne_hdr 8 (by omega)) (hne_hdr 16 (by omega)) hne_slot
            exact hm1.trans (hu_mc a ha8 ha1 ha2)
          have he16_p : memW post (e0 + 16) = memW s (e0 + 16) := by
            have hpw0 : (frameObjects s (e0, c0)).Pairwise Disj := by
              have hpw := hInv.2.2.2.2.2.2.2.1
              rw [evmChain_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
              exact hpw.1
            unfold frameObjects at hpw0
            have hrest := (List.pairwise_cons.1 hpw0).1
            have hd_l0 : Disj (e0, 280) (l0, 24) := hrest _ (by simp [l0])
            have hd_fl : Disj (e0, 280) (frameLogs s (e0, c0)) := hrest _ (by simp)
            have he_lt : e0 + 280 < 2 ^ 64 := by
              have hse : scratchEnd < 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
              exact lt_of_le_of_lt (hhead_FW.1 (e0, 280) (by simp)).1.2 hse
            exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hui_grow (e0, 280) he_lt (Or.inr (hhead_FW.1 (e0, 280) (by simp)).1) hd_l0 hd_fl)
              (by have := he_wok.1; omega) (by omega) ⟨by omega, by omega⟩
          refine ⟨hAR_p, hInv_p, hpost_loc, hpost_be_mc.trans hbe_s_mc, hgk_p, hhp_p,
            hch_p.trans hch_mc, hR_p.trans hR_mc, hfix_p.trans hfeq_mc,
            fun t ht => (hfp_p t ht).trans (hfp_mc t ht), ?_, ?_, ?_, ?_, hui_grow,
            fun ivls hav => avoidsTries_head_log_store_s5 hAR_mc hInv_mc hG_post hpost_glob_mc hpost_be_mc
              (Or.inr ⟨hnp_sb, by convert hwok_mc' using 2; omega, hnp_ht, hnp_fix, hnp_av⟩)
              (by rw [he0_mc, hl0_mc, hn0_mc]; omega) hmem_out_mc
              (avoidsTries_fresh_heap_transport_fc hAs hInv hAR_mc hbe_s_mc hhp_s_mc
                hgk_s_mc hout_s_mc hbyte_s_mc hav), he16_p⟩
          · intro ec hec
            have hec_mc : ec ∈ evmChain s_mc := by rwa [hch_mc]
            obtain ⟨hsc1, hm24, hm32, hm40, hm112, hm56⟩ := hsc_p ec hec_mc
            obtain ⟨he_mc_eq, hc_mc_eq, _⟩ := hrec_mc ec hec
            exact ⟨hsc1.trans (hfo_mc ec hec).2.1,
              hm24.trans (he_mc_eq 24 (by omega) (by omega)),
              hm32.trans (he_mc_eq 32 (by omega) (by omega)),
              hm40.trans (he_mc_eq 40 (by omega) (by omega)),
              hm112.trans (he_mc_eq 112 (by omega) (by omega)),
              hm56.trans (hc_mc_eq 56 (by omega) (by omega))⟩
          · intro ec hec
            rw [evmChain_cons] at hec
            rcases List.mem_cons.1 hec with rfl | htl
            · right
              have hfl0_s : frameLogs post (globN s "ev", globN s "cur_cont") = (npw.toNat, 8 * (2 * cap0)) := by
                simpa [he0_mc, hc0_mc] using hfl0_p
              rw [hfl0_s]
              have hgp : globN post "heap_ptr" = globN s_mc "heap_ptr" := by
                simp [globN, hpost_glob_mc]
              rw [hgp]; exact hnp_sb
            · left
              have htl_mc : ec ∈ (evmChain s_mc).tail := by rwa [hch_mc]
              exact (htail_p ec htl_mc).1.trans (hfo_mc ec (List.mem_of_mem_tail htl)).2.2.1
          · intro ec htl
            have htl_mc : ec ∈ (evmChain s_mc).tail := by rwa [hch_mc]
            exact (htail_p ec htl_mc).2.trans (hfo_mc ec (List.mem_of_mem_tail htl)).1
          · refine ⟨npw.toNat, 2 * cap0, ?_, ?_, ?_⟩
            · simpa [he0_mc, hc0_mc] using hfl0_p
            · right
              have hgp : globN post "heap_ptr" = globN s_mc "heap_ptr" := by
                simp [globN, hpost_glob_mc]
              rw [hgp]; exact hin_fresh
            · have hfo0_s := hfo0_p
              rw [he0_mc, hc0_mc] at hfo0_s
              obtain ⟨he_mc_eq, _, _⟩ := hrec_mc (e0, c0) hhead_mem
              obtain ⟨_, _, _, hfr_mc_eq, hflo_mc_eq⟩ := hfo_mc (e0, c0) hhead_mem
              rw [he_mc_eq 8 (by omega) (by omega), he_mc_eq 232 (by omega) (by omega),
                  he_mc_eq 24 (by omega) (by omega), he_mc_eq 40 (by omega) (by omega),
                  he_mc_eq 88 (by omega) (by omega),
                  hfr_mc_eq, hflo_mc_eq, hlog_own_mc] at hfo0_s
              exact hfo0_s

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
