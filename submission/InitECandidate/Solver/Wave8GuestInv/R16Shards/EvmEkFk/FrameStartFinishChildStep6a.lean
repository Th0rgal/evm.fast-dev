import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChild

set_option Elab.async false
set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23 (GlobalsKept)
open InitECandidate.Solver.Wave8GuestInv.R11Shards

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

theorem lookup_incorporate_child_on_success_6a :
    originalRuntimeCode.lookup (ofString "incorporate_child_on_success") =
      some ([(ofString "child", .one)],
        sourceFnBody Guest.Software.guestFn_incorporate_child_on_success, .one) :=
  lookup_of_guestAst_getElem 592 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_incorporate_child_on_success) rfl

def incorpSuccessCallees (f : MlS) : Bool :=
  f == ofString "incorporate_child_on_error" ||
    logAppendCallees f ||
    htabUnionCallees f ||
    f == ofString "incorporate_child_on_success"

private theorem noCatchableRaise_mono_6a {g1 g2 : MlS → Bool}
    (himp : ∀ f, g1 f = true → g2 f = true) :
    ∀ p : ProgHOL 64, StateRestoreEpilogue.noCatchableRaise g1 p = true →
      StateRestoreEpilogue.noCatchableRaise g2 p = true
  | .skip, _ | .«break», _ | .«continue», _ | .annot _ _, _ | .«return» _, _
  | .assign _ _ _, _ | .store _ _, _ | .storeByte _ _, _ | .store32 _ _, _
  | .shMemStore _ _ _, _ | .extCall _ _ _ _ _, _ => rfl
  | .raise _ _, hp => hp
  | .dec _ _ _ b, hp => noCatchableRaise_mono_6a himp b hp
  | .seq a b, hp => by
      simp only [StateRestoreEpilogue.noCatchableRaise, Bool.and_eq_true] at hp ⊢
      exact ⟨noCatchableRaise_mono_6a himp a hp.1, noCatchableRaise_mono_6a himp b hp.2⟩
  | .ite _ a b, hp => by
      simp only [StateRestoreEpilogue.noCatchableRaise, Bool.and_eq_true] at hp ⊢
      exact ⟨noCatchableRaise_mono_6a himp a hp.1, noCatchableRaise_mono_6a himp b hp.2⟩
  | .while _ b, hp => noCatchableRaise_mono_6a himp b hp
  | .decCall _ _ fn _ cont, hp => by
      simp only [StateRestoreEpilogue.noCatchableRaise, Bool.and_eq_true] at hp ⊢
      exact ⟨himp fn hp.1, noCatchableRaise_mono_6a himp cont hp.2⟩
  | .call tail fn _, hp => by
      rcases tail with _ | ⟨_, hdl⟩
      · simp [StateRestoreEpilogue.noCatchableRaise] at hp
      · rcases hdl with _ | _
        · exact himp fn hp
        · simp [StateRestoreEpilogue.noCatchableRaise] at hp
  | .shMemLoad _ _ _ _, hp => by simp [StateRestoreEpilogue.noCatchableRaise] at hp

theorem incorpSuccessCallees_good :
    ∀ f, incorpSuccessCallees f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      StateRestoreEpilogue.noCatchableRaise incorpSuccessCallees body = true := by
  intro f hf values body callee rs hfound
  simp only [incorpSuccessCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((rfl | hla) | hhu) | rfl
  · obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    have hl := lookup_incorporate_child_on_error
    change originalRuntimeCode.lookup (ofString "incorporate_child_on_error") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · exact noCatchableRaise_mono_6a (fun g hg => by simp [incorpSuccessCallees, hg]) body
      (logAppendCallees_good f hla values body callee rs hfound)
  · exact noCatchableRaise_mono_6a (fun g hg => by simp [incorpSuccessCallees, hg]) body
      (htabUnionCallees_good f hhu values body callee rs hfound)
  · obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    have hl := lookup_incorporate_child_on_success_6a
    change originalRuntimeCode.lookup (ofString "incorporate_child_on_success") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

abbrev M08IvlUnhit6a {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i

theorem disj_symm_6a {i j : Ivl} (h : Disj i j) : Disj j i :=
  R11Shards.Disj.symm h

theorem disj_fresh_of_allocated_6a {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, _, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp
  rcases hj with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))

private theorem disj_fresh_of_zero_or_allocated_6a {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : j.2 = 0 ∨ Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  rcases hj with h0 | hal
  · exact Or.inl h0
  · exact disj_fresh_of_allocated_6a hAs hAp hhp hal

private theorem ivlUnhit_of_out_4_6a {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {l0 p' cap' : Nat} {i : Ivl}
    (hl0_bnd : l0 + 24 ≤ 2 ^ 64)
    (harr_bnd : p' + 8 * cap' ≤ 2 ^ 64)
    (hn0_lt : memW s (l0 + 8) < cap')
    (hmem_out : ∀ x : BitVec 64,
      x ≠ BitVec.ofNat 64 l0 →
      x ≠ BitVec.ofNat 64 (l0 + 8) →
      x ≠ BitVec.ofNat 64 (l0 + 16) →
      x ≠ BitVec.ofNat 64 (p' + 8 * memW s (l0 + 8)) →
      post.memory x = s.memory x)
    (hd_l0 : Disj i (l0, 24))
    (hd_arr : Disj i (p', 8 * cap')) :
    M08IvlUnhit6a s post i := by
  intro a _ ha1 ha2
  apply hmem_out a
  · intro rfl
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ha1 ha2
    rcases hd_l0 with h | h | h | h <;> omega
  · intro rfl
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ha1 ha2
    rcases hd_l0 with h | h | h | h <;> omega
  · intro rfl
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ha1 ha2
    rcases hd_l0 with h | h | h | h <;> omega
  · intro rfl
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ha1 ha2
    rcases hd_arr with h | h | h | h <;> omega

theorem wordsOK_of_unhit_6a {F : Type} {s post : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hdom : post.memaddrs = s.memaddrs) (hw : WordsOK s i) :
    WordsOK post i :=
  (R14Shards.OpHandlersA.wordsOK_congr_dom hdom).2 hw

theorem wordAt_of_unhit_6a {F : Type} {s post : PanSemStateFiniteExact 64 F} {a : Nat}
    (hdom : post.memaddrs = s.memaddrs) (hw : WordAt s a) :
    WordAt post a :=
  (R14Shards.OpHandlersA.wordAt_congr_dom hdom).2 hw

theorem logEntry_unhit_transport_6a {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {log : Nat}
    (hAs : ArenaReady s)
    (hdom : post.memaddrs = s.memaddrs)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (haddr : globN post "vm_system_address" = globN s "vm_system_address")
    (hu : M08IvlUnhit6a s post (log, 40))
    (hlog : LogEntryOK s log) :
    LogEntryOK post log ∧ logOwnedIvls post log = logOwnedIvls s log := by
  have hb : log + 40 < 2 ^ 64 := by
    have hh := hAs.2.2.1
    have hl := hlog.2.1.2
    rw [R11Shards.heapLimit_val] at hh; dsimp only at hl; omega
  have hw : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (log + off) = memW s (log + off) := by
    intro off hoff
    have ho : off + 8 ≤ 40 ∧ off % 8 = 0 := by revert off hoff; decide
    exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu
      (by have := hlog.1.1; omega) (by dsimp; omega) ⟨by omega, by omega⟩
  exact ⟨logEntryOK_transport_fc hlog hdom hhp hw,
    logOwnedIvls_transport_fc haddr hw⟩

theorem ev_head_facts_6a {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
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

theorem eval_load_ev_off_6a {F : Type} (s : PanSemStateFiniteExact 64 F)
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
  unfold memW; rw [hmem_eq]; simp

theorem eval_load_local_off_6a {F : Type} (s : PanSemStateFiniteExact 64 F)
    {lname : String} {base sz off : Nat}
    (hlk : s.locals.lookup (ofString lname) = some (.val (.word (BitVec.ofNat 64 base))))
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
  simp only [hmem_dom, ↓reduceIte, hmem_eq, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq]
  unfold memW; rw [hmem_eq]; simp

theorem wordsOK_updW_6a {F : Type} (s : PanSemStateFiniteExact 64 F)
    {ivl : Ivl} (hw : WordsOK s ivl) (a w : BitVec 64) :
    WordsOK { s with memory := R14Shards.OpHandlersA.updW s.memory a w } ivl := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨wk, hdom, hm⟩ := hw.2.2 k hk
  dsimp only [WordAt, R14Shards.OpHandlersA.updW]
  by_cases heq : BitVec.ofNat 64 (ivl.1 + 8 * k) = a
  · exact ⟨w, hdom, if_pos heq⟩
  · exact ⟨wk, hdom, (if_neg heq).trans hm⟩

theorem fc_eval_sub_words_6a {F : Type} (s : PanSemStateFiniteExact 64 F)
    {a b : ExpHOL 64} {aw bw : BitVec 64}
    (ha : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a =
      some (.val (.word aw)))
    (hb : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) b =
      some (.val (.word bw))) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .sub [a, b]) = some (.val (.word (aw - bw))) := by
  simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp,
    valueIsWord, valueWord]

theorem fc_store_sub_words_6a {F : Type} {s post : PanSemStateFiniteExact 64 F}
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
  have hv := fc_eval_sub_words_6a s ha hb
  obtain ⟨w, hw, hp⟩ := R14Shards.OpHandlersA.store_global_off_word
    he hen hbound (fun v h => by rw [hv] at h; exact ⟨aw - bw, (Option.some.inj h).symm⟩) hrun
  rw [hv] at hw
  have hw' : w = aw - bw := by simpa using hw.symm
  simpa only [hw'] using hp

theorem avoidsTries_sub_6a {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {as bs : List Ivl} (hsub : ∀ a ∈ as, a ∈ bs) (h : AvoidsTries s S bs) :
    AvoidsTries s S as := by
  obtain ⟨Nd, hTr, hd⟩ := h
  exact ⟨Nd, hTr, fun a ha j hj => hd a (hsub a ha) j hj⟩

private theorem avoidsTries_congr_6a {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ivls : List Ivl}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hAp : ArenaReady post) (hglob : post.globals = s.globals) (hbe : post.be = s.be)
    {l0 p' cap' : Nat}
    (hl0_wok : WordsOK s (l0, 24))
    (harr_wok : WordsOK s (p', 8 * cap'))
    (hl0_bnd : l0 + 24 ≤ 2 ^ 64)
    (harr_bnd : p' + 8 * cap' ≤ 2 ^ 64)
    (hn0_lt : memW s (l0 + 8) < cap')
    (hmem_out : ∀ x : BitVec 64,
      x ≠ BitVec.ofNat 64 l0 →
      x ≠ BitVec.ofNat 64 (l0 + 8) →
      x ≠ BitVec.ofNat 64 (l0 + 16) →
      x ≠ BitVec.ofNat 64 (p' + 8 * memW s (l0 + 8)) →
      post.memory x = s.memory x)
    (hl0_fo : (l0, 24) ∈ frameObjects s (globN s "ev", globN s "cur_cont"))
    (harr_fo_or : (p', 8 * cap') ∈ frameObjects s (globN s "ev", globN s "cur_cont") ∨
      ((∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj (p', 8 * cap') j) ∧
       (∀ j ∈ fixedObjects s, Disj (p', 8 * cap') j) ∧
       AvoidsTries s S [(p', 8 * cap')]))
    (hav : AvoidsTries s S ivls) :
    AvoidsTries post S ivls := by
  obtain ⟨Nd_v, hTr_v, hdj_v⟩ := hav
  obtain ⟨Nd_inv, hTr_inv, hAT_inv⟩ := hInv.2.2.2.2.2.2.2.2.2.1
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hFO_disj := hInv.2.2.2.2.2.2.2.2.1
  obtain ⟨Nd_a, hTr_a, hsub_v, hsub_inv, hd_arr_nd⟩ :
      ∃ Nd, TriesTypedWith s S Nd ∧
        (∀ j ∈ nodeExtents s Nd, j ∈ nodeExtents s Nd_v) ∧
        (∀ j ∈ nodeExtents s Nd, j ∈ nodeExtents s Nd_inv) ∧
        (∀ j ∈ nodeExtents s Nd, Disj (p', 8 * cap') j) := by
    obtain ⟨hTr_1, hsub_1⟩ := R11Shards.triesTypedWith_inter hTr_v hTr_inv
    rcases harr_fo_or with hfo | ⟨_, _, ⟨Nd_p, hTr_p, hd_p⟩⟩
    · refine ⟨_, hTr_1, fun j hj => (hsub_1 j hj).1, fun j hj => (hsub_1 j hj).2, fun j hj => ?_⟩
      exact hAT_inv _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead, rfl⟩, hfo⟩) j (hsub_1 j hj).2
    · obtain ⟨hTr_2, hsub_2⟩ := R11Shards.triesTypedWith_inter hTr_1 hTr_p
      refine ⟨_, hTr_2,
        fun j hj => (hsub_1 j (hsub_2 j hj).1).1,
        fun j hj => (hsub_1 j (hsub_2 j hj).1).2,
        fun j hj => hd_p _ (by simp) j (hsub_2 j hj).2⟩
  have hWT : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd_a :=
    ⟨hInv.1.1, hInv.1.2.1, hInv.1.2.2.1, hTr_a⟩
  have hdom_eq : post.memaddrs = s.memaddrs := hAp.1.memaddrs.trans hAs.1.memaddrs.symm
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  set n0 := memW s (l0 + 8)
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
    refine ⟨hAp.1.code.trans hAs.1.code.symm, hdom_eq,
      hAp.1.shMemaddrs.trans hAs.1.shMemaddrs.symm,
      hAp.1.baseAddr.trans hAs.1.baseAddr.symm, hbe, hglob, ?_, ?_, ?_⟩
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
  have hfo_disj_wti : ∀ o ∈ frameObjects s (globN s "ev", globN s "cur_cont"),
      ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_a,
      i.2 = 0 ∨ Disj o i := by
    intro o ho i hi
    unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead _ ho).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead _ ho).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead _ ho).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead _ ho).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead _ ho).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects h5))
    · exact Or.inr (hAT_inv _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead, rfl⟩, ho⟩) i (hsub_inv i h6))
  have harr_disj_wti : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_a,
      i.2 = 0 ∨ Disj (p', 8 * cap') i := by
    rcases harr_fo_or with hfo | ⟨hd_ht, hd_fix, _⟩
    · exact hfo_disj_wti _ hfo
    · intro i hi
      unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi
      simp only [List.mem_append] at hi
      rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
      · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
        exact Or.inr (hd_ht t ht i hfp)
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
        exact Or.inr (hd_fix _ (InitECandidate.Solver.Wave8Contracts.M23.typedRec_in_fixedObjects s hr))
      · simp only [List.mem_singleton] at h3; subst h3
        have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
            32 * globN s "journal_cap") ∈ fixedObjects s := by
          unfold fixedObjects
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
        exact Or.inr (hd_fix _ hfix_j)
      · exact Or.inr (hd_fix _ (InitECandidate.Solver.Wave8Contracts.M23.blockOut_in_fixedObjects h4))
      · exact Or.inr (hd_fix _ (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects h5))
      · exact Or.inr (hd_arr_nd i h6)
  have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd_a :=
    InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect.sameTypedCells
      (Rl := []) (extra := [(l0, 24), (p', 8 * cap')]) hAs.1.memaddrs hWT
      (fun _ h => by simp at h)
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact hfo_disj_wti _ hl0_fo
        · exact harr_disj_wti)
      (by simpa using heff)
  have hfeq := InitECandidate.Solver.Wave8Contracts.M23.fixedObjects_eq_of_nonHeapGlobalsKept
    hAs.2 hWT.1 hWT.2.2.1 hcell (fun name _ _ _ => by rw [hglob])
  have hFT_post := InitECandidate.Solver.Wave8Contracts.M23.fixedTyped_of_eq hAp hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1 hAs hAp hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  refine ⟨Nd_a, hWT_post.2.2.2, fun o ho j hj => ?_⟩
  rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_a.1 hcell] at hj
  exact hdj_v o ho j (hsub_v j hj)

private theorem fresh_heap_bridge_6a {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg_kept : GlobalsKept ["heap_ptr"] s post)
    (hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") →
        memB post b = memB s b) :
    fixedObjects post = fixedObjects s ∧
    (∀ t ∈ S, htabFootprint post t = htabFootprint s t) ∧
    (∀ ec ∈ evmChain s,
      frameObjects post ec = frameObjects s ec ∧
      frameScratch post ec = frameScratch s ec ∧
      frameLogs post ec = frameLogs s ec ∧
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.1 + 112) = memW s (ec.1 + 112) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56)) ∧
    memW post (globN s "ev" + 16) = memW s (globN s "ev" + 16) ∧
    memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) ∧
    memW post (globN s "ev" + 232) = memW s (globN s "ev" + 232) := by
  have hglob_nonHeap : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN post nm = globN s nm := by
    intro nm hne
    exact InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
      (hg_kept (ofString nm) (by simp [hne]))
  have hdom_eq : post.memaddrs = s.memaddrs := hAp.1.memaddrs.trans hAs.1.memaddrs.symm
  obtain ⟨Nd_s, hTr_s, _⟩ := hInv.2.2.2.2.2.2.2.2.2.1
  have hWT_s : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd_s :=
    ⟨hInv.1.1, hInv.1.2.1, hInv.1.2.2.1, hTr_s⟩
  have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd_s := by
    have hwti_disj : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_s,
        Disj i (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
      intro i hi
      exact disj_fresh_of_zero_or_allocated_6a hAs.2 hAp.2 hhp
        (InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls_allocated hWT_s hi)
    refine ⟨hbe, hdom_eq, hAs.1.memaddrs, ?_, ?_, ?_⟩
    · intro a hna; apply hout_dom a; rwa [hAs.1.memaddrs]
    · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
      · have hord := (InitECandidate.Solver.Wave8Contracts.M23.ordinaryDomain_iff (BitVec.ofNat 64 a)).mp hdom
        have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        have hhe : heapEnd < 2 ^ 64 := by rw [R11Shards.heapEnd_val]; decide
        have ha_bound : a + 8 < 2 ^ 64 := by rw [hbit] at hord; omega
        have hw : memW post a = memW s a := by
          apply (R13SoloHtabSet.memW_eq_iff_memB (a₁ := a) (a₂ := a) hbe ha8 ha8 ha_bound ha_bound).2
          intro k hk
          apply hbyte (a + k) (by omega)
          intro ⟨hb1, hb2⟩
          rcases hwti_disj i hi with hd | hd | hd | hd
          · omega
          · dsimp only at hd; omega
          · dsimp only at hd; omega
          · dsimp only at hd; omega
        cases hp : post.memory (BitVec.ofNat 64 a) with
        | word wp =>
          cases hs : s.memory (BitVec.ofNat 64 a) with
          | word ws =>
            simp only [memW, hp, hs] at hw
            exact congrArg HolWordLab.word (BitVec.eq_of_toNat_eq hw)
      · apply hout_dom _ (by rwa [hAs.1.memaddrs])
    · intro b hb ⟨i, hi, hb1, hb2⟩
      apply hbyte b hb
      intro ⟨h1, h2⟩
      rcases hwti_disj i hi with hd | hd | hd | hd
      · omega
      · dsimp only at hd; omega
      · dsimp only at hd; omega
      · dsimp only at hd; omega
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [InitECandidate.Solver.Wave8Contracts.M23.blockOutObjects_eq hAs.2 hWT_s.2.2.1 hcell
          (hglob_nonHeap "bo" (by decide)),
        InitECandidate.Solver.Wave8Contracts.M23.balObjects_eq hAs.2 hWT_s.1 hWT_s.2.2.1 hcell
          (hglob_nonHeap "bal_accounts" (by decide)),
        hglob_nonHeap "journal" (by decide),
        hglob_nonHeap "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    rw [hglob_nonHeap gn.1 hne]
  have hfp_eq : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => InitECandidate.Solver.Wave8Contracts.M23.htabFootprint_eq hcell ht (hWT_s.1.2.1 t ht).1
  have hfo_disj : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec,
      Disj o (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro ec hec o ho
    have hFW := hInv.2.2.2.2.1 ec hec
    have hsep : heapLimit ≤ scratchStart := by decide
    have hhp_lim : globN post "heap_ptr" ≤ heapLimit := hAp.2.2.1
    have hss_fm : scratchStart ≤ globN s "frame_mem_ptr" := hAs.2.2.2.1
    have hfm_sc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.2.1
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
  have hu_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, o.1 + o.2 < 2 ^ 64 →
      M08IvlUnhit6a s post o := by
    intro ec hec o ho hob
    exact ivlUnhit_of_fresh_heap_bytes_fc hbe hhp hbyte hob (hfo_disj ec hec o ho)
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hInv.2.2.2.2.1 ec hec
    have hse_lt : scratchEnd < 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
    have hb1 : ec.1 + 280 < 2 ^ 64 := by
      have h := (hFW.1 (ec.1, 280) (by simp)).1.2; dsimp only at h; omega
    have hb2 : ec.2 + 104 < 2 ^ 64 := by
      have h := (hFW.1 (ec.2, 104) (by simp)).1.2; dsimp only at h; omega
    have hb88 : memW s (ec.1 + 88) + 24 < 2 ^ 64 := by
      have h := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.2; dsimp only at h; omega
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    refine ⟨fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo ec hec (ec.1, 280) (by simp [frameObjects]) hb1)
              (by omega) (by omega) ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo ec hec (ec.2, 104) (by simp [frameObjects]) hb2)
              (by omega) (by omega) ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]) hb88)
              (by omega) (by omega) ⟨by omega, by omega⟩⟩
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [evmChain_cons]; exact List.mem_cons_self
  refine ⟨hfeq, hfp_eq, ?_,
    (hrec_eq _ hhead_mem).1 16 (by omega) (by omega),
    (hrec_eq _ hhead_mem).1 40 (by omega) (by omega),
    (hrec_eq _ hhead_mem).1 232 (by omega) (by omega)⟩
  intro ec hec
  have hFW := hInv.2.2.2.2.1 ec hec
  obtain ⟨he_eq, hc_eq, h88_eq⟩ := hrec_eq ec hec
  have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
    simpa using h88_eq 0 (by omega) (by omega)
  have hl8 : memW post (memW s (ec.1 + 88) + 8) = memW s (memW s (ec.1 + 88) + 8) :=
    h88_eq 8 (by omega) (by omega)
  have hl16 : memW post (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16) :=
    h88_eq 16 (by omega) (by omega)
  have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
    intro i hi
    have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
    have hlen_le := hFW.2.2.2.2.2.2.2.2.2.2.2.1
    have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 < 2 ^ 64 := by
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨_, h2⟩ | ⟨_, h2⟩
      · have hh := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hh; omega
      · have hs := R11Shards.scratchEnd_val; omega
    have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
    exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
      (a := memW s (memW s (ec.1 + 88)) + 8 * i)
      (hu_fo ec hec _ hfl_in hfl_b)
      (by omega) (by unfold frameLogs at hfl_b ⊢; omega)
      ⟨by unfold frameLogs; omega, by unfold frameLogs; omega⟩
  have hflo_eq : frameLogObjects post ec = frameLogObjects s ec := by
    unfold frameLogObjects; dsimp only
    rw [he_eq 88 (by omega) (by omega), hl8]
    apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
    rw [hl0, harr_eq i hi]
    rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
    · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
      have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
      rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
    · exact (logEntry_fresh_heap_transport_fc hAs hAp hbe hhp
        (hglob_nonHeap "vm_system_address" (by decide)) hbyte (hent i hi).2).2.1
  have hfl_eq : frameLogs post ec = frameLogs s ec := by
    unfold frameLogs; rw [he_eq 88 (by omega) (by omega), hl0, hl16]
  have hfs_eq : frameScratch post ec = frameScratch s ec := by
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have hfo_eq : frameObjects post ec = frameObjects s ec := by
    unfold frameObjects frameLogs frameRet
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), hl0, hl16,
        he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega), hflo_eq]
  exact ⟨hfo_eq, hfs_eq, hfl_eq,
    he_eq 24 (by omega) (by omega),
    he_eq 32 (by omega) (by omega),
    he_eq 40 (by omega) (by omega),
    he_eq 112 (by omega) (by omega),
    hc_eq 56 (by omega) (by omega)⟩

private theorem guestInv_store_word_6a {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (ew w : BitVec 64) :
    GuestInv { s with memory := fun a => if a = ew then .word w else s.memory a } :=
  ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩

theorem log_append_head_fc_step {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {logExp : ExpHOL 64} {log : Nat}
    (hBS : FcBranchState s0 s S)
    (hlog_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      logExp = some (.val (.word (BitVec.ofNat 64 log))))
    (hlog_wa : WordAt s log)
    (hlog_ok : LogEntryOK s log)
    (hlog_pw : (logOwnedIvls s log).Pairwise Disj)
    (hlog_disj_fo : ∀ ec ∈ evmChain s, ∀ o1 ∈ logOwnedIvls s log,
      ∀ o2 ∈ frameObjects s ec, Disj o1 o2)
    (hlog_disj_ht : ∀ o ∈ logOwnedIvls s log, ∀ t ∈ S,
      ∀ j ∈ htabFootprint s t, Disj o j)
    (hlog_disj_fix : ∀ o ∈ logOwnedIvls s log, ∀ j ∈ fixedObjects s, Disj o j)
    (hlog_avoids : AvoidsTries s S (logOwnedIvls s log))
    (hlog_disj_msg : ∀ o ∈ logOwnedIvls s log,
      ∀ ec ∈ evmChain s, Disj (memW s (ec.1 + 112), 176) o)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), logExp])).1 ≠ some .timeOut) :
    let prog : ProgHOL 64 := .call (some (none, none)) (ofString "log_append")
      [.var .global (ofString "ev"), logExp]
    (∀ u, (evaluateHOLFiniteState s prog).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s prog).1 ∧
    ((evaluateHOLFiniteState s prog).1 = none →
      let post := (evaluateHOLFiniteState s prog).2
      FcBranchState s0 post S ∧
      post.locals = s.locals ∧
      globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
      GlobalsKept ["heap_ptr"] s post ∧
      post.be = s.be ∧
      evmChain post = evmChain s ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
      fixedObjects post = fixedObjects s ∧
      (∀ t ∈ S, htabFootprint post t = htabFootprint s t) ∧
      (∀ ec ∈ evmChain s, memW post (ec.1 + 112) = memW s (ec.1 + 112)) ∧
      memW post (globN s "ev" + 16) = memW s (globN s "ev" + 16) ∧
      memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) ∧
      memW post (globN s "ev" + 232) = memW s (globN s "ev" + 232) ∧
      (∀ ec ∈ (evmChain s).tail, frameObjects post ec = frameObjects s ec) ∧
      (∀ o ∈ frameObjects post (globN s "ev", globN s "cur_cont"),
        (∃ o0 ∈ frameObjects s (globN s "ev", globN s "cur_cont") ++ logOwnedIvls s log, o = o0) ∨
        Inside o (globN s "heap_ptr") (globN post "heap_ptr")) ∧
      (∀ ivls : List Ivl, AvoidsTries s S ivls → AvoidsTries post S ivls) ∧
      (∀ i : Ivl, (i.2 = 0 ∨ Allocated s i) →
        Disj i (memW s (globN s "ev" + 88), 24) →
        Disj i (frameLogs s (globN s "ev", globN s "cur_cont")) →
        M08IvlUnhit6a s post i)) := by
  dsimp only
  have hAs : ArenaReady s := hBS.arena
  have hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S := hBS.inv
  have hcode : s.code = originalRuntimeCode := hAs.1.code
  obtain ⟨hne_ret, hnone, herr⟩ := call0_outcome_fc (s := s)
    (fname := ofString "log_append") (args := [.var .global (ofString "ev"), logExp]) hnt
  have hno_err : ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), logExp])).1 := by
    intro he
    obtain ⟨vals, body, cal, ret, v, cpost, _, hl, hrun, _⟩ := herr he
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "log_append") vals =
        some (body, cal, ret) := by rwa [← hcode]
    obtain ⟨rfl, _, _, _, _, _, _⟩ :=
      R14Shards.OpHandlersA.two_word_arg_lookup (by decide) lookup_log_append_fc hl_orig
    exact StateRestoreEpilogue.evaluate_noCatchableRaise
      logAppendCallees logAppendCallees_good
      (sourceFnBody Guest.Software.guestFn_log_append) (by decide)
      (callEntryStateHOLFinite s cal) hcode (ofString "EvmErr") v (by decide)
      (by rw [hrun])
  refine ⟨hne_ret, hno_err, fun hn => ?_⟩
  obtain ⟨vals, body, cal, ret, rv, cpost, hargs, hl, hrun, hpost_eq⟩ := hnone hn
  obtain ⟨he_bnd, he_wok, he_lk, _, _⟩ := ev_head_facts_6a hAs hInv
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  set evw := BitVec.ofNat 64 e0
  set logw := BitVec.ofNat 64 log
  have hlog_lt64 : log < 2 ^ 64 := by
    have hh := hAs.2.2.1; have hl0 := hlog_ok.2.1.2
    rw [R11Shards.heapLimit_val] at hh; dsimp only at hl0; omega
  have hlogw_nat : logw.toNat = log := Nat.mod_eq_of_lt hlog_lt64
  have hevw_nat : evw.toNat = e0 := Nat.mod_eq_of_lt (by omega)
  have hev_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "ev")) = some (.val (.word evw)) := he_lk
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, hev_ev, hlog_ev, Option.some.injEq] at hargs
  subst hargs
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "log_append")
      [.val (.word evw), .val (.word logw)] = some (body, cal, ret) := by rwa [← hcode]
  obtain ⟨rfl, rfl, wE, wL, hvals_eq, hcal_e, hcal_log⟩ :=
    R14Shards.OpHandlersA.two_word_arg_lookup (by decide) lookup_log_append_fc hl_orig
  injection hvals_eq with hvE hrestL
  injection hvE with hvE'; injection hvE' with hwE_eq; subst hwE_eq
  injection hrestL with hvL _
  injection hvL with hvL'; injection hvL' with hwL_eq; subst hwL_eq
  set ent := callEntryStateHOLFinite s cal
  have hent_AR : ArenaReady ent := ⟨guestInv_with_locals_clock s cal _ hAs.1, hAs.2⟩
  have hent_e : ent.locals.lookup (ofString "e") = some (.val (.word evw)) := hcal_e
  have hent_log : ent.locals.lookup (ofString "log") = some (.val (.word logw)) := hcal_log
  have hbody_la : sourceFnBody Guest.Software.guestFn_log_append =
      .decCall (ofString "slot") .one (ofString "lst_push")
        [.load .one (.op .add [.var .local (ofString "e"), .const 88#64]), .const 8#64]
        (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
              (.return (.const 0#64))) := rfl
  change evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_log_append) =
    (some (.returned rv), cpost) at hrun
  rw [hbody_la, evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [evmChain_cons]; exact List.mem_cons_self
  have hhead_FW := hInv.2.2.2.2.1 _ hhead_mem
  obtain ⟨_, _, hb88, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb88
  set l0 := memW s (e0 + 88)
  set lw := BitVec.ofNat 64 l0
  have hl0_lt64 : l0 < 2 ^ 64 := by omega
  have hlw_nat : lw.toNat = l0 := Nat.mod_eq_of_lt hl0_lt64
  have hld_e88 := eval_load_local_off_6a ent hent_e he_wok he_bnd (off := 88) (by omega) (by omega)
  have hent_m88 : memW ent (e0 + 88) = l0 := rfl
  rw [hent_m88] at hld_e88
  have hargs_lp : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
      [.load .one (.op .add [.var .local (ofString "e"), .const 88#64]), .const 8#64] =
      some [.val (.word lw), .val (.word 8#64)] := by
    unfold evalListHOLFinite evalListHOLExact
    rw [hld_e88]; rfl
  have hlook_lp := pan_two_word_lookup ent.code.lookup (ofString "lst_push")
    (ofString "l") (ofString "esz")
    (sourceFnBody Guest.Software.guestFn_lst_push) lw 8#64
    (by decide)
    (by rw [hent_AR.1.code]; exact lookup_lst_push_fc)
  rw [hargs_lp] at hrun; dsimp only at hrun
  rw [hlook_lp] at hrun; dsimp only at hrun
  by_cases hclk_ent : ent.clock = 0
  · rw [if_pos hclk_ent] at hrun; simp at hrun
  · rw [if_neg hclk_ent] at hrun
    set cmap_lp := (HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
      (ofString "esz", ValueHOL.val (.word 8#64))
    rcases hlp_out : evaluateHOLFiniteState (callEntryStateHOLFinite ent cmap_lp)
        (sourceFnBody Guest.Software.guestFn_lst_push) with ⟨rlp, slp⟩
    rw [hlp_out] at hrun
    cases rlp with
    | none => simp at hrun
    | some rlp0 =>
      cases rlp0 with
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ => simp at hrun
      | returned vlp =>
        dsimp only at hrun
        have hl0_wok : WordsOK ent (lw.toNat, 24) := by
          rw [hlw_nat]; exact (hhead_FW.1 (l0, 24) (by simp [l0])).2
        have hl0_cap : 1 ≤ memW ent (lw.toNat + 16) := by
          rw [hlw_nat]; exact hhead_FW.2.2.2.2.2.2.2.2.2.2.1
        have hl0_len : memW ent (lw.toNat + 8) ≤ memW ent (lw.toNat + 16) := by
          rw [hlw_nat]; exact hhead_FW.2.2.2.2.2.2.2.2.2.2.2.1
        have harr_in : Inside (memW ent lw.toNat, 8 * memW ent (lw.toNat + 16)) sourceBase (globN ent "heap_ptr") ∨
            Inside (memW ent lw.toNat, 8 * memW ent (lw.toNat + 16)) (globN ent "scratch_ptr") scratchEnd := by
          rw [hlw_nat]; exact hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.1
        have harr_wok : WordsOK ent (memW ent lw.toNat, 8 * memW ent (lw.toNat + 16)) := by
          rw [hlw_nat]; exact hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hpw_head : (frameObjects s (e0, c0)).Pairwise Disj := by
          have hpw := hInv.2.2.2.2.2.2.2.1
          rw [evmChain_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
          exact hpw.1
        have hl_disj_arr : Disj (lw.toNat, 24) (memW ent lw.toNat, 8 * memW ent (lw.toNat + 16)) := by
          rw [hlw_nat]
          change Disj (l0, 24) (frameLogs s (e0, c0))
          unfold frameObjects at hpw_head
          have hp0 := List.pairwise_cons.1 hpw_head
          have hp1 := List.pairwise_cons.1 hp0.2
          have hp2 := List.pairwise_cons.1 hp1.2
          have hp3 := List.pairwise_cons.1 hp2.2
          have hp4 := List.pairwise_cons.1 hp3.2
          exact hp4.1 _ (by simp [frameLogs])
        have hspec := lst_push_body_logs_fc ent lw hent_AR hl0_wok (by rw [hlw_nat]; exact hb88)
          hl0_cap hl0_len harr_in harr_wok hl_disj_arr vlp (congrArg Prod.fst hlp_out)
        dsimp only at hspec
        rw [hlp_out] at hspec; dsimp only at hspec
        set post := (evaluateHOLFiniteState s
          (.call (some (none, none)) (ofString "log_append")
            [.var .global (ofString "ev"), logExp])).2
        rcases hspec with
          ⟨hn_lt_cap, slotw, rfl, hslot_nat, hG_slp, hglob_slp, hbe_slp, hmem_slp,
           hm0_slp, hm8_slp, hm16_slp⟩ |
          ⟨hn_eq_cap, s_mc, npw, slotw, rfl, hnpw_nat, hslot_nat, hAR_mc, hbe_mc, hhp_mc, hgk_mc,
           hout_mc, hbyte_mc, hwok_mc, hpref_mc, hG_slp, hglob_slp, hbe_slp, hmem_slp,
           hm0_slp, hm8_slp, hm16_slp⟩
        · -- Case 1: no grow (`n0 < cap0`)
          have hsh_sw : (shapeEqHOL (shapeOfHOLExact (.val (.word slotw) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word slotw) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hsh_sw] at hrun
          let st_slot := setVarHOLFinite (ofString "slot") (.val (.word slotw)) { slp with locals := ent.locals }
          have hk_eta := Prod.mk.eta (p := evaluateHOLFiniteState st_slot
            (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                  (.return (.const 0#64))))
          set rcont := (evaluateHOLFiniteState st_slot
            (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                  (.return (.const 0#64)))).1
          set scont := (evaluateHOLFiniteState st_slot
            (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                  (.return (.const 0#64)))).2
          change (rcont, { scont with locals := _ }) = (some (.returned rv), cpost) at hrun
          have hrcont_eq : rcont = some (.returned rv) := (Prod.mk.inj hrun).1
          have hcpost_eq : { scont with locals := _ } = cpost := (Prod.mk.inj hrun).2
          have hcont_full : evaluateHOLFiniteState st_slot
              (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                    (.return (.const 0#64))) = (some (.returned rv), scont) := by
            rw [← hk_eta, hrcont_eq]
          rw [evaluateHOLFiniteState_seq_line780] at hcont_full
          have hst_slot_s : st_slot.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
            simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hst_slot_l : st_slot.locals.lookup (ofString "log") = some (.val (.word logw)) := by
            simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_log,
              show ofString "slot" ≠ ofString "log" by decide]
          have harr_bnd : memW s l0 + 8 * memW s (l0 + 16) ≤ 2 ^ 64 := by
            rcases hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨_, h2⟩ | ⟨_, h2⟩
            · have hh := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hh; unfold frameLogs at h2; dsimp only [l0] at *; omega
            · have hs := R11Shards.scratchEnd_val; unfold frameLogs at h2; dsimp only [l0] at *; omega
          have hmem_ent_s : ∀ a, memW ent a = memW s a := fun _ => rfl
          rw [hlw_nat] at hn_lt_cap hslot_nat hmem_slp hm0_slp hm8_slp hm16_slp harr_wok hl0_wok hl0_cap hl0_len hl_disj_arr
          simp only [hmem_ent_s] at hn_lt_cap hslot_nat hm0_slp hm8_slp hm16_slp hl0_cap hl0_len hl_disj_arr
          have harr_wok_s : WordsOK s (memW s l0, 8 * memW s (l0 + 16)) := harr_wok
          have hl0_wok_s : WordsOK s (l0, 24) := hl0_wok
          have hslot_eq_bv : slotw = BitVec.ofNat 64 (memW s l0 + 8 * memW s (l0 + 8)) := by
            apply BitVec.eq_of_toNat_eq
            rw [hslot_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hslot_dom : st_slot.memaddrs slotw := by
            change slp.memaddrs slotw
            rw [hG_slp.memaddrs, ← hAs.1.memaddrs, hslot_eq_bv]
            obtain ⟨_, hd, _⟩ := harr_wok_s.2.2 (memW s (l0 + 8)) (by dsimp only; omega)
            exact hd
          have hev_d : @evalHOLExact 64 F _ st_slot.toExact (fun a => Classical.propDecidable (st_slot.memaddrs a))
              (.var .local (ofString "slot")) = some (.val (.word slotw)) := by
            simp [evalHOLExact, hst_slot_s]
          have hev_v : @evalHOLExact 64 F _ st_slot.toExact (fun a => Classical.propDecidable (st_slot.memaddrs a))
              (.var .local (ofString "log")) = some (.val (.word logw)) := by
            simp [evalHOLExact, hst_slot_l]
          have hst_eq : evaluateHOLFiniteState st_slot
              (.store (.var .local (ofString "slot")) (.var .local (ofString "log"))) =
              (none, { st_slot with memory := fun a => if a = slotw then .word logw else st_slot.memory a }) := by
            rw [evaluateHOLFiniteState_store, hev_d, hev_v]; dsimp only
            simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hslot_dom]
          let st_after := { st_slot with memory := fun a => if a = slotw then .word logw else st_slot.memory a }
          rw [hst_eq] at hcont_full; dsimp only at hcont_full
          rw [evaluateHOLFiniteState_return] at hcont_full
          dsimp only [evalHOLExact] at hcont_full
          have hsz0 : sizeOfShapeWithContextHOL st_after.structs
              (shapeOfHOLExact (.val (.word (0#64 : BitVec 64)))) ≤ 32 := by
            simp [shapeOfHOLExact]
          rw [if_pos hsz0] at hcont_full
          have hscont_eq : st_after.emptyLocalsHOLFinite = scont := (Prod.mk.inj hcont_full).2
          have hpost_mem_fn : post.memory = st_after.memory := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; rfl
          have hpost_glob : post.globals = s.globals := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hglob_slp
          have hpost_be : post.be = s.be := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hbe_slp
          have hpost_loc : post.locals = s.locals := by rw [hpost_eq]
          have hGp : GuestInv post := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hG_slp.code
            · rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hG_slp.memaddrs
            · rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hG_slp.shMemaddrs
            · rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hG_slp.baseAddr
          set p' := memW s l0
          set cap' := memW s (l0 + 16)
          have hmem_out : ∀ x : BitVec 64,
              x ≠ BitVec.ofNat 64 l0 →
              x ≠ BitVec.ofNat 64 (l0 + 8) →
              x ≠ BitVec.ofNat 64 (l0 + 16) →
              x ≠ BitVec.ofNat 64 (p' + 8 * memW s (l0 + 8)) →
              post.memory x = s.memory x := by
            intro x _ hn8 _ hnslot
            rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]
            rw [if_neg (by rwa [hslot_eq_bv])]
            exact hmem_slp x hn8
          have hdisj_l0_slot : ∀ off : Nat, off < 24 → BitVec.ofNat 64 (l0 + off) ≠ slotw := by
            intro off hoff heq
            have h1 : (BitVec.ofNat 64 (l0 + off)).toNat = l0 + off := Nat.mod_eq_of_lt (by omega)
            have h2 := congrArg BitVec.toNat heq
            rw [h1, hslot_nat] at h2
            rcases hl_disj_arr with hd | hd | hd | hd <;> (dsimp only at hd; omega)
          have hl0_post : memW post l0 = p' := by
            have hne := hdisj_l0_slot 0 (by omega); rw [Nat.add_zero] at hne
            have hm : memW post l0 = memW slp l0 := by
              unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
            exact hm.trans hm0_slp
          have hl8_post : memW post (l0 + 8) = memW s (l0 + 8) + 1 := by
            have hne := hdisj_l0_slot 8 (by omega)
            have hm : memW post (l0 + 8) = memW slp (l0 + 8) := by
              unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
            exact hm.trans hm8_slp
          have hl16_post : memW post (l0 + 16) = cap' := by
            have hne := hdisj_l0_slot 16 (by omega)
            have hm : memW post (l0 + 16) = memW slp (l0 + 16) := by
              unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
            exact hm.trans hm16_slp
          have hslot_post : memW post (p' + 8 * memW s (l0 + 8)) = log := by
            change (match post.memory (BitVec.ofNat 64 (p' + 8 * memW s (l0 + 8))) with | .word w => w.toNat) = log
            rw [← hslot_eq_bv, hpost_mem_fn]
            dsimp only [st_after]; rw [if_pos rfl]; exact hlogw_nat
          obtain ⟨hAp, hIp, hch, hR, hfix, hht, hcells, hfl_head, htail, hfo_head⟩ :=
            evmInvAt_of_head_log_store_fc (p' := p') (cap' := cap') (log := log)
              hAs hInv hGp hpost_glob hpost_be (Or.inl rfl)
              hl0_cap
              (by dsimp only [e0, l0, cap'] at *; omega) hmem_out hl0_post hl8_post hl16_post hslot_post
              (fun i _ => rfl) hlog_wa hlog_ok hlog_pw
              hlog_disj_fo hlog_disj_ht hlog_disj_fix hlog_avoids hlog_disj_msg
          have hhp_le : globN s "heap_ptr" ≤ globN post "heap_ptr" := by simp [globN, hpost_glob]
          have hgk : GlobalsKept ["heap_ptr"] s post := fun k _ => by rw [hpost_glob]
          have hBS_post : FcBranchState s0 post S :=
            fcBranchState_of_log_step_fc hBS hAp hIp hhp_le hch hR hpost_loc
              (by simp [globN, hpost_glob]) hfix hht hcells
              (fun ec hec => by
                rw [evmChain_cons] at hec
                rcases List.mem_cons.1 hec with rfl | htl
                · exact Or.inl hfl_head
                · exact Or.inl (htail ec htl).1)
          have he0_unhit : M08IvlUnhit6a s post (e0, 280) := by
            refine ivlUnhit_of_out_4_6a hb88 harr_bnd hn_lt_cap hmem_out ?_ ?_
            · unfold frameObjects at hpw_head
              exact (List.pairwise_cons.1 hpw_head).1 _ (by simp [l0])
            · unfold frameObjects at hpw_head
              exact (List.pairwise_cons.1 hpw_head).1 _ (by simp [frameLogs, l0, p', cap'])
          have he0_8 : e0 % 8 = 0 := he_wok.1
          have hm16 : memW post (e0 + 16) = memW s (e0 + 16) :=
            InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit he0_unhit
              (by omega) (by have := hAs.2.2.2.2.1; have := (hhead_FW.1 (e0, 280) (by simp)).1.2; rw [R11Shards.scratchEnd_val] at *; dsimp at *; omega)
              ⟨by omega, by omega⟩
          have hm40 : memW post (e0 + 40) = memW s (e0 + 40) := (hcells (e0, c0) hhead_mem).2.2.2.1
          have hm232 : memW post (e0 + 232) = memW s (e0 + 232) :=
            InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit he0_unhit
              (by omega) (by have := hAs.2.2.2.2.1; have := (hhead_FW.1 (e0, 280) (by simp)).1.2; rw [R11Shards.scratchEnd_val] at *; dsimp at *; omega)
              ⟨by omega, by omega⟩
          refine ⟨hBS_post, hpost_loc, hhp_le, hgk, hpost_be, hch, hR, hfix, hht,
            fun ec hec => (hcells ec hec).2.2.2.2.1, hm16, hm40, hm232,
            fun ec hec => (htail ec hec).2, ?_, ?_, ?_⟩
          · intro o ho
            rw [hfo_head] at ho
            exact Or.inl ⟨o, by simpa [frameObjects, frameLogs, l0, p', cap', List.append_assoc] using ho, rfl⟩
          · intro ivls hav
            have hmem_l0_fo : (l0, 24) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
              unfold frameObjects; exact List.mem_append_left _ (by simp [e0, l0])
            have hmem_p_fo : (p', 8 * cap') ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
              unfold frameObjects frameLogs; exact List.mem_append_left _ (by simp [e0, l0, p', cap'])
            exact avoidsTries_congr_6a hAs hInv hAp hpost_glob hpost_be
              hl0_wok_s harr_wok_s hb88 harr_bnd hn_lt_cap hmem_out
              hmem_l0_fo (Or.inl hmem_p_fo) hav
          · intro i _ hd1 hd2
            exact ivlUnhit_of_out_4_6a hb88 harr_bnd hn_lt_cap hmem_out hd1 hd2
        · -- Case 2: grow (`n0 = cap0`), `s -> s_mc -> post`
          have hsh_sw : (shapeEqHOL (shapeOfHOLExact (.val (.word slotw) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word slotw) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hsh_sw] at hrun
          let st_slot := setVarHOLFinite (ofString "slot") (.val (.word slotw)) { slp with locals := ent.locals }
          have hk_eta := Prod.mk.eta (p := evaluateHOLFiniteState st_slot
            (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                  (.return (.const 0#64))))
          set rcont := (evaluateHOLFiniteState st_slot
            (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                  (.return (.const 0#64)))).1
          set scont := (evaluateHOLFiniteState st_slot
            (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                  (.return (.const 0#64)))).2
          change (rcont, { scont with locals := _ }) = (some (.returned rv), cpost) at hrun
          have hrcont_eq : rcont = some (.returned rv) := (Prod.mk.inj hrun).1
          have hcpost_eq : { scont with locals := _ } = cpost := (Prod.mk.inj hrun).2
          have hcont_full : evaluateHOLFiniteState st_slot
              (.seq (.store (.var .local (ofString "slot")) (.var .local (ofString "log")))
                    (.return (.const 0#64))) = (some (.returned rv), scont) := by
            rw [← hk_eta, hrcont_eq]
          rw [evaluateHOLFiniteState_seq_line780] at hcont_full
          have hst_slot_s : st_slot.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
            simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hst_slot_l : st_slot.locals.lookup (ofString "log") = some (.val (.word logw)) := by
            simp [st_slot, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_log,
              show ofString "slot" ≠ ofString "log" by decide]
          rw [hlw_nat] at hn_eq_cap hslot_nat hhp_mc hwok_mc hpref_mc hmem_slp hm0_slp hm8_slp hm16_slp hl0_cap
          have hent_m : ∀ a : Nat, memW ent a = memW s a := fun _ => rfl
          have hent_hp_eq : globN ent "heap_ptr" = globN s "heap_ptr" := rfl
          rw [hent_hp_eq] at hnpw_nat
          rw [hent_m, hent_m] at hn_eq_cap
          rw [hent_m] at hslot_nat hhp_mc hwok_mc hm8_slp hm16_slp hl0_cap
          have hpref_mc_s : ∀ i < memW s (l0 + 8), memW s_mc (npw.toNat + 8 * i) = memW s (memW s l0 + 8 * i) :=
            fun i hi => hpref_mc i hi
          have hhp_s_mc : globN s "heap_ptr" ≤ globN s_mc "heap_ptr" := by
            change globN ent "heap_ptr" ≤ globN s_mc "heap_ptr"; omega
          have hgk_s_mc : GlobalsKept ["heap_ptr"] s s_mc := hgk_mc
          have hnonHeap_mc : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN s_mc nm = globN s nm := by
            intro nm hne
            exact InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
              (hgk_s_mc (ofString nm) (by simp [hne]))
          have hev_mc : globN s_mc "ev" = e0 := hnonHeap_mc "ev" (by decide)
          have hcc_mc : globN s_mc "cur_cont" = c0 := hnonHeap_mc "cur_cont" (by decide)
          have hsc_mc : globN s_mc "scratch_ptr" = globN s "scratch_ptr" := hnonHeap_mc "scratch_ptr" (by decide)
          have haddr_mc : globN s_mc "vm_system_address" = globN s "vm_system_address" :=
            hnonHeap_mc "vm_system_address" (by decide)
          obtain ⟨hInv_mc, hch_mc, hR_mc⟩ := OpHandlersB.evmInvAt_of_fresh_heap_step
            hAs hInv hAR_mc hbe_mc hhp_s_mc hgk_s_mc hout_mc hbyte_mc
          obtain ⟨hfix_mc, hht_mc, hcells_mc, hm16_mc, hm40_mc, hm232_mc⟩ :=
            fresh_heap_bridge_6a hAs hInv hAR_mc hbe_mc hhp_s_mc hgk_s_mc hout_mc hbyte_mc
          have hl0_mc_eq : memW s_mc (e0 + 88) = l0 := by
            have hse_lt : scratchEnd < 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
            have hb1 : e0 + 280 < 2 ^ 64 := by
              have h := (hhead_FW.1 (e0, 280) (by simp)).1.2; dsimp only at h; omega
            have he0_8 : e0 % 8 = 0 := he_wok.1
            have hu : M08IvlUnhit6a s s_mc (e0, 280) := by
              refine ivlUnhit_of_fresh_heap_bytes_fc hbe_mc hhp_s_mc hbyte_mc hb1 ?_
              exact disj_fresh_of_zero_or_allocated_6a hAs.2 hAR_mc.2 hhp_s_mc
                (Or.inr (Or.inr (hhead_FW.1 (e0, 280) (by simp)).1))
            exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu
              (by omega) (by omega) ⟨by omega, by omega⟩
          have hl88_unhit_mc : M08IvlUnhit6a s s_mc (l0, 24) := by
            have hse_lt : scratchEnd < 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
            have hb_l0 : l0 + 24 < 2 ^ 64 := by
              have h := (hhead_FW.1 (l0, 24) (by simp [l0])).1.2; dsimp only at h; omega
            exact ivlUnhit_of_fresh_heap_bytes_fc hbe_mc hhp_s_mc hbyte_mc hb_l0
              (disj_fresh_of_zero_or_allocated_6a hAs.2 hAR_mc.2 hhp_s_mc
                (Or.inr (Or.inr (hhead_FW.1 (l0, 24) (by simp [l0])).1)))
          have hl0_8 : l0 % 8 = 0 := (hhead_FW.1 (l0, 24) (by simp [l0])).2.1
          have hl8_mc : memW s_mc (l0 + 8) = memW s (l0 + 8) :=
            InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hl88_unhit_mc
              (by omega) (by omega) ⟨by omega, by omega⟩
          have hl0_val_mc : memW s_mc l0 = memW s l0 := by
            simpa using InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hl88_unhit_mc
              (a := l0) (by omega) (by omega) ⟨by omega, by omega⟩
          set p' := npw.toNat
          set cap' := 2 * memW s (l0 + 16)
          have hp'_bnd : p' + 8 * cap' ≤ 2 ^ 64 := by
            have hh := hAR_mc.2.2.1; rw [R11Shards.heapLimit_val] at hh
            dsimp only [p', cap']; omega
          have hslot_eq_bv : slotw = BitVec.ofNat 64 (p' + 8 * memW s (l0 + 8)) := by
            apply BitVec.eq_of_toNat_eq
            rw [hslot_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [p', cap'] at hp'_bnd ⊢; omega)]
          have hslot_dom : st_slot.memaddrs slotw := by
            change slp.memaddrs slotw
            rw [hG_slp.memaddrs, ← hAR_mc.1.memaddrs, hslot_eq_bv]
            obtain ⟨_, hd, _⟩ := hwok_mc.2.2 (memW s (l0 + 8)) (by dsimp only; omega)
            exact hd
          have hev_d : @evalHOLExact 64 F _ st_slot.toExact (fun a => Classical.propDecidable (st_slot.memaddrs a))
              (.var .local (ofString "slot")) = some (.val (.word slotw)) := by
            simp [evalHOLExact, hst_slot_s]
          have hev_v : @evalHOLExact 64 F _ st_slot.toExact (fun a => Classical.propDecidable (st_slot.memaddrs a))
              (.var .local (ofString "log")) = some (.val (.word logw)) := by
            simp [evalHOLExact, hst_slot_l]
          have hst_eq : evaluateHOLFiniteState st_slot
              (.store (.var .local (ofString "slot")) (.var .local (ofString "log"))) =
              (none, { st_slot with memory := fun a => if a = slotw then .word logw else st_slot.memory a }) := by
            rw [evaluateHOLFiniteState_store, hev_d, hev_v]; dsimp only
            simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hslot_dom]
          let st_after := { st_slot with memory := fun a => if a = slotw then .word logw else st_slot.memory a }
          rw [hst_eq] at hcont_full; dsimp only at hcont_full
          rw [evaluateHOLFiniteState_return] at hcont_full
          dsimp only [evalHOLExact] at hcont_full
          have hsz0 : sizeOfShapeWithContextHOL st_after.structs
              (shapeOfHOLExact (.val (.word (0#64 : BitVec 64)))) ≤ 32 := by
            simp [shapeOfHOLExact]
          rw [if_pos hsz0] at hcont_full
          have hscont_eq : st_after.emptyLocalsHOLFinite = scont := (Prod.mk.inj hcont_full).2
          have hpost_mem_fn : post.memory = st_after.memory := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; rfl
          have hpost_glob_mc : post.globals = s_mc.globals := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hglob_slp
          have hpost_be_mc : post.be = s_mc.be := by
            rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hbe_slp
          have hpost_be : post.be = s.be := hpost_be_mc.trans hbe_mc
          have hpost_loc : post.locals = s.locals := by rw [hpost_eq]
          have hGp : GuestInv post := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hG_slp.code
            · rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hG_slp.memaddrs
            · rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hG_slp.shMemaddrs
            · rw [hpost_eq, ← hcpost_eq, ← hscont_eq]; exact hG_slp.baseAddr
          have hmem_out_mc : ∀ x : BitVec 64,
              x ≠ BitVec.ofNat 64 (memW s_mc (globN s_mc "ev" + 88)) →
              x ≠ BitVec.ofNat 64 (memW s_mc (globN s_mc "ev" + 88) + 8) →
              x ≠ BitVec.ofNat 64 (memW s_mc (globN s_mc "ev" + 88) + 16) →
              x ≠ BitVec.ofNat 64 (p' + 8 * memW s_mc (memW s_mc (globN s_mc "ev" + 88) + 8)) →
              post.memory x = s_mc.memory x := by
            intro x hn0 hn8 hn16 hnslot
            rw [hev_mc, hl0_mc_eq] at hn0 hn8 hn16 hnslot
            rw [hl8_mc] at hnslot
            rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]
            rw [if_neg (by rwa [hslot_eq_bv])]
            exact hmem_slp x hn0 hn8 hn16
          have hin_fresh_p : Inside (p', 8 * cap') (globN s "heap_ptr") (globN s_mc "heap_ptr") := by
            refine ⟨?_, ?_⟩
            · dsimp only [p']; change globN ent "heap_ptr" ≤ npw.toNat; omega
            · dsimp only [p', cap']
              have : 8 * (2 * memW s (l0 + 16)) = 16 * memW s (l0 + 16) := by omega
              omega
          have hl_disj_p' : Disj (l0, 24) (p', 8 * cap') := by
            have hd := disj_fresh_of_zero_or_allocated_6a hAs.2 hAR_mc.2 hhp_s_mc
              (Or.inr (Or.inr (hhead_FW.1 (l0, 24) (by simp [l0])).1))
            exact InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right
              (by rw [Nat.add_sub_of_le hhp_s_mc]; exact hin_fresh_p) hd
          have hdisj_l0_slot : ∀ off : Nat, off < 24 → BitVec.ofNat 64 (l0 + off) ≠ slotw := by
            intro off hoff heq
            have h1 : (BitVec.ofNat 64 (l0 + off)).toNat = l0 + off := Nat.mod_eq_of_lt (by omega)
            have h2 := congrArg BitVec.toNat heq
            rw [h1, hslot_nat] at h2
            rcases hl_disj_p' with hd | hd | hd | hd <;> (dsimp only [p', cap'] at hd; omega)
          have hl0_post : memW post (memW s_mc (globN s_mc "ev" + 88)) = p' := by
            rw [hev_mc, hl0_mc_eq]
            have hne := hdisj_l0_slot 0 (by omega); rw [Nat.add_zero] at hne
            have hm : memW post l0 = memW slp l0 := by
              unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
            exact hm.trans hm0_slp
          have hl8_post : memW post (memW s_mc (globN s_mc "ev" + 88) + 8) =
              memW s_mc (memW s_mc (globN s_mc "ev" + 88) + 8) + 1 := by
            rw [hev_mc, hl0_mc_eq, hl8_mc]
            have hne := hdisj_l0_slot 8 (by omega)
            have hm : memW post (l0 + 8) = memW slp (l0 + 8) := by
              unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
            exact hm.trans hm8_slp
          have hl16_post : memW post (memW s_mc (globN s_mc "ev" + 88) + 16) = cap' := by
            rw [hev_mc, hl0_mc_eq]
            have hne := hdisj_l0_slot 16 (by omega)
            have hm : memW post (l0 + 16) = memW slp (l0 + 16) := by
              unfold memW; rw [hpost_mem_fn]; dsimp only [st_after, st_slot, setVarHOLFinite]; rw [if_neg hne]
            exact hm.trans hm16_slp
          have hslot_post : memW post (p' + 8 * memW s_mc (memW s_mc (globN s_mc "ev" + 88) + 8)) = log := by
            rw [hev_mc, hl0_mc_eq, hl8_mc]
            change (match post.memory (BitVec.ofNat 64 (p' + 8 * memW s (l0 + 8))) with | .word w => w.toNat) = log
            rw [← hslot_eq_bv, hpost_mem_fn]
            dsimp only [st_after]; rw [if_pos rfl]; exact hlogw_nat
          have hprefix_mc : ∀ i < memW s_mc (memW s_mc (globN s_mc "ev" + 88) + 8),
              memW s_mc (p' + 8 * i) = memW s_mc (memW s_mc (memW s_mc (globN s_mc "ev" + 88)) + 8 * i) := by
            intro i hi
            rw [hev_mc, hl0_mc_eq, hl8_mc] at hi
            rw [hev_mc, hl0_mc_eq, hl0_val_mc]
            have h1 := hpref_mc_s i hi
            have hp_in_s := hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.1
            have hp_bnd_s : memW s l0 + 8 * memW s (l0 + 16) < 2 ^ 64 := by
              rcases hp_in_s with ⟨_, h2⟩ | ⟨_, h2⟩
              · have hh := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hh
                unfold frameLogs at h2; dsimp only [e0, l0] at *; omega
              · have hs := R11Shards.scratchEnd_val
                unfold frameLogs at h2; dsimp only [e0, l0] at *; omega
            have hp_8 : (memW s l0) % 8 = 0 := hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
            have hu_old : M08IvlUnhit6a s s_mc (frameLogs s (e0, c0)) :=
              ivlUnhit_of_fresh_heap_bytes_fc hbe_mc hhp_s_mc hbyte_mc
                (by unfold frameLogs; dsimp only [e0, l0] at *; exact hp_bnd_s)
                (disj_fresh_of_zero_or_allocated_6a hAs.2 hAR_mc.2 hhp_s_mc (Or.inr hp_in_s))
            have h2 := InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_old
              (a := memW s l0 + 8 * i)
              (by omega) (by unfold frameLogs; dsimp only [e0, l0] at *; omega)
              ⟨by unfold frameLogs; dsimp only [e0, l0] at *; omega,
               by unfold frameLogs; dsimp only [e0, l0] at *; omega⟩
            exact h1.trans h2.symm
          obtain ⟨hin_sb_mc, hdj_fo_p, hdj_ht_p, hdj_fix_p, hav_p, hdj_msg_p⟩ :=
            fresh_heap_ivl_props_fc hAs hInv hAR_mc hbe_mc hhp_s_mc hgk_s_mc hout_mc hbyte_mc hin_fresh_p
          obtain ⟨hlog_ok_mc, hlog_own_mc, _⟩ :=
            logEntry_fresh_heap_transport_fc hAs hAR_mc hbe_mc hhp_s_mc haddr_mc hbyte_mc hlog_ok
          have hlog_wa_mc : WordAt s_mc log := wordAt_of_unhit_6a (hAR_mc.1.memaddrs.trans hAs.1.memaddrs.symm) hlog_wa
          have hlog_av_mc : AvoidsTries s_mc S (logOwnedIvls s_mc log) :=
            logOwnedIvls_avoidsTries_fresh_heap_fc hAs hInv hAR_mc hbe_mc hhp_s_mc hgk_s_mc
              hout_mc hbyte_mc hlog_ok hlog_avoids
          have hdj_p_log : ∀ o ∈ logOwnedIvls s_mc log, Disj (p', 8 * cap') o := by
            intro o ho
            rw [hlog_own_mc] at ho
            have hal : o.2 = 0 ∨ Allocated s o :=
              (logOwnedIvls_zero_or_heap_fc hlog_ok o ho).imp id Or.inl
            exact disj_symm_6a (InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right
              (by rw [Nat.add_sub_of_le hhp_s_mc]; exact hin_fresh_p)
              (disj_fresh_of_zero_or_allocated_6a hAs.2 hAR_mc.2 hhp_s_mc hal))
          have hwok_p_mc : WordsOK s_mc (p', 8 * cap') := by
            have h16 : 8 * cap' = 16 * memW s (l0 + 16) := by dsimp [cap']; omega
            rwa [h16]
          obtain ⟨hAp, hIp, hch_p, hR_p, hfix_p, hht_p, hcells_p, hfl_head_p, htail_p, hfo_head_p⟩ :=
            evmInvAt_of_head_log_store_fc (s := s_mc) (post := post) (S := S)
              (p' := p') (cap' := cap') (log := log)
              hAR_mc hInv_mc hGp hpost_glob_mc hpost_be_mc
              (Or.inr ⟨hin_sb_mc, hwok_p_mc, hdj_fo_p, hdj_ht_p, hdj_fix_p, hav_p, hdj_msg_p, hdj_p_log⟩)
              (by dsimp [cap']; omega)
              (by rw [hev_mc, hl0_mc_eq, hl8_mc]; dsimp [cap']; omega)
              hmem_out_mc hl0_post hl8_post hl16_post hslot_post hprefix_mc
              hlog_wa_mc hlog_ok_mc (by rwa [hlog_own_mc])
              (fun ec hec o1 ho1 o2 ho2 => by
                rw [hch_mc] at hec; rw [hlog_own_mc] at ho1; rw [(hcells_mc ec hec).1] at ho2
                exact hlog_disj_fo ec hec o1 ho1 o2 ho2)
              (fun o ho t ht j hj => by
                rw [hlog_own_mc] at ho; rw [hht_mc t ht] at hj
                exact hlog_disj_ht o ho t ht j hj)
              (fun o ho j hj => by
                rw [hlog_own_mc] at ho; rw [hfix_mc] at hj
                exact hlog_disj_fix o ho j hj)
              hlog_av_mc
              (fun o ho ec hec => by
                rw [hlog_own_mc] at ho; rw [hch_mc] at hec; rw [(hcells_mc ec hec).2.2.2.2.2.2.1]
                exact hlog_disj_msg o ho ec hec)
          have hhp_le : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
            have : globN post "heap_ptr" = globN s_mc "heap_ptr" := by simp [globN, hpost_glob_mc]
            omega
          have hgk : GlobalsKept ["heap_ptr"] s post := by
            intro k hk; rw [hpost_glob_mc]; exact hgk_s_mc k hk
          have hch : evmChain post = evmChain s := hch_p.trans hch_mc
          have hR : OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := hR_p.trans hR_mc
          have hfix : fixedObjects post = fixedObjects s := hfix_p.trans hfix_mc
          have hht : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
            fun t ht => (hht_p t ht).trans (hht_mc t ht)
          have hBS_post : FcBranchState s0 post S := by
            refine fcBranchState_of_log_step_fc hBS hAp hIp hhp_le hch hR hpost_loc
              (by rw [show globN post "ev" = globN s_mc "ev" by simp [globN, hpost_glob_mc], hev_mc])
              hfix hht
              (fun ec hec => by
                obtain ⟨hfs_p, h24_p, h32_p, h40_p, h112_p, h56_p⟩ := hcells_p ec (by rwa [hch_mc])
                obtain ⟨_, hfs_m, _, h24_m, h32_m, h40_m, h112_m, h56_m⟩ := hcells_mc ec hec
                exact ⟨hfs_p.trans hfs_m, h24_p.trans h24_m, h32_p.trans h32_m,
                  h40_p.trans h40_m, h112_p.trans h112_m, h56_p.trans h56_m⟩) ?_
            intro ec hec
            rw [evmChain_cons] at hec
            rcases List.mem_cons.1 hec with rfl | htl
            · refine Or.inr ?_
              have hfl_eq_p : frameLogs post (globN s "ev", globN s "cur_cont") = (p', 8 * cap') := by
                have h := hfl_head_p; rwa [hev_mc, hcc_mc] at h
              rw [hfl_eq_p]
              have hhp_pm : globN post "heap_ptr" = globN s_mc "heap_ptr" := by simp [globN, hpost_glob_mc]
              rw [hhp_pm]
              exact hin_sb_mc
            · exact Or.inl ((htail_p ec (by rwa [hch_mc])).1.trans
                (hcells_mc ec (List.mem_of_mem_tail htl)).2.2.1)
          have hn_mc_lt : memW s_mc (memW s_mc (globN s_mc "ev" + 88) + 8) < cap' := by
            rw [hev_mc, hl0_mc_eq, hl8_mc]; dsimp [cap']; omega
          have hb88_mc : memW s_mc (globN s_mc "ev" + 88) + 24 ≤ 2 ^ 64 := by
            rw [hev_mc, hl0_mc_eq]; exact hb88
          have he0_unhit_mc : M08IvlUnhit6a s_mc post (e0, 280) := by
            refine ivlUnhit_of_out_4_6a hb88_mc hp'_bnd hn_mc_lt hmem_out_mc ?_ ?_
            · rw [hev_mc, hl0_mc_eq]
              unfold frameObjects at hpw_head
              exact (List.pairwise_cons.1 hpw_head).1 _ (by simp [l0])
            · exact disj_symm_6a (hdj_fo_p (e0, c0) (by rw [hch_mc]; exact hhead_mem)
                (e0, 280) (by rw [(hcells_mc (e0, c0) hhead_mem).1]; simp [frameObjects]))
          have he0_8 : e0 % 8 = 0 := he_wok.1
          have hm16_p : memW post (e0 + 16) = memW s (e0 + 16) := by
            refine (InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit he0_unhit_mc
              (by omega) (by have := (hhead_FW.1 (e0, 280) (by simp)).1.2; rw [R11Shards.scratchEnd_val] at *; dsimp at *; omega)
              ⟨by omega, by omega⟩).trans hm16_mc
          have hm40_p : memW post (e0 + 40) = memW s (e0 + 40) := by
            have h1 := (hcells_p (e0, c0) (by rw [hch_mc]; exact hhead_mem)).2.2.2.1
            exact h1.trans hm40_mc
          have hm232_p : memW post (e0 + 232) = memW s (e0 + 232) := by
            refine (InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit he0_unhit_mc
              (by omega) (by have := (hhead_FW.1 (e0, 280) (by simp)).1.2; rw [R11Shards.scratchEnd_val] at *; dsimp at *; omega)
              ⟨by omega, by omega⟩).trans hm232_mc
          refine ⟨hBS_post, hpost_loc, hhp_le, hgk, hpost_be, hch, hR, hfix, hht,
            fun ec hec => (hcells_p ec (by rwa [hch_mc])).2.2.2.2.1.trans (hcells_mc ec hec).2.2.2.2.2.2.1,
            hm16_p, hm40_p, hm232_p,
            fun ec hec => (htail_p ec (by rwa [hch_mc])).2.trans
              (hcells_mc ec (List.mem_of_mem_tail hec)).1,
            ?_, ?_, ?_⟩
          · intro o ho
            have hfo_h := hfo_head_p
            rw [hev_mc, hcc_mc, hl0_mc_eq] at hfo_h
            rw [hfo_h] at ho
            rcases List.mem_append.1 ho with ho_left | ho_log
            · rcases List.mem_append.1 ho_left with ho7 | ho_flo
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
                rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
                · exact Or.inl ⟨(e0, 280), List.mem_append_left _ (by rw [← (hcells_mc (e0, c0) hhead_mem).1]; unfold frameObjects; exact List.mem_append_left _ (by simp)), rfl⟩
                · exact Or.inl ⟨(c0, 104), List.mem_append_left _ (by rw [← (hcells_mc (e0, c0) hhead_mem).1]; unfold frameObjects; exact List.mem_append_left _ (by simp)), rfl⟩
                · exact Or.inl ⟨_, List.mem_append_left _ (by rw [← (hcells_mc (e0, c0) hhead_mem).1]; unfold frameObjects; exact List.mem_append_left _ (by simp)), rfl⟩
                · exact Or.inl ⟨_, List.mem_append_left _ (by rw [← (hcells_mc (e0, c0) hhead_mem).1]; unfold frameObjects; exact List.mem_append_left _ (by simp)), rfl⟩
                · exact Or.inl ⟨(l0, 24), List.mem_append_left _ (by unfold frameObjects; exact List.mem_append_left _ (by simp [l0])), rfl⟩
                · refine Or.inr ⟨hin_fresh_p.1, ?_⟩
                  have : globN post "heap_ptr" = globN s_mc "heap_ptr" := by simp [globN, hpost_glob_mc]
                  rw [this]; exact hin_fresh_p.2
                · exact Or.inl ⟨frameRet s_mc (e0, c0), List.mem_append_left _ (by rw [← (hcells_mc (e0, c0) hhead_mem).1]; unfold frameObjects; exact List.mem_append_left _ (by simp)), rfl⟩
              · exact Or.inl ⟨o, List.mem_append_left _ (by
                  rw [← (hcells_mc (e0, c0) hhead_mem).1]; unfold frameObjects
                  exact List.mem_append_right _ ho_flo), rfl⟩
            · rw [hlog_own_mc] at ho_log
              exact Or.inl ⟨o, List.mem_append_right _ ho_log, rfl⟩
          · intro ivls hav
            have hav_mc : AvoidsTries s_mc S ivls :=
              avoidsTries_fresh_heap_transport_fc hAs hInv hAR_mc hbe_mc hhp_s_mc hgk_s_mc
                hout_mc hbyte_mc hav
            have hmem_l0_mc : (memW s_mc (globN s_mc "ev" + 88), 24) ∈
                frameObjects s_mc (globN s_mc "ev", globN s_mc "cur_cont") := by
              unfold frameObjects; exact List.mem_append_left _ (by simp)
            exact avoidsTries_congr_6a hAR_mc hInv_mc hAp hpost_glob_mc hpost_be_mc
              (by rw [hev_mc, hl0_mc_eq]; exact wordsOK_of_unhit_6a (hAR_mc.1.memaddrs.trans hAs.1.memaddrs.symm) (by rw [hlw_nat] at hl0_wok; exact hl0_wok))
              hwok_p_mc hb88_mc hp'_bnd hn_mc_lt hmem_out_mc
              hmem_l0_mc
              (Or.inr ⟨hdj_ht_p, hdj_fix_p, hav_p⟩) hav_mc
          · intro i hi_al hd1 _
            have hhp_post_mc : globN post "heap_ptr" = globN s_mc "heap_ptr" := by
              simp [globN, hpost_glob_mc]
            have hi_dj_fresh : Disj i (globN s "heap_ptr", globN s_mc "heap_ptr" - globN s "heap_ptr") :=
              disj_fresh_of_zero_or_allocated_6a hAs.2 hAR_mc.2 hhp_s_mc hi_al
            have hi_dj_p' : Disj i (p', 8 * cap') :=
              InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right
                (by rw [Nat.add_sub_of_le hhp_s_mc]; exact hin_fresh_p) hi_dj_fresh
            have hu2 : M08IvlUnhit6a s_mc post i :=
              ivlUnhit_of_out_4_6a hb88_mc hp'_bnd hn_mc_lt hmem_out_mc
                (by rwa [hev_mc, hl0_mc_eq]) hi_dj_p'
            intro a ha8 ha1 ha2
            have ha_lt : a.toNat + 8 < 2 ^ 64 := by
              rcases hi_al with hz | ⟨_, h2⟩ | ⟨_, h2⟩
              · omega
              · have hh := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hh; omega
              · have hs := R11Shards.scratchEnd_val; omega
            have hu1 : M08IvlUnhit6a s s_mc (a.toNat, 8) :=
              ivlUnhit_of_fresh_heap_bytes_fc hbe_mc hhp_s_mc hbyte_mc ha_lt
                (InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left ⟨ha1, ha2⟩ hi_dj_fresh)
            exact (hu2 a ha8 ha1 ha2).trans (hu1 a ha8 (Nat.le_refl _) (Nat.le_refl _))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
