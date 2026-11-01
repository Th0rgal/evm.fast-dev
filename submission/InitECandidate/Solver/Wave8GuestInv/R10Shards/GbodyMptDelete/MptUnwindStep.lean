import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptUnwindSemantics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.Unwind
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def lvar (n : String) : ExpHOL 64 := .var .local (ofString n)
def frameLoad (off : BitVec 64) : ExpHOL 64 :=
  .load .one (.op .add [lvar "top", .const off])
def extCall : ProgHOL 64 :=
  .call (some (some (.local, ofString "res"), none)) (ofString "_delete_ext_finish")
    [lvar "fnode", frameLoad 24, frameLoad 32, lvar "res"]
def collapseCall : ProgHOL 64 :=
  .call (some (some (.local, ofString "res"), none)) (ofString "_collapse_branch") [lvar "fnode"]
def childAddress : ExpHOL 64 :=
  .op .add [lvar "fnode", .const 32, .panop .mul [frameLoad 32, .const 8]]
def childStore : ProgHOL 64 := .store childAddress (lvar "res")
def finish : ProgHOL 64 :=
  .ite (.cmp .equal (frameLoad 16) (.const 2)) extCall (.seq childStore collapseCall)
def pop : ProgHOL 64 := .assign .local (ofString "top") (frameLoad 0)

theorem body_eq : mptUnwindBody =
    .dec (ofString "fnode") .one (frameLoad 8) (.seq finish pop) := rfl

theorem lookup_ext : originalRuntimeCode.lookup (ofString "_delete_ext_finish") =
    some ([(ofString "node", .one), (ofString "seg", .one), (ofString "sl", .one),
      (ofString "nc", .one)],
      (sourceFunctionEntry Guest.Software.guestFn__delete_ext_finish).2.2.1, .one) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 277 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__delete_ext_finish) rfl

theorem lookup_collapse : originalRuntimeCode.lookup (ofString "_collapse_branch") =
    some ([(ofString "node", .one)],
      (sourceFunctionEntry Guest.Software.guestFn__collapse_branch).2.2.1, .one) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 276 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__collapse_branch) rfl

theorem body_bound (h : MptDeleteCallees) :
    TerminatingProgBoundedOn GuestInv mptUnwindBody mptUnwindCost := by
  rw [body_eq]
  apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
  have he : TerminatingProgBoundedOn GuestInv extCall (K._delete_ext_finish + 1) :=
    TerminatingProgBoundedOn.call_guestInv h.fb__delete_ext_finish
    (some (.local, ofString "res")) [lvar "fnode", frameLoad 24, frameLoad 32, lvar "res"]
  have hc : TerminatingProgBoundedOn GuestInv collapseCall (K._collapse_branch + 1) :=
    TerminatingProgBoundedOn.call_guestInv h.fb__collapse_branch
    (some (.local, ofString "res")) [lvar "fnode"]
  have hs : TerminatingProgBoundedOn GuestInv childStore 0 :=
    TerminatingProgBoundedOn.of_clock (fun s =>
      (evaluate_store_control_frame s childAddress (lvar "res")).2.2)
  have hp : TerminatingProgBoundedOn GuestInv pop 0 :=
    TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)
  intro F s hcode hguest
  simpa only [finish, mptUnwindCost, Nat.zero_add, Nat.add_zero] using
    (TerminatingProgBoundedOn.seq_guestInv
      (TerminatingProgBoundedOn.ite_on (cond := .cmp .equal (frameLoad 16) (.const 2))
        he (TerminatingProgBoundedOn.seq_guestInv hs hc)) hp) s hcode hguest

theorem param_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {x y : String} {v : ValueHOL 64}
    (hx : callee.lookup (ofString x) = some v) (hy : evalAt s (lvar y) = some v) :
    locN (callEntryStateHOLFinite s callee) x = locN s y := by
  change s.locals.lookup (ofString y) = some v at hy
  simp only [locN, callEntryStateHOLFinite, hx, hy]

theorem ext_entry {F : Type} {s : PanSemStateFiniteExact 64 F} {ns : List Nat}
    (hc : s.code = originalRuntimeCode) {p : Nat} (htop : locN s "top" = p)
    (hnode : locN s "fnode" = memW s (p + 8))
    (hf : MptFrameOK s ns p) (hk : memW s (p + 16) = 2)
    (hr : RootIn ns (locN s "res")) :
    ∀ values body callee ret,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [lvar "fnode", frameLoad 24, frameLoad 32, lvar "res"] = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "_delete_ext_finish") values =
        some (body, callee, ret) →
      (∀ n ∈ ["node", "nc"], RootIn ns (locN (callEntryStateHOLFinite s callee) n)) ∧
        (NodeKind (callEntryStateHOLFinite s callee) ns "node" 2 ∧
          KeyIn (callEntryStateHOLFinite s callee) ns
            (locN (callEntryStateHOLFinite s callee) "seg")
            (locN (callEntryStateHOLFinite s callee) "sl")) := by
  intro values body callee ret hargs hl
  obtain ⟨vn, vs, rfl, hvn, hargs⟩ := evalList_cons hargs
  obtain ⟨vp, vs, rfl, hvp, hargs⟩ := evalList_cons hargs
  obtain ⟨vl, vs, rfl, hvl, hargs⟩ := evalList_cons hargs
  obtain ⟨vr, vs, rfl, hvr, hargs⟩ := evalList_cons hargs
  have hnil : vs = [] := by simpa [evalListHOLFinite_eq_toExact, evalListHOLExact] using hargs.symm
  subst vs
  have hlookup := lookup_ext
  rw [← hc] at hlookup
  have hn := (lookupCodeHOLFinite_param_at s.code.lookup (ofString "_delete_ext_finish") []
    (ofString "node") .one _ _ _ (by decide) hlookup (vpre := []) (by rfl) hl).2
  have hp := (lookupCodeHOLFinite_param_at s.code.lookup (ofString "_delete_ext_finish")
    [(ofString "node", .one)] (ofString "seg") .one _ _ _ (by decide) hlookup
    (vpre := [vn]) (by rfl) hl).2
  have hlen := (lookupCodeHOLFinite_param_at s.code.lookup (ofString "_delete_ext_finish")
    [(ofString "node", .one), (ofString "seg", .one)] (ofString "sl") .one _ _ _
    (by decide) hlookup (vpre := [vn, vp]) (by rfl) hl).2
  have hnc := (lookupCodeHOLFinite_param_at s.code.lookup (ofString "_delete_ext_finish")
    [(ofString "node", .one), (ofString "seg", .one), (ofString "sl", .one)]
    (ofString "nc") .one [] _ _ (by simp) hlookup (vpre := [vn, vp, vl]) (by rfl) hl).2
  have hnloc := (param_local hn hvn).trans hnode
  have hrLoc := param_local hnc hvr
  obtain ⟨wp, rfl, hwp⟩ := evalAt_loadL s "top" 24 vp hvp
  obtain ⟨wl, rfl, hwl⟩ := evalAt_loadL s "top" 32 vl hvl
  rw [show (24 : BitVec 64).toNat = 24 by decide] at hwp
  rw [show (32 : BitVec 64).toNat = 32 by decide] at hwl
  have hpLoc : locN (callEntryStateHOLFinite s callee) "seg" = memW s (p + 24) := by
    simp only [locN, callEntryStateHOLFinite, hp]
    simpa only [htop] using hwp
  have hlLoc : locN (callEntryStateHOLFinite s callee) "sl" = memW s (p + 32) := by
    simp only [locN, callEntryStateHOLFinite, hlen]
    simpa only [htop] using hwl
  obtain ⟨hm, hh⟩ := hf.2.2
  have hext : memW s (memW s (p + 8)) = 2 ∧ KeyIn s ns (memW s (p + 24)) (memW s (p + 32)) := by
    rcases hh with hh | hh
    · exact hh.2
    · omega
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hnloc]; exact Or.inr hm
    · rw [hrLoc]; exact hr
  · rw [hnloc]; exact hm
  · change memW s (locN (callEntryStateHOLFinite s callee) "node") = 2
    rw [hnloc]; exact hext.1
  · rw [hpLoc, hlLoc]
    exact hext.2

theorem collapse_entry {F : Type} {s : PanSemStateFiniteExact 64 F} {ns : List Nat}
    (hc : s.code = originalRuntimeCode) (hn : NodeKind s ns "fnode" 3) :
    ∀ values body callee ret,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [lvar "fnode"] = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "_collapse_branch") values =
        some (body, callee, ret) →
      (∀ n ∈ ["node"], RootIn ns (locN (callEntryStateHOLFinite s callee) n)) ∧
        NodeKind (callEntryStateHOLFinite s callee) ns "node" 3 := by
  intro values body callee ret hargs hl
  obtain ⟨v, vs, rfl, hv, ht⟩ := evalList_cons hargs
  have hnil : vs = [] := by simpa [evalListHOLFinite_eq_toExact, evalListHOLExact] using ht.symm
  subst vs
  have hlookup := lookup_collapse
  rw [← hc] at hlookup
  have hp := (lookupCodeHOLFinite_param_at s.code.lookup (ofString "_collapse_branch") []
    (ofString "node") .one [] _ _ (by simp) hlookup (vpre := []) (by rfl) hl).2
  have hnloc := param_local hp hv
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    rw [hnloc]
    exact Or.inr hn.1
  · change locN (callEntryStateHOLFinite s callee) "node" ∈ ns ∧
      memW s (locN (callEntryStateHOLFinite s callee) "node") = 3
    rw [hnloc]
    exact hn

theorem frame_load {F : Type} {s : PanSemStateFiniteExact 64 F} {ns : List Nat}
    {p : Nat} {tw : BitVec 64}
    (ht : s.locals.lookup (ofString "top") = some (.val (.word tw)))
    (hp : tw.toNat = p) (hf : MptFrameOK s ns p) (k : Nat) (hk : k < 5) :
    ∃ w : BitVec 64, evalAt s (frameLoad (BitVec.ofNat 64 (8 * k))) = some (.val (.word w)) ∧
      w.toNat = memW s (p + 8 * k) := by
  obtain ⟨w, hd, hm⟩ := hf.2.1.2.2 k (by change k < 40 / 8; omega)
  have hoff : 8 * k < 2 ^ 64 := by omega
  have he : tw + BitVec.ofNat 64 (8 * k) = BitVec.ofNat 64 (p + 8 * k) := by
    rw [BitVec.add_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff, hp]
  refine ⟨w, ?_, ?_⟩
  · simp [evalAt, frameLoad, lvar, evalHOLExact, evalListHOLExact, ht, valueIsWord,
      valueWord, wordOpHOL, wordOp, memLoadHOLExact, he, hd, hm]
  · simp only [memW, hm]

theorem child_address_eval {F : Type} {s : PanSemStateFiniteExact 64 F} {n idx : BitVec 64}
    (hn : s.locals.lookup (ofString "fnode") = some (.val (.word n)))
    (hi : evalAt s (frameLoad 32) = some (.val (.word idx))) :
    evalAt s childAddress = some (.val (.word (n + 32 + idx * 8))) := by
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
    (frameLoad 32) = some (.val (.word idx)) at hi
  simp only [evalAt, childAddress, lvar, evalHOLExact, evalListHOLExact]
  rw [hi]
  simp [hn, panOpHOL, valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_assoc]

theorem child_store_eval {F : Type} {s : PanSemStateFiniteExact 64 F} {n idx w : BitVec 64}
    (hn : s.locals.lookup (ofString "fnode") = some (.val (.word n)))
    (hi : evalAt s (frameLoad 32) = some (.val (.word idx)))
    (hw : s.locals.lookup (ofString "res") = some (.val (.word w)))
    (h : (evaluateHOLFiniteState s childStore).1 = none) :
    (evaluateHOLFiniteState s childStore).2 = storeWord s (n.toNat + 32 + 8 * idx.toNat) w := by
  have ha := child_address_eval hn hi
  have hv : evalAt s (lvar "res") = some (.val (.word w)) := hw
  have he : n + 32 + idx * 8 = BitVec.ofNat 64 (n.toNat + 32 + 8 * idx.toNat) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.ofNat_mul]
    simp only [BitVec.ofNat_toNat]
    rw [BitVec.mul_comm]
    rfl
  rw [childStore, evaluateHOLFiniteState_store] at h ⊢
  dsimp only [evalAt] at ha hv
  rw [ha, hv] at h ⊢
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at h ⊢
  by_cases hd : s.memaddrs (n + 32 + idx * 8)
  · simp only [hd, ↓reduceIte]
    simp only [storeWord, he]
  · simp only [hd, ↓reduceIte] at h
    cases h

def FinishPost {F : Type} (p : Nat) (fs : List Nat) (next : Nat)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady s ∧ ∃ ns, NodeHeap s ns ∧ MptStack s ns p fs ∧ RootIn ns (locN s "res") ∧
    locN s "top" = p ∧ memW s p = next

theorem extension_post {F : Type} {s t : PanSemStateFiniteExact 64 F} {ns nt fs : List Nat}
    {p : Nat} (ha : ArenaReady s) (hn : NodeHeap s ns) (hs : MptStack s ns p fs) (hp : p ≠ 0)
    (hx : Extension s t ns nt) (hnt : NodeHeap t nt) (hr : RootIn nt (locN t "res"))
    (htop : locN t "top" = p) : FinishPost p fs (memW s p) t := by
  obtain ⟨_, _, hf, _⟩ := stack_pop hs hp
  refine ⟨hx.ready, nt, hnt, hx.stack ha hn hs, hr, htop, ?_⟩
  unfold memW
  rw [hx.scratch ha hn p hf.1.1 (by
    have := hf.1.2
    have : scratchEnd < 2 ^ 64 := by decide
    omega)]

theorem finish_select {F : Type} {s : PanSemStateFiniteExact 64 F} {k : BitVec 64}
    (hk : evalAt s (frameLoad 16) = some (.val (.word k))) :
    evaluateHOLFiniteState s finish =
      if k = 2 then evaluateHOLFiniteState s extCall
      else evaluateHOLFiniteState s (.seq childStore collapseCall) := by
  dsimp only [evalAt] at hk
  rw [finish, evaluateHOLFiniteState_ite]
  simp only [evalHOLExact]
  rw [hk]
  by_cases he : k = 2
  · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · simp [he, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem branch_step (h : MptDeleteCallees) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ns fs : List Nat} {p : Nat} {tw nw : BitVec 64}
    (hc : s.code = originalRuntimeCode) (ha : ArenaReady s) (hn : NodeHeap s ns)
    (hs : MptStack s ns p fs) (hp : p ≠ 0)
    (hroot : RootIn ns (locN s "res"))
    (ht : s.locals.lookup (ofString "top") = some (.val (.word tw))) (htp : tw.toNat = p)
    (hnode : s.locals.lookup (ofString "fnode") = some (.val (.word nw)))
    (hnp : nw.toNat = memW s (p + 8))
    (hk : memW s (p + 16) = 3)
    (hflow : (evaluateHOLFiniteState s (.seq childStore collapseCall)).1 = none) :
    FinishPost p fs (memW s p) (evaluateHOLFiniteState s (.seq childStore collapseCall)).2 := by
  obtain ⟨hstore, hseq⟩ := seq_none hflow
  rw [hseq] at hflow ⊢
  let u := (evaluateHOLFiniteState s childStore).2
  change (evaluateHOLFiniteState u collapseCall).1 = none at hflow
  have hmeta := evaluateHOLFiniteState_metadata s childStore
  have huc : u.code = originalRuntimeCode := hmeta.1.trans hc
  have hul : u.locals = s.locals := (evaluate_store_control_frame s childAddress (lvar "res")).2.1
  obtain ⟨vals, body, callee, ret, v, post, _, hl, _, hshape, hvalid, _⟩ := call_none hflow
  have hrs : ret = .one := lookup_return_shape (by rw [huc]; exact lookup_collapse) hl
  rw [hrs] at hshape
  obtain ⟨res, _, hres, _⟩ := valid_word_destination hshape hvalid
  rw [hul] at hres
  obtain ⟨_, _, hf, _⟩ := stack_pop hs hp
  obtain ⟨idx, hidx, hidxN⟩ := frame_load ht htp hf 4 (by decide)
  change evalAt s (frameLoad 32) = some (.val (.word idx)) at hidx
  change idx.toNat = memW s (p + 32) at hidxN
  have he := child_store_eval hnode hidx hres hstore
  have hf3 : memW s (memW s (p + 8)) = 3 ∧ memW s (p + 32) < 16 := by
    rcases hf.2.2.2 with hh | hh
    · omega
    · exact hh.2
  have hr : RootIn ns res.toNat := by
    simpa only [locN, hres] using hroot
  have hsu := store_child ha hn hf.2.2.1 hf3.1 hf3.2 res hr
  rw [← hnp, ← hidxN] at hsu
  rw [← he] at hsu
  obtain ⟨hx, hnu⟩ := hsu
  have huf : NodeKind u ns "fnode" 3 := by
    have hloc : locN u "fnode" = memW s (p + 8) := by
      simp only [locN, hul, hnode, hnp]
    refine ⟨hloc ▸ hf.2.2.1, ?_⟩
    rw [hloc, hx.kinds _ hf.2.2.1]
    exact hf3.1
  obtain ⟨nt, hcall, hnt, hret, htop⟩ :=
    node_call h.nf__collapse_branch huc hx.ready hnu (collapse_entry huc huf) hflow
  have hup : locN u "top" = p := by simp only [locN, hul, ht, htp]
  have hcpost := extension_post hx.ready hnu (hx.stack ha hn hs) hp hcall hnt hret (htop.trans hup)
  have hmem : memW u p = memW s p := by
    unfold memW
    rw [hx.scratch ha hn p hf.1.1 (by
      have := hf.1.2
      have : scratchEnd < 2 ^ 64 := by decide
      omega)]
  rw [hmem] at hcpost
  exact hcpost

theorem finish_step (h : MptDeleteCallees) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ns fs : List Nat} {p : Nat} {tw nw : BitVec 64}
    (hc : s.code = originalRuntimeCode) (ha : ArenaReady s) (hn : NodeHeap s ns)
    (hs : MptStack s ns p fs) (hp : p ≠ 0) (hr : RootIn ns (locN s "res"))
    (ht : s.locals.lookup (ofString "top") = some (.val (.word tw))) (htp : tw.toNat = p)
    (hnode : s.locals.lookup (ofString "fnode") = some (.val (.word nw)))
    (hnp : nw.toNat = memW s (p + 8))
    (hflow : (evaluateHOLFiniteState s finish).1 = none) :
    FinishPost p fs (memW s p) (evaluateHOLFiniteState s finish).2 := by
  obtain ⟨_, _, hf, _⟩ := stack_pop hs hp
  obtain ⟨k, hk, hkn⟩ := frame_load ht htp hf 2 (by decide)
  change evalAt s (frameLoad 16) = some (.val (.word k)) at hk
  change k.toNat = memW s (p + 16) at hkn
  have htop : locN s "top" = p := by simp only [locN, ht, htp]
  have hfn : locN s "fnode" = memW s (p + 8) := by simp only [locN, hnode, hnp]
  by_cases h2 : memW s (p + 16) = 2
  · have hk2 : k = 2 := BitVec.eq_of_toNat_eq (hkn.trans h2)
    have he := finish_select hk
    rw [if_pos hk2] at he
    rw [he] at hflow ⊢
    obtain ⟨nt, hx, hnt, hret, ht'⟩ := node_call h.nf__delete_ext_finish hc ha hn
      (ext_entry hc htop hfn hf h2 hr) hflow
    exact extension_post ha hn hs hp hx hnt hret (ht'.trans htop)
  · have hk2 : k ≠ 2 := by
      intro he
      apply h2
      rw [← hkn, he]
      decide
    have h3 : memW s (p + 16) = 3 := by
      rcases hf.2.2.2 with hh | hh
      · exact (h2 hh.1).elim
      · exact hh.1
    have he := finish_select hk
    rw [if_neg hk2] at he
    rw [he] at hflow ⊢
    exact branch_step h hc ha hn hs hp hr ht htp hnode hnp h3 hflow

theorem local_word_of_ne_zero {F : Type} {s : PanSemStateFiniteExact 64 F} {x : String}
    (hx : locN s x ≠ 0) :
    ∃ w : BitVec 64, s.locals.lookup (ofString x) = some (.val (.word w)) ∧ w.toNat = locN s x := by
  cases hl : s.locals.lookup (ofString x) with
  | none => simp [locN, hl] at hx
  | some v =>
    cases v with
    | val w => cases w with | word w => exact ⟨w, rfl, by simp only [locN, hl]⟩
    | rStruct vs => simp [locN, hl] at hx
    | nStruct n vs => simp [locN, hl] at hx

theorem body_step (h : MptDeleteCallees) {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hs : MptUnwindHead s) (hp : locN s "top" ≠ 0)
    (hflow : MptFlow s mptUnwindBody) :
    MptUnwindHead (evaluateHOLFiniteState s mptUnwindBody).2 ∧
      locN (evaluateHOLFiniteState s mptUnwindBody).2 "top" = memW s (locN s "top") := by
  have hnflow : (evaluateHOLFiniteState s mptUnwindBody).1 = none :=
    hflow.resolve_right (evaluate_noTopContinue _ (by rw [body_eq]; rfl) s)
  rw [body_eq] at hnflow ⊢
  obtain ⟨ha, ns, fs, hn, hstack, hr⟩ := hs
  obtain ⟨tw, htw, htwn⟩ := local_word_of_ne_zero hp
  obtain ⟨v, hv, hd, hout⟩ := dec_none hnflow
  obtain ⟨nw, rfl, hnwn⟩ := evalAt_loadL s "top" 8 v hv
  rw [show (8 : BitVec 64).toNat = 8 by decide] at hnwn
  let u := setVarHOLFinite (ofString "fnode") (.val (.word nw)) s
  have huTop : locN u "top" = locN s "top" := locN_setVar_ne _ _ _ _ (by decide)
  have huRes : locN u "res" = locN s "res" := locN_setVar_ne _ _ _ _ (by decide)
  have huTW : u.locals.lookup (ofString "top") = some (.val (.word tw)) := by
    simp [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, htw,
      show ofString "fnode" ≠ ofString "top" by decide]
  have huNW : u.locals.lookup (ofString "fnode") = some (.val (.word nw)) := by
    simp [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have huS : MptStack u ns (locN s "top") fs := (stack_locals s _ s.clock ns fs _).2 hstack
  obtain ⟨hfinish, hseq⟩ := seq_none hd
  change (evaluateHOLFiniteState u finish).1 = none at hfinish
  have hmid := finish_step h (s := u) hc (localsFree_arenaReady s u.locals s.clock ha)
    ((nodeHeap_locals s u.locals s.clock ns).2 hn) huS hp (by rw [huRes]; exact hr)
    huTW htwn huNW hnwn hfinish
  let t := (evaluateHOLFiniteState u finish).2
  change FinishPost (locN s "top") fs (memW s (locN s "top")) t at hmid
  obtain ⟨hta, nt, htn, hts, htr, htt, hmem⟩ := hmid
  rw [hseq] at hd
  change (evaluateHOLFiniteState t pop).1 = none at hd
  obtain ⟨v, hv, hpop⟩ := assign_none hd
  obtain ⟨next, rfl, hnext⟩ := evalAt_loadL t "top" 0 v hv
  rw [show (0 : BitVec 64).toNat = 0 by decide, Nat.add_zero, htt, hmem] at hnext
  obtain ⟨qs, hfs, _, htail, _⟩ := stack_pop hts hp
  let post := setVarHOLFinite (ofString "top") (.val (.word next)) t
  have hpHead : MptUnwindHead post := by
    refine ⟨localsFree_arenaReady t _ t.clock hta, nt, qs,
      (nodeHeap_locals t _ t.clock nt).2 htn, ?_, ?_⟩
    · rw [locN_setVar_same]
      apply (stack_locals t _ t.clock nt qs _).2
      rw [hnext, ← hmem]
      exact htail
    · rw [locN_setVar_ne _ _ _ _ (by decide)]
      exact htr
  have hpTop : locN post "top" = memW s (locN s "top") := by
    rw [locN_setVar_same, hnext]
  have hout' : (evaluateHOLFiniteState s
      (.dec (ofString "fnode") .one (frameLoad 8) (.seq finish pop))).2 =
      { post with locals := (HolFiniteMapExact.resVarEq post.locals
          (ofString "fnode", s.locals.lookup (ofString "fnode"))) } := by
    rw [hout, hseq]
    exact congrArg (fun z : PanSemStateFiniteExact 64 F =>
      { z with locals := (HolFiniteMapExact.resVarEq z.locals
          (ofString "fnode", s.locals.lookup (ofString "fnode"))) }) hpop
  rw [hout']
  have hlocals (x : String) (hx : x ∈ ["top", "res"]) :
      (HolFiniteMapExact.resVarEq post.locals
        (ofString "fnode", s.locals.lookup (ofString "fnode"))).lookup (ofString x) =
      post.locals.lookup (ofString x) := by
    apply resVarEq_lookup_ne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide
  refine ⟨head_locals post _ post.clock hlocals hpHead, ?_⟩
  exact (locN_congr post _ post.clock "top" (hlocals _ (by simp))).trans hpTop

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.Unwind
