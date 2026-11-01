import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Calls

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem node_return {names : List String}
    {req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop} {fname : MlS}
    (hf : NodeFn names req fname) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL} {v : ValueHOL 64}
    (ha : ArenaReady s) (hn : NodeHeap s Nd)
    (hroots : ∀ n ∈ names, RootIn Nd (locN (callEntryStateHOLFinite s callee) n))
    (hreq : req (callEntryStateHOLFinite s callee) Nd)
    (hl : lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ Nd', ArenaReady post ∧ NodeHeap post Nd' ∧ (∀ n ∈ Nd, n ∈ Nd') ∧
      (∀ p len, KeyIn s Nd p len → KeyIn post Nd' p len) ∧
      ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat := by
  have hpre : NodeArgs names req (callEntryStateHOLFinite s callee) :=
    ⟨localsFree_arenaReady s callee (s.clock - 1) ha, Nd, hn, hroots, hreq⟩
  have hsafe : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠ some .timeOut := by
    rw [he]
    simp
  have hnf := FunSpec.at_lookup hf s ha.1.code values body callee ret hl hpre hsafe
  rw [he] at hnf
  obtain ⟨hapost, hgrow, _, hnodes⟩ := hnf (Or.inl ⟨v, rfl⟩)
  obtain ⟨Nd', hn', hsub, hkinds, hfresh, hframe, _, hv⟩ := hnodes Nd hn hroots hreq
  have hbe : post.be = s.be := by
    have hm := InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite s callee) body
    rw [he] at hm
    exact hm.2.2.1
  exact ⟨Nd', hapost, hn', hsub,
    fun _ _ hk => keyIn_frame ha hgrow hn hkinds hfresh hframe hbe hk, hv v rfl⟩

/-- The wrapping extension allocation preserves the stopped loop control. -/
theorem newExt_call (h : MptInsertCallees) {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s) (hn : NodeHeap s Nd) (hchild : RootIn Nd (locN s "br"))
    (hkey : KeyIn s Nd (locN s "seg") (locN s "pl"))
    (hr : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "r"), none)) (ofString "node_new_ext")
        [lv "seg", lv "pl", lv "br"]) = (none, t)) :
    ArenaReady t ∧ locN t "go" = locN s "go" := by
  obtain ⟨values, body, callee, ret, v, post, hargs, hl, he, ht⟩ := call_none hr
  dsimp only at ht
  subst t
  have hlookup : s.code.lookup (ofString "node_new_ext") =
      some (InitECandidate.Solver.GuestCodeLookup.sourceFunctionEntry Guest.Software.guestFn_node_new_ext).2 := by
    rw [ha.1.code]
    exact lookup_new_ext
  have hlocals := lookup_locals hlookup hl
  rw [evalListHOLFinite_eq_toExact] at hargs
  obtain ⟨seg, vs1, hseg, hv1, rfl⟩ := args_cons hargs
  obtain ⟨pl, vs2, hpl, hv2, rfl⟩ := args_cons hv1
  obtain ⟨br, vs3, hbr, hv3, rfl⟩ := args_cons hv2
  have hnil : vs3 = [] := (Option.some.inj hv3).symm
  subst vs3
  change s.locals.lookup (ofString "seg") = some seg at hseg
  change s.locals.lookup (ofString "pl") = some pl at hpl
  change s.locals.lookup (ofString "br") = some br at hbr
  have hnib : locN (callEntryStateHOLFinite s callee) "nib" = locN s "seg" := by
    simp only [locN, callEntryStateHOLFinite, hlocals, hseg]
    rfl
  have hnlen : locN (callEntryStateHOLFinite s callee) "nlen" = locN s "pl" := by
    simp only [locN, callEntryStateHOLFinite, hlocals, hpl]
    rfl
  have hch : locN (callEntryStateHOLFinite s callee) "child" = locN s "br" := by
    simp only [locN, callEntryStateHOLFinite, hlocals, hbr]
    rfl
  have hroots : ∀ n ∈ ["child"], RootIn Nd (locN (callEntryStateHOLFinite s callee) n) := by
    intro n hn
    simp only [List.mem_singleton] at hn
    subst n
    rw [hch]
    exact hchild
  have hreq : KeyIn (callEntryStateHOLFinite s callee) Nd
      (locN (callEntryStateHOLFinite s callee) "nib") (locN (callEntryStateHOLFinite s callee) "nlen") := by
    rw [hnib, hnlen]
    exact hkey
  obtain ⟨_, hapost, _, _, _, _⟩ := node_return h.nf_node_new_ext ha hn hroots hreq hl he
  exact ⟨⟨guestInv_congr (s := post) rfl rfl rfl rfl hapost.1, hapost.2⟩,
    RunFramesRace.locN_setVar_ne { post with locals := s.locals } "go" (ofString "r") v (by decide)⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
