import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Run
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Frame
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Expr

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

def bindArgs (params : List (MlS × ShapeHOL)) (values : List (ValueHOL 64)) :
    MlS → Option (ValueHOL 64) :=
  List.foldl (fun m entry x => if x = entry.1 then some entry.2 else m x)
    (fun _ => none) ((params.map Prod.fst).zip values)

theorem lookup_locals {F : Type} {s : PanSemStateFiniteExact 64 F} {fname : MlS}
    {params : List (MlS × ShapeHOL)} {body body' : ProgHOL 64} {ret ret' : ShapeHOL}
    {values : List (ValueHOL 64)} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    (hc : s.code.lookup fname = some (params, body, ret))
    (hl : lookupCodeHOLFinite s.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup = bindArgs params values := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  unfold lookupCodeHOLExact at hraw
  rw [hc] at hraw
  dsimp only at hraw
  split at hraw
  · exact (congrArg (fun x => x.2.1) (Option.some.inj hraw)).symm
  · cases hraw

theorem lookup_invalidate : originalRuntimeCode.lookup (ofString "node_invalidate") =
    some (sourceFunctionEntry Guest.Software.guestFn_node_invalidate).2 := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_invalidate) rfl

theorem lookup_prefix : originalRuntimeCode.lookup (ofString "common_prefix_length") =
    some (sourceFunctionEntry Guest.Software.guestFn_common_prefix_length).2 := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 251 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_common_prefix_length) rfl

theorem lookup_split : originalRuntimeCode.lookup (ofString "_split_extension") =
    some (sourceFunctionEntry Guest.Software.guestFn__split_extension).2 := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 274 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__split_extension) rfl

theorem lookup_new_ext : originalRuntimeCode.lookup (ofString "node_new_ext") =
    some (sourceFunctionEntry Guest.Software.guestFn_node_new_ext).2 := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 257 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_ext) rfl

/-- The caller-visible invalidation effect includes restored locals and a preserved key. -/
theorem invalidate_call (h : MptInsertCallees) {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s) (hn : NodeHeap s Nd) (hroot : RootIn Nd (locN s "node"))
    (hr : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "node_invalidate") [.var .local (ofString "node")]) =
      (none, t)) :
    ∃ Nd', ArenaReady t ∧ NodeHeap t Nd' ∧ (∀ n ∈ Nd, n ∈ Nd') ∧
      (∀ p len, KeyIn s Nd p len → KeyIn t Nd' p len) ∧
      t = { clearCache s (locN s "node") with clock := t.clock } := by
  obtain ⟨values, body, callee, ret, v, post, hargs, hl, he, ht⟩ := call_none hr
  dsimp only at ht
  subst t
  have hlookup : s.code.lookup (ofString "node_invalidate") =
      some (sourceFunctionEntry Guest.Software.guestFn_node_invalidate).2 := by
    rw [ha.1.code]
    exact lookup_invalidate
  have hlocals := lookup_locals hlookup hl
  have hnd : locN (callEntryStateHOLFinite s callee) "nd" = locN s "node" := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact, evalHOLExact] at hargs
    cases hv : s.locals.lookup (ofString "node") with
    | none => simp [hv] at hargs
    | some x =>
      simp only [hv, Option.some.injEq] at hargs
      subst values
      simp only [locN, callEntryStateHOLFinite, hlocals]
      change (match (if ofString "nd" = ofString "nd" then some x else none) with
        | some (.val (.word w)) => w.toNat | _ => 0) = _
      simp only [ite_true, hv]
      rfl
  have haentry : ArenaReady (callEntryStateHOLFinite s callee) :=
    localsFree_arenaReady s callee (s.clock - 1) ha
  have hroots : ∀ n ∈ ["nd"], RootIn Nd (locN (callEntryStateHOLFinite s callee) n) := by
    intro n hn
    simp only [List.mem_singleton] at hn
    subst n
    rw [hnd]
    exact hroot
  have hpre : NodeArgs ["nd"] (fun _ _ => True) (callEntryStateHOLFinite s callee) :=
    ⟨haentry, Nd, hn, hroots, trivial⟩
  have hsafe : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠ some .timeOut := by
    rw [he]
    simp
  have hnf := FunSpec.at_lookup h.nf_node_invalidate s ha.1.code values body callee ret hl hpre hsafe
  have hiz := FunSpec.at_lookup h.iz_node_invalidate s ha.1.code values body callee ret hl hpre hsafe
  rw [he] at hnf hiz
  have hres : Resumes (some (.returned v)) := Or.inl ⟨v, rfl⟩
  obtain ⟨hapost, hgrow, _, hnodes⟩ := hnf hres
  obtain ⟨Nd', hn', hsub, hkinds, hfresh, hframe, _, _⟩ := hnodes Nd hn hroots trivial
  have hbe : post.be = s.be := by
    have hm := InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite s callee) body
    rw [he] at hm
    exact hm.2.2.1
  refine ⟨Nd', localsFree_arenaReady post s.locals post.clock hapost, hn', hsub, ?_, ?_⟩
  · intro p len hk
    exact keyIn_frame ha hgrow hn hkinds hfresh hframe hbe hk
  · have hz := hiz hres
    change post = { clearCache (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "nd") with locals := post.locals, clock := post.clock } at hz
    rw [hnd] at hz
    have hz' := congrArg (fun z : PanSemStateFiniteExact 64 F => { z with locals := s.locals }) hz
    exact hz'

/-- The common-prefix callee is read-only and its return fits the remaining key. -/
theorem prefix_return (h : MptInsertCallees) {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL}
    {v : ValueHOL 64} (hg : GuestInv s) (hlev : locN s "level" ≤ locN s "klen")
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [lv "seg", lv "sl", .op .add [lv "key", lv "level"], .op .sub [lv "klen", lv "level"]] = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "common_prefix_length") values =
      some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ locN s "sl" ∧
      w.toNat ≤ locN s "klen" - locN s "level" ∧
      post = { s with locals := post.locals, clock := post.clock } := by
  have hlookup : s.code.lookup (ofString "common_prefix_length") =
      some (sourceFunctionEntry Guest.Software.guestFn_common_prefix_length).2 := by
    rw [hg.code]
    exact lookup_prefix
  have hlocals := lookup_locals hlookup hl
  rw [evalListHOLFinite_eq_toExact] at hargs
  obtain ⟨seg, vs1, hseg, hv1, rfl⟩ := args_cons hargs
  obtain ⟨sl, vs2, hsl, hv2, rfl⟩ := args_cons hv1
  obtain ⟨key, vs3, hkey, hv3, rfl⟩ := args_cons hv2
  obtain ⟨len, vs, hlen, hv, rfl⟩ := args_cons hv3
  have hvnil : vs = [] := (Option.some.inj hv).symm
  subst vs
  obtain ⟨kl, level, hkl, hlevel, rfl⟩ := eval_sub_locals s "klen" "level" len hlen
  have hklN : locN s "klen" = kl.toNat := by simp only [locN, hkl]
  have hlN : locN s "level" = level.toNat := by simp only [locN, hlevel]
  have hsub : (kl - level).toNat = locN s "klen" - locN s "level" := by
    rw [hklN, hlN]
    exact BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def, hklN, hlN] using hlev)
  have hal : locN (callEntryStateHOLFinite s callee) "al" = locN s "sl" := by
    change s.locals.lookup (ofString "sl") = some sl at hsl
    simp only [locN, callEntryStateHOLFinite, hlocals, hsl]
    rfl
  have hbl : locN (callEntryStateHOLFinite s callee) "bl" = locN s "klen" - locN s "level" := by
    simp only [locN, callEntryStateHOLFinite, hlocals]
    exact hsub
  have hsafe : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠ some .timeOut := by
    rw [he]
    simp
  have hgentry := guestInv_callEntry s callee hg
  have hr := FunSpec.at_lookup h.rv_common_prefix_length s hg.code _ body callee ret hl hgentry hsafe
  have hro := FunSpec.at_lookup h.ro_common_prefix_length s hg.code _ body callee ret hl hgentry hsafe
  rw [he] at hr hro
  obtain ⟨w, hw, hle⟩ := hr v rfl
  dsimp only at hle
  rw [hal, hbl] at hle
  refine ⟨w, hw, (Nat.le_min.mp hle).1, (Nat.le_min.mp hle).2, ?_⟩
  exact hro (Or.inl ⟨v, rfl⟩)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
