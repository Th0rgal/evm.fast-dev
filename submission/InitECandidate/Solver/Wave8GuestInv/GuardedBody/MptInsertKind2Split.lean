import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2NodeCall
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2Tail

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem keyIn_mod {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {p len : Nat} (hk : KeyIn s Nd p len) : KeyIn s Nd (p % 2 ^ 64) len := by
  rcases hk with hz | hk
  · exact Or.inl hz
  · have hbound := hk.2.2.1.2
    have hlimit : heapLimit < 2 ^ 64 := by decide
    rw [Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega)]
    exact Or.inr hk

/-- Preconditions of `_split_extension` are transported through the actual argument bindings. -/
theorem split_return (h : MptInsertCallees) {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL} {v : ValueHOL 64}
    (ha : ArenaReady s) (hn : NodeHeap s Nd) (hnode : locN s "node" ∈ Nd)
    (htag : memW s (locN s "node") = 2)
    (hlev : locN s "level" ≤ locN s "klen")
    (hkey : KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level"))
    (hpl : locN s "pl" < memW s (locN s "node" + 40))
    (hplkey : locN s "pl" ≤ locN s "klen" - locN s "level")
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [lv "node", .op .add [lv "key", lv "level"], .op .sub [lv "klen", lv "level"],
        lv "vptr", lv "vlen", lv "pl"] = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "_split_extension") values = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ Nd', ArenaReady post ∧ NodeHeap post Nd' ∧ (∀ n ∈ Nd, n ∈ Nd') ∧
      (∀ p len, KeyIn s Nd p len → KeyIn post Nd' p len) ∧
      ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat := by
  have hlookup : s.code.lookup (ofString "_split_extension") =
      some (sourceFunctionEntry Guest.Software.guestFn__split_extension).2 := by
    rw [ha.1.code]
    exact lookup_split
  have hlocals := lookup_locals hlookup hl
  rw [evalListHOLFinite_eq_toExact] at hargs
  obtain ⟨node, vs1, hnd, hv1, rfl⟩ := args_cons hargs
  obtain ⟨rk, vs2, hrk, hv2, rfl⟩ := args_cons hv1
  obtain ⟨rl, vs3, hrl, hv3, rfl⟩ := args_cons hv2
  obtain ⟨vp, vs4, hvp, hv4, rfl⟩ := args_cons hv3
  obtain ⟨vl, vs5, hvl, hv5, rfl⟩ := args_cons hv4
  obtain ⟨pl, vs6, hplv, hv6, rfl⟩ := args_cons hv5
  have hnil : vs6 = [] := (Option.some.inj hv6).symm
  subst vs6
  change s.locals.lookup (ofString "node") = some node at hnd
  change s.locals.lookup (ofString "pl") = some pl at hplv
  obtain ⟨key, lev1, hkeyv, hlev1, rfl⟩ := eval_add_locals s "key" "level" rk hrk
  obtain ⟨klen, lev2, hklenv, hlev2, rfl⟩ := eval_sub_locals s "klen" "level" rl hrl
  have hrkN : (key + lev1).toNat = (locN s "key" + locN s "level") % 2 ^ 64 := by
    simp only [locN, hkeyv, hlev1, BitVec.toNat_add]
  have hrlN : (klen - lev2).toNat = locN s "klen" - locN s "level" := by
    have hle : lev2 ≤ klen := by simpa only [BitVec.le_def, locN, hklenv, hlev2] using hlev
    rw [BitVec.toNat_sub_of_le hle]
    simp only [locN, hklenv, hlev2]
  have hndN : locN (callEntryStateHOLFinite s callee) "node" = locN s "node" := by
    simp only [locN, callEntryStateHOLFinite, hlocals, hnd]
    rfl
  have hplN : locN (callEntryStateHOLFinite s callee) "pl" = locN s "pl" := by
    simp only [locN, callEntryStateHOLFinite, hlocals, hplv]
    rfl
  have hrkC : locN (callEntryStateHOLFinite s callee) "rk" = (locN s "key" + locN s "level") % 2 ^ 64 := by
    simp only [locN, callEntryStateHOLFinite, hlocals]
    exact hrkN
  have hrlC : locN (callEntryStateHOLFinite s callee) "rl" = locN s "klen" - locN s "level" := by
    simp only [locN, callEntryStateHOLFinite, hlocals]
    exact hrlN
  have hroots : ∀ n ∈ ["node"], RootIn Nd (locN (callEntryStateHOLFinite s callee) n) := by
    intro n hn
    simp only [List.mem_singleton] at hn
    subst n
    rw [hndN]
    exact Or.inr hnode
  apply node_return h.nf__split_extension ha hn hroots ?_ hl he
  refine ⟨?_, ?_, ?_, ?_⟩
  · change locN (callEntryStateHOLFinite s callee) "node" ∈ Nd ∧
      memW s (locN (callEntryStateHOLFinite s callee) "node") = 2
    rw [hndN]
    exact ⟨hnode, htag⟩
  · rw [hrkC, hrlC]
    exact keyIn_mod hkey
  · rw [hplN, hndN]
    exact hpl
  · rw [hplN, hrlC]
    exact hplkey

/-- Splitting an extension (and possibly wrapping it) keeps `go` unchanged. -/
theorem splitExt_run (h : MptInsertCallees) {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s) (hn : NodeHeap s Nd) (hnode : locN s "node" ∈ Nd)
    (htag : memW s (locN s "node") = 2)
    (hlev : locN s "level" ≤ locN s "klen")
    (hkey : KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level"))
    (hpl : locN s "pl" < memW s (locN s "node" + 40))
    (hplkey : locN s "pl" ≤ locN s "klen" - locN s "level")
    (hseg : KeyIn s Nd (locN s "seg") (locN s "pl"))
    (hr : evaluateHOLFiniteState s splitExt = (none, t)) :
    ArenaReady t ∧ locN t "go" = locN s "go" := by
  rw [splitExt_eq] at hr
  obtain ⟨values, body, callee, ret, v, post, u, hargs, hl, he, hcont, ht⟩ := decCall_none hr
  obtain ⟨Nd', hapost, hnpost, _, hkeys, w, hv, hwroot⟩ :=
    split_return h ha hn hnode htag hlev hkey hpl hplkey hargs hl he
  subst v
  let b := put { post with locals := s.locals } "br" w
  have hab : ArenaReady b := ⟨guestInv_congr (s := post) rfl rfl rfl rfl hapost.1, hapost.2⟩
  have hnb : NodeHeap b Nd' := hnpost
  have hbseg : locN b "seg" = locN s "seg" :=
    RunFramesRace.locN_setVar_ne { post with locals := s.locals } "seg" (ofString "br") _ (by decide)
  have hbpl : locN b "pl" = locN s "pl" :=
    RunFramesRace.locN_setVar_ne { post with locals := s.locals } "pl" (ofString "br") _ (by decide)
  have hbgo : locN b "go" = locN s "go" :=
    RunFramesRace.locN_setVar_ne { post with locals := s.locals } "go" (ofString "br") _ (by decide)
  have hbroot : RootIn Nd' (locN b "br") := by
    change RootIn Nd' (locN (put { post with locals := s.locals } "br" w) "br")
    rw [put, RunFramesRace.locN_setVar_same]
    exact hwroot
  have hbkey : KeyIn b Nd' (locN b "seg") (locN b "pl") := by
    rw [hbseg, hbpl]
    exact hkeys _ _ hseg
  have hu : ArenaReady u ∧ locN u "go" = locN b "go" := by
    rcases ite_none hcont with ⟨_, hnew⟩ | ⟨_, hassign⟩
    · exact newExt_call h (s := b) hab hnb hbroot hbkey hnew
    · exact assign_arena_go (s := b) hab (by decide) hassign
  rw [ht]
  refine ⟨localsFree_arenaReady u _ u.clock hu.1, ?_⟩
  have hrestore : locN { u with locals := (HolFiniteMapExact.resVarEq u.locals
      (ofString "br", s.locals.lookup (ofString "br"))) } "go" = locN u "go" := by
    simp only [locN]
    rw [resVarEq_lookup_ne _ _ _ _ (by decide)]
  exact hrestore.trans (hu.2.trans hbgo)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
