import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind3Scope

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

def mptInsertMain := mptDecBody (mptDecBody (mptDecBody (mptDecBody mptInsertBody)))
def mptInsertDispatch := mptLeft (mptRight mptInsertMain)
def mptInsertNull : ProgHOL 64 := match mptInsertDispatch with | .ite _ a _ => a | _ => .skip
def mptInsertTagged : ProgHOL 64 := match mptInsertDispatch with | .ite _ _ b => b | _ => .skip
def mptInsertTaggedBody := mptDecBody mptInsertTagged
def mptInsertBadTag := mptLeft mptInsertTaggedBody
def mptInsertKindDispatch := mptRight (mptRight mptInsertTaggedBody)
def mptInsertLeaf : ProgHOL 64 := match mptInsertKindDispatch with | .ite _ a _ => a | _ => .skip
def mptInsertExt : ProgHOL 64 := match mptInsertKindDispatch with
  | .ite _ _ (.ite _ a _) => a | _ => .skip

theorem mptInsert_body_parts : mptInsertBody =
    .dec (ofString "r") .one (.const 0)
      (.dec (ofString "next_node") .one (.const 0)
        (.dec (ofString "next_slot") .one (.const 0)
          (.dec (ofString "next_level") .one (.const 0)
            (.seq (.assign .local (ofString "go") (.const 0))
              (.seq mptInsertDispatch mptInsertFinish))))) := rfl

theorem mptInsert_dispatch_parts : mptInsertDispatch =
    .ite (.cmp .equal (.var .local (ofString "node")) (.const 0)) mptInsertNull mptInsertTagged := rfl

theorem mptInsert_tagged_parts : mptInsertTagged =
    .dec (ofString "k") .one (.load .one (.op .add [.var .local (ofString "node"), .const 0]))
      (.seq mptInsertBadTag (.seq
        (.call (some (none, none)) (ofString "node_invalidate") [.var .local (ofString "node")])
        mptInsertKindDispatch)) := rfl

theorem mptInsert_bad_parts : mptInsertBadTag =
    .ite (.cmp .equal (.var .local (ofString "k")) (.const 0))
      (.call (some (none, none)) (ofString "mpt_fail") [.const 2]) .skip := rfl

theorem mptInsert_kind_parts : mptInsertKindDispatch =
    .ite (.cmp .equal (.var .local (ofString "k")) (.const 1)) mptInsertLeaf
      (.ite (.cmp .equal (.var .local (ofString "k")) (.const 2)) mptInsertExt mptInsertBranch) := rfl

theorem mpt_kind3_dispatch_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hk : s.locals.lookup (ofString "k") = some (.val (.word 3))) :
    evaluateHOLFiniteState s mptInsertKindDispatch = evaluateHOLFiniteState s mptInsertBranch := by
  rw [mptInsert_kind_parts, mpt_ite_eq_local s "k" 3 1 _ _ hk,
    if_neg (by decide), mpt_ite_eq_local s "k" 3 2 _ _ hk, if_neg (by decide)]

theorem mpt_tagged_none {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (n : BitVec 64) (hc : s.code = originalRuntimeCode)
    (hn : NodeHeap s Nd) (hm : n.toNat ∈ Nd) (hk : memW s n.toNat = 3)
    (hnode : s.locals.lookup (ofString "node") = some (.val (.word n)))
    (h : evaluateHOLFiniteState s mptInsertTagged = (none, t)) :
    ∃ u, evaluateHOLFiniteState
      {clearCache (setVarHOLFinite (ofString "k") (.val (.word 3)) s) n.toNat with clock := s.clock - 1}
      mptInsertBranch = (none, u) ∧ t = mptRestore u (ofString "k") (s.locals.lookup (ofString "k")) := by
  classical
  have hd0 := mpt_node_field_domain s Nd hn n.toNat hm 0 (by decide)
    (lt_of_lt_of_le (by decide : 0 < 32) (mpt_nodeSize_bounds (memW s n.toNat)).1)
  have hmem := mpt_memW_word s n.toNat (3#64) hk
  simp only [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hd0 hmem
  have htag : evalAt s (.load .one (.op .add [.var .local (ofString "node"), .const 0])) =
      some (.val (.word 3)) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hnode, valueIsWord, valueWord,
      wordOpHOL, wordOp, memLoadHOLExact, hd0, hmem]
  rw [mptInsert_tagged_parts] at h
  obtain ⟨value, u, hv, _, hu, ht⟩ := mpt_dec_none_inv h
  rw [htag] at hv
  have hv' := Option.some.inj hv
  subst value
  let q := setVarHOLFinite (ofString "k") (.val (.word (3#64))) s
  have hqK : q.locals.lookup (ofString "k") = some (.val (.word 3)) := by
    simp [q, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hqN : q.locals.lookup (ofString "node") = some (.val (.word n)) := by
    simpa [q, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ofString] using hnode
  change evaluateHOLFiniteState q _ = (none, u) at hu
  obtain ⟨u0, hbad, hrest⟩ := mpt_seq_none_inv hu
  rw [mptInsert_bad_parts, mpt_ite_eq_local _ "k" 3 0 _ _ hqK, if_neg (by decide),
    evaluateHOLFiniteState_skip] at hbad
  have hu0 := (Prod.mk.inj hbad).2.symm
  subst u0
  obtain ⟨u1, hcall, hdispatch⟩ := mpt_seq_none_inv hrest
  have hdom (off : BitVec 64) (ho : off = 8#64 ∨ off = 16#64 ∨ off = 24#64) :
      q.memaddrs (n + off) := by
    have hsz : off.toNat < nodeSize (memW s n.toNat) := by
      exact lt_of_lt_of_le (by rcases ho with rfl | rfl | rfl <;> decide)
        (mpt_nodeSize_bounds (memW s n.toNat)).1
    have hal : off.toNat % 8 = 0 := by rcases ho with rfl | rfl | rfl <;> decide
    have hx := mpt_node_field_domain s Nd hn n.toNat hm off.toNat hal hsz
    have he : BitVec.ofNat 64 (n.toNat + off.toNat) = n + off := by rw [BitVec.add_def]
    change s.memaddrs (n + off)
    simpa only [he] using hx
  rw [mptInvalidate_call_eval q n hc hqN (hdom 8 (Or.inl rfl))
    (hdom 16 (Or.inr (Or.inl rfl))) (hdom 24 (Or.inr (Or.inr rfl)))] at hcall
  split at hcall
  · cases hcall
  · have hu1 := (Prod.mk.inj hcall).2.symm
    subst u1
    rw [mpt_kind3_dispatch_eval {clearCache q n.toNat with clock := q.clock - 1} hqK] at hdispatch
    exact ⟨u, hdispatch, ht⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
