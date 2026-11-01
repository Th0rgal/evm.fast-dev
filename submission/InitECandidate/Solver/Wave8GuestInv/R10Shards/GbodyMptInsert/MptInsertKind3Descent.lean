import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind3Finish

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.PanRunBounded

def mptChildAddr (n i : BitVec 64) : BitVec 64 := n + (32#64 + i * 8#64)

theorem mpt_child_addr {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (hn : NodeHeap s Nd) (n i : BitVec 64) (hm : n.toNat ∈ Nd)
    (hk : memW s n.toNat = 3) (hi : i.toNat < 16) :
    (mptChildAddr n i).toNat = n.toNat + 32 + 8 * i.toNat := by
  have hb := (hn.1 n.toNat hm).2.2.1
  change sourceBase ≤ n.toNat ∧ n.toNat + nodeSize (memW s n.toNat) ≤ heapLimit at hb
  simp [hk, nodeSize] at hb
  have hlim : heapLimit < 2^64 := by decide
  have hmul : (i * 8#64).toNat = i.toNat * 8 := by
    rw [BitVec.toNat_mul]; norm_num; omega
  simp only [mptChildAddr, BitVec.toNat_add, hmul]
  norm_num
  omega

theorem mpt_descent_none {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (n l i : BitVec 64)
    (hn : NodeHeap s Nd) (hm : n.toNat ∈ Nd) (hk : memW s n.toNat = 3)
    (hi : i.toNat < 16)
    (hnode : s.locals.lookup (ofString "node") = some (.val (.word n)))
    (hlevel : s.locals.lookup (ofString "level") = some (.val (.word l)))
    (hidx : s.locals.lookup (ofString "idx") = some (.val (.word i)))
    (h : evaluateHOLFiniteState s mptInsertDescent = (none, t)) :
    ∃ nn : BitVec 64,
      nn.toNat = memW s (n.toNat + 32 + 8 * i.toNat) ∧
      t = setVarHOLFinite (ofString "go") (.val (.word 1))
        (setVarHOLFinite (ofString "next_level") (.val (.word (l + 1#64)))
          (setVarHOLFinite (ofString "next_slot") (.val (.word (mptChildAddr n i)))
            (setVarHOLFinite (ofString "next_node") (.val (.word nn))
              (setVarHOLFinite (ofString "r") (.val (.word n)) s)))) := by
  classical
  simp [ofString] at hnode hlevel hidx
  have ha := mpt_child_addr s Nd hn n i hm hk hi
  have hda : s.memaddrs (mptChildAddr n i) := by
    have := mpt_node_field_domain s Nd hn n.toNat hm (32 + 8 * i.toNat)
      (by omega) (by simp [hk, nodeSize]; omega)
    rw [← Nat.add_assoc, ← ha] at this
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using this
  cases hmem : s.memory (mptChildAddr n i) with
  | word nn =>
    simp only [mptChildAddr] at hda hmem
    refine ⟨nn, ?_, ?_⟩
    · simp only [← ha, memW, BitVec.ofNat_toNat, BitVec.setWidth_eq, mptChildAddr, hmem]
    obtain ⟨s1, h1, hrest⟩ := mpt_seq_none_inv h
    have he1 : evalAt s (.var .local (ofString "node")) = some (.val (.word n)) := hnode
    have hs1 := mpt_assign_none_word s s1 "r" _ n he1 h1
    subst s1
    obtain ⟨s2, h2, hrest⟩ := mpt_seq_none_inv hrest
    have he2 : evalAt (setVarHOLFinite (ofString "r") (.val (.word n)) s)
        (.load .one (.op .add [.var .local (ofString "node"), .const 32,
          .panop .mul [.var .local (ofString "idx"), .const 8]])) = some (.val (.word nn)) := by
      simpa [evalAt, evalHOLExact, evalListHOLExact, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, ofString, valueIsWord, valueWord,
        wordOpHOL, wordOp, panOpHOL, memLoadHOLExact, mptChildAddr,
        hnode, hidx, hmem, hda]
    -- The local lookups above are independent of the newly assigned temporary.
    have hs2 := mpt_assign_none_word _ s2 "next_node" _ nn he2 h2
    subst s2
    obtain ⟨s3, h3, hrest⟩ := mpt_seq_none_inv hrest
    have hs3 := mpt_assign_none_word _ s3 "next_slot"
      (.op .add [.var .local (ofString "node"), .const 32,
        .panop .mul [.var .local (ofString "idx"), .const 8]]) (mptChildAddr n i)
      (by simp [evalAt, evalHOLExact, evalListHOLExact, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, ofString, hnode, hidx,
        valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, mptChildAddr]) h3
    subst s3
    obtain ⟨s4, h4, h5⟩ := mpt_seq_none_inv hrest
    have hs4 := mpt_assign_none_word _ s4 "next_level"
      (.op .add [.var .local (ofString "level"), .const 1]) (l + 1#64)
      (by simp [evalAt, evalHOLExact, evalListHOLExact, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, ofString, hlevel,
        valueIsWord, valueWord, wordOpHOL, wordOp]) h4
    subst s4
    exact mpt_assign_none_word _ t "go" (.const 1) 1 rfl h5

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
