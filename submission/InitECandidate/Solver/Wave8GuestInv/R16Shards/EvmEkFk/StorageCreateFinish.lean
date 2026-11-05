import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.EkWarmStorageKey
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open InitE InitECandidate.Solver.Wave8GuestInv

theorem allocated_disj_fresh_extent {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {o j : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : Allocated s o)
    (hj : Inside j (globN s "heap_ptr") (globN post "heap_ptr")) :
    Disj o j := by
  have hd := R16Shards.disj_fresh_of_allocated hAs hAp hhp ho
  unfold Inside at hj
  unfold Disj at hd ⊢
  dsimp only at hd ⊢
  rcases hd with h | h | h | h
  · exact Or.inl h
  · by_cases hz : globN post "heap_ptr" = globN s "heap_ptr"
    · right; left; omega
    · omega
  · right; right; left; omega
  · right; right; right; omega

theorem allocated_disj_old_or_fresh_extent {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {o j : Ivl} {old : List Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : Allocated s o)
    (hold : ∀ i ∈ old, Disj o i)
    (hj : (∃ i ∈ old, Inside j i.1 (i.1 + i.2)) ∨
      Inside j (globN s "heap_ptr") (globN post "heap_ptr")) :
    Disj o j := by
  rcases hj with ⟨i, hi, hin⟩ | hfresh
  · have hd := hold i hi
    unfold Inside at hin
    unfold Disj at hd ⊢
    rcases hd with hz | hz | hbefore | hafter
    · exact Or.inl hz
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega
  · exact allocated_disj_fresh_extent hAs hAp hhp ho hfresh

theorem allocated_disj_growing_nodeExtents {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {o : Ivl} {Nd Nd' : List Nat}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : Allocated s o)
    (hold : ∀ i ∈ nodeExtents s Nd, Disj o i)
    (hgrow : ∀ j ∈ nodeExtents post Nd',
      (∃ i ∈ nodeExtents s Nd, Inside j i.1 (i.1 + i.2)) ∨
        Inside j (globN s "heap_ptr") (globN post "heap_ptr")) :
    ∀ j ∈ nodeExtents post Nd', Disj o j := by
  intro j hj
  exact allocated_disj_old_or_fresh_extent hAs hAp hhp ho hold (hgrow j hj)

theorem rootIn_lt_word_limit {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {node : Nat} (hh : NodeHeap s Nd) (hr : RootIn Nd node) :
    node + 1 < 2 ^ 64 := by
  rcases hr with hz | hn
  · subst node; decide
  · have hi := (hh.1 node hn).2.2.1
    change sourceBase ≤ node ∧ node + nodeSize (memW s node) ≤ heapLimit at hi
    have hlim : heapLimit + 1 < 2 ^ 64 := by decide
    omega

theorem rootIn_tagged_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {node : Nat} (hh : NodeHeap s Nd) (hr : RootIn Nd node) :
    RootIn Nd ((BitVec.ofNat 64 (node + 1)).toNat - 1) := by
  have hlt := rootIn_lt_word_limit hh hr
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.add_sub_cancel] using hr

theorem allocated_disj_ownedGrows {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {o : Ivl} {old new : List Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : Allocated s o)
    (hold : ∀ i ∈ old, Disj o i)
    (hgrow : OwnedGrows s post old new) :
    ∀ j ∈ new, Disj o j := by
  intro j hj
  rcases hgrow j hj with hz | hcontained
  · subst j
    exact Or.inr (Or.inl rfl)
  · exact allocated_disj_old_or_fresh_extent hAs hAp hhp ho hold hcontained

theorem allocated_regions_disj_ownedGrows {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {os old new : List Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hos : ∀ o ∈ os, Allocated s o)
    (hold : IvlsDisj os old)
    (hgrow : OwnedGrows s post old new) :
    IvlsDisj os new := by
  intro o ho
  exact allocated_disj_ownedGrows hAs hAp hhp (hos o ho) (hold o ho) hgrow

theorem worldStep_preserves_allocated_separation
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
      Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F →
      List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat} {os : List Ivl}
    (hAs : ArenaOK s) (hstep : WorldStep R gw keep Q s r post)
    (hW : WorldTypedWith s S Nd)
    (hR : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hos : ∀ o ∈ os, Allocated s o)
    (hdisj : IvlsDisj os (worldOwned s S Nd)) :
    ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
      IvlsDisj os (worldOwned post S' Nd') ∧ Q s r post S' Nd' := by
  obtain ⟨hAp, hhp, _, _, htyped⟩ := hstep
  obtain ⟨S', Nd', hsub, hW', hgrow, _, hQ⟩ := htyped S Nd hW hR
  exact ⟨S', Nd', hsub, hW',
    allocated_regions_disj_ownedGrows hAs hAp.2 hhp hos hdisj hgrow, hQ⟩

theorem create_finish_deposit_mul_no_wrap (n : BitVec 64)
    (hn : n.toNat ≤ 65536) :
    (n * 1530).toNat = n.toNat * 1530 := by
  rw [BitVec.toNat_mul]
  change n.toNat * 1530 % 2 ^ 64 = n.toNat * 1530
  exact Nat.mod_eq_of_lt (by omega)

theorem create_finish_alloc_add_no_wrap (n : BitVec 64)
    (hn : n.toNat ≤ 65536) :
    (n + 8).toNat = n.toNat + 8 := by
  apply BitVec.toNat_add_of_lt
  change n.toNat + 8 < 2 ^ 64
  omega

theorem create_finish_word_charge_no_wrap (w : BitVec 64)
    (hw : w.toNat ≤ 2048) :
    (6 * w).toNat = 6 * w.toNat := by
  rw [BitVec.toNat_mul]
  change 6 * w.toNat % 2 ^ 64 = 6 * w.toNat
  exact Nat.mod_eq_of_lt (by omega)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish
