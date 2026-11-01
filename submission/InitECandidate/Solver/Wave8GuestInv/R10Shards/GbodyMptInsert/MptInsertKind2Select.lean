import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Extension
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Prefix

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem clearCache_field {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hn : NodeHeap s Nd) (hnode : locN s "node" ∈ Nd)
    (htag : memW s (locN s "node") = 2) (off : Nat)
    (ho : off = 0 ∨ off = 32 ∨ off = 40 ∨ off = 48) :
    memW (clearCache s (locN s "node")) (locN s "node" + off) =
      memW s (locN s "node" + off) := by
  have hb := (hn.1 _ hnode).2.2.1.2
  change locN s "node" + nodeSize (memW s (locN s "node")) ≤ heapLimit at hb
  rw [htag] at hb
  change locN s "node" + 56 ≤ heapLimit at hb
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hm := clearCache_memory_eq s (locN s "node") (locN s "node" + off)
    (by rcases ho with rfl | rfl | rfl | rfl <;> omega) (by omega)
    (by rcases ho with rfl | rfl | rfl | rfl <;> omega)
    (by rcases ho with rfl | rfl | rfl | rfl <;> omega)
    (by rcases ho with rfl | rfl | rfl | rfl <;> omega)
  simp only [memW, hm]

/-- Invalidation followed by extension dispatch, including restoration of the tag local. -/
theorem selection_run (h : MptInsertCallees) {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s) (hn : NodeHeap s Nd) (hnode : locN s "node" ∈ Nd)
    (htag : memW s (locN s "node") = 2)
    (hlev : locN s "level" ≤ locN s "klen")
    (hkey : KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level"))
    (hvlen : locN s "vlen" < 2 ^ 40)
    (hgo : locN s "go" = 0)
    (hr : evaluateHOLFiniteState s selection = (none, t)) :
    ArenaReady t ∧ (locN t "go" = 0 ∨
      ∃ (node level sl child : BitVec 64) (c : Nat) (Nd' : List Nat),
        s.locals.lookup (ofString "node") = some (.val (.word node)) ∧
        s.locals.lookup (ofString "level") = some (.val (.word level)) ∧
        sl.toNat = memW s (node.toNat + 40) ∧
        child.toNat = memW s (node.toNat + 48) ∧
        sl.toNat ≤ locN s "klen" - locN s "level" ∧
        NodeHeap (clearCache s (locN s "node")) Nd' ∧ locN s "node" ∈ Nd' ∧
        KeyIn (clearCache s (locN s "node")) Nd'
          (locN s "key" + locN s "level") (locN s "klen" - locN s "level") ∧
        t = descended { clearCache s (locN s "node") with clock := c } node level sl child) := by
  have hnonzero : locN s "node" ≠ 0 := by
    have hb := (hn.1 _ hnode).2.2.1.1
    change sourceBase ≤ locN s "node" at hb
    have : 0 < sourceBase := by decide
    omega
  obtain ⟨cleared, u, Nd', hac, hnc, hsub, hkeys, hc, hext, ht⟩ :=
    nonnull_extension h ha hn (Or.inr hnode) htag (selection_nonnull hnonzero hr)
  change t = restore u "k" (s.locals.lookup (ofString "k")) at ht
  have hcloc (n : String) (hne : ofString n ≠ ofString "k") :
      cleared.locals.lookup (ofString n) = s.locals.lookup (ofString n) := by
    rw [hc]
    change (put s "k" 2).locals.lookup (ofString n) = s.locals.lookup (ofString n)
    rw [lookup_put, if_neg hne]
  have hcn (n : String) (hne : ofString n ≠ ofString "k") : locN cleared n = locN s n := by
    simp only [locN, hcloc n hne]
  have hcm (a : Nat) : memW cleared a = memW (clearCache s (locN s "node")) a := by
    rw [hc]
    rfl
  have hctag : memW cleared (locN cleared "node") = 2 := by
    rw [hcn "node" (by decide), hcm]
    have hf := clearCache_field hn hnode htag 0 (Or.inl rfl)
    simpa only [Nat.add_zero, htag] using hf
  have hckey : KeyIn cleared Nd' (locN cleared "key" + locN cleared "level")
      (locN cleared "klen" - locN cleared "level") := by
    rw [hcn "key" (by decide), hcn "level" (by decide), hcn "klen" (by decide)]
    exact hkeys _ _ hkey
  obtain ⟨hau, hcase⟩ := extension_run h hac hnc
    (by rw [hcn "node" (by decide)]; exact hsub _ hnode) hctag
    (by rw [hcn "level" (by decide), hcn "klen" (by decide)]; exact hlev)
    hckey (by rw [hcn "vlen" (by decide)]; exact hvlen)
    (by rw [hcn "go" (by decide)]; exact hgo) hext
  refine ⟨ht ▸ restore_arena "k" _ hau, ?_⟩
  rcases hcase with hz | ⟨node, level, sl, child, c, hnv, hlv, hsl, hchild, hslkey, hu⟩
  · left
    rw [ht, restore_go _ _ _ (by decide)]
    exact hz
  · have hnv' : s.locals.lookup (ofString "node") = some (.val (.word node)) :=
      (hcloc "node" (by decide)).symm.trans hnv
    have hnN : locN s "node" = node.toNat := by simp only [locN, hnv']
    have hsl' : sl.toNat = memW s (node.toNat + 40) := by
      rw [hcm, ← hnN, clearCache_field hn hnode htag 40 (Or.inr (Or.inr (Or.inl rfl)))] at hsl
      simpa only [hnN] using hsl
    have hchild' : child.toNat = memW s (node.toNat + 48) := by
      rw [hcm, ← hnN, clearCache_field hn hnode htag 48 (Or.inr (Or.inr (Or.inr rfl)))] at hchild
      simpa only [hnN] using hchild
    refine Or.inr ⟨node, level, sl, child, c, Nd', hnv',
      (hcloc "level" (by decide)).symm.trans hlv, hsl', hchild', ?_, ?_, hsub _ hnode, ?_, ?_⟩
    · simpa only [hcn "klen" (by decide), hcn "level" (by decide)] using hslkey
    · rw [hc] at hnc
      exact hnc
    · have hk := hkeys _ _ hkey
      rw [hc] at hk
      exact hk
    · rw [ht, hu, restore_descended _ _ _ _ _ "k" _ (by decide), hc]
      change descended (restore (put { clearCache s (locN s "node") with clock := c } "k" 2)
        "k" (({ clearCache s (locN s "node") with clock := c } : PanSemStateFiniteExact 64 F).locals.lookup
          (ofString "k"))) node level sl child = _
      rw [restore_put_same]

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
