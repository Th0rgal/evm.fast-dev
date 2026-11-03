import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2State
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2Select
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2Post

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem finalState_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {node level sl child : BitVec 64} {c : Nat} {Nd : List Nat}
    (ha : MptInsertActive s) (hk : mptKind s = 2)
    (hat : ArenaReady (finalState s c node level sl child))
    (hnv : s.locals.lookup (ofString "node") = some (.val (.word node)))
    (hlv : s.locals.lookup (ofString "level") = some (.val (.word level)))
    (hsl : sl.toNat = memW s (node.toNat + 40))
    (hchild : child.toNat = memW s (node.toNat + 48))
    (hslkey : sl.toNat ≤ locN s "klen" - locN s "level")
    (hn : NodeHeap (clearCache s (locN s "node")) Nd) (hcurrent : locN s "node" ∈ Nd)
    (hkey : KeyIn (clearCache s (locN s "node")) Nd
      (locN s "key" + locN s "level") (locN s "klen" - locN s "level")) :
    MptInsertHead (finalState s c node level sl child) ∧
      MptInsertEffect s (finalState s c node level sl child) := by
  have hnonzero : locN s "node" ≠ 0 := by
    intro hz
    simp [mptKind, hz] at hk
  have htag : memW s (locN s "node") = 2 := by simpa only [mptKind, if_neg hnonzero] using hk
  have hnN : locN s "node" = node.toNat := by simp only [locN, hnv]
  have hlN : locN s "level" = level.toNat := by simp only [locN, hlv]
  obtain ⟨hlev, Nd0, hn0, hr0, _, _⟩ := ha.1.2 ha.2
  have hb := (hn0.1 _ (hr0.resolve_left hnonzero)).2.2.1.2
  change locN s "node" + nodeSize (memW s (locN s "node")) ≤ heapLimit at hb
  rw [htag] at hb
  change locN s "node" + 56 ≤ heapLimit at hb
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hadd : (level + sl).toNat = locN s "level" + memW s (locN s "node" + 40) := by
    have hkl := locN_lt s "klen"
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (show level.toNat + sl.toNat < 2 ^ 64 by omega)]
    rw [← hlN, hsl, ← hnN]
  have hslot : (node + 48).toNat = locN s "node" + 48 := by
    rw [BitVec.toNat_add]
    change (node.toNat + 48) % 2 ^ 64 = locN s "node" + 48
    rw [← hnN, Nat.mod_eq_of_lt (by omega)]
  apply descent_post ha hk hat
  · rw [finalState_shape]
    exact hn
  · exact hcurrent
  · rw [finalState_shape]
    exact hkey
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp +decide [locN, finalState_lookup]
  · simpa +decide only [locN, finalState_lookup, if_true, if_false] using hadd
  · rw [hnN, ← hsl]
    exact hslkey
  · rw [hnN]
    simpa +decide [locN, finalState_lookup] using hchild
  · simpa +decide only [locN, finalState_lookup, if_true, if_false] using hslot
  · by_cases hz : locN s "slot" = 0
    · rw [if_pos hz]
      have hresult : (finalState s c node level sl child).locals.lookup (ofString "result") =
          some (.val (.word node)) := by simp +decide [finalState_lookup, hz]
      simp only [locN, hresult, hnv]
    · rw [if_neg hz]
      have hresult : (finalState s c node level sl child).locals.lookup (ofString "result") =
          s.locals.lookup (ofString "result") := by simp +decide [finalState_lookup, hz]
      simp only [locN, hresult]
  · have hc := congrArg (fun z : PanSemStateFiniteExact 64 F => z.clock)
      (finalState_shape s c node level sl child)
    change (finalState s c node level sl child).clock = c at hc
    rw [hc]
    exact finalState_shape s c node level sl child
  · intro x hx
    have hx' : x ≠ ofString "go" ∧ x ≠ ofString "node" ∧ x ≠ ofString "slot" ∧
        x ≠ ofString "level" ∧ x ≠ ofString "result" := by
      simpa only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or] using hx
    simp only [finalState_lookup, hx'.1, hx'.2.1, hx'.2.2.1, hx'.2.2.2.1, hx'.2.2.2.2,
      and_false, if_false]

/-- Complete normal execution of a kind-2 iteration, with all declarations restored. -/
theorem normal_run (h : MptInsertCallees) {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (ha : MptInsertActive s) (hk : mptKind s = 2)
    (hr : evaluateHOLFiniteState s mptInsertBody = (none, t)) :
    MptInsertHead t ∧ MptInsertEffect s t := by
  obtain ⟨u, hcore, ht⟩ := body_unwrap hr
  rw [core_eq] at hcore
  obtain ⟨z, hzero, hrest⟩ := seq_none hcore
  obtain ⟨v, hv, hz⟩ := assign_none hzero
  cases RunFramesRace.evalAt_const (declared s) 0 v hv
  change z = prepared s at hz
  subst z
  obtain ⟨selected, hselect, htail⟩ := seq_none hrest
  have hnonzero : locN s "node" ≠ 0 := by
    intro hz
    simp [mptKind, hz] at hk
  have htag : memW s (locN s "node") = 2 := by simpa only [mptKind, if_neg hnonzero] using hk
  obtain ⟨hlev, Nd, hn, hrroot, hkey, hslot⟩ := ha.1.2 ha.2
  have hnode : locN s "node" ∈ Nd := hrroot.resolve_left hnonzero
  have hap : ArenaReady (prepared s) := localsFree_arenaReady s _ s.clock ha.1.1
  have hpnode := prepared_locN s "node" (by decide)
  have hplevel := prepared_locN s "level" (by decide)
  have hpklen := prepared_locN s "klen" (by decide)
  have hpkey := prepared_locN s "key" (by decide)
  have hpslot := prepared_locN s "slot" (by decide)
  obtain ⟨has, hcase⟩ := selection_run h (s := prepared s) hap hn
    (hpnode ▸ hnode) (by rw [hpnode]; exact htag)
    (by rw [hplevel, hpklen]; exact hlev)
    (by rw [hpkey, hplevel, hpklen]; exact hkey)
    (by simp only [prepared, locN_put, if_true]; rfl) hselect
  obtain ⟨hau, hgu⟩ := tail_arena_go has htail
  have hat : ArenaReady t := by rw [ht]; exact cleanup_arena s u hau
  rcases hcase with hstop | ⟨node, level, sl, child, c, Nd', hnv, hlv, hsl, hchild, hslkey,
      hnc, hcurrent, hkeyc, hselected⟩
  · have htzero : locN t "go" = 0 := by rw [ht, cleanup_go, hgu, hstop]
    exact ⟨⟨hat, fun hn => False.elim (hn htzero)⟩, Or.inl htzero⟩
  · have hnv' : s.locals.lookup (ofString "node") = some (.val (.word node)) :=
      (prepared_lookup s "node" (by decide)).symm.trans hnv
    have hlv' : s.locals.lookup (ofString "level") = some (.val (.word level)) :=
      (prepared_lookup s "level" (by decide)).symm.trans hlv
    have hnN : locN s "node" = node.toNat := by simp only [locN, hnv']
    rw [hpnode] at hselected hnc hcurrent hkeyc
    rw [hpkey, hplevel, hpklen] at hkeyc
    rw [hplevel, hpklen] at hslkey
    let base := { clearCache (prepared s) (locN s "node") with clock := c }
    have hbslot : locN base "slot" = locN s "slot" := hpslot
    have hstore : locN base "slot" ≠ 0 →
        base.memory (BitVec.ofNat 64 (locN base "slot")) = .word node := by
      intro hz
      have hred := mptSlot_store_redundant hn hnode htag hslot (hbslot ▸ hz)
      have hm := congrArg (fun z : PanSemStateFiniteExact 64 F =>
        z.memory (BitVec.ofNat 64 (locN s "slot"))) hred
      change (if BitVec.ofNat 64 (locN s "slot") = BitVec.ofNat 64 (locN s "slot")
        then HolWordLab.word (BitVec.ofNat 64 (locN s "node"))
        else (clearCache s (locN s "node")).memory (BitVec.ofNat 64 (locN s "slot"))) =
        (clearCache s (locN s "node")).memory (BitVec.ofNat 64 (locN s "slot")) at hm
      have hword : BitVec.ofNat 64 (locN s "node") = node := by
        simp only [hnN, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      simp only [if_true, hword] at hm
      rw [hbslot]
      exact hm.symm
    rw [hselected] at htail
    have hfinish := tail_descended (s := base) node level sl child hstore htail
    have hfinal : t = finalState s c node level sl child := by
      rw [ht, hfinish]
      exact cleanup_finished s c node level sl child
    rw [hfinal] at hat ⊢
    exact finalState_post ha hk hat hnv' hlv' hsl hchild hslkey hnc hcurrent hkeyc

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
