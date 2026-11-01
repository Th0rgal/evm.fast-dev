import InitECandidate.Solver.Wave8GuestInv.Assembly

/-! R11 ownership regressions. These proofs use invariant definitions only. -/
set_option autoImplicit false
namespace InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open InitE
open InitECandidate.Solver.HeapPotential

/-- The log header cannot be mistaken for the shared 20-byte address interval. -/
theorem logRecord_owned {F : Type} (s : PanSemStateFiniteExact 64 F) (log : Nat) :
    (log, 40) ∈ logOwnedIvls s log := by
  simp [logOwnedIvls, logRecordIvls]

/-- Every live log header is included in the existing frame separation invariant. -/
theorem liveLogRecord_mem_frameObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ec : Ivl) (i : Nat) (hi : i < memW s (memW s (ec.1 + 88) + 8)) :
    (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, logRecord_owned s _⟩

/-- Every unfiltered log interval lies in the allocated heap. -/
theorem logRecordIvls_inside {F : Type} (s : PanSemStateFiniteExact 64 F) (log : Nat)
    (h : LogEntryOK s log) (o : Ivl) (ho : o ∈ logRecordIvls s log) :
    Inside o sourceBase (globN s "heap_ptr") := by
  simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact h.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2

/-- The shared address is protected by the existing fixed-object footprint. -/
theorem systemAddress_mem_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : globN s "vm_system_address" ≠ 0) :
    (globN s "vm_system_address", 24) ∈ fixedObjects s := by
  have hm : ("vm_system_address", 24) ∈ globalBuffers := by decide
  have hf : (globN s "vm_system_address", 24) ∈
      globalBuffers.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.mpr ⟨("vm_system_address", 24), hm, by simp [h]⟩
  simp only [fixedObjects, List.mem_append]
  exact Or.inl (Or.inl (Or.inl hf))

/-- In particular, every live log header avoids every mutable typed-table extent. -/
theorem evmInv_liveLogRecord_tables {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : EvmInv s) :
    ∃ S, WorldTyped s S ∧ ∀ ec ∈ evmChain s, ∀ i,
      i < memW s (memW s (ec.1 + 88) + 8) → ∀ t ∈ S,
      ∀ o ∈ htabFootprint s t,
        Disj (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) o := by
  obtain ⟨_, S, hW, hrest⟩ := h
  dsimp only at hrest
  obtain ⟨_, _, _, _, _, _, _, hdis, _⟩ := hrest
  refine ⟨S, hW, ?_⟩
  intro ec he i hi t ht o ho
  exact (hdis ec he _ (liveLogRecord_mem_frameObjects s ec i hi)).1 t ht o ho

/-- All four intervals avoid tables, including the shared system address. -/
theorem evmInv_allLogIntervals_tables {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : EvmInv s) :
    ∃ S, WorldTyped s S ∧ ∀ ec ∈ evmChain s, ∀ i,
      i < memW s (memW s (ec.1 + 88) + 8) →
      ∀ o ∈ logRecordIvls s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)),
      ∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj o j := by
  obtain ⟨hA, S, hW, hrest⟩ := h
  dsimp only at hrest
  obtain ⟨_, _, _, hWF, _, _, _, hdis, _⟩ := hrest
  refine ⟨S, hW, ?_⟩
  intro ec he i hi o ho t ht j hj
  rcases logRecordIvls_covered s _ o ho with howned | hshared
  · have hmem : o ∈ frameObjects s ec :=
      List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨i, List.mem_range.mpr hi, howned⟩))
    exact (hdis ec he o hmem).1 t ht j hj
  · have hframe := hWF ec he
    rcases hframe with ⟨hblocks, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlogs, _⟩
    have hlog : LogEntryOK s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) := by
      rcases hlogs with hz | ⟨_, _, _, _, hentries⟩
      · have hf := (hblocks (memW s (ec.1 + 88), 24) (by simp)).1.1
        have ha := hA.2.2.2.1
        have hb := hA.2.2.2.2.1
        change globN s "scratch_ptr" ≤ memW s (ec.1 + 88) at hf
        have hs : scratchStart = 2952790016 := rfl
        omega
      · exact (hentries i hi).2
    have hins := logRecordIvls_inside s _ hlog o ho
    have hne : globN s "vm_system_address" ≠ 0 := by
      rw [hshared] at hins
      have hp := hins.1
      change sourceBase ≤ globN s "vm_system_address" at hp
      have hs : sourceBase = 2701131776 := rfl
      omega
    have hd := ((hW.1.2.1 t ht).2 j hj).2 _ (systemAddress_mem_fixedObjects s hne)
    rw [hshared]
    simp only [Disj] at hd ⊢
    omega

/-- The existing memory index remains index 3 despite the appended log objects. -/
theorem frameObjects_memory_index {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) :
    (frameObjects s ec)[3]! = (memW s (ec.1 + 24), memW s (ec.1 + 40)) := by
  rfl

/-- Scratch release keeps every surviving ancestor's message, in addition to its blocks. -/
theorem marksOK_ancestor_message {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S : List Nat) (ch : List Ivl) (h : MarksOK s S ch)
    (i : Nat) (hi : i + 1 < ch.length) (j : Nat) (hj : j < ch.length) (hij : i < j) :
    Inside (memW s (ch[j].1 + 112), 176) sourceBase heapLimit ∨
      Inside (memW s (ch[j].1 + 112), 176)
        (memW s ((ch[i]'(by omega)).2 + 48)) scratchEnd := by
  exact ((h i hi).2.2.2.2.1 j hj hij).2.2.2

#print axioms assembly
#print axioms assembly_main
#print axioms logRecordIvls_covered
#print axioms logRecordIvls_inside
#print axioms systemAddress_mem_fixedObjects
#print axioms logRecord_owned
#print axioms liveLogRecord_mem_frameObjects
#print axioms evmInv_liveLogRecord_tables
#print axioms evmInv_allLogIntervals_tables
#print axioms frameObjects_memory_index
#print axioms marksOK_ancestor_message
end InitECandidate.Solver.Wave8GuestInv
