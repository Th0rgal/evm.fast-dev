import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.Wave8GuestInv.EntryDefs

/-! Direct execution of `mem_init` and the empty typed world established by its zero roots. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8GuestInv.SoloMemInitWorld

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup

private theorem heap_ne_scratch : ofString "heap_ptr" ≠ ofString "scratch_ptr" := by decide
private theorem heap_ne_frame : ofString "heap_ptr" ≠ ofString "frame_mem_ptr" := by decide
private theorem scratch_ne_frame : ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" := by decide

/-- The state after the three assignments and the normal return of `mem_init`. -/
def post {F : Type} (s : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite
    (setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word 2952790016))
      (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word 2965299200))
        (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word s.baseAddr)) s)))

/-- Exact evaluation; no clock or memory-content assumption is needed. -/
theorem evaluate {F : Type} (s : PanSemStateFiniteExact 64 F) (hz : GlobalsZero s) :
    evaluateHOLFiniteState s (sourceFunctionEntry Guest.Software.guestFn_mem_init).2.2.1 =
      (some (.returned (.val (.word 0))), post s) := by
  change evaluateHOLFiniteState s
    (.seq (.assign .global (ofString "heap_ptr") .baseAddr)
      (.seq (.assign .global (ofString "scratch_ptr") (.const 2965299200))
        (.seq (.assign .global (ofString "frame_mem_ptr") (.const 2952790016))
          (.return (.const 0))))) = _
  have hh := hz "heap_ptr" (by decide)
  have hs := hz "scratch_ptr" (by decide)
  have hf := hz "frame_mem_ptr" (by decide)
  simp only [GlobalWord] at hh hs hf
  simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign,
    evaluateHOLFiniteState_return, evalHOLExact,
    isValidValueHOLFinite, lookupKvarHOLFinite, hh, hs, hf,
    setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    shapeOfHOLExact, shapeEqHOL, post, heap_ne_scratch, heap_ne_frame, scratch_ne_frame]

/-- Every global other than the allocator pointers keeps its initial value. -/
theorem post_zero {F : Type} (s : PanSemStateFiniteExact 64 F) (hz : GlobalsZero s)
    (name : String) (hn : name ∈ guestGlobalNames)
    (hne : name ∉ ["heap_ptr", "scratch_ptr", "frame_mem_ptr"]) :
    globN (post s) name = 0 := by
  have h := hz name hn
  simp only [GlobalWord] at h
  have distinct : ∀ name ∈ guestGlobalNames,
      name ∉ ["heap_ptr", "scratch_ptr", "frame_mem_ptr"] →
      ofString "heap_ptr" ≠ ofString name ∧
      ofString "scratch_ptr" ≠ ofString name ∧
      ofString "frame_mem_ptr" ≠ ofString name := by decide
  obtain ⟨h1, h2, h3⟩ := distinct name hn hne
  simp [globN, post, emptyLocalsHOLFinite, setGlobalHOLFinite,
    HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, h3, h]

/-- With all world roots zero, tables, journal and tries are typed by empty sets. -/
theorem worldTyped_empty {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hz : ∀ name ∈ guestGlobalNames,
      name ∉ ["heap_ptr", "scratch_ptr", "frame_mem_ptr"] → globN s name = 0) :
    WorldTyped s [] := by
  have hws := hz "ws" (by decide) (by decide)
  have hbs := hz "bs" (by decide) (by decide)
  have hts := hz "ts" (by decide) (by decide)
  have hbal := hz "bal_accounts" (by decide) (by decide)
  have hidxa := hz "bal_idx_accts" (by decide) (by decide)
  have hidxs := hz "bal_idx_stor" (by decide) (by decide)
  have hbo := hz "bo" (by decide) (by decide)
  have hjn := hz "journal_n" (by decide) (by decide)
  have hjc := hz "journal_cap" (by decide) (by decide)
  have hbuf : ∀ gn ∈ globalBuffers, globN s gn.1 = 0 := by
    have members : ∀ gn ∈ globalBuffers,
        gn.1 ∈ guestGlobalNames ∧ gn.1 ∉ ["heap_ptr", "scratch_ptr", "frame_mem_ptr"] := by
      decide
    intro gn hn
    exact hz gn.1 (members gn hn).1 (members gn hn).2
  have hmap : (globalBuffers.map fun gn =>
      (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) =
      globalBuffers.map (fun _ => ((0, 0) : Ivl)) := by
    apply List.map_congr_left
    intro gn hn
    simp [hbuf gn hn]
  have hfixed : ∀ i ∈ fixedObjects s, i.2 = 0 := by
    simp [fixedObjects, hmap, blockOutObjects, hbo, balObjects, balRecords, hbal, hjc]
    rintro a b (⟨_, _, hb⟩ | ⟨_, hb⟩) <;> exact hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [TablesTyped, hws, hbs, hts, hbal, hidxa, hidxs, hbo,
      globalTableRoots, balRecords, RolesOK, worldRoleSlots, recRoles, nestRoles,
      journalRoleSlots, hjn, RootIn]
  · simp [JournalTyped, hjn, hjc, journalCapMax]
  · refine ⟨fun i hi => Or.inl (hfixed i hi), ?_⟩
    have pairwise : ∀ (is : List Ivl), (∀ i ∈ is, i.2 = 0) → is.Pairwise Disj := by
      intro is his
      induction is with
      | nil => exact .nil
      | cons i is ih =>
        exact .cons (fun j _ => Or.inl (his i (by simp)))
          (ih (fun j hj => his j (by simp [hj])))
    exact pairwise _ hfixed
  · exact ⟨[], by simp [TriesTypedWith, NodeHeap, nodeExtents, hws]⟩

/-- Arena separation and the empty typed world after initialization. -/
theorem worldOK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : GuestInv s) (hz : GlobalsZero s) : WorldOK (post s) := by
  have hguest : GuestInv (post s) := guestInv_congr (s := s) rfl rfl rfl rfl hi
  have harena : ArenaOK (post s) := by
    have hb := hi.baseAddr
    simp [ArenaOK, globN, post, emptyLocalsHOLFinite, setGlobalHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE, hb, heapLimit,
      sourceBase, scratchStart, scratchEnd,
      Ne.symm heap_ne_scratch, Ne.symm heap_ne_frame, Ne.symm scratch_ne_frame]
  exact ⟨⟨hguest, harena⟩, [], worldTyped_empty (post s) (post_zero s hz)⟩

end InitECandidate.Solver.Wave8GuestInv.SoloMemInitWorld
