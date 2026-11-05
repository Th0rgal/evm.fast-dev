import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase1R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R13Shards

/-- Before the Phase-4 stable copy, the header and live pointer array may be
scratch-resident. `frame_new` uses `lst_new_scratch`; `lst_push` moves only the
backing array to the heap when it grows. -/
def LogsLiveOwned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (logs : Nat) : Prop :=
  logs ≠ 0 →
    Allocated s (memW s logs, 8 * memW s (logs + 8)) ∧
    IvlsDisj [(logs, 24), (memW s logs, 8 * memW s (logs + 8))] (worldOwned s S Nd) ∧
    ∀ i, i < memW s (logs + 8) →
      IvlsDisj (logOwnedIvls s (memW s (memW s logs + 8 * i))) (worldOwned s S Nd)

/-- The message result owns its live log storage outside the world, without
requiring the temporary header or its initial array to be heap-resident. -/
def RetMessageOutputStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd => RetMessageOutput s r post S Nd ∧
    ∀ v, r = some (.returned v) → ∃ w : BitVec 64,
      v = .val (.word w) ∧ LogsLiveOwned post S Nd (memW post (w.toNat + 16))

def TxAfterCallStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧ WordsOK s (locN s "out", 96) ∧
    Inside (locN s "out", 96) sourceBase (globN s "heap_ptr") ∧
    LogsListOK s (memW s (locN s "out" + 16)) ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧
      IvlsDisj [(locN s "out", 96)] (worldOwned s S Nd) ∧
      LogsLiveOwned s S Nd (memW s (locN s "out" + 16))

def BoListArgStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ BoListArg s ∧ memW s (locN s "l") ≠ 0

/-- Caller locals read by Phase 4 before they are assigned there. `out` is
introduced by Phase 3 itself. The message-building locals `mgas`, `reservoir`
and `m` are not read by Phase 4. -/
def PtxPhase4LocalShapes : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    (∀ name ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))) ∧
    (∃ v, s.locals.lookup (ofString "price") = some v ∧
      shapeOfHOLExact v = .comb [.one, .one, .one, .one]) ∧
    (∃ v, s.locals.lookup (ofString "intrinsic") = some v ∧
      shapeOfHOLExact v = .comb [.one, .one, .one])

theorem ptxPhase4LocalShapes_resume {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (h : PtxPhase4LocalShapes s) :
    PtxPhase4LocalShapes (setVarHOLFinite (ofString "out") v { post with locals := s.locals }) := by
  have hlu : ∀ name : String, ofString name ≠ ofString "out" →
      (setVarHOLFinite (ofString "out") v { post with locals := s.locals }).locals.lookup
        (ofString name) = s.locals.lookup (ofString name) := by
    intro name hn
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hn]
  refine ⟨?_, ?_, ?_⟩
  · intro name hn
    have hne : ofString name ≠ ofString "out" := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hlu name hne]
    exact h.1 name hn
  · rw [hlu "price" (by decide)]; exact h.2.1
  · rw [hlu "intrinsic" (by decide)]; exact h.2.2

namespace PtxP34
open PtxP1

/-- The concrete account proof supplies the scratch frontier bound omitted by
the weaker `PtxCallees.wk_create_ether` interface. -/
theorem create_ether_allocatorGrows {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs =
      some (body, callee, ret))
    (hW : WorldOK (callEntryStateHOLFinite s callee))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠
      some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1) :
    AllocatorGrows (callEntryStateHOLFinite s callee)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2 := by
  have hw := funSpec_at_lookup EvmEkFk.wkSc_create_ether s hc vs body callee ret hl hW hnt hr
  exact ⟨hw.1.2.1, hw.2⟩

/-- Receipt encoding's frozen guard asks for placement even for an empty array.
The allocator-created backing buffer supplies it independently of live cells. -/
theorem logsLiveOwned_disjFixed {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} (hd : LogsLiveOwned s S Nd logs) :
    LogsDisjFixed s logs := by
  by_cases hn : logs = 0
  · exact Or.inl hn
  refine Or.inr ⟨?_, ?_⟩
  · exact (hd hn).1
  · intro o ho j hj
    have hjw : j ∈ worldOwned s S Nd := by
      unfold worldOwned
      simp only [List.mem_append]
      exact Or.inl (Or.inr hj)
    rcases List.mem_append.mp ho with hh | he
    · exact (hd hn).2.1 o hh j hjw
    · obtain ⟨i, hi, ho⟩ := List.mem_flatMap.mp he
      exact (hd hn).2.2 i (List.mem_range.mp hi) o ho j hjw

/-- Allocated scratch survives a framed step just like allocated heap. The
scratch frontier must be retained (or move down), not equal `scratchEnd`. -/
theorem allocated_ivl_survives_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old new R : List Ivl} {b : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hgrow : AllocatorGrows s post)
    (hold0 : ∀ j ∈ old, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post old new)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hb : Allocated s b) (hold : ∀ j ∈ old, Disj b j)
    (hR : ∀ j ∈ R, Disj b j) :
    Allocated post b ∧ (∀ o ∈ new, Disj b o) ∧ IvlUnhit s post b := by
  refine ⟨hgrow.allocated hb, ?_⟩
  rcases hb with hh | hs
  · exact (R13Shards.heap_ivl_survives_step hAs hgrow.1 hold0 hR0 hog hfr
      hb1 hb2 hh hold hR).2
  have hsep : heapLimit ≤ scratchStart := by decide
  have hfm := hAs.2.2.1
  have hsc := hAs.2.2.2.1
  have hhp := hAs.2.1
  have hhpp := hAp.2.1
  constructor
  · intro o ho
    rcases hog o ho with rfl | ⟨j, hj, hin⟩ | hfresh
    · exact R13Shards.disj_zero_right b
    · exact R13Shards.disj_of_inside_right hin (hold j hj)
    · exact Or.inr (Or.inr (Or.inr (by have := hs.1; have := hfresh.2; omega)))
  · intro a ha8 hhit
    obtain ⟨hc1, hc2⟩ := hhit
    have ha_in : b.1 ≤ a.toNat ∧ a.toNat + 8 ≤ b.1 + b.2 := by omega
    apply hfr a
    · intro j hj hcj
      rcases List.mem_append.mp hj with hj12 | hfg
      · rcases List.mem_append.mp hj12 with ho | hr
        · exact R13Shards.not_cellHits_of_disj ha8 (hold0 j ho) ha_in (hold j ho) hcj
        · exact R13Shards.not_cellHits_of_disj ha8 (hR0 j hr) ha_in (hR j hr) hcj
      · simp only [List.mem_singleton] at hfg
        subst j
        obtain ⟨hj1, hj2⟩ := hcj
        unfold freeGap at hj1 hj2
        have := hs.1
        dsimp at hj1 hj2
        omega
    · intro hcf
      obtain ⟨hf1, hf2⟩ := hcf
      unfold heapFree at hf1 hf2
      have := hs.1
      dsimp at hf1 hf2
      omega

/-- Separation from newly owned world storage needs placement, but no cell
alignment. This also covers byte-sized log payload intervals. -/
theorem allocated_disj_ownedGrows {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old new : List Ivl} {b : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hb : Allocated s b)
    (hog : OwnedGrows s post old new) (hd : ∀ j ∈ old, Disj b j) :
    ∀ o ∈ new, Disj b o := by
  intro o ho
  rcases hog o ho with rfl | ⟨j, hj, hin⟩ | hfresh
  · exact R13Shards.disj_zero_right b
  · exact R13Shards.disj_of_inside_right hin (hd j hj)
  · rcases hb with hh | hs
    · exact Or.inr (Or.inr (Or.inl (hh.2.trans hfresh.1)))
    · have hsep : heapLimit ≤ scratchStart := by decide
      have hfm := hAs.2.2.1
      have hsc := hAs.2.2.2.1
      have hhp := hAp.2.1
      exact Or.inr (Or.inr (Or.inr (by have := hs.1; have := hfresh.2; omega)))

/-- All four log intervals are heap-resident, including the byte payloads. -/
theorem logEntryOK_record_placed {F : Type} {s : PanSemStateFiniteExact 64 F}
    {log : Nat} (hl : LogEntryOK s log) :
    ∀ o ∈ logRecordIvls s log, Inside o sourceBase (globN s "heap_ptr") := by
  intro o ho
  simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact hl.2.1
  · exact hl.2.2.2.2.1
  · exact hl.2.2.2.2.2.1
  · exact hl.2.2.2.2.2.2

/-- Framing the record fixes the payload intervals used by the receipt guard.
The shared system address is filtered identically when its global is retained. -/
theorem logOwnedIvls_eq_of_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {log : Nat}
    (hAs : ArenaOK s) (hl : LogEntryOK s log)
    (hu : IvlUnhit s post (log, 40))
    (hsys : globN post "vm_system_address" = globN s "vm_system_address") :
    logOwnedIvls post log = logOwnedIvls s log := by
  have hb := (R13Shards.ivl_allocated_bound hAs (Or.inl hl.2.1)).2
  have ha := hl.1.1
  have hm : ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (log + k) = memW s (log + k) := by
    intro k hk
    apply R13Shards.memW_eq_of_ivlUnhit hu
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    · exact hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> (constructor <;> omega)
  have h0 : memW post log = memW s log := by simpa using hm 0 (by simp)
  simp only [logOwnedIvls, logRecordIvls, hsys, h0,
    hm 8 (by simp), hm 16 (by simp), hm 24 (by simp), hm 32 (by simp)]

theorem logOwnedIvls_disj_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old new : List Ivl} {log : Nat}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hl : LogEntryOK s log)
    (hu : IvlUnhit s post (log, 40))
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (hog : OwnedGrows s post old new) (hd : IvlsDisj (logOwnedIvls s log) old) :
    IvlsDisj (logOwnedIvls post log) new := by
  rw [logOwnedIvls_eq_of_unhit hAs hl hu hsys]
  intro o ho
  have hmem := (List.mem_filter.mp ho).1
  exact allocated_disj_ownedGrows hAs hAp
    (Or.inl (logEntryOK_record_placed hl o hmem)) hog (hd o ho)

/-- Reassemble the log-list invariant from preservation of the header, live
pointer cells and individual log records. This isolates the memory obligations
of the two ether-creation calls from the list invariant itself. -/
theorem logsListOK_congr_live {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {logs : Nat} (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (h : LogsListOK s logs)
    (halloc : Allocated s (logs, 24) → Allocated post (logs, 24))
    (hhead : ∀ k ∈ ([0, 8, 16] : List Nat),
      memW post (logs + k) = memW s (logs + k))
    (hptr : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i))
    (hentry : ∀ i, i < memW s (logs + 8) →
      IvlUnhit s post (memW s (memW s logs + 8 * i), 40)) :
    LogsListOK post logs := by
  rcases h with hz | ⟨hw, ha, hn, hc, he⟩
  · exact Or.inl hz
  have h0 : memW post logs = memW s logs := by simpa using hhead 0 (by simp)
  have h8 := hhead 8 (by simp)
  have h16 := hhead 16 (by simp)
  refine Or.inr ⟨R13Shards.wordsOK_transfer hgS hgP hw, halloc ha, ?_, ?_, ?_⟩
  · rw [h8]; exact hn
  · rw [h8, h16]; exact hc
  · intro i hi
    rw [h8] at hi
    rw [h0, hptr i hi]
    exact ⟨R13Shards.wordAt_transfer hgS hgP (he i hi).1,
      R13Shards.logEntryOK_congr_unhit hAs hgS hgP hhp (he i hi).2 (hentry i hi)⟩

theorem logsListOK_congr_header_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (h : LogsListOK s logs)
    (halloc : Allocated s (logs, 24) → Allocated post (logs, 24))
    (hhead : IvlUnhit s post (logs, 24))
    (hptr : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i))
    (hentry : ∀ i, i < memW s (logs + 8) →
      IvlUnhit s post (memW s (memW s logs + 8 * i), 40)) :
    LogsListOK post logs := by
  rcases h with hz | hl
  · exact Or.inl hz
  apply logsListOK_congr_live hAs hgS hgP hhp (Or.inr hl) halloc _ hptr hentry
  intro k hk
  have h8 := hl.1.1
  have hb := (R13Shards.ivl_allocated_bound hAs hl.2.1).2
  apply R13Shards.memW_eq_of_ivlUnhit hhead
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> omega
  · exact hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> (constructor <;> omega)

/-- The alternate scratch branch in the R11 ownership predicate is empty:
a 24-byte header cannot start at or above `scratchEnd` and end below it. -/
theorem logsOwnedDisj_header_heap {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} (h : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0) :
    Inside (logs, 24) sourceBase (globN s "heap_ptr") := by
  rcases (h hn).1 with hh | ⟨hs, he⟩
  · exact hh
  · unfold Inside at hs
    simp only [he] at hs
    omega

/-- The log header is protected by the world-step frame once its scratch-write
disjointness is established. It remains disjoint from the new owned world. -/
theorem logsOwnedDisj_header_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hlogs : LogsListOK s logs) (hd : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0)
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hR : ∀ j ∈ R, Disj (logs, 24) j) :
    Inside (logs, 24) sourceBase (globN post "heap_ptr") ∧
    (∀ o ∈ new, Disj (logs, 24) o) ∧ IvlUnhit s post (logs, 24) := by
  rcases hlogs with hz | hl
  · exact False.elim (hn hz)
  exact R13Shards.heap_ivl_survives_step hAs hhp hold0 hR0 hog hfr
    hl.1.1 (by norm_num) (logsOwnedDisj_header_heap hd hn)
    (fun j hj => (hd hn).2.1 _ (by simp) j hj) hR

theorem logsOwnedDisj_entry_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs i : Nat}
    {new R : List Ivl} (hAs : ArenaOK s)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hlogs : LogsListOK s logs) (hd : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0)
    (hi : i < memW s (logs + 8))
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hR : ∀ j ∈ R, Disj (memW s (memW s logs + 8 * i), 40) j) :
    Inside (memW s (memW s logs + 8 * i), 40) sourceBase (globN post "heap_ptr") ∧
    (∀ o ∈ new, Disj (memW s (memW s logs + 8 * i), 40) o) ∧
    IvlUnhit s post (memW s (memW s logs + 8 * i), 40) := by
  rcases hlogs with hz | hl
  · exact False.elim (hn hz)
  have he := (hl.2.2.2.2 i hi).2
  exact R13Shards.heap_ivl_survives_step hAs hhp hold0 hR0 hog hfr
    he.1.1 (by norm_num) he.2.1
    (fun j hj => (hd hn).2.2 i hi _ (by simp) j hj) hR

/-- Live pointer-array preservation additionally needs its heap placement.
`LogsOwnedDisj` itself specifies disjointness but not placement of this array. -/
theorem logsOwnedDisj_array_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hd : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0)
    (halign : memW s logs % 8 = 0)
    (hin : Inside (memW s logs, 8 * memW s (logs + 8)) sourceBase (globN s "heap_ptr"))
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hR : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j) :
    (∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i)) ∧
    (∀ o ∈ new, Disj (memW s logs, 8 * memW s (logs + 8)) o) := by
  have hs := R13Shards.heap_ivl_survives_step hAs hhp hold0 hR0 hog hfr
    halign (by simp) hin (fun j hj => (hd hn).2.1 _ (by simp) j hj) hR
  refine ⟨?_, hs.2.1⟩
  intro i hi
  apply R13Shards.memW_eq_of_ivlUnhit hs.2.2
  · omega
  · exact (R13Shards.ivl_allocated_bound hAs (Or.inl hin)).2
  · constructor <;> dsimp <;> omega

/-- A nonempty log list does provide alignment of its backing pointer, through
the ordinary-domain membership of its first live cell. This does not bound
that cell by the current allocation frontier. -/
theorem logsListOK_array_aligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {logs : Nat} (hg : GuestInv s) (h : LogsListOK s logs) (hn : logs ≠ 0)
    (hlen : 0 < memW s (logs + 8)) : memW s logs % 8 = 0 := by
  rcases h with hz | hl
  · exact False.elim (hn hz)
  obtain ⟨w, hdom, _⟩ := (hl.2.2.2.2 0 hlen).1
  rw [hg.memaddrs] at hdom
  have ha := (R13Shards.ordinaryDomain_iff _).mp hdom
  have hlt : memW s logs < 2 ^ 64 := by
    unfold memW
    cases s.memory (BitVec.ofNat 64 logs) with
    | word v => exact v.isLt
  simpa only [Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] using ha.1

/-- A framed world step preserves the entire log list when its live array is
heap-resident and all live log storage avoids the explicit write footprint. -/
theorem logsListOK_of_framed_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hlogs : LogsListOK s logs) (hd : LogsOwnedDisj s S Nd logs)
    (harray : logs ≠ 0 → memW s logs % 8 = 0 ∧
      Inside (memW s logs, 8 * memW s (logs + 8)) sourceBase (globN s "heap_ptr"))
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hRh : ∀ j ∈ R, Disj (logs, 24) j)
    (hRa : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j)
    (hRe : ∀ i, i < memW s (logs + 8) →
      ∀ j ∈ R, Disj (memW s (memW s logs + 8 * i), 40) j) :
    LogsListOK post logs := by
  by_cases hn : logs = 0
  · exact Or.inl hn
  have hh := logsOwnedDisj_header_survives hAs hhp hlogs hd hn hold0 hR0 hog hfr hRh
  have ha := logsOwnedDisj_array_survives hAs hhp hd hn
    (harray hn).1 (harray hn).2 hold0 hR0 hog hfr hRa
  apply logsListOK_congr_header_unhit hAs hgS hgP hhp hlogs
    (fun _ => Or.inl hh.1) hh.2.2 ha.1
  intro i hi
  exact (logsOwnedDisj_entry_survives hAs hhp hlogs hd hn hi
    hold0 hR0 hog hfr (hRe i hi)).2.2

/-- Empty arrays need no placement premise. For nonempty arrays, alignment
follows from `LogsListOK`, leaving only heap placement as an extra obligation. -/
theorem logsListOK_of_framed_step_live {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hlogs : LogsListOK s logs) (hd : LogsOwnedDisj s S Nd logs)
    (harray : logs ≠ 0 → 0 < memW s (logs + 8) →
      Inside (memW s logs, 8 * memW s (logs + 8)) sourceBase (globN s "heap_ptr"))
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hRh : ∀ j ∈ R, Disj (logs, 24) j)
    (hRa : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j)
    (hRe : ∀ i, i < memW s (logs + 8) →
      ∀ j ∈ R, Disj (memW s (memW s logs + 8 * i), 40) j) :
    LogsListOK post logs := by
  by_cases hn : logs = 0
  · exact Or.inl hn
  have hh := logsOwnedDisj_header_survives hAs hhp hlogs hd hn hold0 hR0 hog hfr hRh
  apply logsListOK_congr_header_unhit hAs hgS hgP hhp hlogs
    (fun _ => Or.inl hh.1) hh.2.2
  · intro i hi
    have hpos : 0 < memW s (logs + 8) := by omega
    exact (logsOwnedDisj_array_survives hAs hhp hd hn
      (logsListOK_array_aligned hgS hlogs hn hpos) (harray hn hpos)
      hold0 hR0 hog hfr hRa).1 i hi
  · intro i hi
    exact (logsOwnedDisj_entry_survives hAs hhp hlogs hd hn hi
      hold0 hR0 hog hfr (hRe i hi)).2.2

/-- Live arrays retain both their pointer cells and their separation from the
new world. Empty arrays need no alignment, even when their pointer is arbitrary. -/
theorem logsLiveOwned_array_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hgS : GuestInv s) (hgrow : AllocatorGrows s post)
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs) (hn : logs ≠ 0)
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hRa : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j) :
    Allocated post (memW s logs, 8 * memW s (logs + 8)) ∧
    (∀ o ∈ new, Disj (memW s logs, 8 * memW s (logs + 8)) o) ∧
    (∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i)) := by
  refine ⟨hgrow.allocated (hd hn).1, ?_⟩
  by_cases hz : memW s (logs + 8) = 0
  · constructor
    · intro o ho
      exact Or.inl (by simp [hz])
    · intro i hi
      omega
  have hp : 0 < memW s (logs + 8) := by omega
  have ha := allocated_ivl_survives_step hAs hAp hgrow hold0 hR0 hog hfr
    (logsListOK_array_aligned hgS hl hn hp) (by simp)
    (hd hn).1 (fun j hj => (hd hn).2.1 _ (by simp) j hj) hRa
  refine ⟨ha.2.1, ?_⟩
  intro i hi
  apply R13Shards.memW_eq_of_ivlUnhit ha.2.2
  · have := logsListOK_array_aligned hgS hl hn hp; omega
  · exact (R13Shards.ivl_allocated_bound hAs (hd hn).1).2
  · constructor <;> dsimp <;> omega

/-- Preservation for the actual temporary lists returned by the guest: both
heap and live scratch headers/arrays are allowed, and empty arrays are ignored. -/
theorem logsLiveOwned_list_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hgS : GuestInv s) (hgP : GuestInv post) (hgrow : AllocatorGrows s post)
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs)
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hRh : ∀ j ∈ R, Disj (logs, 24) j)
    (hRa : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j)
    (hRe : ∀ i, i < memW s (logs + 8) →
      ∀ j ∈ R, Disj (memW s (memW s logs + 8 * i), 40) j) :
    LogsListOK post logs := by
  by_cases hn : logs = 0
  · exact Or.inl hn
  have hl' := hl.resolve_left hn
  have hh := allocated_ivl_survives_step hAs hAp hgrow hold0 hR0 hog hfr
    hl'.1.1 (by norm_num : 24 % 8 = 0) hl'.2.1
    (fun j hj => (hd hn).2.1 _ (by simp) j hj) hRh
  apply logsListOK_congr_header_unhit hAs hgS hgP hgrow.1 hl
    (fun _ => hh.1) hh.2.2
  · intro i hi
    exact (logsLiveOwned_array_survives hAs hAp hgS hgrow hl hd hn
      hold0 hR0 hog hfr hRa).2.2 i hi
  · intro i hi
    have he := (hl'.2.2.2.2 i hi).2
    have hmem : (memW s (memW s logs + 8 * i), 40) ∈
        logOwnedIvls s (memW s (memW s logs + 8 * i)) := by
      simp [logOwnedIvls, logRecordIvls]
    exact (R13Shards.heap_ivl_survives_step hAs hgrow.1 hold0 hR0 hog hfr
      he.1.1 (by norm_num) he.2.1
      (fun j hj => (hd hn).2.2 i hi _ hmem j hj) (hRe i hi)).2.2

/-- Full ownership transport, so the same invariant can be used again for the
second ether-creation call and then for receipt encoding. -/
theorem logsLiveOwned_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd S' Nd' : List Nat} {logs : Nat}
    {R : List Ivl} (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hgS : GuestInv s) (hgrow : AllocatorGrows s post)
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs)
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hRh : ∀ j ∈ R, Disj (logs, 24) j)
    (hRa : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j)
    (hRe : ∀ i, i < memW s (logs + 8) →
      ∀ j ∈ R, Disj (memW s (memW s logs + 8 * i), 40) j) :
    LogsLiveOwned post S' Nd' logs := by
  intro hn
  have hl' := hl.resolve_left hn
  have hh := allocated_ivl_survives_step hAs hAp hgrow hold0 hR0 hog hfr
    hl'.1.1 (by norm_num : 24 % 8 = 0) hl'.2.1
    (fun j hj => (hd hn).2.1 _ (by simp) j hj) hRh
  have ha := logsLiveOwned_array_survives hAs hAp hgS hgrow hl hd hn
    hold0 hR0 hog hfr hRa
  have hb := (R13Shards.ivl_allocated_bound hAs hl'.2.1).2
  have h0 : memW post logs = memW s logs :=
    R13Shards.memW_eq_of_ivlUnhit hh.2.2 hl'.1.1 hb ⟨by omega, by omega⟩
  have h8 : memW post (logs + 8) = memW s (logs + 8) :=
    R13Shards.memW_eq_of_ivlUnhit hh.2.2 (by have := hl'.1.1; omega) hb
      ⟨by omega, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h0, h8]; exact ha.1
  · intro o ho j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact hh.2.1 j hj
    · rw [h0, h8]; exact ha.2.1 j hj
  · intro i hi
    rw [h8] at hi
    rw [h0, ha.2.2 i hi]
    have he := (hl'.2.2.2.2 i hi).2
    have hmem : (memW s (memW s logs + 8 * i), 40) ∈
        logOwnedIvls s (memW s (memW s logs + 8 * i)) := by
      simp [logOwnedIvls, logRecordIvls]
    have hu := (R13Shards.heap_ivl_survives_step hAs hgrow.1 hold0 hR0 hog hfr
      he.1.1 (by norm_num) he.2.1
      (fun j hj => (hd hn).2.2 i hi _ hmem j hj) (hRe i hi)).2.2
    exact logOwnedIvls_disj_survives hAs hAp he hu hsys hog ((hd hn).2.2 i hi)

/-- Discharge all explicit scratch-buffer obligations for live logs at once.
This applies to the account mutation footprint, including the 52-byte sk buffer. -/
theorem logsLiveOwned_scratchStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd S' Nd' : List Nat} {logs : Nat}
    {gs : List (String × Nat × Nat)} (hgs : ScratchSpec gs)
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hgS : GuestInv s) (hgP : GuestInv post)
    (hW : WorldTypedWith s S Nd) (hgrow : AllocatorGrows s post)
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs)
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (hog : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hfr : FrameOutside s post
      (worldOwned s S Nd ++ gs.map (fun e => bufferRegion s (e.1, e.2.2)) ++ [freeGap s])
      (heapFree s)) :
    LogsListOK post logs ∧ LogsLiveOwned post S' Nd' logs := by
  by_cases hn : logs = 0
  · exact ⟨Or.inl hn, fun h => False.elim (h hn)⟩
  have hR0 : ∀ j ∈ gs.map (fun e => bufferRegion s (e.1, e.2.2)),
      j.2 = 0 → j.1 % 8 = 0 := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hj
    exact bufferRegion_zero_aligned s e.1 e.2.2 (by have := (hgs e he).2.2.1; omega)
  have hdisj : ∀ b : Ivl, (∀ j ∈ worldOwned s S Nd, Disj b j) →
      ∀ j ∈ gs.map (fun e => bufferRegion s (e.1, e.2.2)), Disj b j := by
    intro b hb j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hj
    exact heap_ivl_disj_bufferRegion_le hb (e.1, e.2.1) (hgs e he).1
      e.2.2 (hgs e he).2.2.2
  have hh := hdisj (logs, 24) (fun j hj => (hd hn).2.1 _ (by simp) j hj)
  have ha := hdisj (memW s logs, 8 * memW s (logs + 8))
    (fun j hj => (hd hn).2.1 _ (by simp) j hj)
  have he : ∀ i, i < memW s (logs + 8) →
      ∀ j ∈ gs.map (fun e => bufferRegion s (e.1, e.2.2)),
        Disj (memW s (memW s logs + 8 * i), 40) j := by
    intro i hi
    apply hdisj
    intro j hj
    exact (hd hn).2.2 i hi _ (by simp [logOwnedIvls, logRecordIvls]) j hj
  exact ⟨logsLiveOwned_list_survives hAs hAp hgS hgP hgrow hl hd
      (R13Shards.worldOwned_zero_aligned hW) hR0 hog hfr hh ha he,
    logsLiveOwned_survives hAs hAp hgS hgrow hl hd hsys
      (R13Shards.worldOwned_zero_aligned hW) hR0 hog hfr hh ha he⟩

def etherScratchSpec : List (String × Nat × Nat) :=
  [("keccak_pad", 136, 136), ("keccak_st", 200, 200),
   ("mpt_nib_scratch", 64, 64), ("sk_buf", 64, 52)]

theorem etherScratchSpec_ok : ScratchSpec etherScratchSpec := by
  unfold ScratchSpec etherScratchSpec
  decide

/-- Specialize the concrete ether-creation step to an entry typing that owns
the temporary logs. Its exit typing retains both validity and ownership. -/
theorem create_ether_logs {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (hlk : lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs =
      some (body, callee, ret))
    (hW : WorldOK (callEntryStateHOLFinite s callee))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1)
    (S Nd : List Nat) (logs : Nat)
    (hWT : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd)
    (hlogs : LogsListOK (callEntryStateHOLFinite s callee) logs)
    (hown : LogsLiveOwned (callEntryStateHOLFinite s callee) S Nd logs) :
    let post := (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2
    ∃ S' Nd', WorldTypedWith post S' Nd' ∧
      LogsListOK post logs ∧ LogsLiveOwned post S' Nd' logs := by
  let ent := callEntryStateHOLFinite s callee
  let post := (evaluateHOLFiniteState ent body).2
  have hw := funSpec_at_lookup EvmEkFk.wkSc_create_ether s hc vs body callee ret hlk hW hnt hr
  have hR : IvlsDisj (R16WkAcctWs.bufRegions EvmEkFk.acctMutBufs ent)
      (worldTypedIvls ent S Nd) := by
    change IvlsDisj (etherScratchSpec.map (fun e => bufferRegion ent (e.1, e.2.2))) _
    intro i hi j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hgb, hnu, _, hle⟩ := etherScratchSpec_ok e he
    exact bufferRegion_disj_le hWT (e.1, e.2.1) hgb hnu e.2.2 hle j hj
  obtain ⟨S', Nd', _, hWT', hog, hfr, _⟩ := hw.1.2.2.2.2 S Nd hWT hR
  have hsys : globN post "vm_system_address" = globN ent "vm_system_address" :=
    R16Shards.globN_eq_of_lookup (hw.1.2.2.1 (ofString "vm_system_address") (by decide))
  have hp := logsLiveOwned_scratchStep etherScratchSpec_ok hW.1.2 hw.1.1.2
    hW.1.1 hw.1.1.1 hWT ⟨hw.1.2.1, hw.2⟩ hlogs hown hsys hog hfr
  exact ⟨S', Nd', hWT', hp⟩

/-- Caller-facing form, usable at either Phase-4 ether call: restore caller
locals while retaining the same live-log pointer and its receipt guard. -/
theorem create_ether_logs_resume {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hlk : lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (hW : WorldOK s) (S Nd : List Nat) (logs : Nat)
    (hWT : WorldTypedWith s S Nd) (hlogs : LogsListOK s logs)
    (hown : LogsLiveOwned s S Nd logs) :
    ∃ S' Nd', WorldTypedWith { post with locals := s.locals } S' Nd' ∧
      LogsListOK { post with locals := s.locals } logs ∧
      LogsLiveOwned { post with locals := s.locals } S' Nd' logs ∧
      LogsDisjFixed { post with locals := s.locals } logs := by
  have hWTc := (R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hWT
  have hLc := (R13Shards.logsListOK_with_locals s callee (s.clock - 1) logs).mpr hlogs
  have hp := create_ether_logs s vs body callee ret hc hlk
    (worldOK_callEntry hW callee) (by rw [hb]; simp)
    (by rw [hb]; exact Or.inl ⟨v, rfl⟩) S Nd logs hWTc hLc hown
  rw [hb] at hp
  obtain ⟨S', Nd', hWT', hL', hO'⟩ := hp
  have hOr : LogsLiveOwned { post with locals := s.locals } S' Nd' logs := hO'
  exact ⟨S', Nd',
    (R13Shards.worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hWT',
    (R13Shards.logsListOK_with_locals post s.locals post.clock logs).mpr hL',
    hOr, logsLiveOwned_disjFixed hOr⟩

/-- Changing only the caller locals transports the strong post-message cut. -/
theorem txAfterCallStrong_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hi : locals.lookup (ofString "index") = s.locals.lookup (ofString "index"))
    (ho : locals.lookup (ofString "out") = s.locals.lookup (ofString "out"))
    (h : TxAfterCallStrong s) :
    TxAfterCallStrong { s with locals := locals, clock := k } := by
  have hout := locN_congr s locals k "out" ho
  obtain ⟨hW, hw, hin, hl, S, Nd, hWT, hd, hown⟩ := h
  refine ⟨⟨localsFree_worldOK s locals k hW.1,
    txEnv_with_locals s locals k hi hW.2⟩, ?_, ?_, ?_, S, Nd,
    (R13Shards.worldTypedWith_with_locals s locals k S Nd).mpr hWT, ?_, ?_⟩
  · change WordsOK s (locN { s with locals := locals, clock := k } "out", 96)
    rw [hout]; exact hw
  · change Inside (locN { s with locals := locals, clock := k } "out", 96)
      sourceBase (globN s "heap_ptr")
    rw [hout]; exact hin
  · rw [hout]
    exact (R13Shards.logsListOK_with_locals s locals k _).mpr hl
  · change IvlsDisj [(locN { s with locals := locals, clock := k } "out", 96)]
      (worldOwned s S Nd)
    rw [hout]; exact hd
  · change LogsLiveOwned s S Nd
      (memW s (locN { s with locals := locals, clock := k } "out" + 16))
    rw [hout]; exact hown

theorem localsOnly_txAfterCallStrong : LocalsOnly ["index", "out"] TxAfterCallStrong := by
  intro F s locals k hl h
  exact txAfterCallStrong_with_locals s locals k
    (hl "index" (by simp)) (hl "out" (by simp)) h

/-- A scratch-buffer world step preserves the complete output record and its
live logs under one common exit world typing. -/
theorem txAfterCallStrong_scratchStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hstep : WorldStep R gw keep Q s r post) (h : TxAfterCallStrong s)
    (hgrow : AllocatorGrows s post)
    {gs : List (String × Nat × Nat)} (hgs : ScratchSpec gs)
    (hR : R s = gs.map (fun e => bufferRegion s (e.1, e.2.2)))
    (hbo : ofString "bo" ∉ gw.map ofString)
    (hjcap : ofString "journal_cap" ∉ gw.map ofString)
    (hsys : ofString "vm_system_address" ∉ gw.map ofString)
    (hkeep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep) :
    TxAfterCallStrong { post with locals := s.locals } := by
  obtain ⟨hW, hw, hin, hl, S, Nd, hWT, hd, hown⟩ := h
  have hRdisj : IvlsDisj (R s) (worldTypedIvls s S Nd) := by
    rw [hR]
    intro i hi j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact bufferRegion_disj_le hWT (e.1, e.2.1) (hgs e he).1
      (hgs e he).2.1 e.2.2 (hgs e he).2.2.2 j hj
  obtain ⟨S', Nd', _, hWT', hog, hfr, _⟩ := hstep.2.2.2.2 S Nd hWT hRdisj
  have hR0 : ∀ i ∈ R s, i.2 = 0 → i.1 % 8 = 0 := by
    rw [hR]
    intro i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact bufferRegion_zero_aligned s e.1 e.2.2
      (by have := (hgs e he).2.2.1; omega)
  have hRout : ∀ i ∈ R s, Disj (locN s "out", 96) i := by
    rw [hR]
    intro i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact heap_ivl_disj_bufferRegion_le (fun j hj => hd _ (by simp) j hj)
      (e.1, e.2.1) (hgs e he).1 e.2.2 (hgs e he).2.2.2
  obtain ⟨hin', hd', hu⟩ := R13Shards.heap_ivl_survives_step hW.1.1.2 hgrow.1
    (R13Shards.worldOwned_zero_aligned hWT) hR0 hog hfr hw.1 (by norm_num)
    hin (fun j hj => hd _ (by simp) j hj) hRout
  have hout16 : memW post (locN s "out" + 16) = memW s (locN s "out" + 16) :=
    memW_eq_of_ivlUnhit hu (by have := hw.1; omega)
      (ivl_allocated_bound hW.1.1.2 (Or.inl hin)).2 ⟨by omega, by omega⟩
  have hsysEq : globN post "vm_system_address" = globN s "vm_system_address" :=
    R16Shards.globN_eq_of_lookup (hstep.2.2.1 _ hsys)
  have hfr' : FrameOutside s post
      (worldOwned s S Nd ++ gs.map (fun e => bufferRegion s (e.1, e.2.2)) ++ [freeGap s])
      (heapFree s) := by simpa only [hR] using hfr
  have hlogs := logsLiveOwned_scratchStep hgs hW.1.1.2 hstep.1.2
    hW.1.1.1 hstep.1.1 hWT hgrow hl hown hsysEq hog hfr'
  have hRbo : ∀ i ∈ R s, Disj i (globN s "bo", 88) :=
    fun i hi => hRdisj i hi _ (bo_mem_typed hW.2.bo_nz)
  have hE := txEnv_preserved_by_worldStep hstep hbo hjcap hkeep hoffs hRbo
    (bo_words hWT.2.2.1 hW.2.bo_nz).2.1 hR0 hW.2 rfl
  refine ⟨⟨worldOK_of_parts
    ((arenaReady_with_locals post s.locals post.clock).mpr hstep.1)
    ((R13Shards.worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hWT'),
    hE⟩, ?_, hin', ?_, S', Nd',
    (R13Shards.worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hWT',
    ?_, ?_⟩
  · exact wordsOK_transfer hW.1.1.1 hstep.1.1 hw
  · change LogsListOK { post with locals := s.locals } (memW post (locN s "out" + 16))
    rw [hout16]
    exact (R13Shards.logsListOK_with_locals post s.locals post.clock _).mpr hlogs.1
  · intro i hi j hj
    simp only [List.mem_singleton] at hi
    subst i
    exact hd' j hj
  · change LogsLiveOwned post S' Nd' (memW post (locN s "out" + 16))
    rw [hout16]; exact hlogs.2

/-- Heap-only world steps preserve the output record and its live logs. -/
theorem txAfterCallStrong_heapStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] Q s r post)
    (h : TxAfterCallStrong s) : TxAfterCallStrong { post with locals := s.locals } := by
  have hsc : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  exact txAfterCallStrong_scratchStep
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    hs h ⟨hs.2.1, by omega⟩ (gs := []) (by intro e he; cases he)
    rfl (by decide) (by decide) (by decide) (by simp)
    (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)

/-- Both ether credits retain the output record and its live logs. -/
theorem create_ether_txAfterCallStrong_resume {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (h : TxAfterCallStrong s) :
    TxAfterCallStrong { post with locals := s.locals } := by
  have hw := funSpec_at_lookup EvmEkFk.wkSc_create_ether s hc vs body callee ret hl
    (worldOK_callEntry h.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hs' := R13Shards.worldStep_with_locals hs.1 s.locals s.clock
  exact txAfterCallStrong_scratchStep
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    hs' h ⟨hs.1.2.1, hs.2⟩ etherScratchSpec_ok
    rfl (by decide) (by decide) (by decide) (by simp)
    (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)

theorem lst_new_txAfterCallStrong_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : TxAfterCallStrong s) :
    TxAfterCallStrong (setVarHOLFinite (ofString "logs") v
      { post with locals := s.locals }) := by
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  exact LocalsOnly.setVar localsOnly_txAfterCallStrong (by decide) v _
    (txAfterCallStrong_heapStep hs' hp)

theorem hoare_create_ether_txAfterCallStrong (args : List (ExpHOL 64)) :
    Hoare TxAfterCallStrong (.call (some (none, none)) (ofString "create_ether") args)
      (fun r t => r = none → TxAfterCallStrong t) := by
  apply R13Shards.Hoare.call0_resume
  intro F s vs body callee ret v post hc hp _ hl hb
  exact create_ether_txAfterCallStrong_resume s vs body callee ret v post hc hl hb hp

theorem resume_ro_txAfterCallStrong {fname name : MlS}
    (hro : ReadOnlyFn fname)
    (hne : ∀ k ∈ (["index", "out"] : List String), ofString k ≠ name)
    (args : List (ExpHOL 64)) :
    DecCallResumeOn TxAfterCallStrong TxAfterCallStrong name fname args := by
  intro F s vs body callee ret v post hc hp _ hl hb
  have hs := funSpec_at_lookup hro s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hs
  have he := hs (Or.inl ⟨v, rfl⟩)
  dsimp only at he
  have he' : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with clock := post.clock } := by rw [he]; rfl
  apply LocalsOnly.setVar localsOnly_txAfterCallStrong hne v
  rw [he']
  exact txAfterCallStrong_with_locals s s.locals post.clock rfl rfl hp

theorem txAfterCallStrong_guest_entry (fn : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn TxAfterCallStrong GuestInv fn args := by
  intro F s vs body callee ret hc hp ha hl
  exact guestInv_callEntry s callee hp.1.1.1.1

/-- The refund arithmetic and both ether credits, before updating block totals. -/
def phase4CreditPrefix (tail : ProgHOL 64) : ProgHOL 64 :=
  spinePlug 11 (spineAt 99 ptxCode) tail

def phase4CreditCost : Nat :=
  (K.udiv_small5 + 1) + (K.min + 1) + (K.max + 1) +
  (K.fee_mul + 1) + (K.u256_sub + 1) + (K.fee_mul + 1) +
  (K.create_ether + 1) + (K.create_ether + 1)

theorem phase4CreditPrefix_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong (phase4CreditPrefix tail)
      (phase4CreditCost + b) := by
  have hb : TerminatingProgBoundedOn TxAfterCallStrong (phase4CreditPrefix tail)
      (K.udiv_small5 + (K.min + (K.max + (K.fee_mul +
        (K.u256_sub + (K.fee_mul + ((K.create_ether + 1) +
          ((K.create_ether + 1) + b)) + 1) + 1) + 1) + 1) + 1) + 1) := by
    unfold phase4CreditPrefix ptxCode
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_udiv_small5 _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_udiv_small5 (by decide) _) ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_min _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_min (by decide) _) ?_
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_max _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_max (by decide) _) ?_
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_fee_mul _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_fee_mul (by decide) _) ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_u256_sub _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_u256_sub (by decide) _) ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_fee_mul _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_fee_mul (by decide) _) ?_
    refine seq_bound_trans ?_ (hoare_create_ether_txAfterCallStrong _) ?_
    · exact bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_create_ether none _)
        (fun s hp => hp.1.1.1.1)
    refine seq_bound_trans ?_ (hoare_create_ether_txAfterCallStrong _) htail
    exact bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_create_ether none _)
      (fun s hp => hp.1.1.1.1)
  have he : K.udiv_small5 + (K.min + (K.max + (K.fee_mul +
        (K.u256_sub + (K.fee_mul + ((K.create_ether + 1) +
          ((K.create_ether + 1) + b)) + 1) + 1) + 1) + 1) + 1) + 1 =
      phase4CreditCost + b := by unfold phase4CreditCost; omega
  rw [he] at hb
  intro F s hc hp
  exact hb s hc hp

/-- A single write inside world storage cannot change an owned live log list. -/
theorem logsLiveOwned_single_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} {x : BitVec 64}
    {mem' : BitVec 64 → HolWordLab 64}
    (hA : ArenaOK s) (hg : GuestInv s) (hgp : GuestInv {s with memory := mem'})
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs)
    (hm : ∀ a, a ≠ x → mem' a = s.memory a)
    (hwrite : ∃ o ∈ worldOwned s S Nd, Inside (x.toNat, 8) o.1 (o.1 + o.2))
    (howned : worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd) :
    LogsListOK {s with memory := mem'} logs ∧
      LogsLiveOwned {s with memory := mem'} S Nd logs := by
  let post := {s with memory := mem'}
  by_cases hn : logs = 0
  · exact ⟨Or.inl hn, fun h => False.elim (h hn)⟩
  have hl' := hl.resolve_left hn
  obtain ⟨o, ho, hin⟩ := hwrite
  have hdisj : ∀ b, (∀ j ∈ worldOwned s S Nd, Disj b j) → Disj b (x.toNat, 8) :=
    fun b hb => disj_of_inside_right hin (hb o ho)
  have hh : IvlUnhit s post (logs, 24) :=
    ivlUnhit_single hm (by simp) (hdisj _ (fun j hj => (hd hn).2.1 _ (by simp) j hj))
  have hb := (ivl_allocated_bound hA hl'.2.1).2
  have h0 : memW post logs = memW s logs :=
    memW_eq_of_ivlUnhit hh hl'.1.1 hb ⟨by omega, by omega⟩
  have h8 : memW post (logs + 8) = memW s (logs + 8) :=
    memW_eq_of_ivlUnhit hh (by have := hl'.1.1; omega) hb ⟨by omega, by omega⟩
  have hp : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
    intro i hi
    have ha := logsListOK_array_aligned hg hl hn (by omega)
    have hu : IvlUnhit s post (memW s logs, 8 * memW s (logs + 8)) :=
      ivlUnhit_single hm (fun _ => ha)
        (hdisj _ (fun j hj => (hd hn).2.1 _ (by simp) j hj))
    exact memW_eq_of_ivlUnhit hu (by omega)
      (ivl_allocated_bound hA (hd hn).1).2 ⟨by dsimp; omega, by dsimp; omega⟩
  have he : ∀ i, i < memW s (logs + 8) →
      IvlUnhit s post (memW s (memW s logs + 8 * i), 40) := by
    intro i hi
    exact ivlUnhit_single hm (by simp)
      (hdisj _ (fun j hj => (hd hn).2.2 i hi _ (by simp [logOwnedIvls, logRecordIvls]) j hj))
  refine ⟨logsListOK_congr_header_unhit hA hg hgp (by rfl) hl
    (fun h => h) hh hp he, ?_⟩
  intro _
  change Allocated post (memW post logs, 8 * memW post (logs + 8)) ∧ _
  rw [h0, h8]
  refine ⟨(hd hn).1, ?_, ?_⟩
  · change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]
    exact (hd hn).2.1
  · intro i hi
    rw [hp i hi]
    rw [logOwnedIvls_eq_of_unhit hA (hl'.2.2.2.2 i hi).2 (he i hi) rfl]
    change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]
    exact (hd hn).2.2 i hi

/-- The four block-total cells are untyped and disjoint from the output/logs. -/
theorem txAfterCallStrong_store_bo {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxAfterCallStrong s) {off : Nat} (hoff : off ∈ ([0, 8, 16, 48] : List Nat))
    {x : BitVec 64} (hx : s.memaddrs x) (hxe : x.toNat = globN s "bo" + off)
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    TxAfterCallStrong {s with memory := mem'} := by
  obtain ⟨hW, hw, hin, hl, S, Nd, hWT, hd, hown⟩ := h
  let post := {s with memory := mem'}
  have hg : GuestInv post := guestInv_congr (s := s) rfl rfl rfl rfl hW.1.1.1
  obtain ⟨hWT', howned, hE⟩ := store_bo_untyped_world hW.1.1 hW.2 hWT hoff hx hxe hm
  have hbo : (globN s "bo", 88) ∈ worldOwned s S Nd :=
    R13Shards.worldTypedIvls_sub_worldOwned (bo_mem_typed hW.2.bo_nz)
  have hix : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    unfold Inside
    dsimp
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  have hu : IvlUnhit s post (locN s "out", 96) :=
    ivlUnhit_single hm (by simp)
      (disj_of_inside_right hix (hd _ (by simp) _ hbo))
  have h16 : memW post (locN s "out" + 16) = memW s (locN s "out" + 16) :=
    memW_eq_of_ivlUnhit hu (by have := hw.1; omega)
      (ivl_allocated_bound hW.1.1.2 (Or.inl hin)).2 ⟨by omega, by omega⟩
  have hlogs := logsLiveOwned_single_store hW.1.1.2 hW.1.1.1 hg hl hown hm
    ⟨_, hbo, hix⟩ howned
  refine ⟨⟨worldOK_of_parts ⟨hg, hW.1.1.2⟩ hWT', hE⟩,
    wordsOK_transfer hW.1.1.1 hg hw, hin, ?_, S, Nd, hWT', ?_, ?_⟩
  · change LogsListOK post (memW post (locN s "out" + 16))
    rw [h16]; exact hlogs.1
  · change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]; exact hd
  · change LogsLiveOwned post S Nd (memW post (locN s "out" + 16))
    rw [h16]; exact hlogs.2

/-- An owned-world write that preserves world typing also preserves the output. -/
theorem txAfterCallStrong_worldStore {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxAfterCallStrong s) {x : BitVec 64}
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a)
    (hpres : ∀ S Nd, WorldTypedWith s S Nd →
      WorldTypedWith {s with memory := mem'} S Nd ∧
      worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
      TxEnv {s with memory := mem'})
    (hx : ∀ S Nd, WorldTypedWith s S Nd →
      ∃ i ∈ worldOwned s S Nd, Inside (x.toNat, 8) i.1 (i.1 + i.2)) :
    TxAfterCallStrong {s with memory := mem'} := by
  obtain ⟨hW, hw, hin, hl, S, Nd, hWT, hd, hown⟩ := h
  let post := {s with memory := mem'}
  have hg : GuestInv post := guestInv_congr (s := s) rfl rfl rfl rfl hW.1.1.1
  obtain ⟨hWT', howned, hE⟩ := hpres S Nd hWT
  obtain ⟨i, hi, hix⟩ := hx S Nd hWT
  have hu : IvlUnhit s post (locN s "out", 96) :=
    ivlUnhit_single hm (by simp)
      (disj_of_inside_right hix (hd _ (by simp) _ hi))
  have h16 : memW post (locN s "out" + 16) = memW s (locN s "out" + 16) :=
    memW_eq_of_ivlUnhit hu (by have := hw.1; omega)
      (ivl_allocated_bound hW.1.1.2 (Or.inl hin)).2 ⟨by omega, by omega⟩
  have hlogs := logsLiveOwned_single_store hW.1.1.2 hW.1.1.1 hg hl hown hm
    ⟨i, hi, hix⟩ howned
  refine ⟨⟨worldOK_of_parts ⟨hg, hW.1.1.2⟩ hWT', hE⟩,
    wordsOK_transfer hW.1.1.1 hg hw, hin, ?_, S, Nd, hWT', ?_, ?_⟩
  · change LogsListOK post (memW post (locN s "out" + 16))
    rw [h16]; exact hlogs.1
  · change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]; exact hd
  · change LogsLiveOwned post S Nd (memW post (locN s "out" + 16))
    rw [h16]; exact hlogs.2

theorem txAfterCallStrong_store_receipt {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxAfterCallStrong s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (memW s (globN s "bo" + 32))
      (memW s (globN s "bo" + 32) + (16 * memW s (globN s "bo" + 80) + 16)))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    TxAfterCallStrong {s with memory := mem'} := by
  apply txAfterCallStrong_worldStore h hm
  · intro S Nd hWT
    exact store_bo_array_world h.1.1.1 h.1.2 hWT (Or.inl ⟨rfl, rfl⟩) hx hin hm
  · intro S Nd hWT
    obtain ⟨_, _, hbo⟩ := blockOutObjects_eq_list h.1.2 hWT.1
    refine ⟨(memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16), ?_, hin⟩
    have hmemb : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
        ∈ blockOutObjects s := by rw [hbo]; simp
    have hmemf : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
        ∈ fixedObjects s := List.mem_append_left _ (List.mem_append_right _ hmemb)
    unfold worldOwned
    simp only [List.mem_append]
    exact Or.inl (Or.inr hmemf)

theorem eval_add_global_const {F : Type} {s : PanSemStateFiniteExact 64 F}
    {g : String} {k x : BitVec 64}
    (hx : evalAt s (.op .add [.var .global (ofString g), .const k]) = some (.val (.word x))) :
    x.toNat = (globN s g + k.toNat) % 2 ^ 64 := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hx
  rcases hg : s.globals.lookup (ofString g) with _ | vg
  · simp [hg] at hx
  · rcases vg with wg | _ | _
    · cases wg with
      | word gw =>
        simp only [hg, valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map,
          Option.map, Bool.and_self, ↓reduceIte, List.foldr, Option.some.injEq,
          ValueHOL.val.injEq, HolWordLab.word.injEq] at hx
        have hgn : globN s g = gw.toNat := by simp [globN, hg]
        have hx' : x = gw + (k + 0) := hx.symm
        have hz0 : (0 : BitVec 64).toNat = 0 := by decide
        rw [hx', BitVec.toNat_add, BitVec.toNat_add, hz0, Nat.add_zero, Nat.add_mod_mod, hgn]
    · simp [hg, valueIsWord] at hx
    · simp [hg, valueIsWord] at hx

theorem hoare_store_bo_total (off : Nat) (hoff : off ∈ ([0, 8, 16, 48] : List Nat))
    (op : BinOp) (args : List (ExpHOL 64)) :
    Hoare TxAfterCallStrong
      (.store (.op .add [.var .global (ofString "bo"), .const (BitVec.ofNat 64 off)])
        (.op op args)) (fun r t => r = none → TxAfterCallStrong t) := by
  apply R13Shards.Hoare.store_fall
  intro F s x v mem' h hx hv hm
  obtain ⟨w, rfl⟩ := PtxP1.eval_is_word_op hv
  have hs := panMemStoresHOL_word_spec (s := s) (x := x) (w := .word w)
    (mem' := mem') (by simpa only [flattenHOL] using hm)
  apply txAfterCallStrong_store_bo h hoff hs.1 _ hs.2.2
  have he := eval_add_global_const hx
  obtain ⟨S, Nd, hWT, _⟩ := h.2.2.2.2
  have hb := (ivl_allocated_bound h.1.1.1.2
    (bo_words hWT.2.2.1 h.1.2.bo_nz).1).2
  have hoff64 : off < 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;> norm_num
  have hsum : globN s "bo" + off < 2 ^ 64 := by
    dsimp at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hsum] using he

/-- The four consecutive block-total writes preserve the strong cut at zero cost. -/
theorem phase4TotalStores_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 5 (spineAt 114 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 5 (spineAt 114 ptxCode) tail) (0 + (0 + (0 + (0 + b)))) := by
    unfold ptxCode
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total 0 (by simp) _ _) ?_
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total 8 (by simp) _ _) ?_
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total 48 (by simp) _ _) ?_
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total 16 (by simp) _ _) ?_
    change TerminatingProgBoundedOn TxAfterCallStrong (.seq .skip tail) b
    intro F s hc hp hnt
    simpa only [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] using
      htail s hc hp (by simpa only [evaluateHOLFiniteState_seq_line780,
        evaluateHOLFiniteState_skip] using hnt)
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

/-- State-gas normalization, regular-gas computation, and all block totals. -/
theorem phase4Totals_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 9 (spineAt 110 ptxCode) tail) (K.max + b + 1) := by
  have hb : TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 9 (spineAt 110 ptxCode) tail) (0 + (K.max + b + 1)) := by
    unfold ptxCode
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallStrong _ (by decide) _ _ ?_
    refine seq_bound_trans (Q := TxAfterCallStrong) ?_ ?_ ?_
    · exact TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _))
        (TerminatingProgBoundedOn.of_clock clock_skip)
    · apply Hoare.ite
      · apply Hoare.mono (P' := TxAfterCallStrong) _ (fun _ hp => hp.1)
        exact Hoare.assign
          (fun s v hp _ _ => LocalsOnly.setVar localsOnly_txAfterCallStrong
            (name := ofString "tx_state_gas_nat") (by decide) v s hp)
          (fun _ _ hr => absurd hr (by simp))
      · exact Hoare.skip (fun _ hp _ => hp.1)
      · exact fun _ _ hr => absurd hr (by simp)
    · refine TerminatingProgBoundedOn.decCall_on h.fb_max _ _ _
        (txAfterCallStrong_guest_entry _ _)
        (resume_ro_txAfterCallStrong h.ro_max (by decide) _) ?_
      have hh := @phase4TotalStores_cut tail b htail
      unfold ptxCode at hh
      intro F s hc hp
      exact hh s hc hp
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

/-- The first twenty Phase-4 steps preserve the complete output/log invariant. -/
theorem phase4CreditTotals_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 20 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + b) := by
  have hb := @phase4CreditPrefix_cut h _ _ (phase4Totals_cut h htail)
  have he : spinePlug 20 (spineAt 99 ptxCode) tail =
      phase4CreditPrefix (spinePlug 9 (spineAt 110 ptxCode) tail) := by
    unfold phase4CreditPrefix ptxCode
    rfl
  rw [he]
  intro F s hc hp
  have hr := hb s hc hp
  convert hr using 1 <;> omega

/-- Empty constructor results need no backing-array cell or log-entry reads. -/
theorem logsListOK_empty {F : Type} {s : PanSemStateFiniteExact 64 F}
    {logs : Nat} (hw : WordsOK s (logs, 24)) (ha : Allocated s (logs, 24))
    (hn : memW s (logs + 8) = 0) : LogsListOK s logs := by
  refine Or.inr ⟨hw, ha, ?_, ?_, ?_⟩
  · rw [hn]; norm_num
  · rw [hn]; exact Nat.zero_le _
  · intro i hi
    rw [hn] at hi
    omega

/-- Separation of an empty list only needs its header; the live array is empty. -/
theorem logsLiveOwned_empty {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat}
    (ha : Allocated s (memW s logs, 0))
    (hd : ∀ j ∈ worldOwned s S Nd, Disj (logs, 24) j)
    (hn : memW s (logs + 8) = 0) : LogsLiveOwned s S Nd logs := by
  intro _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hn, Nat.mul_zero] using ha
  · intro i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hd j hj
    · exact Or.inl (by simp [hn])
  · intro i hi
    rw [hn] at hi
    omega

/-- The two fresh blocks returned by `lst_new(8,1)` establish the receipt guard. -/
theorem fresh_empty_logs {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} (hA : ArenaOK s)
    (hh : FreshBlock s post logs 24)
    (hb : FreshBlock s post (memW post logs) 8)
    (hd : IvlsDisj [(logs, 24), (memW post logs, 8)] (worldOwned post S Nd))
    (hn : memW post (logs + 8) = 0) :
    LogsListOK post logs ∧ LogsLiveOwned post S Nd logs ∧ LogsDisjFixed post logs := by
  have hhi : Inside (logs, 24) sourceBase (globN post "heap_ptr") := by
    have h := hh.2.1
    change Inside (logs, 24) (globN s "heap_ptr") (globN post "heap_ptr") at h
    exact ⟨hA.1.trans h.1, h.2⟩
  have hbi : Inside (memW post logs, 0) sourceBase (globN post "heap_ptr") := by
    have h := hb.2.1
    change Inside (memW post logs, 8) (globN s "heap_ptr") (globN post "heap_ptr") at h
    constructor
    · exact hA.1.trans h.1
    · have := h.2; dsimp at this ⊢; omega
  have ho := logsLiveOwned_empty (S := S) (Nd := Nd) (Or.inl hbi)
    (fun j hj => hd _ (by simp) j hj) hn
  exact ⟨logsListOK_empty hh.2.2 (Or.inl hhi) hn, ho, logsLiveOwned_disjFixed ho⟩

/-- An explicit world typing witnesses ownership of the selected local log list. -/
def LogsWorldOwned {F : Type} (s : PanSemStateFiniteExact 64 F) (logs : Nat) : Prop :=
  ∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd logs

theorem logsWorldOwned_with_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) {logs : Nat}
    (h : LogsWorldOwned s logs) : LogsWorldOwned {s with locals := locals, clock := k} logs := by
  obtain ⟨S, Nd, hw, ho⟩ := h
  exact ⟨S, Nd, (R13Shards.worldTypedWith_with_locals s locals k S Nd).mpr hw, ho⟩

theorem logsWorldOwned_scratchStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hs : WorldStep R gw keep Q s r post) (hA : ArenaReady s)
    (hgrow : AllocatorGrows s post) (hl : LogsListOK s logs)
    (ho : LogsWorldOwned s logs)
    {gs : List (String × Nat × Nat)} (hgs : ScratchSpec gs)
    (hR : R s = gs.map (fun e => bufferRegion s (e.1, e.2.2)))
    (hsys : ofString "vm_system_address" ∉ gw.map ofString) :
    LogsListOK post logs ∧ LogsWorldOwned post logs := by
  obtain ⟨S, Nd, hWT, hd⟩ := ho
  have hRd : IvlsDisj (R s) (worldTypedIvls s S Nd) := by
    rw [hR]
    intro i hi j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact bufferRegion_disj_le hWT (e.1, e.2.1) (hgs e he).1
      (hgs e he).2.1 e.2.2 (hgs e he).2.2.2 j hj
  obtain ⟨S', Nd', _, hWT', hog, hfr, _⟩ := hs.2.2.2.2 S Nd hWT hRd
  have hfr' : FrameOutside s post
      (worldOwned s S Nd ++ gs.map (fun e => bufferRegion s (e.1, e.2.2)) ++ [freeGap s])
      (heapFree s) := by simpa only [hR] using hfr
  have hp := logsLiveOwned_scratchStep hgs hA.2 hs.1.2 hA.1 hs.1.1
    hWT hgrow hl hd (R16Shards.globN_eq_of_lookup (hs.2.2.1 _ hsys)) hog hfr'
  exact ⟨hp.1, S', Nd', hWT', hp.2⟩

theorem logsWorldOwned_heapStep_header {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {keep : List (String × List Nat)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"] keep Q s r post)
    (hA : ArenaReady s) (hl : LogsListOK s logs) (ho : LogsWorldOwned s logs)
    (hn : logs ≠ 0) :
    memW post logs = memW s logs ∧ memW post (logs + 8) = memW s (logs + 8) := by
  obtain ⟨S, Nd, hWT, hd⟩ := ho
  have hgrow : AllocatorGrows s post := ⟨hs.2.1, by
    have he : globN post "scratch_ptr" = globN s "scratch_ptr" :=
      R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
    omega⟩
  obtain ⟨S', Nd', _, _, hog, hfr, _⟩ := hs.2.2.2.2 S Nd hWT (by intro i hi; cases hi)
  have hl' := hl.resolve_left hn
  have hh := allocated_ivl_survives_step hA.2 hs.1.2 hgrow
    (worldOwned_zero_aligned hWT) (by intro j hj; cases hj) hog hfr
    hl'.1.1 (by norm_num : 24 % 8 = 0) hl'.2.1
    (fun j hj => (hd hn).2.1 _ (by simp) j hj) (by intro j hj; cases hj)
  have hb := (ivl_allocated_bound hA.2 hl'.2.1).2
  exact ⟨memW_eq_of_ivlUnhit hh.2.2 hl'.1.1 hb ⟨by omega, by omega⟩,
    memW_eq_of_ivlUnhit hh.2.2 (by have := hl'.1.1; omega) hb ⟨by omega, by omega⟩⟩

def Phase4ReceiptReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxAfterCallStrong s ∧ LogsListOK s (locN s "logs") ∧
    LogsDisjFixed s (locN s "logs") ∧ LogsWorldOwned s (locN s "logs")

theorem lst_new_receiptReady_resume (h : PtxCallees) :
    DecCallResumeOn TxAfterCallStrong Phase4ReceiptReady (ofString "logs")
      (ofString "lst_new") [.const 8, .const 1] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hlc := R13Shards.lookup_lst_new
  rw [← hc] at hlc
  obtain ⟨_, he, hcap⟩ := callee_param_two_exp s (ofString "lst_new")
    (ofString "esz") (ofString "cap") .one .one _ _ hlc
    (.const 8) (.const 1) (.val (.word 8)) (.val (.word 1))
    vs body callee ret rfl rfl ha hl
  let ent := callEntryStateHOLFinite s callee
  have he8 : locN ent "esz" = 8 := by simp [ent, locN, callEntryStateHOLFinite, he]
  have hc4 : locN ent "cap" = 1 := by simp [ent, locN, callEntryStateHOLFinite, hcap]
  have hmul : locN ent "esz" * locN ent "cap" < 2 ^ 64 := by rw [he8, hc4]; norm_num
  have hpos : 1 ≤ locN ent "cap" := by omega
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hWT, _, _⟩ := hp.2.2.2.2
  have hWTc := (R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hWT
  obtain ⟨S', Nd', _, hWT', _, _, hret⟩ := hs.2.2.2.2 S Nd hWTc
    (by intro i hi; cases hi)
  obtain ⟨w, hv, hd⟩ := hret hmul v rfl
  have ht := funSpec_at_lookup h.rt_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1 callee).1 (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨w', hv', _, _, hf⟩ := ht v rfl
  have heq : w' = w := by rw [hv] at hv'; cases hv'; rfl
  subst w'
  obtain ⟨hh, hb, _, hn, _⟩ := hf hmul hpos
  have hb32 : FreshBlock ent post (memW post w.toNat) 8 := by
    change FreshBlock ent post (memW post w.toNat) (locN ent "esz" * locN ent "cap") at hb
    simpa only [he8, hc4] using hb
  have hd32 : IvlsDisj [(w.toNat, 24), (memW post w.toNat, 8)]
      (worldOwned post S' Nd') := by
    change IvlsDisj [(w.toNat, 24), (memW post w.toNat, locN ent "esz" * locN ent "cap")]
      (worldOwned post S' Nd') at hd
    simpa only [he8, hc4] using hd
  obtain ⟨hL, hO, hD⟩ := fresh_empty_logs (s := ent) hp.1.1.1.2 hh hb32 hd32 hn
  have hout := lst_new_txAfterCallStrong_resume h s vs body callee ret v post hc hl hr hp
  refine ⟨hout, ?_, ?_, ?_⟩
  all_goals rw [hv]; simp only [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, if_pos rfl]
  · exact (R13Shards.logsListOK_with_locals post _ post.clock w.toNat).mpr hL
  · exact hD
  · exact logsWorldOwned_with_locals _ _ ⟨S', Nd', hWT', hO⟩

def Phase4LogsReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxAfterCallStrong s ∧
    locN s "logs" = memW s (locN s "out" + 16) ∧
    LogsListOK s (locN s "logs") ∧ LogsDisjFixed s (locN s "logs")

theorem evalAt_load_local {F : Type} (t : PanSemStateFiniteExact 64 F)
    (l : String) (k : BitVec 64) (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString l), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t ((locN t l + k.toNat) % 2 ^ 64) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hl : t.locals.lookup (ofString l) with _ | w
  · simp [hl] at h
  · rcases w with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        rcases hm : t.memory (x + k) with ⟨y⟩
        refine ⟨y, by rw [← h.2, hm], ?_⟩
        have hadd : BitVec.ofNat 64 ((x.toNat + k.toNat) % 2 ^ 64) = x + k := by
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add]
        simp only [locN, memW, hl, hadd, h.2, hm]
    · simp [hl, valueIsWord] at h
    · simp [hl, valueIsWord] at h

theorem evalAt_load_local_nonzero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hg : GuestInv s) (l : String) (v : ValueHOL 64)
    (he : evalAt s (.load .one (.op .add [.var .local (ofString l), .const 8])) = some v) :
    locN s l ≠ 0 := by
  intro hz
  rcases hlu : s.locals.lookup (ofString l) with _ | val
  · simp [evalAt, evalHOLExact, evalListHOLExact, hlu] at he
  rcases val with w | fs | ⟨nm, fs⟩
  · cases w with
    | word w =>
      have hw : w.toNat = 0 := by simpa [locN, hlu] using hz
      have hw0 : w = 0 := BitVec.eq_of_toNat_eq hw
      subst w
      have hdom : ¬ s.memaddrs (8 : BitVec 64) := by
        rw [hg.memaddrs]
        intro hd
        have hb := ((ordinaryDomain_iff (8 : BitVec 64)).mp hd).2.1
        change sourceBase ≤ 8 at hb
        norm_num [sourceBase] at hb
      simp [evalAt, evalHOLExact, evalListHOLExact, hlu, valueIsWord, valueWord,
        wordOpHOL, wordOp, memLoadHOLExact, hdom] at he
      exact hdom he.1
  · simp [evalAt, evalHOLExact, evalListHOLExact, hlu, valueIsWord] at he
  · simp [evalAt, evalHOLExact, evalListHOLExact, hlu, valueIsWord] at he

theorem phase4LogsReady_load {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (h : TxAfterCallStrong s)
    (he : evalAt s (.load .one (.op .add [.var .local (ofString "out"), .const 16])) = some v) :
    Phase4LogsReady (setVarHOLFinite (ofString "logs") v s) := by
  obtain ⟨w, rfl, hw⟩ := evalAt_load_local s "out" 16 v he
  have hb := (ivl_allocated_bound h.1.1.1.2 (Or.inl h.2.2.1)).2
  have hlt : locN s "out" + 16 < 2 ^ 64 := by dsimp at hb; omega
  have hwe : w.toNat = memW s (locN s "out" + 16) := by
    simpa only [show (16 : BitVec 64).toNat = 16 from rfl, Nat.mod_eq_of_lt hlt] using hw
  let post := setVarHOLFinite (ofString "logs") (.val (.word w)) s
  have hout : locN post "out" = locN s "out" := by
    simp [post, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "logs" ≠ ofString "out" from by decide]
  have hlogs : locN post "logs" = w.toNat := by
    simp [post, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hp : TxAfterCallStrong post :=
    LocalsOnly.setVar localsOnly_txAfterCallStrong (by decide) _ s h
  refine ⟨hp, ?_, ?_, ?_⟩
  · change locN post "logs" = memW s (locN post "out" + 16)
    rw [hlogs, hout, hwe]
  · rw [hlogs, hwe]
    exact (R13Shards.logsListOK_with_locals s post.locals s.clock _).mpr h.2.2.2.1
  · obtain ⟨S, Nd, _, _, ho⟩ := h.2.2.2.2
    rw [hlogs, hwe]
    exact logsLiveOwned_disjFixed (s := post) ho

/-- The credit/totals prefix ends with the live-log receipt guard established. -/
theorem phase4ThroughLogs_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4LogsReady tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 21 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + b) := by
  have hl : TerminatingProgBoundedOn TxAfterCallStrong
      (.dec (ofString "logs") .one
        (.load .one (.op .add [.var .local (ofString "out"), .const 16])) tail) b :=
    dec_bound_trans (fun s v hp he => phase4LogsReady_load s v hp he) htail
  have hb := @phase4CreditTotals_cut h _ _ hl
  have he : spinePlug 21 (spineAt 99 ptxCode) tail =
      spinePlug 20 (spineAt 99 ptxCode)
        (.dec (ofString "logs") .one
          (.load .one (.op .add [.var .local (ofString "out"), .const 16])) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem phase4NullLogs_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptReady tail b) :
    TerminatingProgBoundedOn Phase4LogsReady
      (spinePlug 1 (spineAt 120 ptxCode) tail) ((K.lst_new + 1) + b) := by
  have hb : TerminatingProgBoundedOn Phase4LogsReady
      (spinePlug 1 (spineAt 120 ptxCode) tail) (max (K.lst_new + 1) 0 + b) := by
    unfold ptxCode
    refine seq_bound_trans (Q := Phase4ReceiptReady) ?_ ?_ htail
    · apply TerminatingProgBoundedOn.ite_on
      · exact TerminatingProgBoundedOn.call_on h.fb_lst_new _ _
          (fun s vs body callee ret hc hp ha hl => guestInv_callEntry s callee hp.1.1.1.1.1)
      · exact TerminatingProgBoundedOn.of_clock clock_skip
    · apply Hoare.ite
      · apply Hoare.mono (P' := TxAfterCallStrong) _ (fun _ hp => hp.1.1)
        exact Hoare.callLocal_resume (lst_new_receiptReady_resume h)
      · apply Hoare.skip
        intro F s hp _
        refine ⟨hp.1.1, hp.1.2.2.1, hp.1.2.2.2, ?_⟩
        rw [hp.1.2.1]
        obtain ⟨S, Nd, hw, _, ho⟩ := hp.1.1.2.2.2.2
        exact ⟨S, Nd, hw, ho⟩
      · exact fun _ _ hr => absurd hr (by simp)
  intro F s hc hp
  simpa only [Nat.max_zero] using hb s hc hp

theorem localsOnly_phase4ReceiptReady : LocalsOnly ["index", "out", "logs"] Phase4ReceiptReady := by
  intro F s locals k hl hp
  have hg := locN_congr s locals k "logs" (hl "logs" (by simp))
  refine ⟨txAfterCallStrong_with_locals s locals k
    (hl "index" (by simp)) (hl "out" (by simp)) hp.1, ?_, ?_, ?_⟩
  · rw [hg]
    exact (R13Shards.logsListOK_with_locals s locals k _).mpr hp.2.1
  · rw [hg]; exact hp.2.2.1
  · rw [hg]; exact logsWorldOwned_with_locals locals k hp.2.2.2

theorem phase4Succeeded_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptReady tail b) :
    TerminatingProgBoundedOn Phase4ReceiptReady
      (spinePlug 2 (spineAt 121 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn Phase4ReceiptReady
      (spinePlug 2 (spineAt 121 ptxCode) tail) (0 + b) := by
    unfold ptxCode
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_phase4ReceiptReady _ (by decide) _ _ ?_
    refine seq_bound_trans (Q := Phase4ReceiptReady) ?_ ?_ htail
    · exact TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _))
        (TerminatingProgBoundedOn.of_clock clock_skip)
    · apply Hoare.ite
      · apply Hoare.mono (P' := Phase4ReceiptReady) _ (fun _ hp => hp.1)
        exact Hoare.assign
          (fun s v hp _ _ => LocalsOnly.setVar localsOnly_phase4ReceiptReady
            (name := ofString "succeeded") (by decide) v s hp)
          (fun _ _ hr => absurd hr (by simp))
      · exact Hoare.skip (fun _ hp _ => hp.1)
      · exact fun _ _ hr => absurd hr (by simp)
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

/-- The Phase-4 prefix reaches receipt encoding with its full entry guard. -/
theorem phase4BeforeReceipt_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptReady tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 24 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) + b)) := by
  have hb := @phase4ThroughLogs_cut h _ _
    (phase4NullLogs_cut h (phase4Succeeded_cut htail))
  have he : spinePlug 24 (spineAt 99 ptxCode) tail =
      spinePlug 21 (spineAt 99 ptxCode)
        (spinePlug 1 (spineAt 120 ptxCode)
          (spinePlug 2 (spineAt 121 ptxCode) tail)) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

def receiptScratchSpec : List (String × Nat × Nat) :=
  [("keccak_pad", 136, 136), ("keccak_st", 200, 200)]

theorem receiptScratchSpec_ok : ScratchSpec receiptScratchSpec := by
  unfold ScratchSpec receiptScratchSpec
  decide

/-- Receipt encoding preserves the message output independently of its returned slice. -/
theorem encode_receipt_output_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : Phase4ReceiptReady s)
    (hg : locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs") :
    TxAfterCallStrong { post with locals := s.locals } := by
  have hL : LogsListOK (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]
    exact (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.2.1
  have hD : LogsDisjFixed (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]; exact hp.2.2.1
  have hw := funSpec_at_lookup h.wk_encode_receipt s hc vs body callee ret hl
    ⟨worldOK_callEntry hp.1.1.1 callee, hL, hD⟩ (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hsc : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  exact txAfterCallStrong_scratchStep
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    hs' hp.1 ⟨hs.2.1, by omega⟩ receiptScratchSpec_ok
    rfl (by decide) (by decide) (by decide) (by simp)
    (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)

/-- The receipt contract also returns bounded slice words and valid live logs. -/
theorem encode_receipt_result (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : Phase4ReceiptReady s)
    (hg : locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs") :
    ∃ a b : BitVec 64, v = .rStruct [.val (.word a), .val (.word b)] ∧
      Inside (a.toNat, b.toNat) sourceBase (globN post "heap_ptr") ∧
      a.toNat < 2 ^ 61 ∧ b.toNat < 2 ^ 61 ∧
      memW post (locN s "logs" + 8) < 2 ^ 28 ∧ LogsListOK post (locN s "logs") := by
  have hL : LogsListOK (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]
    exact (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.2.1
  have hD : LogsDisjFixed (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]; exact hp.2.2.1
  have hw := funSpec_at_lookup h.wk_encode_receipt s hc vs body callee ret hl
    ⟨worldOK_callEntry hp.1.1.1 callee, hL, hD⟩ (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hWT, _, _⟩ := hp.1.2.2.2.2
  have hWTc := (R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hWT
  have hR : IvlsDisj
      (receiptScratchSpec.map (fun e => bufferRegion (callEntryStateHOLFinite s callee) (e.1, e.2.2)))
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd) := by
    intro i hi j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact bufferRegion_disj_le hWTc (e.1, e.2.1) (receiptScratchSpec_ok e he).1
      (receiptScratchSpec_ok e he).2.1 e.2.2 (receiptScratchSpec_ok e he).2.2.2 j hj
  obtain ⟨S', Nd', _, _, _, _, hret⟩ := hs.2.2.2.2 S Nd hWTc hR
  simpa only [hg] using hret v rfl

theorem encode_receipt_owned (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : Phase4ReceiptReady s)
    (hg : locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs") :
    LogsWorldOwned post (locN s "logs") := by
  have hL : LogsListOK (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]
    exact (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.2.1
  have hD : LogsDisjFixed (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]; exact hp.2.2.1
  have hw := funSpec_at_lookup h.wk_encode_receipt s hc vs body callee ret hl
    ⟨worldOK_callEntry hp.1.1.1 callee, hL, hD⟩ (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hsc : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  exact (logsWorldOwned_scratchStep hs' hp.1.1.1.1
    ⟨hs.2.1, by change globN post "scratch_ptr" ≤ globN s "scratch_ptr"; omega⟩
    hp.2.1 hp.2.2.2 receiptScratchSpec_ok rfl (by decide)).2

def Phase4ReceiptEncoded : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxAfterCallStrong s ∧ LogsListOK s (locN s "logs") ∧
    memW s (locN s "logs" + 8) < 2 ^ 28 ∧
    ∃ a b : BitVec 64,
      s.locals.lookup (ofString "rc") = some (.rStruct [.val (.word a), .val (.word b)]) ∧
      Inside (a.toNat, b.toNat) sourceBase (globN s "heap_ptr") ∧
      a.toNat < 2 ^ 61 ∧ b.toNat < 2 ^ 61 ∧ LogsWorldOwned s (locN s "logs")

theorem localsOnly_phase4ReceiptEncoded :
    LocalsOnly ["index", "out", "logs", "rc"] Phase4ReceiptEncoded := by
  intro F s locals k hl hp
  have hg := locN_congr s locals k "logs" (hl "logs" (by simp))
  obtain ⟨ho, hL, hn, a, b, he, hi, ha, hb, hw⟩ := hp
  refine ⟨txAfterCallStrong_with_locals s locals k
    (hl "index" (by simp)) (hl "out" (by simp)) ho, ?_, ?_, a, b, ?_, hi, ha, hb, ?_⟩
  · rw [hg]; exact (R13Shards.logsListOK_with_locals s locals k _).mpr hL
  · change memW s (locN {s with locals := locals, clock := k} "logs" + 8) < 2 ^ 28
    rw [hg]; exact hn
  · exact (hl "rc" (by simp)).trans he
  · rw [hg]; exact logsWorldOwned_with_locals locals k hw

theorem receiptEncoded_heapStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] Q s r post)
    (h : Phase4ReceiptEncoded s) (hn : locN s "logs" ≠ 0) :
    Phase4ReceiptEncoded {post with locals := s.locals} := by
  obtain ⟨ho, hl, hlen, a, b, he, hi, ha, hb, hw⟩ := h
  have hgrow : AllocatorGrows s post := ⟨hs.2.1, by
    have he : globN post "scratch_ptr" = globN s "scratch_ptr" :=
      R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
    omega⟩
  have hhead := logsWorldOwned_heapStep_header hs ho.1.1.1 hl hw hn
  have hlogs := logsWorldOwned_scratchStep hs ho.1.1.1 hgrow hl hw
    (gs := []) (by intro e he; cases he) rfl (by decide)
  refine ⟨txAfterCallStrong_heapStep hs ho, ?_, ?_, a, b, he, ?_, ha, hb, ?_⟩
  · exact (R13Shards.logsListOK_with_locals post s.locals post.clock _).mpr hlogs.1
  · change memW post (locN s "logs" + 8) < 2 ^ 28
    rw [hhead.2]; exact hlen
  · change Inside (a.toNat, b.toNat) sourceBase (globN post "heap_ptr")
    unfold Inside at hi ⊢; have := hs.2.1; omega
  · exact logsWorldOwned_with_locals s.locals post.clock hlogs.2

def Phase4LogCountReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4ReceiptEncoded s ∧ locN s "nl" = memW s (locN s "logs" + 8) ∧ locN s "logs" ≠ 0

theorem phase4LogCount_load {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (h : Phase4ReceiptEncoded s)
    (he : evalAt s (.load .one (.op .add [.var .local (ofString "logs"), .const 8])) = some v) :
    Phase4LogCountReady (setVarHOLFinite (ofString "nl") v s) := by
  have hn := evalAt_load_local_nonzero s h.1.1.1.1.1 "logs" v he
  obtain ⟨w, rfl, hw⟩ := evalAt_load_local s "logs" 8 v he
  have hlt : locN s "logs" + 8 < 2 ^ 64 := by
    rcases h.2.1 with hz | hl
    · rw [hz]; norm_num
    · have hb := (ivl_allocated_bound h.1.1.1.1.2 hl.2.1).2
      dsimp at hb; omega
  have hwe : w.toNat = memW s (locN s "logs" + 8) := by
    simpa only [show (8 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt hlt] using hw
  refine ⟨LocalsOnly.setVar localsOnly_phase4ReceiptEncoded (by decide) _ s h, ?_⟩
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "nl" ≠ ofString "logs" from by decide] using And.intro hwe hn

theorem localsOnly_phase4LogCountReady :
    LocalsOnly ["index", "out", "logs", "rc", "nl"] Phase4LogCountReady := by
  intro F s locals k hl hp
  refine ⟨localsOnly_phase4ReceiptEncoded s locals k (fun n hn => hl n (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    rcases hn with rfl | rfl | rfl | rfl <;> simp)) hp.1, ?_⟩
  change locN {s with locals := locals, clock := k} "nl" =
    memW s (locN {s with locals := locals, clock := k} "logs" + 8) ∧
      locN {s with locals := locals, clock := k} "logs" ≠ 0
  rw [locN_congr s locals k "nl" (hl "nl" (by simp)),
    locN_congr s locals k "logs" (hl "logs" (by simp))]
  exact hp.2

def Phase4LogPointersReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4LogCountReady s ∧ locN s "lp" = memW s (locN s "logs")

theorem phase4LogPointer_load {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (h : Phase4LogCountReady s)
    (he : evalAt s (.load .one (.op .add [.var .local (ofString "logs"), .const 0])) = some v) :
    Phase4LogPointersReady (setVarHOLFinite (ofString "lp") v s) := by
  obtain ⟨w, rfl, hw⟩ := evalAt_load_local s "logs" 0 v he
  have hlt : locN s "logs" < 2 ^ 64 := by
    rcases h.1.2.1 with hz | hl
    · rw [hz]; norm_num
    · have hb := (ivl_allocated_bound h.1.1.1.1.1.2 hl.2.1).2
      dsimp at hb; omega
  have hwe : w.toNat = memW s (locN s "logs") := by
    simpa only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero,
      Nat.mod_eq_of_lt hlt] using hw
  refine ⟨LocalsOnly.setVar localsOnly_phase4LogCountReady (by decide) _ s h, ?_⟩
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "lp" ≠ ofString "logs" from by decide] using hwe

theorem logPointers_heapStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] Q s r post)
    (h : Phase4LogPointersReady s) (hn : locN s "logs" ≠ 0) :
    Phase4LogPointersReady {post with locals := s.locals} := by
  obtain ⟨a, b, _, _, _, _, hw⟩ := h.1.1.2.2.2
  have hh := logsWorldOwned_heapStep_header hs h.1.1.1.1.1.1 h.1.1.2.1 hw hn
  refine ⟨⟨receiptEncoded_heapStep hs h.1.1 hn, ?_, hn⟩, ?_⟩
  · change locN s "nl" = memW post (locN s "logs" + 8)
    rw [hh.2]; exact h.1.2.1
  · change locN s "lp" = memW post (locN s "logs")
    rw [hh.1]; exact h.2

theorem localsOnly_phase4LogPointersReady :
    LocalsOnly ["index", "out", "logs", "rc", "nl", "lp"] Phase4LogPointersReady := by
  intro F s locals k hl hp
  refine ⟨localsOnly_phase4LogCountReady s locals k (fun n hn => hl n (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> simp)) hp.1, ?_⟩
  change locN {s with locals := locals, clock := k} "lp" =
    memW s (locN {s with locals := locals, clock := k} "logs")
  rw [locN_congr s locals k "lp" (hl "lp" (by simp)),
    locN_congr s locals k "logs" (hl "logs" (by simp))]
  exact hp.2

theorem lst_push_logPointers_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (hp : Phase4LogPointersReady s) (hn : locN s "logs" ≠ 0)
    (harg : BoListArg (callEntryStateHOLFinite s callee)) :
    Phase4LogPointersReady (setVarHOLFinite (ofString "slot") v {post with locals := s.locals}) := by
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  exact LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) v _
    (logPointers_heapStep hs' hp hn)

theorem lst_push_bo40_arg {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode) (hp : TxWorld s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret)) :
    BoListArg (callEntryStateHOLFinite s callee) ∧
      locN (callEntryStateHOLFinite s callee) "l" = memW s (globN s "bo" + 40) := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  rcases hload : evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 40])) with _ | vl
  · simp only [evalListHOLExact, hload] at ha'; cases ha'
  obtain ⟨w, rfl, hw⟩ := evalAt_loadG s "bo" 40 vl hload
  have hparams := callee_param_two_exp s (ofString "lst_push") (ofString "l") (ofString "esz")
    .one .one _ _ (by rw [hc]; exact lookup_lst_push)
    (.load .one (.op .add [.var .global (ofString "bo"), .const 40])) (.const 8)
    (.val (.word w)) (.val (.word 8)) vs body callee ret hload rfl ha hl
  have hle : locN (callEntryStateHOLFinite s callee) "l" = memW s (globN s "bo" + 40) := by
    simpa only [locN, callEntryStateHOLFinite, hparams.2.1,
      show (40 : BitVec 64).toNat = 40 from rfl] using hw
  refine ⟨⟨worldOK_callEntry hp.1 callee, hp.2.bo_nz, Or.inl hle, ?_⟩, hle⟩
  simp only [locN, callEntryStateHOLFinite, hparams.2.2]
  rfl

theorem lst_push_slot_result (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (harg : BoListArg (callEntryStateHOLFinite s callee)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat % 8 = 0 ∧
      Inside (w.toNat, 8) (memW post (locN (callEntryStateHOLFinite s callee) "l"))
        (memW post (locN (callEntryStateHOLFinite s callee) "l") +
          8 * memW post (locN (callEntryStateHOLFinite s callee) "l" + 16)) := by
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, hW⟩ := harg.1.2
  obtain ⟨Nd, hTr⟩ := hW.2.2.2
  have hWT : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hTr⟩
  obtain ⟨_, _, _, _, _, _, hret⟩ := hs.2.2.2.2 S Nd hWT (by intro i hi; cases hi)
  exact hret v rfl

theorem lst_push_bo40_slot_result (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : TxWorld s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat % 8 = 0 ∧
      Inside (w.toNat, 8) (memW post (memW post (globN post "bo" + 40)))
        (memW post (memW post (globN post "bo" + 40)) +
          8 * memW post (memW post (globN post "bo" + 40) + 16)) := by
  have harg := lst_push_bo40_arg s vs body callee ret hc hp ha hl
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg.1 (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hbo : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hm : memW post (globN s "bo" + 40) = memW s (globN s "bo" + 40) :=
    hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hp.2.bo_nz 40 (by simp) (by intro i hi; cases hi)
  obtain ⟨w, hv, hal, hin⟩ := lst_push_slot_result h s vs body callee ret v post hc hl hr harg.1
  refine ⟨w, hv, hal, ?_⟩
  rw [hbo, hm]
  simpa only [harg.2] using hin

def receiptArray {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)

theorem receiptArray_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hF : FixedTyped s) (hE : TxEnv s) : Allocated s (receiptArray s) ∧ WordsOK s (receiptArray s) := by
  have hb : receiptArray s ∈ blockOutObjects s := by
    unfold receiptArray blockOutObjects
    simp [hE.bo_nz, hE.bo32]
  exact (hF.1 _ (List.mem_append_left _ (List.mem_append_right _ hb))).resolve_left
    (by simp [receiptArray])

def receiptDst (high : Bool) : ExpHOL 64 :=
  .op .add ([.load .one (.op .add [.var .global (ofString "bo"), .const 32]),
    .panop .mul [.var .local (ofString "index"), .const 16]] ++
      if high then [.const 8] else [])

theorem receiptDst_inside {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxAfterCallStrong s) (high : Bool) {x : BitVec 64}
    (hx : evalAt s (receiptDst high) = some (.val (.word x))) :
    Inside (x.toNat, 8) (receiptArray s).1 ((receiptArray s).1 + (receiptArray s).2) := by
  have hE := h.1.2
  obtain ⟨S, Nd, hW, _, _⟩ := h.2.2.2.2
  have hhi := (ivl_allocated_bound h.1.1.1.2 (receiptArray_words hW.2.2.1 hE).1).2
  dsimp only [receiptArray] at hhi ⊢
  rcases hld : evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 32])) with _ | vbase
  · cases high <;> simp [receiptDst, evalAt, evalHOLExact, evalListHOLExact] at hx hld
    all_goals rw [hld] at hx; simp at hx
  obtain ⟨abase, rfl, habase_nat⟩ := evalAt_loadG s "bo" 32 vbase hld
  have habase : abase.toNat = memW s (globN s "bo" + 32) := habase_nat
  cases high <;> simp only [receiptDst, Bool.false_eq_true, if_false, if_true,
    List.append_nil, List.cons_append, List.nil_append, evalAt, evalHOLExact, evalListHOLExact] at hx
  all_goals
    simp only [evalAt, evalHOLExact, evalListHOLExact] at hld
    rw [hld] at hx
    rcases hidx_v : s.locals.lookup (ofString "index") with _ | vidx
    · simp [hidx_v] at hx
    rcases vidx with widx | _ | _
    · cases widx with
      | word idx_bv =>
        simp only [hidx_v, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
          ↓reduceIte, panOpHOL, wordOpHOL, wordOp, List.foldr, Option.some.injEq,
          ValueHOL.val.injEq, HolWordLab.word.injEq] at hx
        have hidx_nat : locN s "index" = idx_bv.toNat := by simp [locN, hidx_v]
        have hidx_lt : idx_bv.toNat < memW s (globN s "bo" + 80) := hidx_nat ▸ hE.idx_lt
        subst x
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] at *
        norm_num only [BitVec.toNat_ofNat] at *
        unfold Inside; dsimp only
        simp only [show (16 : BitVec 64).toNat = 16 from rfl,
          show (8 : BitVec 64).toNat = 8 from rfl,
          show (0 : BitVec 64).toNat = 0 from rfl]
        omega
    · simp [hidx_v, valueIsWord] at hx
    · simp [hidx_v, valueIsWord] at hx

theorem receiptEncoded_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : Phase4ReceiptEncoded s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (memW s (globN s "bo" + 32))
      (memW s (globN s "bo" + 32) + (16 * memW s (globN s "bo" + 80) + 16)))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    Phase4ReceiptEncoded {s with memory := mem'} := by
  obtain ⟨ho, hl, hn, a, b, hrc, hi, ha, hb, S, Nd, hWT, hown⟩ := h
  let post := {s with memory := mem'}
  have hg : GuestInv post := guestInv_congr (s := s) rfl rfl rfl rfl ho.1.1.1.1
  obtain ⟨hWT', heq, _⟩ := store_bo_array_world ho.1.1.1 ho.1.2 hWT
    (Or.inl ⟨rfl, rfl⟩) hx hin hm
  obtain ⟨_, _, hbo⟩ := blockOutObjects_eq_list ho.1.2 hWT.1
  have hmemb : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
      ∈ blockOutObjects s := by rw [hbo]; simp
  have hmemf : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
      ∈ fixedObjects s := List.mem_append_left _ (List.mem_append_right _ hmemb)
  have hmemw : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
      ∈ worldOwned s S Nd := by
    unfold worldOwned; simp only [List.mem_append]; exact Or.inl (Or.inr hmemf)
  have hlogs := logsLiveOwned_single_store ho.1.1.1.2 ho.1.1.1.1 hg hl hown hm
    ⟨_, hmemw, hin⟩ heq
  refine ⟨txAfterCallStrong_store_receipt ho hx hin hm, hlogs.1, ?_, a, b, hrc, hi, ha, hb,
    S, Nd, hWT', hlogs.2⟩
  by_cases hz : locN s "logs" = 0
  · have hxlo := ((ordinaryDomain_iff x).mp (ho.1.1.1.1.memaddrs ▸ hx)).2.1
    have hbase : 8 < sourceBase := by decide
    have he : memW post 8 = memW s 8 := by
      unfold memW
      rw [show post.memory (BitVec.ofNat 64 8) = s.memory (BitVec.ofNat 64 8) from hm _ (by
        intro he; have := congrArg BitVec.toNat he; norm_num at this; omega)]
    change memW post (locN s "logs" + 8) < 2 ^ 28
    simpa only [hz, Nat.zero_add, he] using hn
  · rcases hl with he | hl
    · exact False.elim (hz he)
    have hu : IvlUnhit s post (locN s "logs", 24) :=
      ivlUnhit_single hm (by simp)
        (disj_of_inside_right hin ((hown hz).2.1 _ (by simp) _ hmemw))
    have he := memW_eq_of_ivlUnhit (a := locN s "logs" + 8) hu (by have := hl.1.1; omega)
      (ivl_allocated_bound ho.1.1.1.2 hl.2.1).2 ⟨by omega, by omega⟩
    change memW post (locN s "logs" + 8) < 2 ^ 28
    rw [he]; exact hn

theorem logPointers_worldStore {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : Phase4LogPointersReady s) (hn : locN s "logs" ≠ 0) {x : BitVec 64}
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a)
    (hpres : ∀ S Nd, WorldTypedWith s S Nd →
      WorldTypedWith {s with memory := mem'} S Nd ∧
      worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
      TxEnv {s with memory := mem'})
    (hx : ∀ S Nd, WorldTypedWith s S Nd →
      ∃ i ∈ worldOwned s S Nd, Inside (x.toNat, 8) i.1 (i.1 + i.2)) :
    Phase4LogPointersReady {s with memory := mem'} := by
  obtain ⟨⟨⟨ho, hl, hlen, a, b, he, hi, ha, hb, S, Nd, hWT, hown⟩, hnl, _⟩, hlp⟩ := h
  let post := {s with memory := mem'}
  have hg : GuestInv post := guestInv_congr (s := s) rfl rfl rfl rfl ho.1.1.1.1
  obtain ⟨hWT', heq, _⟩ := hpres S Nd hWT
  obtain ⟨i, hiw, hix⟩ := hx S Nd hWT
  have hlogs := logsLiveOwned_single_store ho.1.1.1.2 ho.1.1.1.1 hg hl hown hm
    ⟨i, hiw, hix⟩ heq
  have hl' := hl.resolve_left hn
  have hu : IvlUnhit s post (locN s "logs", 24) :=
    ivlUnhit_single hm (by simp)
      (disj_of_inside_right hix ((hown hn).2.1 _ (by simp) _ hiw))
  have hbnd := (ivl_allocated_bound ho.1.1.1.2 hl'.2.1).2
  have h0 : memW post (locN s "logs") = memW s (locN s "logs") :=
    memW_eq_of_ivlUnhit hu hl'.1.1 hbnd ⟨by omega, by omega⟩
  have h8 : memW post (locN s "logs" + 8) = memW s (locN s "logs" + 8) :=
    memW_eq_of_ivlUnhit hu (by have := hl'.1.1; omega) hbnd ⟨by omega, by omega⟩
  refine ⟨⟨⟨txAfterCallStrong_worldStore ho hm hpres hx, hlogs.1, ?_,
    a, b, he, hi, ha, hb, S, Nd, hWT', hlogs.2⟩, ?_, hn⟩, ?_⟩
  · change memW post (locN s "logs" + 8) < 2 ^ 28
    rw [h8]; exact hlen
  · change locN s "nl" = memW post (locN s "logs" + 8)
    rw [h8]; exact hnl
  · change locN s "lp" = memW post (locN s "logs")
    rw [h0]; exact hlp

theorem logPointers_store_bo40 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : Phase4LogPointersReady s) (hn : locN s "logs" ≠ 0)
    (hback : memW s (memW s (globN s "bo" + 40)) ≠ 0)
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (memW s (memW s (globN s "bo" + 40)))
      (memW s (memW s (globN s "bo" + 40)) +
        8 * memW s (memW s (globN s "bo" + 40) + 16)))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    Phase4LogPointersReady {s with memory := mem'} := by
  apply logPointers_worldStore h hn hm
  · intro S Nd hWT
    exact store_bo_array_world h.1.1.1.1.1.1 h.1.1.1.1.2 hWT
      (Or.inr (Or.inl ⟨rfl, hback, rfl⟩)) hx hin hm
  · intro S Nd hWT
    obtain ⟨hc40, _, hbo⟩ := blockOutObjects_eq_list h.1.1.1.1.2 hWT.1
    let arr := (memW s (memW s (globN s "bo" + 40)),
      8 * memW s (memW s (globN s "bo" + 40) + 16))
    have hmemb : arr ∈ blockOutObjects s := by
      rw [hbo]
      simp [arr, hback, h.1.1.1.1.2.bo_nz, show memW s (memW s (globN s "bo" + 40) + 16) ≠ 0 from by omega]
    have hmemf : arr ∈ fixedObjects s := List.mem_append_left _ (List.mem_append_right _ hmemb)
    refine ⟨arr, ?_, hin⟩
    unfold worldOwned; simp only [List.mem_append]; exact Or.inl (Or.inr hmemf)

def Phase4LogSlotReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4LogPointersReady s ∧
    memW s (memW s (globN s "bo" + 40)) ≠ 0 ∧
    Inside (locN s "slot", 8) (memW s (memW s (globN s "bo" + 40)))
      (memW s (memW s (globN s "bo" + 40)) +
        8 * memW s (memW s (globN s "bo" + 40) + 16))

theorem hoare_logSlot_store (src : ExpHOL 64)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      evalAt s src = some v → ∃ w : HolWordLab 64, v = .val w) :
    Hoare Phase4LogSlotReady (.store (.var .local (ofString "slot")) src)
      (fun r t => r = none → Phase4LogPointersReady t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨w, rfl⟩ := hword s v hv
  obtain ⟨hdom, _, hmem⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  have hslot : locN s "slot" = x.toNat := by
    have hlu : s.locals.lookup (ofString "slot") = some (.val (.word x)) := hx
    simp only [locN, hlu]
  apply logPointers_store_bo40 hp.1 hp.1.1.2.2 hp.2.1 hdom _ hmem
  simpa only [hslot] using hp.2.2

theorem store_receiptSlot (off : Bool) :
    Hoare Phase4ReceiptEncoded
      (.store (receiptDst off) (.rfield (if off then 1 else 0) (.var .local (ofString "rc"))))
      (fun r t => r = none → Phase4ReceiptEncoded t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' h hx hv hst => ?_
  obtain ⟨a, b, he, _⟩ := h.2.2.2
  have hvw : ∃ w : HolWordLab 64, v = .val w := by
    cases off <;> simp [evalAt, evalHOLExact, he] at hv <;> subst v
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨w, rfl⟩ := hvw
  obtain ⟨hdom, _, hmem⟩ := R13Shards.panMemStoresHOL_word_spec (by simpa only [flattenHOL] using hst)
  exact receiptEncoded_store h hdom (receiptDst_inside h.1 off hx) hmem

theorem encode_receipt_encoded_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : Phase4ReceiptReady s)
    (hg : locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs") :
    Phase4ReceiptEncoded (setVarHOLFinite (ofString "rc") v { post with locals := s.locals }) := by
  have ho := encode_receipt_output_resume h s vs body callee ret v post hc hl hr hp hg
  obtain ⟨a, b, hv, hi, ha, hb, hn, hL⟩ :=
    encode_receipt_result h s vs body callee ret v post hc hl hr hp hg
  let t := setVarHOLFinite (ofString "rc") v { post with locals := s.locals }
  have hlogs : locN t "logs" = locN s "logs" := by
    simp [t, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "rc" ≠ ofString "logs" from by decide]
  refine ⟨LocalsOnly.setVar localsOnly_txAfterCallStrong (by decide) v _ ho, ?_, ?_, a, b, ?_, hi, ha, hb, ?_⟩
  · change LogsListOK t (locN t "logs")
    rw [hlogs]
    exact (R13Shards.logsListOK_with_locals post t.locals post.clock _).mpr hL
  · change memW post (locN t "logs" + 8) < 2 ^ 28
    rw [hlogs]; exact hn
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hv]
  · change LogsWorldOwned t (locN t "logs")
    rw [hlogs]
    exact logsWorldOwned_with_locals (s := post) t.locals post.clock
      (encode_receipt_owned h s vs body callee ret v post hc hl hr hp hg)

theorem encode_receipt_logs_param {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 e3 : ExpHOL 64) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [e1, e2, e3, .var .local (ofString "logs")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret)) :
    locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs" := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  cases h1 : evalAt s e1 with
  | none => simp only [evalAt] at h1; simp [evalListHOLExact, h1] at ha'
  | some v1 =>
    cases h2 : evalAt s e2 with
    | none => simp only [evalAt] at h1 h2; simp [evalListHOLExact, h1, h2] at ha'
    | some v2 =>
      cases h3 : evalAt s e3 with
      | none => simp only [evalAt] at h1 h2 h3; simp [evalListHOLExact, h1, h2, h3] at ha'
      | some v3 =>
        cases h4 : evalAt s (.var .local (ofString "logs")) with
        | none => simp only [evalAt] at h1 h2 h3 h4; simp [evalListHOLExact, h1, h2, h3, h4] at ha'
        | some v4 =>
          have hlc := R13Shards.lookup_encode_receipt
          rw [← hc] at hlc
          have hp := callee_param_four_exp' s (ofString "encode_receipt")
            _ _ _ _ _ _ _ _ _ _ hlc e1 e2 e3 (.var .local (ofString "logs"))
            v1 v2 v3 v4 vs body callee ret h1 h2 h3 h4 ha hl
          have hs : s.locals.lookup (ofString "logs") = some v4 := h4
          simp only [locN, callEntryStateHOLFinite, hp.2.2.2, hs]

theorem phase4EncodeReceipt_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptEncoded tail b) :
    TerminatingProgBoundedOn Phase4ReceiptReady
      (spinePlug 1 (spineAt 123 ptxCode) tail) (K.encode_receipt + b + 1) := by
  unfold ptxCode
  refine TerminatingProgBoundedOn.decCall_on h.fb_encode_receipt _ _ _ ?_ ?_ htail
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1
  · intro F s vs body callee ret v post hc hp ha hl hr
    exact encode_receipt_encoded_resume h s vs body callee ret v post hc hl hr hp
      (encode_receipt_logs_param s _ _ _ vs body callee ret hc ha hl)

theorem phase4ThroughReceipt_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptEncoded tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 25 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) + (K.encode_receipt + b + 1))) := by
  have hb := @phase4BeforeReceipt_cut h _ _ (phase4EncodeReceipt_cut h htail)
  have he : spinePlug 25 (spineAt 99 ptxCode) tail =
      spinePlug 24 (spineAt 99 ptxCode) (spinePlug 1 (spineAt 123 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem phase4ReceiptStores_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptEncoded tail b) :
    TerminatingProgBoundedOn Phase4ReceiptEncoded
      (spinePlug 2 (spineAt 124 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn Phase4ReceiptEncoded
      (spinePlug 2 (spineAt 124 ptxCode) tail) (0 + (0 + b)) := by
    unfold ptxCode
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (store_receiptSlot false) ?_
    exact seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (store_receiptSlot true) htail
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

theorem phase4ThroughReceiptStores_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptEncoded tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 27 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) + (K.encode_receipt + b + 1))) := by
  have hb := @phase4ThroughReceipt_cut h _ _ (phase4ReceiptStores_cut htail)
  have he : spinePlug 27 (spineAt 99 ptxCode) tail =
      spinePlug 25 (spineAt 99 ptxCode) (spinePlug 2 (spineAt 124 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem phase4LogPointers_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4LogPointersReady tail b) :
    TerminatingProgBoundedOn Phase4ReceiptEncoded
      (spinePlug 2 (spineAt 126 ptxCode) tail) b := by
  unfold ptxCode
  exact dec_bound_trans (fun s v hp he => phase4LogCount_load s v hp he)
    (dec_bound_trans (fun s v hp he => phase4LogPointer_load s v hp he) htail)

theorem phase4ThroughLogPointers_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4LogPointersReady tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 29 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) + (K.encode_receipt + b + 1))) := by
  have hb := @phase4ThroughReceiptStores_cut h _ _ (phase4LogPointers_cut htail)
  have he : spinePlug 29 (spineAt 99 ptxCode) tail =
      spinePlug 27 (spineAt 99 ptxCode) (spinePlug 2 (spineAt 126 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem hoare_logPointers_increment :
    Hoare Phase4LogPointersReady
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r t => r = none → Phase4LogPointersReady t) := by
  apply Hoare.assign
  · intro F s v hp _ _
    exact LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) v s hp
  · intro F s _ hr
    cases hr

theorem phase4LogCounter_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => Phase4LogPointersReady s ∧ locN s "i" = 0) tail b) :
    TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 1 (spineAt 128 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 1 (spineAt 128 ptxCode) tail) (0 + b) := by
    unfold ptxCode
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _))
      (Hoare.assign ?_ (fun _ _ hr => absurd hr (by simp))) htail
    intro F s v hp he _
    have hv : v = .val (.word (0 : BitVec 64)) := by
      change some (.val (.word (0 : BitVec 64))) = some v at he
      exact (Option.some.inj he).symm
    subst v
    refine ⟨LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) _ s hp, ?_⟩
    change locN (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) s) "i" = 0
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

theorem lookup_process_message_call :
    originalRuntimeCode.lookup (ofString "process_message_call") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_message_call).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 607 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_message_call) rfl

theorem msgReady_with_msg_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hmsg : locals.lookup (ofString "msg") = s.locals.lookup (ofString "msg"))
    (h : MsgReady s) : MsgReady { s with locals := locals, clock := k } := by
  have hm := locN_congr s locals k "msg" hmsg
  obtain ⟨hA, S, hW, hm152, hm160, hin, hw, hd1, hd2, hav, hgas, hroles⟩ := h
  refine ⟨(arenaReady_with_locals s locals k).mpr hA, S,
    (worldTyped_with_locals s locals k S).mpr hW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change memW s (locN { s with locals := locals, clock := k } "msg" + 152) ∈ S
    rw [hm]; exact hm152
  · change memW s (locN { s with locals := locals, clock := k } "msg" + 160) ∈ S
    rw [hm]; exact hm160
  · change Inside (locN { s with locals := locals, clock := k } "msg", 176) sourceBase (globN s "heap_ptr")
    rw [hm]; exact hin
  · change WordsOK s (locN { s with locals := locals, clock := k } "msg", 176)
    rw [hm]; exact hw
  · intro t ht i hi; rw [hm]; exact hd1 t ht i hi
  · intro j hj; rw [hm]; exact hd2 j hj
  · obtain ⟨Nd, hTr, hdTr⟩ := hav
    refine ⟨Nd, hTr, fun o ho j hj => ?_⟩
    change o ∈ [(locN { s with locals := locals, clock := k } "msg", 176)] at ho
    rw [hm] at ho; exact hdTr o ho j hj
  · change memW s (locN { s with locals := locals, clock := k } "msg" + 40) < 2 ^ 63
    rw [hm]; exact hgas
  · change RolesOK s S (worldRoleSlots s ++
      [(memW s (locN { s with locals := locals, clock := k } "msg" + 152), "frame.addr"),
       (memW s (locN { s with locals := locals, clock := k } "msg" + 160), "frame.key")])
      (journalRoleSlots s)
    rw [hm]; exact hroles

theorem msg_word_of_var_eval {F : Type} (s : PanSemStateFiniteExact 64 F) (mv : ValueHOL 64)
    (he : evalAt s (.var .local (ofString "m")) = some mv)
    (hsh : shapeEqHOL (shapeOfHOLExact mv) .one = true) :
    mv = .val (.word (BitVec.ofNat 64 (locN s "m"))) := by
  rw [shapeEqHOL_eq_true] at hsh
  obtain ⟨wm, rfl⟩ := shape_one_word hsh
  have hlu : s.locals.lookup (ofString "m") = some (.val (.word wm)) := by
    simpa [evalAt, evalHOLExact] using he
  have hloc : locN s "m" = wm.toNat := by simp [locN, hlu]
  rw [hloc, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem lookup_pmc_msg_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "m")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "process_message_call") vs =
      some (body', callee, ret')) :
    callee.lookup (ofString "msg") = some (.val (.word (BitVec.ofNat 64 (locN s "m")))) := by
  obtain ⟨mv, he, hm_lu⟩ := params_one_value s (ofString "process_message_call") (ofString "msg")
    .one _ .one (by rw [hc]; exact lookup_process_message_call)
    (.var .local (ofString "m")) vs body' callee ret' ha hl
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  simp only [evalListHOLExact, he, Option.some.injEq] at ha'
  subst ha'
  have hsh : shapeEqHOL (shapeOfHOLExact mv) .one = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
    split at hl
    · cases hl
    · rename_i exactBody exactLocals exactShape raw
      unfold lookupCodeHOLExact at raw
      have hlk : s.code.lookup (ofString "process_message_call") =
          some ([(ofString "msg", .one)], (sourceFunctionEntry Guest.Software.guestFn_process_message_call).2.2.1, .one) := by
        rw [hc]; exact lookup_process_message_call
      rw [hlk] at raw
      dsimp only at raw
      split at raw
      · rename_i hcond
        have hall := hcond.2.2
        simp [shapeEqHOL_eq_true] at hall ⊢
        exact hall.symm
      · cases raw
  rw [msg_word_of_var_eval s mv he hsh] at hm_lu
  exact hm_lu

theorem entry_pmc :
    CallEntryOn PtxMessageReady MsgReady (ofString "process_message_call")
      [.var .local (ofString "m")] := by
  intro F s vs body callee ret hc hP ha hl
  have hlu := lookup_pmc_msg_value s vs body callee ret hc ha hl
  let s_msg := setVarHOLFinite (ofString "msg") (.val (.word (BitVec.ofNat 64 (locN s "m")))) s
  have hs_lu : s_msg.locals.lookup (ofString "msg") =
      some (.val (.word (BitVec.ofNat 64 (locN s "m")))) := by
    simp [s_msg, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  exact msgReady_with_msg_local s_msg callee (s.clock - 1) (hlu.trans hs_lu.symm) hP.2

def pmcScratchSpec : List (String × Nat × Nat) :=
  [("b2_v", 128, 128), ("bn_expw", 352, 352), ("bn_gamma", 384, 384), ("evm_key_buf", 32, 32),
   ("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("pre_hdr_buf", 96, 96),
   ("rmd_h", 40, 40), ("rmd_pad", 128, 128), ("rmd_x", 128, 128), ("sha_pad", 128, 128),
   ("sha_st", 64, 64), ("sk_buf", 64, 52), ("u256_ws", 640, 640)]

theorem pmcScratchSpec_ok : ScratchSpec pmcScratchSpec := by
  unfold ScratchSpec pmcScratchSpec
  decide

/-- R11's conditional scratch footprint, with the strengthened return contract. -/
def PmcStrong : Prop :=
  WorldKeepsIn MsgReady
    (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
    (fun s => (locN s "msg", 176) ::
      pmcScratchSpec.map (fun e => bufferRegion s (e.1, e.2.2)))
    ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetMessageOutputStrong (ofString "process_message_call")

theorem resume_pmc_strong (hwk_strong : PmcStrong) :
    DecCallResumeOn PtxMessageReady TxAfterCallStrong (ofString "out")
      (ofString "process_message_call") [.var .local (ofString "m")] := by
  intro F s vs body callee ret v post hc hP ha hl hb
  unfold PmcStrong at hwk_strong
  have hMR := entry_pmc s vs body callee ret hc hP ha hl
  have hwk := funSpec_at_lookup hwk_strong s hc vs body callee ret hl hMR (by rw [hb]; simp)
  rw [hb] at hwk; dsimp only at hwk
  have hwsi := hwk (Or.inl ⟨v, rfl⟩)
  obtain ⟨_, S, hWT_ce, hm152, hm160, _, _, hd_tab, hd_fix, hav_tr, _, _⟩ := hMR
  obtain ⟨Nd, hTr_ce, hd_tr⟩ := hav_tr
  have hWTW_ce : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd :=
    ⟨hWT_ce.1, hWT_ce.2.1, hWT_ce.2.2.1, hTr_ce⟩
  have hmsg_disj_owned : ∀ j ∈ worldOwned (callEntryStateHOLFinite s callee) S Nd,
      Disj (locN (callEntryStateHOLFinite s callee) "msg", 176) j := by
    intro j hj
    unfold worldOwned at hj
    rcases List.mem_append.mp hj with h1 | hnd
    · rcases List.mem_append.mp h1 with htab | hfix
      · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp htab
        exact hd_tab t ht j hi
      · exact hd_fix j hfix
    · exact hd_tr _ (by simp) j hnd
  let Rlist : List Ivl :=
    (locN (callEntryStateHOLFinite s callee) "msg", 176) ::
      pmcScratchSpec.map (fun e => bufferRegion (callEntryStateHOLFinite s callee) (e.1, e.2.2))
  have hR_disj : IvlsDisj Rlist (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd) := by
    intro i hi j hj
    rcases List.mem_cons.mp hi with rfl | hi_gs
    · exact hmsg_disj_owned j (R13Shards.worldTypedIvls_sub_worldOwned hj)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi_gs
      obtain ⟨hgb, hnu, _, hle⟩ := pmcScratchSpec_ok e he
      exact bufferRegion_disj_le hWTW_ce (e.1, e.2.1) hgb hnu e.2.2 hle j hj
  have hT_in : ∀ t ∈ [memW (callEntryStateHOLFinite s callee) (locN (callEntryStateHOLFinite s callee) "msg" + 152),
      memW (callEntryStateHOLFinite s callee) (locN (callEntryStateHOLFinite s callee) "msg" + 160)], t ∈ S := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hm152
    · exact hm160
  obtain ⟨hAp, _, hg_kept, hrec_kept, hwsi_step⟩ := hwsi
  obtain ⟨S', Nd', _, hWTW_post, _, _, hret_msg⟩ := hwsi_step S Nd hWTW_ce hT_in hR_disj
  obtain ⟨out, rfl, hw_out, hin_out, hdisj_out, hll_out⟩ := hret_msg.1 v rfl
  obtain ⟨out', heq, hlogs_disj⟩ := hret_msg.2 _ rfl
  have hout_eq : out = out' := by cases heq; rfl
  subst out'
  let resumed := setVarHOLFinite (ofString "out") (.val (.word out)) { post with locals := s.locals }
  have hW_resumed : WorldOK resumed :=
    worldOK_of_parts
      ((arenaReady_with_locals post resumed.locals post.clock).mpr hAp)
      ((R13Shards.worldTypedWith_with_locals post resumed.locals post.clock S' Nd').mpr hWTW_post)
  have hE := hP.1.2
  have hbo_eq : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hg_kept (ofString "bo") (by decide))
  have hjcap_eq : globN post "journal_cap" = globN s "journal_cap" :=
    R16Shards.globN_eq_of_lookup (hg_kept (ofString "journal_cap") (by decide))
  have hbo8 : globN s "bo" % 8 = 0 := (R13Shards.bo_words hWT_ce.2.2.1 hE.bo_nz).2.1
  have hR_bo : ∀ i ∈ Rlist, Disj i (globN s "bo", 88) :=
    fun i hi => hR_disj i hi _ (bo_mem_typed (s := callEntryStateHOLFinite s callee) hE.bo_nz)
  have hR_zero : ∀ i ∈ Rlist, i.2 = 0 → i.1 % 8 = 0 := by
    intro i hi hz
    rcases List.mem_cons.mp hi with rfl | hi_gs
    · simp at hz
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi_gs
      exact bufferRegion_zero_aligned _ e.1 e.2.2 (by have := (pmcScratchSpec_ok e he).2.2.1; omega) hz
  have hkw : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk
    have hoffs : k ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80] : List Nat) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp
    have hrec_s : RecordsKept (fun _ => Rlist)
        [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
         ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
        s post := hrec_kept
    apply hrec_s ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hE.bo_nz k hoffs
    intro i hi hch
    have hk_in : k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    have hbase : (globN s "bo" + k) % 8 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    exact R13Shards.not_cellHits_of_disj hbase
      (fun hz => hR_zero i hi hz)
      ⟨by dsimp; omega, by dsimp; omega⟩
      (R13Shards.disj_symm (hR_bo i hi)) hch
  have hidx_lu : resumed.locals.lookup (ofString "index") = s.locals.lookup (ofString "index") := by
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "out" ≠ ofString "index" from by decide]
  have hi_eq : locN resumed "index" = locN s "index" :=
    locN_congr s resumed.locals post.clock "index" hidx_lu
  have hEnv_resumed : TxEnv resumed := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show globN post "bo" ≠ 0; rw [hbo_eq]; exact hE.bo_nz
    · show memW post (globN post "bo" + 24) ≠ 0; rw [hbo_eq, hkw 24 (by simp)]; exact hE.bo24
    · show memW post (globN post "bo" + 32) ≠ 0; rw [hbo_eq, hkw 32 (by simp)]; exact hE.bo32
    · show memW post (globN post "bo" + 40) ≠ 0; rw [hbo_eq, hkw 40 (by simp)]; exact hE.bo40
    · show memW post (globN post "bo" + 72) ≠ 0; rw [hbo_eq, hkw 72 (by simp)]; exact hE.bo72
    · show locN resumed "index" < memW post (globN post "bo" + 80)
      rw [hi_eq, hbo_eq, hkw 80 (by simp)]; exact hE.idx_lt
    · show globN post "journal_cap" ≠ 0; rw [hjcap_eq]; exact hE.jcap_nz
  have hout_loc : locN resumed "out" = out.toNat := by
    simp [resumed, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  refine ⟨⟨hW_resumed, hEnv_resumed⟩, ?_, ?_, ?_, S', Nd',
    (R13Shards.worldTypedWith_with_locals post resumed.locals post.clock S' Nd').mpr hWTW_post, ?_, ?_⟩
  · change WordsOK post (locN resumed "out", 96)
    rw [hout_loc]; exact hw_out
  · change Inside (locN resumed "out", 96) sourceBase (globN post "heap_ptr")
    rw [hout_loc]; exact hin_out
  · change LogsListOK resumed (memW post (locN resumed "out" + 16))
    rw [hout_loc]
    exact (R13Shards.logsListOK_with_locals post resumed.locals post.clock _).mpr hll_out
  · change IvlsDisj [(locN resumed "out", 96)] (worldOwned post S' Nd')
    rw [hout_loc]; exact hdisj_out
  · change LogsLiveOwned post S' Nd' (memW post (locN resumed "out" + 16))
    rw [hout_loc]; exact hlogs_disj

end PtxP34

theorem ptxPhase3_cut_strong (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallStrong tail b) :
    TerminatingProgBoundedOn PtxMessageReady (ptxPhase3 tail) (ptxCost3 + b) := by
  have hb : TerminatingProgBoundedOn PtxMessageReady (ptxPhase3 tail)
      (K.«process_message_call» + b + 1) := by
    unfold ptxPhase3 ptxCode
    exact TerminatingProgBoundedOn.decCall_on h.gb_process_message_call
      (ofString "out") .one [.var .local (ofString "m")]
      PtxP34.entry_pmc (PtxP34.resume_pmc_strong hwk) htail
  have he : K.«process_message_call» + b + 1 = ptxCost3 + b := by
    unfold ptxCost3; omega
  rw [he] at hb
  intro F s hc hp
  exact hb s hc hp

/-- The Phase-3 cut also transports the caller-local shapes required downstream. -/
theorem ptxPhase3_cut_strong_shapes (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => TxAfterCallStrong s ∧ PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s)
      (ptxPhase3 tail) (ptxCost3 + b) := by
  have he : CallEntryOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s)
      MsgReady (ofString "process_message_call") [.var .local (ofString "m")] := by
    intro F s vs body callee ret hc hp ha hl
    exact PtxP34.entry_pmc s vs body callee ret hc hp.1 ha hl
  have hr : DecCallResumeOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s)
      (fun s => TxAfterCallStrong s ∧ PtxPhase4LocalShapes s) (ofString "out")
      (ofString "process_message_call") [.var .local (ofString "m")] := by
    intro F s vs body callee ret v post hc hp ha hl hb
    exact ⟨PtxP34.resume_pmc_strong hwk s vs body callee ret v post hc hp.1 ha hl hb,
      ptxPhase4LocalShapes_resume s post v hp.2⟩
  have hb : TerminatingProgBoundedOn
      (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s) (ptxPhase3 tail)
      (K.«process_message_call» + b + 1) := by
    unfold ptxPhase3 ptxCode
    exact TerminatingProgBoundedOn.decCall_on h.gb_process_message_call
      (ofString "out") .one [.var .local (ofString "m")] he hr htail
  have heq : K.«process_message_call» + b + 1 = ptxCost3 + b := by
    unfold ptxCost3; omega
  rw [heq] at hb
  intro F s hc hp
  exact hb s hc hp

/-- Composition interface for the remaining Phase-4 proof and the shape-aware
Phase-1/2 prefix. Both missing cuts are explicit hypotheses here. -/
theorem gbody_process_transaction_strong_of_cuts
    (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    (h12 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s) tail b →
      TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 (ptxPhase2 tail))
        (ptxCost1 + (ptxCost2 + b)))
    (h4 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn PtxReceiptsDone tail b →
      TerminatingProgBoundedOn (fun s => TxAfterCallStrong s ∧ PtxPhase4LocalShapes s)
        (ptxPhase4 tail) (ptxCost4 + b)) :
    TerminatingFunBoundedOn TxReadyStrong (ofString "process_transaction")
      K.«process_transaction» := by
  refine ⟨_, _, _, ptx_lookup, ?_⟩
  have hb : TerminatingProgBoundedOn TxReadyStrong
      (ptxPhase1 (ptxPhase2 (ptxPhase3 (ptxPhase4 ptxPhase5))))
      (ptxCost1 + (ptxCost2 + (ptxCost3 + (ptxCost4 + ptxCost5)))) :=
    h12 _ _ (ptxPhase3_cut_strong_shapes h hwk
      (h4 _ _ (R13Shards.ptxPhase5_cut h)))
  rw [← ptx_phases_eq, ptx_cost_eq] at hb
  intro F s hc hp
  simpa only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural] using
    (hb (F := F) s hc hp)

end InitECandidate.Solver.Wave8GuestInv.R16Shards
