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

/-- Heap-only calls retain every source-array entry used by the copy loop. -/
theorem logsWorldOwned_heapStep_array {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {keep : List (String × List Nat)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"] keep Q s r post)
    (hA : ArenaReady s) (hl : LogsListOK s logs) (ho : LogsWorldOwned s logs)
    (hn : logs ≠ 0) :
    ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
  obtain ⟨S, Nd, hWT, hd⟩ := ho
  have hgrow : AllocatorGrows s post := ⟨hs.2.1, by
    have he : globN post "scratch_ptr" = globN s "scratch_ptr" :=
      R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
    omega⟩
  obtain ⟨S', Nd', _, _, hog, hfr, _⟩ := hs.2.2.2.2 S Nd hWT (by intro i hi; cases hi)
  exact (logsLiveOwned_array_survives hA.2 hs.1.2 hA.1 hgrow hl hd hn
    (worldOwned_zero_aligned hWT) (by intro j hj; cases hj) hog hfr
    (by intro j hj; cases hj)).2.2

/-- Preserve source ownership with the same witnesses used by a heap call's
return contract. -/
theorem logsWorldOwned_heapStep_joint {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {keep : List (String × List Nat)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"] keep Q s r post)
    (hA : ArenaReady s) (hl : LogsListOK s logs) (ho : LogsWorldOwned s logs) :
    ∃ S Nd, WorldTypedWith post S Nd ∧ LogsLiveOwned post S Nd logs ∧ Q s r post S Nd := by
  obtain ⟨S, Nd, hWT, hd⟩ := ho
  have hgrow : AllocatorGrows s post := ⟨hs.2.1, by
    have he : globN post "scratch_ptr" = globN s "scratch_ptr" :=
      R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
    omega⟩
  obtain ⟨S', Nd', _, hWT', hog, hfr, hQ⟩ := hs.2.2.2.2 S Nd hWT (by intro i hi; cases hi)
  refine ⟨S', Nd', hWT', ?_, hQ⟩
  exact logsLiveOwned_survives hA.2 hs.1.2 hA.1 hgrow hl hd
    (R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide)))
    (worldOwned_zero_aligned hWT) (by intro j hj; cases hj) hog hfr
    (by intro j hj; cases hj) (by intro j hj; cases hj)
    (by intro i hi j hj; cases hj)

/-- Restore caller locals without discarding the allocator's return predicate. -/
theorem heapStep_restore_locals {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {keep : List (String × List Nat)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"] keep Q s r post)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ∀ S Nd, WorldTypedWith {s with locals := locals, clock := k} S Nd →
      ∃ S' Nd', WorldTypedWith post S' Nd' ∧ Q s r post S' Nd' := by
  intro S Nd hW
  have hWs := (R13Shards.worldTypedWith_with_locals s locals k S Nd).mp hW
  obtain ⟨S', Nd', _, hW', _, _, hQ⟩ := hs.2.2.2.2 S Nd hWs (by intro i hi; cases hi)
  exact ⟨S', Nd', hW', hQ⟩

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

theorem lst_push_logSlot_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4LogPointersReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (hback : memW post (memW post (globN post "bo" + 40)) ≠ 0) :
    Phase4LogSlotReady (setVarHOLFinite (ofString "slot") v {post with locals := s.locals}) := by
  have hW := hp.1.1.1.1
  have harg := lst_push_bo40_arg s vs body callee ret hc hW ha hl
  have hptr := lst_push_logPointers_resume h s vs body callee ret v post hc hl hr hp
    hp.1.2.2 harg.1
  obtain ⟨w, rfl, _, hin⟩ := lst_push_bo40_slot_result h s vs body callee ret v post
    hc hW ha hl hr
  refine ⟨hptr, hback, ?_⟩
  simpa [locN, memW, globN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hin

/-- Additional callee fact needed because a null backing pointer is omitted by
`blockOutObjects`, while `RetListSlot` alone only states interval containment. -/
def LstPushBackingNonzero : Prop :=
  FunSpec BoListArg (fun s r post => ∀ v, r = some (.returned v) →
    memW post (locN s "l") ≠ 0) (ofString "lst_push")

theorem resume_lst_push_logSlot (h : PtxCallees) (hnonzero : LstPushBackingNonzero) :
    DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have harg := lst_push_bo40_arg s vs body callee ret hc hp.1.1.1.1 ha hl
  have hn := funSpec_at_lookup hnonzero s hc vs body callee ret hl harg.1
    (by rw [hr]; simp)
  rw [hr] at hn
  have hn' := hn v rfl
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg.1
    (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hbo : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hm : memW post (globN s "bo" + 40) = memW s (globN s "bo" + 40) :=
    hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hp.1.1.1.1.2.bo_nz 40 (by simp) (by intro i hi; cases hi)
  apply lst_push_logSlot_resume h s vs body callee ret v post hc hp ha hl hr
  rw [hbo, hm]
  simpa only [harg.2] using hn'

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

theorem hoare_logSlot_store_increment (src : ExpHOL 64)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      evalAt s src = some v → ∃ w : HolWordLab 64, v = .val w) :
    Hoare Phase4LogSlotReady
      (.seq (.store (.var .local (ofString "slot")) src)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → Phase4LogPointersReady t) :=
  Hoare.seq_fall (hoare_logSlot_store src hword) hoare_logPointers_increment

def phase4LogCopySrc : ExpHOL 64 :=
  .load .one (.op .add [.var .local (ofString "lp"),
    .panop .mul [.var .local (ofString "i"), .const 8]])

def phase4LogCopyBody : ProgHOL 64 :=
  .decCall (ofString "slot") .one (ofString "lst_push")
    [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]
    (.seq (.store (.var .local (ofString "slot")) phase4LogCopySrc)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))

theorem phase4LogCopySrc_word {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (he : evalAt s phase4LogCopySrc = some v) : ∃ w : HolWordLab 64, v = .val w := by
  unfold phase4LogCopySrc at he
  simp only [evalAt, evalHOLExact] at he
  split at he
  · rename_i ha
    split at he
    · rename_i hw
      simp only [memLoadHOLExact] at he
      split at he
      · cases he
        exact ⟨_, rfl⟩
      · cases he
    · cases he
  · cases he

theorem hoare_phase4LogCopyBody
    (hresume : DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]) :
    Hoare Phase4LogPointersReady phase4LogCopyBody
      (fun r t => r = none → Phase4LogPointersReady t) := by
  exact Hoare.decCall_fall (by decide) localsOnly_phase4LogPointersReady hresume
    (hoare_logSlot_store_increment phase4LogCopySrc phase4LogCopySrc_word)

theorem phase4LogCopyLoop_bound (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]) :
    TerminatingProgBoundedOn Phase4LogPointersReady
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        phase4LogCopyBody) ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1)) := by
  apply while_less_localsOnly localsOnly_phase4LogPointersReady
  · unfold phase4LogCopyBody
    have hb : TerminatingProgBoundedOn Phase4LogPointersReady phase4LogCopyBody
        (K.lst_push + (0 + 0) + 1) := TerminatingProgBoundedOn.decCall_on h.fb_lst_push
      (ofString "slot") ShapeHOL.one
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]
      (P := Phase4LogPointersReady) (Q := Phase4LogSlotReady)
      (by intro F s vs body callee ret hc hp ha hl
          exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1)
      hresume
      (seq_bound_trans
        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
        (hoare_logSlot_store phase4LogCopySrc phase4LogCopySrc_word)
        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _)))
    intro F s hc hp
    simpa only [phase4LogCopyBody, Nat.zero_add, Nat.add_zero] using hb s hc hp
  · exact hoare_phase4LogCopyBody hresume
  · unfold phase4LogCopyBody
    ptx_incr

theorem phase4LogCopyLoop_cut (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4LogPointersReady tail b) :
    TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 1 (spineAt 129 ptxCode) tail)
      ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) + b) := by
  have hp : Hoare Phase4LogPointersReady
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        phase4LogCopyBody) (fun r t => r = none → Phase4LogPointersReady t) :=
    hoare_while_less_localsOnly localsOnly_phase4LogPointersReady _ _
      (hoare_phase4LogCopyBody hresume)
      (by unfold phase4LogCopyBody; ptx_incr) (by decide)
  have hb := @seq_bound_trans _ _ _ _ _ _ (phase4LogCopyLoop_bound h hresume) hp htail
  unfold ptxCode
  intro F s hc hs
  exact hb s hc hs

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

theorem phase4ThroughLogCopy_cut (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4LogPointersReady tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 31 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) +
        (K.encode_receipt + ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) + b) + 1))) := by
  have hloop := @phase4LogCopyLoop_cut h hresume _ _ htail
  have hcounter := @phase4LogCounter_cut _ _
    (bound_mono (Q := fun s => Phase4LogPointersReady s ∧ locN s "i" = 0)
      hloop (fun s hp => hp.1))
  have hb := @phase4ThroughLogPointers_cut h _ _ hcounter
  have he : spinePlug 31 (spineAt 99 ptxCode) tail =
      spinePlug 29 (spineAt 99 ptxCode)
        (spinePlug 1 (spineAt 128 ptxCode)
          (spinePlug 1 (spineAt 129 ptxCode) tail)) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

def Phase4StableCapInit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4LogPointersReady s ∧ locN s "stable_log_cap" = locN s "nl"

theorem phase4StableCap_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (hp : Phase4LogPointersReady s)
    (he : evalAt s (.var .local (ofString "nl")) = some v) :
    Phase4StableCapInit (setVarHOLFinite (ofString "stable_log_cap") v s) := by
  refine ⟨LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) v s hp, ?_⟩
  have hlu : s.locals.lookup (ofString "nl") = some v := he
  simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hlu,
    show ofString "stable_log_cap" ≠ ofString "nl" from by decide]

def Phase4StableCapReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4LogPointersReady s ∧
    locN s "stable_log_cap" = max 1 (locN s "nl")

theorem phase4StableCap_bounds {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableCapReady s) :
    1 ≤ locN s "stable_log_cap" ∧ locN s "nl" ≤ locN s "stable_log_cap" ∧
      8 * locN s "stable_log_cap" < 2 ^ 64 := by
  have hn := hp.1.1.2.1
  have hb := hp.1.1.1.2.2.1
  rw [hp.2]
  omega

theorem hoare_phase4StableCap_adjust :
    Hoare Phase4StableCapInit
      (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0))
        (.assign .local (ofString "stable_log_cap") (.const 1)) .skip)
      (fun r t => r = none → Phase4StableCapReady t) := by
  apply Hoare.ite
  · apply Hoare.assign
    · intro F s v hp he _
      obtain ⟨w, hw, hn⟩ := hp.2
      obtain ⟨a, b, ha, hb, hc⟩ := evalAt_cmp s .equal _ _ w hw
      have hb0 : b = 0 := by cases hb; rfl
      subst b
      have ha0 : a = 0 := by
        by_contra h
        have hz : (0 : BitVec 64) = 0#64 := rfl
        have h' : a ≠ 0#64 := h
        simp [wordCmpHOL] at hc
        rw [if_neg h'] at hc
        exact hn hc
      have hz : locN s "stable_log_cap" = 0 := by
        change s.locals.lookup _ = some (.val (.word a)) at ha
        simp [locN, ha, ha0]
      have hv : v = .val (.word (1 : BitVec 64)) := by cases he; rfl
      subst v
      refine ⟨LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) _ s hp.1.1, ?_⟩
      have hn0 : locN s "nl" = 0 := hp.1.2.symm.trans hz
      simp [locN, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "stable_log_cap" ≠ ofString "nl" from by decide] at hn0 ⊢
      rw [hn0]
      decide
    · intro F s hp hr
      cases hr
  · apply Hoare.skip
    intro F s hp _
    obtain ⟨a, b, ha, hb, hc⟩ := evalAt_cmp s .equal _ _ 0 hp.2
    have hb0 : b = 0 := by cases hb; rfl
    subst b
    have ha0 : a ≠ 0 := by
      intro h
      simp [wordCmpHOL, h] at hc
    have hz : locN s "stable_log_cap" ≠ 0 := by
      change s.locals.lookup _ = some (.val (.word a)) at ha
      intro hz
      apply ha0
      apply BitVec.eq_of_toNat_eq
      simpa [locN, ha] using hz
    refine ⟨hp.1.1, ?_⟩
    have he := hp.1.2
    omega
  · intro F s hp hr
    cases hr

theorem phase4StableCap_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableCapReady tail b) :
    TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 2 (spineAt 130 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 2 (spineAt 130 ptxCode) tail) (0 + b) := by
    unfold ptxCode
    refine dec_bound_trans (fun s v hp he => phase4StableCap_init s v hp he) ?_
    refine seq_bound_trans ?_ hoare_phase4StableCap_adjust htail
    exact TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _))
      (TerminatingProgBoundedOn.of_clock clock_skip)
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

theorem lst_new_stable_args {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret)) :
    let ent := callEntryStateHOLFinite s callee
    locN ent "esz" = 8 ∧ locN ent "cap" = locN s "stable_log_cap" ∧
      1 ≤ locN ent "cap" ∧ locN ent "esz" * locN ent "cap" < 2 ^ 64 := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  cases hv : s.locals.lookup (ofString "stable_log_cap") with
  | none => simp [evalListHOLExact, evalHOLExact, hv] at ha'
  | some v =>
    have hlc := R13Shards.lookup_lst_new
    rw [← hc] at hlc
    obtain ⟨_, he, hcap⟩ := callee_param_two_exp s (ofString "lst_new")
      (ofString "esz") (ofString "cap") .one .one _ _ hlc
      (.const 8) (.var .local (ofString "stable_log_cap")) (.val (.word 8)) v
      vs body callee ret rfl hv ha hl
    have he8 : locN (callEntryStateHOLFinite s callee) "esz" = 8 := by
      simp [locN, callEntryStateHOLFinite, he]
    have hce : locN (callEntryStateHOLFinite s callee) "cap" = locN s "stable_log_cap" := by
      simp [locN, callEntryStateHOLFinite, hcap, hv]
    have hb := phase4StableCap_bounds s hp
    exact ⟨he8, hce, hce.symm ▸ hb.1, by rw [he8, hce]; exact hb.2.2⟩

theorem lst_new_stable_fresh (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      FreshBlock (callEntryStateHOLFinite s callee) post w.toNat 24 ∧
      FreshBlock (callEntryStateHOLFinite s callee) post (memW post w.toNat)
        (8 * locN s "stable_log_cap") ∧ memW post (w.toNat + 8) = 0 ∧
      ∃ S Nd, WorldTypedWith post S Nd ∧
        IvlsDisj [(w.toNat, 24), (memW post w.toNat, 8 * locN s "stable_log_cap")]
          (worldOwned post S Nd) := by
  have hargs := lst_new_stable_args s vs body callee ret hc hp ha hl
  have hW := hp.1.1.1.1.1.1
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hW callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, hWT⟩ := hW.2
  obtain ⟨Nd, hTr⟩ := hWT.2.2.2
  have hWTc := (R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr
    ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr⟩
  obtain ⟨S', Nd', _, hWT', _, _, hret⟩ := hs.2.2.2.2 S Nd hWTc
    (by intro i hi; cases hi)
  obtain ⟨w, hv, hd⟩ := hret hargs.2.2.2 v rfl
  have ht := funSpec_at_lookup h.rt_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hW callee).1 (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨w', hv', _, _, hf⟩ := ht v rfl
  have heq : w' = w := by rw [hv] at hv'; cases hv'; rfl
  subst w'
  obtain ⟨hh, hb, _, hn, _⟩ := hf hargs.2.2.2 hargs.2.2.1
  refine ⟨w, hv, hh, ?_, hn, S', Nd', hWT', ?_⟩
  · simpa only [hargs.1, hargs.2.1] using hb
  · simpa only [hargs.1, hargs.2.1] using hd

/-- The allocator separates its returned header from its backing region. -/
theorem lst_new_stable_resumed_header_backing (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Disj (locN t "stable_logs", 24)
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  have hargs := lst_new_stable_args s vs body callee ret hc hp ha hl
  have ht := funSpec_at_lookup h.rt_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee).1 (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨w, rfl, _, _, hf⟩ := ht v rfl
  have hd := (hf hargs.2.2.2 hargs.2.2.1).2.2.1
  rw [hargs.1, hargs.2.1] at hd
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" by decide] using hd

/-- Fresh header allocation establishes the allocation premise of the length store. -/
theorem lst_new_stable_header_allocated (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Allocated t (locN t "stable_logs", 24) := by
  obtain ⟨w, rfl, hh, _⟩ := lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  have hbase := hp.1.1.1.1.1.1.1.2.1
  have hi := hh.2.1
  apply Or.inl
  simpa [Inside, locN, globN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    callEntryStateHOLFinite] using
    (show sourceBase ≤ w.toNat ∧ w.toNat + 24 ≤ globN post "heap_ptr" from
      ⟨hbase.trans hi.1, hi.2⟩)

theorem lst_new_stable_source_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    Phase4StableCapReady (setVarHOLFinite (ofString "stable_logs") v
      {post with locals := s.locals}) := by
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  have hp' := logPointers_heapStep hs' hp.1 hp.1.1.2.2
  refine ⟨LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) v _ hp', ?_⟩
  simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" from by decide,
    show ofString "stable_logs" ≠ ofString "nl" from by decide] using hp.2

theorem lst_new_stable_capacity (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      memW post (w.toNat + 16) = locN s "stable_log_cap" := by
  have hargs := lst_new_stable_args s vs body callee ret hc hp ha hl
  have ht := funSpec_at_lookup h.rt_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee).1 (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨w, hv, _, _, hf⟩ := ht v rfl
  obtain ⟨_, _, _, _, hcap⟩ := hf hargs.2.2.2 hargs.2.2.1
  exact ⟨w, hv, hcap.trans hargs.2.1⟩

theorem fresh_empty_stable_logs {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs cap : Nat} (hA : ArenaOK s)
    (hh : FreshBlock s post logs 24)
    (hb : FreshBlock s post (memW post logs) (8 * cap))
    (hd : IvlsDisj [(logs, 24), (memW post logs, 8 * cap)] (worldOwned post S Nd))
    (hn : memW post (logs + 8) = 0) :
    LogsListOK post logs ∧ LogsLiveOwned post S Nd logs ∧ LogsDisjFixed post logs := by
  have hhi : Inside (logs, 24) sourceBase (globN post "heap_ptr") := by
    have hi := hh.2.1
    change Inside (logs, 24) (globN s "heap_ptr") (globN post "heap_ptr") at hi
    exact ⟨hA.1.trans hi.1, hi.2⟩
  have hbi : Inside (memW post logs, 0) sourceBase (globN post "heap_ptr") := by
    have hi := hb.2.1
    constructor
    · exact hA.1.trans hi.1
    · have := hi.2; dsimp [Inside] at this ⊢; omega
  have ho := logsLiveOwned_empty (S := S) (Nd := Nd) (Or.inl hbi)
    (fun j hj => hd _ (by simp) j hj) hn
  exact ⟨logsListOK_empty hh.2.2 (Or.inl hhi) hn, ho, logsLiveOwned_disjFixed ho⟩

theorem lst_new_stable_owned (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ LogsListOK post w.toNat ∧
      LogsWorldOwned post w.toNat ∧ LogsDisjFixed post w.toNat := by
  obtain ⟨w, hv, hh, hb, hn, S, Nd, hw, hd⟩ :=
    lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  have ho := fresh_empty_stable_logs
    (worldOK_callEntry hp.1.1.1.1.1.1 callee).1.2 hh hb hd hn
  exact ⟨w, hv, ho.1, ⟨S, Nd, hw, ho.2.1⟩, ho.2.2⟩

def Phase4StableAllocated : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4StableCapReady s ∧ LogsListOK s (locN s "stable_logs") ∧
    LogsWorldOwned s (locN s "stable_logs") ∧ LogsDisjFixed s (locN s "stable_logs")

theorem lst_new_stable_allocated_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    Phase4StableAllocated (setVarHOLFinite (ofString "stable_logs") v
      {post with locals := s.locals}) := by
  have hp' := lst_new_stable_source_resume h s vs body callee ret v post hc hp hl hr
  obtain ⟨w, rfl, hlst, howned, hfixed⟩ :=
    lst_new_stable_owned h s vs body callee ret v post hc hp ha hl hr
  refine ⟨hp', ?_, ?_, ?_⟩
  all_goals simp only [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update,
    if_pos rfl, valueWord, Option.getD]
  · exact hlst
  · exact logsWorldOwned_with_locals _ _ howned
  · exact hfixed

/-- Allocation preserves the source pointer and length cells, so source
separation can be transported to the resumed memory. -/
theorem lst_new_stable_source_cells (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    memW post (locN s "logs") = memW s (locN s "logs") ∧
    memW post (locN s "logs" + 8) = memW s (locN s "logs" + 8) := by
  have hp' := lst_new_stable_source_resume h s vs body callee ret v post hc hp hl hr
  have hlp := hp'.1.2
  have hnl := hp'.1.1.2.1
  simp only [locN, memW, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "lp" by decide,
    show ofString "stable_logs" ≠ ofString "logs" by decide,
    show ofString "stable_logs" ≠ ofString "nl" by decide, if_false] at hlp hnl
  exact ⟨hlp.symm.trans hp.1.2, hnl.symm.trans hp.1.1.2.1⟩

/-- The allocator leaves every source record pointer unchanged. -/
theorem lst_new_stable_source_entries (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∀ i, i < memW s (locN s "logs" + 8) →
      memW post (memW s (locN s "logs") + 8 * i) =
        memW s (memW s (locN s "logs") + 8 * i) := by
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hs := R13Shards.worldStep_with_locals (hw (Or.inl ⟨v, rfl⟩)) s.locals s.clock
  obtain ⟨a, b, _, _, _, _, ho⟩ := hp.1.1.1.2.2.2
  exact logsWorldOwned_heapStep_array hs hp.1.1.1.1.1.1.1 hp.1.1.1.2.1 ho hp.1.1.2.2

theorem lst_new_stable_capacity_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let resumed := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Phase4StableAllocated resumed ∧
      memW resumed (locN resumed "stable_logs" + 16) = locN resumed "stable_log_cap" := by
  refine ⟨lst_new_stable_allocated_resume h s vs body callee ret v post hc hp ha hl hr, ?_⟩
  obtain ⟨w, rfl, hw⟩ := lst_new_stable_capacity h s vs body callee ret v post hc hp ha hl hr
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" from by decide] using hw

theorem stable_backing_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p cap : Nat} (hA : ArenaOK s) (hb : FreshBlock s post p (8 * cap)) :
    p % 8 = 0 ∧ Allocated post (p, 8 * cap) ∧ WordsOK post (p, 8 * cap) := by
  have hround : (8 * cap + 7) / 8 * 8 = 8 * cap := by omega
  obtain ⟨halign, hi, hw⟩ := hb
  rw [hround] at hi hw
  exact ⟨halign, Or.inl ⟨hA.1.trans hi.1, hi.2⟩, hw⟩

theorem lst_new_stable_backing_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let resumed := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    let p := memW resumed (locN resumed "stable_logs")
    p % 8 = 0 ∧ Allocated resumed (p, 8 * locN resumed "stable_log_cap") ∧
      WordsOK resumed (p, 8 * locN resumed "stable_log_cap") := by
  obtain ⟨w, rfl, _, hb, _⟩ :=
    lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  have hb' := stable_backing_allocated
    (worldOK_callEntry hp.1.1.1.1.1.1 callee).1.2 hb
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    Allocated, WordsOK, WordAt, globN,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" from by decide] using hb'

def Phase4StableStorageReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4StableAllocated s ∧
    memW s (locN s "stable_logs" + 16) = locN s "stable_log_cap" ∧
    let p := memW s (locN s "stable_logs")
    p % 8 = 0 ∧ Allocated s (p, 8 * locN s "stable_log_cap") ∧
      WordsOK s (p, 8 * locN s "stable_log_cap")

theorem lst_new_stable_storage_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    Phase4StableStorageReady (setVarHOLFinite (ofString "stable_logs") v
      {post with locals := s.locals}) := by
  obtain ⟨hp', hcap⟩ := lst_new_stable_capacity_resume h s vs body callee ret v post hc hp ha hl hr
  exact ⟨hp', hcap, lst_new_stable_backing_resume h s vs body callee ret v post hc hp ha hl hr⟩

theorem phase4StableAllocation_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableStorageReady tail b) :
    TerminatingProgBoundedOn Phase4StableCapReady
      (spinePlug 1 (spineAt 132 ptxCode) tail) (K.lst_new + b + 1) := by
  unfold ptxCode
  refine TerminatingProgBoundedOn.decCall_on h.fb_lst_new _ _ _ ?_ ?_ htail
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1
  · intro F s vs body callee ret v post hc hp ha hl hr
    exact lst_new_stable_storage_resume h s vs body callee ret v post hc hp ha hl hr

theorem phase4StableSetup_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableStorageReady tail b) :
    TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 3 (spineAt 130 ptxCode) tail) (K.lst_new + b + 1) := by
  have hb := @phase4StableCap_cut _ _ (phase4StableAllocation_cut h htail)
  have he : spinePlug 3 (spineAt 130 ptxCode) tail =
      spinePlug 2 (spineAt 130 ptxCode)
        (spinePlug 1 (spineAt 132 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem phase4ThroughStableSetup_cut (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableStorageReady tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 34 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) +
        (K.encode_receipt + ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) +
          (K.lst_new + b + 1)) + 1))) := by
  have hb := @phase4ThroughLogCopy_cut h hresume _ _ (phase4StableSetup_cut h htail)
  have he : spinePlug 34 (spineAt 99 ptxCode) tail =
      spinePlug 31 (spineAt 99 ptxCode) (spinePlug 3 (spineAt 130 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem stable_storage_length_fits {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableStorageReady s) :
    locN s "nl" ≤ memW s (locN s "stable_logs" + 16) ∧
      8 * locN s "nl" < 2 ^ 64 ∧
      ∀ i : Nat, i < locN s "nl" →
        WordAt s (memW s (locN s "stable_logs") + 8 * i) := by
  have hb := phase4StableCap_bounds s hp.1.1
  refine ⟨by rw [hp.2.1]; exact hb.2.1, ?_, ?_⟩
  · exact lt_of_le_of_lt (Nat.mul_le_mul_left 8 hb.2.1) hb.2.2
  · intro i hi
    have hw := hp.2.2.2.2
    apply hw.2.2 i
    have hic : i < locN s "stable_log_cap" := lt_of_lt_of_le hi hb.2.1
    simpa using hic

theorem lst_new_stable_header_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let resumed := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    WordsOK resumed (locN resumed "stable_logs", 24) ∧
      Allocated resumed (locN resumed "stable_logs", 24) := by
  obtain ⟨w, rfl, hh, _⟩ :=
    lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  have hi : Inside (w.toNat, 24) sourceBase (globN post "heap_ptr") :=
    ⟨(worldOK_callEntry hp.1.1.1.1.1.1 callee).1.2.1.trans hh.2.1.1, hh.2.1.2⟩
  have hw : WordsOK post (w.toNat, 24) := hh.2.2
  have ho : Allocated post (w.toNat, 24) := Or.inl hi
  simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    Allocated, WordsOK, WordAt, globN] using And.intro hw ho

theorem stable_length_field_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hh : WordsOK s (locN s "stable_logs", 24)) :
    WordAt s (locN s "stable_logs" + 8) := by
  have hw := hh.2.2 1 (by norm_num)
  simpa using hw

theorem stable_length_address_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hA : ArenaOK s) (hh : Allocated s (locN s "stable_logs", 24)) :
    locN s "stable_logs" + 8 < 2 ^ 64 ∧
      (BitVec.ofNat 64 (locN s "stable_logs") + (8 : BitVec 64)).toNat =
        locN s "stable_logs" + 8 := by
  have hb := (ivl_allocated_bound hA hh).2
  have hlt : locN s "stable_logs" + 8 < 2 ^ 64 := by dsimp at hb; omega
  refine ⟨hlt, ?_⟩
  have hl : locN s "stable_logs" < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hl, show (8 : BitVec 64).toNat = 8 from rfl,
    Nat.mod_eq_of_lt hlt]

theorem stable_length_store_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableStorageReady s)
    (mem' : BitVec 64 → HolWordLab 64)
    (hm : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) =
      .word (BitVec.ofNat 64 (locN s "nl"))) :
    memW {s with memory := mem'} (locN s "stable_logs" + 8) = locN s "nl" := by
  have hb := (stable_storage_length_fits s hp).2.1
  have hn : locN s "nl" < 2 ^ 64 := by omega
  change (valueWord (.val (mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8))))).toNat = _
  rw [hm]
  exact Nat.mod_eq_of_lt hn

theorem stable_length_store_header_unchanged {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hA : ArenaOK s)
    (hh : Allocated s (locN s "stable_logs", 24))
    (mem' : BitVec 64 → HolWordLab 64)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a) :
    memW {s with memory := mem'} (locN s "stable_logs") = memW s (locN s "stable_logs") ∧
    memW {s with memory := mem'} (locN s "stable_logs" + 16) =
      memW s (locN s "stable_logs" + 16) := by
  have hb := (ivl_allocated_bound hA hh).2
  have h0 : locN s "stable_logs" < 2 ^ 64 := by dsimp at hb; omega
  have h8 : locN s "stable_logs" + 8 < 2 ^ 64 := by dsimp at hb; omega
  have h16 : locN s "stable_logs" + 16 < 2 ^ 64 := by dsimp at hb; omega
  have hn0 : BitVec.ofNat 64 (locN s "stable_logs") ≠
      BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    intro he
    have he' := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h8] at he'
    omega
  have hn16 : BitVec.ofNat 64 (locN s "stable_logs" + 16) ≠
      BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    intro he
    have he' := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt h8] at he'
    omega
  constructor <;> simp only [memW]
  · rw [hm _ hn0]
  · rw [hm _ hn16]

theorem stable_length_store_words {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w : BitVec 64)
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) = .word w)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    {i : Ivl} (hi : WordsOK s i) : WordsOK {s with memory := mem'} i := by
  refine ⟨hi.1, hi.2.1, ?_⟩
  intro k hk
  obtain ⟨v, hd, hv⟩ := hi.2.2 k hk
  by_cases ha : BitVec.ofNat 64 (i.1 + 8 * k) =
      BitVec.ofNat 64 (locN s "stable_logs" + 8)
  · exact ⟨w, hd, by change mem' _ = _; rw [ha, he]⟩
  · exact ⟨v, hd, (hm _ ha).trans hv⟩

/-- A word-valued length write retains the allocated, readable stable header
needed by the subsequent backing-pointer load. -/
theorem stable_length_store_header_ready {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w : BitVec 64)
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) = .word w)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24)) :
    let t := {s with memory := mem'}
    WordsOK t (locN t "stable_logs", 24) ∧
      Allocated t (locN t "stable_logs", 24) ∧ WordAt t (locN t "stable_logs") := by
  have hw := stable_length_store_words s mem' w he hm hh
  refine ⟨hw, ha, ?_⟩
  have h0 := hw.2.2 0 (by change 0 < 24 / 8; decide)
  simpa only [Nat.mul_zero, Nat.add_zero, locN] using h0

theorem stable_length_store_backing {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableStorageReady s) (hA : ArenaOK s)
    (hh : Allocated s (locN s "stable_logs", 24))
    (mem' : BitVec 64 → HolWordLab 64) (w : BitVec 64)
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) = .word w)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    Allocated post (memW post (locN post "stable_logs"), 8 * locN post "stable_log_cap") ∧
      WordsOK post (memW post (locN post "stable_logs"), 8 * locN post "stable_log_cap") := by
  have hptr := (stable_length_store_header_unchanged s hA hh mem' hm).1
  change Allocated {s with memory := mem'}
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    WordsOK {s with memory := mem'}
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
  rw [hptr]
  exact ⟨hp.2.2.2.1, stable_length_store_words s mem' w he hm hp.2.2.2.2⟩

theorem stable_length_store_fits {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableStorageReady s) (hA : ArenaOK s)
    (hh : Allocated s (locN s "stable_logs", 24))
    (mem' : BitVec 64 → HolWordLab 64)
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) =
      .word (BitVec.ofNat 64 (locN s "nl")))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a) :
    memW {s with memory := mem'} (locN s "stable_logs" + 8) ≤
      memW {s with memory := mem'} (locN s "stable_logs" + 16) := by
  rw [stable_length_store_value s hp mem' he,
    (stable_length_store_header_unchanged s hA hh mem' hm).2]
  exact (stable_storage_length_fits s hp).1

/-- A store separated from the source header, live array and records retains
both source-log validity and ownership under an unchanged world footprint. -/
theorem logsLiveOwned_disjoint_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} {x : BitVec 64}
    {mem' : BitVec 64 → HolWordLab 64}
    (hA : ArenaOK s) (hg : GuestInv s) (hgp : GuestInv {s with memory := mem'})
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs)
    (hm : ∀ a, a ≠ x → mem' a = s.memory a)
    (hh : Disj (logs, 24) (x.toNat, 8))
    (ha : Disj (memW s logs, 8 * memW s (logs + 8)) (x.toNat, 8))
    (he : ∀ i, i < memW s (logs + 8) →
      Disj (memW s (memW s logs + 8 * i), 40) (x.toNat, 8))
    (howned : worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd) :
    LogsListOK {s with memory := mem'} logs ∧
      LogsLiveOwned {s with memory := mem'} S Nd logs := by
  let post := {s with memory := mem'}
  by_cases hn : logs = 0
  · exact ⟨Or.inl hn, fun h => False.elim (h hn)⟩
  have hl' := hl.resolve_left hn
  have hu : IvlUnhit s post (logs, 24) := ivlUnhit_single hm (by simp) hh
  have hb := (ivl_allocated_bound hA hl'.2.1).2
  have h0 : memW post logs = memW s logs :=
    memW_eq_of_ivlUnhit hu hl'.1.1 hb ⟨by omega, by omega⟩
  have h8 : memW post (logs + 8) = memW s (logs + 8) :=
    memW_eq_of_ivlUnhit hu (by have := hl'.1.1; omega) hb ⟨by omega, by omega⟩
  have hp : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
    intro i hi
    have hal := logsListOK_array_aligned hg hl hn (by omega)
    have hua : IvlUnhit s post (memW s logs, 8 * memW s (logs + 8)) :=
      ivlUnhit_single hm (fun _ => hal) ha
    exact memW_eq_of_ivlUnhit hua (by omega)
      (ivl_allocated_bound hA (hd hn).1).2 ⟨by dsimp; omega, by dsimp; omega⟩
  have hue : ∀ i, i < memW s (logs + 8) →
      IvlUnhit s post (memW s (memW s logs + 8 * i), 40) :=
    fun i hi => ivlUnhit_single hm (by simp) (he i hi)
  refine ⟨logsListOK_congr_header_unhit hA hg hgp (by rfl) hl
    (fun h => h) hu hp hue, ?_⟩
  intro _
  change Allocated post (memW post logs, 8 * memW post (logs + 8)) ∧ _
  rw [h0, h8]
  refine ⟨(hd hn).1, ?_, ?_⟩
  · change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]
    exact (hd hn).2.1
  · intro i hi
    rw [hp i hi, logOwnedIvls_eq_of_unhit hA (hl'.2.2.2.2 i hi).2 (hue i hi) rfl]
    change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]
    exact (hd hn).2.2 i hi

/-- The stable length update preserves the source logs and their ownership.
The separation premises are the freshness facts to retain from `lst_new`. -/
theorem stable_length_store_source {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableStorageReady s)
    (hh : Allocated s (locN s "stable_logs", 24))
    (S Nd : List Nat) (hW : WorldTypedWith s S Nd)
    (ho : LogsLiveOwned s S Nd (locN s "logs"))
    (hs : ∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o)
    (hhead : Disj (locN s "logs", 24) (locN s "stable_logs", 24))
    (harray : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (locN s "stable_logs", 24))
    (hentry : ∀ i, i < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * i), 40) (locN s "stable_logs", 24))
    (hx : s.memaddrs (BitVec.ofNat 64 (locN s "stable_logs" + 8)))
    (mem' : BitVec 64 → HolWordLab 64)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    WorldTypedWith post S Nd ∧ worldOwned post S Nd = worldOwned s S Nd ∧
      TxEnv post ∧ LogsListOK post (locN s "logs") ∧
      LogsLiveOwned post S Nd (locN s "logs") ∧
      memW post (locN s "logs") = memW s (locN s "logs") ∧
      memW post (locN s "logs" + 8) = memW s (locN s "logs" + 8) := by
  have hptr := hp.1.1.1
  have htw := hptr.1.1.1.1
  have hA := htw.1.1
  have hbound := (stable_length_address_bound s hA.2 hh).1
  have hxin : Inside ((BitVec.ofNat 64 (locN s "stable_logs" + 8)).toNat, 8)
      (locN s "stable_logs") (locN s "stable_logs" + 24) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
    constructor <;> dsimp <;> omega
  obtain ⟨hW', heq, hE'⟩ := store_outside_worldOwned hA htw.2 hW hs hx hxin hm
  have hg : GuestInv {s with memory := mem'} :=
    guestInv_congr (s := s) rfl rfl rfl rfl hA.1
  have hl := hptr.1.1.2.1
  have hr := logsLiveOwned_disjoint_store hA.2 hA.1 hg hl ho hm
    (disj_of_inside_right hxin hhead) (disj_of_inside_right hxin harray)
    (fun i hi => disj_of_inside_right hxin (hentry i hi)) heq
  have hl' := hl.resolve_left hptr.1.2.2
  have hu : IvlUnhit s {s with memory := mem'} (locN s "logs", 24) :=
    ivlUnhit_single hm (by simp) (disj_of_inside_right hxin hhead)
  have hb := (ivl_allocated_bound hA.2 hl'.2.1).2
  exact ⟨hW', heq, hE', hr.1, hr.2,
    memW_eq_of_ivlUnhit hu hl'.1.1 hb ⟨by omega, by omega⟩,
    memW_eq_of_ivlUnhit hu (by have := hl'.1.1; omega) hb ⟨by omega, by omega⟩⟩

/-- The length store needs the separation facts supplied by fresh allocation,
as well as the word shapes of its two local operands. -/
def StableLengthPre : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4StableStorageReady s ∧
    Allocated s (locN s "stable_logs", 24) ∧
    s.locals.lookup (ofString "stable_logs") =
      some (.val (.word (BitVec.ofNat 64 (locN s "stable_logs")))) ∧
    s.locals.lookup (ofString "nl") = some (.val (.word (BitVec.ofNat 64 (locN s "nl")))) ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
      (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
      Disj (locN s "logs", 24) (locN s "stable_logs", 24) ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (locN s "stable_logs", 24) ∧
      ∀ i, i < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * i), 40) (locN s "stable_logs", 24)

/-- The allocation contract already supplies the capacity inequality for copy setup. -/
theorem stableLengthPre_copy_capacity {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64) :
    locN {s with memory := mem'} "nl" ≤ locN {s with memory := mem'} "stable_log_cap" := by
  exact (phase4StableCap_bounds s hp.1.1.1).2.1

/-- A memory-only length write retains the three typed setup operands. -/
theorem stableLengthPre_memory_operands {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (p : BitVec 64) (hl : s.locals.lookup (ofString "lp") = some (.val (.word p))) :
    ∃ n p w : BitVec 64,
      ({s with memory := mem'} : PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "nl") = some (.val (.word n)) ∧
      ({s with memory := mem'} : PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "lp") = some (.val (.word p)) ∧
      ({s with memory := mem'} : PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "stable_logs") = some (.val (.word w)) := by
  exact ⟨BitVec.ofNat 64 (locN s "nl"), p, BitVec.ofNat 64 (locN s "stable_logs"),
    hp.2.2.2.1, hl, hp.2.2.1⟩

/-- A positive natural local necessarily came from a word-shaped operand. -/
theorem stable_positive_local_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : String) (hp : 0 < locN s name) :
    s.locals.lookup (ofString name) =
      some (.val (.word (BitVec.ofNat 64 (locN s name)))) := by
  unfold locN at hp ⊢
  cases hlookup : s.locals.lookup (ofString name) with
  | none => simp [hlookup] at hp
  | some v =>
    cases v with
    | val value =>
      cases value with
      | word w => simp
    | rStruct _ => simp [hlookup] at hp
    | nStruct _ _ => simp [hlookup] at hp

/-- The allocation return supplies the canonical word representation of the
stable header pointer required by the length store. -/
theorem lst_new_stable_pointer_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let resumed := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    resumed.locals.lookup (ofString "stable_logs") =
      some (.val (.word (BitVec.ofNat 64 (locN resumed "stable_logs")))) := by
  obtain ⟨w, rfl, _⟩ := lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Returning the allocated header preserves the typed length operand. -/
theorem stable_length_operand_resume {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hn : s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl"))))) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    t.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN t "nl")))) := by
  simpa [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "nl" by decide] using hn

/-- Package the storage and operand premises needed before the length write. -/
theorem lst_new_stable_length_operands (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl")))))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Phase4StableStorageReady t ∧ Allocated t (locN t "stable_logs", 24) ∧
      t.locals.lookup (ofString "stable_logs") =
        some (.val (.word (BitVec.ofNat 64 (locN t "stable_logs")))) ∧
      t.locals.lookup (ofString "nl") =
        some (.val (.word (BitVec.ofNat 64 (locN t "nl")))) := by
  exact ⟨lst_new_stable_storage_resume h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_header_allocated h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_pointer_resume h s vs body callee ret v post hc hp ha hl hr,
    stable_length_operand_resume s post v hn⟩

def StableLengthPost : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧ LogsListOK s (locN s "logs") ∧
    LogsWorldOwned s (locN s "logs") ∧
    locN s "nl" = memW s (locN s "logs" + 8) ∧
    locN s "lp" = memW s (locN s "logs") ∧
    memW s (locN s "stable_logs" + 8) = locN s "nl" ∧
    memW s (locN s "stable_logs" + 8) ≤ memW s (locN s "stable_logs" + 16) ∧
    Allocated s (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    WordsOK s (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")

theorem hoare_stable_length_store :
    Hoare StableLengthPre
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → StableLengthPost t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hp, hh, hlocal, hnl, S, Nd, hW, ho, hs, hhead, harray, hentry⟩ := hp
  have hA := hp.1.1.1.1.1.1.1.1.1
  have hv' : v = .val (.word (BitVec.ofNat 64 (locN s "nl"))) := by
    change s.locals.lookup (ofString "nl") = some v at hv
    rw [hnl] at hv
    exact (Option.some.inj hv).symm
  subst v
  have hx' : x = BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hlocal, valueIsWord,
      valueWord, wordOpHOL, wordOp] at hx
    subst x
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (stable_length_address_bound s hA.2 hh).1] using
      (stable_length_address_bound s hA.2 hh).2
  subst x
  obtain ⟨hdom, he, hm⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  obtain ⟨hW', _, hE', hl', ho', h0, h8⟩ :=
    stable_length_store_source s hp hh S Nd hW ho hs hhead harray hentry hdom mem' hm
  have hg : GuestInv {s with memory := mem'} :=
    guestInv_congr (s := s) rfl rfl rfl rfl hA.1
  have hAp : ArenaReady {s with memory := mem'} := ⟨hg, hA.2⟩
  refine ⟨⟨worldOK_of_parts hAp hW', hE'⟩, hl', ⟨S, Nd, hW', ho'⟩,
    ?_, ?_, stable_length_store_value s hp mem' he,
    stable_length_store_fits s hp hA.2 hh mem' he hm,
    stable_length_store_backing s hp hA.2 hh mem' _ he hm⟩
  · exact hp.1.1.1.1.2.1.trans h8.symm
  · exact hp.1.1.1.2.trans h0.symm

theorem stableLengthPost_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hl : ∀ name ∈ (["index", "logs", "nl", "lp", "stable_logs", "stable_log_cap"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hp : StableLengthPost s) : StableLengthPost {s with locals := locals, clock := k} := by
  have he : ∀ name ∈ (["index", "logs", "nl", "lp", "stable_logs", "stable_log_cap"] : List String),
      locN {s with locals := locals, clock := k} name = locN s name :=
    fun name hn => locN_congr s locals k name (hl name hn)
  obtain ⟨hW, hlogs, hown, hnl, hlp, hlen, hcap, ha, hw⟩ := hp
  refine ⟨⟨localsFree_worldOK s locals k hW.1,
    txEnv_with_locals s locals k (hl "index" (by simp)) hW.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he "logs" (by simp)]
    exact (R13Shards.logsListOK_with_locals s locals k _).mpr hlogs
  · rw [he "logs" (by simp)]
    exact logsWorldOwned_with_locals locals k hown
  · rw [he "nl" (by simp), he "logs" (by simp)]; exact hnl
  · rw [he "lp" (by simp), he "logs" (by simp)]; exact hlp
  · rw [he "stable_logs" (by simp), he "nl" (by simp)]; exact hlen
  · rw [he "stable_logs" (by simp)]; exact hcap
  · rw [he "stable_logs" (by simp), he "stable_log_cap" (by simp)]; exact ha
  · rw [he "stable_logs" (by simp), he "stable_log_cap" (by simp)]; exact hw

theorem localsOnly_stableLengthPost :
    LocalsOnly ["index", "logs", "nl", "lp", "stable_logs", "stable_log_cap"] StableLengthPost := by
  intro F s locals k hl hp
  exact stableLengthPost_with_locals s locals k hl hp

/-- Initializing the stable backing operand preserves the length postcondition. -/
theorem stableLengthPost_set_backing {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (hp : StableLengthPost s) :
    StableLengthPost (setVarHOLFinite (ofString "stable_lp") v s) := by
  apply stableLengthPost_with_locals s _ s.clock _ hp
  intro name hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ofString]

/-- Reassemble the length postcondition after a copy write. The destination
header and source header are framed, and word validity is transported by the
guest memory-domain invariant. -/
theorem stableLengthPost_copy_store {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableLengthPost s)
    (hworld : TxWorld {s with memory := mem'})
    (hlogs : LogsListOK {s with memory := mem'} (locN s "logs"))
    (hown : LogsWorldOwned {s with memory := mem'} (locN s "logs"))
    (hsrc0 : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hsrc8 : memW {s with memory := mem'} (locN s "logs" + 8) = memW s (locN s "logs" + 8))
    (hdst0 : memW {s with memory := mem'} (locN s "stable_logs") = memW s (locN s "stable_logs"))
    (hdst8 : memW {s with memory := mem'} (locN s "stable_logs" + 8) =
      memW s (locN s "stable_logs" + 8))
    (hdst16 : memW {s with memory := mem'} (locN s "stable_logs" + 16) =
      memW s (locN s "stable_logs" + 16)) :
    StableLengthPost {s with memory := mem'} := by
  obtain ⟨hW, _, _, hnl, hlp, hlen, hcap, ha, hw⟩ := hp
  refine ⟨hworld, hlogs, hown, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hnl.trans hsrc8.symm
  · exact hlp.trans hsrc0.symm
  · change memW {s with memory := mem'} (locN s "stable_logs" + 8) = locN s "nl"
    rw [hdst8]; exact hlen
  · change memW {s with memory := mem'} (locN s "stable_logs" + 8) ≤
      memW {s with memory := mem'} (locN s "stable_logs" + 16)
    rw [hdst8, hdst16]; exact hcap
  · change Allocated {s with memory := mem'}
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hdst0]; exact ha
  · change WordsOK {s with memory := mem'}
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hdst0]
    exact wordsOK_transfer hW.1.1.1 hworld.1.1.1 hw

/-- Connect the actual length write at spine position 133 to its continuation. -/
theorem phase4StableLength_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn StableLengthPost tail b) :
    TerminatingProgBoundedOn StableLengthPre
      (spinePlug 1 (spineAt 133 ptxCode) tail) b := by
  have hb := @seq_bound_trans _ _ _ _ _ _
    (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
    hoare_stable_length_store htail
  unfold ptxCode
  intro F s hc hp
  have hr := hb s hc hp
  simp only [Nat.zero_add] at hr
  exact hr

/-- The copied length inherits the source list's receipt-size bound. -/
theorem stableLengthPost_length_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0) :
    locN s "nl" < 2 ^ 28 ∧ memW s (locN s "stable_logs" + 8) < 2 ^ 28 := by
  have hl := hp.2.1.resolve_left hn
  have hb : locN s "nl" < 2 ^ 28 := by
    rw [hp.2.2.2.1]
    exact hl.2.2.1
  exact ⟨hb, hp.2.2.2.2.2.1.symm ▸ hb⟩

/-- At loop exit, equality of the live pointer cells transfers log-entry
validity from the source list to the stable list. -/
theorem stable_copy_complete {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hcap : locN s "nl" ≤ locN s "stable_log_cap")
    (hcopy : ∀ i, i < locN s "nl" →
      memW s (memW s (locN s "stable_logs") + 8 * i) =
        memW s (memW s (locN s "logs") + 8 * i)) :
    PtxReceiptsDone s := by
  have hl := hp.2.1.resolve_left hn
  have hb := stableLengthPost_length_bound s hp hn
  have hlen := hp.2.2.2.2.2.1
  have hfits := hp.2.2.2.2.2.2.1
  have hwords := hp.2.2.2.2.2.2.2.2
  refine ⟨hp.1, Or.inr ⟨hh, ha, hb.2, hfits, ?_⟩, hb.2⟩
  intro i hi
  rw [hlen] at hi
  refine ⟨?_, ?_⟩
  · apply hwords.2.2 i
    have hic : i < locN s "stable_log_cap" := lt_of_lt_of_le hi hcap
    simpa using hic
  · rw [hcopy i hi]
    exact (hl.2.2.2.2 i (by rw [← hp.2.2.2.1]; exact hi)).2

/-- The stable-copy loop records equality only for the already copied prefix. -/
def StableCopyInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
    WordsOK s (locN s "stable_logs", 24) ∧
    Allocated s (locN s "stable_logs", 24) ∧
    locN s "nl" ≤ locN s "stable_log_cap" ∧
    ∀ i, i < locN s "i" → i < locN s "nl" →
      memW s (memW s (locN s "stable_logs") + 8 * i) =
        memW s (memW s (locN s "logs") + 8 * i)

/-- The loop invariant survives clock changes and unrelated temporary locals. -/
theorem stableCopyInv_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hl : ∀ name ∈ (["index", "logs", "nl", "lp", "stable_logs", "stable_log_cap", "i"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hp : StableCopyInv s) : StableCopyInv {s with locals := locals, clock := k} := by
  have he : ∀ name ∈ (["logs", "nl", "stable_logs", "stable_log_cap", "i"] : List String),
      locN {s with locals := locals, clock := k} name = locN s name := by
    intro name hn
    apply locN_congr s locals k name
    apply hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    tauto
  refine ⟨stableLengthPost_with_locals s locals k (fun name hn => hl name (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; tauto)) hp.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he "logs" (by simp)]; exact hp.2.1
  · rw [he "stable_logs" (by simp)]; exact hp.2.2.1
  · rw [he "stable_logs" (by simp)]; exact hp.2.2.2.1
  · rw [he "nl" (by simp), he "stable_log_cap" (by simp)]; exact hp.2.2.2.2.1
  · intro j hj hn
    rw [he "i" (by simp)] at hj
    rw [he "nl" (by simp)] at hn
    rw [he "stable_logs" (by simp), he "logs" (by simp)]
    exact hp.2.2.2.2.2 j hj hn

/-- Clock consumption at a while boundary preserves the copy invariant. -/
theorem stableCopyInv_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) : StableCopyInv (decClockHOLFinite s) := by
  exact stableCopyInv_with_locals s s.locals (s.clock - 1) (fun _ _ => rfl) hp

theorem stableCopyInv_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hcap : locN s "nl" ≤ locN s "stable_log_cap")
    (hj : locN s "i" = 0) : StableCopyInv s := by
  refine ⟨hp, hn, hh, ha, hcap, ?_⟩
  intro i hi _
  omega

/-- The actual zero counter initialization establishes the copy invariant. -/
theorem stableCopyInv_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hcap : locN s "nl" ≤ locN s "stable_log_cap") :
    StableCopyInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) := by
  have hpost : StableLengthPost (setVarHOLFinite (ofString "i") (.val (.word 0)) s) :=
    LocalsOnly.setVar localsOnly_stableLengthPost (by decide) _ s hp
  apply stableCopyInv_zero _ hpost
  · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "logs" from by decide] using hn
  · change WordsOK s _
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "stable_logs" from by decide] using hh
  · change Allocated s _
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "stable_logs" from by decide] using ha
  · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nl" from by decide,
      show ofString "i" ≠ ofString "stable_log_cap" from by decide] using hcap
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Hoare rule for the counter initialization before the stable-copy loop. -/
theorem hoare_stableCopy_init :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap")
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    have hv' : v = .val (.word 0) := by
      simpa [evalAt, evalHOLExact] using hv.symm
    subst v
    exact stableCopyInv_init s hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  · intro F s hp hr
    exact absurd hr (by simp)

theorem stableCopyInv_source_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hj : locN s "i" < locN s "nl") :
    WordAt s (locN s "lp" + 8 * locN s "i") ∧
      LogEntryOK s (memW s (locN s "lp" + 8 * locN s "i")) := by
  have hl := hp.1.2.1.resolve_left hp.2.1
  rw [hp.1.2.2.2.2.1]
  exact hl.2.2.2.2 (locN s "i") (by rw [← hp.1.2.2.2.1]; exact hj)

theorem stableCopyInv_destination_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    WordAt s (memW s (locN s "stable_logs") + 8 * locN s "i") := by
  have hw := hp.1.2.2.2.2.2.2.2.2
  have hcap := hp.2.2.2.2.1
  apply hw.2.2 (locN s "i")
  have hic : locN s "i" < locN s "stable_log_cap" := lt_of_lt_of_le hi hcap
  simpa using hic

theorem stableCopyInv_destination_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    memW s (locN s "stable_logs") + 8 * locN s "nl" ≤ 2 ^ 64 ∧
      memW s (locN s "stable_logs") + 8 * locN s "i" < 2 ^ 64 := by
  have ha := hp.1.2.2.2.2.2.2.2.1
  have hA := hp.1.1.1.1.2
  have hb := (ivl_allocated_bound hA ha).2
  have hc := hp.2.2.2.2.1
  dsimp at hb
  constructor <;> omega

theorem stableCopyInv_source_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    locN s "lp" + 8 * locN s "nl" ≤ 2 ^ 64 ∧
      locN s "lp" + 8 * locN s "i" < 2 ^ 64 := by
  obtain ⟨S, Nd, _, ho⟩ := hp.1.2.2.1
  have hb := (ivl_allocated_bound hp.1.1.1.1.2 (ho hp.2.1).1).2
  rw [hp.1.2.2.2.2.1, hp.1.2.2.2.1] at *
  dsimp at hb
  constructor <;> omega

theorem stableCopyInv_source_aligned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    locN s "lp" % 8 = 0 := by
  rw [hp.1.2.2.2.2.1]
  apply logsListOK_array_aligned hp.1.1.1.1.1 hp.1.2.1 hp.2.1
  rw [← hp.1.2.2.2.1]
  omega

theorem stableCopyInv_offset_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    (BitVec.ofNat 64 (locN s "i") * (8 : BitVec 64)).toNat = 8 * locN s "i" := by
  have hb := (stableCopyInv_source_bound s hp hi).2
  have hi' : locN s "i" < 2 ^ 64 := by omega
  have hm : locN s "i" * 8 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi']
  change locN s "i" * 8 % 2 ^ 64 = 8 * locN s "i"
  rw [Nat.mod_eq_of_lt hm, Nat.mul_comm]

theorem stableCopyInv_address_words {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    (BitVec.ofNat 64 (locN s "lp") +
      BitVec.ofNat 64 (8 * locN s "i")).toNat = locN s "lp" + 8 * locN s "i" ∧
    (BitVec.ofNat 64 (memW s (locN s "stable_logs")) +
      BitVec.ofNat 64 (8 * locN s "i")).toNat =
        memW s (locN s "stable_logs") + 8 * locN s "i" := by
  have hs := (stableCopyInv_source_bound s hp hi).2
  have hd := (stableCopyInv_destination_bound s hp hi).2
  have hi' : 8 * locN s "i" < 2 ^ 64 := by omega
  have hs' : locN s "lp" < 2 ^ 64 := by omega
  have hd' : memW s (locN s "stable_logs") < 2 ^ 64 := by omega
  constructor <;> simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hs', Nat.mod_eq_of_lt hd',
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd]

/-- The natural remaining-copy rank has a uniform bound from the source length. -/
theorem stableCopyInv_rank_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) : locN s "nl" - locN s "i" < 2 ^ 28 := by
  have hn := (stableLengthPost_length_bound s hp.1 hp.2.1).1
  omega

/-- Interpret the signed loop comparison in the bounded natural index range. -/
theorem stableCopyInv_guard {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (i n w : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hib : locN s "i" < 2 ^ 63)
    (he : evalAt s (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nl"))) = some (.val (.word w)))
    (hw : w ≠ 0) : locN s "i" < locN s "nl" := by
  have hnb := (stableLengthPost_length_bound s hp.1 hp.2.1).1
  have hil : locN s "i" = i.toNat := by simp [locN, hi]
  have hnl : locN s "nl" = n.toNat := by simp [locN, hn]
  rw [hil] at hib ⊢
  rw [hnl] at hnb ⊢
  have hnb' : n.toNat < 2 ^ 63 := by omega
  have hc : Compiler.Encoders.Asm.wordCmpHOL .less i n = true := by
    by_contra hc
    simp [evalAt, evalHOLExact, hi, hn, hc] at he
    exact hw he.symm
  norm_num at hib hnb'
  simpa [Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess,
    hib, hnb'] using hc

/-- A false signed guard certifies completion of the bounded copy prefix. -/
theorem stableCopyInv_guard_false {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (i n : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hib : locN s "i" < 2 ^ 63)
    (he : evalAt s (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nl"))) = some (.val (.word 0))) :
    locN s "nl" ≤ locN s "i" := by
  have hnb := (stableLengthPost_length_bound s hp.1 hp.2.1).1
  have hil : locN s "i" = i.toNat := by simp [locN, hi]
  have hnl : locN s "nl" = n.toNat := by simp [locN, hn]
  rw [hil] at hib ⊢
  rw [hnl] at hnb ⊢
  have hnb' : n.toNat < 2 ^ 63 := by omega
  norm_num at hib hnb'
  have hnot : ¬ i.toNat < n.toNat := by
    simpa [evalAt, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL,
      Compiler.Encoders.Asm.holAsmSignedLess, hib, hnb'] using he
  omega

theorem stableCopyInv_exit {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hexit : locN s "nl" ≤ locN s "i") :
    PtxReceiptsDone s := by
  obtain ⟨hp, hn, hh, ha, hcap, hcopy⟩ := hp
  exact stable_copy_complete s hp hn hh ha hcap
    (fun i hi => hcopy i (lt_of_lt_of_le hi hexit) hi)

/-- Exhaustion of the natural copy rank yields the receipt postcondition. -/
theorem stableCopyInv_rank_zero_exit {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hz : locN s "nl" - locN s "i" = 0) :
    PtxReceiptsDone s := by
  apply stableCopyInv_exit s hp
  omega

/-- Separation from the whole backing allocation implies separation from
the current copy destination, including its machine-address conversion. -/
theorem stableCopyInv_destination_disj {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl")
    {region : Ivl}
    (hd : Disj region (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    Disj region
      ((BitVec.ofNat 64 (memW s (locN s "stable_logs") + 8 * locN s "i")).toNat, 8) := by
  apply disj_of_inside_right ?_ hd
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (stableCopyInv_destination_bound s hp hi).2]
  have hc := hp.2.2.2.2.1
  constructor <;> dsimp <;> omega

/-- A copy write preserves any allocated header separated from the backing
array. This supplies the source and destination header frame obligations. -/
theorem stableCopyInv_header_unhit {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl") (p : Nat)
    (ha : Allocated s (p, 24)) (hal : p % 8 = 0)
    (hd : Disj (p, 24) (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a) :
    memW {s with memory := mem'} p = memW s p ∧
      memW {s with memory := mem'} (p + 8) = memW s (p + 8) ∧
      memW {s with memory := mem'} (p + 16) = memW s (p + 16) := by
  have hu : IvlUnhit s {s with memory := mem'} (p, 24) :=
    ivlUnhit_single hm (by simp) (stableCopyInv_destination_disj s hp hi hd)
  have hb := (ivl_allocated_bound hp.1.1.1.1.2 ha).2
  refine ⟨memW_eq_of_ivlUnhit hu hal hb ⟨by omega, by omega⟩, ?_, ?_⟩
  · exact memW_eq_of_ivlUnhit hu (by omega) hb ⟨by omega, by omega⟩
  · exact memW_eq_of_ivlUnhit hu (by omega) hb ⟨by omega, by omega⟩

/-- The semantic memory step of the stable-copy loop extends the copied
prefix by one cell. The source is framed, and destination addresses do not wrap. -/
theorem stable_copy_prefix_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (dst src i n : Nat)
    (hi : i < n) (hbound : dst + 8 * n ≤ 2 ^ 64)
    (hprefix : ∀ j, j < i → memW s (dst + 8 * j) = memW s (src + 8 * j))
    (hwrite : memW {s with memory := mem'} (dst + 8 * i) = memW s (src + 8 * i))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (dst + 8 * i) → mem' a = s.memory a)
    (hsource : ∀ j, j < n →
      memW {s with memory := mem'} (src + 8 * j) = memW s (src + 8 * j)) :
    ∀ j, j < i + 1 →
      memW {s with memory := mem'} (dst + 8 * j) =
        memW {s with memory := mem'} (src + 8 * j) := by
  intro j hj
  rw [hsource j (by omega)]
  by_cases he : j = i
  · subst j; exact hwrite
  have hji : j < i := by omega
  have hdi : dst + 8 * i < 2 ^ 64 := by omega
  have hdj : dst + 8 * j < 2 ^ 64 := by omega
  have hne : BitVec.ofNat 64 (dst + 8 * j) ≠ BitVec.ofNat 64 (dst + 8 * i) := by
    intro heq
    have heq' := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdi, Nat.mod_eq_of_lt hdj] at heq'
    omega
  calc
    memW {s with memory := mem'} (dst + 8 * j) = memW s (dst + 8 * j) := by
      simp only [memW]
      rw [hm _ hne]
    _ = memW s (src + 8 * j) := hprefix j hji

/-- Instantiate prefix extension with the addresses and bound carried by
the stable-copy invariant. -/
theorem stableCopyInv_store_prefix {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl")
    (hwrite : memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a)
    (hsource : ∀ j, j < locN s "nl" →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (hsrc : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hdst : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs")) :
    ∀ j, j < locN s "i" + 1 →
      memW {s with memory := mem'}
          (memW {s with memory := mem'} (locN s "stable_logs") + 8 * j) =
        memW {s with memory := mem'}
          (memW {s with memory := mem'} (locN s "logs") + 8 * j) := by
  intro j hj
  rw [hsrc, hdst]
  exact stable_copy_prefix_step s mem' _ _ _ _ hi
    (stableCopyInv_destination_bound s hp hi).1
    (fun k hk => hp.2.2.2.2.2 k hk (lt_trans hk hi)) hwrite hm hsource j hj

/-- A destination write outside the source array preserves every source
pointer cell, providing the frame premise of `stable_copy_prefix_step`. -/
theorem stable_copy_source_cells {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (src n : Nat) (x : BitVec 64)
    (hA : ArenaOK s) (ha : Allocated s (src, 8 * n)) (hal : src % 8 = 0)
    (hd : Disj (src, 8 * n) (x.toNat, 8))
    (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    ∀ j, j < n → memW {s with memory := mem'} (src + 8 * j) = memW s (src + 8 * j) := by
  have hu : IvlUnhit s {s with memory := mem'} (src, 8 * n) :=
    ivlUnhit_single hm (fun _ => hal) hd
  intro j hj
  exact memW_eq_of_ivlUnhit hu (by omega) (ivl_allocated_bound hA ha).2
    ⟨by dsimp; omega, by dsimp; omega⟩

/-- The stable length write preserves each source pointer cell, enabling
record separation to be transported into the copy-loop entry state. -/
theorem stable_length_source_cells {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (src n : Nat)
    (hA : ArenaOK s) (hh : Allocated s (locN s "stable_logs", 24))
    (ha : Allocated s (src, 8 * n)) (hal : src % 8 = 0)
    (hd : Disj (src, 8 * n) (locN s "stable_logs", 24))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) →
      mem' a = s.memory a) :
    ∀ j, j < n → memW {s with memory := mem'} (src + 8 * j) =
      memW s (src + 8 * j) := by
  apply stable_copy_source_cells s mem' src n _ hA ha hal _ hm
  apply disj_of_inside_right _ hd
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (stable_length_address_bound s hA hh).1]
  constructor <;> dsimp <;> omega

/-- The length-store precondition discharges source-array framing without
requiring a separate allocation or alignment hypothesis. -/
theorem stableLengthPre_source_cells {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a) :
    ∀ j, j < memW s (locN s "logs" + 8) →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j) := by
  obtain ⟨S, Nd, hW, ho, hs, hh, ha, he⟩ := hp.2.2.2.2
  have hptr := hp.1.1.1.1
  have htw := hptr.1.1.1.1
  intro j hj
  exact stable_length_source_cells s mem' _ _ htw.1.1.2 hp.2.1
    (ho hptr.1.2.2).1
    (logsListOK_array_aligned htw.1.1.1 hptr.1.1.2.1 hptr.1.2.2 (by omega))
    ha hm j hj

/-- Specialize source-array framing to the current stable-copy write. -/
theorem stableCopyInv_source_preserved {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl")
    (hd : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a) :
    ∀ j, j < locN s "nl" →
      memW {s with memory := mem'} (locN s "lp" + 8 * j) =
        memW s (locN s "lp" + 8 * j) := by
  obtain ⟨S, Nd, _, ho⟩ := hp.1.2.2.1
  have ha : Allocated s (locN s "lp", 8 * locN s "nl") := by
    rw [hp.1.2.2.2.2.1, hp.1.2.2.2.1]
    exact (ho hp.2.1).1
  exact stable_copy_source_cells s mem' _ _ _ hp.1.1.1.1.2 ha
    (stableCopyInv_source_aligned s hp hi)
    (stableCopyInv_destination_disj s hp hi hd) hm

/-- A copy destination outside the world footprint preserves world typing,
the footprint itself, and the transaction environment. -/
theorem stableCopyInv_world_preserved {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl") (S Nd : List Nat)
    (hW : WorldTypedWith s S Nd)
    (hd : ∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)
    (hx : s.memaddrs (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i")))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a) :
    WorldTypedWith {s with memory := mem'} S Nd ∧
      worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
      TxEnv {s with memory := mem'} := by
  apply store_outside_worldOwned hp.1.1.1.1 hp.1.1.2 hW hd hx ?_ hm
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (stableCopyInv_destination_bound s hp hi).2]
  have hc := hp.2.2.2.2.1
  constructor <;> dsimp <;> omega

/-- Preserve source validity and live ownership across the current copy
write using separation from the complete stable backing allocation. -/
theorem stableCopyInv_logs_preserved {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl") (S Nd : List Nat)
    (ho : LogsLiveOwned s S Nd (locN s "logs"))
    (hg : GuestInv {s with memory := mem'})
    (hworld : worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd)
    (hh : Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (ha : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a) :
    LogsListOK {s with memory := mem'} (locN s "logs") ∧
      LogsLiveOwned {s with memory := mem'} S Nd (locN s "logs") := by
  exact logsLiveOwned_disjoint_store hp.1.1.1.1.2 hp.1.1.1.1.1 hg hp.1.2.1 ho hm
    (stableCopyInv_destination_disj s hp hi hh)
    (stableCopyInv_destination_disj s hp hi ha)
    (fun j hj => stableCopyInv_destination_disj s hp hi (he j hj)) hworld

/-- Assemble world, source ownership, and header fields of the length
postcondition after a separated copy write. -/
theorem stableCopyInv_store_post {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl") (S Nd : List Nat)
    (hW : WorldTypedWith s S Nd) (ho : LogsLiveOwned s S Nd (locN s "logs"))
    (hworld : ∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)
    (hh : Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hd : Disj (locN s "stable_logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (ha : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hx : s.memaddrs (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i")))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a) :
    StableLengthPost {s with memory := mem'} := by
  obtain ⟨hW', hw', hE'⟩ := stableCopyInv_world_preserved s mem' hp hi S Nd hW hworld hx hm
  have hg : GuestInv {s with memory := mem'} :=
    guestInv_congr (s := s) rfl rfl rfl rfl hp.1.1.1.1.1
  obtain ⟨hl', ho'⟩ := stableCopyInv_logs_preserved s mem' hp hi S Nd ho hg hw' hh ha he hm
  have hl := hp.1.2.1.resolve_left hp.2.1
  obtain ⟨hs0, hs8, _⟩ := stableCopyInv_header_unhit s mem' hp hi _ hl.2.1 hl.1.1 hh hm
  obtain ⟨hd0, hd8, hd16⟩ := stableCopyInv_header_unhit s mem' hp hi _
    hp.2.2.2.1 hp.2.2.1.1 hd hm
  exact stableLengthPost_copy_store s mem' hp.1
    ⟨worldOK_of_parts ⟨hg, hp.1.1.1.1.2⟩ hW', hE'⟩ hl' ⟨S, Nd, hW', ho'⟩
    hs0 hs8 hd0 hd8 hd16

/-- Multiplication in the copy offset evaluates to the corresponding word. -/
theorem stable_copy_mul_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w))) :
    evalAt s (.panop .mul [.var .local (ofString "i"), .const 8]) =
      some (.val (.word (w * 8))) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord, panOpHOL]

/-- The copy offset has no modular wrap under the source length bound. -/
theorem stable_copy_mul_nat {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : locN s "i" < locN s "nl") :
    (w * 8).toNat = 8 * locN s "i" := by
  have hwi : locN s "i" = w.toNat := by simp [locN, hw]
  have hn := (stableLengthPost_length_bound s hp.1 hp.2.1).1
  rw [BitVec.toNat_mul]
  change (w.toNat * 8) % 2 ^ 64 = 8 * locN s "i"
  rw [Nat.mod_eq_of_lt (by omega), ← hwi, Nat.mul_comm]

/-- Identify the evaluated offset directly with the natural copy index. -/
theorem stable_copy_offset_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : locN s "i" < locN s "nl") :
    evalAt s (.panop .mul [.var .local (ofString "i"), .const 8]) =
      some (.val (.word (BitVec.ofNat 64 (8 * locN s "i")))) := by
  rw [stable_copy_mul_eval s w hw]
  have he : w * 8 = BitVec.ofNat 64 (8 * locN s "i") := by
    rw [← stable_copy_mul_nat s w hp hw hi]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [he]

/-- Evaluate the source address used by the copy load without modular wrap. -/
theorem stable_copy_source_address_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w p : BitVec 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hi : locN s "i" < locN s "nl") :
    evalAt s (.op .add [.var .local (ofString "lp"),
      .panop .mul [.var .local (ofString "i"), .const 8]]) =
      some (.val (.word (BitVec.ofNat 64 (locN s "lp" + 8 * locN s "i")))) := by
  have hpn : locN s "lp" = p.toNat := by simp [locN, hl]
  have hpw : p = BitVec.ofNat 64 (locN s "lp") := by
    rw [hpn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hoff := stable_copy_offset_eval s w hp hw hi
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hoff ⊢
  rw [hl, hoff]
  simp only [valueIsWord, valueWord, List.all, List.map, Option.map,
    Bool.and_self, ↓reduceIte, wordOpHOL, wordOp, List.foldr]
  have he := (stableCopyInv_address_words s hp hi).1
  rw [hpw]
  rw [← he, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp

/-- Evaluate the destination address of the actual stable-copy store. -/
theorem stable_copy_destination_address_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w p : BitVec 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hl : s.locals.lookup (ofString "stable_lp") = some (.val (.word p)))
    (hptr : p.toNat = memW s (locN s "stable_logs"))
    (hi : locN s "i" < locN s "nl") :
    evalAt s (.op .add [.var .local (ofString "stable_lp"),
      .panop .mul [.var .local (ofString "i"), .const 8]]) =
      some (.val (.word (BitVec.ofNat 64 (memW s (locN s "stable_logs") + 8 * locN s "i")))) := by
  have hpw : p = BitVec.ofNat 64 (memW s (locN s "stable_logs")) := by
    rw [← hptr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hoff := stable_copy_offset_eval s w hp hw hi
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hoff ⊢
  rw [hl, hoff]
  simp only [valueIsWord, valueWord, List.all, List.map, Option.map,
    Bool.and_self, ↓reduceIte, wordOpHOL, wordOp, List.foldr]
  have he := (stableCopyInv_address_words s hp hi).2
  rw [hpw]
  rw [← he, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp

/-- The copy source load returns the word at the indexed source cell. -/
theorem stable_copy_source_load_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w p : BitVec 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hi : locN s "i" < locN s "nl") :
    evalAt s phase4LogCopySrc = some (.val (.word
      (BitVec.ofNat 64 (memW s (locN s "lp" + 8 * locN s "i"))))) := by
  have he := stable_copy_source_address_eval s w p hp hw hl hi
  obtain ⟨v, hd, hm⟩ := (stableCopyInv_source_word s hp hi).1
  have hn : memW s (locN s "lp" + 8 * locN s "i") = v.toNat := by
    simp [memW, hm]
  unfold phase4LogCopySrc
  simp only [evalAt, evalHOLExact, evalListHOLExact] at he ⊢
  rw [he]
  simp [valueIsWord, valueWord, memLoadHOLExact, hd, hm, hn,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Loading the stable header yields the backing-pointer operand for copy setup. -/
theorem stable_backing_load_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64)
    (hw : s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
    (hp : WordAt s (locN s "stable_logs")) :
    evalAt s (.load .one (.var .local (ofString "stable_logs"))) =
      some (.val (.word (BitVec.ofNat 64 (memW s (locN s "stable_logs"))))) := by
  have hl : locN s "stable_logs" = w.toNat := by simp [locN, hw]
  obtain ⟨v, hd, hm⟩ := hp
  have hn : memW s (locN s "stable_logs") = v.toNat := by simp [memW, hm]
  rw [hl] at hd hm
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hd hm
  simp [evalAt, evalHOLExact, hw, valueIsWord, valueWord, memLoadHOLExact,
    hd, hm, hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The concrete backing load initializes its local with the header's word. -/
theorem stable_backing_load_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
    (hp : WordAt s (locN s "stable_logs"))
    (he : evalAt s (.load .one (.var .local (ofString "stable_logs"))) = some v) :
    ∃ q : BitVec 64,
      (setVarHOLFinite (ofString "stable_lp") v s).locals.lookup
        (ofString "stable_lp") = some (.val (.word q)) ∧
      q.toNat = memW s (locN s "stable_logs") := by
  have hv := stable_backing_load_eval s w hw hp
  rw [he] at hv
  have hv' := Option.some.inj hv
  subst v
  obtain ⟨q, hd, hm⟩ := hp
  have hn : memW s (locN s "stable_logs") = q.toNat := by simp [memW, hm]
  refine ⟨q, ?_, hn.symm⟩
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hn]

/-- Backing initialization retains both source operands required by the loop. -/
theorem stable_backing_load_operands {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w n p : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hp : WordAt s (locN s "stable_logs"))
    (he : evalAt s (.load .one (.var .local (ofString "stable_logs"))) = some v) :
    let t := setVarHOLFinite (ofString "stable_lp") v s
    t.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
    t.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
    ∃ q : BitVec 64, t.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
      q.toNat = memW t (locN t "stable_logs") := by
  obtain ⟨q, hq, hd⟩ := stable_backing_load_local s w v hw hp he
  refine ⟨?_, ?_, q, hq, ?_⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hn
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hl
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString, memW, locN] using hd

/-- A successful semantic copy store writes the indexed source value. -/
theorem stable_copy_store_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w p : BitVec 64)
    (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hi : locN s "i" < locN s "nl") (v : ValueHOL 64)
    (hv : evalAt s phase4LogCopySrc = some v)
    (he : mem' (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i")) =
      .word (BitVec.ofNat 64 (memW s (locN s "lp" + 8 * locN s "i")))) :
    v = .val (.word (BitVec.ofNat 64
      (memW s (memW s (locN s "logs") + 8 * locN s "i")))) ∧
    memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i") := by
  have hv' := stable_copy_source_load_eval s w p hp hw hl hi
  have hn : memW s (locN s "lp" + 8 * locN s "i") < 2 ^ 64 := by
    unfold memW
    cases s.memory (BitVec.ofNat 64 (locN s "lp" + 8 * locN s "i")) with
    | word a => exact a.isLt
  constructor
  · rw [hv] at hv'
    rw [hp.1.2.2.2.2.1] at hv'
    exact Option.some.inj hv'
  · change (match mem' _ with | .word a => a.toNat) = _
    rw [he]
    dsimp only
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, hp.1.2.2.2.2.1]

/-- The stored word is exactly the source pointer, with no truncation. -/
theorem stable_copy_written_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl")
    (he : mem' (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i")) =
      .word (BitVec.ofNat 64 (memW s (locN s "lp" + 8 * locN s "i")))) :
    memW {s with memory := mem'}
        (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i") := by
  obtain ⟨w, _, hw⟩ := (stableCopyInv_source_word s hp hi).1
  have hv : memW s (locN s "lp" + 8 * locN s "i") = w.toNat := by
    simp [memW, hw]
  have hdest : memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") = w.toNat := by
    change (mem' (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i"))).1.toNat = w.toNat
    rw [he, hv]
    simp
  rw [hdest, ← hv, hp.1.2.2.2.2.1]

/-- Extract the value and frame facts from the actual one-word copy store. -/
theorem stable_copy_store_semantics {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w p : BitVec 64)
    (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hi : locN s "i" < locN s "nl") (v : ValueHOL 64)
    (hv : evalAt s phase4LogCopySrc = some v)
    (hst : @panMemStoresHOL 64 _
      (BitVec.ofNat 64 (memW s (locN s "stable_logs") + 8 * locN s "i"))
      (flattenHOL v) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    s.memaddrs (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i")) ∧
    memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i") ∧
    ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a := by
  have hv' := stable_copy_source_load_eval s w p hp hw hl hi
  rw [hv] at hv'
  have heq := Option.some.inj hv'
  subst v
  obtain ⟨hd, he, hm⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  exact ⟨hd, stable_copy_written_value s mem' hp hi he, hm⟩

/-- Operand shapes and allocation separation required by the copy store. -/
def StableCopyStorePre : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => StableCopyInv s ∧ locN s "i" < locN s "nl" ∧
    (∃ w p q : BitVec 64,
      s.locals.lookup (ofString "i") = some (.val (.word w)) ∧
      s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
      s.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
      q.toNat = memW s (locN s "stable_logs")) ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
      (∀ o ∈ worldOwned s S Nd,
        Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o) ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")

/-- Framed source pointers retain record/backing separation after a copy
write. This supplies the record-separation premise for the next iteration. -/
theorem stable_copy_record_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64)
    (hs : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hn : memW {s with memory := mem'} (locN s "logs" + 8) =
      memW s (locN s "logs" + 8))
    (hd : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs"))
    (ha : ∀ j, j < memW s (locN s "logs" + 8) →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    let t := {s with memory := mem'}
    ∀ j, j < memW t (locN t "logs" + 8) →
      Disj (memW t (memW t (locN t "logs") + 8 * j), 40)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  dsimp only
  intro j hj
  change j < memW {s with memory := mem'} (locN s "logs" + 8) at hj
  rw [hn] at hj
  change Disj (memW {s with memory := mem'}
    (memW {s with memory := mem'} (locN s "logs") + 8 * j), 40)
    (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
  rw [hs, hd, ha j hj]
  exact he j hj

/-- Carry source-record separation through the stable length update using
the source backing's allocation and disjointness from the stable header. -/
theorem stable_length_record_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64)
    (hA : ArenaOK s) (hh : Allocated s (locN s "stable_logs", 24))
    (ha : Allocated s (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8)))
    (hal : memW s (locN s "logs") % 8 = 0)
    (hdisj : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (locN s "stable_logs", 24))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hs : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hn : memW {s with memory := mem'} (locN s "logs" + 8) = memW s (locN s "logs" + 8))
    (hd : memW {s with memory := mem'} (locN s "stable_logs") = memW s (locN s "stable_logs"))
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    let t := {s with memory := mem'}
    ∀ j, j < memW t (locN t "logs" + 8) →
      Disj (memW t (memW t (locN t "logs") + 8 * j), 40)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  exact stable_copy_record_separation s mem' hs hn hd
    (stable_length_source_cells s mem' _ _ hA hh ha hal hdisj hm) he

/-- The length-store contract preserves record/backing separation with no
additional source-cell framing obligations. -/
theorem stableLengthPre_record_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hx : s.memaddrs (BitVec.ofNat 64 (locN s "stable_logs" + 8)))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    let t := {s with memory := mem'}
    ∀ j, j < memW t (locN t "logs" + 8) →
      Disj (memW t (memW t (locN t "logs") + 8 * j), 40)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  obtain ⟨S, Nd, hW, ho, hs, hh, ha, hr⟩ := hp.2.2.2.2
  have hf := stable_length_store_source s hp.1 hp.2.1 S Nd hW ho hs hh ha hr hx mem' hm
  have hd := (stable_length_store_header_unchanged s hp.1.1.1.1.1.1.1.1.1.1.2
    hp.2.1 mem' hm).1
  exact stable_copy_record_separation s mem' hf.2.2.2.2.2.1 hf.2.2.2.2.2.2 hd
    (stableLengthPre_source_cells s hp mem' hm) he

/-- Both header/backing separation facts survive the stable length update. -/
theorem stableLengthPre_headers_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hs : Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hd : Disj (locN s "stable_logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    let t := {s with memory := mem'}
    Disj (locN t "logs", 24)
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") ∧
    Disj (locN t "stable_logs", 24)
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  have hb := (stable_length_store_header_unchanged s hp.1.1.1.1.1.1.1.1.1.1.2
    hp.2.1 mem' hm).1
  dsimp only
  change Disj (locN s "logs", 24)
    (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    Disj (locN s "stable_logs", 24)
    (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
  rw [hb]
  exact ⟨hs, hd⟩

/-- Source-array/backing separation survives the stable length update. -/
theorem stableLengthPre_array_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hx : s.memaddrs (BitVec.ofNat 64 (locN s "stable_logs" + 8)))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hd : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    let t := {s with memory := mem'}
    Disj (memW t (locN t "logs"), 8 * memW t (locN t "logs" + 8))
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  obtain ⟨S, Nd, hW, ho, hs, hh, ha, hr⟩ := hp.2.2.2.2
  have hf := stable_length_store_source s hp.1 hp.2.1 S Nd hW ho hs hh ha hr hx mem' hm
  have hb := (stable_length_store_header_unchanged s hp.1.1.1.1.1.1.1.1.1.1.2
    hp.2.1 mem' hm).1
  dsimp only
  change Disj (memW {s with memory := mem'} (locN s "logs"),
    8 * memW {s with memory := mem'} (locN s "logs" + 8))
    (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
  rw [hf.2.2.2.2.2.1, hf.2.2.2.2.2.2, hb]
  exact hd

/-- Framing the destination header and world footprint retains separation
from every world-owned interval after the copy store. -/
theorem stable_copy_world_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (S Nd : List Nat)
    (hd : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs"))
    (hw : worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd)
    (hp : ∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o) :
    let t := {s with memory := mem'}
    ∀ o ∈ worldOwned t S Nd,
      Disj (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") o := by
  dsimp only
  intro o ho
  rw [hw] at ho
  change Disj (memW {s with memory := mem'} (locN s "stable_logs"),
    8 * locN s "stable_log_cap") o
  rw [hd]
  exact hp o ho

/-- Preserve backing/world separation across the length write using the
same ownership witnesses as the length-store contract. -/
theorem stableLengthPre_world_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hx : s.memaddrs (BitVec.ofNat 64 (locN s "stable_logs" + 8)))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (S Nd : List Nat) (hW : WorldTypedWith s S Nd)
    (ho : LogsLiveOwned s S Nd (locN s "logs"))
    (hs : ∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o)
    (hb : ∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o) :
    let t := {s with memory := mem'}
    WorldTypedWith t S Nd ∧ LogsLiveOwned t S Nd (locN t "logs") ∧
      ∀ o ∈ worldOwned t S Nd,
        Disj (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") o := by
  obtain ⟨_, _, _, _, _, hh, ha, hr⟩ := hp.2.2.2.2
  have hf := stable_length_store_source s hp.1 hp.2.1 S Nd hW ho hs hh ha hr hx mem' hm
  have hd := (stable_length_store_header_unchanged s hp.1.1.1.1.1.1.1.1.1.1.2
    hp.2.1 mem' hm).1
  exact ⟨hf.1, hf.2.2.2.2.1, stable_copy_world_separation s mem' S Nd hd hf.2.1 hb⟩

/-- Package the spatial obligations needed at copy entry independently of
the counter and operand locals. -/
def StableCopySpatial : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
    (∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o) ∧
    Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    Disj (locN s "stable_logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")

/-- Counter and backing-pointer local initialization preserve spatial facts. -/
theorem stableCopySpatial_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hl : locals.lookup (ofString "logs") = s.locals.lookup (ofString "logs"))
    (hs : locals.lookup (ofString "stable_logs") = s.locals.lookup (ofString "stable_logs"))
    (hc : locals.lookup (ofString "stable_log_cap") = s.locals.lookup (ofString "stable_log_cap"))
    (hp : StableCopySpatial s) : StableCopySpatial {s with locals := locals, clock := k} := by
  obtain ⟨S, Nd, hW, ho, hw, hh, hd, ha, he⟩ := hp
  have el := locN_congr s locals k "logs" hl
  have es := locN_congr s locals k "stable_logs" hs
  have ec := locN_congr s locals k "stable_log_cap" hc
  refine ⟨S, Nd, (R13Shards.worldTypedWith_with_locals s locals k S Nd).mpr hW, ?_⟩
  simp only [el, es, ec]
  exact ⟨ho, hw, hh, hd, ha, he⟩

/-- Updating a local other than the three spatial roots preserves separation. -/
theorem stableCopySpatial_setVar {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (v : ValueHOL 64)
    (hl : name ≠ ofString "logs") (hs : name ≠ ofString "stable_logs")
    (hc : name ≠ ofString "stable_log_cap") (hp : StableCopySpatial s) :
    StableCopySpatial (setVarHOLFinite name v s) := by
  apply stableCopySpatial_with_locals s _ s.clock _ _ _ hp
  all_goals simp [HolFiniteMapExact.lookup_update, FUPDATE, hl, hs, hc]

/-- Local assignments, including the stable backing load, frame the spatial
contract whenever they leave its three root locals unchanged. -/
theorem hoare_stableCopySpatial_assign (name : MlS) (e : ExpHOL 64)
    (hl : name ≠ ofString "logs") (hs : name ≠ ofString "stable_logs")
    (hc : name ≠ ofString "stable_log_cap") :
    Hoare StableCopySpatial (.assign .local name e)
      (fun r t => r = none → StableCopySpatial t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    exact stableCopySpatial_setVar s name v hl hs hc hp
  · intro F s hp hr
    cases hr

/-- The concrete backing load retains spatial facts and installs the exact
word-valued destination pointer used by the copy loop. -/
theorem hoare_stable_backing_load :
    Hoare (fun s => StableCopySpatial s ∧ WordAt s (locN s "stable_logs") ∧
      ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
      (fun r t => r = none → StableCopySpatial t ∧
        ∃ q : BitVec 64, t.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
          q.toNat = memW t (locN t "stable_logs")) := by
  apply Hoare.assign
  · intro F s v hp hv _
    obtain ⟨hs, hw, w, hl⟩ := hp
    have he := stable_backing_load_eval s w hl hw
    change evalAt s (.load .one (.var .local (ofString "stable_logs"))) = some v at hv
    rw [hv] at he
    have hv' := Option.some.inj he
    subst v
    refine ⟨stableCopySpatial_setVar s _ _ (by decide) (by decide) (by decide) hs,
      BitVec.ofNat 64 (memW s (locN s "stable_logs")), ?_, ?_⟩
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, memW, ofString]
  · intro F s hp hr
    cases hr

/-- All copy-entry spatial obligations survive the stable length write. -/
theorem stableLengthPre_spatial {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hx : s.memaddrs (BitVec.ofNat 64 (locN s "stable_logs" + 8)))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hs : ∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
      (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
      (∀ o ∈ worldOwned s S Nd,
        Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o))
    (hh : Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hd : Disj (locN s "stable_logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (ha : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    StableCopySpatial {s with memory := mem'} := by
  obtain ⟨S, Nd, hW, ho, hs, hb⟩ := hs
  obtain ⟨hW', ho', hb'⟩ := stableLengthPre_world_separation s hp mem' hx hm S Nd hW ho hs hb
  obtain ⟨hh', hd'⟩ := stableLengthPre_headers_separation s hp mem' hm hh hd
  exact ⟨S, Nd, hW', ho', hb', hh', hd',
    stableLengthPre_array_separation s hp mem' hx hm ha,
    stableLengthPre_record_separation s hp mem' hx hm he⟩

/-- Spatial framing for the concrete stable length store, retaining a coherent
world witness for both the header and its backing allocation. -/
theorem hoare_stable_length_spatial :
    Hoare (fun s => StableLengthPre s ∧
      (∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
        (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
        (∀ o ∈ worldOwned s S Nd,
          Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)) ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → StableCopySpatial t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hp, hs, hh, hd, ha, he⟩ := hp
  have hlocal := hp.2.2.1
  have hnl := hp.2.2.2.1
  have hv' : v = .val (.word (BitVec.ofNat 64 (locN s "nl"))) := by
    change s.locals.lookup (ofString "nl") = some v at hv
    rw [hnl] at hv
    exact (Option.some.inj hv).symm
  subst v
  have hx' : x = BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hlocal, valueIsWord,
      valueWord, wordOpHOL, wordOp] at hx
    subst x
    apply BitVec.eq_of_toNat_eq
    have hb := stable_length_address_bound s hp.1.1.1.1.1.1.1.1.1.1.2 hp.2.1
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb.1] using hb.2
  subst x
  obtain ⟨hdom, hval, hm⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  exact stableLengthPre_spatial s hp mem' hdom hm hs hh hd ha he

/-- Combine the length and spatial postconditions of the same concrete write. -/
theorem hoare_stable_length_joint :
    Hoare (fun s => StableLengthPre s ∧
      (∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
        (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
        (∀ o ∈ worldOwned s S Nd,
          Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)) ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → StableLengthPost t ∧ StableCopySpatial t) := by
  constructor
  intro F s hc hp hnt hr
  exact ⟨hoare_stable_length_store.run s hc hp.1 hnt hr,
    hoare_stable_length_spatial.run s hc hp hnt hr⟩

/-- The actual length store retains all non-spatial copy-setup operands and
the readable stable header. -/
theorem hoare_stable_length_setup_frame :
    Hoare (fun s => StableLengthPre s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → locN t "logs" ≠ 0 ∧
        WordsOK t (locN t "stable_logs", 24) ∧ Allocated t (locN t "stable_logs", 24) ∧
        locN t "nl" ≤ locN t "stable_log_cap" ∧ WordAt t (locN t "stable_logs") ∧
        ∃ n p w : BitVec 64,
          t.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
          t.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
          t.locals.lookup (ofString "stable_logs") = some (.val (.word w))) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hp, hz, hh, hc, p, hl⟩ := hp
  have hlocal := hp.2.2.1
  have hnl := hp.2.2.2.1
  have hv' : v = .val (.word (BitVec.ofNat 64 (locN s "nl"))) := by
    change s.locals.lookup (ofString "nl") = some v at hv
    rw [hnl] at hv
    exact (Option.some.inj hv).symm
  subst v
  have hx' : x = BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hlocal, valueIsWord,
      valueWord, wordOpHOL, wordOp] at hx
    subst x
    apply BitVec.eq_of_toNat_eq
    have hb := stable_length_address_bound s hp.1.1.1.1.1.1.1.1.1.1.2 hp.2.1
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb.1] using hb.2
  subst x
  obtain ⟨hdom, he, hm⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  obtain ⟨hh', ha', hw'⟩ := stable_length_store_header_ready s mem' _ he hm hh hp.2.1
  exact ⟨hz, hh', ha', hc, hw', stableLengthPre_memory_operands s hp mem' p hl⟩

/-- The length store establishes the complete backing-load setup contract. -/
theorem hoare_stable_length_copy_ready :
    Hoare (fun s => (StableLengthPre s ∧
      (∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
        (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
        (∀ o ∈ worldOwned s S Nd,
          Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)) ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) ∧
      locN s "logs" ≠ 0 ∧ WordsOK s (locN s "stable_logs", 24) ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → StableLengthPost t ∧ locN t "logs" ≠ 0 ∧
        WordsOK t (locN t "stable_logs", 24) ∧ Allocated t (locN t "stable_logs", 24) ∧
        locN t "nl" ≤ locN t "stable_log_cap" ∧ StableCopySpatial t ∧
        WordAt t (locN t "stable_logs") ∧ ∃ n p w : BitVec 64,
          t.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
          t.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
          t.locals.lookup (ofString "stable_logs") = some (.val (.word w))) := by
  constructor
  intro F s hc hp hnt hr
  obtain ⟨hpost, hs⟩ := hoare_stable_length_joint.run s hc hp.1 hnt hr
  have hcap : locN s "nl" ≤ locN s "stable_log_cap" :=
    stableLengthPre_copy_capacity s hp.1.1 s.memory
  obtain ⟨hz, hh, ha, hcap', hw, hop⟩ := hoare_stable_length_setup_frame.run s hc
    ⟨hp.1.1, hp.2.1, hp.2.2.1, hcap, hp.2.2.2⟩ hnt hr
  exact ⟨hpost, hz, hh, ha, hcap', hs, hw, hop⟩

/-- Reassemble the separated store contract from framed source cells and
preserved ownership after a memory update. -/
theorem stableCopyStorePre_memory {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyStorePre s)
    (hinv : StableCopyInv {s with memory := mem'})
    (hs : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hn : memW {s with memory := mem'} (locN s "logs" + 8) =
      memW s (locN s "logs" + 8))
    (hd : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs"))
    (ha : ∀ j, j < memW s (locN s "logs" + 8) →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (hworld : ∀ S Nd, WorldTypedWith s S Nd →
      LogsLiveOwned s S Nd (locN s "logs") →
      WorldTypedWith {s with memory := mem'} S Nd ∧
      LogsLiveOwned {s with memory := mem'} S Nd (locN s "logs") ∧
      worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd) :
    StableCopyStorePre {s with memory := mem'} := by
  obtain ⟨_, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hsep, hh, hdh, harr, he⟩ := hp
  obtain ⟨hW', ho', howned⟩ := hworld S Nd hW ho
  refine ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, ?_⟩,
    S, Nd, hW', ho', ?_, ?_, ?_, ?_, ?_⟩
  · exact hptr.trans hd.symm
  · exact stable_copy_world_separation s mem' S Nd hd howned hsep
  · change Disj (locN s "logs", 24)
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hd]; exact hh
  · change Disj (locN s "stable_logs", 24)
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hd]; exact hdh
  · change Disj (memW {s with memory := mem'} (locN s "logs"),
      8 * memW {s with memory := mem'} (locN s "logs" + 8))
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hs, hn, hd]; exact harr
  · exact stable_copy_record_separation s mem' hs hn hd ha he

/-- The copy write preserves the already copied prefix as well as the
length postcondition, before the counter is advanced. -/
theorem stableCopyInv_after_store {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hpost : StableLengthPost {s with memory := mem'})
    (hi : locN s "i" < locN s "nl")
    (hwrite : memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a)
    (hsource : ∀ j, j < locN s "nl" →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (hs : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hd : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs")) : StableCopyInv {s with memory := mem'} := by
  refine ⟨hpost, hp.2.1, ?_, hp.2.2.2.1, hp.2.2.2.2.1, ?_⟩
  · exact wordsOK_transfer hp.1.1.1.1.1 hpost.1.1.1.1 hp.2.2.1
  · intro j hj hjn
    change j < locN s "i" at hj
    exact stableCopyInv_store_prefix s mem' hp hi hwrite hm hsource hs hd j (by omega)

/-- Loop-head contract: operand shapes, bounded counter, and the separated
store precondition whenever the current index is active. -/
def StableCopyLoopInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => StableCopyInv s ∧
    (∃ i n : BitVec 64,
      s.locals.lookup (ofString "i") = some (.val (.word i)) ∧
      s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
    locN s "i" ≤ locN s "nl" ∧
    (locN s "i" < locN s "nl" → StableCopyStorePre s)

/-- An active separated store state supplies every loop-head premise;
positivity of the length recovers its word-shaped local. -/
theorem stableCopyStorePre_loopInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyStorePre s) : StableCopyLoopInv s := by
  obtain ⟨w, p, q, hw, _⟩ := hp.2.2.1
  have hn : 0 < locN s "nl" := Nat.lt_of_le_of_lt (Nat.zero_le _) hp.2.1
  exact ⟨hp.1, ⟨w, BitVec.ofNat 64 (locN s "nl"), hw,
    stable_positive_local_word s "nl" hn⟩, Nat.le_of_lt hp.2.1, fun _ => hp⟩

/-- A completed copy needs no further separation premise at the loop head. -/
theorem stableCopyLoopInv_complete {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s)
    (hshape : ∃ i n : BitVec 64,
      s.locals.lookup (ofString "i") = some (.val (.word i)) ∧
      s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (he : locN s "i" = locN s "nl") : StableCopyLoopInv s := by
  refine ⟨hp, hshape, Nat.le_of_eq he, ?_⟩
  intro hi
  omega

/-- Empty source lists enter the completed loop directly after zeroing the counter. -/
theorem stableCopyLoopInv_init_empty {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hcap : locN s "nl" ≤ locN s "stable_log_cap")
    (hz : s.locals.lookup (ofString "nl") = some (.val (.word 0))) :
    StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) := by
  apply stableCopyLoopInv_complete _ (stableCopyInv_init s hp hn hh ha hcap)
  · refine ⟨0, 0, ?_, ?_⟩ <;>
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hz]
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hz]

/-- The concrete zero assignment establishes the empty-source loop invariant. -/
theorem hoare_stableCopy_init_empty :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧
      Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧
      s.locals.lookup (ofString "nl") = some (.val (.word 0)))
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
    subst v
    exact stableCopyLoopInv_init_empty s hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
      hp.2.2.2.2.1 hp.2.2.2.2.2
  · intro F s hp hr
    cases hr

/-- A separated active-store state already satisfies the full loop-head
contract; positivity supplies the length operand's word shape. -/
theorem stableCopyLoopInv_of_storePre {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyStorePre s) : StableCopyLoopInv s := by
  obtain ⟨w, p, q, hw, hl, hq, hptr⟩ := hp.2.2.1
  have hn := stable_positive_local_word s "nl" (by have := hp.2.1; omega)
  exact ⟨hp.1, ⟨w, BitVec.ofNat 64 (locN s "nl"), hw, hn⟩,
    Nat.le_of_lt hp.2.1, fun _ => hp⟩

/-- Clock decrement preserves the separated store contract. -/
theorem stableCopyStorePre_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyStorePre s) : StableCopyStorePre (decClockHOLFinite s) := by
  obtain ⟨hinv, hi, hshape, S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  refine ⟨stableCopyInv_with_locals s s.locals (s.clock - 1) (by intros; rfl) hinv,
    hi, hshape, S, Nd, ?_, ho, hworld, hh, hd, ha, he⟩
  exact (R13Shards.worldTypedWith_with_locals s s.locals (s.clock - 1) S Nd).mpr hW

/-- The loop-head contract survives the loop's clock decrement. -/
theorem stableCopyLoopInv_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyLoopInv s) : StableCopyLoopInv (decClockHOLFinite s) := by
  refine ⟨stableCopyInv_with_locals s s.locals (s.clock - 1) (by intros; rfl) hp.1,
    hp.2.1, hp.2.2.1, ?_⟩
  intro hi
  exact stableCopyStorePre_decClock s (hp.2.2.2 hi)

theorem stableCopyLoopInv_rank {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyLoopInv s) : locN s "nl" - locN s "i" ≤ 2 ^ 28 := by
  have hb := (stableLengthPost_length_bound s hp.1.1 hp.1.2.1).1
  omega

theorem stableCopyLoopInv_active {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyLoopInv s)
    (ha : LoopActive (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nl"))) s) : StableCopyStorePre s := by
  obtain ⟨w, hw, hnz⟩ := ha
  obtain ⟨i, n, hi, hn⟩ := hp.2.1
  have hb := (stableLengthPost_length_bound s hp.1.1 hp.1.2.1).1
  exact hp.2.2.2 (stableCopyInv_guard s hp.1 i n w hi hn (by have := hp.2.2.1; omega) hw hnz)

theorem stableCopyLoopInv_done {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyLoopInv s)
    (he : evalAt s (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nl"))) = some (.val (.word 0))) : PtxReceiptsDone s := by
  obtain ⟨i, n, hi, hn⟩ := hp.2.1
  have hb := (stableLengthPost_length_bound s hp.1.1 hp.1.2.1).1
  apply stableCopyInv_exit s hp.1
  exact stableCopyInv_guard_false s hp.1 i n hi hn (by have := hp.2.2.1; omega) he

/-- The actual indexed copy store preserves the length postcondition. -/
theorem hoare_stableCopy_store_post :
    Hoare StableCopyStorePre
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → StableLengthPost t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨hdom, _, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  exact stableCopyInv_store_post s mem' hinv hi S Nd hW ho hworld hh hd ha he hdom hm

/-- The copy store establishes the extended prefix needed by the increment. -/
theorem hoare_stableCopy_store_prefix :
    Hoare StableCopyStorePre
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → ∀ j, j < locN t "i" + 1 → j < locN t "nl" →
        memW t (memW t (locN t "stable_logs") + 8 * j) =
          memW t (memW t (locN t "logs") + 8 * j)) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨hdom, hwrite, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  have hlogs := hinv.1.2.1.resolve_left hinv.2.1
  have hs0 := (stableCopyInv_header_unhit s mem' hinv hi _ hlogs.2.1 hlogs.1.1 hh hm).1
  have hd0 := (stableCopyInv_header_unhit s mem' hinv hi _
    hinv.2.2.2.1 hinv.2.2.1.1 hd hm).1
  have ha' : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") := by
    rw [hinv.1.2.2.2.2.1, hinv.1.2.2.2.1]; exact ha
  have harr := stableCopyInv_source_preserved s mem' hinv hi ha' hm
  rw [hinv.1.2.2.2.2.1] at harr
  intro j hj _
  exact stableCopyInv_store_prefix s mem' hinv hi hwrite hm harr hs0 hd0 j hj

/-- The concrete store retains the invariant at the old counter, allowing
the separation contract to be reconstructed before incrementing. -/
theorem hoare_stableCopy_store_inv :
    Hoare StableCopyStorePre
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → StableCopyInv t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨hdom, hwrite, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  have hpost := stableCopyInv_store_post s mem' hinv hi S Nd hW ho hworld hh hd ha he hdom hm
  have hlogs := hinv.1.2.1.resolve_left hinv.2.1
  have hs0 := (stableCopyInv_header_unhit s mem' hinv hi _ hlogs.2.1 hlogs.1.1 hh hm).1
  have hd0 := (stableCopyInv_header_unhit s mem' hinv hi _
    hinv.2.2.2.1 hinv.2.2.1.1 hd hm).1
  have ha' : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") := by
    rw [hinv.1.2.2.2.2.1, hinv.1.2.2.2.1]; exact ha
  have harr := stableCopyInv_source_preserved s mem' hinv hi ha' hm
  rw [hinv.1.2.2.2.2.1] at harr
  exact stableCopyInv_after_store s mem' hinv hpost hi hwrite hm harr hs0 hd0

/-- A separated concrete copy store preserves the full store contract at
the old index, including its ownership witnesses. -/
theorem hoare_stableCopy_store_pre :
    Hoare StableCopyStorePre
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → StableCopyStorePre t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨hdom, hwrite, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  have hpost := stableCopyInv_store_post s mem' hinv hi S Nd hW ho hworld hh hd ha he hdom hm
  have hlogs := hinv.1.2.1.resolve_left hinv.2.1
  obtain ⟨hs0, hs8, _⟩ := stableCopyInv_header_unhit s mem' hinv hi _ hlogs.2.1 hlogs.1.1 hh hm
  have hd0 := (stableCopyInv_header_unhit s mem' hinv hi _
    hinv.2.2.2.1 hinv.2.2.1.1 hd hm).1
  have ha' : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") := by
    rw [hinv.1.2.2.2.2.1, hinv.1.2.2.2.1]; exact ha
  have harr := stableCopyInv_source_preserved s mem' hinv hi ha' hm
  rw [hinv.1.2.2.2.2.1] at harr
  have hinv' := stableCopyInv_after_store s mem' hinv hpost hi hwrite hm harr hs0 hd0
  obtain ⟨hW', howned, _⟩ := stableCopyInv_world_preserved s mem' hinv hi S Nd hW hworld hdom hm
  have ho' := (stableCopyInv_logs_preserved s mem' hinv hi S Nd ho
    hpost.1.1.1.1 howned hh ha he hm).2
  refine ⟨hinv', hi, ⟨w, p, q, hw, hl, hq, hptr.trans hd0.symm⟩,
    S, Nd, hW', ho', ?_, ?_, ?_, ?_, ?_⟩
  · exact stable_copy_world_separation s mem' S Nd hd0 howned hworld
  · change Disj (locN s "logs", 24)
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hd0]; exact hh
  · change Disj (locN s "stable_logs", 24)
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hd0]; exact hd
  · change Disj (memW {s with memory := mem'} (locN s "logs"),
      8 * memW {s with memory := mem'} (locN s "logs" + 8))
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hs0, hs8, hd0]; exact ha
  · apply stable_copy_record_separation s mem' hs0 hs8 hd0 _ he
    intro j hj
    apply harr j
    rwa [hinv.1.2.2.2.1]

/-- The copy store retains the typed length operand for the increment rule. -/
theorem hoare_stableCopy_store_length_shape :
    Hoare (fun s => StableCopyStorePre s ∧
      ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n)))
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → ∃ n : BitVec 64,
        t.locals.lookup (ofString "nl") = some (.val (.word n))) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  exact hp.2

/-- The concrete store retains the typed length operand required by the
full-invariant increment rule. -/
theorem hoare_stableCopy_store_length_word :
    Hoare (fun s => ∃ n : BitVec 64,
      s.locals.lookup (ofString "nl") = some (.val (.word n)))
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → ∃ n : BitVec 64,
        t.locals.lookup (ofString "nl") = some (.val (.word n))) := by
  exact R13Shards.Hoare.store_fall (fun _ _ _ _ hp _ _ _ => hp)

/-- The actual copy-loop counter increment agrees with natural-number
successor throughout the bounded source list. -/
theorem stable_copy_increment_nat {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : w.toNat < locN s "nl") (hn : locN s "nl" < 2 ^ 28)
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    locN (setVarHOLFinite (ofString "i") v s) "i" = w.toNat + 1 := by
  have hv : v = .val (.word (w + 1)) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord,
      valueWord, wordOpHOL, wordOp] using he.symm
  subst v
  have hb : w.toNat + 1 < 2 ^ 64 := by omega
  simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    BitVec.toNat_add]
  exact hb

/-- An active copy iteration keeps the incremented index in the unsigned
range where the signed loop guard agrees with natural comparison. -/
theorem stable_copy_increment_index_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : w.toNat < locN s "nl") (hn : locN s "nl" < 2 ^ 28)
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    locN (setVarHOLFinite (ofString "i") v s) "i" ≤ locN s "nl" ∧
    locN (setVarHOLFinite (ofString "i") v s) "i" < 2 ^ 63 := by
  rw [stable_copy_increment_nat s w v hw hi hn he]
  constructor <;> omega

/-- The remaining-copy count strictly decreases under the actual increment,
providing a natural-number termination measure for the copy loop. -/
theorem stableCopyInv_increment_decreases {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : locN s "i" < locN s "nl")
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    locN (setVarHOLFinite (ofString "i") v s) "nl" -
        locN (setVarHOLFinite (ofString "i") v s) "i" <
      locN s "nl" - locN s "i" := by
  have hwi : locN s "i" = w.toNat := by simp [locN, hw]
  have hinc := stable_copy_increment_nat s w v hw (by rw [← hwi]; exact hi)
    (stableLengthPost_length_bound s hp.1 hp.2.1).1 he
  have hnl : locN (setVarHOLFinite (ofString "i") v s) "nl" = locN s "nl" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nl" from by decide]
  rw [hnl, hinc]
  omega

/-- The increment retains a word-shaped counter for the next iteration. -/
theorem stable_copy_increment_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    (setVarHOLFinite (ofString "i") v s).locals.lookup (ofString "i") =
      some (.val (.word (w + 1))) := by
  have hv : v = .val (.word (w + 1)) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord,
      valueWord, wordOpHOL, wordOp] using he.symm
  subst v
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Incrementing the counter preserves the typed source, destination, and
length operands needed by the next loop iteration. -/
theorem stable_copy_increment_operands {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w p q n : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hp : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hq : s.locals.lookup (ofString "stable_lp") = some (.val (.word q)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    let t := setVarHOLFinite (ofString "i") v s
    t.locals.lookup (ofString "i") = some (.val (.word (w + 1))) ∧
    t.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
    t.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
    t.locals.lookup (ofString "nl") = some (.val (.word n)) := by
  refine ⟨stable_copy_increment_word s w v hw he, ?_⟩
  simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using ⟨hp, hq, hn⟩

/-- Updating only the counter retains all store separation and operand facts
whenever the new counter remains active. -/
theorem stableCopyStorePre_counter {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (w : BitVec 64) (hp : StableCopyStorePre s)
    (hv : v = .val (.word w))
    (hinv : StableCopyInv (setVarHOLFinite (ofString "i") v s))
    (hi : locN (setVarHOLFinite (ofString "i") v s) "i" < locN s "nl") :
    StableCopyStorePre (setVarHOLFinite (ofString "i") v s) := by
  subst v
  obtain ⟨_, _, ⟨iw, p, q, _, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hW' : WorldTypedWith (setVarHOLFinite (ofString "i") (.val (.word w)) s) S Nd :=
    (R13Shards.worldTypedWith_with_locals s _ s.clock S Nd).mpr hW
  have hn0 : ofString "i" ≠ ofString "nl" := by decide
  have hl0 : ofString "i" ≠ ofString "lp" := by decide
  have hq0 : ofString "i" ≠ ofString "stable_lp" := by decide
  have hs0 : ofString "i" ≠ ofString "stable_logs" := by decide
  have hc0 : ofString "i" ≠ ofString "stable_log_cap" := by decide
  have hg0 : ofString "i" ≠ ofString "logs" := by decide
  refine ⟨hinv, ?_, ⟨w, p, q, ?_, ?_, ?_, ?_⟩,
    S, Nd, hW', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      if_pos rfl, if_neg hn0, if_neg hl0, if_neg hq0, if_neg hs0, if_neg hc0,
      if_neg hg0] at *
  all_goals first | assumption | rfl

/-- The increment restores the full loop-head contract from a separated
store state and the already established prefix invariant. -/
theorem stableCopyLoopInv_counter {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w n : BitVec 64) (v : ValueHOL 64) (hp : StableCopyStorePre s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v)
    (hinv : StableCopyInv (setVarHOLFinite (ofString "i") v s)) :
    StableCopyLoopInv (setVarHOLFinite (ofString "i") v s) := by
  have hv : v = .val (.word (w + 1)) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord,
      valueWord, wordOpHOL, wordOp] using he.symm
  have hnl : (setVarHOLFinite (ofString "i") v s).locals.lookup (ofString "nl") =
      some (.val (.word n)) := by
    simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nl" by decide] using hn
  have hloc : locN (setVarHOLFinite (ofString "i") v s) "nl" = locN s "nl" := by
    simp [locN, hnl, hn]
  have hi : w.toNat < locN s "nl" := by
    simpa [locN, hw] using hp.2.1
  have hb := (stable_copy_increment_index_bound s w v hw hi
    (stableLengthPost_length_bound s hp.1.1 hp.1.2.1).1 he).1
  refine ⟨hinv, ⟨w + 1, n, stable_copy_increment_word s w v hw he, hnl⟩, ?_, ?_⟩
  · rwa [hloc]
  · intro hactive
    apply stableCopyStorePre_counter s v (w + 1) hp hv hinv
    rwa [hloc] at hactive

/-- The zero-counter state is a full loop head once allocation and framing
have supplied its active-store contract. -/
theorem stableCopyLoopInv_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (n : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word 0)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hstore : 0 < locN s "nl" → StableCopyStorePre s) :
    StableCopyLoopInv s := by
  have hz : locN s "i" = 0 := by simp [locN, hi]
  refine ⟨hp, ⟨0, n, hi, hn⟩, ?_, ?_⟩
  · rw [hz]; exact Nat.zero_le _
  · simpa only [hz] using hstore

/-- Combine initialized operands with the spatial and prefix contracts to
obtain the full loop head, including the empty-source case. -/
theorem stableCopyLoopInv_of_spatial_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hs : StableCopySpatial s) (n p q : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word 0)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hq : s.locals.lookup (ofString "stable_lp") = some (.val (.word q)))
    (hd : q.toNat = memW s (locN s "stable_logs")) : StableCopyLoopInv s := by
  apply stableCopyLoopInv_zero s hp n hi hn
  intro hpos
  refine ⟨hp, ?_, ⟨0, p, q, hi, hl, hq, hd⟩, hs⟩
  simpa [locN, hi] using hpos

/-- Counter initialization combines the retained spatial facts and typed
operands into the full copy-loop invariant. -/
theorem stableCopyLoopInv_init_spatial {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hz : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hc : locN s "nl" ≤ locN s "stable_log_cap")
    (hs : StableCopySpatial s) (n p q : BitVec 64)
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hq : s.locals.lookup (ofString "stable_lp") = some (.val (.word q)))
    (hd : q.toNat = memW s (locN s "stable_logs")) :
    StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) := by
  have hsp : StableCopySpatial (setVarHOLFinite (ofString "i") (.val (.word 0)) s) := by
    apply stableCopySpatial_with_locals s _ s.clock (hp := hs) <;>
      simp [HolFiniteMapExact.update, FUPDATE, ofString]
  apply stableCopyLoopInv_of_spatial_zero _ (stableCopyInv_init s hp hz hh ha hc) hsp n p q
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hn
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hl
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hq
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, memW, ofString] using hd

/-- Loading the backing pointer and then zeroing the counter establishes the
loop invariant directly from the post-length state. -/
theorem stableCopyLoopInv_backing_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hz : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hc : locN s "nl" ≤ locN s "stable_log_cap")
    (hs : StableCopySpatial s) (n p w : BitVec 64) (v : ValueHOL 64)
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hw : s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
    (hword : WordAt s (locN s "stable_logs"))
    (he : evalAt s (.load .one (.var .local (ofString "stable_logs"))) = some v) :
    StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0))
      (setVarHOLFinite (ofString "stable_lp") v s)) := by
  obtain ⟨q, hq, hd⟩ := stable_backing_load_local s w v hw hword he
  apply stableCopyLoopInv_init_spatial _ (stableLengthPost_set_backing s v hp)
    (n := n) (p := p) (q := q)
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, ofString] using hz
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, WordsOK, WordAt, ofString] using hh
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, Allocated, globN, ofString] using ha
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, ofString] using hc
  · exact stableCopySpatial_setVar s _ v (by decide) (by decide) (by decide) hs
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hn
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hl
  · exact hq
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, memW, ofString] using hd

/-- Backing assignment establishes the precondition for zero-counter entry. -/
theorem hoare_stableCopy_backing_entry :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
      (fun r t => r = none →
        StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) t)) := by
  apply Hoare.assign
  · intro F s v hp he _
    obtain ⟨hp, hz, hh, ha, hc, hs, hword, n, p, w, hn, hl, hw⟩ := hp
    exact stableCopyLoopInv_backing_init s hp hz hh ha hc hs n p w v hn hl hw hword he
  · intro F s hp hr
    cases hr

/-- Hoare rule for the concrete backing-load and zero-counter setup sequence. -/
theorem hoare_stableCopy_backing_init :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (.seq (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
        (.assign .local (ofString "i") (.const 0)))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.seq_fall (R := fun s =>
    StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s))
  · apply Hoare.assign
    · intro F s v hp hv _
      obtain ⟨hp, hz, hh, ha, hc, hs, hword, n, p, w, hn, hl, hw⟩ := hp
      exact stableCopyLoopInv_backing_init s hp hz hh ha hc hs n p w v hn hl hw hword hv
    · intro F s hp hr
      cases hr
  · apply Hoare.assign
    · intro F s v hp hv _
      have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
      subst v
      exact hp
    · intro F s hp hr
      cases hr

/-- Zeroing the counter realizes the loop-entry weakest precondition. -/
theorem hoare_stableCopy_zero_entry :
    Hoare (fun s => StableCopyLoopInv
      (setVarHOLFinite (ofString "i") (.val (.word 0)) s))
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
    subst v
    exact hp
  · intro F s hp hr
    cases hr

/-- Concrete counter initialization from the post-length spatial contract. -/
theorem hoare_stableCopy_init_spatial :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      ∃ n p q : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
        q.toNat = memW s (locN s "stable_logs"))
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
    subst v
    obtain ⟨hpost, hz, hh, ha, hc, hs, n, p, q, hn, hl, hq, hd⟩ := hp
    exact stableCopyLoopInv_init_spatial s hpost hz hh ha hc hs n p q hn hl hq hd
  · intro F s hp hr
    cases hr

/-- Assigning zero to the counter establishes the full loop contract when its
post-assignment allocation and separation obligations have been supplied. -/
theorem hoare_stableCopy_init_loop :
    Hoare (fun s =>
      StableCopyInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      (0 < locN s "nl" →
        StableCopyStorePre (setVarHOLFinite (ofString "i") (.val (.word 0)) s)))
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
    subst v
    obtain ⟨n, hn⟩ := hp.2.1
    have hnl : (setVarHOLFinite (ofString "i") (.val (.word 0)) s).locals.lookup
        (ofString "nl") = some (.val (.word n)) := by
      simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "i" ≠ ofString "nl" by decide] using hn
    apply stableCopyLoopInv_zero _ hp.1 n
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    · exact hnl
    · simpa only [locN, hnl, hn] using hp.2.2
  · intro F s hp hr
    cases hr

/-- Hoare composition interface for the increment with full loop-head
preservation, including the separated contract for the next active index. -/
theorem hoare_stableCopy_increment_loop :
    Hoare (fun s => StableCopyStorePre s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      ∀ v, evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v →
        StableCopyInv (setVarHOLFinite (ofString "i") v s))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    obtain ⟨n, hn⟩ := hp.2.1
    obtain ⟨w, p, q, hw, _⟩ := hp.1.2.2.1
    exact stableCopyLoopInv_counter s w n v hp.1 hw hn hv (hp.2.2 v hv)
  · intro F s hp hr
    cases hr

/-- Once the store has extended the prefix, the actual counter assignment
re-establishes the loop invariant. -/
theorem stableCopyInv_increment {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hcap : locN s "nl" ≤ locN s "stable_log_cap")
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : w.toNat < locN s "nl")
    (hprefix : ∀ j, j < w.toNat + 1 → j < locN s "nl" →
      memW s (memW s (locN s "stable_logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    StableCopyInv (setVarHOLFinite (ofString "i") v s) := by
  have hpost : StableLengthPost (setVarHOLFinite (ofString "i") v s) :=
    LocalsOnly.setVar localsOnly_stableLengthPost (by decide) v s hp
  have hinc := stable_copy_increment_nat s w v hw hi
    (stableLengthPost_length_bound s hp hn).1 he
  have hloc : ∀ name ∈ (["logs", "stable_logs", "nl", "stable_log_cap"] : List String),
      locN (setVarHOLFinite (ofString "i") v s) name = locN s name := by
    intro name hname
    have hne : ofString "i" ≠ ofString name := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
      rcases hname with rfl | rfl | rfl | rfl <;> decide
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
  refine ⟨hpost, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hloc "logs" (by simp)]; exact hn
  · rw [hloc "stable_logs" (by simp)]; exact hh
  · rw [hloc "stable_logs" (by simp)]; exact ha
  · rw [hloc "nl" (by simp), hloc "stable_log_cap" (by simp)]; exact hcap
  · intro j hj hjn
    rw [hinc] at hj
    rw [hloc "nl" (by simp)] at hjn
    rw [hloc "stable_logs" (by simp), hloc "logs" (by simp)]
    exact hprefix j hj hjn

/-- Hoare rule for the actual increment once the copy store has extended
the prefix through the current index. -/
theorem hoare_stableCopy_increment :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧
      (∃ w : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word w))) ∧
      locN s "i" < locN s "nl" ∧
      ∀ j, j < locN s "i" + 1 → j < locN s "nl" →
        memW s (memW s (locN s "stable_logs") + 8 * j) =
          memW s (memW s (locN s "logs") + 8 * j))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r t => r = none → StableCopyInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    obtain ⟨hpost, hn, hh, ha, hc, ⟨w, hw⟩, hi, hprefix⟩ := hp
    have hwi : locN s "i" = w.toNat := by simp [locN, hw]
    apply stableCopyInv_increment s w v hpost hn hh ha hc hw
      (by rw [← hwi]; exact hi) ?_ hv
    intro j hj hjn
    exact hprefix j (by rw [hwi]; exact hj) hjn
  · intro F s hp hr
    exact absurd hr (by simp)

/-- Compose the semantic copy write with the actual counter assignment. -/
theorem stableCopyInv_store_increment {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w : BitVec 64) (v : ValueHOL 64)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl")
    (hpost : StableLengthPost {s with memory := mem'})
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hwrite : memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a)
    (hsource : ∀ j, j < locN s "nl" →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (hsrc : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hdst : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs"))
    (he : evalAt {s with memory := mem'}
      (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    StableCopyInv (setVarHOLFinite (ofString "i") v {s with memory := mem'}) := by
  have hiw : locN s "i" = w.toNat := by simp [locN, hw]
  apply stableCopyInv_increment {s with memory := mem'} w v hpost hp.2.1
    (wordsOK_transfer hp.1.1.1.1.1 hpost.1.1.1.1 hp.2.2.1)
    hp.2.2.2.1 hp.2.2.2.2.1 hw (by change w.toNat < locN s "nl"; rw [← hiw]; exact hi) ?_ he
  intro j hj _
  exact stableCopyInv_store_prefix s mem' hp hi hwrite hm hsource hsrc hdst j
    (by simpa only [hiw] using hj)

/-- Assemble the source and header frame obligations for a separated store
before invoking the counter-increment invariant proof. -/
theorem stableCopyInv_separated_store_increment {F : Type}
    (s : PanSemStateFiniteExact 64 F) (mem' : BitVec 64 → HolWordLab 64)
    (w : BitVec 64) (v : ValueHOL 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl")
    (hpost : StableLengthPost {s with memory := mem'})
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hwrite : memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a)
    (hs : Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hd : Disj (locN s "stable_logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (ha : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (he : evalAt {s with memory := mem'}
      (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    StableCopyInv (setVarHOLFinite (ofString "i") v {s with memory := mem'}) := by
  have hl := hp.1.2.1.resolve_left hp.2.1
  have hsrc := (stableCopyInv_header_unhit s mem' hp hi _ hl.2.1 hl.1.1 hs hm).1
  have hdst := (stableCopyInv_header_unhit s mem' hp hi _
    hp.2.2.2.1 hp.2.2.1.1 hd hm).1
  have harr := stableCopyInv_source_preserved s mem' hp hi ha hm
  rw [hp.1.2.2.2.2.1] at harr
  exact stableCopyInv_store_increment s mem' w v hp hi hpost hw hwrite hm harr hsrc hdst he

/-- The semantic store establishes the precondition of the actual increment. -/
theorem hoare_stableCopy_store_for_increment :
    Hoare StableCopyStorePre
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → ∀ v,
        evalAt t (.op .add [.var .local (ofString "i"), .const 1]) = some v →
        StableCopyInv (setVarHOLFinite (ofString "i") v t)) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨hdom, hwrite, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  have hpost := stableCopyInv_store_post s mem' hinv hi S Nd hW ho hworld hh hd ha he hdom hm
  have ha' : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") := by
    rw [hinv.1.2.2.2.2.1, hinv.1.2.2.2.1]
    exact ha
  intro value hvalue
  exact stableCopyInv_separated_store_increment s mem' w value hinv hi hpost hw
    hwrite hm hh hd ha' hvalue

/-- Combine store framing and increment preservation into the full loop-head
contract for the concrete body. -/
theorem hoare_stableCopy_body_loop :
    Hoare (fun s => StableCopyStorePre s ∧
      ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n)))
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.seq_fall (h2 := hoare_stableCopy_increment_loop)
  refine ⟨fun s hc hp hnt hr => ?_⟩
  exact ⟨hoare_stableCopy_store_pre.run s hc hp.1 hnt hr,
    hoare_stableCopy_store_length_word.run s hc hp.2 hnt hr,
    hoare_stableCopy_store_for_increment.run s hc hp.1 hnt hr⟩

/-- An active loop head supplies the concrete body's full precondition. -/
theorem hoare_stableCopy_active_body :
    Hoare (fun s => StableCopyLoopInv s ∧
      LoopActive (.cmp .less (.var .local (ofString "i"))
        (.var .local (ofString "nl"))) s)
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → StableCopyLoopInv t) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  obtain ⟨i, n, hi, hn⟩ := hp.1.2.1
  exact hoare_stableCopy_body_loop.run s hc
    ⟨stableCopyLoopInv_active s hp.1 hp.2, n, hn⟩ hnt hr

/-- At an active loop head the concrete body restores the full loop invariant. -/
theorem hoare_stableCopy_body_active :
    Hoare (fun s => StableCopyLoopInv s ∧
      LoopActive (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) s)
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply hoare_stableCopy_body_loop.mono
  intro F s hp
  obtain ⟨i, n, hi, hn⟩ := hp.1.2.1
  exact ⟨stableCopyLoopInv_active s hp.1 hp.2, n, hn⟩

/-- The indexed copy store followed by the real increment preserves the invariant. -/
theorem hoare_stableCopy_body :
    Hoare StableCopyStorePre
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → StableCopyInv t) := by
  apply Hoare.seq_fall hoare_stableCopy_store_for_increment
  apply Hoare.assign
  · intro F s v hp hv _
    exact hp v hv
  · intro F s hp hr
    cases hr

/-- The store/increment body consumes no clock; only the enclosing loop
iteration contributes to its bounded execution cost. -/
theorem stableCopy_body_bound :
    TerminatingProgBoundedOn StableCopyStorePre
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))) 0 := by
  intro F s hc hp
  exact seq_bound_trans
    (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
    hoare_stableCopy_store_for_increment
    (by
      intro F t hc ht
      exact (TerminatingProgBoundedOn.of_clock
        (P := fun _ => True)
        (fun u => clock_assign u .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 1]))) t hc trivial) s hc hp

/-- Bounded-loop assembly for the concrete store/increment body. The remaining
iteration obligation includes preservation of allocation separation. -/
theorem stableCopy_loop_bound_of_step
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → StableCopyLoopInv s →
      LoopActive (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) s →
      let body : ProgHOL 64 := .seq
        (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      StableCopyLoopInv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "nl" -
          locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "i" <
        locN s "nl" - locN s "i") :
    TerminatingProgBoundedOn StableCopyLoopInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      ((2 ^ 28 + 1) * (0 + 1)) := by
  apply TerminatingProgBoundedOn.while_rank_active (fun s => locN s "nl" - locN s "i")
  · exact stableCopyLoopInv_decClock
  · intro F s hc hp
    exact stableCopy_body_bound s hc (stableCopyLoopInv_active s hp.1 hp.2)
  · intro F s hc hp ha
    exact stableCopyLoopInv_rank s hp
  · exact hstep

/-- The concrete stable-copy loop terminates under its full loop contract. -/
theorem stableCopy_loop_bound :
    TerminatingProgBoundedOn StableCopyLoopInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      ((2 ^ 28 + 1) * (0 + 1)) := by
  apply stableCopy_loop_bound_of_step
  intro F s hc hp ha
  dsimp only
  intro hf
  let body : ProgHOL 64 := .seq
    (.store (.op .add [.var .local (ofString "stable_lp"),
      .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
  have hinc : IncrBody (ofString "i") body := by
    dsimp [body]
    ptx_incr
  obtain ⟨i, n, hi, hn⟩ := hp.2.1
  obtain ⟨hnc, hnext⟩ := hinc.run (decClockHOLFinite s) i hi
  have hnone := hf.resolve_right hnc
  have hd := stableCopyLoopInv_decClock s hp
  have hactive := stableCopyLoopInv_active s hp ha
  have hpost := hoare_stableCopy_body_loop.run (decClockHOLFinite s) hc
    ⟨stableCopyStorePre_decClock s hactive, n, hn⟩ (by rw [hnone]; simp) hnone
  refine ⟨hpost, ?_⟩
  have hkeep := evaluate_avoidsLocal_flowing (ofString "nl") body (by decide)
    (decClockHOLFinite s) (Or.inl hnone)
  have hlen : locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "nl" =
      locN s "nl" := by
    simp only [locN, hkeep]
    rfl
  have hidx : locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "i" =
      (i.toNat + 1) % 2 ^ 64 := by
    simp [locN, hnext hnone, BitVec.toNat_add]
  have hil : locN s "i" = i.toNat := by simp [locN, hi]
  have hb := (stableLengthPost_length_bound s hp.1.1 hp.1.2.1).1
  have hai := hactive.2.1
  change locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "nl" -
    locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "i" < _
  rw [hlen, hidx, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The concrete loop's budget is one clock tick per possible iteration,
plus the final guard check. -/
theorem stableCopy_loop_budget :
    TerminatingProgBoundedOn StableCopyLoopInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (2 ^ 28 + 1) := by
  intro F s hc hp
  simpa only [Nat.zero_add, Nat.mul_one] using stableCopy_loop_bound s hc hp

/-- Normal exit from the concrete copy loop establishes receipt readiness. -/
theorem hoare_stableCopy_loop_done :
    Hoare StableCopyLoopInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (fun r t => r = none → PtxReceiptsDone t) := by
  let body : ProgHOL 64 := .seq
    (.store (.op .add [.var .local (ofString "stable_lp"),
      .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
  have hinc : IncrBody (ofString "i") body := by dsimp [body]; ptx_incr
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.while
    (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) body) with ⟨r, post⟩
  change (evaluateHOLFiniteState s (.while _ body)).1 = none at hr
  rw [hrun] at hr
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → st.code = originalRuntimeCode → StableCopyLoopInv st →
      evaluateHOLFiniteState st (.while
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) body) =
        (none, post) → PtxReceiptsDone post from
    this s.clock s rfl hc hp hrun
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp hrun
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i w hw
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hnb := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
            body (by decide) (decClockHOLFinite st)
          obtain ⟨i, n, hi, hn⟩ := hp.2.1
          obtain ⟨hnc, _⟩ := hinc.run (decClockHOLFinite st) i hi
          have ha := stableCopyLoopInv_active st hp ⟨w, hw, hnz⟩
          rcases hb : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hb] at hrun hrem hmeta hnb hnc
          have hlt : mid.clock < k := by
            change mid.clock ≤ st.clock - 1 at hrem
            omega
          cases r with
          | none =>
            have hm := hoare_stableCopy_body_loop.run (decClockHOLFinite st) hc
              ⟨stableCopyStorePre_decClock st ha, n, hn⟩
              (by change (evaluateHOLFiniteState _ body).1 ≠ _; rw [hb]; simp)
              (by change (evaluateHOLFiniteState _ body).1 = _; rw [hb])
            change StableCopyLoopInv (evaluateHOLFiniteState _ body).2 at hm
            rw [hb] at hm
            exact ih mid.clock hlt mid rfl (hmeta.trans hc) hm hrun
          | some r =>
            cases r with
            | «continue» => exact absurd rfl hnc
            | «break» => exact absurd rfl hnb
            | _ => simp at hrun
      · rename_i hz
        have hw0 : w = 0 := Classical.not_not.mp hz
        subst w
        simp at hrun
        obtain ⟨_, rfl⟩ := hrun
        apply stableCopyLoopInv_done _ hp
        exact hw
    · simp at hrun

/-- Compose the completed stable-copy loop with the receipt continuation. -/
theorem stableCopy_loop_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn StableCopyLoopInv
      (.seq
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
          (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
            .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
        tail) (2 ^ 28 + 1 + b) := by
  intro F s hc hp
  exact seq_bound_trans stableCopy_loop_budget hoare_stableCopy_loop_done htail s hc hp

/-- Counter initialization composes with any bounded full-loop continuation. -/
theorem stableCopy_init_spatial_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn StableCopyLoopInv tail b) :
    TerminatingProgBoundedOn (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      ∃ n p q : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
        q.toNat = memW s (locN s "stable_logs"))
      (.seq (.assign .local (ofString "i") (.const 0)) tail) b := by
  rw [← Nat.zero_add b]
  intro F s hc hp
  refine seq_bound_trans (P := fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      ∃ n p q : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
        q.toNat = memW s (locN s "stable_logs"))
    ?_ hoare_stableCopy_init_spatial htail s hc hp
  intro F' t hcode hpre hclock
  have ht := clock_assign t .local (ofString "i") (.const 0)
  exact ⟨by omega, by omega⟩

/-- The concrete right-associated setup adds no clock cost before a bounded
copy-loop continuation. -/
theorem stableCopy_backing_init_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn StableCopyLoopInv tail b) :
    TerminatingProgBoundedOn (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (.seq (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
        (.seq (.assign .local (ofString "i") (.const 0)) tail)) b := by
  have hi : Hoare (fun s => StableCopyLoopInv
      (setVarHOLFinite (ofString "i") (.val (.word 0)) s))
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyLoopInv t) := by
    apply Hoare.assign
    · intro F s v hp hv _
      have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
      subst v
      exact hp
    · intro F s hp hr
      cases hr
  intro F s hc hp
  have hinit : TerminatingProgBoundedOn (fun s => StableCopyLoopInv
      (setVarHOLFinite (ofString "i") (.val (.word 0)) s))
      (.seq (.assign .local (ofString "i") (.const 0)) tail) (0 + b) := by
    intro G t ht hq
    exact seq_bound_trans (fun u _ _ _ => by
      have hu := clock_assign u .local (ofString "i") (.const 0)
      exact ⟨by omega, by omega⟩) hi htail t ht hq
  simpa only [Nat.zero_add] using seq_bound_trans (a := 0)
    (fun u _ _ _ => by
      have hu := clock_assign u .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs")))
      exact ⟨by omega, by omega⟩)
    hoare_stableCopy_backing_entry hinit s hc hp

/-- Complete backing/counter setup followed by copying and a receipt continuation. -/
theorem stableCopy_setup_loop_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (.seq (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
        (.seq (.assign .local (ofString "i") (.const 0))
          (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
            (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
              .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
            tail))) (2 ^ 28 + 1 + b) := by
  intro F s hc hp
  exact stableCopy_backing_init_cut (stableCopy_loop_cut htail) s hc hp

/-- The concrete length store, setup, and copy loop compose with a receipt tail. -/
theorem stable_length_setup_loop_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn (fun s => (StableLengthPre s ∧
      (∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
        (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
        (∀ o ∈ worldOwned s S Nd,
          Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)) ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) ∧
      locN s "logs" ≠ 0 ∧ WordsOK s (locN s "stable_logs", 24) ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.seq (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
        (.seq (.assign .local (ofString "stable_lp")
          (.load .one (.var .local (ofString "stable_logs"))))
          (.seq (.assign .local (ofString "i") (.const 0))
            (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
              (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
                .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
              tail)))) (2 ^ 28 + 1 + b) := by
  intro F s hc hp
  rw [← Nat.zero_add (2 ^ 28 + 1 + b)]
  refine seq_bound_trans ?_ hoare_stable_length_copy_ready
    (stableCopy_setup_loop_cut htail) s hc hp
  intro G t _ _ hclock
  have ht := clock_store t (.op .add [.var .local (ofString "stable_logs"), .const 8])
    (.var .local (ofString "nl"))
  exact ⟨by omega, by omega⟩

/-- Package the length-write framing facts into the complete copy setup contract. -/
theorem stable_length_copy_setup_ready {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w p : BitVec 64)
    (hp : StableLengthPre s) (hz : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (hc : locN s "nl" ≤ locN s "stable_log_cap")
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) = .word w)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hpost : StableLengthPost {s with memory := mem'})
    (hs : StableCopySpatial {s with memory := mem'}) :
    let t := {s with memory := mem'}
    StableLengthPost t ∧ locN t "logs" ≠ 0 ∧
      WordsOK t (locN t "stable_logs", 24) ∧ Allocated t (locN t "stable_logs", 24) ∧
      locN t "nl" ≤ locN t "stable_log_cap" ∧ StableCopySpatial t ∧
      WordAt t (locN t "stable_logs") ∧ ∃ n p w : BitVec 64,
        t.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        t.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        t.locals.lookup (ofString "stable_logs") = some (.val (.word w)) := by
  obtain ⟨hh', ha', hw'⟩ := stable_length_store_header_ready s mem' w he hm hh hp.2.1
  exact ⟨hpost, hz, hh', ha', hc, hs, hw', stableLengthPre_memory_operands s hp mem' p hl⟩

/-- After a framed length write, setup and copying reach any bounded receipt
continuation with the concrete copy-loop budget. -/
theorem stable_length_copy_continuation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w p : BitVec 64)
    (hp : StableLengthPre s) (hz : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (hc : locN s "nl" ≤ locN s "stable_log_cap")
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) = .word w)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hpost : StableLengthPost {s with memory := mem'})
    (hs : StableCopySpatial {s with memory := mem'})
    (hcode : s.code = originalRuntimeCode) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingRunBounded {s with memory := mem'}
      (.seq (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
        (.seq (.assign .local (ofString "i") (.const 0))
          (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
            (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
              .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
            tail))) (2 ^ 28 + 1 + b) := by
  exact stableCopy_setup_loop_cut htail _ hcode
    (stable_length_copy_setup_ready s mem' w p hp hz hh hc hl he hm hpost hs)

/-- An active separated copy state can run the entire remaining loop and
then any receipt-ready continuation. -/
theorem stableCopy_active_loop_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn StableCopyStorePre
      (.seq
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
          (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
            .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
        tail) (2 ^ 28 + 1 + b) := by
  intro F s hc hp
  exact stableCopy_loop_cut htail s hc (stableCopyLoopInv_of_storePre s hp)

/-- Continue from the actual copy body without adding to the tail budget. -/
theorem stableCopy_body_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn StableCopyInv tail b) :
    TerminatingProgBoundedOn StableCopyStorePre
      (.seq (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) ) tail) b := by
  intro F s hc hp
  simpa only [Nat.zero_add] using
    (seq_bound_trans stableCopy_body_bound hoare_stableCopy_body htail s hc hp)

/-- The termination measure decreases across both the memory write and the
counter assignment; the write cannot alter either counter local. -/
theorem stableCopyInv_store_increment_decreases {F : Type}
    (s : PanSemStateFiniteExact 64 F) (mem' : BitVec 64 → HolWordLab 64)
    (w : BitVec 64) (v : ValueHOL 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : locN s "i" < locN s "nl")
    (he : evalAt {s with memory := mem'}
      (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    locN (setVarHOLFinite (ofString "i") v {s with memory := mem'}) "nl" -
        locN (setVarHOLFinite (ofString "i") v {s with memory := mem'}) "i" <
      locN s "nl" - locN s "i" := by
  have he' : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v := by
    simpa only [evalAt, evalHOLExact, evalListHOLExact] using he
  exact stableCopyInv_increment_decreases s w v hp hw hi he'

theorem stable_header_disj_source {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : Nat} (hA : ArenaOK s) (hPost : ArenaOK post)
    (hh : FreshBlock s post p 24) (hp : Phase4LogPointersReady s) :
    Disj (p, 24) (locN s "logs", 24) := by
  have hl := hp.1.1.2.1
  rcases hl with hz | hl
  · exact False.elim (hp.1.2.2 hz)
  · exact hh.disj_allocated hA hPost hl.2.1

/-- Fresh stable storage avoids every source cell that the stable-copy loop
will read, including a scratch-resident source array. -/
theorem fresh_stable_disj_source {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p n : Nat} (hA : ArenaOK s) (hPost : ArenaOK post)
    (hf : FreshBlock s post p n) (hn : n % 8 = 0) (hp : Phase4LogPointersReady s) :
    Disj (p, n) (locN s "logs", 24) ∧
      Disj (p, n) (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8)) ∧
      ∀ i, i < memW s (locN s "logs" + 8) →
        Disj (p, n) (memW s (memW s (locN s "logs") + 8 * i), 40) := by
  have hl := hp.1.1.2.1.resolve_left hp.1.2.2
  obtain ⟨a, b, _, _, _, _, S, Nd, _, ho⟩ := hp.1.1.2.2.2
  have hround : (n + 7) / 8 * 8 = n := by omega
  have hd : ∀ i, Allocated s i → Disj (p, n) i := by
    intro i hi
    simpa only [hround] using hf.disj_allocated hA hPost hi
  refine ⟨hd _ hl.2.1, hd _ (ho hp.1.2.2).1, ?_⟩
  intro i hi
  exact hd _ (Or.inl (hl.2.2.2.2 i hi).2.2.1)

theorem stable_length_cell_disj {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hA : ArenaOK s) (hh : Allocated s (locN s "stable_logs", 24))
    {i : Ivl} (hd : Disj i (locN s "stable_logs", 24)) :
    Disj i ((BitVec.ofNat 64 (locN s "stable_logs" + 8)).toNat, 8) := by
  apply disj_of_inside_right ?_ hd
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (stable_length_address_bound s hA hh).1]
  constructor <;> dsimp <;> omega

/-- Both allocations returned by the stable-list constructor are separated
from the source header, backing cells, and entry records at call entry. -/
theorem lst_new_stable_source_separation (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      ∀ a ∈ [(w.toNat, 24), (memW post w.toNat, 8 * locN s "stable_log_cap")],
        Disj a (locN s "logs", 24) ∧
        Disj a (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8)) ∧
        ∀ i, i < memW s (locN s "logs" + 8) →
          Disj a (memW s (memW s (locN s "logs") + 8 * i), 40) := by
  obtain ⟨w, hv, hh, hb, _⟩ := lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hpost := (hw (Or.inl ⟨v, rfl⟩)).1
  refine ⟨w, hv, ?_⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact fresh_stable_disj_source hp.1.1.1.1.1.1.1.2 hpost.2 hh (by decide) hp.1
  · exact fresh_stable_disj_source hp.1.1.1.1.1.1.1.2 hpost.2 hb (by omega) hp.1

/-- Transport fresh allocation separation to the source array in post-call memory. -/
theorem lst_new_stable_post_source_array (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      Disj (memW post w.toNat, 8 * locN s "stable_log_cap")
        (memW post (locN s "logs"), 8 * memW post (locN s "logs" + 8)) := by
  obtain ⟨w, hv, hs⟩ := lst_new_stable_source_separation h s vs body callee ret v post hc hp ha hl hr
  obtain ⟨hptr, hlen⟩ := lst_new_stable_source_cells h s vs body callee ret v post hc hp hl hr
  refine ⟨w, hv, ?_⟩
  rw [hptr, hlen]
  exact (hs _ (by simp)).2.1

/-- Restored source headers are disjoint from the fresh stable backing. -/
theorem lst_new_stable_resumed_source_header (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Disj (locN t "logs", 24)
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  obtain ⟨w, rfl, hs⟩ :=
    lst_new_stable_source_separation h s vs body callee ret v post hc hp ha hl hr
  have hd := (hs (memW post w.toNat, 8 * locN s "stable_log_cap") (by simp)).1
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "logs" by decide,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" by decide] using
    R13Shards.disj_symm hd

/-- The resumed source array is disjoint from the fresh stable backing. -/
theorem lst_new_stable_resumed_source_array (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Disj (memW t (locN t "logs"), 8 * memW t (locN t "logs" + 8))
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  obtain ⟨w, rfl, hd⟩ :=
    lst_new_stable_post_source_array h s vs body callee ret v post hc hp ha hl hr
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "logs" by decide,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" by decide] using
    R13Shards.disj_symm hd

/-- Fresh stable headers remain separate from the source header and backing
when source addresses are read in the returned memory. -/
theorem lst_new_stable_post_header_separation (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      Disj (locN s "logs", 24) (w.toNat, 24) ∧
      Disj (memW post (locN s "logs"), 8 * memW post (locN s "logs" + 8))
        (w.toNat, 24) := by
  obtain ⟨w, hv, hs⟩ := lst_new_stable_source_separation h s vs body callee ret v post hc hp ha hl hr
  obtain ⟨hptr, hlen⟩ := lst_new_stable_source_cells h s vs body callee ret v post hc hp hl hr
  have hd := hs (w.toNat, 24) (by simp)
  refine ⟨w, hv, R13Shards.disj_symm hd.1, ?_⟩
  rw [hptr, hlen]
  exact R13Shards.disj_symm hd.2.1

/-- Express header/source separation with the caller locals restored. -/
theorem lst_new_stable_resumed_header_separation (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Disj (locN t "logs", 24) (locN t "stable_logs", 24) ∧
      Disj (memW t (locN t "logs"), 8 * memW t (locN t "logs" + 8))
        (locN t "stable_logs", 24) := by
  obtain ⟨w, rfl, hh, hb⟩ :=
    lst_new_stable_post_header_separation h s vs body callee ret v post hc hp ha hl hr
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "logs" by decide] using And.intro hh hb

/-- Source-record separation remains valid after allocator memory updates. -/
theorem lst_new_stable_post_record_separation (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      ∀ i, i < memW post (locN s "logs" + 8) →
        Disj (memW post (memW post (locN s "logs") + 8 * i), 40) (w.toNat, 24) := by
  obtain ⟨w, hv, hs⟩ := lst_new_stable_source_separation h s vs body callee ret v post hc hp ha hl hr
  obtain ⟨hptr, hlen⟩ := lst_new_stable_source_cells h s vs body callee ret v post hc hp hl hr
  have he := lst_new_stable_source_entries h s vs body callee ret v post hc hp hl hr
  refine ⟨w, hv, ?_⟩
  intro i hi
  rw [hlen] at hi
  rw [hptr, he i hi]
  exact R13Shards.disj_symm ((hs _ (by simp)).2.2 i hi)

/-- Every source record remains separate from the returned backing region. -/
theorem lst_new_stable_post_backing_records (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      ∀ i, i < memW post (locN s "logs" + 8) →
        Disj (memW post (memW post (locN s "logs") + 8 * i), 40)
          (memW post w.toNat, 8 * locN s "stable_log_cap") := by
  obtain ⟨w, hv, hs⟩ := lst_new_stable_source_separation h s vs body callee ret v post hc hp ha hl hr
  obtain ⟨hptr, hlen⟩ := lst_new_stable_source_cells h s vs body callee ret v post hc hp hl hr
  have he := lst_new_stable_source_entries h s vs body callee ret v post hc hp hl hr
  refine ⟨w, hv, ?_⟩
  intro i hi
  rw [hlen] at hi
  rw [hptr, he i hi]
  exact R13Shards.disj_symm ((hs _ (by simp)).2.2 i hi)

/-- Restore the source-record/backing separation needed by copy setup. -/
theorem lst_new_stable_resumed_backing_records (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    ∀ i, i < memW t (locN t "logs" + 8) →
      Disj (memW t (memW t (locN t "logs") + 8 * i), 40)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  obtain ⟨w, rfl, he⟩ :=
    lst_new_stable_post_backing_records h s vs body callee ret v post hc hp ha hl hr
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "logs" by decide,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" by decide] using he

/-- Restore caller locals in the source-record separation conclusion. -/
theorem lst_new_stable_resumed_record_separation (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    ∀ i, i < memW t (locN t "logs" + 8) →
      Disj (memW t (memW t (locN t "logs") + 8 * i), 40) (locN t "stable_logs", 24) := by
  obtain ⟨w, rfl, he⟩ :=
    lst_new_stable_post_record_separation h s vs body callee ret v post hc hp ha hl hr
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "logs" by decide] using he

/-- Source ownership and fresh-header separation share allocator witnesses. -/
theorem lst_new_stable_joint_owned (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ ∃ S Nd,
      WorldTypedWith post S Nd ∧ LogsLiveOwned post S Nd (locN s "logs") ∧
      ∀ o ∈ worldOwned post S Nd, Disj (w.toNat, 24) o := by
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  obtain ⟨a, b, _, _, _, _, ho⟩ := hp.1.1.1.2.2.2
  have hLc := (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.1.1.1.2.1
  have hOc := logsWorldOwned_with_locals callee (s.clock - 1) ho
  obtain ⟨S, Nd, hW, hO, hQ⟩ := logsWorldOwned_heapStep_joint
    (hw (Or.inl ⟨v, rfl⟩)) (worldOK_callEntry hp.1.1.1.1.1.1 callee).1 hLc hOc
  have hargs := lst_new_stable_args s vs body callee ret hc hp ha hl
  obtain ⟨w, hv, hd⟩ := hQ hargs.2.2.2 v rfl
  exact ⟨w, hv, S, Nd, hW, hO, fun o ho => hd _ (by simp) o ho⟩

/-- The same allocator world witnesses separate both returned regions. -/
theorem lst_new_stable_joint_regions (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ ∃ S Nd,
      WorldTypedWith post S Nd ∧ LogsLiveOwned post S Nd (locN s "logs") ∧
      (∀ o ∈ worldOwned post S Nd, Disj (w.toNat, 24) o) ∧
      (∀ o ∈ worldOwned post S Nd,
        Disj (memW post w.toNat, 8 * locN s "stable_log_cap") o) := by
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  obtain ⟨a, b, _, _, _, _, ho⟩ := hp.1.1.1.2.2.2
  have hLc := (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.1.1.1.2.1
  have hOc := logsWorldOwned_with_locals callee (s.clock - 1) ho
  obtain ⟨S, Nd, hW, hO, hQ⟩ := logsWorldOwned_heapStep_joint
    (hw (Or.inl ⟨v, rfl⟩)) (worldOK_callEntry hp.1.1.1.1.1.1 callee).1 hLc hOc
  have hargs := lst_new_stable_args s vs body callee ret hc hp ha hl
  obtain ⟨w, hv, hd⟩ := hQ hargs.2.2.2 v rfl
  refine ⟨w, hv, S, Nd, hW, hO, fun o ho => hd _ (by simp) o ho, ?_⟩
  intro o ho
  have hb := hd (memW post w.toNat,
    locN (callEntryStateHOLFinite s callee) "esz" *
      locN (callEntryStateHOLFinite s callee) "cap") (by simp) o ho
  simpa only [hargs.1, hargs.2.1] using hb

/-- Restoring caller locals retains the joint separation witnesses for both
regions used by the stable copy. -/
theorem lst_new_stable_resumed_joint_regions (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    ∃ S Nd, WorldTypedWith t S Nd ∧ LogsLiveOwned t S Nd (locN t "logs") ∧
      (∀ o ∈ worldOwned t S Nd, Disj (locN t "stable_logs", 24) o) ∧
      (∀ o ∈ worldOwned t S Nd,
        Disj (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") o) := by
  obtain ⟨w, rfl, S, Nd, hW, hO, hh, hb⟩ :=
    lst_new_stable_joint_regions h s vs body callee ret v post hc hp ha hl hr
  refine ⟨S, Nd, ?_, ?_, ?_, ?_⟩
  · exact (R13Shards.worldTypedWith_with_locals post _ post.clock S Nd).mpr hW
  · change LogsLiveOwned post S Nd _
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "stable_logs" ≠ ofString "logs" by decide] using hO
  · change ∀ o ∈ worldOwned post S Nd, Disj _ o
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hh
  · change ∀ o ∈ worldOwned post S Nd, Disj _ o
    simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "stable_logs" ≠ ofString "stable_log_cap" by decide] using hb

/-- Assemble all copy spatial facts directly from the allocation return. -/
theorem lst_new_stable_resumed_spatial (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    StableCopySpatial
      (setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}) := by
  obtain ⟨S, Nd, hW, hO, _, hb⟩ :=
    lst_new_stable_resumed_joint_regions h s vs body callee ret v post hc hp ha hl hr
  exact ⟨S, Nd, hW, hO, hb,
    lst_new_stable_resumed_source_header h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_header_backing h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_source_array h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_backing_records h s vs body callee ret v post hc hp ha hl hr⟩

/-- Allocation establishes the full precondition for the stable length write,
given the caller's word-shaped length operand. -/
theorem lst_new_stable_length_pre (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl")))))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    StableLengthPre (setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}) := by
  obtain ⟨hstorage, halloc, hword, hnword⟩ :=
    lst_new_stable_length_operands h s vs body callee ret v post hc hp hn ha hl hr
  obtain ⟨hh, hb⟩ := lst_new_stable_resumed_header_separation h s vs body callee ret v post hc hp ha hl hr
  have he := lst_new_stable_resumed_record_separation h s vs body callee ret v post hc hp ha hl hr
  obtain ⟨w, rfl, S, Nd, hW, hO, hdisj⟩ := lst_new_stable_joint_owned h s vs body callee ret v post hc hp ha hl hr
  refine ⟨hstorage, halloc, hword, hnword, S, Nd, ?_, ?_, ?_, hh, hb, he⟩
  · exact (R13Shards.worldTypedWith_with_locals post _ post.clock S Nd).mpr hW
  · change LogsLiveOwned post S Nd _
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "stable_logs" ≠ ofString "logs" by decide] using hO
  · change ∀ o ∈ worldOwned post S Nd, Disj _ o
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hdisj

/-- Restoring caller locals after allocation preserves the typed source pointer. -/
theorem stable_allocation_source_operand {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) (p : BitVec 64)
    (hp : s.locals.lookup (ofString "lp") = some (.val (.word p))) :
    (setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}).locals.lookup
      (ofString "lp") = some (.val (.word p)) := by
  simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "lp" by decide] using hp

/-- Allocation supplies length validity and copy separation in the same resumed state. -/
theorem lst_new_stable_length_spatial (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl")))))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    StableLengthPre t ∧ StableCopySpatial t := by
  exact ⟨lst_new_stable_length_pre h s vs body callee ret v post hc hp hn ha hl hr,
    lst_new_stable_resumed_spatial h s vs body callee ret v post hc hp ha hl hr⟩

/-- Allocation supplies the coherent spatial precondition of the length write. -/
theorem lst_new_stable_length_joint_pre (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl")))))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    StableLengthPre t ∧
      (∃ S Nd, WorldTypedWith t S Nd ∧ LogsLiveOwned t S Nd (locN t "logs") ∧
        (∀ o ∈ worldOwned t S Nd, Disj (locN t "stable_logs", 24) o) ∧
        (∀ o ∈ worldOwned t S Nd,
          Disj (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") o)) ∧
      Disj (locN t "logs", 24)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") ∧
      Disj (locN t "stable_logs", 24)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") ∧
      Disj (memW t (locN t "logs"), 8 * memW t (locN t "logs" + 8))
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") ∧
      ∀ j, j < memW t (locN t "logs" + 8) →
        Disj (memW t (memW t (locN t "logs") + 8 * j), 40)
          (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  exact ⟨lst_new_stable_length_pre h s vs body callee ret v post hc hp hn ha hl hr,
    lst_new_stable_resumed_joint_regions h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_source_header h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_header_backing h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_source_array h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_backing_records h s vs body callee ret v post hc hp ha hl hr⟩

/-- Returning from allocation retains the remaining non-spatial copy operands. -/
theorem lst_new_stable_copy_operands (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hz : locN s "logs" ≠ 0)
    (hptr : ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    locN t "logs" ≠ 0 ∧ WordsOK t (locN t "stable_logs", 24) ∧
      ∃ p : BitVec 64, t.locals.lookup (ofString "lp") = some (.val (.word p)) := by
  refine ⟨?_, (lst_new_stable_header_resume h s vs body callee ret v post hc hp ha hl hr).1, ?_⟩
  · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "stable_logs" ≠ ofString "logs" by decide] using hz
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "stable_logs" ≠ ofString "lp" by decide] using hptr

/-- A typed length operand has its canonical representation even at zero. -/
theorem stable_length_canonical_operand {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hn : ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) :
    s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl")))) := by
  obtain ⟨n, hn⟩ := hn
  simpa [locN, hn] using hn

/-- A nonempty copy obtains its typed length operand directly from positivity. -/
theorem lst_new_stable_length_pre_nonempty (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : 0 < locN s "nl")
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    StableLengthPre (setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}) := by
  exact lst_new_stable_length_pre h s vs body callee ret v post hc hp
    (stable_positive_local_word s "nl" hn) ha hl hr

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
