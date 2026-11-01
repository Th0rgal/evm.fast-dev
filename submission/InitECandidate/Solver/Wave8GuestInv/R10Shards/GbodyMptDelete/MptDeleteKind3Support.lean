import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Bound
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.Memory

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.Memory (IvlUnhit wordsOK_transfer
  ivl_allocated_bound memW_eq_of_ivlUnhit memB_eq_of_ivlUnhit
  ivlUnhit_of_frameOutside_aligned disj_allocated_freeGap disj_allocated_heapFree
  disj_allocated_fresh_heap disj_symm)

/-- Changing only locals and clock preserves a key array and a typed heap. -/
theorem mptKeyIn_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (Nd : List Nat) (p len : Nat) :
    KeyIn { s with locals := ls, clock := clock } Nd p len ↔ KeyIn s Nd p len := Iff.rfl

theorem mptNodeHeap_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat) (Nd : List Nat) :
    NodeHeap { s with locals := ls, clock := clock } Nd ↔ NodeHeap s Nd := Iff.rfl

theorem mptStack_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat) (Nd : List Nat) :
    ∀ fs p, MptStack { s with locals := ls, clock := clock } Nd p fs ↔ MptStack s Nd p fs := by
  intro fs
  induction fs with
  | nil => exact fun _ => Iff.rfl
  | cons q qs ih =>
    intro p
    simp only [MptStack, MptFrameOK, mptKeyIn_locals, ih]
    exact Iff.rfl

theorem mptLocN_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ls : HolFiniteMapExact MlS (ValueHOL 64)} {clock : Nat} {n : String}
    (h : ls.lookup (ofString n) = s.locals.lookup (ofString n)) :
    locN { s with locals := ls, clock := clock } n = locN s n := by
  simp only [locN, h]

theorem mptSetVar_locN_ne {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (v : ValueHOL 64) (n : String) (hn : ofString n ≠ name) :
    locN (setVarHOLFinite name v s) n = locN s n := by
  simp only [setVarHOLFinite, locN, HolFiniteMapExact.lookup_update_pointwise, hn, if_false]

theorem mptSetVar_locN_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n : String) (w : BitVec 64) :
    locN (setVarHOLFinite (ofString n) (.val (.word w)) s) n = w.toNat := by
  simp only [setVarHOLFinite, locN, HolFiniteMapExact.lookup_update_pointwise, if_true]

theorem mptDeleteHead_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ n ∈ ["top", "res", "go", "level", "klen", "node", "key"],
      ls.lookup (ofString n) = s.locals.lookup (ofString n))
    (hs : MptDeleteHead s) : MptDeleteHead { s with locals := ls, clock := clock } := by
  obtain ⟨ha, Nd, fs, hn, hstack, hres, hactive⟩ := hs
  have heq : ∀ n ∈ ["top", "res", "go", "level", "klen", "node", "key"],
      locN { s with locals := ls, clock := clock } n = locN s n :=
    fun n hn => mptLocN_locals (hl n hn)
  refine ⟨(arenaReady_with_locals s ls clock).2 ha, Nd, fs,
    (mptNodeHeap_locals s ls clock Nd).2 hn, ?_, ?_, ?_⟩
  · rw [heq "top" (by simp)]
    exact (mptStack_locals s ls clock Nd fs _).2 hstack
  · rw [heq "res" (by simp)]
    exact hres
  · intro hgo
    rw [heq "go" (by simp)] at hgo
    obtain ⟨hle, hnode, hkey⟩ := hactive hgo
    simp only [heq "level" (by simp), heq "klen" (by simp), heq "node" (by simp),
      heq "key" (by simp), mptKeyIn_locals]
    exact ⟨hle, hnode, hkey⟩

/-- Saved frames survive a transition that retains their words, node tags and
key arrays. The node heap may grow and the scratch pointer may decrease. -/
theorem mptStack_transfer {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} (hs : GuestInv s) (ht : GuestInv t)
    (hg : AllocatorGrows s t) (hsub : ∀ n ∈ Nd, n ∈ Nd')
    (hkind : ∀ n ∈ Nd, memW t n = memW s n)
    (hkey : ∀ p len, KeyIn s Nd p len → KeyIn t Nd' p len)
    (hmem : ∀ a, globN s "scratch_ptr" ≤ a → a + 8 ≤ scratchEnd → a % 8 = 0 →
      memW t a = memW s a) :
    ∀ fs p, MptStack s Nd p fs → MptStack t Nd' p fs := by
  intro fs
  induction fs with
  | nil => exact fun _ h => h
  | cons q qs ih =>
    intro p hp
    obtain ⟨hpq, hp0, hf, hrest, htail⟩ := hp
    obtain ⟨hi, hw, hn, hk⟩ := hf
    have hp8 : p % 8 = 0 := hw.1
    have heq (off : Nat) (hoff : off ≤ 32) (hal : off % 8 = 0) :
        memW t (p + off) = memW s (p + off) :=
      hmem _ (by have := hi.1; omega) (by have := hi.2; omega) (by omega)
    have heq0 : memW t p = memW s p := by simpa using heq 0 (by omega) (by decide)
    have heq8 := heq 8 (by omega) (by decide)
    have heq16 := heq 16 (by omega) (by decide)
    have heq24 := heq 24 (by omega) (by decide)
    have heq32 := heq 32 (by omega) (by decide)
    refine ⟨hpq, hp0, ?_, hrest, ?_⟩
    · refine ⟨⟨Nat.le_trans hg.2 hi.1, hi.2⟩, wordsOK_transfer hs ht hw, ?_⟩
      dsimp only
      rw [heq8, heq16, heq24, heq32, hkind _ hn]
      refine ⟨hsub _ hn, ?_⟩
      rcases hk with ⟨h2, hn2, hpath⟩ | ⟨h3, hn3, hidx⟩
      · exact Or.inl ⟨h2, hn2, hkey _ _ hpath⟩
      · exact Or.inr ⟨h3, hn3, hidx⟩
    · rw [heq0]
      exact ih _ htail

/-- A key array survives a node function's frame, including growth of the node
set into fresh heap. -/
theorem mptKeyIn_nodeFrame {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} (hs : ArenaReady s) (ht : ArenaReady t)
    (hbe : t.be = s.be) (hg : AllocatorGrows s t)
    (hN : NodeHeap s Nd)
    (hkind : ∀ n ∈ Nd, memW t n = memW s n)
    (hfresh : ∀ n ∈ Nd', n ∈ Nd ∨
      Inside (nodeIvl t n) (globN s "heap_ptr") (globN t "heap_ptr"))
    (hfr : FrameOutside s t
      ((Nd.map fun n => nodeIvl s n) ++
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    {p len : Nat} (hk : KeyIn s Nd p len) : KeyIn t Nd' p len := by
  by_cases hlen : len = 0
  · exact Or.inl hlen
  have ⟨hhlo, hhhi, hflo, hgap, hshi, hh8, hf8, hs8⟩ := hs.2
  rcases hk with hz | ⟨hnib, hal, hi, hd⟩
  · exact Or.inl hz
  · right
    have hunhit : IvlUnhit s t (p, len) := by
      apply ivlUnhit_of_frameOutside_aligned hfr
      · intro j hj
        rcases List.mem_append.1 hj with hj | hj
        · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hj
          exact ⟨(hN.1 n hn).2.2.2.1.1, (hN.1 n hn).2.2.2.1.2.1⟩
        · have hj' := List.mem_singleton.1 hj
          subst j
          exact ⟨hf8, by omega⟩
      · exact ⟨hh8, by
          have h8 : heapLimit % 8 = 0 := by decide
          omega⟩
      · intro j hj
        rcases List.mem_append.1 hj with hj | hj
        · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hj
          exact hd n hn
        · have hj' := List.mem_singleton.1 hj
          subst j
          exact disj_allocated_freeGap hs.2 hal
      · exact disj_allocated_heapFree hs.2 hal
      · exact hlen
    refine ⟨?_, hg.allocated hal, hi, ?_⟩
    · intro k hk
      rw [memB_eq_of_ivlUnhit hunhit hbe (by
        have := hi.2
        have hlim : heapLimit ≤ 2 ^ 64 := by decide
        omega) ⟨by omega, by omega⟩]
      exact hnib k hk
    · intro n hn
      rcases hfresh n hn with hold | hnew
      · have hivl : nodeIvl t n = nodeIvl s n := by
          simp only [nodeIvl, hkind n hold]
        rw [hivl]
        exact hd n hold
      · exact disj_symm (disj_allocated_fresh_heap hs.2 ht.2 hal hnew)

/-- A node function cannot overwrite a word in the caller's allocated scratch
stack: nodes lie in the heap, and the scratch write region ends at the old
scratch pointer. -/
theorem mptScratch_nodeFrame {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : ArenaReady s) (hN : NodeHeap s Nd)
    (hfr : FrameOutside s t
      ((Nd.map fun n => nodeIvl s n) ++
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    {a : Nat} (hlo : globN s "scratch_ptr" ≤ a) (hhi : a + 8 ≤ scratchEnd) :
    memW t a = memW s a := by
  have ⟨hhlo, hhhi, hflo, hgap, hshi, hh8, hf8, hs8⟩ := hs.2
  have hsep : heapLimit ≤ scratchStart := by decide
  have ha : a < 2 ^ 64 := by
    have hlim : scratchEnd < 2 ^ 64 := by decide
    omega
  have hnat : (BitVec.ofNat 64 a).toNat = a := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  unfold memW
  rw [hfr _ ?_ ?_]
  · intro j hj hhit
    rw [hnat] at hhit
    rcases List.mem_append.1 hj with hj | hj
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hj
      have hin := (hN.1 n hn).2.2.1.2
      change n + nodeSize (memW s n) ≤ heapLimit at hin
      change n < a + 8 ∧ a < n + nodeSize (memW s n) at hhit
      omega
    · obtain rfl := List.mem_singleton.1 hj
      change globN s "frame_mem_ptr" < a + 8 ∧
        a < globN s "frame_mem_ptr" +
          (globN s "scratch_ptr" - globN s "frame_mem_ptr") at hhit
      omega
  · rw [hnat]
    change ¬ (globN s "heap_ptr" < a + 8 ∧
      a < globN s "heap_ptr" + (heapLimit - globN s "heap_ptr"))
    omega

theorem mptFreeFrame_unhit {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s)
    (hfr : FrameOutside s t
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    {i : Ivl} (hi : Allocated s i) : IvlUnhit s t i := by
  obtain ⟨hhlo, hhhi, hflo, hgap, hshi, hh8, hf8, hs8⟩ := hs.2
  have hsep : heapLimit ≤ scratchStart := by decide
  intro a ha8 hhit
  apply hfr a
  · intro j hj hjhit
    obtain rfl := List.mem_singleton.1 hj
    dsimp [CellHits] at hhit hjhit
    rcases hi with hi | hi <;> dsimp [Inside] at hi <;> omega
  · intro hhit'
    dsimp [CellHits] at hhit hhit'
    rcases hi with hi | hi <;> dsimp [Inside] at hi <;> omega

theorem mptNodeExtents_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hN : NodeHeap s Nd) {i : Ivl} (hi : i ∈ nodeExtents s Nd) :
    i = (0, 0) ∨ Allocated s i := by
  obtain ⟨n, hn, hi⟩ := List.mem_flatMap.1 hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact Or.inr (hN.1 n hn).2.1
  · obtain rfl := List.mem_singleton.1 hi
    unfold nodePath
    split
    · rename_i hc
      rcases (hN.1 n hn).2.2.2.2.2.2.1 hc.1 with hz | hk
      · exact (hc.2 hz).elim
      · exact Or.inr hk.2.1
    · exact Or.inl rfl

theorem mptFreeFrame_heap {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : ArenaReady s) (ht : ArenaReady t) (hbe : t.be = s.be)
    (hg : AllocatorGrows s t) (hN : NodeHeap s Nd)
    (hfr : FrameOutside s t
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    NodeHeap t Nd ∧ (∀ p len, KeyIn s Nd p len → KeyIn t Nd p len) ∧
      (∀ n ∈ Nd, memW t n = memW s n) := by
  have hu : ∀ i ∈ nodeExtents s Nd, IvlUnhit s t i := by
    intro i hi
    rcases mptNodeExtents_allocated hN hi with rfl | hal
    · intro a _ hhit
      exact (Nat.not_lt_zero _ hhit.2).elim
    · exact mptFreeFrame_unhit hs hfr hal
  have hNt := (InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.Memory.nodeHeap_congr_unhit
    hs.1 ht.1 hbe hg hN hu).1
  have hkind : ∀ n ∈ Nd, memW t n = memW s n := by
    intro n hn
    have hp := hN.1 n hn
    have hmin : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
    exact memW_eq_of_ivlUnhit (mptFreeFrame_unhit hs hfr hp.2.1) hp.2.2.2.1.1
      (ivl_allocated_bound hs.2 hp.2.1).2 ⟨Nat.le_refl _, by dsimp [nodeIvl]; omega⟩
  have hfr' : FrameOutside s t
      ((Nd.map fun n => nodeIvl s n) ++
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
    intro a hk hf
    exact hfr a (fun i hi => hk i (List.mem_append_right _ hi)) hf
  exact ⟨hNt, fun _ _ hk => mptKeyIn_nodeFrame hs ht hbe hg hN hkind
    (fun _ hn => Or.inl hn) hfr' hk, hkind⟩

/-- Restore caller locals and optionally bind a local call destination. -/
def mptCallPost {F : Type} (dst : Option MlS)
    (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    PanSemStateFiniteExact 64 F :=
  match dst with
  | none => { post with locals := s.locals }
  | some n => setVarHOLFinite n v { post with locals := s.locals }

theorem mptOneParam_lookup
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fname param : MlS) (shape ret : ShapeHOL) (body : ProgHOL 64) (v : ValueHOL 64)
    {body' : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hi : code.lookup fname = some ([(param, shape)], body, ret))
    (hl : lookupCodeHOLFinite code.lookup fname [v] = some (body', callee, ret')) :
    callee.lookup param = some v := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · cases hl
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hl
    obtain ⟨rfl, hrest⟩ := Prod.mk.inj heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest
    unfold lookupCodeHOLExact at raw
    rw [hi] at raw
    dsimp only at raw
    split at raw
    · have heq := Option.some.inj raw
      obtain ⟨_, hrest⟩ := Prod.mk.inj heq
      obtain ⟨hloc, _⟩ := Prod.mk.inj hrest
      subst hloc
      simp [List.zip, List.foldl]
    · cases raw

theorem mptOneArg_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {arg : ExpHOL 64} {values : List (ValueHOL 64)}
    (h : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] = some values) :
    ∃ v, values = [v] ∧ evalAt s arg = some v := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp only [evalListHOLExact] at h
  rcases hv : evalAt s arg with _ | v
  · change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg = none at hv
    rw [hv] at h
    cases h
  · change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg = some v at hv
    rw [hv] at h
    cases h
    exact ⟨v, rfl, rfl⟩

theorem mptOneLocal_param {F : Type} {s : PanSemStateFiniteExact 64 F}
    {fname : MlS} {param arg : String} {shape ret : ShapeHOL} {body body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    {values : List (ValueHOL 64)}
    (hi : s.code.lookup fname = some ([(ofString param, shape)], body, ret))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString arg)] = some values)
    (hl : lookupCodeHOLFinite s.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup (ofString param) = s.locals.lookup (ofString arg) := by
  obtain ⟨v, rfl, hv⟩ := mptOneArg_eval ha
  have hp := mptOneParam_lookup s.code fname (ofString param) shape ret body v hi hl
  change s.locals.lookup (ofString arg) = some v at hv
  exact hp.trans hv.symm

/-- Normal calls expose their successful argument/lookup/body evaluations to
the postcondition proof. Other outcomes cannot continue the descent. -/
theorem mptCall_hoare
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (dst : Option MlS) (fname : MlS) (args : List (ExpHOL 64))
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values body callee ret v post,
      s.code = originalRuntimeCode → P s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Q none (mptCallPost dst s post v))
    (hother : ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
      r ≠ none → r ≠ some .continue → Q r t) :
    Hoare P (.call (some (dst.map (fun n => (.local, n)), none)) fname args) Q := by
  refine ⟨fun {F} s hc hp _ => ?_⟩
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s
    (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact hother _ _ (by simp) (by simp)
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · exact hother _ _ (by simp) (by simp)
    · dsimp only
      split
      · exact hother _ _ (by simp) (by simp)
      · rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        cases r with
        | none => exact hother _ _ (by simp) (by simp)
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · cases dst with
              | none => exact hret s values body callee ret v post hc hp hargs hl hr
              | some n =>
                dsimp only [Option.map]
                split
                · exact hret s values body callee ret v post hc hp hargs hl hr
                · exact hother _ _ (by simp) (by simp)
            · exact hother _ _ (by simp) (by simp)
          | «continue» => exact hother _ _ (by simp) (by simp)
          | «break» => exact hother _ _ (by simp) (by simp)
          | timeOut => exact hother _ _ (by simp) (by simp)
          | error => exact hother _ _ (by simp) (by simp)
          | exception _ _ => exact hother _ _ (by simp) (by simp)
          | _ => exact hother _ _ (by simp) (by simp)

theorem mptHoare_seq
    {P R S : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p q : ProgHOL 64}
    (hp : Hoare P p (fun r t => r = none → R t))
    (hq : Hoare R q (fun r t => r = none → S t)) :
    Hoare P (.seq p q) (fun r t => r = none → S t) := by
  apply Hoare.seq (R := R)
  · exact ⟨fun s hc hP hnt => ⟨hp.run s hc hP hnt, fun hn hz => (hn hz).elim⟩⟩
  · exact hq

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
