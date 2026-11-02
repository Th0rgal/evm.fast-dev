import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.GuestTrapOutcomes
import InitECandidate.Solver.HeapPotential
import Guest.SoftwareAst

/-! Shared light-cone definitions and world-typing frame lemmas for contract micro-shard `m08`
(`wave8/contracts-m08`, frozen spec rev9 `8a79d9f28`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.MemoryViews` plus
existing cone modules (`GuestTrapOutcomes`, `HeapPotential`, `Guest.SoftwareAst`).
Restates `FunSpec`, `Resumes`, `WorldStep`, `WorldKeeps`, `RetAvoids`, `RetMptObj`, etc.
verbatim from `campaign/specs-proposed/GuestInv.lean` @ `8a79d9f28bdd7a3522f8a9a81a892d9ecaabdeff`
so every proved theorem delta-reduces definitionally (`rfl`) to its frozen spec statement in
`Axioms.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M08

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Verbatim rev9 contract definitions (`GuestInv.lean` @ `8a79d9f28`) -/

def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

def MptObjInWith {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nm : List Nat) (m : Nat) : Prop :=
  Allocated s (m, 16) ∧ WordsOK s (m, 16) ∧
  (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (m, 16) i) ∧
  (∀ j ∈ fixedObjects s, Disj (m, 16) j) ∧
  NodeHeap s Nm ∧ RootIn Nm (memW s m) ∧
    ∀ o ∈ nodeExtents s Nm, Disj o (m, 16) ∧
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧
      ∀ j ∈ fixedObjects s, Disj o j

def WorldTypedWith {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  TablesTyped s S ∧ JournalTyped s S ∧ FixedTyped s ∧ TriesTypedWith s S Nd

def typedRecords : List (String × Nat) := [("ws", 40), ("bs", 80), ("ts", 72), ("bo", 88)]

def worldTypedIvls {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : List Ivl :=
  S.flatMap (htabFootprint s) ++
    typedRecords.map (fun r => (globN s r.1, if globN s r.1 = 0 then 0 else r.2)) ++
    [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
      32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s ++
    nodeExtents s Nd

def worldOwned {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : List Ivl :=
  S.flatMap (htabFootprint s) ++ fixedObjects s ++ nodeExtents s Nd

def IvlsDisj (os js : List Ivl) : Prop := ∀ o ∈ os, ∀ j ∈ js, Disj o j

def freeGap {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")

def heapFree {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (globN s "heap_ptr", heapLimit - globN s "heap_ptr")

def GlobalsKept (gw : List String) {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ k : MlS, k ∉ gw.map ofString → s.globals.lookup k = post.globals.lookup k

def RecordsKept (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl)
    (keep : List (String × List Nat)) {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ r ∈ keep, globN s r.1 ≠ 0 → ∀ k ∈ r.2, (∀ i ∈ R s, ¬ CellHits (globN s r.1 + k) i) →
    memW post (globN s r.1 + k) = memW s (globN s r.1 + k)

def OwnedGrows {F : Type} (s post : PanSemStateFiniteExact 64 F) (old new : List Ivl) : Prop :=
  ∀ o ∈ new, o = (0, 0) ∨ (∃ j ∈ old, Inside o j.1 (j.1 + j.2)) ∨
    Inside o (globN s "heap_ptr") (globN post "heap_ptr")

def NoExtra : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun _ _ _ _ _ => True

def WorldStep (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post =>
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    GlobalsKept gw s post ∧ RecordsKept R keep s post ∧
    ∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (R s) (worldTypedIvls s S Nd) →
      ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
        FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
        Q s r post S' Nd'

def WorldKeeps (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun s r post => Resumes r → WorldStep R gw keep Q s r post) fname

def mptObjIvls {F : Type} (s : PanSemStateFiniteExact 64 F) (Nm : List Nat) (m : Nat) : List Ivl :=
  (m, 16) :: nodeExtents s Nm

def FreshBlock {F : Type} (s post : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  p % 8 = 0 ∧ Inside (p, (n + 7) / 8 * 8) (globN s "heap_ptr") (globN post "heap_ptr") ∧
    WordsOK post (p, (n + 7) / 8 * 8)

def RetMptObj : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    AllocatorGrows s post ∧
    ∃ Nm, MptObjInWith post S' Nm w.toNat ∧ IvlsDisj (mptObjIvls post Nm w.toNat) (nodeExtents post Nd') ∧
      ∀ o ∈ mptObjIvls post Nm w.toNat, o = (0, 0) ∨
        Inside o (globN s "heap_ptr") (globN post "heap_ptr")

def RetAvoids (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
    List Ivl) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    IvlsDisj (B s post w.toNat) (worldOwned post S' Nd')

/-! ## 2. Ordinary domain & interval geometry -/

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  unfold ordinaryDomain
  rw [StackRemove.mem_addresses]
  have hx := x.isLt
  have hconst : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 ∧
      sourceBase = 2701131776 ∧ heapEnd = 33806089704 ∧
      StackRemove.bytesInWord 64 = BitVec.ofNat 64 8 := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    decide
  rcases hconst with ⟨hn, hsb, hhe, hbw⟩
  rw [hn, hbw]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe]
    omega
  · rintro ⟨hal, hlo, hhi⟩
    refine ⟨(x.toNat - sourceBase) / 8, by simp only [hsb, hhe] at hlo hhi; omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe] at hlo hhi ⊢
    omega

theorem wordAt_of_ordinary {F : Type} {s : PanSemStateFiniteExact 64 F} (hg : GuestInv s)
    {a : Nat} (ha8 : a % 8 = 0) (hlo : sourceBase ≤ a) (hhi : a < heapEnd) :
    WordAt s a := by
  have ha_lt : a < 2 ^ 64 := by
    have : heapEnd < 2 ^ 64 := by decide
    omega
  rcases hm : s.memory (BitVec.ofNat 64 a) with ⟨w⟩
  refine ⟨w, ?_, hm⟩
  rw [hg.memaddrs, ordinaryDomain_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  exact ⟨ha8, hlo, hhi⟩

theorem disj_symm {i j : Ivl} (h : Disj i j) : Disj j i := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem disj_zero_left (j : Ivl) : Disj (0, 0) j := Or.inl rfl
theorem disj_zero_right (i : Ivl) : Disj i (0, 0) := Or.inr (Or.inl rfl)

theorem disj_of_inside_left {i i' j : Ivl} (hin : Inside i i'.1 (i'.1 + i'.2))
    (hd : Disj i' j) : Disj i j := by
  rcases hin with ⟨h1, h2⟩
  rcases hd with h0 | h0 | hd | hd
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem disj_of_inside_right {i j j' : Ivl} (hin : Inside j j'.1 (j'.1 + j'.2))
    (hd : Disj i j') : Disj i j :=
  disj_symm (disj_of_inside_left hin (disj_symm hd))

theorem disj_allocated_fresh_heap {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) (hp : ArenaOK post) {i f : Ivl}
    (hi : Allocated s i) (hf : Inside f (globN s "heap_ptr") (globN post "heap_ptr")) :
    Disj f i := by
  rcases hi with hi | hi
  · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hi.2 hf.1)))
  · have hsep : heapLimit ≤ scratchStart := by decide
    exact Or.inr (Or.inr (Or.inl (Nat.le_trans hf.2 (Nat.le_trans hp.2.1
      (Nat.le_trans hsep (Nat.le_trans hs.2.2.1 (Nat.le_trans hs.2.2.2.1 hi.1)))))))

theorem disj_allocated_heapFree {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) {i : Ivl} (hi : Allocated s i) :
    Disj i (heapFree s) := by
  unfold heapFree
  rcases hi with hi | hi
  · exact Or.inr (Or.inr (Or.inl hi.2))
  · have hsep : heapLimit ≤ scratchStart := by decide
    have := hs.1; have := hs.2.1; have := hs.2.2.1; have := hs.2.2.2.1; have := hi.1
    exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))

theorem disj_allocated_freeGap {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) {i : Ivl} (hi : Allocated s i) :
    Disj i (freeGap s) := by
  unfold freeGap
  rcases hi with hi | hi
  · have hsep : heapLimit ≤ scratchStart := by decide
    have := hs.2.1; have := hs.2.2.1; have := hi.2
    exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
  · have := hs.2.2.2.1; have := hi.1
    exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))

theorem not_cellHits_of_disj {a : Nat} {i j : Ivl}
    (ha8 : a % 8 = 0) (hj1 : j.1 % 8 = 0)
    (ha : a ≥ i.1 ∧ a + 8 ≤ i.1 + i.2) (hd : Disj i j) :
    ¬ CellHits a j := by
  intro ⟨hc1, hc2⟩
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  dsimp only [CellHits, Disj] at ha8 hj1 ha hc1 hc2 hd
  rcases hd with h0 | h0 | hd | hd
  · exact Nat.not_lt.mpr (h0 ▸ ha.2 : a + 8 ≤ i1 + 0) (by omega)
  · have hlt : a < j1 := by simpa [h0] using hc2
    omega
  · omega
  · omega

theorem globN_eq_of_lookup {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : String}
    (h : s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) :
    globN post name = globN s name := by
  unfold globN; rw [← h]

theorem globN_congr {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : post.globals = s.globals) (name : String) :
    globN post name = globN s name := by
  unfold globN; rw [h]

theorem mem0_8_16_eq_of_domain_writes {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hd : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a)
    (hg : GuestInv s) :
    memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
  have hsb : 24 < sourceBase := by decide
  refine ⟨?_, ?_, ?_⟩
  · by_cases heq : post.memory 0 = s.memory 0
    · unfold memW; exact congrArg (fun w => match w with | .word v => v.toNat) heq
    · have hdom := hd 0 heq
      rw [hg.memaddrs, ordinaryDomain_iff] at hdom
      change _ ∧ sourceBase ≤ 0 ∧ _ at hdom; omega
  · by_cases heq : post.memory (BitVec.ofNat 64 8) = s.memory (BitVec.ofNat 64 8)
    · unfold memW; rw [heq]
    · have hdom := hd (BitVec.ofNat 64 8) heq
      rw [hg.memaddrs, ordinaryDomain_iff] at hdom
      have h8 : (BitVec.ofNat 64 8).toNat = 8 := by decide
      rw [h8] at hdom; omega
  · by_cases heq : post.memory (BitVec.ofNat 64 16) = s.memory (BitVec.ofNat 64 16)
    · unfold memW; rw [heq]
    · have hdom := hd (BitVec.ofNat 64 16) heq
      rw [hg.memaddrs, ordinaryDomain_iff] at hdom
      have h16 : (BitVec.ofNat 64 16).toNat = 16 := by decide
      rw [h16] at hdom; omega

/-! ## 3. Sub-object congruence under unhit aligned cells -/

def IvlUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  ∀ a : BitVec 64, a.toNat % 8 = 0 → i.1 ≤ a.toNat → a.toNat + 8 ≤ i.1 + i.2 → post.memory a = s.memory a

theorem memW_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) {a : Nat}
    (ha8 : a % 8 = 0) (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  have hmem := hu (BitVec.ofNat 64 a)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact ha8)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact hin.1)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact hin.2)
  unfold memW
  rw [hmem]

theorem memB_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hi1 : i.1 % 8 = 0) (hi2 : i.2 % 8 = 0) (hu : IvlUnhit s post i) (hbe : post.be = s.be)
    {a : Nat} (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a < i.1 + i.2) :
    memB post a = memB s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  let c := panByteAlignHOL (BitVec.ofNat 64 a)
  have hc_nat : c.toNat = a / 8 * 8 := by
    have hal : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
    change (BitVec.ofNat 64 ((BitVec.ofNat 64 a).toNat / 2 ^ ((64 : Nat) / 8).log2 *
      2 ^ ((64 : Nat) / 8).log2)).toNat = a / 8 * 8
    rw [hal, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self a 8) ha_lt)]
  have hmem := hu c (by rw [hc_nat]; omega) (by rw [hc_nat]; omega) (by rw [hc_nat]; omega)
  unfold memB
  change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v post.be).toNat) =
         (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v s.be).toNat)
  rw [hmem, hbe]

theorem ivl_allocated_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hal : Allocated s i) :
    i.1 + i.2 ≤ heapEnd ∧ i.1 + i.2 ≤ 2 ^ 64 := by
  have h1 : heapLimit ≤ heapEnd := by decide
  have h2 : scratchEnd ≤ heapEnd := by decide
  have h3 : heapEnd < 2 ^ 64 := by decide
  rcases hal with ⟨_, hi⟩ | ⟨_, hi⟩
  · have := hA.2.1; omega
  · have := hA.2.2.2.2.1; omega

theorem wordsOK_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {i : Ivl} (hw : WordsOK s i) :
    WordsOK post i := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨_, hdom, _⟩ := hw.2.2 k hk
  rcases hm : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hm⟩
  rw [hgP.memaddrs, ← hgS.memaddrs]
  exact hdom

theorem wordsOK_fresh_heap {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hg : GuestInv s) {p sz : Nat} (hp8 : p % 8 = 0) (hsz8 : sz % 8 = 0)
    (hlo : sourceBase ≤ p) (hhi : p + sz ≤ heapLimit) :
    WordsOK s (p, sz) := by
  have hhl : heapLimit ≤ heapEnd := by decide
  refine ⟨hp8, hsz8, fun k hk => ?_⟩
  dsimp only at hk ⊢
  exact wordAt_of_ordinary hg (by omega) (by omega) (by omega)

theorem freeChain_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nodes ncap : Nat} (hn8 : nodes % 8 = 0) (hhi : nodes + (ncap + 1) * 32 ≤ 2 ^ 64)
    (hu : IvlUnhit s post (nodes, (ncap + 1) * 32)) :
    ∀ (Fr : List Nat) (head : Nat),
      (∀ f ∈ Fr, 1 ≤ f ∧ f ≤ ncap) →
      (FreeChain post nodes head Fr ↔ FreeChain s nodes head Fr)
  | [], head, _ => Iff.rfl
  | f :: rest, head, hFr => by
    have hf : 1 ≤ f ∧ f ≤ ncap := hFr f (by simp)
    have hnd : nodeF post nodes f 0 = nodeF s nodes f 0 := by
      unfold nodeF
      exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    simp only [FreeChain, hnd]
    exact and_congr Iff.rfl (freeChain_congr_unhit hn8 hhi hu rest _ (fun x hx => hFr x (by simp [hx])))

theorem htabFootprint_eq_of_hdr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} (ht8 : t % 8 = 0) (hhdr_hi : t + 88 ≤ 2 ^ 64) (hu : IvlUnhit s post (t, 88)) :
    (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
  have hhdr : ∀ k, k < 11 → hdr post t k = hdr s t k := fun k hk => by
    unfold hdr
    exact memW_eq_of_ivlUnhit hu (by omega) hhdr_hi ⟨by omega, by omega⟩
  refine ⟨hhdr, ?_⟩
  simp only [htabFootprint, hhdr 1 (by omega), hhdr 4 (by omega), hhdr 5 (by omega),
    hhdr 6 (by omega), hhdr 10 (by omega)]

theorem nodup_len_le {l : List Nat} {n : Nat} (hnd : l.Nodup)
    (hr : ∀ x ∈ l, 1 ≤ x ∧ x < n) : l.length ≤ n - 1 := by
  have hsub : l.toFinset ⊆ Finset.Ico 1 n := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    simp only [Finset.mem_Ico]
    exact hr x hx
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Nat.card_Ico] at this
  exact this

theorem htabValues_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i) :
    htabValues post t = htabValues s t := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have hnd_fp : (hdr s t 5, (hdr s t 10 + 1) * 32) ∈ htabFootprint s t := by simp [htabFootprint]
  have hord_fp : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hnd8 : (hdr s t 5) % 8 = 0 := (hfp _ hnd_fp).2.1
  have hord8 : (hdr s t 6) % 8 = 0 := (hfp _ hord_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, _⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hnd_hi : hdr s t 5 + (hdr s t 10 + 1) * 32 ≤ 2 ^ 64 := by have := (hfp _ hnd_fp).1.2; omega
  have hord_hi : hdr s t 6 + (hdr s t 10 + 1) * 8 ≤ 2 ^ 64 := by have := (hfp _ hord_fp).1.2; omega
  obtain ⟨-, -, -, -, -, _, _, hnext_le, L, I, Fr, hLlen, hnodup, hmem, _, hL, -⟩ := hwf
  have hlen_all := nodup_len_le hnodup (fun x hx => (hmem x).1 hx)
  have hlen_L : L.length ≤ hdr s t 10 := by
    simp only [List.length_append] at hlen_all; omega
  unfold htabValues
  rw [hhdr 3 (by omega), hhdr 5 (by omega), hhdr 6 (by omega)]
  apply List.map_congr_left
  intro idx hidx
  rw [List.mem_range] at hidx
  have hidx_L : idx < L.length := by omega
  have hLi_mem : L[idx] ∈ L ++ I ++ Fr := by
    apply List.mem_append.2; left; apply List.mem_append.2; left; exact List.getElem_mem hidx_L
  have hLi_bound : 1 ≤ L[idx] ∧ L[idx] ≤ hdr s t 10 := by
    have := (hmem L[idx]).1 hLi_mem; omega
  have hord_eq : memW post (hdr s t 6 + 8 * idx) = memW s (hdr s t 6 + 8 * idx) :=
    memW_eq_of_ivlUnhit (hu _ hord_fp) (by omega) hord_hi ⟨by omega, by omega⟩
  rw [hord_eq, (hL idx hidx_L).1]
  unfold nodeF
  exact memW_eq_of_ivlUnhit (hu _ hnd_fp) (by omega) hnd_hi ⟨by omega, by omega⟩

theorem htabValuesIn_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} {S S' : List Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hsub : ∀ x ∈ S, x ∈ S')
    (hval : HtabValuesIn s t S) :
    HtabValuesIn post t S' := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, _⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hvals := htabValues_eq_of_unhit hwf hu
  intro idx hidx
  rw [hhdr 3 (by omega)] at hidx
  have hmem_s : nodeF s (hdr s t 5) (memW s (hdr s t 6 + 8 * idx)) 8 ∈ S := hval idx hidx
  have hget : (htabValues post t)[idx]? = (htabValues s t)[idx]? := by rw [hvals]
  simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr 3 (by omega), hidx,
    Option.map_some, Option.some.injEq] at hget
  rw [hget]
  exact hsub _ hmem_s

theorem htabWF_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    {t : Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i) :
    HtabWF post t := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have hnd_fp : (hdr s t 5, (hdr s t 10 + 1) * 32) ∈ htabFootprint s t := by simp [htabFootprint]
  have hord_fp : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hnd8 : (hdr s t 5) % 8 = 0 := (hfp _ hnd_fp).2.1
  have hord8 : (hdr s t 6) % 8 = 0 := (hfp _ hord_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, hfp_eq⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hnd_hi : hdr s t 5 + (hdr s t 10 + 1) * 32 ≤ 2 ^ 64 := by have := (hfp _ hnd_fp).1.2; omega
  have hord_hi : hdr s t 6 + (hdr s t 10 + 1) * 8 ≤ 2 ^ 64 := by have := (hfp _ hord_fp).1.2; omega
  obtain ⟨hfp1, hfp2, hk1, hk2, hstr, hncap, hnext1, hnext2,
    L, I, Fr, hLlen, hnodup, hmem, hcntI, hL, hI, hr0, hrpos, hnroot, hpI, hdep, hfc⟩ := hwf
  have hlen_all := nodup_len_le hnodup (fun x hx => (hmem x).1 hx)
  have hlen_L : L.length ≤ hdr s t 10 := by
    simp only [List.length_append] at hlen_all; omega
  have hnd_eq : ∀ n, 1 ≤ n → n ≤ hdr s t 10 → ∀ off ∈ ([0, 8, 16, 24] : List Nat),
      nodeF post (hdr s t 5) n off = nodeF s (hdr s t 5) n off := by
    intro n hn1 hn2 off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    unfold nodeF
    rcases hoff with rfl | rfl | rfl | rfl <;>
      exact memW_eq_of_ivlUnhit (hu _ hnd_fp) (by omega) hnd_hi ⟨by omega, by omega⟩
  have hLI_bound : ∀ n ∈ L ++ I, 1 ≤ n ∧ n ≤ hdr s t 10 := fun n hn => by
    have := (hmem n).1 (List.mem_append.2 (Or.inl hn)); omega
  unfold HtabWF
  rw [hfp_eq, hhdr 0 (by omega), hhdr 1 (by omega), hhdr 3 (by omega), hhdr 5 (by omega),
    hhdr 6 (by omega), hhdr 7 (by omega), hhdr 8 (by omega), hhdr 9 (by omega), hhdr 10 (by omega)]
  refine ⟨fun i hi => ⟨(hfp1 i hi).1, wordsOK_transfer hgS hgP (hfp1 i hi).2⟩,
    hfp2, hk1, hk2, hstr, hncap, hnext1, hnext2, L, I, Fr, hLlen, hnodup, hmem, hcntI,
    ?_, ?_, hr0, ?_, ?_, ?_, ?_, ?_⟩
  · intro idx hidx
    have hLi : L[idx] ∈ L ++ I := List.mem_append.2 (Or.inl (List.getElem_mem hidx))
    obtain ⟨hb1, hb2⟩ := hLI_bound L[idx] hLi
    have hord_eq : memW post (hdr s t 6 + 8 * idx) = memW s (hdr s t 6 + 8 * idx) :=
      memW_eq_of_ivlUnhit (hu _ hord_fp) (by omega) hord_hi ⟨by omega, by omega⟩
    rw [hord_eq, hnd_eq L[idx] hb1 hb2 24 (by simp), hnd_eq L[idx] hb1 hb2 16 (by simp)]
    exact hL idx hidx
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append.2 (Or.inr hn)
    obtain ⟨hb1, hb2⟩ := hLI_bound n hnLI
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hI n hn
    obtain ⟨h8_1, h8_2⟩ := hLI_bound _ hc2
    obtain ⟨h16_1, h16_2⟩ := hLI_bound _ hc3
    rw [hnd_eq n hb1 hb2 24 (by simp), hnd_eq n hb1 hb2 8 (by simp), hnd_eq n hb1 hb2 16 (by simp),
      hnd_eq _ h8_1 h8_2 0 (by simp), hnd_eq _ h16_1 h16_2 0 (by simp)]
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩
  · intro hpos
    obtain ⟨hrm, hrp⟩ := hrpos hpos
    obtain ⟨hb1, hb2⟩ := hLI_bound _ hrm
    rw [hnd_eq _ hb1 hb2 0 (by simp)]
    exact ⟨hrm, hrp⟩
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append.2 (Or.inr hn)
    obtain ⟨hb1, hb2⟩ := hLI_bound n hnLI
    rw [hnd_eq n hb1 hb2 8 (by simp), hnd_eq n hb1 hb2 16 (by simp)]
    exact hnroot n hn
  · intro n hn hnr
    obtain ⟨hb1, hb2⟩ := hLI_bound n hn
    rw [hnd_eq n hb1 hb2 0 (by simp)]
    exact hpI n hn hnr
  · obtain ⟨dep, hdep⟩ := hdep
    refine ⟨dep, fun n hn hnr => ?_⟩
    obtain ⟨hb1, hb2⟩ := hLI_bound n hn
    have hp_mem : nodeF s (hdr s t 5) n 0 ∈ L ++ I := List.mem_append.2 (Or.inr (hpI n hn hnr))
    obtain ⟨hpb1, hpb2⟩ := hLI_bound _ hp_mem
    rw [hnd_eq n hb1 hb2 0 (by simp), hnd_eq _ hpb1 hpb2 8 (by simp), hnd_eq _ hpb1 hpb2 16 (by simp)]
    exact hdep n hn hnr
  · exact (freeChain_congr_unhit hnd8 hnd_hi (hu _ hnd_fp) Fr (hdr s t 9)
      (fun f hf => by have := (hmem f).1 (List.mem_append.2 (Or.inr hf)); omega)).2 hfc

/-! ## 4. World-typing preservation (W1) -/

def WorldGlobalsSame {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ gn ∈ globalBuffers, globN post gn.1 = globN s gn.1) ∧
  (∀ g ∈ globalTableRoots, globN post g = globN s g) ∧
  globN post "journal" = globN s "journal" ∧
  globN post "journal_cap" = globN s "journal_cap" ∧
  globN post "journal_n" = globN s "journal_n"

theorem worldGlobalsSame_of_kept {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {gw : List String} (hkept : GlobalsKept gw s post)
    (hsub : ∀ name ∈ gw, name = "heap_ptr" ∨ name = "scratch_ptr") :
    WorldGlobalsSame s post := by
  have hnot : ∀ name, ofString name ≠ ofString "heap_ptr" → ofString name ≠ ofString "scratch_ptr" →
      globN post name = globN s name := fun name h1 h2 =>
    globN_eq_of_lookup (hkept (ofString name) (fun hm => by
      obtain ⟨w, hw, heq⟩ := List.mem_map.1 hm
      rcases hsub w hw with rfl | rfl
      · exact h1 heq.symm
      · exact h2 heq.symm))
  refine ⟨fun ⟨gn, sz⟩ hgn => hnot gn ?_ ?_, fun g hg => hnot g ?_ ?_,
    hnot "journal" (by decide) (by decide),
    hnot "journal_cap" (by decide) (by decide),
    hnot "journal_n" (by decide) (by decide)⟩
  · simp only [globalBuffers, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgn
    repeat' rcases hgn with ⟨rfl, _⟩ | hgn
    all_goals decide
  · simp only [globalBuffers, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgn
    repeat' rcases hgn with ⟨rfl, _⟩ | hgn
    all_goals decide
  · simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
    repeat' rcases hg with rfl | hg
    all_goals decide
  · simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
    repeat' rcases hg with rfl | hg
    all_goals decide

theorem typedRecord_mem_globalBuffers {r : String × Nat} (hr : r ∈ typedRecords) :
    r ∈ globalBuffers := by
  simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp [globalBuffers]

theorem typedRecord_mem_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    {r : String × Nat} (hr : r ∈ typedRecords) :
    (globN s r.1, if globN s r.1 = 0 then 0 else r.2) ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
  exact List.mem_map.2 ⟨r, typedRecord_mem_globalBuffers hr, rfl⟩

theorem rec_word_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hF : FixedTyped s)
    (g : String) (sz : Nat) (hrec : (g, sz) ∈ typedRecords)
    (hg_eq : globN post g = globN s g) (hgnz : globN s g ≠ 0)
    (hu : IvlUnhit s post (globN s g, sz))
    {k : Nat} (hk8 : k % 8 = 0) (hksz : k + 8 ≤ sz) :
    memW post (globN post g + k) = memW s (globN s g + k) := by
  rw [hg_eq]
  have hmem_fix := typedRecord_mem_fixedObjects s hrec
  simp only [hgnz, ↓reduceIte] at hmem_fix
  have hsz_pos : sz ≠ 0 := by omega
  rcases hF.1 _ hmem_fix with h0 | ⟨hal, hwords⟩
  · exact absurd h0 hsz_pos
  · have hhi := (ivl_allocated_bound hA hal).2
    have hg8 : (globN s g) % 8 = 0 := hwords.1
    exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩

theorem blockOutObjects_eq_of_bo_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hF : FixedTyped s) (hbo_eq : globN post "bo" = globN s "bo")
    (hbo_lst_ok : globN s "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
      LstOK s (memW s (globN s "bo" + k)))
    (hk24 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 24) = memW s (globN s "bo" + 24))
    (hk32 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 32) = memW s (globN s "bo" + 32))
    (hk40 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 40) = memW s (globN s "bo" + 40))
    (hk56 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 56) = memW s (globN s "bo" + 56))
    (hk72 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 72) = memW s (globN s "bo" + 72))
    (hk80 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 80) = memW s (globN s "bo" + 80))
    (h0_40 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 40) = 0 →
      (if memW post 0 = 0 then (0, 0) else (memW post 0, 8 * memW post 16)) =
      (if memW s 0 = 0 then (0, 0) else (memW s 0, 8 * memW s 16)))
    (h0_72 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 72) = 0 →
      (if memW post 0 = 0 then (0, 0) else (memW post 0, 8 * memW post 16)) =
      (if memW s 0 = 0 then (0, 0) else (memW s 0, 8 * memW s 16)))
    (hl40 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 40) ≠ 0 →
      IvlUnhit s post (memW s (globN s "bo" + 40), 24))
    (hl72 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 72) ≠ 0 →
      IvlUnhit s post (memW s (globN s "bo" + 72), 24)) :
    blockOutObjects post = blockOutObjects s ∧
    (globN post "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat), memW post (globN post "bo" + k) ≠ 0 →
      LstOK post (memW post (globN post "bo" + k))) := by
  by_cases hbo : globN s "bo" = 0
  · refine ⟨?_, fun hp => absurd (hbo_eq.trans hbo) hp⟩
    simp [blockOutObjects, hbo_eq, hbo]
  · have hlst_hdr : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
        ∀ off ∈ ([0, 8, 16] : List Nat),
          memW post (memW s (globN s "bo" + k) + off) = memW s (memW s (globN s "bo" + k) + off) := by
      intro k hk hknz off hoff
      have hmem_bo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> simp [blockOutObjects, hbo, hknz]
      have hmem_fix : (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hmem_bo)))
      rcases hF.1 _ hmem_fix with h0 | ⟨hal, hwords⟩
      · simp at h0
      · have hhi := (ivl_allocated_bound hA hal).2
        have hp8 : (memW s (globN s "bo" + k)) % 8 = 0 := hwords.1
        have hu : IvlUnhit s post (memW s (globN s "bo" + k), 24) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl
          · exact hl40 hbo hknz
          · exact hl72 hbo hknz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl <;>
          exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    constructor
    · unfold blockOutObjects
      simp only [hbo_eq, hbo, false_or, hk24 hbo, hk32 hbo, hk40 hbo, hk56 hbo, hk72 hbo, hk80 hbo]
      congr 1; congr 1
      · by_cases h40 : memW s (globN s "bo" + 40) = 0
        · simp [h40, h0_40 hbo h40]
        · have h0 := hlst_hdr 40 (by simp) h40 0 (by simp)
          have h16 := hlst_hdr 40 (by simp) h40 16 (by simp)
          simp only [Nat.add_zero] at h0
          simp [h40, h0, h16]
      · by_cases h72 : memW s (globN s "bo" + 72) = 0
        · simp [h72, h0_72 hbo h72]
        · have h0 := hlst_hdr 72 (by simp) h72 0 (by simp)
          have h16 := hlst_hdr 72 (by simp) h72 16 (by simp)
          simp only [Nat.add_zero] at h0
          simp [h72, h0, h16]
    · intro _ k hk hknz
      rw [hbo_eq] at hknz ⊢
      have hk_eq : memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · exact hk40 hbo
        · exact hk72 hbo
      rw [hk_eq] at hknz ⊢
      unfold LstOK
      rw [hlst_hdr k hk hknz 8 (by simp), hlst_hdr k hk hknz 16 (by simp)]
      exact hbo_lst_ok hbo k hk hknz

theorem balRecords_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hT : TablesTyped s S)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    (hu : globN s "bal_accounts" ≠ 0 → ∀ i ∈ htabFootprint s (globN s "bal_accounts"), IvlUnhit s post i) :
    balRecords post = balRecords s := by
  unfold balRecords
  rw [hbal_eq]
  by_cases hbal : globN s "bal_accounts" = 0
  · simp [hbal]
  · simp only [hbal, ↓reduceIte]
    have hmem_S : globN s "bal_accounts" ∈ S := by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hbal
      · exact hm
    have hwf := (hT.2.1 _ hmem_S).1
    exact htabValues_eq_of_unhit hwf (hu hbal)

theorem balObjects_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i)
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    balObjects post = balObjects s ∧
    (∀ ad ∈ balRecords post, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  have hrecs : balRecords post = balRecords s :=
    balRecords_eq_of_unhit hT hbal_eq (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi => by
    unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
  have had_props : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      htabValues post (memW s ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat),
        memW post (memW s (ad + k)) = memW s (memW s (ad + k)) ∧
        memW post (memW s (ad + k) + 8) = memW s (memW s (ad + k) + 8) ∧
        memW post (memW s (ad + k) + 16) = memW s (memW s (ad + k) + 16)) ∧
      (∀ l ∈ htabValues s (memW s ad),
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16)) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s := by
      unfold balObjects
      exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (ivl_allocated_bound hA hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact memW_eq_of_ivlUnhit (hu_bal _ had_bal (by simp)) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_tab _ had_T.1)
    have hlst_eq : ∀ l, (l, 24) ∈ balObjects s →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
      intro l hl_bal
      rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      have hhi_l := (ivl_allocated_bound hA hal_l).2
      have hl8 : l % 8 = 0 := hw_l.1
      have hul := hu_bal _ hl_bal (by simp)
      refine ⟨?_, ?_, ?_⟩
      · simpa using memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    refine ⟨hoff_eq, hvals_ad, ?_, ?_⟩
    · intro k hk
      by_cases hk0 : memW s (ad + k) = 0
      · simp [hk0, hm0.1, hm0.2.1, hm0.2.2]
      · apply hlst_eq
        unfold balObjects
        refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hk0]
    · intro l hl
      by_cases hl0 : l = 0
      · subst hl0; simp [hm0.1, hm0.2.1, hm0.2.2]
      · apply hlst_eq
        unfold balObjects
        refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        apply List.mem_cons_of_mem
        apply List.mem_append.2; right
        exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hl0]⟩
  constructor
  · unfold balObjects
    rw [hrecs]
    apply List.flatMap_congr
    intro ad had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h16 := hoff_eq 16 (by simp)
    have h24 := hoff_eq 24 (by simp)
    have h32 := hoff_eq 32 (by simp)
    obtain ⟨hk16_0, _, hk16_16⟩ := hklst 16 (by simp)
    obtain ⟨hk24_0, _, hk24_16⟩ := hklst 24 (by simp)
    obtain ⟨hk32_0, _, hk32_16⟩ := hklst 32 (by simp)
    have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      rw [h0, hvals_ad]
      apply List.flatMap_congr
      intro l hl
      obtain ⟨hl0, _, hl16⟩ := hllst l hl
      simp [lstObjects, hl0, hl16]
    rw [htail, h16, h24, h32]
    simp [lstObjects, hk16_0, hk16_16, hk24_0, hk24_16, hk32_0, hk32_16]
  · intro ad had
    rw [hrecs] at had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    refine ⟨h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]
      obtain ⟨_, hk8, hk16⟩ := hklst k hk
      unfold LstOK
      rw [hk8, hk16]
      exact had_T.2.2.1 k hk
    · intro l hl
      rw [h0, hvals_ad] at hl
      obtain ⟨_, hl8, hl16⟩ := hllst l hl
      unfold LstOK
      rw [hl8, hl16]
      exact had_T.2.2.2 l hl

theorem worldRoleSlots_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hgs : WorldGlobalsSame s post)
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i)
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    worldRoleSlots post = worldRoleSlots s := by
  have hws_g : globN post "ws" = globN s "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" := hgs.2.1 "bal_idx_accts" (by simp [globalTableRoots])
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" := hgs.2.1 "bal_idx_stor" (by simp [globalTableRoots])
  have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] = recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
    unfold recRoles
    by_cases h : globN s "ws" = 0
    · simp [hws_g, h]
    · have hw16 := rec_word_eq_of_unhit hA hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hA hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
      simp only [hws_g] at hw16 hw32 ⊢
      simp [h, hw16, hw32]
  have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
    unfold recRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · simp only [hbs_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hA hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
      simp only [hbs_g] at hw
      simp [hw]
  have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
    unfold recRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · simp only [hts_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) hk.1 hk.2
      simp only [hts_g] at hw
      simp [hw]
  have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    unfold nestRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · have hw32 := rec_word_eq_of_unhit hA hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
      simp only [hbs_g] at hw32 ⊢
      simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "bs" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "bs" + 32) ∈ S := by
          rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
  have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
    unfold nestRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw32 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      simp only [hts_g] at hw32 ⊢
      simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "ts" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "ts" + 32) ∈ S := by
          rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
  have hrecs_bal := balRecords_eq_of_unhit hT hba_g (fun hnz => by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hu_tab _ hm)
  have hbal_part := (balObjects_eq_of_unhit hA hT hF hba_g hu_tab hu_bal hm0).2
  unfold worldRoleSlots
  rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
  congr 1; congr 1
  apply List.flatMap_congr
  intro ad had
  rw [← hrecs_bal] at had
  obtain ⟨h0, h8, _⟩ := hbal_part ad had
  rw [h0, h8]

theorem journalRoleSlots_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    (hA : ArenaOK s) (hag : AllocatorGrows s post)
    {S S' : List Nat} (hsub : ∀ x ∈ S, x ∈ S')
    (hJ : JournalTyped s S) (hF : FixedTyped s)
    (hgs : WorldGlobalsSame s post)
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap")) :
    journalRoleSlots post = journalRoleSlots s ∧ JournalTyped post S' := by
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hj_g := hgs.2.2.1
  have hjc_g := hgs.2.2.2.1
  have hjn_g := hgs.2.2.2.2
  have hrole_eq : ∀ t, journalRole post t = journalRole s t := fun t => by
    unfold journalRole
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw16 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 16) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      have hw48 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 48) (by omega) (by omega)
      have hw64 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 64) (by omega) (by omega)
      simp only [hts_g] at hw16 hw32 hw48 hw64 ⊢
      rw [hw16, hw32, hw48, hw64]
  have hj_cells : ∀ i, i < globN s "journal_n" →
      memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) ∧
      memW post (globN s "journal" + 32 * i + 16) = memW s (globN s "journal" + 32 * i + 16) ∧
      memW post (globN s "journal" + 32 * i + 24) = memW s (globN s "journal" + 32 * i + 24) := by
    intro i hi
    have hcnz : globN s "journal_cap" ≠ 0 := by have := hJ.1; omega
    rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
    · exact absurd h0 hcnz
    · have hhi := (ivl_allocated_bound hA hal).2
      have hj8 : (globN s "journal") % 8 = 0 := hwords.1
      have huj := hu_jr hcnz
      have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ.1
      refine ⟨?_, ?_, ?_⟩
      · exact memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩
  constructor
  · unfold journalRoleSlots
    rw [hjn_g, hj_g]
    apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    obtain ⟨hc0, hc16, hc24⟩ := hj_cells i hi
    simp only [hc0, hc16, hc24, hrole_eq]
  · unfold JournalTyped
    rw [hjn_g, hjc_g, hj_g]
    refine ⟨hJ.1, hJ.2.1, ?_, ?_⟩
    · rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hgS hgP hwords⟩
    · intro i hi
      rw [(hj_cells i hi).1]
      exact hsub _ (hJ.2.2.2 i hi)

theorem nodeHeap_congr_bytes {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    (hag : AllocatorGrows s post)
    {Nd : List Nat} (hN : NodeHeap s Nd)
    (hu_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n))
    (hu_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k)) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hn_props : ∀ n ∈ Nd,
      memW post n = memW s n ∧
      nodeIvl post n = nodeIvl s n ∧
      (∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k)) ∧
      nodePath post n = nodePath s n ∧
      ((memW s n = 1 ∨ memW s n = 2) → KeyIn post Nd (memW post (n + 32)) (memW post (n + 40))) := by
    intro n hn
    obtain ⟨hk3, hal_n, hin_n, hw_n, _, _, hkey_n, _⟩ := hN.1 n hn
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    have hn8 : n % 8 = 0 := hw_n.1
    have hu_n : IvlUnhit s post (n, nodeSize (memW s n)) := hu_rec n hn
    have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by
      unfold nodeSize; split_ifs <;> omega
    have hw_k : ∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k) := by
      intro k hk
      have hsz8 : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> omega
      exact memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by omega, by omega⟩
    have hw0 : memW post n = memW s n := by simpa using hw_k 0 (by omega)
    have hivl_eq : nodeIvl post n = nodeIvl s n := by simp [nodeIvl, hw0]
    have hpath_eq : nodePath post n = nodePath s n := by
      by_cases h12 : memW s n = 1 ∨ memW s n = 2
      · have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
          unfold nodeSize; rcases h12 with h1 | h2
          · simp [h1]
          · simp [h2]
        have hw32 : memW post (n + 32) = memW s (n + 32) := hw_k 4 (by omega)
        have hw40 : memW post (n + 40) = memW s (n + 40) := hw_k 5 (by omega)
        unfold nodePath
        rw [hw0, hw32, hw40]
      · unfold nodePath; rw [hw0]; simp [h12]
    exact ⟨hw0, hivl_eq, hw_k, hpath_eq, fun h12 => by
      have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize; rcases h12 with h1 | h2
        · simp [h1]
        · simp [h2]
      have hw32 : memW post (n + 32) = memW s (n + 32) := hw_k 4 (by omega)
      have hw40 : memW post (n + 40) = memW s (n + 40) := hw_k 5 (by omega)
      rw [hw32, hw40]
      by_cases hlen0 : memW s (n + 40) = 0
      · exact Or.inl hlen0
      · rcases hkey_n h12 with h0 | ⟨hnib, hal_p, hin_p, hdisj_p⟩
        · exact Or.inl h0
        · right
          refine ⟨fun k hk => ?_, hag.allocated hal_p, hin_p, ?_⟩
          · rw [hu_byte n hn h12 hlen0 k hk]
            exact hnib k hk
          · intro m hm
            have hm_ivl : nodeIvl post m = nodeIvl s m := by
              have hhm_hi : m + nodeSize (memW s m) ≤ 2 ^ 64 := by
                have := (hN.1 m hm).2.2.1.2; dsimp [nodeIvl] at this; omega
              have hm8 : m % 8 = 0 := (hN.1 m hm).2.2.2.1.1
              have hu_m : IvlUnhit s post (m, nodeSize (memW s m)) := hu_rec m hm
              have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
              have hwm : memW post m = memW s m :=
                memW_eq_of_ivlUnhit hu_m hm8 hhm_hi ⟨by omega, by omega⟩
              simp [nodeIvl, hwm]
            rw [hm_ivl]
            exact hdisj_p m hm⟩
  constructor
  · refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
    · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, _, hn16, hn56, hn168⟩ := hN.1 n hn
      obtain ⟨hw0, hivl_eq, hw_k, _, hkey_post⟩ := hn_props n hn
      rw [hw0, hivl_eq]
      refine ⟨hk3, hag.allocated hal_n, hin_n, wordsOK_transfer hgS hgP hw_n, ?_, ?_, hkey_post, ?_, ?_, ?_⟩
      · intro h2
        have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
        have hw48 := hw_k 6 (by omega)
        simpa only [Nat.mul_succ, Nat.mul_zero] using (by rw [hw48]; exact hext h2 : RootIn Nd (memW post (n + 48)))
      · intro h3 i hi
        have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
        have hw_ch := hw_k (4 + i) (by omega)
        have hadd : n + 8 * (4 + i) = n + 32 + 8 * i := by omega
        rw [← hadd, hw_ch, hadd]
        exact hbr h3 i hi
      · have hsz : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
        have hw16 := hw_k 2 (by omega)
        simpa using (by rw [hw16]; exact hn16 : memW post (n + 16) < 2 ^ 40)
      · intro h1
        have hsz : nodeSize (memW s n) = 64 := by unfold nodeSize; simp [h1]
        have hw56 := hw_k 7 (by omega)
        simpa using (by rw [hw56]; exact hn56 h1 : memW post (n + 56) < 2 ^ 40)
      · intro h3
        have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
        have hw168 := hw_k 21 (by omega)
        simpa using (by rw [hw168]; exact hn168 h3 : memW post (n + 168) < 2 ^ 40)
    · rw [(hn_props n hn).2.1, (hn_props m hm).2.1]
      exact hN.2 n hn m hm hne
  · unfold nodeExtents
    apply List.flatMap_congr
    intro n hn
    rw [(hn_props n hn).2.1, (hn_props n hn).2.2.2.1]

theorem fixedObjects_eq_of_parts {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgs : WorldGlobalsSame s post)
    (hbo_obj : blockOutObjects post = blockOutObjects s)
    (hbal_obj : balObjects post = balObjects s) :
    fixedObjects post = fixedObjects s := by
  unfold fixedObjects
  rw [hbo_obj, hbal_obj, hgs.2.2.1, hgs.2.2.2.1]
  congr 3
  apply List.map_congr_left
  intro gn hgn
  rw [hgs.1 gn hgn]

theorem fixedTyped_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) (hag : AllocatorGrows s post)
    (hF : FixedTyped s) (hfix_eq : fixedObjects post = fixedObjects s) :
    FixedTyped post := by
  unfold FixedTyped
  rw [hfix_eq]
  refine ⟨fun i hi => ?_, hF.2⟩
  rcases hF.1 i hi with h0 | ⟨hal, hwords⟩
  · exact Or.inl h0
  · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hgS hgP hwords⟩

theorem worldTypedWith_congr_parts {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hag : AllocatorGrows s post) (hgs : WorldGlobalsSame s post)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88))
    (hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap"))
    (hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i)
    (hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n))
    (hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k))
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    WorldTypedWith post S Nd ∧
    worldOwned post S Nd = worldOwned s S Nd ∧
    nodeExtents post Nd = nodeExtents s Nd ∧
    fixedObjects post = fixedObjects s ∧
    (∀ t ∈ S, htabFootprint post t = htabFootprint s t) := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hws_g : globN post "ws" = globN s "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using rec_word_eq_of_unhit hAs.2 hF "bo" 88 (by simp [typedRecords]) hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_part := blockOutObjects_eq_of_bo_unhit hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun h h40 => hu_bo_lst (memW s (globN s "bo" + 40), 24) (by simp [blockOutObjects, h, h40]) rfl)
    (fun h h72 => hu_bo_lst (memW s (globN s "bo" + 72), 24) (by simp [blockOutObjects, h, h72]) rfl)
  have hbal_part := balObjects_eq_of_unhit hAs.2 hT hF hba_g hu_tab hu_bal hm0
  have hfix_eq := fixedObjects_eq_of_parts hgs hbo_part.1 hbal_part.1
  have hF_post := fixedTyped_transfer hAs.1 hAp.1 hag hF hfix_eq
  have hjr_part := journalRoleSlots_eq_of_unhit hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hgs hu_ts hu_jr
  have hwrs_eq := worldRoleSlots_eq_of_unhit hAs.2 hT hF hgs hu_tab hu_ws hu_bs hu_ts hu_bal hm0
  have hnd_part := nodeHeap_congr_bytes hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
    have h264_he : heapEnd ≤ 2 ^ 64 := by decide
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab t ht _ ht_fp)
  have hflat_fp : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) := by
    apply List.flatMap_congr
    intro t ht; exact (htab_fp_hdr t ht).2
  have howned_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    rw [hflat_fp, hfix_eq, hnd_part.2]
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩ := hT
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2, hfix_eq]
      exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, ((hTt t ht).2 i hi).2⟩⟩
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp t ht u hu_mem hne
    · intro k hk hnz
      rw [hws_g] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) htk.1 htk.2]
      exact htsR k hk hnz
    · intro g hg
      rw [hgs.2.1 g hg]; exact hgR g hg
    · intro hnz hm
      rw [hbs_g] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (hbsN hnz hm)
    · intro hnz hm
      rw [hts_g] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (htsN hnz hm)
    · intro ad had
      obtain ⟨h0, h8, _, hkl, hll⟩ := hbal_part.2 ad had
      have hrecs := balRecords_eq_of_unhit ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩
        hba_g (fun hnz => by
          rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0' | hm
          · exact absurd h0' hnz
          · exact hu_tab _ hm)
      rw [hrecs] at had
      have had_old := hbalT ad had
      refine ⟨by rw [h0]; exact had_old.1, by rw [h8]; exact had_old.2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_part.1]
      refine ⟨fun a ha => ?_, hroles.2.1, hroles.2.2⟩
      obtain ⟨haS, hak⟩ := hroles.1 a ha
      rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
      exact ⟨haS, hak⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hnd_part.1, ?_, ?_⟩
    · intro o ho
      rw [hnd_part.2] at ho
      rw [hfix_eq]
      refine ⟨fun t ht i hi => ?_, (hTr.2.1 o ho).2⟩
      rw [(htab_fp_hdr t ht).2] at hi
      exact (hTr.2.1 o ho).1 t ht i hi
    · intro hnz
      rw [hws_g] at hnz
      have hw24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hwf32 := (hT.2.1 _ hm).1
      have hu32 := hu_tab _ hm
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := htabValues_eq_of_unhit hwf32 hu32
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 hm i hi
  exact ⟨⟨hT_post, hjr_part.2, hF_post, hTr_post⟩, howned_eq, hnd_part.2, hfix_eq,
    fun t ht => (htab_fp_hdr t ht).2⟩

theorem worldTypedIvl_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) {i : Ivl} (hi : i ∈ worldTypedIvls s S Nd) :
    i.2 = 0 ∨ Allocated s i := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  unfold worldTypedIvls at hi
  rcases List.mem_append.1 hi with h12345 | hnd
  · rcases List.mem_append.1 h12345 with h1234 | hbal
    · rcases List.mem_append.1 h1234 with h123 | hbo
      · rcases List.mem_append.1 h123 with h12 | hjr
        · rcases List.mem_append.1 h12 with htab | hrec
          · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 htab
            exact Or.inr (((hT.2.1 t ht).2 i hfp).1)
          · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hrec
            have hmf := typedRecord_mem_fixedObjects s hr
            rcases hF.1 _ hmf with h0 | ⟨hal, _⟩
            · exact Or.inl h0
            · exact Or.inr hal
        · simp only [List.mem_singleton] at hjr; subst hjr
          by_cases hcnz : globN s "journal_cap" = 0
          · exact Or.inl (by simp [hcnz])
          · rcases hJ.2.2.1 with h0 | ⟨hal, _⟩
            · exact absurd h0 hcnz
            · simp only [hcnz, ↓reduceIte]; exact Or.inr hal
      · have hmf : i ∈ fixedObjects s := by
          unfold fixedObjects
          exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hbo)))
        rcases hF.1 i hmf with h0 | ⟨hal, _⟩
        · exact Or.inl h0
        · exact Or.inr hal
    · have hmf : i ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append.2 (Or.inr hbal)
      rcases hF.1 i hmf with h0 | ⟨hal, _⟩
      · exact Or.inl h0
      · exact Or.inr hal
  · unfold nodeExtents at hnd
    obtain ⟨n, hn, hni⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
    rcases hni with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath
      split_ifs with hp
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _, _⟩
        · exact absurd h0 hp.2
        · exact Or.inr hal
      · exact Or.inl rfl

theorem worldOwned_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) {i : Ivl} (hi : i ∈ worldOwned s S Nd) :
    i.2 = 0 ∨ Allocated s i := by
  obtain ⟨hT, _, hF, hTr⟩ := hW
  unfold worldOwned at hi
  rcases List.mem_append.1 hi with h12 | hnd
  · rcases List.mem_append.1 h12 with htab | hfix
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 htab
      exact Or.inr (((hT.2.1 t ht).2 i hfp).1)
    · rcases hF.1 i hfix with h0 | ⟨hal, _⟩
      · exact Or.inl h0
      · exact Or.inr hal
  · unfold nodeExtents at hnd
    obtain ⟨n, hn, hni⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
    rcases hni with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath
      split_ifs with hp
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _, _⟩
        · exact absurd h0 hp.2
        · exact Or.inr hal
      · exact Or.inl rfl

theorem ownedGrows_refl {F : Type} (s post : PanSemStateFiniteExact 64 F) (os : List Ivl) :
    OwnedGrows s post os os :=
  fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩)

theorem worldTyped_iff_with {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) :
    WorldTyped s S ↔ ∃ Nd, WorldTypedWith s S Nd := by
  simp only [WorldTyped, TriesTyped, WorldTypedWith]
  constructor
  · rintro ⟨h1, h2, h3, Nd, h4⟩
    exact ⟨Nd, h1, h2, h3, h4⟩
  · rintro ⟨Nd, h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, Nd, h4⟩

theorem recordsKept_of_free_writes {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    (hWOK : WorldOK s)
    (hfr : FrameOutside s post (R s ++ [freeGap s]) (heapFree s)) :
    RecordsKept R
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] s post := by
  obtain ⟨hAs, S0, hWT0⟩ := hWOK
  have hF := hWT0.2.2.1
  intro rec hrec hgnz k hk hnoR
  have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · refine ⟨40, by simp [typedRecords], ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    · refine ⟨80, by simp [typedRecords], ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · refine ⟨72, by simp [typedRecords], ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · refine ⟨88, by simp [typedRecords], ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨sz, htr, hk8, hksz⟩ := hrec_sz
  have hmf := typedRecord_mem_fixedObjects s htr
  simp only [hgnz, ↓reduceIte] at hmf
  rcases hF.1 _ hmf with h0 | ⟨hal, hwords⟩
  · omega
  · have hhi := (ivl_allocated_bound hAs.2 hal).2
    have hg8 : (globN s rec.1) % 8 = 0 := hwords.1
    have ha_lt : globN s rec.1 + k < 2 ^ 64 := by dsimp at hhi; omega
    have hdj_fg := disj_allocated_freeGap hAs.2 hal
    have hdj_hf := disj_allocated_heapFree hAs.2 hal
    have hfg1 : (freeGap s).1 % 8 = 0 := by
      unfold freeGap; dsimp only
      rcases hAs.2 with ⟨_, _, _, _, _, _, hfm8, _⟩
      exact hfm8
    have hhf1 : (heapFree s).1 % 8 = 0 := by
      unfold heapFree; dsimp only
      rcases hAs.2 with ⟨_, _, _, _, _, hhp8, _, _⟩
      exact hhp8
    have hmem := hfr (BitVec.ofNat 64 (globN s rec.1 + k))
      (fun j hj => by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
        rcases List.mem_append.1 hj with hjR | hjfg
        · exact hnoR j hjR
        · simp only [List.mem_singleton] at hjfg; subst hjfg
          exact not_cellHits_of_disj (i := (globN s rec.1, sz)) (by omega) hfg1 ⟨by omega, by omega⟩ hdj_fg)
      (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
        exact not_cellHits_of_disj (i := (globN s rec.1, sz)) (by omega) hhf1 ⟨by omega, by omega⟩ hdj_hf)
    unfold memW
    rw [hmem]

theorem mem_eq_of_bytes_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {a : BitVec 64}
    (ha_dom : ordinaryDomain a) (hbe : post.be = s.be)
    (hb : ∀ k : Nat, k < 8 → memB post (a.toNat + k) = memB s (a.toNat + k)) :
    post.memory a = s.memory a := by
  have ha_ord : a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
    rwa [ordinaryDomain_iff] at ha_dom
  have hhe_lt : heapEnd ≤ 2 ^ 64 := by decide
  have hhe_8 : heapEnd % 8 = 0 := by decide
  have ha_hi : a.toNat + 8 ≤ 2 ^ 64 := by omega
  rcases hp_m : post.memory a with ⟨wp⟩
  rcases hs_m : s.memory a with ⟨ws⟩
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hbyte_val : ∀ k : Nat, k < 8 →
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) wp s.be).toNat =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) ws s.be).toNat := by
    intro k hk
    have hal_eq : panByteAlignHOL (BitVec.ofNat 64 (a.toNat + k)) = a := by
      apply BitVec.eq_of_toNat_eq
      rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hbk := hb k hk
    unfold memB at hbk
    rw [hal_eq, hp_m, hs_m, hbe] at hbk
    exact hbk
  have hshift : ∀ (w : BitVec 64) (idx : Nat), idx < 8 →
      w.toNat / 256 ^ idx % 256 =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))) w s.be).toNat := by
    intro w idx hidx
    unfold panGetByteHOL
    change w.toNat / 256 ^ idx % 256 =
      (UInt8.ofNat (w.toNat / 256 ^ (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
        else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) % 256)).toNat
    have hexp : (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
        else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) = idx := by
      have hmod_lt : (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat =
          a.toNat + (if s.be then 7 - idx else idx) :=
        Nat.mod_eq_of_lt (by cases s.be <;> simp <;> omega)
      rw [hmod_lt]
      cases s.be <;> simp <;> omega
    rw [hexp, UInt8.toNat_ofNat']
    have h256 : (2 ^ 8 : Nat) = 256 := by decide
    rw [h256, Nat.mod_mod]
  have hpow_eq : ∀ idx : Nat, idx < 8 → wp.toNat / 256 ^ idx % 256 = ws.toNat / 256 ^ idx % 256 := by
    intro idx hidx
    rw [hshift wp idx hidx, hshift ws idx hidx]
    exact hbyte_val (if s.be then 7 - idx else idx) (by cases s.be <;> simp <;> omega)
  have hdecomp : ∀ n : Nat, n < 2 ^ 64 →
      n = (n / 256 ^ 0 % 256) +
          (n / 256 ^ 1 % 256) * 256 ^ 1 +
          (n / 256 ^ 2 % 256) * 256 ^ 2 +
          (n / 256 ^ 3 % 256) * 256 ^ 3 +
          (n / 256 ^ 4 % 256) * 256 ^ 4 +
          (n / 256 ^ 5 % 256) * 256 ^ 5 +
          (n / 256 ^ 6 % 256) * 256 ^ 6 +
          (n / 256 ^ 7 % 256) * 256 ^ 7 := by
    intro n hn; omega
  rw [hdecomp wp.toNat wp.isLt, hdecomp ws.toNat ws.isLt]
  rw [hpow_eq 0 (by omega), hpow_eq 1 (by omega), hpow_eq 2 (by omega), hpow_eq 3 (by omega),
      hpow_eq 4 (by omega), hpow_eq 5 (by omega), hpow_eq 6 (by omega), hpow_eq 7 (by omega)]

/-- Master W1 lemma for pure output-region writers (`R s`, `gw = []`, `heap_ptr` and `scratch_ptr`
unchanged, memory cells written only inside `R s` and `ordinaryDomain`, and bytes `memB` outside
`R s` unchanged), such as `memcpy` and `memzero`. -/
theorem worldStep_of_region_writes {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    (hWOK : WorldOK s)
    (hmeta : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals)
    (hfr : FrameOutside s post (R s) (0, 0))
    (hbyte : ∀ a : Nat, a < 2 ^ 64 → (∀ j ∈ R s, ¬ InIvl a j) → memB post a = memB s a)
    (hdom_wr : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a) :
    WorldStep R []
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra s r post := by
  have hAs := hWOK.1
  have hgP : GuestInv post := guestInv_congr hmeta.1 hmeta.2.1 hmeta.2.2.1 hmeta.2.2.2.1 hAs.1
  have hAp : ArenaReady post := by
    refine ⟨hgP, ?_⟩
    unfold ArenaOK; simp only [globN_congr hmeta.2.2.2.2.2]; exact hAs.2
  have hag : AllocatorGrows s post := by
    unfold AllocatorGrows; simp only [globN_congr hmeta.2.2.2.2.2]; exact ⟨le_rfl, le_rfl⟩
  have hgw : GlobalsKept [] s post := fun _ _ => by rw [hmeta.2.2.2.2.2]
  have hgs := worldGlobalsSame_of_kept hgw (fun _ h => by simp at h)
  have hm0 := mem0_8_16_eq_of_domain_writes hdom_wr hAs.1
  have hfr_ext : FrameOutside s post (R s ++ [freeGap s]) (heapFree s) := by
    intro a hk _
    exact hfr a (fun j hj => hk j (List.mem_append.2 (Or.inl hj)))
      (fun hc => by unfold CellHits at hc; omega)
  have hrk := recordsKept_of_free_writes hWOK hfr_ext
  refine ⟨hAp, hag.1, hgw, hrk, fun S Nd hWT hdisjR => ?_⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hu_al : ∀ i : Ivl, i ∈ worldTypedIvls s S Nd → i.1 % 8 = 0 → i.2 % 8 = 0 → IvlUnhit s post i := by
    intro i hi _ _ a ha8 hin1 hin2
    by_cases heq : post.memory a = s.memory a
    · exact heq
    · have hadom : ordinaryDomain a := by
        have := hdom_wr a heq
        rwa [hAs.1.memaddrs] at this
      have ha_ord : a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
        rwa [ordinaryDomain_iff] at hadom
      have hhe_lt : heapEnd ≤ 2 ^ 64 := by decide
      have hhe_8 : heapEnd % 8 = 0 := by decide
      apply mem_eq_of_bytes_eq hadom hmeta.2.2.2.2.1
      intro k hk
      apply hbyte (a.toNat + k) (by omega)
      intro j hj hinv
      have hdj := hdisjR j hj i hi
      unfold InIvl at hinv
      rcases hdj with h0 | h0 | hd | hd <;> omega
  have hfix_al : ∀ i ∈ fixedObjects s, i.2 = 0 ∨ (i.1 % 8 = 0 ∧ i.2 % 8 = 0) := by
    intro i hi
    rcases hF.1 i hi with h0 | ⟨_, hw⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hw.1, hw.2.1⟩
  have hu_fix_wti : ∀ i ∈ worldTypedIvls s S Nd, i ∈ fixedObjects s → i.2 ≠ 0 → IvlUnhit s post i := by
    intro i hwti hfi hpos
    rcases hfix_al i hfi with h0 | ⟨ha1, ha2⟩
    · exact absurd h0 hpos
    · exact hu_al i hwti ha1 ha2
  obtain ⟨hWT_post, howned_eq, _, _, _⟩ := worldTypedWith_congr_parts hAs hAp hag hgs ⟨hT, hJ, hF, hTr⟩
    (fun t ht i hi => by
      have hw := ((hT.2.1 t ht).1.1 i hi).2
      refine hu_al i ?_ hw.1 hw.2.1
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_flatMap.2 ⟨t, ht, hi⟩)
    (fun hnz => hu_fix_wti _
      (by unfold worldTypedIvls
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords]))
      (by simp))
    (fun hnz => hu_fix_wti _
      (by unfold worldTypedIvls
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords]))
      (by simp))
    (fun hnz => hu_fix_wti _
      (by unfold worldTypedIvls
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords]))
      (by simp))
    (fun hnz => hu_fix_wti _
      (by unfold worldTypedIvls
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords]))
      (by simp))
    (fun hcnz => hu_fix_wti _
      (by unfold worldTypedIvls
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; simp [hcnz])
      (by unfold fixedObjects
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hcnz])
      (by dsimp only; omega))
    (fun i hi h24 => hu_fix_wti i
      (by unfold worldTypedIvls
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects
          apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by omega))
    (fun i hi hpos => hu_fix_wti i
      (by unfold worldTypedIvls
          apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
      hpos)
    (fun n hn => by
      have hw := (hTr.1.1 n hn).2.2.2.1
      refine hu_al _ ?_ hw.1 hw.2.1
      unfold worldTypedIvls
      refine List.mem_append.2 (Or.inr ?_)
      unfold nodeExtents
      exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩)
    (fun n hn h12 hlen0 k hk => by
      have h264 : heapLimit ≤ 2 ^ 64 := by decide
      rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, _, hin_p, _⟩
      · exact absurd h0 hlen0
      · have hp_wti : (memW s (n + 32), memW s (n + 40)) ∈ worldTypedIvls s S Nd := by
          unfold worldTypedIvls
          refine List.mem_append.2 (Or.inr ?_)
          unfold nodeExtents
          exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
        apply hbyte _ (by have := hin_p.2; omega)
        intro j hj hinv
        have hdj := hdisjR j hj _ hp_wti
        unfold InIvl at hinv
        rcases hdj with h0 | h0 | hd | hd
        · omega
        · omega
        · omega
        · omega)
    hm0
  refine ⟨S, Nd, fun _ ht => ht, hWT_post, ?_, ?_, trivial⟩
  · rw [howned_eq]; exact ownedGrows_refl s post _
  · intro a hkeep _
    exact hfr a
      (fun j hj => hkeep j (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))))
      (fun hc => by unfold CellHits at hc; omega)

end InitECandidate.Solver.Wave8Contracts.M08
