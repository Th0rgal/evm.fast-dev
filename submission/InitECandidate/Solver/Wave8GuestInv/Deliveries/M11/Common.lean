import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.HeapPotential
import InitECandidate.Solver.GuestTrapOutcomes
import Guest.SoftwareAst

/-! Shared definitions (verbatim from frozen rev9 `Contracts.lean`), domain/alignment lemmas,
and W1 typed-cell congruence lemmas for contract micro-shard `m11` (`wave8/contracts-m11`).
Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.MemoryViews` plus
existing Solver support and `Guest.SoftwareAst`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.M11

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Verbatim contract definitions from `Contracts.lean` (rev9 `8a79d9f28`) -/

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

def OnReturn (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → Q s post

def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

def ArgNonNull (x : String) (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r _ => Resumes r → locN s x ≠ 0) fname

def ReadOnlyFn (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r post => Resumes r → post = { s with locals := post.locals, clock := post.clock })
    fname

def FreshBlock {F : Type} (s post : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  p % 8 = 0 ∧ Inside (p, (n + 7) / 8 * 8) (globN s "heap_ptr") (globN post "heap_ptr") ∧
    WordsOK post (p, (n + 7) / 8 * 8)

def RetWord (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
    Prop) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ Q s post w.toNat

def Returns (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat → Prop)
    (fname : MlS) : Prop :=
  FunSpec P (RetWord (fun s post p => ArenaReady post ∧ AllocatorGrows s post ∧ Q s post p)) fname

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

def RetAvoids (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
    List Ivl) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    IvlsDisj (B s post w.toNat) (worldOwned post S' Nd')

def RetAvoidsIf (C : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
      List Ivl) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => C s → RetAvoids B s r post S' Nd'

def RetListSlot : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post _ _ => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    w.toNat % 8 = 0 ∧ Inside (w.toNat, 8) (memW post (locN s "l"))
      (memW post (locN s "l") + 8 * memW post (locN s "l" + 16))

def BoListArg : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ globN s "bo" ≠ 0 ∧
    (locN s "l" = memW s (globN s "bo" + 40) ∨ locN s "l" = memW s (globN s "bo" + 72)) ∧
    locN s "esz" = 8

def stdKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]),
   ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
   ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
   ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]

/-! ## 2. Ordinary domain and basic memory/global helpers -/

theorem addresses_iff (b : BitVec 64) (n : Nat) (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔ ∃ i, i < n ∧ x = b + BitVec.ofNat 64 (8 * i) := by
  induction n generalizing b with
  | zero => simp [Flapjack.Compiler.Backend.StackRemove.addresses]
  | succ n ih =>
    simp only [Flapjack.Compiler.Backend.StackRemove.addresses, Flapjack.Compiler.Backend.StackRemove.bytesInWord]
    rw [ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨i + 1, by omega, ?_⟩
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega
    · rintro ⟨i, hi, rfl⟩
      rcases i with _ | i
      · left; simp
      · right
        refine ⟨i, by omega, ?_⟩
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega

theorem ordinaryDomain_eq : ordinaryDomain =
    Flapjack.Compiler.Backend.StackRemove.addresses (BitVec.ofNat 64 2701131776) 3888119741 := by
  have h1 : (BitVec.ofNat 64 sourceBase) = BitVec.ofNat 64 2701131776 := rfl
  have h2 : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 := by decide
  unfold ordinaryDomain
  rw [h1, h2]

theorem addresses_iff_nat (b : BitVec 64) (n : Nat) (hb : b.toNat + 8 * n ≤ 2 ^ 64)
    (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      b.toNat ≤ x.toNat ∧ x.toNat < b.toNat + 8 * n ∧ (x.toNat - b.toNat) % 8 = 0 := by
  rw [addresses_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : (b + BitVec.ofNat 64 (8 * i)).toNat = b.toNat + 8 * i := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [this]
    omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(x.toNat - b.toNat) / 8, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ 2701131776 ≤ x.toNat ∧ x.toNat < 2701131776 + 8 * 3888119741 ∧
      x.toNat % 8 = 0 := by
  have hb : (BitVec.ofNat 64 2701131776).toNat = 2701131776 := rfl
  rw [ordinaryDomain_eq, addresses_iff_nat _ _ (by rw [hb]; norm_num), hb]
  omega

theorem sourceBase_val : sourceBase = 2701131776 := rfl
theorem heapLimit_val : heapLimit = 2952790016 := rfl
theorem scratchStart_val : scratchStart = 2952790016 := rfl
theorem scratchEnd_val : scratchEnd = 2965299200 := rfl
theorem heapEnd_val : heapEnd = 33806089704 := by decide

theorem wordAt_of_dom {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hma : s.memaddrs = ordinaryDomain) (a : Nat) (h1 : 2701131776 ≤ a)
    (h2 : a < 33806089704) (h3 : a % 8 = 0) : WordAt s a := by
  have ha : (BitVec.ofNat 64 a).toNat = a := by
    simp only [BitVec.toNat_ofNat]; omega
  rcases hw : s.memory (BitVec.ofNat 64 a) with ⟨w⟩
  refine ⟨w, ?_, hw⟩
  rw [hma, ordinaryDomain_iff, ha]
  exact ⟨h1, by omega, h3⟩

theorem wordsOK_of_inside_heap {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hma : s.memaddrs = ordinaryDomain) (p l : Nat)
    (hp8 : p % 8 = 0) (hl8 : l % 8 = 0)
    (hlo : sourceBase ≤ p) (hhi : p + l ≤ heapEnd) : WordsOK s (p, l) := by
  rw [sourceBase_val] at hlo
  rw [heapEnd_val] at hhi
  refine ⟨hp8, hl8, fun k hk => wordAt_of_dom s hma (p + 8 * k) (by omega) (by omega) (by omega)⟩

theorem global_word_of_pos {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String)
    (h : 0 < globN s n) :
    ∃ w : BitVec 64, s.globals.lookup (ofString n) = some (.val (.word w)) ∧ w.toNat = globN s n := by
  unfold globN at h ⊢
  split at h
  · rename_i w hw; exact ⟨w, hw, rfl⟩
  · omega

theorem globN_eq_of_lookup_eq {F : Type} {s t : PanSemStateFiniteExact 64 F} {n : String}
    (h : s.globals.lookup (ofString n) = t.globals.lookup (ofString n)) :
    globN s n = globN t n := by
  simp only [globN, h]

theorem Disj.symm {i j : Ivl} (h : Disj i j) : Disj j i := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem cellHits_of_inIvl {a : Nat} {i : Ivl} (h : InIvl a i) : CellHits a i :=
  ⟨by have := h.1; omega, h.2⟩

theorem cellHits_word_of_inIvl {a : Nat} {i : Ivl} (h1 : i.1 ≤ a) (h2 : a + 8 ≤ i.1 + i.2) :
    CellHits a i :=
  ⟨by omega, by omega⟩

theorem not_cellHits_of_disj_aligned {a : Nat} {i j : Ivl}
    (ha8 : a % 8 = 0) (hj1 : j.1 % 8 = 0)
    (ha1 : i.1 ≤ a) (ha2 : a + 8 ≤ i.1 + i.2) (hd : Disj i j) :
    ¬ CellHits a j := by
  intro ⟨hc1, hc2⟩
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  dsimp only [CellHits, Disj] at ha8 hj1 ha1 ha2 hc1 hc2 hd
  rcases hd with h0 | h0 | h | h
  · exact Nat.not_lt.mpr (h0 ▸ ha2 : a + 8 ≤ i1 + 0) (by omega)
  · have hlt : a < j1 := by simpa [h0] using hc2
    omega
  · omega
  · omega

theorem allocated_mono {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    {i : Ivl} (hi : Allocated s i) : Allocated post i :=
  AllocatorGrows.allocated ⟨hh, hsc⟩ hi

def SameTypedCells {F : Type} (s post : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  post.be = s.be ∧ post.memaddrs = s.memaddrs ∧ s.memaddrs = ordinaryDomain ∧
  (∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a) ∧
  (∀ a : Nat, a < 2 ^ 64 → a % 8 = 0 → (∃ i ∈ worldTypedIvls s S Nd, i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) →
    post.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a)) ∧
  (∀ b : Nat, b < 2 ^ 64 → (∃ i ∈ worldTypedIvls s S Nd, i.1 ≤ b ∧ b < i.1 + i.2) →
    memB post b = memB s b)

theorem memW_eq_of_lt_sourceBase {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (h : SameTypedCells s post S Nd) {a : Nat} (ha : a < sourceBase) :
    memW post a = memW s a := by
  unfold memW
  rw [sourceBase_val] at ha
  have hbit : (BitVec.ofNat 64 a).toNat = a := by simp only [BitVec.toNat_ofNat]; omega
  have hnot : ¬ ordinaryDomain (BitVec.ofNat 64 a) := by
    rw [ordinaryDomain_iff, hbit]; omega
  rw [h.2.2.2.1 _ hnot]

theorem memW_eq_of_cellHits {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (h : SameTypedCells s post S Nd) {a : Nat} {i : Ivl}
    (ha : a < 2 ^ 64) (hi : i ∈ worldTypedIvls s S Nd) (hch : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  by_cases ha8 : a % 8 = 0
  · unfold memW
    rw [h.2.2.2.2.1 a ha ha8 ⟨i, hi, hch.1, hch.2⟩]
  · unfold memW
    have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
    have hnot : ¬ ordinaryDomain (BitVec.ofNat 64 a) := by
      rw [ordinaryDomain_iff, hbit]; omega
    rw [h.2.2.2.1 _ hnot]

theorem wordsOK_congr_of_ivl {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (h : SameTypedCells s post S Nd) {i : Ivl}
    (_hbound : i.1 + i.2 ≤ 2 ^ 64) (_hi : i ∈ worldTypedIvls s S Nd) :
    WordsOK post i ↔ WordsOK s i := by
  unfold WordsOK
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun k => imp_congr_right fun _ => ?_))
  unfold WordAt
  rw [h.2.1]
  constructor
  · rintro ⟨_, hdom, _⟩
    cases s.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with
    | word w => exact ⟨w, hdom, rfl⟩
  · rintro ⟨_, hdom, _⟩
    cases post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with
    | word w => exact ⟨w, hdom, rfl⟩

theorem memB_eq_of_inIvl {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (h : SameTypedCells s post S Nd) {a : Nat} {i : Ivl}
    (hbound : i.1 + i.2 ≤ 2 ^ 64) (hi : i ∈ worldTypedIvls s S Nd)
    (hin1 : i.1 ≤ a) (hin2 : a < i.1 + i.2) :
    memB post a = memB s a :=
  h.2.2.2.2.2 a (by omega) ⟨i, hi, hin1, hin2⟩

theorem nibblesOK_congr_of_ivl {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (h : SameTypedCells s post S Nd) {p len : Nat}
    (hbound : p + len ≤ 2 ^ 64) (hi : (p, len) ∈ worldTypedIvls s S Nd) :
    NibblesOK post p len ↔ NibblesOK s p len := by
  unfold NibblesOK
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  rw [memB_eq_of_inIvl h hbound hi (by omega) (by omega)]

/-! ### Sub-list membership into `worldTypedIvls` -/

theorem mem_worldTypedIvls_htab {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {t : Nat} (ht : t ∈ S) {i : Ivl} (hi : i ∈ htabFootprint s t) :
    i ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_flatMap.2 ⟨t, ht, hi⟩

theorem mem_worldTypedIvls_typedRec {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {g : String} {sz : Nat} (hr : (g, sz) ∈ typedRecords) :
    (globN s g, if globN s g = 0 then 0 else sz) ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨(g, sz), hr, rfl⟩

theorem mem_worldTypedIvls_journal {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hjc : globN s "journal_cap" ≠ 0) :
    (globN s "journal", 32 * globN s "journal_cap") ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  simp [hjc]

theorem mem_worldTypedIvls_blockOut {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {i : Ivl} (hi : i ∈ blockOutObjects s) :
    i ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact hi

theorem mem_worldTypedIvls_bal {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {i : Ivl} (hi : i ∈ balObjects s) :
    i ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append_left
  apply List.mem_append_right
  exact hi

theorem mem_worldTypedIvls_nodeExtents {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {i : Ivl} (hi : i ∈ nodeExtents s Nd) :
    i ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  exact List.mem_append_right _ hi

theorem allocated_le_2pow64 {F : Type} {s : PanSemStateFiniteExact 64 F} (hA : ArenaOK s)
    {i : Ivl} (hi : Allocated s i) : i.1 + i.2 ≤ 2 ^ 64 := by
  have hh := hA.2.1
  rw [heapLimit_val] at hh
  rcases hi with ⟨_, h2⟩ | ⟨_, h2⟩
  · omega
  · rw [scratchEnd_val] at h2; omega

theorem fixedObject_le_2pow64 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hF : FixedTyped s) {i : Ivl} (hi : i ∈ fixedObjects s) :
    i.2 = 0 ∨ i.1 + i.2 ≤ 2 ^ 64 := by
  rcases hF.1 i hi with h0 | ⟨hal, _⟩
  · exact Or.inl h0
  · exact Or.inr (allocated_le_2pow64 hA hal)

theorem typedRec_in_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    {g : String} {sz : Nat} (hr : (g, sz) ∈ typedRecords) :
    (globN s g, if globN s g = 0 then 0 else sz) ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map.2
  refine ⟨(g, sz), ?_, rfl⟩
  simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h <;> (rw [h]; decide)

theorem memW_typedRec_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hF : FixedTyped s) (hcell : SameTypedCells s post S Nd)
    {g : String} {sz k : Nat} (hr : (g, sz) ∈ typedRecords) (hg : globN s g ≠ 0) (hk : k + 8 ≤ sz) :
    memW post (globN s g + k) = memW s (globN s g + k) := by
  have hmem := mem_worldTypedIvls_typedRec (s := s) (S := S) (Nd := Nd) hr
  have hfix := typedRec_in_fixedObjects s hr
  have hsz : (if globN s g = 0 then 0 else sz) = sz := if_neg hg
  rcases hF.1 _ hfix with h0 | ⟨hal, _⟩
  · dsimp only at h0; rw [hsz] at h0; omega
  · have hb := allocated_le_2pow64 hA hal
    dsimp only at hb; rw [hsz] at hb
    exact memW_eq_of_cellHits hcell (by omega) hmem ⟨by dsimp only; omega, by dsimp only; rw [hsz]; omega⟩

/-! ### `HtabWF` and `htabValues` congruence on a table `t ∈ S` -/

theorem htab_hdr_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hcell : SameTypedCells s post S Nd) {t : Nat} (ht : t ∈ S)
    (htb : Inside (t, 88) sourceBase heapEnd) (k : Nat) (hk : k < 11) :
    hdr post t k = hdr s t k := by
  unfold hdr
  have h264 : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; norm_num
  have hhi : t + 88 ≤ 2 ^ 64 := le_trans htb.2 h264
  have hfp0 : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  exact memW_eq_of_cellHits hcell (by omega)
    (mem_worldTypedIvls_htab ht hfp0) ⟨by dsimp only; omega, by dsimp only; omega⟩

theorem htabFootprint_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hcell : SameTypedCells s post S Nd) {t : Nat} (ht : t ∈ S) (hW : HtabWF s t) :
    htabFootprint post t = htabFootprint s t := by
  have htb := (hW.1 (t, 88) (by simp [htabFootprint])).1
  have h1 := htab_hdr_eq hcell ht htb 1 (by omega)
  have h4 := htab_hdr_eq hcell ht htb 4 (by omega)
  have h5 := htab_hdr_eq hcell ht htb 5 (by omega)
  have h6 := htab_hdr_eq hcell ht htb 6 (by omega)
  have h10 := htab_hdr_eq hcell ht htb 10 (by omega)
  simp only [htabFootprint, h1, h4, h5, h6, h10]

theorem nodeF_eq_of_lt {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hcell : SameTypedCells s post S Nd) {t : Nat} (ht : t ∈ S) (hW : HtabWF s t)
    {n off : Nat} (hn : n ≤ hdr s t 10) (hoff : off + 8 ≤ 32) :
    nodeF post (hdr s t 5) n off = nodeF s (hdr s t 5) n off := by
  unfold nodeF
  have hfp2 : (hdr s t 5, (hdr s t 10 + 1) * 32) ∈ htabFootprint s t := by simp [htabFootprint]
  have hnb := (hW.1 _ hfp2).1
  have h264 : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; norm_num
  have hhi : hdr s t 5 + (hdr s t 10 + 1) * 32 ≤ 2 ^ 64 := le_trans hnb.2 h264
  exact memW_eq_of_cellHits hcell (by omega)
    (mem_worldTypedIvls_htab ht hfp2)
    ⟨by dsimp only; omega, by dsimp only; omega⟩

theorem freeChain_congr_of_htab {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hcell : SameTypedCells s post S Nd) {t : Nat} (ht : t ∈ S) (hW : HtabWF s t) :
    ∀ (Fr : List Nat) (head : Nat), (∀ f ∈ Fr, f ≤ hdr s t 10) →
      (FreeChain post (hdr s t 5) head Fr ↔ FreeChain s (hdr s t 5) head Fr)
  | [], _ => fun _ => Iff.rfl
  | f :: rest, head => fun hb => by
    simp only [FreeChain]
    rw [nodeF_eq_of_lt hcell ht hW (hb f List.mem_cons_self) (by omega)]
    exact and_congr Iff.rfl (freeChain_congr_of_htab hcell ht hW rest _
      (fun x hx => hb x (List.mem_cons_of_mem f hx)))

theorem htabCount_le_ncap {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat} (hW : HtabWF s t) :
    hdr s t 3 ≤ hdr s t 10 := by
  obtain ⟨_, _, _, _, _, _, _, hnx2, L, I, Fr, hLlen, hnd, hmem, _, _, _, _, _, _, _, _, _⟩ := hW
  have hLn : L.Nodup := ((List.nodup_append.1 hnd).1 |> List.nodup_append.1).1
  have hsub : L ⊆ List.range' 1 (hdr s t 8 - 1) := by
    intro x hx
    rw [List.mem_range']
    have := (hmem x).1 (List.mem_append_left Fr (List.mem_append_left I hx))
    exact ⟨x - 1, by omega, by omega⟩
  have hle := List.Subperm.length_le (hLn.subperm hsub)
  rw [List.length_range'] at hle
  omega

theorem htabOrder_entry_le_ncap {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (hW : HtabWF s t) {i : Nat} (hi : i < hdr s t 3) :
    memW s (hdr s t 6 + 8 * i) ≤ hdr s t 10 := by
  obtain ⟨_, _, _, _, _, _, _, hnx2, L, I, Fr, hLlen, _, hmem, _, hord, _, _, _, _, _, _, _⟩ := hW
  have hiL : i < L.length := by omega
  have heq := (hord i hiL).1
  rw [heq]
  have := (hmem L[i]).1 (List.mem_append_left Fr (List.mem_append_left I (List.getElem_mem _)))
  omega

theorem htabWF_congr {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hcell : SameTypedCells s post S Nd) {t : Nat} (ht : t ∈ S) (hW : HtabWF s t) :
    HtabWF post t := by
  have hW' := hW
  have htb := (hW.1 (t, 88) (by simp [htabFootprint])).1
  have hfp := htabFootprint_eq hcell ht hW
  have h0 := htab_hdr_eq hcell ht htb 0 (by omega)
  have h1 := htab_hdr_eq hcell ht htb 1 (by omega)
  have h3 := htab_hdr_eq hcell ht htb 3 (by omega)
  have h5 := htab_hdr_eq hcell ht htb 5 (by omega)
  have h6 := htab_hdr_eq hcell ht htb 6 (by omega)
  have h7 := htab_hdr_eq hcell ht htb 7 (by omega)
  have h8 := htab_hdr_eq hcell ht htb 8 (by omega)
  have h9 := htab_hdr_eq hcell ht htb 9 (by omega)
  have h10 := htab_hdr_eq hcell ht htb 10 (by omega)
  have hcnt_le := htabCount_le_ncap hW
  have h264 : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; norm_num
  obtain ⟨hblks, hpw, hk1, hk2, hst, hnc, hnx1, hnx2, L, I, Fr,
    hLlen, hnd, hmem, hIlen, hord, hint, hr0, hrpos, hnoroot, hpar, hdep, hfc⟩ := hW
  unfold HtabWF
  simp only [hfp, h0, h1, h3, h5, h6, h7, h8, h9, h10]
  have hin_le : ∀ n ∈ L ++ I, n ≤ hdr s t 10 := fun n hn => by
    have := (hmem n).1 (List.mem_append_left Fr hn); omega
  have hfr_le : ∀ f ∈ Fr, f ≤ hdr s t 10 := fun f hf => by
    have := (hmem f).1 (List.mem_append_right (L ++ I) hf); omega
  have hfp3 : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have hob := (hblks _ hfp3).1
  refine ⟨?_, hpw, hk1, hk2, hst, hnc, hnx1, hnx2, L, I, Fr, hLlen, hnd, hmem, hIlen,
    ?_, ?_, hr0, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hin, hw⟩ := hblks i hi
    exact ⟨hin, (wordsOK_congr_of_ivl hcell (le_trans hin.2 h264) (mem_worldTypedIvls_htab ht hi)).2 hw⟩
  · intro idx hidx
    have hLi : L[idx] ∈ L ++ I := List.mem_append_left I (List.getElem_mem _)
    have hord_eq : memW post (hdr s t 6 + 8 * idx) = memW s (hdr s t 6 + 8 * idx) :=
      memW_eq_of_cellHits hcell (by have := le_trans hob.2 h264; omega)
        (mem_worldTypedIvls_htab ht hfp3)
        ⟨by dsimp only; omega, by dsimp only; omega⟩
    rw [hord_eq, nodeF_eq_of_lt hcell ht hW' (hin_le _ hLi) (by omega),
      nodeF_eq_of_lt hcell ht hW' (hin_le _ hLi) (by omega)]
    exact hord idx hidx
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append_right L hn
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hint n hn
    rw [nodeF_eq_of_lt hcell ht hW' (hin_le _ hnLI) (by omega),
        nodeF_eq_of_lt hcell ht hW' (hin_le _ hnLI) (by omega),
        nodeF_eq_of_lt hcell ht hW' (hin_le _ hnLI) (by omega),
        nodeF_eq_of_lt hcell ht hW' (hin_le _ c2) (by omega),
        nodeF_eq_of_lt hcell ht hW' (hin_le _ c3) (by omega)]
    exact ⟨c1, c2, c3, c4, c5, c6⟩
  · intro hpos
    obtain ⟨hr1, hr2⟩ := hrpos hpos
    rw [nodeF_eq_of_lt hcell ht hW' (hin_le _ hr1) (by omega)]
    exact ⟨hr1, hr2⟩
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append_right L hn
    rw [nodeF_eq_of_lt hcell ht hW' (hin_le _ hnLI) (by omega),
        nodeF_eq_of_lt hcell ht hW' (hin_le _ hnLI) (by omega)]
    exact hnoroot n hn
  · intro n hn hnr
    rw [nodeF_eq_of_lt hcell ht hW' (hin_le _ hn) (by omega)]
    exact hpar n hn hnr
  · obtain ⟨dep, hdep⟩ := hdep
    refine ⟨dep, fun n hn hnr => ?_⟩
    have hpI : nodeF s (hdr s t 5) n 0 ∈ L ++ I := List.mem_append_right L (hpar n hn hnr)
    rw [nodeF_eq_of_lt hcell ht hW' (hin_le _ hn) (by omega),
        nodeF_eq_of_lt hcell ht hW' (hin_le _ hpI) (by omega),
        nodeF_eq_of_lt hcell ht hW' (hin_le _ hpI) (by omega)]
    exact hdep n hn hnr
  · exact (freeChain_congr_of_htab hcell ht hW' Fr _ hfr_le).2 hfc

theorem htabValues_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hcell : SameTypedCells s post S Nd) {t : Nat} (ht : t ∈ S) (hW : HtabWF s t) :
    htabValues post t = htabValues s t := by
  have htb := (hW.1 (t, 88) (by simp [htabFootprint])).1
  have h3 := htab_hdr_eq hcell ht htb 3 (by omega)
  have h5 := htab_hdr_eq hcell ht htb 5 (by omega)
  have h6 := htab_hdr_eq hcell ht htb 6 (by omega)
  have hcnt := htabCount_le_ncap hW
  have hfp3 : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have hob := (hW.1 _ hfp3).1
  have h264 : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; norm_num
  unfold htabValues
  rw [h3, h5, h6]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have ho_eq : memW post (hdr s t 6 + 8 * i) = memW s (hdr s t 6 + 8 * i) :=
    memW_eq_of_cellHits hcell (by have := le_trans hob.2 h264; omega)
      (mem_worldTypedIvls_htab ht hfp3)
      ⟨by dsimp only; omega, by dsimp only; omega⟩
  rw [ho_eq]
  exact nodeF_eq_of_lt hcell ht hW (htabOrder_entry_le_ncap hW hi) (by omega)

theorem htabValuesIn_congr {F : Type} {s post : PanSemStateFiniteExact 64 F} {S S' Nd : List Nat}
    (hcell : SameTypedCells s post S Nd) {t : Nat} (ht : t ∈ S) (hW : HtabWF s t)
    (hsub : ∀ u ∈ S, u ∈ S') (hvin : HtabValuesIn s t S) :
    HtabValuesIn post t S' := by
  have htb := (hW.1 (t, 88) (by simp [htabFootprint])).1
  have h3 := htab_hdr_eq hcell ht htb 3 (by omega)
  have h5 := htab_hdr_eq hcell ht htb 5 (by omega)
  have h6 := htab_hdr_eq hcell ht htb 6 (by omega)
  have hcnt := htabCount_le_ncap hW
  have hfp3 : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have hob := (hW.1 _ hfp3).1
  have h264 : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; norm_num
  intro i hi
  rw [h3] at hi
  rw [h5, h6]
  have ho_eq : memW post (hdr s t 6 + 8 * i) = memW s (hdr s t 6 + 8 * i) :=
    memW_eq_of_cellHits hcell (by have := le_trans hob.2 h264; omega)
      (mem_worldTypedIvls_htab ht hfp3)
      ⟨by dsimp only; omega, by dsimp only; omega⟩
  rw [ho_eq, nodeF_eq_of_lt hcell ht hW (htabOrder_entry_le_ncap hW hi) (by omega)]
  exact hsub _ (hvin i hi)

end InitECandidate.Solver.Wave8GuestInv.M11
