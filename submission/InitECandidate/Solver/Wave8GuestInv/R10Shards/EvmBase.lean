import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.HeapPotential
import InitECandidate.Solver.GuestTrapOutcomes

/-! Shared domain, alignment, and R11 `SameTypedCells` / `WorldTypedWith` congruence
infrastructure for EVM frame contracts (`ek_*` and `frame_*_spec`).
Imports `ContractParts.C07` directly so all R11 definitions (`FunSpec`, `GlobalsKept`,
`Disj`, `frameObjects`, `MarksOK`, `EvmKeeps`, `EvmAvoids`) are used directly without duplication. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.EvmBase

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

def stdKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]),
   ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
   ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
   ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]

/-! ## 1. Ordinary domain and basic memory/global helpers -/

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

theorem cellHits_of_inIvl {a : Nat} {i : Ivl} (h : InIvl a i) : CellHits a i :=
  ⟨by have := h.1; omega, h.2⟩

theorem cellHits_word_of_inIvl {a : Nat} {i : Ivl} (h1 : i.1 ≤ a) (h2 : a + 8 ≤ i.1 + i.2) :
    CellHits a i :=
  ⟨by omega, by omega⟩

theorem not_cellHits_of_disj_aligned {a : Nat} {i j : Ivl} (hj0 : j.2 ≠ 0)
    (ha1 : i.1 ≤ a) (ha2 : a + 8 ≤ i.1 + i.2) (hd : Disj i j) : ¬ CellHits a j := by
  rintro ⟨hc1, hc2⟩
  rcases hd with h0 | h0 | h1 | h2
  · rw [h0, Nat.add_zero] at ha2
    exact Nat.not_le_of_gt (lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 8)) ha2) ha1
  · exact hj0 h0
  · exact Nat.not_lt_of_ge h1 (lt_of_lt_of_le hc1 ha2)
  · exact Nat.not_lt_of_ge h2 (lt_of_le_of_lt ha1 hc2)

theorem allocated_mono {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    {i : Ivl} (hi : Allocated s i) : Allocated post i :=
  AllocatorGrows.allocated ⟨hh, hsc⟩ hi

theorem lookup_param_word_one {F : Type} (s : PanSemStateFiniteExact 64 F)
    {fname : MlS} {pname : String} {body : ProgHOL 64} {ret : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname = some ([(ofString pname, .one)], body, ret))
    (hs : ∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
      some (body, s.locals, ret)) :
    ∃ w : BitVec 64, s.locals.lookup (ofString pname) = some (.val (.word w)) := by
  obtain ⟨values, hl⟩ := hs
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup fname values body s.locals ret hl
  simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
  split at hx
  · rename_i hcond
    have heq := Option.some.inj hx
    obtain ⟨_, hrest⟩ := Prod.mk.inj heq
    obtain ⟨hloc, _⟩ := Prod.mk.inj hrest
    rcases values with _ | ⟨v1, _ | ⟨v2, _⟩⟩
    · simp at hcond
    · have hsh : shapeEqHOL .one (shapeOfHOLExact v1) = true := by
        simpa [List.zip] using hcond.2.2
      have hvw : ∃ w : BitVec 64, v1 = .val (.word w) := by
        rcases v1 with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
        · exact ⟨w, rfl⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh
      obtain ⟨w, rfl⟩ := hvw
      refine ⟨w, ?_⟩
      rw [← hloc]
      simp [List.zip, List.foldl]
    · simp at hcond
  · cases hx

theorem lookup_param_words_two {F : Type} (s : PanSemStateFiniteExact 64 F)
    {fname : MlS} {p1 p2 : String} {body : ProgHOL 64} {ret : ShapeHOL} (hne : ofString p1 ≠ ofString p2)
    (hlook : originalRuntimeCode.lookup fname =
      some ([(ofString p1, .one), (ofString p2, .one)], body, ret))
    (hs : ∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
      some (body, s.locals, ret)) :
    (∃ w1 : BitVec 64, s.locals.lookup (ofString p1) = some (.val (.word w1))) ∧
    (∃ w2 : BitVec 64, s.locals.lookup (ofString p2) = some (.val (.word w2))) := by
  obtain ⟨values, hl⟩ := hs
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup fname values body s.locals ret hl
  simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
  split at hx
  · rename_i hcond
    have heq := Option.some.inj hx
    obtain ⟨_, hrest⟩ := Prod.mk.inj heq
    obtain ⟨hloc, _⟩ := Prod.mk.inj hrest
    rcases values with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
    · simp at hcond
    · simp at hcond
    · have hsh := hcond.2.2
      simp only [List.zip, List.all, Bool.and_true, Bool.and_eq_true] at hsh
      have hvw1 : ∃ w : BitVec 64, v1 = .val (.word w) := by
        rcases v1 with ⟨⟨w⟩⟩ | _ | _
        · exact ⟨w, rfl⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh
      have hvw2 : ∃ w : BitVec 64, v2 = .val (.word w) := by
        rcases v2 with ⟨⟨w⟩⟩ | _ | _
        · exact ⟨w, rfl⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh
      obtain ⟨w1, rfl⟩ := hvw1
      obtain ⟨w2, rfl⟩ := hvw2
      refine ⟨⟨w1, ?_⟩, ⟨w2, ?_⟩⟩
      · rw [← hloc]
        simp [List.zip, List.foldl, hne]
      · rw [← hloc]
        simp [List.zip, List.foldl]
    · simp at hcond
  · cases hx

/-! ## 2. W1: Typed-cell congruence for `WorldTypedWith` (R11) -/

def SameTypedCells {F : Type} (s post : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  post.be = s.be ∧ post.memaddrs = s.memaddrs ∧ s.memaddrs = ordinaryDomain ∧
  (∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a) ∧
  (∀ a : Nat, a < 2 ^ 64 → (∃ i ∈ worldTypedIvls s S Nd, i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) →
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
  unfold memW
  rw [h.2.2.2.2.1 a ha ⟨i, hi, hch.1, hch.2⟩]

theorem wordsOK_congr_of_dom {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hma : post.memaddrs = s.memaddrs) {i : Ivl} :
    WordsOK post i ↔ WordsOK s i := by
  unfold WordsOK WordAt
  rw [hma]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun k => imp_congr_right fun _ => ?_))
  constructor
  · rintro ⟨_, hdom, _⟩
    cases hs : s.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with
    | word w => exact ⟨w, hdom, rfl⟩
  · rintro ⟨_, hdom, _⟩
    cases hp : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with
    | word w => exact ⟨w, hdom, rfl⟩

theorem wordsOK_congr_of_ivl {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (h : SameTypedCells s post S Nd) {i : Ivl}
    (_hbound : i.1 + i.2 ≤ 2 ^ 64) (_hi : i ∈ worldTypedIvls s S Nd) :
    WordsOK post i ↔ WordsOK s i :=
  wordsOK_congr_of_dom h.2.1

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

theorem mem_worldTypedIvls_htab {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {t : Nat} (ht : t ∈ S) {i : Ivl} (hi : i ∈ htabFootprint s t) :
    i ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_flatMap.2 ⟨t, ht, hi⟩

theorem mem_worldTypedIvls_typedRec {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {g : String} {sz : Nat} (hr : (g, sz) ∈ typedRecords) :
    (globN s g, if globN s g = 0 then 0 else sz) ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_right
  exact List.mem_map.2 ⟨(g, sz), hr, rfl⟩

theorem mem_worldTypedIvls_journal {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat} :
    (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈
      worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  simp

theorem mem_worldTypedIvls_blockOut {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {i : Ivl} (hi : i ∈ blockOutObjects s) :
    i ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
  exact hi

theorem mem_worldTypedIvls_bal {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {i : Ivl} (hi : i ∈ balObjects s) :
    i ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append_left; apply List.mem_append_right
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
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
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

/-! ## 3. Congruence of `blockOutObjects`, `balObjects`, `worldRoleSlots`, `journalRoleSlots`, `nodeExtents` (R11) -/

def coreWorldGlobals : List String :=
  ["ws", "bs", "ts", "bo", "bal_accounts", "bal_idx_accts", "bal_idx_stor",
   "journal", "journal_cap", "journal_n"]

theorem globN_eq_of_coreKept {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g) :
    globN post "ws" = globN s "ws" ∧
    globN post "bs" = globN s "bs" ∧
    globN post "ts" = globN s "ts" ∧
    globN post "bo" = globN s "bo" ∧
    globN post "bal_accounts" = globN s "bal_accounts" ∧
    globN post "bal_idx_accts" = globN s "bal_idx_accts" ∧
    globN post "bal_idx_stor" = globN s "bal_idx_stor" ∧
    globN post "journal" = globN s "journal" ∧
    globN post "journal_cap" = globN s "journal_cap" ∧
    globN post "journal_n" = globN s "journal_n" :=
  ⟨hg "ws" (by decide), hg "bs" (by decide), hg "ts" (by decide), hg "bo" (by decide),
   hg "bal_accounts" (by decide), hg "bal_idx_accts" (by decide), hg "bal_idx_stor" (by decide),
   hg "journal" (by decide), hg "journal_cap" (by decide), hg "journal_n" (by decide)⟩

theorem lstOK_congr_of_ivl {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hcell : SameTypedCells s post S Nd) {l : Nat}
    (hb : l + 24 ≤ 2 ^ 64) (hi : (l, 24) ∈ worldTypedIvls s S Nd) :
    LstOK post l ↔ LstOK s l := by
  unfold LstOK
  rw [memW_eq_of_cellHits hcell (by omega) hi ⟨by dsimp only; omega, by dsimp only; omega⟩,
      memW_eq_of_cellHits hcell (by omega) hi ⟨by dsimp only; omega, by dsimp only; omega⟩]

theorem lstObjects_eq_of_ivl {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hcell : SameTypedCells s post S Nd) {l esz : Nat}
    (hb : l + 24 ≤ 2 ^ 64) (hi : (l, 24) ∈ worldTypedIvls s S Nd) :
    lstObjects post l esz = lstObjects s l esz := by
  unfold lstObjects
  by_cases hl0 : l = 0
  · simp [hl0]
  · simp only [hl0, ↓reduceIte]
    rw [memW_eq_of_cellHits hcell (by omega) hi ⟨by dsimp only; omega, by dsimp only; omega⟩,
        memW_eq_of_cellHits hcell (by omega) hi ⟨by dsimp only; omega, by dsimp only; omega⟩]

theorem blockOut_in_fixedObjects {F : Type} {s : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hi : i ∈ blockOutObjects s) : i ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append_left; apply List.mem_append_right
  exact hi

theorem bal_in_fixedObjects {F : Type} {s : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hi : i ∈ balObjects s) : i ∈ fixedObjects s := by
  unfold fixedObjects
  exact List.mem_append_right _ hi

theorem blockOutObjects_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hF : FixedTyped s) (hcell : SameTypedCells s post S Nd)
    (hbo : globN post "bo" = globN s "bo") :
    blockOutObjects post = blockOutObjects s := by
  unfold blockOutObjects
  rw [hbo]
  by_cases hb0 : globN s "bo" = 0
  · simp [hb0]
  · have hr : ("bo", 88) ∈ typedRecords := by decide
    have ew24 := memW_typedRec_eq hA hF hcell hr hb0 (k := 24) (by omega)
    have ew32 := memW_typedRec_eq hA hF hcell hr hb0 (k := 32) (by omega)
    have ew40 := memW_typedRec_eq hA hF hcell hr hb0 (k := 40) (by omega)
    have ew56 := memW_typedRec_eq hA hF hcell hr hb0 (k := 56) (by omega)
    have ew72 := memW_typedRec_eq hA hF hcell hr hb0 (k := 72) (by omega)
    have ew80 := memW_typedRec_eq hA hF hcell hr hb0 (k := 80) (by omega)
    have hlst : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
        let l := memW s (globN s "bo" + k)
        memW post l = memW s l ∧ memW post (l + 16) = memW s (l + 16) := by
      intro k hk hp0 l
      have hmem_bo : (l, 24) ∈ blockOutObjects s := by
        unfold blockOutObjects
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl
        · left; right; simp [hb0, hp0, l]
        · right; simp [hb0, hp0, l]
      rcases fixedObject_le_2pow64 hA hF (blockOut_in_fixedObjects hmem_bo) with h0 | hbnd
      · dsimp only at h0; omega
      · dsimp only at hbnd
        have hwti := mem_worldTypedIvls_blockOut (S := S) (Nd := Nd) hmem_bo
        exact ⟨memW_eq_of_cellHits hcell (a := l) (i := (l, 24)) (by omega) hwti
                 ⟨Nat.le_refl _, Nat.add_le_add_left (by decide : 8 ≤ 24) _⟩,
               memW_eq_of_cellHits hcell (a := l + 16) (i := (l, 24)) (by omega) hwti
                 ⟨Nat.le_add_right _ _, by dsimp only; omega⟩⟩
    dsimp only
    rw [ew24, ew32, ew40, ew56, ew72, ew80]
    congr 1
    · congr 1
      by_cases h40 : memW s (globN s "bo" + 40) = 0
      · simp only [h40, or_true, ↓reduceIte]
      · obtain ⟨e0, e16⟩ := hlst 40 (by simp) h40
        rw [e0, e16]
    · by_cases h72 : memW s (globN s "bo" + 72) = 0
      · simp only [h72, or_true, ↓reduceIte]
      · obtain ⟨e0, e16⟩ := hlst 72 (by simp) h72
        rw [e0, e16]

theorem balRecords_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hT : TablesTyped s S) (hcell : SameTypedCells s post S Nd)
    (hba : globN post "bal_accounts" = globN s "bal_accounts") :
    balRecords post = balRecords s := by
  have heq : ∀ x : PanSemStateFiniteExact 64 F,
      balRecords x = if globN x "bal_accounts" = 0 then [] else htabValues x (globN x "bal_accounts") :=
    fun _ => rfl
  rw [heq, heq, hba]
  split
  · rfl
  · rename_i hne
    have hroot := hT.2.2.2.2.2.2.1 "bal_accounts" (by decide)
    rcases hroot with h0 | hmem
    · exact absurd h0 hne
    · exact htabValues_eq hcell hmem (hT.2.1 _ hmem).1

theorem balRecord_ivl_mem {F : Type} {s : PanSemStateFiniteExact 64 F} {ad : Nat}
    (had : ad ∈ balRecords s) : (ad, 40) ∈ balObjects s := by
  unfold balObjects
  exact List.mem_flatMap.2 ⟨ad, had, by simp⟩

theorem balRecord_lst_ivl_mem {F : Type} {s : PanSemStateFiniteExact 64 F} {ad k : Nat}
    (had : ad ∈ balRecords s) (hk : k ∈ ([16, 24, 32] : List Nat)) (hnz : memW s (ad + k) ≠ 0) :
    (memW s (ad + k), 24) ∈ balObjects s := by
  unfold balObjects
  refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hnz]

theorem balRecord_storLst_ivl_mem {F : Type} {s : PanSemStateFiniteExact 64 F} {ad l : Nat}
    (had : ad ∈ balRecords s) (hl : l ∈ htabValues s (memW s ad)) (hnz : l ≠ 0) :
    (l, 24) ∈ balObjects s := by
  unfold balObjects
  refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
  apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hnz]⟩

theorem balObjects_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    (hcell : SameTypedCells s post S Nd)
    (hba : globN post "bal_accounts" = globN s "bal_accounts") :
    balObjects post = balObjects s := by
  unfold balObjects
  rw [balRecords_eq hT hcell hba]
  apply List.flatMap_congr
  intro ad had
  have had_mem := balRecord_ivl_mem had
  rcases fixedObject_le_2pow64 hA hF (bal_in_fixedObjects had_mem) with h0 | had_bnd
  · dsimp only at h0; omega
  · dsimp only at had_bnd
    have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
    have e0 : memW post ad = memW s ad :=
      memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
    have e16 : memW post (ad + 16) = memW s (ad + 16) :=
      memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
    have e24 : memW post (ad + 24) = memW s (ad + 24) :=
      memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
    have e32 : memW post (ad + 32) = memW s (ad + 32) :=
      memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hbal := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hl_eq : ∀ (k esz : Nat), k ∈ ([16, 24, 32] : List Nat) →
        lstObjects post (memW s (ad + k)) esz = lstObjects s (memW s (ad + k)) esz := by
      intro k esz hk
      by_cases hkz : memW s (ad + k) = 0
      · simp [lstObjects, hkz]
      · have hm := balRecord_lst_ivl_mem had hk hkz
        rcases fixedObject_le_2pow64 hA hF (bal_in_fixedObjects hm) with h0 | hbnd
        · dsimp only at h0; omega
        · exact lstObjects_eq_of_ivl hcell hbnd (mem_worldTypedIvls_bal hm)
    have hval_eq : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq hcell hbal.1 (hT.2.1 _ hbal.1).1
    have hflat_eq : (htabValues s (memW s ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      apply List.flatMap_congr
      intro l hl
      by_cases hlz : l = 0
      · simp [lstObjects, hlz]
      · have hm := balRecord_storLst_ivl_mem had hl hlz
        rcases fixedObject_le_2pow64 hA hF (bal_in_fixedObjects hm) with h0 | hbnd
        · dsimp only at h0; omega
        · exact lstObjects_eq_of_ivl hcell hbnd (mem_worldTypedIvls_bal hm)
    rw [e0, e16, e24, e32, hl_eq 16 40 (by simp), hl_eq 24 16 (by simp), hl_eq 32 24 (by simp),
        hval_eq, hflat_eq]

theorem nodeIvl_eq_of_mem {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hNH : NodeHeap s Nd) (hcell : SameTypedCells s post S Nd) {n : Nat} (hn : n ∈ Nd) :
    memW post n = memW s n ∧ nodeIvl post n = nodeIvl s n := by
  have hmem_ni : nodeIvl s n ∈ nodeExtents s Nd := by
    unfold nodeExtents
    exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
  have hns_pos : 8 ≤ nodeSize (memW s n) := by
    unfold nodeSize; repeat' (first | omega | split)
  have hin := (hNH.1 n hn).2.2.1
  have hhl : heapLimit ≤ 2 ^ 64 := by rw [heapLimit_val]; norm_num
  have hbnd : n + nodeSize (memW s n) ≤ 2 ^ 64 := le_trans hin.2 hhl
  have heq : memW post n = memW s n :=
    memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_nodeExtents hmem_ni)
      ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
  exact ⟨heq, by simp only [nodeIvl, heq]⟩

theorem nodePath_eq_of_mem {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hNH : NodeHeap s Nd) (hcell : SameTypedCells s post S Nd) {n : Nat} (hn : n ∈ Nd) :
    nodePath post n = nodePath s n := by
  obtain ⟨hk0, _⟩ := nodeIvl_eq_of_mem hNH hcell hn
  unfold nodePath
  rw [hk0]
  by_cases h12 : memW s n = 1 ∨ memW s n = 2
  · have hns_ge : 56 ≤ nodeSize (memW s n) := by
      unfold nodeSize; rcases h12 with h1 | h2
      · simp [h1]
      · simp [h2]
    have hmem_ni : nodeIvl s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    have hin := (hNH.1 n hn).2.2.1
    have hhl : heapLimit ≤ 2 ^ 64 := by rw [heapLimit_val]; norm_num
    have hbnd : n + nodeSize (memW s n) ≤ 2 ^ 64 := le_trans hin.2 hhl
    have e32 : memW post (n + 32) = memW s (n + 32) :=
      memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_nodeExtents hmem_ni)
        ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
    have e40 : memW post (n + 40) = memW s (n + 40) :=
      memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_nodeExtents hmem_ni)
        ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
    rw [e32, e40]
  · simp [h12]

theorem nodeExtents_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hNH : NodeHeap s Nd) (hcell : SameTypedCells s post S Nd) :
    nodeExtents post Nd = nodeExtents s Nd := by
  unfold nodeExtents
  apply List.flatMap_congr
  intro n hn
  rw [(nodeIvl_eq_of_mem hNH hcell hn).2, nodePath_eq_of_mem hNH hcell hn]

theorem nodeHeap_congr {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hNH : NodeHeap s Nd) (hcell : SameTypedCells s post S Nd)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr") :
    NodeHeap post Nd := by
  have hhl : heapLimit ≤ 2 ^ 64 := by rw [heapLimit_val]; norm_num
  refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
  · obtain ⟨hk0, hni⟩ := nodeIvl_eq_of_mem hNH hcell hn
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hNH.1 n hn
    have hmem_ni : nodeIvl s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    have hbnd : (nodeIvl s n).1 + (nodeIvl s n).2 ≤ 2 ^ 64 := le_trans h3.2 hhl
    have hns_ge32 : 32 ≤ nodeSize (memW s n) := by
      unfold nodeSize; repeat' (first | omega | split)
    have e16 : memW post (n + 16) = memW s (n + 16) :=
      memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
        (mem_worldTypedIvls_nodeExtents hmem_ni)
        ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
    rw [hk0, hni, e16]
    refine ⟨h1, allocated_mono hh hsc h2, h3,
      (wordsOK_congr_of_ivl hcell hbnd (mem_worldTypedIvls_nodeExtents hmem_ni)).2 h4,
      ?_, ?_, ?_, h8, ?_, ?_⟩
    · intro hk2
      have h56 : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [hk2]
      have e48 : memW post (n + 48) = memW s (n + 48) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      rw [e48]; exact h5 hk2
    · intro hk3 i hi
      have h176 : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [hk3]
      have ei : memW post (n + 32 + 8 * i) = memW s (n + 32 + 8 * i) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      rw [ei]; exact h6 hk3 i hi
    · intro h12
      have hns_ge : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize; rcases h12 with c1 | c2
        · simp [c1]
        · simp [c2]
      have e32 : memW post (n + 32) = memW s (n + 32) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      have e40 : memW post (n + 40) = memW s (n + 40) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      rw [e32, e40]
      by_cases hnz : memW s (n + 40) = 0
      · exact Or.inl hnz
      · rcases h7 h12 with hz | ⟨hnib, hal, hin, hdisj⟩
        · exact absurd hz hnz
        · right
          have hp_mem : nodePath s n ∈ nodeExtents s Nd := by
            unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
          have hp_eq : nodePath s n = (memW s (n + 32), memW s (n + 40)) := by
            unfold nodePath; simp [h12, hnz]
          rw [hp_eq] at hp_mem
          refine ⟨(nibblesOK_congr_of_ivl hcell (le_trans hin.2 hhl)
            (mem_worldTypedIvls_nodeExtents hp_mem)).2 hnib,
            allocated_mono hh hsc hal, hin, fun m hm => ?_⟩
          rw [(nodeIvl_eq_of_mem hNH hcell hm).2]
          exact hdisj m hm
    · intro hk1
      have h64 : nodeSize (memW s n) = 64 := by unfold nodeSize; simp [hk1]
      have e56 : memW post (n + 56) = memW s (n + 56) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      rw [e56]; exact h9 hk1
    · intro hk3
      have h176 : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [hk3]
      have e168 : memW post (n + 168) = memW s (n + 168) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      rw [e168]; exact h10 hk3
  · rw [(nodeIvl_eq_of_mem hNH hcell hn).2, (nodeIvl_eq_of_mem hNH hcell hm).2]
    exact hNH.2 n hn m hm hne

theorem recRoles_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hF : FixedTyped s) (hcell : SameTypedCells s post S Nd)
    {g : String} {sz : Nat} (hr : (g, sz) ∈ typedRecords)
    (hg : globN post g = globN s g)
    {ks : List (Nat × String)} (hks : ∀ p ∈ ks, p.1 + 8 ≤ sz) :
    recRoles post g ks = recRoles s g ks := by
  unfold recRoles
  rw [hg]
  split
  · rfl
  · rename_i hne
    apply List.map_congr_left
    intro p hp
    rw [memW_typedRec_eq hA hF hcell hr hne (hks p hp)]

theorem nestRoles_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    (hcell : SameTypedCells s post S Nd)
    {g r : String} {sz : Nat} (hr : (g, sz) ∈ typedRecords) (hsz : 40 ≤ sz)
    (hg : globN post g = globN s g)
    (hslot : globN s g ≠ 0 → RootIn S (memW s (globN s g + 32))) :
    nestRoles post g r = nestRoles s g r := by
  unfold nestRoles
  rw [hg]
  split
  · rfl
  · rename_i hne
    rw [memW_typedRec_eq hA hF hcell hr hne (by omega)]
    split
    · rfl
    · rename_i htne
      rcases hslot hne with h0 | hmem
      · exact absurd h0 htne
      · rw [htabValues_eq hcell hmem (hT.2.1 _ hmem).1]

theorem worldRoleSlots_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    (hcell : SameTypedCells s post S Nd)
    (hg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g) :
    worldRoleSlots post = worldRoleSlots s := by
  obtain ⟨ews, ebs, ets, _, eba, ebia, ebis, _, _, _⟩ := globN_eq_of_coreKept hg
  unfold worldRoleSlots
  rw [recRoles_eq hA hF hcell (sz := 40) (by decide) ews (by decide),
      recRoles_eq hA hF hcell (sz := 80) (by decide) ebs (by decide),
      recRoles_eq hA hF hcell (sz := 72) (by decide) ets (by decide),
      eba, ebia, ebis,
      nestRoles_eq hA hT hF hcell (sz := 80) (by decide) (by omega) ebs (hT.2.2.2.2.1 32 (by decide)),
      nestRoles_eq hA hT hF hcell (sz := 72) (by decide) (by omega) ets (hT.2.2.2.2.2.1 32 (by decide)),
      balRecords_eq hT hcell eba]
  congr 1; congr 1
  apply List.flatMap_congr
  intro ad had
  have had_mem := balRecord_ivl_mem had
  rcases fixedObject_le_2pow64 hA hF (bal_in_fixedObjects had_mem) with h0 | had_bnd
  · dsimp only at h0; omega
  · dsimp only at had_bnd
    have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
    rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
        memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]

theorem journalRole_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hF : FixedTyped s) (hcell : SameTypedCells s post S Nd)
    (hts : globN post "ts" = globN s "ts") (t : Nat) :
    journalRole post t = journalRole s t := by
  unfold journalRole
  rw [hts]
  by_cases hz : globN s "ts" = 0
  · simp [hz]
  · have hr : ("ts", 72) ∈ typedRecords := by decide
    rw [memW_typedRec_eq hA hF hcell hr hz (by omega),
        memW_typedRec_eq hA hF hcell hr hz (by omega),
        memW_typedRec_eq hA hF hcell hr hz (by omega),
        memW_typedRec_eq hA hF hcell hr hz (by omega)]

theorem journalRoleSlots_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hJ : JournalTyped s S) (hF : FixedTyped s)
    (hcell : SameTypedCells s post S Nd)
    (hg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g) :
    journalRoleSlots post = journalRoleSlots s := by
  obtain ⟨_, _, ets, _, _, _, _, ej, ejc, ejn⟩ := globN_eq_of_coreKept hg
  unfold journalRoleSlots
  rw [ejn, ej]
  apply List.flatMap_congr
  intro i hi
  rw [List.mem_range] at hi
  have hjcap_ne : globN s "journal_cap" ≠ 0 := by have := hJ.1; omega
  rcases hJ.2.2.1 with h0 | ⟨hal, _⟩
  · exact absurd h0 hjcap_ne
  · have hbnd := allocated_le_2pow64 hA hal
    dsimp only at hbnd
    have hwti := mem_worldTypedIvls_journal (s := s) (S := S) (Nd := Nd)
    simp only [hjcap_ne, ↓reduceIte] at hwti
    have hlt : 32 * i + 32 ≤ 32 * globN s "journal_cap" := by have := hJ.1; omega
    have e0 : memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) :=
      memW_eq_of_cellHits hcell (by omega) hwti ⟨by dsimp only; omega, by dsimp only; omega⟩
    have e16 : memW post (globN s "journal" + 32 * i + 16) = memW s (globN s "journal" + 32 * i + 16) :=
      memW_eq_of_cellHits hcell (by omega) hwti ⟨by dsimp only; omega, by dsimp only; omega⟩
    have e24 : memW post (globN s "journal" + 32 * i + 24) = memW s (globN s "journal" + 32 * i + 24) :=
      memW_eq_of_cellHits hcell (by omega) hwti ⟨by dsimp only; omega, by dsimp only; omega⟩
    dsimp only
    rw [e0, e16, e24, journalRole_eq hA hF hcell ets]

theorem worldTypedWith_congr_w1 {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hApost : ArenaReady post)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g)
    (hcell : SameTypedCells s post S Nd)
    (hWT : WorldTypedWith s S Nd)
    (hbuf : FixedTyped post ∧
      (∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
        Inside o (globN s "heap_ptr") (globN post "heap_ptr"))) :
    WorldTypedWith post S Nd ∧
    OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨ews, ebs, ets, ebo, eba, ebia, ebis, ej, ejc, ejn⟩ := globN_eq_of_coreKept hg
  have hbo_eq := blockOutObjects_eq hAs.2 hF hcell ebo
  have hbal_eq := balObjects_eq hAs.2 hT hF hcell eba
  have hne_eq := nodeExtents_eq hTr.1 hcell
  have hwrs_eq := worldRoleSlots_eq hAs.2 hT hF hcell hg
  have hjrs_eq := journalRoleSlots_eq hAs.2 hJ hF hcell hg
  have hdisj_fresh : ∀ i : Ivl, Allocated s i →
      ∀ o : Ivl, Inside o (globN s "heap_ptr") (globN post "heap_ptr") → Disj i o := by
    intro i hi o ho
    rcases hi with ⟨_, hi2⟩ | ⟨hi1, _⟩
    · exact Or.inr (Or.inr (Or.inl (le_trans hi2 ho.1)))
    · have hp_lim := hApost.2.2.1
      have hs_fr := hAs.2.2.2.1
      have hs_gap := hAs.2.2.2.2.1
      rw [heapLimit_val] at hp_lim
      rw [scratchStart_val] at hs_fr
      have ho2 : o.1 + o.2 ≤ globN post "heap_ptr" := ho.2
      exact Or.inr (Or.inr (Or.inr (by omega)))
  have hT_post : TablesTyped post S := by
    have hT' := hT
    obtain ⟨hnd, htwf, htpw, hws, hbs, hts, hgr, hbs32, hts32, hbal_ok, hbo_ok, hroles⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      have hW := (htwf t ht).1
      rw [htabFootprint_eq hcell ht hW]
      refine ⟨htabWF_congr hcell ht hW, fun i hi => ?_⟩
      obtain ⟨hal, hdf⟩ := (htwf t ht).2 i hi
      refine ⟨allocated_mono hh hsc hal, fun j hj => ?_⟩
      rcases hbuf.2 j hj with hj_old | rfl | hj_fr
      · exact hdf j hj_old
      · exact Or.inr (Or.inl rfl)
      · exact hdisj_fresh i hal j hj_fr
    · intro t ht u hu htu i hi j hj
      rw [htabFootprint_eq hcell ht (htwf t ht).1] at hi
      rw [htabFootprint_eq hcell hu (htwf u hu).1] at hj
      exact htpw t ht u hu htu i hi j hj
    · intro k hk hnz
      rw [ews] at hnz ⊢
      have hk_le : k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [memW_typedRec_eq hAs.2 hF hcell (by decide) hnz hk_le]
      exact hws k hk hnz
    · intro k hk hnz
      rw [ebs] at hnz ⊢
      have hk_le : k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [memW_typedRec_eq hAs.2 hF hcell (by decide) hnz hk_le]
      exact hbs k hk hnz
    · intro k hk hnz
      rw [ets] at hnz ⊢
      have hk_le : k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [memW_typedRec_eq hAs.2 hF hcell (by decide) hnz hk_le]
      exact hts k hk hnz
    · intro g hg_mem
      simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg_mem
      rcases hg_mem with rfl | rfl | rfl
      · rw [eba]; exact hgr "bal_accounts" (by decide)
      · rw [ebia]; exact hgr "bal_idx_accts" (by decide)
      · rw [ebis]; exact hgr "bal_idx_stor" (by decide)
    · intro hnz hmem
      rw [ebs] at hnz hmem ⊢
      rw [memW_typedRec_eq hAs.2 hF hcell (sz := 80) (by decide) hnz (by omega)] at hmem ⊢
      exact htabValuesIn_congr hcell hmem (htwf _ hmem).1 (fun _ h => h) (hbs32 hnz hmem)
    · intro hnz hmem
      rw [ets] at hnz hmem ⊢
      rw [memW_typedRec_eq hAs.2 hF hcell (sz := 72) (by decide) hnz (by omega)] at hmem ⊢
      exact htabValuesIn_congr hcell hmem (htwf _ hmem).1 (fun _ h => h) (hts32 hnz hmem)
    · rw [balRecords_eq hT' hcell eba]
      intro ad had
      have had_mem := balRecord_ivl_mem had
      rcases fixedObject_le_2pow64 hAs.2 hF (bal_in_fixedObjects had_mem) with h0 | had_bnd
      · dsimp only at h0; omega
      · dsimp only at had_bnd
        have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
        obtain ⟨c1, c2, c3, c4⟩ := hbal_ok ad had
        have e0 : memW post ad = memW s ad :=
          memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
        have e8 : memW post (ad + 8) = memW s (ad + 8) :=
          memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
        rw [e0, e8]
        refine ⟨c1, c2, ?_, ?_⟩
        · intro k hk
          have hk_le : k + 8 ≤ 40 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl <;> omega
          have ek : memW post (ad + k) = memW s (ad + k) :=
            memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
          rw [ek]
          have hck := c3 k hk
          by_cases hkz : memW s (ad + k) = 0
          · rw [hkz] at hck ⊢
            unfold LstOK at hck ⊢
            rw [memW_eq_of_lt_sourceBase hcell (a := 0 + 16) (by rw [sourceBase_val]; omega),
                memW_eq_of_lt_sourceBase hcell (a := 0 + 8) (by rw [sourceBase_val]; omega)]
            exact hck
          · have hm := balRecord_lst_ivl_mem had hk hkz
            rcases fixedObject_le_2pow64 hAs.2 hF (bal_in_fixedObjects hm) with h0 | hbnd
            · dsimp only at h0; omega
            · exact (lstOK_congr_of_ivl hcell hbnd (mem_worldTypedIvls_bal hm)).2 hck
        · rw [htabValues_eq hcell c1 (htwf _ c1).1]
          intro l hl
          have hcl := c4 l hl
          by_cases hlz : l = 0
          · rw [hlz] at hcl ⊢
            unfold LstOK at hcl ⊢
            rw [memW_eq_of_lt_sourceBase hcell (a := 0 + 16) (by rw [sourceBase_val]; omega),
                memW_eq_of_lt_sourceBase hcell (a := 0 + 8) (by rw [sourceBase_val]; omega)]
            exact hcl
          · have hm := balRecord_storLst_ivl_mem had hl hlz
            rcases fixedObject_le_2pow64 hAs.2 hF (bal_in_fixedObjects hm) with h0 | hbnd
            · dsimp only at h0; omega
            · exact (lstOK_congr_of_ivl hcell hbnd (mem_worldTypedIvls_bal hm)).2 hcl
    · rw [ebo]
      intro hnz k hk hp0
      have hk_le : k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      have ek := memW_typedRec_eq hAs.2 hF hcell (sz := 88) (by decide) hnz hk_le
      rw [ek] at hp0 ⊢
      have hmem_bo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
        unfold blockOutObjects
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl
        · left; right; simp [hnz, hp0]
        · right; simp [hnz, hp0]
      rcases fixedObject_le_2pow64 hAs.2 hF (blockOut_in_fixedObjects hmem_bo) with h0 | hbnd
      · dsimp only at h0; omega
      · exact (lstOK_congr_of_ivl hcell hbnd (mem_worldTypedIvls_blockOut hmem_bo)).2 (hbo_ok hnz k hk hp0)
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjrs_eq]
      refine ⟨fun a ha => ?_, hroles.2⟩
      obtain ⟨haS, hkl⟩ := hroles.1 a ha
      have htb := ((htwf a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
      rw [htab_hdr_eq hcell haS htb 0 (by omega)]
      exact ⟨haS, hkl⟩
  have hJ_post : JournalTyped post S := by
    obtain ⟨hj1, hj2, hj3, hj4⟩ := hJ
    unfold JournalTyped
    rw [ejn, ejc, ej]
    refine ⟨hj1, hj2, ?_, ?_⟩
    · rcases hj3 with hz | ⟨hal, hw⟩
      · exact Or.inl hz
      · by_cases hjcz : globN s "journal_cap" = 0
        · exact Or.inl hjcz
        · right
          have hwti := mem_worldTypedIvls_journal (s := s) (S := S) (Nd := Nd)
          simp only [hjcz, ↓reduceIte] at hwti
          exact ⟨allocated_mono hh hsc hal,
            (wordsOK_congr_of_ivl hcell (allocated_le_2pow64 hAs.2 hal) hwti).2 hw⟩
    · intro i hi
      rcases hj3 with hz | ⟨hal, _⟩
      · omega
      · have hjcz : globN s "journal_cap" ≠ 0 := by omega
        have hbnd := allocated_le_2pow64 hAs.2 hal
        dsimp only at hbnd
        have hwti := mem_worldTypedIvls_journal (s := s) (S := S) (Nd := Nd)
        simp only [hjcz, ↓reduceIte] at hwti
        have e0 : memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) :=
          memW_eq_of_cellHits hcell (by omega) hwti
            ⟨by dsimp only; omega, by dsimp only; omega⟩
        rw [e0]; exact hj4 i hi
  have hTr_post : TriesTypedWith post S Nd := by
    obtain ⟨hNH, hndisj, hws_tr⟩ := hTr
    refine ⟨nodeHeap_congr hNH hcell hh hsc, ?_, ?_⟩
    · rw [hne_eq]
      intro o ho
      have ho_alloc : o = (0, 0) ∨ Allocated s o := by
        unfold nodeExtents at ho
        obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
        rcases hno with rfl | rfl
        · exact Or.inr (hNH.1 n hn).2.1
        · unfold nodePath
          split
          · rename_i hcond
            rcases (hNH.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
            · exact absurd h0 hcond.2
            · exact Or.inr hal
          · exact Or.inl rfl
      refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rw [htabFootprint_eq hcell ht (hT.2.1 t ht).1] at hi
        exact (hndisj o ho).1 t ht i hi
      · rcases hbuf.2 j hj with hj_old | rfl | hj_fr
        · exact (hndisj o ho).2 j hj_old
        · exact Or.inr (Or.inl rfl)
        · rcases ho_alloc with rfl | hal
          · exact Or.inl rfl
          · exact hdisj_fresh o hal j hj_fr
    · rw [ews]
      intro hws_nz
      have e24 := memW_typedRec_eq hAs.2 hF hcell (sz := 40) (k := 24) (by decide) hws_nz (by omega)
      have e32 := memW_typedRec_eq hAs.2 hF hcell (sz := 40) (k := 32) (by decide) hws_nz (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hws_tr hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hW32 := (hT.2.1 _ htS).1
      have hcnt32 := htabCount_le_ncap hW32
      have htb32 := (hW32.1 (memW s (globN s "ws" + 32), 88) (by simp [htabFootprint])).1
      rw [htab_hdr_eq hcell htS htb32 3 (by omega)] at hi
      rw [htab_hdr_eq hcell htS htb32 5 (by omega), htab_hdr_eq hcell htS htb32 6 (by omega)]
      have hfp3 : (hdr s (memW s (globN s "ws" + 32)) 6, (hdr s (memW s (globN s "ws" + 32)) 10 + 1) * 8) ∈
          htabFootprint s (memW s (globN s "ws" + 32)) := by simp [htabFootprint]
      have hob := (hW32.1 _ hfp3).1
      have h264 : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; norm_num
      have ho_eq : memW post (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i) =
          memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i) :=
        memW_eq_of_cellHits hcell (by have := le_trans hob.2 h264; omega)
          (mem_worldTypedIvls_htab htS hfp3) ⟨by dsimp only; omega, by dsimp only; omega⟩
      rw [ho_eq, nodeF_eq_of_lt hcell htS hW32 (htabOrder_entry_le_ncap hW32 hi) (by omega)]
      exact hr32 htS i hi
  refine ⟨⟨hT_post, hJ_post, hbuf.1, hTr_post⟩, ?_⟩
  intro o ho
  unfold worldOwned at ho
  simp only [List.mem_append] at ho
  rcases ho with (ho_htab | ho_fix) | ho_nd
  · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.1 ho_htab
    rw [htabFootprint_eq hcell ht (hT.2.1 t ht).1] at hi
    refine Or.inr (Or.inl ⟨o, ?_, le_refl _, le_refl _⟩)
    unfold worldOwned
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hi⟩))
  · rcases hbuf.2 o ho_fix with ho_old | rfl | ho_fr
    · refine Or.inr (Or.inl ⟨o, ?_, le_refl _, le_refl _⟩)
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_right _ ho_old)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ho_fr)
  · rw [hne_eq] at ho_nd
    refine Or.inr (Or.inl ⟨o, ?_, le_refl _, le_refl _⟩)
    unfold worldOwned
    exact List.mem_append_right _ ho_nd

theorem fixedObjects_eq_of_nonHeapGlobalsKept {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat}
    (hAs : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    (hcell : SameTypedCells s post S Nd)
    (hglob : ∀ name, name ≠ "heap_ptr" → name ≠ "scratch_ptr" → name ≠ "frame_mem_ptr" →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) :
    fixedObjects post = fixedObjects s := by
  have hg : ∀ name, name ≠ "heap_ptr" → name ≠ "scratch_ptr" → name ≠ "frame_mem_ptr" →
      globN post name = globN s name :=
    fun n h1 h2 h3 => (globN_eq_of_lookup_eq (hglob n h1 h2 h3)).symm
  have hgb_eq : (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) =
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
    apply List.map_congr_left
    intro gn hgn
    have hne : gn.1 ≠ "heap_ptr" ∧ gn.1 ≠ "scratch_ptr" ∧ gn.1 ≠ "frame_mem_ptr" := by
      have hm : gn.1 ∈ globalBuffers.map Prod.fst := List.mem_map.2 ⟨gn, hgn, rfl⟩
      exact ⟨fun h => by rw [h] at hm; exact (by decide : "heap_ptr" ∉ globalBuffers.map Prod.fst) hm,
             fun h => by rw [h] at hm; exact (by decide : "scratch_ptr" ∉ globalBuffers.map Prod.fst) hm,
             fun h => by rw [h] at hm; exact (by decide : "frame_mem_ptr" ∉ globalBuffers.map Prod.fst) hm⟩
    rw [hg gn.1 hne.1 hne.2.1 hne.2.2]
  unfold fixedObjects
  rw [hgb_eq,
      blockOutObjects_eq hAs hF hcell (hg "bo" (by decide) (by decide) (by decide)),
      balObjects_eq hAs hT hF hcell (hg "bal_accounts" (by decide) (by decide) (by decide)),
      hg "journal" (by decide) (by decide) (by decide),
      hg "journal_cap" (by decide) (by decide) (by decide)]

theorem wordsOK_of_allocated {F : Type} {post : PanSemStateFiniteExact 64 F}
    (hApost : ArenaReady post) {i : Ivl}
    (hal : Allocated post i) (h1 : i.1 % 8 = 0) (h2 : i.2 % 8 = 0) :
    WordsOK post i := by
  have hlo : sourceBase ≤ i.1 := by
    rcases hal with ⟨hl, _⟩ | ⟨hl, _⟩
    · exact hl
    · have := hApost.2.2.2.1; have := hApost.2.2.2.2.1
      rw [sourceBase_val]; rw [scratchStart_val] at *; omega
  have hhi : i.1 + i.2 ≤ heapEnd := by
    rcases hal with ⟨_, hr⟩ | ⟨_, hr⟩
    · have := hApost.2.2.1; rw [heapLimit_val] at this; rw [heapEnd_val]; omega
    · rw [scratchEnd_val] at hr; rw [heapEnd_val]; omega
  exact wordsOK_of_inside_heap post hApost.1.memaddrs i.1 i.2 h1 h2 hlo hhi

theorem fixedTyped_of_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hApost : ArenaReady post) (hF : FixedTyped s)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hfeq : fixedObjects post = fixedObjects s) :
    FixedTyped post := by
  unfold FixedTyped
  rw [hfeq]
  refine ⟨fun i hi => ?_, hF.2⟩
  rcases hF.1 i hi with h0 | ⟨hal, hw⟩
  · exact Or.inl h0
  · have hal' := allocated_mono hh hsc hal
    exact Or.inr ⟨hal', wordsOK_of_allocated hApost hal' hw.1 hw.2.1⟩

theorem allocated_disj_heapFree {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hi : Allocated s i) : Disj i (heapFree s) := by
  unfold heapFree
  rcases hi with ⟨_, hi2⟩ | ⟨hi1, _⟩
  · exact Or.inr (Or.inr (Or.inl hi2))
  · have hlim := hA.2.1
    have hfr := hA.2.2.1
    have hgap := hA.2.2.2.1
    rw [heapLimit_val] at hlim ⊢; rw [scratchStart_val] at hfr
    exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))

theorem allocated_disj_freeGap {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hi : Allocated s i) : Disj i (freeGap s) := by
  unfold freeGap
  rcases hi with ⟨_, hi2⟩ | ⟨hi1, _⟩
  · have hlim := hA.2.1
    have hfr := hA.2.2.1
    rw [heapLimit_val] at hlim; rw [scratchStart_val] at hfr
    exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
  · have hgap := hA.2.2.2.1
    exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))

theorem worldTypedIvls_allocated {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hWT : WorldTypedWith s S Nd) {i : Ivl} (hi : i ∈ worldTypedIvls s S Nd) :
    i.2 = 0 ∨ Allocated s i := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  unfold worldTypedIvls at hi
  simp only [List.mem_append] at hi
  rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
  · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
    exact Or.inr (((hT.2.1 t ht).2 i hfp).1)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
    rcases hF.1 _ (typedRec_in_fixedObjects s hr) with h0 | ⟨hal, _⟩
    · exact Or.inl h0
    · exact Or.inr hal
  · simp only [List.mem_singleton] at h3
    subst h3
    rcases hJ.2.2.1 with h0 | ⟨hal, _⟩
    · exact Or.inl (by dsimp only; omega)
    · by_cases hcz : globN s "journal_cap" = 0
      · exact Or.inl (by dsimp only; omega)
      · simp only [hcz, ↓reduceIte]
        exact Or.inr hal
  · rcases hF.1 i (blockOut_in_fixedObjects h4) with h0 | ⟨hal, _⟩
    · exact Or.inl h0
    · exact Or.inr hal
  · rcases hF.1 i (bal_in_fixedObjects h5) with h0 | ⟨hal, _⟩
    · exact Or.inl h0
    · exact Or.inr hal
  · unfold nodeExtents at h6
    obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 h6
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
    rcases hno with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath
      split
      · rename_i hcond
        rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
        · exact absurd h0 hcond.2
        · exact Or.inr hal
      · exact Or.inl rfl

def ByteFrameOutside {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (keep : List Ivl) (fresh : Ivl) : Prop :=
  post.be = s.be ∧ post.memaddrs = s.memaddrs ∧ s.memaddrs = ordinaryDomain ∧
  (∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a) ∧
  FrameOutside s post keep fresh ∧
  (∀ a : Nat, a < 2 ^ 64 → (∀ j ∈ keep, Disj (a, 8) j) → Disj (a, 8) fresh →
    post.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a)) ∧
  (∀ b : Nat, b < 2 ^ 64 → (∀ j ∈ keep, ¬ InIvl b j) → ¬ InIvl b fresh →
    memB post b = memB s b)

theorem sameTypedCells_of_byteFrame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {R extra : List Ivl}
    (hAs : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hR : IvlsDisj R (worldTypedIvls s S Nd))
    (hextra : ∀ x ∈ extra, ∀ i ∈ worldTypedIvls s S Nd, i.2 = 0 ∨ Disj x i)
    (hbfr : ByteFrameOutside s post (R ++ extra ++ [freeGap s]) (heapFree s)) :
    SameTypedCells s post S Nd := by
  obtain ⟨hbe, hma, hdom, hnotdom, _, hword, hbyte⟩ := hbfr
  have hall_disj : ∀ j ∈ R ++ extra ++ [freeGap s], ∀ i ∈ worldTypedIvls s S Nd, i.2 = 0 ∨ Disj j i := by
    intro j hj i hi
    rcases List.mem_append.1 hj with hj1 | hjfg
    · rcases List.mem_append.1 hj1 with hjR | hjex
      · exact Or.inr (hR j hjR i hi)
      · exact hextra j hjex i hi
    · simp only [List.mem_singleton] at hjfg
      subst hjfg
      rcases worldTypedIvls_allocated hWT hi with hi0 | hal
      · exact Or.inl hi0
      · exact Or.inr (Disj.flip (allocated_disj_freeGap hAs.2 hal))
  have hhf_disj : ∀ i ∈ worldTypedIvls s S Nd, i.2 = 0 ∨ Disj i (heapFree s) := by
    intro i hi
    rcases worldTypedIvls_allocated hWT hi with hi0 | hal
    · exact Or.inl hi0
    · exact Or.inr (allocated_disj_heapFree hAs.2 hal)
  refine ⟨hbe, hma, hdom, hnotdom, fun a ha ⟨i, hi, ha1, ha2⟩ => ?_, fun b hb ⟨i, hi, hb1, hb2⟩ => ?_⟩
  · apply hword a ha
    · intro j hj
      rcases hall_disj j hj i hi with hi0 | hdj
      · rw [hi0, Nat.add_zero] at ha2
        exact False.elim (Nat.not_le_of_gt (lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 8)) ha2) ha1)
      · rcases hdj with hj0 | hi0 | h1 | h2
        · exact Or.inr (Or.inl hj0)
        · rw [hi0, Nat.add_zero] at ha2
          exact False.elim (Nat.not_le_of_gt (lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 8)) ha2) ha1)
        · exact Or.inr (Or.inr (Or.inr (le_trans h1 ha1)))
        · exact Or.inr (Or.inr (Or.inl (le_trans ha2 h2)))
    · rcases hhf_disj i hi with hi0 | hdj
      · rw [hi0, Nat.add_zero] at ha2
        exact False.elim (Nat.not_le_of_gt (lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 8)) ha2) ha1)
      · rcases hdj with hi0 | hf0 | h1 | h2
        · rw [hi0, Nat.add_zero] at ha2
          exact False.elim (Nat.not_le_of_gt (lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 8)) ha2) ha1)
        · exact Or.inr (Or.inl hf0)
        · exact Or.inr (Or.inr (Or.inl (le_trans ha2 h1)))
        · exact Or.inr (Or.inr (Or.inr (le_trans h2 ha1)))
  · apply hbyte b hb
    · intro j hj ⟨hbj1, hbj2⟩
      rcases hall_disj j hj i hi with hi0 | hdj
      · rw [hi0, Nat.add_zero] at hb2
        exact Nat.not_le_of_gt hb2 hb1
      · rcases hdj with hj0 | hi0 | h1 | h2
        · rw [hj0, Nat.add_zero] at hbj2
          exact Nat.not_le_of_gt hbj2 hbj1
        · rw [hi0, Nat.add_zero] at hb2
          exact Nat.not_le_of_gt hb2 hb1
        · exact Nat.not_lt_of_ge (le_trans h1 hb1) hbj2
        · exact Nat.not_lt_of_ge (le_trans h2 hbj1) hb2
    · intro ⟨hbf1, hbf2⟩
      rcases hhf_disj i hi with hi0 | hdj
      · rw [hi0, Nat.add_zero] at hb2
        exact Nat.not_le_of_gt hb2 hb1
      · rcases hdj with hi0 | hf0 | h1 | h2
        · rw [hi0, Nat.add_zero] at hb2
          exact Nat.not_le_of_gt hb2 hb1
        · rw [hf0, Nat.add_zero] at hbf2
          exact Nat.not_le_of_gt hbf2 hbf1
        · exact Nat.not_lt_of_ge (le_trans h1 hbf1) hb2
        · exact Nat.not_lt_of_ge (le_trans h2 hb1) hbf2

end InitECandidate.Solver.Wave8GuestInv.EvmBase

