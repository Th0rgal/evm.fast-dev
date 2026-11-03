import InitECandidate.Solver.Wave8GuestInv.EntryDefs
import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.HeapPotential
import InitECandidate.Solver.PanRunBoundedExt
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.AddSub

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
/-! ### From SoloHtabSetBase.lean -/

/-! Self-contained proof of `htab_set_spec` for R10 (`ContractParts/C00.lean`). -/


namespace InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Distinctness of local/global names -/

section Names
@[local simp] theorem nm_t_klen : (ofString "t" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_stride : (ofString "t" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_leaf : (ofString "t" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_keys : (ofString "t" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_eq : (ofString "t" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_d : (ofString "t" = ofString "d") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_nodes : (ofString "t" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_p : (ofString "t" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_n : (ofString "t" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_b : (ofString "t" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_nl : (ofString "t" = ofString "nl") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_ni : (ofString "t" = ofString "ni") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_key : (ofString "t" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_value : (ofString "t" = ofString "value") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_pos : (ofString "t" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_f : (ofString "t" = ofString "f") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_nf : (ofString "t" = ofString "nf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_next : (ofString "t" = ofString "next") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_nodecap : (ofString "t" = ofString "nodecap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_ncap : (ofString "t" = ofString "ncap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_order : (ofString "t" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_t_bit : (ofString "t" = ofString "bit") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_heap_scratch : (ofString "heap_ptr" = ofString "scratch_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_scratch_heap : (ofString "scratch_ptr" = ofString "heap_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_heap_frame : (ofString "heap_ptr" = ofString "frame_mem_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm_frame_heap : (ofString "frame_mem_ptr" = ofString "heap_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
end Names

/-! ## 2. Ordinary domain and word/byte read-write helpers -/

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

theorem wordAt_iff {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    WordAt s a ↔ s.memaddrs (BitVec.ofNat 64 a) := by
  constructor
  · rintro ⟨_, h, _⟩; exact h
  · intro h
    rcases hm : s.memory (BitVec.ofNat 64 a) with ⟨w⟩
    exact ⟨w, h, hm⟩

theorem wordAt_of_dom {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hma : s.memaddrs = ordinaryDomain) (a : Nat) (h1 : sourceBase ≤ a)
    (h2 : a < heapEnd) (h3 : a % 8 = 0) : WordAt s a := by
  have hsb : sourceBase = 2701131776 := rfl
  have hhe : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  rw [wordAt_iff, hma, ordinaryDomain_iff]
  have ha : (BitVec.ofNat 64 a).toNat = a := by
    simp only [BitVec.toNat_ofNat]
    omega
  rw [ha]
  omega

theorem wordsOK_block {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hma : s.memaddrs = ordinaryDomain) (b l : Nat) (hb : b % 8 = 0) (hl : l % 8 = 0)
    (h1 : sourceBase ≤ b) (h2 : b + l ≤ heapEnd) : WordsOK s (b, l) := by
  refine ⟨hb, hl, fun j hj => wordAt_of_dom s hma _ (by omega) (by omega) (by omega)⟩

/-! ## 3. `HtabExitAt` reflexivity, transitivity, and local invariance -/

def HtabExitAt {F : Type} (t : Nat) (s post : PanSemStateFiniteExact 64 F) : Prop :=
  let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
  ArenaReady post ∧ HtabWF post t ∧
  hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
  (∀ i ∈ htabFootprint post t, Allocated post i ∧
    ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
  FrameOutside s post (htabFootprint s t) fresh ∧
  (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
    s.globals.lookup k = post.globals.lookup k)

theorem htabExit_iff_at {F : Type} (s post : PanSemStateFiniteExact 64 F) :
    HtabExit s post ↔ HtabExitAt (locN s "t") s post := Iff.rfl

theorem HtabExitAt.refl {F : Type} (t : Nat) (s : PanSemStateFiniteExact 64 F)
    (hA : ArenaReady s) (hW : HtabWF s t)
    (hal : ∀ i ∈ htabFootprint s t, Allocated s i) : HtabExitAt t s s := by
  refine ⟨hA, hW, rfl, rfl, le_refl _, ?_, fun _ _ _ => rfl, fun _ _ => rfl⟩
  intro i hi
  exact ⟨hal i hi, Or.inl ⟨i, hi, le_refl _, le_refl _⟩⟩

theorem HtabExitAt.trans {F : Type} {t : Nat} {a b c : PanSemStateFiniteExact 64 F}
    (hab : HtabExitAt t a b) (hbc : HtabExitAt t b c) : HtabExitAt t a c := by
  obtain ⟨_, _, hk01, hk11, hh1, hfp1, hfr1, hg1⟩ := hab
  obtain ⟨hA2, hW2, hk02, hk12, hh2, hfp2, hfr2, hg2⟩ := hbc
  refine ⟨hA2, hW2, hk02.trans hk01, hk12.trans hk11, le_trans hh1 hh2, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hal, hprov⟩ := hfp2 i hi
    refine ⟨hal, ?_⟩
    rcases hprov with ⟨j, hj, hij⟩ | hfr
    · rcases (hfp1 j hj).2 with ⟨k, hk, hjk⟩ | hjf
      · exact Or.inl ⟨k, hk, ⟨le_trans hjk.1 hij.1, by have := hij.2; have := hjk.2; omega⟩⟩
      · right
        obtain ⟨h1, h2⟩ := hjf
        obtain ⟨h3, h4⟩ := hij
        constructor <;> simp only at * <;> omega
    · right
      obtain ⟨h1, h2⟩ := hfr
      constructor <;> simp only at * <;> omega
  · intro x hx hxf
    have hxb : ∀ j ∈ htabFootprint b t, ¬ CellHits x.toNat j := by
      intro j hj hin
      rcases (hfp1 j hj).2 with ⟨k, hk, hjk⟩ | hjf
      · exact hx k hk ⟨lt_of_le_of_lt hjk.1 hin.1, lt_of_lt_of_le hin.2 hjk.2⟩
      · apply hxf
        obtain ⟨h1, h2⟩ := hjf
        obtain ⟨h3, h4⟩ := hin
        constructor <;> simp only at * <;> omega
    have hxf2 : ¬ CellHits x.toNat (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr") := by
      intro hin
      apply hxf
      obtain ⟨h3, h4⟩ := hin
      constructor <;> simp only at * <;> omega
    have hxf1 : ¬ CellHits x.toNat (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr") := by
      intro hin
      apply hxf
      obtain ⟨h3, h4⟩ := hin
      constructor <;> simp only at * <;> omega
    rw [hfr2 x hxb hxf2, hfr1 x hx hxf1]
  · intro k hk
    rw [hg1 k hk, hg2 k hk]

theorem freeChain_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k nodes : Nat) :
    ∀ (Fr : List Nat) (head : Nat),
      FreeChain { s with locals := locals, clock := k } nodes head Fr ↔ FreeChain s nodes head Fr
  | [], _ => Iff.rfl
  | f :: rest, head => by
    simp only [FreeChain]
    exact and_congr Iff.rfl (freeChain_locals s locals k nodes rest _)

theorem htabWF_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k t : Nat) :
    HtabWF { s with locals := locals, clock := k } t ↔ HtabWF s t := by
  simp only [HtabWF, freeChain_locals]
  exact Iff.rfl

theorem arenaReady_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ArenaReady { s with locals := locals, clock := k } ↔ ArenaReady s :=
  ⟨fun h => ⟨guestInv_congr (s := { s with locals := locals, clock := k }) rfl rfl rfl rfl h.1, h.2⟩,
   fun h => ⟨guestInv_with_locals_clock s locals k h.1, h.2⟩⟩

theorem htabExitAt_locals {F : Type} (t : Nat) (a b : PanSemStateFiniteExact 64 F)
    (L1 L2 : HolFiniteMapExact MlS (ValueHOL 64)) (k1 k2 : Nat) :
    HtabExitAt t { a with locals := L1, clock := k1 } { b with locals := L2, clock := k2 } ↔
      HtabExitAt t a b := by
  simp only [HtabExitAt, arenaReady_locals, htabWF_locals]
  exact Iff.rfl

/-! ## 4. Function lookups for `htab_set` and its callees -/

theorem lookup_htab_set :
    originalRuntimeCode.lookup (ofString "htab_set") =
      some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
        sourceFnBody Guest.Software.guestFn_htab_set, .one) :=
  lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_set) rfl

theorem lookup_htab_find_leaf :
    originalRuntimeCode.lookup (ofString "htab_find_leaf") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_find_leaf, .one) :=
  lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_find_leaf) rfl

theorem lookup_htab_first_diff :
    originalRuntimeCode.lookup (ofString "htab_first_diff") =
      some ([(ofString "a", .one), (ofString "b", .one), (ofString "key_len", .one)],
        sourceFnBody Guest.Software.guestFn_htab_first_diff, .one) :=
  lookup_of_guestAst_getElem 130 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_first_diff) rfl

theorem lookup_htab_new_node :
    originalRuntimeCode.lookup (ofString "htab_new_node") =
      some ([(ofString "t", .one)],
        sourceFnBody Guest.Software.guestFn_htab_new_node, .one) :=
  lookup_of_guestAst_getElem 134 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new_node) rfl

theorem lookup_htab_new_leaf :
    originalRuntimeCode.lookup (ofString "htab_new_leaf") =
      some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
        sourceFnBody Guest.Software.guestFn_htab_new_leaf, .one) :=
  lookup_of_guestAst_getElem 135 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new_leaf) rfl

theorem lookup_htab_new_internal :
    originalRuntimeCode.lookup (ofString "htab_new_internal") =
      some ([(ofString "t", .one), (ofString "bit", .one)],
        sourceFnBody Guest.Software.guestFn_htab_new_internal, .one) :=
  lookup_of_guestAst_getElem 136 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new_internal) rfl

theorem lookup_htab_grow :
    originalRuntimeCode.lookup (ofString "htab_grow") =
      some ([(ofString "t", .one)],
        sourceFnBody Guest.Software.guestFn_htab_grow, .one) :=
  lookup_of_guestAst_getElem 137 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_grow) rfl

theorem lookup_memeq_fn :
    originalRuntimeCode.lookup (ofString "memeq") =
      some ([(ofString "a", .one), (ofString "b", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memeq, .one) :=
  lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memeq) rfl

theorem lookup_memcpy_fn :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem lookup_alloc_fn :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

/-! ## 5. Abstract crit-bit tree preservation (`TreeWF`) -/

def FreeChainF (nd : Nat → Nat → Nat) : Nat → List Nat → Prop
  | head, [] => head = 0
  | head, f :: rest => head = f ∧ FreeChainF nd (nd f 0) rest

def TreeWF (L I Fr : List Nat) (next klen cnt root free : Nat) (nd : Nat → Nat → Nat)
    (ord : Nat → Nat) : Prop :=
  L.length = cnt ∧ (L ++ I ++ Fr).Nodup ∧ (∀ n, n ∈ L ++ I ++ Fr ↔ 1 ≤ n ∧ n < next) ∧
  ((cnt = 0 ∧ I = []) ∨ I.length + 1 = cnt) ∧
  (∀ (i : Nat) (h : i < L.length), ord i = L[i] ∧ nd L[i] 24 = 8 * klen ∧ nd L[i] 16 = i) ∧
  (∀ n ∈ I, nd n 24 < 8 * klen ∧ nd n 8 ∈ L ++ I ∧ nd n 16 ∈ L ++ I ∧ nd n 8 ≠ nd n 16 ∧
    nd (nd n 8) 0 = n ∧ nd (nd n 16) 0 = n) ∧
  (cnt = 0 → root = 0) ∧ (0 < cnt → root ∈ L ++ I ∧ nd root 0 = 0) ∧
  (∀ n ∈ I, nd n 8 ≠ root ∧ nd n 16 ≠ root) ∧
  (∀ n ∈ L ++ I, n ≠ root → nd n 0 ∈ I) ∧
  (∃ dep : Nat → Nat, ∀ n ∈ L ++ I, n ≠ root →
    (nd (nd n 0) 8 = n ∨ nd (nd n 0) 16 = n) ∧ dep (nd n 0) < dep n) ∧
  FreeChainF nd free Fr

theorem FreeChainF.congr {nd nd' : Nat → Nat → Nat} :
    ∀ (Fr : List Nat) (head : Nat), (∀ f ∈ Fr, nd' f 0 = nd f 0) →
      FreeChainF nd head Fr → FreeChainF nd' head Fr
  | [], _, _, h => h
  | f :: rest, head, hc, ⟨h1, h2⟩ => by
    refine ⟨h1, ?_⟩
    rw [hc f (List.mem_cons_self)]
    exact FreeChainF.congr rest _ (fun x hx => hc x (List.mem_cons_of_mem _ hx)) h2

theorem freeChain_iff {F : Type} (s : PanSemStateFiniteExact 64 F) (nodes : Nat) :
    ∀ (Fr : List Nat) (head : Nat), FreeChain s nodes head Fr ↔ FreeChainF (nodeF s nodes) head Fr
  | [], _ => Iff.rfl
  | f :: rest, head => by
    simp only [FreeChain, FreeChainF, freeChain_iff s nodes rest]

def HtabBlocks {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) : Prop :=
  (∀ i ∈ htabFootprint s t, Inside i sourceBase heapEnd ∧ WordsOK s i) ∧
  (htabFootprint s t).Pairwise Disj ∧
  1 ≤ hdr s t 0 ∧ hdr s t 0 ≤ maxKeyLen ∧ hdr s t 1 = (hdr s t 0 + 7) / 8 * 8 ∧
  2 ≤ hdr s t 10 ∧ 1 ≤ hdr s t 8 ∧ hdr s t 8 ≤ hdr s t 10 + 1

theorem htabWF_iff {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) :
    HtabWF s t ↔ HtabBlocks s t ∧ ∃ L I Fr : List Nat,
      TreeWF L I Fr (hdr s t 8) (hdr s t 0) (hdr s t 3) (hdr s t 7) (hdr s t 9)
        (nodeF s (hdr s t 5)) (fun i => memW s (hdr s t 6 + 8 * i)) := by
  simp only [HtabWF, HtabBlocks, TreeWF, freeChain_iff]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, h⟩
    exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, h⟩
  · rintro ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, h⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, h⟩

/-- Overwriting leaf value (+8) preserves `TreeWF`. -/
theorem TreeWF.overwrite_leaf_value {L I Fr : List Nat} {next klen cnt root free : Nat}
    {nd nd' : Nat → Nat → Nat} {ord ord' : Nat → Nat}
    (h : TreeWF L I Fr next klen cnt root free nd ord)
    (h0 : ∀ n ∈ L ++ I ++ Fr, nd' n 0 = nd n 0)
    (hnd16 : ∀ n ∈ L ++ I, nd' n 16 = nd n 16)
    (hnd24 : ∀ n ∈ L ++ I, nd' n 24 = nd n 24)
    (h8i : ∀ n ∈ I, nd' n 8 = nd n 8)
    (horder : ∀ i, i < L.length → ord' i = ord i) :
    TreeWF L I Fr next klen cnt root free nd' ord' := by
  obtain ⟨hlen, hnodup, hmem, hcI, hord, hint, hr0, hr1, hrc, hpar, hdep, hfree⟩ := h
  refine ⟨hlen, hnodup, hmem, hcI, ?_, ?_, hr0, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hiord, h24, h16⟩ := hord i hi
    exact ⟨(horder i hi).trans hiord, (hnd24 _ (by simp [List.getElem_mem])).trans h24,
      (hnd16 _ (by simp [List.getElem_mem])).trans h16⟩
  · intro n hn
    obtain ⟨h24, h8, h16, hne, hpar8, hpar16⟩ := hint n hn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnd24 n (by simp [hn])]; exact h24
    · rw [h8i n hn]; exact h8
    · rw [hnd16 n (by simp [hn])]; exact h16
    · rw [h8i n hn, hnd16 n (by simp [hn])]; exact hne
    · calc
        nd' (nd' n 8) 0 = nd (nd' n 8) 0 := h0 _ (by
          rw [h8i n hn]; simp only [List.mem_append]; exact Or.inl (List.mem_append.mp h8))
        _ = nd (nd n 8) 0 := by rw [h8i n hn]
        _ = n := hpar8
    · calc
        nd' (nd' n 16) 0 = nd (nd' n 16) 0 := h0 _ (by
          rw [hnd16 n (by simp [hn])]; simp only [List.mem_append]; exact Or.inl (List.mem_append.mp h16))
        _ = nd (nd n 16) 0 := by rw [hnd16 n (by simp [hn])]
        _ = n := hpar16
  · intro hcnt
    obtain ⟨hroot, hzero⟩ := hr1 hcnt
    exact ⟨hroot, (h0 _ (by simp only [List.mem_append]; exact Or.inl (List.mem_append.mp hroot))).trans hzero⟩
  · intro n hn
    obtain ⟨h8, h16⟩ := hrc n hn
    exact ⟨by rw [h8i n hn]; exact h8, by rw [hnd16 n (by simp [hn])]; exact h16⟩
  · intro n hn hnr
    rw [h0 n (by simp only [List.mem_append]; exact Or.inl (List.mem_append.mp hn))]
    exact hpar n hn hnr
  · obtain ⟨dep, hd⟩ := hdep
    refine ⟨dep, fun n hn hnr => ?_⟩
    obtain ⟨hchild, hlt⟩ := hd n hn hnr
    have hp : nd n 0 ∈ I := hpar n hn hnr
    refine ⟨by
      rcases hchild with hchild | hchild
      · left
        calc
          nd' (nd' n 0) 8 = nd' (nd n 0) 8 := by
            rw [h0 n (by simp only [List.mem_append]; exact Or.inl (List.mem_append.mp hn))]
          _ = nd (nd n 0) 8 := h8i _ hp
          _ = n := hchild
      · right
        calc
          nd' (nd' n 0) 16 = nd' (nd n 0) 16 := by
            rw [h0 n (by simp only [List.mem_append]; exact Or.inl (List.mem_append.mp hn))]
          _ = nd (nd n 0) 16 := hnd16 _ (by simp [hp])
          _ = n := hchild, by
            rw [h0 n (by simp only [List.mem_append]; exact Or.inl (List.mem_append.mp hn))]
            exact hlt⟩
  · apply FreeChainF.congr Fr free
    · intro f hf; exact h0 f (by simp [hf])
    · exact hfree

/-- Empty table (`cnt = 0`): inserting sole leaf `nl`. -/
theorem TreeWF.insert_empty {Fr' : List Nat} {next' klen free' nl : Nat}
    {nd' : Nat → Nat → Nat} {ord' : Nat → Nat}
    (hnd_fr : (nl :: Fr').Nodup)
    (hmem_fr : ∀ x, x ∈ nl :: Fr' ↔ 1 ≤ x ∧ x < next')
    (hfc : FreeChainF nd' free' Fr')
    (hord0 : ord' 0 = nl)
    (hnl0 : nd' nl 0 = 0)
    (hnl16 : nd' nl 16 = 0)
    (hnl24 : nd' nl 24 = 8 * klen) :
    TreeWF [nl] [] Fr' next' klen 1 nl free' nd' ord' := by
  refine ⟨by simp, by simpa using hnd_fr, by simpa using hmem_fr, Or.inr (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfc⟩
  · intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    exact ⟨hord0, hnl24, hnl16⟩
  · intro n hn; simp at hn
  · intro h; omega
  · intro _; exact ⟨by simp, hnl0⟩
  · intro n hn; simp at hn
  · intro n hn hnr
    simp at hn; subst hn; exact absurd rfl hnr
  · exact ⟨fun _ => 0, fun n hn hnr => by simp at hn; subst hn; exact absurd rfl hnr⟩

/-- Splicing internal node `ni` (at bit `d < 8 * klen`) and leaf `nl` above live node `n0` under `p0`. -/
theorem TreeWF.insert_splice {L I Fr' : List Nat} {next' klen cnt root free' nl ni n0 p0 d : Nat}
    {nd nd' : Nat → Nat → Nat} {ord ord' : Nat → Nat}
    (hLlen : L.length = cnt)
    (hcnt_pos : 0 < cnt)
    (hnodup_new : ((L ++ [nl]) ++ (I ++ [ni]) ++ Fr').Nodup)
    (hmem_new : ∀ x, x ∈ (L ++ [nl]) ++ (I ++ [ni]) ++ Fr' ↔ 1 ≤ x ∧ x < next')
    (hcI : (cnt = 0 ∧ I = []) ∨ I.length + 1 = cnt)
    (hord : ∀ (i : Nat) (h : i < L.length), ord i = L[i] ∧ nd L[i] 24 = 8 * klen ∧ nd L[i] 16 = i)
    (hint : ∀ x ∈ I, nd x 24 < 8 * klen ∧ nd x 8 ∈ L ++ I ∧ nd x 16 ∈ L ++ I ∧ nd x 8 ≠ nd x 16 ∧
      nd (nd x 8) 0 = x ∧ nd (nd x 16) 0 = x)
    (hr1 : 0 < cnt → root ∈ L ++ I ∧ nd root 0 = 0)
    (hrc : ∀ x ∈ I, nd x 8 ≠ root ∧ nd x 16 ≠ root)
    (hpar : ∀ x ∈ L ++ I, x ≠ root → nd x 0 ∈ I)
    (hdep : ∃ dep : Nat → Nat, ∀ x ∈ L ++ I, x ≠ root →
      (nd (nd x 0) 8 = x ∨ nd (nd x 0) 16 = x) ∧ dep (nd x 0) < dep x)
    (hfc' : FreeChainF nd' free' Fr')
    (hd_lt : d < 8 * klen)
    (hn0 : n0 ∈ L ++ I)
    (hp0_spec : (p0 = 0 ∧ n0 = root) ∨ (p0 ∈ I ∧ n0 ≠ root ∧ p0 = nd n0 0))
    (hord_old : ∀ i, i < L.length → ord' i = ord i)
    (hord_new : ord' cnt = nl)
    (hnl_0 : nd' nl 0 = ni)
    (hnl_16 : nd' nl 16 = cnt)
    (hnl_24 : nd' nl 24 = 8 * klen)
    (hni_0 : nd' ni 0 = p0)
    (hni_24 : nd' ni 24 = d)
    (hni_ch : (nd' ni 8 = nl ∧ nd' ni 16 = n0) ∨ (nd' ni 8 = n0 ∧ nd' ni 16 = nl))
    (hn0_0 : nd' n0 0 = ni)
    (hother_0 : ∀ x ∈ L ++ I, x ≠ n0 → nd' x 0 = nd x 0)
    (hother_24 : ∀ x ∈ L ++ I, nd' x 24 = nd x 24)
    (hleaf_16 : ∀ x ∈ L, nd' x 16 = nd x 16)
    (hint_other : ∀ x ∈ I, x ≠ p0 → nd' x 8 = nd x 8 ∧ nd' x 16 = nd x 16)
    (hp0_ch : p0 ≠ 0 →
      (nd p0 8 = n0 → nd' p0 8 = ni ∧ nd' p0 16 = nd p0 16) ∧
      (nd p0 8 ≠ n0 → nd' p0 8 = nd p0 8 ∧ nd' p0 16 = ni)) :
    TreeWF (L ++ [nl]) (I ++ [ni]) Fr' next' klen (cnt + 1) (if p0 = 0 then ni else root) free' nd' ord' := by
  obtain ⟨dep, hd⟩ := hdep
  obtain ⟨hroot_LI, hroot_0⟩ := hr1 hcnt_pos
  have hI_len : I.length + 1 = cnt := by
    rcases hcI with ⟨hc0, _⟩ | h1
    · omega
    · exact h1
  have hnd_all := (List.nodup_append.mp hnodup_new).1
  have hnd_L_nl := (List.nodup_append.mp hnd_all).1
  have hnd_I_ni := (List.nodup_append.mp hnd_all).2.1
  have hdisj_LI := (List.nodup_append.mp hnd_all).2.2
  have hnl_not_L : nl ∉ L := fun h => (List.nodup_append.mp hnd_L_nl).2.2 nl h nl (by simp) rfl
  have hnl_not_I : nl ∉ I := fun h => hdisj_LI nl (by simp) nl (by simp [h]) rfl
  have hni_not_L : ni ∉ L := fun h => hdisj_LI ni (by simp [h]) ni (by simp) rfl
  have hni_not_I : ni ∉ I := fun h => (List.nodup_append.mp hnd_I_ni).2.2 ni h ni (by simp) rfl
  have hnl_ne_ni : nl ≠ ni := fun h => hdisj_LI nl (by simp) ni (by simp) h
  have hn0_ne_nl : n0 ≠ nl := by
    rintro rfl
    rcases List.mem_append.mp hn0 with h | h
    · exact hnl_not_L h
    · exact hnl_not_I h
  have hn0_ne_ni : n0 ≠ ni := by
    rintro rfl
    rcases List.mem_append.mp hn0 with h | h
    · exact hni_not_L h
    · exact hni_not_I h
  have hroot_ne_nl : root ≠ nl := by
    rintro rfl
    rcases List.mem_append.mp hroot_LI with h | h
    · exact hnl_not_L h
    · exact hnl_not_I h
  have hroot_ne_ni : root ≠ ni := by
    rintro rfl
    rcases List.mem_append.mp hroot_LI with h | h
    · exact hni_not_L h
    · exact hni_not_I h
  have mem_new_of_old : ∀ x ∈ L ++ I, x ∈ (L ++ [nl]) ++ (I ++ [ni]) := by
    intro x hx
    rcases List.mem_append.mp hx with hL | hI
    · exact List.mem_append_left _ (List.mem_append_left _ hL)
    · exact List.mem_append_right _ (List.mem_append_left _ hI)
  have hnl_mem_new : nl ∈ (L ++ [nl]) ++ (I ++ [ni]) :=
    List.mem_append_left _ (List.mem_append_right _ (by simp))
  have hni_mem_new : ni ∈ (L ++ [nl]) ++ (I ++ [ni]) :=
    List.mem_append_right _ (List.mem_append_right _ (by simp))
  have hp0_child_old : p0 ≠ 0 → nd p0 8 = n0 ∨ nd p0 16 = n0 := by
    intro hp0_nz
    rcases hp0_spec with ⟨hp0z, _⟩ | ⟨_, hn0_nr, hp0_eq⟩
    · exact absurd hp0z hp0_nz
    · rw [hp0_eq]
      exact (hd n0 hn0 hn0_nr).1
  refine ⟨by simp [hLlen], hnodup_new, hmem_new, Or.inr (by simp [hI_len]), ?_, ?_,
    fun h => by omega, ?_, ?_, ?_, ?_, hfc'⟩
  · intro i hi
    simp only [List.length_append, List.length_singleton, hLlen] at hi
    by_cases hlt : i < L.length
    · rw [List.getElem_append_left hlt]
      obtain ⟨ho, h24, h16⟩ := hord i hlt
      have hmemL : L[i] ∈ L := List.getElem_mem hlt
      have hmemLI : L[i] ∈ L ++ I := List.mem_append_left _ hmemL
      exact ⟨(hord_old i hlt).trans ho, (hother_24 _ hmemLI).trans h24, (hleaf_16 _ hmemL).trans h16⟩
    · have hi_eq : i = cnt := by omega
      subst i
      have hget : (L ++ [nl])[cnt]'(by simp [hLlen]) = nl := by
        simp [List.getElem_append_right (by omega : L.length ≤ cnt), hLlen]
      rw [hget]
      exact ⟨hord_new, hnl_24, hnl_16⟩
  · intro x hx
    rcases List.mem_append.mp hx with hxI | hx_ni
    · obtain ⟨hx24, hx8, hx16, hxne, hx8p, hx16p⟩ := hint x hxI
      have hxLI : x ∈ L ++ I := List.mem_append_right _ hxI
      by_cases hxp : x = p0
      · subst hxp
        have hp0_nz : x ≠ 0 := by
          rintro rfl
          have := (hmem_new 0).mp (List.mem_append_left _ (mem_new_of_old 0 hxLI))
          omega
        have hch := hp0_ch hp0_nz
        have hchild := hp0_child_old hp0_nz
        by_cases h8eq : nd x 8 = n0
        · obtain ⟨hp8', hp16'⟩ := hch.1 h8eq
          have h16_ne_n0 : nd x 16 ≠ n0 := by rw [← h8eq]; exact Ne.symm hxne
          have h16_ne_ni : nd x 16 ≠ ni := by
            intro h
            rcases List.mem_append.mp hx16 with hL | hI
            · exact hni_not_L (h ▸ hL)
            · exact hni_not_I (h ▸ hI)
          refine ⟨by rw [hother_24 x hxLI]; exact hx24, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hp8']; exact hni_mem_new
          · rw [hp16']; exact mem_new_of_old _ hx16
          · rw [hp8', hp16']; exact Ne.symm h16_ne_ni
          · rw [hp8', hni_0]
          · rw [hp16', hother_0 _ hx16 h16_ne_n0, hx16p]
        · obtain ⟨hp8', hp16'⟩ := hch.2 h8eq
          have h8_ne_ni : nd x 8 ≠ ni := by
            intro h
            rcases List.mem_append.mp hx8 with hL | hI
            · exact hni_not_L (h ▸ hL)
            · exact hni_not_I (h ▸ hI)
          refine ⟨by rw [hother_24 x hxLI]; exact hx24, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hp8']; exact mem_new_of_old _ hx8
          · rw [hp16']; exact hni_mem_new
          · rw [hp8', hp16']; exact h8_ne_ni
          · rw [hp8', hother_0 _ hx8 h8eq, hx8p]
          · rw [hp16', hni_0]
      · obtain ⟨hx8', hx16'⟩ := hint_other x hxI hxp
        have hx8_ne_n0 : nd x 8 ≠ n0 := by
          intro h
          rcases hp0_spec with ⟨_, hn0r⟩ | ⟨_, _, hp0_eq⟩
          · exact (hrc x hxI).1 (h.trans hn0r)
          · apply hxp; rw [hp0_eq, ← h, hx8p]
        have hx16_ne_n0 : nd x 16 ≠ n0 := by
          intro h
          rcases hp0_spec with ⟨_, hn0r⟩ | ⟨_, _, hp0_eq⟩
          · exact (hrc x hxI).2 (h.trans hn0r)
          · apply hxp; rw [hp0_eq, ← h, hx16p]
        refine ⟨by rw [hother_24 x hxLI]; exact hx24, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hx8']; exact mem_new_of_old _ hx8
        · rw [hx16']; exact mem_new_of_old _ hx16
        · rw [hx8', hx16']; exact hxne
        · rw [hx8', hother_0 _ hx8 hx8_ne_n0, hx8p]
        · rw [hx16', hother_0 _ hx16 hx16_ne_n0, hx16p]
    · simp at hx_ni; subst hx_ni
      refine ⟨by rw [hni_24]; exact hd_lt, ?_, ?_, ?_, ?_, ?_⟩
      · rcases hni_ch with ⟨h8, _⟩ | ⟨h8, _⟩
        · rw [h8]; exact hnl_mem_new
        · rw [h8]; exact mem_new_of_old _ hn0
      · rcases hni_ch with ⟨_, h16⟩ | ⟨_, h16⟩
        · rw [h16]; exact mem_new_of_old _ hn0
        · rw [h16]; exact hnl_mem_new
      · rcases hni_ch with ⟨h8, h16⟩ | ⟨h8, h16⟩
        · rw [h8, h16]; exact Ne.symm hn0_ne_nl
        · rw [h8, h16]; exact hn0_ne_nl
      · rcases hni_ch with ⟨h8, _⟩ | ⟨h8, _⟩
        · rw [h8, hnl_0]
        · rw [h8, hn0_0]
      · rcases hni_ch with ⟨_, h16⟩ | ⟨_, h16⟩
        · rw [h16, hn0_0]
        · rw [h16, hnl_0]
  · intro _
    by_cases hp0z : p0 = 0
    · rw [if_pos hp0z, hni_0, hp0z]
      exact ⟨hni_mem_new, rfl⟩
    · rw [if_neg hp0z]
      rcases hp0_spec with ⟨h0, _⟩ | ⟨_, hn0_nr, _⟩
      · exact absurd h0 hp0z
      · exact ⟨mem_new_of_old _ hroot_LI, (hother_0 root hroot_LI (Ne.symm hn0_nr)).trans hroot_0⟩
  · intro x hx
    by_cases hp0z : p0 = 0
    · rw [if_pos hp0z]
      rcases List.mem_append.mp hx with hxI | hx_ni
      · have hxp : x ≠ p0 := by
          rw [hp0z]; intro h0; subst h0
          have := (hmem_new 0).mp (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hxI)))
          omega
        obtain ⟨hx8', hx16'⟩ := hint_other x hxI hxp
        rw [hx8', hx16']
        obtain ⟨_, hx8, hx16, _, _, _⟩ := hint x hxI
        constructor
        · intro h; rcases List.mem_append.mp hx8 with hL | hI
          · exact hni_not_L (h ▸ hL)
          · exact hni_not_I (h ▸ hI)
        · intro h; rcases List.mem_append.mp hx16 with hL | hI
          · exact hni_not_L (h ▸ hL)
          · exact hni_not_I (h ▸ hI)
      · simp at hx_ni; subst hx_ni
        rcases hni_ch with ⟨h8, h16⟩ | ⟨h8, h16⟩
        · rw [h8, h16]; exact ⟨hnl_ne_ni, hn0_ne_ni⟩
        · rw [h8, h16]; exact ⟨hn0_ne_ni, hnl_ne_ni⟩
    · rw [if_neg hp0z]
      rcases hp0_spec with ⟨h0, _⟩ | ⟨hp0I, hn0_nr, _⟩
      · exact absurd h0 hp0z
      · rcases List.mem_append.mp hx with hxI | hx_ni
        · by_cases hxp : x = p0
          · subst hxp
            have hch := hp0_ch hp0z
            by_cases h8eq : nd x 8 = n0
            · obtain ⟨hp8', hp16'⟩ := hch.1 h8eq
              rw [hp8', hp16']
              exact ⟨Ne.symm hroot_ne_ni, (hrc x hxI).2⟩
            · obtain ⟨hp8', hp16'⟩ := hch.2 h8eq
              rw [hp8', hp16']
              exact ⟨(hrc x hxI).1, Ne.symm hroot_ne_ni⟩
          · obtain ⟨hx8', hx16'⟩ := hint_other x hxI hxp
            rw [hx8', hx16']
            exact hrc x hxI
        · simp at hx_ni; subst hx_ni
          rcases hni_ch with ⟨h8, h16⟩ | ⟨h8, h16⟩
          · rw [h8, h16]; exact ⟨Ne.symm hroot_ne_nl, hn0_nr⟩
          · rw [h8, h16]; exact ⟨hn0_nr, Ne.symm hroot_ne_nl⟩
  · intro x hx hxr
    have hni_in : ni ∈ I ++ [ni] := List.mem_append_right _ (by simp)
    rcases List.mem_append.mp hx with hxL_nl | hxI_ni
    · rcases List.mem_append.mp hxL_nl with hxL | hx_nl
      · by_cases hxn0 : x = n0
        · subst hxn0; rw [hn0_0]; exact hni_in
        · rw [hother_0 x (List.mem_append_left _ hxL) hxn0]
          by_cases hp0z : p0 = 0
          · rcases hp0_spec with ⟨_, rfl⟩ | ⟨hp0I, _, _⟩
            · exact List.mem_append_left _ (hpar x (List.mem_append_left _ hxL) hxn0)
            · subst hp0z
              have := (hmem_new 0).mp (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hp0I)))
              omega
          · rw [if_neg hp0z] at hxr
            exact List.mem_append_left _ (hpar x (List.mem_append_left _ hxL) hxr)
      · simp at hx_nl; subst hx_nl; rw [hnl_0]; exact hni_in
    · rcases List.mem_append.mp hxI_ni with hxI | hx_ni
      · by_cases hxn0 : x = n0
        · subst hxn0; rw [hn0_0]; exact hni_in
        · rw [hother_0 x (List.mem_append_right _ hxI) hxn0]
          by_cases hp0z : p0 = 0
          · rcases hp0_spec with ⟨_, rfl⟩ | ⟨hp0I, _, _⟩
            · exact List.mem_append_left _ (hpar x (List.mem_append_right _ hxI) hxn0)
            · subst hp0z
              have := (hmem_new 0).mp (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hp0I)))
              omega
          · rw [if_neg hp0z] at hxr
            exact List.mem_append_left _ (hpar x (List.mem_append_right _ hxI) hxr)
      · simp at hx_ni; subst hx_ni
        by_cases hp0z : p0 = 0
        · rw [if_pos hp0z] at hxr; exact absurd rfl hxr
        · rcases hp0_spec with ⟨h0, _⟩ | ⟨hp0I, _, _⟩
          · exact absurd h0 hp0z
          · rw [hni_0]; exact List.mem_append_left _ hp0I
  · by_cases hp0z : p0 = 0
    · rw [if_pos hp0z]
      have hn0_root : n0 = root := by
        rcases hp0_spec with ⟨_, hr⟩ | ⟨hp0I, _, _⟩
        · exact hr
        · subst hp0z
          have := (hmem_new 0).mp (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hp0I)))
          omega
      refine ⟨fun x => if x = ni then 0 else if x = nl then 1 else dep x + 1, ?_⟩
      intro x hx hxr
      rcases List.mem_append.mp hx with hxL_nl | hxI_ni
      · rcases List.mem_append.mp hxL_nl with hxL | hx_nl
        · have hx_ne_ni : x ≠ ni := fun h => hni_not_L (h ▸ hxL)
          have hx_ne_nl : x ≠ nl := fun h => hnl_not_L (h ▸ hxL)
          by_cases hxn0 : x = n0
          · subst hxn0
            rw [hn0_0]
            refine ⟨?_, by simp [hx_ne_ni, hx_ne_nl]⟩
            rcases hni_ch with ⟨_, h16⟩ | ⟨h8, _⟩
            · exact Or.inr h16
            · exact Or.inl h8
          · have hxLI : x ∈ L ++ I := List.mem_append_left _ hxL
            have hx_nr : x ≠ root := hn0_root ▸ hxn0
            have hpI : nd x 0 ∈ I := hpar x hxLI hx_nr
            have hp_ne_p0 : nd x 0 ≠ p0 := by
              rw [hp0z]; intro h0
              have := (hmem_new 0).mp (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (h0 ▸ hpI))))
              omega
            have hp_ne_ni : nd x 0 ≠ ni := fun h => hni_not_I (h ▸ hpI)
            have hp_ne_nl : nd x 0 ≠ nl := fun h => hnl_not_I (h ▸ hpI)
            obtain ⟨hp8', hp16'⟩ := hint_other (nd x 0) hpI hp_ne_p0
            obtain ⟨hch_old, hlt_old⟩ := hd x hxLI hx_nr
            rw [hother_0 x hxLI hxn0, hp8', hp16']
            exact ⟨hch_old, by simp [hx_ne_ni, hx_ne_nl, hp_ne_ni, hp_ne_nl]; omega⟩
        · simp at hx_nl; subst hx_nl
          rw [hnl_0]
          refine ⟨?_, by simp [hnl_ne_ni]⟩
          rcases hni_ch with ⟨h8, _⟩ | ⟨_, h16⟩
          · exact Or.inl h8
          · exact Or.inr h16
      · rcases List.mem_append.mp hxI_ni with hxI | hx_ni
        · have hx_ne_ni : x ≠ ni := fun h => hni_not_I (h ▸ hxI)
          have hx_ne_nl : x ≠ nl := fun h => hnl_not_I (h ▸ hxI)
          by_cases hxn0 : x = n0
          · subst hxn0
            rw [hn0_0]
            refine ⟨?_, by simp [hx_ne_ni, hx_ne_nl]⟩
            rcases hni_ch with ⟨_, h16⟩ | ⟨h8, _⟩
            · exact Or.inr h16
            · exact Or.inl h8
          · have hxLI : x ∈ L ++ I := List.mem_append_right _ hxI
            have hx_nr : x ≠ root := hn0_root ▸ hxn0
            have hpI : nd x 0 ∈ I := hpar x hxLI hx_nr
            have hp_ne_p0 : nd x 0 ≠ p0 := by
              rw [hp0z]; intro h0
              have := (hmem_new 0).mp (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (h0 ▸ hpI))))
              omega
            have hp_ne_ni : nd x 0 ≠ ni := fun h => hni_not_I (h ▸ hpI)
            have hp_ne_nl : nd x 0 ≠ nl := fun h => hnl_not_I (h ▸ hpI)
            obtain ⟨hp8', hp16'⟩ := hint_other (nd x 0) hpI hp_ne_p0
            obtain ⟨hch_old, hlt_old⟩ := hd x hxLI hx_nr
            rw [hother_0 x hxLI hxn0, hp8', hp16']
            exact ⟨hch_old, by simp [hx_ne_ni, hx_ne_nl, hp_ne_ni, hp_ne_nl]; omega⟩
        · simp at hx_ni; exact absurd hx_ni hxr
    · rw [if_neg hp0z]
      rcases hp0_spec with ⟨h0, _⟩ | ⟨hp0I, hn0_nr, hp0_eq⟩
      · exact absurd h0 hp0z
      have hp0_ne_ni : p0 ≠ ni := fun h => hni_not_I (h ▸ hp0I)
      have hp0_ne_nl : p0 ≠ nl := fun h => hnl_not_I (h ▸ hp0I)
      have hdep_p0_n0 : dep p0 < dep n0 := by
        rw [hp0_eq]; exact (hd n0 hn0 hn0_nr).2
      refine ⟨fun x => if x = ni then 2 * dep p0 + 1 else if x = nl then 2 * dep p0 + 2 else 2 * dep x, ?_⟩
      intro x hx hxr
      have helper_old : ∀ (y : Nat), y ∈ L ++ I → y ≠ n0 → y ≠ root → y ≠ ni → y ≠ nl →
          ((nd' (nd' y 0) 8 = y ∨ nd' (nd' y 0) 16 = y) ∧
            (if nd' y 0 = ni then 2 * dep p0 + 1 else if nd' y 0 = nl then 2 * dep p0 + 2 else 2 * dep (nd' y 0)) <
            (if y = ni then 2 * dep p0 + 1 else if y = nl then 2 * dep p0 + 2 else 2 * dep y)) := by
        intro y hyLI hyn0 hyr hy_ni hy_nl
        have hpI : nd y 0 ∈ I := hpar y hyLI hyr
        have hp_ne_ni : nd y 0 ≠ ni := fun h => hni_not_I (h ▸ hpI)
        have hp_ne_nl : nd y 0 ≠ nl := fun h => hnl_not_I (h ▸ hpI)
        obtain ⟨hch_old, hlt_old⟩ := hd y hyLI hyr
        rw [hother_0 y hyLI hyn0]
        refine ⟨?_, by simp [hy_ni, hy_nl, hp_ne_ni, hp_ne_nl]; omega⟩
        by_cases hpp0 : nd y 0 = p0
        · rw [hpp0] at hch_old ⊢
          have hch := hp0_ch hp0z
          by_cases h8eq : nd p0 8 = n0
          · obtain ⟨_, hp16'⟩ := hch.1 h8eq
            rcases hch_old with h8y | h16y
            · exact absurd (h8y.symm.trans h8eq) hyn0
            · exact Or.inr (hp16'.trans h16y)
          · obtain ⟨hp8', _⟩ := hch.2 h8eq
            rcases hch_old with h8y | h16y
            · exact Or.inl (hp8'.trans h8y)
            · have h16n0 : nd p0 16 = n0 := (hp0_child_old hp0z).resolve_left h8eq
              exact absurd (h16y.symm.trans h16n0) hyn0
        · obtain ⟨hp8', hp16'⟩ := hint_other (nd y 0) hpI hpp0
          rw [hp8', hp16']
          exact hch_old
      rcases List.mem_append.mp hx with hxL_nl | hxI_ni
      · rcases List.mem_append.mp hxL_nl with hxL | hx_nl
        · have hx_ne_ni : x ≠ ni := fun h => hni_not_L (h ▸ hxL)
          have hx_ne_nl : x ≠ nl := fun h => hnl_not_L (h ▸ hxL)
          by_cases hxn0 : x = n0
          · subst hxn0
            rw [hn0_0]
            refine ⟨?_, by simp [hx_ne_ni, hx_ne_nl]; omega⟩
            rcases hni_ch with ⟨_, h16⟩ | ⟨h8, _⟩
            · exact Or.inr h16
            · exact Or.inl h8
          · exact helper_old x (List.mem_append_left _ hxL) hxn0 hxr hx_ne_ni hx_ne_nl
        · simp at hx_nl; subst hx_nl
          rw [hnl_0]
          refine ⟨?_, by simp [hnl_ne_ni]⟩
          rcases hni_ch with ⟨h8, _⟩ | ⟨_, h16⟩
          · exact Or.inl h8
          · exact Or.inr h16
      · rcases List.mem_append.mp hxI_ni with hxI | hx_ni
        · have hx_ne_ni : x ≠ ni := fun h => hni_not_I (h ▸ hxI)
          have hx_ne_nl : x ≠ nl := fun h => hnl_not_I (h ▸ hxI)
          by_cases hxn0 : x = n0
          · subst hxn0
            rw [hn0_0]
            refine ⟨?_, by simp [hx_ne_ni, hx_ne_nl]; omega⟩
            rcases hni_ch with ⟨_, h16⟩ | ⟨h8, _⟩
            · exact Or.inr h16
            · exact Or.inl h8
          · exact helper_old x (List.mem_append_right _ hxI) hxn0 hxr hx_ne_ni hx_ne_nl
        · simp at hx_ni; subst hx_ni
          rw [hni_0]
          refine ⟨?_, by simp [hp0_ne_ni, hp0_ne_nl]⟩
          have hch := hp0_ch hp0z
          by_cases h8eq : nd p0 8 = n0
          · exact Or.inl (hch.1 h8eq).1
          · exact Or.inr (hch.2 h8eq).2

/-! ## 6. Byte-level semantics of `memcpy`, `memeq`, and `htab_first_diff` -/

theorem panMemStoreByte_other_byte {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {be : Bool}
    {addr : BitVec 64} {bw : BitVec 8} {mem' : BitVec 64 → HolWordLab 64}
    (hst : panMemStoreByteWord8HOL mem dom be addr bw = some mem') :
    ((match mem' (panByteAlignHOL addr) with | .word v => (panGetByteHOL addr v be).toNat) = bw.toNat) ∧
    (∀ addr' : BitVec 64, addr' ≠ addr →
      (match mem' (panByteAlignHOL addr') with | .word v => (panGetByteHOL addr' v be).toNat) =
      (match mem (panByteAlignHOL addr') with | .word v => (panGetByteHOL addr' v be).toNat)) := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hcell : mem (panByteAlignHOL addr) with
  | word cell =>
    rw [hcell] at hst
    split at hst
    · injection hst with hmem
      subst hmem
      let b : UInt8 := UInt8.ofNat bw.toNat
      have hb8 : b.toNat < 256 := b.toNat_lt_size
      have hbw_eq : bw.toNat = b.toNat := by
        have := bw.isLt
        simp [b, UInt8.toNat_ofNat']
      have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
      have h256_pow : ∀ a : BitVec 64,
          (256 : Nat) ^ (if be then 8 - 1 - a.toNat % 8 else a.toNat % 8) = 2 ^ byteBitIndex a be := by
        intro a
        rw [pow256_eq_two_pow_mul]
        cases be <;> simp [byteBitIndex]
      have hpow_div : ∀ (x y z K : Nat), y < 256 → z < 2 ^ K →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ K % 256 = y := by
        intro x y z K hy hz
        have hpK : 0 < 2 ^ K := Nat.two_pow_pos K
        have h1 : x * 2 ^ (K + 8) + y * 2 ^ K + z = z + (y + x * 256) * 2 ^ K := by
          rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.add_mul,
            Nat.mul_assoc x 256 (2 ^ K), Nat.mul_comm 256 (2 ^ K), ← Nat.mul_assoc]
          omega
        rw [h1, Nat.add_mul_div_right _ _ hpK, Nat.div_eq_of_lt hz, Nat.zero_add]
        omega
      have hpow_div_low : ∀ (x y z K J : Nat), y < 256 → z < 2 ^ K → J + 8 ≤ K →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 = z / 2 ^ J % 256 := by
        intro x y z K J _ _ hJK
        have hpJ : 0 < 2 ^ J := Nat.two_pow_pos J
        have hdK : 2 ^ K = 2 ^ (K - J - 8) * (256 * 2 ^ J) := by
          have hk_eq : K = (K - J - 8) + 8 + J := by omega
          conv_lhs => rw [hk_eq]
          rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
        have hdK8 : 2 ^ (K + 8) = 2 ^ (K - J) * (256 * 2 ^ J) := by
          have hk_eq : K + 8 = (K - J) + 8 + J := by omega
          conv_lhs => rw [hk_eq]
          rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
        have h1 : x * 2 ^ (K + 8) + y * 2 ^ K + z =
            z + ((x * 2 ^ (K - J) + y * 2 ^ (K - J - 8)) * 256) * 2 ^ J := by
          rw [hdK, hdK8, ← Nat.mul_assoc x, ← Nat.mul_assoc y, ← Nat.add_mul, ← Nat.mul_assoc]
          omega
        rw [h1, Nat.add_mul_div_right _ _ hpJ]
        omega
      have hpow_div_high : ∀ (x y z K J : Nat), y < 256 → z < 2 ^ K → K + 8 ≤ J →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 =
            (x * 2 ^ (K + 8)) / 2 ^ J % 256 := by
        intro x y z K J _ hz hKJ
        have hyz : y * 2 ^ K + z < 2 ^ (K + 8) := by
          have : y * 2 ^ K ≤ 255 * 2 ^ K := Nat.mul_le_mul_right _ (by omega)
          have h2 : 255 * 2 ^ K + 2 ^ K = 2 ^ (K + 8) := by
            rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]; omega
          omega
        have hdJ : 2 ^ J = 2 ^ (K + 8) * 2 ^ (J - (K + 8)) := by
          have hj_eq : J = (K + 8) + (J - (K + 8)) := by omega
          conv_lhs => rw [hj_eq]
          rw [Nat.pow_add]
        have hpK8 : 0 < 2 ^ (K + 8) := Nat.two_pow_pos _
        have hsum : x * 2 ^ (K + 8) + y * 2 ^ K + z = (y * 2 ^ K + z) + x * 2 ^ (K + 8) := by omega
        rw [hsum, hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_right _ _ hpK8, Nat.div_eq_of_lt hyz, Nat.zero_add,
          Nat.mul_div_cancel _ hpK8]
      have hcell_high : ∀ J : Nat, byteBitIndex addr be + 8 ≤ J →
          ((cell.toNat / 2 ^ (byteBitIndex addr be + 8)) * 2 ^ (byteBitIndex addr be + 8)) / 2 ^ J =
            cell.toNat / 2 ^ J := by
        intro J hKJ
        have hdJ : 2 ^ J = 2 ^ (byteBitIndex addr be + 8) * 2 ^ (J - (byteBitIndex addr be + 8)) := by
          have hj_eq : J = (byteBitIndex addr be + 8) + (J - (byteBitIndex addr be + 8)) := by omega
          conv_lhs => rw [hj_eq]
          rw [Nat.pow_add]
        have hpK8 : 0 < 2 ^ (byteBitIndex addr be + 8) := Nat.two_pow_pos _
        rw [hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpK8]
      constructor
      · simp only [↓reduceIte, hbw_eq, panGetByteHOL]
        have heq_nat : (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
            256 ^ (if be then 8 - 1 - addr.toNat % 8 else addr.toNat % 8) % 256 = b.toNat := by
          rw [hset_nat, h256_pow addr]
          exact hpow_div _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _))
        change (UInt8.ofNat ((panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
          256 ^ (if be then 8 - 1 - addr.toNat % 8 else addr.toNat % 8) % 256)).toNat = b.toNat
        rw [heq_nat, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hb8]
      · intro addr' hne
        by_cases hal : panByteAlignHOL addr' = panByteAlignHOL addr
        · simp only [hal, ↓reduceIte, hbw_eq, hcell, panGetByteHOL]
          have hmod_ne : addr'.toNat % 8 ≠ addr.toNat % 8 := by
            intro hmeq
            apply hne
            apply BitVec.eq_of_toNat_eq
            have ha1 := panByteAlign_toNat64 addr'
            have ha2 := panByteAlign_toNat64 addr
            rw [hal] at ha1
            omega
          have hidx_sep : byteBitIndex addr' be + 8 ≤ byteBitIndex addr be ∨
              byteBitIndex addr be + 8 ≤ byteBitIndex addr' be := by
            have hm1 : addr'.toNat % 8 < 8 := by omega
            have hm2 : addr.toNat % 8 < 8 := by omega
            cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
          have heq_mod : (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
              256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 =
            cell.toNat / 256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 := by
            rw [hset_nat, h256_pow addr']
            rcases hidx_sep with hlow | hhigh
            · rw [hpow_div_low _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hlow]
              have hc_eq : 2 ^ byteBitIndex addr be =
                  (2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8)) * 256) *
                    2 ^ byteBitIndex addr' be := by
                have hk_eq : byteBitIndex addr be =
                    (byteBitIndex addr be - (byteBitIndex addr' be + 8)) + 8 + byteBitIndex addr' be := by omega
                conv_lhs => rw [hk_eq]
                rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]
              have hcell_eq : cell.toNat =
                  cell.toNat % 2 ^ byteBitIndex addr be +
                  (((cell.toNat / 2 ^ byteBitIndex addr be) *
                    2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
                    2 ^ byteBitIndex addr' be := by
                have hdm := (Nat.div_add_mod cell.toNat (2 ^ byteBitIndex addr be)).symm
                rw [Nat.mul_comm (2 ^ byteBitIndex addr be)] at hdm
                have hmul : (cell.toNat / 2 ^ byteBitIndex addr be) * 2 ^ byteBitIndex addr be =
                    (((cell.toNat / 2 ^ byteBitIndex addr be) *
                      2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
                      2 ^ byteBitIndex addr' be := by
                  rw [hc_eq, ← Nat.mul_assoc, ← Nat.mul_assoc]
                rw [hmul] at hdm
                omega
              conv_rhs => rw [hcell_eq]
              rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
              omega
            · rw [hpow_div_high _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hhigh,
                hcell_high _ hhigh]
          change (UInt8.ofNat ((panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
              256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256)).toNat =
            (UInt8.ofNat (cell.toNat /
              256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256)).toNat
          rw [heq_mod]
        · simp only [hal, ↓reduceIte]
    · cases hst

theorem nat_eq_of_digits_256_8 {u v : Nat} (hu : u < 2 ^ 64) (hv : v < 2 ^ 64)
    (hd : ∀ r : Nat, r < 8 → u / 256 ^ r % 256 = v / 256 ^ r % 256) : u = v := by
  have hstep : ∀ k : Nat, k ≤ 8 → u % 256 ^ k = v % 256 ^ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      have hklt : k < 8 := by omega
      have hprev := ih (by omega)
      have hdk := hd k hklt
      have hp1 : 256 ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ 256 k
      have hdecomp : ∀ x : Nat, x % 256 ^ (k + 1) = (x / 256 ^ k % 256) * 256 ^ k + x % 256 ^ k := by
        intro x
        rw [hp1]
        have hp_pos : 0 < 256 ^ k := Nat.pos_of_ne_zero (by positivity)
        have hlt_rem : (x / 256 ^ k % 256) * 256 ^ k + x % 256 ^ k < 256 ^ k * 256 := by
          have h1 : x / 256 ^ k % 256 ≤ 255 := by omega
          have h2 : (x / 256 ^ k % 256) * 256 ^ k ≤ 255 * 256 ^ k := Nat.mul_le_mul_right _ h1
          have h3 : x % 256 ^ k < 256 ^ k := Nat.mod_lt _ hp_pos
          omega
        have hx_eq : x = ((x / 256 ^ k % 256) * 256 ^ k + x % 256 ^ k) +
            (x / 256 ^ k / 256) * (256 ^ k * 256) := by
          calc x
            _ = 256 ^ k * (x / 256 ^ k) + x % 256 ^ k := (Nat.div_add_mod x (256 ^ k)).symm
            _ = 256 ^ k * (256 * (x / 256 ^ k / 256) + x / 256 ^ k % 256) + x % 256 ^ k := by
                rw [Nat.div_add_mod (x / 256 ^ k) 256]
            _ = ((x / 256 ^ k % 256) * 256 ^ k + x % 256 ^ k) +
                (x / 256 ^ k / 256) * (256 ^ k * 256) := by
                rw [Nat.left_distrib, Nat.mul_comm (256 ^ k) (x / 256 ^ k % 256),
                  ← Nat.mul_assoc, Nat.mul_comm (256 ^ k * 256) (x / 256 ^ k / 256)]
                omega
        conv_lhs => rw [hx_eq]
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt_rem]
      rw [hdecomp u, hdecomp v, hdk, hprev]
  have h8 := hstep 8 (le_refl 8)
  have hp8 : (256 ^ 8 : Nat) = 2 ^ 64 := by decide
  rw [hp8, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at h8
  exact h8

/-- Two aligned words in memory have equal `memW` iff their 8 `memB` bytes agree (assuming same `be`). -/
theorem memW_eq_iff_memB {F : Type} {s₁ s₂ : PanSemStateFiniteExact 64 F}
    {a₁ a₂ : Nat} (hbe : s₁.be = s₂.be)
    (hal₁ : a₁ % 8 = 0) (hal₂ : a₂ % 8 = 0)
    (h1 : a₁ + 8 < 2 ^ 64) (h2 : a₂ + 8 < 2 ^ 64) :
    memW s₁ a₁ = memW s₂ a₂ ↔
      ∀ r : Nat, r < 8 → memB s₁ (a₁ + r) = memB s₂ (a₂ + r) := by
  have hal_off : ∀ (a r : Nat), a % 8 = 0 → a + 8 < 2 ^ 64 → r < 8 →
      panByteAlignHOL (BitVec.ofNat 64 (a + r)) = BitVec.ofNat 64 a ∧
        (BitVec.ofNat 64 (a + r)).toNat % 8 = r := by
    intro a r ha8 ha_lt hr
    have har : (BitVec.ofNat 64 (a + r)).toNat = a + r := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    refine ⟨?_, by omega⟩
    apply BitVec.eq_of_toNat_eq
    rw [panByteAlign_toNat64, har, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rcases hw1 : s₁.memory (BitVec.ofNat 64 a₁) with ⟨w1⟩
  rcases hw2 : s₂.memory (BitVec.ofNat 64 a₂) with ⟨w2⟩
  simp only [memW, hw1, hw2]
  constructor
  · intro hweq r hr
    obtain ⟨hp1, hm1⟩ := hal_off a₁ r hal₁ h1 hr
    obtain ⟨hp2, hm2⟩ := hal_off a₂ r hal₂ h2 hr
    simp only [memB, hp1, hp2, hw1, hw2, hbe, panGetByteHOL]
    change (UInt8.ofNat (w1.toNat /
        256 ^ (if s₂.be then 8 - 1 - (BitVec.ofNat 64 (a₁ + r)).toNat % 8 else (BitVec.ofNat 64 (a₁ + r)).toNat % 8) % 256)).toNat =
      (UInt8.ofNat (w2.toNat /
        256 ^ (if s₂.be then 8 - 1 - (BitVec.ofNat 64 (a₂ + r)).toNat % 8 else (BitVec.ofNat 64 (a₂ + r)).toNat % 8) % 256)).toNat
    rw [hweq, hm1, hm2]
  · intro hbytes
    apply nat_eq_of_digits_256_8 w1.isLt w2.isLt
    intro k hk
    let be2 := s₂.be
    let r := if be2 then 7 - k else k
    have hr : r < 8 := by cases hbe2 : be2 <;> simp [r, hbe2] <;> omega
    have hidx : (if s₂.be then 8 - 1 - r else r) = k := by
      change (if be2 then 8 - 1 - r else r) = k
      cases hbe2 : be2 <;> simp [r, hbe2] <;> omega
    have hb := hbytes r hr
    obtain ⟨hp1, hm1⟩ := hal_off a₁ r hal₁ h1 hr
    obtain ⟨hp2, hm2⟩ := hal_off a₂ r hal₂ h2 hr
    simp only [memB, hp1, hp2, hw1, hw2, hbe, panGetByteHOL] at hb
    change (UInt8.ofNat (w1.toNat /
        256 ^ (if s₂.be then 8 - 1 - (BitVec.ofNat 64 (a₁ + r)).toNat % 8 else (BitVec.ofNat 64 (a₁ + r)).toNat % 8) % 256)).toNat =
      (UInt8.ofNat (w2.toNat /
        256 ^ (if s₂.be then 8 - 1 - (BitVec.ofNat 64 (a₂ + r)).toNat % 8 else (BitVec.ofNat 64 (a₂ + r)).toNat % 8) % 256)).toNat at hb
    rw [hm1, hm2, hidx, UInt8.toNat_ofNat', UInt8.toNat_ofNat',
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))] at hb
    exact hb

/-! ### 6a. `memeq` postcondition on normal return `0` -/

def LocFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

theorem LocFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrame s s := by
  cases s; rfl

theorem LocFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrame s t) (h2 : LocFrame t u) : LocFrame s u := by
  unfold LocFrame at *
  rw [h2]; rw [h1]

theorem LocFrame.locals {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) : LocFrame s { t with locals := L } := by
  unfold LocFrame at *
  rw [h]

def locOnlyW : ProgHOL 64 → Bool
  | .dec _ _ _ body => locOnlyW body
  | .seq first second => locOnlyW first && locOnlyW second
  | .ite _ yes no => locOnlyW yes && locOnlyW no
  | .while _ body => locOnlyW body
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem locFrameW_eval {F : Type} (p : ProgHOL 64) (hp : locOnlyW p = true)
    (s : PanSemStateFiniteExact 64 F) : LocFrame s (evaluateHOLFiniteState s p).2 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; exact LocFrame.refl s
  | «break» => rw [evaluateHOLFiniteState_break]; exact LocFrame.refl s
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact LocFrame.refl s
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact LocFrame.refl s
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · rfl
      · exact LocFrame.refl s
    · exact LocFrame.refl s
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact LocFrame.refl s
    · split
      · rfl
      · exact LocFrame.refl s
  | assign kind name e =>
    cases kind with
    | global => simp [shape, locOnlyW] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact LocFrame.refl s
      · split
        · rfl
        · exact LocFrame.refl s
  | dec name sh init body =>
    have hb : locOnlyW body = true := by simpa [shape, locOnlyW] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact LocFrame.refl s
    · rename_i val _
      split
      · have ih := locFrameW_eval body hb (setVarHOLFinite name val s)
        unfold LocFrame at ih ⊢
        dsimp only
        rw [ih]; rfl
      · exact LocFrame.refl s
  | seq first second =>
    have h12 : locOnlyW first = true ∧ locOnlyW second = true := by
      simpa [shape, locOnlyW, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ih1 := locFrameW_eval first h12.1 s
    have hle0 := evaluateHOLFiniteState_clock_le s first
    rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
    rw [hr1] at ih1 hle0
    dsimp only at ih1 hle0 ⊢
    have mclk : mid.clock ≤ s.clock := hle0
    cases r1 with
    | none => exact ih1.trans (locFrameW_eval second h12.2 mid)
    | some _ => exact ih1
  | ite cond yes no =>
    have h12 : locOnlyW yes = true ∧ locOnlyW no = true := by
      simpa [shape, locOnlyW, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact locFrameW_eval no h12.2 s
      · exact locFrameW_eval yes h12.1 s
    · exact LocFrame.refl s
  | «while» cond body =>
    have hb : locOnlyW body = true := by simpa [shape, locOnlyW] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := locFrameW_eval body hb (decClockHOLFinite s)
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 hrem
          dsimp only at ih1 hrem
          have hlt : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at hrem; omega
          have h0 : LocFrame s mid := by
            unfold LocFrame at ih1 ⊢
            rw [ih1]; rfl
          cases r1 with
          | none =>
            exact h0.trans (locFrameW_eval (.while cond body) (by simpa [locOnlyW] using hb) mid)
          | some res =>
            cases res with
            | «continue» =>
              exact h0.trans (locFrameW_eval (.while cond body) (by simpa [locOnlyW] using hb) mid)
            | _ => exact h0
      · exact LocFrame.refl s
    · exact LocFrame.refl s
  | _ => simp [shape, locOnlyW] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    try simp only [decClockHOLFinite, setVarHOLFinite]
    first
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

theorem memB_of_eval_loadByte {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (addr : BitVec 64) (v : ValueHOL 64)
    (he : evalAt s e = some (.val (.word addr)))
    (hlb : evalAt s (.loadByte e) = some v) :
    s.memaddrs (panByteAlignHOL addr) ∧
      v = .val (.word (BitVec.ofNat 64 (memB s addr.toNat))) := by
  simp only [evalAt, evalHOLExact, he] at hlb
  by_cases hdom : s.memaddrs (panByteAlignHOL addr)
  · rcases hcell : s.memory (panByteAlignHOL addr) with ⟨w⟩
    have hload : @panMemLoadByteHOL 64 _ s.toExact.memory s.toExact.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.toExact.be addr =
        some (panGetByteHOL addr w s.be) := by
      simp [panMemLoadByteHOL, PanSemStateFiniteExact.toExact, hcell, hdom]
    rw [hload] at hlb
    simp only [Option.map, Option.some.injEq] at hlb
    refine ⟨hdom, ?_⟩
    rw [← hlb]
    congr 2
    simp only [memB, BitVec.ofNat_toNat, BitVec.setWidth_eq, hcell]
  · have hload : @panMemLoadByteHOL 64 _ s.toExact.memory s.toExact.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.toExact.be addr = none := by
      rcases hcell : s.memory (panByteAlignHOL addr) with ⟨w⟩
      simp [panMemLoadByteHOL, PanSemStateFiniteExact.toExact, hcell, hdom]
    rw [hload] at hlb
    simp at hlb

theorem memW_of_eval_load {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (addr : BitVec 64) (v : ValueHOL 64)
    (he : evalAt s e = some (.val (.word addr)))
    (hld : evalAt s (.load .one e) = some v) :
    s.memaddrs addr ∧
      v = .val (.word (BitVec.ofNat 64 (memW s addr.toNat))) := by
  simp only [evalAt, evalHOLExact, he, isWfShapeExactHOL, ↓reduceIte, memLoadHOLExact] at hld
  by_cases hdom : s.memaddrs addr
  · simp only [hdom, ↓reduceIte, Option.some.injEq] at hld
    rcases hcell : s.memory addr with ⟨w⟩
    rw [hcell] at hld
    refine ⟨hdom, ?_⟩
    rw [← hld]
    simp [memW, BitVec.ofNat_toNat, hcell]
  · simp [hdom] at hld

private theorem memeq_word_mismatch {F : Type} (s0 s : PanSemStateFiniteExact 64 F)
    (hfr : LocFrame s0 s) (hG0 : GuestInv s0)
    (ea eb : ExpHOL 64) (pa pb : BitVec 64) (cw : BitVec 64)
    (hea : evalAt s ea = some (.val (.word pa)))
    (heb : evalAt s eb = some (.val (.word pb)))
    (hcmp : evalAt s (.cmp .notEqual (.load .one ea) (.load .one eb)) = some (.val (.word cw)))
    (hcw : cw ≠ 0) :
    ∃ r < 8, pa.toNat + 8 < 2 ^ 64 ∧ pb.toNat + 8 < 2 ^ 64 ∧
      memB s0 (pa.toNat + r) ≠ memB s0 (pb.toNat + r) := by
  obtain ⟨wa, wb, hlda, hldb, hcw_eq⟩ := evalAt_cmp s .notEqual _ _ cw hcmp
  obtain ⟨hdoma, hva⟩ := memW_of_eval_load s ea pa (.val (.word wa)) hea hlda
  obtain ⟨hdomb, hvb⟩ := memW_of_eval_load s eb pb (.val (.word wb)) heb hldb
  have hmem : s.memory = s0.memory := by unfold LocFrame at hfr; rw [hfr]
  have hbe : s.be = s0.be := by unfold LocFrame at hfr; rw [hfr]
  have hma : s.memaddrs = ordinaryDomain := by unfold LocFrame at hfr; rw [hfr]; exact hG0.memaddrs
  have ha_ord : 2701131776 ≤ pa.toNat ∧ pa.toNat < 2701131776 + 8 * 3888119741 ∧ pa.toNat % 8 = 0 := by
    rw [hma, ordinaryDomain_iff] at hdoma; exact hdoma
  have hb_ord : 2701131776 ≤ pb.toNat ∧ pb.toNat < 2701131776 + 8 * 3888119741 ∧ pb.toNat % 8 = 0 := by
    rw [hma, ordinaryDomain_iff] at hdomb; exact hdomb
  have hwa_ne : wa ≠ wb := by
    intro heq; subst heq
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hcw_eq
    exact hcw hcw_eq
  have hmwa : memW s pa.toNat = memW s0 pa.toNat := by simp [memW, hmem]
  have hmwb : memW s pb.toNat = memW s0 pb.toNat := by simp [memW, hmem]
  have hne_memW : memW s0 pa.toNat ≠ memW s0 pb.toNat := by
    intro heq
    apply hwa_ne
    simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at hva hvb
    rw [hva, hvb, hmwa, hmwb, heq]
  have hp8a : pa.toNat + 8 < 2 ^ 64 := by omega
  have hp8b : pb.toNat + 8 < 2 ^ 64 := by omega
  have hnot_all : ¬ ∀ r < 8, memB s0 (pa.toNat + r) = memB s0 (pb.toNat + r) := by
    intro hall
    exact hne_memW ((memW_eq_iff_memB rfl ha_ord.2.2 hb_ord.2.2 hp8a hp8b).mpr hall)
  by_contra hnone
  apply hnot_all
  intro r hr
  by_contra hne_r
  exact hnone ⟨r, hr, hp8a, hp8b, hne_r⟩

private theorem memeq_byte_mismatch {F : Type} (s0 s : PanSemStateFiniteExact 64 F)
    (hfr : LocFrame s0 s) (hG0 : GuestInv s0)
    (ea eb : ExpHOL 64) (pa pb : BitVec 64) (cw : BitVec 64)
    (hea : evalAt s ea = some (.val (.word pa)))
    (heb : evalAt s eb = some (.val (.word pb)))
    (hcmp : evalAt s (.cmp .notEqual (.loadByte ea) (.loadByte eb)) = some (.val (.word cw)))
    (hcw : cw ≠ 0) :
    pa.toNat < 2 ^ 64 ∧ pb.toNat < 2 ^ 64 ∧ memB s0 pa.toNat ≠ memB s0 pb.toNat := by
  obtain ⟨wa, wb, hlba, hlbb, hcw_eq⟩ := evalAt_cmp s .notEqual _ _ cw hcmp
  obtain ⟨_, hva⟩ := memB_of_eval_loadByte s ea pa (.val (.word wa)) hea hlba
  obtain ⟨_, hvb⟩ := memB_of_eval_loadByte s eb pb (.val (.word wb)) heb hlbb
  have hmem : s.memory = s0.memory := by unfold LocFrame at hfr; rw [hfr]
  have hbe : s.be = s0.be := by unfold LocFrame at hfr; rw [hfr]
  have hwa_ne : wa ≠ wb := by
    intro heq; subst heq
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hcw_eq
    exact hcw hcw_eq
  have hmba : memB s pa.toNat = memB s0 pa.toNat := by simp [memB, hmem, hbe]
  have hmbb : memB s pb.toNat = memB s0 pb.toNat := by simp [memB, hmem, hbe]
  refine ⟨pa.isLt, pb.isLt, ?_⟩
  intro heq
  apply hwa_ne
  simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at hva hvb
  rw [hva, hvb, hmba, hmbb, heq]

/-- Helper for `memeq`: if a check `ite (cmp != (load a+off) (load b+off)) (return 0) skip` returns `0`,
then some byte in `[off, off + 8)` differs! -/
private theorem memeq_ite_word_ret0 {F : Type} (s0 s : PanSemStateFiniteExact 64 F)
    (hfr : LocFrame s0 s) (hG0 : GuestInv s0)
    (a b : BitVec 64) (n off : Nat) (hoff : off + 8 ≤ n)
    (ha_nw : a.toNat + off < 2 ^ 64) (hb_nw : b.toNat + off < 2 ^ 64)
    (ea eb : ExpHOL 64)
    (hea : evalAt s ea = some (.val (.word (a + BitVec.ofNat 64 off))))
    (heb : evalAt s eb = some (.val (.word (b + BitVec.ofNat 64 off))))
    (hret : (evaluateHOLFiniteState s
      (.ite (.cmp .notEqual (.load .one ea) (.load .one eb)) (.return (.const 0)) .skip)).1 =
      some (.returned (.val (.word 0)))) :
    ∃ k < n, memB s0 ((a + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((b + BitVec.ofNat 64 k).toNat) := by
  rw [evaluateHOLFiniteState_ite] at hret
  split at hret
  · rename_i cw hcmp
    split at hret
    · simp [evaluateHOLFiniteState_skip] at hret
    · rename_i hcw
      have ha_add : (a + BitVec.ofNat 64 off).toNat = a.toNat + off := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hb_add : (b + BitVec.ofNat 64 off).toNat = b.toNat + off := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      obtain ⟨r, hr, hp8a, hp8b, hne⟩ := memeq_word_mismatch s0 s hfr hG0 ea eb _ _ cw hea heb hcmp hcw
      rw [ha_add] at hp8a hne
      rw [hb_add] at hp8b hne
      refine ⟨off + r, by omega, ?_⟩
      have ha_kr : (a + BitVec.ofNat 64 (off + r)).toNat = a.toNat + off + r := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hb_kr : (b + BitVec.ofNat 64 (off + r)).toNat = b.toNat + off + r := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [ha_kr, hb_kr]
      exact hne
  · simp at hret

private theorem memeq_ite_byte_ret0 {F : Type} (s0 s : PanSemStateFiniteExact 64 F)
    (hfr : LocFrame s0 s) (hG0 : GuestInv s0)
    (a b : BitVec 64) (n off : Nat) (hoff : off < n)
    (ea eb : ExpHOL 64)
    (hea : evalAt s ea = some (.val (.word (a + BitVec.ofNat 64 off))))
    (heb : evalAt s eb = some (.val (.word (b + BitVec.ofNat 64 off))))
    (hret : (evaluateHOLFiniteState s
      (.ite (.cmp .notEqual (.loadByte ea) (.loadByte eb)) (.return (.const 0)) .skip)).1 =
      some (.returned (.val (.word 0)))) :
    ∃ k < n, memB s0 ((a + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((b + BitVec.ofNat 64 k).toNat) := by
  rw [evaluateHOLFiniteState_ite] at hret
  split at hret
  · rename_i cw hcmp
    split at hret
    · simp [evaluateHOLFiniteState_skip] at hret
    · rename_i hcw
      obtain ⟨_, _, hne⟩ := memeq_byte_mismatch s0 s hfr hG0 ea eb _ _ cw hea heb hcmp hcw
      exact ⟨off, hoff, hne⟩
  · simp at hret

private theorem seq_ret_or_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p1 p2 : ProgHOL 64) (v : ValueHOL 64)
    (h : (evaluateHOLFiniteState s (.seq p1 p2)).1 = some (.returned v)) :
    (evaluateHOLFiniteState s p1).1 = some (.returned v) ∨
      ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
        (evaluateHOLFiniteState m p2).1 = some (.returned v) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases hr : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  rw [hr] at h
  cases r1 with
  | none => exact Or.inr ⟨m, rfl, h⟩
  | some r => exact Or.inl h

private def mustNotFlow : ProgHOL 64 → Bool
  | .return _ => true
  | .seq a b => mustNotFlow a || mustNotFlow b
  | .ite _ a b => mustNotFlow a && mustNotFlow b
  | _ => false

private theorem evaluate_mustNotFlow {F : Type} (p : ProgHOL 64) (hp : mustNotFlow p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ none := by
  cases shape : p with
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | seq a b =>
    have hab : mustNotFlow a = true ∨ mustNotFlow b = true := by
      simpa [shape, mustNotFlow, Bool.or_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨ra, ma⟩
    cases ra with
    | none =>
      rcases hab with ha | hb
      · exact absurd (by rw [hr]) (evaluate_mustNotFlow a ha s)
      · exact evaluate_mustNotFlow b hb ma
    | some _ => simp
  | ite _ a b =>
    have hab : mustNotFlow a = true ∧ mustNotFlow b = true := by
      simpa [shape, mustNotFlow, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_mustNotFlow b hab.2 s
      · exact evaluate_mustNotFlow a hab.1 s
    · simp
  | _ => simp [shape, mustNotFlow] at hp

private theorem ite_mustNotFlow_skip_none {F : Type} {s m : PanSemStateFiniteExact 64 F}
    {c : ExpHOL 64} {blk : ProgHOL 64} (hmnf : mustNotFlow blk = true)
    (h : evaluateHOLFiniteState s (.ite c blk .skip) = (none, m)) : m = s := by
  rw [evaluateHOLFiniteState_ite] at h
  split at h
  · split at h
    · rw [evaluateHOLFiniteState_skip] at h; injection h with _ e; exact e.symm
    · exfalso
      exact evaluate_mustNotFlow blk hmnf s (congrArg Prod.fst h)
  · simp at h

private theorem memeq_not_ret0_const1 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.return (.const 1))).1 ≠ some (.returned (.val (.word 0))) := by
  rw [evaluateHOLFiniteState_return]
  simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]

private theorem memeq_spec_fast_block {F : Type} (s0 s : PanSemStateFiniteExact 64 F)
    (hfr : LocFrame s0 s) (hG0 : GuestInv s0)
    (a b n : BitVec 64) (hn_lt : n.toNat ≤ 60)
    (ha_nw : a.toNat + n.toNat < 2 ^ 64) (hb_nw : b.toNat + n.toNat < 2 ^ 64)
    (ha_loc : s.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb_loc : s.locals.lookup (ofString "b") = some (.val (.word b)))
    (hn_loc : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (cval : Nat) (hcval : cval = 20 ∨ cval = 32 ∨ cval = 52)
    (blk : ProgHOL 64)
    (hblk_eq : (cval = 20 ∧ blk =
        (.seq (.ite (.cmp .notEqual (.load .one (.var .local (ofString "a"))) (.load .one (.var .local (ofString "b")))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .const 8])) (.load .one (.op .add [.var .local (ofString "b"), .const 8]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .const 16])) (.loadByte (.op .add [.var .local (ofString "b"), .const 16]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .const 17])) (.loadByte (.op .add [.var .local (ofString "b"), .const 17]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .const 18])) (.loadByte (.op .add [.var .local (ofString "b"), .const 18]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .const 19])) (.loadByte (.op .add [.var .local (ofString "b"), .const 19]))) (.return (.const 0)) .skip)
        (.return (.const 1))))))))) ∨
      (cval = 32 ∧ blk =
        (.seq (.ite (.cmp .notEqual (.load .one (.var .local (ofString "a"))) (.load .one (.var .local (ofString "b")))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .const 8])) (.load .one (.op .add [.var .local (ofString "b"), .const 8]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .const 16])) (.load .one (.op .add [.var .local (ofString "b"), .const 16]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .const 24])) (.load .one (.op .add [.var .local (ofString "b"), .const 24]))) (.return (.const 0)) .skip)
        (.return (.const 1))))))) ∨
      (cval = 52 ∧ blk =
        (.seq (.ite (.cmp .notEqual (.load .one (.var .local (ofString "a"))) (.load .one (.var .local (ofString "b")))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .const 8])) (.load .one (.op .add [.var .local (ofString "b"), .const 8]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .const 16])) (.load .one (.op .add [.var .local (ofString "b"), .const 16]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .const 24])) (.load .one (.op .add [.var .local (ofString "b"), .const 24]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .const 32])) (.load .one (.op .add [.var .local (ofString "b"), .const 32]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .const 40])) (.load .one (.op .add [.var .local (ofString "b"), .const 40]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .const 48])) (.loadByte (.op .add [.var .local (ofString "b"), .const 48]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .const 49])) (.loadByte (.op .add [.var .local (ofString "b"), .const 49]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .const 50])) (.loadByte (.op .add [.var .local (ofString "b"), .const 50]))) (.return (.const 0)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .const 51])) (.loadByte (.op .add [.var .local (ofString "b"), .const 51]))) (.return (.const 0)) .skip)
        (.return (.const 1))))))))))))))
    (hret : (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.var .local (ofString "n")) (.const (BitVec.ofNat 64 cval))) blk .skip)).1 =
      some (.returned (.val (.word 0)))) :
    ∃ k < n.toNat, memB s0 ((a + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((b + BitVec.ofNat 64 k).toNat) := by
  have ite_skip_state : ∀ {st m : PanSemStateFiniteExact 64 F} {c e : ExpHOL 64},
      evaluateHOLFiniteState st (.ite c (.return e) .skip) = (none, m) → m = st := by
    intro st m c e h
    rw [evaluateHOLFiniteState_ite] at h
    split at h
    · split at h
      · rw [evaluateHOLFiniteState_skip] at h; injection h with _ hm; exact hm.symm
      · rw [evaluateHOLFiniteState_return] at h
        split at h
        · simp at h
        · split at h <;> simp at h
    · simp at h
  rw [evaluateHOLFiniteState_ite] at hret
  split at hret
  · rename_i cw hcmp
    split at hret
    · simp [evaluateHOLFiniteState_skip] at hret
    · rename_i hcw
      have hn_eq : n.toNat = cval := by
        obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp s .equal _ _ cw hcmp
        simp [evalAt, evalHOLExact, hn_loc] at hva hvb
        subst hva hvb
        by_contra hne
        have hbne : n ≠ BitVec.ofNat 64 cval := by
          intro he; apply hne; rw [he, BitVec.toNat_ofNat]
          rcases hcval with rfl | rfl | rfl <;> decide
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hbne] at hcw_eq
        exact hcw hcw_eq
      have hea0 : evalAt s (.var .local (ofString "a")) = some (.val (.word (a + BitVec.ofNat 64 0))) := by
        simp [evalAt, evalHOLExact, ha_loc]
      have heb0 : evalAt s (.var .local (ofString "b")) = some (.val (.word (b + BitVec.ofNat 64 0))) := by
        simp [evalAt, evalHOLExact, hb_loc]
      have hea_off : ∀ off : Nat,
          evalAt s (.op .add [.var .local (ofString "a"), .const (BitVec.ofNat 64 off)]) =
            some (.val (.word (a + BitVec.ofNat 64 off))) := by
        intro off
        simp [evalAt, evalHOLExact, evalListHOLExact, ha_loc, valueIsWord, valueWord, wordOpHOL, wordOp]
      have heb_off : ∀ off : Nat,
          evalAt s (.op .add [.var .local (ofString "b"), .const (BitVec.ofNat 64 off)]) =
            some (.val (.word (b + BitVec.ofNat 64 off))) := by
        intro off
        simp [evalAt, evalHOLExact, evalListHOLExact, hb_loc, valueIsWord, valueWord, wordOpHOL, wordOp]
      rcases hblk_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- cval = 20
        rcases seq_ret_or_none s _ _ _ hret with h1 | ⟨m1, hm1, hret1⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 0 (by omega) (by omega) (by omega) _ _ hea0 heb0 h1
        rw [ite_skip_state hm1] at hret1
        rcases seq_ret_or_none s _ _ _ hret1 with h2 | ⟨m2, hm2, hret2⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 8 (by omega) (by omega) (by omega) _ _ (hea_off 8) (heb_off 8) h2
        rw [ite_skip_state hm2] at hret2
        rcases seq_ret_or_none s _ _ _ hret2 with h3 | ⟨m3, hm3, hret3⟩
        · exact memeq_ite_byte_ret0 s0 s hfr hG0 a b n.toNat 16 (by omega) _ _ (hea_off 16) (heb_off 16) h3
        rw [ite_skip_state hm3] at hret3
        rcases seq_ret_or_none s _ _ _ hret3 with h4 | ⟨m4, hm4, hret4⟩
        · exact memeq_ite_byte_ret0 s0 s hfr hG0 a b n.toNat 17 (by omega) _ _ (hea_off 17) (heb_off 17) h4
        rw [ite_skip_state hm4] at hret4
        rcases seq_ret_or_none s _ _ _ hret4 with h5 | ⟨m5, hm5, hret5⟩
        · exact memeq_ite_byte_ret0 s0 s hfr hG0 a b n.toNat 18 (by omega) _ _ (hea_off 18) (heb_off 18) h5
        rw [ite_skip_state hm5] at hret5
        rcases seq_ret_or_none s _ _ _ hret5 with h6 | ⟨m6, hm6, hret6⟩
        · exact memeq_ite_byte_ret0 s0 s hfr hG0 a b n.toNat 19 (by omega) _ _ (hea_off 19) (heb_off 19) h6
        exact absurd hret6 (memeq_not_ret0_const1 m6)
      · -- cval = 32
        rcases seq_ret_or_none s _ _ _ hret with h1 | ⟨m1, hm1, hret1⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 0 (by omega) (by omega) (by omega) _ _ hea0 heb0 h1
        rw [ite_skip_state hm1] at hret1
        rcases seq_ret_or_none s _ _ _ hret1 with h2 | ⟨m2, hm2, hret2⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 8 (by omega) (by omega) (by omega) _ _ (hea_off 8) (heb_off 8) h2
        rw [ite_skip_state hm2] at hret2
        rcases seq_ret_or_none s _ _ _ hret2 with h3 | ⟨m3, hm3, hret3⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 16 (by omega) (by omega) (by omega) _ _ (hea_off 16) (heb_off 16) h3
        rw [ite_skip_state hm3] at hret3
        rcases seq_ret_or_none s _ _ _ hret3 with h4 | ⟨m4, hm4, hret4⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 24 (by omega) (by omega) (by omega) _ _ (hea_off 24) (heb_off 24) h4
        exact absurd hret4 (memeq_not_ret0_const1 m4)
      · -- cval = 52
        rcases seq_ret_or_none s _ _ _ hret with h1 | ⟨m1, hm1, hret1⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 0 (by omega) (by omega) (by omega) _ _ hea0 heb0 h1
        rw [ite_skip_state hm1] at hret1
        rcases seq_ret_or_none s _ _ _ hret1 with h2 | ⟨m2, hm2, hret2⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 8 (by omega) (by omega) (by omega) _ _ (hea_off 8) (heb_off 8) h2
        rw [ite_skip_state hm2] at hret2
        rcases seq_ret_or_none s _ _ _ hret2 with h3 | ⟨m3, hm3, hret3⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 16 (by omega) (by omega) (by omega) _ _ (hea_off 16) (heb_off 16) h3
        rw [ite_skip_state hm3] at hret3
        rcases seq_ret_or_none s _ _ _ hret3 with h4 | ⟨m4, hm4, hret4⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 24 (by omega) (by omega) (by omega) _ _ (hea_off 24) (heb_off 24) h4
        rw [ite_skip_state hm4] at hret4
        rcases seq_ret_or_none s _ _ _ hret4 with h5 | ⟨m5, hm5, hret5⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 32 (by omega) (by omega) (by omega) _ _ (hea_off 32) (heb_off 32) h5
        rw [ite_skip_state hm5] at hret5
        rcases seq_ret_or_none s _ _ _ hret5 with h6 | ⟨m6, hm6, hret6⟩
        · exact memeq_ite_word_ret0 s0 s hfr hG0 a b n.toNat 40 (by omega) (by omega) (by omega) _ _ (hea_off 40) (heb_off 40) h6
        rw [ite_skip_state hm6] at hret6
        rcases seq_ret_or_none s _ _ _ hret6 with h7 | ⟨m7, hm7, hret7⟩
        · exact memeq_ite_byte_ret0 s0 s hfr hG0 a b n.toNat 48 (by omega) _ _ (hea_off 48) (heb_off 48) h7
        rw [ite_skip_state hm7] at hret7
        rcases seq_ret_or_none s _ _ _ hret7 with h8 | ⟨m8, hm8, hret8⟩
        · exact memeq_ite_byte_ret0 s0 s hfr hG0 a b n.toNat 49 (by omega) _ _ (hea_off 49) (heb_off 49) h8
        rw [ite_skip_state hm8] at hret8
        rcases seq_ret_or_none s _ _ _ hret8 with h9 | ⟨m9, hm9, hret9⟩
        · exact memeq_ite_byte_ret0 s0 s hfr hG0 a b n.toNat 50 (by omega) _ _ (hea_off 50) (heb_off 50) h9
        rw [ite_skip_state hm9] at hret9
        rcases seq_ret_or_none s _ _ _ hret9 with h10 | ⟨m10, hm10, hret10⟩
        · exact memeq_ite_byte_ret0 s0 s hfr hG0 a b n.toNat 51 (by omega) _ _ (hea_off 51) (heb_off 51) h10
        exact absurd hret10 (memeq_not_ret0_const1 m10)
  · simp at hret

private def noBreak : ProgHOL 64 → Bool
  | .break => false
  | .seq a b => noBreak a && noBreak b
  | .ite _ a b => noBreak a && noBreak b
  | .dec _ _ _ a => noBreak a
  | .while _ _ => true
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip | .return _ => true
  | _ => false

private theorem evaluate_noBreak {F : Type} (p : ProgHOL 64) (hp : noBreak p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break := by
  cases shape : p with
  | «break» => simp [shape, noBreak] at hp
  | skip => simp [evaluateHOLFiniteState_skip]
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noBreak] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | dec _ _ _ a =>
    have ha : noBreak a = true := by simpa [shape, noBreak] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noBreak a ha _
      · simp
  | «while» cond body =>
    suffices hrec : ∀ clk (st : PanSemStateFiniteExact 64 F), st.clock ≤ clk →
        (evaluateHOLFiniteState st (.while cond body)).1 ≠ some .break by
      exact hrec s.clock s le_rfl
    intro clk
    induction clk with
    | zero =>
      intro st hclk
      rw [evaluateHOLFiniteState_while_total]
      split
      · split
        · split
          · simp
          · omega
        · simp
      · simp
    | succ clk ih =>
      intro st hclk
      rw [evaluateHOLFiniteState_while_total]
      split
      · split
        · split
          · simp
          · dsimp only
            rw [fixClockHOLFinite_evaluateState]
            have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
            rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨rb, mid⟩
            rw [hbr] at hrem
            cases rb with
            | none => exact ih mid (by change mid.clock ≤ st.clock - 1 at hrem; omega)
            | some r =>
              cases r with
              | «continue» => exact ih mid (by change mid.clock ≤ st.clock - 1 at hrem; omega)
              | _ => simp
        · simp
      · simp
  | seq a b =>
    have hab : noBreak a = true ∧ noBreak b = true := by
      simpa [shape, noBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noBreak a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact evaluate_noBreak b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noBreak a = true ∧ noBreak b = true := by
      simpa [shape, noBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noBreak b hab.2 s
      · exact evaluate_noBreak a hab.1 s
    · simp
  | _ => simp [shape, noBreak] at hp

private theorem memeq_while_general {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hG0 : GuestInv s0) (a b n : BitVec 64) (hn_lt : n.toNat ≤ 60)
    (ha_nw : a.toNat + n.toNat < 2 ^ 64) (hb_nw : b.toNat + n.toNat < 2 ^ 64)
    (step : BitVec 64) (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnc : noTopContinue body = true) (hnb : noBreak body = true)
    (hcond : (cond = .cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const step]) ∧ (step = 32 ∨ step = 8)) ∨
             (cond = .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")) ∧ step = 1))
    (hbody_spec : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      LocFrame s0 st →
      wi.toNat + step.toNat ≤ n.toNat →
      st.locals.lookup (ofString "a") = some (.val (.word a)) →
      st.locals.lookup (ofString "b") = some (.val (.word b)) →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      ((evaluateHOLFiniteState st body).1 = some (.returned (.val (.word 0))) →
        ∃ k < n.toNat, memB s0 ((a + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((b + BitVec.ofNat 64 k).toNat)) ∧
      ((evaluateHOLFiniteState st body).1 = none →
        LocFrame s0 (evaluateHOLFiniteState st body).2 ∧
        (evaluateHOLFiniteState st body).2.locals.lookup (ofString "a") = some (.val (.word a)) ∧
        (evaluateHOLFiniteState st body).2.locals.lookup (ofString "b") = some (.val (.word b)) ∧
        (evaluateHOLFiniteState st body).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
        (evaluateHOLFiniteState st body).2.locals.lookup (ofString "i") = some (.val (.word (wi + step)))))
    (clk : Nat) (s : PanSemStateFiniteExact 64 F) (wi : BitVec 64)
    (hclk : s.clock ≤ clk) (hfr : LocFrame s0 s) (hwi_le : wi.toNat ≤ n.toNat)
    (ha_loc : s.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb_loc : s.locals.lookup (ofString "b") = some (.val (.word b)))
    (hn_loc : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi_loc : s.locals.lookup (ofString "i") = some (.val (.word wi))) :
    ((evaluateHOLFiniteState s (.while cond body)).1 = some (.returned (.val (.word 0))) →
      ∃ k < n.toNat, memB s0 ((a + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((b + BitVec.ofNat 64 k).toNat)) ∧
    ((evaluateHOLFiniteState s (.while cond body)).1 = none →
      ∃ wi' : BitVec 64,
        LocFrame s0 (evaluateHOLFiniteState s (.while cond body)).2 ∧
        wi'.toNat ≤ n.toNat ∧
        (evaluateHOLFiniteState s (.while cond body)).2.locals.lookup (ofString "a") = some (.val (.word a)) ∧
        (evaluateHOLFiniteState s (.while cond body)).2.locals.lookup (ofString "b") = some (.val (.word b)) ∧
        (evaluateHOLFiniteState s (.while cond body)).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
        (evaluateHOLFiniteState s (.while cond body)).2.locals.lookup (ofString "i") = some (.val (.word wi'))) := by
  induction clk generalizing s wi with
  | zero =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · omega
      · exact ⟨fun h => by simp at h, fun _ => ⟨wi, hfr, hwi_le, ha_loc, hb_loc, hn_loc, hi_loc⟩⟩
    · simp
  | succ clk ih =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · rename_i cw hcond_ev
      split
      · rename_i hnz
        split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hstep_le : wi.toNat + step.toNat ≤ n.toNat := by
            rw [evalHOLFinite_eq_toExact] at hcond_ev
            rcases hcond with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .notLower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hn_loc, hi_loc, valueIsWord, valueWord, wordOpHOL, wordOp] at hva hvb
              subst hva hvb
              have h32 : (32 : BitVec 64).toNat = 32 := rfl
              change wi.toNat + (32 : BitVec 64).toNat ≤ n.toNat
              rw [h32]
              have hadd : (wi + 32#64).toNat = wi.toNat + 32 := by rw [BitVec.toNat_add, show (32#64).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
              by_contra hgt
              have hnle : ¬ (wi + 32#64 ≤ n) := by rw [BitVec.le_def, hadd]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnle] at hcw
              exact hnz hcw
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .notLower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hn_loc, hi_loc, valueIsWord, valueWord, wordOpHOL, wordOp] at hva hvb
              subst hva hvb
              have h8 : (8 : BitVec 64).toNat = 8 := rfl
              change wi.toNat + (8 : BitVec 64).toNat ≤ n.toNat
              rw [h8]
              have hadd : (wi + 8#64).toNat = wi.toNat + 8 := by rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
              by_contra hgt
              have hnle : ¬ (wi + 8#64 ≤ n) := by rw [BitVec.le_def, hadd]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnle] at hcw
              exact hnz hcw
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .lower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hn_loc, hi_loc] at hva hvb
              subst hva hvb
              have h1 : (1 : BitVec 64).toNat = 1 := rfl
              rw [h1]
              by_contra hgt
              have hnlt : ¬ (wi < n) := by rw [BitVec.lt_def]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt] at hcw
              exact hnz hcw
          have hfr_dec : LocFrame s0 (decClockHOLFinite s) := by
            unfold LocFrame at hfr ⊢; dsimp only [decClockHOLFinite]; rw [hfr]
          have hb := hbody_spec (decClockHOLFinite s) wi hfr_dec hstep_le ha_loc hb_loc hn_loc hi_loc
          have hnc' := evaluate_noTopContinue body hnc (decClockHOLFinite s)
          have hnb' := evaluate_noBreak body hnb (decClockHOLFinite s)
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, mid⟩
          rw [hbr] at hb hnc' hnb' hrem
          dsimp only at hb hnc' hnb' hrem
          cases rb with
          | none =>
            obtain ⟨hfr_m, ha_m, hb_m, hn_m, hi_m⟩ := hb.2 rfl
            have hw_add : (wi + step).toNat = wi.toNat + step.toNat := by
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
            exact ih mid (wi + step) (by change mid.clock ≤ s.clock - 1 at hrem; omega)
              hfr_m (by omega) ha_m hb_m hn_m hi_m
          | some r =>
            cases r with
            | «continue» => exact absurd rfl hnc'
            | «break» => exact absurd rfl hnb'
            | returned rv =>
              exact ⟨fun hr => by injection hr with h1; injection h1 with h2; subst h2; exact hb.1 rfl,
                     fun h => by simp at h⟩
            | _ => exact ⟨fun h => by simp at h, fun h => by simp at h⟩
      · exact ⟨fun h => by simp at h, fun _ => ⟨wi, hfr, hwi_le, ha_loc, hb_loc, hn_loc, hi_loc⟩⟩
    · simp

private theorem seq_none_inv {F : Type} {s : PanSemStateFiniteExact 64 F}
    {p1 p2 : ProgHOL 64} (h : (evaluateHOLFiniteState s (.seq p1 p2)).1 = none) :
    ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
      evaluateHOLFiniteState s (.seq p1 p2) = evaluateHOLFiniteState m p2 := by
  rw [evaluateHOLFiniteState_seq_line780] at h ⊢
  rcases hr : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  rw [hr] at h
  cases r1 with
  | none => exact ⟨m, rfl, rfl⟩
  | some _ => simp at h

private theorem seq_eq_none_inv {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {p1 p2 : ProgHOL 64} (h : evaluateHOLFiniteState s (.seq p1 p2) = (none, u)) :
    ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
      evaluateHOLFiniteState m p2 = (none, u) := by
  obtain ⟨m, hm1, hm2⟩ := seq_none_inv (p1 := p1) (p2 := p2) (congrArg Prod.fst h)
  exact ⟨m, hm1, hm2.symm.trans h⟩

/-- Full postcondition of `memeq(a, b, n)` when it returns `0` (`n ≤ 60`, no address wrap):
1. `LocFrame s0 post`
2. There is `k < n.toNat` where `memB s0 ((a + k).toNat) ≠ memB s0 ((b + k).toNat)`. -/
theorem memeq_body_ret0_exists_diff {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hG0 : GuestInv s0) (a b n : BitVec 64)
    (hn_lt : n.toNat ≤ 60)
    (ha_nw : a.toNat + n.toNat < 2 ^ 64) (hb_nw : b.toNat + n.toNat < 2 ^ 64)
    (ha_loc : s0.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb_loc : s0.locals.lookup (ofString "b") = some (.val (.word b)))
    (hn_loc : s0.locals.lookup (ofString "n") = some (.val (.word n)))
    (hret : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memeq)).1 =
      some (.returned (.val (.word 0)))) :
    ∃ k < n.toNat, memB s0 ((a + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((b + BitVec.ofNat 64 k).toNat) := by
  have ite_skip_state : ∀ {st m : PanSemStateFiniteExact 64 F} {c e : ExpHOL 64},
      evaluateHOLFiniteState st (.ite c (.return e) .skip) = (none, m) → m = st := by
    intro st m c e h
    rw [evaluateHOLFiniteState_ite] at h
    split at h
    · split at h
      · rw [evaluateHOLFiniteState_skip] at h; injection h with _ hm; exact hm.symm
      · rw [evaluateHOLFiniteState_return] at h
        split at h
        · simp at h
        · split at h <;> simp at h
    · simp at h
  have assign_i_ok : ∀ (st : PanSemStateFiniteExact 64 F) (wi step : BitVec 64),
      LocFrame s0 st →
      st.locals.lookup (ofString "a") = some (.val (.word a)) →
      st.locals.lookup (ofString "b") = some (.val (.word b)) →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      ((evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).1 =
        some (.returned (.val (.word 0))) → False) ∧
      ((evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).1 = none →
        LocFrame s0 (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2 ∧
        (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "a") = some (.val (.word a)) ∧
        (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "b") = some (.val (.word b)) ∧
        (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
        (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "i") = some (.val (.word (wi + step)))) := by
    intro st wi step hfr ha hb hn hi
    have hrun : evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step])) =
        (none, setVarHOLFinite (ofString "i") (.val (.word (wi + step))) st) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hrun]
    refine ⟨by simp, fun _ => ⟨hfr.locals _, ?_, ?_, ?_, ?_⟩⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha, show ofString "i" ≠ ofString "a" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb, show ofString "i" ≠ ofString "b" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have ea_i : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      wi.toNat ≤ n.toNat →
      st.locals.lookup (ofString "a") = some (.val (.word a)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "a"), .var .local (ofString "i")]) =
        some (.val (.word (a + BitVec.ofNat 64 wi.toNat))) := by
    intro st wi _ ha hi
    simp [evalAt, evalHOLExact, evalListHOLExact, ha, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
  have eb_i : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      wi.toNat ≤ n.toNat →
      st.locals.lookup (ofString "b") = some (.val (.word b)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "b"), .var .local (ofString "i")]) =
        some (.val (.word (b + BitVec.ofNat 64 wi.toNat))) := by
    intro st wi _ hb hi
    simp [evalAt, evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
  have ea_ik : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64) (off : Nat),
      wi.toNat + off ≤ n.toNat →
      st.locals.lookup (ofString "a") = some (.val (.word a)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "a"), .var .local (ofString "i"), .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (a + BitVec.ofNat 64 (wi.toNat + off)))) := by
    intro st wi off hle ha hi
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ha, hi,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hz]
    omega
  have eb_ik : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64) (off : Nat),
      wi.toNat + off ≤ n.toNat →
      st.locals.lookup (ofString "b") = some (.val (.word b)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "b"), .var .local (ofString "i"), .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (b + BitVec.ofNat 64 (wi.toNat + off)))) := by
    intro st wi off hle hb hi
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hb, hi,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hz]
    omega
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memeq,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hret
  rw [evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  have hev0 : @evalHOLExact 64 F _ s0.toExact (fun x => Classical.propDecidable (s0.memaddrs x)) (.const 0#64) =
      some (.val (.word 0#64)) := rfl
  rw [hev0] at hret
  dsimp only at hret
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hret
  dsimp only at hret
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s0
  have hs1_fr : LocFrame s0 s1 := (LocFrame.refl s0).locals _
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha_loc, show ofString "i" ≠ ofString "a" by decide]
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb_loc, show ofString "i" ≠ ofString "b" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_loc, show ofString "i" ≠ ofString "n" by decide]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Loop 1 (32B words)
  have hloop32 : ∀ (s : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      LocFrame s0 s → wi.toNat ≤ n.toNat →
      s.locals.lookup (ofString "a") = some (.val (.word a)) →
      s.locals.lookup (ofString "b") = some (.val (.word b)) →
      s.locals.lookup (ofString "n") = some (.val (.word n)) →
      s.locals.lookup (ofString "i") = some (.val (.word wi)) →
      let lp := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64]))
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .var .local (ofString "i")])) (.load .one (.op .add [.var .local (ofString "b"), .var .local (ofString "i")]))) (.return (.const 0#64)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .var .local (ofString "i"), .const 8#64])) (.load .one (.op .add [.var .local (ofString "b"), .var .local (ofString "i"), .const 8#64]))) (.return (.const 0#64)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .var .local (ofString "i"), .const 16#64])) (.load .one (.op .add [.var .local (ofString "b"), .var .local (ofString "i"), .const 16#64]))) (.return (.const 0#64)) .skip)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .var .local (ofString "i"), .const 24#64])) (.load .one (.op .add [.var .local (ofString "b"), .var .local (ofString "i"), .const 24#64]))) (.return (.const 0#64)) .skip)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32#64]))))))
      ((evaluateHOLFiniteState s lp).1 = some (.returned (.val (.word 0))) →
        ∃ k < n.toNat, memB s0 ((a + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((b + BitVec.ofNat 64 k).toNat)) ∧
      ((evaluateHOLFiniteState s lp).1 = none →
        ∃ wi', LocFrame s0 (evaluateHOLFiniteState s lp).2 ∧ wi'.toNat ≤ n.toNat ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "a") = some (.val (.word a)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "b") = some (.val (.word b)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "i") = some (.val (.word wi'))) := by
    intro s wi hfr hle ha hb hn hi
    apply memeq_while_general s0 hG0 a b n hn_lt ha_nw hb_nw 32#64 _ _ rfl rfl (Or.inl ⟨rfl, Or.inl rfl⟩)
      ?_ s.clock s wi le_rfl hfr hle ha hb hn hi
    intro st w hfr_st hw_step ha_st hb_st hn_st hi_st
    have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
    rw [h32] at hw_step
    constructor
    · intro hr
      rcases seq_ret_or_none st _ _ _ hr with h1 | ⟨m1, hm1, hr1⟩
      · exact memeq_ite_word_ret0 s0 st hfr_st hG0 a b n.toNat w.toNat (by omega) (by omega) (by omega) _ _
          (ea_i st w (by omega) ha_st hi_st) (eb_i st w (by omega) hb_st hi_st) h1
      rw [ite_skip_state hm1] at hr1
      rcases seq_ret_or_none st _ _ _ hr1 with h2 | ⟨m2, hm2, hr2⟩
      · exact memeq_ite_word_ret0 s0 st hfr_st hG0 a b n.toNat (w.toNat + 8) (by omega) (by omega) (by omega) _ _
          (ea_ik st w 8 (by omega) ha_st hi_st) (eb_ik st w 8 (by omega) hb_st hi_st) h2
      rw [ite_skip_state hm2] at hr2
      rcases seq_ret_or_none st _ _ _ hr2 with h3 | ⟨m3, hm3, hr3⟩
      · exact memeq_ite_word_ret0 s0 st hfr_st hG0 a b n.toNat (w.toNat + 16) (by omega) (by omega) (by omega) _ _
          (ea_ik st w 16 (by omega) ha_st hi_st) (eb_ik st w 16 (by omega) hb_st hi_st) h3
      rw [ite_skip_state hm3] at hr3
      rcases seq_ret_or_none st _ _ _ hr3 with h4 | ⟨m4, hm4, hr4⟩
      · exact memeq_ite_word_ret0 s0 st hfr_st hG0 a b n.toNat (w.toNat + 24) (by omega) (by omega) (by omega) _ _
          (ea_ik st w 24 (by omega) ha_st hi_st) (eb_ik st w 24 (by omega) hb_st hi_st) h4
      rw [ite_skip_state hm4] at hr4
      exact False.elim ((assign_i_ok st w 32#64 hfr_st ha_st hb_st hn_st hi_st).1 hr4)
    · intro hnone
      obtain ⟨m1, hm1, eq1⟩ := seq_none_inv hnone; rw [eq1, ite_skip_state hm1] at hnone ⊢
      obtain ⟨m2, hm2, eq2⟩ := seq_none_inv hnone; rw [eq2, ite_skip_state hm2] at hnone ⊢
      obtain ⟨m3, hm3, eq3⟩ := seq_none_inv hnone; rw [eq3, ite_skip_state hm3] at hnone ⊢
      obtain ⟨m4, hm4, eq4⟩ := seq_none_inv hnone; rw [eq4, ite_skip_state hm4] at hnone ⊢
      exact (assign_i_ok st w 32#64 hfr_st ha_st hb_st hn_st hi_st).2 hnone
  -- Loop 2 (8B words)
  have hloop8w : ∀ (s : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      LocFrame s0 s → wi.toNat ≤ n.toNat →
      s.locals.lookup (ofString "a") = some (.val (.word a)) →
      s.locals.lookup (ofString "b") = some (.val (.word b)) →
      s.locals.lookup (ofString "n") = some (.val (.word n)) →
      s.locals.lookup (ofString "i") = some (.val (.word wi)) →
      let lp := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64]))
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "a"), .var .local (ofString "i")])) (.load .one (.op .add [.var .local (ofString "b"), .var .local (ofString "i")]))) (.return (.const 0#64)) .skip)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64])))
      ((evaluateHOLFiniteState s lp).1 = some (.returned (.val (.word 0))) →
        ∃ k < n.toNat, memB s0 ((a + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((b + BitVec.ofNat 64 k).toNat)) ∧
      ((evaluateHOLFiniteState s lp).1 = none →
        ∃ wi', LocFrame s0 (evaluateHOLFiniteState s lp).2 ∧ wi'.toNat ≤ n.toNat ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "a") = some (.val (.word a)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "b") = some (.val (.word b)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "i") = some (.val (.word wi'))) := by
    intro s wi hfr hle ha hb hn hi
    apply memeq_while_general s0 hG0 a b n hn_lt ha_nw hb_nw 8#64 _ _ rfl rfl (Or.inl ⟨rfl, Or.inr rfl⟩)
      ?_ s.clock s wi le_rfl hfr hle ha hb hn hi
    intro st w hfr_st hw_step ha_st hb_st hn_st hi_st
    have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [h8] at hw_step
    constructor
    · intro hr
      rcases seq_ret_or_none st _ _ _ hr with h1 | ⟨m1, hm1, hr1⟩
      · exact memeq_ite_word_ret0 s0 st hfr_st hG0 a b n.toNat w.toNat (by omega) (by omega) (by omega) _ _
          (ea_i st w (by omega) ha_st hi_st) (eb_i st w (by omega) hb_st hi_st) h1
      rw [ite_skip_state hm1] at hr1
      exact False.elim ((assign_i_ok st w 8#64 hfr_st ha_st hb_st hn_st hi_st).1 hr1)
    · intro hnone
      obtain ⟨m1, hm1, eq1⟩ := seq_none_inv hnone; rw [eq1, ite_skip_state hm1] at hnone ⊢
      exact (assign_i_ok st w 8#64 hfr_st ha_st hb_st hn_st hi_st).2 hnone
  -- Loop 3 (8B bytes)
  have hloop8b : ∀ (s : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      LocFrame s0 s → wi.toNat ≤ n.toNat →
      s.locals.lookup (ofString "a") = some (.val (.word a)) →
      s.locals.lookup (ofString "b") = some (.val (.word b)) →
      s.locals.lookup (ofString "n") = some (.val (.word n)) →
      s.locals.lookup (ofString "i") = some (.val (.word wi)) →
      let lp := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64]))
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i")])) (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i")]))) (.return (.const 0#64)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i"), .const 1#64])) (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i"), .const 1#64]))) (.return (.const 0#64)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i"), .const 2#64])) (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i"), .const 2#64]))) (.return (.const 0#64)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i"), .const 3#64])) (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i"), .const 3#64]))) (.return (.const 0#64)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i"), .const 4#64])) (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i"), .const 4#64]))) (.return (.const 0#64)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i"), .const 5#64])) (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i"), .const 5#64]))) (.return (.const 0#64)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i"), .const 6#64])) (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i"), .const 6#64]))) (.return (.const 0#64)) .skip)
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i"), .const 7#64])) (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i"), .const 7#64]))) (.return (.const 0#64)) .skip)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64]))))))))))
      ((evaluateHOLFiniteState s lp).1 = some (.returned (.val (.word 0))) →
        ∃ k < n.toNat, memB s0 ((a + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((b + BitVec.ofNat 64 k).toNat)) ∧
      ((evaluateHOLFiniteState s lp).1 = none →
        ∃ wi', LocFrame s0 (evaluateHOLFiniteState s lp).2 ∧ wi'.toNat ≤ n.toNat ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "a") = some (.val (.word a)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "b") = some (.val (.word b)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "i") = some (.val (.word wi'))) := by
    intro s wi hfr hle ha hb hn hi
    apply memeq_while_general s0 hG0 a b n hn_lt ha_nw hb_nw 8#64 _ _ rfl rfl (Or.inl ⟨rfl, Or.inr rfl⟩)
      ?_ s.clock s wi le_rfl hfr hle ha hb hn hi
    intro st w hfr_st hw_step ha_st hb_st hn_st hi_st
    have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [h8] at hw_step
    constructor
    · intro hr
      rcases seq_ret_or_none st _ _ _ hr with h0 | ⟨m0, hm0, hr0⟩
      · exact memeq_ite_byte_ret0 s0 st hfr_st hG0 a b n.toNat w.toNat (by omega) _ _ (ea_i st w (by omega) ha_st hi_st) (eb_i st w (by omega) hb_st hi_st) h0
      rw [ite_skip_state hm0] at hr0
      rcases seq_ret_or_none st _ _ _ hr0 with h1 | ⟨m1, hm1, hr1⟩
      · exact memeq_ite_byte_ret0 s0 st hfr_st hG0 a b n.toNat (w.toNat + 1) (by omega) _ _ (ea_ik st w 1 (by omega) ha_st hi_st) (eb_ik st w 1 (by omega) hb_st hi_st) h1
      rw [ite_skip_state hm1] at hr1
      rcases seq_ret_or_none st _ _ _ hr1 with h2 | ⟨m2, hm2, hr2⟩
      · exact memeq_ite_byte_ret0 s0 st hfr_st hG0 a b n.toNat (w.toNat + 2) (by omega) _ _ (ea_ik st w 2 (by omega) ha_st hi_st) (eb_ik st w 2 (by omega) hb_st hi_st) h2
      rw [ite_skip_state hm2] at hr2
      rcases seq_ret_or_none st _ _ _ hr2 with h3 | ⟨m3, hm3, hr3⟩
      · exact memeq_ite_byte_ret0 s0 st hfr_st hG0 a b n.toNat (w.toNat + 3) (by omega) _ _ (ea_ik st w 3 (by omega) ha_st hi_st) (eb_ik st w 3 (by omega) hb_st hi_st) h3
      rw [ite_skip_state hm3] at hr3
      rcases seq_ret_or_none st _ _ _ hr3 with h4 | ⟨m4, hm4, hr4⟩
      · exact memeq_ite_byte_ret0 s0 st hfr_st hG0 a b n.toNat (w.toNat + 4) (by omega) _ _ (ea_ik st w 4 (by omega) ha_st hi_st) (eb_ik st w 4 (by omega) hb_st hi_st) h4
      rw [ite_skip_state hm4] at hr4
      rcases seq_ret_or_none st _ _ _ hr4 with h5 | ⟨m5, hm5, hr5⟩
      · exact memeq_ite_byte_ret0 s0 st hfr_st hG0 a b n.toNat (w.toNat + 5) (by omega) _ _ (ea_ik st w 5 (by omega) ha_st hi_st) (eb_ik st w 5 (by omega) hb_st hi_st) h5
      rw [ite_skip_state hm5] at hr5
      rcases seq_ret_or_none st _ _ _ hr5 with h6 | ⟨m6, hm6, hr6⟩
      · exact memeq_ite_byte_ret0 s0 st hfr_st hG0 a b n.toNat (w.toNat + 6) (by omega) _ _ (ea_ik st w 6 (by omega) ha_st hi_st) (eb_ik st w 6 (by omega) hb_st hi_st) h6
      rw [ite_skip_state hm6] at hr6
      rcases seq_ret_or_none st _ _ _ hr6 with h7 | ⟨m7, hm7, hr7⟩
      · exact memeq_ite_byte_ret0 s0 st hfr_st hG0 a b n.toNat (w.toNat + 7) (by omega) _ _ (ea_ik st w 7 (by omega) ha_st hi_st) (eb_ik st w 7 (by omega) hb_st hi_st) h7
      rw [ite_skip_state hm7] at hr7
      exact False.elim ((assign_i_ok st w 8#64 hfr_st ha_st hb_st hn_st hi_st).1 hr7)
    · intro hnone
      obtain ⟨m0, hm0, eq0⟩ := seq_none_inv hnone; rw [eq0, ite_skip_state hm0] at hnone ⊢
      obtain ⟨m1, hm1, eq1⟩ := seq_none_inv hnone; rw [eq1, ite_skip_state hm1] at hnone ⊢
      obtain ⟨m2, hm2, eq2⟩ := seq_none_inv hnone; rw [eq2, ite_skip_state hm2] at hnone ⊢
      obtain ⟨m3, hm3, eq3⟩ := seq_none_inv hnone; rw [eq3, ite_skip_state hm3] at hnone ⊢
      obtain ⟨m4, hm4, eq4⟩ := seq_none_inv hnone; rw [eq4, ite_skip_state hm4] at hnone ⊢
      obtain ⟨m5, hm5, eq5⟩ := seq_none_inv hnone; rw [eq5, ite_skip_state hm5] at hnone ⊢
      obtain ⟨m6, hm6, eq6⟩ := seq_none_inv hnone; rw [eq6, ite_skip_state hm6] at hnone ⊢
      obtain ⟨m7, hm7, eq7⟩ := seq_none_inv hnone; rw [eq7, ite_skip_state hm7] at hnone ⊢
      exact (assign_i_ok st w 8#64 hfr_st ha_st hb_st hn_st hi_st).2 hnone
  -- Loop 4 (1B bytes)
  have hloop1b : ∀ (s : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      LocFrame s0 s → wi.toNat ≤ n.toNat →
      s.locals.lookup (ofString "a") = some (.val (.word a)) →
      s.locals.lookup (ofString "b") = some (.val (.word b)) →
      s.locals.lookup (ofString "n") = some (.val (.word n)) →
      s.locals.lookup (ofString "i") = some (.val (.word wi)) →
      let lp := ProgHOL.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
        (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i")])) (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i")]))) (.return (.const 0#64)) .skip)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))
      ((evaluateHOLFiniteState s lp).1 = some (.returned (.val (.word 0))) →
        ∃ k < n.toNat, memB s0 ((a + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((b + BitVec.ofNat 64 k).toNat)) ∧
      ((evaluateHOLFiniteState s lp).1 = none →
        ∃ wi', LocFrame s0 (evaluateHOLFiniteState s lp).2 ∧ wi'.toNat ≤ n.toNat ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "a") = some (.val (.word a)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "b") = some (.val (.word b)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
          (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "i") = some (.val (.word wi'))) := by
    intro s wi hfr hle ha hb hn hi
    apply memeq_while_general s0 hG0 a b n hn_lt ha_nw hb_nw 1#64 _ _ rfl rfl (Or.inr ⟨rfl, rfl⟩)
      ?_ s.clock s wi le_rfl hfr hle ha hb hn hi
    intro st w hfr_st hw_step ha_st hb_st hn_st hi_st
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [h1] at hw_step
    constructor
    · intro hr
      rcases seq_ret_or_none st _ _ _ hr with h0 | ⟨m0, hm0, hr0⟩
      · exact memeq_ite_byte_ret0 s0 st hfr_st hG0 a b n.toNat w.toNat (by omega) _ _ (ea_i st w (by omega) ha_st hi_st) (eb_i st w (by omega) hb_st hi_st) h0
      rw [ite_skip_state hm0] at hr0
      exact False.elim ((assign_i_ok st w 1#64 hfr_st ha_st hb_st hn_st hi_st).1 hr0)
    · intro hnone
      obtain ⟨m0, hm0, eq0⟩ := seq_none_inv hnone; rw [eq0, ite_skip_state hm0] at hnone ⊢
      exact (assign_i_ok st w 1#64 hfr_st ha_st hb_st hn_st hi_st).2 hnone
  -- Now compose the top-level sequence of `memeq`!
  rcases seq_ret_or_none s1 _ _ _ hret with h_fast | ⟨s2, hs2, hret_tail⟩
  · -- Inside the aligned fast-path `ite`
    rw [evaluateHOLFiniteState_ite] at h_fast
    split at h_fast
    · split at h_fast
      · simp [evaluateHOLFiniteState_skip] at h_fast
      · rcases seq_ret_or_none s1 _ _ _ h_fast with h20 | ⟨m20, hm20, h_fast2⟩
        · exact memeq_spec_fast_block s0 s1 hs1_fr hG0 a b n hn_lt ha_nw hb_nw hs1_a hs1_b hs1_n 20 (Or.inl rfl) _ (Or.inl ⟨rfl, rfl⟩) h20
        rw [ite_mustNotFlow_skip_none rfl hm20] at h_fast2
        rcases seq_ret_or_none s1 _ _ _ h_fast2 with h32 | ⟨m32, hm32, h_fast3⟩
        · exact memeq_spec_fast_block s0 s1 hs1_fr hG0 a b n hn_lt ha_nw hb_nw hs1_a hs1_b hs1_n 32 (Or.inr (Or.inl rfl)) _ (Or.inr (Or.inl ⟨rfl, rfl⟩)) h32
        rw [ite_mustNotFlow_skip_none rfl hm32] at h_fast3
        rcases seq_ret_or_none s1 _ _ _ h_fast3 with h52 | ⟨m52, hm52, h_fast4⟩
        · exact memeq_spec_fast_block s0 s1 hs1_fr hG0 a b n hn_lt ha_nw hb_nw hs1_a hs1_b hs1_n 52 (Or.inr (Or.inr rfl)) _ (Or.inr (Or.inr ⟨rfl, rfl⟩)) h52
        rw [ite_mustNotFlow_skip_none rfl hm52] at h_fast4
        rcases seq_ret_or_none s1 _ _ _ h_fast4 with hl32 | ⟨ml32, hml32, hl8w⟩
        · exact (hloop32 s1 0#64 hs1_fr (Nat.zero_le _) hs1_a hs1_b hs1_n hs1_i).1 hl32
        have hstep32 := (hloop32 s1 0#64 hs1_fr (Nat.zero_le _) hs1_a hs1_b hs1_n hs1_i).2 (congrArg Prod.fst hml32)
        rw [hml32] at hstep32
        obtain ⟨wi1, hfr1, hle1, ha1, hb1, hn1, hi1⟩ := hstep32
        exact (hloop8w ml32 wi1 hfr1 hle1 ha1 hb1 hn1 hi1).1 hl8w
    · simp at h_fast
  · -- Passed the aligned `ite` with `(none, s2)`: extract state invariant at `s2`!
    have hs2_inv : ∃ wi2 : BitVec 64, LocFrame s0 s2 ∧ wi2.toNat ≤ n.toNat ∧
        s2.locals.lookup (ofString "a") = some (.val (.word a)) ∧
        s2.locals.lookup (ofString "b") = some (.val (.word b)) ∧
        s2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
        s2.locals.lookup (ofString "i") = some (.val (.word wi2)) := by
      rw [evaluateHOLFiniteState_ite] at hs2
      split at hs2
      · split at hs2
        · rw [evaluateHOLFiniteState_skip] at hs2; injection hs2 with _ e; rw [← e]
          exact ⟨0#64, hs1_fr, Nat.zero_le _, hs1_a, hs1_b, hs1_n, hs1_i⟩
        · obtain ⟨m20, hm20, hs2⟩ := seq_eq_none_inv hs2
          rw [ite_mustNotFlow_skip_none rfl hm20] at hs2
          obtain ⟨m32, hm32, hs2⟩ := seq_eq_none_inv hs2
          rw [ite_mustNotFlow_skip_none rfl hm32] at hs2
          obtain ⟨m52, hm52, hs2⟩ := seq_eq_none_inv hs2
          rw [ite_mustNotFlow_skip_none rfl hm52] at hs2
          obtain ⟨ml32, hml32, hs2⟩ := seq_eq_none_inv hs2
          have hstep32 := (hloop32 s1 0#64 hs1_fr (Nat.zero_le _) hs1_a hs1_b hs1_n hs1_i).2 (congrArg Prod.fst hml32)
          rw [hml32] at hstep32
          obtain ⟨wi1, hfr1, hle1, ha1, hb1, hn1, hi1⟩ := hstep32
          have h2 := (hloop8w ml32 wi1 hfr1 hle1 ha1 hb1 hn1 hi1).2 (congrArg Prod.fst hs2)
          rw [hs2] at h2
          exact h2
      · simp at hs2
    obtain ⟨wi2, hfr2, hle2, ha2, hb2, hn2, hi2⟩ := hs2_inv
    rcases seq_ret_or_none s2 _ _ _ hret_tail with hl8b | ⟨s3, hs3, hret_tail2⟩
    · exact (hloop8b s2 wi2 hfr2 hle2 ha2 hb2 hn2 hi2).1 hl8b
    have hstep8b := (hloop8b s2 wi2 hfr2 hle2 ha2 hb2 hn2 hi2).2 (congrArg Prod.fst hs3)
    rw [hs3] at hstep8b
    obtain ⟨wi3, hfr3, hle3, ha3, hb3, hn3, hi3⟩ := hstep8b
    rcases seq_ret_or_none s3 _ _ _ hret_tail2 with hl1b | ⟨s4, _, hret_one⟩
    · exact (hloop1b s3 wi3 hfr3 hle3 ha3 hb3 hn3 hi3).1 hl1b
    exact absurd hret_one (memeq_not_ret0_const1 s4)

/-! ### 6b. `htab_first_diff` postcondition on normal return -/

private theorem evalAt_and1 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 : ExpHOL 64) (w1 : BitVec 64)
    (h1 : evalAt s e1 = some (.val (.word w1))) :
    evalAt s (.op .and [e1, .const 1#64]) = some (.val (.word (w1 &&& 1#64))) := by
  unfold evalAt at h1 ⊢
  simp only [evalHOLExact, evalListHOLExact, h1,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    valueIsWord, valueWord, wordOpHOL, wordOp, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
  have hall : (1#64 : BitVec 64) &&& ~~~(0 : BitVec 64) = 1#64 := by decide
  exact congrArg _ hall

private theorem evalAt_notEqual {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 : ExpHOL 64) (w1 w2 : BitVec 64)
    (h1 : evalAt s e1 = some (.val (.word w1)))
    (h2 : evalAt s e2 = some (.val (.word w2))) :
    evalAt s (.cmp .notEqual e1 e2) = some (.val (.word (if w1 ≠ w2 then 1#64 else 0#64))) := by
  unfold evalAt at h1 h2 ⊢
  simp only [evalHOLExact, h1, h2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : w1 = w2 <;> simp [h]

private theorem htab_first_diff_inner_loop {F : Type}
    (x wj wi : BitVec 64) (hx_lt : x.toNat < 256) (hx_nz : x ≠ 0)
    (hwj_le : wj.toNat ≤ 8)
    (hprev_zero : ∀ r < wj.toNat, ((x >>> (7#64 - BitVec.ofNat 64 r)) &&& 1#64) = 0#64)
    (clk : Nat) (s : PanSemStateFiniteExact 64 F) (hclk : s.clock ≤ clk)
    (hx_loc : s.locals.lookup (ofString "x") = some (.val (.word x)))
    (hi_loc : s.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hj_loc : s.locals.lookup (ofString "j") = some (.val (.word wj))) :
    let inner := ProgHOL.while (.cmp .less (.var .local (ofString "j")) (.const 8#64))
      (.seq
        (.ite (.cmp .notEqual (.op .and [.shift .lsr (.var .local (ofString "x")) (.op .sub [.const 7#64, .var .local (ofString "j")]), .const 1#64]) (.const 0#64))
          (.return (.op .add [.panop .mul [.var .local (ofString "i"), .const 8#64], .var .local (ofString "j")]))
          .skip)
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))
    ((evaluateHOLFiniteState s inner).1 ≠ none) ∧
    (∀ v, (evaluateHOLFiniteState s inner).1 = some (.returned v) →
      ∃ j < 8, v = .val (.word (wi * 8#64 + BitVec.ofNat 64 j))) := by
  have hx_has_bit : ∃ r < 8, ((x >>> (7#64 - BitVec.ofNat 64 r)) &&& 1#64) ≠ 0#64 := by
    by_contra hnone
    have hnone' : ∀ r < 8, ((x >>> (7#64 - BitVec.ofNat 64 r)) &&& 1#64) = 0#64 := by
      intro r hr; by_contra hne; exact hnone ⟨r, hr, hne⟩
    apply hx_nz
    apply BitVec.eq_of_toNat_eq
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h0]
    by_contra hpos
    have hbit : ∀ k < 8, (x.toNat >>> k) % 2 = 0 := by
      intro k hk
      have h := hnone' (7 - k) (by omega)
      have hsub : (7#64 - BitVec.ofNat 64 (7 - k)) = BitVec.ofNat 64 k := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub_of_le]
        · simp only [BitVec.toNat_ofNat]; omega
        · rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega
      rw [hsub] at h
      have hand := congrArg BitVec.toNat h
      have hk_lt : (BitVec.ofNat 64 k).toNat = k := by simp only [BitVec.toNat_ofNat]; omega
      have hshr : (x >>> BitVec.ofNat 64 k).toNat = x.toNat >>> k := by
        simp [BitVec.toNat_ushiftRight, hk_lt]
      simp only [BitVec.toNat_and, hshr, show (1#64).toNat = 1 from rfl, show (0#64).toNat = 0 from rfl, Nat.and_one_is_mod] at hand
      exact hand
    have hb0 := hbit 0 (by omega); have hb1 := hbit 1 (by omega)
    have hb2 := hbit 2 (by omega); have hb3 := hbit 3 (by omega)
    have hb4 := hbit 4 (by omega); have hb5 := hbit 5 (by omega)
    have hb6 := hbit 6 (by omega); have hb7 := hbit 7 (by omega)
    simp only [Nat.shiftRight_eq_div_pow] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    omega
  intro inner
  induction clk generalizing s wj with
  | zero =>
    dsimp only [inner]
    rw [evaluateHOLFiniteState_while_total]
    split
    · rename_i cw hcond
      split
      · split
        · exact ⟨by simp, fun _ h => by simp at h⟩
        · omega
      · rename_i hcw0
        exfalso
        rw [evalHOLFinite_eq_toExact] at hcond
        obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .less _ _ cw hcond
        simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hj_loc] at hva hvb
        subst hva hvb
        by_cases hj8 : wj.toNat < 8
        · have hslt : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess wj 8#64 = true := by
            unfold Flapjack.Compiler.Encoders.Asm.holAsmSignedLess
            have h1 : wj.toNat < 2 ^ 63 := by omega
            have h2 : (8#64).toNat < 2 ^ 63 := by decide
            simp only [show 64 - 1 = 63 from rfl, if_pos h1, if_pos h2, decide_eq_true_eq]
            exact hj8
          simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hslt] at hcw
          have hcw_eq0 : cw = 0 := Classical.not_not.mp hcw0
          rw [hcw_eq0] at hcw
          exact absurd hcw (by decide)
        · have hj_eq8 : wj.toNat = 8 := by omega
          obtain ⟨r, hr, hbit⟩ := hx_has_bit
          exact hbit (hprev_zero r (by omega))
    · exact ⟨by simp, fun _ h => by simp at h⟩
  | succ clk ih =>
    dsimp only [inner]
    rw [evaluateHOLFiniteState_while_total]
    split
    · rename_i cw hcond
      split
      · rename_i hcw_nz
        split
        · exact ⟨by simp, fun _ h => by simp at h⟩
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hj_lt8 : wj.toNat < 8 := by
            rw [evalHOLFinite_eq_toExact] at hcond
            obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .less _ _ cw hcond
            simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hj_loc] at hva hvb
            subst hva hvb
            by_contra hge
            have hslt : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess wj 8#64 = false := by
              unfold Flapjack.Compiler.Encoders.Asm.holAsmSignedLess
              have h1 : wj.toNat < 2 ^ 63 := by omega
              have h2 : (8#64).toNat < 2 ^ 63 := by decide
              simp only [show 64 - 1 = 63 from rfl, if_pos h1, if_pos h2, decide_eq_false_iff_not]
              change ¬ (wj.toNat < 8)
              omega
            simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hslt] at hcw
            exact hcw_nz hcw
          let sd := decClockHOLFinite s
          have hrem := evaluateHOLFiniteState_clock_le sd
            (.seq
              (.ite (.cmp .notEqual (.op .and [.shift .lsr (.var .local (ofString "x")) (.op .sub [.const 7#64, .var .local (ofString "j")]), .const 1#64]) (.const 0#64))
                (.return (.op .add [.panop .mul [.var .local (ofString "i"), .const 8#64], .var .local (ofString "j")]))
                .skip)
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))
          have hsub_lt : (7#64 - wj).toNat = 7 - wj.toNat := by
            rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change wj.toNat ≤ 7; omega)]
            rfl
          have hev_shift : evalAt sd (.shift .lsr (.var .local (ofString "x")) (.op .sub [.const 7#64, .var .local (ofString "j")])) =
              some (.val (.word (x >>> (7#64 - wj)))) := by
            simp only [sd, decClockHOLFinite, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
              hx_loc, hj_loc, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
              valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL]
            have hlt64 : ¬ ((7#64 - wj).toNat ≠ 0 ∧ 64 ≤ (7#64 - wj).toNat) := by omega
            rw [if_neg hlt64]
            simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
            rfl
          have hev_test : evalAt sd (.cmp .notEqual (.op .and [.shift .lsr (.var .local (ofString "x")) (.op .sub [.const 7#64, .var .local (ofString "j")]), .const 1#64]) (.const 0#64)) =
              some (.val (.word (if ((x >>> (7#64 - wj)) &&& 1#64) ≠ 0#64 then 1#64 else 0#64))) :=
            evalAt_notEqual sd _ _ _ _ (evalAt_and1 sd _ _ hev_shift) rfl
          unfold evalAt at hev_test
          by_cases htest : ((x >>> (7#64 - wj)) &&& 1#64) ≠ 0#64
          · -- Returns `i * 8 + j`!
            have hbody_ret : evaluateHOLFiniteState sd
                (.seq
                  (.ite (.cmp .notEqual (.op .and [.shift .lsr (.var .local (ofString "x")) (.op .sub [.const 7#64, .var .local (ofString "j")]), .const 1#64]) (.const 0#64))
                    (.return (.op .add [.panop .mul [.var .local (ofString "i"), .const 8#64], .var .local (ofString "j")]))
                    .skip)
                  (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64]))) =
                (some (.returned (.val (.word (wi * 8#64 + wj)))), emptyLocalsHOLFinite sd) := by
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hev_test, if_pos htest]
              dsimp only
              rw [if_neg (by decide : (1#64 : BitVec 64) ≠ 0)]
              rw [evaluateHOLFiniteState_return]
              simp [sd, decClockHOLFinite, evalHOLExact, evalListHOLExact, hi_loc, hj_loc,
                valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp, shapeOfHOLExact, sizeOfShapeWithContextHOL]
            rw [hbody_ret]
            dsimp only
            refine ⟨by simp, fun v hv => ?_⟩
            injection hv with hv1; injection hv1 with hv2
            refine ⟨wj.toNat, hj_lt8, ?_⟩
            rw [← hv2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          · -- Skips and increments `j`!
            have htest0 : ((x >>> (7#64 - wj)) &&& 1#64) = 0#64 := not_not.mp htest
            have hbody_inc : evaluateHOLFiniteState sd
                (.seq
                  (.ite (.cmp .notEqual (.op .and [.shift .lsr (.var .local (ofString "x")) (.op .sub [.const 7#64, .var .local (ofString "j")]), .const 1#64]) (.const 0#64))
                    (.return (.op .add [.panop .mul [.var .local (ofString "i"), .const 8#64], .var .local (ofString "j")]))
                    .skip)
                  (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64]))) =
                (none, setVarHOLFinite (ofString "j") (.val (.word (wj + 1#64))) sd) := by
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hev_test, if_neg htest]
              simp only [show (0#64 : BitVec 64) = 0 from rfl, ↓reduceIte, evaluateHOLFiniteState_skip]
              rw [evaluateHOLFiniteState_assign]
              simp [sd, decClockHOLFinite, evalHOLExact, evalListHOLExact, hj_loc,
                valueIsWord, valueWord, wordOpHOL, wordOp, lookupKvarHOLExact,
                isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
            rw [hbody_inc] at hrem ⊢
            dsimp only
            have hwj1 : (wj + 1#64).toNat = wj.toNat + 1 := by
              rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
            apply ih (wj + 1#64) (by omega)
            · intro r hr
              by_cases hr_lt : r < wj.toNat
              · exact hprev_zero r hr_lt
              · have hr_eq : r = wj.toNat := by omega
                subst hr_eq
                simpa [BitVec.ofNat_toNat] using htest0
            · change s.clock - 1 ≤ clk; omega
            · simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx_loc, show ofString "j" ≠ ofString "x" by decide]
            · simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi_loc, show ofString "j" ≠ ofString "i" by decide]
            · simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · rename_i hcw0
        exfalso
        rw [evalHOLFinite_eq_toExact] at hcond
        obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .less _ _ cw hcond
        simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hj_loc] at hva hvb
        subst hva hvb
        by_cases hj8 : wj.toNat < 8
        · have hslt : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess wj 8#64 = true := by
            unfold Flapjack.Compiler.Encoders.Asm.holAsmSignedLess
            have h1 : wj.toNat < 2 ^ 63 := by omega
            have h2 : (8#64).toNat < 2 ^ 63 := by decide
            simp only [show 64 - 1 = 63 from rfl, if_pos h1, if_pos h2, decide_eq_true_eq]
            exact hj8
          simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hslt] at hcw
          have hcw_eq0 : cw = 0 := Classical.not_not.mp hcw0
          rw [hcw_eq0] at hcw
          exact absurd hcw (by decide)
        · obtain ⟨r, hr, hbit⟩ := hx_has_bit
          exact hbit (hprev_zero r (by omega))
    · exact ⟨by simp, fun _ h => by simp at h⟩

private theorem evalAt_xor2 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 : ExpHOL 64) (v : ValueHOL 64)
    (h : evalAt s (.op .xor [e1, e2]) = some v) :
    ∃ w1 w2 : BitVec 64, evalAt s e1 = some (.val (.word w1)) ∧
      evalAt s e2 = some (.val (.word w2)) ∧
      v = .val (.word (w1 ^^^ w2)) := by
  unfold evalAt at h ⊢
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) e1 with _ | v1
  · simp [evalHOLExact, evalListHOLExact, h1] at h
  · rcases h2 : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) e2 with _ | v2
    · simp [evalHOLExact, evalListHOLExact, h1, h2] at h
    · simp only [evalHOLExact, evalListHOLExact, h1, h2] at h
      rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _
      · simp only [List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
          valueIsWord, valueWord, wordOpHOL, wordOp, Option.some.injEq] at h
        have hz : w2 ^^^ (0 : BitVec 64) = w2 := by simp
        rw [hz] at h
        exact ⟨w1, w2, rfl, rfl, h.symm⟩
      all_goals (simp [List.all, valueIsWord] at h)

/-- Postcondition of `htab_first_diff(a, b, key_len)` when the two keys have a byte mismatch `< key_len`:
every normal return `v` is a word `d` with `d.toNat < 8 * key_len.toNat`, and `LocFrame s0 post` holds! -/
theorem htab_first_diff_ret_lt {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (a b klen : BitVec 64) (hklen_le : klen.toNat ≤ 60)
    (hdiff : ∃ k < klen.toNat, memB s0 ((a + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((b + BitVec.ofNat 64 k).toNat))
    (ha_loc : s0.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb_loc : s0.locals.lookup (ofString "b") = some (.val (.word b)))
    (hk_loc : s0.locals.lookup (ofString "key_len") = some (.val (.word klen)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_htab_first_diff)).1 =
      some (.returned v)) :
    ∃ d : BitVec 64, v = .val (.word d) ∧ d.toNat < 8 * klen.toNat := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htab_first_diff,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hret
  rw [evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  have hev0 : @evalHOLExact 64 F _ s0.toExact (fun x => Classical.propDecidable (s0.memaddrs x)) (.const 0#64) =
      some (.val (.word 0#64)) := rfl
  rw [hev0] at hret
  dsimp only at hret
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hret
  dsimp only at hret
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s0
  -- Outer loop invariant: `wi.toNat ≤ klen.toNat` and for all `r < wi.toNat`, bytes `r` of `a` and `b` are equal!
  -- Therefore the outer loop CANNOT exit normally (`none`) because at exit `wi = klen`, contradicting `hdiff`!
  -- And whenever the outer loop returns `v`, it came from `htab_first_diff_inner_loop` at `wi < klen`, so `d = wi * 8 + j < 8 * klen`!
  suffices houter : ∀ (clk : Nat) (s : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      s.clock ≤ clk →
      LocFrame s0 s →
      wi.toNat ≤ klen.toNat →
      (∀ r < wi.toNat, memB s0 ((a + BitVec.ofNat 64 r).toNat) = memB s0 ((b + BitVec.ofNat 64 r).toNat)) →
      s.locals.lookup (ofString "a") = some (.val (.word a)) →
      s.locals.lookup (ofString "b") = some (.val (.word b)) →
      s.locals.lookup (ofString "key_len") = some (.val (.word klen)) →
      s.locals.lookup (ofString "i") = some (.val (.word wi)) →
      let outer := ProgHOL.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "key_len")))
        (.dec (ofString "x") .one (.op .xor [.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i")]), .loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i")])])
          (.seq
            (.ite (.cmp .notEqual (.var .local (ofString "x")) (.const 0#64))
              (.dec (ofString "j") .one (.const 0#64)
                (.while (.cmp .less (.var .local (ofString "j")) (.const 8#64))
                  (.seq
                    (.ite (.cmp .notEqual (.op .and [.shift .lsr (.var .local (ofString "x")) (.op .sub [.const 7#64, .var .local (ofString "j")]), .const 1#64]) (.const 0#64))
                      (.return (.op .add [.panop .mul [.var .local (ofString "i"), .const 8#64], .var .local (ofString "j")]))
                      .skip)
                    (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))))
              .skip)
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))
      ((evaluateHOLFiniteState s outer).1 ≠ none) ∧
      (∀ rv, (evaluateHOLFiniteState s outer).1 = some (.returned rv) →
        ∃ d : BitVec 64, rv = .val (.word d) ∧ d.toNat < 8 * klen.toNat) by
    have hs1_out := houter s1.clock s1 0#64 le_rfl ((LocFrame.refl s0).locals _) (Nat.zero_le _)
      (fun r hr => by simp at hr)
      (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha_loc, show ofString "i" ≠ ofString "a" by decide])
      (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb_loc, show ofString "i" ≠ ofString "b" by decide])
      (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk_loc, show ofString "i" ≠ ofString "key_len" by decide])
      (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    rcases seq_ret_or_none s1 _ _ _ hret with hout_ret | ⟨m, hm, _⟩
    · exact hs1_out.2 v hout_ret
    · exact False.elim (hs1_out.1 (congrArg Prod.fst hm))
  intro clk
  induction clk with
  | zero =>
    intro s wi hclk hfr hw_le heq_prev ha hb hk hi outer
    dsimp only [outer]
    rw [evaluateHOLFiniteState_while_total]
    split
    · rename_i cw hcond
      split
      · split
        · exact ⟨by simp, fun _ h => by simp at h⟩
        · omega
      · rename_i hcw0
        exfalso
        rw [evalHOLFinite_eq_toExact] at hcond
        obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .lower _ _ cw hcond
        simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hi, hk] at hva hvb
        subst hva hvb
        by_cases hlt : wi < klen
        · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt] at hcw
          have hcw_eq0 : cw = 0 := Classical.not_not.mp hcw0
          rw [hcw_eq0] at hcw
          exact absurd hcw (by decide)
        · rw [BitVec.lt_def] at hlt
          obtain ⟨k, hk_lt, hne_k⟩ := hdiff
          exact hne_k (heq_prev k (by omega))
    · exact ⟨by simp, fun _ h => by simp at h⟩
  | succ clk ih =>
    intro s wi hclk hfr hw_le heq_prev ha hb hk hi outer
    dsimp only [outer]
    rw [evaluateHOLFiniteState_while_total]
    split
    · rename_i cw hcond
      split
      · rename_i hcw_nz
        split
        · exact ⟨by simp, fun _ h => by simp at h⟩
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hwi_lt : wi.toNat < klen.toNat := by
            rw [evalHOLFinite_eq_toExact] at hcond
            obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .lower _ _ cw hcond
            simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hi, hk] at hva hvb
            subst hva hvb
            by_contra hge
            have hnlt : ¬ (wi < klen) := by rw [BitVec.lt_def]; omega
            simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt] at hcw
            exact hcw_nz hcw
          let sd := decClockHOLFinite s
          have hfr_sd : LocFrame s0 sd := by unfold LocFrame at hfr ⊢; dsimp only [sd, decClockHOLFinite]; rw [hfr]
          have hmem_sd : sd.memory = s0.memory := by unfold LocFrame at hfr_sd; rw [hfr_sd]
          have hbe_sd : sd.be = s0.be := by unfold LocFrame at hfr_sd; rw [hfr_sd]
          -- Evaluate `dec "x"` on `sd`
          let body := ProgHOL.dec (ofString "x") .one (.op .xor [.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i")]), .loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i")])])
            (.seq
              (.ite (.cmp .notEqual (.var .local (ofString "x")) (.const 0#64))
                (.dec (ofString "j") .one (.const 0#64)
                  (.while (.cmp .less (.var .local (ofString "j")) (.const 8#64))
                    (.seq
                      (.ite (.cmp .notEqual (.op .and [.shift .lsr (.var .local (ofString "x")) (.op .sub [.const 7#64, .var .local (ofString "j")]), .const 1#64]) (.const 0#64))
                        (.return (.op .add [.panop .mul [.var .local (ofString "i"), .const 8#64], .var .local (ofString "j")]))
                        .skip)
                      (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))))
                .skip)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))
          have hrem := evaluateHOLFiniteState_clock_le sd body
          have hnc := evaluate_noTopContinue body rfl sd
          have hnb := evaluate_noBreak body rfl sd
          -- Inspect evaluation of `dec "x"`
          rcases hbr : evaluateHOLFiniteState sd body with ⟨rb, mid⟩
          rw [hbr] at hrem hnc hnb
          dsimp only at hrem hnc hnb
          have hbody_analysis :
              (rb = none →
                LocFrame s0 mid ∧
                memB s0 ((a + wi).toNat) = memB s0 ((b + wi).toNat) ∧
                mid.locals.lookup (ofString "a") = some (.val (.word a)) ∧
                mid.locals.lookup (ofString "b") = some (.val (.word b)) ∧
                mid.locals.lookup (ofString "key_len") = some (.val (.word klen)) ∧
                mid.locals.lookup (ofString "i") = some (.val (.word (wi + 1#64)))) ∧
              (∀ rv, rb = some (.returned rv) →
                ∃ d : BitVec 64, rv = .val (.word d) ∧ d.toNat < 8 * klen.toNat) := by
            have hbr' := hbr
            dsimp only [body] at hbr'
            rw [evaluateHOLFiniteState_dec_total] at hbr'
            dsimp only at hbr'
            split at hbr'
            · injection hbr' with hr _; subst hr; exact ⟨fun h => by simp at h, fun _ h => by simp at h⟩
            · rename_i xv hxv
              split at hbr'
              · -- `xv` evaluated! Extract `xv = .val (.word x)` where `x = ba ^^^ bb`!
                have h_ea : evalAt sd (.op .add [.var .local (ofString "a"), .var .local (ofString "i")]) =
                    some (.val (.word (a + wi))) := by
                  simp [sd, decClockHOLFinite, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ha, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
                have h_eb : evalAt sd (.op .add [.var .local (ofString "b"), .var .local (ofString "i")]) =
                    some (.val (.word (b + wi))) := by
                  simp [sd, decClockHOLFinite, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
                have hxv_word : ∃ x : BitVec 64,
                    xv = .val (.word x) ∧
                    x = (BitVec.ofNat 64 (memB s0 (a + wi).toNat)) ^^^ (BitVec.ofNat 64 (memB s0 (b + wi).toNat)) ∧
                    x.toNat < 256 := by
                  obtain ⟨w1, w2, hlba, hlbb, rfl⟩ := evalAt_xor2 sd _ _ xv hxv
                  obtain ⟨_, hw1⟩ := memB_of_eval_loadByte sd _ (a + wi) (.val (.word w1)) h_ea hlba
                  obtain ⟨_, hw2⟩ := memB_of_eval_loadByte sd _ (b + wi) (.val (.word w2)) h_eb hlbb
                  injection hw1 with hw1'; injection hw1' with hw1''
                  injection hw2 with hw2'; injection hw2' with hw2''
                  subst hw1'' hw2''
                  have hmba : memB sd (a + wi).toNat = memB s0 (a + wi).toNat := by simp [memB, hmem_sd, hbe_sd]
                  have hmbb : memB sd (b + wi).toNat = memB s0 (b + wi).toNat := by simp [memB, hmem_sd, hbe_sd]
                  rw [hmba, hmbb]
                  refine ⟨_, rfl, rfl, ?_⟩
                  have h1 : memB s0 (a + wi).toNat < 256 := by
                    unfold memB; rcases s0.memory _ with ⟨w⟩; exact UInt8.toNat_lt_size _
                  have h2 : memB s0 (b + wi).toNat < 256 := by
                    unfold memB; rcases s0.memory _ with ⟨w⟩; exact UInt8.toNat_lt_size _
                  have hbvxor : ((BitVec.ofNat 64 (memB s0 (a + wi).toNat)) ^^^ (BitVec.ofNat 64 (memB s0 (b + wi).toNat))).toNat =
                      (BitVec.ofNat 8 (memB s0 (a + wi).toNat) ^^^ BitVec.ofNat 8 (memB s0 (b + wi).toNat)).toNat := by
                    simp only [BitVec.toNat_xor, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega : memB s0 (a + wi).toNat < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : memB s0 (b + wi).toNat < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : memB s0 (a + wi).toNat < 2 ^ 8),
                      Nat.mod_eq_of_lt (by omega : memB s0 (b + wi).toNat < 2 ^ 8)]
                  rw [hbvxor]
                  exact (BitVec.ofNat 8 (memB s0 (a + wi).toNat) ^^^ BitVec.ofNat 8 (memB s0 (b + wi).toNat)).isLt
                obtain ⟨x, rfl, hx_xor, hx_lt⟩ := hxv_word
                set sx := setVarHOLFinite (ofString "x") (.val (.word x)) sd
                by_cases hxz : x = 0#64
                · -- `x = 0`: bytes match! `ite` takes `.skip`, `i` increments to `wi + 1`!
                  subst hxz
                  have heval_sx : evaluateHOLFiniteState sx
                      (.seq
                        (.ite (.cmp .notEqual (.var .local (ofString "x")) (.const 0#64))
                          (.dec (ofString "j") .one (.const 0#64)
                            (.while (.cmp .less (.var .local (ofString "j")) (.const 8#64))
                              (.seq
                                (.ite (.cmp .notEqual (.op .and [.shift .lsr (.var .local (ofString "x")) (.op .sub [.const 7#64, .var .local (ofString "j")]), .const 1#64]) (.const 0#64))
                                  (.return (.op .add [.panop .mul [.var .local (ofString "i"), .const 8#64], .var .local (ofString "j")]))
                                  .skip)
                                (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))))
                          .skip)
                        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))) =
                      (none, setVarHOLFinite (ofString "i") (.val (.word (wi + 1#64))) sx) := by
                    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
                    have hx_lk : sx.locals.lookup (ofString "x") = some (.val (.word 0#64)) := by
                      simp [sx, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    have hi_lk : sx.locals.lookup (ofString "i") = some (.val (.word wi)) := by
                      simp [sx, sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi, show ofString "x" ≠ ofString "i" by decide]
                    simp [PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hx_lk, hi_lk,
                      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, evaluateHOLFiniteState_skip,
                      evaluateHOLFiniteState_assign, valueIsWord, valueWord, wordOpHOL, wordOp,
                      lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
                  rw [heval_sx] at hbr'
                  dsimp only at hbr'
                  injection hbr' with hrb hmid
                  subst hrb
                  rw [← hmid]
                  have heq_bytes : memB s0 (a + wi).toNat = memB s0 (b + wi).toNat := by
                    have h0 := BitVec.xor_eq_zero_iff.mp hx_xor.symm
                    have h0_nat := congrArg BitVec.toNat h0
                    have h1 : memB s0 (a + wi).toNat < 256 := by unfold memB; rcases s0.memory _ with ⟨w⟩; exact UInt8.toNat_lt_size _
                    have h2 : memB s0 (b + wi).toNat < 256 := by unfold memB; rcases s0.memory _ with ⟨w⟩; exact UInt8.toNat_lt_size _
                    simp only [BitVec.toNat_ofNat] at h0_nat
                    omega
                  refine ⟨fun _ => ⟨hfr_sd.locals _ |>.locals _ |>.locals _, heq_bytes, ?_, ?_, ?_, ?_⟩, fun _ h => by simp at h⟩
                  · rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)]
                    simp [sx, sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha,
                      show ofString "i" ≠ ofString "a" by decide, show ofString "x" ≠ ofString "a" by decide]
                  · rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)]
                    simp [sx, sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb,
                      show ofString "i" ≠ ofString "b" by decide, show ofString "x" ≠ ofString "b" by decide]
                  · rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)]
                    simp [sx, sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk,
                      show ofString "i" ≠ ofString "key_len" by decide, show ofString "x" ≠ ofString "key_len" by decide]
                  · rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)]
                    simp [sx, sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                · -- `x ≠ 0`: `ite` enters `dec "j" := 0; while j < 8 ...`, which NEVER flows (`≠ none`) and returns `wi * 8 + j`!
                  have hx_lk : sx.locals.lookup (ofString "x") = some (.val (.word x)) := by
                    simp [sx, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hi_lk : sx.locals.lookup (ofString "i") = some (.val (.word wi)) := by
                    simp [sx, sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi, show ofString "x" ≠ ofString "i" by decide]
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hbr'
                  have hc_ne : @evalHOLExact 64 F _ sx.toExact (fun addr => Classical.propDecidable (sx.memaddrs addr))
                      (.cmp .notEqual (.var .local (ofString "x")) (.const 0#64)) = some (.val (.word 1#64)) := by
                    simp [PanSemStateFiniteExact.toExact, evalHOLExact, hx_lk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hxz]
                  rw [hc_ne] at hbr'
                  dsimp only at hbr'
                  rw [if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hbr'
                  rw [evaluateHOLFiniteState_dec_total] at hbr'
                  dsimp only at hbr'
                  have hevj0 : @evalHOLExact 64 F _ sx.toExact (fun addr => Classical.propDecidable (sx.memaddrs addr)) (.const 0#64) =
                      some (.val (.word 0#64)) := rfl
                  rw [hevj0] at hbr'
                  dsimp only at hbr'
                  rw [if_pos hsh0] at hbr'
                  dsimp only at hbr'
                  set sj := setVarHOLFinite (ofString "j") (.val (.word 0#64)) sx
                  set innerProg := ProgHOL.while (.cmp .less (.var .local (ofString "j")) (.const 8#64))
                    (.seq
                      (.ite (.cmp .notEqual (.op .and [.shift .lsr (.var .local (ofString "x")) (.op .sub [.const 7#64, .var .local (ofString "j")]), .const 1#64]) (.const 0#64))
                        (.return (.op .add [.panop .mul [.var .local (ofString "i"), .const 8#64], .var .local (ofString "j")]))
                        .skip)
                      (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))
                  have hinner := htab_first_diff_inner_loop x 0#64 wi hx_lt hxz (Nat.zero_le _)
                    (fun r hr => by simp at hr) sj.clock sj le_rfl
                    (by simp [sj, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx_lk, show ofString "j" ≠ ofString "x" by decide])
                    (by simp [sj, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi_lk, show ofString "j" ≠ ofString "i" by decide])
                    (by simp [sj, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
                  change (evaluateHOLFiniteState sj innerProg).1 ≠ none ∧
                    (∀ v, (evaluateHOLFiniteState sj innerProg).1 = some (.returned v) →
                      ∃ j < 8, v = .val (.word (wi * 8#64 + BitVec.ofNat 64 j))) at hinner
                  rcases hin_r : evaluateHOLFiniteState sj innerProg with ⟨rin, min⟩
                  rw [hin_r] at hinner hbr'
                  dsimp only at hinner hbr'
                  cases rin with
                  | none => exact False.elim (hinner.1 rfl)
                  | some rin' =>
                    dsimp only at hbr'
                    injection hbr' with hrb _
                    subst hrb
                    refine ⟨fun h => by simp at h, fun rv hrv => ?_⟩
                    obtain ⟨j, hj8, hjv⟩ := hinner.2 rv hrv
                    refine ⟨wi * 8#64 + BitVec.ofNat 64 j, hjv, ?_⟩
                    have hmul8 : (wi * 8#64).toNat = wi.toNat * 8 := by
                      rw [BitVec.toNat_mul, show (8#64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
                    rw [BitVec.toNat_add, hmul8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                    omega
              · injection hbr' with hr _; subst hr; exact ⟨fun h => by simp at h, fun _ h => by simp at h⟩
          cases rb with
          | none =>
            obtain ⟨hfr_m, heq_wi, ha_m, hb_m, hk_m, hi_m⟩ := hbody_analysis.1 rfl
            have hw1 : (wi + 1#64).toNat = wi.toNat + 1 := by
              rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
            exact ih mid (wi + 1#64) (by change mid.clock ≤ s.clock - 1 at hrem; omega)
              hfr_m (by omega)
              (fun r hr => by
                by_cases hlt : r < wi.toNat
                · exact heq_prev r hlt
                · have hreq : r = wi.toNat := by omega
                  subst hreq
                  simpa [BitVec.ofNat_toNat] using heq_wi)
              ha_m hb_m hk_m hi_m
          | some r =>
            cases r with
            | «continue» => exact absurd rfl hnc
            | «break» => exact absurd rfl hnb
            | returned rv => exact ⟨by simp, fun rv' h => by injection h with h1; injection h1 with h2; subst h2; exact hbody_analysis.2 rv rfl⟩
            | _ => exact ⟨by simp, fun _ h => by simp at h⟩
      · rename_i hcw0
        exfalso
        rw [evalHOLFinite_eq_toExact] at hcond
        obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .lower _ _ cw hcond
        simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hi, hk] at hva hvb
        subst hva hvb
        by_cases hlt : wi < klen
        · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt] at hcw
          have hcw_eq0 : cw = 0 := Classical.not_not.mp hcw0
          rw [hcw_eq0] at hcw
          exact absurd hcw (by decide)
        · rw [BitVec.lt_def] at hlt
          obtain ⟨k, hk_lt, hne_k⟩ := hdiff
          exact hne_k (heq_prev k (by omega))
    · exact ⟨by simp, fun _ h => by simp at h⟩

/-! ### 6c. `memcpy` write-frame and byte-copy postcondition on normal return -/

def MemCopyRel {F : Type} (s0 s : PanSemStateFiniteExact 64 F) (dst src : BitVec 64) (len done : Nat) : Prop :=
  s.code = s0.code ∧ s.memaddrs = s0.memaddrs ∧ s.shMemaddrs = s0.shMemaddrs ∧
  s.baseAddr = s0.baseAddr ∧ s.be = s0.be ∧ s.globals = s0.globals ∧
  FrameOutside s0 s [(dst.toNat, len)] (0, 0) ∧
  (∀ k < done, memB s ((dst + BitVec.ofNat 64 k).toNat) = memB s0 ((src + BitVec.ofNat 64 k).toNat)) ∧
  (∀ a : Nat, a < 2 ^ 64 → ¬ InIvl a (dst.toNat, len) → memB s a = memB s0 a)

theorem memCopyRel_refl {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst src : BitVec 64) (len : Nat) :
    MemCopyRel s0 s0 dst src len 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ h => by omega, fun _ _ _ => rfl⟩

theorem memCopyRel_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst src : BitVec 64} {len done : Nat}
    (h : MemCopyRel s0 s dst src len done) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    MemCopyRel s0 { s with locals := L, clock := k } dst src len done :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

private theorem memcpy_store_word_step {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 src0 : BitVec 64} {len off : Nat}
    (hd8 : dst0.toNat % 8 = 0) (hs8 : src0.toNat % 8 = 0) (hoff8 : off % 8 = 0)
    (hoff_le : off + 8 ≤ len)
    (hd_nw : dst0.toNat + len < 2 ^ 64) (hs_nw : src0.toNat + len < 2 ^ 64)
    (hdisj : Disj (dst0.toNat, len) (src0.toNat, len))
    (hrel : MemCopyRel s0 s dst0 src0 len off)
    (ed es : ExpHOL 64)
    (hed : evalAt s ed = some (.val (.word (dst0 + BitVec.ofNat 64 off))))
    (hes : evalAt s es = some (.val (.word (src0 + BitVec.ofNat 64 off))))
    (hnone : (evaluateHOLFiniteState s (.store ed (.load .one es))).1 = none) :
    MemCopyRel s0 (evaluateHOLFiniteState s (.store ed (.load .one es))).2 dst0 src0 len (off + 8) := by
  obtain ⟨hc, hm, hsh, hba, hbe, hg, hfr, hcopied, hout⟩ := hrel
  rw [evaluateHOLFiniteState_store] at hnone ⊢
  unfold evalAt at hed hes
  rw [hed] at hnone ⊢
  dsimp only at hnone ⊢
  revert hnone
  split
  · rename_i v hld
    intro hnone
    obtain ⟨hdom_s, hv_eq⟩ := memW_of_eval_load s es (src0 + BitVec.ofNat 64 off) v hes hld
    subst hv_eq
    set x := dst0 + BitVec.ofNat 64 off
    set y := src0 + BitVec.ofNat 64 off
    have hx_nat : x.toNat = dst0.toNat + off := by
      simp only [x, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hy_nat : y.toNat = src0.toNat + off := by
      simp only [y, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    by_cases hdom_x : s.memaddrs x
    · have hst : @panMemStoresHOL 64 _ x (flattenHOL (.val (.word (BitVec.ofNat 64 (memW s y.toNat)))))
          s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.memory =
          some (fun c => if c = x then .word (BitVec.ofNat 64 (memW s y.toNat)) else s.memory c) := by
        simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_x]
      rw [hst]
      dsimp only
      set s' : PanSemStateFiniteExact 64 F :=
        { s with memory := fun c => if c = x then .word (BitVec.ofNat 64 (memW s y.toNat)) else s.memory c }
      have hmwy_eq : memW s y.toNat = memW s0 y.toNat := by
        apply (memW_eq_iff_memB hbe (by omega) (by omega) (by omega) (by omega)).mpr
        intro r hr
        apply hout _ (by omega)
        unfold InIvl; unfold Disj at hdisj; omega
      have hmwx_s' : memW s' x.toNat = memW s0 y.toNat := by
        have hbx : BitVec.ofNat 64 x.toNat = x := by simp
        unfold memW
        simp only [s', hbx, ↓reduceIte, hmwy_eq]
        have hlt_w : memW s0 y.toNat < 2 ^ 64 := by
          unfold memW; rcases s0.memory _ with ⟨w⟩; exact w.isLt
        exact Nat.mod_eq_of_lt hlt_w
      have hbe' : s'.be = s0.be := hbe
      have hbytes_xy : ∀ r < 8, memB s' (x.toNat + r) = memB s0 (y.toNat + r) :=
        (memW_eq_iff_memB hbe' (by omega) (by omega) (by omega) (by omega)).mp hmwx_s'
      have hother_byte : ∀ a : Nat, a < 2 ^ 64 → ¬ (x.toNat ≤ a ∧ a < x.toNat + 8) →
          memB s' a = memB s a := by
        intro a ha_lt hnot
        have hal_ne : panByteAlignHOL (BitVec.ofNat 64 a) ≠ x := by
          intro heq
          have hp := panByteAlign_toNat64 (BitVec.ofNat 64 a)
          rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at hp
          omega
        simp [memB, s', hal_ne]
      refine ⟨hc, hm, hsh, hba, hbe, hg, ?_, ?_, ?_⟩
      · intro c hk hf
        by_cases hcx : c = x
        · exfalso; subst hcx
          exact hk (dst0.toNat, len) (List.mem_singleton.2 rfl) ⟨by omega, by omega⟩
        · simp only [s', hcx, ↓reduceIte]
          exact hfr c hk hf
      · intro k hk
        have hdk : (dst0 + BitVec.ofNat 64 k).toNat = dst0.toNat + k := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        have hsk : (src0 + BitVec.ofNat 64 k).toNat = src0.toNat + k := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        by_cases hk_old : k < off
        · rw [hdk, hother_byte (dst0.toNat + k) (by omega) (by omega), ← hdk]
          exact hcopied k hk_old
        · have hr_lt : k - off < 8 := by omega
          have hd_eq : dst0.toNat + k = x.toNat + (k - off) := by omega
          have hs_eq : src0.toNat + k = y.toNat + (k - off) := by omega
          rw [hdk, hsk, hd_eq, hs_eq]
          exact hbytes_xy (k - off) hr_lt
      · intro a ha_lt hnot_in
        rw [hother_byte a ha_lt (by unfold InIvl at hnot_in; omega)]
        exact hout a ha_lt hnot_in
    · simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_x] at hnone
  · intro hnone; simp at hnone

private theorem memcpy_store_byte_step {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 src0 : BitVec 64} {len off : Nat}
    (hoff_lt : off < len)
    (hd_nw : dst0.toNat + len < 2 ^ 64) (hs_nw : src0.toNat + len < 2 ^ 64)
    (hdisj : Disj (dst0.toNat, len) (src0.toNat, len))
    (hrel : MemCopyRel s0 s dst0 src0 len off)
    (ed es : ExpHOL 64)
    (hed : evalAt s ed = some (.val (.word (dst0 + BitVec.ofNat 64 off))))
    (hes : evalAt s es = some (.val (.word (src0 + BitVec.ofNat 64 off))))
    (hnone : (evaluateHOLFiniteState s (.storeByte ed (.loadByte es))).1 = none) :
    MemCopyRel s0 (evaluateHOLFiniteState s (.storeByte ed (.loadByte es))).2 dst0 src0 len (off + 1) := by
  obtain ⟨hc, hm, hsh, hba, hbe, hg, hfr, hcopied, hout⟩ := hrel
  rw [evaluateHOLFiniteState_storeByte] at hnone ⊢
  unfold evalAt at hed hes
  rw [hed] at hnone ⊢
  dsimp only at hnone ⊢
  revert hnone
  split
  · rename_i vw hlb
    obtain ⟨_, hv_eq⟩ := memB_of_eval_loadByte s es (src0 + BitVec.ofNat 64 off) (.val (.word vw)) hes hlb
    injection hv_eq with hv1; injection hv1 with hv2
    subst hv2
    set x := dst0 + BitVec.ofNat 64 off
    set y := src0 + BitVec.ofNat 64 off
    have hx_nat : x.toNat = dst0.toNat + off := by
      simp only [x, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hy_nat : y.toNat = src0.toNat + off := by
      simp only [y, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    split
    · rename_i mem' hst
      intro _
      dsimp only
      set s' : PanSemStateFiniteExact 64 F := { s with memory := mem' }
      have hby_s : memB s y.toNat = memB s0 y.toNat := by
        apply hout _ (by omega)
        unfold InIvl; unfold Disj at hdisj; omega
      have hbw_val : (BitVec.ofNat 8 (BitVec.ofNat 64 (memB s y.toNat)).toNat).toNat = memB s0 y.toNat := by
        have hlt256 : memB s0 y.toNat < 256 := by
          unfold memB; rcases s0.memory _ with ⟨w⟩; exact UInt8.toNat_lt_size _
        rw [hby_s, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega
      obtain ⟨hsame, hdiff⟩ := @panMemStoreByte_other_byte s.memory s.memaddrs
        (fun addr => Classical.propDecidable (s.memaddrs addr)) s.be x
        (BitVec.ofNat 8 (BitVec.ofNat 64 (memB s y.toNat)).toNat) mem' hst
      have hcell_frame : ∀ c : BitVec 64, c ≠ panByteAlignHOL x → mem' c = s.memory c := by
        intro c hne
        have hst' := hst
        unfold panMemStoreByteWord8HOL at hst'
        rcases s.memory (panByteAlignHOL x) with ⟨cell⟩
        dsimp only at hst'
        split at hst'
        · injection hst' with hmeq; subst hmeq; simp [hne]
        · cases hst'
      refine ⟨hc, hm, hsh, hba, hbe, hg, ?_, ?_, ?_⟩
      · intro c hk hf
        by_cases hcx : c = panByteAlignHOL x
        · exfalso; subst hcx
          apply hk (dst0.toNat, len) (List.mem_singleton.2 rfl)
          unfold CellHits
          rw [panByteAlign_toNat64]
          omega
        · change mem' c = s0.memory c
          rw [hcell_frame c hcx]
          exact hfr c hk hf
      · intro k hk
        have hdk : (dst0 + BitVec.ofNat 64 k).toNat = dst0.toNat + k := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        have hsk : (src0 + BitVec.ofNat 64 k).toNat = src0.toNat + k := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        by_cases hk_old : k < off
        · have hne : BitVec.ofNat 64 ((dst0 + BitVec.ofNat 64 k).toNat) ≠ x := by
            intro heq
            have := congrArg BitVec.toNat heq
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
            omega
          have hob := hdiff _ hne
          change memB s' ((dst0 + BitVec.ofNat 64 k).toNat) = memB s ((dst0 + BitVec.ofNat 64 k).toNat) at hob
          exact hob.trans (hcopied k hk_old)
        · have hk_eq : k = off := by omega
          subst hk_eq
          have hbx : BitVec.ofNat 64 x.toNat = x := by simp
          change (match mem' (panByteAlignHOL (BitVec.ofNat 64 x.toNat)) with | .word v => (panGetByteHOL (BitVec.ofNat 64 x.toNat) v s.be).toNat) = memB s0 y.toNat
          rw [hbx, hsame, hbw_val]
      · intro a ha_lt hnot_in
        have hne : BitVec.ofNat 64 a ≠ x := by
          intro heq
          have := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at this
          unfold InIvl at hnot_in
          omega
        have hob := hdiff _ hne
        change memB s' a = memB s a at hob
        exact hob.trans (hout a ha_lt hnot_in)
    · intro hnone; simp at hnone
  · intro hnone; simp at hnone

private def noReturnOrRaise : ProgHOL 64 → Bool
  | .seq a b => noReturnOrRaise a && noReturnOrRaise b
  | .ite _ a b => noReturnOrRaise a && noReturnOrRaise b
  | .while _ a => noReturnOrRaise a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noReturn {F : Type} (p : ProgHOL 64) (hp : noReturnOrRaise p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturnOrRaise] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | seq a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturn a hab.1 s v
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    have mclk : m.clock ≤ s.clock := rem
    cases r with
    | none => exact evaluate_noReturn b hab.2 m v
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturn b hab.2 s v
      · exact evaluate_noReturn a hab.1 s v
    · simp
  | «while» cond body =>
    have hb : noReturnOrRaise body = true := by simpa [shape, noReturnOrRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturn body hb (decClockHOLFinite s) v
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none => exact evaluate_noReturn (.while cond body) (by simpa [noReturnOrRaise] using hb) mid v
          | some r1 =>
            cases r1 with
            | «continue» => exact evaluate_noReturn (.while cond body) (by simpa [noReturnOrRaise] using hb) mid v
            | returned _ => exact ih1
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, noReturnOrRaise] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

private theorem memcpy_while_loop {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (dst src n : BitVec 64) (hn_small : n.toNat + 32 < 2 ^ 63)
    (step : BitVec 64) (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnc : noTopContinue body = true) (hnb : noBreak body = true)
    (Pmod : BitVec 64 → Prop)
    (hcond : (cond = .cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const step]) ∧ (step = 32#64 ∨ step = 8#64)) ∨
             (cond = .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")) ∧ step = 1#64))
    (hbody_spec : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      MemCopyRel s0 st dst src n.toNat wi.toNat →
      wi.toNat + step.toNat ≤ n.toNat →
      Pmod wi →
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "src") = some (.val (.word src)) →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      (evaluateHOLFiniteState st body).1 = none →
      MemCopyRel s0 (evaluateHOLFiniteState st body).2 dst src n.toNat (wi.toNat + step.toNat) ∧
      (evaluateHOLFiniteState st body).2.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      (evaluateHOLFiniteState st body).2.locals.lookup (ofString "src") = some (.val (.word src)) ∧
      (evaluateHOLFiniteState st body).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      (evaluateHOLFiniteState st body).2.locals.lookup (ofString "i") = some (.val (.word (wi + step))))
    (hPmod_step : ∀ wi : BitVec 64, Pmod wi → wi.toNat + step.toNat ≤ n.toNat → Pmod (wi + step))
    (clk : Nat) (s u : PanSemStateFiniteExact 64 F) (wi : BitVec 64)
    (hclk : s.clock ≤ clk)
    (hrel : MemCopyRel s0 s dst src n.toNat wi.toNat)
    (hwi_le : wi.toNat ≤ n.toNat) (hP : Pmod wi)
    (hd_loc : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hs_loc : s.locals.lookup (ofString "src") = some (.val (.word src)))
    (hn_loc : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi_loc : s.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, u)) :
    ∃ wi' : BitVec 64,
      MemCopyRel s0 u dst src n.toNat wi'.toNat ∧
      wi'.toNat ≤ n.toNat ∧ Pmod wi' ∧
      (cond = .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")) → wi'.toNat = n.toNat) ∧
      u.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      u.locals.lookup (ofString "src") = some (.val (.word src)) ∧
      u.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      u.locals.lookup (ofString "i") = some (.val (.word wi')) := by
  induction clk generalizing s wi with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond_ev
      split at hrun
      · split at hrun
        · simp at hrun
        · omega
      · rename_i hcw0
        injection hrun with _ hu; subst hu
        refine ⟨wi, hrel, hwi_le, hP, ?_, hd_loc, hs_loc, hn_loc, hi_loc⟩
        intro hc_low
        rw [evalHOLFinite_eq_toExact, hc_low] at hcond_ev
        obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .lower _ _ cw hcond_ev
        simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hi_loc, hn_loc] at hva hvb
        subst hva hvb
        by_cases hlt : wi < n
        · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt] at hcw
          have hcw_eq0 : cw = 0 := Classical.not_not.mp hcw0
          rw [hcw_eq0] at hcw
          exact absurd hcw (by decide)
        · rw [BitVec.lt_def] at hlt; omega
    · simp at hrun
  | succ clk ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond_ev
      split at hrun
      · rename_i hcw_nz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have hstep_le : wi.toNat + step.toNat ≤ n.toNat := by
            rw [evalHOLFinite_eq_toExact] at hcond_ev
            rcases hcond with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .notLower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hn_loc, hi_loc, valueIsWord, valueWord, wordOpHOL, wordOp] at hva hvb
              subst hva hvb
              have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
              change wi.toNat + (32#64 : BitVec 64).toNat ≤ n.toNat
              rw [h32]
              have hadd : (wi + 32#64).toNat = wi.toNat + 32 := by rw [BitVec.toNat_add, h32, Nat.mod_eq_of_lt (by omega)]
              by_contra hgt
              have hnle : ¬ (wi + 32#64 ≤ n) := by rw [BitVec.le_def, hadd]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnle] at hcw
              exact hcw_nz hcw
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .notLower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hn_loc, hi_loc, valueIsWord, valueWord, wordOpHOL, wordOp] at hva hvb
              subst hva hvb
              have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
              change wi.toNat + (8#64 : BitVec 64).toNat ≤ n.toNat
              rw [h8]
              have hadd : (wi + 8#64).toNat = wi.toNat + 8 := by rw [BitVec.toNat_add, h8, Nat.mod_eq_of_lt (by omega)]
              by_contra hgt
              have hnle : ¬ (wi + 8#64 ≤ n) := by rw [BitVec.le_def, hadd]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnle] at hcw
              exact hcw_nz hcw
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .lower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hn_loc, hi_loc] at hva hvb
              subst hva hvb
              have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
              change wi.toNat + (1#64 : BitVec 64).toNat ≤ n.toNat
              rw [h1]
              by_contra hgt
              have hnlt : ¬ (wi < n) := by rw [BitVec.lt_def]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt] at hcw
              exact hcw_nz hcw
          let sd := decClockHOLFinite s
          have hrel_sd : MemCopyRel s0 sd dst src n.toNat wi.toNat := memCopyRel_locals_clock hrel s.locals (s.clock - 1)
          have hnc' := evaluate_noTopContinue body hnc sd
          have hnb' := evaluate_noBreak body hnb sd
          have hrem := evaluateHOLFiniteState_clock_le sd body
          rcases hbr : evaluateHOLFiniteState sd body with ⟨rb, mid⟩
          rw [hbr] at hrun hnc' hnb' hrem
          cases rb with
          | none =>
            have hb := hbody_spec sd wi hrel_sd hstep_le hP
              hd_loc hs_loc hn_loc hi_loc (by rw [hbr])
            rw [hbr] at hb
            obtain ⟨hrel_m, hd_m, hs_m, hn_m, hi_m⟩ := hb
            have h263 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
            have hw_add : (wi + step).toNat = wi.toNat + step.toNat := by
              rcases hcond with ⟨_, rfl | rfl⟩ | ⟨_, rfl⟩
              · rw [BitVec.toNat_add, show (32#64).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
              · rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
              · rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
            rw [← hw_add] at hrel_m
            exact ih mid (wi + step) (by change mid.clock ≤ s.clock - 1 at hrem; omega)
              hrel_m (by omega) (hPmod_step wi hP hstep_le) hd_m hs_m hn_m hi_m hrun
          | some r =>
            cases r with
            | «continue» => exact absurd rfl hnc'
            | «break» => exact absurd rfl hnb'
            | _ => simp at hrun
      · rename_i hcw0
        injection hrun with _ hu; subst hu
        refine ⟨wi, hrel, hwi_le, hP, ?_, hd_loc, hs_loc, hn_loc, hi_loc⟩
        intro hc_low
        rw [evalHOLFinite_eq_toExact, hc_low] at hcond_ev
        obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .lower _ _ cw hcond_ev
        simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hi_loc, hn_loc] at hva hvb
        subst hva hvb
        by_cases hlt : wi < n
        · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt] at hcw
          have hcw_eq0 : cw = 0 := Classical.not_not.mp hcw0
          rw [hcw_eq0] at hcw
          exact absurd hcw (by decide)
        · rw [BitVec.lt_def] at hlt; omega
    · simp at hrun

/-- Full postcondition of `memcpy(dst, src, n)` on normal return when `(dst, n)` and `(src, n)` are
disjoint and do not wrap `2^64` (`n + 32 < 2^63`):
- preserves metadata, `be`, and `globals`;
- `FrameOutside s0 post [(dst.toNat, n.toNat)] (0, 0)`;
- copies all `k < n.toNat` bytes: `memB post ((dst + k).toNat) = memB s0 ((src + k).toNat)`;
- preserves all bytes outside `(dst.toNat, n.toNat)`. -/
theorem memcpy_body_spec {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (dst src n : BitVec 64)
    (hd_nw : dst.toNat + n.toNat < 2 ^ 64)
    (hs_nw : src.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hdisj : Disj (dst.toNat, n.toNat) (src.toNat, n.toNat))
    (hd_loc : s0.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hs_loc : s0.locals.lookup (ofString "src") = some (.val (.word src)))
    (hn_loc : s0.locals.lookup (ofString "n") = some (.val (.word n)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).1 =
      some (.returned v)) :
    v = .val (.word 0#64) ∧
    MemCopyRel s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).2
      dst src n.toNat n.toNat := by
  have ed_i : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
        some (.val (.word (dst + BitVec.ofNat 64 wi.toNat))) := by
    intro st wi hd hi
    simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hd, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
  have es_i : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      st.locals.lookup (ofString "src") = some (.val (.word src)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]) =
        some (.val (.word (src + BitVec.ofNat 64 wi.toNat))) := by
    intro st wi hs hi
    simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hs, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
  have ed_ik : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64) (off : Nat),
      wi.toNat + off ≤ n.toNat →
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (dst + BitVec.ofNat 64 (wi.toNat + off)))) := by
    intro st wi off hle hd hi
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hd, hi,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have h263 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hz]
    omega
  have es_ik : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64) (off : Nat),
      wi.toNat + off ≤ n.toNat →
      st.locals.lookup (ofString "src") = some (.val (.word src)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (src + BitVec.ofNat 64 (wi.toNat + off)))) := by
    intro st wi off hle hs hi
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hs, hi,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have h263 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hz]
    omega
  have store_keep_locals : ∀ {st m : PanSemStateFiniteExact 64 F} {p : ProgHOL 64},
      (∃ a b, p = .store a b ∨ p = .storeByte a b) →
      evaluateHOLFiniteState st p = (none, m) →
      m.locals = st.locals := by
    intro st m p hp hm
    rcases hp with ⟨a, b, rfl | rfl⟩
    · have := (evaluate_store_control_frame st a b).2.1; rw [hm] at this; exact this
    · have := (evaluate_storeByte_control_frame st a b).2.2.1; rw [hm] at this; exact this
  have assign_inc_ok : ∀ (st : PanSemStateFiniteExact 64 F) (wi step : BitVec 64) (done : Nat),
      MemCopyRel s0 st dst src n.toNat done →
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "src") = some (.val (.word src)) →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      MemCopyRel s0 (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2 dst src n.toNat done ∧
      (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "src") = some (.val (.word src)) ∧
      (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "i") = some (.val (.word (wi + step))) := by
    intro st wi step done hrel hd hs hn hi
    have hrun : evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step])) =
        (none, setVarHOLFinite (ofString "i") (.val (.word (wi + step))) st) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hrun]
    refine ⟨memCopyRel_locals_clock hrel _ st.clock, ?_, ?_, ?_, ?_⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd, show ofString "i" ≠ ofString "dst" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs, show ofString "i" ≠ ofString "src" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hret ⊢
  rw [evaluateHOLFiniteState_dec_total] at hret ⊢
  dsimp only at hret ⊢
  have hev0 : @evalHOLExact 64 F _ s0.toExact (fun x => Classical.propDecidable (s0.memaddrs x)) (.const 0#64) =
      some (.val (.word 0#64)) := rfl
  rw [hev0] at hret ⊢
  dsimp only at hret ⊢
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hret ⊢
  dsimp only at hret ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s0
  have hs1_rel : MemCopyRel s0 s1 dst src n.toNat 0 := memCopyRel_locals_clock (memCopyRel_refl s0 dst src n.toNat) _ s0.clock
  have hs1_d : s1.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd_loc, show ofString "i" ≠ ofString "dst" by decide]
  have hs1_s : s1.locals.lookup (ofString "src") = some (.val (.word src)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_loc, show ofString "i" ≠ ofString "src" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_loc, show ofString "i" ≠ ofString "n" by decide]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Step 1: aligned fast-path `ite`
  rcases seq_ret_or_none s1 _ _ _ hret with h_ite_ret | ⟨s2, hs2, hret2⟩
  · exact False.elim (evaluate_noReturn _ rfl s1 v h_ite_ret)
  have hs2_inv : ∃ wi2 : BitVec 64,
      MemCopyRel s0 s2 dst src n.toNat wi2.toNat ∧
      wi2.toNat ≤ n.toNat ∧
      s2.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      s2.locals.lookup (ofString "src") = some (.val (.word src)) ∧
      s2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      s2.locals.lookup (ofString "i") = some (.val (.word wi2)) := by
    rw [evaluateHOLFiniteState_ite] at hs2
    split at hs2
    · rename_i cw halign_ev
      split at hs2
      · rw [evaluateHOLFiniteState_skip] at hs2; injection hs2 with _ e; rw [← e]
        exact ⟨0#64, hs1_rel, Nat.zero_le _, hs1_d, hs1_s, hs1_n, hs1_i⟩
      · rename_i hcw_nz
        -- Extract `dst.toNat % 8 = 0 ∧ src.toNat % 8 = 0` from `((dst ||| src) &&& 7) == 0`!
        have hd8_hs8 : dst.toNat % 8 = 0 ∧ src.toNat % 8 = 0 := by
          obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s1 .equal _ _ cw halign_ev
          simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
            hs1_d, hs1_s, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
            valueIsWord, valueWord, wordOpHOL, wordOp, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hva hvb
          subst hva hvb
          have hsimp : ((dst ||| (src ||| (0 : BitVec 64))) &&& (7#64 &&& ~~~(0 : BitVec 64))) = (dst ||| src) &&& 7#64 := by
            have h1 : src ||| (0 : BitVec 64) = src := by simp
            have h2 : (7#64 : BitVec 64) &&& ~~~(0 : BitVec 64) = 7#64 := by decide
            change (dst ||| (src ||| (0 : BitVec 64))) &&& (7#64 &&& ~~~(0 : BitVec 64)) = _
            rw [h1, h2]
          change cw = if Compiler.Encoders.Asm.wordCmpHOL Cmp.equal ((dst ||| (src ||| (0 : BitVec 64))) &&& (7#64 &&& ~~~(0 : BitVec 64))) 0#64 = true then 1 else 0 at hcw
          rw [hsimp] at hcw
          have heq0 : ((dst ||| src) &&& 7#64) = 0#64 := by
            by_contra hne
            simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne] at hcw
            exact hcw_nz hcw
          have hnat := congrArg BitVec.toNat heq0
          have h7 : ∀ x : BitVec 64, (x &&& 7#64).toNat = x.toNat % 8 := by
            intro x
            rw [BitVec.toNat_and, show (7#64 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl,
              Nat.and_two_pow_sub_one_eq_mod]
          rw [h7, BitVec.toNat_or] at hnat
          change ((dst.toNat ||| src.toNat) % 8) = 0 at hnat
          have hor8 : ((dst.toNat % 8) ||| (src.toNat % 8)) = 0 := by
            have h : (dst.toNat ||| src.toNat) % 2 ^ 3 = (dst.toNat % 2 ^ 3) ||| (src.toNat % 2 ^ 3) :=
              Nat.or_mod_two_pow
            change (dst.toNat ||| src.toNat) % 8 = (dst.toNat % 8) ||| (src.toNat % 8) at h
            omega
          have hor0 := Nat.or_eq_zero_iff.mp hor8
          exact hor0
        obtain ⟨hd8, hs8⟩ := hd8_hs8
        obtain ⟨m32, hm32, hs2_8⟩ := seq_eq_none_inv hs2
        have hl32 := memcpy_while_loop s0 dst src n hn_small 32#64 _ _ rfl rfl (fun w => w.toNat % 8 = 0) (Or.inl ⟨rfl, Or.inl rfl⟩)
          (fun st wi hrel hstep hw8 hd hs hn hi hnone => by
            have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
            rw [h32] at hstep ⊢
            obtain ⟨m1, hm1, eq1⟩ := seq_none_inv hnone; rw [eq1] at hnone ⊢
            have r1 := memcpy_store_word_step hd8 hs8 hw8 (by omega) hd_nw hs_nw hdisj hrel _ _ (ed_i st wi hd hi) (es_i st wi hs hi) (congrArg Prod.fst hm1)
            rw [hm1] at r1; have hl1 := store_keep_locals ⟨_, _, Or.inl rfl⟩ hm1
            obtain ⟨m2, hm2, eq2⟩ := seq_none_inv hnone; rw [eq2] at hnone ⊢
            have r2 := memcpy_store_word_step hd8 hs8 (by omega) (by omega) hd_nw hs_nw hdisj r1 _ _
              (ed_ik m1 wi 8 (by omega) (hl1 ▸ hd) (hl1 ▸ hi)) (es_ik m1 wi 8 (by omega) (hl1 ▸ hs) (hl1 ▸ hi)) (congrArg Prod.fst hm2)
            rw [hm2] at r2; have hl2 := (store_keep_locals ⟨_, _, Or.inl rfl⟩ hm2).trans hl1
            obtain ⟨m3, hm3, eq3⟩ := seq_none_inv hnone; rw [eq3] at hnone ⊢
            have r3 := memcpy_store_word_step hd8 hs8 (by omega) (by omega) hd_nw hs_nw hdisj r2 _ _
              (ed_ik m2 wi 16 (by omega) (hl2 ▸ hd) (hl2 ▸ hi)) (es_ik m2 wi 16 (by omega) (hl2 ▸ hs) (hl2 ▸ hi)) (congrArg Prod.fst hm3)
            rw [hm3] at r3; have hl3 := (store_keep_locals ⟨_, _, Or.inl rfl⟩ hm3).trans hl2
            obtain ⟨m4, hm4, eq4⟩ := seq_none_inv hnone; rw [eq4] at hnone ⊢
            have r4 := memcpy_store_word_step hd8 hs8 (by omega) (by omega) hd_nw hs_nw hdisj r3 _ _
              (ed_ik m3 wi 24 (by omega) (hl3 ▸ hd) (hl3 ▸ hi)) (es_ik m3 wi 24 (by omega) (hl3 ▸ hs) (hl3 ▸ hi)) (congrArg Prod.fst hm4)
            rw [hm4] at r4; have hl4 := (store_keep_locals ⟨_, _, Or.inl rfl⟩ hm4).trans hl3
            exact assign_inc_ok m4 wi 32#64 (wi.toNat + 32) r4 (hl4 ▸ hd) (hl4 ▸ hs) (hl4 ▸ hn) (hl4 ▸ hi))
          (fun wi hmod hstep => by
            have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
            rw [h32] at hstep
            have h263 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
            have hadd : (wi + 32#64).toNat = wi.toNat + 32 := by
              rw [BitVec.toNat_add, h32, Nat.mod_eq_of_lt (by omega)]
            rw [hadd]; omega)
          s1.clock s1 m32 0#64 le_rfl hs1_rel (Nat.zero_le _) rfl hs1_d hs1_s hs1_n hs1_i hm32
        obtain ⟨wi1, hrel1, hle1, hmod1, _, hd1, hs1', hn1, hi1⟩ := hl32
        have hl8w := memcpy_while_loop s0 dst src n hn_small 8#64 _ _ rfl rfl (fun w => w.toNat % 8 = 0) (Or.inl ⟨rfl, Or.inr rfl⟩)
          (fun st wi hrel hstep hw8 hd hs hn hi hnone => by
            have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
            rw [h8] at hstep ⊢
            obtain ⟨m1, hm1, eq1⟩ := seq_none_inv hnone; rw [eq1] at hnone ⊢
            have r1 := memcpy_store_word_step hd8 hs8 hw8 (by omega) hd_nw hs_nw hdisj hrel _ _ (ed_i st wi hd hi) (es_i st wi hs hi) (congrArg Prod.fst hm1)
            rw [hm1] at r1; have hl1 := store_keep_locals ⟨_, _, Or.inl rfl⟩ hm1
            exact assign_inc_ok m1 wi 8#64 (wi.toNat + 8) r1 (hl1 ▸ hd) (hl1 ▸ hs) (hl1 ▸ hn) (hl1 ▸ hi))
          (fun wi hmod hstep => by
            have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
            rw [h8] at hstep
            have h263 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
            have hadd : (wi + 8#64).toNat = wi.toNat + 8 := by
              rw [BitVec.toNat_add, h8, Nat.mod_eq_of_lt (by omega)]
            rw [hadd]; omega)
          m32.clock m32 s2 wi1 le_rfl hrel1 hle1 hmod1 hd1 hs1' hn1 hi1 hs2_8
        obtain ⟨wi2, hrel2, hle2, _, _, hd2, hs2', hn2, hi2⟩ := hl8w
        exact ⟨wi2, hrel2, hle2, hd2, hs2', hn2, hi2⟩
    · simp at hs2
  obtain ⟨wi2, hrel2, hle2, hd2, hs2', hn2, hi2⟩ := hs2_inv
  -- Step 2: 8-byte byte loop
  rcases seq_ret_or_none s2 _ _ _ hret2 with h_l8b_ret | ⟨s3, hs3, hret3⟩
  · exact False.elim (evaluate_noReturn _ rfl s2 v h_l8b_ret)
  have hl8b := memcpy_while_loop s0 dst src n hn_small 8#64 _ _ rfl rfl (fun _ => True) (Or.inl ⟨rfl, Or.inr rfl⟩)
    (fun st wi hrel hstep _ hd hs hn hi hnone => by
      have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
      rw [h8] at hstep ⊢
      obtain ⟨m0, hm0, eq0⟩ := seq_none_inv hnone; rw [eq0] at hnone ⊢
      have r0 := memcpy_store_byte_step (by omega) hd_nw hs_nw hdisj hrel _ _ (ed_i st wi hd hi) (es_i st wi hs hi) (congrArg Prod.fst hm0)
      rw [hm0] at r0; have hl0 := store_keep_locals ⟨_, _, Or.inr rfl⟩ hm0
      obtain ⟨m1, hm1, eq1⟩ := seq_none_inv hnone; rw [eq1] at hnone ⊢
      have r1 := memcpy_store_byte_step (by omega) hd_nw hs_nw hdisj r0 _ _ (ed_ik m0 wi 1 (by omega) (hl0 ▸ hd) (hl0 ▸ hi)) (es_ik m0 wi 1 (by omega) (hl0 ▸ hs) (hl0 ▸ hi)) (congrArg Prod.fst hm1)
      rw [hm1] at r1; have hl1 := (store_keep_locals ⟨_, _, Or.inr rfl⟩ hm1).trans hl0
      obtain ⟨m2, hm2, eq2⟩ := seq_none_inv hnone; rw [eq2] at hnone ⊢
      have r2 := memcpy_store_byte_step (by omega) hd_nw hs_nw hdisj r1 _ _ (ed_ik m1 wi 2 (by omega) (hl1 ▸ hd) (hl1 ▸ hi)) (es_ik m1 wi 2 (by omega) (hl1 ▸ hs) (hl1 ▸ hi)) (congrArg Prod.fst hm2)
      rw [hm2] at r2; have hl2 := (store_keep_locals ⟨_, _, Or.inr rfl⟩ hm2).trans hl1
      obtain ⟨m3, hm3, eq3⟩ := seq_none_inv hnone; rw [eq3] at hnone ⊢
      have r3 := memcpy_store_byte_step (by omega) hd_nw hs_nw hdisj r2 _ _ (ed_ik m2 wi 3 (by omega) (hl2 ▸ hd) (hl2 ▸ hi)) (es_ik m2 wi 3 (by omega) (hl2 ▸ hs) (hl2 ▸ hi)) (congrArg Prod.fst hm3)
      rw [hm3] at r3; have hl3 := (store_keep_locals ⟨_, _, Or.inr rfl⟩ hm3).trans hl2
      obtain ⟨m4, hm4, eq4⟩ := seq_none_inv hnone; rw [eq4] at hnone ⊢
      have r4 := memcpy_store_byte_step (by omega) hd_nw hs_nw hdisj r3 _ _ (ed_ik m3 wi 4 (by omega) (hl3 ▸ hd) (hl3 ▸ hi)) (es_ik m3 wi 4 (by omega) (hl3 ▸ hs) (hl3 ▸ hi)) (congrArg Prod.fst hm4)
      rw [hm4] at r4; have hl4 := (store_keep_locals ⟨_, _, Or.inr rfl⟩ hm4).trans hl3
      obtain ⟨m5, hm5, eq5⟩ := seq_none_inv hnone; rw [eq5] at hnone ⊢
      have r5 := memcpy_store_byte_step (by omega) hd_nw hs_nw hdisj r4 _ _ (ed_ik m4 wi 5 (by omega) (hl4 ▸ hd) (hl4 ▸ hi)) (es_ik m4 wi 5 (by omega) (hl4 ▸ hs) (hl4 ▸ hi)) (congrArg Prod.fst hm5)
      rw [hm5] at r5; have hl5 := (store_keep_locals ⟨_, _, Or.inr rfl⟩ hm5).trans hl4
      obtain ⟨m6, hm6, eq6⟩ := seq_none_inv hnone; rw [eq6] at hnone ⊢
      have r6 := memcpy_store_byte_step (by omega) hd_nw hs_nw hdisj r5 _ _ (ed_ik m5 wi 6 (by omega) (hl5 ▸ hd) (hl5 ▸ hi)) (es_ik m5 wi 6 (by omega) (hl5 ▸ hs) (hl5 ▸ hi)) (congrArg Prod.fst hm6)
      rw [hm6] at r6; have hl6 := (store_keep_locals ⟨_, _, Or.inr rfl⟩ hm6).trans hl5
      obtain ⟨m7, hm7, eq7⟩ := seq_none_inv hnone; rw [eq7] at hnone ⊢
      have r7 := memcpy_store_byte_step (by omega) hd_nw hs_nw hdisj r6 _ _ (ed_ik m6 wi 7 (by omega) (hl6 ▸ hd) (hl6 ▸ hi)) (es_ik m6 wi 7 (by omega) (hl6 ▸ hs) (hl6 ▸ hi)) (congrArg Prod.fst hm7)
      rw [hm7] at r7; have hl7 := (store_keep_locals ⟨_, _, Or.inr rfl⟩ hm7).trans hl6
      exact assign_inc_ok m7 wi 8#64 (wi.toNat + 8) r7 (hl7 ▸ hd) (hl7 ▸ hs) (hl7 ▸ hn) (hl7 ▸ hi))
    (fun _ _ _ => trivial)
    s2.clock s2 s3 wi2 le_rfl hrel2 hle2 trivial hd2 hs2' hn2 hi2 hs3
  obtain ⟨wi3, hrel3, hle3, _, _, hd3, hs3', hn3, hi3⟩ := hl8b
  -- Step 3: 1-byte byte loop
  rcases seq_ret_or_none s3 _ _ _ hret3 with h_l1b_ret | ⟨s4, hs4, hret4⟩
  · exact False.elim (evaluate_noReturn _ rfl s3 v h_l1b_ret)
  have hl1b := memcpy_while_loop s0 dst src n hn_small 1#64 _ _ rfl rfl (fun _ => True) (Or.inr ⟨rfl, rfl⟩)
    (fun st wi hrel hstep _ hd hs hn hi hnone => by
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [h1] at hstep ⊢
      obtain ⟨m0, hm0, eq0⟩ := seq_none_inv hnone; rw [eq0] at hnone ⊢
      have r0 := memcpy_store_byte_step (by omega) hd_nw hs_nw hdisj hrel _ _ (ed_i st wi hd hi) (es_i st wi hs hi) (congrArg Prod.fst hm0)
      rw [hm0] at r0; have hl0 := store_keep_locals ⟨_, _, Or.inr rfl⟩ hm0
      exact assign_inc_ok m0 wi 1#64 (wi.toNat + 1) r0 (hl0 ▸ hd) (hl0 ▸ hs) (hl0 ▸ hn) (hl0 ▸ hi))
    (fun _ _ _ => trivial)
    s3.clock s3 s4 wi3 le_rfl hrel3 hle3 trivial hd3 hs3' hn3 hi3 hs4
  obtain ⟨wi4, hrel4, _, _, hdone4, _, _, _, _⟩ := hl1b
  have hwi4_eq := hdone4 rfl
  rw [hwi4_eq] at hrel4
  -- Step 4: `return 0`!
  have hret_eval : evaluateHOLFiniteState s4 (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s4) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [hret_eval] at hret4
  injection hret4 with hv_eq; injection hv_eq with hv_eq'
  refine ⟨hv_eq'.symm, ?_⟩
  -- Rewrite the post-state of the whole `memcpy` body!
  rw [evaluateHOLFiniteState_seq_line780, hs2]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, hs3]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, hs4]
  dsimp only
  rw [hret_eval]
  exact memCopyRel_locals_clock hrel4 _ s4.clock

end InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

/-! ### From SoloHtabSet.lean -/

/-! Callee and loop-step lemmas for `htab_set_spec` (`htab_grow`, `htab_new_node`, `htab_new_leaf`,
`htab_new_internal`, `htab_find_leaf`, and `htab_set`'s descent loop). -/


namespace InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Store, Address, and `alloc` Helpers -/

def updW (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun c => if c = a then .word w else m c

theorem stores_word {dom : BitVec 64 → Prop} (inst : DecidablePred dom)
    {m m' : BitVec 64 → HolWordLab 64}
    {a w : BitVec 64} (h : @panMemStoresHOL 64 _ a (flattenHOL (.val (.word w))) dom inst m = some m') :
    dom a ∧ m' = updW m a w := by
  unfold flattenHOL panMemStoresHOL panMemStoreHOL at h
  by_cases hd : dom a
  · simp only [hd, ↓reduceIte, panMemStoresHOL, Option.some.injEq] at h
    exact ⟨hd, h.symm⟩
  · simp [hd] at h

theorem ofNat64_eq_of_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have h' := congrArg BitVec.toNat h
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using h'

theorem ofNat64_ne_of_ne_of_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : a ≠ b) : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b :=
  fun hab => h (ofNat64_eq_of_lt ha hb hab)

theorem ofNat_add_toNat (t : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 (t.toNat + n) = t + BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem ofNat_node_addr (nd w : BitVec 64) (off : Nat) :
    BitVec.ofNat 64 (nd.toNat + 32 * w.toNat + off) = nd + w * 32 + BitVec.ofNat 64 off := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have : (32 : BitVec 64).toNat = 32 := rfl
  rw [this]
  omega

theorem memW_updW_same {F : Type} (s : PanSemStateFiniteExact 64 F) (a w : BitVec 64) :
    memW { s with memory := updW s.memory a w } a.toNat = w.toNat := by
  simp [memW, updW]

theorem memW_updW_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a w : BitVec 64) (b : Nat) (h : BitVec.ofNat 64 b ≠ a) :
    memW { s with memory := updW s.memory a w } b = memW s b := by
  simp [memW, updW, h]

theorem hdr_word {F : Type} (s : PanSemStateFiniteExact 64 F) (tw w : BitVec 64)
    (i : Nat) (h : s.memory (tw + BitVec.ofNat 64 (8 * i)) = .word w) :
    hdr s tw.toNat i = w.toNat := by
  unfold hdr memW
  rw [ofNat_add_toNat tw (8 * i), h]

theorem word_of_hdr {F : Type} (s : PanSemStateFiniteExact 64 F) (tw : BitVec 64)
    (i : Nat) (hi : i < 11) (hB : HtabBlocks s tw.toNat) :
    s.memaddrs (tw + BitVec.ofNat 64 (8 * i)) ∧
    s.memory (tw + BitVec.ofNat 64 (8 * i)) = .word (BitVec.ofNat 64 (hdr s tw.toNat i)) := by
  have hhdr := (hB.1 (tw.toNat, 88) (by simp [htabFootprint])).2
  obtain ⟨w, hdom, hm⟩ := hhdr.2.2 i (by omega)
  rw [ofNat_add_toNat] at hdom hm
  refine ⟨hdom, ?_⟩
  rw [hdr_word s tw w i hm, BitVec.ofNat_toNat, BitVec.setWidth_eq, hm]

theorem word_of_node {F : Type} (s : PanSemStateFiniteExact 64 F) (tw nd w : BitVec 64)
    (off : Nat) (h5 : hdr s tw.toNat 5 = nd.toNat)
    (hw : w.toNat < hdr s tw.toNat 10 + 1)
    (hoff : off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24)
    (hB : HtabBlocks s tw.toNat) :
    s.memaddrs (nd + w * 32 + BitVec.ofNat 64 off) ∧
    s.memory (nd + w * 32 + BitVec.ofNat 64 off) =
      .word (BitVec.ofNat 64 (nodeF s nd.toNat w.toNat off)) := by
  have hndB := (hB.1 (hdr s tw.toNat 5, (hdr s tw.toNat 10 + 1) * 32) (by simp [htabFootprint])).2
  rw [h5] at hndB
  let k := 4 * w.toNat + off / 8
  have hk : k < ((hdr s tw.toNat 10 + 1) * 32) / 8 := by rcases hoff with rfl | rfl | rfl | rfl <;> dsimp [k] <;> omega
  obtain ⟨u, hdom, hm⟩ := hndB.2.2 k hk
  have hk_eq : nd.toNat + 8 * k = nd.toNat + 32 * w.toNat + off := by
    rcases hoff with rfl | rfl | rfl | rfl <;> dsimp [k] <;> omega
  rw [hk_eq, ofNat_node_addr] at hdom hm
  refine ⟨hdom, ?_⟩
  unfold nodeF memW
  rw [ofNat_node_addr, hm, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem word_of_order {F : Type} (s : PanSemStateFiniteExact 64 F) (tw ow iw : BitVec 64)
    (h6 : hdr s tw.toNat 6 = ow.toNat)
    (hi : iw.toNat < hdr s tw.toNat 10 + 1)
    (hB : HtabBlocks s tw.toNat) :
    s.memaddrs (ow + iw * 8) ∧
    s.memory (ow + iw * 8) = .word (BitVec.ofNat 64 (memW s (ow.toNat + 8 * iw.toNat))) := by
  have hordB := (hB.1 (hdr s tw.toNat 6, (hdr s tw.toNat 10 + 1) * 8) (by simp [htabFootprint])).2
  rw [h6] at hordB
  obtain ⟨u, hdom, hm⟩ := hordB.2.2 iw.toNat (by omega)
  have haddr : BitVec.ofNat 64 (ow.toNat + 8 * iw.toNat) = ow + iw * 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    have : (8 : BitVec 64).toNat = 8 := rfl
    rw [this]; omega
  rw [haddr] at hdom hm
  refine ⟨hdom, ?_⟩
  unfold memW
  rw [haddr, hm, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem frameOutside_updW {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a w : BitVec 64) (keep : List Ivl) (fresh : Ivl)
    (ha : (∃ i ∈ keep, CellHits a.toNat i) ∨ CellHits a.toNat fresh) :
    FrameOutside s { s with memory := updW s.memory a w } keep fresh := by
  intro x hx hfresh
  by_cases hxa : x = a
  · subst x
    exfalso
    rcases ha with ⟨i, hi, hhit⟩ | hhit
    · exact hx i hi hhit
    · exact hfresh hhit
  · simp [updW, hxa]

theorem frameOutside_trans_same {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh : Ivl}
    (h1 : FrameOutside a b keep fresh) (h2 : FrameOutside b c keep fresh) :
    FrameOutside a c keep fresh :=
  fun x hx hf => (h2 x hx hf).trans (h1 x hx hf)

theorem cellHits_of_inside {a : Nat} {i j : Ivl}
    (hhit : CellHits a i) (hin : Inside i j.1 (j.1 + j.2)) : CellHits a j := by
  have h1 : i.1 < a + 8 := hhit.1
  have h2 : a < i.1 + i.2 := hhit.2
  have h3 : j.1 ≤ i.1 := hin.1
  have h4 : i.1 + i.2 ≤ j.1 + j.2 := hin.2
  exact ⟨by omega, by omega⟩

theorem frameOutside_mono {F : Type} {a b : PanSemStateFiniteExact 64 F}
    {keep1 keep2 : List Ivl} {fresh1 fresh2 : Ivl}
    (h : FrameOutside a b keep1 fresh1)
    (hk : ∀ i ∈ keep1, (∃ j ∈ keep2, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh2.1 (fresh2.1 + fresh2.2))
    (hf : Inside fresh1 fresh2.1 (fresh2.1 + fresh2.2)) :
    FrameOutside a b keep2 fresh2 := by
  intro x hx hxf
  apply h x
  · intro i hi hhit
    rcases hk i hi with ⟨j, hj, hij⟩ | hif'
    · exact hx j hj (cellHits_of_inside hhit hij)
    · exact hxf (cellHits_of_inside hhit hif')
  · intro hhit
    exact hxf (cellHits_of_inside hhit hf)

/-! ### `alloc` body semantics -/

theorem alloc_body_run {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_le : p.toNat ≤ cMax.toNat)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word p) ∧
      p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ cMax.toNat ∧ q.toNat % 8 = 0 ∧
      out.2 = { state with
        globals := (state.globals.update (ofString "heap_ptr", .val (.word q)))
        locals := out.2.locals } := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only
  rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only
  rw [if_pos hsh_p]
  dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (cMax - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 1 w hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some r1' => intro retVal hret; exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]
    dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only
    rw [hq_eval]
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only
    rw [if_pos hsh_q]
    dsimp only
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
        some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : cMax.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 1 w hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some r2' => intro retVal hret; exact False.elim (hno_ret retVal hret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLFinite, isValidValueHOLExact,
          lookupKvarHOLFinite, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      have hcMax : cMax.toNat = 2952790016 := rfl
      have hq_eq : q.toNat = (p + (n + 7)).toNat / 8 * 8 := and_neg8_toNat (p + (n + 7))
      have hq_le : q.toNat ≤ cMax.toNat := Nat.le_of_not_lt hcmp2
      have hsub : (cMax - p).toNat = cMax.toNat - p.toNat := by rw [BitVec.toNat_sub]; omega
      have h7 : (7 : BitVec 64).toNat = 7 := rfl
      have hn7 : (n + 7).toNat = n.toNat + 7 := by rw [BitVec.toNat_add, h7]; omega
      have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by rw [BitVec.toNat_add, hn7]; omega
      intro retVal hret
      injection hret with hr; injection hr with hr'
      change retVal = .val (.word p) ∧ p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ cMax.toNat ∧ q.toNat % 8 = 0 ∧ _
      exact ⟨hr'.symm, by omega, hq_le, by omega, rfl⟩

/-! ## 2. Call-Level Combinators (`Ret`) -/

def Ret {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) → Φ v (evaluateHOLFiniteState s p).2

theorem Ret.seq {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (ha : Ret s a Φ) (hb : ∀ t, evaluateHOLFiniteState s a = (none, t) → Ret t b Φ) :
    Ret s (.seq a b) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780] at hv ⊢
  rcases h : evaluateHOLFiniteState s a with ⟨r, t⟩
  simp only [h] at hv
  try simp only [h]
  cases r with
  | none => exact hb t h v hv
  | some _ =>
    have := ha v (by rw [h]; exact hv)
    rw [h] at this
    exact this

theorem Ret.skip_noret {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} : Ret s .skip Φ := by
  intro v hv; rw [evaluateHOLFiniteState_skip] at hv; cases hv

theorem Ret.seq_skip {F : Type} {s : PanSemStateFiniteExact 64 F} {b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hb : Ret s b Φ) :
    Ret s (.seq .skip b) Φ :=
  Ret.seq Ret.skip_noret fun t ht => by rw [evaluateHOLFiniteState_skip] at ht; injection ht with _ e; rw [← e]; exact hb

theorem Ret.dec {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, evalAt s init = some val →
      Ret (setVarHOLFinite x val s) body
        (fun v t => Φ v { t with
          locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.dec x sh init body) Φ := by
  intro v
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  cases hval : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) init with
  | none => intro hv; simp at hv
  | some val =>
    dsimp only
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact val) = true
    · rw [if_pos hsh]; exact h val hval v
    · rw [if_neg hsh]; intro hv; simp at hv

theorem Ret.ret {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, evalAt s e = some val → Φ val (emptyLocalsHOLFinite s)) :
    Ret s (.return e) Φ := by
  intro v
  rw [evaluateHOLFiniteState_return]
  cases hval : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) e with
  | none => intro hv; simp at hv
  | some val =>
    dsimp only
    by_cases hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact val) ≤ 32
    · rw [if_pos hsz]
      intro hv
      injection hv with hv1; injection hv1 with hv2
      subst hv2
      exact h _ hval
    · rw [if_neg hsz]; intro hv; simp at hv

theorem Ret.seq_storeW {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a w : BitVec 64) (hd : evalAt s d = some (.val (.word a))) (he : evalAt s e = some (.val (.word w)))
    (hb : s.memaddrs a → Ret { s with memory := updW s.memory a w } b Φ) :
    Ret s (.seq (.store d e) b) Φ := by
  refine Ret.seq ?_ ?_
  · intro v hv
    have := (evaluate_store_control_frame s d e).1
    rcases this with h | h <;> rw [h] at hv <;> simp at hv
  · intro t ht
    rw [evaluateHOLFiniteState_store] at ht
    unfold evalAt at hd he
    rw [hd] at ht; dsimp only at ht
    rw [he] at ht; dsimp only at ht
    rcases hm : @panMemStoresHOL 64 _ a (flattenHOL (.val (.word w))) s.memaddrs (fun addr => Classical.propDecidable (s.memaddrs addr)) s.memory with _ | m
    · rw [hm] at ht; simp at ht
    · rw [hm] at ht; injection ht with _ hteq; rw [← hteq]
      obtain ⟨hdom, rfl⟩ := stores_word _ hm
      exact hb hdom

theorem Ret.seq_assign {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (w : BitVec 64) (he : evalAt s e = some (.val (.word w)))
    (hb : Ret (setVarHOLFinite x (.val (.word w)) s) b Φ) :
    Ret s (.seq (.assign .local x e) b) Φ := by
  refine Ret.seq ?_ ?_
  · intro v hv
    rw [evaluateHOLFiniteState_assign] at hv
    unfold evalAt at he
    rw [he] at hv; dsimp only at hv
    by_cases hvld : s.isValidValueHOLFinite .local x (.val (.word w)) = true
    · rw [if_pos hvld] at hv; simp at hv
    · rw [if_neg hvld] at hv; simp at hv
  · intro t ht
    rw [evaluateHOLFiniteState_assign] at ht
    unfold evalAt at he
    rw [he] at ht; dsimp only at ht
    by_cases hvld : s.isValidValueHOLFinite .local x (.val (.word w)) = true
    · rw [if_pos hvld] at ht; injection ht with _ hteq; rw [← hteq]; exact hb
    · rw [if_neg hvld] at ht; simp at ht

theorem Ret.ite {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {y n : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ cw : BitVec 64, evalAt s c = some (.val (.word cw)) →
      (cw ≠ 0 → Ret s y Φ) ∧ (cw = 0 → Ret s n Φ)) :
    Ret s (.ite c y n) Φ := by
  intro v
  rw [evaluateHOLFiniteState_ite]
  cases hcw : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) c with
  | none => intro hv; cases hv
  | some vc =>
    cases vc with
    | val wl =>
      cases wl with
      | word cw =>
        dsimp only
        by_cases hz : cw = 0
        · rw [if_pos hz]; exact (h cw hcw).2 hz v
        · rw [if_neg hz]; exact (h cw hcw).1 hz v
    | rStruct _ => intro hv; cases hv
    | nStruct _ _ => intro hv; cases hv

theorem Ret.seq_ite {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {y n b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ cw : BitVec 64, evalAt s c = some (.val (.word cw)) →
      (cw ≠ 0 → Ret s (.seq y b) Φ) ∧ (cw = 0 → Ret s (.seq n b) Φ)) :
    Ret s (.seq (.ite c y n) b) Φ := by
  intro v
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  cases hcw : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) c with
  | none => intro hv; cases hv
  | some vc =>
    cases vc with
    | val wl =>
      cases wl with
      | word cw =>
        dsimp only
        by_cases hz : cw = 0
        · rw [if_pos hz]
          have := (h cw hcw).2 hz v
          rw [evaluateHOLFiniteState_seq_line780] at this
          exact this
        · rw [if_neg hz]
          have := (h cw hcw).1 hz v
          rw [evaluateHOLFiniteState_seq_line780] at this
          exact this
    | rStruct _ => intro hv; cases hv
    | nStruct _ _ => intro hv; cases hv

theorem Ret.decCall1 {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 : MlS}
    {e1 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], fbody, .one))
    (w1 : BitVec 64) (he1 : evalAt s e1 = some (.val (.word w1)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (p1, .val (.word w1)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one fname [e1] cont) Φ := by
  intro v
  rw [evaluateHOLFiniteState_decCall_total]
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1] =
      some [.val (.word w1)] := by
    unfold evalAt at he1
    simp [evalListHOLFinite, evalListHOLExact, he1]
  have hl := pan_one_word_lookup s.code.lookup fname p1 fbody w1 (by rw [hcode]; exact hlook)
  rw [hargs]; dsimp only
  rw [hl]; dsimp only
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz]; intro hv; cases hv
  · rw [if_neg hcz]
    rw [fixClockHOLFinite_evaluateState]
    cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (p1, .val (.word w1)))) fbody with
    | mk r post =>
      dsimp only
      cases r with
      | none => intro hv; cases hv
      | some r =>
        cases r with
        | returned rv =>
          dsimp only
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) .one && shapeEqHOL (shapeOfHOLExact rv) .one) = true
          · rw [if_pos hsh]
            rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
            · exact hk w post hrun v
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · rw [if_neg hsh]; intro hv; cases hv
        | _ => intro hv; cases hv

theorem Ret.decCall2 {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 p2 : MlS}
    {e1 e2 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], fbody, .one))
    (w1 w2 : BitVec 64)
    (he1 : evalAt s e1 = some (.val (.word w1)))
    (he2 : evalAt s e2 = some (.val (.word w2)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one fname [e1, e2] cont) Φ := by
  intro v
  rw [evaluateHOLFiniteState_decCall_total]
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2] =
      some [.val (.word w1), .val (.word w2)] := by
    unfold evalAt at he1 he2
    simp [evalListHOLFinite, evalListHOLExact, he1, he2]
  have hl := pan_two_word_lookup s.code.lookup fname p1 p2 fbody w1 w2 hne (by rw [hcode]; exact hlook)
  rw [hargs]; dsimp only
  rw [hl]; dsimp only
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz]; intro hv; cases hv
  · rw [if_neg hcz]
    rw [fixClockHOLFinite_evaluateState]
    cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2)))) fbody with
    | mk r post =>
      dsimp only
      cases r with
      | none => intro hv; cases hv
      | some r =>
        cases r with
        | returned rv =>
          dsimp only
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) .one && shapeEqHOL (shapeOfHOLExact rv) .one) = true
          · rw [if_pos hsh]
            rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
            · exact hk w post hrun v
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · rw [if_neg hsh]; intro hv; cases hv
        | _ => intro hv; cases hv

theorem Ret.decCall3 {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 p2 p3 : MlS}
    {e1 e2 e3 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], fbody, .one))
    (w1 w2 w3 : BitVec 64)
    (he1 : evalAt s e1 = some (.val (.word w1)))
    (he2 : evalAt s e2 = some (.val (.word w2)))
    (he3 : evalAt s e3 = some (.val (.word w3)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update (p3, .val (.word w3)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one fname [e1, e2, e3] cont) Φ := by
  intro v
  rw [evaluateHOLFiniteState_decCall_total]
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] =
      some [.val (.word w1), .val (.word w2), .val (.word w3)] := by
    unfold evalAt at he1 he2 he3
    simp [evalListHOLFinite, evalListHOLExact, he1, he2, he3]
  have hl := pan_three_word_lookup s.code.lookup fname p1 p2 p3 fbody w1 w2 w3 hne12 hne13 hne23 (by rw [hcode]; exact hlook)
  rw [hargs]; dsimp only
  rw [hl]; dsimp only
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz]; intro hv; cases hv
  · rw [if_neg hcz]
    rw [fixClockHOLFinite_evaluateState]
    cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update (p3, .val (.word w3)))) fbody with
    | mk r post =>
      dsimp only
      cases r with
      | none => intro hv; cases hv
      | some r =>
        cases r with
        | returned rv =>
          dsimp only
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) .one && shapeEqHOL (shapeOfHOLExact rv) .one) = true
          · rw [if_pos hsh]
            rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
            · exact hk w post hrun v
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · rw [if_neg hsh]; intro hv; cases hv
        | _ => intro hv; cases hv

theorem call_none_noRet {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨fb, cl, rs⟩
    · simp
    · dsimp only
      by_cases hcz : s.clock = 0
      · rw [if_pos hcz]; simp
      · rw [if_neg hcz]
        rcases evaluateHOLFiniteState _ _ with ⟨r, _⟩
        cases r with
        | none => simp
        | some r =>
          cases r with
          | returned rv =>
            try dsimp only
            by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) rs = true
            · rw [if_pos hsh]; simp
            · rw [if_neg hsh]; simp
          | _ => simp

theorem Ret.seq_call1 {F : Type} {s : PanSemStateFiniteExact 64 F} {fname p1 : MlS}
    {e1 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], fbody, .one))
    (w1 : BitVec 64) (he1 : evalAt s e1 = some (.val (.word w1)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (p1, .val (.word w1)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret { post with locals := s.locals } cont Φ) :
    Ret s (.seq (.call (some (none, none)) fname [e1]) cont) Φ := by
  refine Ret.seq (fun v hv => False.elim (call_none_noRet s fname [e1] v hv)) ?_
  intro t ht
  rw [evaluateHOLFiniteState_call] at ht
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1] =
      some [.val (.word w1)] := by
    unfold evalAt at he1
    simp [evalListHOLFinite, evalListHOLExact, he1]
  have hl := pan_one_word_lookup s.code.lookup fname p1 fbody w1 (by rw [hcode]; exact hlook)
  rw [hargs] at ht; dsimp only at ht
  rw [hl] at ht; dsimp only at ht
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at ht; simp at ht
  · rw [if_neg hcz] at ht
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (p1, .val (.word w1)))) fbody with ⟨r, post⟩
    rw [hrun] at ht
    rcases r with _ | r
    · simp at ht
    · cases r with
      | returned rv =>
        try dsimp only at ht
        by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) .one = true
        · rw [if_pos hsh] at ht
          rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
          · injection ht with _ hteq; rw [← hteq]; exact hk w post hrun
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · rw [if_neg hsh] at ht; simp at ht
      | _ => simp at ht

theorem Ret.seq_call3 {F : Type} {s : PanSemStateFiniteExact 64 F} {fname p1 p2 p3 : MlS}
    {e1 e2 e3 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], fbody, .one))
    (w1 w2 w3 : BitVec 64)
    (he1 : evalAt s e1 = some (.val (.word w1)))
    (he2 : evalAt s e2 = some (.val (.word w2)))
    (he3 : evalAt s e3 = some (.val (.word w3)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update (p3, .val (.word w3)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret { post with locals := s.locals } cont Φ) :
    Ret s (.seq (.call (some (none, none)) fname [e1, e2, e3]) cont) Φ := by
  refine Ret.seq (fun v hv => False.elim (call_none_noRet s fname [e1, e2, e3] v hv)) ?_
  intro t ht
  rw [evaluateHOLFiniteState_call] at ht
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] =
      some [.val (.word w1), .val (.word w2), .val (.word w3)] := by
    unfold evalAt at he1 he2 he3
    simp [evalListHOLFinite, evalListHOLExact, he1, he2, he3]
  have hl := pan_three_word_lookup s.code.lookup fname p1 p2 p3 fbody w1 w2 w3 hne12 hne13 hne23 (by rw [hcode]; exact hlook)
  rw [hargs] at ht; dsimp only at ht
  rw [hl] at ht; dsimp only at ht
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at ht; simp at ht
  · rw [if_neg hcz] at ht
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update (p3, .val (.word w3)))) fbody with ⟨r, post⟩
    rw [hrun] at ht
    rcases r with _ | r
    · simp at ht
    · cases r with
      | returned rv =>
        try dsimp only at ht
        by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) .one = true
        · rw [if_pos hsh] at ht
          rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
          · injection ht with _ hteq; rw [← hteq]; exact hk w post hrun
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · rw [if_neg hsh] at ht; simp at ht
      | _ => simp at ht

end InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

/-! ### From SoloHtabSetLoops.lean -/

/-! Flow/while-invariant rules (`Flw`, `while_inv2`, `while_noRet`), frame-only `memcpy`
(`memcpy_body_frame`, no `Disj` required), `htab_find_leaf` postcondition, and the `htab_set`
descent loop invariant. -/


namespace InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. `htab_unfold` macro and `FlowR` / `Flw` / `while_inv2` / `while_noRet` -/

macro "htab_unfold" d:ident : tactic => `(tactic| dsimp only [sourceFnBody, sourceFunctionEntry, extractFn, $d:ident,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map])

def FlowR (r : Option (PanSemResultExact 64)) : Prop :=
  r = none ∨ r = some .continue ∨ r = some .break

theorem flowing_of_flowR {r : Option (PanSemResultExact 64)} (h : FlowR r) : Flowing r := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

def Flw {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  FlowR (evaluateHOLFiniteState s p).1 → Ψ (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2

section FlwRules
variable {F : Type} {s : PanSemStateFiniteExact 64 F}
  {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}

theorem Flw.dec {x : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (h : ∀ v, evalAt s init = some v →
      Flw (setVarHOLFinite x v s) body
        (fun r t => Ψ r { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Flw s (.dec x sh init body) Ψ := by
  rw [Flw, evaluateHOLFiniteState_dec_total]
  dsimp only
  cases hv : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) init with
  | none => intro hf; rcases hf with h' | h' | h' <;> cases h'
  | some v =>
    dsimp only
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · rw [if_pos hsh]; exact h v hv
    · rw [if_neg hsh]; intro hf; rcases hf with h' | h' | h' <;> cases h'

theorem Flw.seq {a b : ProgHOL 64}
    (h : Flw s a (fun r t => (r = none → Flw t b Ψ) ∧ (r ≠ none → Ψ r t))) :
    Flw s (.seq a b) Ψ := by
  rw [Flw, evaluateHOLFiniteState_seq_line780]
  cases hr : evaluateHOLFiniteState s a with
  | mk r t =>
    have h' := h
    unfold Flw at h'
    rw [hr] at h'
    dsimp only at h' ⊢
    cases r with
    | none => exact (h' (Or.inl rfl)).1 rfl
    | some _ => intro hf; exact (h' hf).2 (by simp)

theorem Flw.ite {c : ExpHOL 64} {y n : ProgHOL 64}
    (h : ∀ w, evalAt s c = some (.val (.word w)) → (w ≠ 0 → Flw s y Ψ) ∧ (w = 0 → Flw s n Ψ)) :
    Flw s (.ite c y n) Ψ := by
  rw [Flw, evaluateHOLFiniteState_ite]
  cases hcw : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) c with
  | none => intro hf; rcases hf with h' | h' | h' <;> cases h'
  | some vc =>
    cases vc with
    | val wl =>
      cases wl with
      | word w =>
        dsimp only
        by_cases hz : w = 0
        · rw [if_pos hz]; exact (h w hcw).2 hz
        · rw [if_neg hz]; exact (h w hcw).1 hz
    | rStruct _ => intro hf; rcases hf with h' | h' | h' <;> cases h'
    | nStruct _ _ => intro hf; rcases hf with h' | h' | h' <;> cases h'

theorem Flw.brk (h : Ψ (some .break) s) : Flw s .break Ψ := by
  intro _; rw [evaluateHOLFiniteState_break]; exact h

theorem Flw.skip (h : Ψ none s) : Flw s .skip Ψ := by
  intro _; rw [evaluateHOLFiniteState_skip]; exact h

theorem Flw.assign {x : MlS} {e : ExpHOL 64}
    (h : ∀ v, evalAt s e = some v → Ψ none (setVarHOLFinite x v s)) :
    Flw s (.assign .local x e) Ψ := by
  rw [Flw, evaluateHOLFiniteState_assign]
  cases hv : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) e with
  | none => intro hf; rcases hf with h' | h' | h' <;> cases h'
  | some v =>
    dsimp only
    by_cases hvld : s.isValidValueHOLFinite .local x v = true
    · rw [if_pos hvld]; intro _; exact h v hv
    · rw [if_neg hvld]; intro hf; rcases hf with h' | h' | h' <;> cases h'

end FlwRules

def NoRet (p : ProgHOL 64) : Prop :=
  ∀ {F : Type} (st : PanSemStateFiniteExact 64 F) v,
    (evaluateHOLFiniteState st p).1 ≠ some (.returned v)

theorem NoRet.seq {a b : ProgHOL 64} (ha : NoRet a) (hb : NoRet b) : NoRet (.seq a b) := by
  intro F st v
  rw [evaluateHOLFiniteState_seq_line780]
  cases h : evaluateHOLFiniteState st a with
  | mk r t =>
    have := ha st v
    rw [h] at this
    cases r with
    | none => exact hb t v
    | some _ => exact this

theorem NoRet.ite {c : ExpHOL 64} {y n : ProgHOL 64} (hy : NoRet y) (hn : NoRet n) :
    NoRet (.ite c y n) := by
  intro F st v
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn st v
    · exact hy st v
  · simp

theorem NoRet.skip : NoRet .skip := by
  intro F st v; rw [evaluateHOLFiniteState_skip]; simp

theorem NoRet.brk : NoRet .break := by
  intro F st v; rw [evaluateHOLFiniteState_break]; simp

theorem NoRet.assign {x : MlS} {e : ExpHOL 64} : NoRet (.assign .local x e) := by
  intro F st v
  rw [evaluateHOLFiniteState_assign]
  split
  · simp
  · split <;> simp

theorem NoRet.dec' {x : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {p : ProgHOL 64} (hp : NoRet p) :
    NoRet (.dec x sh e p) := by
  intro F st v
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · split
    · exact hp _ v
    · simp

theorem while_noRet {F : Type} (cond : ExpHOL 64) (body : ProgHOL 64)
    (hb : ∀ s : PanSemStateFiniteExact 64 F, ∀ v,
      (evaluateHOLFiniteState s body).1 ≠ some (.returned v)) :
    ∀ (n : Nat) (s : PanSemStateFiniteExact 64 F), s.clock ≤ n → ∀ v,
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some (.returned v) := by
  intro n
  induction n with
  | zero =>
    intro s hcl v
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    split
    · rename_i w hw
      by_cases hz : w = 0
      · simp [hz]
      · rw [if_pos hz, if_pos (by omega)]; simp
    · simp
  | succ n ih =>
    intro s hcl v
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    split
    · rename_i w hw
      by_cases hz : w = 0
      · simp [hz]
      · rw [if_pos hz]
        by_cases hc : s.clock = 0
        · rw [if_pos hc]; simp
        · rw [if_neg hc]
          have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hbv := hb (decClockHOLFinite s) v
          cases hbd : evaluateHOLFiniteState (decClockHOLFinite s) body with
          | mk r t =>
            rw [hbd] at hle hbv
            change t.clock ≤ s.clock - 1 at hle
            dsimp only at hbv ⊢
            cases r with
            | none => exact ih t (by omega) v
            | some r =>
              cases r with
              | «continue» => exact ih t (by omega) v
              | «break» => simp
              | returned v' => exact hbv
              | _ => simp
    · simp

theorem while_inv2 {F : Type} (I Bk : PanSemStateFiniteExact 64 F → Prop) (cond : ExpHOL 64)
    (body : ProgHOL 64)
    (hstep : ∀ s : PanSemStateFiniteExact 64 F, I s → LoopActive cond s → s.clock ≠ 0 →
      (((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
        I (evaluateHOLFiniteState (decClockHOLFinite s) body).2) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break →
        Bk (evaluateHOLFiniteState (decClockHOLFinite s) body).2)) :
    ∀ (n : Nat) (s : PanSemStateFiniteExact 64 F), s.clock ≤ n → I s →
      (evaluateHOLFiniteState s (.while cond body)).1 = none →
      (I (evaluateHOLFiniteState s (.while cond body)).2 ∧
        CondFalse cond (evaluateHOLFiniteState s (.while cond body)).2) ∨
      Bk (evaluateHOLFiniteState s (.while cond body)).2 := by
  intro n
  induction n with
  | zero =>
    intro s hcl hs hnone
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    revert hnone
    split
    · rename_i w hw
      by_cases hz : w = 0
      · subst hz; simp; exact Or.inl ⟨hs, hw⟩
      · rw [if_pos hz, if_pos (by omega)]; simp
    · simp
  | succ n ih =>
    intro s hcl hs hnone
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    revert hnone
    split
    · rename_i w hw
      by_cases hz : w = 0
      · subst hz; simp; exact Or.inl ⟨hs, hw⟩
      · rw [if_pos hz]
        by_cases hc : s.clock = 0
        · rw [if_pos hc]; simp
        · rw [if_neg hc]
          have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hst := hstep s hs ⟨w, hw, hz⟩ hc
          cases hb : evaluateHOLFiniteState (decClockHOLFinite s) body with
          | mk r t =>
            rw [hb] at hle hst
            change t.clock ≤ s.clock - 1 at hle
            dsimp only at hst ⊢
            cases r with
            | none =>
              intro hn
              exact ih t (by omega) (hst.1 (Or.inl rfl)) hn
            | some r =>
              cases r with
              | «continue» =>
                intro hn
                exact ih t (by omega) (hst.1 (Or.inr rfl)) hn
              | «break» =>
                intro _
                exact Or.inr (hst.2 rfl)
              | _ => simp
    · simp

/-! ## 2. Frame-only `memcpy` postcondition (no `Disj` required) -/

def MemCopyFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (len : Nat) : Prop :=
  s.code = s0.code ∧ s.memaddrs = s0.memaddrs ∧ s.shMemaddrs = s0.shMemaddrs ∧
  s.baseAddr = s0.baseAddr ∧ s.be = s0.be ∧ s.globals = s0.globals ∧
  FrameOutside s0 s [(dst.toNat, len)] (0, 0)

theorem memCopyFrame_refl {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (len : Nat) :
    MemCopyFrame s0 s0 dst len :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem memCopyFrame_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst : BitVec 64} {len : Nat}
    (h : MemCopyFrame s0 s dst len) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    MemCopyFrame s0 { s with locals := L, clock := k } dst len :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem mcf_seq_none {F : Type} {s : PanSemStateFiniteExact 64 F}
    {p1 p2 : ProgHOL 64} (h : (evaluateHOLFiniteState s (.seq p1 p2)).1 = none) :
    ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
      evaluateHOLFiniteState s (.seq p1 p2) = evaluateHOLFiniteState m p2 := by
  rw [evaluateHOLFiniteState_seq_line780] at h ⊢
  cases hr : evaluateHOLFiniteState s p1 with
  | mk r1 m =>
    rw [hr] at h
    cases r1 with
    | none => exact ⟨m, rfl, rfl⟩
    | some _ => simp at h

private theorem mcf_store_word {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 : BitVec 64} {len off : Nat}
    (hoff_le : off + 8 ≤ len) (hd_nw : dst0.toNat + len < 2 ^ 64)
    (hrel : MemCopyFrame s0 s dst0 len)
    (ed es : ExpHOL 64)
    (hed : evalAt s ed = some (.val (.word (dst0 + BitVec.ofNat 64 off))))
    (hnone : (evaluateHOLFiniteState s (.store ed (.load .one es))).1 = none) :
    MemCopyFrame s0 (evaluateHOLFiniteState s (.store ed (.load .one es))).2 dst0 len ∧
    (evaluateHOLFiniteState s (.store ed (.load .one es))).2.locals = s.locals := by
  obtain ⟨hc, hm, hsh, hba, hbe, hg, hfr⟩ := hrel
  have hl := (evaluate_store_control_frame s ed (.load .one es)).2.1
  refine ⟨?_, hl⟩
  rw [evaluateHOLFiniteState_store] at hnone ⊢
  unfold evalAt at hed
  rw [hed] at hnone ⊢
  dsimp only at hnone ⊢
  revert hnone
  split
  · rename_i v hld
    have hv_word : ∃ w, v = .val (.word w) := by
      simp only [evalHOLExact, isWfShapeExactHOL, ↓reduceIte, memLoadHOLExact] at hld
      split at hld
      · rename_i va hva
        split at hld
        · rcases hm_va : s.memory va with ⟨w⟩
          rw [hm_va] at hld
          injection hld with heq
          exact ⟨w, heq.symm⟩
        · cases hld
      · cases hld
    obtain ⟨w, rfl⟩ := hv_word
    cases hst : @panMemStoresHOL 64 _ (dst0 + BitVec.ofNat 64 off) (flattenHOL (.val (.word w)))
        s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.memory with
    | none => intro hn; cases hn
    | some mem' =>
      intro _
      dsimp only
      obtain ⟨_, rfl⟩ := stores_word _ hst
      set x := dst0 + BitVec.ofNat 64 off
      have hx_nat : x.toNat = dst0.toNat + off := by
        simp only [x, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      refine ⟨hc, hm, hsh, hba, hbe, hg, ?_⟩
      intro c hk hf
      by_cases hcx : c = x
      · exfalso; subst hcx
        exact hk (dst0.toNat, len) (List.mem_singleton.2 rfl) ⟨by omega, by omega⟩
      · simp only [updW, hcx, ↓reduceIte]
        exact hfr c hk hf
  · intro hn; cases hn

private theorem mcf_store_byte {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 : BitVec 64} {len off : Nat}
    (hoff_lt : off < len) (hd_nw : dst0.toNat + len < 2 ^ 64)
    (hrel : MemCopyFrame s0 s dst0 len)
    (ed es : ExpHOL 64)
    (hed : evalAt s ed = some (.val (.word (dst0 + BitVec.ofNat 64 off))))
    (hnone : (evaluateHOLFiniteState s (.storeByte ed es)).1 = none) :
    MemCopyFrame s0 (evaluateHOLFiniteState s (.storeByte ed es)).2 dst0 len ∧
    (evaluateHOLFiniteState s (.storeByte ed es)).2.locals = s.locals := by
  obtain ⟨hc, hm, hsh, hba, hbe, hg, hfr⟩ := hrel
  have hl := (evaluate_storeByte_control_frame s ed es).2.2.1
  refine ⟨?_, hl⟩
  rw [evaluateHOLFiniteState_storeByte] at hnone ⊢
  unfold evalAt at hed
  rw [hed] at hnone ⊢
  dsimp only at hnone ⊢
  revert hnone
  split
  · rename_i vw hlb
    set x := dst0 + BitVec.ofNat 64 off
    have hx_nat : x.toNat = dst0.toNat + off := by
      simp only [x, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    split
    · rename_i mem' hst
      intro _
      dsimp only
      have hcell_frame : ∀ c : BitVec 64, c ≠ panByteAlignHOL x → mem' c = s.memory c := by
        intro c hne
        unfold panMemStoreByteWord8HOL at hst
        rcases s.memory (panByteAlignHOL x) with ⟨cell⟩
        dsimp only at hst
        split at hst
        · injection hst with hmeq; subst hmeq; simp [hne]
        · cases hst
      refine ⟨hc, hm, hsh, hba, hbe, hg, ?_⟩
      intro c hk hf
      by_cases hcx : c = panByteAlignHOL x
      · exfalso; subst hcx
        apply hk (dst0.toNat, len) (List.mem_singleton.2 rfl)
        unfold CellHits
        rw [panByteAlign_toNat64]
        omega
      · change mem' c = s0.memory c
        rw [hcell_frame c hcx]
        exact hfr c hk hf
    · intro hn; cases hn
  · intro hn; cases hn

private def mcfNoRet : ProgHOL 64 → Bool
  | .seq a b => mcfNoRet a && mcfNoRet b
  | .ite _ a b => mcfNoRet a && mcfNoRet b
  | .while _ a => mcfNoRet a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem mcf_eval_noRet {F : Type} (p : ProgHOL 64) (hp : mcfNoRet p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | assign k _ _ =>
    cases k with
    | global => simp [shape, mcfNoRet] at hp
    | «local» => rw [evaluateHOLFiniteState_assign]; split <;> [simp; (split <;> simp)]
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | seq a b =>
    have hab : mcfNoRet a = true ∧ mcfNoRet b = true := by
      simpa [shape, mcfNoRet, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := mcf_eval_noRet a hab.1 s v
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    have mclk : m.clock ≤ s.clock := rem
    cases r with
    | none => exact mcf_eval_noRet b hab.2 m v
    | some _ => exact ha
  | ite _ a b =>
    have hab : mcfNoRet a = true ∧ mcfNoRet b = true := by
      simpa [shape, mcfNoRet, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact mcf_eval_noRet b hab.2 s v
      · exact mcf_eval_noRet a hab.1 s v
    · simp
  | «while» cond body =>
    have hb : mcfNoRet body = true := by simpa [shape, mcfNoRet] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := mcf_eval_noRet body hb (decClockHOLFinite s) v
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none => exact mcf_eval_noRet (.while cond body) (by simpa [mcfNoRet] using hb) mid v
          | some r1 =>
            cases r1 with
            | «continue» => exact mcf_eval_noRet (.while cond body) (by simpa [mcfNoRet] using hb) mid v
            | returned _ => exact ih1
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, mcfNoRet] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

private def mcfNoBreak : ProgHOL 64 → Bool
  | .seq a b => mcfNoBreak a && mcfNoBreak b
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem mcf_eval_noBreak {F : Type} (p : ProgHOL 64) (hp : mcfNoBreak p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break := by
  cases shape : p with
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, mcfNoBreak] at hp
    | «local» => rw [evaluateHOLFiniteState_assign]; split <;> [simp; (split <;> simp)]
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | seq a b =>
    have hab : mcfNoBreak a = true ∧ mcfNoBreak b = true := by
      simpa [shape, mcfNoBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := mcf_eval_noBreak a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact mcf_eval_noBreak b hab.2 m
    | some _ => exact ha
  | _ => simp [shape, mcfNoBreak] at hp

private theorem mcf_while_loop {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (dst n : BitVec 64) (hn_small : n.toNat + 32 < 2 ^ 63)
    (step : BitVec 64) (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnc : noTopContinue body = true) (hnb : mcfNoBreak body = true)
    (hcond : (cond = .cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const step]) ∧ (step = 32#64 ∨ step = 8#64)) ∨
             (cond = .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")) ∧ step = 1#64))
    (hbody_spec : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      MemCopyFrame s0 st dst n.toNat →
      wi.toNat + step.toNat ≤ n.toNat →
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      (evaluateHOLFiniteState st body).1 = none →
      MemCopyFrame s0 (evaluateHOLFiniteState st body).2 dst n.toNat ∧
      (evaluateHOLFiniteState st body).2.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      (evaluateHOLFiniteState st body).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      (evaluateHOLFiniteState st body).2.locals.lookup (ofString "i") = some (.val (.word (wi + step))))
    (clk : Nat) (s u : PanSemStateFiniteExact 64 F) (wi : BitVec 64)
    (hclk : s.clock ≤ clk)
    (hrel : MemCopyFrame s0 s dst n.toNat)
    (hwi_le : wi.toNat ≤ n.toNat)
    (hd_loc : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn_loc : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi_loc : s.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, u)) :
    ∃ wi' : BitVec 64,
      MemCopyFrame s0 u dst n.toNat ∧
      wi'.toNat ≤ n.toNat ∧
      u.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      u.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      u.locals.lookup (ofString "i") = some (.val (.word wi')) := by
  induction clk generalizing s wi with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · split at hrun
      · split at hrun
        · simp at hrun
        · omega
      · injection hrun with _ hu; subst hu
        exact ⟨wi, hrel, hwi_le, hd_loc, hn_loc, hi_loc⟩
    · simp at hrun
  | succ clk ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond_ev
      split at hrun
      · rename_i hcw_nz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have hstep_le : wi.toNat + step.toNat ≤ n.toNat := by
            rw [evalHOLFinite_eq_toExact] at hcond_ev
            rcases hcond with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .notLower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hn_loc, hi_loc, valueIsWord, valueWord, wordOpHOL, wordOp] at hva hvb
              subst hva hvb
              have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
              change wi.toNat + (32#64 : BitVec 64).toNat ≤ n.toNat
              rw [h32]
              have hadd : (wi + 32#64).toNat = wi.toNat + 32 := by rw [BitVec.toNat_add, h32, Nat.mod_eq_of_lt (by omega)]
              by_contra hgt
              have hnle : ¬ (wi + 32#64 ≤ n) := by rw [BitVec.le_def, hadd]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnle] at hcw
              exact hcw_nz hcw
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .notLower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hn_loc, hi_loc, valueIsWord, valueWord, wordOpHOL, wordOp] at hva hvb
              subst hva hvb
              have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
              change wi.toNat + (8#64 : BitVec 64).toNat ≤ n.toNat
              rw [h8]
              have hadd : (wi + 8#64).toNat = wi.toNat + 8 := by rw [BitVec.toNat_add, h8, Nat.mod_eq_of_lt (by omega)]
              by_contra hgt
              have hnle : ¬ (wi + 8#64 ≤ n) := by rw [BitVec.le_def, hadd]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnle] at hcw
              exact hcw_nz hcw
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .lower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hn_loc, hi_loc] at hva hvb
              subst hva hvb
              have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
              change wi.toNat + (1#64 : BitVec 64).toNat ≤ n.toNat
              rw [h1]
              by_contra hgt
              have hnlt : ¬ (wi < n) := by rw [BitVec.lt_def]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt] at hcw
              exact hcw_nz hcw
          let sd := decClockHOLFinite s
          have hrel_sd : MemCopyFrame s0 sd dst n.toNat := memCopyFrame_locals_clock hrel s.locals (s.clock - 1)
          have hnc' := evaluate_noTopContinue body hnc sd
          have hnb' := mcf_eval_noBreak body hnb sd
          have hrem := evaluateHOLFiniteState_clock_le sd body
          rcases hbr : evaluateHOLFiniteState sd body with ⟨rb, mid⟩
          rw [hbr] at hrun hnc' hnb' hrem
          cases rb with
          | none =>
            have hb := hbody_spec sd wi hrel_sd hstep_le hd_loc hn_loc hi_loc (by rw [hbr])
            rw [hbr] at hb
            obtain ⟨hrel_m, hd_m, hn_m, hi_m⟩ := hb
            have h263 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
            have hw_add : (wi + step).toNat = wi.toNat + step.toNat := by
              rcases hcond with ⟨_, rfl | rfl⟩ | ⟨_, rfl⟩
              · rw [BitVec.toNat_add, show (32#64).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
              · rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
              · rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
            exact ih mid (wi + step) (by change mid.clock ≤ s.clock - 1 at hrem; omega)
              hrel_m (by omega) hd_m hn_m hi_m hrun
          | some r =>
            cases r with
            | «continue» => exact absurd rfl hnc'
            | «break» => exact absurd rfl hnb'
            | _ => simp at hrun
      · injection hrun with _ hu; subst hu
        exact ⟨wi, hrel, hwi_le, hd_loc, hn_loc, hi_loc⟩
    · simp at hrun

/-- Frame-only `memcpy(dst, src, n)` postcondition without any `Disj` requirement:
only cells hitting `(dst.toNat, n.toNat)` can change, and metadata/`be`/`globals` are preserved. -/
theorem memcpy_body_frame {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (dst n : BitVec 64)
    (hd_nw : dst.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hd_loc : s0.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn_loc : s0.locals.lookup (ofString "n") = some (.val (.word n)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).1 =
      some (.returned v)) :
    v = .val (.word 0#64) ∧
    MemCopyFrame s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).2
      dst n.toNat := by
  have seq_ret_or_none : ∀ (s : PanSemStateFiniteExact 64 F) (p1 p2 : ProgHOL 64) (rv : ValueHOL 64),
      (evaluateHOLFiniteState s (.seq p1 p2)).1 = some (.returned rv) →
      (evaluateHOLFiniteState s p1).1 = some (.returned rv) ∨
        ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
          (evaluateHOLFiniteState m p2).1 = some (.returned rv) := by
    intro s p1 p2 rv h
    rw [evaluateHOLFiniteState_seq_line780] at h
    rcases hr : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
    rw [hr] at h
    cases r1 with
    | none => exact Or.inr ⟨m, rfl, h⟩
    | some _ => exact Or.inl h
  have ed_i : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
        some (.val (.word (dst + BitVec.ofNat 64 wi.toNat))) := by
    intro st wi hd hi
    simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hd, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
  have ed_ik : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64) (off : Nat),
      wi.toNat + off ≤ n.toNat →
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (dst + BitVec.ofNat 64 (wi.toNat + off)))) := by
    intro st wi off hle hd hi
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hd, hi,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have h263 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hz]
    omega
  have assign_inc_ok : ∀ (st : PanSemStateFiniteExact 64 F) (wi step : BitVec 64),
      MemCopyFrame s0 st dst n.toNat →
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      MemCopyFrame s0 (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2 dst n.toNat ∧
      (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "i") = some (.val (.word (wi + step))) := by
    intro st wi step hrel hd hn hi
    have hrun : evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step])) =
        (none, setVarHOLFinite (ofString "i") (.val (.word (wi + step))) st) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hrun]
    refine ⟨memCopyFrame_locals_clock hrel _ st.clock, ?_, ?_, ?_⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd, show ofString "i" ≠ ofString "dst" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hret ⊢
  rw [evaluateHOLFiniteState_dec_total] at hret ⊢
  dsimp only at hret ⊢
  have hev0 : @evalHOLExact 64 F _ s0.toExact (fun x => Classical.propDecidable (s0.memaddrs x)) (.const 0#64) =
      some (.val (.word 0#64)) := rfl
  rw [hev0] at hret ⊢
  dsimp only at hret ⊢
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hret ⊢
  dsimp only at hret ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s0
  have hs1_rel : MemCopyFrame s0 s1 dst n.toNat := memCopyFrame_locals_clock (memCopyFrame_refl s0 dst n.toNat) _ s0.clock
  have hs1_d : s1.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd_loc, show ofString "i" ≠ ofString "dst" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_loc, show ofString "i" ≠ ofString "n" by decide]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rcases seq_ret_or_none s1 _ _ _ hret with h_ite_ret | ⟨s2, hs2, hret2⟩
  · exact False.elim (mcf_eval_noRet _ rfl s1 v h_ite_ret)
  have hs2_inv : ∃ wi2 : BitVec 64,
      MemCopyFrame s0 s2 dst n.toNat ∧
      wi2.toNat ≤ n.toNat ∧
      s2.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      s2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      s2.locals.lookup (ofString "i") = some (.val (.word wi2)) := by
    rw [evaluateHOLFiniteState_ite] at hs2
    split at hs2
    · split at hs2
      · rw [evaluateHOLFiniteState_skip] at hs2; injection hs2 with _ e; rw [← e]
        exact ⟨0#64, hs1_rel, Nat.zero_le _, hs1_d, hs1_n, hs1_i⟩
      · obtain ⟨m32, hm32, eq_s2⟩ := mcf_seq_none (congrArg Prod.fst hs2)
        have hs2_8 : evaluateHOLFiniteState m32 _ = (none, s2) := eq_s2.symm.trans hs2
        have hl32 := mcf_while_loop s0 dst n hn_small 32#64 _ _ rfl rfl (Or.inl ⟨rfl, Or.inl rfl⟩)
          (fun st wi hrel hstep hd hn hi hnone => by
            have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
            rw [h32] at hstep
            obtain ⟨m1, hm1, eq1⟩ := mcf_seq_none hnone; rw [eq1] at hnone ⊢
            obtain ⟨r1, hl1⟩ := mcf_store_word (by omega) hd_nw hrel _ _ (ed_i st wi hd hi) (congrArg Prod.fst hm1)
            rw [hm1] at r1 hl1
            obtain ⟨m2, hm2, eq2⟩ := mcf_seq_none hnone; rw [eq2] at hnone ⊢
            obtain ⟨r2, hl2⟩ := mcf_store_word (by omega) hd_nw r1 _ _ (ed_ik m1 wi 8 (by omega) (hl1 ▸ hd) (hl1 ▸ hi)) (congrArg Prod.fst hm2)
            rw [hm2] at r2 hl2; have hl2' := hl2.trans hl1
            obtain ⟨m3, hm3, eq3⟩ := mcf_seq_none hnone; rw [eq3] at hnone ⊢
            obtain ⟨r3, hl3⟩ := mcf_store_word (by omega) hd_nw r2 _ _ (ed_ik m2 wi 16 (by omega) (hl2' ▸ hd) (hl2' ▸ hi)) (congrArg Prod.fst hm3)
            rw [hm3] at r3 hl3; have hl3' := hl3.trans hl2'
            obtain ⟨m4, hm4, eq4⟩ := mcf_seq_none hnone; rw [eq4] at hnone ⊢
            obtain ⟨r4, hl4⟩ := mcf_store_word (by omega) hd_nw r3 _ _ (ed_ik m3 wi 24 (by omega) (hl3' ▸ hd) (hl3' ▸ hi)) (congrArg Prod.fst hm4)
            rw [hm4] at r4 hl4; have hl4' := hl4.trans hl3'
            exact assign_inc_ok m4 wi 32#64 r4 (hl4' ▸ hd) (hl4' ▸ hn) (hl4' ▸ hi))
          s1.clock s1 m32 0#64 le_rfl hs1_rel (Nat.zero_le _) hs1_d hs1_n hs1_i hm32
        obtain ⟨wi1, hrel1, hle1, hd1, hn1, hi1⟩ := hl32
        have hl8w := mcf_while_loop s0 dst n hn_small 8#64 _ _ rfl rfl (Or.inl ⟨rfl, Or.inr rfl⟩)
          (fun st wi hrel hstep hd hn hi hnone => by
            have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
            rw [h8] at hstep
            obtain ⟨m1, hm1, eq1⟩ := mcf_seq_none hnone; rw [eq1] at hnone ⊢
            obtain ⟨r1, hl1⟩ := mcf_store_word (by omega) hd_nw hrel _ _ (ed_i st wi hd hi) (congrArg Prod.fst hm1)
            rw [hm1] at r1 hl1
            exact assign_inc_ok m1 wi 8#64 r1 (hl1 ▸ hd) (hl1 ▸ hn) (hl1 ▸ hi))
          m32.clock m32 s2 wi1 le_rfl hrel1 hle1 hd1 hn1 hi1 hs2_8
        exact hl8w
    · simp at hs2
  obtain ⟨wi2, hrel2, hle2, hd2, hn2, hi2⟩ := hs2_inv
  rcases seq_ret_or_none s2 _ _ _ hret2 with h_l8b_ret | ⟨s3, hs3, hret3⟩
  · exact False.elim (mcf_eval_noRet _ rfl s2 v h_l8b_ret)
  have hl8b := mcf_while_loop s0 dst n hn_small 8#64 _ _ rfl rfl (Or.inl ⟨rfl, Or.inr rfl⟩)
    (fun st wi hrel hstep hd hn hi hnone => by
      have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
      rw [h8] at hstep
      obtain ⟨m0, hm0, eq0⟩ := mcf_seq_none hnone; rw [eq0] at hnone ⊢
      obtain ⟨r0, hl0⟩ := mcf_store_byte (by omega) hd_nw hrel _ _ (ed_i st wi hd hi) (congrArg Prod.fst hm0)
      rw [hm0] at r0 hl0
      obtain ⟨m1, hm1, eq1⟩ := mcf_seq_none hnone; rw [eq1] at hnone ⊢
      obtain ⟨r1, hl1⟩ := mcf_store_byte (by omega) hd_nw r0 _ _ (ed_ik m0 wi 1 (by omega) (hl0 ▸ hd) (hl0 ▸ hi)) (congrArg Prod.fst hm1)
      rw [hm1] at r1 hl1; have hl1' := hl1.trans hl0
      obtain ⟨m2, hm2, eq2⟩ := mcf_seq_none hnone; rw [eq2] at hnone ⊢
      obtain ⟨r2, hl2⟩ := mcf_store_byte (by omega) hd_nw r1 _ _ (ed_ik m1 wi 2 (by omega) (hl1' ▸ hd) (hl1' ▸ hi)) (congrArg Prod.fst hm2)
      rw [hm2] at r2 hl2; have hl2' := hl2.trans hl1'
      obtain ⟨m3, hm3, eq3⟩ := mcf_seq_none hnone; rw [eq3] at hnone ⊢
      obtain ⟨r3, hl3⟩ := mcf_store_byte (by omega) hd_nw r2 _ _ (ed_ik m2 wi 3 (by omega) (hl2' ▸ hd) (hl2' ▸ hi)) (congrArg Prod.fst hm3)
      rw [hm3] at r3 hl3; have hl3' := hl3.trans hl2'
      obtain ⟨m4, hm4, eq4⟩ := mcf_seq_none hnone; rw [eq4] at hnone ⊢
      obtain ⟨r4, hl4⟩ := mcf_store_byte (by omega) hd_nw r3 _ _ (ed_ik m3 wi 4 (by omega) (hl3' ▸ hd) (hl3' ▸ hi)) (congrArg Prod.fst hm4)
      rw [hm4] at r4 hl4; have hl4' := hl4.trans hl3'
      obtain ⟨m5, hm5, eq5⟩ := mcf_seq_none hnone; rw [eq5] at hnone ⊢
      obtain ⟨r5, hl5⟩ := mcf_store_byte (by omega) hd_nw r4 _ _ (ed_ik m4 wi 5 (by omega) (hl4' ▸ hd) (hl4' ▸ hi)) (congrArg Prod.fst hm5)
      rw [hm5] at r5 hl5; have hl5' := hl5.trans hl4'
      obtain ⟨m6, hm6, eq6⟩ := mcf_seq_none hnone; rw [eq6] at hnone ⊢
      obtain ⟨r6, hl6⟩ := mcf_store_byte (by omega) hd_nw r5 _ _ (ed_ik m5 wi 6 (by omega) (hl5' ▸ hd) (hl5' ▸ hi)) (congrArg Prod.fst hm6)
      rw [hm6] at r6 hl6; have hl6' := hl6.trans hl5'
      obtain ⟨m7, hm7, eq7⟩ := mcf_seq_none hnone; rw [eq7] at hnone ⊢
      obtain ⟨r7, hl7⟩ := mcf_store_byte (by omega) hd_nw r6 _ _ (ed_ik m6 wi 7 (by omega) (hl6' ▸ hd) (hl6' ▸ hi)) (congrArg Prod.fst hm7)
      rw [hm7] at r7 hl7; have hl7' := hl7.trans hl6'
      exact assign_inc_ok m7 wi 8#64 r7 (hl7' ▸ hd) (hl7' ▸ hn) (hl7' ▸ hi))
    s2.clock s2 s3 wi2 le_rfl hrel2 hle2 hd2 hn2 hi2 hs3
  obtain ⟨wi3, hrel3, hle3, hd3, hn3, hi3⟩ := hl8b
  rcases seq_ret_or_none s3 _ _ _ hret3 with h_l1b_ret | ⟨s4, hs4, hret4⟩
  · exact False.elim (mcf_eval_noRet _ rfl s3 v h_l1b_ret)
  have hl1b := mcf_while_loop s0 dst n hn_small 1#64 _ _ rfl rfl (Or.inr ⟨rfl, rfl⟩)
    (fun st wi hrel hstep hd hn hi hnone => by
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [h1] at hstep
      obtain ⟨m0, hm0, eq0⟩ := mcf_seq_none hnone; rw [eq0] at hnone ⊢
      obtain ⟨r0, hl0⟩ := mcf_store_byte (by omega) hd_nw hrel _ _ (ed_i st wi hd hi) (congrArg Prod.fst hm0)
      rw [hm0] at r0 hl0
      exact assign_inc_ok m0 wi 1#64 r0 (hl0 ▸ hd) (hl0 ▸ hn) (hl0 ▸ hi))
    s3.clock s3 s4 wi3 le_rfl hrel3 hle3 hd3 hn3 hi3 hs4
  obtain ⟨_, hrel4, _, _, _, _⟩ := hl1b
  have hret_eval : evaluateHOLFiniteState s4 (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s4) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [hret_eval] at hret4
  injection hret4 with hv_eq; injection hv_eq with hv_eq'
  refine ⟨hv_eq'.symm, ?_⟩
  rw [evaluateHOLFiniteState_seq_line780, hs2]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, hs3]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, hs4]
  dsimp only
  rw [hret_eval]
  exact memCopyFrame_locals_clock hrel4 _ s4.clock

/-! ## 3. `htab_find_leaf` and `htab_set` descent loop -/

theorem memW_node {F : Type} (x : PanSemStateFiniteExact 64 F) (nd w : BitVec 64) (off : Nat) :
    memW x (nd.toNat + 32 * w.toNat + off) =
      (match x.memory (nd + w * 32 + BitVec.ofNat 64 off) with | .word u => u.toNat) := by
  unfold memW; rw [ofNat_node_addr]

theorem ev_node_load {F : Type} (s : PanSemStateFiniteExact 64 F) (nd w off : BitVec 64)
    (h1 : s.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (h2 : s.locals.lookup (ofString "n") = some (.val (.word w))) (v : ValueHOL 64)
    (h : evalAt s (.load .one (.op .add [.var .local (ofString "nodes"),
      .panop .mul [.var .local (ofString "n"), .const 32], .const off])) = some v) :
    s.memaddrs (nd + w * 32 + off) ∧ v = .val (s.memory (nd + w * 32 + off)) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, h1, h2, panOpHOL, valueIsWord, valueWord, wordOpHOL,
    wordOp, memLoadHOLExact] at h
  rw [BitVec.add_assoc]
  exact ⟨h.1, h.2.symm⟩

theorem ev_field_load {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (tw off : BitVec 64)
    (h1 : s.locals.lookup x = some (.val (.word tw))) (v : ValueHOL 64)
    (h : evalAt s (.load .one (.op .add [.var .local x, .const off])) = some v) :
    s.memaddrs (tw + off) ∧ v = .val (s.memory (tw + off)) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, h1, valueIsWord, valueWord, wordOpHOL,
    wordOp, memLoadHOLExact] at h
  exact ⟨h.1, h.2.symm⟩

theorem LocFrame.setVar {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t)
    (x : MlS) (v : ValueHOL 64) : LocFrame s (setVarHOLFinite x v t) := h.locals _

theorem LocFrame.emptyLocals {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t) :
    LocFrame s (emptyLocalsHOLFinite t) := h.locals _

theorem LocFrame.memory {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t) :
    t.memory = s.memory := by
  unfold LocFrame at h; rw [h]

theorem locFrameW_dec {F : Type} {s : PanSemStateFiniteExact 64 F} (p : ProgHOL 64)
    (hp : locOnlyW p = true) : LocFrame s (evaluateHOLFiniteState (decClockHOLFinite s) p).2 := by
  have := locFrameW_eval p hp (decClockHOLFinite s)
  unfold LocFrame at this ⊢
  rw [this]; rfl

theorem active_n_ne {F : Type} (x : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hn : x.locals.lookup (ofString "n") = some (.val (.word w)))
    (h : LoopActive (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) x) : w ≠ 0 := by
  obtain ⟨c, hc, hnz⟩ := h
  change evalAt x _ = _ at hc
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp x .notEqual _ _ c hc
  simp [evalAt, evalHOLExact, hn] at ha
  simp [evalAt, evalHOLExact] at hb
  subst ha hb
  intro hw; subst hw
  simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
  exact hnz hcw

theorem condFalse_n_eq_zero {F : Type} (x : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hn : x.locals.lookup (ofString "n") = some (.val (.word w)))
    (hcf : CondFalse (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) x) : w = 0 := by
  unfold CondFalse at hcf
  change evalAt x _ = _ at hcf
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp x .notEqual _ _ 0 hcf
  simp [evalAt, evalHOLExact, hn] at ha hb
  subst ha hb
  by_cases hw0 : w = 0#64
  · exact hw0
  · exfalso; simp [Compiler.Encoders.Asm.wordCmpHOL, hw0] at hcw

theorem fl_iter {F : Type} (x : PanSemStateFiniteExact 64 F) (nd w kb : BitVec 64)
    (S : List Nat)
    (hnd : x.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (hn : x.locals.lookup (ofString "n") = some (.val (.word w)))
    (hkb : x.locals.lookup (ofString "keybits") = some (.val (.word kb)))
    (hw : w.toNat ∈ S)
    (htree : memW x (nd.toNat + 32 * w.toNat + 24) ≠ kb.toNat →
      memW x (nd.toNat + 32 * w.toNat + 8) ∈ S ∧ memW x (nd.toNat + 32 * w.toNat + 16) ∈ S)
    (body : ProgHOL 64)
    (hbody : body = .dec (ofString "b") .one (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const 32], .const 24]))
      (.seq (.ite (.cmp .equal (.var .local (ofString "b")) (.var .local (ofString "keybits")))
          .break .skip)
        (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const 3)])) (.op .sub [.const 7,
            .op .and [.var .local (ofString "b"), .const 7]]), .const 1]) (.const 0))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 8])))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 16]))))))
    : Flw x body (fun _ t => ∃ w' : BitVec 64,
        t.locals.lookup (ofString "n") = some (.val (.word w')) ∧ w'.toNat ∈ S) := by
  subst hbody
  apply Flw.dec
  intro bv hbv
  obtain ⟨_, rfl⟩ := ev_node_load x nd w 24 hnd hn bv hbv
  apply Flw.seq
  apply Flw.ite
  intro c hc
  constructor
  · intro _
    apply Flw.brk
    refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
    refine ⟨w, ?_, hw⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, PanRunBounded.resVarEq_lookup, hn,
      show ofString "n" ≠ ofString "b" by decide, show ofString "b" ≠ ofString "n" by decide]
  · intro hz
    apply Flw.skip
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    have hne : memW x (nd.toNat + 32 * w.toNat + 24) ≠ kb.toNat := by
      obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at ha
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hkb, show ofString "b" ≠ ofString "keybits" by decide] at hb
      subst hb
      rw [memW_node]
      have ha' : x.memory (nd + w * 32 + BitVec.ofNat 64 24) = .word a := ha
      rw [ha']
      intro heq
      have := BitVec.eq_of_toNat_eq heq
      subst this hz
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
    obtain ⟨h8, h16⟩ := htree hne
    apply Flw.ite
    intro c2 _
    constructor
    · intro _
      apply Flw.assign
      intro v hv
      obtain ⟨_, rfl⟩ := ev_node_load _ nd w 8
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd, show ofString "b" ≠ ofString "nodes" by decide])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "b" ≠ ofString "n" by decide]) v hv
      rw [memW_node] at h8
      rcases hm : x.memory (nd + w * 32 + 8) with ⟨u⟩
      refine ⟨u, ?_, ?_⟩
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          PanRunBounded.resVarEq_lookup, show ofString "n" ≠ ofString "b" by decide]
        exact hm
      · have : x.memory (nd + w * 32 + BitVec.ofNat 64 8) = .word u := hm
        rw [this] at h8; exact h8
    · intro _
      apply Flw.assign
      intro v hv
      obtain ⟨_, rfl⟩ := ev_node_load _ nd w 16
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd, show ofString "b" ≠ ofString "nodes" by decide])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "b" ≠ ofString "n" by decide]) v hv
      rw [memW_node] at h16
      rcases hm : x.memory (nd + w * 32 + 16) with ⟨u⟩
      refine ⟨u, ?_, ?_⟩
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          PanRunBounded.resVarEq_lookup, show ofString "n" ≠ ofString "b" by decide]
        exact hm
      · have : x.memory (nd + w * 32 + BitVec.ofNat 64 16) = .word u := hm
        rw [this] at h16; exact h16

theorem fl_brk {F : Type} (x : PanSemStateFiniteExact 64 F) (nd w kb : BitVec 64)
    (hnd : x.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (hn : x.locals.lookup (ofString "n") = some (.val (.word w)))
    (hkb : x.locals.lookup (ofString "keybits") = some (.val (.word kb)))
    (body : ProgHOL 64)
    (hbody : body = .dec (ofString "b") .one (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const 32], .const 24]))
      (.seq (.ite (.cmp .equal (.var .local (ofString "b")) (.var .local (ofString "keybits")))
          .break .skip)
        (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const 3)])) (.op .sub [.const 7,
            .op .and [.var .local (ofString "b"), .const 7]]), .const 1]) (.const 0))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 8])))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 16]))))))
    : Flw x body (fun r t => r = some .break →
        t.locals.lookup (ofString "n") = some (.val (.word w)) ∧
        memW x (nd.toNat + 32 * w.toNat + 24) = kb.toNat) := by
  subst hbody
  apply Flw.dec
  intro bv hbv
  obtain ⟨_, rfl⟩ := ev_node_load x nd w 24 hnd hn bv hbv
  apply Flw.seq
  apply Flw.ite
  intro c hc
  constructor
  · intro hc0
    apply Flw.brk
    refine ⟨fun h => absurd h (by simp), fun _ _ => ⟨?_, ?_⟩⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        PanRunBounded.resVarEq_lookup, hn, show ofString "n" ≠ ofString "b" by decide,
        show ofString "b" ≠ ofString "n" by decide]
    · obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at ha
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hkb, show ofString "b" ≠ ofString "keybits" by decide] at hb
      subst hb
      have hab : a = kb := by
        by_contra hne
        simp [Compiler.Encoders.Asm.wordCmpHOL, hne] at hcw
        exact hc0 hcw
      subst hab
      rw [memW_node]
      have ha' : x.memory (nd + w * 32 + BitVec.ofNat 64 24) = .word a := ha
      rw [ha']
  · intro _
    apply Flw.skip
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply Flw.ite
    intro c2 _
    constructor <;> intro _ <;> apply Flw.assign <;> intro v _ <;> intro h <;> cases h

theorem find_leaf_ret2 {F : Type} (E : PanSemStateFiniteExact 64 F)
    (tw : BitVec 64) (ht : E.locals.lookup (ofString "t") = some (.val (.word tw)))
    (S : List Nat)
    (hroot : ∀ u, E.memory (tw + 56) = .word u → u.toNat ∈ S)
    (htree : ∀ nd k : BitVec 64, E.memory (tw + 40) = .word nd → E.memory (tw + 0) = .word k →
      ∀ w : BitVec 64, w.toNat ∈ S → w ≠ 0 →
        memW E (nd.toNat + 32 * w.toNat + 24) ≠ (k * 8).toNat →
        memW E (nd.toNat + 32 * w.toNat + 8) ∈ S ∧ memW E (nd.toNat + 32 * w.toNat + 16) ∈ S) :
    Ret E (sourceFnBody Guest.Software.guestFn_htab_find_leaf)
      (fun v post => ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ∈ S ∧ LocFrame E post ∧
        (w ≠ 0 → ∀ nd k : BitVec 64, E.memory (tw + 40) = .word nd → E.memory (tw + 0) = .word k →
          memW E (nd.toNat + 32 * w.toNat + 24) = (k * 8).toNat)) := by
  htab_unfold Guest.Software.guestFn_htab_find_leaf
  apply Ret.dec
  intro kbv hkbv
  rcases hk : E.memory (tw + 0) with ⟨k⟩
  have hk' : E.memory tw = .word k := by simpa using hk
  have hkbv' : kbv = .val (.word (k * 8)) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, ht, valueIsWord, valueWord, wordOpHOL, wordOp,
      memLoadHOLExact, panOpHOL, hk'] at hkbv
    by_cases hm : E.memaddrs tw
    · simp [hm] at hkbv; exact hkbv.symm
    · simp [hm] at hkbv
  subst hkbv'
  apply Ret.dec
  intro ndv hndv
  rcases hnd : E.memory (tw + 40) with ⟨nd⟩
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 40
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht, show ofString "keybits" ≠ ofString "t" by decide]) ndv hndv
  apply Ret.dec
  intro nv hnv
  rcases hrt : E.memory (tw + 56) with ⟨r0⟩
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 56
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "nodes" ≠ ofString "t" by decide, show ofString "keybits" ≠ ofString "t" by decide]) nv hnv
  simp only [setVarHOLFinite] at *
  set E3 := { E with locals := ((E.locals.update (ofString "keybits", .val (.word (k * 8)))).update
    (ofString "nodes", .val (E.memory (tw + 40)))).update (ofString "n", .val (E.memory (tw + 56))) }
    with hE3
  apply Ret.seq
  · intro w hw
    exfalso
    revert hw
    apply while_noRet _ _ _ _ _ le_rfl
    exact NoRet.dec' (NoRet.seq (NoRet.ite NoRet.brk NoRet.skip) (NoRet.ite NoRet.assign NoRet.assign))
  · intro u hu
    let J : PanSemStateFiniteExact 64 F → Prop := fun y =>
      LocFrame E y ∧ y.locals.lookup (ofString "nodes") = some (.val (.word nd)) ∧
        y.locals.lookup (ofString "keybits") = some (.val (.word (k * 8))) ∧
        ∃ w : BitVec 64, y.locals.lookup (ofString "n") = some (.val (.word w)) ∧ w.toNat ∈ S
    have hJ3 : J E3 := by
      refine ⟨LocFrame.locals (LocFrame.refl E) _, ?_, ?_, r0, ?_, hroot r0 hrt⟩
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "n" ≠ ofString "nodes" by decide]; exact hnd
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "keybits" by decide, show ofString "nodes" ≠ ofString "keybits" by decide]
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE]; exact hrt
    let Bk : PanSemStateFiniteExact 64 F → Prop := fun y => J y ∧
      ∃ w : BitVec 64, y.locals.lookup (ofString "n") = some (.val (.word w)) ∧
        memW E (nd.toNat + 32 * w.toNat + 24) = (k * 8).toNat
    have hJu : (J u ∧ CondFalse (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) u) ∨ Bk u := by
      have := while_inv2 J Bk _ _ ?_ E3.clock E3 le_rfl hJ3 (by rw [hu])
      · rw [hu] at this; exact this
      · intro x hx hact _
        obtain ⟨hfr, hxnd, hxkb, w, hxn, hwS⟩ := hx
        have hw0 := active_n_ne x w hxn hact
        have hmem := hfr.memory
        have hm : ∀ a, memW (decClockHOLFinite x) a = memW E a := fun a => by
          simp only [memW, decClockHOLFinite, hmem]
        constructor
        · intro hflow
          have hflow' : FlowR _ := hflow.elim Or.inl (fun h => Or.inr (Or.inl h))
          have hit := fl_iter (decClockHOLFinite x) nd w (k * 8) S hxnd hxn hxkb hwS (by
            intro hne
            simp only [hm] at hne ⊢
            exact htree nd k hnd hk w hwS hw0 hne) _ rfl hflow'
          obtain ⟨w', hw', hw'S⟩ := hit
          refine ⟨hfr.trans (locFrameW_dec _ (by rfl)), ?_, ?_, w', hw', hw'S⟩
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]; decide) _ (flowing_of_flowR hflow')]
            exact hxnd
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]; decide) _ (flowing_of_flowR hflow')]
            exact hxkb
        · intro hbrk
          have hflow' : FlowR _ := Or.inr (Or.inr hbrk)
          have hbk := fl_brk (decClockHOLFinite x) nd w (k * 8) hxnd hxn hxkb _ rfl hflow' hbrk
          obtain ⟨hn', hcrit⟩ := hbk
          refine ⟨⟨hfr.trans (locFrameW_dec _ (by rfl)), ?_, ?_, w, hn', hwS⟩, w, hn', ?_⟩
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]; decide) _ (flowing_of_flowR hflow')]
            exact hxnd
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]; decide) _ (flowing_of_flowR hflow')]
            exact hxkb
          · rw [hm] at hcrit
            exact hcrit
    apply Ret.ret
    intro val hval
    rcases hJu with ⟨⟨hfr, _, _, w, hun, hwS⟩, hcf⟩ | ⟨⟨hfr, _, _, w0, hun0, hwS0⟩, w, hun, hcrit⟩
    · simp [evalAt, evalHOLExact, hun] at hval
      subst hval
      refine ⟨w, rfl, hwS, (hfr.emptyLocals.locals _).locals _ |>.locals _ |>.locals _, ?_⟩
      intro hw0
      exact absurd (condFalse_n_eq_zero u w hun hcf) hw0
    · simp [evalAt, evalHOLExact, hun] at hval
      subst hval
      refine ⟨w, rfl, ?_, (hfr.emptyLocals.locals _).locals _ |>.locals _ |>.locals _, ?_⟩
      · rw [hun0] at hun
        simp at hun
        rw [← hun]; exact hwS0
      · intro _ nd' k' hnd' hk'
        simp only [HolWordLab.word.injEq] at hnd' hk'
        subst hnd' hk'
        exact hcrit

/-- Corollary of `find_leaf_ret2` specialized to a well-formed table `HtabWF E tw.toNat`:
- If `cnt = 0`, returns `w = 0`.
- If `0 < cnt`, returns `w` with `w.toNat ∈ L` (a live leaf!).
Wait: can `htab_find_leaf` return `0` when `0 < cnt`?
In `HtabWF`: `0 < cnt → root ∈ L ++ I`, and every `n ∈ L ++ I` has `1 ≤ n < next` so `n ≠ 0`!
And every `n ∈ I` has `nd n 8 ∈ L ++ I` and `nd n 16 ∈ L ++ I`, which are also `≥ 1` so `≠ 0`!
Thus when `0 < cnt`, `S = L ++ I` (WITHOUT `0`!) is closed under root and children!
Wait — THAT'S HUGE!!
Let's check! When `0 < cnt`, `root ∈ L ++ I`. Every `n ∈ L ++ I` satisfies `1 ≤ n`, so `w ≠ 0`!
Wait: what if `w.toNat ∈ L ++ I` and `w` is a 64-bit word with `w.toNat ≥ 1`? Then `w ≠ 0`!
So the loop NEVER exits via `n == 0` when `0 < cnt` — it ONLY exits via `break` when `b == keybits`,
and since every `n ∈ I` has `nd n 24 < 8 * klen = (k * 8).toNat`, `w.toNat` CANNOT be in `I`, so `w.toNat ∈ L`!
WAIT A SECOND! Is `htab_find_leaf` guaranteed to return `w = 0` iff `cnt = 0`?!
Let's verify!!
1. Suppose `cnt = 0`. By `HtabWF`, `cnt = 0 → root = 0`. And `r0.toNat = hdr E tw 7 = root = 0`, so `r0 = 0`!
   Take `S = [0]`: `r0.toNat = 0 ∈ [0]`, and `htree` has hypothesis `w.toNat ∈ [0]` and `w ≠ 0`, which is vacuously false!
   So `find_leaf_ret2` with `S = [0]` gives `w.toNat ∈ [0]`, hence `w = 0`!
2. Suppose `0 < cnt`. Take `S = L ++ I`!
   - `hroot`: `u.toNat = hdr E tw 7 = root ∈ L ++ I = S`!
   - `htree`: if `w.toNat ∈ L ++ I` and `nd w 24 ≠ 8 * klen`, then `w.toNat ∉ L` (since leaves have `nd _ 24 = 8 * klen`), so `w.toNat ∈ I`, hence `nd w 8 ∈ L ++ I` and `nd w 16 ∈ L ++ I`!
   - Then `find_leaf_ret2` gives `w.toNat ∈ L ++ I`!
   - Since `∀ x ∈ L ++ I, 1 ≤ x`, we have `1 ≤ w.toNat`, so `w ≠ 0`!
   - Therefore `hcrit` fires: `nd w.toNat 24 = 8 * klen`!
   - Since `∀ x ∈ I, nd x 24 < 8 * klen`, `w.toNat ∉ I`, so `w.toNat ∈ L`!!
MIND BLOWN!! That simultaneously proves:
- In branch `leaf == 0` of `htab_set`: `cnt = 0` (table is empty! `L = []`, `I = []`, `root = 0`)!
- In branch `leaf != 0` of `htab_set`: `0 < cnt` AND `leaf.toNat ∈ L` (so `1 ≤ leaf.toNat < next ≤ ncap + 1`, and in overwrite or `memeq` / `htab_first_diff`, `keys + leaf * stride` is in-bounds of `keys`, and `nodes + leaf * 32 + 8` is a leaf's `+8` field)! -/
theorem find_leaf_spec_wf {F : Type} (E : PanSemStateFiniteExact 64 F)
    (tw : BitVec 64) (ht : E.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hW : HtabWF E tw.toNat) :
    Ret E (sourceFnBody Guest.Software.guestFn_htab_find_leaf)
      (fun v post => ∃ w : BitVec 64, v = .val (.word w) ∧ LocFrame E post ∧
        ((w = 0 ∧ hdr E tw.toNat 3 = 0) ∨
         (w ≠ 0 ∧ 0 < hdr E tw.toNat 3 ∧
          ∀ L I Fr, TreeWF L I Fr (hdr E tw.toNat 8) (hdr E tw.toNat 0) (hdr E tw.toNat 3)
            (hdr E tw.toNat 7) (hdr E tw.toNat 9) (nodeF E (hdr E tw.toNat 5))
            (fun i => memW E (hdr E tw.toNat 6 + 8 * i)) → w.toNat ∈ L))) := by
  have ⟨hB, L0, I0, Fr0, hT0⟩ := (htabWF_iff E tw.toNat).mp hW
  obtain ⟨_, hk_mem⟩ := word_of_hdr E tw 0 (by omega) hB
  obtain ⟨_, hnd_mem⟩ := word_of_hdr E tw 5 (by omega) hB
  obtain ⟨_, hrt_mem⟩ := word_of_hdr E tw 7 (by omega) hB
  have hk0 : tw + BitVec.ofNat 64 (8 * 0) = tw + 0 := rfl
  have hnd40 : tw + BitVec.ofNat 64 (8 * 5) = tw + 40 := rfl
  have hrt56 : tw + BitVec.ofNat 64 (8 * 7) = tw + 56 := rfl
  rw [hk0] at hk_mem; rw [hnd40] at hnd_mem; rw [hrt56] at hrt_mem
  have hk_lt : hdr E tw.toNat 0 ≤ 60 := hB.2.2.2.1
  by_cases hcnt0 : hdr E tw.toNat 3 = 0
  · have hr0 : hdr E tw.toNat 7 = 0 := hT0.2.2.2.2.2.2.1 hcnt0
    intro v hv
    obtain ⟨w, rfl, hwS, hfr, _⟩ := find_leaf_ret2 E tw ht [0]
      (fun u hu => by
        rw [hrt_mem, hr0] at hu
        injection hu with hu'; subst hu'; simp)
      (fun _ _ _ _ w hwS hw0 _ => by
        simp at hwS
        exact absurd (BitVec.eq_of_toNat_eq (by simpa using hwS)) hw0)
      v hv
    simp at hwS
    exact ⟨w, rfl, hfr, Or.inl ⟨BitVec.eq_of_toNat_eq (by simpa using hwS), hcnt0⟩⟩
  · have hcnt_pos : 0 < hdr E tw.toNat 3 := by omega
    intro v hv
    obtain ⟨w, rfl, hwS, hfr, hcrit⟩ := find_leaf_ret2 E tw ht (L0 ++ I0)
      (fun u hu => by
        rw [hrt_mem] at hu; injection hu with hu'; subst hu'
        have hr_lt : hdr E tw.toNat 7 < 2 ^ 64 := by
          have hmem := (hT0.2.2.1 _).mp (List.mem_append_left _ (hT0.2.2.2.2.2.2.2.1 hcnt_pos).1)
          have hnodes_in := (hB.1 (hdr E tw.toNat 5, (hdr E tw.toNat 10 + 1) * 32) (by simp [htabFootprint])).1
          have hhe : heapEnd < 2 ^ 64 := by decide
          have hnx := hB.2.2.2.2.2.2.2
          unfold Inside at hnodes_in
          omega
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt]
        exact (hT0.2.2.2.2.2.2.2.1 hcnt_pos).1)
      (fun nd' k' hnd' hk' w hwS hw0 hne => by
        rw [hnd_mem] at hnd'; rw [hk_mem] at hk'
        injection hnd' with hnd_eq; injection hk' with hk_eq
        subst hnd_eq hk_eq
        have hnd_lt : hdr E tw.toNat 5 < 2 ^ 64 := by
          have hnodes_in := (hB.1 (hdr E tw.toNat 5, (hdr E tw.toNat 10 + 1) * 32) (by simp [htabFootprint])).1
          have hhe : heapEnd < 2 ^ 64 := by decide
          unfold Inside at hnodes_in; omega
        have hnd_nat : (BitVec.ofNat 64 (hdr E tw.toNat 5)).toNat = hdr E tw.toNat 5 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnd_lt]
        have hk8_nat : (BitVec.ofNat 64 (hdr E tw.toNat 0) * 8).toNat = 8 * hdr E tw.toNat 0 := by
          rw [BitVec.toNat_mul, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]
          omega
        rw [hnd_nat] at hne ⊢
        rw [hk8_nat] at hne
        rcases List.mem_append.mp hwS with hwL | hwI
        · exfalso
          obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hwL
          have hc := (hT0.2.2.2.2.1 i hi).2.1
          rw [hiw] at hc
          exact hne hc
        · obtain ⟨_, h8, h16, _⟩ := hT0.2.2.2.2.2.1 _ hwI
          exact ⟨h8, h16⟩)
      v hv
    have hw_ge1 : 1 ≤ w.toNat := ((hT0.2.2.1 w.toNat).mp (List.mem_append_left _ hwS)).1
    have hw_nz : w ≠ 0 := by
      intro h0; subst h0; simp at hw_ge1
    have hc := hcrit hw_nz _ _ hnd_mem hk_mem
    have hnd_lt : hdr E tw.toNat 5 < 2 ^ 64 := by
      have hnodes_in := (hB.1 (hdr E tw.toNat 5, (hdr E tw.toNat 10 + 1) * 32) (by simp [htabFootprint])).1
      have hhe : heapEnd < 2 ^ 64 := by decide
      unfold Inside at hnodes_in; omega
    have hnd_nat : (BitVec.ofNat 64 (hdr E tw.toNat 5)).toNat = hdr E tw.toNat 5 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnd_lt]
    have hk8_nat : (BitVec.ofNat 64 (hdr E tw.toNat 0) * 8).toNat = 8 * hdr E tw.toNat 0 := by
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]
      omega
    rw [hnd_nat, hk8_nat] at hc
    refine ⟨w, rfl, hfr, Or.inr ⟨hw_nz, hcnt_pos, ?_⟩⟩
    intro L I Fr hT
    have hw_lt : w.toNat < hdr E tw.toNat 8 := ((hT0.2.2.1 w.toNat).mp (List.mem_append_left _ hwS)).2
    have hw_mem : w.toNat ∈ L ++ I ++ Fr := (hT.2.2.1 w.toNat).mpr ⟨hw_ge1, hw_lt⟩
    -- Wait: can `w.toNat` be in `Fr` for another decomposition `(L, I, Fr)`?
    -- Wait: `L` is uniquely determined by `order[0..cnt)`! Every `L[i] = ord i`!
    -- Even simpler: let's also check `L = L0` because `L.length = cnt = L0.length` and `L[i] = ord i = L0[i]`!
    have hLw0 : w.toNat ∈ L0 := by
      rcases List.mem_append.mp hwS with hwL | hwI
      · exact hwL
      · exfalso
        have hlt := (hT0.2.2.2.2.2.1 _ hwI).1
        unfold nodeF at hlt
        omega
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hLw0
    have hlen_eq : L.length = L0.length := hT.1.trans hT0.1.symm
    have hiL : i < L.length := by omega
    have hord_i0 := (hT0.2.2.2.2.1 i hi).1
    have hord_i := (hT.2.2.2.2.1 i hiL).1
    have heq_elem : L[i] = w.toNat := by omega
    rw [← heq_elem]
    exact List.getElem_mem hiL

/-! ### `htab_set` descent loop invariant -/

/-- One iteration of `htab_set`'s `while (n != 0)` loop:
```
dec b := load(nodes + n * 32 + 24);
if (b >= d) break;
p := n;
if (((loadByte(key + (b >>> 3)) >>> (7 - (b & 7))) & 1) == 0)
  n := load(nodes + n * 32 + 8)
else
  n := load(nodes + n * 32 + 16)
```
When `0 < cnt`, `n` starts at `root ∈ L ++ I` and `p` starts at `0`, so the pair `(p, n)` satisfies:
`n.toNat ∈ L ++ I ∧ ((p = 0 ∧ n.toNat = root) ∨ (p.toNat ∈ I ∧ n.toNat ≠ root ∧ p.toNat = nodeF E nodes n.toNat 0))`.
And because `d < 8 * klen`:
- If `b < d`, then `b < 8 * klen`, so `n.toNat ∉ L` (since leaves have `b = 8 * klen`), hence `n.toNat ∈ I`!
  Then `p' := n` has `p'.toNat ∈ I`, and `n'` is either `nd n 8` or `nd n 16`, both of which are in `L ++ I`,
  satisfy `n' ≠ root` (by `hrc`), and satisfy `nd n' 0 = n.toNat = p'.toNat` (by `hint`)!
- And `n'` always satisfies `1 ≤ n'.toNat` so `n' ≠ 0`, meaning the `CondFalse` (`n == 0`) exit is impossible! -/
theorem set_descent_iter {F : Type} (x : PanSemStateFiniteExact 64 F)
    (nd dw pw nw : BitVec 64) (L I : List Nat) (klen root : Nat)
    (hnd : x.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (hd_loc : x.locals.lookup (ofString "d") = some (.val (.word dw)))
    (hp_loc : x.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hn_loc : x.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hd_lt : dw.toNat < 8 * klen)
    (hn_LI : nw.toNat ∈ L ++ I)
    (hleaves : ∀ z ∈ L, nodeF x nd.toNat z 24 = 8 * klen)
    (hint : ∀ z ∈ I, nodeF x nd.toNat z 24 < 8 * klen ∧
      nodeF x nd.toNat z 8 ∈ L ++ I ∧ nodeF x nd.toNat z 16 ∈ L ++ I ∧
      nodeF x nd.toNat z 8 ≠ root ∧ nodeF x nd.toNat z 16 ≠ root ∧
      nodeF x nd.toNat (nodeF x nd.toNat z 8) 0 = z ∧
      nodeF x nd.toNat (nodeF x nd.toNat z 16) 0 = z)
    (body : ProgHOL 64)
    (hbody : body = .dec (ofString "b") .one (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const 32], .const 24]))
      (.seq (.ite (.cmp .notLower (.var .local (ofString "b")) (.var .local (ofString "d")))
          .break .skip)
        (.seq (.assign .local (ofString "p") (.var .local (ofString "n")))
          (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
              .shift .lsr (.var .local (ofString "b")) (.const 3)])) (.op .sub [.const 7,
              .op .and [.var .local (ofString "b"), .const 7]]), .const 1]) (.const 0))
            (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const 32], .const 8])))
            (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const 32], .const 16]))))))) :
    Flw x body (fun r t =>
      (r = some .break →
        t.locals.lookup (ofString "p") = some (.val (.word pw)) ∧
        t.locals.lookup (ofString "n") = some (.val (.word nw))) ∧
      (r ≠ some .break →
        ∃ nw' : BitVec 64,
          t.locals.lookup (ofString "p") = some (.val (.word nw)) ∧
          t.locals.lookup (ofString "n") = some (.val (.word nw')) ∧
          nw'.toNat ∈ L ++ I ∧ nw.toNat ∈ I ∧ nw'.toNat ≠ root ∧
          nw.toNat = nodeF x nd.toNat nw'.toNat 0)) := by
  subst hbody
  apply Flw.dec
  intro bv hbv
  obtain ⟨_, rfl⟩ := ev_node_load x nd nw 24 hnd hn_loc bv hbv
  apply Flw.seq
  apply Flw.ite
  intro c hc
  constructor
  · intro _
    apply Flw.brk
    refine ⟨fun h => absurd h (by simp), fun _ => ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd rfl h⟩⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        PanRunBounded.resVarEq_lookup, hp_loc,
        show ofString "p" ≠ ofString "b" by decide, show ofString "b" ≠ ofString "p" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        PanRunBounded.resVarEq_lookup, hn_loc,
        show ofString "n" ≠ ofString "b" by decide, show ofString "b" ≠ ofString "n" by decide]
  · intro hz
    apply Flw.skip
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    have hlt_d : nodeF x nd.toNat nw.toNat 24 < dw.toNat := by
      obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .notLower _ _ c hc
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at ha
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hd_loc, show ofString "b" ≠ ofString "d" by decide] at hb
      subst hb
      unfold nodeF
      rw [memW_node]
      have ha' : x.memory (nd + nw * 32 + BitVec.ofNat 64 24) = .word a := ha
      rw [ha']
      dsimp only
      by_contra hge
      have hle_bv : dw ≤ a := by rw [BitVec.le_def]; omega
      simp [Compiler.Encoders.Asm.wordCmpHOL, hle_bv] at hcw
      exact absurd hcw (by rw [hz]; decide)
    have hnw_I : nw.toNat ∈ I := by
      rcases List.mem_append.mp hn_LI with hL | hI
      · exfalso; have := hleaves _ hL; omega
      · exact hI
    obtain ⟨_, h8_LI, h16_LI, h8_nr, h16_nr, h8_p, h16_p⟩ := hint _ hnw_I
    apply Flw.seq
    apply Flw.assign
    intro pv hpv
    have hpv_eq : pv = .val (.word nw) := by
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hn_loc, show ofString "b" ≠ ofString "n" by decide] at hpv
      exact hpv.symm
    subst hpv_eq
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply Flw.ite
    intro c2 _
    constructor
    · intro _
      apply Flw.assign
      intro v8 hv8
      obtain ⟨_, rfl⟩ := ev_node_load _ nd nw 8
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd,
          show ofString "p" ≠ ofString "nodes" by decide, show ofString "b" ≠ ofString "nodes" by decide])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_loc,
          show ofString "p" ≠ ofString "n" by decide, show ofString "b" ≠ ofString "n" by decide]) v8 hv8
      cases hm8 : x.memory (nd + nw * 32 + 8) with
      | word u8 =>
        have hu8_eq : nodeF x nd.toNat nw.toNat 8 = u8.toNat := by
          unfold nodeF; rw [memW_node]
          have hm8' : x.memory (nd + nw * 32 + BitVec.ofNat 64 8) = .word u8 := hm8
          rw [hm8']
        constructor
        · intro h; cases h
        · intro _
          refine ⟨u8, ?_, ?_, ?_, hnw_I, ?_, ?_⟩
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              PanRunBounded.resVarEq_lookup,
              show ofString "p" ≠ ofString "b" by decide, show ofString "b" ≠ ofString "p" by decide,
              show ofString "n" ≠ ofString "p" by decide]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              PanRunBounded.resVarEq_lookup, show ofString "n" ≠ ofString "b" by decide,
              show ofString "b" ≠ ofString "n" by decide]
            exact hm8
          · rw [← hu8_eq]; exact h8_LI
          · rw [← hu8_eq]; exact h8_nr
          · rw [← hu8_eq]; exact h8_p.symm
    · intro _
      apply Flw.assign
      intro v16 hv16
      obtain ⟨_, rfl⟩ := ev_node_load _ nd nw 16
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd,
          show ofString "p" ≠ ofString "nodes" by decide, show ofString "b" ≠ ofString "nodes" by decide])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_loc,
          show ofString "p" ≠ ofString "n" by decide, show ofString "b" ≠ ofString "n" by decide]) v16 hv16
      cases hm16 : x.memory (nd + nw * 32 + 16) with
      | word u16 =>
        have hu16_eq : nodeF x nd.toNat nw.toNat 16 = u16.toNat := by
          unfold nodeF; rw [memW_node]
          have hm16' : x.memory (nd + nw * 32 + BitVec.ofNat 64 16) = .word u16 := hm16
          rw [hm16']
        constructor
        · intro h; cases h
        · intro _
          refine ⟨u16, ?_, ?_, ?_, hnw_I, ?_, ?_⟩
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              PanRunBounded.resVarEq_lookup,
              show ofString "p" ≠ ofString "b" by decide, show ofString "b" ≠ ofString "p" by decide,
              show ofString "n" ≠ ofString "p" by decide]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              PanRunBounded.resVarEq_lookup, show ofString "n" ≠ ofString "b" by decide,
              show ofString "b" ≠ ofString "n" by decide]
            exact hm16
          · rw [← hu16_eq]; exact h16_LI
          · rw [← hu16_eq]; exact h16_nr
          · rw [← hu16_eq]; exact h16_p.symm

/-- Full `while (n != 0)` descent loop of `htab_set`: preserves `LocFrame`, avoids all locals
except `p` and `n`, and exits with `n.toNat ∈ L ++ I` and `(p = 0 ∧ n = root) ∨ (p ∈ I ∧ n ≠ root ∧ p = nd n 0)`. -/
theorem set_descent_loop {F : Type} (s0 u : PanSemStateFiniteExact 64 F)
    (nd dw rw0 : BitVec 64) (L I Fr : List Nat) (next klen cnt root free : Nat)
    (ord : Nat → Nat)
    (hcnt_pos : 0 < cnt)
    (hd_lt : dw.toNat < 8 * klen)
    (hnext_lt : next ≤ 2 ^ 64)
    (hrw0 : rw0.toNat = root)
    (hT : TreeWF L I Fr next klen cnt root free (nodeF s0 nd.toNat) ord)
    (hnd_s0 : s0.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (hd_s0 : s0.locals.lookup (ofString "d") = some (.val (.word dw)))
    (hp_s0 : s0.locals.lookup (ofString "p") = some (.val (.word 0#64)))
    (hn_s0 : s0.locals.lookup (ofString "n") = some (.val (.word rw0)))
    (body : ProgHOL 64)
    (hbody : body = .dec (ofString "b") .one (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const 32], .const 24]))
      (.seq (.ite (.cmp .notLower (.var .local (ofString "b")) (.var .local (ofString "d")))
          .break .skip)
        (.seq (.assign .local (ofString "p") (.var .local (ofString "n")))
          (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
              .shift .lsr (.var .local (ofString "b")) (.const 3)])) (.op .sub [.const 7,
              .op .and [.var .local (ofString "b"), .const 7]]), .const 1]) (.const 0))
            (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const 32], .const 8])))
            (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const 32], .const 16])))))))
    (hu : evaluateHOLFiniteState s0 (.while (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) body) = (none, u)) :
    LocFrame s0 u ∧
    (∀ k : MlS, k ≠ ofString "p" → k ≠ ofString "n" → u.locals.lookup k = s0.locals.lookup k) ∧
    ∃ pw nw : BitVec 64,
      u.locals.lookup (ofString "p") = some (.val (.word pw)) ∧
      u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      nw.toNat ∈ L ++ I ∧
      ((pw.toNat = 0 ∧ nw.toNat = root) ∨
       (pw.toNat ∈ I ∧ nw.toNat ≠ root ∧ pw.toNat = nodeF s0 nd.toNat nw.toNat 0)) := by
  have hloc_keep : ∀ k : MlS, k ≠ ofString "p" → k ≠ ofString "n" → u.locals.lookup k = s0.locals.lookup k := by
    intro k hkp hkn
    have hav : avoidsLocal k (.while (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) body) = true := by
      subst hbody
      by_cases hkb : ofString "b" = k
      · simp [avoidsLocal, hkb]
      · simp [avoidsLocal, hkb, Ne.symm hkp, Ne.symm hkn]
    have hfl : Flowing (evaluateHOLFiniteState s0 (.while (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) body)).1 := by
      rw [hu]; exact Or.inl rfl
    have heq := evaluate_avoidsLocal_flowing k _ hav s0 hfl
    rw [hu] at heq
    exact heq
  obtain ⟨hLlen, _, hmem, _, hord_spec, hint_spec, _, hr1, hrc, _, _, _⟩ := hT
  have hleaves : ∀ z ∈ L, nodeF s0 nd.toNat z 24 = 8 * klen := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    exact (hord_spec i hi).2.1
  have hint_all : ∀ z ∈ I, nodeF s0 nd.toNat z 24 < 8 * klen ∧
      nodeF s0 nd.toNat z 8 ∈ L ++ I ∧ nodeF s0 nd.toNat z 16 ∈ L ++ I ∧
      nodeF s0 nd.toNat z 8 ≠ root ∧ nodeF s0 nd.toNat z 16 ≠ root ∧
      nodeF s0 nd.toNat (nodeF s0 nd.toNat z 8) 0 = z ∧
      nodeF s0 nd.toNat (nodeF s0 nd.toNat z 16) 0 = z := by
    intro z hz
    obtain ⟨a1, a2, a3, _, a5, a6⟩ := hint_spec z hz
    obtain ⟨b1, b2⟩ := hrc z hz
    exact ⟨a1, a2, a3, b1, b2, a5, a6⟩
  have hbound_LI : ∀ z ∈ L ++ I, z < 2 ^ 64 := by
    intro z hz
    have := (hmem z).mp (List.mem_append_left _ hz)
    omega
  let J : PanSemStateFiniteExact 64 F → Prop := fun y =>
    LocFrame s0 y ∧
    y.locals.lookup (ofString "nodes") = some (.val (.word nd)) ∧
    y.locals.lookup (ofString "d") = some (.val (.word dw)) ∧
    ∃ pw nw : BitVec 64,
      y.locals.lookup (ofString "p") = some (.val (.word pw)) ∧
      y.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      nw.toNat ∈ L ++ I ∧
      ((pw.toNat = 0 ∧ nw.toNat = root) ∨
       (pw.toNat ∈ I ∧ nw.toNat ≠ root ∧ pw.toNat = nodeF s0 nd.toNat nw.toNat 0))
  have hJ0 : J s0 := by
    refine ⟨LocFrame.refl s0, hnd_s0, hd_s0, 0#64, rw0, hp_s0, hn_s0, ?_, Or.inl ⟨rfl, hrw0⟩⟩
    rw [hrw0]; exact (hr1 hcnt_pos).1
  have hJu : (J u ∧ CondFalse (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) u) ∨ J u := by
    have := while_inv2 J J _ _ ?_ s0.clock s0 le_rfl hJ0 (by rw [hu])
    · rw [hu] at this; exact this
    · intro x hx hact _
      obtain ⟨hfr, hxnd, hxd, pw, nw, hxp, hxn, hnw_LI, hrel_pn⟩ := hx
      have hmem_eq := hfr.memory
      have hnodeF_eq : ∀ z off, nodeF (decClockHOLFinite x) nd.toNat z off = nodeF s0 nd.toNat z off := by
        intro z off; simp [nodeF, memW, decClockHOLFinite, hmem_eq]
      have hloc_body : locOnlyW body = true := by subst hbody; rfl
      have hav_nd : avoidsLocal (ofString "nodes") body = true := by subst hbody; decide
      have hav_d : avoidsLocal (ofString "d") body = true := by subst hbody; decide
      constructor
      · intro hflow
        have hflow' : FlowR _ := hflow.elim Or.inl (fun h => Or.inr (Or.inl h))
        have hit := set_descent_iter (decClockHOLFinite x) nd dw pw nw L I klen root
          hxnd hxd hxp hxn hd_lt hnw_LI
          (fun z hz => by rw [hnodeF_eq]; exact hleaves z hz)
          (fun z hz => by simp only [hnodeF_eq]; exact hint_all z hz)
          body hbody hflow'
        have hnot_brk : (evaluateHOLFiniteState (decClockHOLFinite x) body).1 ≠ some .break := by
          rcases hflow with h | h <;> rw [h] <;> simp
        obtain ⟨nw', hp', hn', hnw'_LI, hnw_I, hnw'_nr, hpar_eq⟩ := hit.2 hnot_brk
        rw [hnodeF_eq] at hpar_eq
        refine ⟨hfr.trans (locFrameW_dec body hloc_body), ?_, ?_, nw, nw', hp', hn', hnw'_LI,
          Or.inr ⟨hnw_I, hnw'_nr, hpar_eq⟩⟩
        · rw [evaluate_avoidsLocal_flowing _ _ hav_nd _ (flowing_of_flowR hflow')]; exact hxnd
        · rw [evaluate_avoidsLocal_flowing _ _ hav_d _ (flowing_of_flowR hflow')]; exact hxd
      · intro hbrk
        have hflow' : FlowR _ := Or.inr (Or.inr hbrk)
        have hit := set_descent_iter (decClockHOLFinite x) nd dw pw nw L I klen root
          hxnd hxd hxp hxn hd_lt hnw_LI
          (fun z hz => by rw [hnodeF_eq]; exact hleaves z hz)
          (fun z hz => by simp only [hnodeF_eq]; exact hint_all z hz)
          body hbody hflow'
        obtain ⟨hp', hn'⟩ := hit.1 hbrk
        refine ⟨hfr.trans (locFrameW_dec body hloc_body), ?_, ?_, pw, nw, hp', hn', hnw_LI, hrel_pn⟩
        · rw [evaluate_avoidsLocal_flowing _ _ hav_nd _ (flowing_of_flowR hflow')]; exact hxnd
        · rw [evaluate_avoidsLocal_flowing _ _ hav_d _ (flowing_of_flowR hflow')]; exact hxd
  have hJu' : J u := hJu.elim And.left id
  obtain ⟨hfr, _, _, pw, nw, hup, hun, hnw_LI, hrel_pn⟩ := hJu'
  exact ⟨hfr, hloc_keep, pw, nw, hup, hun, hnw_LI, hrel_pn⟩

end InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

/-! ### From SoloHtabSetNodes.lean -/

/-! Semantic specs for `htab_grow`, `htab_new_node`, `htab_new_leaf`, and `htab_new_internal`. -/


namespace InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Arithmetic, Disjointness, and Arena Helpers -/

theorem nodup_len_le_range {l : List Nat} {n : Nat} (hnd : l.Nodup)
    (hr : ∀ x ∈ l, 1 ≤ x ∧ x < n) : l.length ≤ n - 1 := by
  have hsub : l.toFinset ⊆ Finset.Ico 1 n := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    simp only [Finset.mem_Ico]
    exact hr x hx
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Nat.card_Ico] at this
  exact this

/-- Every `HtabBlocks` table has `hdr s t 10 < 10^9`, `hdr s t 1 ≤ 64`, `hdr s t 1 % 8 = 0`, `8 ≤ hdr s t 1`. -/
theorem htabBlocks_bounds {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (hB : HtabBlocks s t) :
    hdr s t 10 < 1000000000 ∧ 8 ≤ hdr s t 1 ∧ hdr s t 1 ≤ 64 ∧ hdr s t 1 % 8 = 0 ∧
    sourceBase ≤ t ∧ t + 88 ≤ heapEnd ∧ t % 8 = 0 := by
  have hhdr_in := (hB.1 (t, 88) (by simp [htabFootprint]))
  have hnd_in := (hB.1 (hdr s t 5, (hdr s t 10 + 1) * 32) (by simp [htabFootprint])).1
  have hk1 := hB.2.2.1
  have hk60 : hdr s t 0 ≤ 60 := hB.2.2.2.1
  have hst := hB.2.2.2.2.1
  have hsb : sourceBase = 2701131776 := rfl
  have hhe : heapEnd = 33806089704 := rfl
  unfold Inside WordsOK at hhdr_in
  unfold Inside at hnd_in
  refine ⟨by omega, by omega, by omega, by omega, hhdr_in.1.1, hhdr_in.1.2, hhdr_in.2.1⟩

/-- Every `ArenaReady` state has a `BitVec 64` word bound to `"heap_ptr"` in `globals` with `toNat = globN s "heap_ptr"`. -/
theorem arenaReady_heap_word {F : Type} {s : PanSemStateFiniteExact 64 F} (hA : ArenaReady s) :
    ∃ hp : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) ∧
      hp.toNat = globN s "heap_ptr" ∧
      sourceBase ≤ hp.toNat ∧ hp.toNat ≤ cMax.toNat ∧ hp.toNat % 8 = 0 := by
  have hsb : sourceBase = 2701131776 := rfl
  have hhl : heapLimit = cMax.toNat := rfl
  have hok := hA.2
  have hge : sourceBase ≤ globN s "heap_ptr" := hok.1
  cases hg : s.globals.lookup (ofString "heap_ptr") with
  | none => have hz : globN s "heap_ptr" = 0 := by unfold globN; rw [hg]
            omega
  | some val =>
    cases val with
    | val wl =>
      cases wl with
      | word hp =>
        have hgn : globN s "heap_ptr" = hp.toNat := by unfold globN; rw [hg]
        refine ⟨hp, rfl, hgn.symm, by omega, ?_, ?_⟩
        · have := hok.2.1; rw [hgn, hhl] at this; exact this
        · have := hok.2.2.2.2.2.1; rw [hgn] at this; exact this
    | rStruct _ => have hz : globN s "heap_ptr" = 0 := by unfold globN; rw [hg]
                   omega
    | nStruct _ _ => have hz : globN s "heap_ptr" = 0 := by unfold globN; rw [hg]
                     omega

/-- Updating `"heap_ptr"` to an aligned `q` with `hp ≤ q ≤ cMax` preserves `ArenaReady` and advances `globN _ "heap_ptr"` to `q.toNat`. -/
theorem arenaReady_upd_heap {F : Type} {s : PanSemStateFiniteExact 64 F}
    {q : BitVec 64} (hA : ArenaReady s)
    (hq_lo : globN s "heap_ptr" ≤ q.toNat) (hq_hi : q.toNat ≤ cMax.toNat) (hq_al : q.toNat % 8 = 0) :
    let s' := { s with globals := s.globals.update (ofString "heap_ptr", .val (.word q)) }
    ArenaReady s' ∧ globN s' "heap_ptr" = q.toNat ∧
    (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString → s.globals.lookup k = s'.globals.lookup k) := by
  intro s'
  have hG : GuestInv s' := guestInv_congr (s := s) rfl rfl rfl rfl hA.1
  have hhp : globN s' "heap_ptr" = q.toNat := by
    simp [s', globN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hfm : globN s' "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    simp [s', globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hsp : globN s' "scratch_ptr" = globN s "scratch_ptr" := by
    simp [s', globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have hhl : heapLimit = cMax.toNat := rfl
  obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, h9⟩ := hA.2
  refine ⟨⟨hG, ?_⟩, hhp, ?_⟩
  · unfold ArenaOK
    rw [hhp, hfm, hsp, hhl]
    exact ⟨le_trans h1 hq_lo, hq_hi, h3, h4, h5, hq_al, h7, h8,
      globalsWord_update (ofString "heap_ptr") q rfl h9⟩
  · intro k hk
    have hne : ofString "heap_ptr" ≠ k := by
      rintro rfl; exact hk (by simp)
    simp [s', HolFiniteMapExact.lookup_update, FUPDATE, hne]

/-- An `Allocated` interval with positive length does not overlap `[lo, hi)` when `globN s "heap_ptr" ≤ lo`, `lo < hi`, and `hi ≤ heapLimit`. -/
theorem disj_fresh_of_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {i : Ivl} {lo hi : Nat} (hA : ArenaReady s) (hal : Allocated s i)
    (hlo : globN s "heap_ptr" ≤ lo) (hhi : hi ≤ heapLimit) :
    i.2 = 0 ∨ hi ≤ lo ∨ lo + (hi - lo) ≤ i.1 ∨ i.1 + i.2 ≤ lo := by
  have hok := hA.2
  have hss : heapLimit = scratchStart := rfl
  by_cases hlen : hi ≤ lo
  · exact Or.inr (Or.inl hlen)
  · rcases hal with ⟨_, hi2⟩ | ⟨hi1, _⟩
    · exact Or.inr (Or.inr (Or.inr (by omega)))
    · have : scratchStart ≤ i.1 := by have := hok.2.2.1; have := hok.2.2.2.1; omega
      exact Or.inr (Or.inr (Or.inl (by omega)))

/-- Compatibility wrapper returning `Disj (lo, hi - lo) i`. -/
theorem disj_fresh_ivl {F : Type} {s : PanSemStateFiniteExact 64 F}
    {i : Ivl} {lo hi : Nat} (hA : ArenaReady s) (hal : Allocated s i)
    (hlo : globN s "heap_ptr" ≤ lo) (hhi : hi ≤ heapLimit) :
    Disj (lo, hi - lo) i := by
  rcases disj_fresh_of_allocated hA hal hlo hhi with hz | hle | h1 | h2
  · exact Or.inr (Or.inl hz)
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h2))

/-- If `FrameOutside s1 s2 [iv] (0, 0)` holds and `iv.2 = 0 ∨ a + 8 ≤ iv.1 ∨ iv.1 + iv.2 ≤ a` where `a < 2^64`,
then `memW s2 a = memW s1 a`. -/
theorem memW_eq_of_frame_disj {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    {iv : Ivl} {a : Nat}
    (hfr : FrameOutside s1 s2 [iv] (0, 0))
    (ha_lt : a < 2 ^ 64)
    (hsep : a + 8 ≤ iv.1 ∨ iv.1 + iv.2 ≤ a) :
    memW s2 a = memW s1 a := by
  have hcell : s2.memory (BitVec.ofNat 64 a) = s1.memory (BitVec.ofNat 64 a) := by
    apply hfr (BitVec.ofNat 64 a)
    · intro j hj hhit
      rw [List.mem_singleton.mp hj] at hhit
      have hba : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
      have h1 : iv.1 < a + 8 := by have := hhit.1; omega
      have h2 : a < iv.1 + iv.2 := by have := hhit.2; omega
      rcases hsep with hle | hle
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 hle)
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 hle)
    · intro hhit
      have h2 : (BitVec.ofNat 64 a).toNat < (0, 0).1 + (0, 0).2 := hhit.2
      dsimp only at h2
      omega
  unfold memW
  rw [hcell]

/-- Under `MemCopyRel s1 s2 dst src len len`, when `dst % 8 = 0`, `src % 8 = 0`, `off + 8 ≤ len`, `off % 8 = 0`,
`memW s2 (dst.toNat + off) = memW s1 (src.toNat + off)`. -/
theorem memW_copied_of_memCopyRel {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    {dst src : BitVec 64} {len off : Nat}
    (hrel : MemCopyRel s1 s2 dst src len len)
    (hd8 : dst.toNat % 8 = 0) (hs8 : src.toNat % 8 = 0) (hoff8 : off % 8 = 0)
    (hoff_le : off + 8 ≤ len)
    (hd_nw : dst.toNat + len < 2 ^ 64) (hs_nw : src.toNat + len < 2 ^ 64) :
    memW s2 (dst.toNat + off) = memW s1 (src.toNat + off) := by
  have hbe : s2.be = s1.be := hrel.2.2.2.2.1
  apply (memW_eq_iff_memB hbe (by omega) (by omega) (by omega) (by omega)).mpr
  intro r hr
  have hc := hrel.2.2.2.2.2.2.2.1 (off + r) (by omega)
  have hd_eq : (dst + BitVec.ofNat 64 (off + r)).toNat = (dst.toNat + off) + r := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hs_eq : (src + BitVec.ofNat 64 (off + r)).toNat = (src.toNat + off) + r := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [← hd_eq, ← hs_eq]
  exact hc

/-- `Ret.decCall_alloc`: specialized `decCall1` for `alloc(arg)` from an `ArenaReady` state. -/
theorem Ret.decCall_alloc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x : MlS} {arg : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hA : ArenaReady s)
    (nv : BitVec 64) (harg : evalAt s arg = some (.val (.word nv)))
    (hk : ∀ (hp q : BitVec 64) (s' : PanSemStateFiniteExact 64 F),
      hp.toNat = globN s "heap_ptr" →
      hp.toNat % 8 = 0 →
      hp.toNat + nv.toNat ≤ q.toNat →
      q.toNat ≤ cMax.toNat →
      q.toNat % 8 = 0 →
      ArenaReady s' →
      globN s' "heap_ptr" = q.toNat →
      s'.memory = s.memory →
      s'.be = s.be →
      (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString → s.globals.lookup k = s'.globals.lookup k) →
      s'.locals = s.locals →
      Ret (setVarHOLFinite x (.val (.word hp)) s') cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one (ofString "alloc") [arg] cont) Φ := by
  obtain ⟨hp, hhp_g, hhp_nat, _, hhp_hi, hhp_al⟩ := arenaReady_heap_word hA
  refine Ret.decCall1 hA.1.code lookup_alloc_fn nv harg ?_
  intro w post hrun
  let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))
  have hrun_spec := alloc_body_run entry hp nv hA.1.code hhp_hi hhp_g
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (.val (.word w)) (by rw [hrun])
  rw [hrun] at hrun_spec
  obtain ⟨hw_eq, hq_lo, hq_hi, hq_al, hpost_eq⟩ := hrun_spec
  dsimp only at hpost_eq
  injection hw_eq with hw1; injection hw1 with hw2
  have hw_eq_hp : w = hp := hw2
  subst hw_eq_hp
  let q := (w + (nv + 7)) &&& ((0 : BitVec 64) - 8)
  have hq_lo' : w.toNat + nv.toNat ≤ q.toNat := hq_lo
  have hhp_le_q : globN s "heap_ptr" ≤ q.toNat := by omega
  obtain ⟨hA', hgn', hg_keep⟩ := arenaReady_upd_heap hA hhp_le_q hq_hi hq_al
  let s_res := { post with locals := s.locals }
  have hs_res_eq : s_res = { s with globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := post.clock } := by
    dsimp only [s_res]
    rw [hpost_eq]
    cases s; rfl
  have hA_res : ArenaReady s_res := by
    rw [hs_res_eq]
    exact (arenaReady_locals { s with globals := s.globals.update (ofString "heap_ptr", .val (.word q)) } s.locals post.clock).mpr hA'
  exact hk w q s_res hhp_nat hhp_al hq_lo hq_hi hq_al hA_res
    (by rw [hs_res_eq]; exact hgn')
    (by rw [hs_res_eq])
    (by rw [hs_res_eq])
    (fun k hk' => by rw [hs_res_eq]; exact hg_keep k hk')
    rfl

/-- `Ret.seq_memcpy_disj`: `call memcpy(ed, es, en); cont` when `(dst, n)` and `(src, n)` are disjoint. -/
theorem Ret.seq_memcpy_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ed es en : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hA : ArenaReady s)
    (dst src n : BitVec 64)
    (hd_nw : dst.toNat + n.toNat < 2 ^ 64)
    (hs_nw : src.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hdisj : Disj (dst.toNat, n.toNat) (src.toNat, n.toNat))
    (hed : evalAt s ed = some (.val (.word dst)))
    (hes : evalAt s es = some (.val (.word src)))
    (hen : evalAt s en = some (.val (.word n)))
    (hk : ∀ s' : PanSemStateFiniteExact 64 F,
      ArenaReady s' →
      MemCopyRel s s' dst src n.toNat n.toNat →
      s'.locals = s.locals →
      Ret s' cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "memcpy") [ed, es, en]) cont) Φ := by
  refine Ret.seq_call3 hA.1.code
    (by decide) (by decide) (by decide) lookup_memcpy_fn dst src n hed hes hen ?_
  intro w post hrun
  let entry := callEntryStateHOLFinite s
    (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst))).update
      (ofString "src", .val (.word src))).update (ofString "n", .val (.word n)))
  have hspec := memcpy_body_spec entry dst src n hd_nw hs_nw hn_small hdisj
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "src" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (.val (.word w)) (by rw [hrun])
  rw [hrun] at hspec
  obtain ⟨_, hrel⟩ := hspec
  let s_res := { post with locals := s.locals }
  have hrel_s : MemCopyRel s s_res dst src n.toNat n.toNat := by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hrel
    exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩
  have hG_res : GuestInv s_res :=
    guestInv_congr hrel_s.1 hrel_s.2.1 hrel_s.2.2.1 hrel_s.2.2.2.1 hA.1
  have hA_res : ArenaReady s_res := ⟨hG_res, arenaOK_congr hrel_s.2.2.2.2.2.1 hA.2⟩
  exact hk s_res hA_res hrel_s rfl

/-- `Ret.seq_memcpy_frame`: `call memcpy(ed, es, en); cont` without `Disj` (frame-only). -/
theorem Ret.seq_memcpy_frame {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ed es en : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hA : ArenaReady s)
    (dst src n : BitVec 64)
    (hd_nw : dst.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hed : evalAt s ed = some (.val (.word dst)))
    (hes : evalAt s es = some (.val (.word src)))
    (hen : evalAt s en = some (.val (.word n)))
    (hk : ∀ s' : PanSemStateFiniteExact 64 F,
      ArenaReady s' →
      MemCopyFrame s s' dst n.toNat →
      s'.locals = s.locals →
      Ret s' cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "memcpy") [ed, es, en]) cont) Φ := by
  refine Ret.seq_call3 hA.1.code
    (by decide) (by decide) (by decide) lookup_memcpy_fn dst src n hed hes hen ?_
  intro w post hrun
  let entry := callEntryStateHOLFinite s
    (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst))).update
      (ofString "src", .val (.word src))).update (ofString "n", .val (.word n)))
  have hspec := memcpy_body_frame entry dst n hd_nw hn_small
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (.val (.word w)) (by rw [hrun])
  rw [hrun] at hspec
  obtain ⟨_, hrel⟩ := hspec
  let s_res := { post with locals := s.locals }
  have hrel_s : MemCopyFrame s s_res dst n.toNat := by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hrel
    exact ⟨c1, c2, c3, c4, c5, c6, c7⟩
  have hG_res : GuestInv s_res :=
    guestInv_congr hrel_s.1 hrel_s.2.1 hrel_s.2.2.1 hrel_s.2.2.2.1 hA.1
  have hA_res : ArenaReady s_res := ⟨hG_res, arenaOK_congr hrel_s.2.2.2.2.2.1 hA.2⟩
  exact hk s_res hA_res hrel_s rfl

/-! ## 2. `htab_grow` Postcondition -/

theorem htab_grow_body_spec {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (tw : BitVec 64)
    (ht : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hA0 : ArenaReady s0)
    (hB0 : HtabBlocks s0 tw.toNat)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_grow)
      (fun v post =>
        let t := tw.toNat
        let fresh : Ivl := (globN s0 "heap_ptr", globN post "heap_ptr" - globN s0 "heap_ptr")
        v = .val (.word 0#64) ∧
        ArenaReady post ∧
        HtabBlocks post t ∧
        hdr post t 0 = hdr s0 t 0 ∧
        hdr post t 1 = hdr s0 t 1 ∧
        hdr post t 3 = hdr s0 t 3 ∧
        hdr post t 7 = hdr s0 t 7 ∧
        hdr post t 8 = hdr s0 t 8 ∧
        hdr post t 9 = hdr s0 t 9 ∧
        hdr post t 10 = 2 * hdr s0 t 10 ∧
        (∀ n, n < hdr s0 t 10 + 1 → ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
          nodeF post (hdr post t 5) n off = nodeF s0 (hdr s0 t 5) n off) ∧
        (∀ i, i < hdr s0 t 10 + 1 →
          memW post (hdr post t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i)) ∧
        globN s0 "heap_ptr" ≤ globN post "heap_ptr" ∧
        (∀ i ∈ htabFootprint post t, Allocated post i ∧
          ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
        FrameOutside s0 post [(t, 88)] fresh ∧
        (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
          s0.globals.lookup k = post.globals.lookup k)) := by
  set t := tw.toNat
  obtain ⟨hncap_lt, hst_ge8, hst_le64, hst_al, ht_lo, ht_hi, ht_al⟩ := htabBlocks_bounds hB0
  have hnc2 : 2 ≤ hdr s0 t 10 := hB0.2.2.2.2.2.1
  have hnx1 : 1 ≤ hdr s0 t 8 := hB0.2.2.2.2.2.2.1
  have hnx_le : hdr s0 t 8 ≤ hdr s0 t 10 + 1 := hB0.2.2.2.2.2.2.2
  have hhe : heapEnd = 33806089704 := rfl
  have hcMax_val : cMax.toNat = 2952790016 := rfl
  have hhl_val : heapLimit = 2952790016 := rfl
  have hkeys_in0 := (hB0.1 (hdr s0 t 4, (hdr s0 t 10 + 1) * hdr s0 t 1) (by simp [htabFootprint]))
  have hnodes_in0 := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint]))
  have horder_in0 := (hB0.1 (hdr s0 t 6, (hdr s0 t 10 + 1) * 8) (by simp [htabFootprint]))
  have hhdr_al0 : Allocated s0 (t, 88) := hal0 (t, 88) (by simp [htabFootprint])
  have hkeys_al0 : Allocated s0 (hdr s0 t 4, (hdr s0 t 10 + 1) * hdr s0 t 1) := hal0 _ (by simp [htabFootprint])
  have hnodes_al0 : Allocated s0 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) := hal0 _ (by simp [htabFootprint])
  have horder_al0 : Allocated s0 (hdr s0 t 6, (hdr s0 t 10 + 1) * 8) := hal0 _ (by simp [htabFootprint])
  obtain ⟨hdom_t0, hm_t0⟩ := word_of_hdr s0 tw 0 (by omega) hB0
  obtain ⟨hdom_t1, hm_t1⟩ := word_of_hdr s0 tw 1 (by omega) hB0
  obtain ⟨hdom_t2, hm_t2⟩ := word_of_hdr s0 tw 2 (by omega) hB0
  obtain ⟨hdom_t3, hm_t3⟩ := word_of_hdr s0 tw 3 (by omega) hB0
  obtain ⟨hdom_t4, hm_t4⟩ := word_of_hdr s0 tw 4 (by omega) hB0
  obtain ⟨hdom_t5, hm_t5⟩ := word_of_hdr s0 tw 5 (by omega) hB0
  obtain ⟨hdom_t6, hm_t6⟩ := word_of_hdr s0 tw 6 (by omega) hB0
  obtain ⟨hdom_t7, hm_t7⟩ := word_of_hdr s0 tw 7 (by omega) hB0
  obtain ⟨hdom_t8, hm_t8⟩ := word_of_hdr s0 tw 8 (by omega) hB0
  obtain ⟨hdom_t9, hm_t9⟩ := word_of_hdr s0 tw 9 (by omega) hB0
  obtain ⟨hdom_t10, hm_t10⟩ := word_of_hdr s0 tw 10 (by omega) hB0
  set nodecap := hdr s0 t 10
  set ncap := 2 * nodecap
  set stride := hdr s0 t 1
  set old_keys := hdr s0 t 4
  set old_nodes := hdr s0 t 5
  set old_order := hdr s0 t 6
  have hw_nc0 : (BitVec.ofNat 64 nodecap).toNat = nodecap := by rw [BitVec.toNat_ofNat]; omega
  have hw_st : (BitVec.ofNat 64 stride).toNat = stride := by rw [BitVec.toNat_ofNat]; omega
  have hw_nc : (BitVec.ofNat 64 nodecap * 2#64).toNat = ncap := by
    rw [BitVec.toNat_mul, hw_nc0, show (2#64).toNat = 2 from rfl]; omega
  have hw_nc_eq : BitVec.ofNat 64 nodecap * 2#64 = BitVec.ofNat 64 ncap := by
    apply BitVec.eq_of_toNat_eq; rw [hw_nc, BitVec.toNat_ofNat]; omega
  htab_unfold Guest.Software.guestFn_htab_grow
  -- 1. dec nodecap := load(t + 80)
  apply Ret.dec; intro v_nc0 hv_nc0
  obtain ⟨_, rfl⟩ := ev_field_load s0 (ofString "t") tw 80 ht v_nc0 hv_nc0
  have hm80 : s0.memory (tw + 80) = .word (BitVec.ofNat 64 nodecap) := hm_t10
  rw [hm80]
  -- 2. dec ncap := nodecap * 2
  apply Ret.dec; intro v_nc hv_nc
  have hv_nc_eq : v_nc = .val (.word (BitVec.ofNat 64 ncap)) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, panOpHOL, valueIsWord, valueWord, hw_nc_eq] at hv_nc
    exact hv_nc.symm
  subst hv_nc_eq
  -- 3. dec stride := load(t + 8)
  apply Ret.dec; intro v_st hv_st
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 8
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "ncap" ≠ ofString "t" by decide, show ofString "nodecap" ≠ ofString "t" by decide]) v_st hv_st
  have hm8 : s0.memory (tw + 8) = .word (BitVec.ofNat 64 stride) := hm_t1
  simp only [setVarHOLFinite] at *
  rw [hm8]
  let L0_3 : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((s0.locals.update (ofString "nodecap", .val (.word (BitVec.ofNat 64 nodecap)))).update
      (ofString "ncap", .val (.word (BitVec.ofNat 64 ncap)))).update
      (ofString "stride", .val (.word (BitVec.ofNat 64 stride)))
  let s0_3 : PanSemStateFiniteExact 64 F := { s0 with locals := L0_3 }
  have hb_mul1 : (ncap + 1) * stride < 2 ^ 64 := by
    have : 2 * nodecap + 1 ≤ 2000000000 := by omega
    have : (2 * nodecap + 1) * stride ≤ 2000000000 * 64 := Nat.mul_le_mul (by omega) hst_le64
    dsimp only [ncap]; omega
  have hb_mul2 : (nodecap + 1) * stride < 2 ^ 64 := by
    have : (nodecap + 1) * stride ≤ 1000000000 * 64 := Nat.mul_le_mul (by omega) hst_le64
    omega
  have hb_mul3 : (ncap + 1) * 32 < 2 ^ 64 := by dsimp only [ncap]; omega
  have hb_mul4 : (nodecap + 1) * 32 < 2 ^ 64 := by omega
  have hb_mul5 : (ncap + 1) * 8 < 2 ^ 64 := by dsimp only [ncap]; omega
  have hb_mul6 : (nodecap + 1) * 8 < 2 ^ 64 := by omega
  -- 4. decCall keys := alloc((ncap + 1) * stride)
  have harg_k : evalAt s0_3 (.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .var .local (ofString "stride")]) =
      some (.val (.word (BitVec.ofNat 64 ((ncap + 1) * stride)))) := by
    have h1 : s0_3.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 ncap))) := by
      simp [s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "stride" ≠ ofString "ncap" by decide]
    have h2 : s0_3.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 stride))) := by
      simp [s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE]
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, h1, h2,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    have hnc_lt : ncap < 2 ^ 64 := by dsimp only [ncap]; omega
    have hnc1_lt : ncap + 1 < 2 ^ 64 := by dsimp only [ncap]; omega
    have hst_lt : stride < 2 ^ 64 := by omega
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, show (1#64).toNat = 1 from rfl, hz0, Nat.add_zero]
    have h1m : 1 % 2 ^ 64 = 1 := rfl
    rw [h1m, Nat.mod_eq_of_lt hnc_lt, Nat.mod_eq_of_lt hnc1_lt, Nat.mod_eq_of_lt hst_lt]
  refine Ret.decCall_alloc (s := s0_3) ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩
    (BitVec.ofNat 64 ((ncap + 1) * stride)) harg_k ?_
  intro kptr q1 s1 hkptr_nat hkptr_al hq1_lo hq1_hi hq1_al hA1 hgn1 hmem1 hbe1 hg1 hloc1
  have hkptr_s0 : kptr.toNat = globN s0 "heap_ptr" := hkptr_nat
  have hsz_k : (BitVec.ofNat 64 ((ncap + 1) * stride)).toNat = (ncap + 1) * stride := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul1]
  rw [hsz_k] at hq1_lo
  -- 5. call memcpy(keys, load(t + 32), (nodecap + 1) * stride)
  set s1k := setVarHOLFinite (ofString "keys") (.val (.word kptr)) s1
  have hA1k : ArenaReady s1k := ⟨guestInv_congr (s := s1) rfl rfl rfl rfl hA1.1, hA1.2⟩
  have hsz_ok : (BitVec.ofNat 64 ((nodecap + 1) * stride)).toNat = (nodecap + 1) * stride := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul2]
  have he_kd : evalAt s1k (.var .local (ofString "keys")) = some (.val (.word kptr)) := by
    simp [s1k, evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have ht_s1k : s1k.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s1k, setVarHOLFinite, hloc1, s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "keys" ≠ ofString "t" by decide, show ofString "stride" ≠ ofString "t" by decide,
      show ofString "ncap" ≠ ofString "t" by decide, show ofString "nodecap" ≠ ofString "t" by decide]
  have hnc0_s1k : s1k.locals.lookup (ofString "nodecap") = some (.val (.word (BitVec.ofNat 64 nodecap))) := by
    simp [s1k, setVarHOLFinite, hloc1, s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "nodecap" by decide, show ofString "stride" ≠ ofString "nodecap" by decide,
      show ofString "ncap" ≠ ofString "nodecap" by decide]
  have hnc_s1k : s1k.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 ncap))) := by
    simp [s1k, setVarHOLFinite, hloc1, s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "ncap" by decide, show ofString "stride" ≠ ofString "ncap" by decide]
  have hst_s1k : s1k.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 stride))) := by
    simp [s1k, setVarHOLFinite, hloc1, s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "stride" by decide]
  have he_ks : evalAt s1k (.load .one (.op .add [.var .local (ofString "t"), .const 32#64])) =
      some (.val (.word (BitVec.ofNat 64 old_keys))) := by
    have hdom32 : s1k.memaddrs (tw + 32#64) := by
      have : s1k.memaddrs = s0.memaddrs := hA1.1.memaddrs.trans hA0.1.memaddrs.symm
      rw [this]; exact hdom_t4
    have hm32 : s1k.memory (tw + 32#64) = .word (BitVec.ofNat 64 old_keys) := by
      change s1.memory (tw + 32#64) = _; rw [hmem1]; exact hm_t4
    simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s1k,
      valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hdom32, hm32]
  have he_kn : evalAt s1k (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .var .local (ofString "stride")]) =
      some (.val (.word (BitVec.ofNat 64 ((nodecap + 1) * stride)))) := by
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnc0_s1k, hst_s1k,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    have hnc0_lt : nodecap < 2 ^ 64 := by omega
    have hnc01_lt : nodecap + 1 < 2 ^ 64 := by omega
    have hst_lt : stride < 2 ^ 64 := by omega
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, show (1#64).toNat = 1 from rfl, hz0, Nat.add_zero]
    have h1m : 1 % 2 ^ 64 = 1 := rfl
    rw [h1m, Nat.mod_eq_of_lt hnc0_lt, Nat.mod_eq_of_lt hnc01_lt, Nat.mod_eq_of_lt hst_lt]
  have hle_ok_k : (nodecap + 1) * stride ≤ (ncap + 1) * stride := Nat.mul_le_mul_right stride (by dsimp only [ncap]; omega)
  refine Ret.seq_memcpy_frame hA1k kptr (BitVec.ofNat 64 old_keys) (BitVec.ofNat 64 ((nodecap + 1) * stride))
    (by rw [hsz_ok]; omega)
    (by rw [hsz_ok]; have : (nodecap + 1) * stride ≤ 1000000000 * 64 := Nat.mul_le_mul (by omega) hst_le64; omega)
    he_kd he_ks he_kn ?_
  intro s2 hA2 hmcf_k hloc2
  -- 6. store(t + 32, keys)
  have ht_s2 : s2.locals.lookup (ofString "t") = some (.val (.word tw)) := by rw [hloc2]; exact ht_s1k
  have hk_s2 : s2.locals.lookup (ofString "keys") = some (.val (.word kptr)) := by
    rw [hloc2]; simp [s1k, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine Ret.seq_storeW (tw + 32#64) kptr
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s2, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hk_s2]) ?_
  intro _
  set s3 := { s2 with memory := updW s2.memory (tw + 32#64) kptr }
  have hA3 : ArenaReady s3 := ⟨guestInv_congr (s := s2) rfl rfl rfl rfl hA2.1, hA2.2⟩
  -- 7. decCall nodes := alloc((ncap + 1) * 32)
  have harg_nd : evalAt s3 (.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .const 32#64]) =
      some (.val (.word (BitVec.ofNat 64 ((ncap + 1) * 32)))) := by
    have hnc_s3 : s3.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 ncap))) := by
      change s2.locals.lookup _ = _; rw [hloc2]; exact hnc_s1k
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnc_s3,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    have hnc_lt : ncap < 2 ^ 64 := by dsimp only [ncap]; omega
    have hnc1_lt : ncap + 1 < 2 ^ 64 := by dsimp only [ncap]; omega
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1#64).toNat = 1 from rfl, show (32#64).toNat = 32 from rfl, hz0, Nat.add_zero]
    have h1m : 1 % 2 ^ 64 = 1 := rfl
    rw [h1m, Nat.mod_eq_of_lt hnc_lt, Nat.mod_eq_of_lt hnc1_lt]
  refine Ret.decCall_alloc hA3 (BitVec.ofNat 64 ((ncap + 1) * 32)) harg_nd ?_
  intro nptr q2 s4 hnptr_nat hnptr_al hq2_lo hq2_hi hq2_al hA4 hgn4 hmem4 hbe4 hg4 hloc4
  have hgn3 : globN s3 "heap_ptr" = q1.toNat := by
    change globN s2 "heap_ptr" = _
    have hg2 : s2.globals = s1k.globals := hmcf_k.2.2.2.2.2.1
    unfold globN at hgn1 ⊢; rw [hg2]; exact hgn1
  rw [hgn3] at hnptr_nat
  have hsz_nd : (BitVec.ofNat 64 ((ncap + 1) * 32)).toNat = (ncap + 1) * 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul3]
  rw [hsz_nd] at hq2_lo
  -- Frame of s3 relative to s0: only `(t, 88)` (at `t+32`) and `(kptr, (nodecap+1)*stride)` changed!
  have hfr_s0_s3 : FrameOutside s0 s3 [(t, 88)] (globN s0 "heap_ptr", q1.toNat - globN s0 "heap_ptr") := by
    have hfr_s0_s2 : FrameOutside s0 s2 [(t, 88)] (globN s0 "heap_ptr", q1.toNat - globN s0 "heap_ptr") := by
      intro x hxk hxf
      have hm2_1 : s2.memory x = s1k.memory x := by
        apply hmcf_k.2.2.2.2.2.2 x
        · intro i hi hhit
          rw [List.mem_singleton.mp hi, hsz_ok] at hhit
          apply hxf
          exact cellHits_of_inside hhit ⟨by omega, by omega⟩
        · intro ⟨_, h2⟩; omega
      rw [hm2_1]; exact congrFun hmem1 x
    have htw32 : (tw + 32#64).toNat = t + 32 := by
      rw [BitVec.toNat_add, show (32#64).toNat = 32 from rfl]; omega
    exact frameOutside_trans_same hfr_s0_s2
      (frameOutside_updW s2 (tw + 32#64) kptr [(t, 88)] _
        (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
  -- Check that `load(t + 40)` in `s4` still reads `old_nodes`, and `old_nodes` words are untouched!
  set s4n := setVarHOLFinite (ofString "nodes") (.val (.word nptr)) s4
  have hA4n : ArenaReady s4n := ⟨guestInv_congr (s := s4) rfl rfl rfl rfl hA4.1, hA4.2⟩
  have hsz_ond : (BitVec.ofNat 64 ((nodecap + 1) * 32)).toNat = (nodecap + 1) * 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul4]
  have hw_ond : (BitVec.ofNat 64 old_nodes).toNat = old_nodes := by
    rw [BitVec.toNat_ofNat]; unfold Inside at hnodes_in0; omega
  have hdisj_nd : Disj (nptr.toNat, (nodecap + 1) * 32) (old_nodes, (nodecap + 1) * 32) := by
    have hd := disj_fresh_ivl hA0 hnodes_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
    dsimp only [ncap] at hq2_lo
    unfold Disj at hd ⊢; omega
  have he_nd_d : evalAt s4n (.var .local (ofString "nodes")) = some (.val (.word nptr)) := by
    simp [s4n, evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have he_nd_s : evalAt s4n (.load .one (.op .add [.var .local (ofString "t"), .const 40#64])) =
      some (.val (.word (BitVec.ofNat 64 old_nodes))) := by
    have ht_s4n : s4n.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [s4n, setVarHOLFinite, hloc4, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nodes" ≠ ofString "t" by decide]
      exact ht_s2
    have hdom40 : s4n.memaddrs (tw + 40#64) := by
      have : s4n.memaddrs = s0.memaddrs := hA4.1.memaddrs.trans hA0.1.memaddrs.symm
      rw [this]; exact hdom_t5
    have hne40_32 : tw + 40#64 ≠ tw + 32#64 := by
      intro he; have := congrArg BitVec.toNat he
      rw [BitVec.toNat_add, BitVec.toNat_add, show (40#64).toNat = 40 from rfl, show (32#64).toNat = 32 from rfl] at this
      omega
    have hm40 : s4n.memory (tw + 40#64) = .word (BitVec.ofNat 64 old_nodes) := by
      change s4.memory (tw + 40#64) = _; rw [hmem4]
      simp only [s3, updW, hne40_32, ↓reduceIte]
      have hm2_1 : s2.memory (tw + 40#64) = s1k.memory (tw + 40#64) := by
        apply hmcf_k.2.2.2.2.2.2 (tw + 40#64)
        · intro i hi hhit
          rw [List.mem_singleton.mp hi, hsz_ok] at hhit
          have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := kptr.toNat) (hi := q1.toNat) (by omega) (by omega)
          have htw40 : (tw + 40#64).toNat = t + 40 := by rw [BitVec.toNat_add, show (40#64).toNat = 40 from rfl]; omega
          rw [htw40] at hhit
          obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
        · intro ⟨_, h2⟩; omega
      rw [hm2_1]; change s1.memory _ = _; rw [hmem1]; exact hm_t5
    simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s4n,
      valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hdom40, hm40]
  have he_nd_n : evalAt s4n (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .const 32#64]) =
      some (.val (.word (BitVec.ofNat 64 ((nodecap + 1) * 32)))) := by
    have hnc_l : s4n.locals.lookup (ofString "nodecap") = some (.val (.word (BitVec.ofNat 64 nodecap))) := by
      simp only [s4n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nodes" ≠ ofString "nodecap" by decide, ↓reduceIte]
      rw [hloc4]; change s2.locals.lookup _ = _; rw [hloc2]; exact hnc0_s1k
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnc_l,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1#64).toNat = 1 from rfl, show (32#64).toNat = 32 from rfl, hz0, Nat.add_zero]
    omega
  -- 8. call memcpy(nodes, load(t + 40), (nodecap + 1) * 32)
  refine Ret.seq_memcpy_disj hA4n nptr (BitVec.ofNat 64 old_nodes) (BitVec.ofNat 64 ((nodecap + 1) * 32))
    (by rw [hsz_ond]; dsimp only [ncap] at hq2_lo; omega)
    (by rw [hw_ond, hsz_ond]; unfold Inside at hnodes_in0; omega)
    (by rw [hsz_ond]; omega)
    (by rw [hw_ond, hsz_ond]; exact hdisj_nd)
    he_nd_d he_nd_s he_nd_n ?_
  intro s5 hA5 hrel_nd hloc5
  -- 9. store(t + 40, nodes)
  have ht_s5 : s5.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    rw [hloc5]; simp [s4n, setVarHOLFinite, hloc4, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "nodes" ≠ ofString "t" by decide]; exact ht_s2
  have hnd_s5 : s5.locals.lookup (ofString "nodes") = some (.val (.word nptr)) := by
    rw [hloc5]; simp [s4n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine Ret.seq_storeW (tw + 40#64) nptr
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s5, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hnd_s5]) ?_
  intro _
  set s6 := { s5 with memory := updW s5.memory (tw + 40#64) nptr }
  have hA6 : ArenaReady s6 := ⟨guestInv_congr (s := s5) rfl rfl rfl rfl hA5.1, hA5.2⟩
  -- 10. decCall order := alloc((ncap + 1) * 8)
  have harg_ord : evalAt s6 (.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .const 8#64]) =
      some (.val (.word (BitVec.ofNat 64 ((ncap + 1) * 8)))) := by
    have hnc_s6 : s6.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 ncap))) := by
      change s5.locals.lookup _ = _; rw [hloc5]
      simp only [s4n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nodes" ≠ ofString "ncap" by decide, ↓reduceIte]
      rw [hloc4]; change s2.locals.lookup _ = _; rw [hloc2]; exact hnc_s1k
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnc_s6,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    have hnc_lt : ncap < 2 ^ 64 := by dsimp only [ncap]; omega
    have hnc1_lt : ncap + 1 < 2 ^ 64 := by dsimp only [ncap]; omega
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1#64).toNat = 1 from rfl, show (8#64).toNat = 8 from rfl, hz0, Nat.add_zero]
    have h1m : 1 % 2 ^ 64 = 1 := rfl
    rw [h1m, Nat.mod_eq_of_lt hnc_lt, Nat.mod_eq_of_lt hnc1_lt]
  refine Ret.decCall_alloc hA6 (BitVec.ofNat 64 ((ncap + 1) * 8)) harg_ord ?_
  intro optr q3 s7 hoptr_nat hoptr_al hq3_lo hq3_hi hq3_al hA7 hgn7 hmem7 hbe7 hg7 hloc7
  have hgn6 : globN s6 "heap_ptr" = q2.toNat := by
    change globN s5 "heap_ptr" = _
    have hg5 : s5.globals = s4n.globals := hrel_nd.2.2.2.2.2.1
    unfold globN at hgn4 ⊢; rw [hg5]; exact hgn4
  rw [hgn6] at hoptr_nat
  have hsz_ord : (BitVec.ofNat 64 ((ncap + 1) * 8)).toNat = (ncap + 1) * 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul5]
  rw [hsz_ord] at hq3_lo
  have hfr_s0_s6 : FrameOutside s0 s6 [(t, 88)] (globN s0 "heap_ptr", q2.toNat - globN s0 "heap_ptr") := by
    have hfr_s0_s5 : FrameOutside s0 s5 [(t, 88)] (globN s0 "heap_ptr", q2.toNat - globN s0 "heap_ptr") := by
      intro x hxk hxf
      have hm5_4 : s5.memory x = s4n.memory x := by
        apply hrel_nd.2.2.2.2.2.2.1 x
        · intro i hi hhit
          rw [List.mem_singleton.mp hi, hsz_ond] at hhit
          dsimp only [ncap] at hq2_lo
          exact hxf (cellHits_of_inside hhit ⟨by omega, by omega⟩)
        · intro ⟨_, h2⟩; omega
      rw [hm5_4]; change s4.memory x = _; rw [hmem4]
      apply hfr_s0_s3 x hxk
      intro hhit; exact hxf (cellHits_of_inside hhit ⟨by omega, by omega⟩)
    have htw40 : (tw + 40#64).toNat = t + 40 := by
      rw [BitVec.toNat_add, show (40#64).toNat = 40 from rfl]; omega
    exact frameOutside_trans_same hfr_s0_s5
      (frameOutside_updW s5 (tw + 40#64) nptr [(t, 88)] _
        (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
  -- 11. call memcpy(order, load(t + 48), (nodecap + 1) * 8)
  set s7o := setVarHOLFinite (ofString "order") (.val (.word optr)) s7
  have hA7o : ArenaReady s7o := ⟨guestInv_congr (s := s7) rfl rfl rfl rfl hA7.1, hA7.2⟩
  have hsz_oord : (BitVec.ofNat 64 ((nodecap + 1) * 8)).toNat = (nodecap + 1) * 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul6]
  have hw_oord : (BitVec.ofNat 64 old_order).toNat = old_order := by
    rw [BitVec.toNat_ofNat]; unfold Inside at horder_in0; omega
  have hdisj_ord : Disj (optr.toNat, (nodecap + 1) * 8) (old_order, (nodecap + 1) * 8) := by
    have hd := disj_fresh_ivl hA0 horder_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
    dsimp only [ncap] at hq3_lo
    unfold Disj at hd ⊢; omega
  have he_ord_d : evalAt s7o (.var .local (ofString "order")) = some (.val (.word optr)) := by
    simp [s7o, evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have he_ord_s : evalAt s7o (.load .one (.op .add [.var .local (ofString "t"), .const 48#64])) =
      some (.val (.word (BitVec.ofNat 64 old_order))) := by
    have ht_s7o : s7o.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [s7o, setVarHOLFinite, hloc7, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "order" ≠ ofString "t" by decide]
      exact ht_s5
    have hdom48 : s7o.memaddrs (tw + 48#64) := by
      have : s7o.memaddrs = s0.memaddrs := hA7.1.memaddrs.trans hA0.1.memaddrs.symm
      rw [this]; exact hdom_t6
    have hm48 : s7o.memory (tw + 48#64) = .word (BitVec.ofNat 64 old_order) := by
      change s7.memory (tw + 48#64) = _; rw [hmem7]
      have hne48_40 : tw + 48#64 ≠ tw + 40#64 := by
        intro he; have := congrArg BitVec.toNat he
        rw [BitVec.toNat_add, BitVec.toNat_add, show (48#64).toNat = 48 from rfl, show (40#64).toNat = 40 from rfl] at this; omega
      have hne48_32 : tw + 48#64 ≠ tw + 32#64 := by
        intro he; have := congrArg BitVec.toNat he
        rw [BitVec.toNat_add, BitVec.toNat_add, show (48#64).toNat = 48 from rfl, show (32#64).toNat = 32 from rfl] at this; omega
      simp only [s6, updW, hne48_40, ↓reduceIte]
      have hm5_4 : s5.memory (tw + 48#64) = s4n.memory (tw + 48#64) := by
        apply hrel_nd.2.2.2.2.2.2.1 (tw + 48#64)
        · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_ond] at hhit
          have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
          have htw48 : (tw + 48#64).toNat = t + 48 := by rw [BitVec.toNat_add, show (48#64).toNat = 48 from rfl]; omega
          rw [htw48] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; dsimp only [ncap] at hq2_lo; omega
        · intro ⟨_, h2⟩; omega
      rw [hm5_4]; change s4.memory _ = _; rw [hmem4]
      simp only [s3, updW, hne48_32, ↓reduceIte]
      have hm2_1 : s2.memory (tw + 48#64) = s1k.memory (tw + 48#64) := by
        apply hmcf_k.2.2.2.2.2.2 (tw + 48#64)
        · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_ok] at hhit
          have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := kptr.toNat) (hi := q1.toNat) (by omega) (by omega)
          have htw48 : (tw + 48#64).toNat = t + 48 := by rw [BitVec.toNat_add, show (48#64).toNat = 48 from rfl]; omega
          rw [htw48] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
        · intro ⟨_, h2⟩; omega
      rw [hm2_1]; change s1.memory _ = _; rw [hmem1]; exact hm_t6
    simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s7o,
      valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hdom48, hm48]
  have he_ord_n : evalAt s7o (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .const 8#64]) =
      some (.val (.word (BitVec.ofNat 64 ((nodecap + 1) * 8)))) := by
    have hnc_l : s7o.locals.lookup (ofString "nodecap") = some (.val (.word (BitVec.ofNat 64 nodecap))) := by
      simp only [s7o, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "order" ≠ ofString "nodecap" by decide, ↓reduceIte]
      rw [hloc7]; change s5.locals.lookup _ = _; rw [hloc5]
      simp only [s4n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nodes" ≠ ofString "nodecap" by decide, ↓reduceIte]
      rw [hloc4]; change s2.locals.lookup _ = _; rw [hloc2]; exact hnc0_s1k
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnc_l,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1#64).toNat = 1 from rfl, show (8#64).toNat = 8 from rfl, hz0, Nat.add_zero]
    omega
  refine Ret.seq_memcpy_disj hA7o optr (BitVec.ofNat 64 old_order) (BitVec.ofNat 64 ((nodecap + 1) * 8))
    (by rw [hsz_oord]; dsimp only [ncap] at hq3_lo; omega)
    (by rw [hw_oord, hsz_oord]; unfold Inside at horder_in0; omega)
    (by rw [hsz_oord]; omega)
    (by rw [hw_oord, hsz_oord]; exact hdisj_ord)
    he_ord_d he_ord_s he_ord_n ?_
  intro s8 hA8 hrel_ord hloc8
  -- 12. store(t + 48, order)
  have ht_s8 : s8.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    rw [hloc8]; simp [s7o, setVarHOLFinite, hloc7, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "order" ≠ ofString "t" by decide]; exact ht_s5
  have hord_s8 : s8.locals.lookup (ofString "order") = some (.val (.word optr)) := by
    rw [hloc8]; simp [s7o, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine Ret.seq_storeW (tw + 48#64) optr
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s8, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hord_s8]) ?_
  intro _
  set s9 := { s8 with memory := updW s8.memory (tw + 48#64) optr }
  -- 13. store(t + 16, load(t + 16) * 2)
  have hdom16_s9 : s9.memaddrs (tw + 16#64) := by
    have : s9.memaddrs = s0.memaddrs := hA8.1.memaddrs.trans hA0.1.memaddrs.symm
    rw [this]; exact hdom_t2
  rcases hm16_s9 : s9.memory (tw + 16#64) with ⟨capw⟩
  refine Ret.seq_storeW (tw + 16#64) (capw * 2#64)
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          show s9.locals.lookup (ofString "t") = some (.val (.word tw)) from ht_s8, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          show s9.locals.lookup (ofString "t") = some (.val (.word tw)) from ht_s8,
          valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, memLoadHOLExact, hdom16_s9, hm16_s9]) ?_
  intro _
  set s10 := { s9 with memory := updW s9.memory (tw + 16#64) (capw * 2#64) }
  -- 14. store(t + 80, ncap)
  have hnc_s10 : s10.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 ncap))) := by
    change s8.locals.lookup _ = _; rw [hloc8]
    simp only [s7o, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "order" ≠ ofString "ncap" by decide, ↓reduceIte]
    rw [hloc7]; change s5.locals.lookup _ = _; rw [hloc5]
    simp only [s4n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "nodes" ≠ ofString "ncap" by decide, ↓reduceIte]
    rw [hloc4]; change s2.locals.lookup _ = _; rw [hloc2]; exact hnc_s1k
  refine Ret.seq_storeW (tw + 80#64) (BitVec.ofNat 64 ncap)
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          show s10.locals.lookup (ofString "t") = some (.val (.word tw)) from ht_s8, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hnc_s10]) ?_
  intro _
  set s11 := { s10 with memory := updW s10.memory (tw + 80#64) (BitVec.ofNat 64 ncap) }
  -- 15. return 0
  apply Ret.ret
  intro val hval
  have hval0 : val = .val (.word 0#64) := by simp [evalAt, evalHOLExact] at hval; exact hval.symm
  subst hval0
  -- Note: the final post-state `pEnd` has the same `memory`, `globals`, `code`, `memaddrs`, `shMemaddrs`, `baseAddr`, `be` as `s11`!
  -- Let's prove our postconditions on `s11` first, and since every conjunct is independent of `locals` and `clock`, transfer immediately!
  have hA11 : ArenaReady s11 := ⟨guestInv_congr (s := s8) rfl rfl rfl rfl hA8.1, hA8.2⟩
  have hgn11 : globN s11 "heap_ptr" = q3.toNat := by
    change globN s8 "heap_ptr" = _
    have hg8 : s8.globals = s7o.globals := hrel_ord.2.2.2.2.2.1
    unfold globN at hgn7 ⊢; rw [hg8]; exact hgn7
  have hncap_eq : ncap = 2 * nodecap := rfl
  have hgn1 : globN s1 "heap_ptr" = q1.toNat := hgn1
  have hgn4 : globN s4 "heap_ptr" = q2.toNat := hgn4
  have hgn7 : globN s7 "heap_ptr" = q3.toNat := hgn7
  have hg_all : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s0.globals.lookup k = s11.globals.lookup k := by
    intro k hk'
    have e1 := hg1 k hk'
    have e2 : s1k.globals.lookup k = s2.globals.lookup k := congrArg (fun g => g.lookup k) hmcf_k.2.2.2.2.2.1.symm
    have e4 := hg4 k hk'
    have e5 : s4n.globals.lookup k = s5.globals.lookup k := congrArg (fun g => g.lookup k) hrel_nd.2.2.2.2.2.1.symm
    have e7 := hg7 k hk'
    have e8 : s7o.globals.lookup k = s8.globals.lookup k := congrArg (fun g => g.lookup k) hrel_ord.2.2.2.2.2.1.symm
    exact e1.trans (e2.trans (e4.trans (e5.trans (e7.trans e8))))
  -- Frame of s11 relative to s0:
  have hfr_s0_s8 : FrameOutside s0 s8 [(t, 88)] (globN s0 "heap_ptr", q3.toNat - globN s0 "heap_ptr") := by
    intro x hxk hxf
    have hm8_7 : s8.memory x = s7o.memory x := by
      apply hrel_ord.2.2.2.2.2.2.1 x
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_oord] at hhit
        exact hxf (cellHits_of_inside hhit ⟨by omega, by omega⟩)
      · intro ⟨_, h2⟩; omega
    rw [hm8_7]; change s7.memory x = _; rw [hmem7]
    apply hfr_s0_s6 x hxk
    intro hhit; exact hxf (cellHits_of_inside hhit ⟨by omega, by omega⟩)
  have htw48 : (tw + 48#64).toNat = t + 48 := by rw [BitVec.toNat_add, show (48#64).toNat = 48 from rfl]; omega
  have htw16 : (tw + 16#64).toNat = t + 16 := by rw [BitVec.toNat_add, show (16#64).toNat = 16 from rfl]; omega
  have htw80 : (tw + 80#64).toNat = t + 80 := by rw [BitVec.toNat_add, show (80#64).toNat = 80 from rfl]; omega
  have hfr_s0_s9 := frameOutside_trans_same hfr_s0_s8
    (frameOutside_updW s8 (tw + 48#64) optr [(t, 88)] _
      (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
  have hfr_s0_s10 := frameOutside_trans_same hfr_s0_s9
    (frameOutside_updW s9 (tw + 16#64) (capw * 2#64) [(t, 88)] _
      (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
  have hfr_s0_s11 := frameOutside_trans_same hfr_s0_s10
    (frameOutside_updW s10 (tw + 80#64) (BitVec.ofNat 64 ncap) [(t, 88)] _
      (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
  -- Helper: header word `tw + 8*k` for `k ∉ {2, 4, 5, 6, 10}` is untouched across all steps!
  have hdr_unchanged : ∀ k : Nat, k < 11 → k ≠ 2 → k ≠ 4 → k ≠ 5 → k ≠ 6 → k ≠ 10 →
      hdr s11 t k = hdr s0 t k := by
    intro k hklt hk2 hk4 hk5 hk6 hk10
    have haddr_eq : BitVec.ofNat 64 (t + 8 * k) = tw + BitVec.ofNat 64 (8 * k) := ofNat_add_toNat tw (8 * k)
    have hne : ∀ j : Nat, j < 11 → j ≠ k → BitVec.ofNat 64 (t + 8 * k) ≠ tw + BitVec.ofNat 64 (8 * j) := by
      intro j hjlt hjk heq
      rw [← ofNat_add_toNat tw (8 * j)] at heq
      have := ofNat64_eq_of_lt (by omega) (by omega) heq
      omega
    have hne10 := hne 10 (by omega) (Ne.symm hk10)
    have hne2 := hne 2 (by omega) (Ne.symm hk2)
    have hne6 := hne 6 (by omega) (Ne.symm hk6)
    have hne5 := hne 5 (by omega) (Ne.symm hk5)
    have hne4 := hne 4 (by omega) (Ne.symm hk4)
    unfold hdr memW
    have hm11_8 : s11.memory (BitVec.ofNat 64 (t + 8 * k)) = s8.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      simp only [s11, s10, s9, updW]
      rw [if_neg hne10, if_neg hne2, if_neg hne6]
    have hm8_7 : s8.memory (BitVec.ofNat 64 (t + 8 * k)) = s7o.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      apply hrel_ord.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_oord] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
        have hb : (BitVec.ofNat 64 (t + 8 * k)).toNat = t + 8 * k := by rw [BitVec.toNat_ofNat]; omega
        rw [hb] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    have hm6_5 : s6.memory (BitVec.ofNat 64 (t + 8 * k)) = s5.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      simp only [s6, updW]; rw [if_neg hne5]
    have hm5_4 : s5.memory (BitVec.ofNat 64 (t + 8 * k)) = s4n.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      apply hrel_nd.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_ond] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
        have hb : (BitVec.ofNat 64 (t + 8 * k)).toNat = t + 8 * k := by rw [BitVec.toNat_ofNat]; omega
        rw [hb] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    have hm3_2 : s3.memory (BitVec.ofNat 64 (t + 8 * k)) = s2.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      simp only [s3, updW]; rw [if_neg hne4]
    have hm2_1 : s2.memory (BitVec.ofNat 64 (t + 8 * k)) = s1k.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      apply hmcf_k.2.2.2.2.2.2
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_ok] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := kptr.toNat) (hi := q1.toNat) (by omega) (by omega)
        have hb : (BitVec.ofNat 64 (t + 8 * k)).toNat = t + 8 * k := by rw [BitVec.toNat_ofNat]; omega
        rw [hb] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    rw [hm11_8, hm8_7]
    change (match s7.memory _ with | .word w => w.toNat) = _
    rw [hmem7, hm6_5, hm5_4]
    change (match s4.memory _ with | .word w => w.toNat) = _
    rw [hmem4, hm3_2, hm2_1]
    change (match s1.memory _ with | .word w => w.toNat) = _
    rw [hmem1]
  have hh0 : hdr s11 t 0 = hdr s0 t 0 := hdr_unchanged 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh1 : hdr s11 t 1 = stride := hdr_unchanged 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh3 : hdr s11 t 3 = hdr s0 t 3 := hdr_unchanged 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh7 : hdr s11 t 7 = hdr s0 t 7 := hdr_unchanged 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh8 : hdr s11 t 8 = hdr s0 t 8 := hdr_unchanged 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh9 : hdr s11 t 9 = hdr s0 t 9 := hdr_unchanged 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh10 : hdr s11 t 10 = ncap := by
    unfold hdr memW
    rw [ofNat_add_toNat tw (8 * 10)]
    have : tw + BitVec.ofNat 64 (8 * 10) = tw + 80#64 := rfl
    rw [this]; simp only [s11, updW, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  have hh6 : hdr s11 t 6 = optr.toNat := by
    have hne10 : tw + 48#64 ≠ tw + 80#64 := by
      intro he; have := congrArg BitVec.toNat he; rw [htw48, htw80] at this; omega
    have hne2 : tw + 48#64 ≠ tw + 16#64 := by
      intro he; have := congrArg BitVec.toNat he; rw [htw48, htw16] at this; omega
    unfold hdr memW
    rw [ofNat_add_toNat tw (8 * 6)]
    have : tw + BitVec.ofNat 64 (8 * 6) = tw + 48#64 := rfl
    rw [this]; simp only [s11, s10, s9, updW, hne10, hne2, ↓reduceIte]
  have hh5 : hdr s11 t 5 = nptr.toNat := by
    have htw40 : (tw + 40#64).toNat = t + 40 := by rw [BitVec.toNat_add, show (40#64).toNat = 40 from rfl]; omega
    have hne10 : tw + 40#64 ≠ tw + 80#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw40, htw80] at this; omega
    have hne2 : tw + 40#64 ≠ tw + 16#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw40, htw16] at this; omega
    have hne6 : tw + 40#64 ≠ tw + 48#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw40, htw48] at this; omega
    unfold hdr memW
    rw [ofNat_add_toNat tw (8 * 5)]
    have : tw + BitVec.ofNat 64 (8 * 5) = tw + 40#64 := rfl
    rw [this]; simp only [s11, s10, s9, updW, hne10, hne2, hne6, ↓reduceIte]
    have hm8_7 : s8.memory (tw + 40#64) = s7o.memory (tw + 40#64) := by
      apply hrel_ord.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_oord] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
        rw [htw40] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    rw [hm8_7]; change (match s7.memory _ with | .word w => w.toNat) = _; rw [hmem7]
    simp [s6, updW]
  have hh4 : hdr s11 t 4 = kptr.toNat := by
    have htw32 : (tw + 32#64).toNat = t + 32 := by rw [BitVec.toNat_add, show (32#64).toNat = 32 from rfl]; omega
    have htw40 : (tw + 40#64).toNat = t + 40 := by rw [BitVec.toNat_add, show (40#64).toNat = 40 from rfl]; omega
    have hne10 : tw + 32#64 ≠ tw + 80#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw32, htw80] at this; omega
    have hne2 : tw + 32#64 ≠ tw + 16#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw32, htw16] at this; omega
    have hne6 : tw + 32#64 ≠ tw + 48#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw32, htw48] at this; omega
    have hne5 : tw + 32#64 ≠ tw + 40#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw32, htw40] at this; omega
    unfold hdr memW
    rw [ofNat_add_toNat tw (8 * 4)]
    have : tw + BitVec.ofNat 64 (8 * 4) = tw + 32#64 := rfl
    rw [this]; simp only [s11, s10, s9, updW, hne10, hne2, hne6, ↓reduceIte]
    have hm8_7 : s8.memory (tw + 32#64) = s7o.memory (tw + 32#64) := by
      apply hrel_ord.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_oord] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
        rw [htw32] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    rw [hm8_7]; change (match s7.memory _ with | .word w => w.toNat) = _; rw [hmem7]
    simp only [s6, updW, hne5, ↓reduceIte]
    have hm5_4 : s5.memory (tw + 32#64) = s4n.memory (tw + 32#64) := by
      apply hrel_nd.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_ond] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
        rw [htw32] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    rw [hm5_4]; change (match s4.memory _ with | .word w => w.toNat) = _; rw [hmem4]
    simp [s3, updW]
  -- Copied node fields: for `n < nodecap + 1`, `nodeF s11 nptr.toNat n off = nodeF s0 old_nodes n off`!
  have hnodes_copied : ∀ n, n < nodecap + 1 → ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s11 nptr.toNat n off = nodeF s0 old_nodes n off := by
    intro n hn_lt off hoff
    unfold nodeF
    set a := nptr.toNat + 32 * n + off
    have ha_al : a % 8 = 0 := by rcases hoff with rfl | rfl | rfl | rfl <;> dsimp [a] <;> omega
    have ha_hi : a + 8 ≤ nptr.toNat + (nodecap + 1) * 32 := by rcases hoff with rfl | rfl | rfl | rfl <;> dsimp [a] <;> omega
    -- `a` is in `[nptr, q2)`, disjoint from `(t, 88)` and `[optr, q3)`!
    have hd_hdr := disj_fresh_ivl hA0 hhdr_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
    have hm11_8 : s11.memory (BitVec.ofNat 64 a) = s8.memory (BitVec.ofNat 64 a) := by
      have hne : ∀ off_t : BitVec 64, off_t.toNat < 88 → BitVec.ofNat 64 a ≠ tw + off_t := by
        intro off_t hoff_t heq
        have := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)] at this
        unfold Disj at hd_hdr; omega
      simp only [s11, s10, s9, updW, hne 80#64 (by decide), hne 16#64 (by decide), hne 48#64 (by decide), ↓reduceIte]
    have hm8_7 : s8.memory (BitVec.ofNat 64 a) = s7o.memory (BitVec.ofNat 64 a) := by
      apply hrel_ord.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_oord] at hhit
        have hb : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
        rw [hb] at hhit; obtain ⟨h1, h2⟩ := hhit; omega
      · intro ⟨_, h2⟩; omega
    have hm6_5 : s6.memory (BitVec.ofNat 64 a) = s5.memory (BitVec.ofNat 64 a) := by
      have hne40 : BitVec.ofNat 64 a ≠ tw + 40#64 := by
        intro heq; have := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_add, show (40#64).toNat = 40 from rfl, Nat.mod_eq_of_lt (by omega)] at this
        unfold Disj at hd_hdr; omega
      simp [s6, updW, hne40]
    have hm11_5 : memW s11 a = memW s5 a := by
      unfold memW; rw [hm11_8, hm8_7]; change (match s7.memory _ with | .word w => w.toNat) = _; rw [hmem7, hm6_5]
    rw [hm11_5]
    -- Now use `memW_copied_of_memCopyRel` on `hrel_nd : MemCopyRel s4n s5 nptr (BitVec.ofNat 64 old_nodes) ((nodecap+1)*32) ((nodecap+1)*32)`!
    have hsz_eq : (BitVec.ofNat 64 ((nodecap + 1) * 32)).toNat = (nodecap + 1) * 32 := hsz_ond
    have hrel_nd' : MemCopyRel s4n s5 nptr (BitVec.ofNat 64 old_nodes) ((nodecap + 1) * 32) ((nodecap + 1) * 32) := by
      rw [← hsz_eq]; exact hrel_nd
    have ha_eq : a = nptr.toNat + (32 * n + off) := by dsimp [a]; omega
    have hcp := memW_copied_of_memCopyRel (off := 32 * n + off) hrel_nd' hnptr_al
      (by rw [hw_ond]; exact hnodes_in0.2.1)
      (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)
      (by dsimp only [ncap] at hq2_lo; omega) (by rw [hw_ond]; unfold Inside at hnodes_in0; omega)
    rw [ha_eq, hcp, hw_ond]
    -- Finally, `memW s4n (old_nodes + (32 * n + off)) = memW s0 (old_nodes + 32 * n + off)` by `hfr_s0_s3`!
    have hb_eq : old_nodes + (32 * n + off) = old_nodes + 32 * n + off := by omega
    rw [hb_eq]
    change memW s4 (old_nodes + 32 * n + off) = _
    unfold memW; rw [hmem4]
    have hm3_0 : s3.memory (BitVec.ofNat 64 (old_nodes + 32 * n + off)) = s0.memory (BitVec.ofNat 64 (old_nodes + 32 * n + off)) := by
      have hb_nat : (BitVec.ofNat 64 (old_nodes + 32 * n + off)).toNat = old_nodes + 32 * n + off := by
        rw [BitVec.toNat_ofNat]; unfold Inside at hnodes_in0
        rcases hoff with rfl | rfl | rfl | rfl <;> omega
      apply hfr_s0_s3
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hb_nat] at hhit
        have hpair := hB0.2.1; simp only [htabFootprint, List.pairwise_cons, List.mem_cons] at hpair
        have hd_tn : Disj (t, 88) (old_nodes, (nodecap + 1) * 32) := hpair.1 _ (Or.inr (Or.inl rfl))
        obtain ⟨c1, c2⟩ := hhit; unfold Disj at hd_tn
        rcases hoff with rfl | rfl | rfl | rfl <;> omega
      · intro hhit
        have c1 : globN s0 "heap_ptr" < (BitVec.ofNat 64 (old_nodes + 32 * n + off)).toNat + 8 := hhit.1
        have c2 : (BitVec.ofNat 64 (old_nodes + 32 * n + off)).toNat < globN s0 "heap_ptr" + (q1.toNat - globN s0 "heap_ptr") := hhit.2
        have c1' : globN s0 "heap_ptr" < old_nodes + 32 * n + off + 8 := hb_nat ▸ c1
        have c2' : old_nodes + 32 * n + off < globN s0 "heap_ptr" + (q1.toNat - globN s0 "heap_ptr") := hb_nat ▸ c2
        have hd_fn := disj_fresh_of_allocated hA0 hnodes_al0 (lo := globN s0 "heap_ptr") (hi := q1.toNat) le_rfl (by omega)
        have hpos_q1 : globN s0 "heap_ptr" < q1.toNat := by
          have : 0 < (ncap + 1) * stride := Nat.mul_pos (by dsimp [ncap]; omega) (by omega)
          omega
        rcases hd_fn with hz | hle_bad | hle | hle
        · change (hdr s0 t 10 + 1) * 32 = 0 at hz; omega
        · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hpos_q1 hle_bad)
        · change globN s0 "heap_ptr" + (q1.toNat - globN s0 "heap_ptr") ≤ hdr s0 t 5 at hle
          have hsub : hdr s0 t 5 ≤ old_nodes + 32 * n + off := by
            change old_nodes ≤ (old_nodes + 32 * n) + off
            exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
          exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le c2' (Nat.le_trans hle hsub))
        · change hdr s0 t 5 + (hdr s0 t 10 + 1) * 32 ≤ globN s0 "heap_ptr" at hle
          have hsub : old_nodes + 32 * n + off + 8 ≤ hdr s0 t 5 + (hdr s0 t 10 + 1) * 32 := by
            change hdr s0 t 5 + 32 * n + off + 8 ≤ hdr s0 t 5 + (nodecap + 1) * 32
            rcases hoff with rfl | rfl | rfl | rfl <;> omega
          exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le c1' (Nat.le_trans hsub hle))
    rw [hm3_0]
  -- Copied order words: for `i < nodecap + 1`, `memW s11 (optr.toNat + 8 * i) = memW s0 (old_order + 8 * i)`!
  have horder_copied : ∀ i, i < nodecap + 1 →
      memW s11 (optr.toNat + 8 * i) = memW s0 (old_order + 8 * i) := by
    intro i hi_lt
    set a := optr.toNat + 8 * i
    have hd_hdr := disj_fresh_ivl hA0 hhdr_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
    have hm11_8 : s11.memory (BitVec.ofNat 64 a) = s8.memory (BitVec.ofNat 64 a) := by
      have hne : ∀ off_t : BitVec 64, off_t.toNat < 88 → BitVec.ofNat 64 a ≠ tw + off_t := by
        intro off_t hoff_t heq
        have := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)] at this
        unfold Disj at hd_hdr; omega
      simp only [s11, s10, s9, updW, hne 80#64 (by decide), hne 16#64 (by decide), hne 48#64 (by decide), ↓reduceIte]
    have hm11_8w : memW s11 a = memW s8 a := by unfold memW; rw [hm11_8]
    rw [hm11_8w]
    have hrel_ord' : MemCopyRel s7o s8 optr (BitVec.ofNat 64 old_order) ((nodecap + 1) * 8) ((nodecap + 1) * 8) := by
      rw [← hsz_oord]; exact hrel_ord
    have hcp := memW_copied_of_memCopyRel (off := 8 * i) hrel_ord' hoptr_al
      (by rw [hw_oord]; exact horder_in0.2.1)
      (by omega) (by omega) (by omega) (by rw [hw_oord]; unfold Inside at horder_in0; omega)
    rw [show a = optr.toNat + 8 * i from rfl, hcp, hw_oord]
    change memW s7 (old_order + 8 * i) = _
    unfold memW; rw [hmem7]
    have hm6_0 : s6.memory (BitVec.ofNat 64 (old_order + 8 * i)) = s0.memory (BitVec.ofNat 64 (old_order + 8 * i)) := by
      have hb_nat : (BitVec.ofNat 64 (old_order + 8 * i)).toNat = old_order + 8 * i := by
        rw [BitVec.toNat_ofNat]; unfold Inside at horder_in0; omega
      apply hfr_s0_s6
      · intro iv hiv hhit; rw [List.mem_singleton.mp hiv, hb_nat] at hhit
        have hpair := hB0.2.1; simp only [htabFootprint, List.pairwise_cons, List.mem_cons] at hpair
        have hd_to : Disj (t, 88) (old_order, (nodecap + 1) * 8) := hpair.1 _ (Or.inr (Or.inr (Or.inl rfl)))
        obtain ⟨c1, c2⟩ := hhit; unfold Disj at hd_to; omega
      · intro hhit; rw [hb_nat] at hhit
        have hd_fo := disj_fresh_ivl hA0 horder_al0 (lo := globN s0 "heap_ptr") (hi := q2.toNat) (by omega) (by omega)
        obtain ⟨c1, c2⟩ := hhit; unfold Disj at hd_fo; omega
    rw [hm6_0]
  -- `HtabBlocks s11 t`:
  have hsb_val : sourceBase = 2701131776 := rfl
  have hhp0_lo : sourceBase ≤ globN s0 "heap_ptr" := hA0.2.1
  have hB11 : HtabBlocks s11 t := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro iv hiv
      simp only [htabFootprint, hh4, hh5, hh6, hh10, hh1, List.mem_cons, List.not_mem_nil, or_false] at hiv
      rcases hiv with rfl | rfl | rfl | rfl
      · exact ⟨⟨ht_lo, ht_hi⟩, wordsOK_block s11 hA11.1.memaddrs t 88 ht_al (by omega) ht_lo ht_hi⟩
      · have hmul_le : (ncap + 1) * stride ≤ q1.toNat - kptr.toNat := by omega
        exact ⟨⟨by omega, by omega⟩, wordsOK_block s11 hA11.1.memaddrs kptr.toNat ((ncap + 1) * stride) hkptr_al (Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_of_dvd_right (Nat.dvd_iff_mod_eq_zero.mpr hst_al) _)) (by omega) (by omega)⟩
      · exact ⟨⟨by omega, by omega⟩, wordsOK_block s11 hA11.1.memaddrs nptr.toNat ((ncap + 1) * 32) hnptr_al (by omega) (by omega) (by omega)⟩
      · exact ⟨⟨by omega, by omega⟩, wordsOK_block s11 hA11.1.memaddrs optr.toNat ((ncap + 1) * 8) hoptr_al (by omega) (by omega) (by omega)⟩
    · simp only [htabFootprint, hh4, hh5, hh6, hh10, hh1, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
      have hd_tk := disj_fresh_ivl hA0 hhdr_al0 (lo := kptr.toNat) (hi := q1.toNat) (by omega) (by omega)
      have hd_tn := disj_fresh_ivl hA0 hhdr_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
      have hd_to := disj_fresh_ivl hA0 hhdr_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, fun _ h => False.elim h⟩
      · unfold Disj at hd_tk ⊢; omega
      · unfold Disj at hd_tn ⊢; omega
      · unfold Disj at hd_to ⊢; omega
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    · rw [hh0]; exact hB0.2.2.1
    · rw [hh0]; exact hB0.2.2.2.1
    · rw [hh1, hh0]; exact hB0.2.2.2.2.1
    · rw [hh10]; omega
    · rw [hh8]; exact hnx1
    · rw [hh8, hh10]; omega
  -- Footprint allocation + provenance in `s11`:
  have hfp11 : ∀ iv ∈ htabFootprint s11 t, Allocated s11 iv ∧
      ((∃ j ∈ htabFootprint s0 t, Inside iv j.1 (j.1 + j.2)) ∨
        Inside iv (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (q3.toNat - globN s0 "heap_ptr"))) := by
    have hgrows : AllocatorGrows s0 s11 := by
      refine ⟨by rw [hgn11]; omega, ?_⟩
      have hsp := hg_all (ofString "scratch_ptr") (by simp [show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide])
      unfold globN; rw [← hsp]
    intro iv hiv
    simp only [htabFootprint, hh4, hh5, hh6, hh10, hh1, List.mem_cons, List.not_mem_nil, or_false] at hiv
    rcases hiv with rfl | rfl | rfl | rfl
    · exact ⟨hgrows.allocated hhdr_al0, Or.inl ⟨(t, 88), by simp [htabFootprint], le_rfl, le_rfl⟩⟩
    · exact ⟨Or.inl ⟨by omega, by rw [hgn11]; omega⟩, Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨Or.inl ⟨by omega, by rw [hgn11]; omega⟩, Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨Or.inl ⟨by omega, by rw [hgn11]; omega⟩, Or.inr ⟨by omega, by omega⟩⟩
  -- Now package for the final state (same `memory`/`globals`/metadata as `s11`)!
  refine ⟨rfl, ⟨guestInv_congr (s := s11) rfl rfl rfl rfl hA11.1, hA11.2⟩,
    hB11, hh0, hh1, hh3, hh7, hh8, hh9, hh10, ?_, ?_, ?_, ?_, ?_, hg_all⟩
  · intro n hn off hoff
    change nodeF s11 (hdr s11 t 5) n off = nodeF s0 old_nodes n off
    rw [hh5]; exact hnodes_copied n hn off hoff
  · intro i hi
    change memW s11 (hdr s11 t 6 + 8 * i) = memW s0 (old_order + 8 * i)
    rw [hh6]; exact horder_copied i hi
  · change globN s0 "heap_ptr" ≤ globN s11 "heap_ptr"; rw [hgn11]; omega
  · change ∀ iv ∈ htabFootprint s11 t, Allocated s11 iv ∧
      ((∃ j ∈ htabFootprint s0 t, Inside iv j.1 (j.1 + j.2)) ∨
        Inside iv (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s11 "heap_ptr" - globN s0 "heap_ptr")))
    rw [hgn11]; exact hfp11
  · change FrameOutside s0 s11 [(t, 88)] (globN s0 "heap_ptr", globN s11 "heap_ptr" - globN s0 "heap_ptr")
    rw [hgn11]; exact hfr_s0_s11

end InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

/-! ### From SoloHtabSetNewNode.lean -/

/-! Normal-form (`NS`) local-insensitive `Ret` combinators and `htab_new_node` postcondition. -/


namespace InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Normal-Form States (`NS`) and Local-Insensitive `Ret` Combinators -/

def NS {F : Type} (s : PanSemStateFiniteExact 64 F) (L G : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C : Nat) : PanSemStateFiniteExact 64 F :=
  { s with locals := L, globals := G, memory := M, clock := C }

section NSlemmas
variable {F : Type} (s : PanSemStateFiniteExact 64 F) (L G : HolFiniteMapExact MlS (ValueHOL 64))
  (M : BitVec 64 → HolWordLab 64) (C : Nat)
@[simp] theorem NS_locals : (NS s L G M C).locals = L := rfl
@[simp] theorem NS_globals : (NS s L G M C).globals = G := rfl
@[simp] theorem NS_memory : (NS s L G M C).memory = M := rfl
@[simp] theorem NS_clock : (NS s L G M C).clock = C := rfl
@[simp] theorem NS_code : (NS s L G M C).code = s.code := rfl
@[simp] theorem NS_memaddrs : (NS s L G M C).memaddrs = s.memaddrs := rfl
@[simp] theorem NS_shMemaddrs : (NS s L G M C).shMemaddrs = s.shMemaddrs := rfl
@[simp] theorem NS_baseAddr : (NS s L G M C).baseAddr = s.baseAddr := rfl
@[simp] theorem NS_be : (NS s L G M C).be = s.be := rfl
@[simp] theorem NS_structs : (NS s L G M C).structs = s.structs := rfl
@[simp] theorem NS_toExact_memaddrs : (NS s L G M C).toExact.memaddrs = s.memaddrs := rfl
@[simp] theorem NS_toExact_memory : (NS s L G M C).toExact.memory = M := rfl
end NSlemmas

def LocFreePost {F : Type} (Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ v (t : PanSemStateFiniteExact 64 F) L', Φ v { t with locals := L' } → Φ v t

theorem Ret.ite_ret {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {y b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hyn : ∀ u : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState s y).1 ≠ none)
    (h : ∀ cw : BitVec 64, evalAt s c = some (.val (.word cw)) →
      (cw ≠ 0 → Ret s y Φ) ∧ (cw = 0 → Ret s b Φ)) :
    Ret s (.seq (.ite c y .skip) b) Φ := by
  refine Ret.seq_ite fun cw hcw => ⟨fun hnz => ?_, fun hz => Ret.seq_skip ((h cw hcw).2 hz)⟩
  exact Ret.seq ((h cw hcw).1 hnz) fun u hu => False.elim (hyn u (congrArg Prod.fst hu))

theorem noFlow_dec {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {init : ExpHOL 64} {body : ProgHOL 64}
    (hb : ∀ s' : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState s' body).1 ≠ none) :
    (evaluateHOLFiniteState s (.dec x sh init body)).1 ≠ none := by
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  split
  · simp
  · split
    · exact hb _
    · simp

theorem noFlow_seq_right {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (hb : ∀ s' : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState s' b).1 ≠ none) :
    (evaluateHOLFiniteState s (.seq a b)).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s a with ⟨r, m⟩
  cases r with
  | none => exact hb m
  | some _ => simp

theorem noFlow_ret {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64} :
    (evaluateHOLFiniteState s (.return e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

theorem ev_var_node_load {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (nd w off : BitVec 64)
    (h1 : s.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (h2 : s.locals.lookup x = some (.val (.word w))) (v : ValueHOL 64)
    (h : evalAt s (.load .one (.op .add [.var .local (ofString "nodes"),
      .panop .mul [.var .local x, .const 32], .const off])) = some v) :
    s.memaddrs (nd + w * 32 + off) ∧ v = .val (s.memory (nd + w * 32 + off)) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, h1, h2, panOpHOL, valueIsWord, valueWord, wordOpHOL,
    wordOp, memLoadHOLExact] at h
  rw [BitVec.add_assoc]
  exact ⟨h.1, h.2.symm⟩

theorem Ret.of_NS {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : Ret (NS s s.locals s.globals s.memory s.clock) p Φ) : Ret s p Φ := by
  cases s; exact h

theorem Ret.ns_dec_lf {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {x : MlS}
    {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (h : ∀ val, evalAt (NS s L G M C) init = some val →
      Ret (NS s (L.update (x, val)) G M C) body Φ) :
    Ret (NS s L G M C) (.dec x sh init body) Φ :=
  Ret.dec fun val hval v hv => hLF v _ _ (h val hval v hv)

theorem Ret.ns_storeW {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {d e : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a w : BitVec 64) (hd : evalAt (NS s L G M C) d = some (.val (.word a)))
    (he : evalAt (NS s L G M C) e = some (.val (.word w)))
    (hb : s.memaddrs a → Ret (NS s L G (updW M a w) C) b Φ) :
    Ret (NS s L G M C) (.seq (.store d e) b) Φ :=
  Ret.seq_storeW a w hd he hb

theorem Ret.ns_assign {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {x : MlS} {e : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (w : BitVec 64) (he : evalAt (NS s L G M C) e = some (.val (.word w)))
    (hb : Ret (NS s (L.update (x, .val (.word w))) G M C) b Φ) :
    Ret (NS s L G M C) (.seq (.assign .local x e) b) Φ :=
  Ret.seq_assign w he hb

theorem Ret.ns_ret {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {e : ExpHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, evalAt (NS s L G M C) e = some val →
      Φ val (NS s HolFiniteMapExact.empty G M C)) :
    Ret (NS s L G M C) (.return e) Φ :=
  Ret.ret h

theorem Ret.decCall1_lf {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 : MlS}
    {e1 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], fbody, .one))
    (w1 : BitVec 64) (he1 : evalAt s e1 = some (.val (.word w1)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (p1, .val (.word w1)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont Φ) :
    Ret s (.decCall x .one fname [e1] cont) Φ :=
  Ret.decCall1 hcode hlook w1 he1 fun w post hrun v hv => hLF v _ _ (hk w post hrun v hv)

theorem Ret.decCall2_lf {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 p2 : MlS}
    {e1 e2 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (hcode : s.code = originalRuntimeCode) (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], fbody, .one))
    (w1 w2 : BitVec 64)
    (he1 : evalAt s e1 = some (.val (.word w1)))
    (he2 : evalAt s e2 = some (.val (.word w2)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont Φ) :
    Ret s (.decCall x .one fname [e1, e2] cont) Φ :=
  Ret.decCall2 hcode hne hlook w1 w2 he1 he2 fun w post hrun v hv => hLF v _ _ (hk w post hrun v hv)

theorem Ret.decCall3_lf {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 p2 p3 : MlS}
    {e1 e2 e3 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (hcode : s.code = originalRuntimeCode) (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], fbody, .one))
    (w1 w2 w3 : BitVec 64)
    (he1 : evalAt s e1 = some (.val (.word w1)))
    (he2 : evalAt s e2 = some (.val (.word w2)))
    (he3 : evalAt s e3 = some (.val (.word w3)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update (p3, .val (.word w3)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont Φ) :
    Ret s (.decCall x .one fname [e1, e2, e3] cont) Φ :=
  Ret.decCall3 hcode hne12 hne13 hne23 hlook w1 w2 w3 he1 he2 he3 fun w post hrun v hv => hLF v _ _ (hk w post hrun v hv)

/-! ## 2. Structured Node-Allocation Invariant (`NodeState`) -/

def NodeState {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) (A Fr : List Nat) : Prop :=
  HtabBlocks s t ∧
  (A ++ Fr).Nodup ∧
  (∀ x, x ∈ A ++ Fr ↔ 1 ≤ x ∧ x < hdr s t 8) ∧
  FreeChainF (nodeF s (hdr s t 5)) (hdr s t 9) Fr

theorem htabBlocks_cell_sep {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (hB : HtabBlocks s t) :
    (∀ k < 11, ∀ n < hdr s t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      BitVec.ofNat 64 (t + 8 * k) ≠ BitVec.ofNat 64 (hdr s t 5 + 32 * n + off)) ∧
    (∀ k < 11, ∀ i < hdr s t 10 + 1,
      BitVec.ofNat 64 (t + 8 * k) ≠ BitVec.ofNat 64 (hdr s t 6 + 8 * i)) ∧
    (∀ n < hdr s t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      ∀ i < hdr s t 10 + 1,
      BitVec.ofNat 64 (hdr s t 6 + 8 * i) ≠ BitVec.ofNat 64 (hdr s t 5 + 32 * n + off)) ∧
    (∀ n1 < hdr s t 10 + 1, ∀ off1, (off1 = 0 ∨ off1 = 8 ∨ off1 = 16 ∨ off1 = 24) →
      ∀ n2 < hdr s t 10 + 1, ∀ off2, (off2 = 0 ∨ off2 = 8 ∨ off2 = 16 ∨ off2 = 24) →
      (n1 ≠ n2 ∨ off1 ≠ off2) →
      BitVec.ofNat 64 (hdr s t 5 + 32 * n1 + off1) ≠ BitVec.ofNat 64 (hdr s t 5 + 32 * n2 + off2)) ∧
    (∀ i1 < hdr s t 10 + 1, ∀ i2 < hdr s t 10 + 1, i1 ≠ i2 →
      BitVec.ofNat 64 (hdr s t 6 + 8 * i1) ≠ BitVec.ofNat 64 (hdr s t 6 + 8 * i2)) := by
  have hhe : heapEnd = 33806089704 := rfl
  have hhdr_in := (hB.1 (t, 88) (by simp [htabFootprint])).1
  have hnd_in := (hB.1 (hdr s t 5, (hdr s t 10 + 1) * 32) (by simp [htabFootprint])).1
  have hord_in := (hB.1 (hdr s t 6, (hdr s t 10 + 1) * 8) (by simp [htabFootprint])).1
  unfold Inside at hhdr_in hnd_in hord_in
  have hpair := hB.2.1
  simp only [htabFootprint, List.pairwise_cons, List.mem_cons] at hpair
  have hd_tn : Disj (t, 88) (hdr s t 5, (hdr s t 10 + 1) * 32) := hpair.1 _ (Or.inr (Or.inl rfl))
  have hd_to : Disj (t, 88) (hdr s t 6, (hdr s t 10 + 1) * 8) := hpair.1 _ (Or.inr (Or.inr (Or.inl rfl)))
  have hd_no : Disj (hdr s t 5, (hdr s t 10 + 1) * 32) (hdr s t 6, (hdr s t 10 + 1) * 8) := hpair.2.2.1 _ (Or.inl rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk n hn off hoff
    apply ofNat64_ne_of_ne_of_lt (by omega) (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)
    unfold Disj at hd_tn
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  · intro k hk i hi
    apply ofNat64_ne_of_ne_of_lt (by omega) (by omega)
    unfold Disj at hd_to; omega
  · intro n hn off hoff i hi
    apply ofNat64_ne_of_ne_of_lt (by omega) (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)
    unfold Disj at hd_no
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  · intro n1 hn1 off1 hoff1 n2 hn2 off2 hoff2 hne
    apply ofNat64_ne_of_ne_of_lt
      (by rcases hoff1 with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hoff2 with rfl | rfl | rfl | rfl <;> omega)
    rcases hoff1 with rfl | rfl | rfl | rfl <;> rcases hoff2 with rfl | rfl | rfl | rfl <;> omega
  · intro i1 hi1 i2 hi2 hne
    apply ofNat64_ne_of_ne_of_lt (by omega) (by omega)
    omega

theorem wordsOK_updW {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a w : BitVec 64) (i : Ivl) (hi : WordsOK s i) :
    WordsOK { s with memory := updW s.memory a w } i := by
  refine ⟨hi.1, hi.2.1, fun k hk => ?_⟩
  obtain ⟨u, hdom, hu⟩ := hi.2.2 k hk
  by_cases heq : BitVec.ofNat 64 (i.1 + 8 * k) = a
  · exact ⟨w, hdom, by simp [updW, heq]⟩
  · exact ⟨u, hdom, by simp [updW, heq, hu]⟩

theorem htabBlocks_updW_nonlayout {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (a w : BitVec 64) (hB : HtabBlocks s t)
    (hnot0 : BitVec.ofNat 64 (t + 8 * 0) ≠ a)
    (hnot1 : BitVec.ofNat 64 (t + 8 * 1) ≠ a)
    (hnot4 : BitVec.ofNat 64 (t + 8 * 4) ≠ a)
    (hnot5 : BitVec.ofNat 64 (t + 8 * 5) ≠ a)
    (hnot6 : BitVec.ofNat 64 (t + 8 * 6) ≠ a)
    (hnot10 : BitVec.ofNat 64 (t + 8 * 10) ≠ a)
    (hnx_ok : BitVec.ofNat 64 (t + 8 * 8) = a → 1 ≤ w.toNat ∧ w.toNat ≤ hdr s t 10 + 1) :
    let s' := { s with memory := updW s.memory a w }
    HtabBlocks s' t ∧ htabFootprint s' t = htabFootprint s t := by
  intro s'
  have hh0 : hdr s' t 0 = hdr s t 0 := memW_updW_other s a w _ hnot0
  have hh1 : hdr s' t 1 = hdr s t 1 := memW_updW_other s a w _ hnot1
  have hh4 : hdr s' t 4 = hdr s t 4 := memW_updW_other s a w _ hnot4
  have hh5 : hdr s' t 5 = hdr s t 5 := memW_updW_other s a w _ hnot5
  have hh6 : hdr s' t 6 = hdr s t 6 := memW_updW_other s a w _ hnot6
  have hh10 : hdr s' t 10 = hdr s t 10 := memW_updW_other s a w _ hnot10
  have hfp_eq : htabFootprint s' t = htabFootprint s t := by
    simp [htabFootprint, hh1, hh4, hh5, hh6, hh10]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hfp_eq⟩
  · intro iv hiv
    rw [hfp_eq] at hiv
    obtain ⟨hin, hwok⟩ := hB.1 iv hiv
    exact ⟨hin, wordsOK_updW s a w iv hwok⟩
  · rw [hfp_eq]; exact hB.2.1
  · rw [hh0]; exact hB.2.2.1
  · rw [hh0]; exact hB.2.2.2.1
  · rw [hh1, hh0]; exact hB.2.2.2.2.1
  · rw [hh10]; exact hB.2.2.2.2.2.1
  · by_cases h8 : BitVec.ofNat 64 (t + 8 * 8) = a
    · have : hdr s' t 8 = w.toNat := by simp [hdr, memW, s', updW, h8]
      rw [this]; exact (hnx_ok h8).1
    · rw [show hdr s' t 8 = hdr s t 8 from memW_updW_other s a w _ h8]; exact hB.2.2.2.2.2.2.1
  · by_cases h8 : BitVec.ofNat 64 (t + 8 * 8) = a
    · have : hdr s' t 8 = w.toNat := by simp [hdr, memW, s', updW, h8]
      rw [this, hh10]; exact (hnx_ok h8).2
    · rw [show hdr s' t 8 = hdr s t 8 from memW_updW_other s a w _ h8, hh10]; exact hB.2.2.2.2.2.2.2

/-! ## 3. `htab_new_node` Postcondition -/

def NewNodePost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat) (A : List Nat)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) : Prop :=
  let fresh : Ivl := (globN s0 "heap_ptr", globN post "heap_ptr" - globN s0 "heap_ptr")
  ∃ nw : BitVec 64, ∃ Fr1 : List Nat,
    v = .val (.word nw) ∧
    ArenaReady post ∧
    NodeState post t (A ++ [nw.toNat]) Fr1 ∧
    hdr post t 0 = hdr s0 t 0 ∧
    hdr post t 1 = hdr s0 t 1 ∧
    hdr post t 3 = hdr s0 t 3 ∧
    hdr post t 7 = hdr s0 t 7 ∧
    hdr s0 t 10 ≤ hdr post t 10 ∧
    (∀ x ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF post (hdr post t 5) x off = nodeF s0 (hdr s0 t 5) x off) ∧
    (∀ i, i < hdr s0 t 10 + 1 →
      memW post (hdr post t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i)) ∧
    globN s0 "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i ∧
      ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
    FrameOutside s0 post [(t, 88)] fresh ∧
    (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s0.globals.lookup k = post.globals.lookup k)

theorem locFree_newNodePost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat) (A : List Nat) :
    LocFreePost (NewNodePost s0 t A) := by
  intro v p L' h
  obtain ⟨nw, Fr1, hv, hA, hNS, c0, c1, c3, c7, c10, cnd, cord, chp, cfp, cfr, cg⟩ := h
  exact ⟨nw, Fr1, hv, ⟨guestInv_congr (s := { p with locals := L' }) rfl rfl rfl rfl hA.1, hA.2⟩,
    hNS, c0, c1, c3, c7, c10, cnd, cord, chp, cfp, cfr, cg⟩

theorem htab_new_node_body_spec {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (tw : BitVec 64) (A Fr0 : List Nat)
    (ht : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_new_node) (NewNodePost s0 tw.toNat A) := by
  set t := tw.toNat
  have hLF := locFree_newNodePost s0 t A
  obtain ⟨hB0, hnodup0, hmem0, hfc0⟩ := hNS0
  obtain ⟨hncap_lt, hst_ge8, hst_le64, hst_al, ht_lo, ht_hi, ht_al⟩ := htabBlocks_bounds hB0
  have hnx_le0 : hdr s0 t 8 ≤ hdr s0 t 10 + 1 := hB0.2.2.2.2.2.2.2
  have hnx_ge1 : 1 ≤ hdr s0 t 8 := hB0.2.2.2.2.2.2.1
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom_t5, hm_t5⟩ := word_of_hdr s0 tw 5 (by omega) hB0
  obtain ⟨hdom_t8, hm_t8⟩ := word_of_hdr s0 tw 8 (by omega) hB0
  obtain ⟨hdom_t9, hm_t9⟩ := word_of_hdr s0 tw 9 (by omega) hB0
  obtain ⟨hdom_t10, hm_t10⟩ := word_of_hdr s0 tw 10 (by omega) hB0
  htab_unfold Guest.Software.guestFn_htab_new_node
  apply Ret.of_NS
  -- 1. dec f := load(t + 72)
  apply Ret.ns_dec_lf hLF; intro vf hvf
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 72#64 ht vf hvf
  have hm72 : s0.memory (tw + 72#64) = .word (BitVec.ofNat 64 (hdr s0 t 9)) := hm_t9
  simp only [NS_memory, hm72]
  set fw := BitVec.ofNat 64 (hdr s0 t 9)
  -- 2. seq (ite (f != 0) (...) skip) (...)
  apply Ret.seq_ite
  intro cw hcw
  have hcw_spec : (cw ≠ 0 → hdr s0 t 9 ≠ 0) ∧ (cw = 0 → hdr s0 t 9 = 0) := by
    obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp _ .notEqual _ _ cw hcw
    simp [evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE] at hva hvb
    subst hva hvb
    have hf_lt : hdr s0 t 9 < 2 ^ 64 := by
      cases Fr0 with
      | nil => simp [FreeChainF] at hfc0; omega
      | cons f0 Fr1 =>
        have hf0_eq : hdr s0 t 9 = f0 := hfc0.1
        have hf0_mem : f0 ∈ A ++ (f0 :: Fr1) := List.mem_append_right _ List.mem_cons_self
        have := (hmem0 f0).mp hf0_mem
        omega
    have hfw_nat : fw.toNat = hdr s0 t 9 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf_lt]
    have hz0 : (0#64 : BitVec 64).toNat = 0 := rfl
    constructor
    · intro hnz h0; apply hnz
      have hfw0 : fw = 0#64 := BitVec.eq_of_toNat_eq (by rw [hfw_nat, hz0]; exact h0)
      simp [Compiler.Encoders.Asm.wordCmpHOL, hfw0] at hcw_eq; exact hcw_eq
    · intro hz; by_contra hne
      have hfw_ne : fw ≠ 0#64 := fun h => hne (by have := congrArg BitVec.toNat h; rw [hfw_nat, hz0] at this; exact this)
      simp [Compiler.Encoders.Asm.wordCmpHOL, hfw_ne] at hcw_eq
      rw [hz] at hcw_eq; exact absurd hcw_eq (by decide)
  refine ⟨fun hcw_nz => ?_, fun hcw_z => ?_⟩
  · -- CASE A: Free list non-empty (`hdr s0 t 9 ≠ 0`)!
    have hfree_nz := hcw_spec.1 hcw_nz
    cases Fr0 with
    | nil => simp [FreeChainF] at hfc0; exact absurd hfc0 hfree_nz
    | cons f0 Fr1 =>
      obtain ⟨hf0_eq, hfc1⟩ := hfc0
      have hf0_mem : f0 ∈ A ++ (f0 :: Fr1) := List.mem_append_right _ List.mem_cons_self
      have hf0_rng := (hmem0 f0).mp hf0_mem
      have hfw_nat : fw.toNat = f0 := by rw [BitVec.toNat_ofNat, ← hf0_eq]; omega
      refine Ret.seq ?_ ?_
      · apply Ret.ns_dec_lf hLF; intro vnd hvnd
        obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 40#64
          (by simp [HolFiniteMapExact.lookup_update, FUPDATE, ht, show ofString "f" ≠ ofString "t" by decide]) vnd hvnd
        have hm40 : s0.memory (tw + 40#64) = .word (BitVec.ofNat 64 (hdr s0 t 5)) := hm_t5
        simp only [NS_memory, hm40]
        set ndw := BitVec.ofNat 64 (hdr s0 t 5)
        have hndw_nat : ndw.toNat = hdr s0 t 5 := by
          have hnd_in := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint])).1
          unfold Inside at hnd_in; rw [BitVec.toNat_ofNat]; omega
        apply Ret.ns_dec_lf hLF; intro vnf hvnf
        obtain ⟨_, rfl⟩ := ev_var_node_load _ (ofString "f") ndw fw 0#64
          (by simp [HolFiniteMapExact.lookup_update, FUPDATE])
          (by simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "nodes" ≠ ofString "f" by decide]) vnf hvnf
        have hf0_lt_nc0 : fw.toNat < hdr s0 tw.toNat 10 + 1 := by
          change fw.toNat < hdr s0 t 10 + 1
          omega
        obtain ⟨_, hm_nf⟩ := word_of_node s0 tw ndw fw 0 hndw_nat.symm hf0_lt_nc0 (Or.inl rfl) hB0
        have hm_nf' : s0.memory (ndw + fw * 32 + 0#64) = .word (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) f0 0)) := by
          rw [← hndw_nat, ← hfw_nat]; exact hm_nf
        set nfw := BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) f0 0)
        have hnfw_nat : nfw.toNat = nodeF s0 (hdr s0 t 5) f0 0 := by
          cases Fr1 with
          | nil =>
            simp only [FreeChainF] at hfc1
            dsimp only [nfw]
            rw [hfc1]; rfl
          | cons f1 Fr2 =>
            have hf1_eq : nodeF s0 (hdr s0 t 5) f0 0 = f1 := hfc1.1
            have hf1_mem : f1 ∈ A ++ (f0 :: f1 :: Fr2) := List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
            have := (hmem0 f1).mp hf1_mem
            dsimp only [nfw]
            rw [BitVec.toNat_ofNat, hf1_eq]; omega
        refine Ret.ns_storeW (tw + 72#64) nfw
          (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
                HolFiniteMapExact.lookup_update, FUPDATE, ht,
                show ofString "nf" ≠ ofString "t" by decide, show ofString "nodes" ≠ ofString "t" by decide,
                show ofString "f" ≠ ofString "t" by decide, valueIsWord, valueWord, wordOpHOL, wordOp])
          (by
            simp only [NS_memory, hm_nf']
            simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE]) ?_
        intro _
        apply Ret.ns_ret; intro val hval
        have hval_eq : val = .val (.word fw) := by
          simp [evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "nf" ≠ ofString "f" by decide, show ofString "nodes" ≠ ofString "f" by decide] at hval
          exact hval.symm
        subst hval_eq
        let s_a := NS s0 HolFiniteMapExact.empty s0.globals (updW s0.memory (tw + 72#64) nfw) s0.clock
        have htw72_eq : BitVec.ofNat 64 (t + 8 * 9) = tw + 72#64 := ofNat_add_toNat tw 72
        have hne_hdr : ∀ k < 11, k ≠ 9 → BitVec.ofNat 64 (t + 8 * k) ≠ tw + 72#64 := by
          intro k hk hne; rw [← htw72_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
        obtain ⟨hB_a', hfp_a'⟩ := htabBlocks_updW_nonlayout (tw + 72#64) nfw hB0
          (hne_hdr 0 (by omega) (by omega)) (hne_hdr 1 (by omega) (by omega))
          (hne_hdr 4 (by omega) (by omega)) (hne_hdr 5 (by omega) (by omega))
          (hne_hdr 6 (by omega) (by omega)) (hne_hdr 10 (by omega) (by omega))
          (fun h8 => absurd h8 (hne_hdr 8 (by omega) (by omega)))
        have hsep := htabBlocks_cell_sep hB0
        have hh5_a : hdr s_a t 5 = hdr s0 t 5 := memW_updW_other s0 _ _ _ (hne_hdr 5 (by omega) (by omega))
        have hh6_a : hdr s_a t 6 = hdr s0 t 6 := memW_updW_other s0 _ _ _ (hne_hdr 6 (by omega) (by omega))
        have hh8_a : hdr s_a t 8 = hdr s0 t 8 := memW_updW_other s0 _ _ _ (hne_hdr 8 (by omega) (by omega))
        have hh9_a : hdr s_a t 9 = nfw.toNat := by simp [hdr, memW, s_a, updW, htw72_eq]
        have hnd_same : ∀ n < hdr s0 t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
            nodeF s_a (hdr s0 t 5) n off = nodeF s0 (hdr s0 t 5) n off := by
          intro n hn off hoff; unfold nodeF; apply memW_updW_other s0; rw [← htw72_eq]
          exact (hsep.1 9 (by omega) n hn off hoff).symm
        have hord_same : ∀ i < hdr s0 t 10 + 1,
            memW s_a (hdr s0 t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
          intro i hi; apply memW_updW_other s0; rw [← htw72_eq]
          exact (hsep.2.1 9 (by omega) i hi).symm
        have hperm : List.Perm ((A ++ [f0]) ++ Fr1) (A ++ (f0 :: Fr1)) := by simp [List.append_assoc]
        have hnodup_a : ((A ++ [fw.toNat]) ++ Fr1).Nodup := by
          rw [hfw_nat]; exact hperm.nodup_iff.mpr hnodup0
        have hmem_a : ∀ x, x ∈ (A ++ [fw.toNat]) ++ Fr1 ↔ 1 ≤ x ∧ x < hdr s_a t 8 := by
          intro x; rw [hfw_nat, hh8_a, hperm.mem_iff]; exact hmem0 x
        have hfc_a : FreeChainF (nodeF s_a (hdr s_a t 5)) (hdr s_a t 9) Fr1 := by
          rw [hh5_a, hh9_a, hnfw_nat]
          refine FreeChainF.congr Fr1 _ ?_ hfc1
          intro x hx
          have hx_rng := (hmem0 x).mp (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
          exact hnd_same x (by omega) 0 (Or.inl rfl)
        have hfr_a : FrameOutside s0 s_a [(t, 88)] (globN s0 "heap_ptr", 0) := by
          have htw72_nat : (tw + 72#64).toNat = t + 72 := by rw [BitVec.toNat_add, show (72#64).toNat = 72 from rfl]; omega
          exact frameOutside_updW s0 (tw + 72#64) nfw [(t, 88)] _
            (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩)
        refine ⟨fw, Fr1, rfl, ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩,
          ⟨hB_a', hnodup_a, hmem_a, hfc_a⟩,
          memW_updW_other s0 _ _ _ (hne_hdr 0 (by omega) (by omega)),
          memW_updW_other s0 _ _ _ (hne_hdr 1 (by omega) (by omega)),
          memW_updW_other s0 _ _ _ (hne_hdr 3 (by omega) (by omega)),
          memW_updW_other s0 _ _ _ (hne_hdr 7 (by omega) (by omega)),
          (by change hdr s0 t 10 ≤ hdr { s0 with memory := updW s0.memory (tw + 72#64) nfw } t 10
              rw [show hdr { s0 with memory := updW s0.memory (tw + 72#64) nfw } t 10 = hdr s0 t 10 from memW_updW_other s0 _ _ _ (hne_hdr 10 (by omega) (by omega))]),
          ?_, ?_, le_rfl, ?_, ?_, fun _ _ => rfl⟩
        · intro x hxA off hoff; rw [hh5_a]
          have hx_rng := (hmem0 x).mp (List.mem_append_left _ hxA)
          exact hnd_same x (by omega) off hoff
        · intro i hi; rw [hh6_a]; exact hord_same i hi
        · change ∀ iv ∈ htabFootprint { s0 with memory := updW s0.memory (tw + 72#64) nfw } t, Allocated s0 iv ∧ _
          rw [hfp_a']; intro iv hiv; exact ⟨hal0 iv hiv, Or.inl ⟨iv, hiv, le_rfl, le_rfl⟩⟩
        · change FrameOutside s0 s_a [(t, 88)] (globN s0 "heap_ptr", globN s0 "heap_ptr" - globN s0 "heap_ptr")
          rw [Nat.sub_self]; exact hfr_a
      · exact fun u hu => False.elim (noFlow_dec (fun _ => noFlow_dec (fun _ => noFlow_seq_right (fun _ => noFlow_ret))) (congrArg Prod.fst hu))
  · -- CASE B: Free list is empty (`hdr s0 t 9 = 0`)!
    have hfree_z := hcw_spec.2 hcw_z
    have hFr0_nil : Fr0 = [] := by
      cases Fr0 with
      | nil => rfl
      | cons f0 Fr1 =>
        have hf0_eq : hdr s0 t 9 = f0 := hfc0.1
        have hf0_rng := (hmem0 f0).mp (List.mem_append_right _ List.mem_cons_self)
        omega
    subst hFr0_nil
    apply Ret.seq_skip
    -- 3. dec next := load(t + 64)
    apply Ret.ns_dec_lf hLF; intro vnx hvnx
    obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 64#64
      (by simp [HolFiniteMapExact.lookup_update, FUPDATE, ht, show ofString "f" ≠ ofString "t" by decide]) vnx hvnx
    have hm64 : s0.memory (tw + 64#64) = .word (BitVec.ofNat 64 (hdr s0 t 8)) := hm_t8
    simp only [NS_memory, hm64]
    set nxw := BitVec.ofNat 64 (hdr s0 t 8)
    have hnxw_nat : nxw.toNat = hdr s0 t 8 := by rw [BitVec.toNat_ofNat]; omega
    -- 4. seq (ite (load(t + 80) < next) (call htab_grow(t)) skip) (...)
    apply Ret.seq_ite
    intro cw2 hcw2
    have hcw2_spec : (cw2 ≠ 0 → hdr s0 t 10 < hdr s0 t 8) ∧ (cw2 = 0 → hdr s0 t 8 ≤ hdr s0 t 10) := by
      obtain ⟨va, vb, hva, hvb, hcw2_eq⟩ := evalAt_cmp _ .lower _ _ cw2 hcw2
      obtain ⟨_, hva_mem⟩ := ev_field_load _ (ofString "t") tw 80#64
        (by simp [HolFiniteMapExact.lookup_update, FUPDATE, ht,
          show ofString "next" ≠ ofString "t" by decide, show ofString "f" ≠ ofString "t" by decide]) (.val (.word va)) hva
      have hm80 : s0.memory (tw + 80#64) = .word (BitVec.ofNat 64 (hdr s0 t 10)) := hm_t10
      simp only [NS_memory, hm80, ValueHOL.val.injEq, HolWordLab.word.injEq] at hva_mem
      subst hva_mem
      simp [evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE] at hvb
      subst hvb
      have hnc_nat : (BitVec.ofNat 64 (hdr s0 t 10)).toNat = hdr s0 t 10 := by rw [BitVec.toNat_ofNat]; omega
      constructor
      · intro hnz; by_contra hge
        have hnlt : ¬ (BitVec.ofNat 64 (hdr s0 t 10) < nxw) := by rw [BitVec.lt_def, hnc_nat, hnxw_nat]; omega
        simp [Compiler.Encoders.Asm.wordCmpHOL, hnlt] at hcw2_eq; exact hnz hcw2_eq
      · intro hz; by_contra hlt
        have hlt_bv : BitVec.ofNat 64 (hdr s0 t 10) < nxw := by rw [BitVec.lt_def, hnc_nat, hnxw_nat]; omega
        simp [Compiler.Encoders.Asm.wordCmpHOL, hlt_bv] at hcw2_eq; rw [hz] at hcw2_eq; exact absurd hcw2_eq (by decide)
    have finish_bump : ∀ (sm : PanSemStateFiniteExact 64 F),
        sm.locals.lookup (ofString "t") = some (.val (.word tw)) →
        ArenaReady sm → HtabBlocks sm t →
        hdr sm t 0 = hdr s0 t 0 → hdr sm t 1 = hdr s0 t 1 → hdr sm t 3 = hdr s0 t 3 →
        hdr sm t 7 = hdr s0 t 7 → hdr sm t 8 = hdr s0 t 8 → hdr sm t 9 = 0 →
        hdr s0 t 10 ≤ hdr sm t 10 → hdr sm t 8 ≤ hdr sm t 10 →
        (∀ x ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
          nodeF sm (hdr sm t 5) x off = nodeF s0 (hdr s0 t 5) x off) →
        (∀ i, i < hdr s0 t 10 + 1 →
          memW sm (hdr sm t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i)) →
        globN s0 "heap_ptr" ≤ globN sm "heap_ptr" →
        (∀ i ∈ htabFootprint sm t, Allocated sm i ∧
          ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨
            Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN sm "heap_ptr" - globN s0 "heap_ptr")))) →
        FrameOutside s0 sm [(t, 88)] (globN s0 "heap_ptr", globN sm "heap_ptr" - globN s0 "heap_ptr") →
        (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
          s0.globals.lookup k = sm.globals.lookup k) →
        Ret sm
          (.dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "t"), .const 64#64]))
            (.seq
              (.store (.op .add [.var .local (ofString "t"), .const 64#64])
                (.op .add [.var .local (ofString "n"), .const 1#64]))
              (.return (.var .local (ofString "n")))))
          (NewNodePost s0 t A) := by
      intro sm ht_sm hAm hBm hh0m hh1m hh3m hh7m hh8m hh9m hnc_le hnx_lt_nc hnd_m hord_m hhp_m hfp_m hfr_m hg_m
      obtain ⟨hncap_m_lt, _, _, _, _, _, _⟩ := htabBlocks_bounds hBm
      obtain ⟨_, hm64_sm⟩ := word_of_hdr sm tw 8 (by omega) hBm
      have hm64_sm' : sm.memory (tw + 64#64) = .word nxw := by rw [hh8m] at hm64_sm; exact hm64_sm
      apply Ret.of_NS
      apply Ret.ns_dec_lf hLF; intro vn hvn
      obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 64#64 ht_sm vn hvn
      simp only [NS_memory, hm64_sm']
      have hnx1_eq : nxw + (1#64 + (0 : BitVec 64)) = BitVec.ofNat 64 (hdr s0 t 8 + 1) := by
        apply BitVec.eq_of_toNat_eq
        have h10 : 1#64 + (0 : BitVec 64) = 1#64 := rfl
        have hlt_nx1 : hdr s0 t 8 + 1 < 2 ^ 64 := by omega
        rw [h10, BitVec.toNat_add, hnxw_nat, show (1#64 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hlt_nx1]
      refine Ret.ns_storeW (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1))
        (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
              HolFiniteMapExact.lookup_update, FUPDATE, ht_sm,
              show ofString "n" ≠ ofString "t" by decide, valueIsWord, valueWord, wordOpHOL, wordOp])
        (by
          have hn_lk : (sm.locals.update (ofString "n", .val (.word nxw))).lookup (ofString "n") = some (.val (.word nxw)) := by
            simp [HolFiniteMapExact.lookup_update, FUPDATE]
          simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
            hn_lk, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
            valueIsWord, valueWord, wordOpHOL, wordOp, hnx1_eq]) ?_
      intro _
      apply Ret.ns_ret; intro val hval
      have hval_eq : val = .val (.word nxw) := by
        simp [evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE] at hval; exact hval.symm
      subst hval_eq
      let s_b := NS sm HolFiniteMapExact.empty sm.globals (updW sm.memory (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1))) sm.clock
      have htw64_eq : BitVec.ofNat 64 (t + 8 * 8) = tw + 64#64 := ofNat_add_toNat tw 64
      have hne_hdr : ∀ k < 11, k ≠ 8 → BitVec.ofNat 64 (t + 8 * k) ≠ tw + 64#64 := by
        intro k hk hne; rw [← htw64_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
      have hw_nx1_nat : (BitVec.ofNat 64 (hdr s0 t 8 + 1)).toNat = hdr s0 t 8 + 1 := by rw [BitVec.toNat_ofNat]; omega
      obtain ⟨hB_b', hfp_b'⟩ := htabBlocks_updW_nonlayout (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1)) hBm
        (hne_hdr 0 (by omega) (by omega)) (hne_hdr 1 (by omega) (by omega))
        (hne_hdr 4 (by omega) (by omega)) (hne_hdr 5 (by omega) (by omega))
        (hne_hdr 6 (by omega) (by omega)) (hne_hdr 10 (by omega) (by omega))
        (fun _ => by rw [hw_nx1_nat]; omega)
      have hsep_m := htabBlocks_cell_sep hBm
      have hh5_b : hdr s_b t 5 = hdr sm t 5 := memW_updW_other sm _ _ _ (hne_hdr 5 (by omega) (by omega))
      have hh6_b : hdr s_b t 6 = hdr sm t 6 := memW_updW_other sm _ _ _ (hne_hdr 6 (by omega) (by omega))
      have hh8_b : hdr s_b t 8 = hdr s0 t 8 + 1 := by
        change memW { sm with memory := updW sm.memory (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1)) } (t + 8 * 8) = hdr s0 t 8 + 1
        unfold memW
        rw [htw64_eq]
        simp only [updW, ↓reduceIte, hw_nx1_nat]
      have hh9_b : hdr s_b t 9 = 0 := (memW_updW_other sm _ _ _ (hne_hdr 9 (by omega) (by omega))).trans hh9m
      have hnx_not_A : hdr s0 t 8 ∉ A := by
        intro hmemA; have := (hmem0 (hdr s0 t 8)).mp (by simpa using hmemA); omega
      have hnodup_b : ((A ++ [nxw.toNat]) ++ ([] : List Nat)).Nodup := by
        rw [List.append_nil, hnxw_nat, List.nodup_append]
        have hndA : A.Nodup := by simpa using hnodup0
        exact ⟨hndA, List.nodup_singleton _, fun x hx y hy hxy => by simp at hy; subst hy; subst hxy; exact hnx_not_A hx⟩
      have hmem_b : ∀ x, x ∈ (A ++ [nxw.toNat]) ++ ([] : List Nat) ↔ 1 ≤ x ∧ x < hdr s_b t 8 := by
        intro x
        rw [List.append_nil, hnxw_nat, hh8_b, List.mem_append, List.mem_singleton]
        have hx0 := hmem0 x; rw [List.append_nil] at hx0
        constructor
        · rintro (hxA | rfl)
          · have := hx0.mp hxA; omega
          · omega
        · intro ⟨h1, h2⟩
          by_cases heq : x = hdr s0 t 8
          · exact Or.inr heq
          · exact Or.inl (hx0.mpr ⟨h1, by omega⟩)
      have hfc_b : FreeChainF (nodeF s_b (hdr s_b t 5)) (hdr s_b t 9) [] := hh9_b
      have hfr_b : FrameOutside s0 s_b [(t, 88)] (globN s0 "heap_ptr", globN sm "heap_ptr" - globN s0 "heap_ptr") := by
        have htw64_nat : (tw + 64#64).toNat = t + 64 := by rw [BitVec.toNat_add, show (64#64).toNat = 64 from rfl]; omega
        exact frameOutside_trans_same hfr_m
          (frameOutside_updW sm (tw + 64#64) _ [(t, 88)] _
            (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
      refine ⟨nxw, [], rfl, ⟨guestInv_congr (s := sm) rfl rfl rfl rfl hAm.1, hAm.2⟩,
        ⟨hB_b', hnodup_b, hmem_b, hfc_b⟩,
        (memW_updW_other sm _ _ _ (hne_hdr 0 (by omega) (by omega))).trans hh0m,
        (memW_updW_other sm _ _ _ (hne_hdr 1 (by omega) (by omega))).trans hh1m,
        (memW_updW_other sm _ _ _ (hne_hdr 3 (by omega) (by omega))).trans hh3m,
        (memW_updW_other sm _ _ _ (hne_hdr 7 (by omega) (by omega))).trans hh7m,
        (by change hdr s0 t 10 ≤ hdr { sm with memory := updW sm.memory (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1)) } t 10
            rw [show hdr { sm with memory := updW sm.memory (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1)) } t 10 = hdr sm t 10 from memW_updW_other sm _ _ _ (hne_hdr 10 (by omega) (by omega))]; exact hnc_le),
        ?_, ?_, hhp_m, ?_, hfr_b, hg_m⟩
      · intro x hxA off hoff; rw [hh5_b]
        have hx_rng := (hmem0 x).mp (by simpa using hxA)
        have h1 : nodeF s_b (hdr sm t 5) x off = nodeF sm (hdr sm t 5) x off := by
          unfold nodeF; apply memW_updW_other sm; rw [← htw64_eq]
          exact (hsep_m.1 8 (by omega) x (by omega) off hoff).symm
        exact h1.trans (hnd_m x hxA off hoff)
      · intro i hi; rw [hh6_b]
        have h1 : memW s_b (hdr sm t 6 + 8 * i) = memW sm (hdr sm t 6 + 8 * i) := by
          apply memW_updW_other sm; rw [← htw64_eq]
          exact (hsep_m.2.1 8 (by omega) i (by omega)).symm
        exact h1.trans (hord_m i hi)
      · change ∀ iv ∈ htabFootprint { sm with memory := updW sm.memory (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1)) } t, Allocated sm iv ∧ _
        rw [hfp_b']; exact hfp_m
    refine ⟨fun hcw2_nz => ?_, fun hcw2_z => ?_⟩
    · have hlt_nc := hcw2_spec.1 hcw2_nz
      have hnx_eq : hdr s0 t 8 = hdr s0 t 10 + 1 := by omega
      let s_pre := NS s0 ((s0.locals.update (ofString "f", .val (.word fw))).update (ofString "next", .val (.word nxw))) s0.globals s0.memory s0.clock
      have ht_pre : s_pre.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_pre, HolFiniteMapExact.lookup_update, FUPDATE, ht,
          show ofString "next" ≠ ofString "t" by decide, show ofString "f" ≠ ofString "t" by decide]
      refine Ret.seq_call1 (s := s_pre) hA0.1.code lookup_htab_grow tw
        (by simp [evalAt, evalHOLExact, ht_pre]) ?_
      intro wg gpost hgrow_run
      let gentry := callEntryStateHOLFinite s_pre (HolFiniteMapExact.empty.update (ofString "t", .val (.word tw)))
      have hg_spec := htab_grow_body_spec gentry tw
        (by simp [gentry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩ hB0 hal0
        (.val (.word wg)) (by rw [hgrow_run])
      rw [hgrow_run] at hg_spec
      obtain ⟨_, hAg, hBg, hh0g, hh1g, hh3g, hh7g, hh8g, hh9g, hh10g, hnd_g, hord_g, hhp_g, hfp_g, hfr_g, hg_g⟩ := hg_spec
      let sm := { gpost with locals := s_pre.locals }
      have hnc2 : 2 ≤ hdr s0 t 10 := hB0.2.2.2.2.2.1
      have hh10g' : hdr gpost t 10 = 2 * hdr s0 t 10 := hh10g
      have hh8g' : hdr gpost t 8 = hdr s0 t 8 := hh8g
      exact finish_bump sm ht_pre
        ⟨guestInv_congr (s := gpost) rfl rfl rfl rfl hAg.1, hAg.2⟩ hBg
        hh0g hh1g hh3g hh7g hh8g (hh9g.trans hfree_z)
        (by change hdr s0 t 10 ≤ hdr gpost t 10; rw [hh10g']; omega)
        (by change hdr gpost t 8 ≤ hdr gpost t 10; rw [hh8g', hh10g']; omega)
        (fun x hxA off hoff => by
          have hx_rng := (hmem0 x).mp (by simpa using hxA)
          have hlt_x : x < hdr s0 t 10 + 1 := by omega
          exact hnd_g x hlt_x off hoff)
        hord_g hhp_g hfp_g hfr_g hg_g
    · have hle_nc := hcw2_spec.2 hcw2_z
      apply Ret.seq_skip
      let s_pre := NS s0 ((s0.locals.update (ofString "f", .val (.word fw))).update (ofString "next", .val (.word nxw))) s0.globals s0.memory s0.clock
      have ht_pre : s_pre.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_pre, HolFiniteMapExact.lookup_update, FUPDATE, ht,
          show ofString "next" ≠ ofString "t" by decide, show ofString "f" ≠ ofString "t" by decide]
      exact finish_bump s_pre ht_pre
        ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩ hB0
        rfl rfl rfl rfl rfl hfree_z le_rfl hle_nc
        (fun _ _ _ _ => rfl) (fun _ _ => rfl) le_rfl
        (fun iv hiv => ⟨hal0 iv hiv, Or.inl ⟨iv, hiv, le_rfl, le_rfl⟩⟩)
        (fun _ _ _ => rfl) (fun _ _ => rfl)

/-- `Ret.decCall_new_node_lf`: call `htab_new_node(t)` under `LocFreePost Φ`! -/
theorem Ret.decCall_new_node_lf {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {x : MlS} {et : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (tw : BitVec 64) (A Fr0 : List Nat)
    (het : evalAt s0 et = some (.val (.word tw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i)
    (hk : ∀ (nw : BitVec 64) (Fr1 : List Nat) (s1 : PanSemStateFiniteExact 64 F),
      ArenaReady s1 →
      NodeState s1 tw.toNat (A ++ [nw.toNat]) Fr1 →
      hdr s1 tw.toNat 0 = hdr s0 tw.toNat 0 →
      hdr s1 tw.toNat 1 = hdr s0 tw.toNat 1 →
      hdr s1 tw.toNat 3 = hdr s0 tw.toNat 3 →
      hdr s1 tw.toNat 7 = hdr s0 tw.toNat 7 →
      hdr s0 tw.toNat 10 ≤ hdr s1 tw.toNat 10 →
      (∀ z ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        nodeF s1 (hdr s1 tw.toNat 5) z off = nodeF s0 (hdr s0 tw.toNat 5) z off) →
      (∀ i, i < hdr s0 tw.toNat 10 + 1 →
        memW s1 (hdr s1 tw.toNat 6 + 8 * i) = memW s0 (hdr s0 tw.toNat 6 + 8 * i)) →
      globN s0 "heap_ptr" ≤ globN s1 "heap_ptr" →
      (∀ i ∈ htabFootprint s1 tw.toNat, Allocated s1 i ∧
        ((∃ j ∈ htabFootprint s0 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
          Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s1 "heap_ptr" - globN s0 "heap_ptr")))) →
      FrameOutside s0 s1 [(tw.toNat, 88)] (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") →
      (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
        s0.globals.lookup k = s1.globals.lookup k) →
      s1.locals = s0.locals →
      Ret (setVarHOLFinite x (.val (.word nw)) s1) cont Φ) :
    Ret s0 (.decCall x .one (ofString "htab_new_node") [et] cont) Φ := by
  refine Ret.decCall1_lf hLF hA0.1.code lookup_htab_new_node tw het ?_
  intro nw post hrun
  let entry := callEntryStateHOLFinite s0 (HolFiniteMapExact.empty.update (ofString "t", .val (.word tw)))
  have hspec := htab_new_node_body_spec entry tw A Fr0
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩ hNS0 hal0
    (.val (.word nw)) (by rw [hrun])
  rw [hrun] at hspec
  obtain ⟨nw', Fr1, hnw_eq, hAp, hNSp, hh0, hh1, hh3, hh7, hnc_le, hnd, hord, hhp, hfp, hfr, hg⟩ := hspec
  injection hnw_eq with h1; injection h1 with h2; subst h2
  let s1 := { post with locals := s0.locals }
  exact hk nw Fr1 s1
    ⟨guestInv_congr (s := post) rfl rfl rfl rfl hAp.1, hAp.2⟩
    hNSp hh0 hh1 hh3 hh7 hnc_le hnd hord hhp hfp hfr hg rfl

end InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

/-! ### From SoloHtabSetLeafInt.lean -/

/-! Semantic specs for `htab_new_leaf` and `htab_new_internal`. -/


namespace InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem Ret.dec_lf {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (h : ∀ val, evalAt s init = some val → Ret (setVarHOLFinite x val s) body Φ) :
    Ret s (.dec x sh init body) Φ :=
  Ret.dec fun val hval v hv => hLF v _ _ (h val hval v hv)

theorem ev_order_addr {F : Type} (st : PanSemStateFiniteExact 64 F) (tw posw ow : BitVec 64)
    (ht : st.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hp : st.locals.lookup (ofString "pos") = some (.val (.word posw)))
    (hdom : st.memaddrs (tw + 48#64))
    (hm : st.memory (tw + 48#64) = .word ow) :
    evalAt st (.op .add [.load .one (.op .add [.var .local (ofString "t"), .const 48#64]),
      .panop .mul [.var .local (ofString "pos"), .const 8#64]]) =
      some (.val (.word (ow + (posw * 8#64 + (0 : BitVec 64))))) := by
  simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht, hp,
    isWfShapeExactHOL, memLoadHOLExact, hdom, hm, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]

theorem frameOutside_updW_mem {F : Type} (s s' : PanSemStateFiniteExact 64 F)
    (m1 : BitVec 64 → HolWordLab 64)
    (hm1 : s'.memory = m1)
    (a w : BitVec 64) (keep : List Ivl) (fresh : Ivl)
    (hprev : FrameOutside s s' keep fresh)
    (ha : (∃ i ∈ keep, CellHits a.toNat i) ∨ CellHits a.toNat fresh)
    (s'' : PanSemStateFiniteExact 64 F) (hm2 : s''.memory = updW m1 a w) :
    FrameOutside s s'' keep fresh := by
  intro x hx hfresh
  rw [hm2]
  by_cases hxa : x = a
  · subst x; exfalso
    rcases ha with ⟨i, hi, hhit⟩ | hhit
    · exact hx i hi hhit
    · exact hfresh hhit
  · simp only [updW, hxa, ↓reduceIte, ← hm1]
    exact hprev x hx hfresh

/-! ## 1. `htab_new_leaf` Postcondition -/

def NewLeafPost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat) (valw : BitVec 64)
    (A : List Nat) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) : Prop :=
  let fresh : Ivl := (globN s0 "heap_ptr", globN post "heap_ptr" - globN s0 "heap_ptr")
  ∃ nl : BitVec 64, ∃ Fr1 : List Nat,
    v = .val (.word nl) ∧
    ArenaReady post ∧
    NodeState post t (A ++ [nl.toNat]) Fr1 ∧
    hdr post t 0 = hdr s0 t 0 ∧
    hdr post t 1 = hdr s0 t 1 ∧
    hdr post t 3 = hdr s0 t 3 + 1 ∧
    hdr post t 7 = hdr s0 t 7 ∧
    nodeF post (hdr post t 5) nl.toNat 0 = 0 ∧
    nodeF post (hdr post t 5) nl.toNat 8 = valw.toNat ∧
    nodeF post (hdr post t 5) nl.toNat 16 = hdr s0 t 3 ∧
    nodeF post (hdr post t 5) nl.toNat 24 = 8 * hdr s0 t 0 ∧
    memW post (hdr post t 6 + 8 * hdr s0 t 3) = nl.toNat ∧
    (∀ x ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF post (hdr post t 5) x off = nodeF s0 (hdr s0 t 5) x off) ∧
    (∀ i, i < hdr s0 t 3 →
      memW post (hdr post t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i)) ∧
    globN s0 "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i ∧
      ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
    FrameOutside s0 post (htabFootprint s0 t) fresh ∧
    (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s0.globals.lookup k = post.globals.lookup k)

theorem locFree_newLeafPost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat)
    (valw : BitVec 64) (A : List Nat) :
    LocFreePost (NewLeafPost s0 t valw A) := by
  intro v p L' h
  obtain ⟨nl, Fr1, hv, hA, hNS, c0, c1, c3, c7, n0, n8, n16, n24, ordc, cnd, cord, chp, cfp, cfr, cg⟩ := h
  exact ⟨nl, Fr1, hv, ⟨guestInv_congr (s := { p with locals := L' }) rfl rfl rfl rfl hA.1, hA.2⟩,
    hNS, c0, c1, c3, c7, n0, n8, n16, n24, ordc, cnd, cord, chp, cfp, cfr, cg⟩

theorem htab_new_leaf_body_spec {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (tw keyw valw : BitVec 64) (A Fr0 : List Nat)
    (ht : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey : s0.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hval : s0.locals.lookup (ofString "value") = some (.val (.word valw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hcnt_le : hdr s0 tw.toNat 3 ≤ A.length)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_new_leaf)
      (NewLeafPost s0 tw.toNat valw A) := by
  set t := tw.toNat
  have hLF := locFree_newLeafPost s0 t valw A
  set cnt := hdr s0 t 3
  set klen := hdr s0 t 0
  set stride := hdr s0 t 1
  have hA_len : A.length ≤ hdr s0 t 10 := by
    have hndA : A.Nodup := (List.nodup_append.mp hNS0.2.1).1
    have hle := nodup_len_le_range hndA (fun x hx => (hNS0.2.2.1 x).mp (List.mem_append_left _ hx))
    have := hNS0.1.2.2.2.2.2.2
    omega
  have hcnt_le_nc0 : cnt ≤ hdr s0 t 10 := le_trans hcnt_le hA_len
  htab_unfold Guest.Software.guestFn_htab_new_leaf
  -- 1. decCall n := htab_new_node(t)
  refine Ret.decCall_new_node_lf hLF tw A Fr0 (by simp [evalAt, evalHOLExact, ht]) hA0 hNS0 hal0 ?_
  intro nlw Fr1 s1 hA1 hNS1 hh0_1 hh1_1 hh3_1 hh7_1 hnc_le_1 hnd_1 hord_1 hhp_1 hfp_1 hfr_1 hg_1 hloc_1
  change NodeState s1 t (A ++ [nlw.toNat]) Fr1 at hNS1
  change hdr s1 t 0 = hdr s0 t 0 at hh0_1
  change hdr s1 t 1 = hdr s0 t 1 at hh1_1
  change hdr s1 t 3 = hdr s0 t 3 at hh3_1
  change hdr s1 t 7 = hdr s0 t 7 at hh7_1
  change hdr s0 t 10 ≤ hdr s1 t 10 at hnc_le_1
  obtain ⟨hB1, hnodup1, hmem1, hfc1⟩ := hNS1
  obtain ⟨hnc1_lt, hst1_ge8, hst1_le64, hst1_al, ht_lo, ht_hi, ht_al⟩ := htabBlocks_bounds hB1
  have hnx1_le : hdr s1 t 8 ≤ hdr s1 t 10 + 1 := hB1.2.2.2.2.2.2.2
  have hnl_rng : 1 ≤ nlw.toNat ∧ nlw.toNat < hdr s1 t 8 :=
    (hmem1 nlw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  have hnl_lt_nc1 : nlw.toNat < hdr s1 t 10 + 1 := by omega
  have hcnt_lt_nc1 : cnt < hdr s1 t 10 + 1 := by
    have hndAnl : (A ++ [nlw.toNat]).Nodup := (List.nodup_append.mp hnodup1).1
    have hle := nodup_len_le_range hndAnl (fun x hx => (hmem1 x).mp (List.mem_append_left _ hx))
    rw [List.length_append, List.length_singleton] at hle
    have : cnt ≤ A.length := hcnt_le
    omega
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom1_t0, hm1_t0⟩ := word_of_hdr s1 tw 0 (by omega) hB1
  obtain ⟨hdom1_t1, hm1_t1⟩ := word_of_hdr s1 tw 1 (by omega) hB1
  obtain ⟨hdom1_t3, hm1_t3⟩ := word_of_hdr s1 tw 3 (by omega) hB1
  obtain ⟨hdom1_t4, hm1_t4⟩ := word_of_hdr s1 tw 4 (by omega) hB1
  obtain ⟨hdom1_t5, hm1_t5⟩ := word_of_hdr s1 tw 5 (by omega) hB1
  obtain ⟨hdom1_t6, hm1_t6⟩ := word_of_hdr s1 tw 6 (by omega) hB1
  -- 2. dec klen := load(t + 0)
  apply Ret.dec_lf hLF; intro vkl hvkl
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 0#64
    (by simp [setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "n" ≠ ofString "t" by decide]) vkl hvkl
  have hm0 : (setVarHOLFinite (ofString "n") (.val (.word nlw)) s1).memory (tw + 0#64) = .word (BitVec.ofNat 64 klen) := by
    change s1.memory (tw + BitVec.ofNat 64 (8 * 0)) = .word (BitVec.ofNat 64 (hdr s0 tw.toNat 0))
    rw [← hh0_1]; exact hm1_t0
  rw [hm0]
  -- 3. dec stride := load(t + 8)
  apply Ret.dec_lf hLF; intro vst hvst
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 8#64
    (by simp [setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "klen" ≠ ofString "t" by decide, show ofString "n" ≠ ofString "t" by decide]) vst hvst
  have hm8 : (setVarHOLFinite (ofString "klen") (.val (.word (BitVec.ofNat 64 klen)))
      (setVarHOLFinite (ofString "n") (.val (.word nlw)) s1)).memory (tw + 8#64) = .word (BitVec.ofNat 64 stride) := by
    change s1.memory (tw + BitVec.ofNat 64 (8 * 1)) = .word (BitVec.ofNat 64 (hdr s0 tw.toNat 1))
    rw [← hh1_1]; exact hm1_t1
  rw [hm8]
  -- 4. call memcpy(load(t + 32) + n * stride, key, klen)
  let L1_3 : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((s1.locals.update (ofString "n", .val (.word nlw))).update
      (ofString "klen", .val (.word (BitVec.ofNat 64 klen)))).update
      (ofString "stride", .val (.word (BitVec.ofNat 64 stride)))
  let s1_3 : PanSemStateFiniteExact 64 F := { s1 with locals := L1_3 }
  change Ret s1_3 _ _
  have hkeys1_in := (hB1.1 (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) (by simp [htabFootprint])).1
  change hdr s1 t 4 ≥ sourceBase ∧ hdr s1 t 4 + (hdr s1 t 10 + 1) * hdr s1 t 1 ≤ heapEnd at hkeys1_in
  have hklen_le_st : klen ≤ stride := by have := hNS0.1.2.2.2.2.1; dsimp [klen, stride]; omega
  have hklen_le60 : klen ≤ 60 := hNS0.1.2.2.2.1
  have hh1_1_t : hdr s1 t 1 = stride := hh1_1
  have hmul_le_nl : nlw.toNat * stride + stride ≤ (hdr s1 t 10 + 1) * stride := by
    have h1 : (nlw.toNat + 1) * stride ≤ (hdr s1 t 10 + 1) * stride := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    exact h1
  have hkeys1_hi : hdr s1 t 4 + (hdr s1 t 10 + 1) * stride ≤ heapEnd := by
    rw [← hh1_1_t]; exact hkeys1_in.2
  have hst_le64_0 : stride ≤ 64 := by rw [← hh1_1_t]; exact hst1_le64
  set dst_k := BitVec.ofNat 64 (hdr s1 t 4 + nlw.toNat * stride)
  have hdst_k_nat : dst_k.toNat = hdr s1 t 4 + nlw.toNat * stride := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have he_md : evalAt s1_3 (.op .add [.load .one (.op .add [.var .local (ofString "t"), .const 32#64]),
      .panop .mul [.var .local (ofString "n"), .var .local (ofString "stride")]]) =
      some (.val (.word dst_k)) := by
    have ht_l : s1_3.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [s1_3, L1_3, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
        show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide,
        show ofString "n" ≠ ofString "t" by decide]
    have hn_l : s1_3.locals.lookup (ofString "n") = some (.val (.word nlw)) := by
      simp [s1_3, L1_3, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "stride" ≠ ofString "n" by decide, show ofString "klen" ≠ ofString "n" by decide]
    have hst_l : s1_3.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 stride))) := by
      simp [s1_3, L1_3, HolFiniteMapExact.lookup_update, FUPDATE]
    have h320 : 32#64 + (0 : BitVec 64) = 32#64 := rfl
    have hdom32 : s1_3.memaddrs (tw + 32#64) := hdom1_t4
    have hm32 : s1_3.memory (tw + 32#64) = .word (BitVec.ofNat 64 (hdr s1 t 4)) := hm1_t4
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
      ht_l, hn_l, hst_l, h320, hdom32, hm32, isWfShapeExactHOL, memLoadHOLExact,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hst_mod : (BitVec.ofNat 64 stride).toNat = stride := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hmul_mod : (nlw * BitVec.ofNat 64 stride).toNat = nlw.toNat * stride := by
      rw [BitVec.toNat_mul, hst_mod, Nat.mod_eq_of_lt (by omega)]
    have h4_mod : (BitVec.ofNat 64 (hdr s1 t 4)).toNat = hdr s1 t 4 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hz : nlw * BitVec.ofNat 64 stride + (0 : BitVec 64) = nlw * BitVec.ofNat 64 stride := BitVec.add_zero _
    rw [hz, BitVec.toNat_add, h4_mod, hmul_mod, hdst_k_nat, Nat.mod_eq_of_lt (by omega)]
  have he_ms : evalAt s1_3 (.var .local (ofString "key")) = some (.val (.word keyw)) := by
    simp [s1_3, L1_3, hloc_1, evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hkey,
      show ofString "stride" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide,
      show ofString "n" ≠ ofString "key" by decide]
  have he_mn : evalAt s1_3 (.var .local (ofString "klen")) = some (.val (.word (BitVec.ofNat 64 klen))) := by
    simp [s1_3, L1_3, evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "stride" ≠ ofString "klen" by decide]
  have hwklen : (BitVec.ofNat 64 klen).toNat = klen := by rw [BitVec.toNat_ofNat]; omega
  refine Ret.seq_memcpy_frame (s := s1_3) ⟨guestInv_congr (s := s1) rfl rfl rfl rfl hA1.1, hA1.2⟩
    dst_k keyw (BitVec.ofNat 64 klen)
    (by rw [hdst_k_nat, hwklen]; omega)
    (by rw [hwklen]; omega)
    he_md he_ms he_mn ?_
  intro s2 hA2 hmcf_k hloc2
  have hpair1 := hB1.2.1
  simp only [htabFootprint, List.pairwise_cons, List.mem_cons] at hpair1
  have hd1_tk : Disj (t, 88) (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) := hpair1.1 _ (Or.inl rfl)
  have hd1_kn : Disj (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) := hpair1.2.1 _ (Or.inl rfl)
  have hd1_ko : Disj (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) (hdr s1 t 6, (hdr s1 t 10 + 1) * 8) := hpair1.2.1 _ (Or.inr (Or.inl rfl))
  have hsub_keys : Inside (dst_k.toNat, (BitVec.ofNat 64 klen).toNat) (hdr s1 t 4) (hdr s1 t 4 + (hdr s1 t 10 + 1) * hdr s1 t 1) := by
    rw [hdst_k_nat, hwklen, hh1_1_t]
    exact ⟨by omega, by omega⟩
  have hdr_s2_eq : ∀ k < 11, hdr s2 t k = hdr s1 t k := by
    intro k hk
    unfold hdr
    apply memW_eq_of_frame_disj hmcf_k.2.2.2.2.2.2 (by omega)
    have h1 := hsub_keys.1; have h2 := hsub_keys.2
    rcases hd1_tk with hz | hz | hle | hle
    · cases hz
    · rw [hh1_1_t] at hz; have : 0 < (hdr s1 t 10 + 1) * stride := Nat.mul_pos (by omega) (by omega); omega
    · exact Or.inl (by change t + 88 ≤ hdr s1 t 4 at hle; omega)
    · exact Or.inr (by change hdr s1 t 4 + (hdr s1 t 10 + 1) * hdr s1 t 1 ≤ t at hle; omega)
  have hnd_s2_eq : ∀ n < hdr s1 t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s2 (hdr s1 t 5) n off = nodeF s1 (hdr s1 t 5) n off := by
    intro n hn off hoff
    have hnd1_in := (hB1.1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd1_in
    unfold nodeF
    apply memW_eq_of_frame_disj hmcf_k.2.2.2.2.2.2 (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)
    have h1 := hsub_keys.1; have h2 := hsub_keys.2
    rcases hd1_kn with hz | hz | hle | hle
    · rw [hh1_1_t] at hz; have : 0 < (hdr s1 t 10 + 1) * stride := Nat.mul_pos (by omega) (by omega); omega
    · omega
    · exact Or.inr (by change hdr s1 t 4 + (hdr s1 t 10 + 1) * hdr s1 t 1 ≤ hdr s1 t 5 at hle; rcases hoff with rfl | rfl | rfl | rfl <;> omega)
    · exact Or.inl (by change hdr s1 t 5 + (hdr s1 t 10 + 1) * 32 ≤ hdr s1 t 4 at hle; rcases hoff with rfl | rfl | rfl | rfl <;> omega)
  have hord_s2_eq : ∀ i < hdr s1 t 10 + 1,
      memW s2 (hdr s1 t 6 + 8 * i) = memW s1 (hdr s1 t 6 + 8 * i) := by
    intro i hi
    have hord1_in := (hB1.1 (hdr s1 t 6, (hdr s1 t 10 + 1) * 8) (by simp [htabFootprint])).1
    unfold Inside at hord1_in
    apply memW_eq_of_frame_disj hmcf_k.2.2.2.2.2.2 (by omega)
    have h1 := hsub_keys.1; have h2 := hsub_keys.2
    rcases hd1_ko with hz | hz | hle | hle
    · rw [hh1_1_t] at hz; have : 0 < (hdr s1 t 10 + 1) * stride := Nat.mul_pos (by omega) (by omega); omega
    · omega
    · exact Or.inr (by change hdr s1 t 4 + (hdr s1 t 10 + 1) * hdr s1 t 1 ≤ hdr s1 t 6 at hle; omega)
    · exact Or.inl (by change hdr s1 t 6 + (hdr s1 t 10 + 1) * 8 ≤ hdr s1 t 4 at hle; omega)
  have hfp_s2 : htabFootprint s2 t = htabFootprint s1 t := by
    simp [htabFootprint, hdr_s2_eq 1 (by omega), hdr_s2_eq 4 (by omega), hdr_s2_eq 5 (by omega), hdr_s2_eq 6 (by omega), hdr_s2_eq 10 (by omega)]
  have hB2 : HtabBlocks s2 t := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro iv hiv
      rw [hfp_s2] at hiv
      obtain ⟨hin, hwok⟩ := hB1.1 iv hiv
      exact ⟨hin, wordsOK_block s2 hA2.1.memaddrs iv.1 iv.2 hwok.1 hwok.2.1 hin.1 hin.2⟩
    · rw [hfp_s2]; exact hB1.2.1
    · rw [hdr_s2_eq 0 (by omega)]; exact hB1.2.2.1
    · rw [hdr_s2_eq 0 (by omega)]; exact hB1.2.2.2.1
    · rw [hdr_s2_eq 1 (by omega), hdr_s2_eq 0 (by omega)]; exact hB1.2.2.2.2.1
    · rw [hdr_s2_eq 10 (by omega)]; exact hB1.2.2.2.2.2.1
    · rw [hdr_s2_eq 8 (by omega)]; exact hB1.2.2.2.2.2.2.1
    · rw [hdr_s2_eq 8 (by omega), hdr_s2_eq 10 (by omega)]; exact hB1.2.2.2.2.2.2.2
  have hfr_s0_s2 : FrameOutside s0 s2 (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
    intro x hxk hxf
    have hm2_1 : s2.memory x = s1_3.memory x := by
      apply hmcf_k.2.2.2.2.2.2 x
      · intro i hi hhit
        rw [List.mem_singleton.mp hi] at hhit
        have hhit_keys : CellHits x.toNat (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) :=
          cellHits_of_inside hhit hsub_keys
        rcases (hfp_1 (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) (by dsimp [t]; simp [htabFootprint])).2 with ⟨j, hj, hij⟩ | hfresh
        · exact hxk j hj (cellHits_of_inside hhit_keys hij)
        · exact hxf (cellHits_of_inside hhit_keys hfresh)
      · intro ⟨_, c2⟩; omega
    rw [hm2_1]
    exact hfr_1 x (fun i hi => by rw [List.mem_singleton.mp hi]; exact hxk (t, 88) (by simp [htabFootprint])) hxf
  -- 5. Now enter `NS` on `s2` for the rest of `htab_new_leaf`!
  obtain ⟨hdom2_t5, hm2_t5⟩ := word_of_hdr s2 tw 5 (by omega) hB2
  obtain ⟨hdom2_t3, hm2_t3⟩ := word_of_hdr s2 tw 3 (by omega) hB2
  obtain ⟨hdom2_t6, hm2_t6⟩ := word_of_hdr s2 tw 6 (by omega) hB2
  apply Ret.of_NS
  apply Ret.ns_dec_lf hLF; intro vnd hvnd
  obtain ⟨_, hvnd_eq⟩ := ev_field_load (NS s2 s2.locals s2.globals s2.memory s2.clock) (ofString "t") tw 40#64
    (by simp only [NS_locals, hloc2]; simp [s1_3, L1_3, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide,
      show ofString "n" ≠ ofString "t" by decide]) vnd hvnd
  have hm40_2 : s2.memory (tw + 40#64) = .word (BitVec.ofNat 64 (hdr s1 t 5)) := by
    rw [← hdr_s2_eq 5 (by omega)]; exact hm2_t5
  have hvnd_eq' : vnd = .val (.word (BitVec.ofNat 64 (hdr s1 t 5))) := by
    rw [NS_memory, hm40_2] at hvnd_eq; exact hvnd_eq
  subst hvnd_eq'
  set ndw := BitVec.ofNat 64 (hdr s1 t 5)
  have hndw_nat : ndw.toNat = hdr s1 t 5 := by
    have hnd1_in := (hB1.1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd1_in; rw [BitVec.toNat_ofNat]; omega
  have eval_nd_nl : ∀ (st : PanSemStateFiniteExact 64 F) (off : Nat),
      st.locals.lookup (ofString "nodes") = some (.val (.word ndw)) →
      st.locals.lookup (ofString "n") = some (.val (.word nlw)) →
      evalAt st (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "n"), .const 32#64], .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (ndw + nlw * 32#64 + BitVec.ofNat 64 off))) := by
    intro st off hnd_l hn_l
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnd_l, hn_l,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
    rw [hz, BitVec.add_assoc]
  let L_s2n := s2.locals.update (ofString "nodes", .val (.word ndw))
  have hloc_s2n_nd : L_s2n.lookup (ofString "nodes") = some (.val (.word ndw)) := by
    simp [L_s2n, HolFiniteMapExact.lookup_update, FUPDATE]
  have hloc_s2n_n : L_s2n.lookup (ofString "n") = some (.val (.word nlw)) := by
    simp [L_s2n, hloc2, s1_3, L1_3, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "nodes" ≠ ofString "n" by decide,
      show ofString "stride" ≠ ofString "n" by decide, show ofString "klen" ≠ ofString "n" by decide]
  have hloc_s2n_val : L_s2n.lookup (ofString "value") = some (.val (.word valw)) := by
    simp [L_s2n, hloc2, s1_3, L1_3, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, hval,
      show ofString "nodes" ≠ ofString "value" by decide,
      show ofString "stride" ≠ ofString "value" by decide, show ofString "klen" ≠ ofString "value" by decide,
      show ofString "n" ≠ ofString "value" by decide]
  have hloc_s2n_t : L_s2n.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [L_s2n, hloc2, s1_3, L1_3, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "nodes" ≠ ofString "t" by decide,
      show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide,
      show ofString "n" ≠ ofString "t" by decide]
  have hloc_s2n_kl : L_s2n.lookup (ofString "klen") = some (.val (.word (BitVec.ofNat 64 klen))) := by
    simp [L_s2n, hloc2, s1_3, L1_3, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "nodes" ≠ ofString "klen" by decide,
      show ofString "stride" ≠ ofString "klen" by decide]
  -- 6. store(nodes + n * 32 + 0, 0)
  refine Ret.ns_storeW (ndw + nlw * 32#64 + 0#64) 0#64
    (eval_nd_nl _ 0 hloc_s2n_nd hloc_s2n_n) rfl ?_
  intro _
  -- 7. store(nodes + n * 32 + 8, value)
  refine Ret.ns_storeW (ndw + nlw * 32#64 + 8#64) valw
    (eval_nd_nl _ 8 hloc_s2n_nd hloc_s2n_n)
    (by simp [evalAt, evalHOLExact]; exact hloc_s2n_val) ?_
  intro _
  -- 8. dec pos := load(t + 24)
  apply Ret.ns_dec_lf hLF; intro vpos hvpos
  obtain ⟨_, hvpos_eq⟩ := ev_field_load (NS s2 L_s2n s2.globals (updW (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64) (ndw + nlw * 32#64 + 8#64) valw) s2.clock)
    (ofString "t") tw 24#64 hloc_s2n_t vpos hvpos
  have hsep1 := htabBlocks_cell_sep hB1
  have haddr_nl : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      ndw + nlw * 32#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (hdr s1 t 5 + 32 * nlw.toNat + off) := by
    intro off _; rw [← hndw_nat]; exact (ofNat_node_addr ndw nlw off).symm
  have hm24_cur : (updW (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64) (ndw + nlw * 32#64 + 8#64) valw) (tw + 24#64) =
      .word (BitVec.ofNat 64 cnt) := by
    have htw24 : tw + 24#64 = BitVec.ofNat 64 (t + 8 * 3) := (ofNat_add_toNat tw 24).symm
    have hne8 : tw + 24#64 ≠ ndw + nlw * 32#64 + 8#64 := by
      rw [htw24, haddr_nl 8 (Or.inr (Or.inl rfl))]; exact hsep1.1 3 (by omega) nlw.toNat hnl_lt_nc1 8 (Or.inr (Or.inl rfl))
    have hne0 : tw + 24#64 ≠ ndw + nlw * 32#64 + 0#64 := by
      rw [htw24, haddr_nl 0 (Or.inl rfl)]; exact hsep1.1 3 (by omega) nlw.toNat hnl_lt_nc1 0 (Or.inl rfl)
    simp only [updW, hne8, hne0, ↓reduceIte]
    have hm24_s2 : s2.memory (tw + 24#64) = .word (BitVec.ofNat 64 (hdr s2 t 3)) := hm2_t3
    rw [hm24_s2, hdr_s2_eq 3 (by omega), hh3_1]
  have hvpos_eq' : vpos = .val (.word (BitVec.ofNat 64 cnt)) := by
    rw [NS_memory, hm24_cur] at hvpos_eq; exact hvpos_eq
  subst hvpos_eq'
  set posw := BitVec.ofNat 64 cnt
  have hposw_nat : posw.toNat = cnt := by rw [BitVec.toNat_ofNat]; omega
  let L_pos := L_s2n.update (ofString "pos", .val (.word posw))
  have hl_pos_nd : L_pos.lookup (ofString "nodes") = some (.val (.word ndw)) := by
    simp [L_pos, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "pos" ≠ ofString "nodes" by decide, hloc_s2n_nd]
  have hl_pos_n : L_pos.lookup (ofString "n") = some (.val (.word nlw)) := by
    simp [L_pos, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "pos" ≠ ofString "n" by decide, hloc_s2n_n]
  have hl_pos_t : L_pos.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [L_pos, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "pos" ≠ ofString "t" by decide, hloc_s2n_t]
  have hl_pos_kl : L_pos.lookup (ofString "klen") = some (.val (.word (BitVec.ofNat 64 klen))) := by
    simp [L_pos, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "pos" ≠ ofString "klen" by decide, hloc_s2n_kl]
  have hl_pos_p : L_pos.lookup (ofString "pos") = some (.val (.word posw)) := by
    simp [L_pos, HolFiniteMapExact.lookup_update, FUPDATE]
  -- 9. store(nodes + n * 32 + 16, pos)
  refine Ret.ns_storeW (ndw + nlw * 32#64 + 16#64) posw
    (eval_nd_nl _ 16 hl_pos_nd hl_pos_n)
    (by simp [evalAt, evalHOLExact]; exact hl_pos_p) ?_
  intro _
  -- 10. store(nodes + n * 32 + 24, klen * 8)
  have hkl8_eq : BitVec.ofNat 64 klen * 8#64 = BitVec.ofNat 64 (8 * klen) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show (8#64).toNat = 8 from rfl]
    omega
  refine Ret.ns_storeW (ndw + nlw * 32#64 + 24#64) (BitVec.ofNat 64 (8 * klen))
    (eval_nd_nl _ 24 hl_pos_nd hl_pos_n)
    (by
      have hkl_cur : ((s2.locals.update (ofString "nodes", .val (.word ndw))).update (ofString "pos", .val (.word posw))).lookup (ofString "klen") = some (.val (.word (BitVec.ofNat 64 klen))) := hl_pos_kl
      simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          hkl_cur, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
          panOpHOL, valueIsWord, valueWord, hkl8_eq]) ?_
  intro _
  -- 11. store(load(t + 48) + pos * 8, n)
  set ow := BitVec.ofNat 64 (hdr s1 t 6)
  have hord1_in := (hB1.1 (hdr s1 t 6, (hdr s1 t 10 + 1) * 8) (by simp [htabFootprint])).1
  change hdr s1 t 6 ≥ sourceBase ∧ hdr s1 t 6 + (hdr s1 t 10 + 1) * 8 ≤ heapEnd at hord1_in
  have how_nat : ow.toNat = hdr s1 t 6 := by
    rw [BitVec.toNat_ofNat]; omega
  set m4 := updW (updW (updW (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64)
              (ndw + nlw * 32#64 + 8#64) valw)
              (ndw + nlw * 32#64 + 16#64) posw)
              (ndw + nlw * 32#64 + 24#64) (BitVec.ofNat 64 (8 * klen))
  have hm48_m4 : m4 (tw + 48#64) = .word ow := by
    have htw48 : tw + 48#64 = BitVec.ofNat 64 (t + 8 * 6) := (ofNat_add_toNat tw 48).symm
    have hne : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) → tw + 48#64 ≠ ndw + nlw * 32#64 + BitVec.ofNat 64 off := by
      intro off hoff; rw [htw48, haddr_nl off hoff]; exact hsep1.1 6 (by omega) nlw.toNat hnl_lt_nc1 off hoff
    simp only [m4, updW, hne 24 (Or.inr (Or.inr (Or.inr rfl))), hne 16 (Or.inr (Or.inr (Or.inl rfl))),
      hne 8 (Or.inr (Or.inl rfl)), hne 0 (Or.inl rfl), ↓reduceIte]
    have hm48_s2 : s2.memory (tw + 48#64) = .word (BitVec.ofNat 64 (hdr s2 t 6)) := hm2_t6
    rw [hm48_s2, hdr_s2_eq 6 (by omega)]
  have hord_addr_eq : ow + (posw * 8#64 + (0 : BitVec 64)) = BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) := by
    apply BitVec.eq_of_toNat_eq
    have hz : posw * 8#64 + (0 : BitVec 64) = posw * 8#64 := BitVec.add_zero _
    have hp8 : (posw * 8#64).toNat = cnt * 8 := by
      rw [BitVec.toNat_mul, hposw_nat, show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
    rw [hz, BitVec.toNat_add, how_nat, hp8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  refine Ret.ns_storeW (BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt)) nlw
    (by rw [← hord_addr_eq]; exact ev_order_addr _ tw posw ow hl_pos_t hl_pos_p hdom2_t6 hm48_m4)
    (by
      have hn_cur : ((s2.locals.update (ofString "nodes", .val (.word ndw))).update (ofString "pos", .val (.word posw))).lookup (ofString "n") = some (.val (.word nlw)) := hl_pos_n
      simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hn_cur]) ?_
  intro _
  -- 12. store(t + 24, pos + 1)
  have hpos1_eq : posw + (1#64 + (0 : BitVec 64)) = BitVec.ofNat 64 (cnt + 1) := by
    apply BitVec.eq_of_toNat_eq
    have h10 : 1#64 + (0 : BitVec 64) = 1#64 := rfl
    have hlt_c1 : cnt + 1 < 2 ^ 64 := by omega
    rw [h10, BitVec.toNat_add, hposw_nat, show (1#64 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlt_c1]
  refine Ret.ns_storeW (tw + 24#64) (BitVec.ofNat 64 (cnt + 1))
    (by
      have ht_cur : ((s2.locals.update (ofString "nodes", .val (.word ndw))).update (ofString "pos", .val (.word posw))).lookup (ofString "t") = some (.val (.word tw)) := hl_pos_t
      have h240 : 24#64 + (0 : BitVec 64) = 24#64 := rfl
      simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_cur,
        List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
        valueIsWord, valueWord, wordOpHOL, wordOp, h240])
    (by
      have hp_cur : ((s2.locals.update (ofString "nodes", .val (.word ndw))).update (ofString "pos", .val (.word posw))).lookup (ofString "pos") = some (.val (.word posw)) := hl_pos_p
      simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          hp_cur, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
          valueIsWord, valueWord, wordOpHOL, wordOp, hpos1_eq]) ?_
  intro _
  -- 13. return n
  apply Ret.ns_ret; intro val hval
  have hval_eq : val = .val (.word nlw) := by
    have hn_cur : ((s2.locals.update (ofString "nodes", .val (.word ndw))).update (ofString "pos", .val (.word posw))).lookup (ofString "n") = some (.val (.word nlw)) := hl_pos_n
    simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hn_cur, Option.some.injEq] at hval
    exact hval.symm
  subst hval_eq
  set m6 := updW (updW m4 (BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt)) nlw) (tw + 24#64) (BitVec.ofNat 64 (cnt + 1))
  let s_end := NS s2 HolFiniteMapExact.empty s2.globals m6 s2.clock
  have htw24_eq : tw + 24#64 = BitVec.ofNat 64 (t + 8 * 3) := (ofNat_add_toNat tw 24).symm
  have hdr_end_other : ∀ k < 11, k ≠ 3 → hdr s_end t k = hdr s1 t k := by
    intro k hk hk3
    have hne3 : BitVec.ofNat 64 (t + 8 * k) ≠ tw + 24#64 := by
      rw [htw24_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
    have hne_ord : BitVec.ofNat 64 (t + 8 * k) ≠ BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) :=
      hsep1.2.1 k hk cnt hcnt_lt_nc1
    have hne_nd : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        BitVec.ofNat 64 (t + 8 * k) ≠ ndw + nlw * 32#64 + BitVec.ofNat 64 off := by
      intro off hoff; rw [haddr_nl off hoff]; exact hsep1.1 k hk nlw.toNat hnl_lt_nc1 off hoff
    unfold hdr memW
    have hm : s_end.memory (BitVec.ofNat 64 (t + 8 * k)) = s2.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      simp only [s_end, NS_memory, m6, m4, updW, hne3, hne_ord,
        hne_nd 24 (Or.inr (Or.inr (Or.inr rfl))), hne_nd 16 (Or.inr (Or.inr (Or.inl rfl))),
        hne_nd 8 (Or.inr (Or.inl rfl)), hne_nd 0 (Or.inl rfl), ↓reduceIte]
    rw [hm]; exact hdr_s2_eq k hk
  have hh3_end : hdr s_end t 3 = cnt + 1 := by
    unfold hdr memW
    rw [← htw24_eq]
    simp only [s_end, NS_memory, m6, updW, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  have hh5_end : hdr s_end t 5 = hdr s1 t 5 := hdr_end_other 5 (by omega) (by omega)
  have hh6_end : hdr s_end t 6 = hdr s1 t 6 := hdr_end_other 6 (by omega) (by omega)
  have hh8_end : hdr s_end t 8 = hdr s1 t 8 := hdr_end_other 8 (by omega) (by omega)
  have hh9_end : hdr s_end t 9 = hdr s1 t 9 := hdr_end_other 9 (by omega) (by omega)
  have hfp_end : htabFootprint s_end t = htabFootprint s1 t := by
    simp [htabFootprint, hdr_end_other 1 (by omega) (by omega), hdr_end_other 4 (by omega) (by omega),
      hh5_end, hh6_end, hdr_end_other 10 (by omega) (by omega)]
  have hB_end : HtabBlocks s_end t := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro iv hiv; rw [hfp_end] at hiv; obtain ⟨hin, hwok⟩ := hB1.1 iv hiv
      exact ⟨hin, wordsOK_block s_end hA2.1.memaddrs iv.1 iv.2 hwok.1 hwok.2.1 hin.1 hin.2⟩
    · rw [hfp_end]; exact hB1.2.1
    · rw [hdr_end_other 0 (by omega) (by omega)]; exact hB1.2.2.1
    · rw [hdr_end_other 0 (by omega) (by omega)]; exact hB1.2.2.2.1
    · rw [hdr_end_other 1 (by omega) (by omega), hdr_end_other 0 (by omega) (by omega)]; exact hB1.2.2.2.2.1
    · rw [hdr_end_other 10 (by omega) (by omega)]; exact hB1.2.2.2.2.2.1
    · rw [hh8_end]; exact hB1.2.2.2.2.2.2.1
    · rw [hh8_end, hdr_end_other 10 (by omega) (by omega)]; exact hB1.2.2.2.2.2.2.2
  have hnl_field : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      s_end.memory (BitVec.ofNat 64 (hdr s1 t 5 + 32 * nlw.toNat + off)) =
        m4 (BitVec.ofNat 64 (hdr s1 t 5 + 32 * nlw.toNat + off)) := by
    intro off hoff
    have hne3 : BitVec.ofNat 64 (hdr s1 t 5 + 32 * nlw.toNat + off) ≠ tw + 24#64 := by
      rw [htw24_eq]; exact (hsep1.1 3 (by omega) nlw.toNat hnl_lt_nc1 off hoff).symm
    have hne_ord : BitVec.ofNat 64 (hdr s1 t 5 + 32 * nlw.toNat + off) ≠ BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) :=
      (hsep1.2.2.1 nlw.toNat hnl_lt_nc1 off hoff cnt hcnt_lt_nc1).symm
    simp [s_end, m6, updW, hne3, hne_ord]
  have hnl_0 : nodeF s_end (hdr s1 t 5) nlw.toNat 0 = 0 := by
    unfold nodeF memW; rw [hnl_field 0 (Or.inl rfl)]
    have hne24 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 0 (Or.inl rfl) nlw.toNat hnl_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    have hne16 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 0 (Or.inl rfl) nlw.toNat hnl_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    have hne8 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 0 (Or.inl rfl) nlw.toNat hnl_lt_nc1 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    simp only [m4, updW, haddr_nl 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_nl 16 (Or.inr (Or.inr (Or.inl rfl))),
      haddr_nl 8 (Or.inr (Or.inl rfl)), haddr_nl 0 (Or.inl rfl), hne24, hne16, hne8, ↓reduceIte]
    rfl
  have hnl_8 : nodeF s_end (hdr s1 t 5) nlw.toNat 8 = valw.toNat := by
    unfold nodeF memW; rw [hnl_field 8 (Or.inr (Or.inl rfl))]
    have hne24 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 8 (Or.inr (Or.inl rfl)) nlw.toNat hnl_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    have hne16 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 8 (Or.inr (Or.inl rfl)) nlw.toNat hnl_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    simp only [m4, updW, haddr_nl 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_nl 16 (Or.inr (Or.inr (Or.inl rfl))),
      haddr_nl 8 (Or.inr (Or.inl rfl)), hne24, hne16, ↓reduceIte]
  have hnl_16 : nodeF s_end (hdr s1 t 5) nlw.toNat 16 = cnt := by
    unfold nodeF memW; rw [hnl_field 16 (Or.inr (Or.inr (Or.inl rfl)))]
    have hne24 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) nlw.toNat hnl_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    simp only [m4, updW, haddr_nl 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_nl 16 (Or.inr (Or.inr (Or.inl rfl))), hne24, ↓reduceIte, hposw_nat]
  have hnl_24 : nodeF s_end (hdr s1 t 5) nlw.toNat 24 = 8 * klen := by
    unfold nodeF memW; rw [hnl_field 24 (Or.inr (Or.inr (Or.inr rfl)))]
    simp only [m4, updW, haddr_nl 24 (Or.inr (Or.inr (Or.inr rfl))), ↓reduceIte, BitVec.toNat_ofNat]
    omega
  have hnd_other : ∀ x < hdr s1 t 10 + 1, x ≠ nlw.toNat → ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s_end (hdr s1 t 5) x off = nodeF s1 (hdr s1 t 5) x off := by
    intro x hx hxne off hoff
    have hne3 : BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off) ≠ tw + 24#64 := by
      rw [htw24_eq]; exact (hsep1.1 3 (by omega) x hx off hoff).symm
    have hne_ord : BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off) ≠ BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) :=
      (hsep1.2.2.1 x hx off hoff cnt hcnt_lt_nc1).symm
    have hne_nl : ∀ off2, (off2 = 0 ∨ off2 = 8 ∨ off2 = 16 ∨ off2 = 24) →
        BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off) ≠ ndw + nlw * 32#64 + BitVec.ofNat 64 off2 := by
      intro off2 hoff2; rw [haddr_nl off2 hoff2]
      exact hsep1.2.2.2.1 x hx off hoff nlw.toNat hnl_lt_nc1 off2 hoff2 (Or.inl hxne)
    have hm : s_end.memory (BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off)) = s2.memory (BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off)) := by
      simp only [s_end, NS_memory, m6, m4, updW, hne3, hne_ord,
        hne_nl 24 (Or.inr (Or.inr (Or.inr rfl))), hne_nl 16 (Or.inr (Or.inr (Or.inl rfl))),
        hne_nl 8 (Or.inr (Or.inl rfl)), hne_nl 0 (Or.inl rfl), ↓reduceIte]
    have h1 : nodeF s_end (hdr s1 t 5) x off = nodeF s2 (hdr s1 t 5) x off := by unfold nodeF memW; rw [hm]
    exact h1.trans (hnd_s2_eq x hx off hoff)
  have hord_cnt : memW s_end (hdr s1 t 6 + 8 * cnt) = nlw.toNat := by
    have hne3 : BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) ≠ tw + 24#64 := by
      rw [htw24_eq]; exact (hsep1.2.1 3 (by omega) cnt hcnt_lt_nc1).symm
    unfold memW; simp [s_end, m6, updW, hne3]
  have hord_lt : ∀ i < cnt, memW s_end (hdr s1 t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
    intro i hi
    have hi_lt : i < hdr s1 t 10 + 1 := by omega
    have hne3 : BitVec.ofNat 64 (hdr s1 t 6 + 8 * i) ≠ tw + 24#64 := by
      rw [htw24_eq]; exact (hsep1.2.1 3 (by omega) i hi_lt).symm
    have hne_cnt : BitVec.ofNat 64 (hdr s1 t 6 + 8 * i) ≠ BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) :=
      hsep1.2.2.2.2 i hi_lt cnt hcnt_lt_nc1 (by omega)
    have hne_nl : ∀ off2, (off2 = 0 ∨ off2 = 8 ∨ off2 = 16 ∨ off2 = 24) →
        BitVec.ofNat 64 (hdr s1 t 6 + 8 * i) ≠ ndw + nlw * 32#64 + BitVec.ofNat 64 off2 := by
      intro off2 hoff2; rw [haddr_nl off2 hoff2]
      exact hsep1.2.2.1 nlw.toNat hnl_lt_nc1 off2 hoff2 i hi_lt
    have hm : s_end.memory (BitVec.ofNat 64 (hdr s1 t 6 + 8 * i)) = s2.memory (BitVec.ofNat 64 (hdr s1 t 6 + 8 * i)) := by
      simp only [s_end, NS_memory, m6, m4, updW, hne3, hne_cnt,
        hne_nl 24 (Or.inr (Or.inr (Or.inr rfl))), hne_nl 16 (Or.inr (Or.inr (Or.inl rfl))),
        hne_nl 8 (Or.inr (Or.inl rfl)), hne_nl 0 (Or.inl rfl), ↓reduceIte]
    have h1 : memW s_end (hdr s1 t 6 + 8 * i) = memW s2 (hdr s1 t 6 + 8 * i) := by unfold memW; rw [hm]
    exact (h1.trans (hord_s2_eq i hi_lt)).trans (hord_1 i (by change i < hdr s0 t 10 + 1; omega))
  have hNS_end : NodeState s_end t (A ++ [nlw.toNat]) Fr1 := by
    refine ⟨hB_end, hnodup1, fun x => by rw [hh8_end]; exact hmem1 x, ?_⟩
    rw [hh5_end, hh9_end]
    refine FreeChainF.congr Fr1 _ ?_ hfc1
    intro f hf
    have hf_ne : f ≠ nlw.toNat := by
      rintro rfl
      exact (List.nodup_append.mp hnodup1).2.2 nlw.toNat (List.mem_append_right _ (by simp)) nlw.toNat hf rfl
    have hf_rng := (hmem1 f).mp (List.mem_append_right _ hf)
    exact hnd_other f (by omega) hf_ne 0 (Or.inl rfl)
  have hfr_end : FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
    have hit_of_s1_fp : ∀ (addr : BitVec 64) (blk : Ivl),
        blk ∈ htabFootprint s1 t → CellHits addr.toNat blk →
        (∃ j ∈ htabFootprint s0 t, CellHits addr.toNat j) ∨
          CellHits addr.toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
      intro addr blk hblk hhit
      rcases (hfp_1 blk hblk).2 with ⟨j, hj, hij⟩ | hfr
      · exact Or.inl ⟨j, hj, cellHits_of_inside hhit hij⟩
      · exact Or.inr (cellHits_of_inside hhit hfr)
    have hit_nd : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        (∃ j ∈ htabFootprint s0 t, CellHits (ndw + nlw * 32#64 + BitVec.ofNat 64 off).toNat j) ∨
          CellHits (ndw + nlw * 32#64 + BitVec.ofNat 64 off).toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
      intro off hoff
      apply hit_of_s1_fp _ (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])
      rw [haddr_nl off hoff, BitVec.toNat_ofNat]
      have hnd1_in := (hB1.1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])).1
      unfold Inside at hnd1_in
      rw [Nat.mod_eq_of_lt (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)]
      unfold CellHits
      rcases hoff with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    have hit_ord : (∃ j ∈ htabFootprint s0 t, CellHits (BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt)).toNat j) ∨
        CellHits (BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt)).toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
      apply hit_of_s1_fp _ (hdr s1 t 6, (hdr s1 t 10 + 1) * 8) (by simp [htabFootprint])
      have hord1_in := (hB1.1 (hdr s1 t 6, (hdr s1 t 10 + 1) * 8) (by simp [htabFootprint])).1
      unfold Inside at hord1_in
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact ⟨by omega, by omega⟩
    have hit_t24 : (∃ j ∈ htabFootprint s0 t, CellHits (tw + 24#64).toNat j) ∨
        CellHits (tw + 24#64).toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
      have htw24_nat : (tw + 24#64).toNat = t + 24 := by rw [BitVec.toNat_add, show (24#64).toNat = 24 from rfl]; omega
      exact Or.inl ⟨(t, 88), by simp [htabFootprint], by rw [htw24_nat]; exact ⟨by omega, by omega⟩⟩
    have f1 := frameOutside_updW_mem s0 s2 s2.memory rfl _ 0#64 _ _ hfr_s0_s2 (hit_nd 0 (Or.inl rfl))
      (NS s2 HolFiniteMapExact.empty s2.globals (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64) s2.clock) rfl
    have f2 := frameOutside_updW_mem s0 _ _ rfl _ valw _ _ f1 (hit_nd 8 (Or.inr (Or.inl rfl)))
      (NS s2 HolFiniteMapExact.empty s2.globals (updW (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64) (ndw + nlw * 32#64 + 8#64) valw) s2.clock) rfl
    have f3 := frameOutside_updW_mem s0 _ _ rfl _ posw _ _ f2 (hit_nd 16 (Or.inr (Or.inr (Or.inl rfl))))
      (NS s2 HolFiniteMapExact.empty s2.globals (updW (updW (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64) (ndw + nlw * 32#64 + 8#64) valw) (ndw + nlw * 32#64 + 16#64) posw) s2.clock) rfl
    have f4 := frameOutside_updW_mem s0 _ _ rfl _ (BitVec.ofNat 64 (8 * klen)) _ _ f3 (hit_nd 24 (Or.inr (Or.inr (Or.inr rfl))))
      (NS s2 HolFiniteMapExact.empty s2.globals m4 s2.clock) rfl
    have f5 := frameOutside_updW_mem s0 _ _ rfl _ nlw _ _ f4 hit_ord
      (NS s2 HolFiniteMapExact.empty s2.globals (updW m4 (BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt)) nlw) s2.clock) rfl
    exact frameOutside_updW_mem s0 _ _ rfl _ (BitVec.ofNat 64 (cnt + 1)) _ _ f5 hit_t24 s_end rfl
  have hg2_1 : s2.globals = s1.globals := hmcf_k.2.2.2.2.2.1
  have hgn_end : globN s_end "heap_ptr" = globN s1 "heap_ptr" := by
    change globN s2 "heap_ptr" = _; unfold globN; rw [hg2_1]
  have hal_end : ∀ iv ∈ htabFootprint s_end t, Allocated s_end iv ∧
      ((∃ j ∈ htabFootprint s0 t, Inside iv j.1 (j.1 + j.2)) ∨
        Inside iv (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s1 "heap_ptr" - globN s0 "heap_ptr"))) := by
    rw [hfp_end]
    intro iv hiv
    obtain ⟨hal_s1, hprov⟩ := hfp_1 iv hiv
    have hal_s2 : Allocated s_end iv := by
      change Allocated s2 iv; unfold Allocated globN; rw [hg2_1]; exact hal_s1
    exact ⟨hal_s2, hprov⟩
  refine ⟨nlw, Fr1, rfl, ⟨guestInv_congr (s := s2) rfl rfl rfl rfl hA2.1, hA2.2⟩,
    hNS_end,
    (hdr_end_other 0 (by omega) (by omega)).trans hh0_1,
    (hdr_end_other 1 (by omega) (by omega)).trans hh1_1,
    hh3_end,
    (hdr_end_other 7 (by omega) (by omega)).trans hh7_1,
    by rw [hh5_end]; exact hnl_0,
    by rw [hh5_end]; exact hnl_8,
    by rw [hh5_end]; exact hnl_16,
    by rw [hh5_end]; exact hnl_24,
    by rw [hh6_end]; exact hord_cnt,
    ?_, ?_,
    by rw [hgn_end]; exact hhp_1,
    ?_, ?_,
    fun k hk => (hg_1 k hk).trans (congrArg (fun g => g.lookup k) hg2_1.symm)⟩
  · intro x hxA off hoff
    rw [hh5_end]
    have hx_ne : x ≠ nlw.toNat := by
      rintro rfl
      have hndAnl : (A ++ [nlw.toNat]).Nodup := (List.nodup_append.mp hnodup1).1
      exact (List.nodup_append.mp hndAnl).2.2 nlw.toNat hxA nlw.toNat (by simp) rfl
    have hx_rng := (hmem1 x).mp (List.mem_append_left _ (List.mem_append_left _ hxA))
    exact (hnd_other x (by omega) hx_ne off hoff).trans (hnd_1 x hxA off hoff)
  · intro i hi
    rw [hh6_end]; exact hord_lt i hi
  · rw [hgn_end]; exact hal_end
  · change FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s_end "heap_ptr" - globN s0 "heap_ptr")
    rw [hgn_end]; exact hfr_end

/-! ## 2. `htab_new_internal` Postcondition -/

def NewInternalPost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat) (bitw : BitVec 64)
    (A : List Nat) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) : Prop :=
  let fresh : Ivl := (globN s0 "heap_ptr", globN post "heap_ptr" - globN s0 "heap_ptr")
  ∃ ni : BitVec 64, ∃ Fr1 : List Nat,
    v = .val (.word ni) ∧
    ArenaReady post ∧
    NodeState post t (A ++ [ni.toNat]) Fr1 ∧
    hdr post t 0 = hdr s0 t 0 ∧
    hdr post t 1 = hdr s0 t 1 ∧
    hdr post t 3 = hdr s0 t 3 ∧
    hdr post t 7 = hdr s0 t 7 ∧
    hdr s0 t 10 ≤ hdr post t 10 ∧
    nodeF post (hdr post t 5) ni.toNat 0 = 0 ∧
    nodeF post (hdr post t 5) ni.toNat 8 = 0 ∧
    nodeF post (hdr post t 5) ni.toNat 16 = 0 ∧
    nodeF post (hdr post t 5) ni.toNat 24 = bitw.toNat ∧
    (∀ x ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF post (hdr post t 5) x off = nodeF s0 (hdr s0 t 5) x off) ∧
    (∀ i, i < hdr s0 t 10 + 1 →
      memW post (hdr post t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i)) ∧
    globN s0 "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i ∧
      ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
    FrameOutside s0 post (htabFootprint s0 t) fresh ∧
    (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s0.globals.lookup k = post.globals.lookup k)

theorem locFree_newInternalPost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat)
    (bitw : BitVec 64) (A : List Nat) :
    LocFreePost (NewInternalPost s0 t bitw A) := by
  intro v p L' h
  obtain ⟨ni, Fr1, hv, hA, hNS, c0, c1, c3, c7, c10, n0, n8, n16, n24, cnd, cord, chp, cfp, cfr, cg⟩ := h
  exact ⟨ni, Fr1, hv, ⟨guestInv_congr (s := { p with locals := L' }) rfl rfl rfl rfl hA.1, hA.2⟩,
    hNS, c0, c1, c3, c7, c10, n0, n8, n16, n24, cnd, cord, chp, cfp, cfr, cg⟩

theorem htab_new_internal_body_spec {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (tw bitw : BitVec 64) (A Fr0 : List Nat)
    (ht : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hbit : s0.locals.lookup (ofString "bit") = some (.val (.word bitw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_new_internal)
      (NewInternalPost s0 tw.toNat bitw A) := by
  set t := tw.toNat
  have hLF := locFree_newInternalPost s0 t bitw A
  htab_unfold Guest.Software.guestFn_htab_new_internal
  -- 1. decCall n := htab_new_node(t)
  refine Ret.decCall_new_node_lf hLF tw A Fr0 (by simp [evalAt, evalHOLExact, ht]) hA0 hNS0 hal0 ?_
  intro niw Fr1 s1 hA1 hNS1 hh0_1 hh1_1 hh3_1 hh7_1 hnc_le_1 hnd_1 hord_1 hhp_1 hfp_1 hfr_1 hg_1 hloc_1
  change NodeState s1 t (A ++ [niw.toNat]) Fr1 at hNS1
  change hdr s1 t 0 = hdr s0 t 0 at hh0_1
  change hdr s1 t 1 = hdr s0 t 1 at hh1_1
  change hdr s1 t 3 = hdr s0 t 3 at hh3_1
  change hdr s1 t 7 = hdr s0 t 7 at hh7_1
  change hdr s0 t 10 ≤ hdr s1 t 10 at hnc_le_1
  obtain ⟨hB1, hnodup1, hmem1, hfc1⟩ := hNS1
  obtain ⟨hnc1_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB1
  have hnx1_le : hdr s1 t 8 ≤ hdr s1 t 10 + 1 := hB1.2.2.2.2.2.2.2
  have hni_rng : 1 ≤ niw.toNat ∧ niw.toNat < hdr s1 t 8 :=
    (hmem1 niw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  have hni_lt_nc1 : niw.toNat < hdr s1 t 10 + 1 := by omega
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨_, hm1_t5⟩ := word_of_hdr s1 tw 5 (by omega) hB1
  -- 2. dec nodes := load(t + 40) via `NS`!
  let L_init := s1.locals.update (ofString "n", .val (.word niw))
  change Ret (NS s1 L_init s1.globals s1.memory s1.clock) _ _
  apply Ret.ns_dec_lf hLF; intro vnd hvnd
  obtain ⟨_, hvnd_eq⟩ := ev_field_load (NS s1 L_init s1.globals s1.memory s1.clock) (ofString "t") tw 40#64
    (by simp [L_init, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "n" ≠ ofString "t" by decide]) vnd hvnd
  have hm40 : s1.memory (tw + 40#64) = .word (BitVec.ofNat 64 (hdr s1 t 5)) := hm1_t5
  have hvnd_eq' : vnd = .val (.word (BitVec.ofNat 64 (hdr s1 t 5))) := by
    rw [NS_memory, hm40] at hvnd_eq; exact hvnd_eq
  subst hvnd_eq'
  set ndw := BitVec.ofNat 64 (hdr s1 t 5)
  have hndw_nat : ndw.toNat = hdr s1 t 5 := by
    have hnd1_in := (hB1.1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd1_in; rw [BitVec.toNat_ofNat]; omega
  have eval_nd_ni : ∀ (st : PanSemStateFiniteExact 64 F) (off : Nat),
      st.locals.lookup (ofString "nodes") = some (.val (.word ndw)) →
      st.locals.lookup (ofString "n") = some (.val (.word niw)) →
      evalAt st (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "n"), .const 32#64], .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (ndw + niw * 32#64 + BitVec.ofNat 64 off))) := by
    intro st off hnd_l hn_l
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnd_l, hn_l,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
    rw [hz, BitVec.add_assoc]
  let L_ni : HolFiniteMapExact MlS (ValueHOL 64) := L_init.update (ofString "nodes", .val (.word ndw))
  have hl_nd : L_ni.lookup (ofString "nodes") = some (.val (.word ndw)) := by
    simp [L_ni, HolFiniteMapExact.lookup_update, FUPDATE]
  have hl_n : L_ni.lookup (ofString "n") = some (.val (.word niw)) := by
    simp [L_ni, L_init, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "nodes" ≠ ofString "n" by decide]
  have hl_bit : L_ni.lookup (ofString "bit") = some (.val (.word bitw)) := by
    simp [L_ni, L_init, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, hbit,
      show ofString "nodes" ≠ ofString "bit" by decide, show ofString "n" ≠ ofString "bit" by decide]
  -- 3. Four stores to `ni` (+0 := 0, +8 := 0, +16 := 0, +24 := bit)
  change Ret (NS s1 L_ni s1.globals s1.memory s1.clock) _ _
  refine Ret.ns_storeW (ndw + niw * 32#64 + 0#64) 0#64 (eval_nd_ni _ 0 hl_nd hl_n) rfl ?_
  intro _
  refine Ret.ns_storeW (ndw + niw * 32#64 + 8#64) 0#64 (eval_nd_ni _ 8 hl_nd hl_n) rfl ?_
  intro _
  refine Ret.ns_storeW (ndw + niw * 32#64 + 16#64) 0#64 (eval_nd_ni _ 16 hl_nd hl_n) rfl ?_
  intro _
  refine Ret.ns_storeW (ndw + niw * 32#64 + 24#64) bitw (eval_nd_ni _ 24 hl_nd hl_n)
    (by simp [evalAt, evalHOLExact, hl_bit]) ?_
  intro _
  apply Ret.ns_ret; intro val hval
  have hval_eq : val = .val (.word niw) := by
    simp [evalAt, evalHOLExact, hl_n] at hval; exact hval.symm
  subst hval_eq
  set m_ni := updW (updW (updW (updW s1.memory (ndw + niw * 32#64 + 0#64) 0#64)
                (ndw + niw * 32#64 + 8#64) 0#64)
                (ndw + niw * 32#64 + 16#64) 0#64)
                (ndw + niw * 32#64 + 24#64) bitw
  let s_end := NS s1 HolFiniteMapExact.empty s1.globals m_ni s1.clock
  have hsep1 := htabBlocks_cell_sep hB1
  have haddr_ni : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      ndw + niw * 32#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (hdr s1 t 5 + 32 * niw.toNat + off) := by
    intro off _; rw [← hndw_nat]; exact (ofNat_node_addr ndw niw off).symm
  have hdr_end_eq : ∀ k < 11, hdr s_end t k = hdr s1 t k := by
    intro k hk
    have hne : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        BitVec.ofNat 64 (t + 8 * k) ≠ ndw + niw * 32#64 + BitVec.ofNat 64 off := by
      intro off hoff; rw [haddr_ni off hoff]; exact hsep1.1 k hk niw.toNat hni_lt_nc1 off hoff
    unfold hdr memW
    have hm : s_end.memory (BitVec.ofNat 64 (t + 8 * k)) = s1.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      simp only [s_end, NS_memory, m_ni, updW, hne 24 (Or.inr (Or.inr (Or.inr rfl))),
        hne 16 (Or.inr (Or.inr (Or.inl rfl))), hne 8 (Or.inr (Or.inl rfl)), hne 0 (Or.inl rfl), ↓reduceIte]
    rw [hm]
  have hh5_end : hdr s_end t 5 = hdr s1 t 5 := hdr_end_eq 5 (by omega)
  have hh6_end : hdr s_end t 6 = hdr s1 t 6 := hdr_end_eq 6 (by omega)
  have hh8_end : hdr s_end t 8 = hdr s1 t 8 := hdr_end_eq 8 (by omega)
  have hh9_end : hdr s_end t 9 = hdr s1 t 9 := hdr_end_eq 9 (by omega)
  have hfp_end : htabFootprint s_end t = htabFootprint s1 t := by
    simp [htabFootprint, hdr_end_eq 1 (by omega), hdr_end_eq 4 (by omega), hh5_end, hh6_end, hdr_end_eq 10 (by omega)]
  have hB_end : HtabBlocks s_end t := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro iv hiv; rw [hfp_end] at hiv; obtain ⟨hin, hwok⟩ := hB1.1 iv hiv
      exact ⟨hin, wordsOK_block s_end hA1.1.memaddrs iv.1 iv.2 hwok.1 hwok.2.1 hin.1 hin.2⟩
    · rw [hfp_end]; exact hB1.2.1
    · rw [hdr_end_eq 0 (by omega)]; exact hB1.2.2.1
    · rw [hdr_end_eq 0 (by omega)]; exact hB1.2.2.2.1
    · rw [hdr_end_eq 1 (by omega), hdr_end_eq 0 (by omega)]; exact hB1.2.2.2.2.1
    · rw [hdr_end_eq 10 (by omega)]; exact hB1.2.2.2.2.2.1
    · rw [hh8_end]; exact hB1.2.2.2.2.2.2.1
    · rw [hh8_end, hdr_end_eq 10 (by omega)]; exact hB1.2.2.2.2.2.2.2
  have hni_0 : nodeF s_end (hdr s1 t 5) niw.toNat 0 = 0 := by
    unfold nodeF memW
    have hne24 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 0 (Or.inl rfl) niw.toNat hni_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    have hne16 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 0 (Or.inl rfl) niw.toNat hni_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    have hne8 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 0 (Or.inl rfl) niw.toNat hni_lt_nc1 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    simp only [s_end, NS_memory, m_ni, updW, haddr_ni 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_ni 16 (Or.inr (Or.inr (Or.inl rfl))),
      haddr_ni 8 (Or.inr (Or.inl rfl)), haddr_ni 0 (Or.inl rfl), hne24, hne16, hne8, ↓reduceIte]
    rfl
  have hni_8 : nodeF s_end (hdr s1 t 5) niw.toNat 8 = 0 := by
    unfold nodeF memW
    have hne24 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    have hne16 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    simp only [s_end, NS_memory, m_ni, updW, haddr_ni 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_ni 16 (Or.inr (Or.inr (Or.inl rfl))),
      haddr_ni 8 (Or.inr (Or.inl rfl)), hne24, hne16, ↓reduceIte]
    rfl
  have hni_16 : nodeF s_end (hdr s1 t 5) niw.toNat 16 = 0 := by
    unfold nodeF memW
    have hne24 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) niw.toNat hni_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    simp only [s_end, NS_memory, m_ni, updW, haddr_ni 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_ni 16 (Or.inr (Or.inr (Or.inl rfl))), hne24, ↓reduceIte]
    rfl
  have hni_24 : nodeF s_end (hdr s1 t 5) niw.toNat 24 = bitw.toNat := by
    unfold nodeF memW
    simp [s_end, m_ni, updW, haddr_ni 24 (Or.inr (Or.inr (Or.inr rfl)))]
  have hnd_other : ∀ x < hdr s1 t 10 + 1, x ≠ niw.toNat → ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s_end (hdr s1 t 5) x off = nodeF s1 (hdr s1 t 5) x off := by
    intro x hx hxne off hoff
    have hne : ∀ off2, (off2 = 0 ∨ off2 = 8 ∨ off2 = 16 ∨ off2 = 24) →
        BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off) ≠ ndw + niw * 32#64 + BitVec.ofNat 64 off2 := by
      intro off2 hoff2; rw [haddr_ni off2 hoff2]
      exact hsep1.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc1 off2 hoff2 (Or.inl hxne)
    unfold nodeF memW
    have hm : s_end.memory (BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off)) = s1.memory (BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off)) := by
      simp only [s_end, NS_memory, m_ni, updW, hne 24 (Or.inr (Or.inr (Or.inr rfl))),
        hne 16 (Or.inr (Or.inr (Or.inl rfl))), hne 8 (Or.inr (Or.inl rfl)), hne 0 (Or.inl rfl), ↓reduceIte]
    rw [hm]
  have hord_end : ∀ i < hdr s0 t 10 + 1, memW s_end (hdr s1 t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
    intro i hi
    have hi1 : i < hdr s1 t 10 + 1 := by omega
    have hne : ∀ off2, (off2 = 0 ∨ off2 = 8 ∨ off2 = 16 ∨ off2 = 24) →
        BitVec.ofNat 64 (hdr s1 t 6 + 8 * i) ≠ ndw + niw * 32#64 + BitVec.ofNat 64 off2 := by
      intro off2 hoff2; rw [haddr_ni off2 hoff2]
      exact hsep1.2.2.1 niw.toNat hni_lt_nc1 off2 hoff2 i hi1
    have h1 : memW s_end (hdr s1 t 6 + 8 * i) = memW s1 (hdr s1 t 6 + 8 * i) := by
      unfold memW
      have hm : s_end.memory (BitVec.ofNat 64 (hdr s1 t 6 + 8 * i)) = s1.memory (BitVec.ofNat 64 (hdr s1 t 6 + 8 * i)) := by
        simp only [s_end, NS_memory, m_ni, updW, hne 24 (Or.inr (Or.inr (Or.inr rfl))),
          hne 16 (Or.inr (Or.inr (Or.inl rfl))), hne 8 (Or.inr (Or.inl rfl)), hne 0 (Or.inl rfl), ↓reduceIte]
      rw [hm]
    exact h1.trans (hord_1 i hi)
  have hNS_end : NodeState s_end t (A ++ [niw.toNat]) Fr1 := by
    refine ⟨hB_end, hnodup1, fun x => by rw [hh8_end]; exact hmem1 x, ?_⟩
    rw [hh5_end, hh9_end]
    refine FreeChainF.congr Fr1 _ ?_ hfc1
    intro f hf
    have hf_ne : f ≠ niw.toNat := by
      rintro rfl
      exact (List.nodup_append.mp hnodup1).2.2 niw.toNat (List.mem_append_right _ (by simp)) niw.toNat hf rfl
    have hf_rng := (hmem1 f).mp (List.mem_append_right _ hf)
    exact hnd_other f (by omega) hf_ne 0 (Or.inl rfl)
  have hfr_s0_s1_fp : FrameOutside s0 s1 (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") :=
    fun x hxk hxf => hfr_1 x (fun i hi => by rw [List.mem_singleton.mp hi]; exact hxk (t, 88) (by simp [htabFootprint])) hxf
  have hfr_end : FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
    have hit_nd : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        (∃ j ∈ htabFootprint s0 t, CellHits (ndw + niw * 32#64 + BitVec.ofNat 64 off).toNat j) ∨
          CellHits (ndw + niw * 32#64 + BitVec.ofNat 64 off).toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
      intro off hoff
      have hhit_blk : CellHits (ndw + niw * 32#64 + BitVec.ofNat 64 off).toNat (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) := by
        rw [haddr_ni off hoff, BitVec.toNat_ofNat]
        have hnd1_in := (hB1.1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])).1
        unfold Inside at hnd1_in
        rw [Nat.mod_eq_of_lt (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)]
        unfold CellHits
        rcases hoff with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rcases (hfp_1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by dsimp [t]; simp [htabFootprint])).2 with ⟨j, hj, hij⟩ | hfr
      · exact Or.inl ⟨j, hj, cellHits_of_inside hhit_blk hij⟩
      · exact Or.inr (cellHits_of_inside hhit_blk hfr)
    have f1 := frameOutside_updW_mem s0 s1 s1.memory rfl _ 0#64 _ _ hfr_s0_s1_fp (hit_nd 0 (Or.inl rfl))
      (NS s1 HolFiniteMapExact.empty s1.globals (updW s1.memory (ndw + niw * 32#64 + 0#64) 0#64) s1.clock) rfl
    have f2 := frameOutside_updW_mem s0 _ _ rfl _ 0#64 _ _ f1 (hit_nd 8 (Or.inr (Or.inl rfl)))
      (NS s1 HolFiniteMapExact.empty s1.globals (updW (updW s1.memory (ndw + niw * 32#64 + 0#64) 0#64) (ndw + niw * 32#64 + 8#64) 0#64) s1.clock) rfl
    have f3 := frameOutside_updW_mem s0 _ _ rfl _ 0#64 _ _ f2 (hit_nd 16 (Or.inr (Or.inr (Or.inl rfl))))
      (NS s1 HolFiniteMapExact.empty s1.globals (updW (updW (updW s1.memory (ndw + niw * 32#64 + 0#64) 0#64) (ndw + niw * 32#64 + 8#64) 0#64) (ndw + niw * 32#64 + 16#64) 0#64) s1.clock) rfl
    exact frameOutside_updW_mem s0 _ _ rfl _ bitw _ _ f3 (hit_nd 24 (Or.inr (Or.inr (Or.inr rfl)))) s_end rfl
  refine ⟨niw, Fr1, rfl, ⟨guestInv_congr (s := s1) rfl rfl rfl rfl hA1.1, hA1.2⟩,
    hNS_end,
    (hdr_end_eq 0 (by omega)).trans hh0_1,
    (hdr_end_eq 1 (by omega)).trans hh1_1,
    (hdr_end_eq 3 (by omega)).trans hh3_1,
    (hdr_end_eq 7 (by omega)).trans hh7_1,
    (by change hdr s0 t 10 ≤ hdr s_end t 10; rw [hdr_end_eq 10 (by omega)]; exact hnc_le_1),
    by rw [hh5_end]; exact hni_0,
    by rw [hh5_end]; exact hni_8,
    by rw [hh5_end]; exact hni_16,
    by rw [hh5_end]; exact hni_24,
    ?_, ?_,
    hhp_1,
    (by change ∀ iv ∈ htabFootprint s_end t, Allocated s1 iv ∧ _
        rw [hfp_end]; exact hfp_1),
    hfr_end, hg_1⟩
  · intro x hxA off hoff
    rw [hh5_end]
    have hx_ne : x ≠ niw.toNat := by
      rintro rfl
      have hndAni : (A ++ [niw.toNat]).Nodup := (List.nodup_append.mp hnodup1).1
      exact (List.nodup_append.mp hndAni).2.2 niw.toNat hxA niw.toNat (by simp) rfl
    have hx_rng := (hmem1 x).mp (List.mem_append_left _ (List.mem_append_left _ hxA))
    exact (hnd_other x (by omega) hx_ne off hoff).trans (hnd_1 x hxA off hoff)
  · intro i hi
    rw [hh6_end]; exact hord_end i hi

/-- `Ret.decCall_new_leaf_lf`: call `htab_new_leaf(et, ekey, eval_)` under `LocFreePost Φ`! -/
theorem Ret.decCall_new_leaf_lf {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {x : MlS} {et ekey eval_ : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (tw keyw valw : BitVec 64) (A Fr0 : List Nat)
    (het : evalAt s0 et = some (.val (.word tw)))
    (hekey : evalAt s0 ekey = some (.val (.word keyw)))
    (heval : evalAt s0 eval_ = some (.val (.word valw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hcnt_le : hdr s0 tw.toNat 3 ≤ A.length)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i)
    (hk : ∀ (nlw : BitVec 64) (Fr1 : List Nat) (s1 : PanSemStateFiniteExact 64 F),
      ArenaReady s1 →
      NodeState s1 tw.toNat (A ++ [nlw.toNat]) Fr1 →
      hdr s1 tw.toNat 0 = hdr s0 tw.toNat 0 →
      hdr s1 tw.toNat 1 = hdr s0 tw.toNat 1 →
      hdr s1 tw.toNat 3 = hdr s0 tw.toNat 3 + 1 →
      hdr s1 tw.toNat 7 = hdr s0 tw.toNat 7 →
      nodeF s1 (hdr s1 tw.toNat 5) nlw.toNat 0 = 0 →
      nodeF s1 (hdr s1 tw.toNat 5) nlw.toNat 8 = valw.toNat →
      nodeF s1 (hdr s1 tw.toNat 5) nlw.toNat 16 = hdr s0 tw.toNat 3 →
      nodeF s1 (hdr s1 tw.toNat 5) nlw.toNat 24 = 8 * hdr s0 tw.toNat 0 →
      memW s1 (hdr s1 tw.toNat 6 + 8 * hdr s0 tw.toNat 3) = nlw.toNat →
      (∀ z ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        nodeF s1 (hdr s1 tw.toNat 5) z off = nodeF s0 (hdr s0 tw.toNat 5) z off) →
      (∀ i, i < hdr s0 tw.toNat 3 →
        memW s1 (hdr s1 tw.toNat 6 + 8 * i) = memW s0 (hdr s0 tw.toNat 6 + 8 * i)) →
      globN s0 "heap_ptr" ≤ globN s1 "heap_ptr" →
      (∀ i ∈ htabFootprint s1 tw.toNat, Allocated s1 i ∧
        ((∃ j ∈ htabFootprint s0 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
          Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s1 "heap_ptr" - globN s0 "heap_ptr")))) →
      FrameOutside s0 s1 (htabFootprint s0 tw.toNat) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") →
      (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
        s0.globals.lookup k = s1.globals.lookup k) →
      s1.locals = s0.locals →
      Ret (setVarHOLFinite x (.val (.word nlw)) s1) cont Φ) :
    Ret s0 (.decCall x .one (ofString "htab_new_leaf") [et, ekey, eval_] cont) Φ := by
  refine Ret.decCall3_lf hLF hA0.1.code (by decide) (by decide) (by decide)
    lookup_htab_new_leaf tw keyw valw het hekey heval ?_
  intro nlw post hrun
  let entry := callEntryStateHOLFinite s0
    (((HolFiniteMapExact.empty.update (ofString "t", .val (.word tw))).update
      (ofString "key", .val (.word keyw))).update (ofString "value", .val (.word valw)))
  have hspec := htab_new_leaf_body_spec entry tw keyw valw A Fr0
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "value" ≠ ofString "t" by decide, show ofString "key" ≠ ofString "t" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "value" ≠ ofString "key" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩ hNS0 hcnt_le hal0
    (.val (.word nlw)) (by rw [hrun])
  rw [hrun] at hspec
  obtain ⟨nlw', Fr1, heq, hAp, hNSp, hh0, hh1, hh3, hh7, n0, n8, n16, n24, ordc, hnd, hord, hhp, hfp, hfr, hg⟩ := hspec
  injection heq with h1; injection h1 with h2; subst h2
  let s1 := { post with locals := s0.locals }
  exact hk nlw Fr1 s1
    ⟨guestInv_congr (s := post) rfl rfl rfl rfl hAp.1, hAp.2⟩
    hNSp hh0 hh1 hh3 hh7 n0 n8 n16 n24 ordc hnd hord hhp hfp hfr hg rfl

/-- `Ret.decCall_new_internal_lf`: call `htab_new_internal(et, ebit)` under `LocFreePost Φ`! -/
theorem Ret.decCall_new_internal_lf {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {x : MlS} {et ebit : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (tw bitw : BitVec 64) (A Fr0 : List Nat)
    (het : evalAt s0 et = some (.val (.word tw)))
    (hebit : evalAt s0 ebit = some (.val (.word bitw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i)
    (hk : ∀ (niw : BitVec 64) (Fr1 : List Nat) (s1 : PanSemStateFiniteExact 64 F),
      ArenaReady s1 →
      NodeState s1 tw.toNat (A ++ [niw.toNat]) Fr1 →
      hdr s1 tw.toNat 0 = hdr s0 tw.toNat 0 →
      hdr s1 tw.toNat 1 = hdr s0 tw.toNat 1 →
      hdr s1 tw.toNat 3 = hdr s0 tw.toNat 3 →
      hdr s1 tw.toNat 7 = hdr s0 tw.toNat 7 →
      hdr s0 tw.toNat 10 ≤ hdr s1 tw.toNat 10 →
      nodeF s1 (hdr s1 tw.toNat 5) niw.toNat 0 = 0 →
      nodeF s1 (hdr s1 tw.toNat 5) niw.toNat 8 = 0 →
      nodeF s1 (hdr s1 tw.toNat 5) niw.toNat 16 = 0 →
      nodeF s1 (hdr s1 tw.toNat 5) niw.toNat 24 = bitw.toNat →
      (∀ z ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        nodeF s1 (hdr s1 tw.toNat 5) z off = nodeF s0 (hdr s0 tw.toNat 5) z off) →
      (∀ i, i < hdr s0 tw.toNat 10 + 1 →
        memW s1 (hdr s1 tw.toNat 6 + 8 * i) = memW s0 (hdr s0 tw.toNat 6 + 8 * i)) →
      globN s0 "heap_ptr" ≤ globN s1 "heap_ptr" →
      (∀ i ∈ htabFootprint s1 tw.toNat, Allocated s1 i ∧
        ((∃ j ∈ htabFootprint s0 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
          Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s1 "heap_ptr" - globN s0 "heap_ptr")))) →
      FrameOutside s0 s1 (htabFootprint s0 tw.toNat) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") →
      (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
        s0.globals.lookup k = s1.globals.lookup k) →
      s1.locals = s0.locals →
      Ret (setVarHOLFinite x (.val (.word niw)) s1) cont Φ) :
    Ret s0 (.decCall x .one (ofString "htab_new_internal") [et, ebit] cont) Φ := by
  refine Ret.decCall2_lf hLF hA0.1.code (by decide)
    lookup_htab_new_internal tw bitw het hebit ?_
  intro niw post hrun
  let entry := callEntryStateHOLFinite s0
    ((HolFiniteMapExact.empty.update (ofString "t", .val (.word tw))).update
      (ofString "bit", .val (.word bitw)))
  have hspec := htab_new_internal_body_spec entry tw bitw A Fr0
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "bit" ≠ ofString "t" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩ hNS0 hal0
    (.val (.word niw)) (by rw [hrun])
  rw [hrun] at hspec
  obtain ⟨niw', Fr1, heq, hAp, hNSp, hh0, hh1, hh3, hh7, hnc_le, n0, n8, n16, n24, hnd, hord, hhp, hfp, hfr, hg⟩ := hspec
  injection heq with h1; injection h1 with h2; subst h2
  let s1 := { post with locals := s0.locals }
  exact hk niw Fr1 s1
    ⟨guestInv_congr (s := post) rfl rfl rfl rfl hAp.1, hAp.2⟩
    hNSp hh0 hh1 hh3 hh7 hnc_le n0 n8 n16 n24 hnd hord hhp hfp hfr hg rfl

end InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

/-! ### From SoloHtabSetMain.lean -/

/-! Proof of `htab_set_body_spec` and `htab_set_spec_proof` (`FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set")`). -/


namespace InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Entry Parameter Extraction and Postcondition Local-Insensitivity -/

theorem three_word_params_of_lookupCode {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname p1 p2 p3 : MlS)
    (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (body : ProgHOL 64) (retShape : ShapeHOL)
    (hc : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    (values : List (ValueHOL 64))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, s.locals, retShape)) :
    ∃ w1 w2 w3 : BitVec 64,
      s.locals.lookup p1 = some (.val (.word w1)) ∧
      s.locals.lookup p2 = some (.val (.word w2)) ∧
      s.locals.lookup p3 = some (.val (.word w3)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup fname values body s.locals retShape hl
  unfold lookupCodeHOLExact at hx
  rw [hc] at hx
  dsimp only at hx
  split at hx
  · rename_i hcond
    injection hx with hx_eq
    have hmap := congrArg (fun x => x.2.1) hx_eq
    rcases values with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
    · simp at hcond
    · simp at hcond
    · simp at hcond
    · have hall := hcond.2.2
      simp only [List.zip, List.all, Bool.and_true, Bool.and_eq_true] at hall
      have h1w : ∃ w1, v1 = .val (.word w1) := by
        rcases v1 with ⟨⟨w1⟩⟩ | _ | _
        · exact ⟨w1, rfl⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
      have h2w : ∃ w2, v2 = .val (.word w2) := by
        rcases v2 with ⟨⟨w2⟩⟩ | _ | _
        · exact ⟨w2, rfl⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
      have h3w : ∃ w3, v3 = .val (.word w3) := by
        rcases v3 with ⟨⟨w3⟩⟩ | _ | _
        · exact ⟨w3, rfl⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
      obtain ⟨w1, rfl⟩ := h1w
      obtain ⟨w2, rfl⟩ := h2w
      obtain ⟨w3, rfl⟩ := h3w
      refine ⟨w1, w2, w3, ?_, ?_, ?_⟩
      · have := congrFun hmap.symm p1
        simpa [List.map, List.zip, List.foldl, hne13, hne12] using this
      · have := congrFun hmap.symm p2
        simpa [List.map, List.zip, List.foldl, hne23] using this
      · have := congrFun hmap.symm p3
        simpa [List.map, List.zip, List.foldl] using this
    · simp at hcond
  · cases hx

theorem locFree_htabExitAt {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat) :
    LocFreePost (fun _ post => HtabExitAt t s0 post) := by
  intro _ post L' h
  have hs0 : { s0 with locals := s0.locals, clock := s0.clock } = s0 := by cases s0; rfl
  have hp : { post with locals := post.locals, clock := post.clock } = post := by cases post; rfl
  have h1 := (htabExitAt_locals t s0 post s0.locals L' s0.clock post.clock).mp (by rw [hs0]; exact h)
  have h2 := (htabExitAt_locals t s0 post s0.locals post.locals s0.clock post.clock).mpr h1
  rw [hs0, hp] at h2
  exact h2

theorem storeW_mem {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {ed ee : ExpHOL 64} (a w : BitVec 64)
    (hed : evalAt s ed = some (.val (.word a)))
    (hee : evalAt s ee = some (.val (.word w)))
    (hu : evaluateHOLFiniteState s (.store ed ee) = (none, u)) :
    s.memaddrs a ∧ u = { s with memory := updW s.memory a w } := by
  rw [evaluateHOLFiniteState_store] at hu
  unfold evalAt at hed hee
  rw [hed] at hu; dsimp only at hu
  rw [hee] at hu; dsimp only at hu
  rcases hm : @panMemStoresHOL 64 _ a (flattenHOL (.val (.word w))) s.memaddrs
    (fun addr => Classical.propDecidable (s.memaddrs addr)) s.memory with _ | m
  · rw [hm] at hu; simp at hu
  · rw [hm] at hu
    injection hu with _ hteq
    obtain ⟨hdom, rfl⟩ := stores_word _ hm
    exact ⟨hdom, hteq.symm⟩

/-! ## 2. Sub-proof A: Empty Table Insertion (`leaf == 0`) -/

theorem htab_set_branch_empty {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F)
    (tw keyw valw : BitVec 64)
    (hLF : LocFreePost (fun _ post => HtabExitAt tw.toNat s0 post))
    (hs_fr : LocFrame s0 s)
    (hA0 : ArenaReady s0)
    (hW0 : HtabWF s0 tw.toNat)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i)
    (hcnt0 : hdr s0 tw.toNat 3 = 0)
    (ht_s : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey_s : s.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hval_s : s.locals.lookup (ofString "value") = some (.val (.word valw))) :
    Ret s
      (.decCall (ofString "nl") .one (ofString "htab_new_leaf")
        [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")]
        (.seq
          (.store (.op .add [.var .local (ofString "t"), .const 56#64]) (.var .local (ofString "nl")))
          (.return (.const 0#64))))
      (fun _ post => HtabExitAt tw.toNat s0 post) := by
  set t := tw.toNat
  have hmem_s : s.memory = s0.memory := hs_fr.memory
  have hg_s : s.globals = s0.globals := by unfold LocFrame at hs_fr; rw [hs_fr]
  obtain ⟨hB0, L0, I0, Fr0, hT0⟩ := (htabWF_iff s0 t).mp hW0
  have hL0_nil : L0 = [] := List.eq_nil_of_length_eq_zero (hT0.1.trans hcnt0)
  have hI0_nil : I0 = [] := by
    rcases hT0.2.2.2.1 with ⟨_, hI⟩ | hlen
    · exact hI
    · omega
  subst hL0_nil hI0_nil
  have hNS_s : NodeState s t [] Fr0 := by
    have hNS0 : NodeState s0 t [] Fr0 :=
      ⟨hB0, by simpa using hT0.2.1, by simpa using hT0.2.2.1, hT0.2.2.2.2.2.2.2.2.2.2.2⟩
    unfold LocFrame at hs_fr; rw [hs_fr]; exact hNS0
  have hA_s : ArenaReady s := by unfold LocFrame at hs_fr; rw [hs_fr]; exact (arenaReady_locals s0 _ _).mpr hA0
  have hal_s : ∀ i ∈ htabFootprint s t, Allocated s i := by
    unfold LocFrame at hs_fr; rw [hs_fr]; exact hal0
  have hcnt_s : hdr s t 3 ≤ ([] : List Nat).length := by
    have : hdr s t 3 = 0 := by unfold hdr memW; rw [hmem_s]; exact hcnt0
    omega
  refine Ret.decCall_new_leaf_lf hLF tw keyw valw [] Fr0
    (by simp [evalAt, evalHOLExact, ht_s])
    (by simp [evalAt, evalHOLExact, hkey_s])
    (by simp [evalAt, evalHOLExact, hval_s])
    hA_s hNS_s hcnt_s hal_s ?_
  intro nlw Fr1 s1 hA1 hNS1 hh0_1 hh1_1 hh3_1 _ n0_1 _ n16_1 n24_1 ordc_1 _ _ hhp_1 hfp_1 hfr_1 hg_1 hloc_1
  change NodeState s1 t [nlw.toNat] Fr1 at hNS1
  have hh0_s : hdr s t 0 = hdr s0 t 0 := by unfold hdr memW; rw [hmem_s]
  have hh1_s : hdr s t 1 = hdr s0 t 1 := by unfold hdr memW; rw [hmem_s]
  have hh3_s : hdr s t 3 = 0 := by unfold hdr memW; rw [hmem_s]; exact hcnt0
  have hfp_s : htabFootprint s t = htabFootprint s0 t := by
    simp [htabFootprint, hdr, memW, hmem_s]
  have hgn_s : globN s "heap_ptr" = globN s0 "heap_ptr" := by unfold globN; rw [hg_s]
  obtain ⟨hB1, hnodup1, hmem1, hfc1⟩ := hNS1
  obtain ⟨hnc1_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB1
  have hhe : heapEnd = 33806089704 := rfl
  -- Now execute `store(t + 56, nl); return 0` via `NS`!
  let L_nl := s.locals.update (ofString "nl", .val (.word nlw))
  have ht_nl : L_nl.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [L_nl, HolFiniteMapExact.lookup_update, FUPDATE, ht_s, show ofString "nl" ≠ ofString "t" by decide]
  have hnl_lk : L_nl.lookup (ofString "nl") = some (.val (.word nlw)) := by
    simp [L_nl, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_nl_eq : setVarHOLFinite (ofString "nl") (.val (.word nlw)) s1 = NS s1 L_nl s1.globals s1.memory s1.clock := by
    simp [setVarHOLFinite, NS, hloc_1, L_nl]
  rw [hs1_nl_eq]
  refine Ret.ns_storeW (tw + 56#64) nlw
    (by
      have h560 : 56#64 + (0 : BitVec 64) = 56#64 := rfl
      simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
        ht_nl, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
        valueIsWord, valueWord, wordOpHOL, wordOp, h560])
    (by simp [evalAt, evalHOLExact, hnl_lk]) ?_
  intro _
  apply Ret.ns_ret; intro _ _
  let s_end := NS s1 HolFiniteMapExact.empty s1.globals (updW s1.memory (tw + 56#64) nlw) s1.clock
  have htw56_eq : BitVec.ofNat 64 (t + 8 * 7) = tw + 56#64 := ofNat_add_toNat tw 56
  have hne_hdr : ∀ k < 11, k ≠ 7 → BitVec.ofNat 64 (t + 8 * k) ≠ tw + 56#64 := by
    intro k hk hne; rw [← htw56_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
  obtain ⟨hB_end, hfp_end⟩ := htabBlocks_updW_nonlayout (tw + 56#64) nlw hB1
    (hne_hdr 0 (by omega) (by omega)) (hne_hdr 1 (by omega) (by omega))
    (hne_hdr 4 (by omega) (by omega)) (hne_hdr 5 (by omega) (by omega))
    (hne_hdr 6 (by omega) (by omega)) (hne_hdr 10 (by omega) (by omega))
    (fun h8 => absurd h8 (hne_hdr 8 (by omega) (by omega)))
  have hsep1 := htabBlocks_cell_sep hB1
  have hh0_end : hdr s_end t 0 = hdr s0 t 0 :=
    (memW_updW_other s1 _ _ _ (hne_hdr 0 (by omega) (by omega))).trans (hh0_1.trans hh0_s)
  have hh1_end : hdr s_end t 1 = hdr s0 t 1 :=
    (memW_updW_other s1 _ _ _ (hne_hdr 1 (by omega) (by omega))).trans (hh1_1.trans hh1_s)
  have hh3_end : hdr s_end t 3 = 1 := by
    have h1 : hdr s_end t 3 = hdr s1 t 3 := memW_updW_other s1 _ _ _ (hne_hdr 3 (by omega) (by omega))
    have h2 : hdr s1 t 3 = hdr s t 3 + 1 := hh3_1
    omega
  have hh5_end : hdr s_end t 5 = hdr s1 t 5 := memW_updW_other s1 _ _ _ (hne_hdr 5 (by omega) (by omega))
  have hh6_end : hdr s_end t 6 = hdr s1 t 6 := memW_updW_other s1 _ _ _ (hne_hdr 6 (by omega) (by omega))
  have hh7_end : hdr s_end t 7 = nlw.toNat := by
    change memW { s1 with memory := updW s1.memory (tw + 56#64) nlw } (t + 8 * 7) = nlw.toNat
    unfold memW; rw [htw56_eq]; simp [updW]
  have hh8_end : hdr s_end t 8 = hdr s1 t 8 := memW_updW_other s1 _ _ _ (hne_hdr 8 (by omega) (by omega))
  have hh9_end : hdr s_end t 9 = hdr s1 t 9 := memW_updW_other s1 _ _ _ (hne_hdr 9 (by omega) (by omega))
  have hnd_end : ∀ x < hdr s1 t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s_end (hdr s1 t 5) x off = nodeF s1 (hdr s1 t 5) x off := by
    intro x hx off hoff
    unfold nodeF
    apply memW_updW_other s1
    rw [← htw56_eq]
    exact (hsep1.1 7 (by omega) x hx off hoff).symm
  have hnl_rng : 1 ≤ nlw.toNat ∧ nlw.toNat < hdr s1 t 8 :=
    (hmem1 nlw.toNat).mp (List.mem_append_left _ (by simp))
  have hnl_lt_nc1 : nlw.toNat < hdr s1 t 10 + 1 := by have := hB1.2.2.2.2.2.2.2; omega
  have h0_lt_nc1 : 0 < hdr s1 t 10 + 1 := by omega
  have hord0_end : memW s_end (hdr s_end t 6 + 8 * 0) = nlw.toNat := by
    rw [hh6_end]
    have h1 : memW s_end (hdr s1 t 6 + 8 * 0) = memW s1 (hdr s1 t 6 + 8 * 0) := by
      apply memW_updW_other s1; rw [← htw56_eq]; exact (hsep1.2.1 7 (by omega) 0 h0_lt_nc1).symm
    have h2 : memW s1 (hdr s1 t 6 + 8 * 0) = nlw.toNat := by
      have hc0 : hdr s tw.toNat 3 = 0 := hh3_s
      rw [hc0] at ordc_1; exact ordc_1
    exact h1.trans h2
  have hfc_end : FreeChainF (nodeF s_end (hdr s_end t 5)) (hdr s_end t 9) Fr1 := by
    rw [hh5_end, hh9_end]
    refine FreeChainF.congr Fr1 _ ?_ hfc1
    intro f hf
    have hf_rng := (hmem1 f).mp (List.mem_append_right _ hf)
    have := hB1.2.2.2.2.2.2.2
    exact hnd_end f (by omega) 0 (Or.inl rfl)
  have hT_end : TreeWF [nlw.toNat] [] Fr1 (hdr s_end t 8) (hdr s_end t 0) (hdr s_end t 3)
      (hdr s_end t 7) (hdr s_end t 9) (nodeF s_end (hdr s_end t 5))
      (fun i => memW s_end (hdr s_end t 6 + 8 * i)) := by
    rw [hh3_end, hh7_end, hh0_end]
    apply TreeWF.insert_empty
    · simpa using hnodup1
    · intro x; rw [hh8_end]; simpa using hmem1 x
    · exact hfc_end
    · exact hord0_end
    · rw [hh5_end, hnd_end nlw.toNat hnl_lt_nc1 0 (Or.inl rfl)]; exact n0_1
    · rw [hh5_end, hnd_end nlw.toNat hnl_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl)))]
      exact n16_1.trans hh3_s
    · rw [hh5_end, hnd_end nlw.toNat hnl_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl)))]
      exact n24_1.trans (congrArg (8 * ·) hh0_s)
  have hW_end : HtabWF s_end t := (htabWF_iff s_end t).mpr ⟨hB_end, [nlw.toNat], [], Fr1, hT_end⟩
  have hfr_s0_s1 : FrameOutside s0 s1 (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
    intro x hxk hxf
    have hm1 := hfr_1 x (by rw [hfp_s]; exact hxk) (by rw [hgn_s]; exact hxf)
    rw [hm1, hmem_s]
  have htw56_hit : (∃ j ∈ htabFootprint s0 t, CellHits (tw + 56#64).toNat j) ∨
      CellHits (tw + 56#64).toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
    have htw56_nat : (tw + 56#64).toNat = t + 56 := by rw [BitVec.toNat_add, show (56#64).toNat = 56 from rfl]; omega
    exact Or.inl ⟨(t, 88), by simp [htabFootprint], by rw [htw56_nat]; exact ⟨by omega, by omega⟩⟩
  have hfr_end : FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") :=
    frameOutside_updW_mem s0 s1 s1.memory rfl (tw + 56#64) nlw _ _ hfr_s0_s1 htw56_hit s_end rfl
  refine ⟨⟨guestInv_congr (s := s1) rfl rfl rfl rfl hA1.1, hA1.2⟩,
    hW_end, hh0_end, hh1_end,
    by change globN s0 "heap_ptr" ≤ globN s1 "heap_ptr"; rw [← hgn_s]; exact hhp_1,
    ?_, hfr_end,
    fun k hk => by rw [← hg_s]; exact hg_1 k hk⟩
  · change ∀ iv ∈ htabFootprint { s1 with memory := updW s1.memory (tw + 56#64) nlw } t, Allocated s1 iv ∧ _
    rw [hfp_end]
    intro iv hiv
    obtain ⟨hal_iv, hprov⟩ := hfp_1 iv hiv
    rw [hfp_s, hgn_s] at hprov
    exact ⟨hal_iv, hprov⟩

/-! ## 3. Sub-proof B: Key Match Overwrite (`eq != 0`) -/

theorem htab_set_branch_overwrite {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F)
    (tw leafw valw : BitVec 64)
    (hs_fr : LocFrame s0 s)
    (hA0 : ArenaReady s0)
    (hW0 : HtabWF s0 tw.toNat)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i)
    (hleaf_mem : ∀ L I Fr, TreeWF L I Fr (hdr s0 tw.toNat 8) (hdr s0 tw.toNat 0) (hdr s0 tw.toNat 3)
      (hdr s0 tw.toNat 7) (hdr s0 tw.toNat 9) (nodeF s0 (hdr s0 tw.toNat 5))
      (fun i => memW s0 (hdr s0 tw.toNat 6 + 8 * i)) → leafw.toNat ∈ L)
    (ht_s : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hleaf_s : s.locals.lookup (ofString "leaf") = some (.val (.word leafw)))
    (hval_s : s.locals.lookup (ofString "value") = some (.val (.word valw))) :
    Ret s
      (.seq
        (.store (.op .add [
            .load .one (.op .add [.var .local (ofString "t"), .const 40#64]),
            .panop .mul [.var .local (ofString "leaf"), .const 32#64],
            .const 8#64])
          (.var .local (ofString "value")))
        (.return (.const 0#64)))
      (fun _ post => HtabExitAt tw.toNat s0 post) := by
  set t := tw.toNat
  have hmem_s : s.memory = s0.memory := hs_fr.memory
  have hma_s : s.memaddrs = s0.memaddrs := by unfold LocFrame at hs_fr; rw [hs_fr]
  have hg_s : s.globals = s0.globals := by unfold LocFrame at hs_fr; rw [hs_fr]
  obtain ⟨hB0, L0, I0, Fr0, hT0⟩ := (htabWF_iff s0 t).mp hW0
  have hleaf_L0 : leafw.toNat ∈ L0 := hleaf_mem L0 I0 Fr0 hT0
  have hleaf_rng := (hT0.2.2.1 leafw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ hleaf_L0))
  have hleaf_lt_nc0 : leafw.toNat < hdr s0 t 10 + 1 := by have := hB0.2.2.2.2.2.2.2; omega
  obtain ⟨hnc0_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB0
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom0_t5, hm0_t5⟩ := word_of_hdr s0 tw 5 (by omega) hB0
  set ndw := BitVec.ofNat 64 (hdr s0 t 5)
  have hndw_nat : ndw.toNat = hdr s0 t 5 := by
    have hnd0_in := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd0_in; rw [BitVec.toNat_ofNat]; omega
  have hed : evalAt s (.op .add [
      .load .one (.op .add [.var .local (ofString "t"), .const 40#64]),
      .panop .mul [.var .local (ofString "leaf"), .const 32#64],
      .const 8#64]) =
      some (.val (.word (ndw + leafw * 32#64 + 8#64))) := by
    have hdom40 : s.memaddrs (tw + 40#64) := by rw [hma_s]; exact hdom0_t5
    have hm40 : s.memory (tw + 40#64) = .word ndw := by rw [hmem_s]; exact hm0_t5
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
      ht_s, hleaf_s, isWfShapeExactHOL, memLoadHOLExact,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
    have h400 : 40#64 + (0 : BitVec 64) = 40#64 := rfl
    rw [h400]
    simp only [hdom40, hm40, ↓reduceIte, List.all, List.map, Bool.and_self, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    have hz : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
    rw [hz, BitVec.add_assoc]
  have hs_ns : s = NS s0 s.locals s0.globals s0.memory s.clock := by
    unfold LocFrame at hs_fr
    exact hs_fr
  rw [hs_ns]
  refine Ret.ns_storeW (ndw + leafw * 32#64 + 8#64) valw
    (by rw [← hs_ns]; exact hed)
    (by simp [evalAt, evalHOLExact, hval_s]) ?_
  intro _
  apply Ret.ns_ret; intro _ _
  -- State returned is `NS s0 HolFiniteMapExact.empty s0.globals (updW s0.memory addr valw) s.clock`!
  set addr := ndw + leafw * 32#64 + 8#64
  have haddr_eq : addr = BitVec.ofNat 64 (hdr s0 t 5 + 32 * leafw.toNat + 8) := by
    dsimp [addr]; rw [← hndw_nat]; exact (ofNat_node_addr ndw leafw 8).symm
  let s_end := NS s0 HolFiniteMapExact.empty s0.globals (updW s0.memory addr valw) s.clock
  have hsep0 := htabBlocks_cell_sep hB0
  have hne_hdr : ∀ k < 11, BitVec.ofNat 64 (t + 8 * k) ≠ addr := by
    intro k hk; rw [haddr_eq]; exact hsep0.1 k hk leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl))
  obtain ⟨hB_end, hfp_end⟩ := htabBlocks_updW_nonlayout addr valw hB0
    (hne_hdr 0 (by omega)) (hne_hdr 1 (by omega))
    (hne_hdr 4 (by omega)) (hne_hdr 5 (by omega))
    (hne_hdr 6 (by omega)) (hne_hdr 10 (by omega))
    (fun h8 => absurd h8 (hne_hdr 8 (by omega)))
  have hh0_end : hdr s_end t 0 = hdr s0 t 0 := memW_updW_other s0 _ _ _ (hne_hdr 0 (by omega))
  have hh1_end : hdr s_end t 1 = hdr s0 t 1 := memW_updW_other s0 _ _ _ (hne_hdr 1 (by omega))
  have hh3_end : hdr s_end t 3 = hdr s0 t 3 := memW_updW_other s0 _ _ _ (hne_hdr 3 (by omega))
  have hh5_end : hdr s_end t 5 = hdr s0 t 5 := memW_updW_other s0 _ _ _ (hne_hdr 5 (by omega))
  have hh6_end : hdr s_end t 6 = hdr s0 t 6 := memW_updW_other s0 _ _ _ (hne_hdr 6 (by omega))
  have hh7_end : hdr s_end t 7 = hdr s0 t 7 := memW_updW_other s0 _ _ _ (hne_hdr 7 (by omega))
  have hh8_end : hdr s_end t 8 = hdr s0 t 8 := memW_updW_other s0 _ _ _ (hne_hdr 8 (by omega))
  have hh9_end : hdr s_end t 9 = hdr s0 t 9 := memW_updW_other s0 _ _ _ (hne_hdr 9 (by omega))
  have hnd_L0_I0 : (L0 ++ I0).Nodup := (List.nodup_append.mp hT0.2.1).1
  have hleaf_not_I0 : leafw.toNat ∉ I0 := fun hI =>
    (List.nodup_append.mp hnd_L0_I0).2.2 leafw.toNat hleaf_L0 leafw.toNat hI rfl
  have hT_end : TreeWF L0 I0 Fr0 (hdr s_end t 8) (hdr s_end t 0) (hdr s_end t 3)
      (hdr s_end t 7) (hdr s_end t 9) (nodeF s_end (hdr s_end t 5))
      (fun i => memW s_end (hdr s_end t 6 + 8 * i)) := by
    rw [hh8_end, hh0_end, hh3_end, hh7_end, hh9_end, hh5_end, hh6_end]
    apply TreeWF.overwrite_leaf_value hT0
    · intro x hx
      have hx_rng := (hT0.2.2.1 x).mp hx
      have := hB0.2.2.2.2.2.2.2
      unfold nodeF; apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.2.1 x (by omega) 0 (Or.inl rfl) leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    · intro x hx
      have hx_rng := (hT0.2.2.1 x).mp (List.mem_append_left _ hx)
      have := hB0.2.2.2.2.2.2.2
      unfold nodeF; apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.2.1 x (by omega) 16 (Or.inr (Or.inr (Or.inl rfl))) leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    · intro x hx
      have hx_rng := (hT0.2.2.1 x).mp (List.mem_append_left _ hx)
      have := hB0.2.2.2.2.2.2.2
      unfold nodeF; apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.2.1 x (by omega) 24 (Or.inr (Or.inr (Or.inr rfl))) leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    · intro x hxI
      have hx_ne : x ≠ leafw.toNat := fun h => hleaf_not_I0 (h ▸ hxI)
      have hx_rng := (hT0.2.2.1 x).mp (List.mem_append_left _ (List.mem_append_right _ hxI))
      have := hB0.2.2.2.2.2.2.2
      unfold nodeF; apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.2.1 x (by omega) 8 (Or.inr (Or.inl rfl)) leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) (Or.inl hx_ne)
    · intro i hi
      have hLlen : L0.length ≤ hdr s0 t 10 := by
        have hle := nodup_len_le_range (List.nodup_append.mp hnd_L0_I0).1
          (fun x hx => (hT0.2.2.1 x).mp (List.mem_append_left _ (List.mem_append_left _ hx)))
        have := hB0.2.2.2.2.2.2.2
        omega
      apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.1 leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) i (by omega)
  have hW_end : HtabWF s_end t := (htabWF_iff s_end t).mpr ⟨hB_end, L0, I0, Fr0, hT_end⟩
  have hhit_addr : (∃ j ∈ htabFootprint s0 t, CellHits addr.toNat j) ∨ CellHits addr.toNat (globN s0 "heap_ptr", 0) := by
    have hnd0_in := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd0_in
    have ha_nat : addr.toNat = hdr s0 t 5 + 32 * leafw.toNat + 8 := by
      rw [haddr_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Or.inl ⟨(hdr s0 t 5, (hdr s0 t 10 + 1) * 32), by simp [htabFootprint], by rw [ha_nat]; exact ⟨by omega, by omega⟩⟩
  have hfr_end : FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", 0) :=
    frameOutside_updW_mem s0 s0 s0.memory rfl addr valw _ _ (fun _ _ _ => rfl) hhit_addr s_end rfl
  refine ⟨⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩,
    hW_end, hh0_end, hh1_end, le_rfl,
    ?_,
    by change FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s0 "heap_ptr" - globN s0 "heap_ptr")
       rw [Nat.sub_self]; exact hfr_end,
    fun _ _ => rfl⟩
  · change ∀ iv ∈ htabFootprint { s0 with memory := updW s0.memory addr valw } t, Allocated s0 iv ∧ _
    rw [hfp_end]
    intro iv hiv
    exact ⟨hal0 iv hiv, Or.inl ⟨iv, hiv, le_rfl, le_rfl⟩⟩

/-! ## 4. Sub-proof C: Crit-Bit Splice Tail (after `htab_new_leaf` and `htab_new_internal`) -/

theorem Ret.ns_seq_storeW2 {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {d1 e1 d2 e2 : ExpHOL 64} {b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a1 w1 a2 w2 : BitVec 64)
    (hd1 : evalAt (NS s L G M C) d1 = some (.val (.word a1)))
    (he1 : evalAt (NS s L G M C) e1 = some (.val (.word w1)))
    (hd2 : evalAt (NS s L G (updW M a1 w1) C) d2 = some (.val (.word a2)))
    (he2 : evalAt (NS s L G (updW M a1 w1) C) e2 = some (.val (.word w2)))
    (hb : s.memaddrs a1 → s.memaddrs a2 → Ret (NS s L G (updW (updW M a1 w1) a2 w2) C) b Φ) :
    Ret (NS s L G M C) (.seq (.seq (.store d1 e1) (.store d2 e2)) b) Φ := by
  refine Ret.seq ?_ ?_
  · intro v hv
    rw [evaluateHOLFiniteState_seq_line780] at hv
    rcases hr1 : evaluateHOLFiniteState (NS s L G M C) (.store d1 e1) with ⟨r1, m1⟩
    rw [hr1] at hv
    cases r1 with
    | none =>
      have := (evaluate_store_control_frame m1 d2 e2).1
      rcases this with h | h <;> rw [h] at hv <;> simp at hv
    | some _ =>
      have := (evaluate_store_control_frame (NS s L G M C) d1 e1).1
      rw [hr1] at this
      rcases this with h | h <;> simp at h <;> subst h <;> simp at hv
  · intro t2 ht2
    obtain ⟨m1, hm1, hm2⟩ := (by
      rw [evaluateHOLFiniteState_seq_line780] at ht2
      rcases hr : evaluateHOLFiniteState (NS s L G M C) (.store d1 e1) with ⟨r1, m⟩
      rw [hr] at ht2
      cases r1 with
      | none => exact ⟨m, rfl, ht2⟩
      | some _ => simp at ht2 : ∃ m1, evaluateHOLFiniteState (NS s L G M C) (.store d1 e1) = (none, m1) ∧
          evaluateHOLFiniteState m1 (.store d2 e2) = (none, t2))
    obtain ⟨ha1, hm1_eq⟩ := storeW_mem a1 w1 hd1 he1 hm1
    have hd2' : evalAt m1 d2 = some (.val (.word a2)) := by rw [hm1_eq]; exact hd2
    have he2' : evalAt m1 e2 = some (.val (.word w2)) := by rw [hm1_eq]; exact he2
    obtain ⟨ha2, hm2_eq⟩ := storeW_mem a2 w2 hd2' he2' hm2
    have ha2' : s.memaddrs a2 := by rw [hm1_eq] at ha2; exact ha2
    have ht2_eq : t2 = NS s L G (updW (updW M a1 w1) a2 w2) C := by
      rw [hm2_eq, hm1_eq]; rfl
    rw [ht2_eq]
    exact hb ha1 ha2'

theorem eval_node_field_expr {F : Type} (st : PanSemStateFiniteExact 64 F)
    (x : MlS) (ndw xw : BitVec 64) (off : Nat)
    (hnd : st.locals.lookup (ofString "nodes") = some (.val (.word ndw)))
    (hx : st.locals.lookup x = some (.val (.word xw))) :
    evalAt st (.op .add [.var .local (ofString "nodes"),
      .panop .mul [.var .local x, .const 32#64],
      .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (ndw + xw * 32#64 + BitVec.ofNat 64 off))) := by
  simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnd, hx,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
    Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
  rw [hz, BitVec.add_assoc]

theorem htab_set_splice_memory_wf {F : Type}
    (s0 s2 : PanSemStateFiniteExact 64 F)
    (tw dw pw nw nlw niw : BitVec 64)
    (L0 I0 Fr0 Fr2 : List Nat)
    (ch_left : Bool)
    (m_final : BitVec 64 → HolWordLab 64)
    (hm_final :
      let ndw := BitVec.ofNat 64 (hdr s2 tw.toNat 5)
      let m3 := updW (updW (updW s2.memory
                  (ndw + niw * 32#64 + 0#64) pw)
                  (ndw + nlw * 32#64 + 0#64) niw)
                  (ndw + nw * 32#64 + 0#64) niw
      let m5 := if ch_left then
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
                else
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw
      m_final = if pw.toNat = 0 then
                  updW m5 (tw + 56#64) niw
                else if nodeF s0 (hdr s0 tw.toNat 5) pw.toNat 8 = nw.toNat then
                  updW m5 (ndw + pw * 32#64 + 8#64) niw
                else
                  updW m5 (ndw + pw * 32#64 + 16#64) niw)
    (hA2 : ArenaReady s2)
    (hNS2 : NodeState s2 tw.toNat (((L0 ++ I0) ++ [nlw.toNat]) ++ [niw.toNat]) Fr2)
    (hT0 : TreeWF L0 I0 Fr0
      (hdr s0 tw.toNat 8) (hdr s0 tw.toNat 0) (hdr s0 tw.toNat 3) (hdr s0 tw.toNat 7) (hdr s0 tw.toNat 9)
      (nodeF s0 (hdr s0 tw.toNat 5)) (fun i => memW s0 (hdr s0 tw.toNat 6 + 8 * i)))
    (hcnt_pos : 0 < hdr s0 tw.toNat 3)
    (hd_lt : dw.toNat < 8 * hdr s0 tw.toNat 0)
    (hnw_LI : nw.toNat ∈ L0 ++ I0)
    (hpw_spec : (pw.toNat = 0 ∧ nw.toNat = hdr s0 tw.toNat 7) ∨
      (pw.toNat ∈ I0 ∧ nw.toNat ≠ hdr s0 tw.toNat 7 ∧ pw.toNat = nodeF s0 (hdr s0 tw.toNat 5) nw.toNat 0))
    (hh0_2 : hdr s2 tw.toNat 0 = hdr s0 tw.toNat 0)
    (hh1_2 : hdr s2 tw.toNat 1 = hdr s0 tw.toNat 1)
    (hh3_2 : hdr s2 tw.toNat 3 = hdr s0 tw.toNat 3 + 1)
    (hh7_2 : hdr s2 tw.toNat 7 = hdr s0 tw.toNat 7)
    (hnl_16_2 : nodeF s2 (hdr s2 tw.toNat 5) nlw.toNat 16 = hdr s0 tw.toNat 3)
    (hnl_24_2 : nodeF s2 (hdr s2 tw.toNat 5) nlw.toNat 24 = 8 * hdr s0 tw.toNat 0)
    (hni_24_2 : nodeF s2 (hdr s2 tw.toNat 5) niw.toNat 24 = dw.toNat)
    (hord_cnt_2 : memW s2 (hdr s2 tw.toNat 6 + 8 * hdr s0 tw.toNat 3) = nlw.toNat)
    (hord_old_2 : ∀ i, i < hdr s0 tw.toNat 3 →
      memW s2 (hdr s2 tw.toNat 6 + 8 * i) = memW s0 (hdr s0 tw.toNat 6 + 8 * i))
    (hnd_old_2 : ∀ z ∈ L0 ++ I0, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s2 (hdr s2 tw.toNat 5) z off = nodeF s0 (hdr s0 tw.toNat 5) z off)
    (hhp_2 : globN s0 "heap_ptr" ≤ globN s2 "heap_ptr")
    (hfp_2 : ∀ i ∈ htabFootprint s2 tw.toNat, Allocated s2 i ∧
      ((∃ j ∈ htabFootprint s0 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s2 "heap_ptr" - globN s0 "heap_ptr"))))
    (hfr_2 : FrameOutside s0 s2 (htabFootprint s0 tw.toNat) (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr"))
    (hg_2 : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s0.globals.lookup k = s2.globals.lookup k) :
    HtabExitAt tw.toNat s0 (NS s2 HolFiniteMapExact.empty s2.globals m_final s2.clock) := by
  set t := tw.toNat
  obtain ⟨hB2, hnodup2, hmem2, hfc2⟩ := hNS2
  obtain ⟨hnc2_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB2
  have hnx2_le : hdr s2 t 8 ≤ hdr s2 t 10 + 1 := hB2.2.2.2.2.2.2.2
  have hhe : heapEnd = 33806089704 := rfl
  have hsep2 := htabBlocks_cell_sep hB2
  set ndw := BitVec.ofNat 64 (hdr s2 t 5)
  have hndw_nat : ndw.toNat = hdr s2 t 5 := by
    have hnd2_in := (hB2.1 (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd2_in; rw [BitVec.toNat_ofNat]; omega
  have haddr_nd : ∀ (xw : BitVec 64) (off : Nat),
      ndw + xw * 32#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (hdr s2 t 5 + 32 * xw.toNat + off) := by
    intro xw off; rw [← hndw_nat]; exact (ofNat_node_addr ndw xw off).symm
  -- Distinctness & bounds of `niw`, `nlw`, `nw`, `pw` from `hnodup2` and `hmem2`:
  have hperm_new : List.Perm ((L0 ++ [nlw.toNat]) ++ (I0 ++ [niw.toNat]) ++ Fr2)
      ((((L0 ++ I0) ++ [nlw.toNat]) ++ [niw.toNat]) ++ Fr2) := by
    have p0 : List.Perm ([nlw.toNat] ++ I0) (I0 ++ [nlw.toNat]) := List.perm_append_comm
    have p1 : List.Perm (L0 ++ ([nlw.toNat] ++ I0)) (L0 ++ (I0 ++ [nlw.toNat])) := p0.append_left L0
    have p2 : List.Perm ((L0 ++ ([nlw.toNat] ++ I0)) ++ [niw.toNat]) ((L0 ++ (I0 ++ [nlw.toNat])) ++ [niw.toNat]) := p1.append_right [niw.toNat]
    have p3 := p2.append_right Fr2
    simpa only [List.append_assoc] using p3
  have hnodup_new : ((L0 ++ [nlw.toNat]) ++ (I0 ++ [niw.toNat]) ++ Fr2).Nodup :=
    hperm_new.nodup_iff.mpr hnodup2
  have hmem_new : ∀ x, x ∈ (L0 ++ [nlw.toNat]) ++ (I0 ++ [niw.toNat]) ++ Fr2 ↔ 1 ≤ x ∧ x < hdr s2 t 8 := by
    intro x; rw [hperm_new.mem_iff]; exact hmem2 x
  have hnd_all := (List.nodup_append.mp hnodup2).1
  have hnd_Anl := (List.nodup_append.mp hnd_all).1
  have hni_not_Anl : niw.toNat ∉ (L0 ++ I0) ++ [nlw.toNat] := fun h =>
    (List.nodup_append.mp hnd_all).2.2 niw.toNat h niw.toNat (by simp) rfl
  have hnl_not_LI : nlw.toNat ∉ L0 ++ I0 := fun h =>
    (List.nodup_append.mp hnd_Anl).2.2 nlw.toNat h nlw.toNat (by simp) rfl
  have hnl_ne_ni : nlw.toNat ≠ niw.toNat := fun h =>
    hni_not_Anl (List.mem_append_right _ (by simp [h]))
  have hnw_ne_nl : nw.toNat ≠ nlw.toNat := fun h => hnl_not_LI (h ▸ hnw_LI)
  have hnw_ne_ni : nw.toNat ≠ niw.toNat := fun h => hni_not_Anl (List.mem_append_left _ (h ▸ hnw_LI))
  have hnl_lt_nc2 : nlw.toNat < hdr s2 t 10 + 1 := by
    have := (hmem2 nlw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp))))
    omega
  have hni_lt_nc2 : niw.toNat < hdr s2 t 10 + 1 := by
    have := (hmem2 niw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp)))
    omega
  have hnw_lt_nc2 : nw.toNat < hdr s2 t 10 + 1 := by
    have := (hmem2 nw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hnw_LI)))
    omega
  have hLI_lt_nc2 : ∀ z ∈ L0 ++ I0, z < hdr s2 t 10 + 1 := by
    intro z hz
    have := (hmem2 z).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hz)))
    omega
  set m3 := updW (updW (updW s2.memory
              (ndw + niw * 32#64 + 0#64) pw)
              (ndw + nlw * 32#64 + 0#64) niw)
              (ndw + nw * 32#64 + 0#64) niw
  set m5 := if ch_left then
              updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
            else
              updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw
  have hm_eq : m_final = if pw.toNat = 0 then
                  updW m5 (tw + 56#64) niw
                else if nodeF s0 (hdr s0 t 5) pw.toNat 8 = nw.toNat then
                  updW m5 (ndw + pw * 32#64 + 8#64) niw
                else
                  updW m5 (ndw + pw * 32#64 + 16#64) niw := hm_final
  let s_end := NS s2 HolFiniteMapExact.empty s2.globals m_final s2.clock
  have htw56_eq : tw + 56#64 = BitVec.ofNat 64 (t + 8 * 7) := (ofNat_add_toNat tw 56).symm
  -- Helper: `m5` agrees with `s2.memory` on all header cells `t + 8 * k` (`k < 11`) and all order cells!
  have hm5_hdr : ∀ k < 11, m5 (BitVec.ofNat 64 (t + 8 * k)) = s2.memory (BitVec.ofNat 64 (t + 8 * k)) := by
    intro k hk
    have h1 := hsep2.1 k hk niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl)))
    have h2 := hsep2.1 k hk niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl))
    have h3 := hsep2.1 k hk nw.toNat hnw_lt_nc2 0 (Or.inl rfl)
    have h4 := hsep2.1 k hk nlw.toNat hnl_lt_nc2 0 (Or.inl rfl)
    have h5 := hsep2.1 k hk niw.toNat hni_lt_nc2 0 (Or.inl rfl)
    rw [← haddr_nd] at h1 h2 h3 h4 h5
    cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
  have hm5_ord : ∀ i < hdr s2 t 10 + 1, m5 (BitVec.ofNat 64 (hdr s2 t 6 + 8 * i)) = s2.memory (BitVec.ofNat 64 (hdr s2 t 6 + 8 * i)) := by
    intro i hi
    have h1 := hsep2.2.2.1 niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) i hi
    have h2 := hsep2.2.2.1 niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) i hi
    have h3 := hsep2.2.2.1 nw.toNat hnw_lt_nc2 0 (Or.inl rfl) i hi
    have h4 := hsep2.2.2.1 nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) i hi
    have h5 := hsep2.2.2.1 niw.toNat hni_lt_nc2 0 (Or.inl rfl) i hi
    rw [← haddr_nd] at h1 h2 h3 h4 h5
    cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
  have hp_lt_nc2 : pw.toNat ≠ 0 → pw.toNat < hdr s2 t 10 + 1 := by
    intro hpz
    rcases hpw_spec with ⟨h0, _⟩ | ⟨hpI, _, _⟩
    · exact absurd h0 hpz
    · exact hLI_lt_nc2 pw.toNat (List.mem_append_right _ hpI)
  have hdr_end_other : ∀ k < 11, k ≠ 7 → hdr s_end t k = hdr s2 t k := by
    intro k hk hk7
    unfold hdr memW
    simp only [s_end, NS_memory, hm_eq]
    by_cases hpz : pw.toNat = 0
    · have hne7 : BitVec.ofNat 64 (t + 8 * k) ≠ tw + 56#64 := by
        rw [htw56_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
      simp only [hpz, ↓reduceIte, updW, hne7, hm5_hdr k hk]
    · simp only [hpz, ↓reduceIte]
      have hp_lt := hp_lt_nc2 hpz
      have hne8 : BitVec.ofNat 64 (t + 8 * k) ≠ ndw + pw * 32#64 + 8#64 := by
        rw [haddr_nd]; exact hsep2.1 k hk pw.toNat hp_lt 8 (Or.inr (Or.inl rfl))
      have hne16 : BitVec.ofNat 64 (t + 8 * k) ≠ ndw + pw * 32#64 + 16#64 := by
        rw [haddr_nd]; exact hsep2.1 k hk pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl)))
      split <;> simp only [updW, hne8, hne16, ↓reduceIte, hm5_hdr k hk]
  have hh0_end : hdr s_end t 0 = hdr s0 t 0 := (hdr_end_other 0 (by omega) (by omega)).trans hh0_2
  have hh1_end : hdr s_end t 1 = hdr s0 t 1 := (hdr_end_other 1 (by omega) (by omega)).trans hh1_2
  have hh3_end : hdr s_end t 3 = hdr s0 t 3 + 1 := (hdr_end_other 3 (by omega) (by omega)).trans hh3_2
  have hh4_end : hdr s_end t 4 = hdr s2 t 4 := hdr_end_other 4 (by omega) (by omega)
  have hh5_end : hdr s_end t 5 = hdr s2 t 5 := hdr_end_other 5 (by omega) (by omega)
  have hh6_end : hdr s_end t 6 = hdr s2 t 6 := hdr_end_other 6 (by omega) (by omega)
  have hh8_end : hdr s_end t 8 = hdr s2 t 8 := hdr_end_other 8 (by omega) (by omega)
  have hh9_end : hdr s_end t 9 = hdr s2 t 9 := hdr_end_other 9 (by omega) (by omega)
  have hh10_end : hdr s_end t 10 = hdr s2 t 10 := hdr_end_other 10 (by omega) (by omega)
  have hh7_end : hdr s_end t 7 = if pw.toNat = 0 then niw.toNat else hdr s0 t 7 := by
    unfold hdr memW
    simp only [s_end, NS_memory, hm_eq]
    by_cases hpz : pw.toNat = 0
    · rw [← htw56_eq]; simp [hpz, updW]
    · simp only [hpz, ↓reduceIte]
      have hp_lt := hp_lt_nc2 hpz
      have hne8 : BitVec.ofNat 64 (t + 8 * 7) ≠ ndw + pw * 32#64 + 8#64 := by
        rw [haddr_nd]; exact hsep2.1 7 (by omega) pw.toNat hp_lt 8 (Or.inr (Or.inl rfl))
      have hne16 : BitVec.ofNat 64 (t + 8 * 7) ≠ ndw + pw * 32#64 + 16#64 := by
        rw [haddr_nd]; exact hsep2.1 7 (by omega) pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl)))
      split
      · simp only [updW, hne8, ↓reduceIte, hm5_hdr 7 (by omega)]; exact hh7_2
      · simp only [updW, hne16, ↓reduceIte, hm5_hdr 7 (by omega)]; exact hh7_2
  have hfp_end : htabFootprint s_end t = htabFootprint s2 t := by
    simp [htabFootprint, hdr_end_other 1 (by omega) (by omega), hh4_end, hh5_end, hh6_end, hh10_end]
  have hB_end : HtabBlocks s_end t := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro iv hiv; rw [hfp_end] at hiv; obtain ⟨hin, hwok⟩ := hB2.1 iv hiv
      exact ⟨hin, wordsOK_block s_end hA2.1.memaddrs iv.1 iv.2 hwok.1 hwok.2.1 hin.1 hin.2⟩
    · rw [hfp_end]; exact hB2.2.1
    · rw [hdr_end_other 0 (by omega) (by omega)]; exact hB2.2.2.1
    · rw [hdr_end_other 0 (by omega) (by omega)]; exact hB2.2.2.2.1
    · rw [hdr_end_other 1 (by omega) (by omega), hdr_end_other 0 (by omega) (by omega)]; exact hB2.2.2.2.2.1
    · rw [hh10_end]; exact hB2.2.2.2.2.2.1
    · rw [hh8_end]; exact hB2.2.2.2.2.2.2.1
    · rw [hh8_end, hh10_end]; exact hB2.2.2.2.2.2.2.2
  -- Order entries in `s_end` equal those in `s2`:
  have hord_end : ∀ i < hdr s2 t 10 + 1, memW s_end (hdr s2 t 6 + 8 * i) = memW s2 (hdr s2 t 6 + 8 * i) := by
    intro i hi
    unfold memW
    simp only [s_end, NS_memory, hm_eq]
    by_cases hpz : pw.toNat = 0
    · have hne7 : BitVec.ofNat 64 (hdr s2 t 6 + 8 * i) ≠ tw + 56#64 := by
        rw [htw56_eq]; exact (hsep2.2.1 7 (by omega) i hi).symm
      simp only [hpz, ↓reduceIte, updW, hne7, hm5_ord i hi]
    · simp only [hpz, ↓reduceIte]
      have hp_lt := hp_lt_nc2 hpz
      have hne8 : BitVec.ofNat 64 (hdr s2 t 6 + 8 * i) ≠ ndw + pw * 32#64 + 8#64 := by
        rw [haddr_nd]; exact hsep2.2.2.1 pw.toNat hp_lt 8 (Or.inr (Or.inl rfl)) i hi
      have hne16 : BitVec.ofNat 64 (hdr s2 t 6 + 8 * i) ≠ ndw + pw * 32#64 + 16#64 := by
        rw [haddr_nd]; exact hsep2.2.2.1 pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl))) i hi
      split <;> simp only [updW, hne8, hne16, ↓reduceIte, hm5_ord i hi]
  -- Helper: any node field `(x, off)` with `off = 0` or `off = 24` (or `x ≠ pw.toNat`) is unaffected by the final `if pw = 0 ...` write!
  have hm_final_non_p_ch : ∀ x < hdr s2 t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      (x ≠ pw.toNat ∨ off = 0 ∨ off = 24) →
      m_final (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off)) = m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off)) := by
    intro x hx off hoff hcond
    rw [hm_eq]
    by_cases hpz : pw.toNat = 0
    · have hne7 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off) ≠ tw + 56#64 := by
        rw [htw56_eq]; exact (hsep2.1 7 (by omega) x hx off hoff).symm
      simp only [hpz, ↓reduceIte, updW, hne7]
    · simp only [hpz, ↓reduceIte]
      have hp_lt := hp_lt_nc2 hpz
      have hne8 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off) ≠ ndw + pw * 32#64 + 8#64 := by
        rw [haddr_nd]
        apply hsep2.2.2.2.1 x hx off hoff pw.toNat hp_lt 8 (Or.inr (Or.inl rfl))
        rcases hcond with hne | rfl | rfl
        · exact Or.inl hne
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      have hne16 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off) ≠ ndw + pw * 32#64 + 16#64 := by
        rw [haddr_nd]
        apply hsep2.2.2.2.1 x hx off hoff pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl)))
        rcases hcond with hne | rfl | rfl
        · exact Or.inl hne
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      split <;> simp only [updW, hne8, hne16, ↓reduceIte]
  -- Helper: any node field `(x, off)` with `off ≠ 0` and `(x ≠ niw.toNat ∨ off = 24)` has `m5` = `s2.memory`!
  have hm5_keep : ∀ x < hdr s2 t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      (x ≠ niw.toNat → x ≠ nlw.toNat → x ≠ nw.toNat → m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off)) = s2.memory (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off))) ∧
      ((off = 8 ∨ off = 16 ∨ off = 24) → x ≠ niw.toNat → m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off)) = s2.memory (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off))) ∧
      (off = 24 → m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off)) = s2.memory (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off))) := by
    intro x hx off hoff
    refine ⟨?_, ?_, ?_⟩
    · intro hx_ni hx_nl hx_nw
      have h1 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hx_ni)
      have h2 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inl hx_ni)
      have h3 := hsep2.2.2.2.1 x hx off hoff nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inl hx_nw)
      have h4 := hsep2.2.2.2.1 x hx off hoff nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inl hx_nl)
      have h5 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inl hx_ni)
      rw [← haddr_nd] at h1 h2 h3 h4 h5
      cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
    · intro hoff_nz hx_ni
      have h0 : off ≠ 0 := by rcases hoff_nz with rfl | rfl | rfl <;> omega
      have h1 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hx_ni)
      have h2 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inl hx_ni)
      have h3 := hsep2.2.2.2.1 x hx off hoff nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inr h0)
      have h4 := hsep2.2.2.2.1 x hx off hoff nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inr h0)
      have h5 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inl hx_ni)
      rw [← haddr_nd] at h1 h2 h3 h4 h5
      cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
    · rintro rfl
      have h1 := hsep2.2.2.2.1 x hx 24 (Or.inr (Or.inr (Or.inr rfl))) niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
      have h2 := hsep2.2.2.2.1 x hx 24 (Or.inr (Or.inr (Or.inr rfl))) niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
      have h3 := hsep2.2.2.2.1 x hx 24 (Or.inr (Or.inr (Or.inr rfl))) nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
      have h4 := hsep2.2.2.2.1 x hx 24 (Or.inr (Or.inr (Or.inr rfl))) nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
      have h5 := hsep2.2.2.2.1 x hx 24 (Or.inr (Or.inr (Or.inr rfl))) niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
      rw [← haddr_nd] at h1 h2 h3 h4 h5
      cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
  -- Specific node field values in `s_end`:
  have hm5_at_0 : ∀ x < hdr s2 t 10 + 1,
      m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + 0)) = m3 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + 0)) := by
    intro x hx
    have h1 := hsep2.2.2.2.1 x hx 0 (Or.inl rfl) niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    have h2 := hsep2.2.2.2.1 x hx 0 (Or.inl rfl) niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    rw [← haddr_nd] at h1 h2
    cases ch_left <;> simp only [m5, updW, Bool.false_eq_true, ↓reduceIte, h1, h2]
  have hnl_0_end : nodeF s_end (hdr s2 t 5) nlw.toNat 0 = niw.toNat := by
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inr (Or.inl rfl)),
      hm5_at_0 nlw.toNat hnl_lt_nc2]
    have hne_nw := hsep2.2.2.2.1 nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inl hnw_ne_nl.symm)
    simp only [m3, updW, haddr_nd nw 0, haddr_nd nlw 0, hne_nw, ↓reduceIte]
  have hni_0_end : nodeF s_end (hdr s2 t 5) niw.toNat 0 = pw.toNat := by
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inr (Or.inl rfl)),
      hm5_at_0 niw.toNat hni_lt_nc2]
    have hne_nw := hsep2.2.2.2.1 niw.toNat hni_lt_nc2 0 (Or.inl rfl) nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inl hnw_ne_ni.symm)
    have hne_nl := hsep2.2.2.2.1 niw.toNat hni_lt_nc2 0 (Or.inl rfl) nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inl hnl_ne_ni.symm)
    simp only [m3, updW, haddr_nd nw 0, haddr_nd nlw 0, haddr_nd niw 0, hne_nw, hne_nl, ↓reduceIte]
  have hnw_0_end : nodeF s_end (hdr s2 t 5) nw.toNat 0 = niw.toNat := by
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inr (Or.inl rfl)),
      hm5_at_0 nw.toNat hnw_lt_nc2]
    simp only [m3, updW, haddr_nd nw 0, ↓reduceIte]
  have hnl_16_end : nodeF s_end (hdr s2 t 5) nlw.toNat 16 = hdr s0 t 3 := by
    have hnl_ne_pw : nlw.toNat ≠ pw.toNat := by
      intro h; rcases hpw_spec with ⟨hpz, _⟩ | ⟨hpI, _, _⟩
      · have := (hmem2 nlw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))); omega
      · exact hnl_not_LI (h ▸ List.mem_append_right _ hpI)
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch nlw.toNat hnl_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hnl_ne_pw),
      (hm5_keep nlw.toNat hnl_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl)))).2.1 (Or.inr (Or.inl rfl)) hnl_ne_ni]
    exact hnl_16_2
  have hnl_24_end : nodeF s_end (hdr s2 t 5) nlw.toNat 24 = 8 * hdr s0 t 0 := by
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch nlw.toNat hnl_lt_nc2 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr rfl)),
      (hm5_keep nlw.toNat hnl_lt_nc2 24 (Or.inr (Or.inr (Or.inr rfl)))).2.2 rfl]
    exact hnl_24_2
  have hni_24_end : nodeF s_end (hdr s2 t 5) niw.toNat 24 = dw.toNat := by
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch niw.toNat hni_lt_nc2 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr rfl)),
      (hm5_keep niw.toNat hni_lt_nc2 24 (Or.inr (Or.inr (Or.inr rfl)))).2.2 rfl]
    exact hni_24_2
  have hni_ne_pw : niw.toNat ≠ pw.toNat := by
    intro h; rcases hpw_spec with ⟨hpz, _⟩ | ⟨hpI, _, _⟩
    · have := (hmem2 niw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp))); omega
    · exact hni_not_Anl (List.mem_append_left _ (List.mem_append_right _ (h ▸ hpI)))
  have hni_ch_end : (nodeF s_end (hdr s2 t 5) niw.toNat 8 = nlw.toNat ∧ nodeF s_end (hdr s2 t 5) niw.toNat 16 = nw.toNat) ∨
      (nodeF s_end (hdr s2 t 5) niw.toNat 8 = nw.toNat ∧ nodeF s_end (hdr s2 t 5) niw.toNat 16 = nlw.toNat) := by
    have h8_m5 := hm_final_non_p_ch niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inl hni_ne_pw)
    have h16_m5 := hm_final_non_p_ch niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hni_ne_pw)
    have hne8_16 := hsep2.2.2.2.1 niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    unfold nodeF memW
    simp only [s_end, NS_memory, h8_m5, h16_m5]
    cases hcl : ch_left
    · right
      have hm5_f : m5 = updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw := by simp [m5, hcl]
      rw [hm5_f]
      simp [updW, haddr_nd niw 16, haddr_nd niw 8, hne8_16]
    · left
      have hm5_t : m5 = updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw := by simp [m5, hcl]
      rw [hm5_t]
      simp [updW, haddr_nd niw 16, haddr_nd niw 8, hne8_16]
  -- FreeChain in `s_end`:
  have hfc_end : FreeChainF (nodeF s_end (hdr s2 t 5)) (hdr s2 t 9) Fr2 := by
    refine FreeChainF.congr Fr2 _ ?_ hfc2
    intro f hf
    have hf_lt : f < hdr s2 t 10 + 1 := by
      have := (hmem2 f).mp (List.mem_append_right _ hf); omega
    have hf_not_all : f ∉ (((L0 ++ I0) ++ [nlw.toNat]) ++ [niw.toNat]) := fun h =>
      (List.nodup_append.mp hnodup2).2.2 f h f hf rfl
    have hf_ni : f ≠ niw.toNat := fun h => hf_not_all (List.mem_append_right _ (by simp [h]))
    have hf_nl : f ≠ nlw.toNat := fun h => hf_not_all (List.mem_append_left _ (List.mem_append_right _ (by simp [h])))
    have hf_nw : f ≠ nw.toNat := fun h => hf_not_all (List.mem_append_left _ (List.mem_append_left _ (h ▸ hnw_LI)))
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch f hf_lt 0 (Or.inl rfl) (Or.inr (Or.inl rfl)),
      (hm5_keep f hf_lt 0 (Or.inl rfl)).1 hf_ni hf_nl hf_nw]
  -- Assemble `TreeWF.insert_splice`!
  have hT_end : TreeWF (L0 ++ [nlw.toNat]) (I0 ++ [niw.toNat]) Fr2
      (hdr s_end t 8) (hdr s_end t 0) (hdr s_end t 3) (hdr s_end t 7) (hdr s_end t 9)
      (nodeF s_end (hdr s_end t 5)) (fun i => memW s_end (hdr s_end t 6 + 8 * i)) := by
    rw [hh8_end, hh0_end, hh3_end, hh7_end, hh9_end, hh5_end, hh6_end]
    have hcnt_lt_nc2 : hdr s0 t 3 < hdr s2 t 10 + 1 := by
      have hlen_le := nodup_len_le_range hnd_all (fun x hx => (hmem2 x).mp (List.mem_append_left _ hx))
      have hLlen0 := hT0.1
      simp only [List.length_append, List.length_singleton] at hlen_le
      omega
    apply TreeWF.insert_splice (nd := nodeF s0 (hdr s0 t 5)) (ord := fun i => memW s0 (hdr s0 t 6 + 8 * i))
      hT0.1 hcnt_pos hnodup_new hmem_new hT0.2.2.2.1 hT0.2.2.2.2.1 hT0.2.2.2.2.2.1
      hT0.2.2.2.2.2.2.2.1 hT0.2.2.2.2.2.2.2.2.1 hT0.2.2.2.2.2.2.2.2.2.1 hT0.2.2.2.2.2.2.2.2.2.2.1
      hfc_end hd_lt hnw_LI hpw_spec
    · intro i hi
      rw [hT0.1] at hi
      exact (hord_end i (by omega)).trans (hord_old_2 i hi)
    · exact (hord_end (hdr s0 t 3) hcnt_lt_nc2).trans hord_cnt_2
    · exact hnl_0_end
    · exact hnl_16_end
    · exact hnl_24_end
    · exact hni_0_end
    · exact hni_24_end
    · exact hni_ch_end
    · exact hnw_0_end
    · intro x hxLI hx_nw
      have hx_lt := hLI_lt_nc2 x hxLI
      have hx_ni : x ≠ niw.toNat := fun h => hni_not_Anl (List.mem_append_left _ (h ▸ hxLI))
      have hx_nl : x ≠ nlw.toNat := fun h => hnl_not_LI (h ▸ hxLI)
      have h1 : nodeF s_end (hdr s2 t 5) x 0 = nodeF s2 (hdr s2 t 5) x 0 := by
        unfold nodeF memW; simp only [s_end, NS_memory]
        rw [hm_final_non_p_ch x hx_lt 0 (Or.inl rfl) (Or.inr (Or.inl rfl)),
          (hm5_keep x hx_lt 0 (Or.inl rfl)).1 hx_ni hx_nl hx_nw]
      exact h1.trans (hnd_old_2 x hxLI 0 (Or.inl rfl))
    · intro x hxLI
      have hx_lt := hLI_lt_nc2 x hxLI
      have h1 : nodeF s_end (hdr s2 t 5) x 24 = nodeF s2 (hdr s2 t 5) x 24 := by
        unfold nodeF memW; simp only [s_end, NS_memory]
        rw [hm_final_non_p_ch x hx_lt 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr rfl)),
          (hm5_keep x hx_lt 24 (Or.inr (Or.inr (Or.inr rfl)))).2.2 rfl]
      exact h1.trans (hnd_old_2 x hxLI 24 (Or.inr (Or.inr (Or.inr rfl))))
    · intro x hxL
      have hxLI : x ∈ L0 ++ I0 := List.mem_append_left _ hxL
      have hx_lt := hLI_lt_nc2 x hxLI
      have hx_ni : x ≠ niw.toNat := fun h => hni_not_Anl (List.mem_append_left _ (h ▸ hxLI))
      have hx_pw : x ≠ pw.toNat := by
        intro h; rcases hpw_spec with ⟨hpz, _⟩ | ⟨hpI, _, _⟩
        · have := (hT0.2.2.1 x).mp (List.mem_append_left _ hxLI); omega
        · have hndLI0 := (List.nodup_append.mp hT0.2.1).1
          exact (List.nodup_append.mp hndLI0).2.2 x hxL x (h ▸ hpI) rfl
      have h1 : nodeF s_end (hdr s2 t 5) x 16 = nodeF s2 (hdr s2 t 5) x 16 := by
        unfold nodeF memW; simp only [s_end, NS_memory]
        rw [hm_final_non_p_ch x hx_lt 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hx_pw),
          (hm5_keep x hx_lt 16 (Or.inr (Or.inr (Or.inl rfl)))).2.1 (Or.inr (Or.inl rfl)) hx_ni]
      exact h1.trans (hnd_old_2 x hxLI 16 (Or.inr (Or.inr (Or.inl rfl))))
    · intro x hxI hx_pw
      have hxLI : x ∈ L0 ++ I0 := List.mem_append_right _ hxI
      have hx_lt := hLI_lt_nc2 x hxLI
      have hx_ni : x ≠ niw.toNat := fun h => hni_not_Anl (List.mem_append_left _ (h ▸ hxLI))
      have h8 : nodeF s_end (hdr s2 t 5) x 8 = nodeF s2 (hdr s2 t 5) x 8 := by
        unfold nodeF memW; simp only [s_end, NS_memory]
        rw [hm_final_non_p_ch x hx_lt 8 (Or.inr (Or.inl rfl)) (Or.inl hx_pw),
          (hm5_keep x hx_lt 8 (Or.inr (Or.inl rfl))).2.1 (Or.inl rfl) hx_ni]
      have h16 : nodeF s_end (hdr s2 t 5) x 16 = nodeF s2 (hdr s2 t 5) x 16 := by
        unfold nodeF memW; simp only [s_end, NS_memory]
        rw [hm_final_non_p_ch x hx_lt 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hx_pw),
          (hm5_keep x hx_lt 16 (Or.inr (Or.inr (Or.inl rfl)))).2.1 (Or.inr (Or.inl rfl)) hx_ni]
      exact ⟨h8.trans (hnd_old_2 x hxLI 8 (Or.inr (Or.inl rfl))),
             h16.trans (hnd_old_2 x hxLI 16 (Or.inr (Or.inr (Or.inl rfl))))⟩
    · intro hpz
      have hpI : pw.toNat ∈ I0 := by
        rcases hpw_spec with ⟨h0, _⟩ | ⟨hI, _, _⟩
        · exact absurd h0 hpz
        · exact hI
      have hpLI : pw.toNat ∈ L0 ++ I0 := List.mem_append_right _ hpI
      have hp_lt := hp_lt_nc2 hpz
      have hp_ni : pw.toNat ≠ niw.toNat := hni_ne_pw.symm
      have hne8_16 := hsep2.2.2.2.1 pw.toNat hp_lt 8 (Or.inr (Or.inl rfl)) pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
      have hm5_p8 := (hm5_keep pw.toNat hp_lt 8 (Or.inr (Or.inl rfl))).2.1 (Or.inl rfl) hp_ni
      have hm5_p16 := (hm5_keep pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl)))).2.1 (Or.inr (Or.inl rfl)) hp_ni
      constructor
      · intro hp8_eq
        refine ⟨?_, ?_⟩
        · unfold nodeF memW; simp only [s_end, NS_memory, hm_eq, hpz, hp8_eq, ↓reduceIte, updW, haddr_nd pw 8]
        · have h1 : nodeF s_end (hdr s2 t 5) pw.toNat 16 = nodeF s2 (hdr s2 t 5) pw.toNat 16 := by
            unfold nodeF memW
            simp only [s_end, NS_memory, hm_eq, hpz, hp8_eq, ↓reduceIte, updW, haddr_nd pw 8, hne8_16.symm, hm5_p16]
          exact h1.trans (hnd_old_2 pw.toNat hpLI 16 (Or.inr (Or.inr (Or.inl rfl))))
      · intro hp8_ne
        refine ⟨?_, ?_⟩
        · have h1 : nodeF s_end (hdr s2 t 5) pw.toNat 8 = nodeF s2 (hdr s2 t 5) pw.toNat 8 := by
            unfold nodeF memW
            simp only [s_end, NS_memory, hm_eq, hpz, hp8_ne, ↓reduceIte, updW, haddr_nd pw 16, hne8_16, hm5_p8]
          exact h1.trans (hnd_old_2 pw.toNat hpLI 8 (Or.inr (Or.inl rfl)))
        · unfold nodeF memW; simp only [s_end, NS_memory, hm_eq, hpz, hp8_ne, ↓reduceIte, updW, haddr_nd pw 16]
  have hW_end : HtabWF s_end t := (htabWF_iff s_end t).mpr ⟨hB_end, L0 ++ [nlw.toNat], I0 ++ [niw.toNat], Fr2, hT_end⟩
  -- Finally, `FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr")`!
  have hit_nd2 : ∀ (xw : BitVec 64) (off : Nat),
      xw.toNat < hdr s2 t 10 + 1 → (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      (∃ j ∈ htabFootprint s0 t, CellHits (ndw + xw * 32#64 + BitVec.ofNat 64 off).toNat j) ∨
        CellHits (ndw + xw * 32#64 + BitVec.ofNat 64 off).toNat (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") := by
    intro xw off hxw hoff
    have hnd2_in := (hB2.1 (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd2_in
    have hhit_blk : CellHits (ndw + xw * 32#64 + BitVec.ofNat 64 off).toNat (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) := by
      rw [haddr_nd xw off, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)]
      unfold CellHits
      rcases hoff with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    rcases (hfp_2 (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) (by simp [htabFootprint])).2 with ⟨j, hj, hij⟩ | hfr
    · exact Or.inl ⟨j, hj, cellHits_of_inside hhit_blk hij⟩
    · exact Or.inr (cellHits_of_inside hhit_blk hfr)
  have hit_t56 : (∃ j ∈ htabFootprint s0 t, CellHits (tw + 56#64).toNat j) ∨
      CellHits (tw + 56#64).toNat (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") := by
    have htw56_nat : (tw + 56#64).toNat = t + 56 := by rw [BitVec.toNat_add, show (56#64).toNat = 56 from rfl]; omega
    exact Or.inl ⟨(t, 88), by simp [htabFootprint], by rw [htw56_nat]; exact ⟨by omega, by omega⟩⟩
  have hfr_m3 : FrameOutside s0 (NS s2 HolFiniteMapExact.empty s2.globals m3 s2.clock)
      (htabFootprint s0 t) (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") := by
    have f1 := frameOutside_updW_mem s0 s2 s2.memory rfl _ pw _ _ hfr_2 (hit_nd2 niw 0 hni_lt_nc2 (Or.inl rfl))
      (NS s2 HolFiniteMapExact.empty s2.globals (updW s2.memory (ndw + niw * 32#64 + 0#64) pw) s2.clock) rfl
    have f2 := frameOutside_updW_mem s0 _ _ rfl _ niw _ _ f1 (hit_nd2 nlw 0 hnl_lt_nc2 (Or.inl rfl))
      (NS s2 HolFiniteMapExact.empty s2.globals (updW (updW s2.memory (ndw + niw * 32#64 + 0#64) pw) (ndw + nlw * 32#64 + 0#64) niw) s2.clock) rfl
    exact frameOutside_updW_mem s0 _ _ rfl _ niw _ _ f2 (hit_nd2 nw 0 hnw_lt_nc2 (Or.inl rfl))
      (NS s2 HolFiniteMapExact.empty s2.globals m3 s2.clock) rfl
  have hfr_m5 : FrameOutside s0 (NS s2 HolFiniteMapExact.empty s2.globals m5 s2.clock)
      (htabFootprint s0 t) (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") := by
    cases hcl : ch_left
    · have hm5_f : m5 = updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw := by simp [m5, hcl]
      have f4 := frameOutside_updW_mem s0 _ _ rfl _ nw _ _ hfr_m3 (hit_nd2 niw 8 hni_lt_nc2 (Or.inr (Or.inl rfl)))
        (NS s2 HolFiniteMapExact.empty s2.globals (updW m3 (ndw + niw * 32#64 + 8#64) nw) s2.clock) rfl
      exact frameOutside_updW_mem s0 _ _ rfl _ nlw _ _ f4 (hit_nd2 niw 16 hni_lt_nc2 (Or.inr (Or.inr (Or.inl rfl))))
        (NS s2 HolFiniteMapExact.empty s2.globals m5 s2.clock) hm5_f
    · have hm5_t : m5 = updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw := by simp [m5, hcl]
      have f4 := frameOutside_updW_mem s0 _ _ rfl _ nlw _ _ hfr_m3 (hit_nd2 niw 8 hni_lt_nc2 (Or.inr (Or.inl rfl)))
        (NS s2 HolFiniteMapExact.empty s2.globals (updW m3 (ndw + niw * 32#64 + 8#64) nlw) s2.clock) rfl
      exact frameOutside_updW_mem s0 _ _ rfl _ nw _ _ f4 (hit_nd2 niw 16 hni_lt_nc2 (Or.inr (Or.inr (Or.inl rfl))))
        (NS s2 HolFiniteMapExact.empty s2.globals m5 s2.clock) hm5_t
  have hfr_end : FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") := by
    by_cases hpz : pw.toNat = 0
    · have hm_p0 : s_end.memory = updW m5 (tw + 56#64) niw := by simp [s_end, hm_eq, hpz]
      exact frameOutside_updW_mem s0 _ _ rfl _ niw _ _ hfr_m5 hit_t56 s_end hm_p0
    · have hp_lt := hp_lt_nc2 hpz
      by_cases hp8 : nodeF s0 (hdr s0 t 5) pw.toNat 8 = nw.toNat
      · have hm_p8 : s_end.memory = updW m5 (ndw + pw * 32#64 + 8#64) niw := by simp [s_end, hm_eq, hpz, hp8]
        exact frameOutside_updW_mem s0 _ _ rfl _ niw _ _ hfr_m5 (hit_nd2 pw 8 hp_lt (Or.inr (Or.inl rfl))) s_end hm_p8
      · have hm_p16 : s_end.memory = updW m5 (ndw + pw * 32#64 + 16#64) niw := by simp [s_end, hm_eq, hpz, hp8]
        exact frameOutside_updW_mem s0 _ _ rfl _ niw _ _ hfr_m5 (hit_nd2 pw 16 hp_lt (Or.inr (Or.inr (Or.inl rfl)))) s_end hm_p16
  refine ⟨⟨guestInv_congr (s := s2) rfl rfl rfl rfl hA2.1, hA2.2⟩,
    hW_end, hh0_end, hh1_end, hhp_2,
    ?_, hfr_end, hg_2⟩
  · change ∀ iv ∈ htabFootprint s_end t, Allocated s2 iv ∧ _
    rw [hfp_end]; exact hfp_2

end InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

/-! ### From SoloHtabSetFinal.lean -/

/-! Final composition of `htab_set_body_spec` and `htab_set_spec_proof` (`FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set")`). -/


namespace InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Execution of the Post-Allocation Splice Program -/

theorem eval_field_load_word {F : Type} (st : PanSemStateFiniteExact 64 F)
    (tw off w : BitVec 64)
    (ht : st.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hdom : st.memaddrs (tw + off))
    (hm : st.memory (tw + off) = .word w) :
    evalAt st (.load .one (.op .add [.var .local (ofString "t"), .const off])) =
      some (.val (.word w)) := by
  simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht,
    isWfShapeExactHOL, memLoadHOLExact, hdom, hm, valueIsWord, valueWord, wordOpHOL, wordOp]

theorem htab_set_splice_exec {F : Type}
    (s0 s2 : PanSemStateFiniteExact 64 F)
    (tw dw pw nw nlw niw : BitVec 64)
    (L0 I0 Fr0 Fr2 : List Nat)
    (L_cur : HolFiniteMapExact MlS (ValueHOL 64))
    (ht_cur : L_cur.lookup (ofString "t") = some (.val (.word tw)))
    (hp_cur : L_cur.lookup (ofString "p") = some (.val (.word pw)))
    (hn_cur : L_cur.lookup (ofString "n") = some (.val (.word nw)))
    (hnl_cur : L_cur.lookup (ofString "nl") = some (.val (.word nlw)))
    (hni_cur : L_cur.lookup (ofString "ni") = some (.val (.word niw)))
    (hA2 : ArenaReady s2)
    (hNS2 : NodeState s2 tw.toNat (((L0 ++ I0) ++ [nlw.toNat]) ++ [niw.toNat]) Fr2)
    (hT0 : TreeWF L0 I0 Fr0
      (hdr s0 tw.toNat 8) (hdr s0 tw.toNat 0) (hdr s0 tw.toNat 3) (hdr s0 tw.toNat 7) (hdr s0 tw.toNat 9)
      (nodeF s0 (hdr s0 tw.toNat 5)) (fun i => memW s0 (hdr s0 tw.toNat 6 + 8 * i)))
    (hcnt_pos : 0 < hdr s0 tw.toNat 3)
    (hd_lt : dw.toNat < 8 * hdr s0 tw.toNat 0)
    (hnw_LI : nw.toNat ∈ L0 ++ I0)
    (hpw_spec : (pw.toNat = 0 ∧ nw.toNat = hdr s0 tw.toNat 7) ∨
      (pw.toNat ∈ I0 ∧ nw.toNat ≠ hdr s0 tw.toNat 7 ∧ pw.toNat = nodeF s0 (hdr s0 tw.toNat 5) nw.toNat 0))
    (hh0_2 : hdr s2 tw.toNat 0 = hdr s0 tw.toNat 0)
    (hh1_2 : hdr s2 tw.toNat 1 = hdr s0 tw.toNat 1)
    (hh3_2 : hdr s2 tw.toNat 3 = hdr s0 tw.toNat 3 + 1)
    (hh7_2 : hdr s2 tw.toNat 7 = hdr s0 tw.toNat 7)
    (hnl_16_2 : nodeF s2 (hdr s2 tw.toNat 5) nlw.toNat 16 = hdr s0 tw.toNat 3)
    (hnl_24_2 : nodeF s2 (hdr s2 tw.toNat 5) nlw.toNat 24 = 8 * hdr s0 tw.toNat 0)
    (hni_24_2 : nodeF s2 (hdr s2 tw.toNat 5) niw.toNat 24 = dw.toNat)
    (hord_cnt_2 : memW s2 (hdr s2 tw.toNat 6 + 8 * hdr s0 tw.toNat 3) = nlw.toNat)
    (hord_old_2 : ∀ i, i < hdr s0 tw.toNat 3 →
      memW s2 (hdr s2 tw.toNat 6 + 8 * i) = memW s0 (hdr s0 tw.toNat 6 + 8 * i))
    (hnd_old_2 : ∀ z ∈ L0 ++ I0, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s2 (hdr s2 tw.toNat 5) z off = nodeF s0 (hdr s0 tw.toNat 5) z off)
    (hhp_2 : globN s0 "heap_ptr" ≤ globN s2 "heap_ptr")
    (hfp_2 : ∀ i ∈ htabFootprint s2 tw.toNat, Allocated s2 i ∧
      ((∃ j ∈ htabFootprint s0 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s2 "heap_ptr" - globN s0 "heap_ptr"))))
    (hfr_2 : FrameOutside s0 s2 (htabFootprint s0 tw.toNat) (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr"))
    (hg_2 : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s0.globals.lookup k = s2.globals.lookup k) :
    Ret (NS s2 L_cur s2.globals s2.memory s2.clock)
      (.seq
        (.assign .local (ofString "nodes") (.load .one (.op .add [.var .local (ofString "t"), .const 40#64])))
        (.seq
          (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 0#64]) (.var .local (ofString "p")))
          (.seq
            (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "nl"), .const 32#64], .const 0#64]) (.var .local (ofString "ni")))
            (.seq
              (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "n"), .const 32#64], .const 0#64]) (.var .local (ofString "ni")))
              (.seq
                (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"), .shift .lsr (.var .local (ofString "d")) (.const 3#64)])) (.op .sub [.const 7#64, .op .and [.var .local (ofString "d"), .const 7#64]]), .const 1#64]) (.const 0#64))
                  (.seq
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 8#64]) (.var .local (ofString "nl")))
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 16#64]) (.var .local (ofString "n"))))
                  (.seq
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 8#64]) (.var .local (ofString "n")))
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 16#64]) (.var .local (ofString "nl")))))
                (.seq
                  (.ite (.cmp .equal (.var .local (ofString "p")) (.const 0#64))
                    (.store (.op .add [.var .local (ofString "t"), .const 56#64]) (.var .local (ofString "ni")))
                    (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64])) (.var .local (ofString "n")))
                      (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64]) (.var .local (ofString "ni")))
                      (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 16#64]) (.var .local (ofString "ni")))))
                  (.return (.const 0#64))))))))
      (fun _ post => HtabExitAt tw.toNat s0 post) := by
  set t := tw.toNat
  have hB2 := hNS2.1
  have hnodup2 := hNS2.2.1
  have hmem2 := hNS2.2.2.1
  have hfc2 := hNS2.2.2.2
  obtain ⟨hnc2_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB2
  have hnx2_le : hdr s2 t 8 ≤ hdr s2 t 10 + 1 := hB2.2.2.2.2.2.2.2
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom2_t5, hm2_t5⟩ := word_of_hdr s2 tw 5 (by omega) hB2
  set ndw := BitVec.ofNat 64 (hdr s2 t 5)
  have hndw_nat : ndw.toNat = hdr s2 t 5 := by
    have hnd2_in := (hB2.1 (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd2_in; rw [BitVec.toNat_ofNat]; omega
  -- 1. `nodes := load(t + 40)`
  have hev_nd : evalAt (NS s2 L_cur s2.globals s2.memory s2.clock)
      (.load .one (.op .add [.var .local (ofString "t"), .const 40#64])) =
      some (.val (.word ndw)) :=
    eval_field_load_word _ tw 40#64 ndw ht_cur hdom2_t5 hm2_t5
  refine Ret.ns_assign ndw hev_nd ?_
  let L_nd := L_cur.update (ofString "nodes", .val (.word ndw))
  have hl_nd : L_nd.lookup (ofString "nodes") = some (.val (.word ndw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE]
  have hl_t : L_nd.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, ht_cur, show ofString "nodes" ≠ ofString "t" by decide]
  have hl_p : L_nd.lookup (ofString "p") = some (.val (.word pw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hp_cur, show ofString "nodes" ≠ ofString "p" by decide]
  have hl_n : L_nd.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hn_cur, show ofString "nodes" ≠ ofString "n" by decide]
  have hl_nl : L_nd.lookup (ofString "nl") = some (.val (.word nlw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hnl_cur, show ofString "nodes" ≠ ofString "nl" by decide]
  have hl_ni : L_nd.lookup (ofString "ni") = some (.val (.word niw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hni_cur, show ofString "nodes" ≠ ofString "ni" by decide]
  -- 2. Three parent stores: `ni.+0 := p`, `nl.+0 := ni`, `n.+0 := ni`
  refine Ret.ns_storeW (ndw + niw * 32#64 + 0#64) pw
    (eval_node_field_expr _ (ofString "ni") ndw niw 0 hl_nd hl_ni)
    (by simp [evalAt, evalHOLExact]; exact hl_p) ?_
  intro _
  refine Ret.ns_storeW (ndw + nlw * 32#64 + 0#64) niw
    (eval_node_field_expr _ (ofString "nl") ndw nlw 0 hl_nd hl_nl)
    (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
  intro _
  refine Ret.ns_storeW (ndw + nw * 32#64 + 0#64) niw
    (eval_node_field_expr _ (ofString "n") ndw nw 0 hl_nd hl_n)
    (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
  intro _
  set m3 := updW (updW (updW s2.memory
              (ndw + niw * 32#64 + 0#64) pw)
              (ndw + nlw * 32#64 + 0#64) niw)
              (ndw + nw * 32#64 + 0#64) niw
  -- Helper: from `NS s2 L_nd s2.globals m5_val s2.clock` where `m5_val` corresponds to `ch_left : Bool`,
  -- execute the final `ite (p == 0)` and `return 0`!
  have exec_parent_link : ∀ (ch_left : Bool) (m5_val : BitVec 64 → HolWordLab 64),
      m5_val = (if ch_left then
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
                else
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw) →
      Ret (NS s2 L_nd s2.globals m5_val s2.clock)
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "p")) (.const 0#64))
            (.store (.op .add [.var .local (ofString "t"), .const 56#64]) (.var .local (ofString "ni")))
            (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64])) (.var .local (ofString "n")))
              (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64]) (.var .local (ofString "ni")))
              (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 16#64]) (.var .local (ofString "ni")))))
          (.return (.const 0#64)))
        (fun _ post => HtabExitAt t s0 post) := by
    intro ch_left m5_val hm5_eq
    apply Ret.seq_ite
    intro cwp hcwp
    have hp_lt_264 : pw.toNat < 2 ^ 64 := pw.isLt
    have hcwp_spec : (cwp ≠ 0 → pw.toNat = 0) ∧ (cwp = 0 → pw.toNat ≠ 0) := by
      obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp _ .equal _ _ cwp hcwp
      simp only [NS_locals, evalAt, evalHOLExact, hl_p, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hva hvb
      subst hva hvb
      have hz0 : (0#64 : BitVec 64).toNat = 0 := rfl
      constructor
      · intro hnz; by_contra hne
        have hp_ne : pw ≠ 0#64 := fun h => hne (by rw [h]; exact hz0)
        simp [Compiler.Encoders.Asm.wordCmpHOL, hp_ne] at hcw_eq
        exact hnz hcw_eq
      · intro hz hp0
        have hp_eq : pw = 0#64 := BitVec.eq_of_toNat_eq (by rw [hp0, hz0])
        simp [Compiler.Encoders.Asm.wordCmpHOL, hp_eq] at hcw_eq
        rw [hz] at hcw_eq; exact absurd hcw_eq (by decide)
    refine ⟨fun hcwp_nz => ?_, fun hcwp_z => ?_⟩
    · -- `pw.toNat = 0`: `store(t + 56, ni); return 0`
      have hpz := hcwp_spec.1 hcwp_nz
      refine Ret.ns_storeW (tw + 56#64) niw
        (by
          have h560 : 56#64 + (0 : BitVec 64) = 56#64 := rfl
          simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
            hl_t, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
            valueIsWord, valueWord, wordOpHOL, wordOp, h560])
        (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
      intro _
      apply Ret.ns_ret; intro _ _
      exact htab_set_splice_memory_wf s0 s2 tw dw pw nw nlw niw L0 I0 Fr0 Fr2 ch_left
        (updW m5_val (tw + 56#64) niw)
        (by dsimp only; rw [if_pos hpz, hm5_eq])
        hA2 hNS2 hT0 hcnt_pos hd_lt hnw_LI hpw_spec hh0_2 hh1_2 hh3_2 hh7_2
        hnl_16_2 hnl_24_2 hni_24_2 hord_cnt_2 hord_old_2 hnd_old_2 hhp_2 hfp_2 hfr_2 hg_2
    · -- `pw.toNat ≠ 0`: `ite (load(nodes + p*32 + 8) == n)`
      have hpnz := hcwp_spec.2 hcwp_z
      have hpI : pw.toNat ∈ I0 := by
        rcases hpw_spec with ⟨h0, _⟩ | ⟨hI, _, _⟩
        · exact absurd h0 hpnz
        · exact hI
      have hpLI : pw.toNat ∈ L0 ++ I0 := List.mem_append_right _ hpI
      have hp_lt_nc2 : pw.toNat < hdr s2 t 10 + 1 := by
        have := (hmem2 pw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hpLI)))
        omega
      -- Show `m5_val (ndw + pw * 32 + 8) = .word (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8))`!
      have hsep2 := htabBlocks_cell_sep hB2
      have haddr_nd : ∀ (xw : BitVec 64) (off : Nat),
          ndw + xw * 32#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (hdr s2 t 5 + 32 * xw.toNat + off) := by
        intro xw off; rw [← hndw_nat]; exact (ofNat_node_addr ndw xw off).symm
      have hnd_all := (List.nodup_append.mp hnodup2).1
      have hp_ne_ni : pw.toNat ≠ niw.toNat := fun h =>
        (List.nodup_append.mp hnd_all).2.2 niw.toNat (List.mem_append_left _ (h ▸ hpLI)) niw.toNat (by simp) rfl
      have hni_lt_nc2 : niw.toNat < hdr s2 t 10 + 1 := by
        have := (hmem2 niw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp))); omega
      have hnl_lt_nc2 : nlw.toNat < hdr s2 t 10 + 1 := by
        have := (hmem2 nlw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))); omega
      have hnw_lt_nc2 : nw.toNat < hdr s2 t 10 + 1 := by
        have := (hmem2 nw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hnw_LI))); omega
      obtain ⟨hdom_p8, hm2_p8⟩ := word_of_node s2 tw ndw pw 8 hndw_nat.symm hp_lt_nc2 (Or.inr (Or.inl rfl)) hB2
      have hm5_p8 : m5_val (ndw + pw * 32#64 + 8#64) = .word (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8)) := by
        have h1 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hp_ne_ni)
        have h2 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inl hp_ne_ni)
        have h3 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
        have h4 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
        have h5 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inl hp_ne_ni)
        rw [hm5_eq]
        have hm5_s2 : (if ch_left = true then updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
            else updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw) (ndw + pw * 32#64 + 8#64) =
            s2.memory (ndw + pw * 32#64 + 8#64) := by
          cases ch_left <;> simp only [m3, updW, Bool.false_eq_true, ↓reduceIte,
            haddr_nd pw 8, haddr_nd niw 16, haddr_nd niw 8, haddr_nd nw 0, haddr_nd nlw 0, haddr_nd niw 0,
            h1, h2, h3, h4, h5]
        rw [hm5_s2]
        have hm2_p8' : s2.memory (ndw + pw * 32#64 + 8#64) = .word (BitVec.ofNat 64 (nodeF s2 (hdr s2 t 5) pw.toNat 8)) := by
          rw [← hndw_nat]; exact hm2_p8
        rw [hm2_p8', hnd_old_2 pw.toNat hpLI 8 (Or.inr (Or.inl rfl))]
      have hp8_lt_264 : nodeF s0 (hdr s0 t 5) pw.toNat 8 < 2 ^ 64 := by
        unfold nodeF memW; rcases s0.memory _ with ⟨w⟩; exact w.isLt
      apply Ret.seq_ite
      intro cw8 hcw8
      have hcw8_spec : (cw8 ≠ 0 → nodeF s0 (hdr s0 t 5) pw.toNat 8 = nw.toNat) ∧
          (cw8 = 0 → nodeF s0 (hdr s0 t 5) pw.toNat 8 ≠ nw.toNat) := by
        obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp _ .equal _ _ cw8 hcw8
        obtain ⟨_, hva_mem⟩ := ev_var_node_load (NS s2 L_nd s2.globals m5_val s2.clock) (ofString "p") ndw pw 8#64 hl_nd hl_p (.val (.word va)) hva
        have hm5_p8' : m5_val (ndw + pw * 32 + 8#64) = .word (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8)) := hm5_p8
        simp only [NS_memory, hm5_p8', ValueHOL.val.injEq, HolWordLab.word.injEq] at hva_mem
        subst hva_mem
        simp only [NS_locals, evalAt, evalHOLExact, hl_n, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hvb
        subst hvb
        have hva_nat : (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8)).toNat = nodeF s0 (hdr s0 t 5) pw.toNat 8 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp8_lt_264]
        constructor
        · intro hnz; by_contra hne
          have hbne : BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8) ≠ nw := fun h =>
            hne (by have := congrArg BitVec.toNat h; rw [hva_nat] at this; exact this)
          simp [Compiler.Encoders.Asm.wordCmpHOL, hbne] at hcw_eq
          exact hnz hcw_eq
        · intro hz heq
          have hbeq : BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8) = nw :=
            BitVec.eq_of_toNat_eq (by rw [hva_nat, heq])
          simp [Compiler.Encoders.Asm.wordCmpHOL, hbeq] at hcw_eq
          rw [hz] at hcw_eq; exact absurd hcw_eq (by decide)
      refine ⟨fun hcw8_nz => ?_, fun hcw8_z => ?_⟩
      · have hp8_eq := hcw8_spec.1 hcw8_nz
        refine Ret.ns_storeW (ndw + pw * 32#64 + 8#64) niw
          (eval_node_field_expr _ (ofString "p") ndw pw 8 hl_nd hl_p)
          (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
        intro _
        apply Ret.ns_ret; intro _ _
        exact htab_set_splice_memory_wf s0 s2 tw dw pw nw nlw niw L0 I0 Fr0 Fr2 ch_left
          (updW m5_val (ndw + pw * 32#64 + 8#64) niw)
          (by dsimp only; rw [if_neg hpnz, if_pos hp8_eq, hm5_eq])
          hA2 hNS2 hT0 hcnt_pos hd_lt hnw_LI hpw_spec hh0_2 hh1_2 hh3_2 hh7_2
          hnl_16_2 hnl_24_2 hni_24_2 hord_cnt_2 hord_old_2 hnd_old_2 hhp_2 hfp_2 hfr_2 hg_2
      · have hp8_ne := hcw8_spec.2 hcw8_z
        refine Ret.ns_storeW (ndw + pw * 32#64 + 16#64) niw
          (eval_node_field_expr _ (ofString "p") ndw pw 16 hl_nd hl_p)
          (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
        intro _
        apply Ret.ns_ret; intro _ _
        exact htab_set_splice_memory_wf s0 s2 tw dw pw nw nlw niw L0 I0 Fr0 Fr2 ch_left
          (updW m5_val (ndw + pw * 32#64 + 16#64) niw)
          (by dsimp only; rw [if_neg hpnz, if_neg hp8_ne, hm5_eq])
          hA2 hNS2 hT0 hcnt_pos hd_lt hnw_LI hpw_spec hh0_2 hh1_2 hh3_2 hh7_2
          hnl_16_2 hnl_24_2 hni_24_2 hord_cnt_2 hord_old_2 hnd_old_2 hhp_2 hfp_2 hfr_2 hg_2
  -- 3. Dispatch the `ite (bit_at_d == 0)` child-ordering test!
  apply Ret.seq_ite
  intro cw_bit _
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · -- `ch_left = true`: `ni.+8 := nl`, `ni.+16 := n`
    refine Ret.ns_seq_storeW2
      (ndw + niw * 32#64 + 8#64) nlw
      (ndw + niw * 32#64 + 16#64) nw
      (eval_node_field_expr _ (ofString "ni") ndw niw 8 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_nl)
      (eval_node_field_expr _ (ofString "ni") ndw niw 16 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_n) ?_
    intro _ _
    exact exec_parent_link true _ rfl
  · -- `ch_left = false`: `ni.+8 := n`, `ni.+16 := nl`
    refine Ret.ns_seq_storeW2
      (ndw + niw * 32#64 + 8#64) nw
      (ndw + niw * 32#64 + 16#64) nlw
      (eval_node_field_expr _ (ofString "ni") ndw niw 8 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_n)
      (eval_node_field_expr _ (ofString "ni") ndw niw 16 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_nl) ?_
    intro _ _
    exact exec_parent_link false _ rfl

/-! ## 2. `memeq` Address Bound When Returning Normally on `1 ≤ n ≤ 60` -/

theorem memeq_ret_key_no_wrap {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (hG0 : GuestInv s0) (a b n : BitVec 64)
    (hn_ge1 : 1 ≤ n.toNat) (hn_le60 : n.toNat ≤ 60)
    (ha_loc : s0.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb_loc : s0.locals.lookup (ofString "b") = some (.val (.word b)))
    (hn_loc : s0.locals.lookup (ofString "n") = some (.val (.word n)))
    (rv : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memeq)).1 =
      some (.returned rv)) :
    b.toNat + n.toNat < 2 ^ 64 := by
  have hb_of_dom_word : ∀ {st : PanSemStateFiniteExact 64 F},
      st.memaddrs = ordinaryDomain → st.memaddrs b → b.toNat + n.toNat < 2 ^ 64 := by
    intro st hma hdom
    rw [hma, ordinaryDomain_iff] at hdom
    have h264 : 2701131776 + 8 * 3888119741 + 60 < 2 ^ 64 := by decide
    omega
  have hb_of_dom_byte : ∀ {st : PanSemStateFiniteExact 64 F},
      st.memaddrs = ordinaryDomain → st.memaddrs (panByteAlignHOL b) → b.toNat + n.toNat < 2 ^ 64 := by
    intro st hma hdom
    rw [hma, ordinaryDomain_iff] at hdom
    have hp := panByteAlign_toNat64 b
    have h264 : 2701131776 + 8 * 3888119741 + 8 + 60 < 2 ^ 64 := by decide
    omega
  have hma0 : s0.memaddrs = ordinaryDomain := hG0.memaddrs
  have first_word_b : ∀ {st : PanSemStateFiniteExact 64 F} {ea eb : ExpHOL 64} {rest : ProgHOL 64},
      st.memaddrs = ordinaryDomain →
      evalAt st eb = some (.val (.word b)) →
      (evaluateHOLFiniteState st
        (.seq (.ite (.cmp .notEqual (.load .one ea) (.load .one eb)) (.return (.const 0#64)) .skip) rest)).1 ≠ some .error →
      b.toNat + n.toNat < 2 ^ 64 := by
    intro st ea eb rest hma heb hev
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hev
    split at hev
    · rename_i cw hcmp
      obtain ⟨_, wb, _, hldb, _⟩ := evalAt_cmp st .notEqual _ _ cw hcmp
      obtain ⟨hdomb, _⟩ := memW_of_eval_load st eb b (.val (.word wb)) heb hldb
      exact hb_of_dom_word hma hdomb
    · exfalso; exact hev rfl
  have first_byte_b : ∀ {st : PanSemStateFiniteExact 64 F} {ea eb : ExpHOL 64} {rest : ProgHOL 64},
      st.memaddrs = ordinaryDomain →
      evalAt st eb = some (.val (.word b)) →
      (evaluateHOLFiniteState st
        (.seq (.ite (.cmp .notEqual (.loadByte ea) (.loadByte eb)) (.return (.const 0#64)) .skip) rest)).1 ≠ some .error →
      b.toNat + n.toNat < 2 ^ 64 := by
    intro st ea eb rest hma heb hev
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hev
    split at hev
    · rename_i cw hcmp
      obtain ⟨_, wb, _, hlbb, _⟩ := evalAt_cmp st .notEqual _ _ cw hcmp
      obtain ⟨hdomb, _⟩ := memB_of_eval_loadByte st eb b (.val (.word wb)) heb hlbb
      exact hb_of_dom_byte hma hdomb
    · exfalso; exact hev rfl
  have while_first_iter : ∀ {st : PanSemStateFiniteExact 64 F} {cond : ExpHOL 64} {body : ProgHOL 64} {r0 : Option (PanSemResultExact 64)},
      (∃ cw, evalAt st cond = some (.val (.word cw)) ∧ cw ≠ 0) →
      r0 = none ∨ (∃ u, r0 = some (.returned u)) →
      ((evaluateHOLFiniteState (decClockHOLFinite st) body).1 ≠ some .error → b.toNat + n.toNat < 2 ^ 64) →
      (evaluateHOLFiniteState st (.while cond body)).1 = r0 →
      b.toNat + n.toNat < 2 ^ 64 := by
    intro st cond body r0 ⟨cw, hcond, hnz⟩ hr0 hbody hw
    rw [evaluateHOLFiniteState_while_total] at hw
    rw [evalHOLFinite_eq_toExact] at hw
    unfold evalAt at hcond
    rw [hcond] at hw
    dsimp only at hw
    rw [if_pos hnz] at hw
    split at hw
    · rcases hr0 with rfl | ⟨_, rfl⟩ <;> simp at hw
    · rw [fixClockHOLFinite_evaluateState] at hw
      apply hbody
      intro herr
      rw [herr] at hw
      rcases hr0 with rfl | ⟨_, rfl⟩ <;> simp at hw
  have while_skip_false : ∀ {st u : PanSemStateFiniteExact 64 F} {cond : ExpHOL 64} {body : ProgHOL 64},
      evalAt st cond = some (.val (.word 0#64)) →
      evaluateHOLFiniteState st (.while cond body) = (none, u) →
      u = st := by
    intro st u cond body hcond hw
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hw
    unfold evalAt at hcond
    rw [hcond] at hw
    dsimp only at hw
    rw [if_neg (by decide : ¬ (0#64 : BitVec 64) ≠ 0)] at hw
    injection hw with _ e; exact e.symm
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memeq,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hret
  rw [evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  have hev0 : @evalHOLExact 64 F _ s0.toExact (fun x => Classical.propDecidable (s0.memaddrs x)) (.const 0#64) =
      some (.val (.word 0#64)) := rfl
  rw [hev0] at hret
  dsimp only at hret
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hret
  dsimp only at hret
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s0
  have hs1_ma : s1.memaddrs = ordinaryDomain := hma0
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb_loc, show ofString "i" ≠ ofString "b" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_loc, show ofString "i" ≠ ofString "n" by decide]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have heb_var : ∀ {st : PanSemStateFiniteExact 64 F},
      st.locals.lookup (ofString "b") = some (.val (.word b)) →
      evalAt st (.var .local (ofString "b")) = some (.val (.word b)) := by
    intro st hb; simp [evalAt, evalHOLExact, hb]
  have heb_i0 : ∀ {st : PanSemStateFiniteExact 64 F},
      st.locals.lookup (ofString "b") = some (.val (.word b)) →
      st.locals.lookup (ofString "i") = some (.val (.word 0#64)) →
      evalAt st (.op .add [.var .local (ofString "b"), .var .local (ofString "i")]) = some (.val (.word b)) := by
    intro st hb hi
    simp [evalAt, evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
  have fast_ite_err_or_skip : ∀ {st : PanSemStateFiniteExact 64 F} {cval : BitVec 64} {ea eb : ExpHOL 64} {rest : ProgHOL 64} {r0 : Option (PanSemResultExact 64)},
      st.memaddrs = ordinaryDomain →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      evalAt st eb = some (.val (.word b)) →
      r0 = none ∨ (∃ u, r0 = some (.returned u)) →
      (evaluateHOLFiniteState st
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const cval))
          (.seq (.ite (.cmp .notEqual (.load .one ea) (.load .one eb)) (.return (.const 0#64)) .skip) rest)
          .skip)).1 = r0 →
      b.toNat + n.toNat < 2 ^ 64 ∨
      evaluateHOLFiniteState st
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const cval))
          (.seq (.ite (.cmp .notEqual (.load .one ea) (.load .one eb)) (.return (.const 0#64)) .skip) rest)
          .skip) = (none, st) := by
    intro st cval ea eb rest r0 hma hn_st heb hr0 hev
    rw [evaluateHOLFiniteState_ite] at hev ⊢
    have hc : @evalHOLExact 64 F _ st.toExact (fun addr => Classical.propDecidable (st.memaddrs addr))
        (.cmp .equal (.var .local (ofString "n")) (.const cval)) =
        some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .equal n cval then 1#64 else 0#64))) := by
      simp [evalHOLExact, hn_st]
    rw [hc] at hev ⊢
    dsimp only at hev ⊢
    by_cases hcz : (if Compiler.Encoders.Asm.wordCmpHOL .equal n cval then (1#64 : BitVec 64) else 0#64) = 0
    · rw [if_pos hcz]; right; exact evaluateHOLFiniteState_skip st
    · rw [if_neg hcz] at hev
      left; apply first_word_b hma heb; intro herr; rw [herr] at hev
      rcases hr0 with rfl | ⟨_, rfl⟩ <;> simp at hev
  have seq_step : ∀ {st : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64} {r0 : Option (PanSemResultExact 64)},
      r0 = none ∨ (∃ u, r0 = some (.returned u)) →
      (evaluateHOLFiniteState st (.seq p1 p2)).1 = r0 →
      (∃ u, (evaluateHOLFiniteState st p1).1 = some (.returned u)) ∨
      ∃ m, evaluateHOLFiniteState st p1 = (none, m) ∧ (evaluateHOLFiniteState m p2).1 = r0 := by
    intro st p1 p2 r0 hr0 h
    rw [evaluateHOLFiniteState_seq_line780] at h
    rcases hp1 : evaluateHOLFiniteState st p1 with ⟨r1, m⟩
    rw [hp1] at h
    cases r1 with
    | none => exact Or.inr ⟨m, rfl, h⟩
    | some x =>
      cases x with
      | returned u => exact Or.inl ⟨u, rfl⟩
      | _ => rcases hr0 with rfl | ⟨_, rfl⟩ <;> simp at h
  -- Helper for `s2` (after the aligned `ite`): if aligned `ite` exited with `(none, s2)`, either `b` was already checked (so `< 2^64`) or `s2 = s1` (when `n < 8` or unaligned)!
  rcases seq_step (Or.inr ⟨rv, rfl⟩) hret with ⟨u1, hu1⟩ | ⟨s2, hs2, hret2⟩
  · -- Aligned `ite` returned `u1`!
    rw [evaluateHOLFiniteState_ite] at hu1
    split at hu1
    · split at hu1
      · simp [evaluateHOLFiniteState_skip] at hu1
      · -- Inside aligned fast block!
        rcases seq_step (Or.inr ⟨u1, rfl⟩) hu1 with ⟨ua, hua⟩ | ⟨m20, hm20, h2⟩
        · rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inr ⟨ua, rfl⟩) hua with hlt | heq
          · exact hlt
          · rw [heq] at hua; simp at hua
        rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm20) with hlt | heq20
        · exact hlt
        rw [hm20] at heq20; injection heq20 with _ eq_m20; subst eq_m20
        rcases seq_step (Or.inr ⟨u1, rfl⟩) h2 with ⟨ub, hub⟩ | ⟨m32, hm32, h3⟩
        · rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inr ⟨ub, rfl⟩) hub with hlt | heq
          · exact hlt
          · rw [heq] at hub; simp at hub
        rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm32) with hlt | heq32
        · exact hlt
        rw [hm32] at heq32; injection heq32 with _ eq_m32; subst eq_m32
        rcases seq_step (Or.inr ⟨u1, rfl⟩) h3 with ⟨uc, huc⟩ | ⟨m52, hm52, h4⟩
        · rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inr ⟨uc, rfl⟩) huc with hlt | heq
          · exact hlt
          · rw [heq] at huc; simp at huc
        rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm52) with hlt | heq52
        · exact hlt
        rw [hm52] at heq52; injection heq52 with _ eq_m52; subst eq_m52
        -- Now `h4` is `(seq while32 while8w).1 = some (.returned u1)` from `s1`!
        -- Notice `while32` and `while8w` only return `0`, and CANNOT return anything if `n < 8`!
        by_cases hn32 : 32 ≤ n.toNat
        · have hcond32 : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
              some (.val (.word 1#64)) := by
            have hle_bv : 32#64 ≤ n := by rw [BitVec.le_def]; exact hn32
            simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
              Compiler.Encoders.Asm.wordCmpHOL, hle_bv]
          rcases seq_step (Or.inr ⟨u1, rfl⟩) h4 with ⟨ud, hud⟩ | ⟨ml32, hml32, _⟩
          · exact while_first_iter ⟨1#64, hcond32, by decide⟩ (Or.inr ⟨ud, rfl⟩)
              (fun herr => first_word_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) hud
          · exact while_first_iter ⟨1#64, hcond32, by decide⟩ (Or.inl rfl)
              (fun herr => first_word_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) (congrArg Prod.fst hml32)
        · have hcond32_f : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
              some (.val (.word 0#64)) := by
            have hlt_bv : n < 32#64 := by rw [BitVec.lt_def]; change n.toNat < 32; omega
            have hnle_bv : ¬ (32#64 ≤ n) := by rw [BitVec.le_def]; change ¬ (32 ≤ n.toNat); omega
            simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
              Compiler.Encoders.Asm.wordCmpHOL, hnle_bv, hlt_bv]
          rcases seq_step (Or.inr ⟨u1, rfl⟩) h4 with ⟨ud, hud⟩ | ⟨ml32, hml32, hl8w⟩
          · rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hud
            unfold evalAt at hcond32_f; rw [hcond32_f] at hud; simp at hud
          have hml32_eq := while_skip_false hcond32_f hml32; subst hml32_eq
          by_cases hn8 : 8 ≤ n.toNat
          · have hcond8 : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                some (.val (.word 1#64)) := by
              have hle_bv : 8#64 ≤ n := by rw [BitVec.le_def]; exact hn8
              simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                Compiler.Encoders.Asm.wordCmpHOL, hle_bv]
            exact while_first_iter ⟨1#64, hcond8, by decide⟩ (Or.inr ⟨u1, rfl⟩)
              (fun herr => first_word_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) hl8w
          · have hcond8_f : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                some (.val (.word 0#64)) := by
              have hlt_bv : n < 8#64 := by rw [BitVec.lt_def]; change n.toNat < 8; omega
              have hnle_bv : ¬ (8#64 ≤ n) := by rw [BitVec.le_def]; change ¬ (8 ≤ n.toNat); omega
              simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                Compiler.Encoders.Asm.wordCmpHOL, hnle_bv, hlt_bv]
            rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hl8w
            unfold evalAt at hcond8_f; rw [hcond8_f] at hl8w; simp at hl8w
    · simp at hu1
  · -- Aligned `ite` exited with `(none, s2)`!
    have seq_none_pair : ∀ {st u : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64},
        evaluateHOLFiniteState st (.seq p1 p2) = (none, u) →
        ∃ m, evaluateHOLFiniteState st p1 = (none, m) ∧ evaluateHOLFiniteState m p2 = (none, u) := by
      intro st u p1 p2 h
      rw [evaluateHOLFiniteState_seq_line780] at h
      rcases hp1 : evaluateHOLFiniteState st p1 with ⟨r1, m⟩
      rw [hp1] at h
      cases r1 with
      | none => exact ⟨m, rfl, h⟩
      | some _ => simp at h
    -- Either `b.toNat + n.toNat < 2 ^ 64` ALREADY holds (if `8 ≤ n` and aligned branch ran), OR `s2 = s1`!
    have hs2_or : b.toNat + n.toNat < 2 ^ 64 ∨ s2 = s1 := by
      rw [evaluateHOLFiniteState_ite] at hs2
      split at hs2
      · split at hs2
        · rw [evaluateHOLFiniteState_skip] at hs2; injection hs2 with _ e; exact Or.inr e.symm
        · obtain ⟨m20, hm20, hs2'⟩ := seq_none_pair hs2
          rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm20) with hlt | heq20
          · exact Or.inl hlt
          rw [hm20] at heq20; injection heq20 with _ eq_m20; subst eq_m20
          obtain ⟨m32, hm32, hs2'⟩ := seq_none_pair hs2'
          rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm32) with hlt | heq32
          · exact Or.inl hlt
          rw [hm32] at heq32; injection heq32 with _ eq_m32; subst eq_m32
          obtain ⟨m52, hm52, hs2'⟩ := seq_none_pair hs2'
          rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm52) with hlt | heq52
          · exact Or.inl hlt
          rw [hm52] at heq52; injection heq52 with _ eq_m52; subst eq_m52
          obtain ⟨ml32, hml32, hs2'⟩ := seq_none_pair hs2'
          by_cases hn32 : 32 ≤ n.toNat
          · left
            have hcond32 : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
                some (.val (.word 1#64)) := by
              have hle_bv : 32#64 ≤ n := by rw [BitVec.le_def]; exact hn32
              simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                Compiler.Encoders.Asm.wordCmpHOL, hle_bv]
            exact while_first_iter ⟨1#64, hcond32, by decide⟩ (Or.inl rfl)
              (fun herr => first_word_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) (congrArg Prod.fst hml32)
          · have hcond32_f : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
                some (.val (.word 0#64)) := by
              have hlt_bv : n < 32#64 := by rw [BitVec.lt_def]; change n.toNat < 32; omega
              have hnle_bv : ¬ (32#64 ≤ n) := by rw [BitVec.le_def]; change ¬ (32 ≤ n.toNat); omega
              simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                Compiler.Encoders.Asm.wordCmpHOL, hnle_bv, hlt_bv]
            have hml32_eq := while_skip_false hcond32_f hml32; subst hml32_eq
            by_cases hn8 : 8 ≤ n.toNat
            · left
              have hcond8 : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                  some (.val (.word 1#64)) := by
                have hle_bv : 8#64 ≤ n := by rw [BitVec.le_def]; exact hn8
                simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                  Compiler.Encoders.Asm.wordCmpHOL, hle_bv]
              exact while_first_iter ⟨1#64, hcond8, by decide⟩ (Or.inl rfl)
                (fun herr => first_word_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) (congrArg Prod.fst hs2')
            · right
              have hcond8_f : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                  some (.val (.word 0#64)) := by
                have hlt_bv : n < 8#64 := by rw [BitVec.lt_def]; change n.toNat < 8; omega
                have hnle_bv : ¬ (8#64 ≤ n) := by rw [BitVec.le_def]; change ¬ (8 ≤ n.toNat); omega
                simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                  Compiler.Encoders.Asm.wordCmpHOL, hnle_bv, hlt_bv]
              exact while_skip_false hcond8_f hs2'
      · simp at hs2
    rcases hs2_or with hlt | rfl
    · exact hlt
    -- Now `s2 = s1`! Next in `hret2` is `seq while8b (seq while1b (return 1))`!
    by_cases hn8 : 8 ≤ n.toNat
    · have hcond8b : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
          some (.val (.word 1#64)) := by
        have hle_bv : 8#64 ≤ n := by rw [BitVec.le_def]; exact hn8
        simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
          Compiler.Encoders.Asm.wordCmpHOL, hle_bv]
      rcases seq_step (Or.inr ⟨rv, rfl⟩) hret2 with ⟨ue, hue⟩ | ⟨s3, hs3, _⟩
      · exact while_first_iter ⟨1#64, hcond8b, by decide⟩ (Or.inr ⟨ue, rfl⟩)
          (fun herr => first_byte_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) hue
      · exact while_first_iter ⟨1#64, hcond8b, by decide⟩ (Or.inl rfl)
          (fun herr => first_byte_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) (congrArg Prod.fst hs3)
    · have hcond8b_f : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
          some (.val (.word 0#64)) := by
        have hlt_bv : n < 8#64 := by rw [BitVec.lt_def]; change n.toNat < 8; omega
        have hnle_bv : ¬ (8#64 ≤ n) := by rw [BitVec.le_def]; change ¬ (8 ≤ n.toNat); omega
        simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
          Compiler.Encoders.Asm.wordCmpHOL, hnle_bv, hlt_bv]
      rcases seq_step (Or.inr ⟨rv, rfl⟩) hret2 with ⟨ue, hue⟩ | ⟨s3, hs3, hret3⟩
      · rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hue
        unfold evalAt at hcond8b_f; rw [hcond8b_f] at hue; simp at hue
      have hs3_eq := while_skip_false hcond8b_f hs3; subst hs3_eq
      -- Now `s3 = s1`, and `1 ≤ n.toNat`, so `0 < n` (`while1b` condition `i < n` is TRUE)!
      have hcond1b : evalAt s1 (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
          some (.val (.word 1#64)) := by
        have hlt_bv : (0#64 : BitVec 64) < n := by rw [BitVec.lt_def]; change 0 < n.toNat; omega
        simp [evalAt, evalHOLExact, hs1_n, hs1_i, Compiler.Encoders.Asm.wordCmpHOL, hlt_bv]
      rcases seq_step (Or.inr ⟨rv, rfl⟩) hret3 with ⟨uf, huf⟩ | ⟨s4, hs4, _⟩
      · exact while_first_iter ⟨1#64, hcond1b, by decide⟩ (Or.inr ⟨uf, rfl⟩)
          (fun herr => first_byte_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) huf
      · exact while_first_iter ⟨1#64, hcond1b, by decide⟩ (Or.inl rfl)
          (fun herr => first_byte_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) (congrArg Prod.fst hs4)

/-! ## 3. Full `htab_set` Body Spec and `htab_set_spec_proof` -/

theorem htab_set_body_spec {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (tw keyw valw : BitVec 64)
    (ht0 : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey0 : s0.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hval0 : s0.locals.lookup (ofString "value") = some (.val (.word valw)))
    (hA0 : ArenaReady s0)
    (hW0 : HtabWF s0 tw.toNat)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_set)
      (fun _ post => HtabExitAt tw.toNat s0 post) := by
  set t := tw.toNat
  have hLF := locFree_htabExitAt s0 t
  obtain ⟨hB0, L0, I0, Fr0, hT0⟩ := (htabWF_iff s0 t).mp hW0
  obtain ⟨hnc0_lt, hst0_ge8, hst0_le64, hst0_al, ht_lo, ht_hi, ht_al⟩ := htabBlocks_bounds hB0
  have hnx0_le : hdr s0 t 8 ≤ hdr s0 t 10 + 1 := hB0.2.2.2.2.2.2.2
  have hklen_le60 : hdr s0 t 0 ≤ 60 := hB0.2.2.2.1
  have hklen_le_st : hdr s0 t 0 ≤ hdr s0 t 1 := by have := hB0.2.2.2.2.1; omega
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom0_t0, hm0_t0⟩ := word_of_hdr s0 tw 0 (by omega) hB0
  obtain ⟨hdom0_t1, hm0_t1⟩ := word_of_hdr s0 tw 1 (by omega) hB0
  obtain ⟨hdom0_t4, hm0_t4⟩ := word_of_hdr s0 tw 4 (by omega) hB0
  obtain ⟨hdom0_t5, hm0_t5⟩ := word_of_hdr s0 tw 5 (by omega) hB0
  obtain ⟨hdom0_t7, hm0_t7⟩ := word_of_hdr s0 tw 7 (by omega) hB0
  set klenw := BitVec.ofNat 64 (hdr s0 t 0)
  set stridew := BitVec.ofNat 64 (hdr s0 t 1)
  set keysw := BitVec.ofNat 64 (hdr s0 t 4)
  set nodesw0 := BitVec.ofNat 64 (hdr s0 t 5)
  set rootw0 := BitVec.ofNat 64 (hdr s0 t 7)
  have hklenw_nat : klenw.toNat = hdr s0 t 0 := by rw [BitVec.toNat_ofNat]; omega
  have hstridew_nat : stridew.toNat = hdr s0 t 1 := by rw [BitVec.toNat_ofNat]; omega
  have hkeysw_nat : keysw.toNat = hdr s0 t 4 := by
    have hk_in := (hB0.1 (hdr s0 t 4, (hdr s0 t 10 + 1) * hdr s0 t 1) (by simp [htabFootprint])).1
    unfold Inside at hk_in; rw [BitVec.toNat_ofNat]; omega
  have hnodesw0_nat : nodesw0.toNat = hdr s0 t 5 := by
    have hn_in := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hn_in; rw [BitVec.toNat_ofNat]; omega
  htab_unfold Guest.Software.guestFn_htab_set
  -- 1. dec klen := load(t + 0)
  apply Ret.dec_lf hLF; intro vkl hvkl
  obtain ⟨_, rfl⟩ := ev_field_load s0 (ofString "t") tw 0#64 ht0 vkl hvkl
  have hm0 : s0.memory (tw + 0#64) = .word klenw := hm0_t0
  rw [hm0]
  -- 2. dec stride := load(t + 8)
  apply Ret.dec_lf hLF; intro vst hvst
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 8#64
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht0, show ofString "klen" ≠ ofString "t" by decide]) vst hvst
  have hm8 : (setVarHOLFinite (ofString "klen") (.val (.word klenw)) s0).memory (tw + 8#64) = .word stridew := hm0_t1
  rw [hm8]
  -- 3. decCall leaf := htab_find_leaf(t, key)
  let s_fl_pre := setVarHOLFinite (ofString "stride") (.val (.word stridew))
    (setVarHOLFinite (ofString "klen") (.val (.word klenw)) s0)
  have ht_fl_pre : s_fl_pre.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht0,
      show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide]
  have hkey_fl_pre : s_fl_pre.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
    simp [s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey0,
      show ofString "stride" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide]
  refine Ret.decCall2_lf hLF hA0.1.code (by decide) lookup_htab_find_leaf tw keyw
    (by simp [evalAt, evalHOLExact]; exact ht_fl_pre)
    (by simp [evalAt, evalHOLExact]; exact hkey_fl_pre) ?_
  intro leafw post_fl hrun_fl
  let entry_fl := callEntryStateHOLFinite s_fl_pre
    ((HolFiniteMapExact.empty.update (ofString "t", .val (.word tw))).update (ofString "key", .val (.word keyw)))
  have hW_entry_fl : HtabWF entry_fl t := (htabWF_locals s0 _ _ t).mpr hW0
  have hfl_spec := find_leaf_spec_wf entry_fl tw
    (by simp [entry_fl, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "key" ≠ ofString "t" by decide])
    hW_entry_fl (.val (.word leafw)) (by rw [hrun_fl])
  rw [hrun_fl] at hfl_spec
  obtain ⟨lw', hlw_eq, hfr_fl, hleaf_cases⟩ := hfl_spec
  dsimp only at hfr_fl
  injection hlw_eq with h1; injection h1 with h2; subst h2
  -- Notice `LocFrame entry_fl post_fl` gives `LocFrame s0 { post_fl with locals := s_fl_pre.locals }`!
  have hs_lf_fr : LocFrame s0 (setVarHOLFinite (ofString "leaf") (.val (.word leafw)) { post_fl with locals := s_fl_pre.locals }) := by
    unfold LocFrame at hfr_fl ⊢
    dsimp [setVarHOLFinite]
    rw [hfr_fl]; rfl
  -- 4. dec keys := load(t + 32)
  apply Ret.dec_lf hLF; intro vks hvks
  obtain ⟨_, hvks_eq⟩ := ev_field_load _ (ofString "t") tw 32#64
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "leaf" ≠ ofString "t" by decide]; exact ht_fl_pre) vks hvks
  have hm32_lf : (setVarHOLFinite (ofString "leaf") (.val (.word leafw)) { post_fl with locals := s_fl_pre.locals }).memory (tw + 32#64) = .word keysw := by
    rw [hs_lf_fr.memory]; exact hm0_t4
  rw [hm32_lf] at hvks_eq
  subst hvks_eq
  let s_k := setVarHOLFinite (ofString "keys") (.val (.word keysw))
    (setVarHOLFinite (ofString "leaf") (.val (.word leafw)) { post_fl with locals := s_fl_pre.locals })
  have hs_k_fr : LocFrame s0 s_k := hs_lf_fr.setVar _ _
  have hcode_sk : s_k.code = originalRuntimeCode := by unfold LocFrame at hs_k_fr; rw [hs_k_fr]; exact hA0.1.code
  have ht_sk : s_k.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht0,
      show ofString "keys" ≠ ofString "t" by decide, show ofString "leaf" ≠ ofString "t" by decide,
      show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide]
  have hkey_sk : s_k.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey0,
      show ofString "keys" ≠ ofString "key" by decide, show ofString "leaf" ≠ ofString "key" by decide,
      show ofString "stride" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide]
  have hval_sk : s_k.locals.lookup (ofString "value") = some (.val (.word valw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval0,
      show ofString "keys" ≠ ofString "value" by decide, show ofString "leaf" ≠ ofString "value" by decide,
      show ofString "stride" ≠ ofString "value" by decide, show ofString "klen" ≠ ofString "value" by decide]
  have hleaf_sk : s_k.locals.lookup (ofString "leaf") = some (.val (.word leafw)) := by
    simp [s_k, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "keys" ≠ ofString "leaf" by decide]
  have hkeys_sk : s_k.locals.lookup (ofString "keys") = some (.val (.word keysw)) := by
    simp [s_k, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hkl_sk : s_k.locals.lookup (ofString "klen") = some (.val (.word klenw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "klen" by decide, show ofString "leaf" ≠ ofString "klen" by decide,
      show ofString "stride" ≠ ofString "klen" by decide]
  have hst_sk : s_k.locals.lookup (ofString "stride") = some (.val (.word stridew)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "stride" by decide, show ofString "leaf" ≠ ofString "stride" by decide]
  -- 5. `ite (leaf == 0)`
  refine Ret.ite_ret
    (fun _ => by
      rw [evaluateHOLFiniteState_decCall_total]
      split
      · simp
      · split
        · simp
        · split
          · simp
          · dsimp only
            rw [fixClockHOLFinite_evaluateState]
            rcases evaluateHOLFiniteState _ _ with ⟨r, _⟩
            cases r with
            | none => simp
            | some r =>
              cases r with
              | returned _ =>
                dsimp only; split
                · exact noFlow_seq_right fun _ => noFlow_ret
                · simp
              | _ => simp)
    ?_
  intro cw_lf hcw_lf
  have hcw_lf_spec : (cw_lf ≠ 0 → leafw = 0) ∧ (cw_lf = 0 → leafw ≠ 0) := by
    obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp s_k .equal _ _ cw_lf hcw_lf
    simp [evalAt, evalHOLExact, hleaf_sk] at hva hvb
    subst hva hvb
    constructor
    · intro hnz; by_contra hne
      have hne' : leafw ≠ 0#64 := hne
      simp [Compiler.Encoders.Asm.wordCmpHOL, hne'] at hcw_eq
      exact hnz hcw_eq
    · intro hz heq
      have heq' : leafw = 0#64 := heq
      simp [Compiler.Encoders.Asm.wordCmpHOL, heq'] at hcw_eq
      rw [hz] at hcw_eq; exact absurd hcw_eq (by decide)
  refine ⟨fun hcw_nz => ?_, fun hcw_z => ?_⟩
  · -- Branch A: `leaf == 0` (`cnt = 0`)!
    have hlf0 := hcw_lf_spec.1 hcw_nz
    have hcnt0 : hdr s0 t 3 = 0 := by
      rcases hleaf_cases with ⟨_, hc⟩ | ⟨hnz, _⟩
      · exact hc
      · exact absurd hlf0 hnz
    exact htab_set_branch_empty s0 s_k tw keyw valw hLF hs_k_fr hA0 hW0 hal0 hcnt0 ht_sk hkey_sk hval_sk
  · -- `leaf != 0` (`0 < cnt`, `leafw.toNat ∈ L0`)!
    have hlf_nz := hcw_lf_spec.2 hcw_z
    obtain ⟨_, hcnt_pos_efl, hleaf_mem_efl⟩ := hleaf_cases.resolve_left (fun h => hlf_nz h.1)
    have hcnt_pos : 0 < hdr s0 t 3 := hcnt_pos_efl
    have hleaf_mem : ∀ L I Fr,
        TreeWF L I Fr (hdr s0 t 8) (hdr s0 t 0) (hdr s0 t 3) (hdr s0 t 7) (hdr s0 t 9)
          (nodeF s0 (hdr s0 t 5)) (fun i => memW s0 (hdr s0 t 6 + 8 * i)) →
        leafw.toNat ∈ L := hleaf_mem_efl
    have hleaf_L0 : leafw.toNat ∈ L0 := hleaf_mem L0 I0 Fr0 hT0
    have hleaf_rng := (hT0.2.2.1 leafw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ hleaf_L0))
    have hleaf_lt_nc0 : leafw.toNat < hdr s0 t 10 + 1 := by omega
    have hkeys0_in := (hB0.1 (hdr s0 t 4, (hdr s0 t 10 + 1) * hdr s0 t 1) (by simp [htabFootprint])).1
    change hdr s0 t 4 ≥ sourceBase ∧ hdr s0 t 4 + (hdr s0 t 10 + 1) * hdr s0 t 1 ≤ heapEnd at hkeys0_in
    have hmul_lf_le : leafw.toNat * hdr s0 t 1 + hdr s0 t 1 ≤ (hdr s0 t 10 + 1) * hdr s0 t 1 := by
      have h1 : (leafw.toNat + 1) * hdr s0 t 1 ≤ (hdr s0 t 10 + 1) * hdr s0 t 1 := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1; exact h1
    set lkeyw := keysw + leafw * stridew
    have hlkeyw_nat : lkeyw.toNat = hdr s0 t 4 + leafw.toNat * hdr s0 t 1 := by
      have hmul_nat : (leafw * stridew).toNat = leafw.toNat * hdr s0 t 1 := by
        rw [BitVec.toNat_mul, hstridew_nat, Nat.mod_eq_of_lt (by omega)]
      change (keysw + leafw * stridew).toNat = _
      rw [BitVec.toNat_add, hkeysw_nat, hmul_nat, Nat.mod_eq_of_lt (by omega)]
    have hev_lkey : evalAt s_k (.op .add [.var .local (ofString "keys"),
        .panop .mul [.var .local (ofString "leaf"), .var .local (ofString "stride")]]) =
        some (.val (.word lkeyw)) := by
      simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
        hkeys_sk, hleaf_sk, hst_sk, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
        valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
      have hz : leafw * stridew + (0 : BitVec 64) = leafw * stridew := BitVec.add_zero _
      rw [hz]
    -- 6. `decCall eq := memeq(keys + leaf * stride, key, klen)`
    refine Ret.decCall3_lf hLF hcode_sk (by decide) (by decide) (by decide)
      lookup_memeq_fn lkeyw keyw klenw hev_lkey
      (by simp [evalAt, evalHOLExact]; exact hkey_sk)
      (by simp [evalAt, evalHOLExact]; exact hkl_sk) ?_
    intro eqw post_meq hrun_meq
    let entry_meq := callEntryStateHOLFinite s_k
      (((HolFiniteMapExact.empty.update (ofString "a", .val (.word lkeyw))).update
        (ofString "b", .val (.word keyw))).update (ofString "n", .val (.word klenw)))
    have hfr_meq_eval := locFrameW_eval (sourceFnBody Guest.Software.guestFn_memeq) (by rfl) entry_meq
    rw [hrun_meq] at hfr_meq_eval
    dsimp only at hfr_meq_eval
    let s_eq := setVarHOLFinite (ofString "eq") (.val (.word eqw)) { post_meq with locals := s_k.locals }
    have hs_eq_fr : LocFrame s0 s_eq := by
      unfold LocFrame at hs_k_fr hfr_meq_eval ⊢
      dsimp [s_eq, setVarHOLFinite]
      rw [hfr_meq_eval]
      dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]
      rw [hs_k_fr]
    have hcode_seq : s_eq.code = originalRuntimeCode := by unfold LocFrame at hs_eq_fr; rw [hs_eq_fr]; exact hA0.1.code
    have ht_seq : s_eq.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_sk, show ofString "eq" ≠ ofString "t" by decide]
    have hkey_seq : s_eq.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey_sk, show ofString "eq" ≠ ofString "key" by decide]
    have hval_seq : s_eq.locals.lookup (ofString "value") = some (.val (.word valw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval_sk, show ofString "eq" ≠ ofString "value" by decide]
    have hleaf_seq : s_eq.locals.lookup (ofString "leaf") = some (.val (.word leafw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hleaf_sk, show ofString "eq" ≠ ofString "leaf" by decide]
    have hkeys_seq : s_eq.locals.lookup (ofString "keys") = some (.val (.word keysw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkeys_sk, show ofString "eq" ≠ ofString "keys" by decide]
    have hkl_seq : s_eq.locals.lookup (ofString "klen") = some (.val (.word klenw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkl_sk, show ofString "eq" ≠ ofString "klen" by decide]
    have hst_seq : s_eq.locals.lookup (ofString "stride") = some (.val (.word stridew)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_sk, show ofString "eq" ≠ ofString "stride" by decide]
    have heq_seq : s_eq.locals.lookup (ofString "eq") = some (.val (.word eqw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    -- 7. `ite (eq != 0)`
    refine Ret.ite_ret
      (fun _ => noFlow_seq_right fun _ => noFlow_ret) ?_
    intro cw_eq hcw_eq
    have hcw_eq_spec : (cw_eq ≠ 0 → eqw ≠ 0) ∧ (cw_eq = 0 → eqw = 0) := by
      obtain ⟨va, vb, hva, hvb, hcwe⟩ := evalAt_cmp s_eq .notEqual _ _ cw_eq hcw_eq
      simp [evalAt, evalHOLExact, heq_seq] at hva hvb
      subst hva hvb
      constructor
      · intro hnz heq0
        have heq0' : eqw = 0#64 := heq0
        simp [Compiler.Encoders.Asm.wordCmpHOL, heq0'] at hcwe
        exact hnz hcwe
      · intro hz; by_contra hne
        have hne' : eqw ≠ 0#64 := hne
        simp [Compiler.Encoders.Asm.wordCmpHOL, hne'] at hcwe
        rw [hz] at hcwe; exact absurd hcwe (by decide)
    refine ⟨fun hcw_eq_nz => ?_, fun hcw_eq_z => ?_⟩
    · -- Branch B: `eq != 0` -> key match overwrite!
      exact htab_set_branch_overwrite s0 s_eq tw leafw valw hs_eq_fr hA0 hW0 hal0 hleaf_mem ht_seq hleaf_seq hval_seq
    · -- Branch C: `eq == 0` -> key mismatch -> crit-bit splice!
      have heqw0 : eqw = 0 := hcw_eq_spec.2 hcw_eq_z
      have hG_entry_meq : GuestInv entry_meq := by
        have hfr_em : LocFrame s0 entry_meq := by
          unfold LocFrame at hs_k_fr ⊢
          dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]
          rw [hs_k_fr]
        unfold LocFrame at hfr_em; rw [hfr_em]
        exact guestInv_with_locals_clock s0 _ _ hA0.1
      have ha_meq : entry_meq.locals.lookup (ofString "a") = some (.val (.word lkeyw)) := by
        simp [entry_meq, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "a" by decide, show ofString "b" ≠ ofString "a" by decide]
      have hb_meq : entry_meq.locals.lookup (ofString "b") = some (.val (.word keyw)) := by
        simp [entry_meq, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "b" by decide]
      have hn_meq : entry_meq.locals.lookup (ofString "n") = some (.val (.word klenw)) := by
        simp [entry_meq, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hklen_ge1 : 1 ≤ klenw.toNat := by rw [hklenw_nat]; exact hB0.2.2.1
      have hklen_le60_w : klenw.toNat ≤ 60 := by rw [hklenw_nat]; exact hklen_le60
      have hlkey_nw : lkeyw.toNat + klenw.toNat < 2 ^ 64 := by
        rw [hlkeyw_nat, hklenw_nat]; omega
      have hrun_meq0 : (evaluateHOLFiniteState entry_meq (sourceFnBody Guest.Software.guestFn_memeq)).1 =
          some (.returned (.val (.word 0))) := by
        rw [hrun_meq, heqw0]
      have hkey_nw : keyw.toNat + klenw.toNat < 2 ^ 64 :=
        memeq_ret_key_no_wrap entry_meq hG_entry_meq lkeyw keyw klenw
          hklen_ge1 hklen_le60_w ha_meq hb_meq hn_meq (.val (.word 0)) hrun_meq0
      have hdiff_meq := memeq_body_ret0_exists_diff entry_meq hG_entry_meq lkeyw keyw klenw
        hklen_le60_w hlkey_nw hkey_nw ha_meq hb_meq hn_meq hrun_meq0
      have hmemB_em_s0 : ∀ addr : Nat, memB entry_meq addr = memB s0 addr := by
        intro addr
        have hmem_em : entry_meq.memory = s0.memory := by
          dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]; exact hs_k_fr.memory
        have hbe_em : entry_meq.be = s0.be := by
          dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]
          unfold LocFrame at hs_k_fr; rw [hs_k_fr]
        simp [memB, hmem_em, hbe_em]
      have hdiff_s0 : ∃ k < klenw.toNat,
          memB s0 ((keyw + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((lkeyw + BitVec.ofNat 64 k).toNat) := by
        obtain ⟨k, hk, hne⟩ := hdiff_meq
        rw [hmemB_em_s0, hmemB_em_s0] at hne
        exact ⟨k, hk, hne.symm⟩
      -- 8. `decCall d := htab_first_diff(key, keys + leaf * stride, klen)`
      have hev_lkey_seq : evalAt s_eq (.op .add [.var .local (ofString "keys"),
          .panop .mul [.var .local (ofString "leaf"), .var .local (ofString "stride")]]) =
          some (.val (.word lkeyw)) := by
        simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          hkeys_seq, hleaf_seq, hst_seq, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
          valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
        have hz : leafw * stridew + (0 : BitVec 64) = leafw * stridew := BitVec.add_zero _
        rw [hz]
      refine Ret.decCall3_lf hLF hcode_seq (by decide) (by decide) (by decide)
        lookup_htab_first_diff keyw lkeyw klenw
        (by simp [evalAt, evalHOLExact]; exact hkey_seq)
        hev_lkey_seq
        (by simp [evalAt, evalHOLExact]; exact hkl_seq) ?_
      intro dw post_fd hrun_fd
      let entry_fd := callEntryStateHOLFinite s_eq
        (((HolFiniteMapExact.empty.update (ofString "a", .val (.word keyw))).update
          (ofString "b", .val (.word lkeyw))).update (ofString "key_len", .val (.word klenw)))
      have hfr_fd_eval := locFrameW_eval (sourceFnBody Guest.Software.guestFn_htab_first_diff) (by rfl) entry_fd
      rw [hrun_fd] at hfr_fd_eval
      dsimp only at hfr_fd_eval
      have hdiff_fd : ∃ k < klenw.toNat,
          memB entry_fd ((keyw + BitVec.ofNat 64 k).toNat) ≠ memB entry_fd ((lkeyw + BitVec.ofNat 64 k).toNat) := by
        have hmem_fd : entry_fd.memory = s0.memory := by
          dsimp [entry_fd, callEntryStateHOLFinite, decClockHOLFinite]; exact hs_eq_fr.memory
        have hbe_fd : entry_fd.be = s0.be := by
          dsimp [entry_fd, callEntryStateHOLFinite, decClockHOLFinite]
          unfold LocFrame at hs_eq_fr; rw [hs_eq_fr]
        obtain ⟨k, hk, hne⟩ := hdiff_s0
        refine ⟨k, hk, ?_⟩
        simpa [memB, hmem_fd, hbe_fd] using hne
      obtain ⟨dw', hdw_eq, hd_lt_w⟩ := htab_first_diff_ret_lt entry_fd keyw lkeyw klenw hklen_le60_w hdiff_fd
        (by simp [entry_fd, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "key_len" ≠ ofString "a" by decide, show ofString "b" ≠ ofString "a" by decide])
        (by simp [entry_fd, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "key_len" ≠ ofString "b" by decide])
        (by simp [entry_fd, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (.val (.word dw)) (by rw [hrun_fd])
      injection hdw_eq with h1; injection h1 with h2; subst h2
      have hd_lt : dw.toNat < 8 * hdr s0 t 0 := by rw [← hklenw_nat]; exact hd_lt_w
      let s_d := setVarHOLFinite (ofString "d") (.val (.word dw)) { post_fd with locals := s_eq.locals }
      have hs_d_fr : LocFrame s0 s_d := by
        unfold LocFrame at hs_eq_fr hfr_fd_eval ⊢
        dsimp [s_d, setVarHOLFinite]
        rw [hfr_fd_eval]
        dsimp [entry_fd, callEntryStateHOLFinite, decClockHOLFinite]
        rw [hs_eq_fr]
      have ht_sd : s_d.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_seq, show ofString "d" ≠ ofString "t" by decide]
      have hkey_sd : s_d.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey_seq, show ofString "d" ≠ ofString "key" by decide]
      have hval_sd : s_d.locals.lookup (ofString "value") = some (.val (.word valw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval_seq, show ofString "d" ≠ ofString "value" by decide]
      -- 9. `dec nodes := load(t + 40); dec p := 0; dec n := load(t + 56)`
      apply Ret.dec_lf hLF; intro vnd hvnd
      obtain ⟨_, hvnd_eq⟩ := ev_field_load s_d (ofString "t") tw 40#64 ht_sd vnd hvnd
      rw [hs_d_fr.memory, hm0_t5] at hvnd_eq; subst hvnd_eq
      apply Ret.dec_lf hLF; intro vp0 hvp0
      have hvp0_eq : vp0 = .val (.word 0#64) := by simp [evalAt, evalHOLExact] at hvp0; exact hvp0.symm
      subst hvp0_eq
      apply Ret.dec_lf hLF; intro vr0 hvr0
      obtain ⟨_, hvr0_eq⟩ := ev_field_load _ (ofString "t") tw 56#64
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "p" ≠ ofString "t" by decide, show ofString "nodes" ≠ ofString "t" by decide]; exact ht_sd) vr0 hvr0
      have hm56_sd : (setVarHOLFinite (ofString "p") (.val (.word 0#64))
          (setVarHOLFinite (ofString "nodes") (.val (.word nodesw0)) s_d)).memory (tw + 56#64) = .word rootw0 := by
        dsimp [setVarHOLFinite]; rw [hs_d_fr.memory]; exact hm0_t7
      rw [hm56_sd] at hvr0_eq; subst hvr0_eq
      let s_lp := setVarHOLFinite (ofString "n") (.val (.word rootw0))
        (setVarHOLFinite (ofString "p") (.val (.word 0#64))
          (setVarHOLFinite (ofString "nodes") (.val (.word nodesw0)) s_d))
      have hs_lp_fr : LocFrame s0 s_lp := ((hs_d_fr.setVar _ _).setVar _ _).setVar _ _
      have hrootw0_nat : rootw0.toNat = hdr s0 t 7 := by
        have hr_mem : hdr s0 t 7 ∈ L0 ++ I0 := (hT0.2.2.2.2.2.2.2.1 hcnt_pos).1
        have hr_rng := (hT0.2.2.1 (hdr s0 t 7)).mp (List.mem_append_left _ hr_mem)
        rw [BitVec.toNat_ofNat]; omega
      -- 10. Descent `while (n != 0)` loop!
      apply Ret.seq
      · intro v hv
        refine False.elim (while_noRet _ _ (fun st v' => ?_) s_lp.clock s_lp le_rfl v hv)
        exact NoRet.dec' (NoRet.seq (NoRet.ite NoRet.brk NoRet.skip)
          (NoRet.seq NoRet.assign (NoRet.ite NoRet.assign NoRet.assign))) st v'
      intro u_lp hu_lp
      have hT_slp : TreeWF L0 I0 Fr0 (hdr s0 t 8) (hdr s0 t 0) (hdr s0 t 3) (hdr s0 t 7) (hdr s0 t 9)
          (nodeF s_lp nodesw0.toNat) (fun i => memW s0 (hdr s0 t 6 + 8 * i)) := by
        have hnf_eq : nodeF s_lp nodesw0.toNat = nodeF s0 (hdr s0 t 5) := by
          funext z off; simp [nodeF, memW, hs_lp_fr.memory, hnodesw0_nat]
        rw [hnf_eq]; exact hT0
      obtain ⟨hu_fr_lp, hu_keep, pw, nw, hp_ulp, hn_ulp, hnw_LI, hpw_spec⟩ :=
        set_descent_loop s_lp u_lp nodesw0 dw rootw0 L0 I0 Fr0
          (hdr s0 t 8) (hdr s0 t 0) (hdr s0 t 3) (hdr s0 t 7) (hdr s0 t 9)
          (fun i => memW s0 (hdr s0 t 6 + 8 * i))
          hcnt_pos hd_lt (by omega) hrootw0_nat hT_slp
          (by simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "nodes" by decide, show ofString "p" ≠ ofString "nodes" by decide])
          (by simp [s_lp, s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "d" by decide, show ofString "p" ≠ ofString "d" by decide,
            show ofString "nodes" ≠ ofString "d" by decide])
          (by simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "p" by decide])
          (by simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          _ rfl hu_lp
      have hu_fr : LocFrame s0 u_lp := hs_lp_fr.trans hu_fr_lp
      have hpw_spec0 : (pw.toNat = 0 ∧ nw.toNat = hdr s0 t 7) ∨
          (pw.toNat ∈ I0 ∧ nw.toNat ≠ hdr s0 t 7 ∧ pw.toNat = nodeF s0 (hdr s0 t 5) nw.toNat 0) := by
        have hnf_eq : nodeF s_lp nodesw0.toNat nw.toNat 0 = nodeF s0 (hdr s0 t 5) nw.toNat 0 := by
          simp [nodeF, memW, hs_lp_fr.memory, hnodesw0_nat]
        rw [hnf_eq] at hpw_spec; exact hpw_spec
      have ht_ulp : u_lp.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        rw [hu_keep (ofString "t") (by decide) (by decide)]
        simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_sd,
          show ofString "n" ≠ ofString "t" by decide, show ofString "p" ≠ ofString "t" by decide,
          show ofString "nodes" ≠ ofString "t" by decide]
      have hkey_ulp : u_lp.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
        rw [hu_keep (ofString "key") (by decide) (by decide)]
        simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey_sd,
          show ofString "n" ≠ ofString "key" by decide, show ofString "p" ≠ ofString "key" by decide,
          show ofString "nodes" ≠ ofString "key" by decide]
      have hval_ulp : u_lp.locals.lookup (ofString "value") = some (.val (.word valw)) := by
        rw [hu_keep (ofString "value") (by decide) (by decide)]
        simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval_sd,
          show ofString "n" ≠ ofString "value" by decide, show ofString "p" ≠ ofString "value" by decide,
          show ofString "nodes" ≠ ofString "value" by decide]
      have hd_ulp : u_lp.locals.lookup (ofString "d") = some (.val (.word dw)) := by
        rw [hu_keep (ofString "d") (by decide) (by decide)]
        simp [s_lp, s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "d" by decide, show ofString "p" ≠ ofString "d" by decide,
          show ofString "nodes" ≠ ofString "d" by decide]
      -- 11. `decCall nl := htab_new_leaf(t, key, value)`
      have hmem_u : u_lp.memory = s0.memory := hu_fr.memory
      have hg_u : u_lp.globals = s0.globals := by unfold LocFrame at hu_fr; rw [hu_fr]
      have hA_ulp : ArenaReady u_lp := by
        unfold LocFrame at hu_fr; rw [hu_fr]; exact (arenaReady_locals s0 _ _).mpr hA0
      have hNS_ulp : NodeState u_lp t (L0 ++ I0) Fr0 := by
        have hNS0 : NodeState s0 t (L0 ++ I0) Fr0 := ⟨hB0, hT0.2.1, hT0.2.2.1, hT0.2.2.2.2.2.2.2.2.2.2.2⟩
        unfold LocFrame at hu_fr; rw [hu_fr]; exact hNS0
      have hcnt_le_ulp : hdr u_lp t 3 ≤ (L0 ++ I0).length := by
        have hh3_u : hdr u_lp t 3 = hdr s0 t 3 := by unfold hdr memW; rw [hmem_u]
        have hlen := hT0.1
        rw [hh3_u, List.length_append]; omega
      have hal_ulp : ∀ i ∈ htabFootprint u_lp t, Allocated u_lp i := by
        unfold LocFrame at hu_fr; rw [hu_fr]; exact hal0
      refine Ret.decCall_new_leaf_lf hLF tw keyw valw (L0 ++ I0) Fr0
        (by simp [evalAt, evalHOLExact]; exact ht_ulp)
        (by simp [evalAt, evalHOLExact]; exact hkey_ulp)
        (by simp [evalAt, evalHOLExact]; exact hval_ulp)
        hA_ulp hNS_ulp hcnt_le_ulp hal_ulp ?_
      intro nlw Fr1 s1 hA1 hNS1 hh0_1 hh1_1 hh3_1 hh7_1 _ _ n16_1 n24_1 ordc_1 hnd_1 hord_1 hhp_1 hfp_1 hfr_1 hg_1 hloc_1
      let s1_nl := setVarHOLFinite (ofString "nl") (.val (.word nlw)) s1
      have hA1_nl : ArenaReady s1_nl := (arenaReady_locals s1 _ s1.clock).mpr hA1
      have hNS1_nl : NodeState s1_nl t ((L0 ++ I0) ++ [nlw.toNat]) Fr1 := hNS1
      have hal1_nl : ∀ i ∈ htabFootprint s1_nl t, Allocated s1_nl i := fun i hi => (hfp_1 i hi).1
      have ht_s1nl : (setVarHOLFinite (ofString "nl") (.val (.word nlw)) s1).locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht_ulp,
          show ofString "nl" ≠ ofString "t" by decide]
      have hd_s1nl : (setVarHOLFinite (ofString "nl") (.val (.word nlw)) s1).locals.lookup (ofString "d") = some (.val (.word dw)) := by
        simp [setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, hd_ulp,
          show ofString "nl" ≠ ofString "d" by decide]
      -- 12. `decCall ni := htab_new_internal(t, d)`
      refine Ret.decCall_new_internal_lf hLF tw dw ((L0 ++ I0) ++ [nlw.toNat]) Fr1
        (by simp [evalAt, evalHOLExact]; exact ht_s1nl)
        (by simp [evalAt, evalHOLExact]; exact hd_s1nl)
        hA1_nl hNS1_nl hal1_nl ?_
      intro niw Fr2 s2 hA2 hNS2 hh0_2 hh1_2 hh3_2 hh7_2 _ _ _ _ ni24_2 hnd_2 hord_2 hhp_2 hfp_2 hfr_2 hg_2 hloc_2
      -- Normalize `setVarHOLFinite "ni" niw s2` into `NS s2 L_cur s2.globals s2.memory s2.clock`!
      let L_cur := (u_lp.locals.update (ofString "nl", .val (.word nlw))).update (ofString "ni", .val (.word niw))
      have hs2_ni_eq : setVarHOLFinite (ofString "ni") (.val (.word niw)) s2 =
          NS s2 L_cur s2.globals s2.memory s2.clock := by
        simp [setVarHOLFinite, NS, hloc_2, hloc_1, L_cur]
      rw [hs2_ni_eq]
      -- Assemble all hypotheses of `htab_set_splice_exec`!
      have hh_u : ∀ k, hdr u_lp t k = hdr s0 t k := fun k => by unfold hdr memW; rw [hmem_u]
      have hfp_u : htabFootprint u_lp t = htabFootprint s0 t := by simp [htabFootprint, hdr, memW, hmem_u]
      have hgn_u : globN u_lp "heap_ptr" = globN s0 "heap_ptr" := by unfold globN; rw [hg_u]
      have hh0_20 : hdr s2 t 0 = hdr s0 t 0 := hh0_2.trans (hh0_1.trans (hh_u 0))
      have hh1_20 : hdr s2 t 1 = hdr s0 t 1 := hh1_2.trans (hh1_1.trans (hh_u 1))
      have hh3_20 : hdr s2 t 3 = hdr s0 t 3 + 1 := hh3_2.trans (hh3_1.trans (by rw [hh_u 3]))
      have hh7_20 : hdr s2 t 7 = hdr s0 t 7 := hh7_2.trans (hh7_1.trans (hh_u 7))
      have hnl_mem_A1 : nlw.toNat ∈ (L0 ++ I0) ++ [nlw.toNat] := List.mem_append_right _ (by simp)
      have hnl16_20 : nodeF s2 (hdr s2 t 5) nlw.toNat 16 = hdr s0 t 3 :=
        (hnd_2 nlw.toNat hnl_mem_A1 16 (Or.inr (Or.inr (Or.inl rfl)))).trans (n16_1.trans (hh_u 3))
      have hnl24_20 : nodeF s2 (hdr s2 t 5) nlw.toNat 24 = 8 * hdr s0 t 0 :=
        (hnd_2 nlw.toNat hnl_mem_A1 24 (Or.inr (Or.inr (Or.inr rfl)))).trans (n24_1.trans (by rw [hh_u 0]))
      have hcnt_lt_nc1 : hdr s0 t 3 < hdr s1 tw.toNat 10 + 1 := by
        have hB1 : HtabBlocks s1 tw.toNat := hNS1.1
        have hnx1_le : hdr s1 tw.toNat 8 ≤ hdr s1 tw.toNat 10 + 1 := hB1.2.2.2.2.2.2.2
        have hnd1 := (List.nodup_append.mp hNS1.2.1).1
        have hr1 : ∀ x ∈ (L0 ++ I0) ++ [nlw.toNat], 1 ≤ x ∧ x < hdr s1 tw.toNat 8 := fun x hx =>
          (hNS1.2.2.1 x).mp (List.mem_append_left _ hx)
        have hlen_le := nodup_len_le_range hnd1 hr1
        have hL0_len : L0.length = hdr s0 t 3 := hT0.1
        have hnl_rng := hr1 nlw.toNat (List.mem_append_right _ (by simp))
        have hnx1_ge1 : 1 ≤ hdr s1 tw.toNat 8 := by omega
        simp only [List.length_append, List.length_singleton] at hlen_le
        omega
      have hord_cnt_20 : memW s2 (hdr s2 t 6 + 8 * hdr s0 t 3) = nlw.toNat := by
        have h1 := hord_2 (hdr s0 t 3) hcnt_lt_nc1
        have h2 : memW s1 (hdr s1 t 6 + 8 * hdr s0 t 3) = nlw.toNat := by
          rw [← hh_u 3]; exact ordc_1
        exact h1.trans h2
      have hord_old_20 : ∀ i, i < hdr s0 t 3 →
          memW s2 (hdr s2 t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
        intro i hi
        have h1 := hord_2 i (lt_trans hi hcnt_lt_nc1)
        have h2 : memW s1 (hdr s1 t 6 + 8 * i) = memW u_lp (hdr u_lp t 6 + 8 * i) :=
          hord_1 i (by rw [hh_u 3]; exact hi)
        have h3 : memW u_lp (hdr u_lp t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
          rw [hh_u 6]; unfold memW; rw [hmem_u]
        exact (h1.trans h2).trans h3
      have hnd_old_20 : ∀ z ∈ L0 ++ I0, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
          nodeF s2 (hdr s2 t 5) z off = nodeF s0 (hdr s0 t 5) z off := by
        intro z hz off hoff
        have h1 := hnd_2 z (List.mem_append_left _ hz) off hoff
        have h2 : nodeF s1 (hdr s1 t 5) z off = nodeF u_lp (hdr u_lp t 5) z off :=
          hnd_1 z hz off hoff
        have h3 : nodeF u_lp (hdr u_lp t 5) z off = nodeF s0 (hdr s0 t 5) z off := by
          rw [hh_u 5]; unfold nodeF memW; rw [hmem_u]
        exact (h1.trans h2).trans h3
      have hhp_01 : globN s0 "heap_ptr" ≤ globN s1 "heap_ptr" := by rw [← hgn_u]; exact hhp_1
      have hhp_12 : globN s1 "heap_ptr" ≤ globN s2 "heap_ptr" := hhp_2
      have hhp_20 : globN s0 "heap_ptr" ≤ globN s2 "heap_ptr" := le_trans hhp_01 hhp_12
      have hfp_10 : ∀ i ∈ htabFootprint s1 t, Allocated s1 i ∧
          ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨
            Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s1 "heap_ptr" - globN s0 "heap_ptr"))) := by
        intro i hi
        obtain ⟨hal, hprov⟩ := hfp_1 i hi
        rw [hfp_u, hgn_u] at hprov
        exact ⟨hal, hprov⟩
      have hfp_20 : ∀ i ∈ htabFootprint s2 t, Allocated s2 i ∧
          ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨
            Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s2 "heap_ptr" - globN s0 "heap_ptr"))) := by
        intro i hi
        obtain ⟨hal2, hprov2⟩ := hfp_2 i hi
        refine ⟨hal2, ?_⟩
        rcases hprov2 with ⟨j, hj, hij⟩ | hfr2
        · rcases (hfp_10 j hj).2 with ⟨k, hk, hjk⟩ | hjf
          · exact Or.inl ⟨k, hk, ⟨le_trans hjk.1 hij.1, le_trans hij.2 hjk.2⟩⟩
          · exact Or.inr ⟨le_trans hjf.1 hij.1, by have := hij.2; have := hjf.2; omega⟩
        · change Inside i (globN s1 "heap_ptr") (globN s1 "heap_ptr" + (globN s2 "heap_ptr" - globN s1 "heap_ptr")) at hfr2
          exact Or.inr ⟨by have := hfr2.1; omega, by have := hfr2.2; omega⟩
      have hfr_10 : FrameOutside s0 s1 (htabFootprint s0 t)
          (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
        intro x hxk hxf
        rw [hfr_1 x (by rw [hfp_u]; exact hxk) (by rw [hgn_u]; exact hxf), hmem_u]
      have hfr_10_wide : FrameOutside s0 s1 (htabFootprint s0 t)
          (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") :=
        frameOutside_mono hfr_10 (fun i hi => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) ⟨le_rfl, by dsimp; omega⟩
      have hfr_12_wide : FrameOutside s1 s2 (htabFootprint s0 t)
          (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") :=
        frameOutside_mono (a := s1) (b := s2) hfr_2
          (fun i hi => (hfp_10 i hi).2.elim Or.inl (fun h => Or.inr ⟨h.1, le_trans h.2 (by dsimp; omega)⟩))
          ⟨hhp_01, by change globN s1 "heap_ptr" + (globN s2 "heap_ptr" - globN s1 "heap_ptr") ≤ globN s0 "heap_ptr" + (globN s2 "heap_ptr" - globN s0 "heap_ptr"); omega⟩
      have hfr_20 : FrameOutside s0 s2 (htabFootprint s0 t)
          (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") :=
        fun x hxk hxf => (hfr_12_wide x hxk hxf).trans (hfr_10_wide x hxk hxf)
      have hg_20 : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
          s0.globals.lookup k = s2.globals.lookup k := by
        intro k hk
        rw [← hg_u, hg_1 k hk]
        exact hg_2 k hk
      exact htab_set_splice_exec s0 s2 tw dw pw nw nlw niw L0 I0 Fr0 Fr2 L_cur
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, ht_ulp,
          show ofString "ni" ≠ ofString "t" by decide, show ofString "nl" ≠ ofString "t" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, hp_ulp,
          show ofString "ni" ≠ ofString "p" by decide, show ofString "nl" ≠ ofString "p" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, hn_ulp,
          show ofString "ni" ≠ ofString "n" by decide, show ofString "nl" ≠ ofString "n" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "ni" ≠ ofString "nl" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE])
        hA2 hNS2 hT0 hcnt_pos hd_lt hnw_LI hpw_spec0
        hh0_20 hh1_20 hh3_20 hh7_20 hnl16_20 hnl24_20 ni24_2
        hord_cnt_20 hord_old_20 hnd_old_20 hhp_20 hfp_20 hfr_20 hg_20

theorem htab_set_spec_proof :
    ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
      originalRuntimeCode.lookup (ofString "htab_set") = some (params, body, retShape) ∧
      ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → HtabArgWF s →
        (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set") values =
          some (body, s.locals, retShape)) →
        (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
        ∀ v, (evaluateHOLFiniteState s body).1 = some (.returned v) →
          HtabExit s (evaluateHOLFiniteState s body).2 := by
  refine ⟨[(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
    sourceFnBody Guest.Software.guestFn_htab_set, .one, lookup_htab_set, ?_⟩
  intro F s _ hP ⟨values, hl⟩ _ v hv
  obtain ⟨tw, keyw, valw, ht, hkey, hval⟩ :=
    three_word_params_of_lookupCode s (ofString "htab_set")
      (ofString "t") (ofString "key") (ofString "value")
      (by decide) (by decide) (by decide) _ _ lookup_htab_set values hl
  have hloc_t : locN s "t" = tw.toNat := by simp [locN, ht]
  obtain ⟨hA0, hW0, hal0⟩ := hP
  rw [hloc_t] at hW0 hal0
  rw [htabExit_iff_at, hloc_t]
  exact htab_set_body_spec s tw keyw valw ht hkey hval hA0 hW0 hal0 v hv

end InitECandidate.Solver.Wave8GuestInv.R13SoloHtabSet

