import InitECandidate.Solver.Wave8GuestInv.EntryDefs
import InitECandidate.Solver.HeapPotential
import InitECandidate.Solver.PanRunBoundedExt
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.AddSub

/-! Self-contained proof of `htab_set_spec` for R10 (`ContractParts/C00.lean`). -/

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

namespace InitECandidate.Solver.Wave8GuestInv.SoloHtabSet

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

end InitECandidate.Solver.Wave8GuestInv.SoloHtabSet
