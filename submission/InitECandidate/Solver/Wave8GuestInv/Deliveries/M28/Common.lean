import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.GuestTrapAlign
import InitECandidate.Solver.HeapPotential
import Guest.SoftwareAst

/-! Shared definitions and allocator/memory helpers for contract micro-shard `m28`
(`wave8/contracts-m28`), checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.MemoryViews` plus
cone modules (`GuestTrapAlign`, `HeapPotential`, `Guest.SoftwareAst`).
Restates `FunSpec`, `Resumes`, `WritesWithin`, `FreshBlock`, `FreshScratch`, `PushesFrame`, and
`ResolvesNode` verbatim from `campaign/specs-proposed/GuestInv.lean` @ `8a79d9f28` so every theorem
is definitionally (`rfl`) equal to its spec statement in `Axioms.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8Contracts.M28

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
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

def WritesWithin (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => Resumes r →
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    FrameOutside s post
      (R s ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
    ∀ k : MlS, k ∉ gw.map ofString → s.globals.lookup k = post.globals.lookup k)
    fname

def FreshBlock {F : Type} (s post : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  p % 8 = 0 ∧ Inside (p, (n + 7) / 8 * 8) (globN s "heap_ptr") (globN post "heap_ptr") ∧
    WordsOK post (p, (n + 7) / 8 * 8)

def FreshScratch {F : Type} (s post : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  p % 8 = 0 ∧ globN s "frame_mem_ptr" ≤ p ∧
    Inside (p, (n + 7) / 8 * 8) (globN post "scratch_ptr") (globN s "scratch_ptr") ∧
    WordsOK post (p, (n + 7) / 8 * 8)

def PushesFrame (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) → ∃ a b : BitVec 64,
    v = .rStruct [.val (.word a), .val (.word b)] ∧
    (a.toNat = 0 → b.toNat = 0 ∨ FreshBlock s post b.toNat 32) ∧ (a.toNat ≠ 0 →
      FreshScratch s post b.toNat 88 ∧ (memW post (b.toNat + 8) = 1 ∨
        (memW post (b.toNat + 8) = 2 ∧ memW post (b.toNat + 32) = 0 ∧
          memW post (b.toNat + 40) = 0 ∧
          FreshBlock s post (memW post (b.toNat + 16)) 176)))) fname

def ResolvesNode (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) → ∃ a b c d : BitVec 64,
    v = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] ∧
    (a.toNat = 0 → b.toNat = 0 ∨ FreshBlock s post b.toNat 32)) fname

/-! ## 2. Ordinary domain, `WordsOK`, and `ArenaOK` helpers -/

theorem addresses_iff (b : BitVec 64) (n : Nat) (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      ∃ i, i < n ∧ x = b + BitVec.ofNat 64 (8 * i) := by
  induction n generalizing b with
  | zero => simp [Flapjack.Compiler.Backend.StackRemove.addresses]
  | succ n ih =>
    simp only [Flapjack.Compiler.Backend.StackRemove.addresses,
      Flapjack.Compiler.Backend.StackRemove.bytesInWord]
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
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  have hb : (BitVec.ofNat 64 2701131776).toNat = 2701131776 := rfl
  have hsb : sourceBase = 2701131776 := by decide
  have hhe : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  rw [ordinaryDomain_eq, addresses_iff_nat _ _ (by rw [hb]; norm_num), hb, hsb, hhe]
  omega

theorem ordinaryDomain_of_nat (a : Nat) (hlo : sourceBase ≤ a) (hhi : a < heapEnd)
    (hal : a % 8 = 0) : ordinaryDomain (BitVec.ofNat 64 a) := by
  have hlt : a < 2 ^ 64 := by
    have : heapEnd < 2 ^ 64 := by decide
    omega
  have hbv : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [ordinaryDomain_iff, hbv]
  exact ⟨hal, hlo, hhi⟩

theorem wordsOK_of_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (p len : Nat) (hp : p % 8 = 0) (hlen : len % 8 = 0)
    (hlo : sourceBase ≤ p) (hhi : p + len ≤ heapEnd) :
    WordsOK s (p, len) := by
  refine ⟨hp, hlen, ?_⟩
  intro k hk
  rcases hmem : s.memory (BitVec.ofNat 64 (p + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hmem⟩
  rw [hG.memaddrs]
  exact ordinaryDomain_of_nat (p + 8 * k) (by omega) (by omega) (by omega)

theorem globWord_of_pos {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String)
    (hpos : 0 < globN s name) :
    ∃ w : BitVec 64, s.globals.lookup (ofString name) = some (.val (.word w)) ∧
      w.toNat = globN s name := by
  unfold globN at hpos ⊢
  rcases hg : s.globals.lookup (ofString name) with _ | v
  · simp [hg] at hpos
  · rcases v with ⟨⟨w⟩⟩ | _ | _
    · exact ⟨w, rfl, by simp [hg]⟩
    · simp [hg] at hpos
    · simp [hg] at hpos

theorem arenaOK_globals {F : Type} (s : PanSemStateFiniteExact 64 F) (hA : ArenaOK s) :
    ∃ hp fp sp : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) ∧
      hp.toNat = globN s "heap_ptr" ∧
      s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)) ∧
      fp.toNat = globN s "frame_mem_ptr" ∧
      s.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) ∧
      sp.toNat = globN s "scratch_ptr" := by
  have hsb : 0 < sourceBase := by decide
  have hss : 0 < scratchStart := by decide
  obtain ⟨hp, hhp, hhp_eq⟩ := globWord_of_pos s "heap_ptr" (by have := hA.1; omega)
  obtain ⟨fp, hfp, hfp_eq⟩ := globWord_of_pos s "frame_mem_ptr" (by have := hA.2.2.1; omega)
  obtain ⟨sp, hsp, hsp_eq⟩ := globWord_of_pos s "scratch_ptr"
    (by have := hA.2.2.1; have := hA.2.2.2.1; omega)
  exact ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩

/-! ## 3. Function lookups in `originalRuntimeCode` -/

theorem lookup__resolve_step :
    originalRuntimeCode.lookup (ofString "_resolve_step") =
      some ([(ofString "db", .one), (ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn__resolve_step,
        .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 260 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__resolve_step) rfl

theorem lookup__decode_step :
    originalRuntimeCode.lookup (ofString "_decode_step") =
      some ([(ofString "db", .one), (ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn__decode_step,
        .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 261 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__decode_step) rfl

theorem lookup_mpt_nibble_key :
    originalRuntimeCode.lookup (ofString "mpt_nibble_key") =
      some ([(ofString "m", .one), (ofString "key", .one), (ofString "klen", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_nibble_key,
        .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 270 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_nibble_key) rfl

theorem lookup_scratch_alloc :
    originalRuntimeCode.lookup (ofString "scratch_alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_scratch_alloc, .one) :=
  lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_alloc) rfl

theorem lookup_node_new_hashed :
    originalRuntimeCode.lookup (ofString "node_new_hashed") =
      some ([(ofString "hash", .one)], sourceFnBody Guest.Software.guestFn_node_new_hashed, .one) :=
  lookup_of_guestAst_getElem 255 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_hashed) rfl

theorem lookup_node_new_leaf :
    originalRuntimeCode.lookup (ofString "node_new_leaf") =
      some ([(ofString "nib", .one), (ofString "nlen", .one),
             (ofString "vptr", .one), (ofString "vlen", .one)],
        sourceFnBody Guest.Software.guestFn_node_new_leaf, .one) :=
  lookup_of_guestAst_getElem 256 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_leaf) rfl

theorem lookup_node_new_branch :
    originalRuntimeCode.lookup (ofString "node_new_branch") =
      some ([], sourceFnBody Guest.Software.guestFn_node_new_branch, .one) :=
  lookup_of_guestAst_getElem 258 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_branch) rfl

theorem lookup_mpt_fail :
    originalRuntimeCode.lookup (ofString "mpt_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
  lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_fail) rfl

end InitECandidate.Solver.Wave8Contracts.M28
