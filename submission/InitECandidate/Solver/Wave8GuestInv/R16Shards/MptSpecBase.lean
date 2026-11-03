import InitECandidate.Solver.Wave8GuestInv.ContractParts.C00Defs
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_memeq
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.nf_node_invalidate
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.Common
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_common_prefix_length
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M28.ww_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.zv_memzero

/-! Cycle-free MPT base definitions and `NodeFn` / `NodeStep` infrastructure for `R16Shards`
(imported by `ContractParts/C00.lean`, so must NOT import `ContractParts/C00..C07`). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

def ReadOnlyFn (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r post => Resumes r → post = { s with locals := post.locals, clock := post.clock })
    fname

def NodeKind {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (x : String) (k : Nat) : Prop :=
  locN s x ∈ Nd ∧ memW s (locN s x) = k

def NodeArgs (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ (∀ n ∈ names, RootIn Nd (locN s n)) ∧ req s Nd

def NodeFnExit (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => Resumes r → ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    ∀ Nd, NodeHeap s Nd → (∀ n ∈ names, RootIn Nd (locN s n)) → req s Nd →
      ∃ Nd', NodeHeap post Nd' ∧ (∀ n ∈ Nd, n ∈ Nd') ∧
        (∀ n ∈ Nd, memW post n = memW s n) ∧
        (∀ n ∈ Nd', n ∈ Nd ∨ Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr")) ∧
        FrameOutside s post
          ((Nd.map fun n => nodeIvl s n) ++
            [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
          (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
        (∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString →
          s.globals.lookup k = post.globals.lookup k) ∧
        ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat

def NodeFn (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec (NodeArgs names req) (NodeFnExit names req) fname

def RetLe (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat) (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r _ => ∀ v, r = some (.returned v) →
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ B s) fname

theorem arenaReady_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ArenaReady { s with locals := locals, clock := k } ↔ ArenaReady s :=
  ⟨fun h => ⟨guestInv_congr (s := { s with locals := locals, clock := k }) rfl rfl rfl rfl h.1, h.2⟩,
   fun h => ⟨guestInv_with_locals_clock s locals k h.1, h.2⟩⟩

theorem localsFree_arenaReady : LocalsFree ArenaReady :=
  fun s locals k h => (arenaReady_with_locals s locals k).2 h

theorem locN_congr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (n : String)
    (h : locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    locN { s with locals := locals, clock := k } n = locN s n := by
  simp only [locN, h]

theorem resVarEq_lookup_ne (m : HolFiniteMapExact MlS (ValueHOL 64)) (name n : MlS)
    (o : Option (ValueHOL 64)) (h : n ≠ name) :
    (HolFiniteMapExact.resVarEq m (name, o)).lookup n = m.lookup n := by
  rcases o with _ | v
  · simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, h]
  · simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq, FUPDATE_HOL]
    split
    · rename_i heq; exact absurd heq h
    · rfl

theorem FunSpec.at_lookup {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS}
    (hf : FunSpec Pc Qc fname) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (hcode : state.code = originalRuntimeCode) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret'))
    (hPc : Pc (callEntryStateHOLFinite state callee))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1 ≠
      some .timeOut) :
    Qc (callEntryStateHOLFinite state callee)
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').2 := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  have hret := lookupCodeHOLFinite_installed_return state fname params body' body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hret
  exact hspec _ hcode hPc ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩ hnt

theorem nf_node_invalidate :
    NodeFn ["nd"] (fun _ _ => True) (ofString "node_invalidate") :=
  Wave8Contracts.M25.nf_node_invalidate

/-! ## 1. Function lookup lemmas -/

theorem lookup_node_new_leaf :
    originalRuntimeCode.lookup (ofString "node_new_leaf") =
      some ([(ofString "nib", .one), (ofString "nlen", .one),
             (ofString "vptr", .one), (ofString "vlen", .one)],
        sourceFnBody Guest.Software.guestFn_node_new_leaf, .one) :=
  lookup_of_guestAst_getElem 256 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_leaf) rfl

theorem lookup_node_new_ext :
    originalRuntimeCode.lookup (ofString "node_new_ext") =
      some ([(ofString "nib", .one), (ofString "nlen", .one),
             (ofString "child", .one)],
        sourceFnBody Guest.Software.guestFn_node_new_ext, .one) :=
  lookup_of_guestAst_getElem 257 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_ext) rfl

theorem lookup_node_new_branch :
    originalRuntimeCode.lookup (ofString "node_new_branch") =
      some ([], sourceFnBody Guest.Software.guestFn_node_new_branch, .one) :=
  lookup_of_guestAst_getElem 258 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_branch) rfl

theorem lookup__create_branch_from_two_leaves :
    originalRuntimeCode.lookup (ofString "_create_branch_from_two_leaves") =
      some ([(ofString "k1", .one), (ofString "l1", .one),
             (ofString "v1", .one), (ofString "vl1", .one),
             (ofString "k2", .one), (ofString "l2", .one),
             (ofString "v2", .one), (ofString "vl2", .one)],
        sourceFnBody Guest.Software.guestFn__create_branch_from_two_leaves, .one) :=
  lookup_of_guestAst_getElem 272 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__create_branch_from_two_leaves) rfl

theorem lookup__insert_into_leaf :
    originalRuntimeCode.lookup (ofString "_insert_into_leaf") =
      some ([(ofString "node", .one), (ofString "rk", .one),
             (ofString "rl", .one), (ofString "vptr", .one),
             (ofString "vlen", .one)],
        sourceFnBody Guest.Software.guestFn__insert_into_leaf, .one) :=
  lookup_of_guestAst_getElem 273 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__insert_into_leaf) rfl

theorem lookup__split_extension :
    originalRuntimeCode.lookup (ofString "_split_extension") =
      some ([(ofString "node", .one), (ofString "rk", .one),
             (ofString "rl", .one), (ofString "vptr", .one),
             (ofString "vlen", .one), (ofString "pl", .one)],
        sourceFnBody Guest.Software.guestFn__split_extension, .one) :=
  lookup_of_guestAst_getElem 274 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__split_extension) rfl

theorem lookup__collapse_branch :
    originalRuntimeCode.lookup (ofString "_collapse_branch") =
      some ([(ofString "node", .one)],
        sourceFnBody Guest.Software.guestFn__collapse_branch, .one) :=
  lookup_of_guestAst_getElem 276 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__collapse_branch) rfl

theorem lookup__delete_ext_finish :
    originalRuntimeCode.lookup (ofString "_delete_ext_finish") =
      some ([(ofString "node", .one), (ofString "seg", .one),
             (ofString "sl", .one), (ofString "nc", .one)],
        sourceFnBody Guest.Software.guestFn__delete_ext_finish, .one) :=
  lookup_of_guestAst_getElem 277 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__delete_ext_finish) rfl

theorem lookup_mpt_fail :
    originalRuntimeCode.lookup (ofString "mpt_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
  lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_fail) rfl

theorem lookup_nibbles_concat :
    originalRuntimeCode.lookup (ofString "nibbles_concat") =
      some ([(ofString "a", .one), (ofString "al", .one),
             (ofString "b", .one), (ofString "bl", .one)],
        sourceFnBody Guest.Software.guestFn_nibbles_concat, .one) :=
  lookup_of_guestAst_getElem 252 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_nibbles_concat) rfl

theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem lookup_memeq :
    originalRuntimeCode.lookup (ofString "memeq") =
      some ([(ofString "a", .one), (ofString "b", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memeq, .one) :=
  lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memeq) rfl

theorem lookup_common_prefix_length :
    originalRuntimeCode.lookup (ofString "common_prefix_length") =
      some ([(ofString "a", .one), (ofString "al", .one),
             (ofString "b", .one), (ofString "bl", .one)],
        sourceFnBody Guest.Software.guestFn_common_prefix_length, .one) :=
  lookup_of_guestAst_getElem 251 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_common_prefix_length) rfl

/-! ## 2. Basic `Resumes`, domain, alignment, and `NodeStep` combinators -/

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem not_resumes_none : ¬ Resumes (none : Option (PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem arenaOK_congr_globals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hg : t.globals = s.globals) (hA : ArenaOK s) : ArenaOK t :=
  arenaOK_congr hg hA

theorem arenaOK_update_heap {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {q : BitVec 64} (hg : t.globals = s.globals.update (ofString "heap_ptr", .val (.word q)))
    (hlo : sourceBase ≤ q.toNat) (hhi : q.toNat ≤ heapLimit) (hal : q.toNat % 8 = 0)
    (hA : ArenaOK s) : ArenaOK t := by
  have hhp : globN t "heap_ptr" = q.toNat := by
    unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hfp : globN t "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [hg]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hsp : globN t "scratch_ptr" = globN s "scratch_ptr" := by
    unfold globN; rw [hg]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have hgw : GlobalsWord t := globalsWord_update (ofString "heap_ptr") q hg hA.2.2.2.2.2.2.2.2
  unfold ArenaOK at hA ⊢
  rw [hhp, hfp, hsp]
  exact ⟨hlo, hhi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hal, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1, hgw⟩

theorem nodeSize_bounds (k : Nat) : 32 ≤ nodeSize k ∧ nodeSize k ≤ 176 ∧ nodeSize k % 8 = 0 := by
  unfold nodeSize
  split_ifs <;> decide

theorem byteCell_toNat {a : Nat} (ha : a < 2 ^ 64) :
    (panByteAlignHOL (BitVec.ofNat 64 a)).toNat = a / 8 * 8 := by
  have hal : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
  change (BitVec.ofNat 64 ((BitVec.ofNat 64 a).toNat / 2 ^ ((64 : Nat) / 8).log2 *
    2 ^ ((64 : Nat) / 8).log2)).toNat = a / 8 * 8
  rw [hal, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self a 8) ha)]

theorem keyIn_heap {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {p len : Nat} (ha : ArenaReady s) (hk : KeyIn s Nd p len) (hz : len ≠ 0) :
    sourceBase ≤ p ∧ p + len ≤ globN s "heap_ptr" ∧ p + len ≤ heapLimit := by
  obtain ⟨_, hal, hi, _⟩ := hk.resolve_left hz
  rcases hal with hal | hal
  · exact ⟨hal.1, hal.2, hi.2⟩
  · have hframe := ha.2.2.2.1
    have hscratch := ha.2.2.2.2.1
    have hheap := hi.2
    have hlo := hal.1
    have hsep : heapLimit ≤ scratchStart := by decide
    omega

theorem keyIn_zero {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (p : Nat) :
    KeyIn s Nd p 0 :=
  Or.inl rfl

theorem keyIn_subslice {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {p len off sublen : Nat} (hkey : KeyIn s Nd p len)
    (hsub : off + sublen ≤ len) :
    KeyIn s Nd ((BitVec.ofNat 64 p + BitVec.ofNat 64 off).toNat) sublen := by
  by_cases hz : sublen = 0
  · subst hz; exact Or.inl rfl
  · have hlen_nz : len ≠ 0 := by omega
    obtain ⟨hnib, halloc, hins, hdisj⟩ := hkey.resolve_left hlen_nz
    have hhl : heapLimit < 2 ^ 64 := by decide
    have hp_lt : p + len < 2 ^ 64 := by dsimp [Inside] at hins; omega
    have hpo : (BitVec.ofNat 64 p + BitVec.ofNat 64 off).toNat = p + off := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [hpo]
    right
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      have hk_eq : p + off + k = p + (off + k) := by omega
      rw [hk_eq]
      exact hnib (off + k) (by omega)
    · rcases halloc with h1 | h2
      · exact Or.inl ⟨by dsimp [Inside] at h1; omega, by dsimp [Inside] at h1; omega⟩
      · exact Or.inr ⟨by dsimp [Inside] at h2; omega, by dsimp [Inside] at h2; omega⟩
    · exact ⟨by dsimp [Inside] at hins; omega, by dsimp [Inside] at hins; omega⟩
    · intro n hn
      rcases hdisj n hn with h0 | h0 | h1 | h2
      · omega
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Relational step between MPT node-heap states `s` and `post` for a fixed `Nd` -> `Nd'`. -/
structure NodeStep {F : Type} (s post : PanSemStateFiniteExact 64 F) (Nd Nd' : List Nat) : Prop where
  arena   : ArenaReady post
  hp_le   : globN s "heap_ptr" ≤ globN post "heap_ptr"
  sp_le   : globN post "scratch_ptr" ≤ globN s "scratch_ptr"
  be_eq   : post.be = s.be
  heap    : NodeHeap post Nd'
  sub     : ∀ n ∈ Nd, n ∈ Nd'
  kinds   : ∀ n ∈ Nd, memW post n = memW s n
  fresh   : ∀ n ∈ Nd', n ∈ Nd ∨ Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr")
  frame   : FrameOutside s post
              ((Nd.map fun n => nodeIvl s n) ++
                [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
              (globN s "heap_ptr", heapLimit - globN s "heap_ptr")
  globals : ∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString →
              s.globals.lookup k = post.globals.lookup k

theorem NodeStep.refl {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s) (hn : NodeHeap s Nd) : NodeStep s s Nd Nd where
  arena := ha
  hp_le := le_rfl
  sp_le := le_rfl
  be_eq := rfl
  heap := hn
  sub := fun _ h => h
  kinds := fun _ _ => rfl
  fresh := fun _ h => Or.inl h
  frame := fun _ _ _ => rfl
  globals := fun _ _ => rfl

theorem NodeStep.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} (h : NodeStep s post Nd Nd')
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (C : Nat) :
    NodeStep s { post with locals := L, clock := C } Nd Nd' where
  arena := localsFree_arenaReady post L C h.arena
  hp_le := h.hp_le
  sp_le := h.sp_le
  be_eq := h.be_eq
  heap := h.heap
  sub := h.sub
  kinds := h.kinds
  fresh := h.fresh
  frame := h.frame
  globals := h.globals

theorem NodeStep.from_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {C : Nat}
    (h : NodeStep { s with locals := L, clock := C } post Nd Nd') :
    NodeStep s post Nd Nd' where
  arena := h.arena
  hp_le := h.hp_le
  sp_le := h.sp_le
  be_eq := h.be_eq
  heap := h.heap
  sub := h.sub
  kinds := h.kinds
  fresh := h.fresh
  frame := h.frame
  globals := h.globals

theorem NodeStep.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    {Nd1 Nd2 Nd3 : List Nat} (ha : ArenaReady a)
    (h1 : NodeStep a b Nd1 Nd2) (h2 : NodeStep b c Nd2 Nd3) :
    NodeStep a c Nd1 Nd3 where
  arena := h2.arena
  hp_le := Nat.le_trans h1.hp_le h2.hp_le
  sp_le := Nat.le_trans h2.sp_le h1.sp_le
  be_eq := h2.be_eq.trans h1.be_eq
  heap := h2.heap
  sub := fun n hn => h2.sub n (h1.sub n hn)
  kinds := fun n hn => (h2.kinds n (h1.sub n hn)).trans (h1.kinds n hn)
  fresh := by
    intro n hn3
    rcases h2.fresh n hn3 with hn2 | hfr2
    · rcases h1.fresh n hn2 with hn1 | hfr1
      · exact Or.inl hn1
      · right
        rw [nodeIvl, h2.kinds n hn2]
        exact ⟨hfr1.1, Nat.le_trans hfr1.2 h2.hp_le⟩
    · exact Or.inr ⟨Nat.le_trans h1.hp_le hfr2.1, hfr2.2⟩
  frame := by
    intro x hkeep hfresh
    have hfp_eq : globN b "frame_mem_ptr" = globN a "frame_mem_ptr" := by
      have hg := h1.globals (ofString "frame_mem_ptr") (by decide)
      unfold globN; rw [← hg]
    have hkeep2 : ∀ i ∈ (Nd2.map fun n => nodeIvl b n) ++
        [(globN b "frame_mem_ptr", globN b "scratch_ptr" - globN b "frame_mem_ptr")],
        ¬ CellHits x.toNat i := by
      intro i hi hhit
      rcases List.mem_append.mp hi with hi_nd | hi_gap
      · obtain ⟨n, hn2, rfl⟩ := List.mem_map.mp hi_nd
        rcases h1.fresh n hn2 with hn1 | hfr1
        · rw [nodeIvl, h1.kinds n hn1] at hhit
          exact hkeep (nodeIvl a n)
            (List.mem_append_left _ (List.mem_map.mpr ⟨n, hn1, rfl⟩)) hhit
        · apply hfresh
          have hb_hp_lim : globN b "heap_ptr" ≤ heapLimit := h1.arena.2.2.1
          dsimp [CellHits] at hhit ⊢
          dsimp [Inside] at hfr1
          omega
      · rw [List.mem_singleton.mp hi_gap, hfp_eq] at hhit
        apply hkeep (globN a "frame_mem_ptr", globN a "scratch_ptr" - globN a "frame_mem_ptr")
          (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        have hsp_le := h1.sp_le
        dsimp [CellHits] at hhit ⊢
        omega
    have hfresh2 : ¬ CellHits x.toNat (globN b "heap_ptr", heapLimit - globN b "heap_ptr") := by
      intro hhit
      apply hfresh
      have := h1.hp_le
      have hb_hp_lim : globN b "heap_ptr" ≤ heapLimit := h1.arena.2.2.1
      dsimp [CellHits] at hhit ⊢
      omega
    exact (h2.frame x hkeep2 hfresh2).trans (h1.frame x hkeep hfresh)
  globals := fun k hk => (h1.globals k hk).trans (h2.globals k hk)

theorem NodeStep.keyIn {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} {p len : Nat}
    (ha : ArenaReady s) (hn : NodeHeap s Nd)
    (hst : NodeStep s post Nd Nd') (hk : KeyIn s Nd p len) :
    KeyIn post Nd' p len := by
  by_cases hz : len = 0
  · exact Or.inl hz
  obtain ⟨hplo, hheap, hphi⟩ := keyIn_heap ha hk hz
  obtain ⟨hnib, _, hi, hd⟩ := hk.resolve_left hz
  have hp_grow := hst.hp_le
  right
  refine ⟨?_, Or.inl ⟨hi.1, by omega⟩, hi, ?_⟩
  · intro k hkl
    have ha64 : p + k < 2 ^ 64 := by
      have : heapLimit < 2 ^ 64 := by decide
      omega
    let c := panByteAlignHOL (BitVec.ofNat 64 (p + k))
    have hc : c.toNat = (p + k) / 8 * 8 := byteCell_toNat ha64
    have hptr8 := ha.2.2.2.2.2.2.1
    have hfr8 := ha.2.2.2.2.2.2.2.1
    have hfrlo := ha.2.2.2.1
    have hheaphi := ha.2.2.1
    have hsep : heapLimit ≤ scratchStart := by decide
    have hmem : post.memory c = s.memory c := by
      apply hst.frame c
      · intro i him hcHit
        rcases List.mem_append.1 him with him | him
        · obtain ⟨n, hnm, rfl⟩ := List.mem_map.1 him
          have hn8 := (hn.1 n hnm).2.2.2.1.1
          obtain ⟨hsz32, _, hsz8⟩ := nodeSize_bounds (memW s n)
          have hdisj := hd n hnm
          rcases hdisj with h0 | h0 | h1 | h2
          · omega
          · dsimp [nodeIvl] at h0; omega
          · dsimp [nodeIvl, CellHits] at hn8 hcHit h1
            rw [hc] at hcHit; omega
          · dsimp [nodeIvl, CellHits] at hn8 hcHit h2
            rw [hc] at hcHit; omega
        · rw [List.mem_singleton.mp him] at hcHit
          dsimp [CellHits] at hcHit
          rw [hc] at hcHit
          omega
      · intro hcHit
        dsimp [CellHits] at hcHit
        rw [hc] at hcHit
        omega
    have hb : memB post (p + k) = memB s (p + k) := by
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL _ v post.be).toNat) =
        (match s.memory c with | .word v => (panGetByteHOL _ v s.be).toNat)
      rw [hmem, hst.be_eq]
    rw [hb]
    exact hnib k hkl
  · intro n hnm
    rcases hst.fresh n hnm with hold | hnew
    · simpa only [nodeIvl, hst.kinds n hold] using hd n hold
    · exact Or.inr (Or.inr (Or.inl (by have := hnew.1; omega)))

theorem NodeStep.rootIn {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} {x : Nat} (hst : NodeStep s post Nd Nd') (hr : RootIn Nd x) :
    RootIn Nd' x := by
  rcases hr with rfl | hm
  · exact Or.inl rfl
  · exact Or.inr (hst.sub x hm)

/-! ## 3. Exception / `Resumes` helpers (`alloc`, `mpt_fail`, `store`, `storeByte`, `decCall`) -/

theorem store_res_not_resumes {F : Type} {s : PanSemStateFiniteExact 64 F}
    {d e : ExpHOL 64} {r : PanSemResultExact 64} {t : PanSemStateFiniteExact 64 F}
    (h : evaluateHOLFiniteState s (.store d e) = (some r, t)) :
    ¬ Resumes (some r) := by
  have h1 := congrArg Prod.fst h
  rw [evaluateHOLFiniteState_store] at h1
  revert h1
  split
  · split
    · split <;> intro h1 <;> simp at h1
      subst h1; exact not_resumes_error
    · intro h1; simp at h1; subst h1; exact not_resumes_error
  · intro h1; simp at h1; subst h1; exact not_resumes_error

theorem storeByte_res_not_resumes {F : Type} {s : PanSemStateFiniteExact 64 F}
    {d e : ExpHOL 64} {r : PanSemResultExact 64} {t : PanSemStateFiniteExact 64 F}
    (h : evaluateHOLFiniteState s (.storeByte d e) = (some r, t)) :
    ¬ Resumes (some r) := by
  have h1 := congrArg Prod.fst h
  rw [evaluateHOLFiniteState_storeByte] at h1
  revert h1
  split
  · split
    · split <;> intro h1 <;> simp at h1
      subst h1; exact not_resumes_error
    · intro h1; simp at h1; subst h1; exact not_resumes_error
  · intro h1; simp at h1; subst h1; exact not_resumes_error

theorem assign_res_not_resumes {F : Type} {s : PanSemStateFiniteExact 64 F}
    {k : VarKind} {x : MlS} {e : ExpHOL 64} {r : PanSemResultExact 64}
    {t : PanSemStateFiniteExact 64 F}
    (h : evaluateHOLFiniteState s (.assign k x e) = (some r, t)) :
    ¬ Resumes (some r) := by
  have h1 := congrArg Prod.fst h
  rw [evaluateHOLFiniteState_assign] at h1
  revert h1
  split
  · intro h1; simp at h1; subst h1; exact not_resumes_error
  · split <;> intro h1 <;> simp at h1
    subst h1; exact not_resumes_error

theorem seq_noResumes_left {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b : ProgHOL 64}
    (ha : ∀ r t, evaluateHOLFiniteState s a = (some r, t) → ¬ Resumes (some r))
    (hres : Resumes (evaluateHOLFiniteState s (.seq a b)).1) :
    ∃ mid, evaluateHOLFiniteState s a = (none, mid) ∧
      evaluateHOLFiniteState s (.seq a b) = evaluateHOLFiniteState mid b := by
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
  rw [hr] at hres
  cases r with
  | none => exact ⟨mid, rfl, rfl⟩
  | some r' => exact absurd hres (ha r' mid hr)

theorem seq_store_resumes {F : Type} {s : PanSemStateFiniteExact 64 F}
    {d e : ExpHOL 64} {b : ProgHOL 64}
    (hres : Resumes (evaluateHOLFiniteState s (.seq (.store d e) b)).1) :
    ∃ mid, evaluateHOLFiniteState s (.store d e) = (none, mid) ∧
      evaluateHOLFiniteState s (.seq (.store d e) b) = evaluateHOLFiniteState mid b :=
  seq_noResumes_left (fun _ _ h => store_res_not_resumes h) hres

theorem alloc_body_resumes_eq_returned {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (hcode : state.code = originalRuntimeCode)
    (hres : Resumes (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    ∃ v, (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)).1 =
      some (.returned v) := by
  rcases hres with ⟨v, hv⟩ | ⟨eid, v, hexn, hne_trap⟩
  · exact ⟨v, hv⟩
  · exfalso
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
    rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hexn
    dsimp only at hexn
    split at hexn
    · simp at hexn
    · split at hexn
      · rename_i pv _ _
        set pState := setVarHOLFinite (ofString "p") pv state
        have hcode_p : pState.code = originalRuntimeCode := hcode
        rw [evaluateHOLFiniteState_seq_line780] at hexn
        rcases h1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1])
              .skip) with ⟨r1, s1⟩
        rw [h1] at hexn
        cases r1 with
        | some r1' =>
          dsimp only at hexn
          rw [evaluateHOLFiniteState_ite] at h1
          split at h1
          · split at h1
            · rw [evaluateHOLFiniteState_skip] at h1; simp at h1
            · have hnr := Wave8Contracts.M29.evaluate_call_trap_with_not_resumes pState 1 hcode_p
              rw [h1] at hnr
              exact hnr (Or.inr ⟨eid, v, hexn, hne_trap⟩)
          · have h1' := congrArg Prod.fst h1; simp at h1'; subst h1'; simp at hexn
        | none =>
          dsimp only at hexn
          have hcode_s1 : s1.code = originalRuntimeCode := by
            rw [evaluateHOLFiniteState_ite] at h1
            split at h1
            · split at h1
              · rw [evaluateHOLFiniteState_skip] at h1; injection h1 with _ hs; rw [← hs]; exact hcode_p
              · have hnn := evaluate_call_trap_with_no_none pState 1 hcode_p
                rw [h1] at hnn; exact absurd rfl hnn
            · simp at h1
          rw [evaluateHOLFiniteState_dec_total] at hexn
          dsimp only at hexn
          split at hexn
          · simp at hexn
          · split at hexn
            · rename_i qv _ _
              set qState := setVarHOLFinite (ofString "q") qv s1
              have hcode_q : qState.code = originalRuntimeCode := hcode_s1
              rw [evaluateHOLFiniteState_seq_line780] at hexn
              rcases h2 : evaluateHOLFiniteState qState
                  (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                    (.call (some (none, none)) (ofString "trap_with") [.const 1])
                    .skip) with ⟨r2, s2⟩
              rw [h2] at hexn
              cases r2 with
              | some r2' =>
                dsimp only at hexn
                rw [evaluateHOLFiniteState_ite] at h2
                split at h2
                · split at h2
                  · rw [evaluateHOLFiniteState_skip] at h2; simp at h2
                  · have hnr := Wave8Contracts.M29.evaluate_call_trap_with_not_resumes qState 1 hcode_q
                    rw [h2] at hnr
                    exact hnr (Or.inr ⟨eid, v, hexn, hne_trap⟩)
                · have h2' := congrArg Prod.fst h2; simp at h2'; subst h2'; simp at hexn
              | none =>
                dsimp only at hexn
                rw [evaluateHOLFiniteState_seq_line780] at hexn
                rcases h3 : evaluateHOLFiniteState s2
                    (.assign .global (ofString "heap_ptr") (.var .local (ofString "q"))) with ⟨r3, s3⟩
                rw [h3] at hexn
                cases r3 with
                | some r3' =>
                  dsimp only at hexn
                  exact assign_res_not_resumes h3 (Or.inr ⟨eid, v, hexn, hne_trap⟩)
                | none =>
                  dsimp only at hexn
                  rw [evaluateHOLFiniteState_return] at hexn
                  split at hexn
                  · simp at hexn
                  · split at hexn <;> simp at hexn
            · simp at hexn
      · simp at hexn

theorem decCall_resumes_inv {F : Type}
    {s : PanSemStateFiniteExact 64 F} {x fname : MlS} {sh : ShapeHOL}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hres : Resumes (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (retShape : ShapeHOL),
      s.clock ≠ 0 ∧
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) ∧
      ((∃ eid ev, evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
          (some (.exception eid ev), (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2) ∧
          eid ≠ ofString "TrapErr" ∧
          evaluateHOLFiniteState s (.decCall x sh fname args cont) =
            (some (.exception eid ev),
              emptyLocalsHOLFinite (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2)) ∨
       (∃ rv post,
          evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), post) ∧
          (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) retShape) = true ∧
          Resumes (evaluateHOLFiniteState (setVarHOLFinite x rv { post with locals := s.locals }) cont).1 ∧
          (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 =
            (evaluateHOLFiniteState (setVarHOLFinite x rv { post with locals := s.locals }) cont).1 ∧
          (evaluateHOLFiniteState s (.decCall x sh fname args cont)).2 =
            { (evaluateHOLFiniteState (setVarHOLFinite x rv { post with locals := s.locals }) cont).2 with
              locals := HolFiniteMapExact.resVarEq
                (evaluateHOLFiniteState (setVarHOLFinite x rv { post with locals := s.locals }) cont).2.locals
                (x, s.locals.lookup x) })) := by
  have hdec := evaluateHOLFiniteState_decCall_total s x sh fname args cont
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hdec, hargs] at hres; exact absurd hres not_resumes_error
  · rw [hargs] at hdec
    dsimp only at hdec
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, retShape⟩
    · rw [hdec, hl] at hres; exact absurd hres not_resumes_error
    · rw [hl] at hdec
      dsimp only at hdec
      by_cases hcz : s.clock = 0
      · rw [hdec, if_pos hcz] at hres
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      · rw [if_neg hcz] at hdec
        have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        have hfix : fixClockHOLFinite (callEntryStateHOLFinite s callee)
            (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) = (r, post) := by
          rw [hrun] at hrem ⊢
          simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
        rw [hfix] at hdec
        rw [hrun] at hdec
        dsimp only at hdec
        refine ⟨values, body, callee, retShape, hcz, rfl, hl, ?_⟩
        rcases r with _ | r'
        · rw [hdec] at hres; exact absurd hres not_resumes_error
        · cases r' with
          | returned rv =>
            dsimp only at hdec
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) retShape) = true
            · rw [if_pos hsh] at hdec
              rw [hdec] at hres ⊢
              exact Or.inr ⟨rv, post, hrun, hsh, hres, rfl, rfl⟩
            · rw [if_neg hsh] at hdec
              rw [hdec] at hres; exact absurd hres not_resumes_error
          | exception eid ev =>
            dsimp only at hdec
            rw [hdec] at hres ⊢
            rcases hres with ⟨_, h⟩ | ⟨eid', ev', h, hne⟩
            · simp at h
            · injection h with h1; injection h1 with he1 he2
              subst he1 he2
              rw [hrun]
              exact Or.inl ⟨eid, ev, rfl, hne, rfl⟩
          | _ =>
            rw [hdec] at hres
            rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

theorem mpt_fail_call_resumes {F : Type}
    {s : PanSemStateFiniteExact 64 F} {codeExp : ExpHOL 64}
    (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s) {Nd : List Nat} (hNd : NodeHeap s Nd)
    (hres : Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_fail") [codeExp])).1) :
    ∃ eid ev,
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_fail") [codeExp])).1 =
        some (.exception eid ev) ∧
      eid ≠ ofString "TrapErr" ∧
      NodeStep s (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_fail") [codeExp])).2 Nd Nd := by
  have hcall := evaluateHOLFiniteState_call s (some (none, none)) (ofString "mpt_fail") [codeExp]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [codeExp] with _ | values
  · rw [hcall, hargs] at hres; exact absurd hres not_resumes_error
  · rw [hargs] at hcall
    dsimp only at hcall
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "mpt_fail") values with _ | ⟨body, callee, retShape⟩
    · rw [hcall, hl] at hres; exact absurd hres not_resumes_error
    · rw [hl] at hcall
      dsimp only at hcall
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "mpt_fail")
        _ _ _ _ _ values callee (by rw [hcode]; exact lookup_mpt_fail) hl
      subst hsame
      by_cases hcz : s.clock = 0
      · rw [hcall, if_pos hcz] at hres
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      · rw [if_neg hcz] at hcall
        have hbody : sourceFnBody Guest.Software.guestFn_mpt_fail =
            .seq (.raise (ofString "MptErr") (.var .local (ofString "code")))
              (.return (.const 0)) := rfl
        rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise] at hcall
        rcases hesh : (callEntryStateHOLFinite s callee).eshapes.lookup (ofString "MptErr") with _ | esh
        · rw [hesh] at hcall
          rcases hcv : @evalHOLExact 64 F _ (callEntryStateHOLFinite s callee).toExact
              (fun a => Classical.propDecidable ((callEntryStateHOLFinite s callee).memaddrs a))
              (.var .local (ofString "code")) with _ | cv <;>
            (rw [hcv] at hcall; dsimp only at hcall; rw [hcall] at hres; exact absurd hres not_resumes_error)
        · rw [hesh] at hcall
          rcases hcv : @evalHOLExact 64 F _ (callEntryStateHOLFinite s callee).toExact
              (fun a => Classical.propDecidable ((callEntryStateHOLFinite s callee).memaddrs a))
              (.var .local (ofString "code")) with _ | cv
          · rw [hcv] at hcall; dsimp only at hcall; rw [hcall] at hres; exact absurd hres not_resumes_error
          · rw [hcv] at hcall
            dsimp only at hcall
            by_cases hsh_ok : shapeOfHOLExact cv = esh ∧
                sizeOfShapeWithContextHOL (callEntryStateHOLFinite s callee).structs (shapeOfHOLExact cv) ≤ 32
            · rw [if_pos hsh_ok] at hcall
              dsimp only at hcall
              rw [hcall]
              refine ⟨ofString "MptErr", cv, rfl, by decide, ?_⟩
              exact (NodeStep.refl hA hNd).with_locals_clock _ _
            · rw [if_neg hsh_ok] at hcall
              dsimp only at hcall
              rw [hcall] at hres; exact absurd hres not_resumes_error

/-! ## 4. Call-inversion, `NodeFn` bridge, and memory-preservation helpers -/

theorem call_none_resumes_inv {F : Type}
    {s : PanSemStateFiniteExact 64 F} {fname : MlS} {args : List (ExpHOL 64)}
    (hres : Resumes (evaluateHOLFiniteState s (.call none fname args)).1) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (retShape : ShapeHOL),
      s.clock ≠ 0 ∧
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) ∧
      ((∃ eid ev,
          evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
            (some (.exception eid ev), (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2) ∧
          eid ≠ ofString "TrapErr" ∧
          evaluateHOLFiniteState s (.call none fname args) =
            (some (.exception eid ev),
              emptyLocalsHOLFinite (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2)) ∨
       (∃ rv post,
          evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), post) ∧
          shapeEqHOL (shapeOfHOLExact rv) retShape = true ∧
          evaluateHOLFiniteState s (.call none fname args) =
            (some (.returned rv), emptyLocalsHOLFinite post))) := by
  have hcall := evaluateHOLFiniteState_call s none fname args
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hcall, hargs] at hres; exact absurd hres not_resumes_error
  · rw [hargs] at hcall
    dsimp only at hcall
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, retShape⟩
    · rw [hcall, hl] at hres; exact absurd hres not_resumes_error
    · rw [hl] at hcall
      dsimp only at hcall
      by_cases hcz : s.clock = 0
      · rw [hcall, if_pos hcz] at hres
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      · rw [if_neg hcz] at hcall
        refine ⟨values, body, callee, retShape, hcz, rfl, hl, ?_⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post) := hrun
        rw [hrun'] at hcall
        rcases r with _ | r'
        · rw [hcall] at hres; exact absurd hres not_resumes_error
        · cases r' with
          | returned rv =>
            dsimp only at hcall
            by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) retShape = true
            · rw [if_pos hsh] at hcall
              exact Or.inr ⟨rv, post, rfl, hsh, hcall⟩
            · rw [if_neg hsh] at hcall
              rw [hcall] at hres; exact absurd hres not_resumes_error
          | exception eid ev =>
            dsimp only at hcall
            rw [hcall] at hres ⊢
            rcases hres with ⟨_, h⟩ | ⟨eid', ev', h, hne⟩
            · simp at h
            · injection h with h1; injection h1 with he1 he2
              subst he1 he2
              exact Or.inl ⟨eid, ev, rfl, hne, rfl⟩
          | _ =>
            rw [hcall] at hres
            rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

theorem call_void_flow_or_resumes {F : Type}
    {s : PanSemStateFiniteExact 64 F} {fname : MlS} {args : List (ExpHOL 64)} {b : ProgHOL 64}
    (hres : Resumes (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) b)).1) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (retShape : ShapeHOL),
      s.clock ≠ 0 ∧
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) ∧
      ((∃ eid ev,
          evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
            (some (.exception eid ev), (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2) ∧
          eid ≠ ofString "TrapErr" ∧
          evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) b) =
            (some (.exception eid ev),
              emptyLocalsHOLFinite (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2)) ∨
       (∃ rv post,
          evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), post) ∧
          shapeEqHOL (shapeOfHOLExact rv) retShape = true ∧
          Resumes (evaluateHOLFiniteState { post with locals := s.locals } b).1 ∧
          evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) b) =
            evaluateHOLFiniteState { post with locals := s.locals } b)) := by
  have hseq := evaluateHOLFiniteState_seq_line780 s (.call (some (none, none)) fname args) b
  have hcall := evaluateHOLFiniteState_call s (some (none, none)) fname args
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hseq, hcall, hargs] at hres; exact absurd hres not_resumes_error
  · rw [hargs] at hcall
    dsimp only at hcall
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, retShape⟩
    · rw [hseq, hcall, hl] at hres; exact absurd hres not_resumes_error
    · rw [hl] at hcall
      dsimp only at hcall
      by_cases hcz : s.clock = 0
      · rw [hseq, hcall, if_pos hcz] at hres
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      · rw [if_neg hcz] at hcall
        refine ⟨values, body, callee, retShape, hcz, rfl, hl, ?_⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post) := hrun
        rw [hrun'] at hcall
        rcases r with _ | r'
        · rw [hseq, hcall] at hres; exact absurd hres not_resumes_error
        · cases r' with
          | returned rv =>
            dsimp only at hcall
            by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) retShape = true
            · rw [if_pos hsh] at hcall
              rw [hseq, hcall] at hres ⊢
              exact Or.inr ⟨rv, post, rfl, hsh, hres, rfl⟩
            · rw [if_neg hsh] at hcall
              rw [hseq, hcall] at hres; exact absurd hres not_resumes_error
          | exception eid ev =>
            dsimp only at hcall
            rw [hseq, hcall] at hres ⊢
            rcases hres with ⟨_, h⟩ | ⟨eid', ev', h, hne⟩
            · simp at h
            · injection h with h1; injection h1 with he1 he2
              subst he1 he2
              exact Or.inl ⟨eid, ev, rfl, hne, rfl⟩
          | _ =>
            rw [hseq, hcall] at hres
            rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

theorem nodeFnExit_of_step {names : List String}
    {req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hhdr : ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
      globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hstep : ∀ Nd, NodeHeap s Nd → (∀ n ∈ names, RootIn Nd (locN s n)) → req s Nd →
      ∃ Nd', NodeStep s post Nd Nd' ∧
        ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat) :
    NodeFnExit names req s r post := by
  intro _
  refine ⟨hhdr.1, hhdr.2.1, hhdr.2.2, ?_⟩
  intro Nd hNd hroots hreq
  obtain ⟨Nd', hns, hret⟩ := hstep Nd hNd hroots hreq
  exact ⟨Nd', hns.heap, hns.sub, hns.kinds, hns.fresh, hns.frame, hns.globals, hret⟩

theorem nodeStep_of_nodeFn {names : List String}
    {req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop}
    {fname : MlS} (hnf : NodeFn names req fname)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s) {Nd : List Nat} (hNd : NodeHeap s Nd)
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {retShape : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape))
    (hroots : ∀ n ∈ names, RootIn Nd (locN (callEntryStateHOLFinite s callee) n))
    (hreq : req (callEntryStateHOLFinite s callee) Nd)
    (hres : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1) :
    ∃ Nd', NodeStep s (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2 Nd Nd' ∧
      ∀ v, (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned v) →
        ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat := by
  let entry := callEntryStateHOLFinite s callee
  have hA_ent : ArenaReady entry := localsFree_arenaReady s callee (s.clock - 1) hA
  have hP_ent : NodeArgs names req entry := ⟨hA_ent, Nd, hNd, hroots, hreq⟩
  have hnt : (evaluateHOLFiniteState entry body).1 ≠ some .timeOut := by
    intro hto
    rw [hto] at hres
    rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  have hexit := FunSpec.at_lookup hnf s hcode values body callee retShape hl hP_ent hnt hres
  obtain ⟨hA_post, hhp, hsp, hforall⟩ := hexit
  obtain ⟨Nd', hNd', hsub, hkinds, hfresh, hframe, hglob, hret⟩ := hforall Nd hNd hroots hreq
  have hbe : (evaluateHOLFiniteState entry body).2.be = s.be :=
    (evaluateHOLFiniteState_metadata entry body).2.2.1
  refine ⟨Nd', ⟨hA_post, hhp, hsp, hbe, hNd', hsub, hkinds, hfresh, hframe, hglob⟩, hret⟩

/-- If `post` agrees with `s` on every memory cell `< hp0`, has `be = s.be`, `ArenaReady post`,
and `hp0 = globN s "heap_ptr" ≤ globN post "heap_ptr"`, then any `KeyIn s Nd p len` stays
`KeyIn post Nd p len` (before adding any new fresh nodes). -/
theorem keyIn_unchanged_below_hp {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {p len : Nat}
    (ha : ArenaReady s) (hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hbe : post.be = s.be)
    (hmem_lt : ∀ a : BitVec 64, a.toNat < globN s "heap_ptr" → post.memory a = s.memory a)
    (hkinds : ∀ n ∈ Nd, memW post n = memW s n)
    (hk : KeyIn s Nd p len) :
    KeyIn post Nd p len := by
  by_cases hz : len = 0
  · exact Or.inl hz
  obtain ⟨hplo, hheap, hphi⟩ := keyIn_heap ha hk hz
  obtain ⟨hnib, _, hi, hd⟩ := hk.resolve_left hz
  right
  refine ⟨?_, Or.inl ⟨hi.1, by omega⟩, hi, ?_⟩
  · intro k hkl
    have ha64 : p + k < 2 ^ 64 := by
      have : heapLimit < 2 ^ 64 := by decide
      omega
    let c := panByteAlignHOL (BitVec.ofNat 64 (p + k))
    have hc : c.toNat = (p + k) / 8 * 8 := byteCell_toNat ha64
    have hptr8 : globN s "heap_ptr" % 8 = 0 := ha.2.2.2.2.2.2.1
    have hcell_lt : c.toNat < globN s "heap_ptr" := by omega
    have hmem_c := hmem_lt c hcell_lt
    have hb : memB post (p + k) = memB s (p + k) := by
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL _ v post.be).toNat) =
        (match s.memory c with | .word v => (panGetByteHOL _ v s.be).toNat)
      rw [hmem_c, hbe]
    rw [hb]
    exact hnib k hkl
  · intro n hnm
    simpa only [nodeIvl, hkinds n hnm] using hd n hnm

/-- Adding a single fresh node `nd = globN s "heap_ptr"` of size `sz = nodeSize k` (where
`Inside (nd, sz) (globN s "heap_ptr") (globN post "heap_ptr")`) preserves `KeyIn` for any key
already `KeyIn post Nd p len` with `p + len ≤ globN post "heap_ptr"` and disjoint from `(nd, sz)`. -/
theorem keyIn_cons_fresh {F : Type}
    {post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {nd p len : Nat}
    (hk : KeyIn post Nd p len)
    (hdisj_nd : len ≠ 0 → Disj (p, len) (nodeIvl post nd)) :
    KeyIn post (nd :: Nd) p len := by
  by_cases hz : len = 0
  · exact Or.inl hz
  obtain ⟨hnib, hal, hi, hd⟩ := hk.resolve_left hz
  right
  refine ⟨hnib, hal, hi, ?_⟩
  intro n hnm
  rcases List.mem_cons.mp hnm with rfl | hnm'
  · exact hdisj_nd hz
  · exact hd n hnm'

/-- If `post` agrees with `s` on every memory cell `< globN s "heap_ptr"`, has `be = s.be`,
`ArenaReady post`, and `globN s "heap_ptr" ≤ globN post "heap_ptr"`, then every old node `n ∈ Nd`
keeps its exact `memW` at all its offsets and `NodeHeap post Nd` holds, and adding a fresh node
`nd` (`Inside (nodeIvl post nd) (globN s "heap_ptr") (globN post "heap_ptr")`) that satisfies its
own node invariants yields `NodeHeap post (nd :: Nd)`. -/
theorem nodeHeap_cons_fresh {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {nd : Nat}
    (ha : ArenaReady s) (hapost : ArenaReady post)
    (hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hbe : post.be = s.be)
    (hmem_lt : ∀ a : BitVec 64, a.toNat < globN s "heap_ptr" → post.memory a = s.memory a)
    (hNd : NodeHeap s Nd)
    (hnd_fresh : Inside (nodeIvl post nd) (globN s "heap_ptr") (globN post "heap_ptr"))
    (hnd_align : nd % 8 = 0)
    (hnd_kind : memW post nd ≤ 3)
    (hnd_ext : memW post nd = 2 → RootIn (nd :: Nd) (memW post (nd + 48)))
    (hnd_br : memW post nd = 3 → ∀ i, i < 16 → RootIn (nd :: Nd) (memW post (nd + 32 + 8 * i)))
    (hnd_path : (memW post nd = 1 ∨ memW post nd = 2) →
      KeyIn post (nd :: Nd) (memW post (nd + 32)) (memW post (nd + 40)))
    (hnd_c16 : memW post (nd + 16) < 2 ^ 40)
    (hnd_v1 : memW post nd = 1 → memW post (nd + 56) < 2 ^ 40)
    (hnd_v3 : memW post nd = 3 → memW post (nd + 168) < 2 ^ 40) :
    NodeHeap post (nd :: Nd) ∧ (∀ n ∈ Nd, memW post n = memW s n) := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhe_ge : heapLimit ≤ heapEnd := by decide
  have hp_hi_post : globN post "heap_ptr" ≤ heapLimit := hapost.2.2.1
  have hp_lo_s : sourceBase ≤ globN s "heap_ptr" := ha.2.1
  have halloc_heap : ∀ {n : Nat}, n ∈ Nd → Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
    intro n hn
    have hp := hNd.1 n hn
    rcases hp.2.1 with h1 | h2
    · exact h1
    · have := hp.2.2.1.2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := ha.2.2.2.1; have := ha.2.2.2.2.1
      obtain ⟨hsz, _, _⟩ := nodeSize_bounds (memW s n)
      dsimp [nodeIvl, Inside] at *
      omega
  have hold_word_eq : ∀ n ∈ Nd, ∀ off, off + 8 ≤ nodeSize (memW s n) →
      memW post (n + off) = memW s (n + off) := by
    intro n hn off hoff
    have hins := halloc_heap hn
    dsimp [nodeIvl, Inside] at hins
    have hlt : n + off < globN s "heap_ptr" := by omega
    have hlt64 : n + off < 2 ^ 64 := by have := ha.2.2.1; omega
    unfold memW
    rw [hmem_lt (BitVec.ofNat 64 (n + off)) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; exact hlt)]
  have hkinds : ∀ n ∈ Nd, memW post n = memW s n := by
    intro n hn
    obtain ⟨hsz, _, _⟩ := nodeSize_bounds (memW s n)
    simpa using hold_word_eq n hn 0 (by omega)
  have hivl_eq : ∀ n ∈ Nd, nodeIvl post n = nodeIvl s n := by
    intro n hn; simp [nodeIvl, hkinds n hn]
  refine ⟨⟨?_, ?_⟩, hkinds⟩
  · intro x hx
    rcases List.mem_cons.mp hx with hxeq | hx_old
    · -- New node `nd`
      subst hxeq
      obtain ⟨hsz32, hsz176, hsz8⟩ := nodeSize_bounds (memW post x)
      have hins_lim : Inside (nodeIvl post x) sourceBase heapLimit := by
        dsimp [Inside, nodeIvl] at hnd_fresh ⊢; omega
      have halloc_nd : Allocated post (nodeIvl post x) := by
        left; dsimp [Inside, nodeIvl] at hnd_fresh ⊢; omega
      have hwok_nd : WordsOK post (nodeIvl post x) :=
        Wave8Contracts.M26.wordsOK_of_guestInv post hapost.1 x (nodeSize (memW post x))
          hnd_align hsz8 (by dsimp [Inside, nodeIvl] at hins_lim; omega)
          (by dsimp [Inside, nodeIvl] at hins_lim; omega)
      exact ⟨hnd_kind, halloc_nd, hins_lim, hwok_nd, hnd_ext, hnd_br, hnd_path, hnd_c16, hnd_v1, hnd_v3⟩
    · -- Old node `x ∈ Nd`
      have hp := hNd.1 x hx_old
      have hx_in : Inside (nodeIvl s x) sourceBase (globN s "heap_ptr") := halloc_heap hx_old
      rw [hkinds x hx_old, hivl_eq x hx_old]
      refine ⟨hp.1, Or.inl ⟨hx_in.1, Nat.le_trans hx_in.2 hgrow⟩, hp.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- WordsOK
        obtain ⟨ha1, ha2, _⟩ := hp.2.2.2.1
        exact Wave8Contracts.M26.wordsOK_of_guestInv post hapost.1 x (nodeSize (memW s x))
          ha1 ha2 hp.2.2.1.1 (Nat.le_trans hp.2.2.1.2 hhe_ge)
      · intro hk2
        have hsz2 : nodeSize (memW s x) = 56 := by simp [nodeSize, hk2]
        rw [hold_word_eq x hx_old 48 (by omega)]
        rcases hp.2.2.2.2.1 hk2 with h0 | hm
        · exact Or.inl h0
        · exact Or.inr (List.mem_cons_of_mem _ hm)
      · intro hk3 i hi
        have hsz3 : nodeSize (memW s x) = 176 := by simp [nodeSize, hk3]
        have heq : x + 32 + 8 * i = x + (32 + 8 * i) := by omega
        rw [heq, hold_word_eq x hx_old (32 + 8 * i) (by omega), ← heq]
        rcases hp.2.2.2.2.2.1 hk3 i hi with h0 | hm
        · exact Or.inl h0
        · exact Or.inr (List.mem_cons_of_mem _ hm)
      · intro hk12
        have hsz12 : 56 ≤ nodeSize (memW s x) := by
          rcases hk12 with hk1 | hk2
          · simp [nodeSize, hk1]
          · simp [nodeSize, hk2]
        rw [hold_word_eq x hx_old 32 (by omega), hold_word_eq x hx_old 40 (by omega)]
        have hk_old := hp.2.2.2.2.2.2.1 hk12
        have hk_post := keyIn_unchanged_below_hp ha hgrow hbe hmem_lt hkinds hk_old
        refine keyIn_cons_fresh hk_post (fun hlen_nz => ?_)
        obtain ⟨_, hplen_hp, _⟩ := keyIn_heap ha hk_old hlen_nz
        exact Or.inr (Or.inr (Or.inl (Nat.le_trans hplen_hp hnd_fresh.1)))
      · obtain ⟨hsz32, _, _⟩ := nodeSize_bounds (memW s x)
        rw [hold_word_eq x hx_old 16 (by omega)]
        exact hp.2.2.2.2.2.2.2.1
      · intro hk1
        have hsz1 : nodeSize (memW s x) = 64 := by simp [nodeSize, hk1]
        rw [hold_word_eq x hx_old 56 (by omega)]
        exact hp.2.2.2.2.2.2.2.2.1 hk1
      · intro hk3
        have hsz3 : nodeSize (memW s x) = 176 := by simp [nodeSize, hk3]
        rw [hold_word_eq x hx_old 168 (by omega)]
        exact hp.2.2.2.2.2.2.2.2.2 hk3
  · intro x hx y hy hxy
    rcases List.mem_cons.mp hx with rfl | hx_old <;> rcases List.mem_cons.mp hy with rfl | hy_old
    · exact absurd rfl hxy
    · rw [hivl_eq y hy_old]
      have hy_in := halloc_heap hy_old
      exact Or.inr (Or.inr (Or.inr (Nat.le_trans hy_in.2 hnd_fresh.1)))
    · rw [hivl_eq x hx_old]
      have hx_in := halloc_heap hx_old
      exact Or.inr (Or.inr (Or.inl (Nat.le_trans hx_in.2 hnd_fresh.1)))
    · rw [hivl_eq x hx_old, hivl_eq y hy_old]
      exact hNd.2 x hx_old y hy_old hxy

/-- FrameOutside helper when `post` changes memory only inside `[globN s "heap_ptr", heapLimit)`. -/
theorem frameOutside_of_mem_lt_hp {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s)
    (hmem : ∀ a : BitVec 64,
      (a.toNat < globN s "heap_ptr" ∨ heapLimit ≤ a.toNat) → post.memory a = s.memory a) :
    FrameOutside s post
      ((Nd.map fun n => nodeIvl s n) ++
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
  intro a _ hfresh
  apply hmem a
  by_cases hlt : a.toNat < globN s "heap_ptr"
  · exact Or.inl hlt
  · by_cases hge : heapLimit ≤ a.toNat
    · exact Or.inr hge
    · exfalso
      apply hfresh
      have hhp_lim : globN s "heap_ptr" ≤ heapLimit := ha.2.2.1
      dsimp [CellHits]
      omega

/-- Extract word value from a successful `store` step. -/
theorem store_none_inv {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    {d e : ExpHOL 64} {addr : BitVec 64}
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) d =
      some (.val (.word addr)))
    (h1 : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hst : evaluateHOLFiniteState s (.store d e) = (none, mid)) :
    ∃ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
        some (.val (.word w)) ∧
      s.memaddrs addr ∧
      mid = { s with memory := Wave8Contracts.M26.updW s.memory addr w } := by
  rw [evaluateHOLFiniteState_store, hd] at hst
  dsimp only at hst
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
  · rw [hev] at hst; simp at hst
  · rw [hev] at hst
    dsimp only at hst
    obtain ⟨w, rfl⟩ := h1 val hev
    rcases hm : @panMemStoresHOL 64 _ addr (flattenHOL (.val (.word w))) s.memaddrs
        (fun x => Classical.propDecidable (s.memaddrs x)) s.memory with _ | m'
    · rw [hm] at hst; simp at hst
    · rw [hm] at hst
      injection hst with _ hmid
      obtain ⟨hdom, rfl⟩ := Wave8Contracts.M26.stores_word _ hm
      exact ⟨w, rfl, hdom, hmid.symm⟩

/-- Lookup local word from `evalHOLExact (.var .local x) = some (.val (.word w))`. -/
theorem local_word_of_eval {F : Type} {s : PanSemStateFiniteExact 64 F} {x : String} {w : BitVec 64}
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString x)) = some (.val (.word w))) :
    s.locals.lookup (ofString x) = some (.val (.word w)) ∧ locN s x = w.toNat := by
  simp only [evalHOLExact] at h
  exact ⟨h, by simp [locN, h]⟩

theorem local_is_word_of_eval {F : Type} {s : PanSemStateFiniteExact 64 F} {x : String}
    {Nd : List Nat} {n : Nat} (hNd : NodeHeap s Nd) (hn : n ∈ Nd)
    (off : Nat) (hoff8 : off % 8 = 0) (hoff : off < nodeSize (memW s n)) :
    WordAt s (n + off) ∧
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.const (BitVec.ofNat 64 n), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW s (n + off))))) := by
  have hp := hNd.1 n hn
  have hins := hp.2.2.1
  have hwok := hp.2.2.2.1
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  obtain ⟨_, _, hsz8⟩ := nodeSize_bounds (memW s n)
  have hk : off / 8 < nodeSize (memW s n) / 8 := by omega
  have hwa : WordAt s (n + off) := by
    have h := hwok.2.2 (off / 8) hk
    dsimp [nodeIvl] at h
    have heq : n + 8 * (off / 8) = n + off := by omega
    rwa [heq] at h
  refine ⟨hwa, ?_⟩
  obtain ⟨w, hdom, hmem⟩ := hwa
  have hlt : n + off < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hins; omega
  have hadd : BitVec.ofNat 64 n + BitVec.ofNat 64 off = BitVec.ofNat 64 (n + off) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hmw : BitVec.ofNat 64 (memW s (n + off)) = w := by
    unfold memW; rw [hmem]; simp
  simp [evalHOLExact, evalListHOLExact, valueIsWord, valueWord, wordOpHOL, wordOp,
    isWfShapeExactHOL, memLoadHOLExact, hadd, hdom, hmem, hmw]

/-- Modifying an existing node `node ∈ Nd` at aligned offsets strictly ≥ 8 (`off ∈ [8, nodeSize (memW s node))`)
while keeping its kind `+0`, path `+32/+40`, children (except any updated child in `RootIn Nd`),
and cache/value bounds preserves `NodeHeap` and `FrameOutside`. -/
theorem nodeStep_modify_node {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {node : Nat}
    (ha : ArenaReady s) (hNd : NodeHeap s Nd) (hnode : node ∈ Nd)
    (hc : post.code = s.code) (hm : post.memaddrs = s.memaddrs)
    (hsh : post.shMemaddrs = s.shMemaddrs) (hba : post.baseAddr = s.baseAddr)
    (hbe : post.be = s.be) (hg : post.globals = s.globals)
    (hmem_other : ∀ a : BitVec 64,
      ¬ (node + 8 ≤ a.toNat ∧ a.toNat + 8 ≤ node + nodeSize (memW s node)) →
      post.memory a = s.memory a)
    (hnode_ext : memW s node = 2 → RootIn Nd (memW post (node + 48)))
    (hnode_br : memW s node = 3 → ∀ i, i < 16 → RootIn Nd (memW post (node + 32 + 8 * i)))
    (hnode_path : (memW s node = 1 ∨ memW s node = 2) →
      memW post (node + 32) = memW s (node + 32) ∧ memW post (node + 40) = memW s (node + 40))
    (hnode_c16 : memW post (node + 16) < 2 ^ 40)
    (hnode_v1 : memW s node = 1 → memW post (node + 56) < 2 ^ 40)
    (hnode_v3 : memW s node = 3 → memW post (node + 168) < 2 ^ 40) :
    NodeStep s post Nd Nd := by
  have hG_post : GuestInv post := guestInv_congr hc hm hsh hba ha.1
  have hglob_eq : ∀ nm : String, globN post nm = globN s nm := fun nm => by
    unfold globN; rw [hg]
  have hA_post : ArenaReady post := ⟨hG_post, arenaOK_congr_globals hg ha.2⟩
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhe_ge : heapLimit ≤ heapEnd := by decide
  have hp_node := hNd.1 node hnode
  have hnode_ins := hp_node.2.2.1
  obtain ⟨hsz_node32, _, _⟩ := nodeSize_bounds (memW s node)
  have hword_out : ∀ a : Nat, a < 2 ^ 64 →
      ¬ (node + 8 ≤ a ∧ a + 8 ≤ node + nodeSize (memW s node)) →
      memW post a = memW s a := by
    intro a ha64 hout
    unfold memW
    rw [hmem_other (BitVec.ofNat 64 a) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64]; exact hout)]
  have hkinds : ∀ n ∈ Nd, memW post n = memW s n := by
    intro n hn
    have hins := (hNd.1 n hn).2.2.1
    obtain ⟨hsz, _, _⟩ := nodeSize_bounds (memW s n)
    dsimp [Inside, nodeIvl] at hins hnode_ins
    by_cases hne : n = node
    · subst hne; exact hword_out _ (by omega) (by omega)
    · have hd := hNd.2 n hn node hnode hne
      dsimp [Disj, nodeIvl] at hd
      exact hword_out _ (by omega) (by omega)
  have hivl_eq : ∀ n ∈ Nd, nodeIvl post n = nodeIvl s n := by
    intro n hn; simp [nodeIvl, hkinds n hn]
  have hkey_keep : ∀ p len, KeyIn s Nd p len → KeyIn post Nd p len := by
    intro p len hk
    by_cases hz : len = 0
    · exact Or.inl hz
    obtain ⟨hnib, halloc, hins, hd⟩ := hk.resolve_left hz
    have halloc_post : Allocated post (p, len) := by
      unfold Allocated; simp only [hglob_eq]; exact halloc
    right
    refine ⟨?_, halloc_post, hins, fun n hn => by rw [hivl_eq n hn]; exact hd n hn⟩
    intro k hk_lt
    have ha64 : p + k < 2 ^ 64 := by dsimp [Inside] at hins; omega
    let c := panByteAlignHOL (BitVec.ofNat 64 (p + k))
    have hc_nat : c.toNat = (p + k) / 8 * 8 := byteCell_toNat ha64
    have hd_node := hd node hnode
    have hnd8 := hp_node.2.2.2.1.1
    obtain ⟨_, _, hsz8⟩ := nodeSize_bounds (memW s node)
    dsimp [Disj, nodeIvl] at hd_node hnd8
    have hmc : post.memory c = s.memory c := by
      apply hmem_other c
      rw [hc_nat]
      rcases hd_node with h0 | h0 | h1 | h2 <;> omega
    have hb : memB post (p + k) = memB s (p + k) := by
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL _ v post.be).toNat) =
        (match s.memory c with | .word v => (panGetByteHOL _ v s.be).toNat)
      rw [hmc, hbe]
    rw [hb]
    exact hnib k hk_lt
  refine ⟨hA_post, by rw [hglob_eq], by rw [hglob_eq], hbe, ⟨?_, ?_⟩,
    fun _ h => h, hkinds, fun _ h => Or.inl h, ?_, fun k _ => by rw [hg]⟩
  · intro n hn
    have hp := hNd.1 n hn
    have hins := hp.2.2.1
    obtain ⟨hsz32, _, _⟩ := nodeSize_bounds (memW s n)
    rw [hkinds n hn, hivl_eq n hn]
    have halloc_n : Allocated post (nodeIvl s n) := by
      unfold Allocated; simp only [hglob_eq]; exact hp.2.1
    have hwok_n : WordsOK post (nodeIvl s n) :=
      Wave8Contracts.M26.wordsOK_of_guestInv post hG_post n (nodeSize (memW s n))
        hp.2.2.2.1.1 hp.2.2.2.1.2.1 hins.1 (Nat.le_trans hins.2 hhe_ge)
    by_cases hne : n = node
    · subst hne
      refine ⟨hp.1, halloc_n, hins, hwok_n, hnode_ext, hnode_br, ?_, hnode_c16, hnode_v1, hnode_v3⟩
      intro hk12
      obtain ⟨he32, he40⟩ := hnode_path hk12
      rw [he32, he40]
      exact hkey_keep _ _ (hp.2.2.2.2.2.2.1 hk12)
    · have hd := hNd.2 n hn node hnode hne
      have hoff_eq : ∀ off, off + 8 ≤ nodeSize (memW s n) → memW post (n + off) = memW s (n + off) := by
        intro off hoff
        dsimp [Inside, Disj, nodeIvl] at hins hnode_ins hd
        exact hword_out _ (by omega) (by omega)
      refine ⟨hp.1, halloc_n, hins, hwok_n, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro hk2
        have : nodeSize (memW s n) = 56 := by simp [nodeSize, hk2]
        rw [hoff_eq 48 (by omega)]; exact hp.2.2.2.2.1 hk2
      · intro hk3 i hi
        have : nodeSize (memW s n) = 176 := by simp [nodeSize, hk3]
        have heq : n + 32 + 8 * i = n + (32 + 8 * i) := by omega
        rw [heq, hoff_eq (32 + 8 * i) (by omega), ← heq]
        exact hp.2.2.2.2.2.1 hk3 i hi
      · intro hk12
        have : 56 ≤ nodeSize (memW s n) := by
          rcases hk12 with hk1 | hk2
          · simp [nodeSize, hk1]
          · simp [nodeSize, hk2]
        rw [hoff_eq 32 (by omega), hoff_eq 40 (by omega)]
        exact hkey_keep _ _ (hp.2.2.2.2.2.2.1 hk12)
      · rw [hoff_eq 16 (by omega)]; exact hp.2.2.2.2.2.2.2.1
      · intro hk1
        have : nodeSize (memW s n) = 64 := by simp [nodeSize, hk1]
        rw [hoff_eq 56 (by omega)]; exact hp.2.2.2.2.2.2.2.2.1 hk1
      · intro hk3
        have : nodeSize (memW s n) = 176 := by simp [nodeSize, hk3]
        rw [hoff_eq 168 (by omega)]; exact hp.2.2.2.2.2.2.2.2.2 hk3
  · intro x hx y hy hxy
    rw [hivl_eq x hx, hivl_eq y hy]
    exact hNd.2 x hx y hy hxy
  · intro a hkeep _
    apply hmem_other a
    intro hhit_node
    apply hkeep (nodeIvl s node) (List.mem_append_left _ (List.mem_map.mpr ⟨node, hnode, rfl⟩))
    dsimp [CellHits, nodeIvl]
    omega

/-! ## 5. Parameter word extraction from `lookupCodeHOLFinite` -/

private theorem foldl_lookup_preserved {α β : Type} [DecidableEq α]
    (pairs : List (α × β)) (init : α → Option β) (target : α)
    (hnot : ∀ q ∈ pairs, q.1 ≠ target) :
    List.foldl (fun map entry current => if current = entry.1 then some entry.2 else map current)
      init pairs target = init target := by
  induction pairs generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q hq => hnot q (List.mem_cons_of_mem _ hq))]
    have hne : target ≠ hd.1 := Ne.symm (hnot hd (by simp))
    simp [hne]

private theorem zip_fst_ne {α β γ : Type}
    (names : List (α × γ)) (vals : List β) (target : α)
    (hnot : ∀ q ∈ names, q.1 ≠ target) :
    ∀ p ∈ (names.map Prod.fst).zip vals, p.1 ≠ target := by
  induction names generalizing vals with
  | nil => intro p hp; simp at hp
  | cons hd tl ih =>
    cases vals with
    | nil => intro p hp; simp at hp
    | cons v vs =>
      intro p hp
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp'
      · exact hnot hd (by simp)
      · exact ih vs (fun q hq => hnot q (List.mem_cons_of_mem _ hq)) p hp'

theorem lookup_param_word {code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fname : MlS} {params : List (MlS × ShapeHOL)}
    {body foundBody : ProgHOL 64} {rs foundRs : ShapeHOL}
    {values : List (ValueHOL 64)} {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlook : code fname = some (params, body, rs))
    (hfound : lookupCodeHOLFinite code fname values =
      some (foundBody, locals, foundRs))
    (pre : List (MlS × ShapeHOL)) (pk : String) (post : List (MlS × ShapeHOL))
    (hp_split : params = pre ++ (ofString pk, .one) :: post)
    (hafter : ∀ q ∈ post, q.1 ≠ ofString pk) :
    ∃ w : BitVec 64,
      locals.lookup (ofString pk) = some (.val (.word w)) ∧
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.locals = locals → locN s pk = w.toNat) := by
  have raw := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some code fname values foundBody locals foundRs hfound
  unfold lookupCodeHOLExact at raw
  rw [hlook] at raw
  dsimp only at raw
  split at raw
  · rename_i hall
    have hloc_fn : locals.lookup =
        List.foldl (fun map entry current => if current = entry.1 then some entry.2 else map current)
          (fun _ => none) ((List.map Prod.fst params).zip values) :=
      (Prod.mk.inj (Prod.mk.inj (Option.some.inj raw)).2).1.symm
    obtain ⟨_, hlen_eq, hzip_all⟩ := hall
    have hidx_p : pre.length < params.length := by rw [hp_split]; simp
    have hidx_v : pre.length < values.length := by omega
    set vk := values[pre.length]'hidx_v
    have hv_split : values = values.take pre.length ++ vk :: values.drop (pre.length + 1) := by
      conv_lhs => rw [← List.take_append_drop pre.length values]
      congr 1
      exact List.drop_eq_getElem_cons hidx_v
    have hlen_take : (values.take pre.length).length = pre.length := by
      simp; omega
    have hmem_pair : ((ofString pk, ShapeHOL.one), vk) ∈ params.zip values := by
      rw [hp_split, hv_split, List.zip_append hlen_take.symm, List.zip_cons_cons]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    have hsh_i : shapeEqHOL .one (shapeOfHOLExact vk) = true :=
      (List.all_eq_true.mp hzip_all) _ hmem_pair
    have hvk_word : ∃ w : BitVec 64, vk = .val (.word w) := by
      rcases vk with ⟨⟨w⟩⟩ | _ | _
      · exact ⟨w, rfl⟩
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh_i
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh_i
    obtain ⟨w, hvk_eq⟩ := hvk_word
    have hlk : locals.lookup (ofString pk) = some (.val (.word w)) := by
      have hfn := congrFun hloc_fn (ofString pk)
      rw [hfn, hp_split, hv_split]
      have hzip : (List.map Prod.fst (pre ++ (ofString pk, ShapeHOL.one) :: post)).zip
          (values.take pre.length ++ vk :: values.drop (pre.length + 1)) =
          (pre.map Prod.fst).zip (values.take pre.length) ++
            (ofString pk, vk) :: (post.map Prod.fst).zip (values.drop (pre.length + 1)) := by
        rw [List.map_append, List.map_cons, List.zip_append (by simp [hlen_take]), List.zip_cons_cons]
      rw [hzip, List.foldl_append, List.foldl_cons]
      rw [foldl_lookup_preserved ((post.map Prod.fst).zip (values.drop (pre.length + 1))) _ (ofString pk)
        (zip_fst_ne post _ (ofString pk) hafter)]
      simp [hvk_eq]
    refine ⟨w, hlk, fun s hsloc => ?_⟩
    unfold locN
    rw [hsloc, hlk]
  · cases raw

theorem lookup_param_exact {code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fname : MlS} {params : List (MlS × ShapeHOL)}
    {body foundBody : ProgHOL 64} {rs foundRs : ShapeHOL}
    {values : List (ValueHOL 64)} {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlook : code fname = some (params, body, rs))
    (hfound : lookupCodeHOLFinite code fname values =
      some (foundBody, locals, foundRs))
    (pre : List (MlS × ShapeHOL)) (pk : String) (sk : ShapeHOL) (post : List (MlS × ShapeHOL))
    (vpre : List (ValueHOL 64)) (vk : ValueHOL 64) (vpost : List (ValueHOL 64))
    (hp_split : params = pre ++ (ofString pk, sk) :: post)
    (hv_split : values = vpre ++ vk :: vpost)
    (hlen : vpre.length = pre.length)
    (hafter : ∀ q ∈ post, q.1 ≠ ofString pk) :
    foundBody = body ∧ locals.lookup (ofString pk) = some vk := by
  have raw := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some code fname values foundBody locals foundRs hfound
  unfold lookupCodeHOLExact at raw
  rw [hlook] at raw
  dsimp only at raw
  split at raw
  · have hb_eq : foundBody = body := (Prod.mk.inj (Option.some.inj raw)).1.symm
    have hloc_fn : locals.lookup =
        List.foldl (fun map entry current => if current = entry.1 then some entry.2 else map current)
          (fun _ => none) ((List.map Prod.fst params).zip values) :=
      (Prod.mk.inj (Prod.mk.inj (Option.some.inj raw)).2).1.symm
    refine ⟨hb_eq, ?_⟩
    have hfn := congrFun hloc_fn (ofString pk)
    rw [hfn, hp_split, hv_split]
    have hzip : (List.map Prod.fst (pre ++ (ofString pk, sk) :: post)).zip
        (vpre ++ vk :: vpost) =
        (pre.map Prod.fst).zip vpre ++
          (ofString pk, vk) :: (post.map Prod.fst).zip vpost := by
      rw [List.map_append, List.map_cons, List.zip_append (by simp [hlen]), List.zip_cons_cons]
    rw [hzip, List.foldl_append, List.foldl_cons]
    rw [foldl_lookup_preserved ((post.map Prod.fst).zip vpost) _ (ofString pk)
      (zip_fst_ne post _ (ofString pk) hafter)]
    simp
  · cases raw

/-! ## 6. `noExn` checker and `node_new_branch` contract -/

def noExnProg : ProgHOL 64 → Bool
  | .dec _ _ _ b => noExnProg b
  | .seq a b => noExnProg a && noExnProg b
  | .ite _ a b => noExnProg a && noExnProg b
  | .while _ b => noExnProg b
  | .assign _ _ _ | .store _ _ | .storeByte _ _ => true
  | .skip | .break | .continue | .annot _ _ | .return _ => true
  | _ => false

theorem evaluate_noExnProg {F : Type} (p : ProgHOL 64) (hp : noExnProg p = true)
    (s : PanSemStateFiniteExact 64 F) (eid : MlS) (ev : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.exception eid ev) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | «break» => rw [evaluateHOLFiniteState_break]; simp
  | «continue» => rw [evaluateHOLFiniteState_continue]; simp
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; simp
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | assign _ _ _ =>
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
  | dec x sh init b =>
    have hb : noExnProg b = true := by simpa [shape, noExnProg] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noExnProg b hb _ eid ev
      · simp
  | seq a b =>
    have hab : noExnProg a = true ∧ noExnProg b = true := by
      simpa [shape, noExnProg, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noExnProg a hab.1 s eid ev
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    have mclk : m.clock ≤ s.clock := rem
    cases r with
    | none => exact evaluate_noExnProg b hab.2 m eid ev
    | some _ => exact ha
  | ite _ a b =>
    have hab : noExnProg a = true ∧ noExnProg b = true := by
      simpa [shape, noExnProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noExnProg b hab.2 s eid ev
      · exact evaluate_noExnProg a hab.1 s eid ev
    · simp
  | «while» cond body =>
    have hb : noExnProg body = true := by simpa [shape, noExnProg] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noExnProg body hb (decClockHOLFinite s) eid ev
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none =>
            exact evaluate_noExnProg (.while cond body) (by simpa [noExnProg] using hb) mid eid ev
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noExnProg (.while cond body) (by simpa [noExnProg] using hb) mid eid ev
            | exception _ _ => exact ih1
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, noExnProg] at hp
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

theorem memzero_body_no_exception {F : Type} (s : PanSemStateFiniteExact 64 F)
    (eid : MlS) (ev : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memzero)).1 ≠
      some (.exception eid ev) :=
  evaluate_noExnProg _ (by decide) s eid ev

theorem memcpy_body_no_exception {F : Type} (s : PanSemStateFiniteExact 64 F)
    (eid : MlS) (ev : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1 ≠
      some (.exception eid ev) :=
  evaluate_noExnProg _ (by decide) s eid ev

theorem memeq_body_no_exception {F : Type} (s : PanSemStateFiniteExact 64 F)
    (eid : MlS) (ev : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memeq)).1 ≠
      some (.exception eid ev) :=
  evaluate_noExnProg _ (by decide) s eid ev

theorem node_new_branch_spec {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (hAR : ArenaReady s)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_branch)).1) :
    let r := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_branch)).1
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_branch)).2
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
      globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
      ∃ br : BitVec 64,
        r = some (.returned (.val (.word br))) ∧
        br.toNat = globN s "heap_ptr" ∧
        br.toNat % 8 = 0 ∧
        globN post "heap_ptr" = br.toNat + 176 ∧
        memW post br.toNat = 3 ∧
        (∀ i < 16, memW post (br.toNat + 32 + 8 * i) = 0) ∧
        memW post (br.toNat + 16) = 0 ∧
        memW post (br.toNat + 168) = 0 ∧
        ∀ Nd, NodeHeap s Nd →
          NodeStep s post Nd (br.toNat :: Nd) := by
  intro r post
  have hG : GuestInv s := hAR.1
  have hA : ArenaOK s := hAR.2
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_branch =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 176]
        (.seq
          (.call (some (none, none)) (ofString "memzero")
            [.var .local (ofString "nd"), .const (BitVec.ofNat 64 176)])
          (.seq
            (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 0)])
              (.const (BitVec.ofNat 64 3)))
            (.return (.var .local (ofString "nd"))))) := rfl
  have hres' : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_branch)).1 := hres
  rw [hbody] at hres'
  obtain ⟨values, abody, acallee, aret, hcz, hargs, hl, hexn | ⟨rv, apost, harun, _, hcont_res, hr_eq, hp_eq⟩⟩ :=
    decCall_resumes_inv hres'
  · obtain ⟨eid, ev, ha_exn, hne_trap, _⟩ := hexn
    have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc")
      _ _ _ _ _ values acallee (by rw [hcode]; exact lookup_alloc) hl
    subst hsame
    obtain ⟨_, hret_a⟩ := alloc_body_resumes_eq_returned (callEntryStateHOLFinite s acallee) hcode
      (by rw [ha_exn]; exact Or.inr ⟨eid, ev, rfl, hne_trap⟩)
    rw [ha_exn] at hret_a; cases hret_a
  · have hvals : values = [.val (.word 176)] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simpa [evalListHOLExact, evalHOLExact] using hargs.symm
    subst hvals
    have hl_exact := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_alloc) 176 (by rw [hcode]; exact lookup_alloc)
    rw [hl_exact] at hl
    obtain ⟨hbody_a, hrest_a⟩ := Prod.mk.inj (Option.some.inj hl.symm)
    obtain ⟨hcal_a, hret_a⟩ := Prod.mk.inj hrest_a
    subst hbody_a hcal_a hret_a
    have hn_ent : (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 176)))).locals.lookup
        (ofString "n") = some (.val (.word 176)) := by
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have harun_info := Wave8Contracts.M26.alloc_body_run
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 176))))
      hp 176 hcode hhp hn_ent rv (by rw [harun])
    rw [harun] at harun_info
    obtain ⟨rfl, hcmp1, hcmp2, hapost_eq⟩ := harun_info
    dsimp only at hapost_eq
    set q : BitVec 64 := (hp + (176 + 7)) &&& ((0 : BitVec 64) - 8)
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := Wave8Contracts.M26.alloc_arith hp 176 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = hp.toNat + ((176 : BitVec 64).toNat + 7) / 8 * 8 at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    have h176 : ((176 : BitVec 64).toNat + 7) / 8 * 8 = 176 := by decide
    rw [h176] at hq_eq
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hhe_ge : heapLimit ≤ heapEnd := by decide
    set s0 := setVarHOLFinite (ofString "nd") (.val (.word hp)) { apost with locals := s.locals }
    have hs0_nd : s0.locals.lookup (ofString "nd") = some (.val (.word hp)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs0_code : s0.code = originalRuntimeCode := by
      simp [s0, setVarHOLFinite]; rw [hapost_eq]; exact hcode
    have hs0_G : GuestInv s0 := by
      refine ⟨hs0_code, ?_, ?_, ?_⟩ <;> (simp [s0, setVarHOLFinite]; rw [hapost_eq])
      · exact hG.memaddrs
      · exact hG.shMemaddrs
      · exact hG.baseAddr
    have hs0_glob : s0.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
      simp [s0, setVarHOLFinite]; rw [hapost_eq]; rfl
    have hs0_hp : globN s0 "heap_ptr" = q.toNat := by
      unfold globN; rw [hs0_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hs0_fp : globN s0 "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      unfold globN; rw [hs0_glob]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hs0_sp : globN s0 "scratch_ptr" = globN s "scratch_ptr" := by
      unfold globN; rw [hs0_glob]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hs0_AR : ArenaReady s0 :=
      ⟨hs0_G, arenaOK_update_heap hs0_glob (by have := hA.1; omega) hq_hi hq_al hA⟩
    obtain ⟨mvals, mbody, mcallee, mret, _, hmargs, hml, hmexn | ⟨mrv, mpost, hmrun, _, hst_res, hm_eq⟩⟩ :=
      call_void_flow_or_resumes hcont_res
    · obtain ⟨eid, ev, hm_exn, _, _⟩ := hmexn
      have hsame := lookupCodeHOLFinite_installed_body s0.code.lookup (ofString "memzero")
        _ _ _ _ _ mvals mcallee (by rw [hs0_code]; exact lookup_memzero) hml
      subst hsame
      exact absurd (congrArg Prod.fst hm_exn) (memzero_body_no_exception _ eid ev)
    · have hmvals : mvals = [.val (.word hp), .val (.word 176)] := by
        rw [evalListHOLFinite_eq_toExact] at hmargs
        simpa [evalListHOLExact, evalHOLExact, hs0_nd] using hmargs.symm
      subst hmvals
      have hml_exact := pan_two_word_lookup s0.code.lookup (ofString "memzero")
        (ofString "dst") (ofString "n") (sourceFnBody Guest.Software.guestFn_memzero)
        hp 176 (by decide) (by rw [hs0_code]; exact lookup_memzero)
      rw [hml_exact] at hml
      obtain ⟨hbody_m, hrest_m⟩ := Prod.mk.inj (Option.some.inj hml.symm)
      obtain ⟨hcal_m, hret_m⟩ := Prod.mk.inj hrest_m
      subst hbody_m hcal_m hret_m
      let mentry := callEntryStateHOLFinite s0
        ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word hp))).update
          (ofString "n", .val (.word 176)))
      have hm_dst : locN mentry "dst" = hp.toNat := by
        simp [mentry, locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "dst" by decide]
      have hm_n : locN mentry "n" = 176 := by
        simp [mentry, locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hm_AR : ArenaReady mentry := localsFree_arenaReady s0 _ _ hs0_AR
      have hm_frame := Wave8Contracts.M28.memzero_body_frame mentry hs0_code hm_AR.1
        (by rw [hmrun]; exact Or.inl ⟨mrv, rfl⟩)
      rw [hmrun, hm_dst, hm_n] at hm_frame
      have hzv_spec : FunSpec ArenaReady
          (fun st r' post' => ∀ v, r' = some (.returned v) → ∀ a, locN st "dst" ≤ a →
            a + 8 ≤ locN st "dst" + locN st "n" → a % 8 = 0 → memW post' a = 0)
          (ofString "memzero") := Wave8Contracts.M29.zv_memzero
      have hzv := FunSpec.at_lookup hzv_spec s0 hs0_code
        [.val (.word hp), .val (.word 176)] (sourceFnBody Guest.Software.guestFn_memzero)
        ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word hp))).update
          (ofString "n", .val (.word 176))) .one
        hml_exact hm_AR (by rw [hmrun]; simp) mrv (by rw [hmrun])
      rw [hmrun, hm_dst, hm_n] at hzv
      set s1 : PanSemStateFiniteExact 64 F := { mpost with locals := s0.locals }
      have hs1_nd : s1.locals.lookup (ofString "nd") = some (.val (.word hp)) := hs0_nd
      have hs1_ma : s1.memaddrs = ordinaryDomain := by
        change mpost.memaddrs = ordinaryDomain
        rw [hm_frame.2.1]; exact hs0_G.memaddrs
      have hdom_hp0 : s1.memaddrs (hp + BitVec.ofNat 64 0) := by
        have h0 : hp + BitVec.ofNat 64 0 = BitVec.ofNat 64 hp.toNat := by simp
        rw [hs1_ma, h0]
        exact Wave8Contracts.M26.ordinaryDomain_of_nat hp.toNat
          (by rw [hhp_eq]; exact hA.1) (by omega) hhp_al
      have hst_eval : evaluateHOLFiniteState s1
          (.seq
            (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 0)])
              (.const (BitVec.ofNat 64 3)))
            (.return (.var .local (ofString "nd")))) =
          (some (.returned (.val (.word hp))),
            emptyLocalsHOLFinite { s1 with memory := Wave8Contracts.M26.updW mpost.memory (hp + BitVec.ofNat 64 0) (BitVec.ofNat 64 3) }) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
        have hd : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 0)]) =
            some (.val (.word (hp + BitVec.ofNat 64 0))) := by
          simp [evalHOLExact, evalListHOLExact, hs1_nd, valueIsWord, valueWord, wordOpHOL, wordOp]
        have he : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.const (BitVec.ofNat 64 3)) = some (.val (.word (BitVec.ofNat 64 3))) := rfl
        rw [hd, he]
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_hp0, ↓reduceIte]
        rw [evaluateHOLFiniteState_return]
        simp [evalHOLExact, hs1_nd, shapeOfHOLExact, sizeOfShapeWithContextHOL]
        rfl
      have hr_final : r = some (.returned (.val (.word hp))) := by
        change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_branch)).1 = _
        rw [hbody, hr_eq, hm_eq, hst_eval]
      have hpost_mem : post.memory = Wave8Contracts.M26.updW mpost.memory (hp + BitVec.ofNat 64 0) (BitVec.ofNat 64 3) := by
        change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_branch)).2.memory = _
        rw [hbody, hp_eq, hm_eq, hst_eval]; rfl
      have hpost_glob : post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
        change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_branch)).2.globals = _
        rw [hbody, hp_eq, hm_eq, hst_eval]
        simp [emptyLocalsHOLFinite, s1]; rw [hm_frame.2.2.2.2.2.1]; exact hs0_glob
      have hpost_be : post.be = s.be :=
        (evaluateHOLFiniteState_metadata s (sourceFnBody Guest.Software.guestFn_node_new_branch)).2.2.1
      have hG_post : GuestInv post := guestInv_evaluate s _ hG
      have hpost_hp : globN post "heap_ptr" = q.toNat := by
        unfold globN; rw [hpost_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
        unfold globN; rw [hpost_glob]
        simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
      have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
        unfold globN; rw [hpost_glob]
        simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
      have hA_post : ArenaReady post :=
        ⟨hG_post, arenaOK_update_heap hpost_glob (by have := hA.1; omega) hq_hi hq_al hA⟩
      have hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [← hhp_eq, hpost_hp]; exact hp_le_q
      have hsp_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hpost_sp]
      have hmentry_mem : mentry.memory = s.memory := by
        simp [mentry, callEntryStateHOLFinite, s0, setVarHOLFinite]; rw [hapost_eq]; rfl
      have hmentry_ma : mentry.memaddrs = ordinaryDomain := hs0_G.memaddrs
      have hmem_outside : ∀ a : BitVec 64,
          (a.toNat < hp.toNat ∨ hp.toNat + 176 ≤ a.toNat) → post.memory a = s.memory a := by
        intro a hout
        have hne0 : a ≠ hp + BitVec.ofNat 64 0 := by
          intro heq; rw [heq] at hout; simp at hout
        rw [hpost_mem]
        simp only [Wave8Contracts.M26.updW, if_neg hne0]
        by_cases hchg : mpost.memory a = mentry.memory a
        · rw [hchg, hmentry_mem]
        · have hdom_a : mentry.memaddrs a := hm_frame.2.2.2.2.2.2.2.2.2 a hchg
          rw [hmentry_ma, Wave8Contracts.M26.ordinaryDomain_iff] at hdom_a
          have ha8 : a.toNat % 8 = 0 := hdom_a.2.2
          exfalso
          have hmfr := hm_frame.2.2.2.2.2.2.2.2.1 a
            (fun iv hiv hhit => by
              rw [List.mem_singleton.mp hiv] at hhit
              dsimp [CellHits] at hhit
              rcases hout with h1 | h2 <;> omega)
            (fun hhit => by dsimp [CellHits] at hhit; omega)
          exact hchg hmfr
      have hmem_lt : ∀ a : BitVec 64, a.toNat < globN s "heap_ptr" → post.memory a = s.memory a := by
        intro a hlt; rw [← hhp_eq] at hlt; exact hmem_outside a (Or.inl hlt)
      have hmw_0 : memW post hp.toNat = 3 := by
        have ha0 : BitVec.ofNat 64 hp.toNat = hp + BitVec.ofNat 64 0 := by simp
        unfold memW; rw [ha0, hpost_mem]
        simp [Wave8Contracts.M26.updW]
      have hmw_zero_pos : ∀ off : Nat, 0 < off → off + 8 ≤ 176 → off % 8 = 0 →
          memW post (hp.toNat + off) = 0 := by
        intro off hpos hhi hoff8
        have hlt : hp.toNat + off < 2 ^ 64 := by omega
        have hne0 : BitVec.ofNat 64 (hp.toNat + off) ≠ hp + BitVec.ofNat 64 0 := by
          intro heq
          have := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
          simp at this; omega
        have hmem_eq : post.memory (BitVec.ofNat 64 (hp.toNat + off)) =
            mpost.memory (BitVec.ofNat 64 (hp.toNat + off)) := by
          rw [hpost_mem]; simp only [Wave8Contracts.M26.updW, if_neg hne0]
        have hm_eq_mw : memW post (hp.toNat + off) = memW mpost (hp.toNat + off) := by
          unfold memW; rw [hmem_eq]
        rw [hm_eq_mw]
        exact hzv (hp.toNat + off) (by omega) (by omega) (by omega)
      have hmw_children : ∀ i < 16, memW post (hp.toNat + 32 + 8 * i) = 0 := by
        intro i hi
        have heq : hp.toNat + 32 + 8 * i = hp.toNat + (32 + 8 * i) := by omega
        rw [heq]
        exact hmw_zero_pos (32 + 8 * i) (by omega) (by omega) (by omega)
      have hmw_16 : memW post (hp.toNat + 16) = 0 := hmw_zero_pos 16 (by decide) (by decide) (by decide)
      have hmw_168 : memW post (hp.toNat + 168) = 0 := hmw_zero_pos 168 (by decide) (by decide) (by decide)
      refine ⟨hA_post, hgrow, hsp_le, hp, hr_final, hhp_eq, hhp_al, ?_, hmw_0, hmw_children, hmw_16, hmw_168, ?_⟩
      · rw [hpost_hp, hq_eq]
      · intro Nd hNd
        have hnd_fresh : Inside (nodeIvl post hp.toNat) (globN s "heap_ptr") (globN post "heap_ptr") := by
          dsimp [nodeIvl, Inside]
          rw [hmw_0, show nodeSize 3 = 176 by decide, ← hhp_eq, hpost_hp]
          omega
        obtain ⟨hNd', hkinds⟩ := nodeHeap_cons_fresh hAR hA_post hgrow hpost_be hmem_lt hNd hnd_fresh hhp_al
          (by rw [hmw_0])
          (by rw [hmw_0]; intro h; cases h)
          (by intro _ i hi; rw [hmw_children i hi]; exact Or.inl rfl)
          (by rw [hmw_0]; rintro (h | h) <;> cases h)
          (by rw [hmw_16]; decide)
          (by rw [hmw_0]; intro h; cases h)
          (by intro _; rw [hmw_168]; decide)
        refine ⟨hA_post, hgrow, hsp_le, hpost_be, hNd',
          fun n hn => List.mem_cons_of_mem _ hn, hkinds, ?_, ?_, ?_⟩
        · intro n hn
          rcases List.mem_cons.mp hn with rfl | hold
          · exact Or.inr hnd_fresh
          · exact Or.inl hold
        · apply frameOutside_of_mem_lt_hp hAR
          intro a ha_out
          apply hmem_outside a
          rcases ha_out with h1 | h2
          · rw [← hhp_eq] at h1; exact Or.inl h1
          · exact Or.inr (by omega)
        · intro k hk
          rw [hpost_glob]
          have hne : ofString "heap_ptr" ≠ k := by
            rintro rfl; exact hk (by simp)
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]

/-! ## 7. Branch-slot & branch-value single/pair store helpers -/

/-- Storing `(vptr, vlen)` with `vlen < 2^40` at `(br + 160, br + 168)` of a branch `br ∈ Nd`
(`memW s br = 3`) produces a `NodeStep s post Nd Nd` preserving `br ∈ Nd` and `memW post br = 3`. -/
theorem branch_store_value_step {F : Type}
    {s : PanSemStateFiniteExact 64 F} {Nd : List Nat} {br wvptr wvlen : BitVec 64}
    (ha : ArenaReady s) (hNd : NodeHeap s Nd)
    (hbr_in : br.toNat ∈ Nd) (hbr_k : memW s br.toNat = 3)
    (hvl_lt : wvlen.toNat < 2 ^ 40) :
    let m1 := Wave8Contracts.M26.updW s.memory (br + BitVec.ofNat 64 160) wvptr
    let m2 := Wave8Contracts.M26.updW m1 (br + BitVec.ofNat 64 168) wvlen
    s.memaddrs (br + BitVec.ofNat 64 160) ∧
    s.memaddrs (br + BitVec.ofNat 64 168) ∧
    NodeStep s { s with memory := m2 } Nd Nd ∧
    memW { s with memory := m2 } br.toNat = 3 := by
  intro m1 m2
  have hp := hNd.1 br.toNat hbr_in
  have hins := hp.2.2.1
  have hsz : nodeSize (memW s br.toNat) = 176 := by simp [nodeSize, hbr_k]
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hbr_add : ∀ k : Nat, k ≤ 168 →
      br + BitVec.ofNat 64 k = BitVec.ofNat 64 (br.toNat + k) ∧
      (br + BitVec.ofNat 64 k).toNat = br.toNat + k := by
    intro k hk
    have hlt : br.toNat + k < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hins; omega
    have heq : br + BitVec.ofNat 64 k = BitVec.ofNat 64 (br.toNat + k) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]⟩
  have hdom160 : s.memaddrs (br + BitVec.ofNat 64 160) := by
    obtain ⟨_, hd, _⟩ := hp.2.2.2.1.2.2 20 (by dsimp [nodeIvl]; omega)
    dsimp [nodeIvl] at hd
    rw [(hbr_add 160 (by decide)).1]
    simpa using hd
  have hdom168 : s.memaddrs (br + BitVec.ofNat 64 168) := by
    obtain ⟨_, hd, _⟩ := hp.2.2.2.1.2.2 21 (by dsimp [nodeIvl]; omega)
    dsimp [nodeIvl] at hd
    rw [(hbr_add 168 (by decide)).1]
    simpa using hd
  set post := ({ s with memory := m2 } : PanSemStateFiniteExact 64 F)
  have hne_addr : ∀ (a : Nat) (k : Nat), a < 2 ^ 64 → k ≤ 168 → a ≠ br.toNat + k →
      BitVec.ofNat 64 a ≠ br + BitVec.ofNat 64 k := by
    intro a k ha64 hk hne heq
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64, (hbr_add k hk).2] at this
    exact hne this
  have hmw_other : ∀ off : Nat, off < 160 → memW post (br.toNat + off) = memW s (br.toNat + off) := by
    intro off hoff
    have hlt : br.toNat + off < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hins; omega
    have hne168 := hne_addr (br.toNat + off) 168 hlt (by decide) (by omega)
    have hne160 := hne_addr (br.toNat + off) 160 hlt (by decide) (by omega)
    unfold memW
    change (match m2 (BitVec.ofNat 64 (br.toNat + off)) with | .word w => w.toNat) = _
    simp only [m2, m1, Wave8Contracts.M26.updW, if_neg hne168, if_neg hne160]
  have hmw_168 : memW post (br.toNat + 168) = wvlen.toNat := by
    have ha168 : BitVec.ofNat 64 (br.toNat + 168) = br + BitVec.ofNat 64 168 := (hbr_add 168 (by decide)).1.symm
    unfold memW
    change (match m2 (BitVec.ofNat 64 (br.toNat + 168)) with | .word w => w.toNat) = _
    rw [ha168]; simp [m2, Wave8Contracts.M26.updW]
  have hstep : NodeStep s post Nd Nd := by
    refine nodeStep_modify_node ha hNd hbr_in rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro a hout
      by_cases h168 : a = br + BitVec.ofNat 64 168
      · exfalso; apply hout; rw [h168, (hbr_add 168 (by decide)).2, hsz]; omega
      · by_cases h160 : a = br + BitVec.ofNat 64 160
        · exfalso; apply hout; rw [h160, (hbr_add 160 (by decide)).2, hsz]; omega
        · simp only [post, m2, m1, Wave8Contracts.M26.updW, if_neg h168, if_neg h160]
    · rw [hbr_k]; intro h; cases h
    · intro _ i hi
      have heq : br.toNat + 32 + 8 * i = br.toNat + (32 + 8 * i) := by omega
      rw [heq, hmw_other (32 + 8 * i) (by omega), ← heq]
      exact hp.2.2.2.2.2.1 hbr_k i hi
    · rw [hbr_k]; rintro (h | h) <;> cases h
    · rw [hmw_other 16 (by decide)]; exact hp.2.2.2.2.2.2.2.1
    · rw [hbr_k]; intro h; cases h
    · intro _; rw [hmw_168]; exact hvl_lt
  have hmw0 : memW post br.toNat = 3 := by
    have := hmw_other 0 (by decide)
    simpa [hbr_k] using this
  exact ⟨hdom160, hdom168, hstep, hmw0⟩

/-- Storing a typed child `wch` (`RootIn Nd wch.toNat`) at `br + 32 + idx * 8` where `idx < 16`
on a branch `br ∈ Nd` (`memW s br = 3`) produces a `NodeStep s post Nd Nd` preserving `memW post br = 3`. -/
theorem branch_store_child_step {F : Type}
    {s : PanSemStateFiniteExact 64 F} {Nd : List Nat} {br idx wch : BitVec 64}
    (ha : ArenaReady s) (hNd : NodeHeap s Nd)
    (hbr_in : br.toNat ∈ Nd) (hbr_k : memW s br.toNat = 3)
    (hidx_lt : idx.toNat < 16) (hch_root : RootIn Nd wch.toNat) :
    let slot := br + BitVec.ofNat 64 32 + idx * BitVec.ofNat 64 8
    let m1 := Wave8Contracts.M26.updW s.memory slot wch
    s.memaddrs slot ∧
    NodeStep s { s with memory := m1 } Nd Nd ∧
    memW { s with memory := m1 } br.toNat = 3 := by
  intro slot m1
  have hp := hNd.1 br.toNat hbr_in
  have hins := hp.2.2.1
  have hsz : nodeSize (memW s br.toNat) = 176 := by simp [nodeSize, hbr_k]
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hslot_lt : br.toNat + 32 + 8 * idx.toNat < 2 ^ 64 := by
    dsimp [Inside, nodeIvl] at hins; omega
  have hslot_eq : slot = BitVec.ofNat 64 (br.toNat + (32 + 8 * idx.toNat)) ∧
      slot.toNat = br.toNat + (32 + 8 * idx.toNat) := by
    have heq : slot = BitVec.ofNat 64 (br.toNat + (32 + 8 * idx.toNat)) := by
      dsimp only [slot]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
    exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]⟩
  have hdom_slot : s.memaddrs slot := by
    obtain ⟨_, hd, _⟩ := hp.2.2.2.1.2.2 (4 + idx.toNat) (by dsimp [nodeIvl]; omega)
    dsimp [nodeIvl] at hd
    rw [hslot_eq.1]
    have heq : br.toNat + 8 * (4 + idx.toNat) = br.toNat + (32 + 8 * idx.toNat) := by omega
    rwa [← heq]
  set post := ({ s with memory := m1 } : PanSemStateFiniteExact 64 F)
  have hmw_other : ∀ off : Nat, off ≤ 168 → off ≠ 32 + 8 * idx.toNat →
      memW post (br.toNat + off) = memW s (br.toNat + off) := by
    intro off hoff hne
    have hlt : br.toNat + off < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hins; omega
    have hne_bv : BitVec.ofNat 64 (br.toNat + off) ≠ slot := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, hslot_eq.2] at this
      omega
    unfold memW
    change (match m1 (BitVec.ofNat 64 (br.toNat + off)) with | .word w => w.toNat) = _
    simp only [m1, Wave8Contracts.M26.updW, if_neg hne_bv]
  have hmw_slot : memW post (br.toNat + (32 + 8 * idx.toNat)) = wch.toNat := by
    unfold memW
    change (match m1 (BitVec.ofNat 64 (br.toNat + (32 + 8 * idx.toNat))) with | .word w => w.toNat) = _
    rw [← hslot_eq.1]; simp [m1, Wave8Contracts.M26.updW]
  have hstep : NodeStep s post Nd Nd := by
    refine nodeStep_modify_node ha hNd hbr_in rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro a hout
      by_cases hsl : a = slot
      · exfalso; apply hout; rw [hsl, hslot_eq.2, hsz]; omega
      · simp only [post, m1, Wave8Contracts.M26.updW, if_neg hsl]
    · rw [hbr_k]; intro h; cases h
    · intro _ i hi
      have heq : br.toNat + 32 + 8 * i = br.toNat + (32 + 8 * i) := by omega
      rw [heq]
      by_cases hii : i = idx.toNat
      · subst hii; rw [hmw_slot]; exact hch_root
      · rw [hmw_other (32 + 8 * i) (by omega) (by omega), ← heq]
        exact hp.2.2.2.2.2.1 hbr_k i hi
    · rw [hbr_k]; rintro (h | h) <;> cases h
    · rw [hmw_other 16 (by decide) (by omega)]; exact hp.2.2.2.2.2.2.2.1
    · rw [hbr_k]; intro h; cases h
    · intro _; rw [hmw_other 168 (by decide) (by omega)]; exact hp.2.2.2.2.2.2.2.2.2 hbr_k
  have hmw0 : memW post br.toNat = 3 := by
    have := hmw_other 0 (by decide) (by omega)
    simpa [hbr_k] using this
  exact ⟨hdom_slot, hstep, hmw0⟩

/-- Evaluating `loadByte e` when `e` evaluates to word `wk` and `(wk, len)` satisfies `KeyIn s Nd wk.toNat len`
with `len ≠ 0`: if `loadByte e` succeeds (or directly from `GuestInv s`), it evaluates to a word `< 16`! -/
theorem eval_loadByte_nibble {F : Type}
    {s : PanSemStateFiniteExact 64 F} {Nd : List Nat} {e : ExpHOL 64} {wk : BitVec 64} {len : Nat}
    (hG : GuestInv s) (hKey : KeyIn s Nd wk.toNat len) (hlen : len ≠ 0)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word wk))) :
    ∃ idx : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.loadByte e) =
        some (.val (.word idx)) ∧
      idx.toNat < 16 := by
  obtain ⟨hnib, _, hins, _⟩ := hKey.resolve_left hlen
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhe_ge : heapLimit ≤ heapEnd := by decide
  have hwk_lo : sourceBase ≤ wk.toNat := hins.1
  have hwk_hi : wk.toNat < heapLimit := by dsimp [Inside] at hins; omega
  have hal_nat : (panByteAlignHOL wk).toNat = wk.toNat / 8 * 8 := by
    have hwk_bv : BitVec.ofNat 64 wk.toNat = wk := by simp
    have hb := byteCell_toNat (a := wk.toNat) (by omega)
    rwa [hwk_bv] at hb
  have hsb8 : sourceBase % 8 = 0 := by decide
  have hdom : s.memaddrs (panByteAlignHOL wk) := by
    rw [hG.memaddrs, Wave8Contracts.M26.ordinaryDomain_iff, hal_nat]
    exact ⟨by omega, by omega, by omega⟩
  have hn0 : memB s wk.toNat < 16 := by simpa using hnib 0 (by omega)
  have hwk_bv : BitVec.ofNat 64 wk.toNat = wk := by simp
  unfold memB at hn0
  rw [hwk_bv] at hn0
  rcases hcell : s.memory (panByteAlignHOL wk) with ⟨cw⟩
  rw [hcell] at hn0
  let b := panGetByteHOL wk cw s.be
  change b.toNat < 16 at hn0
  refine ⟨BitVec.ofNat 64 b.toNat, ?_, ?_⟩
  · simp [evalHOLExact, he, panMemLoadByteHOL, hcell, hdom, b]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hn0



/-! ## 8. Read-only / return-bound helper for `common_prefix_length` and `memeq` -/

theorem ro_common_prefix_length_spec : ReadOnlyFn (ofString "common_prefix_length") := by
  let good : MlS → Bool := fun f => f == ofString "min"
  have hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      Wave8Contracts.M15.readOnlyProg good body = true := by
    intro function hfn values body callee rs hfound
    simp only [good, beq_iff_eq] at hfn
    subst hfn
    have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "min")
      _ _ _ _ _ values callee Wave8Contracts.M27.lookup_min hfound
    subst hsame
    rfl
  exact Wave8Contracts.M15.readOnlyFn_of_guestAst 251 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_common_prefix_length rfl good hgood rfl

theorem cpl_body_no_nonTrap_exn {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (eid : MlS) (ev : ValueHOL 64) (hne : eid ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_common_prefix_length)).1 ≠
      some (.exception eid ev) := by
  intro hexn
  have hbody : sourceFnBody Guest.Software.guestFn_common_prefix_length =
      .decCall (ofString "n") .one (ofString "min")
        [.var .local (ofString "al"), .var .local (ofString "bl")]
        (.dec (ofString "i") .one (.const 0)
          (.seq
            (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
              (.seq
                (.ite (.cmp .notEqual
                    (.loadByte (.op .add [.var .local (ofString "a"), .var .local (ofString "i")]))
                    (.loadByte (.op .add [.var .local (ofString "b"), .var .local (ofString "i")])))
                  (.return (.var .local (ofString "i")))
                  .skip)
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
            (.return (.var .local (ofString "n"))))) := rfl
  rw [hbody] at hexn
  obtain ⟨mvals, mbody, mc, _, _, _, hl, hmexn | ⟨mrv, mpost, _, _, _, hcont_eq, _⟩⟩ :=
    decCall_resumes_inv (Or.inr ⟨eid, ev, hexn, hne⟩)
  · obtain ⟨meid, mev, hme, _, _⟩ := hmexn
    have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "min")
      _ _ _ _ _ mvals mc (by rw [hcode]; exact Wave8Contracts.M27.lookup_min) hl
    subst hsame
    exact evaluate_noExnProg _ (by decide) _ meid mev (congrArg Prod.fst hme)
  · rw [hexn] at hcont_eq
    exact evaluate_noExnProg _ (by decide) _ eid ev hcont_eq.symm



end InitECandidate.Solver.Wave8GuestInv.R16Shards
