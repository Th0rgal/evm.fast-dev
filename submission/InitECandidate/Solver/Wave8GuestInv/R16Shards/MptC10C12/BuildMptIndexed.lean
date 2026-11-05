import InitECandidate.Solver.Wave8GuestInv.ContractParts.C11
import InitECandidate.Solver.Wave8GuestInv.MergedLeaves
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbCore
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_Exec
import InitECandidate.Solver.Wave8GuestInv.R13Shards.NodeRlpKeep
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptRoot
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_NodeHash
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_NodeRlp
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptSet
import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptSet_Memory
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PrimC08Closure
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.RlpHelpers
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_scratch_alloc

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

namespace ArenaNodeRlp

theorem straight (p : ProgHOL 64) (h : extStraightLine p = true) :
    TerminatingProgBoundedOn GuestInv p 0 :=
  fun s hc _ => TerminatingProgBounded.straight p h s hc

theorem weakenGuard {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {k : Nat} (h : TerminatingProgBoundedOn Q p k)
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s) :
    TerminatingProgBoundedOn P p k := fun s hc hP => h s hc (hp s hP)

theorem call_ro {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} (hP : LocalsOnly names P)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    {f : MlS} (h : ReadOnlyFn f) (args : List (ExpHOL 64)) :
    Hoare P (.call (some (none, none)) f args) (fun r t => r = none → P t) := by
  apply Hoare.call0 h (callEntryOn_of_imp localsFree_guestInv hPG _ _)
  · intro F s callee post v hc hPs hq _
    rw [hq (Or.inl ⟨v, rfl⟩)]
    exact hP s s.locals post.clock (fun _ _ => rfl) hPs
  · intro F r t hr _ he
    exact False.elim (hr he)

theorem lookup_fill : originalRuntimeCode.lookup (ofString "_node_rlp_fill") =
    some ((sourceFunctionEntry Guest.Software.guestFn__node_rlp_fill).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 284 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_fill) rfl

theorem lookup_rlp : originalRuntimeCode.lookup (ofString "node_rlp") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_rlp).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 285 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_rlp) rfl

theorem lookup_hash : originalRuntimeCode.lookup (ofString "node_hash") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_hash).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 290 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_hash) rfl

theorem lookup_root : originalRuntimeCode.lookup (ofString "mpt_root") =
    some ((sourceFunctionEntry Guest.Software.guestFn_mpt_root).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 291 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_root) rfl

theorem localsOnly_arena : LocalsOnly [] ArenaReady :=
  fun s locals k _ h => localsFree_arenaReady s locals k h

theorem arena_entry (fname : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn ArenaReady ArenaReady fname args :=
  callEntryOn_of_imp localsFree_arenaReady (fun _ h => h) fname args

theorem node_rlp_arena
    (hf : TerminatingFunBoundedOn ArenaReady (ofString "_node_rlp_fill") K.«_node_rlp_fill»)
    (hm : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»)
    (hr : ReadOnlyFn (ofString "mpt_fail")) :
    TerminatingFunBoundedOn ArenaReady (ofString "node_rlp") K.«node_rlp» := by
  refine ⟨_, _, _, lookup_rlp, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_rlp,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals localsOnly_arena _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (weakenGuard (straight _ rfl) (fun s h => h.1))
        (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.seq_hoare
          (TerminatingProgBoundedOn.ite_on
            (TerminatingProgBoundedOn.call_on hm _ _
              (callEntryOn_of_imp localsFree_guestInv (fun s h => h.1) _ _))
            (weakenGuard (straight _ rfl) (fun s h => h.1)))
          (Hoare.ite
            (Hoare.mono (call_ro localsOnly_arena (fun s h => h.1) hr _) (fun s h => h.1))
            (Hoare.skip (fun s h _ => h.1)) (fun _ _ h => absurd h (by simp)))
          (TerminatingProgBoundedOn.seq_guestInv_after
            (TerminatingProgBoundedOn.call_on hf _ _ (arena_entry _ _))
            (fun s h => h.1)
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«node_rlp»
  simp only [Nat.max_def]
  split <;> omega

theorem node_hash_arena
    (ha : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hk : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (hn : TerminatingFunBoundedOn ArenaReady (ofString "node_rlp") K.«node_rlp») :
    TerminatingFunBoundedOn ArenaReady (ofString "node_hash") K.«node_hash» := by
  refine ⟨_, _, _, lookup_hash, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_hash,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals localsOnly_arena _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (weakenGuard (straight _ rfl) (fun s h => h.1))
        (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.decCall_on hn _ _ _ (arena_entry _ _)
          (decCallResumeOn_guestInv (fun s h => h.1) _ _ _)
          (TerminatingProgBoundedOn.decCall_guestInv ha _ _ _
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.call_guestInv hk _ _)
              (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
                (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))) ?_
  unfold K.«node_hash»
  omega

theorem mpt_root_arena
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hn : TerminatingFunBoundedOn ArenaReady (ofString "node_hash") K.«node_hash») :
    TerminatingFunBoundedOn ArenaReady (ofString "mpt_root") K.«mpt_root» := by
  refine ⟨_, _, _, lookup_root, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_mpt_root,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals localsOnly_arena _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.ite_on
          (weakenGuard
            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hm _ _)
              (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))
            (fun s h => h.1))
          (weakenGuard (straight _ rfl) (fun s h => h.1)))
        (Hoare.ite
          ⟨fun s hc hP hnt he => by
            rw [evaluateHOLFiniteState_seq_line780] at he
            dsimp only at he
            split at he
            · exact False.elim (return_ne_none _ _ he)
            · simp_all⟩
          (Hoare.skip (fun s h _ => h.1)) (fun _ _ h => absurd h (by simp)))
        (TerminatingProgBoundedOn.decCall_on hn _ _ _ (arena_entry _ _)
          (decCallResumeOn_guestInv (fun s h => h.1) _ _ _)
          (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hm _ _)
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«mpt_root»
  simp only [Nat.max_def]
  split <;> omega

end ArenaNodeRlp

section RelaxedMpt

def RelaxedNodeHeap {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : Prop :=
  (∀ n ∈ Nd, memW s n ≤ 3 ∧ Allocated s (nodeIvl s n) ∧ Inside (nodeIvl s n) sourceBase heapLimit ∧
    WordsOK s (nodeIvl s n) ∧
    (memW s n = 2 → RootIn Nd (memW s (n + 48))) ∧
    (memW s n = 3 → ∀ i, i < 16 → RootIn Nd (memW s (n + 32 + 8 * i))) ∧
    ((memW s n = 1 ∨ memW s n = 2) → KeyIn s Nd (memW s (n + 32)) (memW s (n + 40))) ∧
    memW s (n + 16) < 2 ^ 40) ∧
  (∀ n ∈ Nd, ∀ m ∈ Nd, n ≠ m → Disj (nodeIvl s n) (nodeIvl s m))

def RelaxedNodeRlpReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, RelaxedNodeHeap s Nd ∧ RootIn Nd (locN s "node")

def RelaxedMptObjInWith {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nm : List Nat) (m : Nat) : Prop :=
  Allocated s (m, 16) ∧ WordsOK s (m, 16) ∧
  (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (m, 16) i) ∧
  (∀ j ∈ fixedObjects s, Disj (m, 16) j) ∧
  RelaxedNodeHeap s Nm ∧ RootIn Nm (memW s m) ∧
    ∀ o ∈ nodeExtents s Nm, Disj o (m, 16) ∧
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧
      ∀ j ∈ fixedObjects s, Disj o j

def RelaxedMptObjIn {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  ∃ Nm, RelaxedMptObjInWith s S Nm (locN s "m")

def RelaxedMptObjAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧ RelaxedMptObjIn s S ∧ (∀ i ∈ R s,
    (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj i j) ∧ ∀ j ∈ fixedObjects s, Disj i j) ∧
    AvoidsTries s S ((locN s "m", 16) :: R s) ∧
    ∃ Nm Nd, RelaxedMptObjInWith s S Nm (locN s "m") ∧ TriesTypedWith s S Nd ∧
      ∀ o ∈ (locN s "m", 16) :: R s ++ nodeExtents s Nm, ∀ j ∈ nodeExtents s Nd, Disj o j

def RelaxedMptObjReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => RelaxedMptObjAvoids (fun _ => []) s

def RelaxedMptSetReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => RelaxedMptObjReady s ∧ locN s "klen" ≤ 32

theorem relaxedNodeHeap_of_nodeHeap {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (h : NodeHeap s Nd) : RelaxedNodeHeap s Nd := by
  refine ⟨fun n hn => ?_, h.2⟩
  obtain ⟨hk, ha, hi, hw, h2, h3, hkey, hrl, _, _⟩ := h.1 n hn
  exact ⟨hk, ha, hi, hw, h2, h3, hkey, hrl⟩

theorem relaxedMptObjInWith_of_mptObjInWith {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nm : List Nat} {m : Nat} (h : MptObjInWith s S Nm m) : RelaxedMptObjInWith s S Nm m :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, relaxedNodeHeap_of_nodeHeap h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem relaxedNodeIvl_aligned {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hNh : RelaxedNodeHeap s Nd) {n : Nat} (hn : n ∈ Nd) :
    (nodeIvl s n).1 % 8 = 0 ∧ (nodeIvl s n).2 % 8 = 0 := by
  obtain ⟨_, _, _, hwo, _, _, _, _⟩ := hNh.1 n hn
  refine ⟨hwo.1, ?_⟩
  dsimp [nodeIvl, nodeSize]
  split_ifs <;> decide

theorem relaxedNodeIvl_pos {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) :
    0 < (nodeIvl s n).2 := by
  dsimp [nodeIvl, nodeSize]
  split_ifs <;> decide

theorem relaxedNodeIvl_lt_heap_ptr {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hA : ArenaOK s) (hNh : RelaxedNodeHeap s Nd) {n : Nat} (hn : n ∈ Nd) :
    sourceBase ≤ n ∧ n + (nodeIvl s n).2 ≤ globN s "heap_ptr" := by
  obtain ⟨_, hal, hin, _, _, _, _, _⟩ := hNh.1 n hn
  rcases hal with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact ⟨h1, h2⟩
  · have hsep : heapLimit ≤ scratchStart := by decide
    have hpos := relaxedNodeIvl_pos s n
    have h2 := hin.2
    have hsp := hA.2.2.1
    have hfm := hA.2.2.2.1
    dsimp [nodeIvl] at h1 h2 hpos
    omega

theorem relaxedNodeHeap_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post)
    {Nd : List Nat} (hN : RelaxedNodeHeap s Nd)
    (hu : ∀ o ∈ nodeExtents s Nd, o.2 ≠ 0 → P3MptSet.IvlUnhit s post o) :
    RelaxedNodeHeap post Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hn_props : ∀ n ∈ Nd,
      memW post n = memW s n ∧
      nodeIvl post n = nodeIvl s n ∧
      (∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k)) ∧
      ((memW s n = 1 ∨ memW s n = 2) → KeyIn post Nd (memW post (n + 32)) (memW post (n + 40))) := by
    intro n hn
    obtain ⟨hk3, hal_n, hin_n, hw_n, _, _, hkey_n, _⟩ := hN.1 n hn
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    have hn8 : n % 8 = 0 := hw_n.1
    have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
    have hu_n : P3MptSet.IvlUnhit s post (n, nodeSize (memW s n)) :=
      hu _ (by unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩) (by dsimp only; omega)
    have hw_k : ∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k) := by
      intro k hk
      have hsz8 : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> omega
      exact P3MptSet.memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by omega, by omega⟩
    have hw0 : memW post n = memW s n := by simpa using hw_k 0 (by omega)
    have hivl_eq : nodeIvl post n = nodeIvl s n := by simp [nodeIvl, hw0]
    exact ⟨hw0, hivl_eq, hw_k, fun h12 => by
      have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize
        rcases h12 with h1 | h2
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
          have hu_p : P3MptSet.IvlUnhit s post (memW s (n + 32), memW s (n + 40)) :=
            hu _ (by unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩) hlen0
          refine ⟨fun k hk => ?_, hag.allocated hal_p, hin_p, ?_⟩
          · rw [P3MptSet.memB_eq_of_ivlUnhit hu_p hbe (by have := hin_p.2; omega) ⟨by omega, by omega⟩]
            exact hnib k hk
          · intro m hm
            have hhm_hi : m + nodeSize (memW s m) ≤ 2 ^ 64 := by
              have := (hN.1 m hm).2.2.1.2; dsimp [nodeIvl] at this; omega
            have hm8 : m % 8 = 0 := (hN.1 m hm).2.2.2.1.1
            have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
            have hu_m : P3MptSet.IvlUnhit s post (m, nodeSize (memW s m)) :=
              hu _ (by unfold nodeExtents; exact List.mem_flatMap.2 ⟨m, hm, by simp [nodeIvl]⟩) (by dsimp only; omega)
            have hwm : memW post m = memW s m :=
              P3MptSet.memW_eq_of_ivlUnhit hu_m hm8 hhm_hi ⟨by omega, by omega⟩
            simp [nodeIvl, hwm]
            exact hdisj_p m hm⟩
  refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
  · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, _, hcache⟩ := hN.1 n hn
    obtain ⟨hw0, hivl_eq, hw_k, hkey_post⟩ := hn_props n hn
    rw [hw0, hivl_eq]
    refine ⟨hk3, hag.allocated hal_n, hin_n, P3MptSet.wordsOK_transfer hgS hgP hw_n, ?_, ?_, hkey_post, ?_⟩
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
      have he := hw_k 2 (by omega)
      simpa only [Nat.reduceMul, he] using hcache
  · rw [(hn_props n hn).2.1, (hn_props m hm).2.1]
    exact hN.2 n hn m hm hne

end RelaxedMpt

section LeafAdapters

theorem ro_mpt_fail_local : ReadOnlyFn (ofString "mpt_fail") := by
  obtain ⟨params, body, rs, hl, hrun⟩ :=
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves.«ro_mpt_fail»
  refine ⟨params, body, rs, hl, ?_⟩
  intro F s hc hs hval hnt hres
  exact hrun s hc hs hval hnt hres

theorem ro__node_needs_rlp_local : ReadOnlyFn (ofString "_node_needs_rlp") := by
  obtain ⟨params, body, rs, hl, hrun⟩ :=
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves.«ro__node_needs_rlp»
  refine ⟨params, body, rs, hl, ?_⟩
  intro F s hc hs hval hnt hres
  exact hrun s hc hs hval hnt hres

theorem ro_nodedb_lookup_local : ReadOnlyFn (ofString "nodedb_lookup") := by
  obtain ⟨params, body, rs, hl, hrun⟩ :=
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves.«ro_nodedb_lookup»
  refine ⟨params, body, rs, hl, ?_⟩
  intro F s hc hs hval hnt hres
  exact hrun s hc hs hval hnt hres

theorem rt_scratch_alloc_local :
    Returns ArenaReady
      (fun s post p =>
        (p % 8 = 0 ∧ globN s "frame_mem_ptr" ≤ p ∧
          Inside (p, (locN s "n" + 7) / 8 * 8) (globN post "scratch_ptr") (globN s "scratch_ptr") ∧
          WordsOK post (p, (locN s "n" + 7) / 8 * 8)) ∧
        globN post "scratch_ptr" = p)
      (ofString "scratch_alloc") := by
  obtain ⟨params, body, rs, hl, hrun⟩ := InitECandidate.Solver.Wave8Contracts.M26.«rt_scratch_alloc»
  refine ⟨params, body, rs, hl, ?_⟩
  intro F s hc hs hval hnt v hret
  obtain ⟨w, rfl, hA, hAG, hFS, hp⟩ := hrun s hc hs hval hnt v hret
  exact ⟨w, rfl, hA, hAG, ⟨hFS.1, hFS.2.1, hFS.2.2.1, hFS.2.2.2⟩, hp⟩

end LeafAdapters

section RelaxedNodeRlpStack

private theorem localsOnly_relaxedNodeRlpReady : LocalsOnly ["node"] RelaxedNodeRlpReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "node" (hl "node" (by simp))
  simp only [RelaxedNodeRlpReady, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

private theorem entry_relaxedNodeRlpReady {fname : MlS} {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e)
    (hp : e.1 = [(ofString "node", .one)]) :
    CallEntryOn RelaxedNodeRlpReady RelaxedNodeRlpReady fname [.var .local (ofString "node")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "node") .one b r
    (by rw [hcode]; exact hl) values body' callee ret' hargs hlook
  exact localsOnly_relaxedNodeRlpReady state callee (state.clock - 1) (by simpa using hc) hP

private theorem lookup_fill_rel : originalRuntimeCode.lookup (ofString "_node_rlp_fill") =
    some ((sourceFunctionEntry Guest.Software.guestFn__node_rlp_fill).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 284 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_fill) rfl

private theorem lookup_rlp_rel : originalRuntimeCode.lookup (ofString "node_rlp") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_rlp).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 285 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_rlp) rfl

private theorem lookup_hash_rel : originalRuntimeCode.lookup (ofString "node_hash") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_hash).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 290 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_hash) rfl

private theorem lookup_root_rel : originalRuntimeCode.lookup (ofString "mpt_root") =
    some ((sourceFunctionEntry Guest.Software.guestFn_mpt_root).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 291 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_root) rfl

theorem node_rlp_relaxed
    (hf : TerminatingFunBoundedOn RelaxedNodeRlpReady (ofString "_node_rlp_fill") K.«_node_rlp_fill»)
    (hm : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»)
    (hr : ReadOnlyFn (ofString "mpt_fail")) :
    TerminatingFunBoundedOn RelaxedNodeRlpReady (ofString "node_rlp") K.«node_rlp» := by
  refine ⟨_, _, _, lookup_rlp_rel, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_rlp,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals localsOnly_relaxedNodeRlpReady _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (ArenaNodeRlp.weakenGuard (ArenaNodeRlp.straight _ rfl) (fun s h => h.1.1))
        (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.seq_hoare
          (TerminatingProgBoundedOn.ite_on
            (TerminatingProgBoundedOn.call_on hm _ _
              (callEntryOn_of_imp localsFree_guestInv (fun s h => h.1.1) _ _))
            (ArenaNodeRlp.weakenGuard (ArenaNodeRlp.straight _ rfl) (fun s h => h.1.1)))
          (Hoare.ite
            (Hoare.mono (ArenaNodeRlp.call_ro localsOnly_relaxedNodeRlpReady (fun s h => h.1.1) hr _) (fun s h => h.1))
            (Hoare.skip (fun s h _ => h.1)) (fun _ _ h => absurd h (by simp)))
          (TerminatingProgBoundedOn.seq_guestInv_after
            (TerminatingProgBoundedOn.call_on hf _ _ (entry_relaxedNodeRlpReady lookup_fill_rel (by rfl)))
            (fun s h => h.1.1)
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«node_rlp»
  simp only [Nat.max_def]
  split <;> omega

theorem node_hash_relaxed
    (ha : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hk : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (hn : TerminatingFunBoundedOn RelaxedNodeRlpReady (ofString "node_rlp") K.«node_rlp») :
    TerminatingFunBoundedOn RelaxedNodeRlpReady (ofString "node_hash") K.«node_hash» := by
  refine ⟨_, _, _, lookup_hash_rel, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_hash,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals localsOnly_relaxedNodeRlpReady _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (ArenaNodeRlp.weakenGuard (ArenaNodeRlp.straight _ rfl) (fun s h => h.1.1))
        (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.decCall_on hn _ _ _ (entry_relaxedNodeRlpReady lookup_rlp_rel (by rfl))
          (decCallResumeOn_guestInv (fun s h => h.1.1) _ _ _)
          (TerminatingProgBoundedOn.decCall_guestInv ha _ _ _
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.call_guestInv hk _ _)
              (TerminatingProgBoundedOn.seq_guestInv (ArenaNodeRlp.straight _ rfl)
                (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))) ?_
  unfold K.«node_hash»
  omega

private def RelaxedRootReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, RelaxedNodeHeap s Nd ∧ RootIn Nd (locN s "root")

private theorem evalAt_loadL'_rel {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString g), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (locN t g + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hg : t.locals.lookup (ofString g) with _ | v
  · simp [hg] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [locN, memW, hg, hadd, h.2]
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

private theorem evalAt_loadL_rel {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (locN t g + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hg : t.locals.lookup (ofString g) with _ | w
    · simp [hg] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hg, valueIsWord] at h
      · simp [hg, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  exact ⟨a, rfl, evalAt_loadL'_rel t g k a h⟩

private theorem callee_param_alias_rel {F : Type} (state : PanSemStateFiniteExact 64 F) (fname pk caller : MlS)
    (sk : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(pk, sk)], body, ret))
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local caller] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup pk = state.locals.lookup caller := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, evalHOLExact] at hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    rcases hv : state.locals.lookup caller with _ | v
    · rw [hv] at hargs; cases hargs
    · rw [hv] at hargs
      cases hargs
      split at raw
      · have rawEq := Option.some.inj raw
        rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
        rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
        subst hloc
        simp
      · cases raw

private theorem dec_guard_rel {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {k : Nat}
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s init = some v → Q (setVarHOLFinite name v s))
    (hb : TerminatingProgBoundedOn Q body k) :
    TerminatingProgBoundedOn P (.dec name shape init body) k := by
  intro F s hc hP hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rename_i v hv
    revert hnt
    split <;> intro hnt
    · have h := hb (setVarHOLFinite name v s) hc (hi s v hP hv) hnt
      simpa only [setVarHOLFinite] using h
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

private theorem relaxedRoot_init {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hs : RelaxedMptObjReady s)
    (hv : evalAt s (.load .one (.op .add [.var .local (ofString "m"), .const 0])) = some v) :
    RelaxedRootReady (setVarHOLFinite (ofString "root") v s) := by
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL_rel s "m" 0 v hv
  obtain ⟨ha, S, _hS, ⟨Nd, hm⟩, _rest⟩ := hs
  refine ⟨localsFree_arenaReady s _ _ ha, Nd, hm.2.2.2.2.1, ?_⟩
  rw [locN_setVar_same, hw]
  simpa using hm.2.2.2.2.2.1

private theorem relaxedRoot_entry :
    CallEntryOn RelaxedRootReady RelaxedNodeRlpReady (ofString "node_hash") [.var .local (ofString "root")] := by
  intro F s vs b callee r hc hP hargs hl
  have hp := callee_param_alias_rel s (ofString "node_hash") (ofString "node") (ofString "root")
    .one _ _ (by rw [hc]; exact lookup_hash_rel) vs b callee r hargs hl
  refine ⟨localsFree_arenaReady s _ _ hP.1, ?_⟩
  have hx : locN (callEntryStateHOLFinite s callee) "node" = locN s "root" := by
    simp only [locN, callEntryStateHOLFinite, hp]
  rw [hx]
  exact hP.2

theorem mpt_root_relaxed
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hn : TerminatingFunBoundedOn RelaxedNodeRlpReady (ofString "node_hash") K.«node_hash») :
    TerminatingFunBoundedOn RelaxedMptObjReady (ofString "mpt_root") K.«mpt_root» := by
  refine ⟨_, _, _, lookup_root_rel, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_mpt_root,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (dec_guard_rel _ _ _ relaxedRoot_init
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.ite_on
          (ArenaNodeRlp.weakenGuard
            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hm _ _)
              (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))
            (fun s h => h.1.1))
          (ArenaNodeRlp.weakenGuard (ArenaNodeRlp.straight _ rfl) (fun s h => h.1.1)))
        (Hoare.ite
          ⟨fun s hc hP hnt he => by
            rw [evaluateHOLFiniteState_seq_line780] at he
            dsimp only at he
            split at he
            · exact False.elim (return_ne_none _ _ he)
            · simp_all⟩
          (Hoare.skip (fun s h _ => h.1)) (fun _ _ h => absurd h (by simp)))
        (TerminatingProgBoundedOn.decCall_on hn _ _ _ relaxedRoot_entry
          (decCallResumeOn_guestInv (fun s h => h.1.1) _ _ _)
          (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hm _ _)
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«mpt_root»
  simp only [Nat.max_def]
  split <;> omega

/-! ### Outer & inner loop bounds for `_node_rlp_fill` -/

def scanCond : ExpHOL 64 :=
  .op .and [.cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.const 16)),
    .cmp .notEqual (.const 0) (.cmp .equal (.var .local (ofString "found")) (.const 0))]

def scanBody : ProgHOL 64 :=
  .seq (.assign .local (ofString "child")
    (.load .one (.op .add [.var .local (ofString "nd"), .const 32,
      .panop .mul [.var .local (ofString "i"), .const 8]])))
    (.seq (.assign .local (ofString "i")
      (.op .add [.var .local (ofString "i"), .const 1]))
      (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
        [.var .local (ofString "child")]))

def ScanReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ locN s "i" ≤ 16

theorem seq_none_rel {F : Type} (s : PanSemStateFiniteExact 64 F) (p q : ProgHOL 64)
    (h : (evaluateHOLFiniteState s (.seq p q)).1 = none) :
    (evaluateHOLFiniteState s p).1 = none ∧
    (evaluateHOLFiniteState (evaluateHOLFiniteState s p).2 q).1 = none ∧
    (evaluateHOLFiniteState s (.seq p q)).2 =
      (evaluateHOLFiniteState (evaluateHOLFiniteState s p).2 q).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at h ⊢
  rcases hr : evaluateHOLFiniteState s p with ⟨r, t⟩
  simp only [hr] at h ⊢
  cases r with
  | none => exact ⟨rfl, h, rfl⟩
  | some r => simp at h

private theorem scan_advance {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (w : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hn : (evaluateHOLFiniteState s scanBody).1 = none) :
    (evaluateHOLFiniteState s scanBody).2.locals.lookup (ofString "i") =
      some (.val (.word (w + 1))) := by
  unfold scanBody at hn ⊢
  obtain ⟨hn1, hn2, heq⟩ := seq_none_rel _ _ _ hn
  rw [heq]
  obtain ⟨hn3, hn4, heq2⟩ := seq_none_rel _ _ _ hn2
  rw [heq2]
  rw [evaluate_avoidsLocal_flowing (ofString "i") _ (by decide) _ (Or.inl hn4)]
  have hkeep := evaluate_avoidsLocal_flowing (ofString "i") _ (by decide) s (Or.inl hn1)
  have hcount : CountedBody (ofString "i") 1
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) 0 :=
    CountedBody.incr
  exact (hcount.run _ ((evaluateHOLFiniteState_metadata s _).1.trans hc) w
    (hkeep.trans hi) (Nat.zero_le _)).2.2.2.2 hn3 |>.1

private theorem scan_active {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : ScanReady s)
    (ha : LoopActive scanCond s) :
    ∃ w : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word w)) ∧ w.toNat < 16 := by
  obtain ⟨word, he, hw⟩ := ha
  rw [evalHOLFinite_eq_toExact] at he
  rcases hi : s.locals.lookup (ofString "i") with _ | vi
  · simp [scanCond, evalHOLExact, evalListHOLExact, hi] at he
  · rcases vi with ⟨⟨i⟩⟩ | fs | ⟨n, fs⟩
    · have hle : i.toNat ≤ 16 := by simpa [ScanReady, locN, hi] using hP.2
      refine ⟨i, rfl, ?_⟩
      by_contra hn
      have hi16 : i = 16 := BitVec.eq_of_toNat_eq (by simpa using (show i.toNat = 16 by omega))
      subst hi16
      rcases hf : s.locals.lookup (ofString "found") with _ | vf
      · simp [scanCond, evalHOLExact, evalListHOLExact, hi, hf] at he
      · rcases vf with ⟨⟨f⟩⟩ | fs | ⟨n, fs⟩ <;>
          simp [scanCond, evalHOLExact, evalListHOLExact, hi, hf,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
            Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, valueIsWord, valueWord,
            wordOpHOL, wordOp] at he
        exact hw he.symm
    · simp [scanCond, evalHOLExact, evalListHOLExact, hi] at he
    · simp [scanCond, evalHOLExact, evalListHOLExact, hi] at he

private theorem scan_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hP : ScanReady s) (ha : LoopActive scanCond s)
    (hnone : (evaluateHOLFiniteState (decClockHOLFinite s) scanBody).1 = none) :
    ScanReady (evaluateHOLFiniteState (decClockHOLFinite s) scanBody).2 ∧
      16 - locN (evaluateHOLFiniteState (decClockHOLFinite s) scanBody).2 "i" <
        16 - locN s "i" := by
  obtain ⟨i, hi, hil⟩ := scan_active s hP ha
  have hnew := scan_advance (decClockHOLFinite s) hc i hi hnone
  have hadd : (i + 1).toNat = i.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change i.toNat + 1 < 2^64; omega)
  have hnloc : locN (evaluateHOLFiniteState (decClockHOLFinite s) scanBody).2 "i" =
      i.toNat + 1 := by simp only [locN, hnew, hadd]
  have hiloc : locN s "i" = i.toNat := by simp only [locN, hi]
  refine ⟨⟨guestInv_evaluate _ _ (guestInv_congr (s := s) rfl rfl rfl rfl hP.1), ?_⟩, ?_⟩
  · rw [hnloc]; omega
  · rw [hnloc, hiloc]; omega

private theorem scan_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp») :
    TerminatingProgBoundedOn ScanReady (.while scanCond scanBody)
      ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) := by
  apply TerminatingProgBoundedOn.while_rank (fun s => 16 - locN s "i")
  · intro F s hP
    exact ⟨guestInv_congr (s := s) rfl rfl rfl rfl hP.1, hP.2⟩
  · refine ArenaNodeRlp.weakenGuard (P := ScanReady) (Q := GuestInv) ?_ (fun s h => h.1)
    unfold scanBody
    refine TerminatingProgBoundedOn.mono_bound
      (TerminatingProgBoundedOn.seq_guestInv (ArenaNodeRlp.straight _ rfl)
        (TerminatingProgBoundedOn.seq_guestInv (ArenaNodeRlp.straight _ rfl)
          (TerminatingProgBoundedOn.call_guestInv hn _ _))) (by omega)
  · intro F s hc hP ha
    exact Nat.sub_le _ _
  · intro F s hc hP ha hf
    have hnc := evaluate_noTopContinue scanBody (by rfl) (decClockHOLFinite s)
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) scanBody).1 = none :=
      hf.elim id (fun h => False.elim (hnc h))
    exact scan_step s hc hP ha hnone

def ScanEntry : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ memW s (locN s "top" + 16) ≤ 16

private theorem scanEntry_locals : LocalsOnly ["top"] ScanEntry := by
  intro F s ls k hl hs
  have ht : locN { s with locals := ls, clock := k } "top" = locN s "top" := by
    simp only [locN, hl "top" (by simp)]
  refine ⟨guestInv_with_locals_clock s ls k hs.1, ?_⟩
  change memW s (locN { s with locals := ls, clock := k } "top" + 16) ≤ 16
  rw [ht]
  exact hs.2

def scanProgram : ProgHOL 64 :=
  .dec (ofString "i") .one (.load .one (.op .add [.var .local (ofString "top"), .const 16]))
    (.seq (.while scanCond scanBody)
      (.store (.op .add [.var .local (ofString "top"), .const 16]) (.var .local (ofString "i"))))

private theorem scan_program_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp») :
    TerminatingProgBoundedOn ScanEntry scanProgram
      ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) := by
  unfold scanProgram
  refine TerminatingProgBoundedOn.mono_bound (dec_guard_rel _ _ _ ?_
    (TerminatingProgBoundedOn.seq_guestInv_after (scan_bound hn) (fun s h => h.1)
      (ArenaNodeRlp.straight _ rfl))) (by omega)
  intro F s v hs hv
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL_rel s "top" 16 v hv
  refine ⟨guestInv_setVar _ _ _ hs.1, ?_⟩
  have hloc : locN (setVarHOLFinite (ofString "i") (.val (.word w)) s) "i" = w.toNat := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [hloc, hw]
  simpa using hs.2

def fillBody : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn__node_rlp_fill with
  | .decCall _ _ _ _ (.decCall _ _ _ _
      (.seq _ (.seq _ (.seq _ (.seq _ (.dec _ _ _ (.seq (.while _ b) _))))))) => b
  | _ => .skip

def fillSearch : ProgHOL 64 :=
  match fillBody with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq p _)))) => p
  | _ => .skip

def fillTail : ProgHOL 64 :=
  match fillBody with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq _ p)))) => p
  | _ => .skip

private theorem fillSearch_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp») :
    TerminatingProgBoundedOn ScanEntry fillSearch
      (max (max (K.«_node_needs_rlp» + 1) 0)
        (max ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) 0)) := by
  change TerminatingProgBoundedOn ScanEntry
    (.ite _ (.ite _ (.seq _ (.seq _ (.call _ _ _))) .skip)
      (.ite _ scanProgram .skip)) _
  apply TerminatingProgBoundedOn.ite_on
  · apply TerminatingProgBoundedOn.ite_on
    · refine ArenaNodeRlp.weakenGuard (P := ScanEntry) (Q := GuestInv) ?_ (fun s h => h.1)
      exact TerminatingProgBoundedOn.mono_bound
        (TerminatingProgBoundedOn.seq_guestInv (ArenaNodeRlp.straight _ rfl)
          (TerminatingProgBoundedOn.seq_guestInv (ArenaNodeRlp.straight _ rfl)
            (TerminatingProgBoundedOn.call_guestInv hn _ _))) (by omega)
    · exact ArenaNodeRlp.weakenGuard (ArenaNodeRlp.straight _ rfl) (fun s h => h.1)
  · exact TerminatingProgBoundedOn.ite_on (scan_program_bound hn)
      (ArenaNodeRlp.weakenGuard (ArenaNodeRlp.straight _ rfl) (fun s h => h.1))

private theorem fillTail_bound
    (ha : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    (hb : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish») :
    TerminatingProgBoundedOn GuestInv fillTail
      (max ((K.«scratch_alloc» + 1) + (K.«_node_rlp_begin» + 1)) (K.«_node_rlp_finish» + 1)) := by
  change TerminatingProgBoundedOn GuestInv (.ite _ (.decCall _ _ _ _
    (.seq _ (.seq _ (.seq _ (.seq (.call _ _ _) (.assign _ _ _))))))
    (.seq (.call _ _ _) (.assign _ _ _))) _
  apply TerminatingProgBoundedOn.ite_on
  · refine TerminatingProgBoundedOn.mono_bound
      (TerminatingProgBoundedOn.decCall_guestInv ha _ _ _
        (TerminatingProgBoundedOn.seq_guestInv (ArenaNodeRlp.straight _ rfl)
          (TerminatingProgBoundedOn.seq_guestInv (ArenaNodeRlp.straight _ rfl)
            (TerminatingProgBoundedOn.seq_guestInv (ArenaNodeRlp.straight _ rfl)
              (TerminatingProgBoundedOn.seq_guestInv
                (TerminatingProgBoundedOn.call_guestInv hb _ _) (ArenaNodeRlp.straight _ rfl)))))) (by omega)
  · exact TerminatingProgBoundedOn.mono_bound
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.call_guestInv hf _ _) (ArenaNodeRlp.straight _ rfl)) (by omega)

def fillBodyCost : Nat :=
  max (max (K.«_node_needs_rlp» + 1) 0)
    (max ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) 0) +
  max ((K.«scratch_alloc» + 1) + (K.«_node_rlp_begin» + 1)) (K.«_node_rlp_finish» + 1)

private theorem fillBody_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp»)
    (ha : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    (hb : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish») :
    TerminatingProgBoundedOn ScanEntry fillBody fillBodyCost := by
  change TerminatingProgBoundedOn ScanEntry (.dec _ _ _ (.dec _ _ _ (.dec _ _ _
    (.dec _ _ _ (.seq fillSearch fillTail))))) _
  exact TerminatingProgBoundedOn.dec_onLocals scanEntry_locals _ (by decide) _ _
    (TerminatingProgBoundedOn.dec_onLocals scanEntry_locals _ (by decide) _ _
      (TerminatingProgBoundedOn.dec_onLocals scanEntry_locals _ (by decide) _ _
        (TerminatingProgBoundedOn.dec_onLocals scanEntry_locals _ (by decide) _ _
          (TerminatingProgBoundedOn.seq_guestInv_after (fillSearch_bound hn) (fun s h => h.1)
            (fillTail_bound ha hb hf)))))

def allocationMeasure : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat :=
  fun s => heapLimit - globN s "heap_ptr" + (globN s "scratch_ptr" - scratchStart)

private theorem allocationMeasure_le {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : ArenaReady s) : allocationMeasure s ≤ 2 ^ 62 := by
  have hsp := hs.2.2.2.2.2.1
  dsimp only [allocationMeasure, heapLimit, scratchStart, scratchEnd] at *
  omega

private theorem allocationMeasure_decreases {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (_hs : ArenaReady s) (ht : ArenaReady t) (hg : AllocatorGrows s t)
    (hstrict : globN s "heap_ptr" < globN t "heap_ptr" ∨
      globN t "scratch_ptr" < globN s "scratch_ptr") :
    allocationMeasure t < allocationMeasure s := by
  have hhp := ht.2.2.1
  have hsl : scratchStart ≤ globN t "scratch_ptr" := ht.2.2.2.1.trans ht.2.2.2.2.1
  rcases hg with ⟨hh, hsp⟩
  unfold allocationMeasure
  omega

def fillCond : ExpHOL 64 :=
  .cmp .notEqual (.var .local (ofString "top")) (.const 0)

theorem fill_loop_bound
    {I : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), I s → I (decClockHOLFinite s))
    (hguard : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), I s → ArenaReady s ∧ ScanEntry s)
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp»)
    (ha : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    (hb : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish»)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      I s → LoopActive fillCond s →
      (evaluateHOLFiniteState (decClockHOLFinite s) fillBody).1 = none →
      let t := (evaluateHOLFiniteState (decClockHOLFinite s) fillBody).2
      I t ∧ AllocatorGrows s t ∧ (globN s "heap_ptr" < globN t "heap_ptr" ∨
        globN t "scratch_ptr" < globN s "scratch_ptr")) :
    TerminatingProgBoundedOn I (.while fillCond fillBody)
      ((2 ^ 62 + 1) * (fillBodyCost + 1)) := by
  apply TerminatingProgBoundedOn.while_rank allocationMeasure hdec
    (ArenaNodeRlp.weakenGuard (fillBody_bound hn ha hb hf) (fun s hs => (hguard s hs).2))
  · intro F s _ hs _
    exact allocationMeasure_le s (hguard s hs).1
  · intro F s hc hs hact hflow
    have hnc := evaluate_noTopContinue fillBody (by rfl) (decClockHOLFinite s)
    have hnone := hflow.elim id (fun h => False.elim (hnc h))
    obtain ⟨ht, hg, hp⟩ := hstep s hc hs hact hnone
    exact ⟨ht, allocationMeasure_decreases _ _ (hguard s hs).1 (hguard _ ht).1 hg hp⟩

/-! ### `EncFrame`: memory write-frame outside explicit intervals + heap bump -/

structure EncFrame {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  arena : ArenaReady post
  heap_le : globN s "heap_ptr" ≤ globN post "heap_ptr"
  nonHeap : ∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = s.globals.lookup k
  be : post.be = s.be
  cell_frame : ∀ a : BitVec 64, (∀ i ∈ Rl, ¬ CellHits a.toNat i) →
    ¬ CellHits a.toNat (globN s "heap_ptr", heapLimit - globN s "heap_ptr") →
    post.memory a = s.memory a
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → (∀ i ∈ Rl, ¬ InIvl b i) →
    ¬ InIvl b (globN s "heap_ptr", heapLimit - globN s "heap_ptr") →
    memB post b = memB s b

theorem EncFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) (hA : ArenaReady s) (Rl : List Ivl) :
    EncFrame s s Rl :=
  ⟨hA, Nat.le_refl _, fun _ _ => rfl, rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem EncFrame.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : EncFrame s post Rl) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    EncFrame s { post with locals := L, clock := k } Rl :=
  ⟨localsFree_arenaReady post L k h.arena, h.heap_le, h.nonHeap, h.be, h.cell_frame, h.byte_frame⟩

theorem EncFrame.mono {F : Type} {s post : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl}
    (h : EncFrame s post R1)
    (hsub : ∀ i ∈ R1, (∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit)) :
    EncFrame s post R2 := by
  refine ⟨h.arena, h.heap_le, h.nonHeap, h.be, ?_, ?_⟩
  · intro a ha hfr
    apply h.cell_frame a ?_ hfr
    intro i hi ⟨hc1, hc2⟩
    rcases hsub i hi with ⟨j, hj, h1, h2⟩ | ⟨hh1, hh2⟩
    · exact ha j hj ⟨by omega, by omega⟩
    · exact hfr ⟨by dsimp only; omega, by dsimp only; omega⟩
  · intro b hb hno hfr
    apply h.byte_frame b hb ?_ hfr
    intro i hi ⟨hb1, hb2⟩
    rcases hsub i hi with ⟨j, hj, h1, h2⟩ | ⟨hh1, hh2⟩
    · exact hno j hj ⟨by omega, by omega⟩
    · exact hfr ⟨by dsimp only; omega, by dsimp only; omega⟩

theorem EncFrame.trans {F : Type} {s mid post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h1 : EncFrame s mid Rl) (h2 : EncFrame mid post Rl) :
    EncFrame s post Rl := by
  refine ⟨h2.arena, Nat.le_trans h1.heap_le h2.heap_le,
    fun k hk => (h2.nonHeap k hk).trans (h1.nonHeap k hk),
    h2.be.trans h1.be, ?_, ?_⟩
  · intro a ha hfr
    have hfr_mid : ¬ CellHits a.toNat (globN mid "heap_ptr", heapLimit - globN mid "heap_ptr") := by
      intro ⟨hc1, hc2⟩
      dsimp only at hc1 hc2
      have hmid_hi := h1.arena.2.2.1
      exact hfr ⟨by dsimp only; have := h1.heap_le; omega, by dsimp only; omega⟩
    rw [h2.cell_frame a ha hfr_mid, h1.cell_frame a ha hfr]
  · intro b hb hno hfr
    have hfr_mid : ¬ InIvl b (globN mid "heap_ptr", heapLimit - globN mid "heap_ptr") := by
      intro ⟨hb1, hb2⟩
      dsimp only at hb1 hb2
      have hmid_hi := h1.arena.2.2.1
      exact hfr ⟨by dsimp only; have := h1.heap_le; omega, by dsimp only; omega⟩
    rw [h2.byte_frame b hb hno hfr_mid, h1.byte_frame b hb hno hfr]

theorem EncFrame.of_byteEff {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hA : ArenaReady s) (heff : R10Shards.P26_P28.ByteEff s post Rl) :
    EncFrame s post Rl := by
  have hG' : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hA.1
  have hA' : ArenaReady post :=
    ⟨hG', by simpa only [ArenaOK, globN, GlobalWord, GlobalsWord, heff.globals] using hA.2⟩
  refine ⟨hA', by simp [globN, heff.globals], fun _ _ => by rw [heff.globals], heff.be, ?_, ?_⟩
  · intro a ha _
    by_contra hne
    obtain ⟨i, hi, _, hc⟩ := heff.cell_frame a hne
    exact ha i hi hc
  · intro b hb hno _
    by_contra hne
    obtain ⟨i, hi, hin⟩ := heff.byte_frame b hb hne
    exact hno i hi hin

theorem EncFrame.of_alloc_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {v : ValueHOL 64} {Rl : List Ivl}
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1 = some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2
    ∃ p : BitVec 64,
      v = .val (.word p) ∧
      p.toNat = globN s "heap_ptr" ∧
      globN post "heap_ptr" = p.toNat + (locN s "n" + 7) / 8 * 8 ∧
      EncFrame s post Rl := by
  obtain ⟨p, q, hrv, hp_eq, hq_eq, _, _, hp_le_q, hpost_g, hpost_m, hpost_be, _, hA_post, hpost_hp, _⟩ :=
    R13Shards.alloc_body_resumes_props s hc hA (Or.inl ⟨v, hret⟩)
  rw [hrv] at hret
  injection hret with h1; injection h1 with h2; subst h2
  refine ⟨p, rfl, hp_eq, by rw [hpost_hp, hq_eq], ?_⟩
  refine ⟨hA_post, by rw [← hp_eq, hpost_hp]; exact hp_le_q, ?_, hpost_be,
    fun a _ _ => by rw [hpost_m], fun b _ _ _ => by unfold memB; rw [hpost_m, hpost_be]⟩
  intro k hk
  have hne : ofString "heap_ptr" ≠ k := fun h => hk h.symm
  rw [hpost_g]
  simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]

/-! ### RLP read-only length helpers (`rlp_be_len`, `rlp_header_len`, `rlp_list_header_len`, `rlp_bytes_encoded_len`, `rlp_value_encoded_len`, `node_ref_len`) -/

private theorem lookup_rlp_be_len :
    originalRuntimeCode.lookup (ofString "rlp_be_len") =
      some ([(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_rlp_be_len, .one) :=
  lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_be_len) rfl

private theorem lookup_rlp_header_len :
    originalRuntimeCode.lookup (ofString "rlp_header_len") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_rlp_header_len, .one) :=
  lookup_of_guestAst_getElem 121 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_header_len) rfl

private theorem lookup_rlp_list_header_len :
    originalRuntimeCode.lookup (ofString "rlp_list_header_len") =
      some ([(ofString "payload_len", .one)], sourceFnBody Guest.Software.guestFn_rlp_list_header_len, .one) :=
  lookup_of_guestAst_getElem 126 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_header_len) rfl

private theorem lookup_rlp_bytes_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len") =
      some ([(ofString "first_byte", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len, .one) :=
  lookup_of_guestAst_getElem 125 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_bytes_encoded_len) rfl

private theorem lookup_rlp_value_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_value_encoded_len") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len, .one) :=
  lookup_of_guestAst_getElem 286 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_value_encoded_len) rfl

private theorem lookup_node_ref_len :
    originalRuntimeCode.lookup (ofString "node_ref_len") =
      some ([(ofString "child", .one)], sourceFnBody Guest.Software.guestFn_node_ref_len, .one) :=
  lookup_of_guestAst_getElem 287 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_ref_len) rfl

private theorem lookup_mpt_fail_rel :
    originalRuntimeCode.lookup (ofString "mpt_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
  lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_fail) rfl

private def roEncGood (f : MlS) : Bool :=
  ((["rlp_be_len", "rlp_header_len", "rlp_list_header_len", "rlp_bytes_encoded_len",
    "rlp_value_encoded_len", "node_ref_len", "mpt_fail"] : List String).map ofString).contains f

private def roEncProg : ProgHOL 64 → Bool
  | .dec _ _ _ body => roEncProg body
  | .seq first second => roEncProg first && roEncProg second
  | .ite _ yes no => roEncProg yes && roEncProg no
  | .while _ body => roEncProg body
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .decCall _ _ function _ continuation => roEncGood function && roEncProg continuation
  | .call none function _ => roEncGood function
  | .call (some (none, none)) function _ => roEncGood function
  | .call (some (some (.local, _), none)) function _ => roEncGood function
  | _ => false

private theorem roEnc_installed_body (f : MlS)
    (hf : roEncGood f = true)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs)) :
    roEncProg body = true := by
  simp only [roEncGood, List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_be_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_header_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_list_header_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_bytes_encoded_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_value_encoded_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_node_ref_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_mpt_fail_rel hl; subst hb; rfl

theorem evaluate_roEncProg {F : Type} (program : ProgHOL 64)
    (supported : roEncProg program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2 =
      { state with locals := (evaluateHOLFiniteState state program).2.locals,
                   clock := (evaluateHOLFiniteState state program).2.clock } := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : roEncProg body = true := by simpa only [shape, roEncProg] using supported
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · rfl
    · rename_i val _
      split
      · have ih := evaluate_roEncProg body child (setVarHOLFinite name val state) code
        dsimp only [setVarHOLFinite] at ih ⊢
        rw [ih]
      · rfl
  | decCall name kind function arguments continuation =>
    have children : roEncGood function = true ∧ roEncProg continuation = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        rw [code] at found
        split
        · rfl
        · rename_i nonzero
          dsimp only
          have hsafe := roEnc_installed_body function children.1 values body callee rs found
          have hbody := evaluate_roEncProg body hsafe (callEntryStateHOLFinite state callee) code
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbody meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at hbody meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try (rw [hbody]; cases state; rfl))
          split
          · have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            let resumed : PanSemStateFiniteExact 64 F :=
              setVarHOLFinite name v
                { st with locals := state.locals,
                          clock := if (callEntryStateHOLFinite state callee).clock < st.clock
                                   then (callEntryStateHOLFinite state callee).clock else st.clock }
            have ih := evaluate_roEncProg continuation children.2 resumed stCode
            dsimp only [resumed, setVarHOLFinite] at ih ⊢
            conv_lhs => rw [ih]
            rw [hbody]; cases state; rfl
          · rw [hbody]; cases state; rfl
  | assign kind name value =>
    cases kind with
    | global => simp [shape, roEncProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split <;> (cases state; rfl)
  | seq first second =>
    have children : roEncProg first = true ∧ roEncProg second = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    have h1 := evaluate_roEncProg first children.1 state code
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at h1 remaining meta'
      dsimp only at h1 remaining meta'
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        have h2 := evaluate_roEncProg second children.2 middle (meta'.1.trans code)
        dsimp only
        rw [h2, h1]
      | some _ => exact h1
  | ite condition yes no =>
    have children : roEncProg yes = true ∧ roEncProg no = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_roEncProg no children.2 state code
      · exact evaluate_roEncProg yes children.1 state code
    · rfl
  | «while» condition body =>
    have child : roEncProg body = true := by simpa only [shape, roEncProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hb := evaluate_roEncProg body child (decClockHOLFinite state) code
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at hb remaining meta'
            dsimp only at hb remaining meta'
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining; omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none =>
              have hw := evaluate_roEncProg (.while condition body) (by simpa [roEncProg] using child) middle mCode
              rw [hw, hb]; cases state; rfl
            | some r =>
              cases r with
              | «continue» =>
                have hw := evaluate_roEncProg (.while condition body) (by simpa [roEncProg] using child) middle mCode
                rw [hw, hb]; cases state; rfl
              | _ => rw [hb]; cases state; rfl
      · rfl
    · rfl
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot tag text => rw [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> (cases state; rfl)
    · rfl
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> (cases state; rfl)
  | call info function arguments =>
    have hk : roEncGood function = true ∧
        (info = none ∨ info = some (none, none) ∨ ∃ nm, info = some (some (.local, nm), none)) := by
      rcases info with _ | ⟨_ | ⟨kind, nm⟩, _ | _⟩
      · exact ⟨by simpa [shape, roEncProg] using supported, Or.inl rfl⟩
      · exact ⟨by simpa [shape, roEncProg] using supported, Or.inr (Or.inl rfl)⟩
      · simp [shape, roEncProg] at supported
      · cases kind
        · exact ⟨by simpa [shape, roEncProg] using supported, Or.inr (Or.inr ⟨nm, rfl⟩)⟩
        · simp [shape, roEncProg] at supported
      · simp [shape, roEncProg] at supported
    rw [evaluateHOLFiniteState_call]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        rw [code] at found
        split
        · rfl
        · rename_i nonzero
          have hsafe := roEnc_installed_body function hk.1 values body callee rs found
          have hbody := evaluate_roEncProg body hsafe (callEntryStateHOLFinite state callee) code
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbody
          obtain ⟨r, st⟩ := out
          dsimp only at hbody ⊢
          rcases hk.2 with rfl | rfl | ⟨nm, rfl⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (rw [hbody]; cases state; rfl)
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (rw [hbody]; cases state; rfl)
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (try dsimp only [setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite]) <;>
              (rw [hbody]; cases state; rfl)
  | _ => simp [shape, roEncProg] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | omega

/-! ###Write-frame combinators & callees for `_node_rlp_begin` and `_node_rlp_finish` -/

private theorem lookup_nibble_list_to_compact :
    originalRuntimeCode.lookup (ofString "nibble_list_to_compact") =
      some ([(ofString "nibs", .one), (ofString "n", .one), (ofString "is_leaf", .one), (ofString "dst", .one)],
        sourceFnBody Guest.Software.guestFn_nibble_list_to_compact, .one) :=
  lookup_of_guestAst_getElem 250 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_nibble_list_to_compact) rfl

private theorem lookup_node_hash_cached :
    originalRuntimeCode.lookup (ofString "node_hash_cached") =
      some ([(ofString "node", .one)],
        sourceFnBody Guest.Software.guestFn_node_hash_cached, .one) :=
  lookup_of_guestAst_getElem 288 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_hash_cached) rfl

private theorem lookup_node_write_ref :
    originalRuntimeCode.lookup (ofString "node_write_ref") =
      some ([(ofString "child", .one), (ofString "dst", .one)],
        sourceFnBody Guest.Software.guestFn_node_write_ref, .one) :=
  lookup_of_guestAst_getElem 289 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_write_ref) rfl

private theorem lookup__node_rlp_begin :
    originalRuntimeCode.lookup (ofString "_node_rlp_begin") =
      some ([(ofString "fr", .one), (ofString "node", .one)],
        sourceFnBody Guest.Software.guestFn__node_rlp_begin, .one) :=
  lookup_of_guestAst_getElem 281 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_begin) rfl

private theorem lookup__node_rlp_finish :
    originalRuntimeCode.lookup (ofString "_node_rlp_finish") =
      some ([(ofString "fr", .one), (ofString "node", .one)],
        sourceFnBody Guest.Software.guestFn__node_rlp_finish, .one) :=
  lookup_of_guestAst_getElem 282 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_finish) rfl

def freeGapIvl {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")

theorem EncFrame.of_heapByteEff {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : R16Shards.WkBlockTxEnc.HeapByteEff s post Rl ["heap_ptr"]) :
    EncFrame s post (freeGapIvl s :: Rl) := by
  refine ⟨h.arena, h.hp_le, ?_, h.be, ?_, ?_⟩
  · intro k hk
    exact (h.globals k (by simp [hk])).symm
  · intro a ha hfr
    by_contra hne
    rcases h.cell_frame a hne with ⟨i, hi, _, hc⟩ | hfg | hhf
    · exact ha i (List.mem_cons_of_mem _ hi) hc
    · exact ha (freeGapIvl s) List.mem_cons_self hfg.2
    · exact hfr hhf.2
  · intro b hb hno hfr
    by_contra hne
    rcases h.byte_frame b hb hne with ⟨i, hi, hin⟩ | hfg | hhf
    · exact hno i (List.mem_cons_of_mem _ hi) hin
    · exact hno (freeGapIvl s) List.mem_cons_self hfg
    · exact hfr hhf

theorem EncFrame.of_m11_bre {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hA : ArenaReady s) (heff : M11.ByteRegionEffect s post Rl) :
    EncFrame s post Rl := by
  have hG : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hA.1
  have hAK : ArenaOK post := by simpa only [ArenaOK, globN, GlobalWord, GlobalsWord, heff.globals] using hA.2
  refine ⟨⟨hG, hAK⟩, by simp [globN, heff.globals], fun _ _ => by rw [heff.globals], heff.be, ?_, ?_⟩
  · intro a ha _
    by_contra hne
    have hdom : ordinaryDomain a := by
      rw [← hA.1.memaddrs]
      by_contra hnd; exact hne (heff.out_dom a hnd)
    have ha_ord := (M11.ordinaryDomain_iff a).1 hdom
    have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [M11.heapEnd_val]; decide
    have ha_lt_he : a.toNat < heapEnd := by rw [M11.heapEnd_val]; omega
    apply hne
    apply R16Shards.WkBlockTxEnc.mem_eq_of_bytes_eq heff.be a hdom
    intro k hk
    apply heff.byte_frame (a.toNat + k) (by omega)
    intro i hi ⟨hb1, hb2⟩
    exact ha i hi ⟨by omega, by omega⟩
  · intro b hb hno _
    apply heff.byte_frame b hb
    intro i hi hin; exact hno i hi hin

theorem EncFrame.seq_none {F : Type} {s : PanSemStateFiniteExact 64 F} {p q : ProgHOL 64} {Rl : List Ivl}
    (hnone : (evaluateHOLFiniteState s (.seq p q)).1 = none)
    (hp : (evaluateHOLFiniteState s p).1 = none → EncFrame s (evaluateHOLFiniteState s p).2 Rl)
    (hq : ∀ mid, evaluateHOLFiniteState s p = (none, mid) →
      (evaluateHOLFiniteState mid q).1 = none → EncFrame mid (evaluateHOLFiniteState mid q).2 Rl) :
    EncFrame s (evaluateHOLFiniteState s (.seq p q)).2 Rl := by
  obtain ⟨hp1, hq1, heq⟩ := seq_none_rel s p q hnone
  rw [heq]
  have hf1 := hp hp1
  exact hf1.trans (hq (evaluateHOLFiniteState s p).2 (Prod.ext hp1 rfl) hq1)

theorem EncFrame.dec_any {F : Type} {s : PanSemStateFiniteExact 64 F}
    (nm : MlS) (sh : ShapeHOL) (e : ExpHOL 64) (body : ProgHOL 64) {Rl : List Ivl}
    (hA : ArenaReady s)
    (hb : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      shapeEqHOL sh (shapeOfHOLExact v) = true →
      EncFrame (setVarHOLFinite nm v s) (evaluateHOLFiniteState (setVarHOLFinite nm v s) body).2 Rl) :
    EncFrame s (evaluateHOLFiniteState s (.dec nm sh e body)).2 Rl := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact EncFrame.refl s hA Rl
  · rename_i v hv
    split
    · rename_i hsh
      have h0 : EncFrame s (setVarHOLFinite nm v s) Rl :=
        (EncFrame.refl s hA Rl).with_locals_clock _ _
      exact (h0.trans (hb v hv hsh)).with_locals_clock _ _
    · exact EncFrame.refl s hA Rl

theorem EncFrame.ite_any {F : Type} {s : PanSemStateFiniteExact 64 F}
    (cond : ExpHOL 64) (yes no : ProgHOL 64) {Rl : List Ivl}
    (hA : ArenaReady s)
    (hy : ∀ cw : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word cw)) →
      cw ≠ 0 → EncFrame s (evaluateHOLFiniteState s yes).2 Rl)
    (hn : ∀ cw : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word cw)) →
      cw = 0 → EncFrame s (evaluateHOLFiniteState s no).2 Rl) :
    EncFrame s (evaluateHOLFiniteState s (.ite cond yes no)).2 Rl := by
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i cw hcw
    split
    · rename_i hz; exact hn cw hcw hz
    · rename_i hnz; exact hy cw hcw hnz
  · exact EncFrame.refl s hA Rl

theorem EncFrame.of_roEncProg {F : Type} {s : PanSemStateFiniteExact 64 F}
    (p : ProgHOL 64) (hp : roEncProg p = true) (hc : s.code = originalRuntimeCode)
    (hA : ArenaReady s) (Rl : List Ivl) :
    EncFrame s (evaluateHOLFiniteState s p).2 Rl := by
  have heq := evaluate_roEncProg p hp s hc
  rw [heq]
  exact (EncFrame.refl s hA Rl).with_locals_clock _ _

theorem EncFrame.decCall_roEnc {F : Type} {s : PanSemStateFiniteExact 64 F}
    (nm : MlS) (sh : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64) {Rl : List Ivl}
    (hfn : roEncGood fn = true) (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hcont : ∀ (v : ValueHOL 64) (mid : PanSemStateFiniteExact 64 F),
      mid = { s with locals := s.locals.update (nm, v), clock := mid.clock } →
      EncFrame mid (evaluateHOLFiniteState mid cont).2 Rl) :
    EncFrame s (evaluateHOLFiniteState s (.decCall nm sh fn args cont)).2 Rl := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · exact EncFrame.refl s hA Rl
  · rename_i values _
    split
    · exact EncFrame.refl s hA Rl
    · rename_i body callee rs hl
      split
      · exact (EncFrame.refl s hA Rl).with_locals_clock _ _
      · have hsafe := roEnc_installed_body fn hfn values body callee rs (by rw [← hc]; exact hl)
        have hro := evaluate_roEncProg body hsafe (callEntryStateHOLFinite s callee) hc
        have hclk_le := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        dsimp only
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
        have hro' : st = { (callEntryStateHOLFinite s callee) with locals := st.locals, clock := st.clock } := by
          have := hro; rw [hcal] at this; exact this
        have hclk_le' : st.clock ≤ (callEntryStateHOLFinite s callee).clock := by
          have := hclk_le; rw [hcal] at this; exact this
        dsimp only
        rcases r with _ | r0
        · dsimp only [fixClockHOLFinite]
          rw [hro']; exact (EncFrame.refl s hA Rl).with_locals_clock _ _
        · cases r0 with
          | returned v =>
            dsimp only [fixClockHOLFinite]
            split
            · let mid : PanSemStateFiniteExact 64 F :=
                setVarHOLFinite nm v
                  { st with locals := s.locals,
                            clock := if (callEntryStateHOLFinite s callee).clock < st.clock
                                     then (callEntryStateHOLFinite s callee).clock else st.clock }
              have hmid_eq : mid = { s with locals := s.locals.update (nm, v), clock := mid.clock } := by
                dsimp only [mid, setVarHOLFinite]
                rw [hro']; cases s; rfl
              have h0 : EncFrame s mid Rl := by
                rw [hmid_eq]; exact (EncFrame.refl s hA Rl).with_locals_clock _ _
              have hclk_if : (if (callEntryStateHOLFinite s callee).clock < st.clock
                  then (callEntryStateHOLFinite s callee).clock else st.clock) = st.clock :=
                if_neg (by omega)
              have hmid_eq2 : mid = setVarHOLFinite nm v { st with locals := s.locals } := by
                dsimp only [mid]; rw [hclk_if]
              rw [← hmid_eq2]
              exact (h0.trans (hcont v mid hmid_eq)).with_locals_clock _ _
            · rw [hro']; exact (EncFrame.refl s hA Rl).with_locals_clock _ _
          | «break» =>
            dsimp only [fixClockHOLFinite]
            rw [hro']; exact (EncFrame.refl s hA Rl).with_locals_clock _ _
          | «continue» =>
            dsimp only [fixClockHOLFinite]
            rw [hro']; exact (EncFrame.refl s hA Rl).with_locals_clock _ _
          | _ =>
            dsimp only [fixClockHOLFinite, emptyLocalsHOLFinite]
            rw [hro']; exact (EncFrame.refl s hA Rl).with_locals_clock _ _

private theorem eval_noTopBreak : ∀ (p : ProgHOL 64),
    (p = .storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
          (.op .or [
            .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
            .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]) ∨
     p = .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]) ∨
     p = .assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1])) →
    ∀ {F : Type} (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState st p).1 ≠ some .break := by
  rintro p (rfl | rfl | rfl) F st
  · rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  · rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  · rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp

private theorem eval_compactBody_noBreak {F : Type} (st : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState st
      (.seq
        (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
          (.op .or [
            .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
            .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
        (.seq
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
          (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1]))))).1 ≠ some .break := by
  let p0 : ProgHOL 64 := .storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
    (.op .or [
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
      .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])])
  rw [evaluateHOLFiniteState_seq_line780]; dsimp only
  split
  · rw [evaluateHOLFiniteState_seq_line780]; dsimp only
    split
    · exact eval_noTopBreak _ (Or.inr (Or.inr rfl)) _
    · exact eval_noTopBreak _ (Or.inr (Or.inl rfl)) ((st.evaluateHOLFiniteState p0).2)
  · exact eval_noTopBreak _ (Or.inl rfl) st

private theorem eval_compactBody_noReturn {F : Type} (st : PanSemStateFiniteExact 64 F) (rv : ValueHOL 64) :
    (evaluateHOLFiniteState st
      (.seq
        (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
          (.op .or [
            .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
            .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
        (.seq
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
          (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1]))))).1 ≠ some (.returned rv) := by
  have hnr : ∀ (p : ProgHOL 64),
      (p = .storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
            (.op .or [
              .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
              .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]) ∨
       p = .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]) ∨
       p = .assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1])) →
      ∀ (u : PanSemStateFiniteExact 64 F),
        (evaluateHOLFiniteState u p).1 ≠ some (.returned rv) := by
    rintro p (rfl | rfl | rfl) u
    · rw [evaluateHOLFiniteState_storeByte]
      split
      · split
        · split <;> simp
        · simp
      · simp
    · rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
    · rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  let p0 : ProgHOL 64 := .storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
    (.op .or [
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
      .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])])
  rw [evaluateHOLFiniteState_seq_line780]; dsimp only
  split
  · rw [evaluateHOLFiniteState_seq_line780]; dsimp only
    split
    · exact hnr _ (Or.inr (Or.inr rfl)) _
    · exact hnr _ (Or.inr (Or.inl rfl)) ((st.evaluateHOLFiniteState p0).2)
  · exact hnr _ (Or.inl rfl) st

private def compactLoop : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    (.seq
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
        (.op .or [
          .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
          .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
      (.seq
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
        (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1]))))

private theorem eval_compactLoop_not_returned {F : Type} :
    ∀ (kk : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = kk →
      ∀ v', (evaluateHOLFiniteState st compactLoop).1 ≠ some (.returned v') := by
  intro kk
  induction kk using Nat.strong_induction_on with
  | h kk ih =>
    intro st hkk v' hbad
    rw [compactLoop, evaluateHOLFiniteState_while_fixClockRewrite, ← compactLoop] at hbad
    split at hbad
    · split at hbad
      · split at hbad
        · simp at hbad
        · let bProg : ProgHOL 64 :=
            .seq
              (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
                (.op .or [
                  .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
                  .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
              (.seq
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
                (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1])))
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) bProg
          have hnr_b := eval_compactBody_noReturn (decClockHOLFinite st) v'
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) bProg with ⟨rb1, mb1⟩
          change evaluateHOLFiniteState (decClockHOLFinite st) _ = (rb1, mb1) at hbr
          rw [hbr] at hbad hrem hnr_b
          cases rb1 with
          | none => exact ih mb1.clock (by simp [decClockHOLFinite, hkk] at hrem ⊢; omega) mb1 rfl v' hbad
          | some rb1' =>
            cases rb1' with
            | «continue» => exact ih mb1.clock (by simp [decClockHOLFinite, hkk] at hrem ⊢; omega) mb1 rfl v' hbad
            | returned v'' =>
              have hnr_b' := eval_compactBody_noReturn (decClockHOLFinite st) v''
              rw [hbr] at hnr_b'
              exact hnr_b' rfl
            | _ => simp at hbad
      · simp at hbad
    · simp at hbad

private theorem eval_compactLoop_eff {F : Type} :
    ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F) (dst0 nw iw ow : BitVec 64) (cap : Nat),
      s.clock ≤ k →
      GuestInv s →
      dst0.toNat + cap ≤ heapLimit →
      s.locals.lookup (ofString "dst") = some (.val (.word dst0)) →
      s.locals.lookup (ofString "n") = some (.val (.word nw)) →
      s.locals.lookup (ofString "i") = some (.val (.word iw)) →
      s.locals.lookup (ofString "o") = some (.val (.word ow)) →
      1 ≤ ow.toNat →
      ow.toNat + (nw.toNat + 1 - iw.toNat) / 2 ≤ cap →
      iw.toNat ≤ nw.toNat + 1 →
      nw.toNat < 2 ^ 63 →
      (evaluateHOLFiniteState s compactLoop).1 = none →
      ∃ ow' : BitVec 64,
        1 ≤ ow'.toNat ∧ ow'.toNat ≤ cap ∧
        (evaluateHOLFiniteState s compactLoop).2.locals.lookup (ofString "o") = some (.val (.word ow')) ∧
        R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s compactLoop).2 [(dst0.toNat, cap)] := by
  intro k
  induction k with
  | zero =>
    intro s dst0 nw iw ow cap hk _ _ _ hn hi ho how1 how_cap _ _ hnone
    unfold compactLoop at hnone ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    have hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1 else 0))) := by
      simp [evalHOLFinite, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hc] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hk0 : s.clock = 0 := by omega
      simp [hlt, hk0] at hnone
    · simp only [hlt, ↓reduceIte]
      exact ⟨ow, how1, by omega, ho, (R10Shards.P26_P28.ByteEff.refl s _).locals_clock _ _⟩
  | succ k ih =>
    intro s dst0 nw iw ow cap hk hG hcap hdst hn hi ho how1 how_cap hi_le hnw_hi hnone
    rw [compactLoop, evaluateHOLFiniteState_while_fixClockRewrite, ← compactLoop] at hnone ⊢
    have hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1 else 0))) := by
      simp [evalHOLFinite, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hc] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos hlt, if_pos h10] at hnone ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnone
      · rw [if_neg hk0] at hnone ⊢
        let sd := decClockHOLFinite s
        have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
        have hhl_he : heapLimit ≤ heapEnd := by decide
        have h264 : heapEnd < 2 ^ 64 := by decide
        have how_lt_cap : ow.toNat < cap := by omega
        let sbProg : ProgHOL 64 :=
          .storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
            (.op .or [
              .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
              .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])])
        let asgProg : ProgHOL 64 :=
          .seq (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
            (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1]))
        have hsb_eff : R10Shards.P26_P28.ByteEff sd
            (evaluateHOLFiniteState sd sbProg).2 [(dst0.toNat, cap)] := by
          apply R10Shards.P26_P28.byteEff_storeByte_at hGd _ _ dst0 ow.toNat cap (by omega)
            (fun _ => ⟨(dst0.toNat, cap), List.mem_singleton.2 rfl, le_refl _, le_refl _⟩) how_lt_cap
          have hod : sd.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hdst
          have hoo : sd.locals.lookup (ofString "o") = some (.val (.word ow)) := ho
          simp [evalHOLExact, evalListHOLExact, hod, hoo, wordOpHOL, wordOp, valueIsWord, valueWord,
            BitVec.add_zero]
        have hclk_b := evaluateHOLFiniteState_clock_le sd (.seq sbProg asgProg)
        rcases hbo_sd : evaluateHOLFiniteState (decClockHOLFinite s) (.seq sbProg asgProg) with ⟨rb, sb⟩
        have hbo_sd' : evaluateHOLFiniteState sd (.seq sbProg asgProg) = (rb, sb) := hbo_sd
        have hbo_raw : evaluateHOLFiniteState (decClockHOLFinite s)
            (.seq
              (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
                (.op .or [
                  .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
                  .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
              (.seq (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
                (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1])))) = (rb, sb) := hbo_sd
        rw [hbo_raw] at hnone
        rw [hbo_sd'] at hclk_b
        have hnc : rb ≠ some .continue := by
          have := evaluate_noTopContinue (.seq sbProg asgProg) rfl sd
          rw [hbo_sd'] at this; exact this
        dsimp only at hnone ⊢
        cases rb with
        | some r' =>
          cases r' with
          | «continue» => exact absurd rfl hnc
          | «break» =>
            have hnb := eval_compactBody_noBreak sd
            rw [hbo_sd'] at hnb; exact absurd rfl hnb
          | _ => simp at hnone
        | none =>
          obtain ⟨hsb_none, hasg_none, hsb_eq⟩ := seq_none_rel sd sbProg asgProg (by rw [hbo_sd'])
          let s1 := (evaluateHOLFiniteState sd sbProg).2
          have hs1_loc : s1.locals = s.locals := by
            dsimp only [s1, sbProg] at hsb_none ⊢
            rw [evaluateHOLFiniteState_storeByte] at hsb_none ⊢
            split at hsb_none
            · split at hsb_none
              · split at hsb_none <;> simp_all [sd, decClockHOLFinite]
              · simp at hsb_none
            · simp at hsb_none
          have hasg_ev : evaluateHOLFiniteState s1 asgProg =
              (none, setVarHOLFinite (ofString "o") (.val (.word (ow + 1)))
                (setVarHOLFinite (ofString "i") (.val (.word (iw + 2))) s1)) := by
            dsimp only [asgProg]
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hs1_loc]; exact hi
            have hs1_o : s1.locals.lookup (ofString "o") = some (.val (.word ow)) := by rw [hs1_loc]; exact ho
            have hne_io : ofString "i" ≠ ofString "o" := by decide
            simp [evalHOLExact, evalListHOLExact, hs1_i, hs1_o, hne_io, Ne.symm hne_io,
              wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero,
              isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL,
              setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              evaluateHOLFiniteState_assign]
          have hsb_def : sb = setVarHOLFinite (ofString "o") (.val (.word (ow + 1)))
              (setVarHOLFinite (ofString "i") (.val (.word (iw + 2))) s1) := by
            have := hsb_eq; rw [hbo_sd', hasg_ev] at this; exact this
          have hiw2_nat : (iw + 2).toNat = iw.toNat + 2 := by
            have h2val : ((2 : BitVec 64)).toNat = 2 := rfl
            rw [BitVec.toNat_add, h2val]; exact Nat.mod_eq_of_lt (by omega)
          have how1_nat : (ow + 1).toNat = ow.toNat + 1 := by
            have h1val : ((1 : BitVec 64)).toNat = 1 := rfl
            rw [BitVec.toNat_add, h1val]; exact Nat.mod_eq_of_lt (by omega)
          have heff_iter : R10Shards.P26_P28.ByteEff s sb [(dst0.toNat, cap)] := by
            rw [hsb_def]
            exact ((((R10Shards.P26_P28.ByteEff.refl s _).locals_clock sd.locals sd.clock).trans hsb_eff).locals_clock _ _).locals_clock _ _
          have hG_sb : GuestInv sb :=
            guestInv_congr heff_iter.code heff_iter.memaddrs heff_iter.shMemaddrs heff_iter.baseAddr hG
          have hsb_dst : sb.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            rw [hsb_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_loc, hdst,
              show ofString "o" ≠ ofString "dst" by decide, show ofString "i" ≠ ofString "dst" by decide]
          have hsb_n : sb.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            rw [hsb_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_loc, hn,
              show ofString "o" ≠ ofString "n" by decide, show ofString "i" ≠ ofString "n" by decide]
          have hsb_i : sb.locals.lookup (ofString "i") = some (.val (.word (iw + 2))) := by
            rw [hsb_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "o" ≠ ofString "i" by decide]
          have hsb_o : sb.locals.lookup (ofString "o") = some (.val (.word (ow + 1))) := by
            rw [hsb_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hclk_sb : sb.clock ≤ k := by
            change sb.clock ≤ s.clock - 1 at hclk_b; omega
          have hnone_sb : (evaluateHOLFiniteState sb compactLoop).1 = none := hnone
          obtain ⟨ow', how'1, how'_cap, hpost_o, heff_rest⟩ :=
            ih sb dst0 nw (iw + 2) (ow + 1) cap hclk_sb hG_sb hcap hsb_dst hsb_n hsb_i hsb_o
              (by omega) (by rw [how1_nat, hiw2_nat]; omega) (by rw [hiw2_nat]; omega)
              hnw_hi hnone_sb
          exact ⟨ow', how'1, how'_cap, hpost_o, (heff_iter.trans heff_rest).locals_clock _ _⟩
    · simp only [hlt, ↓reduceIte]
      exact ⟨ow, how1, by omega, ho, (R10Shards.P26_P28.ByteEff.refl s _).locals_clock _ _⟩

private theorem byteEff_fixClock_snd {F : Type} {s0 s1 post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {r : Option (PanSemResultExact 64)}
    (h : R10Shards.P26_P28.ByteEff s0 post Rl) :
    R10Shards.P26_P28.ByteEff s0 (fixClockHOLFinite s1 (r, post)).2 Rl := by
  dsimp only [fixClockHOLFinite]
  exact h.locals_clock post.locals _

private theorem byteEff_resVar_snd {F : Type} {s0 post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {nm : MlS} {old : Option (ValueHOL 64)}
    (h : R10Shards.P26_P28.ByteEff s0 post Rl) :
    R10Shards.P26_P28.ByteEff s0
      { post with locals := HolFiniteMapExact.resVarEq post.locals (nm, old) } Rl :=
  h.locals_clock _ post.clock

private theorem eval_nibble_list_to_compact_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (nibsw nw islw dst0 : BitVec 64) (cap : Nat) (v : ValueHOL 64)
    (hG : GuestInv s)
    (hcap : dst0.toNat + cap ≤ heapLimit)
    (_hnibs : s.locals.lookup (ofString "nibs") = some (.val (.word nibsw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hisl : s.locals.lookup (ofString "is_leaf") = some (.val (.word islw)))
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hnw_hi : nw.toNat < 2 ^ 63)
    (hn_cap : nw.toNat / 2 + 1 ≤ cap)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact)).1 =
      some (.returned v)) :
    ∃ ow : BitVec 64,
      v = .val (.word ow) ∧ 1 ≤ ow.toNat ∧ ow.toNat ≤ nw.toNat / 2 + 1 ∧
      R10Shards.P26_P28.ByteEff s
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact)).2
        [(dst0.toNat, cap)] := by
  have hcap_pos : 1 ≤ cap := by omega
  have hb : sourceFnBody Guest.Software.guestFn_nibble_list_to_compact =
      .dec (ofString "flag") .one (.panop .mul [.var .local (ofString "is_leaf"), .const 2])
        (.dec (ofString "i") .one (.const 0)
          (.seq
            (.ite (.cmp .equal (.op .and [.var .local (ofString "n"), .const 1]) (.const 0))
              (.storeByte (.var .local (ofString "dst"))
                (.panop .mul [.const 16, .var .local (ofString "flag")]))
              (.seq
                (.storeByte (.var .local (ofString "dst"))
                  (.op .add [
                    .panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
                    .loadByte (.var .local (ofString "nibs"))]))
                (.assign .local (ofString "i") (.const 1))))
            (.dec (ofString "o") .one (.const 1)
              (.seq compactLoop (.return (.var .local (ofString "o"))))))) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hret ⊢
  have hev_fl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.panop .mul [.var .local (ofString "is_leaf"), .const 2]) = some (.val (.word (islw * 2))) := by
    simp [evalHOLExact, evalListHOLExact, hisl, panOpHOL, valueIsWord, valueWord]
  have hsh_fl : shapeEqHOL .one (shapeOfHOLExact (.val (.word (islw * 2)) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hret ⊢
  rw [hev_fl] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsh_fl] at hret ⊢
  let s1 := setVarHOLFinite (ofString "flag") (.val (.word (islw * 2))) s
  rw [evaluateHOLFiniteState_dec_total] at hret ⊢
  have hev_i0 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.const 0) = some (.val (.word 0)) := rfl
  have hsh_0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hret ⊢
  rw [hev_i0] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsh_0] at hret ⊢
  let s2 := setVarHOLFinite (ofString "i") (.val (.word 0)) s1
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "i" ≠ ofString "n" by decide, show ofString "flag" ≠ ofString "n" by decide]
  have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst,
      show ofString "i" ≠ ofString "dst" by decide, show ofString "flag" ≠ ofString "dst" by decide]
  let hdrProg : ProgHOL 64 :=
    .ite (.cmp .equal (.op .and [.var .local (ofString "n"), .const 1]) (.const 0))
      (.storeByte (.var .local (ofString "dst"))
        (.panop .mul [.const 16, .var .local (ofString "flag")]))
      (.seq
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [
            .panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
            .loadByte (.var .local (ofString "nibs"))]))
        (.assign .local (ofString "i") (.const 1)))
  let tailProg : ProgHOL 64 :=
    .dec (ofString "o") .one (.const 1) (.seq compactLoop (.return (.var .local (ofString "o"))))
  rcases hhdr : evaluateHOLFiniteState s2 hdrProg with ⟨rh, sh⟩
  have hhdr_cases : rh = none →
      ∃ iw : BitVec 64,
        (nw.toNat % 2 = 0 ∧ iw = 0 ∨ nw.toNat % 2 = 1 ∧ iw = 1) ∧
        sh.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
        sh.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        sh.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
        R10Shards.P26_P28.ByteEff s sh [(dst0.toNat, cap)] := by
    intro hrh
    dsimp only [hdrProg] at hhdr
    rw [evaluateHOLFiniteState_ite] at hhdr
    have hcond : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
        (.cmp .equal (.op .and [.var .local (ofString "n"), .const 1]) (.const 0)) =
        some (.val (.word (if (nw &&& 1) = 0 then 1 else 0))) := by
      simp [evalHOLExact, evalListHOLExact, hs2_n, wordOpHOL, wordOp,
        Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord]
    rw [hcond] at hhdr
    dsimp only at hhdr
    have hs2_eff0 : R10Shards.P26_P28.ByteEff s s2 [(dst0.toNat, cap)] :=
      ((R10Shards.P26_P28.ByteEff.refl s _).locals_clock s1.locals s1.clock).locals_clock s2.locals s2.clock
    have hG_s2 : GuestInv s2 := guestInv_congr (s := s) rfl rfl rfl rfl hG
    by_cases hodd : nw &&& 1 = 0
    · have hcw : (if nw &&& 1 = 0 then (1 : BitVec 64) else 0) ≠ 0 := by rw [if_pos hodd]; decide
      rw [if_neg hcw] at hhdr
      have hpar : nw.toNat % 2 = 0 := by
        have := congrArg BitVec.toNat hodd
        simpa [BitVec.toNat_and, Nat.and_one_is_mod] using this
      have hsb_eff : R10Shards.P26_P28.ByteEff s2
          (evaluateHOLFiniteState s2
            (.storeByte (.var .local (ofString "dst"))
              (.panop .mul [.const 16, .var .local (ofString "flag")]))).2
          [(dst0.toNat, cap)] :=
        (R10Shards.P26_P28.byteEff_storeByte (s := s2) (Rl := [(dst0.toNat, cap)]) hG_s2
          (.var .local (ofString "dst"))
          (.panop .mul [.const 16, .var .local (ofString "flag")])
          (fun x hx _ => by
            have hxd : x = dst0 := (by simpa [evalHOLExact, hs2_dst] using hx : dst0 = x).symm
            rw [hxd]
            exact ⟨(dst0.toNat, cap), List.mem_singleton.mpr rfl, le_rfl, by dsimp; omega⟩)).1
      have hsb_loc : (evaluateHOLFiniteState s2
          (.storeByte (.var .local (ofString "dst"))
            (.panop .mul [.const 16, .var .local (ofString "flag")]))).2.locals = s2.locals := by
        rw [evaluateHOLFiniteState_storeByte] at hhdr ⊢
        split at hhdr
        · split at hhdr
          · split at hhdr <;> simp_all
          · simp_all
        · simp_all
      rw [hhdr] at hsb_eff hsb_loc
      refine ⟨0, Or.inl ⟨hpar, rfl⟩, ?_, by rw [hsb_loc]; exact hs2_n,
        by rw [hsb_loc]; exact hs2_dst, hs2_eff0.trans hsb_eff⟩
      rw [hsb_loc]; simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · have hcw : (if nw &&& 1 = 0 then (1 : BitVec 64) else 0) = 0 := by rw [if_neg hodd]
      rw [if_pos hcw] at hhdr
      have hpar : nw.toNat % 2 = 1 := by
        have : nw.toNat &&& 1 ≠ 0 := by
          intro hz; apply hodd; apply BitVec.eq_of_toNat_eq; simpa [BitVec.toNat_and] using hz
        have hlt2 : nw.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
        have hand_mod : nw.toNat &&& 1 = nw.toNat % 2 := Nat.and_one_is_mod nw.toNat
        omega
      obtain ⟨hsb_n, _, hseq_eq⟩ := seq_none_rel s2
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [
            .panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
            .loadByte (.var .local (ofString "nibs"))]))
        (.assign .local (ofString "i") (.const 1))
        (by rw [hhdr]; exact hrh)
      let sm := (evaluateHOLFiniteState s2
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [
            .panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
            .loadByte (.var .local (ofString "nibs"))]))).2
      have hsb_eff : R10Shards.P26_P28.ByteEff s2 sm [(dst0.toNat, cap)] :=
        (R10Shards.P26_P28.byteEff_storeByte (s := s2) (Rl := [(dst0.toNat, cap)]) hG_s2
          (.var .local (ofString "dst"))
          (.op .add [
            .panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
            .loadByte (.var .local (ofString "nibs"))])
          (fun x hx _ => by
            have hxd : x = dst0 := (by simpa [evalHOLExact, hs2_dst] using hx : dst0 = x).symm
            rw [hxd]
            exact ⟨(dst0.toNat, cap), List.mem_singleton.mpr rfl, le_rfl, by dsimp; omega⟩)).1
      have hsm_loc : sm.locals = s2.locals := by
        dsimp only [sm] at hsb_n ⊢
        rw [evaluateHOLFiniteState_storeByte] at hsb_n ⊢
        split at hsb_n
        · split at hsb_n
          · split at hsb_n <;> simp_all
          · simp at hsb_n
        · simp at hsb_n
      have hasg_ev : evaluateHOLFiniteState sm (.assign .local (ofString "i") (.const 1)) =
          (none, setVarHOLFinite (ofString "i") (.val (.word 1)) sm) := by
        rw [evaluateHOLFiniteState_assign]
        have hsm_i : sm.locals.lookup (ofString "i") = some (.val (.word 0)) := by
          rw [hsm_loc]; simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        simp [evalHOLExact, isValidValueHOLExact, lookupKvarHOLExact, hsm_i,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
      have hsh_eq : sh = setVarHOLFinite (ofString "i") (.val (.word 1)) sm := by
        have := hseq_eq; rw [hhdr, hasg_ev] at this; exact this
      refine ⟨1, Or.inr ⟨hpar, rfl⟩, ?_, ?_, ?_, ?_⟩
      · rw [hsh_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · rw [hsh_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsm_loc, hs2_n,
          show ofString "i" ≠ ofString "n" by decide]
      · rw [hsh_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsm_loc, hs2_dst,
          show ofString "i" ≠ ofString "dst" by decide]
      · rw [hsh_eq]; exact (hs2_eff0.trans hsb_eff).locals_clock _ _
  change (evaluateHOLFiniteState s2 (.seq hdrProg tailProg)).1 = some (.returned v) at hret
  have hrh_none : rh = none := by
    rcases rh with _ | r0
    · rfl
    · exfalso
      rw [evaluateHOLFiniteState_seq_line780, hhdr] at hret
      dsimp only at hret
      injection hret with hr0; subst hr0
      dsimp only [hdrProg] at hhdr
      rw [evaluateHOLFiniteState_ite] at hhdr
      split at hhdr
      · split at hhdr
        · rw [evaluateHOLFiniteState_seq_line780] at hhdr; dsimp only at hhdr
          split at hhdr
          · rw [evaluateHOLFiniteState_assign] at hhdr
            split at hhdr
            · simp at hhdr
            · split at hhdr <;> simp at hhdr
          · rename_i r1 h1
            rw [evaluateHOLFiniteState_storeByte] at h1
            split at h1
            · split at h1
              · split at h1 <;> simp_all
              · simp_all
            · simp_all
        · rw [evaluateHOLFiniteState_storeByte] at hhdr
          split at hhdr
          · split at hhdr
            · split at hhdr <;> simp at hhdr
            · simp at hhdr
          · simp at hhdr
      · simp at hhdr
  obtain ⟨iw, hpar_iw, hsh_i, hsh_n, hsh_dst, hsh_eff⟩ := hhdr_cases hrh_none
  change ∃ ow : BitVec 64,
    v = .val (.word ow) ∧ 1 ≤ ow.toNat ∧ ow.toNat ≤ nw.toNat / 2 + 1 ∧
    R10Shards.P26_P28.ByteEff s
      { (evaluateHOLFiniteState s2 (.seq hdrProg tailProg)).2 with
        locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s2 (.seq hdrProg tailProg)).2.locals
            (ofString "i", s1.locals.lookup (ofString "i")))
          (ofString "flag", s.locals.lookup (ofString "flag")) }
      [(dst0.toNat, cap)]
  rw [evaluateHOLFiniteState_seq_line780, hhdr, hrh_none] at hret ⊢
  dsimp only [tailProg] at hret ⊢
  rw [evaluateHOLFiniteState_dec_total] at hret ⊢
  have hev_o1 : @evalHOLExact 64 F _ sh.toExact (fun a => Classical.propDecidable (sh.memaddrs a))
      (.const 1) = some (.val (.word 1)) := rfl
  have hsh_1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hret ⊢
  rw [hev_o1] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsh_1] at hret ⊢
  let so := setVarHOLFinite (ofString "o") (.val (.word 1)) sh
  rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
  set rlp := (evaluateHOLFiniteState so compactLoop).1 with hrlp_def
  set slp := (evaluateHOLFiniteState so compactLoop).2 with hslp_def
  have hlp : evaluateHOLFiniteState so compactLoop = (rlp, slp) := Prod.ext hrlp_def.symm hslp_def.symm
  rw [hlp] at hret ⊢
  dsimp only at hret ⊢
  have hrlp_none : rlp = none := by
    rcases hr_cases : rlp with _ | r0
    · rfl
    · exfalso
      rw [hr_cases] at hret
      dsimp only at hret
      injection hret with hr0; subst hr0
      exact eval_compactLoop_not_returned so.clock so rfl v (by rw [hlp, hr_cases])
  rw [hrlp_none] at hret hlp ⊢
  dsimp only at hret ⊢
  have hG_so : GuestInv so :=
    guestInv_congr hsh_eff.code hsh_eff.memaddrs hsh_eff.shMemaddrs hsh_eff.baseAddr hG
  have hso_dst : so.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsh_dst,
      show ofString "o" ≠ ofString "dst" by decide]
  have hso_n : so.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsh_n,
      show ofString "o" ≠ ofString "n" by decide]
  have hso_i : so.locals.lookup (ofString "i") = some (.val (.word iw)) := by
    simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsh_i,
      show ofString "o" ≠ ofString "i" by decide]
  have hso_o : so.locals.lookup (ofString "o") = some (.val (.word 1)) := by
    simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have ho_cap_init : ((1 : BitVec 64)).toNat + (nw.toNat + 1 - iw.toNat) / 2 ≤ cap := by
    rcases hpar_iw with ⟨hp0, rfl⟩ | ⟨hp1, rfl⟩
    · change 1 + (nw.toNat + 1) / 2 ≤ cap; omega
    · change 1 + (nw.toNat + 1 - 1) / 2 ≤ cap; omega
  have hi_le_init : iw.toNat ≤ nw.toNat + 1 := by
    rcases hpar_iw with ⟨_, rfl⟩ | ⟨hp1, rfl⟩
    · change 0 ≤ nw.toNat + 1; omega
    · change 1 ≤ nw.toNat + 1; omega
  have how_cap_tight : ((1 : BitVec 64)).toNat + (nw.toNat + 1 - iw.toNat) / 2 ≤ nw.toNat / 2 + 1 := by
    rcases hpar_iw with ⟨hp0, rfl⟩ | ⟨hp1, rfl⟩
    · change 1 + (nw.toNat + 1) / 2 ≤ nw.toNat / 2 + 1; omega
    · change 1 + (nw.toNat + 1 - 1) / 2 ≤ nw.toNat / 2 + 1; omega
  obtain ⟨ow, how1, how_bound, hslp_o, heff_lp⟩ :=
    eval_compactLoop_eff so.clock so dst0 nw iw 1 (nw.toNat / 2 + 1) le_rfl hG_so (by omega)
      hso_dst hso_n hso_i hso_o (by decide) how_cap_tight hi_le_init hnw_hi
      (by rw [hlp])
  have hslp_o' : slp.locals.lookup (ofString "o") = some (.val (.word ow)) := by
    rw [hlp] at hslp_o; exact hslp_o
  have heff_lp' : R10Shards.P26_P28.ByteEff so slp [(dst0.toNat, nw.toNat / 2 + 1)] := by
    rw [hlp] at heff_lp; exact heff_lp
  have heff_lp_cap : R10Shards.P26_P28.ByteEff so slp [(dst0.toNat, cap)] :=
    heff_lp'.mono (fun i hi _ => by
      simp only [List.mem_singleton] at hi; subst hi
      exact ⟨(dst0.toNat, cap), List.mem_singleton.mpr rfl, le_rfl, by dsimp; omega⟩)
  rw [evaluateHOLFiniteState_return] at hret ⊢
  simp [evalHOLExact, hslp_o', shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret ⊢
  subst hret
  refine ⟨ow, rfl, how1, how_bound, ?_⟩
  exact ((hsh_eff.locals_clock so.locals so.clock).trans heff_lp_cap).locals_clock _ _

end RelaxedNodeRlpStack

/-- `BuildMptIndexedReady` / `buildMptIndexedReady_worldOK` now live in `ContractParts/C11.lean`
(wave8 cutover rehearsal). -/

theorem localsOnly_buildMptIndexedReady :
    LocalsOnly ["slice_arr", "n", "out"] BuildMptIndexedReady := by
  intro F s locals k hl h
  have hs : locN {s with locals := locals, clock := k} "slice_arr" = locN s "slice_arr" := by
    simp only [locN, hl "slice_arr" (by simp)]
  have hn : locN {s with locals := locals, clock := k} "n" = locN s "n" := by
    simp only [locN, hl "n" (by simp)]
  refine ⟨localsFree_worldOK s locals k h.1, ?_, ?_⟩
  · intro name hname
    obtain ⟨w, hw⟩ := h.2.1 name hname
    exact ⟨w, (hl name hname).trans hw⟩
  · rw [hs, hn]
    exact h.2.2

theorem lookup_build_mpt_indexed_strong :
    originalRuntimeCode.lookup (ofString "build_mpt_indexed") =
      some ([(ofString "slice_arr", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_build_mpt_indexed, .one) :=
  lookup_of_guestAst_getElem 292 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_build_mpt_indexed) rfl

theorem callEntryOn_buildMptIndexedReady :
    CallEntryOn BuildMptIndexedReady BuildMptIndexedReady (ofString "build_mpt_indexed")
      [.var .local (ofString "slice_arr"), .var .local (ofString "n"),
        .var .local (ofString "out")] := by
  intro F s values body callee ret hcode h hargs hlook
  obtain ⟨v1, v2, v3, he1, he2, he3, hc1, hc2, hc3⟩ :=
    P3MptSet.callee_param_three_exp s (ofString "build_mpt_indexed")
      (ofString "slice_arr") (ofString "n") (ofString "out") .one .one .one _ _
      (by rw [hcode]; exact lookup_build_mpt_indexed_strong) _ _ _
      values body callee ret hargs hlook
  apply localsOnly_buildMptIndexedReady s callee (s.clock - 1) _ h
  intro name hname
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with rfl | rfl | rfl
  · exact hc1.trans (by simpa only [evalAt, evalHOLExact] using he1.symm)
  · exact hc2.trans (by simpa only [evalAt, evalHOLExact] using he2.symm)
  · exact hc3.trans (by simpa only [evalAt, evalHOLExact] using he3.symm)

def BuildMptInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧
    Inside (locN s "m", 16) sourceBase (globN s "heap_ptr") ∧
    ∃ S Nd Nm, WorldTypedWith s S Nd ∧
      MptObjInWith s S Nm (locN s "m") ∧
      IvlsDisj ((locN s "m", 16) :: nodeExtents s Nm) (nodeExtents s Nd)

theorem worldTypedWith_build_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) :
    WorldTypedWith {s with locals := locals, clock := k} S Nd ↔ WorldTypedWith s S Nd := by
  simp only [WorldTypedWith, tablesTyped_with_locals]
  exact Iff.rfl

theorem localsOnly_buildMptInv : LocalsOnly ["m"] BuildMptInv := by
  intro F s locals k hl h
  have hm : locN {s with locals := locals, clock := k} "m" = locN s "m" := by
    simp only [locN, hl "m" (by simp)]
  obtain ⟨hA, hin, S, Nd, Nm, hWT, hobj, hdisj⟩ := h
  refine ⟨localsFree_arenaReady s locals k hA, ?_, S, Nd, Nm,
    (worldTypedWith_build_locals s locals k S Nd).2 hWT, ?_, ?_⟩
  · rw [hm]; exact hin
  · rw [hm]; exact hobj
  · rw [hm]; exact hdisj

theorem buildMptInv_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BuildMptInv s) : WorldOK s := by
  obtain ⟨hA, _, S, Nd, _, hWT, _⟩ := h
  exact ⟨hA, S, (worldTyped_iff_with s S).2 ⟨Nd, hWT⟩⟩

theorem buildMptInv_mptObjReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BuildMptInv s) : MptObjReady s := by
  obtain ⟨hA, _, S, Nd, Nm, hWT, hm, hdisj⟩ := h
  have hS : WorldTyped s S := (worldTyped_iff_with s S).2 ⟨Nd, hWT⟩
  refine ⟨hA, S, hS, ⟨Nm, hm⟩, (fun i hi => by simp at hi), ?_,
    Nm, Nd, hm, hWT.2.2.2, ?_⟩
  · refine ⟨Nd, hWT.2.2.2, ?_⟩
    intro o ho j hj
    simp only [List.mem_singleton] at ho
    subst o
    exact hdisj (locN s "m", 16) (by simp) j hj
  · intro o ho j hj
    exact hdisj o (by simpa using ho) j hj

theorem indexed_lengths_preserved {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {arr n : Nat}
    (hw : WordsOK s (arr, 16 * n))
    (hfit : arr + 16 * n ≤ 2 ^ 64)
    (hu : P3MptSet.IvlUnhit s post (arr, 16 * n))
    (hlen : ∀ i, i < n → memW s (arr + 16 * i + 8) < 2 ^ 40) :
    ∀ i, i < n → memW post (arr + 16 * i + 8) < 2 ^ 40 := by
  intro i hi
  rw [P3MptSet.memW_eq_of_ivlUnhit hu (by have := hw.1; omega) hfit
    (by constructor <;> omega)]
  exact hlen i hi

theorem indexed_lengths_preserved_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {arr n : Nat}
    {keep : List Ivl} {fresh : Ivl}
    (hw : WordsOK s (arr, 16 * n))
    (hfit : arr + 16 * n ≤ 2 ^ 64)
    (hfr : FrameOutside s post keep fresh)
    (hk : ∀ j ∈ keep,
      (j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ Disj (arr, 16 * n) j) ∨
        j.1 + j.2 + 8 ≤ arr)
    (hf_al : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hf : Disj (arr, 16 * n) fresh)
    (hlen : ∀ i, i < n → memW s (arr + 16 * i + 8) < 2 ^ 40) :
    ∀ i, i < n → memW post (arr + 16 * i + 8) < 2 ^ 40 := by
  by_cases hn : n = 0
  · subst n
    intro i hi
    omega
  · exact indexed_lengths_preserved hw hfit
      (P3MptSet.ivlUnhit_of_frameOutside hfr hk hf_al hf (by dsimp; omega)) hlen

theorem indexed_unhit_below_mark {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {arr n mark : Nat}
    {buffers owned : List Ivl}
    (_hw : WordsOK s (arr, 16 * n))
    (hin : Inside (arr, 16 * n) sourceBase mark)
    (hmark : mark ≤ globN s "heap_ptr")
    (hA : ArenaReady s)
    (hfr : FrameOutside s post (buffers ++ owned ++ [freeGap s]) (heapFree s))
    (hbuf : ∀ j ∈ buffers,
      (j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ Disj (arr, 16 * n) j) ∨
        j.1 + j.2 + 8 ≤ arr)
    (howned : ∀ j ∈ owned,
      j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ mark ≤ j.1)
    (hn : n ≠ 0) :
    P3MptSet.IvlUnhit s post (arr, 16 * n) := by
  have hAcopy := hA
  obtain ⟨_, _, hheap, _, _, _, hhp8, hfm8, hsp8⟩ := hAcopy
  have halloc : Allocated s (arr, 16 * n) :=
    Or.inl ⟨hin.1, hin.2.trans hmark⟩
  apply P3MptSet.ivlUnhit_of_frameOutside hfr
  · intro j hj
    simp only [List.mem_append, List.mem_singleton] at hj
    rcases hj with (hj | hj) | rfl
    · exact hbuf j hj
    · obtain ⟨ha, hl, hm⟩ := howned j hj
      exact Or.inl ⟨ha, hl, Or.inr (Or.inr (Or.inl (hin.2.trans hm)))⟩
    · exact Or.inl ⟨hfm8, by dsimp [freeGap]; omega,
        P3MptSet.disj_allocated_freeGap hA.2 halloc⟩
  · refine ⟨hhp8, ?_⟩
    have : heapLimit % 8 = 0 := by decide
    dsimp [heapFree]
    omega
  · exact P3MptSet.disj_allocated_heapFree hA.2 halloc
  · dsimp; omega

theorem indexed_lengths_preserved_below_mark {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {arr n mark : Nat}
    {buffers owned : List Ivl}
    (hw : WordsOK s (arr, 16 * n))
    (hin : Inside (arr, 16 * n) sourceBase mark)
    (hmark : mark ≤ globN s "heap_ptr")
    (hA : ArenaReady s)
    (hfr : FrameOutside s post (buffers ++ owned ++ [freeGap s]) (heapFree s))
    (hbuf : ∀ j ∈ buffers,
      (j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ Disj (arr, 16 * n) j) ∨
        j.1 + j.2 + 8 ≤ arr)
    (howned : ∀ j ∈ owned,
      j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ mark ≤ j.1)
    (hlen : ∀ i, i < n → memW s (arr + 16 * i + 8) < 2 ^ 40) :
    ∀ i, i < n → memW post (arr + 16 * i + 8) < 2 ^ 40 := by
  by_cases hn : n = 0
  · subst n
    intro i hi
    omega
  · apply indexed_lengths_preserved hw ?_
      (indexed_unhit_below_mark hw hin hmark hA hfr hbuf howned hn) hlen
    have hlim : heapLimit ≤ 2 ^ 64 := by decide
    have hheap := hA.2.2.1
    have hbound := hin.2.trans hmark
    dsimp only at hbound
    omega

theorem buildMptIndexedReady_of_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (h : BuildMptIndexedReady s)
    (hW : WorldOK post)
    (hl : ∀ name ∈ (["slice_arr", "n", "out"] : List String),
      post.locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hbuf : ∀ gn ∈ ([("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
        ("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion post gn = bufferRegion s gn)
    (hu : P3MptSet.IvlUnhit s post (locN s "slice_arr", 16 * locN s "n")) :
    BuildMptIndexedReady post := by
  have harr : locN post "slice_arr" = locN s "slice_arr" := by
    simp only [locN, hl "slice_arr" (by simp)]
  have hn : locN post "n" = locN s "n" := by
    simp only [locN, hl "n" (by simp)]
  obtain ⟨hWs, hlocals, hnb, hin, hw, hd, hlen⟩ := h
  refine ⟨hW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name hname
    obtain ⟨w, he⟩ := hlocals name hname
    exact ⟨w, (hl name hname).trans he⟩
  · rw [hn]; exact hnb
  · rw [harr, hn]
    exact ⟨hin.1, hin.2.trans hhp⟩
  · rw [harr, hn]
    exact P3MptSet.wordsOK_transfer hWs.1.1 hW.1.1 hw
  · rw [harr, hn]
    intro i hi j hj
    obtain ⟨gn, hgn, rfl⟩ := List.mem_map.mp hj
    rw [hbuf gn hgn]
    exact hd i hi _ (List.mem_map.mpr ⟨gn, hgn, rfl⟩)
  · rw [harr, hn]
    apply indexed_lengths_preserved hw ?_ hu hlen
    have hheap := hW.1.2.2.1
    have hlim : heapLimit ≤ 2 ^ 64 := by decide
    have hbound := hin.2.trans hhp
    dsimp only at hbound
    omega

theorem buildMptIndexedReady_preserved_below_mark {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {mark : Nat}
    {buffers owned : List Ivl}
    (h : BuildMptIndexedReady s)
    (hW : WorldOK post)
    (hl : ∀ name ∈ (["slice_arr", "n", "out"] : List String),
      post.locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hbuf : ∀ gn ∈ ([("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
        ("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion post gn = bufferRegion s gn)
    (hin : Inside (locN s "slice_arr", 16 * locN s "n") sourceBase mark)
    (hmark : mark ≤ globN s "heap_ptr")
    (hfr : FrameOutside s post (buffers ++ owned ++ [freeGap s]) (heapFree s))
    (hbuffers : ∀ j ∈ buffers,
      (j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ Disj (locN s "slice_arr", 16 * locN s "n") j) ∨
        j.1 + j.2 + 8 ≤ locN s "slice_arr")
    (howned : ∀ j ∈ owned,
      j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ mark ≤ j.1) :
    BuildMptIndexedReady post := by
  by_cases hn : locN s "n" = 0
  · have harr : locN post "slice_arr" = locN s "slice_arr" := by
      simp only [locN, hl "slice_arr" (by simp)]
    have hnpost : locN post "n" = 0 := by
      simpa only [locN, hl "n" (by simp)] using hn
    obtain ⟨hWs, hlocals, _, hins, hw, hd, _⟩ := h
    refine ⟨hW, ?_, by rw [hnpost]; decide, ?_, ?_, ?_, ?_⟩
    · intro name hname
      obtain ⟨w, he⟩ := hlocals name hname
      exact ⟨w, (hl name hname).trans he⟩
    · rw [harr, hnpost]
      simpa only [hn] using (show Inside (locN s "slice_arr", 16 * locN s "n")
        sourceBase (globN post "heap_ptr") from ⟨hins.1, hins.2.trans hhp⟩)
    · rw [harr, hnpost]
      simpa only [hn] using P3MptSet.wordsOK_transfer hWs.1.1 hW.1.1 hw
    · rw [harr, hnpost]
      intro i hi j hj
      obtain ⟨gn, hgn, rfl⟩ := List.mem_map.mp hj
      rw [hbuf gn hgn]
      apply hd i (by simpa only [hn] using hi)
      exact List.mem_map.mpr ⟨gn, hgn, rfl⟩
    · intro i hi
      rw [hnpost] at hi
      omega
  · exact buildMptIndexedReady_of_unhit h hW hl hhp hbuf
      (indexed_unhit_below_mark h.2.2.2.2.1 hin hmark h.1.1 hfr hbuffers howned hn)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
