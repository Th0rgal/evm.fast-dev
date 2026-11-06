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
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRoot
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_C08WkShard03
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure1
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure2
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure3
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P02
import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmFrameSpecs
import InitECandidate.Solver.Wave8GuestInv.R10Ports.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_memeq

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
  cell_frame : ∀ a : BitVec 64, (∀ i ∈ Rl, ¬ R10Shards.P26_P28.CellHitsPos a.toNat i) →
    ¬ R10Shards.P26_P28.CellHitsPos a.toNat (globN s "heap_ptr", heapLimit - globN s "heap_ptr") →
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
    intro i hi ⟨hipos, hc1, hc2⟩
    rcases hsub i hi with ⟨j, hj, h1, h2⟩ | ⟨hh1, hh2⟩
    · exact ha j hj ⟨by omega, by omega, by omega⟩
    · exact hfr ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
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
    have hfr_mid : ¬ R10Shards.P26_P28.CellHitsPos a.toNat (globN mid "heap_ptr", heapLimit - globN mid "heap_ptr") := by
      intro ⟨hpos, hc1, hc2⟩
      dsimp only at hpos hc1 hc2
      have hmid_hi := h1.arena.2.2.1
      exact hfr ⟨by dsimp only; have := h1.heap_le; omega,
        by dsimp only; have := h1.heap_le; omega, by dsimp only; omega⟩
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
    obtain ⟨i, hi, hipos, hc⟩ := heff.cell_frame a hne
    exact ha i hi ⟨hipos, hc⟩
  · intro b hb hno _
    by_contra hne
    obtain ⟨i, hi, hin⟩ := heff.byte_frame b hb hne
    exact hno i hi hin

theorem EncFrame.of_store_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl}
    (hA : ArenaReady s)
    (hval : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) → s.memaddrs addr →
      (∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ i.1 + i.2) ∨
        (globN s "heap_ptr" ≤ addr.toNat ∧ addr.toNat + 8 ≤ heapLimit)) :
    EncFrame s (evaluateHOLFiniteState s (.store dst val)).2 Rl := by
  let heap := (globN s "heap_ptr", heapLimit - globN s "heap_ptr")
  have hbyte := (R10Shards.P26_P28.byteEff_store_one
    (Rl := heap :: Rl) hA.1 dst val hval (by
      intro addr hd hm
      rcases hin addr hd hm with ⟨i, hi, h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨i, List.mem_cons_of_mem _ hi, h1, h2⟩
      · exact ⟨heap, List.mem_cons_self, h1, by
          dsimp only [heap]
          have := hA.2.2.1
          omega⟩)).1
  apply (EncFrame.of_byteEff hA hbyte).mono
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · exact Or.inr ⟨le_rfl, by dsimp only [heap]; have := hA.2.2.1; omega⟩
  · exact Or.inl ⟨i, hi, le_rfl, le_rfl⟩

theorem EncFrame.of_storeByte {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl}
    (hA : ArenaReady s)
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) → s.memaddrs (panByteAlignHOL addr) →
      (∃ i ∈ Rl, InIvl addr.toNat i) ∨
        (globN s "heap_ptr" ≤ addr.toNat ∧ addr.toNat < heapLimit)) :
    EncFrame s (evaluateHOLFiniteState s (.storeByte dst val)).2 Rl := by
  let heap := (globN s "heap_ptr", heapLimit - globN s "heap_ptr")
  have hbyte := (R10Shards.P26_P28.byteEff_storeByte
    (Rl := heap :: Rl) hA.1 dst val (by
      intro addr hd hm
      rcases hin addr hd hm with ⟨i, hi, hmem⟩ | ⟨h1, h2⟩
      · exact ⟨i, List.mem_cons_of_mem _ hi, hmem⟩
      · exact ⟨heap, List.mem_cons_self, h1, by
          dsimp only [heap]
          have := hA.2.2.1
          omega⟩)).1
  apply (EncFrame.of_byteEff hA hbyte).mono
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · exact Or.inr ⟨le_rfl, by dsimp only [heap]; have := hA.2.2.1; omega⟩
  · exact Or.inl ⟨i, hi, le_rfl, le_rfl⟩

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

theorem alloc_returned_size_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1 =
      some (.returned v)) :
    globN s "heap_ptr" + locN s "n" ≤
      globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2 "heap_ptr" ∧
    locN s "n" < 2 ^ 40 := by
  obtain ⟨p, _, hp, hpost, heff⟩ :=
    EncFrame.of_alloc_returned (Rl := []) hc hA hret
  have hlimit := heff.arena.2.2.1
  have hheap : heapLimit < 2 ^ 40 := by decide
  rw [hpost] at hlimit ⊢
  rw [hp] at hlimit ⊢
  omega

theorem alloc_returned_heap_progress {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (v : ValueHOL 64) (hn : 0 < locN s "n")
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1 =
      some (.returned v)) :
    globN s "heap_ptr" <
      globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2 "heap_ptr" := by
  have hsize := (alloc_returned_size_bound s hc hA v hret).1
  omega

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
    rcases h.cell_frame a hne with ⟨i, hi, hipos, hc⟩ | hfg | hhf
    · exact ha i (List.mem_cons_of_mem _ hi) ⟨hipos, hc⟩
    · exact ha (freeGapIvl s) List.mem_cons_self hfg
    · exact hfr hhf
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
    exact ha i hi ⟨by omega, by omega, by omega⟩
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

theorem eval_call_mpt_fail_no_none_no_ret {F : Type}
    (s : PanSemStateFiniteExact 64 F) (c : BitVec 64) (hc : s.code = originalRuntimeCode) :
    let out := evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_fail") [.const c])
    out.1 ≠ none ∧ (∀ v, out.1 ≠ some (.returned v)) := by
  dsimp only
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const c] =
      some [.val (.word c)] := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "mpt_fail") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_mpt_fail) c (by rw [hc]; exact lookup_mpt_fail_rel)
  rw [hargs]; dsimp only; rw [hlk]; dsimp only
  split
  · exact ⟨by simp, fun _ => by simp⟩
  · have hb : sourceFnBody Guest.Software.guestFn_mpt_fail =
        .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
    have hraise_out : ∀ st : PanSemStateFiniteExact 64 F,
        let ro := (evaluateHOLFiniteState st (.raise (ofString "MptErr") (.var .local (ofString "code")))).1
        ro = some .error ∨ ∃ ev, ro = some (.exception (ofString "MptErr") ev) := by
      intro st; dsimp only; rw [evaluateHOLFiniteState_raise]
      split
      · dsimp only; split <;> simp
      · simp
    let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "code", .val (.word c)))
    rcases hbody : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_mpt_fail) with ⟨res, st⟩
    have hr := hraise_out entry
    rw [hb, evaluateHOLFiniteState_seq_line780] at hbody
    rcases hr_st : evaluateHOLFiniteState entry (.raise (ofString "MptErr") (.var .local (ofString "code"))) with ⟨rr, sr⟩
    rw [hr_st] at hr hbody
    dsimp only at hr hbody
    rcases hr with rfl | ⟨ev, rfl⟩
    · injection hbody with h1 _; subst h1; exact ⟨by simp, fun _ => by simp⟩
    · injection hbody with h1 _; subst h1; exact ⟨by simp, fun _ => by simp⟩

theorem eval_rlp_header_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).1 =
      some (.returned v)) :
    ∃ hl : BitVec 64,
      v = .val (.word hl) ∧ 1 ≤ hl.toNat ∧ hl.toNat ≤ 9 ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).2.clock } := by
  have hro := evaluate_roEncProg (sourceFnBody Guest.Software.guestFn_rlp_header_len) rfl s hc
  have hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).1 ≠ some .timeOut := by
    rw [hret]; simp
  rcases hn : s.locals.lookup (ofString "n") with _ | nv
  · have hb : sourceFnBody Guest.Software.guestFn_rlp_header_len =
        .seq
          (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n"))) (.return (.const 1)) .skip)
          (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
            (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
    rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
    simp [evalHOLExact, hn] at hret
  · rcases nv with ⟨⟨nw⟩⟩ | _ | _
    · obtain ⟨hret_eq, _⟩ := R16Shards.WkBlockTxEnc.eval_rlp_header_len_body_exact s nw hc hn hnt
      rw [hret] at hret_eq
      injection hret_eq with h1; injection h1 with h2; subst h2
      have hbnd := R16Shards.WkBlockTxEnc.rlpHeaderLenPure_bounds nw.toNat
      have hnat : (BitVec.ofNat 64 (R16Shards.WkBlockTxEnc.rlpHeaderLenPure nw.toNat)).toNat =
          R16Shards.WkBlockTxEnc.rlpHeaderLenPure nw.toNat := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      exact ⟨_, rfl, by omega, by omega, hro⟩
    · have hb : sourceFnBody Guest.Software.guestFn_rlp_header_len =
          .seq
            (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n"))) (.return (.const 1)) .skip)
            (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
              (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
      simp [evalHOLExact, hn, valueIsWord] at hret
    · have hb : sourceFnBody Guest.Software.guestFn_rlp_header_len =
          .seq
            (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n"))) (.return (.const 1)) .skip)
            (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
              (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
      simp [evalHOLExact, hn, valueIsWord] at hret

theorem eval_rlp_bytes_encoded_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (nw : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnw60 : nw.toNat < 2 ^ 60)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len)).1 =
      some (.returned v)) :
    ∃ el : BitVec 64,
      v = .val (.word el) ∧ 1 ≤ el.toNat ∧ el.toNat ≤ nw.toNat + 9 ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len)).2.clock } := by
  have hro := evaluate_roEncProg (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) rfl s hc
  have hb : sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len =
      .seq
        (.ite (.op .and [
            .cmp .notEqual (.const 0#64) (.cmp .equal (.var .local (ofString "n")) (.const 1#64)),
            .cmp .notEqual (.const 0#64) (.cmp .lower (.var .local (ofString "first_byte")) (.const 128#64))])
          (.return (.const 1#64))
          .skip)
        (.decCall (ofString "h") .one (ofString "rlp_header_len") [.var .local (ofString "n")]
          (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .and [
        .cmp .notEqual (.const 0#64) (.cmp .equal (.var .local (ofString "n")) (.const 1#64)),
        .cmp .notEqual (.const 0#64) (.cmp .lower (.var .local (ofString "first_byte")) (.const 128#64))]) with _ | cv
  · simp [hcond] at hret
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · simp only [hcond] at hret
      by_cases hcw0 : cw = 0
      · rw [if_pos hcw0, evaluateHOLFiniteState_skip] at hret
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
        have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            [.var .local (ofString "n")] = some [.val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
        have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_header_len") (ofString "n")
          (sourceFnBody Guest.Software.guestFn_rlp_header_len) nw (by rw [hc]; exact lookup_rlp_header_len)
        simp only [hargs, hlk] at hret
        by_cases hclk0 : s.clock = 0
        · simp [hclk0] at hret
        · simp only [hclk0, ↓reduceIte] at hret
          let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nw)))
          rcases hcal : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_header_len) with ⟨rc, sc⟩
          have hcal' : evaluateHOLFiniteState
              (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nw))))
              (sourceFnBody Guest.Software.guestFn_rlp_header_len) = (rc, sc) := hcal
          simp only [hcal'] at hret
          cases rc with
          | none => simp at hret
          | some rc' =>
            cases rc' with
            | returned vc =>
              obtain ⟨hlw, rfl, h1, h9, _⟩ := eval_rlp_header_len_returned entry hc vc (by rw [hcal])
              have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hlw) : ValueHOL 64)) .one &&
                  shapeEqHOL (shapeOfHOLExact (.val (.word hlw) : ValueHOL 64)) .one) = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              simp only [hsh, ↓reduceIte] at hret
              let resSt := setVarHOLFinite (ofString "h") (.val (.word hlw)) { sc with locals := s.locals }
              rw [evaluateHOLFiniteState_return] at hret
              have hev_add : @evalHOLExact 64 F _ resSt.toExact (fun a => Classical.propDecidable (resSt.memaddrs a))
                  (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) =
                  some (.val (.word (hlw + nw))) := by
                have hne : ofString "h" ≠ ofString "n" := by decide
                simp [resSt, evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  hne, Ne.symm hne, hn, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
              have hsz : sizeOfShapeWithContextHOL resSt.structs
                  (shapeOfHOLExact (.val (.word (hlw + nw)) : ValueHOL 64)) ≤ 32 := by simp [shapeOfHOLExact]
              rw [hev_add] at hret; dsimp only at hret; rw [if_pos hsz] at hret
              injection hret with hr; injection hr with hr'; subst hr'
              have hsum : (hlw + nw).toNat = hlw.toNat + nw.toNat := by
                rw [BitVec.toNat_add]; omega
              exact ⟨hlw + nw, rfl, by omega, by omega, hro⟩
            | _ => simp at hret
      · rw [if_neg hcw0] at hret
        rw [evaluateHOLFiniteState_return] at hret
        simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
        subst hret
        exact ⟨1#64, rfl, by decide, by change 1 ≤ nw.toNat + 9; omega, hro⟩
    · simp [hcond] at hret
    · simp [hcond] at hret

theorem eval_rlp_value_encoded_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (pw nw : BitVec 64)
    (_hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnw60 : nw.toNat < 2 ^ 60)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len)).1 =
      some (.returned v)) :
    ∃ vl : BitVec 64,
      v = .val (.word vl) ∧ 1 ≤ vl.toNat ∧ vl.toNat ≤ nw.toNat + 9 ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len)).2.clock } := by
  have hro := evaluate_roEncProg (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len) rfl s hc
  have hb : sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len =
      .dec (ofString "fb") .one (.const 0)
        (.seq
          (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
            (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p"))))
            .skip)
          (.call none (ofString "rlp_bytes_encoded_len")
            [.var .local (ofString "fb"), .var .local (ofString "n")])) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [hev0] at hret; dsimp only at hret; rw [if_pos hsh0] at hret
  let s1 := setVarHOLFinite (ofString "fb") (.val (.word 0)) s
  change (evaluateHOLFiniteState s1 (.seq
    (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
      (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p"))))
      .skip)
    (.call none (ofString "rlp_bytes_encoded_len")
      [.var .local (ofString "fb"), .var .local (ofString "n")]))).1 = some (.returned v) at hret
  rw [evaluateHOLFiniteState_seq_line780] at hret
  rcases hite : evaluateHOLFiniteState s1
      (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
        (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p"))))
        .skip) with ⟨ri, si⟩
  have hite' : evaluateHOLFiniteState s1
      (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
        (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p"))))
        .skip) = (ri, si) := hite
  have hsi_code : si.code = originalRuntimeCode := by
    have hm := (InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata s1
      (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
        (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p")))) .skip)).1
    rw [hite] at hm; exact hm.trans hc
  have hsi_n : ri = none → si.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    intro hri
    have hn_keep := evaluate_avoidsLocal_flowing (ofString "n")
      (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
        (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p")))) .skip)
      (by decide) s1 (Or.inl (by rw [hite]; exact hri))
    rw [hite] at hn_keep
    have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
        show ofString "fb" ≠ ofString "n" by decide]
    exact hn_keep.trans hs1_n
  simp only [hite'] at hret
  cases ri with
  | some ri' =>
    injection hret with hr_eq; subst hr_eq
    rw [evaluateHOLFiniteState_ite] at hite
    split at hite
    · split at hite
      · rw [evaluateHOLFiniteState_skip] at hite; cases hite
      · rw [evaluateHOLFiniteState_assign] at hite
        split at hite
        · cases hite
        · split at hite <;> cases hite
    · cases hite
  | none =>
    have hsin := hsi_n rfl
    change (evaluateHOLFiniteState si (.call none (ofString "rlp_bytes_encoded_len")
      [.var .local (ofString "fb"), .var .local (ofString "n")])).1 = some (.returned v) at hret
    rw [evaluateHOLFiniteState_call] at hret
    rcases hfb : si.locals.lookup (ofString "fb") with _ | fbv
    · simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb] at hret
    · rcases fbv with ⟨⟨fbw⟩⟩ | fs | ⟨nm, fs⟩
      · have hargs : evalListHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
            [.var .local (ofString "fb"), .var .local (ofString "n")] =
            some [.val (.word fbw), .val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb, hsin]
        have hlk := pan_two_word_lookup si.code.lookup (ofString "rlp_bytes_encoded_len")
          (ofString "first_byte") (ofString "n")
          (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) fbw nw
          (by decide) (by rw [hsi_code]; exact lookup_rlp_bytes_encoded_len)
        simp only [hargs, hlk] at hret
        by_cases hclk0 : si.clock = 0
        · simp [hclk0] at hret
        · simp only [hclk0, ↓reduceIte] at hret
          let cmap := (HolFiniteMapExact.empty.update (ofString "first_byte", ValueHOL.val (.word fbw))).update
            (ofString "n", ValueHOL.val (.word nw))
          let entry := callEntryStateHOLFinite si cmap
          have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rcases hcal : evaluateHOLFiniteState entry
              (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) with ⟨rc, sc⟩
          have hcal' := hcal
          dsimp only [entry, cmap] at hcal'
          rw [hcal'] at hret
          cases rc with
          | none => simp at hret
          | some rc' =>
            cases rc' with
            | returned vc =>
              obtain ⟨el, rfl, h1, hub, _⟩ := eval_rlp_bytes_encoded_len_returned entry hsi_code nw hent_n hnw60 vc (by rw [hcal])
              have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word el) : ValueHOL 64)) .one = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              simp only [hsh, ↓reduceIte] at hret
              injection hret with hr; injection hr with hr'; subst hr'
              exact ⟨el, rfl, h1, hub, hro⟩
            | _ => simp at hret
      · have hargs : evalListHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
            [.var .local (ofString "fb"), .var .local (ofString "n")] =
            some [ValueHOL.rStruct fs, .val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb, hsin]
        have hnone : PanSemStateFiniteExact.lookupCodeHOLFinite si.code.lookup (ofString "rlp_bytes_encoded_len")
            [ValueHOL.rStruct fs, .val (.word nw)] = none := by
          rw [hsi_code]; unfold PanSemStateFiniteExact.lookupCodeHOLFinite
          have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len")
              [ValueHOL.rStruct fs, .val (.word nw)] = none := by
            simp [lookupCodeHOLExact, lookup_rlp_bytes_encoded_len, shapeOfHOLExact, shapeEqHOL]
          split
          · rfl
          · rename_i _ _ _ h; rw [hraw] at h; cases h
        rw [hargs] at hret; dsimp only at hret; rw [hnone] at hret; cases hret
      · have hargs : evalListHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
            [.var .local (ofString "fb"), .var .local (ofString "n")] =
            some [ValueHOL.nStruct nm fs, .val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb, hsin]
        have hnone : PanSemStateFiniteExact.lookupCodeHOLFinite si.code.lookup (ofString "rlp_bytes_encoded_len")
            [ValueHOL.nStruct nm fs, .val (.word nw)] = none := by
          rw [hsi_code]; unfold PanSemStateFiniteExact.lookupCodeHOLFinite
          have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len")
              [ValueHOL.nStruct nm fs, .val (.word nw)] = none := by
            simp [lookupCodeHOLExact, lookup_rlp_bytes_encoded_len, shapeOfHOLExact, shapeEqHOL]
          split
          · rfl
          · rename_i _ _ _ h; rw [hraw] at h; cases h
        rw [hargs] at hret; dsimp only at hret; rw [hnone] at hret; cases hret

theorem eval_node_ref_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).1 =
      some (.returned v)) :
    ∃ rl : BitVec 64,
      v = .val (.word rl) ∧ rl.toNat ≤ 33 ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).2.clock } := by
  have hro := evaluate_roEncProg (sourceFnBody Guest.Software.guestFn_node_ref_len) rfl s hc
  have hb : sourceFnBody Guest.Software.guestFn_node_ref_len =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "child")) (.const 0)) (.return (.const 1)) .skip)
        (.seq
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
            (.return (.const 33)) .skip)
          (.seq
            (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
              (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip)
            (.dec (ofString "rl") .one (.load .one (.op .add [.var .local (ofString "child"), .const 16]))
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "rl")) (.const 32))
                  (.return (.var .local (ofString "rl"))) .skip)
                (.return (.const 33)))))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780] at hret
  rcases h1 : evaluateHOLFiniteState s
      (.ite (.cmp .equal (.var .local (ofString "child")) (.const 0)) (.return (.const 1)) .skip) with ⟨r1, s1⟩
  simp only [h1] at hret
  cases r1 with
  | some r1' =>
    rw [evaluateHOLFiniteState_ite] at h1
    split at h1
    · split at h1
      · rw [evaluateHOLFiniteState_skip] at h1; cases h1
      · rw [evaluateHOLFiniteState_return] at h1
        simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at h1
        obtain ⟨rfl, _⟩ := h1; simp at hret; subst hret
        exact ⟨1, rfl, by decide, hro⟩
    · injection h1 with hr _; cases hr; simp at hret
  | none =>
    have hs1 : s1 = s := by
      rw [evaluateHOLFiniteState_ite] at h1
      split at h1
      · split at h1
        · rw [evaluateHOLFiniteState_skip] at h1; exact (Prod.mk.inj h1).2.symm
        · exfalso; exact return_ne_none s _ (congrArg Prod.fst h1)
      · cases h1
    rw [hs1] at hret
    rw [evaluateHOLFiniteState_seq_line780] at hret
    rcases h2 : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
          (.return (.const 33)) .skip) with ⟨r2, s2⟩
    simp only [h2] at hret
    cases r2 with
    | some r2' =>
      rw [evaluateHOLFiniteState_ite] at h2
      split at h2
      · split at h2
        · rw [evaluateHOLFiniteState_skip] at h2; cases h2
        · rw [evaluateHOLFiniteState_return] at h2
          simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at h2
          obtain ⟨rfl, _⟩ := h2; simp at hret; subst hret
          exact ⟨33, rfl, by decide, hro⟩
      · injection h2 with hr _; cases hr; simp at hret
    | none =>
      have hs2 : s2 = s := by
        rw [evaluateHOLFiniteState_ite] at h2
        split at h2
        · split at h2
          · rw [evaluateHOLFiniteState_skip] at h2; exact (Prod.mk.inj h2).2.symm
          · exfalso; exact return_ne_none s _ (congrArg Prod.fst h2)
        · cases h2
      rw [hs2] at hret
      rw [evaluateHOLFiniteState_seq_line780] at hret
      rcases h3 : evaluateHOLFiniteState s
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) with ⟨r3, s3⟩
      simp only [h3] at hret
      have hmf := eval_call_mpt_fail_no_none_no_ret s 13 hc
      cases r3 with
      | some r3' =>
        injection hret with hr3; subst hr3
        rw [evaluateHOLFiniteState_ite] at h3
        split at h3
        · split at h3
          · rw [evaluateHOLFiniteState_skip] at h3; cases h3
          · exact False.elim (hmf.2 v (congrArg Prod.fst h3))
        · cases h3
      | none =>
        have hs3 : s3 = s := by
          rw [evaluateHOLFiniteState_ite] at h3
          split at h3
          · split at h3
            · rw [evaluateHOLFiniteState_skip] at h3; exact (Prod.mk.inj h3).2.symm
            · exact False.elim (hmf.1 (congrArg Prod.fst h3))
          · cases h3
        rw [hs3] at hret
        change (evaluateHOLFiniteState s (.dec (ofString "rl") .one
          (.load .one (.op .add [.var .local (ofString "child"), .const 16]))
          (.seq
            (.ite (.cmp .lower (.var .local (ofString "rl")) (.const 32))
              (.return (.var .local (ofString "rl"))) .skip)
            (.return (.const 33))))).1 = some (.returned v) at hret
        rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
        rcases hld : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "child"), .const 16])) with _ | rlv
        · rw [hld] at hret; cases hret
        · obtain ⟨rlw, rfl⟩ := R10Shards.P26_P28.eval_load_one_word s _ rlv hld
          have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word rlw) : ValueHOL 64)) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [hld] at hret; dsimp only at hret; rw [if_pos hsh] at hret; dsimp only at hret
          let s4 := setVarHOLFinite (ofString "rl") (.val (.word rlw)) s
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
          have hcmp : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
              (.cmp .lower (.var .local (ofString "rl")) (.const 32)) =
              some (.val (.word (if rlw.toNat < 32 then 1 else 0))) := by
            simp [s4, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
          rw [hcmp] at hret; dsimp only at hret
          by_cases hlt32 : rlw.toNat < 32
          · rw [if_pos hlt32] at hret
            have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
            rw [if_neg h10, evaluateHOLFiniteState_return] at hret
            simp [s4, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
            subst hret
            exact ⟨rlw, rfl, by omega, hro⟩
          · rw [if_neg hlt32] at hret
            simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hret
            rw [evaluateHOLFiniteState_return] at hret
            simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
            subst hret
            exact ⟨33, rfl, by decide, hro⟩

/-! ### `NodeHeap` preservation under `EncFrame` over node cache slots (`+8`, `+16`, `+24`) -/

def nodeCacheIvls (Nd : List Nat) : List Ivl :=
  Nd.map (fun n => (n + 8, 24))

def nodeHashCacheIvls (Nd : List Nat) : List Ivl :=
  Nd.map (fun n => (n + 24, 8))

def keccakScratchIvls {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200)]

theorem EncFrame.allocatorGrows {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : EncFrame s post Rl) : AllocatorGrows s post := by
  have hsp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    have hk := h.nonHeap (ofString "scratch_ptr") (by decide)
    simp only [globN, hk]
  exact ⟨h.heap_le, by omega⟩

theorem nodeIvl_lt_heap_ptr {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hA : ArenaOK s) (hNh : NodeHeap s Nd) {n : Nat} (hn : n ∈ Nd) :
    sourceBase ≤ n ∧ n + (nodeIvl s n).2 ≤ globN s "heap_ptr" :=
  relaxedNodeIvl_lt_heap_ptr hA (relaxedNodeHeap_of_nodeHeap hNh) hn

theorem keyIn_lt_heap_ptr {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hA : ArenaOK s) {p len : Nat} (hkey : KeyIn s Nd p len) (hlen : len ≠ 0) :
    sourceBase ≤ p ∧ p + len ≤ globN s "heap_ptr" := by
  rcases hkey with rfl | ⟨_, hal, hin, _⟩
  · exact absurd rfl hlen
  · rcases hal with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact ⟨h1, h2⟩
    · have hsep : heapLimit ≤ scratchStart := by decide
      have h2 := hin.2
      have hsp := hA.2.2.1
      have hfm := hA.2.2.2.1
      omega

theorem EncFrame.memW_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (heff : EncFrame s post Rl) {a : Nat} (ha8 : a % 8 = 0) (ha_lt : a + 8 ≤ globN s "heap_ptr")
    (hno : ∀ i ∈ Rl, ¬ R10Shards.P26_P28.CellHitsPos a i) :
    memW post a = memW s a := by
  have hlim : globN s "heap_ptr" ≤ heapLimit := by
    have := heff.arena.2.2.1; have := heff.heap_le; omega
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have ha64 : a < 2 ^ 64 := by omega
  have hbv : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64]
  unfold memW
  rw [heff.cell_frame (BitVec.ofNat 64 a)]
  · intro i hi hc
    rw [hbv] at hc
    exact hno i hi hc
  · intro ⟨_, hc1, hc2⟩
    rw [hbv] at hc1 hc2
    dsimp only at hc1 hc2
    omega

theorem EncFrame.memB_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (heff : EncFrame s post Rl) {b : Nat} (hb_lt : b < globN s "heap_ptr")
    (hno : ∀ i ∈ Rl, ¬ InIvl b i) :
    memB post b = memB s b := by
  have hlim : globN s "heap_ptr" ≤ heapLimit := by
    have := heff.arena.2.2.1; have := heff.heap_le; omega
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  apply heff.byte_frame b (by omega) hno
  intro ⟨h1, _⟩
  dsimp only at h1
  omega

theorem relaxedNodeHeap_preserved_of_encFrame_cache {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {Rl_extra : List Ivl}
    (hAs : ArenaReady s)
    (heff : EncFrame s post (nodeCacheIvls Nd ++ Rl_extra))
    (hN : RelaxedNodeHeap s Nd)
    (hdisj_extra : ∀ r ∈ Rl_extra, ∀ o ∈ nodeExtents s Nd, Disj r o)
    (hrlp_len : ∀ n ∈ Nd, memW post (n + 16) < 2 ^ 40) :
    RelaxedNodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have hag := heff.allocatorGrows
  have hno_extra_w : ∀ {o : Ivl}, o ∈ nodeExtents s Nd → ∀ {a : Nat},
      o.1 ≤ a → a + 8 ≤ o.1 + o.2 → ∀ r ∈ Rl_extra, ¬ R10Shards.P26_P28.CellHitsPos a r := by
    intro o ho a ha1 ha2 r hr ⟨hrpos, hc1, hc2⟩
    rcases hdisj_extra r hr o ho with h0 | h0 | hd | hd <;> omega
  have hno_extra_b : ∀ {o : Ivl}, o ∈ nodeExtents s Nd → ∀ {b : Nat},
      o.1 ≤ b → b < o.1 + o.2 → ∀ r ∈ Rl_extra, ¬ InIvl b r := by
    intro o ho b hb1 hb2 r hr ⟨hc1, hc2⟩
    rcases hdisj_extra r hr o ho with h0 | h0 | hd | hd <;> omega
  have hno_cache_non123 : ∀ {n : Nat}, n ∈ Nd → ∀ {k : Nat},
      k < nodeSize (memW s n) / 8 → k ≠ 1 → k ≠ 2 → k ≠ 3 →
      ∀ i ∈ nodeCacheIvls Nd, ¬ R10Shards.P26_P28.CellHitsPos (n + 8 * k) i := by
    intro n hn k hk hk1 hk2 hk3 i hi ⟨_, hc1, hc2⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hi
    dsimp only at hc1 hc2
    by_cases hnm : n = m
    · subst hnm; omega
    · have hsz_n : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
      have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
      have hsz8 : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> omega
      rcases hN.2 n hn m hm hnm with h0 | h0 | hd | hd
      · dsimp [nodeIvl] at h0; omega
      · dsimp [nodeIvl] at h0; omega
      · dsimp [nodeIvl] at hd; omega
      · dsimp [nodeIvl] at hd; omega
  have hn_mem_ext : ∀ {n : Nat}, n ∈ Nd → nodeIvl s n ∈ nodeExtents s Nd := by
    intro n hn; unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
  have hn_wk : ∀ {n : Nat} (hn : n ∈ Nd) {k : Nat} (hk : k < nodeSize (memW s n) / 8),
      k ≠ 1 → k ≠ 2 → k ≠ 3 → memW post (n + 8 * k) = memW s (n + 8 * k) := by
    intro n hn k hk hk1 hk2 hk3
    have hn8 : n % 8 = 0 := (hN.1 n hn).2.2.2.1.1
    have hlt := (relaxedNodeIvl_lt_heap_ptr hAs.2 hN hn).2
    have hsz8 : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> omega
    dsimp [nodeIvl] at hlt
    apply heff.memW_eq (by omega) (by omega)
    intro ivl hivl hhit
    rcases List.mem_append.1 hivl with hic | hir
    · exact hno_cache_non123 hn hk hk1 hk2 hk3 ivl hic hhit
    · exact hno_extra_w (hn_mem_ext hn) (by dsimp [nodeIvl]; omega) (by dsimp [nodeIvl]; omega) ivl hir hhit
  have hn_w0 : ∀ {n : Nat}, n ∈ Nd → memW post n = memW s n := by
    intro n hn
    have hsz : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
    simpa using hn_wk hn (k := 0) (by omega) (by omega) (by omega) (by omega)
  have hn_ivl : ∀ {n : Nat}, n ∈ Nd → nodeIvl post n = nodeIvl s n := by
    intro n hn; simp only [nodeIvl, hn_w0 hn]
  have hn_path : ∀ {n : Nat}, n ∈ Nd → nodePath post n = nodePath s n := by
    intro n hn
    by_cases h12 : memW s n = 1 ∨ memW s n = 2
    · have hsz56 : 56 ≤ nodeSize (memW s n) := by unfold nodeSize; rcases h12 with h | h <;> simp [h]
      have hw32 : memW post (n + 32) = memW s (n + 32) := by
        simpa using hn_wk hn (k := 4) (by omega) (by omega) (by omega) (by omega)
      have hw40 : memW post (n + 40) = memW s (n + 40) := by
        simpa using hn_wk hn (k := 5) (by omega) (by omega) (by omega) (by omega)
      simp only [nodePath, hn_w0 hn, hw32, hw40]
    · have h12' : ¬ (memW post n = 1 ∨ memW post n = 2) := by rw [hn_w0 hn]; exact h12
      unfold nodePath
      rw [if_neg (fun h => h12' h.1), if_neg (fun h => h12 h.1)]
  have hext_eq : nodeExtents post Nd = nodeExtents s Nd := by
    unfold nodeExtents
    apply List.flatMap_congr
    intro n hn
    rw [hn_ivl hn, hn_path hn]
  refine ⟨⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩, hext_eq⟩
  · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, hkey_n, _⟩ := hN.1 n hn
    rw [hn_w0 hn, hn_ivl hn]
    refine ⟨hk3, hag.allocated hal_n, hin_n,
      P3MptSet.wordsOK_transfer hAs.1 heff.arena.1 hw_n, ?_, ?_, ?_, hrlp_len n hn⟩
    · intro h2
      have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
      have hw48 : memW post (n + 48) = memW s (n + 48) := by
        simpa using hn_wk hn (k := 6) (by omega) (by omega) (by omega) (by omega)
      rw [hw48]; exact hext h2
    · intro h3 i hi
      have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
      have hw_ch : memW post (n + 8 * (4 + i)) = memW s (n + 8 * (4 + i)) :=
        hn_wk hn (k := 4 + i) (by omega) (by omega) (by omega) (by omega)
      have heq_addr : n + 32 + 8 * i = n + 8 * (4 + i) := by omega
      rw [heq_addr, hw_ch, ← heq_addr]
      exact hbr h3 i hi
    · intro h12
      have hsz56 : 56 ≤ nodeSize (memW s n) := by unfold nodeSize; rcases h12 with h | h <;> simp [h]
      have hw32 : memW post (n + 32) = memW s (n + 32) := by
        simpa using hn_wk hn (k := 4) (by omega) (by omega) (by omega) (by omega)
      have hw40 : memW post (n + 40) = memW s (n + 40) := by
        simpa using hn_wk hn (k := 5) (by omega) (by omega) (by omega) (by omega)
      rw [hw32, hw40]
      rcases hkey_n h12 with h0 | ⟨hnib, hal_p, hin_p, hdisj_p⟩
      · exact Or.inl h0
      · by_cases hlen0 : memW s (n + 40) = 0
        · exact Or.inl hlen0
        · right
          have hlt_p := (keyIn_lt_heap_ptr hAs.2 (hkey_n h12) hlen0).2
          have hp_ext : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
            unfold nodeExtents
            exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
          refine ⟨fun k hk => ?_, hag.allocated hal_p, hin_p, fun m hm => ?_⟩
          · rw [heff.memB_eq (b := memW s (n + 32) + k) (by omega)]
            · exact hnib k hk
            · intro ivl hivl hbi
              rcases List.mem_append.1 hivl with hic | hir
              · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hic
                have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
                dsimp only [InIvl] at hbi
                rcases hdisj_p m hm with h0 | h0 | hd | hd
                · omega
                · dsimp [nodeIvl] at h0; omega
                · dsimp [nodeIvl] at hd; omega
                · dsimp [nodeIvl] at hd; omega
              · exact hno_extra_b hp_ext (by omega) (by omega) ivl hir hbi
          · rw [hn_ivl hm]; exact hdisj_p m hm
  · rw [hn_ivl hn, hn_ivl hm]
    exact hN.2 n hn m hm hne

theorem relaxedNodeHeap_preserved_of_encFrame_hashCache {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {Rl_extra : List Ivl}
    (hAs : ArenaReady s)
    (heff : EncFrame s post (nodeHashCacheIvls Nd ++ Rl_extra))
    (hN : RelaxedNodeHeap s Nd)
    (hdisj_extra : ∀ r ∈ Rl_extra, ∀ o ∈ nodeExtents s Nd, Disj r o) :
    RelaxedNodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have heff_wide : EncFrame s post (nodeCacheIvls Nd ++ Rl_extra) := by
    apply heff.mono
    intro i hi
    rcases List.mem_append.1 hi with hic | hir
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hic
      exact Or.inl ⟨(n + 8, 24), List.mem_append_left _ (List.mem_map.2 ⟨n, hn, rfl⟩), by omega, by omega⟩
    · exact Or.inl ⟨i, List.mem_append_right _ hir, le_rfl, le_rfl⟩
  apply relaxedNodeHeap_preserved_of_encFrame_cache hAs heff_wide hN hdisj_extra
  intro n hn
  have hn8 : n % 8 = 0 := (hN.1 n hn).2.2.2.1.1
  have hlt := (relaxedNodeIvl_lt_heap_ptr hAs.2 hN hn).2
  have hsz : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
  dsimp [nodeIvl] at hlt
  have hw16 : memW post (n + 16) = memW s (n + 16) := by
    apply heff.memW_eq (by omega) (by omega)
    intro ivl hivl ⟨hpos, hc1, hc2⟩
    rcases List.mem_append.1 hivl with hic | hir
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hic
      dsimp only at hc1 hc2
      by_cases hnm : n = m
      · subst hnm; omega
      · have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
        rcases hN.2 n hn m hm hnm with h0 | h0 | hd | hd
        · dsimp [nodeIvl] at h0; omega
        · dsimp [nodeIvl] at h0; omega
        · dsimp [nodeIvl] at hd; omega
        · dsimp [nodeIvl] at hd; omega
    · have hn_ext : nodeIvl s n ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
      rcases hdisj_extra ivl hir (nodeIvl s n) hn_ext with h0 | h0 | hd | hd
      · omega
      · dsimp [nodeIvl] at h0; omega
      · dsimp [nodeIvl] at hd; omega
      · dsimp [nodeIvl] at hd; omega
  rw [hw16]
  exact (hN.1 n hn).2.2.2.2.2.2.2

theorem nodeHeap_preserved_of_encFrame_cache {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {Rl_extra : List Ivl}
    (hAs : ArenaReady s)
    (heff : EncFrame s post (nodeCacheIvls Nd ++ Rl_extra))
    (hN : NodeHeap s Nd)
    (hdisj_extra : ∀ r ∈ Rl_extra, ∀ o ∈ nodeExtents s Nd, Disj r o)
    (hrlp_len : ∀ n ∈ Nd, memW post (n + 16) < 2 ^ 40) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have hag := heff.allocatorGrows
  have hno_extra_w : ∀ {o : Ivl}, o ∈ nodeExtents s Nd → ∀ {a : Nat},
      o.1 ≤ a → a + 8 ≤ o.1 + o.2 → ∀ r ∈ Rl_extra, ¬ R10Shards.P26_P28.CellHitsPos a r := by
    intro o ho a ha1 ha2 r hr ⟨hrpos, hc1, hc2⟩
    rcases hdisj_extra r hr o ho with h0 | h0 | hd | hd
    · omega
    · omega
    · omega
    · omega
  have hno_extra_b : ∀ {o : Ivl}, o ∈ nodeExtents s Nd → ∀ {b : Nat},
      o.1 ≤ b → b < o.1 + o.2 → ∀ r ∈ Rl_extra, ¬ InIvl b r := by
    intro o ho b hb1 hb2 r hr ⟨hc1, hc2⟩
    rcases hdisj_extra r hr o ho with h0 | h0 | hd | hd
    · omega
    · omega
    · omega
    · omega
  have hno_cache_non123 : ∀ {n : Nat}, n ∈ Nd → ∀ {k : Nat},
      k < nodeSize (memW s n) / 8 → k ≠ 1 → k ≠ 2 → k ≠ 3 →
      ∀ i ∈ nodeCacheIvls Nd, ¬ R10Shards.P26_P28.CellHitsPos (n + 8 * k) i := by
    intro n hn k hk hk1 hk2 hk3 i hi ⟨_, hc1, hc2⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hi
    dsimp only at hc1 hc2
    by_cases hnm : n = m
    · subst hnm; omega
    · have hsz_n : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
      have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
      have hsz8 : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> omega
      rcases hN.2 n hn m hm hnm with h0 | h0 | hd | hd
      · dsimp [nodeIvl] at h0; omega
      · dsimp [nodeIvl] at h0; omega
      · dsimp [nodeIvl] at hd; omega
      · dsimp [nodeIvl] at hd; omega
  have hn_mem_ext : ∀ {n : Nat}, n ∈ Nd → nodeIvl s n ∈ nodeExtents s Nd := by
    intro n hn; unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
  have hn_wk : ∀ {n : Nat} (hn : n ∈ Nd) {k : Nat} (hk : k < nodeSize (memW s n) / 8),
      k ≠ 1 → k ≠ 2 → k ≠ 3 → memW post (n + 8 * k) = memW s (n + 8 * k) := by
    intro n hn k hk hk1 hk2 hk3
    have hn8 : n % 8 = 0 := (hN.1 n hn).2.2.2.1.1
    have hlt := (nodeIvl_lt_heap_ptr hAs.2 hN hn).2
    have hsz8 : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> omega
    dsimp [nodeIvl] at hlt
    apply heff.memW_eq (by omega) (by omega)
    intro i hi hc
    rcases List.mem_append.1 hi with hic | hir
    · exact hno_cache_non123 hn hk hk1 hk2 hk3 i hic hc
    · exact hno_extra_w (hn_mem_ext hn) (by dsimp [nodeIvl]; omega) (by dsimp [nodeIvl]; omega) i hir hc
  have hn_w0 : ∀ {n : Nat}, n ∈ Nd → memW post n = memW s n := by
    intro n hn
    have hsz : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
    simpa using hn_wk hn (k := 0) (by omega) (by omega) (by omega) (by omega)
  have hn_ivl : ∀ {n : Nat}, n ∈ Nd → nodeIvl post n = nodeIvl s n := by
    intro n hn; simp [nodeIvl, hn_w0 hn]
  have hn_path : ∀ {n : Nat}, n ∈ Nd → nodePath post n = nodePath s n := by
    intro n hn
    by_cases h12 : memW s n = 1 ∨ memW s n = 2
    · have hsz : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize
        rcases h12 with h1 | h2
        · simp [h1]
        · simp [h2]
      have hw32 : memW post (n + 32) = memW s (n + 32) := by
        simpa using hn_wk hn (k := 4) (by omega) (by omega) (by omega) (by omega)
      have hw40 : memW post (n + 40) = memW s (n + 40) := by
        simpa using hn_wk hn (k := 5) (by omega) (by omega) (by omega) (by omega)
      simp only [nodePath, hn_w0 hn, hw32, hw40]
    · have h12' : ¬ (memW post n = 1 ∨ memW post n = 2) := by rw [hn_w0 hn]; exact h12
      unfold nodePath
      rw [if_neg (fun h => h12' h.1), if_neg (fun h => h12 h.1)]
  have hext_eq : nodeExtents post Nd = nodeExtents s Nd := by
    unfold nodeExtents
    apply List.flatMap_congr
    intro n hn
    rw [hn_ivl hn, hn_path hn]
  refine ⟨⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩, hext_eq⟩
  · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, hkey_n, _, hv1, hv3⟩ := hN.1 n hn
    rw [hn_w0 hn, hn_ivl hn]
    refine ⟨hk3, hag.allocated hal_n, hin_n,
      P3MptSet.wordsOK_transfer hAs.1 heff.arena.1 hw_n, ?_, ?_, ?_, hrlp_len n hn, ?_, ?_⟩
    · intro h2
      have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
      have hw48 : memW post (n + 48) = memW s (n + 48) := by
        simpa using hn_wk hn (k := 6) (by omega) (by omega) (by omega) (by omega)
      rw [hw48]; exact hext h2
    · intro h3 i hi
      have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
      have hw_ch : memW post (n + 8 * (4 + i)) = memW s (n + 8 * (4 + i)) :=
        hn_wk hn (k := 4 + i) (by omega) (by omega) (by omega) (by omega)
      have hadd : n + 8 * (4 + i) = n + 32 + 8 * i := by omega
      rw [← hadd, hw_ch, hadd]
      exact hbr h3 i hi
    · intro h12
      have hsz : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize
        rcases h12 with h1 | h2
        · simp [h1]
        · simp [h2]
      have hw32 : memW post (n + 32) = memW s (n + 32) := by
        simpa using hn_wk hn (k := 4) (by omega) (by omega) (by omega) (by omega)
      have hw40 : memW post (n + 40) = memW s (n + 40) := by
        simpa using hn_wk hn (k := 5) (by omega) (by omega) (by omega) (by omega)
      rw [hw32, hw40]
      by_cases hlen0 : memW s (n + 40) = 0
      · exact Or.inl hlen0
      · rcases hkey_n h12 with h0 | ⟨hnib, hal_p, hin_p, hdisj_p⟩
        · exact Or.inl h0
        · right
          have hp_lt := (keyIn_lt_heap_ptr hAs.2 (Or.inr ⟨hnib, hal_p, hin_p, hdisj_p⟩) hlen0).2
          have hp_ext : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
            unfold nodeExtents
            exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
          refine ⟨fun k hk => ?_, hag.allocated hal_p, hin_p, fun m hm => ?_⟩
          · rw [heff.memB_eq (b := memW s (n + 32) + k) (by omega)]
            · exact hnib k hk
            · intro ivl hivl hbi
              rcases List.mem_append.1 hivl with hic | hir
              · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hic
                have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
                dsimp only [InIvl] at hbi
                rcases hdisj_p m hm with h0 | h0 | hd | hd
                · omega
                · dsimp [nodeIvl] at h0; omega
                · dsimp [nodeIvl] at hd; omega
                · dsimp [nodeIvl] at hd; omega
              · exact hno_extra_b hp_ext (by omega) (by omega) ivl hir hbi
          · rw [hn_ivl hm]; exact hdisj_p m hm
    · intro h1
      have hsz : nodeSize (memW s n) = 64 := by unfold nodeSize; simp [h1]
      have hw56 : memW post (n + 56) = memW s (n + 56) := by
        simpa using hn_wk hn (k := 7) (by omega) (by omega) (by omega) (by omega)
      rw [hw56]; exact hv1 h1
    · intro h3
      have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
      have hw168 : memW post (n + 168) = memW s (n + 168) := by
        simpa using hn_wk hn (k := 21) (by omega) (by omega) (by omega) (by omega)
      rw [hw168]; exact hv3 h3
  · rw [hn_ivl hn, hn_ivl hm]
    exact hN.2 n hn m hm hne

theorem nodeHeap_preserved_of_encFrame_hashCache {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {Rl_extra : List Ivl}
    (hAs : ArenaReady s)
    (heff : EncFrame s post (nodeHashCacheIvls Nd ++ Rl_extra))
    (hN : NodeHeap s Nd)
    (hdisj_extra : ∀ r ∈ Rl_extra, ∀ o ∈ nodeExtents s Nd, Disj r o) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have heff_wide : EncFrame s post (nodeCacheIvls Nd ++ Rl_extra) := by
    apply heff.mono
    intro i hi
    rcases List.mem_append.1 hi with hic | hir
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hic
      exact Or.inl ⟨(n + 8, 24), List.mem_append_left _ (List.mem_map.2 ⟨n, hn, rfl⟩), by omega, by omega⟩
    · exact Or.inl ⟨i, List.mem_append_right _ hir, le_rfl, le_rfl⟩
  apply nodeHeap_preserved_of_encFrame_cache hAs heff_wide hN hdisj_extra
  intro n hn
  have hn8 : n % 8 = 0 := (hN.1 n hn).2.2.2.1.1
  have hlt := (nodeIvl_lt_heap_ptr hAs.2 hN hn).2
  have hsz : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
  dsimp [nodeIvl] at hlt
  have hw16 : memW post (n + 16) = memW s (n + 16) := by
    apply heff.memW_eq (by omega) (by omega)
    intro ivl hivl ⟨hpos, hc1, hc2⟩
    rcases List.mem_append.1 hivl with hic | hir
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hic
      dsimp only at hc1 hc2
      by_cases hnm : n = m
      · subst hnm; omega
      · have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
        rcases hN.2 n hn m hm hnm with h0 | h0 | hd | hd
        · dsimp [nodeIvl] at h0; omega
        · dsimp [nodeIvl] at h0; omega
        · dsimp [nodeIvl] at hd; omega
        · dsimp [nodeIvl] at hd; omega
    · have hn_ext : nodeIvl s n ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
      rcases hdisj_extra ivl hir (nodeIvl s n) hn_ext with h0 | h0 | hd | hd
      · omega
      · dsimp [nodeIvl] at h0; omega
      · dsimp [nodeIvl] at hd; omega
      · dsimp [nodeIvl] at hd; omega
  rw [hw16]
  exact (hN.1 n hn).2.2.2.2.2.2.2.1

end RelaxedNodeRlpStack

-- `BuildMptIndexedReady` / `buildMptIndexedReady_worldOK` now live in `ContractParts/C11.lean`
-- (wave8 cutover rehearsal).

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

theorem buildMptInv_preserved_mptObjStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    (h : BuildMptInv s)
    (hstep : MptObjStep R gw keep s post)
    (hl : post.locals.lookup (ofString "m") = s.locals.lookup (ofString "m"))
    (havoid : ∀ S Nd Nm, WorldTypedWith s S Nd →
      MptObjInWith s S Nm (locN s "m") →
      IvlsDisj ((locN s "m", 16) :: nodeExtents s Nm) (nodeExtents s Nd) →
      IvlsDisj (R s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m")) ∧
      IvlsDisj (R s) (nodeExtents s Nd)) :
    BuildMptInv post := by
  obtain ⟨hA, hin, S, Nd, Nm, hWT, hm, hd⟩ := h
  obtain ⟨hR, hRN⟩ := havoid S Nd Nm hWT hm hd
  have hcross : IvlsDisj ((locN s "m", 16) :: R s ++ nodeExtents s Nm)
      (nodeExtents s Nd) := by
    intro i hi j hj
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hd _ (by simp) j hj
    · rcases List.mem_append.mp hi with hi | hi
      · exact hRN i hi j hj
      · exact hd i (List.mem_cons_of_mem _ hi) j hj
  obtain ⟨S', Nd', Nm', _, hWT', hm', hd', _, _⟩ :=
    hstep.2.2.2.2 S Nd Nm hWT hm hcross hR
  have hml : locN post "m" = locN s "m" := by
    simp only [locN, hl]
  refine ⟨hstep.1, ?_, S', Nd', Nm', hWT', ?_, ?_⟩
  · rw [hml]
    exact ⟨hin.1, hin.2.trans hstep.2.1⟩
  · rw [hml]
    exact hm'
  · rw [hml]
    exact hd'

theorem buildMptInv_preserved_mptObjStep_buffers {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    (h : BuildMptInv s)
    (hstep : MptObjStep R gw keep s post)
    (hl : post.locals.lookup (ofString "m") = s.locals.lookup (ofString "m"))
    (hbuffers : ∀ i ∈ R s, ∃ gn ∈ globalBuffers,
      gn.1 ∉ typedRecords.map Prod.fst ∧ i = bufferRegion s gn) :
    BuildMptInv post := by
  apply buildMptInv_preserved_mptObjStep h hstep hl
  intro S Nd Nm hWT hm _hd
  have hworld : IvlsDisj (R s) (worldTypedIvls s S Nd) := by
    intro i hi j hj
    obtain ⟨gn, hg, hu, rfl⟩ := hbuffers i hi
    exact bufferRegion_disj hWT gn hg hu j hj
  have hobj : IvlsDisj (R s) (mptObjIvls s Nm (locN s "m")) := by
    intro i hi j hj
    obtain ⟨gn, hg, _, rfl⟩ := hbuffers i hi
    have hf : bufferRegion s gn ∈ fixedObjects s := by
      unfold fixedObjects
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
        (Or.inl (List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨gn, hg, rfl⟩))))))
    apply Disj.flip
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hm.2.2.2.1 _ hf
    · exact (hm.2.2.2.2.2.2 j hj).2.2 _ hf
  constructor
  · intro i hi j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hworld i hi j hj
    · exact hobj i hi j hj
  · intro i hi j hj
    apply hworld i hi j
    simp only [worldTypedIvls, List.mem_append]
    exact Or.inr hj

theorem buildMptInv_preserved_mptSetStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (h : BuildMptInv s)
    (hstep : MptObjStep (fun t =>
      [bufferRegion t ("keccak_pad", 136), bufferRegion t ("keccak_st", 200),
        bufferRegion t ("mpt_hash_scratch", 40)])
      ["heap_ptr", "scratch_ptr"] R10Shards.P26_P28.stdKeep s post)
    (hl : post.locals.lookup (ofString "m") = s.locals.lookup (ofString "m")) :
    BuildMptInv post := by
  apply buildMptInv_preserved_mptObjStep_buffers h hstep hl
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨("keccak_pad", 136), by decide, by decide, rfl⟩
  · exact ⟨("keccak_st", 200), by decide, by decide, rfl⟩
  · exact ⟨("mpt_hash_scratch", 40), by decide, by decide, rfl⟩

theorem buildMptInv_mptSetReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BuildMptInv s) (hk : locN s "klen" ≤ 32)
    (hv : locN s "vlen" < 2 ^ 40) : MptSetReady s :=
  ⟨buildMptInv_mptObjReady h, hk, hv⟩

theorem buildMptInv_empty {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat}
    (hA : ArenaReady s)
    (hWT : WorldTypedWith s S Nd)
    (hin : Inside (locN s "m", 16) sourceBase (globN s "heap_ptr"))
    (hw : WordsOK s (locN s "m", 16))
    (hroot : memW s (locN s "m") = 0)
    (hd : IvlsDisj [(locN s "m", 16)] (worldOwned s S Nd)) :
    BuildMptInv s := by
  refine ⟨hA, hin, S, Nd, [], hWT, ?_, ?_⟩
  · refine ⟨Or.inl hin, hw, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht i hi
      apply hd _ (by simp) i
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨t, ht, hi⟩))
    · intro j hj
      apply hd _ (by simp) j
      exact List.mem_append_left _ (List.mem_append_right _ hj)
    · simp [NodeHeap]
    · exact Or.inl hroot
    · simp [nodeExtents]
  · intro i hi j hj
    simp only [nodeExtents, List.flatMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    subst i
    apply hd _ (by simp) j
    exact List.mem_append_right _ hj

theorem buildMptInv_of_new_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {w : BitVec 64}
    (hW : WorldOK s)
    (hstep : WorldStep (fun _ => []) ["heap_ptr"] R10Shards.P26_P28.stdKeep
      (RetAvoids (fun _ _ p => [(p, 16)])) s
      (some (.returned (.val (.word w)))) post)
    (hf : FreshBlock s post w.toNat 16)
    (hroot : memW post w.toNat = 0) :
    BuildMptInv (setVarHOLFinite (ofString "m") (.val (.word w)) post) := by
  have hsource := hW.1.2.1
  obtain ⟨_, S, hS⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hS
  obtain ⟨S', Nd', _, hWT', _, _, hret⟩ :=
    hstep.2.2.2.2 S Nd hWT (fun i hi => by simp at hi)
  obtain ⟨w', heq, hd⟩ := hret (.val (.word w)) rfl
  have hw' : w' = w := by cases heq; rfl
  subst w'
  let t := setVarHOLFinite (ofString "m") (.val (.word w)) post
  have htm : locN t "m" = w.toNat := by
    simp [t, setVarHOLFinite, locN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hloc : t = {post with locals := t.locals, clock := t.clock} := rfl
  apply buildMptInv_empty (S := S') (Nd := Nd')
  · exact localsFree_arenaReady post t.locals t.clock hstep.1
  · exact (worldTypedWith_build_locals post t.locals t.clock S' Nd').2 hWT'
  · rw [htm]
    exact ⟨hsource.trans hf.2.1.1, hf.2.1.2⟩
  · rw [htm]
    exact hf.2.2
  · rw [htm]
    exact hroot
  · rw [htm]
    exact hd

def BuildMptLoopInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BuildMptIndexedReady s ∧ BuildMptInv s ∧
    Inside (locN s "slice_arr", 16 * locN s "n") sourceBase (locN s "mark") ∧
    locN s "mark" ≤ globN s "heap_ptr" ∧
    (∀ name ∈ (["mark", "m", "i"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w)))

theorem localsOnly_buildMptLoopInv :
    LocalsOnly ["slice_arr", "n", "out", "mark", "m", "i"] BuildMptLoopInv := by
  intro F s locals k hl h
  have harr := locN_congr s locals k "slice_arr" (hl "slice_arr" (by simp))
  have hn := locN_congr s locals k "n" (hl "n" (by simp))
  have hm := locN_congr s locals k "mark" (hl "mark" (by simp))
  have hready : BuildMptIndexedReady {s with locals := locals, clock := k} := by
    apply localsOnly_buildMptIndexedReady s locals k _ h.1
    intro name hname
    apply hl name
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname ⊢
    rcases hname with rfl | rfl | rfl <;> simp
  refine ⟨hready,
    localsOnly_buildMptInv s locals k (fun n hn => hl n (by simp_all)) h.2.1,
    ?_, ?_, ?_⟩
  · rw [harr, hn, hm]
    exact h.2.2.1
  · rw [hm]
    exact h.2.2.2.1
  · intro name hname
    obtain ⟨w, hw⟩ := h.2.2.2.2 name hname
    exact ⟨w, (hl name (by simp_all)).trans hw⟩

theorem buildMptLoopInv_set_counter {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BuildMptLoopInv s) (w : BitVec 64) :
    BuildMptLoopInv (setVarHOLFinite (ofString "i") (.val (.word w)) s) := by
  refine ⟨localsOnly_buildMptIndexedReady.setVar (by decide) _ s h.1,
    localsOnly_buildMptInv.setVar (by decide) _ s h.2.1,
    ?_, ?_, ?_⟩
  · rw [locN_setVar_ne s "slice_arr" (ofString "i") (.val (.word w)) (by decide),
      locN_setVar_ne s "n" (ofString "i") (.val (.word w)) (by decide),
      locN_setVar_ne s "mark" (ofString "i") (.val (.word w)) (by decide)]
    exact h.2.2.1
  · rw [locN_setVar_ne s "mark" (ofString "i") (.val (.word w)) (by decide)]
    exact h.2.2.2.1
  · intro name hname
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl | rfl
    · obtain ⟨v, hv⟩ := h.2.2.2.2 "mark" (by simp)
      exact ⟨v, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv,
        show ofString "i" ≠ ofString "mark" by decide]⟩
    · obtain ⟨v, hv⟩ := h.2.2.2.2 "m" (by simp)
      exact ⟨v, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv,
        show ofString "i" ≠ ofString "m" by decide]⟩
    · exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩

theorem callee_param_five_exp {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 p4 p5 : MlS) (s1 s2 s3 s4 s5 : ShapeHOL)
    (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname =
      some ([(p1, s1), (p2, s2), (p3, s3), (p4, s4), (p5, s5)], body, ret))
    (e1 e2 e3 e4 e5 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3, e4, e5] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2 v3 v4 v5,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧
      evalAt state e3 = some v3 ∧ evalAt state e4 = some v4 ∧ evalAt state e5 = some v5 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧
      callee.lookup p3 = some v3 ∧ callee.lookup p4 = some v4 ∧ callee.lookup p5 = some v5 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : evalAt state e1 with _ | v1 <;>
  rcases he2 : evalAt state e2 with _ | v2 <;>
  rcases he3 : evalAt state e3 with _ | v3 <;>
  rcases he4 : evalAt state e4 with _ | v4 <;>
  rcases he5 : evalAt state e5 with _ | v5 <;>
    simp only [evalAt] at he1 he2 he3 he4 he5 <;>
    simp only [he1, he2, he3, he4, he5, Option.some.injEq] at hargs <;>
    cases hargs
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
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      refine ⟨v1, v2, v3, v4, v5, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1.1, hnd.1.2.1, hnd.1.2.2.1, hnd.1.2.2.2]
      · simp [List.zip, List.foldl, hnd.2.1.1, hnd.2.1.2.1, hnd.2.1.2.2]
      · simp [List.zip, List.foldl, hnd.2.2.1.1, hnd.2.2.1.2]
      · simp [List.zip, List.foldl, hnd.2.2.2.1]
      · simp [List.zip, List.foldl]
    · cases raw

theorem callee_param_two_exp {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 : MlS) (s1 s2 : ShapeHOL)
    (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2)], body, ret))
    (e1 e2 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : evalAt state e1 with _ | v1 <;>
  rcases he2 : evalAt state e2 with _ | v2 <;>
    simp only [evalAt] at he1 he2 <;>
    simp only [he1, he2, Option.some.injEq] at hargs <;>
    cases hargs
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
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false] at hnd
      refine ⟨v1, v2, rfl, rfl, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1]
      · simp [List.zip, List.foldl]
    · cases raw

theorem lookup_heap_mark_bmi :
    originalRuntimeCode.lookup (ofString "heap_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_heap_mark, .one) :=
  lookup_of_guestAst_getElem 8 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_mark) rfl

theorem lookup_mpt_new_bmi :
    originalRuntimeCode.lookup (ofString "mpt_new") =
      some ([(ofString "root_node", .one), (ofString "secured", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_new, .one) :=
  lookup_of_guestAst_getElem 268 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_new) rfl

theorem lookup_rlp_encode_word_bmi :
    originalRuntimeCode.lookup (ofString "rlp_encode_word") =
      some ([(ofString "dst", .one), (ofString "w", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_word, .one) :=
  lookup_of_guestAst_getElem 123 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_word) rfl

def BuildMptAfterMark : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BuildMptIndexedReady s ∧
    Inside (locN s "slice_arr", 16 * locN s "n") sourceBase (locN s "mark") ∧
    locN s "mark" = globN s "heap_ptr" ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "mark") = some (.val (.word w)))

theorem decCallResume_heap_mark_bmi
    (hro : ReadOnlyFn (ofString "heap_mark")) :
    DecCallResumeOn BuildMptIndexedReady BuildMptAfterMark (ofString "mark")
      (ofString "heap_mark") [] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  have hready : BuildMptIndexedReady
      (setVarHOLFinite (ofString "mark") value { post with locals := state.locals }) :=
    ReadOnlyFn.resumeOn localsOnly_buildMptIndexedReady
      (fun s hs => hs.1.1.1) hro (ofString "mark") (by decide) []
      state values body callee ret value post hcode hP hargs hl hrun
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "heap_mark")
    [] (sourceFnBody Guest.Software.guestFn_heap_mark) body .one ret values callee
    (by rw [hcode]; exact lookup_heap_mark_bmi) hl
  subst hsame
  have hpos : 0 < globN state "heap_ptr" := by
    have hsb := hP.1.1.2.1
    have : 0 < sourceBase := by decide
    omega
  obtain ⟨hw, hgw, hwnat⟩ : ∃ hw : BitVec 64,
      state.globals.lookup (ofString "heap_ptr") = some (.val (.word hw)) ∧
      hw.toNat = globN state "heap_ptr" := by
    unfold globN at hpos ⊢
    split at hpos
    · rename_i w hlook; exact ⟨w, hlook, rfl⟩
    · omega
  have hbhm : sourceFnBody Guest.Software.guestFn_heap_mark =
      .return (.var .global (ofString "heap_ptr")) := rfl
  rw [hbhm, evaluateHOLFiniteState_return] at hrun
  have hge : (callEntryStateHOLFinite state callee).globals.lookup (ofString "heap_ptr") =
      some (.val (.word hw)) := hgw
  simp [evalHOLExact, hge, shapeOfHOLExact] at hrun
  obtain ⟨rfl, rfl⟩ := hrun
  let resumed := setVarHOLFinite (ofString "mark") (.val (.word hw))
    { emptyLocalsHOLFinite (callEntryStateHOLFinite state callee) with locals := state.locals }
  have hmark : locN resumed "mark" = globN state "heap_ptr" := by
    simp [resumed, setVarHOLFinite, locN, HolFiniteMapExact.lookup_update, FUPDATE, hwnat]
  have hhp : globN resumed "heap_ptr" = globN state "heap_ptr" := rfl
  have harr : locN resumed "slice_arr" = locN state "slice_arr" :=
    locN_setVar_ne _ "slice_arr" (ofString "mark") (.val (.word hw)) (by decide)
  have hn : locN resumed "n" = locN state "n" :=
    locN_setVar_ne _ "n" (ofString "mark") (.val (.word hw)) (by decide)
  refine ⟨hready, ?_, ?_, ⟨hw, by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩⟩
  · rw [harr, hn, hmark]
    exact hP.2.2.2.1
  · rw [hmark, hhp]

def BuildMptAfterNew : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BuildMptIndexedReady s ∧ BuildMptInv s ∧
    Inside (locN s "slice_arr", 16 * locN s "n") sourceBase (locN s "mark") ∧
    locN s "mark" ≤ globN s "heap_ptr" ∧
    (∀ name ∈ (["mark", "m"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w)))

theorem decCallResume_mpt_new_bmi
    (hwk : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"] R10Shards.P26_P28.stdKeep
      (RetAvoids (fun _ _ w => [(w, 16)])) (ofString "mpt_new"))
    (hrt : Returns ArenaReady (fun s post m => FreshBlock s post m 16 ∧
      memW post m = locN s "root_node" ∧ memW post (m + 8) = locN s "secured")
      (ofString "mpt_new")) :
    DecCallResumeOn BuildMptAfterMark BuildMptAfterNew (ofString "m")
      (ofString "mpt_new") [.const 0, .const 0] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨hready, hin_mark, hmark_eq, hw_mark⟩ := hP
  let entry := callEntryStateHOLFinite state callee
  have hentryW : WorldOK entry :=
    localsFree_worldOK state callee (state.clock - 1) hready.1
  have hstep0 : WorldStep (fun _ => []) ["heap_ptr"] R10Shards.P26_P28.stdKeep
      (RetAvoids (fun _ _ w => [(w, 16)])) entry (some (.returned value)) post := by
    have hspec := FunSpec.at_lookup hwk state hcode values body callee ret hl hentryW
      (by rw [hrun]; simp)
    rw [hrun] at hspec
    exact hspec (Or.inl ⟨value, rfl⟩)
  have hret0 := FunSpec.at_lookup hrt state hcode values body callee ret hl hentryW.1
    (by rw [hrun]; simp)
  rw [hrun] at hret0
  obtain ⟨wm, rfl, hA_post, hAG, hf0, hroot0, _⟩ := hret0 value rfl
  obtain ⟨v1, v2, he1, he2, hc1, hc2⟩ :=
    callee_param_two_exp state (ofString "mpt_new")
      (ofString "root_node") (ofString "secured") .one .one _ _
      (by rw [hcode]; exact lookup_mpt_new_bmi) _ _ values body callee ret hargs hl
  have hv1 : v1 = .val (.word 0) := by
    simpa [evalAt, evalHOLExact] using he1.symm
  have hv2 : v2 = .val (.word 0) := by
    simpa [evalAt, evalHOLExact] using he2.symm
  subst hv1 hv2
  have hrn0 : locN entry "root_node" = 0 := by
    simp [entry, callEntryStateHOLFinite, locN, hc1]
  have hroot : memW post wm.toNat = 0 := hroot0.trans hrn0
  have hf : FreshBlock state post wm.toNat 16 := hf0
  have hstep : WorldStep (fun _ => []) ["heap_ptr"] R10Shards.P26_P28.stdKeep
      (RetAvoids (fun _ _ w => [(w, 16)])) state
      (some (.returned (.val (.word wm)))) post := by
    refine ⟨hstep0.1, hstep0.2.1, hstep0.2.2.1, hstep0.2.2.2.1, ?_⟩
    intro S Nd hWT hD
    have hWT_e : WorldTypedWith entry S Nd :=
      (worldTypedWith_build_locals state callee (state.clock - 1) S Nd).2 hWT
    exact hstep0.2.2.2.2 S Nd hWT_e (fun i hi => by simp at hi)
  let postCaller : PanSemStateFiniteExact 64 F := { post with locals := state.locals }
  have hstep_c : WorldStep (fun _ => []) ["heap_ptr"] R10Shards.P26_P28.stdKeep
      (RetAvoids (fun _ _ w => [(w, 16)])) state
      (some (.returned (.val (.word wm)))) postCaller := by
    refine ⟨localsFree_arenaReady post state.locals post.clock hstep.1,
      hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, ?_⟩
    intro S Nd hWT hD
    obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hRA⟩ := hstep.2.2.2.2 S Nd hWT hD
    refine ⟨S', Nd', hsub,
      (worldTypedWith_build_locals post state.locals post.clock S' Nd').2 hWT',
      hOG, hFO, hRA⟩
  have hf_c : FreshBlock state postCaller wm.toNat 16 :=
    ⟨hf.1, hf.2.1, hf.2.2⟩
  have hinv : BuildMptInv (setVarHOLFinite (ofString "m") (.val (.word wm)) postCaller) :=
    buildMptInv_of_new_step hready.1 hstep_c hf_c hroot
  obtain ⟨_, S0, hS0⟩ := hready.1
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with state S0).1 hS0
  obtain ⟨S0', Nd0', _, hWT0', _, _, _⟩ :=
    hstep.2.2.2.2 S0 Nd0 hWT0 (fun i hi => by simp at hi)
  have hW_post : WorldOK post :=
    ⟨hstep.1, S0', (worldTyped_iff_with post S0').2 ⟨Nd0', hWT0'⟩⟩
  let resumed := setVarHOLFinite (ofString "m") (.val (.word wm)) postCaller
  have hW_res : WorldOK resumed :=
    localsFree_worldOK post resumed.locals resumed.clock hW_post
  have hl_res : ∀ name ∈ (["slice_arr", "n", "out"] : List String),
      resumed.locals.lookup (ofString name) = state.locals.lookup (ofString name) := by
    intro name hname
    have hne : ofString "m" ≠ ofString name := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
      rcases hname with rfl | rfl | rfl <;> decide
    simp [resumed, postCaller, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hbuf_res : ∀ gn ∈ ([("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
      ("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion resumed gn = bufferRegion state gn := by
    intro gn hgn
    have hgk : state.globals.lookup (ofString gn.1) = post.globals.lookup (ofString gn.1) := by
      apply hstep.2.2.1 (ofString gn.1)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgn
      rcases hgn with rfl | rfl | rfl | rfl <;> decide
    have hglob : globN resumed gn.1 = globN state gn.1 := by
      simp [resumed, postCaller, setVarHOLFinite, globN, ← hgk]
    simp [bufferRegion, hglob]
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "mpt_new")
    [(ofString "root_node", .one), (ofString "secured", .one)]
    (sourceFnBody Guest.Software.guestFn_mpt_new) body .one ret values callee
    (by rw [hcode]; exact lookup_mpt_new_bmi) hl
  subst hsame
  obtain ⟨hp, q, _, hhp_eq, hhp_al, hq_eq, hq_hi, _, _, hpost_m, _, _, _, _, _, _⟩ :=
    R13Shards.mpt_new_resumes_props entry 0 0 hcode hentryW.1 hc1 hc2
      (by rw [hrun]; exact Or.inl ⟨.val (.word wm), rfl⟩)
  dsimp only [entry] at hpost_m hhp_eq
  rw [hrun] at hpost_m
  dsimp only at hpost_m
  have hhp_st : hp.toNat = globN state "heap_ptr" := by
    simpa [callEntryStateHOLFinite, globN] using hhp_eq
  have hne0_hp : hp + 0 = hp := BitVec.add_zero hp
  have hfr_fresh : FrameOutside state resumed ([] ++ [] ++ [freeGap state]) (heapFree state) := by
    intro a _ hnhf
    have hp8_nat : (hp + 8#64).toNat = hp.toNat + 8 :=
      BitVec.toNat_add_of_lt
        (by rw [Wave8Contracts.M12.heapLimit_val] at hq_hi; change hp.toNat + 8 < 2 ^ 64; omega)
    have hne0 : a ≠ hp := by
      rintro rfl
      apply hnhf
      simp only [CellHits, heapFree]
      omega
    have hne8 : a ≠ hp + 8#64 := by
      rintro rfl
      apply hnhf
      simp only [CellHits, heapFree, hp8_nat]
      omega
    change post.memory a = state.memory a
    rw [hpost_m, hne0_hp]
    simp [Wave8Contracts.M26.updW, callEntryStateHOLFinite, hne8, hne0]
  have hready_res : BuildMptIndexedReady resumed :=
    buildMptIndexedReady_preserved_below_mark (buffers := []) (owned := [])
      hready hW_res hl_res hstep.2.1 hbuf_res hin_mark (le_of_eq hmark_eq)
      hfr_fresh (fun _ hj => by simp at hj) (fun _ hj => by simp at hj)
  have harr_res : locN resumed "slice_arr" = locN state "slice_arr" :=
    locN_setVar_ne postCaller "slice_arr" (ofString "m") (.val (.word wm)) (by decide)
  have hn_res : locN resumed "n" = locN state "n" :=
    locN_setVar_ne postCaller "n" (ofString "m") (.val (.word wm)) (by decide)
  have hmark_res : locN resumed "mark" = locN state "mark" :=
    locN_setVar_ne postCaller "mark" (ofString "m") (.val (.word wm)) (by decide)
  refine ⟨hready_res, hinv, ?_, ?_, ?_⟩
  · rw [harr_res, hn_res, hmark_res]
    exact hin_mark
  · rw [hmark_res, hmark_eq]
    exact hstep.2.1
  · intro name hname
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl
    · obtain ⟨w0, hw0⟩ := hw_mark
      exact ⟨w0, by simp [resumed, postCaller, setVarHOLFinite, HolFiniteMapExact.lookup_update,
        FUPDATE, hw0, show ofString "m" ≠ ofString "mark" by decide]⟩
    · exact ⟨wm, by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩

theorem buildMptAfterNew_set_counter {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BuildMptAfterNew s) (w : BitVec 64) :
    BuildMptLoopInv (setVarHOLFinite (ofString "i") (.val (.word w)) s) := by
  refine ⟨localsOnly_buildMptIndexedReady.setVar (by decide) _ s h.1,
    localsOnly_buildMptInv.setVar (by decide) _ s h.2.1,
    ?_, ?_, ?_⟩
  · rw [locN_setVar_ne s "slice_arr" (ofString "i") (.val (.word w)) (by decide),
      locN_setVar_ne s "n" (ofString "i") (.val (.word w)) (by decide),
      locN_setVar_ne s "mark" (ofString "i") (.val (.word w)) (by decide)]
    exact h.2.2.1
  · rw [locN_setVar_ne s "mark" (ofString "i") (.val (.word w)) (by decide)]
    exact h.2.2.2.1
  · intro name hname
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl | rfl
    · obtain ⟨v, hv⟩ := h.2.2.2.2 "mark" (by simp)
      exact ⟨v, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv,
        show ofString "i" ≠ ofString "mark" by decide]⟩
    · obtain ⟨v, hv⟩ := h.2.2.2.2 "m" (by simp)
      exact ⟨v, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv,
        show ofString "i" ≠ ofString "m" by decide]⟩
    · exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩

theorem buildMptLoopInv_active_lt {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hact : LoopActive (.cmp .lower (.var .local (ofString "i"))
      (.var .local (ofString "n"))) s) :
    locN s "i" < locN s "n" := by
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨a, b, ha, hb, hword⟩ := evalAt_cmp s .lower _ _ word hw
  have hia : s.locals.lookup (ofString "i") = some (.val (.word a)) := by
    simpa only [evalAt, evalHOLExact] using ha
  have hnb : s.locals.lookup (ofString "n") = some (.val (.word b)) := by
    simpa only [evalAt, evalHOLExact] using hb
  have hcmp : wordCmpHOL .lower a b = true := by
    by_contra hc
    simp [hc] at hword
    exact hnz hword
  have hlt : a.toNat < b.toNat := by
    simpa [wordCmpHOL, decide_eq_true_eq, BitVec.lt_def] using hcmp
  simpa only [locN, hia, hnb] using hlt

def buildMptLoopRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  locN s "n" - locN s "i"

theorem buildMptLoopRank_le {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BuildMptLoopInv s) : buildMptLoopRank s ≤ 2 ^ 64 := by
  have hn := h.1.2.2.1
  dsimp only [buildMptLoopRank]
  omega

theorem buildMptLoopRank_decreases {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (i : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hlt : locN s "i" < locN s "n")
    (hn : locN s "n" < 2 ^ 32)
    (hpost_i : post.locals.lookup (ofString "i") = some (.val (.word (i + 1))))
    (hpost_n : post.locals.lookup (ofString "n") = s.locals.lookup (ofString "n")) :
    buildMptLoopRank post < buildMptLoopRank s := by
  have hi_nat : locN s "i" = i.toNat := by simp only [locN, hi]
  have hadd : (i + 1#64).toNat = i.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt]
    · simp
    · simp; omega
  have hni : locN post "i" = i.toNat + 1 := by
    change (match post.locals.lookup (ofString "i") with
      | some (.val (.word w)) => w.toNat | _ => 0) = _
    rw [hpost_i]
    exact hadd
  have hnn : locN post "n" = locN s "n" := by
    simp only [locN, hpost_n]
  dsimp only [buildMptLoopRank]
  rw [hni, hnn]
  omega

def BuildMptAfterKey : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BuildMptLoopInv s ∧ locN s "i" < locN s "n" ∧
    locN s "klen" ≤ 32 ∧
    ∃ w : BitVec 64, s.locals.lookup (ofString "klen") = some (.val (.word w))

theorem decCallResume_rlp_encode_word_bmi
    (hwk : WorldKeeps WorldOK (fun s => [(locN s "dst", 9)])
      [] R10Shards.P26_P28.stdKeep NoExtra (ofString "rlp_encode_word")) :
    DecCallResumeOn
      (fun s => BuildMptLoopInv s ∧
        LoopActive (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) s)
      BuildMptAfterKey (ofString "klen") (ofString "rlp_encode_word")
      [.var .global (ofString "mpt_key_scratch"), .var .local (ofString "i")] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨hloop, hact⟩ := hP
  have hlt : locN state "i" < locN state "n" := buildMptLoopInv_active_lt hact
  obtain ⟨hready, hinv, hin_mark, hmark_le, hlocs⟩ := hloop
  let entry := callEntryStateHOLFinite state callee
  have hentryW : WorldOK entry :=
    localsFree_worldOK state callee (state.clock - 1) hready.1
  have hstep0 : WorldStep (fun s => [(locN s "dst", 9)]) [] R10Shards.P26_P28.stdKeep
      NoExtra entry (some (.returned value)) post := by
    have hspec := FunSpec.at_lookup hwk state hcode values body callee ret hl hentryW
      (by rw [hrun]; simp)
    rw [hrun] at hspec
    exact hspec (Or.inl ⟨value, rfl⟩)
  obtain ⟨v1, v2, he1, he2, hc1, hc2⟩ :=
    callee_param_two_exp state (ofString "rlp_encode_word")
      (ofString "dst") (ofString "w") .one .one _ _
      (by rw [hcode]; exact lookup_rlp_encode_word_bmi) _ _ values body callee ret hargs hl
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "rlp_encode_word")
    [(ofString "dst", .one), (ofString "w", .one)]
    (sourceFnBody Guest.Software.guestFn_rlp_encode_word) body .one ret values callee
    (by rw [hcode]; exact lookup_rlp_encode_word_bmi) hl
  subst hsame
  obtain ⟨wi, hwi⟩ := hlocs "i" (by simp)
  have hv2 : v2 = .val (.word wi) := by
    simpa [evalAt, evalHOLExact, hwi] using he2.symm
  subst hv2
  have hsb_ok : ∀ (t : PanSemStateFiniteExact 64 F) (val : ExpHOL 64),
      t.memaddrs = ordinaryDomain →
      t.locals.lookup (ofString "dst") = some v1 →
      (evaluateHOLFiniteState t (.storeByte (.var .local (ofString "dst")) val)).1 = none →
      ∃ dst0 : BitVec 64, v1 = .val (.word dst0) ∧ dst0 ≠ 0 := by
    intro t val hma htd hnone
    rw [evaluateHOLFiniteState_storeByte] at hnone
    rcases v1 with ⟨⟨d0⟩⟩ | _ | _
    · simp only [evalHOLExact, htd] at hnone
      split at hnone
      · split at hnone
        · rename_i m' hst
          unfold panMemStoreByteWord8HOL at hst
          dsimp only at hst
          cases hm : t.memory (panByteAlignHOL d0) with
          | word cell =>
            by_cases hdom : t.memaddrs (panByteAlignHOL d0)
            · have hlo := (M11.byteAlign_lt_heapEnd hma d0 hdom).1
              refine ⟨d0, rfl, ?_⟩
              rintro rfl
              have h0_al : (panByteAlignHOL (0 : BitVec 64)).toNat = 0 := by decide
              rw [h0_al] at hlo
              norm_num [sourceBase] at hlo
            · simp [hm, hdom] at hst
        · simp at hnone
      · simp at hnone
    · simp [evalHOLExact, htd] at hnone
    · simp [evalHOLExact, htd] at hnone
  have hsb_none_or_err : ∀ (t : PanSemStateFiniteExact 64 F) (val : ExpHOL 64),
      (evaluateHOLFiniteState t (.storeByte (.var .local (ofString "dst")) val)).1 = none ∨
      (evaluateHOLFiniteState t (.storeByte (.var .local (ofString "dst")) val)).1 = some .error := by
    intro t val
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact Or.inr rfl
    · exact Or.inr rfl
  have hdst_ex : ∃ dst0 : BitVec 64, v1 = .val (.word dst0) ∧ dst0 ≠ 0 := by
    have hb_rlp : sourceFnBody Guest.Software.guestFn_rlp_encode_word =
        .seq
          (.ite (.cmp .equal (.var .local (ofString "w")) (.const 0))
            (.seq (.storeByte (.var .local (ofString "dst")) (.const 128)) (.return (.const 1)))
            .skip)
          (.seq
            (.ite (.cmp .lower (.var .local (ofString "w")) (.const 128))
              (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w"))) (.return (.const 1)))
              .skip)
            (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "w")]
              (.seq
                (.storeByte (.var .local (ofString "dst"))
                  (.op .add [.const 128, .var .local (ofString "ll")]))
                (.seq
                  (.call (some (none, none)) (ofString "rlp_put_be")
                    [.op .add [.var .local (ofString "dst"), .const 1],
                     .var .local (ofString "w"),
                     .var .local (ofString "ll")])
                  (.return (.op .add [.const 1, .var .local (ofString "ll")])))))) := rfl
    have hrun' : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_encode_word) =
        (some (.returned value), post) := hrun
    rw [hb_rlp, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun'
    have hwev : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a))
        (.cmp .equal (.var .local (ofString "w")) (.const 0)) =
        some (.val (.word (if wi = 0 then 1 else 0))) := by
      simp [entry, callEntryStateHOLFinite, evalHOLExact, hc2, wordCmpHOL]
    rw [hwev] at hrun'
    dsimp only at hrun'
    by_cases hwz : wi = 0
    · rw [if_pos hwz, if_neg (by decide : ¬ ((1 : BitVec 64) = 0)),
        evaluateHOLFiniteState_seq_line780] at hrun'
      rcases hsb : evaluateHOLFiniteState entry (.storeByte (.var .local (ofString "dst")) (.const 128)) with ⟨rsb, s1⟩
      simp only [hsb] at hrun'
      rcases hsb_none_or_err entry (.const 128) with hsn | hse
      · exact hsb_ok entry (.const 128) hentryW.1.1.memaddrs hc1 hsn
      · rw [hsb] at hse; dsimp only at hse; subst hse
        cases hrun'
    · rw [if_neg hwz, if_pos rfl, evaluateHOLFiniteState_skip] at hrun'
      dsimp only at hrun'
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun'
      have hwev2 : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a))
          (.cmp .lower (.var .local (ofString "w")) (.const 128)) =
          some (.val (.word (if wi < 128 then 1 else 0))) := by
        simp [entry, callEntryStateHOLFinite, evalHOLExact, hc2, wordCmpHOL]
      rw [hwev2] at hrun'
      dsimp only at hrun'
      by_cases hlt128 : wi < 128
      · rw [if_pos hlt128, if_neg (by decide : ¬ ((1 : BitVec 64) = 0)),
          evaluateHOLFiniteState_seq_line780] at hrun'
        rcases hsb : evaluateHOLFiniteState entry (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w"))) with ⟨rsb, s1⟩
        simp only [hsb] at hrun'
        rcases hsb_none_or_err entry (.var .local (ofString "w")) with hsn | hse
        · exact hsb_ok entry (.var .local (ofString "w")) hentryW.1.1.memaddrs hc1 hsn
        · rw [hsb] at hse; dsimp only at hse; subst hse
          cases hrun'
      · rw [if_neg hlt128, if_pos rfl, evaluateHOLFiniteState_skip] at hrun'
        dsimp only at hrun'
        obtain ⟨ll, mid, _, _, hmid_loc, hmid_eq, _, hr_eq, _⟩ :=
          M11.eval_decCall_rlp_be_len entry "ll" (.var .local (ofString "w")) wi
            (.seq
              (.storeByte (.var .local (ofString "dst"))
                (.op .add [.const 128, .var .local (ofString "ll")]))
              (.seq
                (.call (some (none, none)) (ofString "rlp_put_be")
                  [.op .add [.var .local (ofString "dst"), .const 1],
                   .var .local (ofString "w"),
                   .var .local (ofString "ll")])
                (.return (.op .add [.const 1, .var .local (ofString "ll")]))))
            hcode (by simp [entry, callEntryStateHOLFinite, evalHOLExact, hc2])
            (by rw [hrun']; simp)
        have hcr_ll : (evaluateHOLFiniteState mid
            (.seq
              (.storeByte (.var .local (ofString "dst"))
                (.op .add [.const 128, .var .local (ofString "ll")]))
              (.seq
                (.call (some (none, none)) (ofString "rlp_put_be")
                  [.op .add [.var .local (ofString "dst"), .const 1],
                   .var .local (ofString "w"),
                   .var .local (ofString "ll")])
                (.return (.op .add [.const 1, .var .local (ofString "ll")]))))).1 =
            some (.returned value) := by
          rw [← hr_eq, hrun']
        have hma_ll : mid.memaddrs = ordinaryDomain := by
          rw [hmid_eq]; exact hentryW.1.1.memaddrs
        have hdst_ll : mid.locals.lookup (ofString "dst") = some v1 := by
          have hne : ofString "ll" ≠ ofString "dst" := by decide
          rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, entry, callEntryStateHOLFinite, hc1]
        rw [evaluateHOLFiniteState_seq_line780] at hcr_ll
        rcases hsb : evaluateHOLFiniteState mid
          (.storeByte (.var .local (ofString "dst"))
            (.op .add [.const 128, .var .local (ofString "ll")])) with ⟨rsb, s1⟩
        simp only [hsb] at hcr_ll
        rcases hsb_none_or_err mid (.op .add [.const 128, .var .local (ofString "ll")]) with hsn | hse
        · exact hsb_ok mid _ hma_ll hdst_ll hsn
        · rw [hsb] at hse; dsimp only at hse; subst hse
          cases hcr_ll
  obtain ⟨dst0, rfl, hdst_nz⟩ := hdst_ex
  have hdst_glob : state.globals.lookup (ofString "mpt_key_scratch") = some (.val (.word dst0)) := by
    simpa [evalAt, evalHOLExact] using he1
  have hdst_nat : dst0.toNat = globN state "mpt_key_scratch" := by
    simp [globN, hdst_glob]
  have hks_nz : globN state "mpt_key_scratch" ≠ 0 := by
    intro hz
    apply hdst_nz
    apply BitVec.eq_of_toNat_eq
    simp [hdst_nat, hz]
  have hrlp' := WkBlockTxEnc.eval_rlp_encode_word_body_exact entry dst0 wi
    [bufferRegion state ("mpt_key_scratch", 16)]
    hcode hentryW.1.1.memaddrs hc1 hc2
    ⟨bufferRegion state ("mpt_key_scratch", 16), by simp,
      by simp [bufferRegion, hks_nz, hdst_nat],
      by simp [bufferRegion, hks_nz, hdst_nat]⟩
    (by rw [hrun]; simp)
  obtain ⟨klen, rfl, _, hklen9, _, heff⟩ := hrlp'.1 value (by rw [hrun])
  rw [hrun] at heff
  dsimp only at heff
  have hpost_glob : post.globals = state.globals := heff.globals
  let resumed := setVarHOLFinite (ofString "klen") (.val (.word klen))
    { post with locals := state.locals }
  have heff_res : M11.ByteRegionEffect state resumed
      ([bufferRegion state ("mpt_key_scratch", 16)] ++ ([] : List Ivl)) := by
    have heff0 : M11.ByteRegionEffect state post
        ([bufferRegion state ("mpt_key_scratch", 16)] ++ ([] : List Ivl)) := by
      simp only [List.append_nil]
      exact ⟨heff.code, heff.memaddrs, heff.shMemaddrs, heff.baseAddr, heff.be,
        heff.globals, heff.out_dom, heff.cell_frame, heff.byte_frame⟩
    have hres_eq : { post with locals := resumed.locals, clock := resumed.clock } = resumed := by
      simp [resumed, setVarHOLFinite]
    rw [← hres_eq]
    exact heff0.with_locals_clock resumed.locals resumed.clock
  have hstep_res : WorldStep (fun s => [bufferRegion s ("mpt_key_scratch", 16)])
      [] R10Shards.P26_P28.stdKeep NoExtra state (some (.returned (.val (.word klen)))) resumed :=
    M11.ByteRegionEffect.to_worldStep (R := fun s => [bufferRegion s ("mpt_key_scratch", 16)])
      (extra := fun _ => []) (r := some (.returned (.val (.word klen))))
      hready.1 (fun _ hx => by simp at hx) heff_res
  obtain ⟨_, S0, hS0⟩ := hready.1
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with state S0).1 hS0
  have hdisj_w0 : IvlsDisj [bufferRegion state ("mpt_key_scratch", 16)] (worldTypedIvls state S0 Nd0) := by
    intro iv hi j hj
    simp only [List.mem_singleton] at hi
    subst iv
    exact bufferRegion_disj hWT0 ("mpt_key_scratch", 16) (by decide) (by decide) j hj
  have hW_res : WorldOK resumed :=
    hstep_res.worldOK ⟨S0, Nd0, hWT0, hdisj_w0⟩
  have hl_ne : ∀ name : String, ofString "klen" ≠ ofString name →
      resumed.locals.lookup (ofString name) = state.locals.lookup (ofString name) := by
    intro name hne
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hbuf_res : ∀ gn ∈ ([("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
      ("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion resumed gn = bufferRegion state gn := by
    intro gn _
    have hglob : globN resumed gn.1 = globN state gn.1 := by
      simp [resumed, setVarHOLFinite, globN, hpost_glob]
    simp [bufferRegion, hglob]
  have hfix_ks : (globN state "mpt_key_scratch", 16) ∈ fixedObjects state :=
    P3MptSet.buf_in_fixedObjects state "mpt_key_scratch" 16 (by decide) hks_nz
  have hks8 : globN state "mpt_key_scratch" % 8 = 0 := by
    rcases hWT0.2.2.1.1 _ hfix_ks with hz | ⟨_, hw_ks⟩
    · omega
    · exact hw_ks.1
  have hdisj_arr_ks : Disj (locN state "slice_arr", 16 * locN state "n")
      (bufferRegion state ("mpt_key_scratch", 16)) :=
    hready.2.2.2.2.2.1 _ (by simp) _
      (List.mem_map.mpr ⟨("mpt_key_scratch", 16), by simp, rfl⟩)
  have hfr_res : FrameOutside state resumed
      ([bufferRegion state ("mpt_key_scratch", 16)] ++ [] ++ [freeGap state])
      (heapFree state) := by
    intro a ha _
    exact heff_res.cell_frame a fun iv hiv =>
      ha iv (List.mem_append_left _ (List.mem_append_left _ (by simpa using hiv)))
  have hready_res : BuildMptIndexedReady resumed :=
    buildMptIndexedReady_preserved_below_mark
      (buffers := [bufferRegion state ("mpt_key_scratch", 16)]) (owned := [])
      hready hW_res
      (fun name hname => hl_ne name (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
        rcases hname with rfl | rfl | rfl <;> decide))
      hstep_res.2.1 hbuf_res hin_mark hmark_le hfr_res
      (fun j hj => by
        simp only [List.mem_singleton] at hj
        subst j
        exact Or.inl ⟨by simp [bufferRegion, hks_nz, hks8],
          by simp [bufferRegion, hks_nz], hdisj_arr_ks⟩)
      (fun _ hj => by simp at hj)
  have hhp_eq : globN resumed "heap_ptr" = globN state "heap_ptr" := by
    simp [resumed, setVarHOLFinite, globN, hpost_glob]
  have hinv_res : BuildMptInv resumed := by
    obtain ⟨hA_st, hin_m, S, Nd, Nm, hWT, hm, hd⟩ := hinv
    have hml : locN resumed "m" = locN state "m" := by
      simp only [locN, hl_ne "m" (by decide)]
    have hsp_eq : globN resumed "scratch_ptr" = globN state "scratch_ptr" := by
      simp [resumed, setVarHOLFinite, globN, hpost_glob]
    have hag_res : AllocatorGrows state resumed :=
      ⟨le_of_eq hhp_eq.symm, le_of_eq hsp_eq⟩
    have hdisj_w : IvlsDisj [bufferRegion state ("mpt_key_scratch", 16)]
        (worldTypedIvls state S Nd) := by
      intro iv hiv j hj
      simp only [List.mem_singleton] at hiv
      subst iv
      exact bufferRegion_disj hWT ("mpt_key_scratch", 16) (by decide) (by decide) j hj
    have hbuf_ks : bufferRegion state ("mpt_key_scratch", 16) = (globN state "mpt_key_scratch", 16) := by
      simp [bufferRegion, hks_nz]
    have hcell : M11.SameTypedCells state resumed S Nd := by
      refine ⟨heff_res.be, heff_res.memaddrs, hA_st.1.memaddrs, ?_, ?_, ?_⟩
      · intro a hna
        apply heff_res.out_dom a
        rwa [hA_st.1.memaddrs]
      · intro a ha ha8 ⟨iv, hiv, ha1, ha2⟩
        have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        apply heff_res.cell_frame (BitVec.ofNat 64 a)
        intro x hx hcx
        have hx' : x = (globN state "mpt_key_scratch", 16) := by
          simp only [List.append_nil, List.mem_singleton, hbuf_ks] at hx
          exact hx
        subst hx'
        have hdj := hdisj_w (bufferRegion state ("mpt_key_scratch", 16)) (by simp) iv hiv
        rw [hbuf_ks] at hdj
        rw [hbit] at hcx
        obtain ⟨_, _⟩ := hcx
        rcases hdj with h0 | h0 | h | h <;> omega
      · intro b hb ⟨iv, hiv, hb1, hb2⟩
        apply heff_res.byte_frame b hb
        intro x hx hbx
        have hx' : x = (globN state "mpt_key_scratch", 16) := by
          simp only [List.append_nil, List.mem_singleton, hbuf_ks] at hx
          exact hx
        subst hx'
        have hdj := hdisj_w (bufferRegion state ("mpt_key_scratch", 16)) (by simp) iv hiv
        rw [hbuf_ks] at hdj
        obtain ⟨_, _⟩ := hbx
        rcases hdj with h0 | h0 | h | h <;> omega
    have hfeq : fixedObjects resumed = fixedObjects state :=
      M11.fixedObjects_eq_of_nonHeapGlobalsKept hA_st.2 hWT.1 hWT.2.2.1 hcell
        (fun name _ _ _ => by simp [resumed, setVarHOLFinite, hpost_glob])
    have hFT_res : FixedTyped resumed :=
      M11.fixedTyped_of_eq hW_res.1 hWT.2.2.1 (le_of_eq hhp_eq.symm) (le_of_eq hsp_eq) hfeq
    have hglob_eq : ∀ g, globN resumed g = globN state g := fun g => by
      simp [resumed, setVarHOLFinite, globN, hpost_glob]
    obtain ⟨hWT_res, _⟩ := M11.worldTypedWith_congr_w1 hA_st hW_res.1
      (le_of_eq hhp_eq.symm) (le_of_eq hsp_eq) (fun g _ => hglob_eq g) hcell hWT
      ⟨hFT_res, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
    have hfp_eq : ∀ t ∈ S, htabFootprint resumed t = htabFootprint state t :=
      fun t ht => M11.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
    have hne_nd_eq : nodeExtents resumed Nd = nodeExtents state Nd :=
      M11.nodeExtents_eq hWT.2.2.2.1 hcell
    obtain ⟨hm_al, hm_w, hm_tab, hm_fix, hm_nh, hm_root, hm_ext⟩ := hm
    have hu_obj : ∀ o ∈ mptObjIvls state Nm (locN state "m"), o.2 ≠ 0 →
        P3MptSet.IvlUnhit state resumed o := by
      intro o ho hpos a _ hhit
      apply heff_res.cell_frame a
      intro x hx hcx
      have hx' : x = (globN state "mpt_key_scratch", 16) := by
        simp only [List.append_nil, List.mem_singleton, hbuf_ks] at hx
        exact hx
      subst hx'
      have hdj : Disj o (globN state "mpt_key_scratch", 16) := by
        rcases List.mem_cons.mp ho with rfl | ho'
        · exact hm_fix _ hfix_ks
        · exact (hm_ext o ho').2.2 _ hfix_ks
      obtain ⟨_, _⟩ := hhit
      obtain ⟨_, _⟩ := hcx
      rcases hdj with h0 | h0 | h | h <;> omega
    have hu_m : P3MptSet.IvlUnhit state resumed (locN state "m", 16) :=
      hu_obj _ (by simp [mptObjIvls]) (by simp)
    have hm_hi : locN state "m" + 16 ≤ 2 ^ 64 :=
      P3MptSet.ivl_allocated_bound hA_st.2 hm_al
    have hm_root_eq : memW resumed (locN state "m") = memW state (locN state "m") :=
      P3MptSet.memW_eq_of_ivlUnhit hu_m hm_w.1 hm_hi ⟨by omega, by omega⟩
    have hm_nh_res : NodeHeap resumed Nm :=
      P3MptSet.nodeHeap_congr_unhit hA_st.1 hW_res.1.1 heff_res.be hag_res hm_nh
        (fun o ho hpos => hu_obj o (List.mem_cons_of_mem _ ho) hpos)
    have hne_nm_eq : nodeExtents resumed Nm = nodeExtents state Nm := by
      unfold nodeExtents
      apply List.flatMap_congr
      intro nd hnd
      obtain ⟨hk3, _, hin_nd, hw_nd, _, _, hkey_nd, _⟩ := hm_nh.1 nd hnd
      have hhi_nd : nd + nodeSize (memW state nd) ≤ 2 ^ 64 := by
        have : heapLimit ≤ 2 ^ 64 := by decide
        have : nd + nodeSize (memW state nd) ≤ heapLimit := hin_nd.2
        omega
      have hsz_ge : 32 ≤ nodeSize (memW state nd) := by unfold nodeSize; split_ifs <;> omega
      have hu_nd : P3MptSet.IvlUnhit state resumed (nd, nodeSize (memW state nd)) :=
        hu_obj _ (List.mem_cons_of_mem _ (by unfold nodeExtents; exact List.mem_flatMap.2 ⟨nd, hnd, by simp [nodeIvl]⟩))
          (by dsimp only; omega)
      have hw0 : memW resumed nd = memW state nd :=
        P3MptSet.memW_eq_of_ivlUnhit hu_nd hw_nd.1 hhi_nd ⟨by omega, by omega⟩
      have hni_eq : nodeIvl resumed nd = nodeIvl state nd := by simp [nodeIvl, hw0]
      have hnp_eq : nodePath resumed nd = nodePath state nd := by
        unfold nodePath
        rw [hw0]
        by_cases h12 : memW state nd = 1 ∨ memW state nd = 2
        · have h56 : 56 ≤ nodeSize (memW state nd) := by
            unfold nodeSize
            rcases h12 with c1 | c2
            · simp [c1]
            · simp [c2]
          have hnd8 : nd % 8 = 0 := hw_nd.1
          have hw32 : memW resumed (nd + 32) = memW state (nd + 32) :=
            P3MptSet.memW_eq_of_ivlUnhit hu_nd (by omega) hhi_nd ⟨by omega, by omega⟩
          have hw40 : memW resumed (nd + 40) = memW state (nd + 40) :=
            P3MptSet.memW_eq_of_ivlUnhit hu_nd (by omega) hhi_nd ⟨by omega, by omega⟩
          rw [hw32, hw40]
        · simp [h12]
      rw [hni_eq, hnp_eq]
    refine ⟨hW_res.1, ?_, S, Nd, Nm, hWT_res, ?_, ?_⟩
    · rw [hml, hhp_eq]
      exact hin_m
    · rw [hml]
      refine ⟨hag_res.allocated hm_al, P3MptSet.wordsOK_transfer hA_st.1 hW_res.1.1 hm_w,
        ?_, ?_, hm_nh_res, ?_, ?_⟩
      · intro t ht iv hiv
        rw [hfp_eq t ht] at hiv
        exact hm_tab t ht iv hiv
      · rw [hfeq]
        exact hm_fix
      · rw [hm_root_eq]
        exact hm_root
      · rw [hne_nm_eq]
        intro o ho
        refine ⟨(hm_ext o ho).1, ?_, ?_⟩
        · intro t ht iv hiv
          rw [hfp_eq t ht] at hiv
          exact (hm_ext o ho).2.1 t ht iv hiv
        · rw [hfeq]
          exact (hm_ext o ho).2.2
    · rw [hml, hne_nm_eq, hne_nd_eq]
      exact hd
  have hklen_lookup : resumed.locals.lookup (ofString "klen") = some (.val (.word klen)) := by
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hklen_le32 : locN resumed "klen" ≤ 32 := by
    have : locN resumed "klen" = klen.toNat := by simp [locN, hklen_lookup]
    omega
  have hl_loc : ∀ name, ofString "klen" ≠ ofString name → locN resumed name = locN state name :=
    fun name hne => by simp only [locN, hl_ne name hne]
  refine ⟨⟨hready_res, hinv_res, ?_, ?_, ?_⟩, ?_, hklen_le32, ⟨klen, hklen_lookup⟩⟩
  · change Inside (locN resumed "slice_arr", 16 * locN resumed "n") sourceBase (locN resumed "mark")
    rw [hl_loc "slice_arr" (by decide), hl_loc "n" (by decide), hl_loc "mark" (by decide)]
    exact hin_mark
  · change locN resumed "mark" ≤ globN resumed "heap_ptr"
    rw [hl_loc "mark" (by decide), hhp_eq]
    exact hmark_le
  · intro name hname
    obtain ⟨w, hw⟩ := hlocs name hname
    refine ⟨w, ?_⟩
    rw [hl_ne name (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
      rcases hname with rfl | rfl | rfl <;> decide)]
    exact hw
  · change locN resumed "i" < locN resumed "n"
    rw [hl_loc "i" (by decide), hl_loc "n" (by decide)]
    exact hlt

theorem callEntryOn_mpt_root_bmi :
    CallEntryOn BuildMptLoopInv MptObjReady (ofString "mpt_root")
      [.var .local (ofString "m"), .var .local (ofString "out")] := by
  intro F s values body callee ret hcode hP hargs hl
  obtain ⟨v1, v2, he1, he2, hc1, hc2⟩ :=
    callee_param_two_exp s (ofString "mpt_root")
      (ofString "m") (ofString "out") .one .one _ _
      (by rw [hcode]; exact ArenaNodeRlp.lookup_root) _ _ values body callee ret hargs hl
  have hm : callee.lookup (ofString "m") = s.locals.lookup (ofString "m") :=
    hc1.trans (by simpa only [evalAt, evalHOLExact] using he1.symm)
  have hinv : BuildMptInv (callEntryStateHOLFinite s callee) :=
    localsOnly_buildMptInv s callee (s.clock - 1)
      (fun name hname => by
        simp only [List.mem_singleton] at hname
        subst name
        exact hm) hP.2.1
  exact buildMptInv_mptObjReady hinv

theorem buildMptIndexed_tail_bound
    (hroot : TerminatingFunBoundedOn MptObjReady (ofString "mpt_root") K.«mpt_root»)
    (hrelease : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») :
    TerminatingProgBoundedOn BuildMptLoopInv
      (.seq
        (.call (some (none, none)) (ofString "mpt_root")
          [.var .local (ofString "m"), .var .local (ofString "out")])
        (.seq
          (.call (some (none, none)) (ofString "heap_release")
            [.var .local (ofString "mark")])
          (.return (.const 0))))
      ((K.«mpt_root» + 1) + (K.«heap_release» + 1)) := by
  exact TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.seq_guestInv_after
      (TerminatingProgBoundedOn.call_on hroot none _ callEntryOn_mpt_root_bmi)
      (fun s h => h.1.1.1.1)
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.call_guestInv hrelease none
          [.var .local (ofString "mark")])
        (TerminatingProgBoundedOn.of_clock (fun s => clock_return s (.const 0)))))
    (by omega)

theorem evalAt_slice_word_bmi {F : Type} (s : PanSemStateFiniteExact 64 F)
    (harr : ∃ w : BitVec 64, s.locals.lookup (ofString "slice_arr") = some (.val (.word w)))
    (hi : ∃ w : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hlt : locN s "i" < locN s "n")
    (hin : Inside (locN s "slice_arr", 16 * locN s "n") sourceBase (globN s "heap_ptr"))
    (hA : ArenaReady s) (_hw : WordsOK s (locN s "slice_arr", 16 * locN s "n")) :
    (∀ v, evalAt s (.load .one
        (.op .add [.var .local (ofString "slice_arr"),
          .panop .mul [.var .local (ofString "i"), .const 16]])) = some v →
      ∃ w : BitVec 64, v = .val (.word w) ∧
        w.toNat = memW s (locN s "slice_arr" + 16 * locN s "i")) ∧
    (∀ v, evalAt s (.load .one
        (.op .add
          [.var .local (ofString "slice_arr"),
           .panop .mul [.var .local (ofString "i"), .const 16],
           .const 8])) = some v →
      ∃ w : BitVec 64, v = .val (.word w) ∧
        w.toNat = memW s (locN s "slice_arr" + 16 * locN s "i" + 8)) := by
  obtain ⟨wa, hwa⟩ := harr
  obtain ⟨wi, hwi⟩ := hi
  have hwa_nat : wa.toNat = locN s "slice_arr" := by simp [locN, hwa]
  have hwi_nat : wi.toNat = locN s "i" := by simp [locN, hwi]
  have hfit : locN s "slice_arr" + 16 * locN s "n" < 2 ^ 64 := by
    have hlim : heapLimit < 2 ^ 64 := by decide
    have hheap := hA.2.2.1
    have hbound := hin.2
    dsimp only at hbound
    omega
  have hmul : (wi * 16#64).toNat = 16 * locN s "i" := by
    rw [BitVec.toNat_mul, hwi_nat]
    change (locN s "i" * 16) % 2 ^ 64 = 16 * locN s "i"
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hadd0 : (wa + wi * 16#64).toNat = locN s "slice_arr" + 16 * locN s "i" := by
    rw [BitVec.toNat_add, hwa_nat, hmul, Nat.mod_eq_of_lt (by omega)]
  have hadd8 : (wa + (wi * 16#64 + 8#64)).toNat = locN s "slice_arr" + 16 * locN s "i" + 8 := by
    have : wa + (wi * 16#64 + 8#64) = wa + wi * 16#64 + 8#64 := (BitVec.add_assoc _ _ _).symm
    rw [this, BitVec.toNat_add, hadd0]
    change (locN s "slice_arr" + 16 * locN s "i" + 8) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt (by omega)]
  have hb0 : BitVec.ofNat 64 (locN s "slice_arr" + 16 * locN s "i") = wa + wi * 16#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hadd0]
  have hb8 : BitVec.ofNat 64 (locN s "slice_arr" + 16 * locN s "i" + 8) = wa + (wi * 16#64 + 8#64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hadd8]
  constructor
  · intro v hv
    simp [evalAt, evalHOLExact, evalListHOLExact, hwa, hwi, panOpHOL, valueIsWord, valueWord,
      wordOpHOL, wordOp, memLoadHOLExact] at hv
    rcases hm : s.memory (wa + wi * 16#64) with ⟨y⟩
    refine ⟨y, by rw [← hv.2, hm], ?_⟩
    unfold memW
    rw [hb0, hm]
  · intro v hv
    simp [evalAt, evalHOLExact, evalListHOLExact, hwa, hwi, panOpHOL, valueIsWord, valueWord,
      wordOpHOL, wordOp, memLoadHOLExact] at hv
    rcases hm : s.memory (wa + (wi * 16#64 + 8#64)) with ⟨y⟩
    refine ⟨y, by rw [← hv.2, hm], ?_⟩
    unfold memW
    rw [hb8, hm]

theorem callEntryOn_mpt_set_bmi :
    CallEntryOn BuildMptAfterKey MptSetReady (ofString "mpt_set")
      [.var .local (ofString "m"),
       .var .global (ofString "mpt_key_scratch"),
       .var .local (ofString "klen"),
       .load .one (.op .add [.var .local (ofString "slice_arr"),
         .panop .mul [.var .local (ofString "i"), .const 16]]),
       .load .one (.op .add
         [.var .local (ofString "slice_arr"),
          .panop .mul [.var .local (ofString "i"), .const 16],
          .const 8])] := by
  intro F s values body callee ret hcode hP hargs hl
  obtain ⟨hloop, hlt, hklen_le, hwklen⟩ := hP
  obtain ⟨hready, hinv, _, _, hlocs⟩ := hloop
  obtain ⟨v1, v2, v3, v4, v5, he1, he2, he3, he4, he5, hc1, hc2, hc3, hc4, hc5⟩ :=
    callee_param_five_exp s (ofString "mpt_set")
      (ofString "m") (ofString "key") (ofString "klen") (ofString "vptr") (ofString "vlen")
      .one .one .one .one .one _ _
      (by rw [hcode]; exact P3MptSet.lookup_mpt_set)
      _ _ _ _ _ values body callee ret hargs hl
  have hm : callee.lookup (ofString "m") = s.locals.lookup (ofString "m") :=
    hc1.trans (by simpa only [evalAt, evalHOLExact] using he1.symm)
  have hklen : callee.lookup (ofString "klen") = s.locals.lookup (ofString "klen") :=
    hc3.trans (by simpa only [evalAt, evalHOLExact] using he3.symm)
  obtain ⟨_, hsl8⟩ := evalAt_slice_word_bmi s
    (hready.2.1 "slice_arr" (by simp))
    (hlocs "i" (by simp))
    hlt hready.2.2.2.1 hready.1.1 hready.2.2.2.2.1
  obtain ⟨wvlen, rfl, hwvlen⟩ := hsl8 v5 he5
  let entry := callEntryStateHOLFinite s callee
  have hinv_e : BuildMptInv entry :=
    localsOnly_buildMptInv s callee (s.clock - 1)
      (fun name hname => by
        simp only [List.mem_singleton] at hname
        subst name
        exact hm) hinv
  have hklen_e : locN entry "klen" ≤ 32 := by
    have : locN entry "klen" = locN s "klen" := by
      simp only [entry, callEntryStateHOLFinite, locN, hklen]
    omega
  have hvlen_e : locN entry "vlen" < 2 ^ 40 := by
    have : locN entry "vlen" = wvlen.toNat := by
      simp [entry, callEntryStateHOLFinite, locN, hc5]
    rw [this, hwvlen]
    exact hready.2.2.2.2.2.2 (locN s "i") hlt
  exact buildMptInv_mptSetReady hinv_e hklen_e hvlen_e

theorem buildMptIndexed_increment_bmi {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hloop : BuildMptLoopInv s) (hlt : locN s "i" < locN s "n") :
    ∃ post, evaluateHOLFiniteState s
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 1])) = (none, post) ∧
      BuildMptLoopInv post ∧ buildMptLoopRank post < buildMptLoopRank s := by
  obtain ⟨i, hi⟩ := hloop.2.2.2.2 "i" (by simp)
  let post := setVarHOLFinite (ofString "i") (.val (.word (i + 1))) s
  refine ⟨post, ?_, buildMptLoopInv_set_counter hloop (i + 1), ?_⟩
  · rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
      valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
      shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, post]
  · apply buildMptLoopRank_decreases i hi hlt hloop.1.2.2.1
    · simp [post, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [post, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "n" by decide]

theorem mptSetStep_caller_bmi {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    (hm_callee : callee.lookup (ofString "m") = s.locals.lookup (ofString "m"))
    (hstep : MptObjStep (fun t =>
      [bufferRegion t ("keccak_pad", 136), bufferRegion t ("keccak_st", 200),
        bufferRegion t ("mpt_hash_scratch", 40)])
      ["heap_ptr", "scratch_ptr"] R10Shards.P26_P28.stdKeep
      (callEntryStateHOLFinite s callee) post) :
    MptObjStep (fun t =>
      [bufferRegion t ("keccak_pad", 136), bufferRegion t ("keccak_st", 200),
        bufferRegion t ("mpt_hash_scratch", 40)])
      ["heap_ptr", "scratch_ptr"] R10Shards.P26_P28.stdKeep s
      { post with locals := s.locals } := by
  let entry := callEntryStateHOLFinite s callee
  have hm_eq : locN entry "m" = locN s "m" := by
    simp only [entry, callEntryStateHOLFinite, locN, hm_callee]
  refine ⟨localsFree_arenaReady post s.locals post.clock hstep.1,
    hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, ?_⟩
  intro S Nd Nm hWT hm hd hR
  have hWT_e : WorldTypedWith entry S Nd :=
    (worldTypedWith_build_locals s callee (s.clock - 1) S Nd).2 hWT
  have hm_e : MptObjInWith entry S Nm (locN entry "m") := by
    rw [hm_eq]
    exact hm
  have hd_e : IvlsDisj ((locN entry "m", 16) ::
      [bufferRegion entry ("keccak_pad", 136), bufferRegion entry ("keccak_st", 200),
        bufferRegion entry ("mpt_hash_scratch", 40)] ++ nodeExtents entry Nm)
      (nodeExtents entry Nd) := by
    rw [hm_eq]; exact hd
  have hR_e : IvlsDisj
      [bufferRegion entry ("keccak_pad", 136), bufferRegion entry ("keccak_st", 200),
        bufferRegion entry ("mpt_hash_scratch", 40)]
      (worldTypedIvls entry S Nd ++ mptObjIvls entry Nm (locN entry "m")) := by
    rw [hm_eq]; exact hR
  obtain ⟨S', Nd', Nm', hsub, hWT', hm', hd', hog, hfr⟩ :=
    hstep.2.2.2.2 S Nd Nm hWT_e hm_e hd_e hR_e
  rw [hm_eq] at hm' hd' hog hfr
  refine ⟨S', Nd', Nm', hsub,
    (worldTypedWith_build_locals post s.locals post.clock S' Nd').2 hWT',
    hm', hd', hog, hfr⟩

theorem gbody_mpt_set :
    TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set» := by
  have g_del_body :=
    R16Shards.PrimC08Closure.«gbody__mpt_delete_node_body»
      R11Adapters.«fb__collapse_branch»
      R11Adapters.«fb__delete_ext_finish»
      R11Adapters.«fb_common_prefix_length»
      Merged.fb_memeq
      Merged.fb_mpt_fail
      Merged.fb_node_invalidate
      Merged.fb_scratch_alloc
      R16Shards.«nf__collapse_branch»
      R16Shards.«nf__delete_ext_finish»
      R10Ports.ro_common_prefix_length
      Merged.rv_common_prefix_length
      InitECandidate.Solver.Wave8Contracts.M15.«ro_memeq»
      R11Adapters.ReadOnlyLeaves.«ro_mpt_fail»
      Merged.nf_node_invalidate
      EvmFrameSpecs.iz_node_invalidate
      R10Shards.P02.ww_scratch_alloc
      Merged.rt_scratch_alloc
  have g_del :=
    «gbody__mpt_delete_node»
      g_del_body
      Merged.fb_scratch_mark
      Merged.fb_scratch_release
      R10Shards.P02.ro_scratch_mark
  have g_ins :=
    R16Shards.PrimC08Closure.«gbody__mpt_insert_node»
      R11Adapters.«fb__insert_into_leaf»
      R11Adapters.«fb__split_extension»
      R11Adapters.«fb_common_prefix_length»
      Merged.fb_mpt_fail
      Merged.fb_node_invalidate
      Merged.fb_node_new_ext
      R10Shards.P02.fb_node_new_leaf
      R16Shards.«nf__insert_into_leaf»
      R16Shards.«nf__split_extension»
      R10Ports.ro_common_prefix_length
      Merged.rv_common_prefix_length
      R11Adapters.ReadOnlyLeaves.«ro_mpt_fail»
      Merged.nf_node_invalidate
      EvmFrameSpecs.iz_node_invalidate
      R16Shards.«nf_node_new_ext»
      R16Shards.«rt_node_new_ext»
      R16Shards.«nf_node_new_leaf»
  exact P3C10C12.«gbody_mpt_set»
    g_del g_ins R11Adapters.«fb_mpt_nibble_key»
    R16Shards.ww_mpt_nibble_key
    R16Shards.PrimC08Closure.«nk_mpt_nibble_key»

section MptObjStepHelper

open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

structure MptEff {F : Type}
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl)
    (B : List (String × Nat))
    (gw : List String)
    (s post : PanSemStateFiniteExact 64 F) : Prop where
  arena   : ArenaReady post
  grows   : AllocatorGrows s post
  gw_kept : GlobalsKept gw s post
  dom_wr  : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a
  write_frame : ∀ Nm : List Nat,
    Allocated s (locN s "m", 16) →
    WordsOK s (locN s "m", 16) →
    NodeHeap s Nm →
    RootIn Nm (memW s (locN s "m")) →
    (∀ o ∈ nodeExtents s Nm, Disj o (locN s "m", 16) ∧ ∀ gs ∈ B, Disj o (bufferRegion s gs)) →
    (∀ gs ∈ B, Disj (locN s "m", 16) (bufferRegion s gs)) →
    (∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ ivl ∈ R s, CellHitsPos a.toNat ivl) ∨
      (∃ gs ∈ B, CellHitsPos a.toNat (bufferRegion s gs)) ∨
      (∃ o ∈ mptObjIvls s Nm (locN s "m"), CellHitsPos a.toNat o) ∨
      CellHitsPos a.toNat (freeGap s) ∨
      CellHitsPos a.toNat (heapFree s)) ∧
    (∀ b : Nat, b < 2 ^ 64 → memB post b ≠ memB s b →
      (∃ ivl ∈ R s, InIvl b ivl) ∨
      (∃ gs ∈ B, InIvl b (bufferRegion s gs)) ∨
      (∃ o ∈ mptObjIvls s Nm (locN s "m"), InIvl b o) ∨
      InIvl b (freeGap s) ∨
      InIvl b (heapFree s))
  obj_pres : ∀ Nm : List Nat,
    Allocated s (locN s "m", 16) →
    WordsOK s (locN s "m", 16) →
    NodeHeap s Nm →
    RootIn Nm (memW s (locN s "m")) →
    (∀ o ∈ nodeExtents s Nm, Disj o (locN s "m", 16) ∧ ∀ gs ∈ B, Disj o (bufferRegion s gs)) →
    (∀ gs ∈ B, Disj (locN s "m", 16) (bufferRegion s gs)) →
    IvlsDisj (R s) (mptObjIvls s Nm (locN s "m")) →
    ∃ Nm' : List Nat,
      NodeHeap post Nm' ∧
      RootIn Nm' (memW post (locN s "m")) ∧
      (∀ o ∈ nodeExtents post Nm',
        o = (0, 0) ∨
        (∃ j ∈ nodeExtents s Nm, Inside o j.1 (j.1 + j.2)) ∨
        Inside o (globN s "heap_ptr") (globN post "heap_ptr"))

theorem freshBufsOK_of_gw_alloc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {gw : List String} (hgw : GlobalsKept gw s post)
    (hsub : ∀ g ∈ gw, ofString g = ofString "heap_ptr" ∨ ofString g = ofString "scratch_ptr") :
    FreshBufsOK s post := by
  have hg_eq : ∀ gn ∈ globalBuffers, globN post gn.1 = globN s gn.1 := by
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" ∧ ofString gn.1 ≠ ofString "scratch_ptr" := by
      revert gn hgn; decide
    apply globN_eq_of_lookup
    apply hgw
    intro hm
    obtain ⟨g, hg_mem, hg_eq'⟩ := List.mem_map.1 hm
    rcases hsub g hg_mem with h1 | h2
    · exact hne.1 (hg_eq'.symm.trans h1)
    · exact hne.2 (hg_eq'.symm.trans h2)
  refine ⟨fun gn hgn => Or.inl (hg_eq gn hgn), ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi _ _ h1 _
  exact absurd (hg_eq _ (List.getElem_mem hi)) h1.1

theorem disj_fresh_heap_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) {o j : Ivl}
    (ho : Inside o (globN s "heap_ptr") (globN post "heap_ptr"))
    (hj : j.2 = 0 ∨ Allocated s j) :
    Disj o j := by
  rcases hj with hj0 | hal
  · exact Or.inr (Or.inl hj0)
  · rcases hal with ⟨_, hj2⟩ | ⟨hj1, _⟩
    · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hj2 ho.1)))
    · have hsep : heapLimit ≤ scratchStart := by decide
      have := hAp.2.1; have := hAs.2.2.1; have := hAs.2.2.2.1
      obtain ⟨ho1, ho2⟩ := ho
      exact Or.inr (Or.inr (Or.inl (by omega)))

theorem disj_inside_left {o j k : Ivl}
    (hin : Inside o j.1 (j.1 + j.2)) (hdj : Disj j k) : Disj o k := by
  obtain ⟨h1, h2⟩ := hin
  rcases hdj with h0 | h0 | hd | hd
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

private theorem bufferRegion_in_fixedObjects_mpt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (gs : String × Nat) (hgb : gs ∈ globalBuffers) :
    bufferRegion s gs ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.2 ⟨gs, hgb, rfl⟩

private theorem mptObjIvl_disj_worldTypedIvls {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd Nm : List Nat}
    (hWT : WorldTypedWith s S Nd)
    (hm : MptObjInWith s S Nm (locN s "m"))
    (hdisj_nd : IvlsDisj ((locN s "m", 16) :: nodeExtents s Nm) (nodeExtents s Nd))
    {o i : Ivl} (ho : o ∈ mptObjIvls s Nm (locN s "m")) (hi : i ∈ worldTypedIvls s S Nd) :
    Disj o i := by
  obtain ⟨_, hJ, _, _⟩ := hWT
  unfold worldTypedIvls at hi
  simp only [List.mem_append] at hi
  have ho_fix_tab : (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj o j) ∧ ∀ j ∈ fixedObjects s, Disj o j := by
    rcases List.mem_cons.1 ho with rfl | ho_ne
    · exact ⟨hm.2.2.1, hm.2.2.2.1⟩
    · exact (hm.2.2.2.2.2.2 o ho_ne).2
  rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
  · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
    exact ho_fix_tab.1 t ht i hfp
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
    exact ho_fix_tab.2 _ (typedRecord_mem_fixedObjects s hr)
  · simp only [List.mem_singleton] at h3; subst h3
    have hj_fo : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈
        fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_singleton.2 rfl
    exact ho_fix_tab.2 _ hj_fo
  · have hfo : i ∈ fixedObjects s := by
      unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_right; exact h4
    exact ho_fix_tab.2 i hfo
  · have hfo : i ∈ fixedObjects s := by
      unfold fixedObjects; exact List.mem_append_right _ h5
    exact ho_fix_tab.2 i hfo
  · exact hdisj_nd o ho i h6

theorem MptEff.to_mptObjStep {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {B : List (String × Nat)} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F}
    (hMpt : MptObjReady s)
    (hB_ok : ∀ gs ∈ B, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hgw_sub : ∀ g ∈ gw, ofString g = ofString "heap_ptr" ∨ ofString g = ofString "scratch_ptr")
    (heff : MptEff R B gw s post) :
    MptObjStep R gw stdKeep s post := by
  have hAs : ArenaReady s := hMpt.1
  have hAp : ArenaReady post := heff.arena
  have hag : AllocatorGrows s post := heff.grows
  obtain ⟨S0, hWT0, ⟨Nm0, hm0⟩, _⟩ := hMpt.2
  obtain ⟨Nd0, hWTW0⟩ := (worldTyped_iff_with s S0).1 hWT0
  have hcore_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ gw.map ofString := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" ∧ ofString g ≠ ofString "scratch_ptr" := by
      revert g hg; decide
    intro hm
    obtain ⟨g', hg', heq⟩ := List.mem_map.1 hm
    rcases hgw_sub g' hg' with h1 | h2
    · exact hne.1 (heq.symm.trans h1)
    · exact hne.2 (heq.symm.trans h2)
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g :=
    fun g hg => globN_eq_of_lookup (heff.gw_kept (ofString g) (hcore_out g hg))
  have hbuf : FreshBufsOK s post := freshBufsOK_of_gw_alloc heff.gw_kept hgw_sub
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨mem_low_eq_of_domain_writes heff.dom_wr hAs.1 (by rw [sourceBase_val]; omega),
     mem_low_eq_of_domain_writes heff.dom_wr hAs.1 (by rw [sourceBase_val]; omega)⟩
  have hRecKept : RecordsKept R stdKeep s post := by
    have hF0 := hWTW0.2.2.1
    obtain ⟨hm0_al, hm0_w, hm0_tab, hm0_fix, hm0_nh, hm0_root, hm0_ext⟩ := hm0
    obtain ⟨hcell0, _⟩ := heff.write_frame Nm0 hm0_al hm0_w hm0_nh hm0_root
      (fun o ho => ⟨(hm0_ext o ho).1, fun gs hgs => (hm0_ext o ho).2.2 _ (bufferRegion_in_fixedObjects_mpt s gs (hB_ok gs hgs).1)⟩)
      (fun gs hgs => hm0_fix _ (bufferRegion_in_fixedObjects_mpt s gs (hB_ok gs hgs).1))
    intro rec hrec hgnz k hk hnoR
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], ?_⟩; simp at hk; omega
      · refine ⟨80, by simp [typedRecords], ?_⟩; simp at hk; omega
      · refine ⟨72, by simp [typedRecords], ?_⟩; simp at hk; omega
      · refine ⟨88, by simp [typedRecords], ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hk8, hksz⟩ := hrec_sz
    have hmf := typedRecord_mem_fixedObjects s htr
    have hmf_nz : (globN s rec.1, sz) ∈ fixedObjects s := by simpa [hgnz] using hmf
    have hwti_rec : (globN s rec.1, sz) ∈ worldTypedIvls s S0 Nd0 := by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨(rec.1, sz), htr, by simp [hgnz]⟩
    rcases hF0.1 _ hmf_nz with h0 | ⟨hal, hwords⟩
    · omega
    · have hhi := (ivl_allocated_bound hAs.2 hal).2
      have ha_lt : globN s rec.1 + k < 2 ^ 64 := by dsimp at hhi; omega
      unfold memW
      have hmem_eq : post.memory (BitVec.ofNat 64 (globN s rec.1 + k)) =
          s.memory (BitVec.ofNat 64 (globN s rec.1 + k)) := by
        by_contra hne
        have hcases := hcell0 _ hne
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at hcases
        have hin_rec : globN s rec.1 + k ≥ globN s rec.1 ∧ globN s rec.1 + k + 8 ≤ globN s rec.1 + sz :=
          ⟨by omega, by omega⟩
        rcases hcases with ⟨ivl, hivl, _, hhit⟩ | ⟨gs, hgs, hhit⟩ | ⟨o, ho, hhit⟩ | hfg | hhf
        · exact hnoR ivl hivl hhit
        · obtain ⟨hgs_gb, hgs_nt⟩ := hB_ok gs hgs
          have hdj := Disj.flip (untypedBuf_disj_worldTypedIvls hWTW0 gs hgs_gb hgs_nt _ hwti_rec)
          exact not_cellHitsPos_of_disj hin_rec hdj hhit
        · have hdj_o : Disj (globN s rec.1, sz) o := by
            rcases List.mem_cons.1 ho with rfl | ho_ne
            · exact Disj.flip (hm0_fix _ hmf_nz)
            · exact Disj.flip ((hm0_ext o ho_ne).2.2 _ hmf_nz)
          exact not_cellHitsPos_of_disj hin_rec hdj_o hhit
        · exact not_cellHitsPos_of_disj hin_rec (disj_allocated_freeGap hAs.2 hal) hfg
        · exact not_cellHitsPos_of_disj hin_rec (disj_allocated_heapFree hAs.2 hal) hhf
      rw [hmem_eq]
  refine ⟨hAp, hag.1, heff.gw_kept, hRecKept, fun S Nd Nm hWT hMptIn hDisjRNmNd hDisjRAll => ?_⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨hm_al, hm_w, hm_tab, hm_fix, hm_nh, hm_root, hm_ext⟩ := hMptIn
  have hDisjR_wti : IvlsDisj (R s) (worldTypedIvls s S Nd) :=
    fun r hr j hj => hDisjRAll r hr j (List.mem_append_left _ hj)
  have hDisjR_obj : IvlsDisj (R s) (mptObjIvls s Nm (locN s "m")) :=
    fun r hr j hj => hDisjRAll r hr j (List.mem_append_right _ hj)
  have hDisjObj_Nd : IvlsDisj ((locN s "m", 16) :: nodeExtents s Nm) (nodeExtents s Nd) := by
    intro o ho j hj
    rcases List.mem_cons.1 ho with rfl | ho_ne
    · exact hDisjRNmNd (locN s "m", 16) (List.mem_cons_self) j hj
    · exact hDisjRNmNd o (List.mem_cons_of_mem _ (List.mem_append_right _ ho_ne)) j hj
  have hNm_B : ∀ o ∈ nodeExtents s Nm, Disj o (locN s "m", 16) ∧ ∀ gs ∈ B, Disj o (bufferRegion s gs) :=
    fun o ho => ⟨(hm_ext o ho).1,
      fun gs hgs => (hm_ext o ho).2.2 _ (bufferRegion_in_fixedObjects_mpt s gs (hB_ok gs hgs).1)⟩
  have hm_B : ∀ gs ∈ B, Disj (locN s "m", 16) (bufferRegion s gs) :=
    fun gs hgs => hm_fix _ (bufferRegion_in_fixedObjects_mpt s gs (hB_ok gs hgs).1)
  obtain ⟨hcell, hbyte⟩ := heff.write_frame Nm hm_al hm_w hm_nh hm_root hNm_B hm_B
  obtain ⟨Nm', hNH_Nm', hRoot_Nm', hExt_Nm'⟩ :=
    heff.obj_pres Nm hm_al hm_w hm_nh hm_root hNm_B hm_B hDisjR_obj
  let keep0 : List Ivl := R s ++ B.map (bufferRegion s) ++ mptObjIvls s Nm (locN s "m") ++ [freeGap s]
  have hfr_pos : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ j ∈ keep0, CellHitsPos a.toNat j) ∨ CellHitsPos a.toNat (heapFree s) := by
    intro a hne
    rcases hcell a hne with ⟨ivl, hivl, hhit⟩ | ⟨gs, hgs, hhit⟩ | ⟨o, ho, hhit⟩ | hfg | hhf
    · left; refine ⟨ivl, ?_, hhit⟩
      simp only [keep0, List.mem_append]; exact Or.inl (Or.inl (Or.inl hivl))
    · left; refine ⟨bufferRegion s gs, ?_, hhit⟩
      simp only [keep0, List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨gs, hgs, rfl⟩)))
    · left; refine ⟨o, ?_, hhit⟩
      simp only [keep0, List.mem_append]; exact Or.inl (Or.inr ho)
    · left; refine ⟨freeGap s, ?_, hfg⟩
      simp only [keep0, List.mem_append, List.mem_singleton]; exact Or.inr trivial
    · exact Or.inr hhf
  have hu_wti_aligned : ∀ i ∈ worldTypedIvls s S Nd, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 →
      IvlUnhit s post i := by
    intro i hi hal hi1 hi2
    refine ivlUnhit_of_cellHitsPos hi1 hi2 hfr_pos (fun j hj => ?_) (disj_allocated_heapFree hAs.2 hal)
    simp only [keep0, List.mem_append, List.mem_singleton] at hj
    rcases hj with ((hjR | hjB) | hjM) | rfl
    · exact Disj.flip (hDisjR_wti j hjR i hi)
    · obtain ⟨gs, hgs, rfl⟩ := List.mem_map.1 hjB
      obtain ⟨hgs_gb, hgs_nt⟩ := hB_ok gs hgs
      exact Disj.flip (untypedBuf_disj_worldTypedIvls ⟨hT, hJ, hF, hTr⟩ gs hgs_gb hgs_nt i hi)
    · exact Disj.flip (mptObjIvl_disj_worldTypedIvls ⟨hT, hJ, hF, hTr⟩ ⟨hm_al, hm_w, hm_tab, hm_fix, hm_nh, hm_root, hm_ext⟩ hDisjObj_Nd hjM hi)
    · exact disj_allocated_freeGap hAs.2 hal
  have hu_fix_wti : ∀ i ∈ worldTypedIvls s S Nd, i ∈ fixedObjects s → i.2 ≠ 0 → IvlUnhit s post i := by
    intro i hwti hfi hpos
    rcases hF.1 i hfi with h0 | ⟨hal, hw⟩
    · exact absurd h0 hpos
    · exact hu_wti_aligned i hwti hal hw.1 hw.2.1
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
    intro t ht i hi
    have hal := ((hT.2.1 t ht).2 i hi).1
    have hw := ((hT.2.1 t ht).1.1 i hi).2
    refine hu_wti_aligned i ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; left
    exact List.mem_flatMap.2 ⟨t, ht, hi⟩
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords]))
      (by simp)
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords]))
      (by simp)
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords]))
      (by simp)
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords]))
      (by simp)
  have hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hcnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hcnz])
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; simp [hcnz])
      (by dsimp only; omega)
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi h24 =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hpos =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
      hpos
  have hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hal := (hTr.1.1 n hn).2.1
    have hw := (hTr.1.1 n hn).2.2.2.1
    refine hu_wti_aligned _ ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls; refine List.mem_append.2 (Or.inr ?_)
    unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      have hp_wti : (memW s (n + 32), memW s (n + 40)) ∈ worldTypedIvls s S Nd := by
        unfold worldTypedIvls; exact List.mem_append.2 (Or.inr hp_ne)
      by_contra hne_b
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; dsimp at this; omega
      rcases hbyte _ ha_lt hne_b with ⟨ivl, hivl, hin_ivl⟩ | ⟨gs, hgs, hin_gs⟩ | ⟨o, ho, hin_o⟩ | hfg | hhf
      · have hdj := hDisjR_wti ivl hivl _ hp_wti
        unfold InIvl at hin_ivl; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · obtain ⟨hgs_gb, hgs_nt⟩ := hB_ok gs hgs
        have hdj := untypedBuf_disj_worldTypedIvls ⟨hT, hJ, hF, hTr⟩ gs hgs_gb hgs_nt _ hp_wti
        unfold InIvl at hin_gs; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := hDisjObj_Nd o ho _ hp_ne
        unfold InIvl at hin_o; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := disj_allocated_freeGap hAs.2 hal_p
        unfold InIvl at hfg; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := disj_allocated_heapFree hAs.2 hal_p
        unfold InIvl at hhf; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
  have hbo_eq := (blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst).1
  have hbal_eq := (balObjects_eq_of_unhit hAs.2 hT hF (hcore "bal_accounts" (by decide))
    hu_tab hu_bal hlow).1
  obtain ⟨hF_post, hfix_new⟩ := fixedTyped_of_freshBufsOK hAs hAp hag hF
    (hcore "journal" (by decide)) (hcore "journal_cap" (by decide)) hbo_eq hbal_eq hbuf
  obtain ⟨hWT_post, hOG_world, hne_eq, hfp_eq⟩ := worldTypedWith_congr_w1 hAs hAp hag hcore
    ⟨hT, hJ, hF, hTr⟩ hu_tab hu_ws hu_bs hu_ts hu_bo hu_jr hu_bo_lst hu_bal hu_nd_rec hu_nd_byte
    hlow hF_post hfix_new
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_eq, hbal_eq, hcore "journal" (by decide), hcore "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" ∧ ofString gn.1 ≠ ofString "scratch_ptr" := by
      revert gn hgn; decide
    have heq : globN post gn.1 = globN s gn.1 := by
      apply globN_eq_of_lookup
      apply heff.gw_kept
      intro hm
      obtain ⟨g, hg_mem, hg_eq'⟩ := List.mem_map.1 hm
      rcases hgw_sub g hg_mem with h1 | h2
      · exact hne.1 (hg_eq'.symm.trans h1)
      · exact hne.2 (hg_eq'.symm.trans h2)
    rw [heq]
  have hMptIn_post : MptObjInWith post S Nm' (locN s "m") := by
    refine ⟨hag.allocated hm_al, wordsOK_transfer hAs.1 hAp.1 hm_w, ?_, ?_, hNH_Nm', hRoot_Nm', ?_⟩
    · intro t ht i hi
      rw [hfp_eq t ht] at hi
      exact hm_tab t ht i hi
    · rw [hfix_eq]; exact hm_fix
    · intro o ho
      rcases hExt_Nm' o ho with rfl | ⟨j, hj, hin_j⟩ | hin_fr
      · exact ⟨Or.inl rfl, fun _ _ _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩
      · refine ⟨disj_inside_left hin_j (hm_ext j hj).1, ?_, ?_⟩
        · intro t ht i hi
          rw [hfp_eq t ht] at hi
          exact disj_inside_left hin_j ((hm_ext j hj).2.1 t ht i hi)
        · rw [hfix_eq]
          intro f hf
          exact disj_inside_left hin_j ((hm_ext j hj).2.2 f hf)
      · refine ⟨disj_fresh_heap_allocated hAs.2 hAp.2 hin_fr (Or.inr hm_al), ?_, ?_⟩
        · intro t ht i hi
          rw [hfp_eq t ht] at hi
          exact disj_fresh_heap_allocated hAs.2 hAp.2 hin_fr (Or.inr (((hT.2.1 t ht).2 i hi).1))
        · rw [hfix_eq]
          intro f hf
          exact disj_fresh_heap_allocated hAs.2 hAp.2 hin_fr
            ((hF.1 f hf).elim Or.inl (fun h => Or.inr h.1))
  have hDisjPost : IvlsDisj ((locN s "m", 16) :: nodeExtents post Nm') (nodeExtents post Nd) := by
    rw [hne_eq]
    intro o ho p hp
    have hp_al : p.2 = 0 ∨ Allocated s p := by
      unfold nodeExtents at hp
      obtain ⟨n, hn, hnp⟩ := List.mem_flatMap.1 hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hnp
      rcases hnp with rfl | rfl
      · exact Or.inr (hTr.1.1 n hn).2.1
      · unfold nodePath
        split
        · rename_i hcond
          rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
          · exact absurd h0 hcond.2
          · exact Or.inr hal
        · exact Or.inl rfl
    rcases List.mem_cons.1 ho with rfl | ho_ne
    · exact hDisjObj_Nd (locN s "m", 16) List.mem_cons_self p hp
    · rcases hExt_Nm' o ho_ne with rfl | ⟨j, hj, hin_j⟩ | hin_fr
      · exact Or.inl rfl
      · exact disj_inside_left hin_j (hDisjObj_Nd j (List.mem_cons_of_mem _ hj) p hp)
      · exact disj_fresh_heap_allocated hAs.2 hAp.2 hin_fr hp_al
  have hOG_all : OwnedGrows s post
      (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m"))
      (worldOwned post S Nd ++ mptObjIvls post Nm' (locN s "m")) := by
    intro o ho
    rcases List.mem_append.1 ho with ho_w | ho_m
    · rcases hOG_world o ho_w with rfl | ⟨j, hj, hin⟩ | hfr
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨j, List.mem_append_left _ hj, hin⟩)
      · exact Or.inr (Or.inr hfr)
    · rcases List.mem_cons.1 ho_m with rfl | ho_ne
      · exact Or.inr (Or.inl ⟨(locN s "m", 16), List.mem_append_right _ List.mem_cons_self,
          Nat.le_refl _, Nat.le_refl _⟩)
      · rcases hExt_Nm' o ho_ne with rfl | ⟨j, hj, hin_j⟩ | hfr
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨j, List.mem_append_right _ (List.mem_cons_of_mem _ hj), hin_j⟩)
        · exact Or.inr (Or.inr hfr)
  refine ⟨S, Nd, Nm', fun _ ht => ht, hWT_post, hMptIn_post, hDisjPost, hOG_all, ?_⟩
  intro a hkeep hfresh
  by_contra hne
  rcases hcell a hne with ⟨ivl, hivl, _, hhit⟩ | ⟨gs, hgs, _, hhit⟩ | ⟨o, ho, _, hhit⟩ | ⟨_, hfg⟩ | ⟨_, hhf⟩
  · exact hkeep ivl (List.mem_append_left _ (List.mem_append_right _ hivl)) hhit
  · have hfo_gs := bufferRegion_in_fixedObjects_mpt s gs (hB_ok gs hgs).1
    have hwo_gs : bufferRegion s gs ∈ worldOwned s S Nd := by
      unfold worldOwned; exact List.mem_append_left _ (List.mem_append_right _ hfo_gs)
    exact hkeep _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hwo_gs))) hhit
  · exact hkeep o (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ho))) hhit
  · exact hkeep (freeGap s) (List.mem_append_right _ List.mem_cons_self) hfg
  · exact hfresh hhf

end MptObjStepHelper

theorem heapSafe_decCall_alloc_progress {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (nExp : ExpHOL 64)
    (cont : ProgHOL 64)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hn_pos : ∀ n : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
        some (.val (.word n)) → 0 < n.toNat)
    (hcont_mono : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode → ArenaReady mid →
      globN mid "heap_ptr" ≤ globN (evaluateHOLFiniteState mid cont).2 "heap_ptr")
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).1) :
    globN s "heap_ptr" <
      globN (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).2 "heap_ptr" := by
  obtain ⟨hp, n, q, mid, hnv, hhp_nat, _, _, hp_le_q, _, _, hmid_hp, _, _, _, heff, _, _, heval⟩ :=
    R16Shards.WkBlockTxEnc.eval_decCall_alloc_resumes s lname nExp cont [] ["heap_ptr"]
      hcode hAR (by simp) hnt hres
  have hpos := hn_pos n hnv
  have hlt : globN s "heap_ptr" < globN mid "heap_ptr" := by
    rw [← hhp_nat, hmid_hp]
    omega
  have hmid_code : mid.code = originalRuntimeCode := heff.arena.1.code
  have hle := hcont_mono mid hmid_code heff.arena
  have hpost_hp :
      globN (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).2 "heap_ptr" =
      globN (evaluateHOLFiniteState mid cont).2 "heap_ptr" := by
    rw [heval]
    rfl
  rw [hpost_hp]
  exact Nat.lt_of_lt_of_le hlt hle

theorem rlp_allocation_size_positive (payload hl : BitVec 64)
    (hp : payload.toNat < 2 ^ 60) (hh : 1 ≤ hl.toNat ∧ hl.toNat ≤ 9) :
    0 < (hl + payload).toNat := by
  have hadd : (hl + payload).toNat = hl.toNat + payload.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  rw [hadd]
  omega

theorem heapSafe_decCall_alloc_rlp_progress {F : Type}
    (s : PanSemStateFiniteExact 64 F) (cont : ProgHOL 64)
    (payload hl : BitVec 64)
    (hpayload : s.locals.lookup (ofString "payload") = some (.val (.word payload)))
    (hhl : s.locals.lookup (ofString "hl") = some (.val (.word hl)))
    (hp : payload.toNat < 2 ^ 60) (hh : 1 ≤ hl.toNat ∧ hl.toNat ≤ 9)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hcont_mono : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode → ArenaReady mid →
      globN mid "heap_ptr" ≤ globN (evaluateHOLFiniteState mid cont).2 "heap_ptr")
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "buf") .one (ofString "alloc")
        [.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]] cont)).1 ≠
          some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "buf") .one (ofString "alloc")
        [.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]] cont)).1) :
    globN s "heap_ptr" < globN (evaluateHOLFiniteState s
      (.decCall (ofString "buf") .one (ofString "alloc")
        [.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]] cont)).2
          "heap_ptr" := by
  apply heapSafe_decCall_alloc_progress s "buf" _ cont hcode hAR ?_ hcont_mono hnt hres
  intro n hn
  have heval : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]) =
        some (.val (.word (hl + payload))) := by
    simp [evalHOLExact, evalListHOLExact, hhl, hpayload, valueIsWord, valueWord,
      wordOpHOL, wordOp]
  rw [heval] at hn
  cases hn
  exact rlp_allocation_size_positive payload hl hp hh

theorem heapSafe_rlp_header_alloc_progress {F : Type}
    (s : PanSemStateFiniteExact 64 F) (cont : ProgHOL 64) (payload : BitVec 64)
    (hpayload : s.locals.lookup (ofString "payload") = some (.val (.word payload)))
    (hp : payload.toNat < 2 ^ 60)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hcont_mono : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode → ArenaReady mid →
      globN mid "heap_ptr" ≤ globN (evaluateHOLFiniteState mid cont).2 "heap_ptr")
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
        [.var .local (ofString "payload")]
        (.decCall (ofString "buf") .one (ofString "alloc")
          [.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]] cont))).1 ≠
            some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
        [.var .local (ofString "payload")]
        (.decCall (ofString "buf") .one (ofString "alloc")
          [.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]] cont))).1) :
    globN s "heap_ptr" < globN (evaluateHOLFiniteState s
      (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
        [.var .local (ofString "payload")]
        (.decCall (ofString "buf") .one (ofString "alloc")
          [.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]] cont))).2
            "heap_ptr" := by
  obtain ⟨mid, _, hhl_lo, hhl_hi, hg, _, hloc, heff, hnt_mid, heval⟩ :=
    R16Shards.WkBlockTxEnc.eval_decCall_rlp_list_header_len s "hl"
      (.var .local (ofString "payload")) payload _ [] [] hcode hAR
      (by simp [evalHOLExact, hpayload]) hnt
  have hp_mid : mid.locals.lookup (ofString "payload") = some (.val (.word payload)) := by
    rw [hloc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hpayload,
      show ofString "hl" ≠ ofString "payload" by decide]
  have hhl_mid : mid.locals.lookup (ofString "hl") =
      some (.val (.word (BitVec.ofNat 64
        (R16Shards.WkBlockTxEnc.rlpHeaderLenPure payload.toNat)))) := by
    rw [hloc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hres_mid : Resumes (evaluateHOLFiniteState mid
      (.decCall (ofString "buf") .one (ofString "alloc")
        [.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]] cont)).1 := by
    rw [heval] at hres
    exact hres
  have hprogress := heapSafe_decCall_alloc_rlp_progress mid cont payload _ hp_mid hhl_mid
    hp ⟨hhl_lo, hhl_hi⟩ heff.arena.1.code heff.arena hcont_mono hnt_mid hres_mid
  rw [heval]
  simpa only [globN, hg] using hprogress

private theorem encFrame_call_keccak256 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pExp nExp outExp : ExpHOL 64)
    (pw nw outw : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp = some (.val (.word pw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp = some (.val (.word nw)))
    (hout : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) outExp = some (.val (.word outw)))
    (hout_in : (∃ ivl ∈ Rl, ivl.1 ≤ outw.toNat ∧ outw.toNat + 32 ≤ ivl.1 + ivl.2) ∨
      (globN s "heap_ptr" ≤ outw.toNat ∧ outw.toNat + 32 ≤ heapLimit))
    (hpad_in : globN s "keccak_pad" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s "keccak_pad" ∧ globN s "keccak_pad" + 136 ≤ ivl.1 + ivl.2)
    (hst_in : globN s "keccak_st" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s "keccak_st" ∧ globN s "keccak_st" + 200 ≤ ivl.1 + ivl.2)
    (hnone : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "keccak256") [pExp, nExp, outExp])).1 = none) :
    let post := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "keccak256") [pExp, nExp, outExp])).2
    EncFrame s post Rl ∧ post.locals = s.locals ∧ post.globals = s.globals := by
  let heap := (globN s "heap_ptr", heapLimit - globN s "heap_ptr")
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [pExp, nExp, outExp] = some [.val (.word pw), .val (.word nw), .val (.word outw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hp, hn, hout]
  have heff := R13Shards.Keccak256.call0_byteEff R13Shards.Keccak256.funByteEff_keccak256
    s [pExp, nExp, outExp] (heap :: Rl) hcode hAR.1
    (fun vs hvs i hi hipos => by
      rw [ha] at hvs; injection hvs with hvs; subst hvs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · rw [R13Shards.Keccak256.globBufIvl_eq_bufferRegion] at hipos ⊢
        by_cases h0 : globN s "keccak_st" = 0
        · simp [bufferRegion, h0] at hipos
        · simp only [bufferRegion, h0, ↓reduceIte]
          obtain ⟨r, hr, h1, h2⟩ := hst_in h0
          exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2⟩
      · rw [R13Shards.Keccak256.globBufIvl_eq_bufferRegion] at hipos ⊢
        by_cases h0 : globN s "keccak_pad" = 0
        · simp [bufferRegion, h0] at hipos
        · simp only [bufferRegion, h0, ↓reduceIte]
          obtain ⟨r, hr, h1, h2⟩ := hpad_in h0
          exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2⟩
      · simp only [R13Shards.Keccak256.valWordNat, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.getD_some]
        rcases hout_in with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2⟩
        · exact ⟨heap, List.mem_cons_self, h1, by dsimp [heap]; have := hAR.2.2.1; omega⟩)
    (by rw [hnone]; simp) (Or.inl hnone)
  have henc : EncFrame s (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "keccak256") [pExp, nExp, outExp])).2 Rl := by
    have h1 : EncFrame s (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "keccak256") [pExp, nExp, outExp])).2 (heap :: Rl) := by
      have hG' : GuestInv (evaluateHOLFiniteState s
          (.call (some (none, none)) (ofString "keccak256") [pExp, nExp, outExp])).2 :=
        guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAR.1
      have hA' : ArenaReady (evaluateHOLFiniteState s
          (.call (some (none, none)) (ofString "keccak256") [pExp, nExp, outExp])).2 :=
        ⟨hG', by simpa only [ArenaOK, globN, GlobalWord, GlobalsWord, heff.globals] using hAR.2⟩
      refine ⟨hA', by simp [globN, heff.globals], fun _ _ => by rw [heff.globals], heff.be, ?_, ?_⟩
      · intro a ha _
        by_contra hne
        obtain ⟨i, hi, hipos, hc⟩ := heff.cell_frame a hne
        exact ha i hi ⟨hipos, hc⟩
      · intro b hb hno _
        by_contra hne
        obtain ⟨i, hi, hin⟩ := heff.byte_frame b hb hne
        exact hno i hi hin
    apply h1.mono
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact Or.inr ⟨le_rfl, by dsimp [heap]; have := hAR.2.2.1; omega⟩
    · exact Or.inl ⟨i, hi, le_rfl, le_rfl⟩
  have hloc : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "keccak256") [pExp, nExp, outExp])).2.locals = s.locals := by
    have hkc := R16Shards.WkBlockTxEnc.eval_call_keccak256_heap s pExp nExp outExp pw nw outw (heap :: Rl) []
      hcode hAR hp hn hout
      (by rcases hout_in with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2⟩
          · exact ⟨heap, List.mem_cons_self, h1, by dsimp [heap]; have := hAR.2.2.1; omega⟩)
      (fun h0 => by obtain ⟨r, hr, h1, h2⟩ := hpad_in h0; exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2⟩)
      (fun h0 => by obtain ⟨r, hr, h1, h2⟩ := hst_in h0; exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2⟩)
      (by rw [hnone]; simp) (Or.inl hnone)
    exact (hkc.2 hnone).1
  exact ⟨henc, hloc, heff.globals⟩

private theorem encFrame_call_memcpy {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp = some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp = some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp = some (.val (.word n0)))
    (hsub : 0 < n0.toNat → (∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2) ∨
      (globN s "heap_ptr" ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapLimit))
    (hnone : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 = none) :
    let post := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).2
    EncFrame s post Rl ∧ post.locals = s.locals ∧ post.globals = s.globals := by
  let heap := (globN s "heap_ptr", heapLimit - globN s "heap_ptr")
  have hmc := M11.eval_call_memcpy_bre s dstExp srcExp nExp dst0 src0 n0 (heap :: Rl)
    hcode hAR.1.memaddrs hdst hsrc hn
    (fun hpos => by
      rcases hsub hpos with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2⟩
      · exact ⟨heap, List.mem_cons_self, h1, by dsimp [heap]; have := hAR.2.2.1; omega⟩)
    (by rw [hnone]; simp)
  obtain ⟨heff, hloc⟩ := hmc.1 hnone
  refine ⟨?_, hloc, heff.globals⟩
  apply (EncFrame.of_m11_bre hAR heff).mono
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · exact Or.inr ⟨le_rfl, by dsimp [heap]; have := hAR.2.2.1; omega⟩
  · exact Or.inl ⟨i, hi, le_rfl, le_rfl⟩

private theorem encFrame_store_node_cache {F : Type}
    (s : PanSemStateFiniteExact 64 F) (nodeExp valExp : ExpHOL 64)
    (nw : BitVec 64) (off : Nat) (Nd : List Nat) (Rl_extra : List Ivl)
    (hAR : ArenaReady s)
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp = some (.val (.word nw)))
    (hn_in : nw.toNat ∈ Nd)
    (hn_sz : nw.toNat + 32 ≤ heapLimit)
    (hoff : off = 8 ∨ off = 16 ∨ off = 24)
    (hval : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w)) :
    EncFrame s (evaluateHOLFiniteState s (.store (.op .add [nodeExp, .const (BitVec.ofNat 64 off)]) valExp)).2
      (nodeCacheIvls Nd ++ Rl_extra) := by
  apply EncFrame.of_store_word hAR hval
  intro addr haddr _
  have hlt64 : heapLimit < 2 ^ 64 := by decide
  have hoff_bv : (BitVec.ofNat 64 off).toNat = off := by
    rcases hoff with rfl | rfl | rfl <;> decide
  have hadd_nat : (nw + BitVec.ofNat 64 off).toNat = nw.toNat + off := by
    rw [BitVec.toNat_add_of_lt (by rw [hoff_bv]; rcases hoff with rfl | rfl | rfl <;> omega), hoff_bv]
  simp [evalHOLExact, evalListHOLExact, hn, valueIsWord, valueWord, wordOpHOL, wordOp] at haddr
  subst haddr
  left
  refine ⟨(nw.toNat + 8, 24), List.mem_append_left _ (List.mem_map.2 ⟨nw.toNat, hn_in, rfl⟩), ?_, ?_⟩
  · rw [hadd_nat]; rcases hoff with rfl | rfl | rfl <;> omega
  · rw [hadd_nat]; rcases hoff with rfl | rfl | rfl <;> omega

private theorem encFrame_store_node_hash_cache {F : Type}
    (s : PanSemStateFiniteExact 64 F) (nodeExp valExp : ExpHOL 64)
    (nw : BitVec 64) (Nd : List Nat) (Rl_extra : List Ivl)
    (hAR : ArenaReady s)
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp = some (.val (.word nw)))
    (hn_in : nw.toNat ∈ Nd)
    (hn_sz : nw.toNat + 32 ≤ heapLimit)
    (hval : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w)) :
    EncFrame s (evaluateHOLFiniteState s (.store (.op .add [nodeExp, .const 24]) valExp)).2
      (nodeHashCacheIvls Nd ++ Rl_extra) := by
  apply EncFrame.of_store_word hAR hval
  intro addr haddr _
  have hlt64 : heapLimit < 2 ^ 64 := by decide
  have h24_bv : (24#64).toNat = 24 := by decide
  have hadd_nat : (nw + 24#64).toNat = nw.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by rw [h24_bv]; omega), h24_bv]
  simp [evalHOLExact, evalListHOLExact, hn, valueIsWord, valueWord, wordOpHOL, wordOp] at haddr
  subst haddr
  left
  refine ⟨(nw.toNat + 24, 8), List.mem_append_left _ (List.mem_map.2 ⟨nw.toNat, hn_in, rfl⟩), ?_, ?_⟩
  · rw [hadd_nat]
  · rw [hadd_nat]

private theorem eval_node_hash_cached_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (nw : BitVec 64) (Nd : List Nat) (Rl_extra : List Ivl) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s) (hNh : RelaxedNodeHeap s Nd)
    (hn : s.locals.lookup (ofString "node") = some (.val (.word nw)))
    (hn_in : nw.toNat ∈ Nd)
    (hkeccak_sub : ∀ k ∈ keccakScratchIvls s, k.2 > 0 →
      ∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ k.1 ∧ k.1 + k.2 ≤ r.1 + r.2)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_hash_cached)).1 = some (.returned rv)) :
    (∃ hw : BitVec 64, rv = .val (.word hw)) ∧
    EncFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_hash_cached)).2
      (nodeHashCacheIvls Nd ++ Rl_extra) := by
  have hn_al : nw.toNat % 8 = 0 := (hNh.1 nw.toNat hn_in).2.2.2.1.1
  have hn_bounds := relaxedNodeIvl_lt_heap_ptr hAR.2 hNh hn_in
  have hn_ge : sourceBase ≤ nw.toNat := hn_bounds.1
  have hn_sz : nw.toNat + 32 ≤ heapLimit := by
    have hsz : 32 ≤ (nodeIvl s nw.toNat).2 := by dsimp [nodeIvl, nodeSize]; split_ifs <;> omega
    have hhp := hAR.2.2.1
    omega
  have hbody : sourceFnBody Guest.Software.guestFn_node_hash_cached =
      .dec (ofString "cached") .one (.load .one (.op .add [.var .local (ofString "node"), .const 24]))
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "cached")) (.const 0))
            (.return (.var .local (ofString "cached")))
            .skip)
          (.seq
            (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "node"), .const 8])) (.const 0))
              (.call (some (none, none)) (ofString "mpt_fail") [.const 13])
              .skip)
            (.decCall (ofString "h") .one (ofString "alloc") [.const 32]
              (.seq
                (.call (some (none, none)) (ofString "keccak256")
                  [.load .one (.op .add [.var .local (ofString "node"), .const 8]),
                   .load .one (.op .add [.var .local (ofString "node"), .const 16]),
                   .var .local (ofString "h")])
                (.seq
                  (.store (.op .add [.var .local (ofString "node"), .const 24]) (.var .local (ofString "h")))
                  (.return (.var .local (ofString "h")))))))) := rfl
  rcases hout : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_hash_cached) with ⟨r0, post⟩
  rw [hout] at hret
  dsimp only at hret
  subst hret
  rw [hbody, evaluateHOLFiniteState_dec_total] at hout
  dsimp only at hout
  rcases hld : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "node"), .const 24])) with _ | cv
  · rw [hld] at hout; cases hout
  · obtain ⟨cachedw, rfl⟩ := R10Shards.P26_P28.eval_load_one_word s _ cv hld
    have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word cachedw) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [hld] at hout; dsimp only at hout; rw [if_pos hsh1] at hout
    set e1 := setVarHOLFinite (ofString "cached") (.val (.word cachedw)) s
    have he1_enc : EncFrame s e1 (nodeHashCacheIvls Nd ++ Rl_extra) :=
      (EncFrame.refl s hAR _).with_locals_clock _ _
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hout
    have hcmp1 : @evalHOLExact 64 F _ e1.toExact (fun a => Classical.propDecidable (e1.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "cached")) (.const 0)) =
        some (.val (.word (if cachedw ≠ 0 then 1 else 0))) := by
      simp [e1, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp1] at hout; dsimp only at hout
    by_cases hcz_c : cachedw = 0
    · subst hcz_c
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, evaluateHOLFiniteState_skip] at hout
      rw [evaluateHOLFiniteState_seq_line780] at hout
      rcases hmf_step : evaluateHOLFiniteState e1
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "node"), .const 8])) (.const 0))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) with ⟨rmf, e2⟩
      simp only [hmf_step] at hout
      have hmf := eval_call_mpt_fail_no_none_no_ret e1 13 hc
      cases rmf with
      | some rmf' =>
        have hr_eq : rmf' = .returned rv := by
          exact Option.some.inj (congrArg Prod.fst hout)
        subst hr_eq
        rw [evaluateHOLFiniteState_ite] at hmf_step
        split at hmf_step
        · split at hmf_step
          · rw [evaluateHOLFiniteState_skip] at hmf_step; cases hmf_step
          · exact False.elim (hmf.2 rv (congrArg Prod.fst hmf_step))
        · cases hmf_step
      | none =>
        have he2 : e2 = e1 := by
          rw [evaluateHOLFiniteState_ite] at hmf_step
          split at hmf_step
          · split at hmf_step
            · rw [evaluateHOLFiniteState_skip] at hmf_step; exact (Prod.mk.inj hmf_step).2.symm
            · exact False.elim (hmf.1 (congrArg Prod.fst hmf_step))
          · cases hmf_step
        subst he2
        dsimp only at hout
        have he1_AR : ArenaReady e1 := he1_enc.arena
        have he1_n : e1.locals.lookup (ofString "node") = some (.val (.word nw)) := by
          simp [e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
            show ofString "cached" ≠ ofString "node" by decide]
        let kcTail : ProgHOL 64 :=
          .seq
            (.call (some (none, none)) (ofString "keccak256")
              [.load .one (.op .add [.var .local (ofString "node"), .const 8]),
               .load .one (.op .add [.var .local (ofString "node"), .const 16]),
               .var .local (ofString "h")])
            (.seq
              (.store (.op .add [.var .local (ofString "node"), .const 24]) (.var .local (ofString "h")))
              (.return (.var .local (ofString "h"))))
        have hout_fst := congrArg Prod.fst hout
        have hout_snd := congrArg Prod.snd hout
        dsimp only at hout_fst hout_snd
        have hnt_alloc : (evaluateHOLFiniteState e1 (.decCall (ofString "h") .one (ofString "alloc") [.const 32] kcTail)).1 ≠ some .timeOut := by
          rw [hout_fst]; simp
        have hres_alloc : Resumes (evaluateHOLFiniteState e1 (.decCall (ofString "h") .one (ofString "alloc") [.const 32] kcTail)).1 := by
          rw [hout_fst]; exact Or.inl ⟨rv, rfl⟩
        obtain ⟨hp0, n32, q32, midA, h32_ev, hhp0_nat, _, _, hhp_le_q, hq_le_lim, _, hmidA_hp, hmidA_g, hmidA_m, hmidA_loc, heffA, hnt_k, _, hevalA⟩ :=
          R16Shards.WkBlockTxEnc.eval_decCall_alloc_resumes e1 "h" (.const 32) kcTail
            (nodeHashCacheIvls Nd ++ Rl_extra) ["heap_ptr"] hc he1_AR (by simp) hnt_alloc hres_alloc
        simp [evalHOLExact] at h32_ev; subst h32_ev
        have hmidA_h : midA.locals.lookup (ofString "h") = some (.val (.word hp0)) := by
          rw [hmidA_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hmidA_n : midA.locals.lookup (ofString "node") = some (.val (.word nw)) := by
          rw [hmidA_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, he1_n,
            show ofString "h" ≠ ofString "node" by decide]
        have heff_s_midA : EncFrame s midA (nodeHashCacheIvls Nd ++ Rl_extra) := by
          refine he1_enc.trans ⟨heffA.arena, heffA.hp_le, ?_, heffA.be,
            fun a _ _ => by rw [hmidA_m], fun b _ _ _ => by unfold memB; rw [hmidA_m, heffA.be]⟩
          intro k hk
          rw [hmidA_g]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        change (evaluateHOLFiniteState e1 (.decCall (ofString "h") .one (ofString "alloc") [.const 32] kcTail)).1 = some (.returned rv) at hout_fst
        change { (evaluateHOLFiniteState e1 (.decCall (ofString "h") .one (ofString "alloc") [.const 32] kcTail)).2 with
            locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState e1 (.decCall (ofString "h") .one (ofString "alloc") [.const 32] kcTail)).2.locals
              (ofString "cached", s.locals.lookup (ofString "cached")) } = post at hout_snd
        rw [hevalA] at hout_fst hout_snd
        dsimp only [kcTail] at hout_fst hout_snd hnt_k
        rw [evaluateHOLFiniteState_seq_line780] at hout_fst hout_snd hnt_k
        rcases hkc : evaluateHOLFiniteState midA
            (.call (some (none, none)) (ofString "keccak256")
              [.load .one (.op .add [.var .local (ofString "node"), .const 8]),
               .load .one (.op .add [.var .local (ofString "node"), .const 16]),
               .var .local (ofString "h")]) with ⟨rkc, skc⟩
        simp only [hkc] at hout_fst hout_snd hnt_k
        cases rkc with
        | some rkc' =>
          dsimp only at hout_fst
          obtain ⟨rfl⟩ := Option.some.inj hout_fst
          exfalso
          have hcall := hkc
          rw [evaluateHOLFiniteState_call] at hcall
          repeat' split at hcall
          all_goals simp_all
        | none =>
          dsimp only at hout_fst hout_snd
          have hhe : heapLimit ≤ heapEnd := by decide
          have hlt64 : heapLimit < 2 ^ 64 := by decide
          have hsb : sourceBase = 2701131776 := M11.sourceBase_val
          have hhe_val : heapEnd = 2701131776 + 8 * 3888119741 := M11.heapEnd_val
          have hlim_val : heapLimit ≤ 2701131776 + 8 * 3888119741 := by rw [← hhe_val]; exact hhe
          have h8_bv : (8#64).toNat = 8 := by decide
          have h16_bv : (16#64).toNat = 16 := by decide
          have hadd8 : (nw + 8#64).toNat = nw.toNat + 8 := by
            rw [BitVec.toNat_add_of_lt (by rw [h8_bv]; omega), h8_bv]
          have hadd16 : (nw + 16#64).toNat = nw.toNat + 16 := by
            rw [BitVec.toNat_add_of_lt (by rw [h16_bv]; omega), h16_bv]
          have hdom8 : midA.memaddrs (nw + 8#64) := by
            rw [heffA.arena.1.memaddrs]
            exact (M11.ordinaryDomain_iff (nw + 8#64)).2 ⟨by rw [hadd8]; omega, by rw [hadd8]; omega, by rw [hadd8]; omega⟩
          have hdom16 : midA.memaddrs (nw + 16#64) := by
            rw [heffA.arena.1.memaddrs]
            exact (M11.ordinaryDomain_iff (nw + 16#64)).2 ⟨by rw [hadd16]; omega, by rw [hadd16]; omega, by rw [hadd16]; omega⟩
          rcases hm8 : midA.memory (nw + 8#64) with ⟨w8⟩
          rcases hm16 : midA.memory (nw + 16#64) with ⟨w16⟩
          have hev8 : @evalHOLExact 64 F _ midA.toExact (fun a => Classical.propDecidable (midA.memaddrs a))
              (.load .one (.op .add [.var .local (ofString "node"), .const 8])) = some (.val (.word w8)) := by
            simp [evalHOLExact, evalListHOLExact, hmidA_n, valueIsWord, valueWord, wordOpHOL, wordOp,
              memLoadHOLExact]
            exact ⟨hdom8, hm8⟩
          have hev16 : @evalHOLExact 64 F _ midA.toExact (fun a => Classical.propDecidable (midA.memaddrs a))
              (.load .one (.op .add [.var .local (ofString "node"), .const 16])) = some (.val (.word w16)) := by
            simp [evalHOLExact, evalListHOLExact, hmidA_n, valueIsWord, valueWord, wordOpHOL, wordOp,
              memLoadHOLExact]
            exact ⟨hdom16, hm16⟩
          have hev_h : @evalHOLExact 64 F _ midA.toExact (fun a => Classical.propDecidable (midA.memaddrs a))
              (.var .local (ofString "h")) = some (.val (.word hp0)) := by
            simp [evalHOLExact, hmidA_h]
          let allocIvl : Ivl := (hp0.toNat, 32)
          have hpad_eq : globN midA "keccak_pad" = globN s "keccak_pad" := by
            have hk : midA.globals.lookup (ofString "keccak_pad") = s.globals.lookup (ofString "keccak_pad") :=
              heff_s_midA.nonHeap _ (by decide)
            simp only [globN, hk]
          have hst_eq : globN midA "keccak_st" = globN s "keccak_st" := by
            have hk : midA.globals.lookup (ofString "keccak_st") = s.globals.lookup (ofString "keccak_st") :=
              heff_s_midA.nonHeap _ (by decide)
            simp only [globN, hk]
          obtain ⟨heff_kc_raw, hskc_loc, hskc_glob⟩ := encFrame_call_keccak256 midA
            (.load .one (.op .add [.var .local (ofString "node"), .const 8]))
            (.load .one (.op .add [.var .local (ofString "node"), .const 16]))
            (.var .local (ofString "h"))
            w8 w16 hp0 (allocIvl :: (nodeHashCacheIvls Nd ++ Rl_extra))
            heffA.arena.1.code heffA.arena hev8 hev16 hev_h
            (Or.inl ⟨allocIvl, List.mem_cons_self, le_rfl, le_rfl⟩)
            (fun h0 => by
              rw [hpad_eq] at h0 ⊢
              obtain ⟨r, hr, h1, h2⟩ := hkeccak_sub (bufferRegion s ("keccak_pad", 136))
                (by simp [keccakScratchIvls]) (by simp [bufferRegion, h0])
              simp only [bufferRegion, h0, ↓reduceIte] at h1 h2
              exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2⟩)
            (fun h0 => by
              rw [hst_eq] at h0 ⊢
              obtain ⟨r, hr, h1, h2⟩ := hkeccak_sub (bufferRegion s ("keccak_st", 200))
                (by simp [keccakScratchIvls]) (by simp [bufferRegion, h0])
              simp only [bufferRegion, h0, ↓reduceIte] at h1 h2
              exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2⟩)
            (congrArg Prod.fst hkc)
          have hskc_eq : (evaluateHOLFiniteState midA
              (.call (some (none, none)) (ofString "keccak256")
                [.load .one (.op .add [.var .local (ofString "node"), .const 8]),
                 .load .one (.op .add [.var .local (ofString "node"), .const 16]),
                 .var .local (ofString "h")])).2 = skc := congrArg Prod.snd hkc
          rw [hskc_eq] at heff_kc_raw hskc_loc hskc_glob
          have heff_s_skc : EncFrame s skc (nodeHashCacheIvls Nd ++ Rl_extra) := by
            have h1 : EncFrame s midA (allocIvl :: (nodeHashCacheIvls Nd ++ Rl_extra)) :=
              heff_s_midA.mono (fun i hi => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩)
            have hfit32 : hp0.toNat + 32 ≤ heapLimit := by
              change hp0.toNat + (32#64).toNat ≤ q32.toNat at hhp_le_q
              have h32 : (32#64).toNat = 32 := by decide
              omega
            apply (h1.trans heff_kc_raw).mono
            intro i hi
            rcases List.mem_cons.mp hi with rfl | hi
            · exact Or.inr ⟨by dsimp [allocIvl]; change globN e1 "heap_ptr" ≤ hp0.toNat; omega,
                by dsimp [allocIvl]; exact hfit32⟩
            · exact Or.inl ⟨i, hi, le_rfl, le_rfl⟩
          rw [evaluateHOLFiniteState_seq_line780] at hout_fst hout_snd
          rcases hst_step : evaluateHOLFiniteState skc
              (.store (.op .add [.var .local (ofString "node"), .const 24]) (.var .local (ofString "h"))) with ⟨rst, sst⟩
          simp only [hst_step] at hout_fst hout_snd
          cases rst with
          | some rst' =>
            dsimp only at hout_fst
            rw [evaluateHOLFiniteState_store] at hst_step
            repeat' split at hst_step
            all_goals (try (obtain ⟨h1, _⟩ := Prod.mk.inj hst_step; rw [← h1] at hout_fst; exact absurd hout_fst (by simp)))
          | none =>
            dsimp only at hout_fst hout_snd
            have hskc_n : skc.locals.lookup (ofString "node") = some (.val (.word nw)) := by rw [hskc_loc]; exact hmidA_n
            have hskc_h : skc.locals.lookup (ofString "h") = some (.val (.word hp0)) := by rw [hskc_loc]; exact hmidA_h
            have heff_st : EncFrame skc sst (nodeHashCacheIvls Nd ++ Rl_extra) := by
              have hst_eq_sst : (evaluateHOLFiniteState skc
                (.store (.op .add [.var .local (ofString "node"), .const 24]) (.var .local (ofString "h")))).2 = sst :=
                congrArg Prod.snd hst_step
              rw [← hst_eq_sst]
              exact encFrame_store_node_hash_cache skc (.var .local (ofString "node")) (.var .local (ofString "h"))
                nw Nd Rl_extra heff_s_skc.arena (by simp [evalHOLExact, hskc_n]) hn_in hn_sz
                (fun v hv => by simp [evalHOLExact, hskc_h] at hv; exact ⟨hp0, hv.symm⟩)
            have hsst_loc : sst.locals = skc.locals := by
              rw [evaluateHOLFiniteState_store] at hst_step
              repeat' split at hst_step
              all_goals (obtain ⟨h1, h2⟩ := Prod.mk.inj hst_step; cases h1; try exact (congrArg PanSemStateFiniteExact.locals h2).symm)
            have hsst_h : @evalHOLExact 64 F _ sst.toExact (fun a => Classical.propDecidable (sst.memaddrs a))
                (.var .local (ofString "h")) = some (.val (.word hp0)) := by
              simp [evalHOLExact, hsst_loc, hskc_h]
            rw [evaluateHOLFiniteState_return] at hout_fst hout_snd
            simp only [hsst_h, shapeOfHOLExact, sizeOfShapeWithContextHOL, ↓reduceIte] at hout_fst hout_snd
            have hrv : PanSemResultExact.returned (.val (.word hp0)) = PanSemResultExact.returned rv :=
              Option.some.inj hout_fst
            obtain ⟨rfl⟩ := PanSemResultExact.returned.inj hrv
            rw [← hout_snd]
            exact ⟨⟨hp0, rfl⟩, ((heff_s_skc.trans heff_st).with_locals_clock _ _).with_locals_clock _ _⟩
    · simp only [ne_eq, hcz_c, not_false_eq_true, ↓reduceIte, evaluateHOLFiniteState_return] at hout
      have he1_c : @evalHOLExact 64 F _ e1.toExact (fun a => Classical.propDecidable (e1.memaddrs a))
          (.var .local (ofString "cached")) = some (.val (.word cachedw)) := by
        simp [e1, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hout_f := congrArg Prod.fst hout
      have hout_s := congrArg Prod.snd hout
      simp only [he1_c, shapeOfHOLExact, sizeOfShapeWithContextHOL, ↓reduceIte] at hout_f hout_s
      have hrv : PanSemResultExact.returned (.val (.word cachedw)) = PanSemResultExact.returned rv :=
        Option.some.inj hout_f
      obtain ⟨rfl⟩ := PanSemResultExact.returned.inj hrv
      rw [← hout_s]
      exact ⟨⟨cachedw, rfl⟩, (he1_enc.with_locals_clock _ _).with_locals_clock _ _⟩

private theorem eval_decCall_node_hash_cached {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (nodeExp : ExpHOL 64)
    (nw : BitVec 64) (Nd : List Nat) (Rl_extra : List Ivl) (cont : ProgHOL 64) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s) (hNh : RelaxedNodeHeap s Nd)
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
      some (.val (.word nw)))
    (hn_in : nw.toNat ∈ Nd)
    (hkeccak_sub : ∀ k ∈ keccakScratchIvls s, k.2 > 0 →
      ∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ k.1 ∧ k.1 + k.2 ≤ r.1 + r.2)
    (hret : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "node_hash_cached") [nodeExp] cont)).1 = some (.returned rv)) :
    ∃ (hw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      mid.locals = s.locals.update (ofString lname, .val (.word hw)) ∧
      EncFrame s mid (nodeHashCacheIvls Nd ++ Rl_extra) ∧
      (evaluateHOLFiniteState mid cont).1 = some (.returned rv) ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "node_hash_cached") [nodeExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString lname, s.locals.lookup (ofString lname)) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [nodeExp] = some [.val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hn]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "node_hash_cached") (ofString "node")
    (sourceFnBody Guest.Software.guestFn_node_hash_cached) nw (by rw [hc]; exact lookup_node_hash_cached)
  simp only [hargs, hlk] at hret ⊢
  by_cases hclk0 : s.clock = 0
  · simp [hclk0] at hret
  · simp only [hclk0, ↓reduceIte] at hret ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "node", ValueHOL.val (.word nw))
    set entry := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady entry := localsFree_arenaReady s cmap (s.clock - 1) hAR
    have hent_Nh : RelaxedNodeHeap entry Nd :=
      relaxedNodeHeap_congr_unhit hAR.1 hent_AR.1 rfl ⟨le_rfl, le_rfl⟩ hNh (fun _ _ _ _ _ _ => rfl)
    have hent_n : entry.locals.lookup (ofString "node") = some (.val (.word nw)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hclk_le := evaluateHOLFiniteState_clock_le entry (sourceFnBody Guest.Software.guestFn_node_hash_cached)
    rcases hcal : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_node_hash_cached) with ⟨rc, sc⟩
    simp only [hcal] at hret hclk_le ⊢
    cases rc with
    | none => simp [fixClockHOLFinite] at hret
    | some rc' =>
      cases rc' with
      | returned vc =>
        obtain ⟨⟨hw, rfl⟩, henc_c⟩ := eval_node_hash_cached_returned entry nw Nd Rl_extra vc
          hc hent_AR hent_Nh hent_n hn_in hkeccak_sub (by rw [hcal])
        rw [hcal] at henc_c
        dsimp only [fixClockHOLFinite] at hret ⊢
        have hclk_if : (if entry.clock < sc.clock then entry.clock else sc.clock) = sc.clock :=
          if_neg (by omega)
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word hw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte, hclk_if] at hret ⊢
        let mid : PanSemStateFiniteExact 64 F :=
          setVarHOLFinite (ofString lname) (.val (.word hw)) { sc with locals := s.locals }
        have hhenc0 : EncFrame s entry (nodeHashCacheIvls Nd ++ Rl_extra) :=
          (EncFrame.refl s hAR _).with_locals_clock _ _
        have hhenc_mid : EncFrame s mid (nodeHashCacheIvls Nd ++ Rl_extra) :=
          (hhenc0.trans henc_c).with_locals_clock _ _
        refine ⟨hw, mid, rfl, hhenc_mid, hret, rfl⟩
      | _ => simp [fixClockHOLFinite] at hret

private theorem eval_node_write_ref_kind0 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (cw dst0 : BitVec 64) (Nd : List Nat) (Rl_extra : List Ivl) (rv : ValueHOL 64)
    (post : PanSemStateFiniteExact 64 F)
    (hAR : ArenaReady s)
    (hchild : s.locals.lookup (ofString "child") = some (.val (.word cw)))
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hc_al : cw.toNat % 8 = 0)
    (hc_ge : sourceBase ≤ cw.toNat)
    (hc_sz : cw.toNat + 32 ≤ heapLimit)
    (hdst_hi : dst0.toNat + 33 ≤ heapLimit)
    (hdst_sub : (∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ dst0.toNat ∧ dst0.toNat + 33 ≤ r.1 + r.2) ∨
      (globN s "heap_ptr" ≤ dst0.toNat ∧ dst0.toNat + 33 ≤ heapLimit))
    (hout : evaluateHOLFiniteState s
      (.seq
        (.storeByte (.var .local (ofString "dst")) (.const 160))
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "dst"), .const 1],
             .load .one (.op .add [.var .local (ofString "child"), .const 24]),
             .const 32])
          (.return (.const 33)))) = (some (.returned rv), post)) :
    ∃ w : BitVec 64,
      rv = .val (.word w) ∧ w.toNat ≤ 33 ∧
      EncFrame s post (nodeHashCacheIvls Nd ++ Rl_extra) := by
  have hlt64 : heapLimit < 2 ^ 64 := by decide
  have hdst1_nat : (dst0 + 1#64).toNat = dst0.toNat + 1 := by
    have h1bv : (1#64).toNat = 1 := by decide
    rw [BitVec.toNat_add_of_lt (by omega), h1bv]
  rw [evaluateHOLFiniteState_seq_line780] at hout
  rcases hsb2 : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 160)) with ⟨rsb, ssb⟩
  simp only [hsb2] at hout
  cases rsb with
  | some rsb' =>
    dsimp only at hout; obtain ⟨h0, _⟩ := Prod.mk.inj hout
    rw [evaluateHOLFiniteState_storeByte] at hsb2
    repeat' split at hsb2
    all_goals (obtain ⟨h1, _⟩ := Prod.mk.inj hsb2; rw [← h1] at h0; cases h0)
  | none =>
    dsimp only at hout
    have henc_sb : EncFrame s ssb (nodeHashCacheIvls Nd ++ Rl_extra) := by
      have hsb_m : EncFrame s (evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 160))).2
          (nodeHashCacheIvls Nd ++ Rl_extra) := by
        apply EncFrame.of_storeByte hAR
        intro addr haddr _
        simp [evalHOLExact, hdst] at haddr; subst haddr
        rcases hdst_sub with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨r, hr, h1, by omega⟩
        · exact Or.inr ⟨h1, by omega⟩
      rwa [hsb2] at hsb_m
    have hssb_loc : ssb.locals = s.locals := by
      rw [evaluateHOLFiniteState_storeByte] at hsb2
      repeat' split at hsb2
      all_goals (obtain ⟨h1, h2⟩ := Prod.mk.inj hsb2; cases h1; try exact (congrArg PanSemStateFiniteExact.locals h2).symm)
    have hssb_hp : globN ssb "heap_ptr" = globN s "heap_ptr" := by
      rw [evaluateHOLFiniteState_storeByte] at hsb2
      repeat' split at hsb2
      all_goals (obtain ⟨h1, h2⟩ := Prod.mk.inj hsb2; cases h1; try (have hg := congrArg PanSemStateFiniteExact.globals h2; simp [globN, ← hg]))
    rw [evaluateHOLFiniteState_seq_line780] at hout
    rcases hmc2 : evaluateHOLFiniteState ssb
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .const 1],
           .load .one (.op .add [.var .local (ofString "child"), .const 24]),
           .const 32]) with ⟨rmc, smc⟩
    simp only [hmc2] at hout
    cases rmc with
    | some rmc' =>
      dsimp only at hout; obtain ⟨h0, _⟩ := Prod.mk.inj hout
      obtain ⟨rfl⟩ := Option.some.inj h0
      rw [evaluateHOLFiniteState_call] at hmc2
      repeat' split at hmc2
      all_goals simp_all
    | none =>
      dsimp only at hout
      rw [evaluateHOLFiniteState_return] at hout
      simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hout
      obtain ⟨rfl, rfl⟩ := hout
      have hsb_val : sourceBase = 2701131776 := M11.sourceBase_val
      have hhe_val : heapEnd = 2701131776 + 8 * 3888119741 := M11.heapEnd_val
      have hhe : heapLimit ≤ heapEnd := by decide
      have hlim_val : heapLimit ≤ 2701131776 + 8 * 3888119741 := by rw [← hhe_val]; exact hhe
      have h24_bv : (24#64).toNat = 24 := by decide
      have hadd24 : (cw + 24#64).toNat = cw.toNat + 24 := by
        rw [BitVec.toNat_add_of_lt (by rw [h24_bv]; omega), h24_bv]
      have hdom24 : ssb.memaddrs (cw + 24#64) := by
        rw [henc_sb.arena.1.memaddrs]
        exact (M11.ordinaryDomain_iff (cw + 24#64)).2 ⟨by rw [hadd24]; omega, by rw [hadd24]; omega, by rw [hadd24]; omega⟩
      rcases hm24 : ssb.memory (cw + 24#64) with ⟨w24⟩
      have hev_src : @evalHOLExact 64 F _ ssb.toExact (fun a => Classical.propDecidable (ssb.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "child"), .const 24])) = some (.val (.word w24)) := by
        simp [evalHOLExact, evalListHOLExact, hssb_loc, hchild, valueIsWord, valueWord, wordOpHOL, wordOp,
          memLoadHOLExact]
        exact ⟨hdom24, hm24⟩
      have hev_dst1 : @evalHOLExact 64 F _ ssb.toExact (fun a => Classical.propDecidable (ssb.memaddrs a))
          (.op .add [.var .local (ofString "dst"), .const 1]) = some (.val (.word (dst0 + 1#64))) := by
        simp [evalHOLExact, evalListHOLExact, hssb_loc, hdst, valueIsWord, valueWord, wordOpHOL, wordOp]
      obtain ⟨henc_mc, _, _⟩ := encFrame_call_memcpy ssb
        (.op .add [.var .local (ofString "dst"), .const 1])
        (.load .one (.op .add [.var .local (ofString "child"), .const 24]))
        (.const 32) (dst0 + 1#64) w24 32#64 (nodeHashCacheIvls Nd ++ Rl_extra)
        henc_sb.arena.1.code henc_sb.arena hev_dst1 hev_src rfl
        (fun _ => by
          have h32bv : (32#64).toNat = 32 := by decide
          rw [hdst1_nat, h32bv]
          rcases hdst_sub with hsub_l | ⟨h1, h2⟩
          · obtain ⟨r, hr, h1, h2⟩ := hsub_l
            exact Or.inl ⟨r, hr, by omega, by omega⟩
          · exact Or.inr ⟨by rw [hssb_hp]; omega, by omega⟩)
        (congrArg Prod.fst hmc2)
      rw [congrArg Prod.snd hmc2] at henc_mc
      exact ⟨33, rfl, by decide, (henc_sb.trans henc_mc).with_locals_clock _ _⟩

private theorem eval_node_write_ref_hashed {F : Type}
    (s d2 : PanSemStateFiniteExact 64 F) (cw dst0 : BitVec 64) (Nd : List Nat) (Rl_extra : List Ivl)
    (rv : ValueHOL 64)
    (hc : d2.code = originalRuntimeCode) (hAR : ArenaReady s) (hd2_AR : ArenaReady d2) (hd2_Nh : RelaxedNodeHeap d2 Nd)
    (hd2_enc : EncFrame s d2 (nodeHashCacheIvls Nd ++ Rl_extra))
    (hd2_child : d2.locals.lookup (ofString "child") = some (.val (.word cw)))
    (hd2_dst : d2.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hc_in : cw.toNat ∈ Nd)
    (hdst_hi : dst0.toNat + 33 ≤ heapLimit)
    (hdst_sub : (∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ dst0.toNat ∧ dst0.toNat + 33 ≤ r.1 + r.2) ∨
      (globN s "heap_ptr" ≤ dst0.toNat ∧ dst0.toNat + 33 ≤ heapLimit))
    (hkeccak_sub : ∀ k ∈ keccakScratchIvls d2, k.2 > 0 →
      ∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ k.1 ∧ k.1 + k.2 ≤ r.1 + r.2)
    (hout_f : (evaluateHOLFiniteState d2
      (.decCall (ofString "h") .one (ofString "node_hash_cached") [.var .local (ofString "child")]
        (.seq
          (.storeByte (.var .local (ofString "dst")) (.const 160))
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .const 1],
               .var .local (ofString "h"),
               .const 32])
            (.return (.const 33)))))).1 = some (.returned rv)) :
    rv = .val (.word 33) ∧
    EncFrame s (emptyLocalsHOLFinite (evaluateHOLFiniteState d2
      (.decCall (ofString "h") .one (ofString "node_hash_cached") [.var .local (ofString "child")]
        (.seq
          (.storeByte (.var .local (ofString "dst")) (.const 160))
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .const 1],
               .var .local (ofString "h"),
               .const 32])
            (.return (.const 33)))))).2) (nodeHashCacheIvls Nd ++ Rl_extra) := by
  have hlt64 : heapLimit < 2 ^ 64 := by decide
  have hdst1_nat : (dst0 + 1#64).toNat = dst0.toNat + 1 := by
    have h1bv : (1#64).toNat = 1 := by decide
    rw [BitVec.toNat_add_of_lt (by omega), h1bv]
  let nhCont : ProgHOL 64 :=
    .seq
      (.storeByte (.var .local (ofString "dst")) (.const 160))
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .const 1],
           .var .local (ofString "h"),
           .const 32])
        (.return (.const 33)))
  obtain ⟨hw, midH, hmidH_loc, henc_nh, hnh_f, hnh_s⟩ :=
    eval_decCall_node_hash_cached d2 "h" (.var .local (ofString "child")) cw Nd Rl_extra nhCont rv
      hc hd2_AR hd2_Nh (by simp [evalHOLExact, hd2_child]) hc_in hkeccak_sub hout_f
  dsimp only [nhCont] at hnh_f hnh_s
  rw [evaluateHOLFiniteState_seq_line780] at hnh_f
  rcases hsb3 : evaluateHOLFiniteState midH (.storeByte (.var .local (ofString "dst")) (.const 160)) with ⟨rsb, ssb⟩
  have hsb3' := hsb3
  simp only [hsb3] at hnh_f
  cases rsb with
  | some rsb' =>
    rw [evaluateHOLFiniteState_storeByte] at hsb3
    repeat' split at hsb3
    all_goals (obtain ⟨h1, _⟩ := Prod.mk.inj hsb3; simp [← h1] at hnh_f)
  | none =>
    have hmidH_dst : midH.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      rw [hmidH_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hd2_dst,
        show ofString "h" ≠ ofString "dst" by decide]
    have hmidH_h : midH.locals.lookup (ofString "h") = some (.val (.word hw)) := by
      rw [hmidH_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have henc_sb3 : EncFrame s ssb (nodeHashCacheIvls Nd ++ Rl_extra) := by
      have hsb_m : EncFrame midH (evaluateHOLFiniteState midH (.storeByte (.var .local (ofString "dst")) (.const 160))).2
          (nodeHashCacheIvls Nd ++ Rl_extra ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) := by
        apply EncFrame.of_storeByte henc_nh.arena
        intro addr haddr _
        simp [evalHOLExact, hmidH_dst] at haddr; subst haddr
        rcases hdst_sub with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨r, List.mem_append_left _ hr, h1, by omega⟩
        · exact Or.inl ⟨(globN s "heap_ptr", heapLimit - globN s "heap_ptr"),
            List.mem_append_right _ (List.mem_singleton.2 rfl), h1,
            by dsimp only; have := hAR.2.2.1; omega⟩
      have h1 : EncFrame d2 midH (nodeHashCacheIvls Nd ++ Rl_extra ++
          [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) :=
        henc_nh.mono (fun i hi => Or.inl ⟨i, List.mem_append_left _ hi, le_rfl, le_rfl⟩)
      have hsb_m' : EncFrame midH ssb (nodeHashCacheIvls Nd ++ Rl_extra ++
          [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) := by
        rwa [hsb3'] at hsb_m
      apply ((hd2_enc.mono (fun i hi => Or.inl ⟨i, List.mem_append_left _ hi, le_rfl, le_rfl⟩)).trans
        (h1.trans hsb_m')).mono
      intro i hi
      rcases List.mem_append.1 hi with hi1 | hi2
      · exact Or.inl ⟨i, hi1, le_rfl, le_rfl⟩
      · simp only [List.mem_singleton] at hi2; subst hi2
        exact Or.inr ⟨le_rfl, by dsimp only; have := hAR.2.2.1; omega⟩
    have hssb_loc : ssb.locals = midH.locals := by
      rw [evaluateHOLFiniteState_storeByte] at hsb3
      repeat' split at hsb3
      all_goals (obtain ⟨h1, h2⟩ := Prod.mk.inj hsb3; cases h1; try exact (congrArg PanSemStateFiniteExact.locals h2).symm)
    rw [evaluateHOLFiniteState_seq_line780] at hnh_f
    rcases hmc3 : evaluateHOLFiniteState ssb
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .const 1],
           .var .local (ofString "h"),
           .const 32]) with ⟨rmc, smc⟩
    simp only [hmc3] at hnh_f
    cases rmc with
    | some rmc' =>
      obtain ⟨rfl⟩ := Option.some.inj hnh_f
      rw [evaluateHOLFiniteState_call] at hmc3
      repeat' split at hmc3
      all_goals simp_all
    | none =>
      rw [evaluateHOLFiniteState_return] at hnh_f
      simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hnh_f
      subst hnh_f
      have hev_dst1 : @evalHOLExact 64 F _ ssb.toExact (fun a => Classical.propDecidable (ssb.memaddrs a))
          (.op .add [.var .local (ofString "dst"), .const 1]) = some (.val (.word (dst0 + 1#64))) := by
        simp [evalHOLExact, evalListHOLExact, hssb_loc, hmidH_dst, valueIsWord, valueWord, wordOpHOL, wordOp]
      have hev_h : @evalHOLExact 64 F _ ssb.toExact (fun a => Classical.propDecidable (ssb.memaddrs a))
          (.var .local (ofString "h")) = some (.val (.word hw)) := by
        simp [evalHOLExact, hssb_loc, hmidH_h]
      obtain ⟨henc_mc3, _, _⟩ := encFrame_call_memcpy ssb
        (.op .add [.var .local (ofString "dst"), .const 1])
        (.var .local (ofString "h")) (.const 32)
        (dst0 + 1#64) hw 32#64
        (nodeHashCacheIvls Nd ++ Rl_extra ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")])
        henc_sb3.arena.1.code henc_sb3.arena hev_dst1 hev_h rfl
        (fun _ => by
          have h32bv : (32#64).toNat = 32 := by decide
          rw [hdst1_nat, h32bv]
          rcases hdst_sub with hsub_l | ⟨h1, h2⟩
          · obtain ⟨r, hr, h1, h2⟩ := hsub_l
            exact Or.inl ⟨r, List.mem_append_left _ hr, by omega, by omega⟩
          · exact Or.inl ⟨(globN s "heap_ptr", heapLimit - globN s "heap_ptr"),
              List.mem_append_right _ (List.mem_singleton.2 rfl), by omega,
              by dsimp only; have := hAR.2.2.1; omega⟩)
        (congrArg Prod.fst hmc3)
      rw [congrArg Prod.snd hmc3] at henc_mc3
      have henc_tot : EncFrame s smc (nodeHashCacheIvls Nd ++ Rl_extra) := by
        apply ((henc_sb3.mono (fun i hi => Or.inl ⟨i, List.mem_append_left _ hi, le_rfl, le_rfl⟩)).trans henc_mc3).mono
        intro i hi
        rcases List.mem_append.1 hi with hi1 | hi2
        · exact Or.inl ⟨i, hi1, le_rfl, le_rfl⟩
        · simp only [List.mem_singleton] at hi2; subst hi2
          exact Or.inr ⟨le_rfl, by dsimp only; have := hAR.2.2.1; omega⟩
      have hcont_snd : (evaluateHOLFiniteState midH nhCont).2 =
          emptyLocalsHOLFinite smc := by
        dsimp only [nhCont]
        rw [evaluateHOLFiniteState_seq_line780, hsb3']
        dsimp only
        rw [evaluateHOLFiniteState_seq_line780, hmc3]
        dsimp only
        rw [evaluateHOLFiniteState_return]
        simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      have hpost_eq : emptyLocalsHOLFinite (evaluateHOLFiniteState d2
          (.decCall (ofString "h") .one (ofString "node_hash_cached") [.var .local (ofString "child")] nhCont)).2 =
          emptyLocalsHOLFinite smc := by
        dsimp only [nhCont]
        rw [hnh_s]
        change emptyLocalsHOLFinite
          { (evaluateHOLFiniteState midH nhCont).2 with
            locals := _ } = emptyLocalsHOLFinite smc
        rw [hcont_snd]
        rfl
      dsimp only [nhCont] at hpost_eq
      rw [hpost_eq]
      exact ⟨rfl, henc_tot.with_locals_clock _ _⟩

private theorem eval_node_write_ref_tail {F : Type}
    (s : PanSemStateFiniteExact 64 F) (cw dst0 : BitVec 64) (Nd : List Nat) (Rl_extra : List Ivl) (rv : ValueHOL 64)
    (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s) (hNh : RelaxedNodeHeap s Nd)
    (hchild : s.locals.lookup (ofString "child") = some (.val (.word cw)))
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hc_in : cw.toNat ∈ Nd)
    (hdst_hi : dst0.toNat + 33 ≤ heapLimit)
    (hdst_sub : (∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ dst0.toNat ∧ dst0.toNat + 33 ≤ r.1 + r.2) ∨
      (globN s "heap_ptr" ≤ dst0.toNat ∧ dst0.toNat + 33 ≤ heapLimit))
    (hkeccak_sub : ∀ k ∈ keccakScratchIvls s, k.2 > 0 →
      ∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ k.1 ∧ k.1 + k.2 ≤ r.1 + r.2)
    (hout_f : (evaluateHOLFiniteState s
      (.seq
        (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
          (.call (some (none, none)) (ofString "mpt_fail") [.const 13])
          .skip)
        (.dec (ofString "rp") .one (.load .one (.op .add [.var .local (ofString "child"), .const 8]))
          (.dec (ofString "rl") .one (.load .one (.op .add [.var .local (ofString "child"), .const 16]))
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "rl")) (.const 32))
                (.seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")])
                  (.return (.var .local (ofString "rl"))))
                .skip)
              (.decCall (ofString "h") .one (ofString "node_hash_cached") [.var .local (ofString "child")]
                (.seq
                  (.storeByte (.var .local (ofString "dst")) (.const 160))
                  (.seq
                    (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "dst"), .const 1],
                       .var .local (ofString "h"),
                       .const 32])
                    (.return (.const 33)))))))))).1 = some (.returned rv))
    (hout_s : (evaluateHOLFiniteState s
      (.seq
        (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
          (.call (some (none, none)) (ofString "mpt_fail") [.const 13])
          .skip)
        (.dec (ofString "rp") .one (.load .one (.op .add [.var .local (ofString "child"), .const 8]))
          (.dec (ofString "rl") .one (.load .one (.op .add [.var .local (ofString "child"), .const 16]))
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "rl")) (.const 32))
                (.seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")])
                  (.return (.var .local (ofString "rl"))))
                .skip)
              (.decCall (ofString "h") .one (ofString "node_hash_cached") [.var .local (ofString "child")]
                (.seq
                  (.storeByte (.var .local (ofString "dst")) (.const 160))
                  (.seq
                    (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "dst"), .const 1],
                       .var .local (ofString "h"),
                       .const 32])
                    (.return (.const 33)))))))))).2 = post) :
    ∃ w : BitVec 64,
      rv = .val (.word w) ∧ w.toNat ≤ 33 ∧
      EncFrame s (emptyLocalsHOLFinite post) (nodeHashCacheIvls Nd ++ Rl_extra) := by
  have hlt64 : heapLimit < 2 ^ 64 := by decide
  have hdst1_nat : (dst0 + 1#64).toNat = dst0.toNat + 1 := by
    have h1bv : (1#64).toNat = 1 := by decide
    rw [BitVec.toNat_add_of_lt (by omega), h1bv]
  rw [evaluateHOLFiniteState_seq_line780] at hout_f hout_s
  rcases hmf_step : evaluateHOLFiniteState s
      (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
        (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) with ⟨rmf, e1⟩
  simp only [hmf_step] at hout_f hout_s
  have hmf := eval_call_mpt_fail_no_none_no_ret s 13 hc
  cases rmf with
  | some rmf' =>
    have hr_eq : rmf' = .returned rv := Option.some.inj hout_f
    subst hr_eq
    rw [evaluateHOLFiniteState_ite] at hmf_step
    split at hmf_step
    · split at hmf_step
      · rw [evaluateHOLFiniteState_skip] at hmf_step; cases hmf_step
      · exact False.elim (hmf.2 rv (congrArg Prod.fst hmf_step))
    · cases hmf_step
  | none =>
    have he1 : e1 = s := by
      rw [evaluateHOLFiniteState_ite] at hmf_step
      split at hmf_step
      · split at hmf_step
        · rw [evaluateHOLFiniteState_skip] at hmf_step; exact (Prod.mk.inj hmf_step).2.symm
        · exact False.elim (hmf.1 (congrArg Prod.fst hmf_step))
      · cases hmf_step
    rw [he1] at hout_f hout_s
    rw [evaluateHOLFiniteState_dec_total] at hout_f hout_s; try dsimp only at hout_f hout_s
    rcases hld8 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "child"), .const 8])) with _ | rpv
    · rw [hld8] at hout_f; cases hout_f
    · obtain ⟨rpw, rfl⟩ := R10Shards.P26_P28.eval_load_one_word s _ rpv hld8
      have hsh_rp : shapeEqHOL .one (shapeOfHOLExact (.val (.word rpw) : ValueHOL 64)) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [hld8] at hout_f hout_s; dsimp only at hout_f hout_s; rw [if_pos hsh_rp] at hout_f hout_s
      set d1 := setVarHOLFinite (ofString "rp") (.val (.word rpw)) s
      rw [evaluateHOLFiniteState_dec_total] at hout_f hout_s; dsimp only at hout_f hout_s
      rcases hld16 : @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "child"), .const 16])) with _ | rlv
      · rw [hld16] at hout_f; cases hout_f
      · obtain ⟨rlw, rfl⟩ := R10Shards.P26_P28.eval_load_one_word d1 _ rlv hld16
        have hsh_rl : shapeEqHOL .one (shapeOfHOLExact (.val (.word rlw) : ValueHOL 64)) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [hld16] at hout_f hout_s; dsimp only at hout_f hout_s; rw [if_pos hsh_rl] at hout_f hout_s
        set d2 := setVarHOLFinite (ofString "rl") (.val (.word rlw)) d1
        have hd2_AR : ArenaReady d2 := localsFree_arenaReady s d2.locals d2.clock hAR
        have hd2_enc : EncFrame s d2 (nodeHashCacheIvls Nd ++ Rl_extra) :=
          (EncFrame.refl s hAR _).with_locals_clock _ _
        have hd2_child : d2.locals.lookup (ofString "child") = some (.val (.word cw)) := by
          simp [d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hchild,
            show ofString "rl" ≠ ofString "child" by decide, show ofString "rp" ≠ ofString "child" by decide]
        have hd2_dst : d2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          simp [d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst,
            show ofString "rl" ≠ ofString "dst" by decide, show ofString "rp" ≠ ofString "dst" by decide]
        have hd2_rp : d2.locals.lookup (ofString "rp") = some (.val (.word rpw)) := by
          simp [d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rl" ≠ ofString "rp" by decide]
        have hd2_rl : d2.locals.lookup (ofString "rl") = some (.val (.word rlw)) := by
          simp [d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hout_f hout_s
        have hcmp_rl : @evalHOLExact 64 F _ d2.toExact (fun a => Classical.propDecidable (d2.memaddrs a))
            (.cmp .lower (.var .local (ofString "rl")) (.const 32)) =
            some (.val (.word (if rlw.toNat < 32 then 1 else 0))) := by
          simp [evalHOLExact, hd2_rl, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
        rw [hcmp_rl] at hout_f hout_s; dsimp only at hout_f hout_s
        by_cases hrl32 : rlw.toNat < 32
        · rw [if_pos hrl32] at hout_f hout_s
          have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
          rw [if_neg h10] at hout_f hout_s
          rw [evaluateHOLFiniteState_seq_line780] at hout_f hout_s
          rcases hmc_in : evaluateHOLFiniteState d2
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")]) with ⟨rmc, smc⟩
          simp only [hmc_in] at hout_f hout_s
          cases rmc with
          | some rmc' =>
            obtain ⟨rfl⟩ := Option.some.inj hout_f
            rw [evaluateHOLFiniteState_call] at hmc_in
            repeat' split at hmc_in
            all_goals simp_all
          | none =>
            try dsimp only at hout_f hout_s
            obtain ⟨henc_mc, hsmc_loc, _⟩ := encFrame_call_memcpy d2
              (.var .local (ofString "dst")) (.var .local (ofString "rp")) (.var .local (ofString "rl"))
              dst0 rpw rlw (nodeHashCacheIvls Nd ++ Rl_extra)
              hc hd2_AR (by simp [evalHOLExact, hd2_dst]) (by simp [evalHOLExact, hd2_rp])
              (by simp [evalHOLExact, hd2_rl])
              (fun _ => by
                rcases hdst_sub with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩
                · exact Or.inl ⟨r, hr, h1, by omega⟩
                · exact Or.inr ⟨h1, by omega⟩)
              (congrArg Prod.fst hmc_in)
            rw [hmc_in] at henc_mc hsmc_loc
            dsimp only at henc_mc hsmc_loc
            rw [evaluateHOLFiniteState_return] at hout_f hout_s
            have hsmc_rl : @evalHOLExact 64 F _ smc.toExact (fun a => Classical.propDecidable (smc.memaddrs a))
                (.var .local (ofString "rl")) = some (.val (.word rlw)) := by
              simp [evalHOLExact, hsmc_loc, hd2_rl]
            simp only [hsmc_rl, shapeOfHOLExact, sizeOfShapeWithContextHOL, ↓reduceIte] at hout_f hout_s
            have hrv : PanSemResultExact.returned (.val (.word rlw)) = PanSemResultExact.returned rv :=
              Option.some.inj hout_f
            obtain ⟨rfl⟩ := PanSemResultExact.returned.inj hrv
            have hpost_eq : emptyLocalsHOLFinite post = emptyLocalsHOLFinite smc := by
              rw [← hout_s]; rfl
            rw [hpost_eq]
            exact ⟨rlw, rfl, by omega, (hd2_enc.trans henc_mc).with_locals_clock _ _⟩
        · rw [if_neg hrl32] at hout_f hout_s
          rw [if_pos rfl, evaluateHOLFiniteState_skip] at hout_f hout_s
          dsimp only at hout_f hout_s
          have hd2_Nh : RelaxedNodeHeap d2 Nd :=
            relaxedNodeHeap_congr_unhit hAR.1 hd2_AR.1 rfl ⟨le_rfl, le_rfl⟩ hNh (fun _ _ _ _ _ _ => rfl)
          have hkeccak_d2 : ∀ k ∈ keccakScratchIvls d2, k.2 > 0 →
              ∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ k.1 ∧ k.1 + k.2 ≤ r.1 + r.2 := hkeccak_sub
          obtain ⟨rfl, henc_h⟩ := eval_node_write_ref_hashed s d2 cw dst0 Nd Rl_extra rv
            hc hAR hd2_AR hd2_Nh hd2_enc hd2_child hd2_dst hc_in hdst_hi hdst_sub hkeccak_d2 hout_f
          have hpost_eq : emptyLocalsHOLFinite post =
              emptyLocalsHOLFinite (evaluateHOLFiniteState d2
                (.decCall (ofString "h") .one (ofString "node_hash_cached") [.var .local (ofString "child")]
                  (.seq
                    (.storeByte (.var .local (ofString "dst")) (.const 160))
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.op .add [.var .local (ofString "dst"), .const 1],
                         .var .local (ofString "h"),
                         .const 32])
                      (.return (.const 33)))))).2 := by
            rw [← hout_s]
            rfl
          rw [hpost_eq]
          exact ⟨33, rfl, by decide, henc_h⟩

private theorem eval_node_write_ref_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (cw dst0 : BitVec 64) (Nd : List Nat) (Rl_extra : List Ivl) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s) (hNh : RelaxedNodeHeap s Nd)
    (hchild : s.locals.lookup (ofString "child") = some (.val (.word cw)))
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hroot : RootIn Nd cw.toNat)
    (hdst_hi : dst0.toNat + 33 ≤ heapLimit)
    (hdst_sub : (∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ dst0.toNat ∧ dst0.toNat + 33 ≤ r.1 + r.2) ∨
      (globN s "heap_ptr" ≤ dst0.toNat ∧ dst0.toNat + 33 ≤ heapLimit))
    (hkeccak_sub : ∀ k ∈ keccakScratchIvls s, k.2 > 0 →
      ∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ k.1 ∧ k.1 + k.2 ≤ r.1 + r.2)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_write_ref)).1 = some (.returned rv)) :
    ∃ w : BitVec 64,
      rv = .val (.word w) ∧ w.toNat ≤ 33 ∧
      EncFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_write_ref)).2
        (nodeHashCacheIvls Nd ++ Rl_extra) := by
  have hb : sourceFnBody Guest.Software.guestFn_node_write_ref =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "child")) (.const 0))
          (.seq (.storeByte (.var .local (ofString "dst")) (.const 128)) (.return (.const 1)))
          .skip)
        (.seq
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
            (.seq
              (.storeByte (.var .local (ofString "dst")) (.const 160))
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"), .const 1],
                   .load .one (.op .add [.var .local (ofString "child"), .const 24]),
                   .const 32])
                (.return (.const 33))))
            .skip)
          (.seq
            (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
              (.call (some (none, none)) (ofString "mpt_fail") [.const 13])
              .skip)
            (.dec (ofString "rp") .one (.load .one (.op .add [.var .local (ofString "child"), .const 8]))
              (.dec (ofString "rl") .one (.load .one (.op .add [.var .local (ofString "child"), .const 16]))
                (.seq
                  (.ite (.cmp .lower (.var .local (ofString "rl")) (.const 32))
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")])
                      (.return (.var .local (ofString "rl"))))
                    .skip)
                  (.decCall (ofString "h") .one (ofString "node_hash_cached") [.var .local (ofString "child")]
                    (.seq
                      (.storeByte (.var .local (ofString "dst")) (.const 160))
                      (.seq
                        (.call (some (none, none)) (ofString "memcpy")
                          [.op .add [.var .local (ofString "dst"), .const 1],
                           .var .local (ofString "h"),
                           .const 32])
                        (.return (.const 33)))))))))) := rfl
  rcases hout : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_write_ref) with ⟨r0, post⟩
  rw [hout] at hret; dsimp only at hret; subst hret
  have hout_f := congrArg Prod.fst hout
  have hout_s := congrArg Prod.snd hout
  dsimp only at hout_f hout_s
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hout_f hout_s
  have hcmp0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "child")) (.const 0)) =
      some (.val (.word (if cw = 0 then 1 else 0))) := by
    simp [evalHOLExact, hchild, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp0] at hout_f hout_s; dsimp only at hout_f hout_s
  by_cases hcw0 : cw = 0
  · subst hcw0
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_pos rfl, if_neg h10] at hout_f hout_s
    rw [evaluateHOLFiniteState_seq_line780] at hout_f hout_s
    rcases hsb1 : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 128)) with ⟨rsb, ssb⟩
    simp only [hsb1] at hout_f hout_s
    cases rsb with
    | some rsb' =>
      dsimp only at hout_f
      rw [evaluateHOLFiniteState_storeByte] at hsb1
      repeat' split at hsb1
      all_goals (obtain ⟨h1, _⟩ := Prod.mk.inj hsb1 <;> (try cases h1) <;> (try simp at hout_f))
    | none =>
      dsimp only at hout_f hout_s
      have henc1 : EncFrame s ssb (nodeHashCacheIvls Nd ++ Rl_extra) := by
        have hsb_m : EncFrame s (evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 128))).2
            (nodeHashCacheIvls Nd ++ Rl_extra) := by
          apply EncFrame.of_storeByte hAR
          intro addr haddr _
          simp [evalHOLExact, hdst] at haddr; subst haddr
          rcases hdst_sub with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨r, hr, h1, by omega⟩
          · exact Or.inr ⟨h1, by omega⟩
        rwa [hsb1] at hsb_m
      rw [evaluateHOLFiniteState_return] at hout_f hout_s
      simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hout_f hout_s
      subst hout_f hout_s
      dsimp only
      exact ⟨1, rfl, by decide, henc1.with_locals_clock _ _⟩
  · have hc_in : cw.toNat ∈ Nd := by
      rcases hroot with h0 | hin
      · exfalso; apply hcw0; exact BitVec.eq_of_toNat_eq (by simpa using h0)
      · exact hin
    have hc_al : cw.toNat % 8 = 0 := (hNh.1 cw.toNat hc_in).2.2.2.1.1
    have hc_bounds := relaxedNodeIvl_lt_heap_ptr hAR.2 hNh hc_in
    have hc_sz : cw.toNat + 32 ≤ heapLimit := by
      have hsz : 32 ≤ (nodeIvl s cw.toNat).2 := by dsimp [nodeIvl, nodeSize]; split_ifs <;> omega
      have hhp := hAR.2.2.1; omega
    rw [if_neg hcw0, if_pos rfl, evaluateHOLFiniteState_skip] at hout_f hout_s
    dsimp only at hout_f hout_s
    rw [evaluateHOLFiniteState_seq_line780] at hout_f hout_s
    rcases hbr2 : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
          (.seq
            (.storeByte (.var .local (ofString "dst")) (.const 160))
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"), .const 1],
                 .load .one (.op .add [.var .local (ofString "child"), .const 24]),
                 .const 32])
              (.return (.const 33))))
          .skip) with ⟨r2, s2⟩
    simp only [hbr2] at hout_f hout_s
    rw [evaluateHOLFiniteState_ite] at hbr2
    rcases hld0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "child"), .const 0])) with _ | kv0
    · have hcmp_none : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0)) = none := by
        unfold evalHOLExact; rw [hld0]
      rw [hcmp_none] at hbr2; obtain ⟨rfl, _⟩ := Prod.mk.inj hbr2; simp at hout_f
    · obtain ⟨kw0, rfl⟩ := R10Shards.P26_P28.eval_load_one_word s _ kv0 hld0
      have hcmp_k0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0)) =
          some (.val (.word (if kw0 = 0 then 1 else 0))) := by
        unfold evalHOLExact; rw [hld0]; simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hcmp_k0] at hbr2; dsimp only at hbr2
      by_cases hkw0 : kw0 = 0
      · subst hkw0
        have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
        rw [if_pos rfl, if_neg h10] at hbr2
        cases r2 with
        | none =>
          exfalso
          rw [evaluateHOLFiniteState_seq_line780] at hbr2
          rcases hsb_tmp : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 160)) with ⟨rs, ss⟩
          rw [hsb_tmp] at hbr2
          cases rs with
          | some _ => cases hbr2
          | none =>
            dsimp only at hbr2
            rw [evaluateHOLFiniteState_seq_line780] at hbr2
            rcases hmc_tmp : evaluateHOLFiniteState ss
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"), .const 1],
                   .load .one (.op .add [.var .local (ofString "child"), .const 24]),
                   .const 32]) with ⟨rm, sm⟩
            rw [hmc_tmp] at hbr2
            cases rm with
            | some _ => cases hbr2
            | none =>
              dsimp only at hbr2
              rw [evaluateHOLFiniteState_return] at hbr2
              simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hbr2
        | some r2' =>
          dsimp only at hout_f hout_s
          obtain ⟨rfl⟩ := Option.some.inj hout_f
          subst hout_s
          dsimp only
          exact eval_node_write_ref_kind0 s cw dst0 Nd Rl_extra rv s2 hAR hchild hdst
            hc_al hc_bounds.1 hc_sz hdst_hi hdst_sub hbr2
      · rw [if_neg hkw0, if_pos rfl, evaluateHOLFiniteState_skip] at hbr2
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbr2
        dsimp only at hout_f hout_s
        obtain ⟨w, rfl, hw_le, henc_t⟩ := eval_node_write_ref_tail s cw dst0 Nd Rl_extra rv post
          hc hAR hNh hchild hdst hc_in hdst_hi hdst_sub hkeccak_sub hout_f hout_s
        dsimp only
        exact ⟨w, rfl, hw_le, henc_t.with_locals_clock _ _⟩

private theorem eval_decCall_node_write_ref {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (childExp dstExp : ExpHOL 64)
    (cw dst0 : BitVec 64) (Nd : List Nat) (Rl_extra : List Ivl) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s) (hNh : RelaxedNodeHeap s Nd)
    (hchild : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) childExp =
      some (.val (.word cw)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hroot : RootIn Nd cw.toNat)
    (hdst_hi : dst0.toNat + 33 ≤ heapLimit)
    (hdst_sub : (∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ dst0.toNat ∧ dst0.toNat + 33 ≤ r.1 + r.2) ∨
      (globN s "heap_ptr" ≤ dst0.toNat ∧ dst0.toNat + 33 ≤ heapLimit))
    (hdisj_extra : ∀ r ∈ Rl_extra, ∀ o ∈ nodeExtents s Nd, Disj r o)
    (hkeccak_sub : ∀ k ∈ keccakScratchIvls s, k.2 > 0 →
      ∃ r ∈ nodeHashCacheIvls Nd ++ Rl_extra, r.1 ≤ k.1 ∧ k.1 + k.2 ≤ r.1 + r.2)
    (hret : ((evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "node_write_ref") [childExp, dstExp] cont)).1 = none) ∨
      ∃ rv, (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "node_write_ref") [childExp, dstExp] cont)).1 = some (.returned rv)) :
    ∃ (w : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      w.toNat ≤ 33 ∧
      mid.locals = s.locals.update (ofString lname, .val (.word w)) ∧
      EncFrame s mid (nodeHashCacheIvls Nd ++ Rl_extra) ∧
      RelaxedNodeHeap mid Nd ∧
      (((evaluateHOLFiniteState mid cont).1 = none) ∨
        ∃ rv, (evaluateHOLFiniteState mid cont).1 = some (.returned rv)) ∧
      evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "node_write_ref") [childExp, dstExp] cont) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [childExp, dstExp] = some [.val (.word cw), .val (.word dst0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hchild, hdst]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "node_write_ref")
    (ofString "child") (ofString "dst")
    (sourceFnBody Guest.Software.guestFn_node_write_ref) cw dst0
    (by decide) (by rw [hc]; exact lookup_node_write_ref)
  simp only [hargs, hlk] at hret ⊢
  by_cases hclk0 : s.clock = 0
  · simp [hclk0] at hret
  · simp only [hclk0, ↓reduceIte] at hret ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "child", ValueHOL.val (.word cw))).update
      (ofString "dst", ValueHOL.val (.word dst0))
    set entry := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady entry := localsFree_arenaReady s cmap (s.clock - 1) hAR
    have hent_Nh : RelaxedNodeHeap entry Nd :=
      relaxedNodeHeap_congr_unhit hAR.1 hent_AR.1 rfl ⟨le_rfl, le_rfl⟩ hNh (fun _ _ _ _ _ _ => rfl)
    have hent_c : entry.locals.lookup (ofString "child") = some (.val (.word cw)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "dst" ≠ ofString "child" by decide]
    have hent_d : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hclk_le := evaluateHOLFiniteState_clock_le entry (sourceFnBody Guest.Software.guestFn_node_write_ref)
    rcases hcal : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_node_write_ref) with ⟨rc, sc⟩
    simp only [hcal] at hret hclk_le ⊢
    cases rc with
    | none => simp [fixClockHOLFinite] at hret
    | some rc' =>
      cases rc' with
      | returned vc =>
        obtain ⟨w, rfl, hw_le, henc_c⟩ := eval_node_write_ref_returned entry cw dst0 Nd Rl_extra vc
          hc hent_AR hent_Nh hent_c hent_d hroot hdst_hi hdst_sub hkeccak_sub (by rw [hcal])
        rw [hcal] at henc_c
        dsimp only [fixClockHOLFinite] at hret ⊢
        have hclk_if : (if entry.clock < sc.clock then entry.clock else sc.clock) = sc.clock :=
          if_neg (by omega)
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte, hclk_if] at hret ⊢
        let mid : PanSemStateFiniteExact 64 F :=
          setVarHOLFinite (ofString lname) (.val (.word w)) { sc with locals := s.locals }
        have hhenc0 : EncFrame s entry (nodeHashCacheIvls Nd ++ Rl_extra) :=
          (EncFrame.refl s hAR _).with_locals_clock _ _
        have hhenc_mid : EncFrame s mid (nodeHashCacheIvls Nd ++ Rl_extra) :=
          (hhenc0.trans henc_c).with_locals_clock _ _
        have hmid_Nh : RelaxedNodeHeap mid Nd :=
          (relaxedNodeHeap_preserved_of_encFrame_hashCache hAR hhenc_mid hNh hdisj_extra).1
        refine ⟨w, mid, hw_le, rfl, hhenc_mid, hmid_Nh, hret, ?_⟩
        rcases evaluateHOLFiniteState mid cont with ⟨r_end, s_end⟩
        rfl
      | _ => simp [fixClockHOLFinite] at hret

def PathBounded {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (Nd Nd' : List Nat) (extra : List Ivl) : Prop :=
  ∀ n ∈ Nd', (memW post n = 1 ∨ memW post n = 2) → memW post (n + 40) ≠ 0 →
    (∃ j ∈ nodeExtents s Nd ++ extra,
      Inside (memW post (n + 32), memW post (n + 40)) j.1 (j.1 + j.2)) ∨
    Inside (memW post (n + 32), memW post (n + 40))
      (globN s "heap_ptr") (globN post "heap_ptr")

theorem nodeExtents_ownedGrows_of_pathBounded {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd Nd' : List Nat} {extra : List Ivl}
    (hstep : R16Shards.NodeStep s post Nd Nd') (hpath : PathBounded s post Nd Nd' extra) :
    OwnedGrows s post (nodeExtents s Nd ++ extra) (nodeExtents post Nd') := by
  intro o ho
  obtain ⟨n, hn, ho⟩ := List.mem_flatMap.1 ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · rcases hstep.fresh n hn with hold | hfresh
    · right; left
      refine ⟨nodeIvl s n, List.mem_append_left _ ?_, ?_⟩
      · exact List.mem_flatMap.2 ⟨n, hold, by simp⟩
      · have heq : nodeIvl post n = nodeIvl s n := by
          unfold nodeIvl; rw [hstep.kinds n hold]
        rw [heq]
        exact ⟨le_rfl, le_rfl⟩
    · exact Or.inr (Or.inr hfresh)
  · unfold nodePath
    split
    · rename_i hcond
      exact Or.inr (hpath n hn hcond.1 hcond.2)
    · exact Or.inl rfl

structure ExtNodeStep {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (Nd Nd' : List Nat) (extra : List Ivl) : Prop where
  step : R16Shards.NodeStep s post Nd Nd'
  owned : OwnedGrows s post (nodeExtents s Nd ++ extra) (nodeExtents post Nd')

def BoundedKey {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (extra : List Ivl) (p len : Nat) : Prop :=
  len = 0 ∨
    (∃ j ∈ nodeExtents s Nd ++ extra, Inside (p, len) j.1 (j.1 + j.2)) ∨
    Inside (p, len) (globN s "heap_ptr") (globN post "heap_ptr")

theorem BoundedKey.zero {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {extra : List Ivl} {p : Nat} :
    BoundedKey s post Nd extra p 0 :=
  Or.inl rfl

theorem BoundedKey.of_extra {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {extra : List Ivl} {p len : Nat}
    (hmem : (p, len) ∈ extra) :
    BoundedKey s s Nd extra p len :=
  Or.inr (Or.inl ⟨(p, len), List.mem_append_right _ hmem, le_rfl, le_rfl⟩)

theorem BoundedKey.of_fresh {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {extra : List Ivl} {p len : Nat}
    (hfr : len = 0 ∨ Inside (p, len) (globN s "heap_ptr") (globN post "heap_ptr")) :
    BoundedKey s post Nd extra p len := by
  rcases hfr with rfl | hin
  · exact Or.inl rfl
  · exact Or.inr (Or.inr hin)

theorem BoundedKey.mono_hp {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {extra : List Ivl} {p len : Nat}
    (hbk : BoundedKey s mid Nd extra p len)
    (hhp : globN mid "heap_ptr" ≤ globN post "heap_ptr") :
    BoundedKey s post Nd extra p len := by
  rcases hbk with rfl | ⟨j, hj, hin⟩ | hfr
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨j, hj, hin⟩)
  · exact Or.inr (Or.inr ⟨hfr.1, le_trans hfr.2 hhp⟩)

theorem BoundedKey.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {extra : List Ivl} {p len : Nat}
    (hbk : BoundedKey s post Nd extra p len)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (C : Nat) :
    BoundedKey s { post with locals := L, clock := C } Nd extra p len :=
  hbk

theorem BoundedKey.subslice {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {extra : List Ivl} {p len off sub : Nat}
    (hA : ArenaReady post) {Nd' : List Nat}
    (hkey : KeyIn post Nd' p len)
    (hbk : BoundedKey s post Nd extra p len)
    (hsub : off + sub ≤ len) :
    BoundedKey s post Nd extra ((BitVec.ofNat 64 p + BitVec.ofNat 64 off).toNat) sub := by
  by_cases hz : sub = 0
  · subst hz; exact Or.inl rfl
  · have hlen_nz : len ≠ 0 := by omega
    obtain ⟨_, _, hins, _⟩ := hkey.resolve_left hlen_nz
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hlt64 : p + off < 2 ^ 64 := by dsimp [Inside] at hins; omega
    have hadd_eq : (BitVec.ofNat 64 p + BitVec.ofNat 64 off).toNat = p + off := by
      have hp64 : p < 2 ^ 64 := by omega
      have hoff64 : off < 2 ^ 64 := by omega
      rw [BitVec.toNat_add_of_lt]
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp64,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64]
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp64,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64]
        omega
    have _ := hA
    rw [hadd_eq]
    rcases hbk with rfl | ⟨j, hj, hj_in⟩ | hfr
    · exact absurd rfl hlen_nz
    · exact Or.inr (Or.inl ⟨j, hj, by dsimp [Inside] at hj_in ⊢; omega, by dsimp [Inside] at hj_in ⊢; omega⟩)
    · exact Or.inr (Or.inr ⟨by dsimp [Inside] at hfr ⊢; omega, by dsimp [Inside] at hfr ⊢; omega⟩)

theorem BoundedKey.of_node_path {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} {extra : List Ivl} {n : Nat}
    (hext : ExtNodeStep s mid Nd Nd' extra)
    (hn : n ∈ Nd') (hk : memW mid n = 1 ∨ memW mid n = 2) :
    BoundedKey s mid Nd extra (memW mid (n + 32)) (memW mid (n + 40)) := by
  by_cases hz : memW mid (n + 40) = 0
  · exact Or.inl hz
  · have hmem : (memW mid (n + 32), memW mid (n + 40)) ∈ nodeExtents mid Nd' := by
      unfold nodeExtents
      exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, hk, hz]⟩
    rcases hext.owned _ hmem with heq0 | ⟨j, hj, hin⟩ | hfr
    · exact absurd (congrArg Prod.snd heq0) hz
    · exact Or.inr (Or.inl ⟨j, hj, hin⟩)
    · exact Or.inr (Or.inr hfr)

theorem mem_nodeExtents_zero_or_pos {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {o : Ivl} (ho : o ∈ nodeExtents s Nd) :
    o = (0, 0) ∨ 0 < o.2 := by
  obtain ⟨n, _, hmem⟩ := List.mem_flatMap.1 ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · right
    dsimp [nodeIvl]
    unfold nodeSize
    split_ifs <;> omega
  · unfold nodePath
    split
    · rename_i hcond
      exact Or.inr (Nat.pos_of_ne_zero hcond.2)
    · exact Or.inl rfl

theorem BoundedKey.lift {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} {extra extra' : List Ivl} {p len : Nat}
    (h1 : ExtNodeStep s mid Nd Nd' extra)
    (hhp2 : globN mid "heap_ptr" ≤ globN post "heap_ptr")
    (h2 : BoundedKey mid post Nd' extra' p len)
    (hextra : ∀ e ∈ extra', BoundedKey s mid Nd extra e.1 e.2) :
    BoundedKey s post Nd extra p len := by
  rcases h2 with rfl | ⟨j, hj, hin⟩ | hfr
  · exact Or.inl rfl
  · rcases List.mem_append.1 hj with hj_nd | hj_ex
    · rcases h1.owned j hj_nd with rfl | ⟨k, hk, hkj⟩ | hj_fr
      · by_cases hlen0 : len = 0
        · exact Or.inl hlen0
        · dsimp [Inside] at hin; omega
      · exact Or.inr (Or.inl ⟨k, hk, le_trans hkj.1 hin.1, le_trans hin.2 hkj.2⟩)
      · exact Or.inr (Or.inr ⟨le_trans hj_fr.1 hin.1,
          le_trans (le_trans hin.2 hj_fr.2) hhp2⟩)
    · rcases hextra j hj_ex with h0 | ⟨k, hk, hkj⟩ | hj_fr
      · by_cases hlen0 : len = 0
        · exact Or.inl hlen0
        · dsimp [Inside] at hin; omega
      · exact Or.inr (Or.inl ⟨k, hk, le_trans hkj.1 hin.1, le_trans hin.2 hkj.2⟩)
      · exact Or.inr (Or.inr ⟨le_trans hj_fr.1 hin.1,
          le_trans (le_trans hin.2 hj_fr.2) hhp2⟩)
  · exact Or.inr (Or.inr ⟨le_trans h1.step.hp_le hfr.1, hfr.2⟩)

theorem ExtNodeStep.refl {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {extra : List Ivl} (hAR : ArenaReady s) (hNd : NodeHeap s Nd) :
    ExtNodeStep s s Nd Nd extra := by
  refine ⟨R16Shards.NodeStep.refl hAR hNd, ?_⟩
  intro o ho
  exact Or.inr (Or.inl ⟨o, List.mem_append_left _ ho, le_rfl, le_rfl⟩)

theorem ExtNodeStep.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} {extra : List Ivl}
    (h : ExtNodeStep s post Nd Nd' extra)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (C : Nat) :
    ExtNodeStep s { post with locals := L, clock := C } Nd Nd' extra :=
  ⟨h.step.with_locals_clock L C, h.owned⟩

theorem ExtNodeStep.from_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} {extra : List Ivl}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {C : Nat}
    (h : ExtNodeStep { s with locals := L, clock := C } post Nd Nd' extra) :
    ExtNodeStep s post Nd Nd' extra :=
  ⟨R16Shards.NodeStep.from_locals_clock h.step, h.owned⟩

theorem ExtNodeStep.trans {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    {Nd Nd' Nd'' : List Nat} {extra extra' : List Ivl} (hAR : ArenaReady s)
    (h1 : ExtNodeStep s mid Nd Nd' extra)
    (h2 : ExtNodeStep mid post Nd' Nd'' extra')
    (hextra : ∀ e ∈ extra', BoundedKey s mid Nd extra e.1 e.2) :
    ExtNodeStep s post Nd Nd'' extra := by
  refine ⟨R16Shards.NodeStep.trans hAR h1.step h2.step, ?_⟩
  intro o ho
  rcases mem_nodeExtents_zero_or_pos ho with rfl | hpos
  · exact Or.inl rfl
  · rcases h2.owned o ho with hz | ⟨j, hj, hin⟩ | hfresh
    · exact Or.inl hz
    · rcases List.mem_append.1 hj with hj_nd | hj_ex
      · rcases h1.owned j hj_nd with rfl | ⟨k, hk, hjk⟩ | hjfresh
        · dsimp [Inside] at hin hpos; omega
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hjk.1 hin.1, le_trans hin.2 hjk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hjfresh.1 hin.1,
            le_trans (le_trans hin.2 hjfresh.2) h2.step.hp_le⟩)
      · rcases hextra j hj_ex with h0 | ⟨k, hk, hjk⟩ | hjfresh
        · dsimp [Inside] at hin hpos; omega
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hjk.1 hin.1, le_trans hin.2 hjk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hjfresh.1 hin.1,
            le_trans (le_trans hin.2 hjfresh.2) h2.step.hp_le⟩)
    · exact Or.inr (Or.inr ⟨le_trans h1.step.hp_le hfresh.1, hfresh.2⟩)

theorem ExtNodeStep.of_mem_lt_hp {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {extra : List Ivl}
    (hstep : R16Shards.NodeStep s post Nd Nd)
    (hmem_lt : ∀ a : BitVec 64, a.toNat < globN s "heap_ptr" → post.memory a = s.memory a)
    (hAR : ArenaReady s) (hNd : NodeHeap s Nd) :
    ExtNodeStep s post Nd Nd extra := by
  refine ⟨hstep, nodeExtents_ownedGrows_of_pathBounded hstep ?_⟩
  intro n hn hk12 hlen_nz
  have hp_n := hNd.1 n hn
  have hn_in : Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
    rcases hp_n.2.1 with h1 | h2
    · exact h1
    · have := hp_n.2.2.1.2
      have := hAR.2.2.2.1
      have := hAR.2.2.2.2.1
      have hsep : heapLimit ≤ scratchStart := by decide
      obtain ⟨hsz, _, _⟩ := R16Shards.nodeSize_bounds (memW s n)
      dsimp [nodeIvl, Inside] at *; omega
  have hk12_s : memW s n = 1 ∨ memW s n = 2 := by
    rwa [← hstep.kinds n hn]
  have hsz56 : 56 ≤ nodeSize (memW s n) := by
    rcases hk12_s with h1 | h2
    · simp [nodeSize, h1]
    · simp [nodeSize, h2]
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhp_hi : globN s "heap_ptr" ≤ heapLimit := hAR.2.2.1
  dsimp [nodeIvl, Inside] at hn_in
  have hw_eq : ∀ off : Nat, off ≤ 40 → memW post (n + off) = memW s (n + off) := by
    intro off hoff
    have hlt64 : n + off < 2 ^ 64 := by omega
    unfold memW
    rw [hmem_lt (BitVec.ofNat 64 (n + off))
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; omega)]
  have hw32 := hw_eq 32 (by decide)
  have hw40 := hw_eq 40 (by decide)
  rw [hw40] at hlen_nz
  rw [hw32, hw40]
  left
  refine ⟨(memW s (n + 32), memW s (n + 40)), List.mem_append_left _ ?_, le_rfl, le_rfl⟩
  unfold nodeExtents
  exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, hk12_s, hlen_nz]⟩

theorem ExtNodeStep.of_modify_node {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {extra : List Ivl} {node : Nat}
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
    ExtNodeStep s post Nd Nd extra := by
  have hstep := R16Shards.nodeStep_modify_node ha hNd hnode hc hm hsh hba hbe hg
    hmem_other hnode_ext hnode_br hnode_path hnode_c16 hnode_v1 hnode_v3
  refine ⟨hstep, nodeExtents_ownedGrows_of_pathBounded hstep ?_⟩
  intro n hn hk12 hlen_nz
  have hk12_s : memW s n = 1 ∨ memW s n = 2 := by
    rwa [← hstep.kinds n hn]
  have hp_n := hNd.1 n hn
  have hn_ins := hp_n.2.2.1
  have hnode_ins := (hNd.1 node hnode).2.2.1
  have hsz56 : 56 ≤ nodeSize (memW s n) := by
    rcases hk12_s with h1 | h2
    · simp [nodeSize, h1]
    · simp [nodeSize, h2]
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp [nodeIvl, Inside] at hn_ins hnode_ins
  have hpath_eq : memW post (n + 32) = memW s (n + 32) ∧ memW post (n + 40) = memW s (n + 40) := by
    by_cases hne : n = node
    · subst hne; exact hnode_path hk12_s
    · have hd := hNd.2 n hn node hnode hne
      dsimp [Disj, nodeIvl] at hd
      obtain ⟨hsz_node, _, _⟩ := R16Shards.nodeSize_bounds (memW s node)
      have hw : ∀ off : Nat, off ≤ 40 → memW post (n + off) = memW s (n + off) := by
        intro off hoff
        have hlt64 : n + off < 2 ^ 64 := by omega
        unfold memW
        rw [hmem_other (BitVec.ofNat 64 (n + off))
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; omega)]
      exact ⟨hw 32 (by decide), hw 40 (by decide)⟩
  rw [hpath_eq.2] at hlen_nz
  rw [hpath_eq.1, hpath_eq.2]
  left
  refine ⟨(memW s (n + 32), memW s (n + 40)), List.mem_append_left _ ?_, le_rfl, le_rfl⟩
  unfold nodeExtents
  exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, hk12_s, hlen_nz]⟩

theorem extNodeStep_of_node_invalidate {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s) {Nd : List Nat} (hNd : NodeHeap s Nd) {extra : List Ivl}
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {retShape : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "node_invalidate") values =
      some (body, callee, retShape))
    (hroots : ∀ n ∈ (["nd"] : List String), RootIn Nd (locN (callEntryStateHOLFinite s callee) n))
    (hres : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1) :
    ∃ Nd_ni,
      ExtNodeStep s (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2 Nd Nd_ni extra ∧
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2.globals = s.globals := by
  let entry := callEntryStateHOLFinite s callee
  have hA_ent : ArenaReady entry := localsFree_arenaReady s callee (s.clock - 1) hA
  have hnt : (evaluateHOLFiniteState entry body).1 ≠ some .timeOut := by
    intro hto; rw [hto] at hres; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  have hiz := FunSpec.at_lookup EvmFrameSpecs.iz_node_invalidate s hcode values body callee retShape
    hl ⟨hA_ent, Nd, hNd, hroots, trivial⟩ hnt hres
  set post := (evaluateHOLFiniteState entry body).2
  let nd := locN entry "nd"
  have hnd_root : RootIn Nd nd := hroots "nd" (by simp)
  have hmem_unchanged : ∀ a : BitVec 64,
      a ≠ BitVec.ofNat 64 (nd + 8) → a ≠ BitVec.ofNat 64 (nd + 16) →
      a ≠ BitVec.ofNat 64 (nd + 24) → post.memory a = s.memory a := by
    intro a h8 h16 h24
    have hm := congrArg (fun st => st.memory a) hiz
    change post.memory a =
      (if a = BitVec.ofNat 64 (nd + 8) ∨ a = BitVec.ofNat 64 (nd + 16) ∨ a = BitVec.ofNat 64 (nd + 24)
       then HolWordLab.word 0 else entry.memory a) at hm
    rw [hm, if_neg]
    · rfl
    · rintro (h | h | h)
      · exact h8 h
      · exact h16 h
      · exact h24 h
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hsb_ge : 65536 ≤ sourceBase := by decide
  have hpath_unchanged : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) →
      memW post (n + 32) = memW s (n + 32) ∧ memW post (n + 40) = memW s (n + 40) := by
    intro n hn hk12
    have hp_n := hNd.1 n hn
    have hn_ins := hp_n.2.2.1
    have hsz56 : 56 ≤ nodeSize (memW s n) := by
      rcases hk12 with h1 | h2
      · simp [nodeSize, h1]
      · simp [nodeSize, h2]
    dsimp [nodeIvl, Inside] at hn_ins
    have hw : ∀ off : Nat, (off = 32 ∨ off = 40) → memW post (n + off) = memW s (n + off) := by
      intro off hoff
      have hlt64 : n + off < 2 ^ 64 := by omega
      have hlo : sourceBase ≤ n := hn_ins.1
      have hne_off : ∀ k : Nat, (k = 8 ∨ k = 16 ∨ k = 24) →
          BitVec.ofNat 64 (n + off) ≠ BitVec.ofNat 64 (nd + k) := by
        intro k hk heq
        have h1 := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at h1
        rcases hnd_root with hnd0 | hnd_in
        · rw [hnd0] at h1
          rw [Nat.zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
          omega
        · have hnd_ins := (hNd.1 nd hnd_in).2.2.1
          obtain ⟨hsz_nd, _, _⟩ := R16Shards.nodeSize_bounds (memW s nd)
          dsimp [nodeIvl, Inside] at hnd_ins
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
          by_cases hnn : n = nd
          · subst hnn; omega
          · have hd := hNd.2 n hn nd hnd_in hnn
            dsimp [Disj, nodeIvl] at hd
            omega
      unfold memW
      rw [hmem_unchanged _ (hne_off 8 (Or.inl rfl))
        (hne_off 16 (Or.inr (Or.inl rfl))) (hne_off 24 (Or.inr (Or.inr rfl)))]
    exact ⟨hw 32 (Or.inl rfl), hw 40 (Or.inr rfl)⟩
  have hkind_unchanged : ∀ n ∈ Nd, memW post n = memW s n := by
    intro n hn
    have hp_n := hNd.1 n hn
    have hn_ins := hp_n.2.2.1
    obtain ⟨hsz_n, _, _⟩ := R16Shards.nodeSize_bounds (memW s n)
    dsimp [nodeIvl, Inside] at hn_ins
    have hlt64 : n < 2 ^ 64 := by omega
    have hne_off : ∀ k : Nat, (k = 8 ∨ k = 16 ∨ k = 24) →
        BitVec.ofNat 64 n ≠ BitVec.ofNat 64 (nd + k) := by
      intro k hk heq
      have h1 := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at h1
      rcases hnd_root with hnd0 | hnd_in
      · rw [hnd0] at h1
        rw [Nat.zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
        omega
      · have hnd_ins := (hNd.1 nd hnd_in).2.2.1
        obtain ⟨hsz_nd, _, _⟩ := R16Shards.nodeSize_bounds (memW s nd)
        dsimp [nodeIvl, Inside] at hnd_ins
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
        by_cases hnn : n = nd
        · subst hnn; omega
        · have hd := hNd.2 n hn nd hnd_in hnn
          dsimp [Disj, nodeIvl] at hd
          omega
    unfold memW
    rw [hmem_unchanged _ (hne_off 8 (Or.inl rfl))
      (hne_off 16 (Or.inr (Or.inl rfl))) (hne_off 24 (Or.inr (Or.inr rfl)))]
  obtain ⟨Nd_ni, hstep_ni, _⟩ := R16Shards.nodeStep_of_nodeFn R16Shards.nf_node_invalidate
    s hcode hA hNd hl hroots trivial hres
  have hg_post : post.globals = s.globals := by
    have hg := congrArg (fun st => st.globals) hiz
    simpa [entry, callEntryStateHOLFinite] using hg
  refine ⟨Nd_ni, ⟨hstep_ni, nodeExtents_ownedGrows_of_pathBounded hstep_ni ?_⟩, hg_post⟩
  intro n hn hk12 hlen_nz
  have hhp_eq : globN post "heap_ptr" = globN s "heap_ptr" := by
    unfold globN; rw [hg_post]
  rcases hstep_ni.fresh n hn with hn_old | hfr
  · have hk12_s : memW s n = 1 ∨ memW s n = 2 := by
      rwa [← hkind_unchanged n hn_old]
    obtain ⟨hw32, hw40⟩ := hpath_unchanged n hn_old hk12_s
    rw [hw40] at hlen_nz
    rw [hw32, hw40]
    left
    refine ⟨(memW s (n + 32), memW s (n + 40)), List.mem_append_left _ ?_, le_rfl, le_rfl⟩
    unfold nodeExtents
    exact List.mem_flatMap.2 ⟨n, hn_old, by simp [nodePath, hk12_s, hlen_nz]⟩
  · exfalso
    change Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr") at hfr
    rw [hhp_eq] at hfr
    obtain ⟨hsz, _, _⟩ := R16Shards.nodeSize_bounds (memW post n)
    dsimp [nodeIvl, Inside] at hfr
    omega

private theorem m26_updW_ne {m : BitVec 64 → HolWordLab 64} {a b w : BitVec 64} (h : b ≠ a) :
    Wave8Contracts.M26.updW m a w b = m b := by
  simp [Wave8Contracts.M26.updW, h]

private theorem m26_updW_eq {m : BitVec 64 → HolWordLab 64} {a w : BitVec 64} :
    Wave8Contracts.M26.updW m a w a = .word w := by
  simp [Wave8Contracts.M26.updW]

theorem mem_lt_hp_of_frameOutside_nil {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (hframe : FrameOutside s post
      ((([] : List Nat).map fun n => nodeIvl s n) ++
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    ∀ a : BitVec 64, a.toNat % 8 = 0 → a.toNat < globN s "heap_ptr" → post.memory a = s.memory a := by
  intro a ha8 hlt
  have hhp_fm : globN s "heap_ptr" ≤ globN s "frame_mem_ptr" := by
    have h1 : globN s "heap_ptr" ≤ heapLimit := hAR.2.2.1
    have h2 : scratchStart ≤ globN s "frame_mem_ptr" := hAR.2.2.2.1
    have h3 : heapLimit ≤ scratchStart := by decide
    omega
  have hhp8 : globN s "heap_ptr" % 8 = 0 := hAR.2.2.2.2.2.2.1
  apply hframe a
  · intro i hi hhit
    simp only [List.map_nil, List.nil_append, List.mem_singleton] at hi
    subst hi
    dsimp [CellHits] at hhit
    omega
  · intro hhit
    dsimp [CellHits] at hhit
    omega

theorem extNodeStep_of_node_new_branch {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) {Nd : List Nat} (hNd : NodeHeap s Nd) {extra : List Ivl}
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_branch)).1) :
    let r := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_branch)).1
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_branch)).2
    ∃ br : BitVec 64,
      r = some (.returned (.val (.word br))) ∧
      br.toNat = globN s "heap_ptr" ∧
      br.toNat % 8 = 0 ∧
      globN post "heap_ptr" = br.toNat + 176 ∧
      memW post br.toNat = 3 ∧
      (∀ i < 16, memW post (br.toNat + 32 + 8 * i) = 0) ∧
      memW post (br.toNat + 16) = 0 ∧
      memW post (br.toNat + 168) = 0 ∧
      ExtNodeStep s post Nd (br.toNat :: Nd) extra := by
  intro r post
  obtain ⟨_, _, _, br, hr, hbr_eq, hbr_al, hhp_post, hmw0, hch, hmw16, hmw168, hstep_all⟩ :=
    R16Shards.node_new_branch_spec s hcode hAR hres
  have hstep := hstep_all Nd hNd
  have hNd_nil : NodeHeap s [] := And.intro (fun _ h => nomatch h) (fun _ h => nomatch h)
  have hstep_nil := hstep_all [] hNd_nil
  have hmem_lt := mem_lt_hp_of_frameOutside_nil hAR hstep_nil.frame
  refine ⟨br, hr, hbr_eq, hbr_al, hhp_post, hmw0, hch, hmw16, hmw168, hstep, ?_⟩
  apply nodeExtents_ownedGrows_of_pathBounded hstep
  intro n hn hk12 hlen_nz
  rcases List.mem_cons.1 hn with rfl | hn_old
  · rw [hmw0] at hk12; rcases hk12 with h | h <;> cases h
  · have hp_n := hNd.1 n hn_old
    have hn8 : n % 8 = 0 := hp_n.2.2.2.1.1
    have hn_in : Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
      rcases hp_n.2.1 with h1 | h2
      · exact h1
      · have := hp_n.2.2.1.2
        have := hAR.2.2.2.1
        have := hAR.2.2.2.2.1
        have hsep : heapLimit ≤ scratchStart := by decide
        obtain ⟨hsz, _, _⟩ := R16Shards.nodeSize_bounds (memW s n)
        dsimp [nodeIvl, Inside] at *; omega
    have hk12_s : memW s n = 1 ∨ memW s n = 2 := by rwa [← hstep.kinds n hn_old]
    have hsz56 : 56 ≤ nodeSize (memW s n) := by
      rcases hk12_s with h1 | h2
      · simp [nodeSize, h1]
      · simp [nodeSize, h2]
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hhp_hi : globN s "heap_ptr" ≤ heapLimit := hAR.2.2.1
    dsimp [nodeIvl, Inside] at hn_in
    have hw_eq : ∀ off : Nat, off ≤ 40 → off % 8 = 0 → memW post (n + off) = memW s (n + off) := by
      intro off hoff hoff8
      have hlt64 : n + off < 2 ^ 64 := by omega
      unfold memW
      rw [hmem_lt (BitVec.ofNat 64 (n + off))
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; omega)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; omega)]
    have hw32 := hw_eq 32 (by decide) (by decide)
    have hw40 := hw_eq 40 (by decide) (by decide)
    rw [hw40] at hlen_nz
    rw [hw32, hw40]
    left
    refine ⟨(memW s (n + 32), memW s (n + 40)), List.mem_append_left _ ?_, le_rfl, le_rfl⟩
    unfold nodeExtents
    exact List.mem_flatMap.2 ⟨n, hn_old, by simp [nodePath, hk12_s, hlen_nz]⟩

theorem extNodeStep_of_node_new_leaf {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) {Nd : List Nat} (hNd : NodeHeap s Nd) {extra : List Ivl}
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {retShape : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "node_new_leaf") values =
      some (body, callee, retShape))
    (hKey : KeyIn s Nd (locN (callEntryStateHOLFinite s callee) "nib")
      (locN (callEntryStateHOLFinite s callee) "nlen"))
    (hbk : BoundedKey s s Nd extra (locN (callEntryStateHOLFinite s callee) "nib")
      (locN (callEntryStateHOLFinite s callee) "nlen"))
    (hvlen : locN (callEntryStateHOLFinite s callee) "vlen" < 2 ^ 40)
    (hres : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1) :
    ∃ Nd',
      ExtNodeStep s (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2 Nd Nd' extra ∧
      ∀ v, (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned v) →
        ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat := by
  let entry := callEntryStateHOLFinite s callee
  have hKey_nil : KeyIn entry [] (locN entry "nib") (locN entry "nlen") := by
    rcases hKey with h0 | ⟨hnib, halloc, hins, _⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hnib, halloc, hins, fun _ h => nomatch h⟩
  have hNd_nil : NodeHeap s [] := And.intro (fun _ h => nomatch h) (fun _ h => nomatch h)
  obtain ⟨_, hstep_nil, _⟩ := R16Shards.nodeStep_of_nodeFn R16Shards.nf_node_new_leaf s hcode hAR hNd_nil hl
    (fun _ h => nomatch h) ⟨hKey_nil, hvlen⟩ hres
  obtain ⟨Nd', hstep, hret⟩ := R16Shards.nodeStep_of_nodeFn R16Shards.nf_node_new_leaf s hcode hAR hNd hl
    (fun _ h => nomatch h) ⟨hKey, hvlen⟩ hres
  have hmem_lt := mem_lt_hp_of_frameOutside_nil hAR hstep_nil.frame
  have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "node_new_leaf")
    _ _ _ _ _ values callee (by rw [hcode]; exact R16Shards.lookup_node_new_leaf) hl
  subst hsame
  have hhl_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_leaf") values =
      some (sourceFnBody Guest.Software.guestFn_node_new_leaf, callee, retShape) := by rwa [← hcode]
  obtain ⟨wnib, hlk_nib, hloc_nib⟩ := R16Shards.lookup_param_word R16Shards.lookup_node_new_leaf hhl_code
    [] "nib" [(ofString "nlen", .one), (ofString "vptr", .one), (ofString "vlen", .one)] rfl (by decide)
  obtain ⟨wnlen, hlk_nlen, hloc_nlen⟩ := R16Shards.lookup_param_word R16Shards.lookup_node_new_leaf hhl_code
    [(ofString "nib", .one)] "nlen" [(ofString "vptr", .one), (ofString "vlen", .one)] rfl (by decide)
  obtain ⟨wvptr, hlk_vptr, _⟩ := R16Shards.lookup_param_word R16Shards.lookup_node_new_leaf hhl_code
    [(ofString "nib", .one), (ofString "nlen", .one)] "vptr" [(ofString "vlen", .one)] rfl (by decide)
  obtain ⟨wvlen, hlk_vlen, _⟩ := R16Shards.lookup_param_word R16Shards.lookup_node_new_leaf hhl_code
    [(ofString "nib", .one), (ofString "nlen", .one), (ofString "vptr", .one)] "vlen" [] rfl (by decide)
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ := Wave8Contracts.M26.arenaOK_globals entry hAR.2
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_leaf =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 64]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 0)]) (.const (BitVec.ofNat 64 1)))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 8)]) (.const (BitVec.ofNat 64 0)))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 16)]) (.const (BitVec.ofNat 64 0)))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 24)]) (.const (BitVec.ofNat 64 0)))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 32)]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 40)]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 48)]) (.var .local (ofString "vptr")))
                      (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 56)]) (.var .local (ofString "vlen")))
                        (.return (.var .local (ofString "nd"))))))))))) := rfl
  have hres' : Resumes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_node_new_leaf)).1 := hres
  rw [hbody] at hres'
  obtain ⟨avals, abody, acallee, aret, _, hargs, ahl, hexn | ⟨arv, apost, harun, _, _, _, hp_eq⟩⟩ :=
    R16Shards.decCall_resumes_inv hres'
  · obtain ⟨eid, ev, ha_exn, hne_trap, _⟩ := hexn
    have hsame_a := lookupCodeHOLFinite_installed_body entry.code.lookup (ofString "alloc")
      _ _ _ _ _ avals acallee (by change s.code.lookup _ = _; rw [hcode]; exact lookup_alloc) ahl
    subst hsame_a
    obtain ⟨_, hret_a⟩ := R16Shards.alloc_body_resumes_eq_returned (callEntryStateHOLFinite entry acallee) hcode
      (by rw [ha_exn]; exact Or.inr ⟨eid, ev, rfl, hne_trap⟩)
    rw [ha_exn] at hret_a; cases hret_a
  · have havals : avals = [.val (.word 64)] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simpa [evalListHOLExact, evalHOLExact] using hargs.symm
    subst havals
    have ahl_exact := pan_one_word_lookup entry.code.lookup (ofString "alloc") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_alloc) 64 (by change s.code.lookup _ = _; rw [hcode]; exact lookup_alloc)
    rw [ahl_exact] at ahl
    obtain ⟨hbody_a, hrest_a⟩ := Prod.mk.inj (Option.some.inj ahl.symm)
    obtain ⟨hcal_a, hret_a⟩ := Prod.mk.inj hrest_a
    subst hbody_a hcal_a hret_a
    have hn_ent : (callEntryStateHOLFinite entry (HolFiniteMapExact.empty.update (ofString "n", .val (.word 64)))).locals.lookup
        (ofString "n") = some (.val (.word 64)) := by
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have harun_info := Wave8Contracts.M26.alloc_body_run
      (callEntryStateHOLFinite entry (HolFiniteMapExact.empty.update (ofString "n", .val (.word 64))))
      hp 64 hcode hhp hn_ent arv (by rw [harun])
    rw [harun] at harun_info
    obtain ⟨rfl, hcmp1, hcmp2, hapost_eq⟩ := harun_info
    dsimp only at hapost_eq
    set q : BitVec 64 := (hp + (64 + 7)) &&& ((0 : BitVec 64) - 8)
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hAR.2.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hAR.2.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, _, _⟩ := Wave8Contracts.M26.alloc_arith hp 64 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = hp.toNat + ((64 : BitVec 64).toNat + 7) / 8 * 8 at hq_eq
    have h64 : ((64 : BitVec 64).toNat + 7) / 8 * 8 = 64 := by decide
    rw [h64] at hq_eq
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hhp_add : ∀ k : Nat, k ≤ 64 →
        hp + BitVec.ofNat 64 k = BitVec.ofNat 64 (hp.toNat + k) ∧
        (hp + BitVec.ofNat 64 k).toNat = hp.toNat + k := by
      intro k hk
      have hlt : hp.toNat + k < 2 ^ 64 := by omega
      have heq : hp + BitVec.ofNat 64 k = BitVec.ofNat 64 (hp.toNat + k) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]⟩
    set s0 := setVarHOLFinite (ofString "nd") (.val (.word hp)) { apost with locals := entry.locals }
    have hs0_nd : s0.locals.lookup (ofString "nd") = some (.val (.word hp)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs0_nib : s0.locals.lookup (ofString "nib") = some (.val (.word wnib)) := by
      simp [s0, entry, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_nib,
        show ofString "nd" ≠ ofString "nib" by decide]
    have hs0_nlen : s0.locals.lookup (ofString "nlen") = some (.val (.word wnlen)) := by
      simp [s0, entry, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_nlen,
        show ofString "nd" ≠ ofString "nlen" by decide]
    have hs0_vptr : s0.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) := by
      simp [s0, entry, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_vptr,
        show ofString "nd" ≠ ofString "vptr" by decide]
    have hs0_vlen : s0.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) := by
      simp [s0, entry, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_vlen,
        show ofString "nd" ≠ ofString "vlen" by decide]
    have hs0_dom : ∀ k : Nat, k < 64 → k % 8 = 0 → s0.memaddrs (hp + BitVec.ofNat 64 k) := by
      intro k hk hk8
      have hma : s0.memaddrs = ordinaryDomain := by
        simp [s0, setVarHOLFinite]; rw [hapost_eq]; exact hAR.1.memaddrs
      rw [hma, (hhp_add k (by omega)).1]
      change q.toNat ≤ heapLimit at hq_hi
      have hhe_ge : heapLimit ≤ heapEnd := by decide
      have hsb_lo : sourceBase ≤ hp.toNat := by
        rw [hhp_eq]; change sourceBase ≤ globN s "heap_ptr"; exact hAR.2.1
      exact Wave8Contracts.M26.ordinaryDomain_of_nat (hp.toNat + k)
        (by omega) (by omega) (by omega)
    have step_store_const : ∀ (st : PanSemStateFiniteExact 64 F) (k c : Nat),
        st.locals = s0.locals → st.memaddrs = s0.memaddrs → k < 64 → k % 8 = 0 →
        evaluateHOLFiniteState st
          (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)])
            (.const (BitVec.ofNat 64 c))) =
          (none, { st with memory := Wave8Contracts.M26.updW st.memory (hp + BitVec.ofNat 64 k) (BitVec.ofNat 64 c) }) := by
      intro st k c hloc hma hk hk8
      have hnd : st.locals.lookup (ofString "nd") = some (.val (.word hp)) := by rw [hloc]; exact hs0_nd
      have hdom : st.memaddrs (hp + BitVec.ofNat 64 k) := by rw [hma]; exact hs0_dom k hk hk8
      rw [evaluateHOLFiniteState_store]
      have hd : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)]) =
          some (.val (.word (hp + BitVec.ofNat 64 k))) := by
        simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord, valueWord, wordOpHOL, wordOp]
      have he : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.const (BitVec.ofNat 64 c)) = some (.val (.word (BitVec.ofNat 64 c))) := rfl
      rw [hd, he]
      simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]
      rfl
    have step_store_var : ∀ (st : PanSemStateFiniteExact 64 F) (k : Nat) (nm : String) (w : BitVec 64),
        st.locals = s0.locals → st.memaddrs = s0.memaddrs → k < 64 → k % 8 = 0 →
        s0.locals.lookup (ofString nm) = some (.val (.word w)) →
        evaluateHOLFiniteState st
          (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)])
            (.var .local (ofString nm))) =
          (none, { st with memory := Wave8Contracts.M26.updW st.memory (hp + BitVec.ofNat 64 k) w }) := by
      intro st k nm w hloc hma hk hk8 hnm
      have hnd : st.locals.lookup (ofString "nd") = some (.val (.word hp)) := by rw [hloc]; exact hs0_nd
      have hnm' : st.locals.lookup (ofString nm) = some (.val (.word w)) := by rw [hloc]; exact hnm
      have hdom : st.memaddrs (hp + BitVec.ofNat 64 k) := by rw [hma]; exact hs0_dom k hk hk8
      rw [evaluateHOLFiniteState_store]
      have hd : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)]) =
          some (.val (.word (hp + BitVec.ofNat 64 k))) := by
        simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord, valueWord, wordOpHOL, wordOp]
      have he : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.var .local (ofString nm)) = some (.val (.word w)) := hnm'
      rw [hd, he]
      simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]
      rfl
    set M8 :=
      Wave8Contracts.M26.updW
        (Wave8Contracts.M26.updW
          (Wave8Contracts.M26.updW
            (Wave8Contracts.M26.updW
              (Wave8Contracts.M26.updW
                (Wave8Contracts.M26.updW
                  (Wave8Contracts.M26.updW
                    (Wave8Contracts.M26.updW entry.memory (hp + BitVec.ofNat 64 0) (BitVec.ofNat 64 1))
                    (hp + BitVec.ofNat 64 8) (BitVec.ofNat 64 0))
                  (hp + BitVec.ofNat 64 16) (BitVec.ofNat 64 0))
                (hp + BitVec.ofNat 64 24) (BitVec.ofNat 64 0))
              (hp + BitVec.ofNat 64 32) wnib)
            (hp + BitVec.ofNat 64 40) wnlen)
          (hp + BitVec.ofNat 64 48) wvptr)
        (hp + BitVec.ofNat 64 56) wvlen
    have hs0_mem_eq : s0.memory = entry.memory := by simp [s0, setVarHOLFinite]; rw [hapost_eq]; rfl
    have hcont_eval : evaluateHOLFiniteState s0
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 0)]) (.const (BitVec.ofNat 64 1)))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 8)]) (.const (BitVec.ofNat 64 0)))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 16)]) (.const (BitVec.ofNat 64 0)))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 24)]) (.const (BitVec.ofNat 64 0)))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 32)]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 40)]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 48)]) (.var .local (ofString "vptr")))
                      (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 56)]) (.var .local (ofString "vlen")))
                        (.return (.var .local (ofString "nd"))))))))))) =
        (some (.returned (.val (.word hp))), emptyLocalsHOLFinite { s0 with memory := M8 }) := by
      rw [evaluateHOLFiniteState_seq_line780, step_store_const s0 0 1 rfl rfl (by decide) (by decide)]
      dsimp only
      set m1 := { s0 with memory := Wave8Contracts.M26.updW s0.memory (hp + BitVec.ofNat 64 0) (BitVec.ofNat 64 1) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_const m1 8 0 rfl rfl (by decide) (by decide)]
      dsimp only
      set m2 := { m1 with memory := Wave8Contracts.M26.updW m1.memory (hp + BitVec.ofNat 64 8) (BitVec.ofNat 64 0) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_const m2 16 0 rfl rfl (by decide) (by decide)]
      dsimp only
      set m3 := { m2 with memory := Wave8Contracts.M26.updW m2.memory (hp + BitVec.ofNat 64 16) (BitVec.ofNat 64 0) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_const m3 24 0 rfl rfl (by decide) (by decide)]
      dsimp only
      set m4 := { m3 with memory := Wave8Contracts.M26.updW m3.memory (hp + BitVec.ofNat 64 24) (BitVec.ofNat 64 0) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_var m4 32 "nib" wnib rfl rfl (by decide) (by decide) hs0_nib]
      dsimp only
      set m5 := { m4 with memory := Wave8Contracts.M26.updW m4.memory (hp + BitVec.ofNat 64 32) wnib }
      rw [evaluateHOLFiniteState_seq_line780, step_store_var m5 40 "nlen" wnlen rfl rfl (by decide) (by decide) hs0_nlen]
      dsimp only
      set m6 := { m5 with memory := Wave8Contracts.M26.updW m5.memory (hp + BitVec.ofNat 64 40) wnlen }
      rw [evaluateHOLFiniteState_seq_line780, step_store_var m6 48 "vptr" wvptr rfl rfl (by decide) (by decide) hs0_vptr]
      dsimp only
      set m7 := { m6 with memory := Wave8Contracts.M26.updW m6.memory (hp + BitVec.ofNat 64 48) wvptr }
      rw [evaluateHOLFiniteState_seq_line780, step_store_var m7 56 "vlen" wvlen rfl rfl (by decide) (by decide) hs0_vlen]
      dsimp only
      set m8 := { m7 with memory := Wave8Contracts.M26.updW m7.memory (hp + BitVec.ofNat 64 56) wvlen }
      have hm8_eq : m8 = { s0 with memory := M8 } := by
        dsimp only [m8, m7, m6, m5, m4, m3, m2, m1, M8]
        rw [hs0_mem_eq]
      rw [hm8_eq, evaluateHOLFiniteState_return]
      simp [evalHOLExact, hs0_nd, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    set post := (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_node_new_leaf)).2
    have hpost_mem : post.memory = M8 := by
      change (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_node_new_leaf)).2.memory = M8
      rw [hbody, hp_eq, hcont_eval]; rfl
    have hpost_hp : globN post "heap_ptr" = q.toNat := by
      have hpost_glob : post.globals = entry.globals.update (ofString "heap_ptr", .val (.word q)) := by
        change (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_node_new_leaf)).2.globals = _
        rw [hbody, hp_eq, hcont_eval]
        simp [emptyLocalsHOLFinite, s0, setVarHOLFinite]; rw [hapost_eq]; rfl
      unfold globN; rw [hpost_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hne_off : ∀ j k : Nat, j ≤ 56 → k ≤ 56 → j ≠ k → hp + BitVec.ofNat 64 j ≠ hp + BitVec.ofNat 64 k := by
      intro j k hj hk hjk heq
      have h1 := (hhp_add j (by omega)).2
      have h2 := (hhp_add k (by omega)).2
      rw [heq] at h1; omega
    have hmw_32 : memW post (hp.toNat + 32) = locN entry "nib" := by
      have ha : BitVec.ofNat 64 (hp.toNat + 32) = hp + BitVec.ofNat 64 32 := (hhp_add 32 (by decide)).1.symm
      unfold memW; rw [ha, hloc_nib entry rfl, hpost_mem]
      dsimp only [M8]
      rw [m26_updW_ne (hne_off 32 56 (by decide) (by decide) (by decide)),
          m26_updW_ne (hne_off 32 48 (by decide) (by decide) (by decide)),
          m26_updW_ne (hne_off 32 40 (by decide) (by decide) (by decide)),
          m26_updW_eq]
    have hmw_40 : memW post (hp.toNat + 40) = locN entry "nlen" := by
      have ha : BitVec.ofNat 64 (hp.toNat + 40) = hp + BitVec.ofNat 64 40 := (hhp_add 40 (by decide)).1.symm
      unfold memW; rw [ha, hloc_nlen entry rfl, hpost_mem]
      dsimp only [M8]
      rw [m26_updW_ne (hne_off 40 56 (by decide) (by decide) (by decide)),
          m26_updW_ne (hne_off 40 48 (by decide) (by decide) (by decide)),
          m26_updW_eq]
    refine ⟨Nd', ⟨hstep, nodeExtents_ownedGrows_of_pathBounded hstep ?_⟩, hret⟩
    intro n hn hk12 hlen_nz
    rcases hstep.fresh n hn with hn_old | hfr
    · have hp_n := hNd.1 n hn_old
      have hn8 : n % 8 = 0 := hp_n.2.2.2.1.1
      have hn_in : Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
        rcases hp_n.2.1 with h1 | h2
        · exact h1
        · have := hp_n.2.2.1.2
          have := hAR.2.2.2.1
          have := hAR.2.2.2.2.1
          have hsep : heapLimit ≤ scratchStart := by decide
          obtain ⟨hsz, _, _⟩ := R16Shards.nodeSize_bounds (memW s n)
          dsimp [nodeIvl, Inside] at *; omega
      have hk12_s : memW s n = 1 ∨ memW s n = 2 := by rwa [← hstep.kinds n hn_old]
      have hsz56 : 56 ≤ nodeSize (memW s n) := by
        rcases hk12_s with h1 | h2
        · simp [nodeSize, h1]
        · simp [nodeSize, h2]
      have hhp_hi_s : globN s "heap_ptr" ≤ heapLimit := hAR.2.2.1
      dsimp [nodeIvl, Inside] at hn_in
      have hw_eq : ∀ off : Nat, off ≤ 40 → off % 8 = 0 → memW post (n + off) = memW s (n + off) := by
        intro off hoff hoff8
        have hlt64 : n + off < 2 ^ 64 := by omega
        unfold memW
        rw [hmem_lt (BitVec.ofNat 64 (n + off))
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; omega)
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; omega)]
      have hw32 := hw_eq 32 (by decide) (by decide)
      have hw40 := hw_eq 40 (by decide) (by decide)
      rw [hw40] at hlen_nz
      rw [hw32, hw40]
      left
      refine ⟨(memW s (n + 32), memW s (n + 40)), List.mem_append_left _ ?_, le_rfl, le_rfl⟩
      unfold nodeExtents
      exact List.mem_flatMap.2 ⟨n, hn_old, by simp [nodePath, hk12_s, hlen_nz]⟩
    · have hhp_s_eq : globN s "heap_ptr" = hp.toNat := hhp_eq.symm
      change Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr") at hfr
      rw [hhp_s_eq, hpost_hp, hq_eq] at hfr
      have hsz64_post : nodeSize (memW post n) = 64 ∨ nodeSize (memW post n) = 56 := by
        rcases hk12 with h1 | h2
        · left; simp [nodeSize, h1]
        · right; simp [nodeSize, h2]
      have hn8_post : n % 8 = 0 := (hstep.heap.1 n hn).2.2.2.1.1
      dsimp [nodeIvl, Inside] at hfr
      have hn_eq : n = hp.toNat := by
        by_cases hne_n : n = hp.toNat
        · exact hne_n
        · have hn_ge8 : hp.toNat + 8 ≤ n := by omega
          have hmw_n : memW post n = 0 := by
            have hn_eq56 : n = hp.toNat + 8 := by omega
            subst hn_eq56
            have ha : BitVec.ofNat 64 (hp.toNat + 8) = hp + BitVec.ofNat 64 8 := (hhp_add 8 (by decide)).1.symm
            unfold memW; rw [ha, hpost_mem]
            dsimp only [M8]
            rw [m26_updW_ne (hne_off 8 56 (by decide) (by decide) (by decide)),
                m26_updW_ne (hne_off 8 48 (by decide) (by decide) (by decide)),
                m26_updW_ne (hne_off 8 40 (by decide) (by decide) (by decide)),
                m26_updW_ne (hne_off 8 32 (by decide) (by decide) (by decide)),
                m26_updW_ne (hne_off 8 24 (by decide) (by decide) (by decide)),
                m26_updW_ne (hne_off 8 16 (by decide) (by decide) (by decide)),
                m26_updW_eq]
            rfl
          rw [hmw_n] at hk12
          omega
      subst hn_eq
      rw [hmw_40] at hlen_nz
      rw [hmw_32, hmw_40]
      have hbk' := hbk.mono_hp (post := post) hstep.hp_le
      rcases hbk' with h0 | hok
      · exact absurd h0 hlen_nz
      · exact hok

theorem extNodeStep_of_node_new_ext {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) {Nd : List Nat} (hNd : NodeHeap s Nd) {extra : List Ivl}
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {retShape : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "node_new_ext") values =
      some (body, callee, retShape))
    (hroots : ∀ n ∈ (["child"] : List String), RootIn Nd (locN (callEntryStateHOLFinite s callee) n))
    (hKey : KeyIn s Nd (locN (callEntryStateHOLFinite s callee) "nib")
      (locN (callEntryStateHOLFinite s callee) "nlen"))
    (hbk : BoundedKey s s Nd extra (locN (callEntryStateHOLFinite s callee) "nib")
      (locN (callEntryStateHOLFinite s callee) "nlen"))
    (hres : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1) :
    ∃ Nd',
      ExtNodeStep s (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2 Nd Nd' extra ∧
      ∀ v, (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned v) →
        ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat := by
  let entry := callEntryStateHOLFinite s callee
  obtain ⟨Nd', hstep, hret⟩ := R16Shards.nodeStep_of_nodeFn R16Shards.nf_node_new_ext s hcode hAR hNd hl
    hroots hKey hres
  have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "node_new_ext")
    _ _ _ _ _ values callee (by rw [hcode]; exact R16Shards.lookup_node_new_ext) hl
  subst hsame
  have hhl_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_ext") values =
      some (sourceFnBody Guest.Software.guestFn_node_new_ext, callee, retShape) := by rwa [← hcode]
  obtain ⟨wnib, hlk_nib, hloc_nib⟩ := R16Shards.lookup_param_word R16Shards.lookup_node_new_ext hhl_code
    [] "nib" [(ofString "nlen", .one), (ofString "child", .one)] rfl (by decide)
  obtain ⟨wnlen, hlk_nlen, hloc_nlen⟩ := R16Shards.lookup_param_word R16Shards.lookup_node_new_ext hhl_code
    [(ofString "nib", .one)] "nlen" [(ofString "child", .one)] rfl (by decide)
  obtain ⟨wchild, hlk_child, _⟩ := R16Shards.lookup_param_word R16Shards.lookup_node_new_ext hhl_code
    [(ofString "nib", .one), (ofString "nlen", .one)] "child" [] rfl (by decide)
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ := Wave8Contracts.M26.arenaOK_globals entry hAR.2
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_ext =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 56]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 0)]) (.const (BitVec.ofNat 64 2)))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 8)]) (.const (BitVec.ofNat 64 0)))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 16)]) (.const (BitVec.ofNat 64 0)))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 24)]) (.const (BitVec.ofNat 64 0)))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 32)]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 40)]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 48)]) (.var .local (ofString "child")))
                      (.return (.var .local (ofString "nd")))))))))) := rfl
  have hres' : Resumes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_node_new_ext)).1 := hres
  rw [hbody] at hres'
  obtain ⟨avals, abody, acallee, aret, _, hargs, ahl, hexn | ⟨arv, apost, harun, _, _, _, hp_eq⟩⟩ :=
    R16Shards.decCall_resumes_inv hres'
  · obtain ⟨eid, ev, ha_exn, hne_trap, _⟩ := hexn
    have hsame_a := lookupCodeHOLFinite_installed_body entry.code.lookup (ofString "alloc")
      _ _ _ _ _ avals acallee (by change s.code.lookup _ = _; rw [hcode]; exact lookup_alloc) ahl
    subst hsame_a
    obtain ⟨_, hret_a⟩ := R16Shards.alloc_body_resumes_eq_returned (callEntryStateHOLFinite entry acallee) hcode
      (by rw [ha_exn]; exact Or.inr ⟨eid, ev, rfl, hne_trap⟩)
    rw [ha_exn] at hret_a; cases hret_a
  · have havals : avals = [.val (.word 56)] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simpa [evalListHOLExact, evalHOLExact] using hargs.symm
    subst havals
    have ahl_exact := pan_one_word_lookup entry.code.lookup (ofString "alloc") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_alloc) 56 (by change s.code.lookup _ = _; rw [hcode]; exact lookup_alloc)
    rw [ahl_exact] at ahl
    obtain ⟨hbody_a, hrest_a⟩ := Prod.mk.inj (Option.some.inj ahl.symm)
    obtain ⟨hcal_a, hret_a⟩ := Prod.mk.inj hrest_a
    subst hbody_a hcal_a hret_a
    have hn_ent : (callEntryStateHOLFinite entry (HolFiniteMapExact.empty.update (ofString "n", .val (.word 56)))).locals.lookup
        (ofString "n") = some (.val (.word 56)) := by
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have harun_info := Wave8Contracts.M26.alloc_body_run
      (callEntryStateHOLFinite entry (HolFiniteMapExact.empty.update (ofString "n", .val (.word 56))))
      hp 56 hcode hhp hn_ent arv (by rw [harun])
    rw [harun] at harun_info
    obtain ⟨rfl, hcmp1, hcmp2, hapost_eq⟩ := harun_info
    dsimp only at hapost_eq
    set q : BitVec 64 := (hp + (56 + 7)) &&& ((0 : BitVec 64) - 8)
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hAR.2.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hAR.2.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, _, _⟩ := Wave8Contracts.M26.alloc_arith hp 56 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = hp.toNat + ((56 : BitVec 64).toNat + 7) / 8 * 8 at hq_eq
    have h56 : ((56 : BitVec 64).toNat + 7) / 8 * 8 = 56 := by decide
    rw [h56] at hq_eq
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hhp_add : ∀ k : Nat, k ≤ 56 →
        hp + BitVec.ofNat 64 k = BitVec.ofNat 64 (hp.toNat + k) ∧
        (hp + BitVec.ofNat 64 k).toNat = hp.toNat + k := by
      intro k hk
      have hlt : hp.toNat + k < 2 ^ 64 := by omega
      have heq : hp + BitVec.ofNat 64 k = BitVec.ofNat 64 (hp.toNat + k) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]⟩
    set s0 := setVarHOLFinite (ofString "nd") (.val (.word hp)) { apost with locals := entry.locals }
    have hs0_nd : s0.locals.lookup (ofString "nd") = some (.val (.word hp)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs0_nib : s0.locals.lookup (ofString "nib") = some (.val (.word wnib)) := by
      simp [s0, entry, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_nib,
        show ofString "nd" ≠ ofString "nib" by decide]
    have hs0_nlen : s0.locals.lookup (ofString "nlen") = some (.val (.word wnlen)) := by
      simp [s0, entry, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_nlen,
        show ofString "nd" ≠ ofString "nlen" by decide]
    have hs0_child : s0.locals.lookup (ofString "child") = some (.val (.word wchild)) := by
      simp [s0, entry, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_child,
        show ofString "nd" ≠ ofString "child" by decide]
    have hs0_dom : ∀ k : Nat, k < 56 → k % 8 = 0 → s0.memaddrs (hp + BitVec.ofNat 64 k) := by
      intro k hk hk8
      have hma : s0.memaddrs = ordinaryDomain := by
        simp [s0, setVarHOLFinite]; rw [hapost_eq]; exact hAR.1.memaddrs
      rw [hma, (hhp_add k (by omega)).1]
      change q.toNat ≤ heapLimit at hq_hi
      have hhe_ge : heapLimit ≤ heapEnd := by decide
      have hsb_lo : sourceBase ≤ hp.toNat := by
        rw [hhp_eq]; change sourceBase ≤ globN s "heap_ptr"; exact hAR.2.1
      exact Wave8Contracts.M26.ordinaryDomain_of_nat (hp.toNat + k)
        (by omega) (by omega) (by omega)
    have step_store_const : ∀ (st : PanSemStateFiniteExact 64 F) (k c : Nat),
        st.locals = s0.locals → st.memaddrs = s0.memaddrs → k < 56 → k % 8 = 0 →
        evaluateHOLFiniteState st
          (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)])
            (.const (BitVec.ofNat 64 c))) =
          (none, { st with memory := Wave8Contracts.M26.updW st.memory (hp + BitVec.ofNat 64 k) (BitVec.ofNat 64 c) }) := by
      intro st k c hloc hma hk hk8
      have hnd : st.locals.lookup (ofString "nd") = some (.val (.word hp)) := by rw [hloc]; exact hs0_nd
      have hdom : st.memaddrs (hp + BitVec.ofNat 64 k) := by rw [hma]; exact hs0_dom k hk hk8
      rw [evaluateHOLFiniteState_store]
      have hd : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)]) =
          some (.val (.word (hp + BitVec.ofNat 64 k))) := by
        simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord, valueWord, wordOpHOL, wordOp]
      have he : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.const (BitVec.ofNat 64 c)) = some (.val (.word (BitVec.ofNat 64 c))) := rfl
      rw [hd, he]
      simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]
      rfl
    have step_store_var : ∀ (st : PanSemStateFiniteExact 64 F) (k : Nat) (nm : String) (w : BitVec 64),
        st.locals = s0.locals → st.memaddrs = s0.memaddrs → k < 56 → k % 8 = 0 →
        s0.locals.lookup (ofString nm) = some (.val (.word w)) →
        evaluateHOLFiniteState st
          (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)])
            (.var .local (ofString nm))) =
          (none, { st with memory := Wave8Contracts.M26.updW st.memory (hp + BitVec.ofNat 64 k) w }) := by
      intro st k nm w hloc hma hk hk8 hnm
      have hnd : st.locals.lookup (ofString "nd") = some (.val (.word hp)) := by rw [hloc]; exact hs0_nd
      have hnm' : st.locals.lookup (ofString nm) = some (.val (.word w)) := by rw [hloc]; exact hnm
      have hdom : st.memaddrs (hp + BitVec.ofNat 64 k) := by rw [hma]; exact hs0_dom k hk hk8
      rw [evaluateHOLFiniteState_store]
      have hd : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)]) =
          some (.val (.word (hp + BitVec.ofNat 64 k))) := by
        simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord, valueWord, wordOpHOL, wordOp]
      have he : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.var .local (ofString nm)) = some (.val (.word w)) := hnm'
      rw [hd, he]
      simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]
      rfl
    set M7 :=
      Wave8Contracts.M26.updW
        (Wave8Contracts.M26.updW
          (Wave8Contracts.M26.updW
            (Wave8Contracts.M26.updW
              (Wave8Contracts.M26.updW
                (Wave8Contracts.M26.updW
                  (Wave8Contracts.M26.updW entry.memory (hp + BitVec.ofNat 64 0) (BitVec.ofNat 64 2))
                  (hp + BitVec.ofNat 64 8) (BitVec.ofNat 64 0))
                (hp + BitVec.ofNat 64 16) (BitVec.ofNat 64 0))
              (hp + BitVec.ofNat 64 24) (BitVec.ofNat 64 0))
            (hp + BitVec.ofNat 64 32) wnib)
          (hp + BitVec.ofNat 64 40) wnlen)
        (hp + BitVec.ofNat 64 48) wchild
    have hs0_mem_eq : s0.memory = entry.memory := by simp [s0, setVarHOLFinite]; rw [hapost_eq]; rfl
    have hcont_eval : evaluateHOLFiniteState s0
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 0)]) (.const (BitVec.ofNat 64 2)))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 8)]) (.const (BitVec.ofNat 64 0)))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 16)]) (.const (BitVec.ofNat 64 0)))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 24)]) (.const (BitVec.ofNat 64 0)))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 32)]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 40)]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 48)]) (.var .local (ofString "child")))
                      (.return (.var .local (ofString "nd")))))))))) =
        (some (.returned (.val (.word hp))), emptyLocalsHOLFinite { s0 with memory := M7 }) := by
      rw [evaluateHOLFiniteState_seq_line780, step_store_const s0 0 2 rfl rfl (by decide) (by decide)]
      dsimp only
      set m1 := { s0 with memory := Wave8Contracts.M26.updW s0.memory (hp + BitVec.ofNat 64 0) (BitVec.ofNat 64 2) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_const m1 8 0 rfl rfl (by decide) (by decide)]
      dsimp only
      set m2 := { m1 with memory := Wave8Contracts.M26.updW m1.memory (hp + BitVec.ofNat 64 8) (BitVec.ofNat 64 0) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_const m2 16 0 rfl rfl (by decide) (by decide)]
      dsimp only
      set m3 := { m2 with memory := Wave8Contracts.M26.updW m2.memory (hp + BitVec.ofNat 64 16) (BitVec.ofNat 64 0) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_const m3 24 0 rfl rfl (by decide) (by decide)]
      dsimp only
      set m4 := { m3 with memory := Wave8Contracts.M26.updW m3.memory (hp + BitVec.ofNat 64 24) (BitVec.ofNat 64 0) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_var m4 32 "nib" wnib rfl rfl (by decide) (by decide) hs0_nib]
      dsimp only
      set m5 := { m4 with memory := Wave8Contracts.M26.updW m4.memory (hp + BitVec.ofNat 64 32) wnib }
      rw [evaluateHOLFiniteState_seq_line780, step_store_var m5 40 "nlen" wnlen rfl rfl (by decide) (by decide) hs0_nlen]
      dsimp only
      set m6 := { m5 with memory := Wave8Contracts.M26.updW m5.memory (hp + BitVec.ofNat 64 40) wnlen }
      rw [evaluateHOLFiniteState_seq_line780, step_store_var m6 48 "child" wchild rfl rfl (by decide) (by decide) hs0_child]
      dsimp only
      set m7 := { m6 with memory := Wave8Contracts.M26.updW m6.memory (hp + BitVec.ofNat 64 48) wchild }
      have hm7_eq : m7 = { s0 with memory := M7 } := by
        dsimp only [m7, m6, m5, m4, m3, m2, m1, M7]
        rw [hs0_mem_eq]
      rw [hm7_eq, evaluateHOLFiniteState_return]
      simp [evalHOLExact, hs0_nd, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    set post := (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_node_new_ext)).2
    have hpost_mem : post.memory = M7 := by
      change (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_node_new_ext)).2.memory = M7
      rw [hbody, hp_eq, hcont_eval]; rfl
    have hpost_hp : globN post "heap_ptr" = q.toNat := by
      have hpost_glob : post.globals = entry.globals.update (ofString "heap_ptr", .val (.word q)) := by
        change (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_node_new_ext)).2.globals = _
        rw [hbody, hp_eq, hcont_eval]
        simp [emptyLocalsHOLFinite, s0, setVarHOLFinite]; rw [hapost_eq]; rfl
      unfold globN; rw [hpost_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hmem_lt : ∀ a : BitVec 64, a.toNat < globN s "heap_ptr" → post.memory a = s.memory a := by
      intro a hlt
      have hhp_ent_s : hp.toNat = globN s "heap_ptr" := hhp_eq
      have hne : ∀ k : Nat, k < 56 → a ≠ hp + BitVec.ofNat 64 k := by
        intro k hk heq
        have := (hhp_add k (by omega)).2
        rw [heq] at hlt; omega
      rw [hpost_mem]
      dsimp only [M7]
      rw [m26_updW_ne (hne 48 (by decide)),
          m26_updW_ne (hne 40 (by decide)),
          m26_updW_ne (hne 32 (by decide)),
          m26_updW_ne (hne 24 (by decide)),
          m26_updW_ne (hne 16 (by decide)),
          m26_updW_ne (hne 8 (by decide)),
          m26_updW_ne (hne 0 (by decide))]
      rfl
    have hne_off : ∀ j k : Nat, j ≤ 48 → k ≤ 48 → j ≠ k → hp + BitVec.ofNat 64 j ≠ hp + BitVec.ofNat 64 k := by
      intro j k hj hk hjk heq
      have h1 := (hhp_add j (by omega)).2
      have h2 := (hhp_add k (by omega)).2
      rw [heq] at h1; omega
    have hmw_32 : memW post (hp.toNat + 32) = locN entry "nib" := by
      have ha : BitVec.ofNat 64 (hp.toNat + 32) = hp + BitVec.ofNat 64 32 := (hhp_add 32 (by decide)).1.symm
      unfold memW; rw [ha, hloc_nib entry rfl, hpost_mem]
      dsimp only [M7]
      rw [m26_updW_ne (hne_off 32 48 (by decide) (by decide) (by decide)),
          m26_updW_ne (hne_off 32 40 (by decide) (by decide) (by decide)),
          m26_updW_eq]
    have hmw_40 : memW post (hp.toNat + 40) = locN entry "nlen" := by
      have ha : BitVec.ofNat 64 (hp.toNat + 40) = hp + BitVec.ofNat 64 40 := (hhp_add 40 (by decide)).1.symm
      unfold memW; rw [ha, hloc_nlen entry rfl, hpost_mem]
      dsimp only [M7]
      rw [m26_updW_ne (hne_off 40 48 (by decide) (by decide) (by decide)),
          m26_updW_eq]
    refine ⟨Nd', ⟨hstep, nodeExtents_ownedGrows_of_pathBounded hstep ?_⟩, hret⟩
    intro n hn hk12 hlen_nz
    rcases hstep.fresh n hn with hn_old | hfr
    · have hp_n := hNd.1 n hn_old
      have hn_in : Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
        rcases hp_n.2.1 with h1 | h2
        · exact h1
        · have := hp_n.2.2.1.2
          have := hAR.2.2.2.1
          have := hAR.2.2.2.2.1
          have hsep : heapLimit ≤ scratchStart := by decide
          obtain ⟨hsz, _, _⟩ := R16Shards.nodeSize_bounds (memW s n)
          dsimp [nodeIvl, Inside] at *; omega
      have hk12_s : memW s n = 1 ∨ memW s n = 2 := by rwa [← hstep.kinds n hn_old]
      have hsz56 : 56 ≤ nodeSize (memW s n) := by
        rcases hk12_s with h1 | h2
        · simp [nodeSize, h1]
        · simp [nodeSize, h2]
      have hhp_hi_s : globN s "heap_ptr" ≤ heapLimit := hAR.2.2.1
      dsimp [nodeIvl, Inside] at hn_in
      have hw_eq : ∀ off : Nat, off ≤ 40 → memW post (n + off) = memW s (n + off) := by
        intro off hoff
        have hlt64 : n + off < 2 ^ 64 := by omega
        unfold memW
        rw [hmem_lt (BitVec.ofNat 64 (n + off))
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; omega)]
      have hw32 := hw_eq 32 (by decide)
      have hw40 := hw_eq 40 (by decide)
      rw [hw40] at hlen_nz
      rw [hw32, hw40]
      left
      refine ⟨(memW s (n + 32), memW s (n + 40)), List.mem_append_left _ ?_, le_rfl, le_rfl⟩
      unfold nodeExtents
      exact List.mem_flatMap.2 ⟨n, hn_old, by simp [nodePath, hk12_s, hlen_nz]⟩
    · have hhp_s_eq : globN s "heap_ptr" = hp.toNat := hhp_eq.symm
      change Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr") at hfr
      rw [hhp_s_eq, hpost_hp, hq_eq] at hfr
      have hsz56_post : 56 ≤ nodeSize (memW post n) := by
        rcases hk12 with h1 | h2
        · simp [nodeSize, h1]
        · simp [nodeSize, h2]
      dsimp [nodeIvl, Inside] at hfr
      have hn_eq : n = hp.toNat := by omega
      subst hn_eq
      rw [hmw_40] at hlen_nz
      rw [hmw_32, hmw_40]
      have hbk' := hbk.mono_hp (post := post) hstep.hp_le
      rcases hbk' with h0 | hok
      · exact absurd h0 hlen_nz
      · exact hok

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
