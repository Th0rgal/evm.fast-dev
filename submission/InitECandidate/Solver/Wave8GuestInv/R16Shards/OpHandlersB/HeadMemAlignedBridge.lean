import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmGBody
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group04
import InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
import InitECandidate.Solver.GuestGlobalKeep
import InitECandidate.Solver.GuestFrameMemKeep
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M28.ww_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.zv_memzero
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs

/-! # `HeadMemAligned` as a frame-chain invariant through `run_frames`

`HeadMemAligned` (Group04) is a fact about the *head* frame only, so it is not preserved by
`finish_child` (which makes the parent the head) unless every frame on the chain carries the
corresponding fact. `HeadMemChainWF` is that chain-wide invariant:

* every frame `ec` on `evmChain s` has a 32-aligned memory length (`ec.1+32`) and an 8-aligned
  memory capacity (`ec.1+40`);
* the head frame's memory ends exactly at `frame_mem_ptr` (`mem + cap = frame_mem_ptr`);
* each parent's memory ends exactly at the frame-memory mark recorded in the child's
  continuation (`ch[i+1].1+24 + ch[i+1].1+40 = ch[i].2+56`), which `finish_child` restores
  into `frame_mem_ptr` via `frame_mem_release`.

This file proves the invariant implies `HeadMemAligned`, that it depends only on memory and
globals, entry establishment for a depth-0 chain, and `gbody_run_frames_aligned`: the
`run_frames` bound under `EvmInv ∧ HeadMemChainWF`, given aligned contracts of the four frame
functions (their unaligned versions in `ContractParts.C00` are not all proved). -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. The chain invariant -/

/-- Parent links: the memory of frame `b` (the parent of `a`) ends at `a`'s recorded mark. -/
def ChainLinks (m : Nat → Nat) : List Ivl → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => m (b.1 + 24) + m (b.1 + 40) = m (a.2 + 56) ∧ ChainLinks m (b :: rest)

def HeadMemChainWF {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ ec ∈ evmChain s, memW s (ec.1 + 32) % 32 = 0 ∧ memW s (ec.1 + 40) % 8 = 0) ∧
  memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr" ∧
  ChainLinks (memW s) (evmChain s)

theorem evmChain_cons {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evmChain s = (globN s "ev", globN s "cur_cont") ::
      (if memW s (globN s "cur_cont" + 16) = 0 then [] else
        evmChainFrom s maxChain (memW s (globN s "cur_cont"))
          (memW s (globN s "cur_cont" + 8))) := by
  simp only [evmChain, evmChainFrom]

theorem head_mem_evmChain {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
  rw [evmChain_cons]; exact List.mem_cons_self

/-! ### Local copies of the Group04 head-memory vocabulary

Re-stated verbatim from `R16Shards/OpHandlers/Group04.lean` (staging `345f0f06d`) so this file's
statements read standalone; each is proved definitionally equal to the Group04 original, so
results transfer in both directions with no edit to Group04. -/

def HeadMemAligned {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  memW s (globN s "ev" + 32) % 32 = 0 ∧
  (memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr")

def ExtendMemoryPre {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ ebw : BitVec 64, s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
    (ebw = 0#64 ∨ (memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
      (memW s (globN s "ev" + 32) + ebw.toNat) % 8 = 0 ∧
      memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr"))

theorem headMemAligned_iff_group04 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    HeadMemAligned s ↔ R16Shards.OpHandlers.HeadMemAligned s := Iff.rfl

theorem extendMemoryPre_iff_group04 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ExtendMemoryPre s ↔ R16Shards.OpHandlers.ExtendMemoryPre s := Iff.rfl

/-- Bridge of the proved Group04 `extend_memory` contract to the local precondition. -/
theorem eps_extend_memory_aligned_local :
    R14Shards.OpHandlersA.EvmPreservingSpec ExtendMemoryPre
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "frame_mem_ptr" →
        globN post g = globN s g)
      (ofString "extend_memory") :=
  R16Shards.OpHandlers.eps_extend_memory_aligned

theorem headMemChainWF_headMemAligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : HeadMemChainWF s) : HeadMemAligned s :=
  ⟨(h.1 _ (head_mem_evmChain s)).1, h.2.1⟩

theorem headMemChainWF_headMemAligned_group04 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : HeadMemChainWF s) : R16Shards.OpHandlers.HeadMemAligned s :=
  (headMemAligned_iff_group04 s).1 (headMemChainWF_headMemAligned h)

/-- A head-aligned frame whose next `extend_memory` grows by an 8-aligned amount that keeps the
length below `2^37` meets `ExtendMemoryPre` (the `ebw ≠ 0` branch). -/
theorem extendMemoryPre_of_headMemAligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : HeadMemAligned s) (ebw : BitVec 64)
    (hl : s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)))
    (hb : memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37)
    (h8 : (memW s (globN s "ev" + 32) + ebw.toNat) % 8 = 0) :
    ExtendMemoryPre s :=
  ⟨ebw, hl, Or.inr ⟨hb, h8, h.2⟩⟩

theorem headMemChainWF_congr {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hm : t.memory = s.memory) (hg : t.globals = s.globals) :
    HeadMemChainWF t ↔ HeadMemChainWF s := by
  unfold HeadMemChainWF
  rw [evmChain_congr hm hg, memW_congr hm, globN_congr hg]

theorem headMemChainWF_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : HeadMemChainWF s) :
    HeadMemChainWF { s with locals := locals, clock := k } :=
  (headMemChainWF_congr (s := s) (t := { s with locals := locals, clock := k }) rfl rfl).2 h

/-- Entry establishment at depth 0 (the outermost continuation has kind `cur_cont+16 = 0`, as
set by `depth0_prepare`): the chain is the head alone, so the invariant is exactly the head's
alignment facts and `mem + cap = frame_mem_ptr`. -/
theorem headMemChainWF_depth0 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hk : memW s (globN s "cur_cont" + 16) = 0)
    (hlen : memW s (globN s "ev" + 32) % 32 = 0)
    (hcap : memW s (globN s "ev" + 40) % 8 = 0)
    (hend : memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr") :
    HeadMemChainWF s := by
  have hc : evmChain s = [(globN s "ev", globN s "cur_cont")] := by
    rw [evmChain_cons, if_pos hk]
  refine ⟨?_, hend, ?_⟩
  · rw [hc]; intro ec hec
    rw [List.mem_singleton] at hec; subst hec; exact ⟨hlen, hcap⟩
  · rw [hc]; exact trivial

/-- Pushing a child frame (`frame_open` + `start_child`): if the new chain is the child on top
of the old chain, the child's continuation records the old `frame_mem_ptr`-derived mark that
the old head's memory ends at, and the old chain is unchanged in memory, the invariant holds. -/
theorem chainLinks_cons (m : Nat → Nat) (a b : Ivl) (rest : List Ivl)
    (hab : m (b.1 + 24) + m (b.1 + 40) = m (a.2 + 56)) (h : ChainLinks m (b :: rest)) :
    ChainLinks m (a :: b :: rest) := ⟨hab, h⟩

theorem chainLinks_tail (m : Nat → Nat) (a : Ivl) (rest : List Ivl)
    (h : ChainLinks m (a :: rest)) : ChainLinks m rest := by
  match rest, h with
  | [], _ => trivial
  | _ :: _, h => exact h.2

theorem evmChainFrom_succ {F : Type} (s : PanSemStateFiniteExact 64 F) (n e c : Nat) :
    evmChainFrom s (n + 1) e c =
      (e, c) :: (if memW s (c + 16) = 0 then [] else evmChainFrom s n (memW s c) (memW s (c + 8))) :=
  rfl

theorem maxChain_succ : maxChain = 16383 + 1 := rfl

/-- Links transport: links that only read `+24/+40` of frames and `+56` of continuations of
`l` carry over to any memory agreeing with the old one on those cells. -/
theorem chainLinks_transport (m m' : Nat → Nat) :
    ∀ l : List Ivl, (∀ ec ∈ l, m' (ec.1 + 24) = m (ec.1 + 24) ∧
      m' (ec.1 + 40) = m (ec.1 + 40) ∧ m' (ec.2 + 56) = m (ec.2 + 56)) →
      ChainLinks m l → ChainLinks m' l
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: rest, hm, hl => by
    refine ⟨?_, chainLinks_transport m m' (b :: rest)
      (fun ec hec => hm ec (List.mem_cons_of_mem _ hec)) hl.2⟩
    have ha := hm a List.mem_cons_self
    have hb := hm b (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [hb.1, hb.2.1, ha.2.2]; exact hl.1

/-- Popping the head (`finish_child`): the parent becomes the head, its memory ends at the
child's recorded mark, and `frame_mem_release(mark)` sets `frame_mem_ptr` to that mark. -/
theorem headMemChainWF_pop {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : HeadMemChainWF s)
    (hk : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hchain : evmChain post = (evmChain s).tail)
    (hmem : ∀ ec ∈ evmChain post, memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧ memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56))
    (hev : globN post "ev" = memW s (globN s "cur_cont"))
    (hfmp : globN post "frame_mem_ptr" = memW s (globN s "cur_cont" + 56)) :
    HeadMemChainWF post := by
  obtain ⟨hal, _, hlk⟩ := hs
  have hcs := evmChain_cons s
  rw [if_neg hk] at hcs
  have htail : (evmChain s).tail = evmChainFrom s maxChain (memW s (globN s "cur_cont"))
      (memW s (globN s "cur_cont" + 8)) := by rw [hcs]; rfl
  rw [htail] at hchain
  refine ⟨?_, ?_, ?_⟩
  · intro ec hec
    have hm := hmem ec hec
    rw [hchain] at hec
    have := hal ec (by rw [hcs]; exact List.mem_cons_of_mem _ hec)
    rw [hm.2.1, hm.2.2.1]; exact this
  · have hhd : (globN post "ev", globN post "cur_cont") ∈ evmChain post := head_mem_evmChain post
    have hm := hmem _ hhd
    rw [hm.1, hm.2.2.1, hfmp, hev]
    rw [hcs, maxChain_succ, evmChainFrom_succ] at hlk
    exact hlk.1
  · rw [hcs] at hlk
    have h1 := chainLinks_tail _ _ _ hlk
    rw [← hchain] at h1
    exact chainLinks_transport (memW s) (memW post) _
      (fun ec hec => ⟨(hmem ec hec).1, (hmem ec hec).2.2.1, (hmem ec hec).2.2.2⟩) h1

/-- Chain-stable preservation (`frame_exception`, `frame_epilogue`, non-frame opcodes): a step
that keeps the chain, `ev`, `frame_mem_ptr`, and the `+24/+32/+40` frame cells and `+56`
continuation cells of every chain frame preserves the invariant. -/
theorem headMemChainWF_of_agree {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : HeadMemChainWF s)
    (hchain : evmChain post = evmChain s)
    (hmem : ∀ ec ∈ evmChain s, memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧ memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56))
    (hev : globN post "ev" = globN s "ev")
    (hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr") :
    HeadMemChainWF post := by
  obtain ⟨hal, hhd, hlk⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · intro ec hec
    rw [hchain] at hec
    have hm := hmem ec hec
    rw [hm.2.1, hm.2.2.1]; exact hal ec hec
  · have hm := hmem _ (head_mem_evmChain s)
    rw [hev, hm.1, hm.2.2.1, hfmp]; exact hhd
  · rw [hchain]
    exact chainLinks_transport (memW s) (memW post) _
      (fun ec hec => ⟨(hmem ec hec).1, (hmem ec hec).2.2.1, (hmem ec hec).2.2.2⟩) hlk

/-- `extend_memory` preservation: the head's capacity grows to a new 8-aligned value, its
length becomes a 32-aligned value, `mem` is unchanged, and `frame_mem_ptr` advances by exactly
the growth; every other chain cell is kept. -/
theorem headMemChainWF_extend {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : HeadMemChainWF s)
    (hchain : evmChain post = evmChain s)
    (hk : ∀ ec ∈ (evmChain s).tail, memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧ memW post (ec.1 + 40) = memW s (ec.1 + 40))
    (hc : ∀ ec ∈ evmChain s, memW post (ec.2 + 56) = memW s (ec.2 + 56))
    (hev : globN post "ev" = globN s "ev")
    (hmem0 : memW post (globN s "ev" + 24) = memW s (globN s "ev" + 24))
    (hlen0 : memW post (globN s "ev" + 32) % 32 = 0)
    (hcap0 : memW post (globN s "ev" + 40) % 8 = 0)
    (hfmp : memW s (globN s "ev" + 24) + memW post (globN s "ev" + 40) =
      globN post "frame_mem_ptr") :
    HeadMemChainWF post := by
  obtain ⟨hal, _, hlk⟩ := hs
  obtain ⟨tl, hcs⟩ : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl :=
    ⟨_, evmChain_cons s⟩
  rw [hcs] at hal hlk hk hc
  rw [List.tail_cons] at hk
  refine ⟨?_, ?_, ?_⟩
  · intro ec hec
    rw [hchain, hcs] at hec
    rcases List.mem_cons.mp hec with rfl | hec'
    · exact ⟨hlen0, hcap0⟩
    · have hm := hk ec hec'
      rw [hm.2.1, hm.2.2]; exact hal ec (List.mem_cons_of_mem _ hec')
  · rw [hev, hmem0]; exact hfmp
  · rw [hchain, hcs]
    -- the head's own `+24/+40` cells are never read by `ChainLinks` (only parents' are)
    cases tl with
    | nil => trivial
    | cons b rest =>
      have hb := hk b List.mem_cons_self
      refine ⟨?_, chainLinks_transport (memW s) (memW post) _ (fun ec hec => ?_) hlk.2⟩
      · rw [hb.1, hb.2.2, hc _ List.mem_cons_self]; exact hlk.1
      · have h1 := hk ec hec
        exact ⟨h1.1, h1.2.2, hc ec (List.mem_cons_of_mem _ hec)⟩

/-- Head status/gas updates (the write footprint of `refill_frame_state_gas`, `frame_halt`,
`frame_exception`: `R11Shards.headAllowedOffsets`, i.e. head-record words `ev+64…ev+200` and
`cur_cont+32`) never touch a cell read by `HeadMemChainWF`: under `EvmInv` the head record and
continuation are disjoint from each other and from every other frame's blocks, so the invariant
is preserved. -/
theorem headMemChainWF_of_headAllowed {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hE : EvmInv s) (hs : HeadMemChainWF s)
    (hglob : post.globals = s.globals)
    (hchain : evmChain post = evmChain s)
    (hmem_out : ∀ x : BitVec 64,
      (∀ addr ∈ R11Shards.headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 addr) →
      post.memory x = s.memory x) :
    HeadMemChainWF post := by
  have hev : globN post "ev" = globN s "ev" := by simp [globN, hglob]
  have hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by simp [globN, hglob]
  obtain ⟨_, S, _, hrest⟩ := hE
  dsimp only at hrest
  obtain ⟨_, _, _, hFWF, _, _, hPair, _⟩ := hrest
  obtain ⟨tl, hcs⟩ : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl :=
    ⟨_, evmChain_cons s⟩
  have hSE : scratchEnd = 2965299200 := rfl
  have hhead := hFWF _ (head_mem_evmChain s)
  have he_in := (hhead.1 (globN s "ev", 280) (by simp)).1.2
  have hc_in := (hhead.1 (globN s "cur_cont", 104) (by simp)).1.2
  dsimp only at he_in hc_in
  rw [hcs, List.map_cons, List.flatten_cons, List.pairwise_append] at hPair
  obtain ⟨hP0, _, hcross⟩ := hPair
  have hdec : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
    unfold frameObjects at hP0
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hP0).1).1 _ (by simp)
  have hsafe : ∀ a : Nat, a < 2 ^ 64 →
      (∀ addr ∈ R11Shards.headAllowedOffsets (globN s "ev") (globN s "cur_cont"), a ≠ addr) →
      memW post a = memW s a := by
    intro a hlt hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    intro addr haddr heq
    have hal : addr < 2 ^ 64 := by
      simp only [R11Shards.headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
      rw [hSE] at he_in hc_in
      rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hal] at this
    exact hne addr haddr this
  refine headMemChainWF_of_agree hs hchain ?_ hev hfmp
  intro ec hec
  rw [hcs] at hec
  rcases List.mem_cons.mp hec with rfl | htl
  · unfold Disj at hdec; dsimp only at hdec
    rw [hSE] at he_in hc_in
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply hsafe <;> (try dsimp only) <;> (try omega) <;>
      (intro addr haddr
       simp only [R11Shards.headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
       rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  · have hFec := hFWF ec (by rw [hcs]; exact List.mem_cons_of_mem _ htl)
    have hr_in := (hFec.1 (ec.1, 280) (by simp)).1.2
    have hk_in := (hFec.1 (ec.2, 104) (by simp)).1.2
    dsimp only at hr_in hk_in
    have hmemb : ∀ o ∈ [(ec.1, 280), (ec.2, 104)],
        o ∈ ((tl.map (frameObjects s)).flatten) := by
      intro o ho
      exact List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map_of_mem htl,
        by unfold frameObjects; simp only [List.mem_cons, List.mem_append] at ho ⊢; tauto⟩
    have hA : (globN s "ev", 280) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
      unfold frameObjects; simp
    have hB : (globN s "cur_cont", 104) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
      unfold frameObjects; simp
    have d1 := hcross _ hA _ (hmemb (ec.1, 280) (by simp))
    have d2 := hcross _ hB _ (hmemb (ec.1, 280) (by simp))
    have d3 := hcross _ hA _ (hmemb (ec.2, 104) (by simp))
    have d4 := hcross _ hB _ (hmemb (ec.2, 104) (by simp))
    unfold Disj at d1 d2 d3 d4; dsimp only at d1 d2 d3 d4
    rw [hSE] at he_in hc_in hr_in hk_in
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply hsafe <;> (try omega) <;>
      (intro addr haddr
       simp only [R11Shards.headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
       rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)

/-! ## 2. The aligned invariant and the aligned frame contracts -/

def EvmInvA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ HeadMemChainWF s

def EvmRunA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInvA s ∧ ¬ EvmDone s

def FinishReadyA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInvA s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0

theorem localsFree_evmInvA : LocalsFree EvmInvA :=
  fun s locals k h => ⟨localsFree_evmInv s locals k h.1, headMemChainWF_locals s locals k h.2⟩

theorem evmInvA_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInvA s) :
    GuestInv s :=
  evmInv_guestInv s h.1

theorem evmInvA_headMemAligned {F : Type} {s : PanSemStateFiniteExact 64 F} (h : EvmInvA s) :
    HeadMemAligned s :=
  headMemChainWF_headMemAligned h.2

/-- Aligned `op_dispatch` contract (`op_dispatch_spec` with `HeadMemChainWF` carried). -/
def OpDispatchSpecA : Prop :=
  FunSpec (fun s => EvmInv s ∧ HeadMemChainWF s ∧ ¬ EvmDone s)
    (fun s r post =>
      ((∃ v, r = some (.returned v)) → (EvmInv post ∧ HeadMemChainWF post) ∧
        evmPot post < evmPot s) ∧
      (IsEvmErr r → (EvmInv post ∧ HeadMemChainWF post) ∧
        (evmChain post).length = (evmChain s).length ∧ Wave8GuestInv.evmR post ≤ Wave8GuestInv.evmR s))
    (ofString "op_dispatch")

def FrameExceptionSpecA : Prop :=
  FunSpec EvmInvA
    (OnReturn fun s post => EvmInvA post ∧ EvmDone post ∧
      (evmChain post).length = (evmChain s).length ∧ Wave8GuestInv.evmR post ≤ Wave8GuestInv.evmR s)
    (ofString "frame_exception")

def FrameEpilogueSpecA : Prop :=
  FunSpec (fun s => EvmInvA s ∧ EvmDone s)
    (OnReturn fun s post => EvmInvA post ∧ EvmDone post ∧
      (evmChain post).length = (evmChain s).length ∧ Wave8GuestInv.evmR post ≤ Wave8GuestInv.evmR s)
    (ofString "frame_epilogue")

def FinishChildSpecA : Prop :=
  FunSpec (fun s => EvmInvA s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
    (fun s r post => ((∃ v, r = some (.returned v)) ∨ IsEvmErr r) →
      EvmInvA post ∧ (evmChain post).length + 1 = (evmChain s).length ∧ Wave8GuestInv.evmR post ≤ Wave8GuestInv.evmR s)
    (ofString "finish_child")

/-- `OpDispatchSpecA` in the `EvmInvA ∧ ¬ EvmDone` shape used by the walk. -/
def OpDispatchSpecW : Prop :=
  FunSpec (fun s => EvmInvA s ∧ ¬ EvmDone s)
    (fun s r post =>
      ((∃ v, r = some (.returned v)) → EvmInvA post ∧ evmPot post < evmPot s) ∧
      (IsEvmErr r → EvmInvA post ∧ (evmChain post).length = (evmChain s).length ∧
        Wave8GuestInv.evmR post ≤ Wave8GuestInv.evmR s))
    (ofString "op_dispatch")

theorem opDispatchSpecW_of_A (h : OpDispatchSpecA) : OpDispatchSpecW := by
  obtain ⟨ps, body, ret, hl, hrun⟩ := h
  exact ⟨ps, body, ret, hl, fun s hc hP hex hnt => hrun s hc ⟨hP.1.1, hP.1.2, hP.2⟩ hex hnt⟩

/-! ## 3. The `run_frames` walk under `EvmInvA` (port of `EvmGBody.RunFramesProof`) -/

section RunFramesGlueA

variable (p0 R0 L0 F0 : Nat)

/-- Loop-head facts carried through the body: the potential components of the head. -/
def GPreA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInvA t ∧ evmPot t = p0 ∧ Wave8GuestInv.evmR t = R0 ∧ (evmChain t).length = L0 ∧ evmFp t = F0

def GQA : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none ∨ r = some .continue) → (EvmInvA t ∧ evmPot t < p0) ∨ locN t "go" = 0

def GMidA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => (GPreA p0 R0 L0 F0 t ∧ EvmDone t ∧ locN t "done" ≠ 0) ∨
    (EvmInvA t ∧ evmPot t < p0 ∧ locN t "done" = 0)

def GAA : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none → GMidA p0 R0 L0 F0 t) ∧ (r ≠ none → GQA p0 r t)

theorem gqA_other {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (h1 : r ≠ none) (h2 : r ≠ some .continue) : GQA p0 r t := by
  intro h; rcases h with h | h <;> contradiction

theorem gaA_other {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (h1 : r ≠ none) (h2 : r ≠ some .continue) : GAA p0 R0 L0 F0 r t :=
  ⟨fun h => absurd h h1, fun _ => gqA_other p0 r t h1 h2⟩

theorem gpreA_congr {F : Type} {t u : PanSemStateFiniteExact 64 F} (hm : u.memory = t.memory)
    (hg : u.globals = t.globals) (hinv : EvmInvA u) (h : GPreA p0 R0 L0 F0 t) :
    GPreA p0 R0 L0 F0 u := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  obtain ⟨e1, e2, e3, e4⟩ := evm_congr hm hg
  exact ⟨hinv, e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4⟩

theorem evmInvA_locals {F : Type} {t : PanSemStateFiniteExact 64 F}
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (h : EvmInvA t) :
    EvmInvA { t with locals := locals } :=
  localsFree_evmInvA t locals t.clock h

theorem evmInvA_setVar {F : Type} {t : PanSemStateFiniteExact 64 F} (n : MlS) (v : ValueHOL 64)
    (h : EvmInvA t) : EvmInvA (setVarHOLFinite n v t) :=
  localsFree_evmInvA t _ t.clock h

theorem evmInvA_entry {F : Type} {t : PanSemStateFiniteExact 64 F}
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : EvmInvA t) :
    EvmInvA (callEntryStateHOLFinite t callee) :=
  localsFree_evmInvA t _ _ h

theorem gqA_postLocals : PostLocalsOnly ["go"] (GQA p0) := by
  intro F r t locals hl h hr
  rcases h hr with ⟨hi, hp⟩ | hgo
  · left
    exact ⟨evmInvA_locals locals hi, by rw [(evm_congr (s := t) (t := { t with locals := locals }) rfl rfl).1]; exact hp⟩
  · right
    rw [locN_congr t locals t.clock "go" (hl "go" (by simp))]
    exact hgo

theorem gaA_postLocals : PostLocalsOnly ["go", "done"] (GAA p0 R0 L0 F0) := by
  intro F r t locals hl h
  have hgo := hl "go" (by simp)
  have hdone := locN_congr t locals t.clock "done" (hl "done" (by simp))
  refine ⟨fun hr => ?_, fun hr => gqA_postLocals p0 r t locals (fun n hn => by
    simp at hn; subst hn; exact hgo) (h.2 hr)⟩
  rcases h.1 hr with ⟨hp, hd, hn⟩ | ⟨hi, hp, hn⟩
  · left
    refine ⟨gpreA_congr p0 R0 L0 F0 (t := t) (u := { t with locals := locals }) rfl rfl
      (evmInvA_locals locals hp.1) hp, ?_, ?_⟩
    · exact (evmDone_congr (s := t) (t := { t with locals := locals }) rfl rfl).2 hd
    · change locN { t with locals := locals, clock := t.clock } "done" ≠ 0
      rw [hdone]; exact hn
  · right
    refine ⟨evmInvA_locals locals hi, ?_, ?_⟩
    · rw [(evm_congr (s := t) (t := { t with locals := locals }) rfl rfl).1]; exact hp
    · change locN { t with locals := locals, clock := t.clock } "done" = 0
      rw [hdone]; exact hn

end RunFramesGlueA

section RunFramesGlueA2

variable (p0 R0 L0 F0 : Nat)

/-- After `dec done 0`. -/
def GP1A : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPreA p0 R0 L0 F0 t ∧ locN t "done" = 0

/-- After `dec pc (load ev)` on the not-yet-done path. -/
def GPpcA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPreA p0 R0 L0 F0 t ∧ locN t "done" = 0 ∧
    memW t (globN t "cur_cont" + 32) = 0 ∧ memW t (globN t "ev" + 104) ≠ 0 ∧
    locN t "pc" = memW t (globN t "ev")

/-- At the `op_dispatch` call: a running frame. -/
def GPdispA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPreA p0 R0 L0 F0 t ∧ locN t "done" = 0 ∧ ¬ EvmDone t ∧ F0 = 2 * L0 + 1

/-- In the `EvmErr` handler of `op_dispatch`. -/
def GPhA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInvA t ∧ (evmChain t).length = L0 ∧ Wave8GuestInv.evmR t ≤ R0 ∧ locN t "done" = 0 ∧
    F0 = 2 * L0 + 1

/-- The done branch, before `frame_epilogue`. -/
def GPdoneA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPreA p0 R0 L0 F0 t ∧ EvmDone t

/-- After `frame_epilogue`. -/
def GPepiA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInvA t ∧ EvmDone t ∧ (evmChain t).length = L0 ∧ Wave8GuestInv.evmR t ≤ R0 ∧ 2 * L0 ≤ F0

/-- At the `finish_child` call. -/
def GPfinA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPepiA R0 L0 F0 t ∧ memW t (globN t "cur_cont" + 16) ≠ 0

/-- In the `EvmErr` handler of `finish_child`. -/
def GPh4A : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInvA t ∧ (evmChain t).length + 1 = L0 ∧ Wave8GuestInv.evmR t ≤ R0 ∧ 2 * L0 ≤ F0

end RunFramesGlueA2

section RunFramesProofA

private def rfCharge (f : MlS) : Nat :=
  if f = ofString "op_dispatch" then K.op_dispatch else
  if f = ofString "finish_child" then K.finish_child else
  if f = ofString "frame_epilogue" then K.frame_epilogue else
  if f = ofString "frame_exception" then K.frame_exception else 0

private theorem rfCharge_op_dispatch : rfCharge (ofString "op_dispatch") = K.op_dispatch := by
  simp only [rfCharge, ↓reduceIte]

private theorem rfCharge_finish_child : rfCharge (ofString "finish_child") = K.finish_child := by
  simp only [rfCharge, if_neg (show ofString "finish_child" ≠ ofString "op_dispatch" from by decide), ↓reduceIte]

private theorem rfCharge_frame_epilogue : rfCharge (ofString "frame_epilogue") = K.frame_epilogue := by
  simp only [rfCharge, if_neg (show ofString "frame_epilogue" ≠ ofString "op_dispatch" from by decide),
    if_neg (show ofString "frame_epilogue" ≠ ofString "finish_child" from by decide), ↓reduceIte]

private theorem rfCharge_frame_exception : rfCharge (ofString "frame_exception") = K.frame_exception := by
  simp only [rfCharge, if_neg (show ofString "frame_exception" ≠ ofString "op_dispatch" from by decide),
    if_neg (show ofString "frame_exception" ≠ ofString "finish_child" from by decide),
    if_neg (show ofString "frame_exception" ≠ ofString "frame_epilogue" from by decide), ↓reduceIte]

private def rfWalkCost : ProgHOL 64 → Nat
  | .seq a b => rfWalkCost a + rfWalkCost b
  | .ite _ a b => max (rfWalkCost a) (rfWalkCost b)
  | .dec _ _ _ b => rfWalkCost b
  | .call (some (_, some (_, _, h))) f _ => (rfCharge f + 1) + rfWalkCost h
  | .call _ f _ => rfCharge f + 1
  | _ => 0

private structure BHoare (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (prog : ProgHOL 64)
    (Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) : Prop where
  hoare : Hoare P prog Q
  bounded : TerminatingProgBoundedOn P prog (rfWalkCost prog)

private theorem BHoare.of_bound {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64}
    (hb : TerminatingProgBoundedOn P prog (rfWalkCost prog)) (h : Hoare P prog Q) :
    BHoare P prog Q := ⟨h, hb⟩

private theorem BHoare.skip {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q none s) :
    BHoare P .skip Q :=
  ⟨Hoare.skip h, TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)⟩

private theorem BHoare.seq {P R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64}
    (h1 : BHoare P first fun r t => (r = none → R t) ∧ (r ≠ none → Q r t))
    (h2 : BHoare R second Q) : BHoare P (.seq first second) Q := by
  refine ⟨Hoare.seq h1.hoare h2.hoare, ?_⟩
  intro F state hcode hP hnt
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    have hp := h1.hoare.run state hcode hP hnt1
    rw [hr1] at hp
    obtain ⟨s1, k1⟩ := h1.bounded state hcode hP hnt1
    rw [hr1] at s1 k1
    obtain ⟨s2, k2⟩ := h2.bounded mid (hmeta.1.trans hcode) (hp.1 rfl) hnt
    exact ⟨by change state.clock ≤ _ + (rfWalkCost first + rfWalkCost second); dsimp only at s1 k1; omega,
      by dsimp only at k1; omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1.bounded state hcode hP hnt1
    rw [hr1] at s1 k1
    exact ⟨by change state.clock ≤ _ + (rfWalkCost first + rfWalkCost second); dsimp only at s1; omega, k1⟩

private theorem BHoare.ite {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : BHoare (fun s => P s ∧ CondTrue cond s) yes Q)
    (hno : BHoare (fun s => P s ∧ CondFalse cond s) no Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    BHoare P (.ite cond yes no) Q :=
  ⟨Hoare.ite hyes.hoare hno.hoare herr,
    TerminatingProgBoundedOn.ite_cond_on hyes.bounded hno.bounded⟩

private theorem BHoare.dec {P P' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64}
    {body : ProgHOL 64} (hname : ∀ n ∈ names, ofString n ≠ name)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some v → P' (setVarHOLFinite name v s))
    (hbody : BHoare P' body Q) (hQ : PostLocalsOnly names Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    BHoare P (.dec name shape init body) Q := by
  refine ⟨Hoare.dec hname hinit hbody.hoare hQ herr, ?_⟩
  intro F state hcode hPs hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i val hv _
      have hb := hbody.bounded (setVarHOLFinite name val state) hcode (hinit state val hPs hv) hnt
      simpa only [setVarHOLFinite, rfWalkCost] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

private theorem BHoare.assign {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {kind : VarKind} {name : MlS} {source : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) source =
        some v → Q none (setKvarHOLFinite kind name v s))
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    BHoare P (.assign kind name source) Q :=
  ⟨Hoare.assign h herr, TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)⟩

private def rfCond : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "go")) (.const 0)
private def rfCode : ProgHOL 64 := (sourceFunctionEntry Guest.Software.guestFn_run_frames).2.2.1
private def rfBody : ProgHOL 64 :=
  match rfCode with
  | .dec _ _ _ (.seq (.while _ b) _) => b
  | _ => .skip

private theorem rfCode_eq : rfCode = .dec (ofString "go") .one (.const 1)
    (.seq (.while rfCond rfBody) (.return (.const 0))) := rfl

private theorem rfCost_eq : rfWalkCost rfBody =
    max 0 (max 0 (max 0 ((K.op_dispatch + 1) + (K.frame_exception + 1)))) +
      max ((K.frame_epilogue + 1) + max 0 ((K.finish_child + 1) + (K.frame_exception + 1))) 0 := rfl

private def rfFirst : ProgHOL 64 :=
  match rfBody with
  | .dec _ _ _ (.seq a _) => a
  | _ => .skip

private def rfSecond : ProgHOL 64 :=
  match rfBody with
  | .dec _ _ _ (.seq _ b) => b
  | _ => .skip

private theorem rfBody_eq : rfBody = .dec (ofString "done") .one (.const 0)
    (.seq rfFirst rfSecond) := rfl

private theorem rf_firstwalk
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.frame_exception)
    (bd : TerminatingFunBoundedOn EvmRunA (ofString "op_dispatch") K.op_dispatch)
    (h1 : OpDispatchSpecW)
    (h2 : FrameExceptionSpecA)
    (p0 R0 L0 F0 : Nat)
    (hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInvA t → Wave8GuestInv.evmR t ≤ R0 →
      evmFp t < F0 → evmPot t < p0) :
    BHoare (GP1A p0 R0 L0 F0) rfFirst (GAA p0 R0 L0 F0) := by
  simp only [rfFirst, rfSecond, rfBody, rfCode, sourceFunctionEntry,
    Guest.Software.guestFn_run_frames,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  refine BHoare.ite ?_ ?_ (fun _ _ => gaA_other p0 R0 L0 F0 _ _ (by simp) (by simp))
  · refine BHoare.assign (fun t v hP hv => ?_)
      (fun _ _ => gaA_other p0 R0 L0 F0 _ _ (by simp) (by simp))
    cases evalAt_const t 1 v hv
    refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
    · exact gpreA_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t) rfl rfl
        (evmInvA_setVar _ _ hP.1.1.1) hP.1.1
    · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
      have := condTrue_ne0 hP.2
      exact Or.inl (by simpa using this)
    · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
      rw [locN_setVar_same]; decide
  · refine BHoare.ite ?_ ?_ (fun _ _ => gaA_other p0 R0 L0 F0 _ _ (by simp) (by simp))
    · refine BHoare.assign (fun t v hP hv => ?_)
        (fun _ _ => gaA_other p0 R0 L0 F0 _ _ (by simp) (by simp))
      cases evalAt_const t 1 v hv
      refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
      · exact gpreA_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t) rfl rfl
          (evmInvA_setVar _ _ hP.1.1.1.1) hP.1.1.1
      · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
        have := condTrue_eq0 hP.2
        exact Or.inr (Or.inl (by simpa using this))
      · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
        rw [locN_setVar_same]; decide
    · refine BHoare.dec (names := ["go", "done"]) (P' := GPpcA p0 R0 L0 F0) (by decide) ?_ ?_
        (gaA_postLocals p0 R0 L0 F0)
        (fun _ _ => gaA_other p0 R0 L0 F0 _ _ (by simp) (by simp))
      · intro F t v hP hv
        obtain ⟨⟨hP1, hc1⟩, hc2⟩ := hP
        obtain ⟨a, rfl, ha⟩ := evalAt_loadG t "ev" 0 v hv
        refine ⟨gpreA_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
          (evmInvA_setVar _ _ hP1.1.1) hP1.1, ?_, ?_, ?_, ?_⟩
        · rw [locN_setVar_ne t "done" (ofString "pc") _ (by decide)]; exact hP1.2
        · show memW t (globN t "cur_cont" + 32) = 0
          have := condFalse_ne0 hc1; simpa using this
        · show memW t (globN t "ev" + 104) ≠ 0
          have := condFalse_eq0 hc2; simpa using this
        · rw [locN_setVar_same]
          show a.toNat = memW t (globN t "ev")
          simpa using ha
      · refine BHoare.ite ?_ ?_ (fun _ _ => gaA_other p0 R0 L0 F0 _ _ (by simp) (by simp))
        · refine BHoare.assign (fun t v hP hv => ?_)
            (fun _ _ => gaA_other p0 R0 L0 F0 _ _ (by simp) (by simp))
          cases evalAt_const t 1 v hv
          obtain ⟨⟨hpre, _, _, _, hpc⟩, w, hw, hne⟩ := hP
          refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
          · exact gpreA_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t)
              rfl rfl (evmInvA_setVar _ _ hpre.1) hpre
          · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
            have := (cond_notLower hw).1 hne
            refine Or.inr (Or.inr ?_)
            rw [← hpc]; simpa using this
          · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
            rw [locN_setVar_same]; decide
        · refine BHoare.dec (names := ["go", "done"]) (P' := GPdispA p0 R0 L0 F0) (by decide)
            ?_ ?_ (gaA_postLocals p0 R0 L0 F0)
            (fun _ _ => gaA_other p0 R0 L0 F0 _ _ (by simp) (by simp))
          · intro F t v hP hv
            cases evalAt_const t 0 v hv
            obtain ⟨⟨hpre, hdone, hc1, hc2, hpc⟩, hc3⟩ := hP
            have hlt := (cond_notLower hc3).2 rfl
            have hnd : ¬ EvmDone t := by
              rintro (h | h | h)
              · exact h hc1
              · exact hc2 h
              · rw [← hpc] at h; simp at hlt; omega
            refine ⟨gpreA_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
              (evmInvA_setVar _ _ hpre.1) hpre, ?_, ?_, ?_⟩
            · rw [locN_setVar_ne t "done" (ofString "err") _ (by decide)]; exact hdone
            · exact fun h => hnd ((evmDone_congr (s := t) (t := setVarHOLFinite _ _ t)
                rfl rfl).1 h)
            · rw [← hpre.2.2.2.2, ← hpre.2.2.2.1, evmFp_notDone hnd]
          · refine BHoare.of_bound ?_ ?_
            · have hb : TerminatingProgBoundedOn (GPdispA p0 R0 L0 F0) _ _ :=
                TerminatingProgBoundedOn.callHandle_on bd
                  (fun t hP => evmInvA_guestInv t hP.1.1) none (ofString "EvmErr") (ofString "err")
                  (TerminatingProgBoundedOn.call_guestInv bx none [(.var .local (ofString "err"))])
                  [.loadByte (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 48]),
                    .var .local (ofString "pc")])]
                  (P := GPdispA p0 R0 L0 F0)
                  (by
                    intro F t values body callee ret _ hP _ _
                    exact ⟨evmInvA_entry callee hP.1.1, fun hd => hP.2.2.1
                      ((evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1 hd)⟩)
              intro F u hc hi
              simpa [InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
                InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
                InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
                rfWalkCost, rfCharge_op_dispatch, rfCharge_finish_child,
                rfCharge_frame_epilogue, rfCharge_frame_exception,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb u hc hi
            refine Hoare.callH (Pc := fun s => EvmInvA s ∧ ¬ EvmDone s) (Ph := GPhA R0 L0 F0)
              h1 ?_ ?_ ?_ ?_ (fun r t h h' => gaA_other p0 R0 L0 F0 r t h h')
            · intro F t values body callee ret _ hP _ _
              exact ⟨evmInvA_entry callee hP.1.1, fun hd => hP.2.2.1
                ((evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1 hd)⟩
            · intro F t callee post v _ hP hq
              obtain ⟨hi, hlt⟩ := hq.1 ⟨v, rfl⟩
              refine ⟨fun _ => Or.inr ⟨evmInvA_locals _ hi, ?_, hP.2.1⟩, fun h => absurd rfl h⟩
              rw [(evm_congr (s := post) (t := { post with locals := t.locals }) rfl rfl).1]
              rw [(evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1,
                hP.1.2.1] at hlt
              exact hlt
            · intro F t callee post v _ hP hq
              obtain ⟨hi, hlen, hR⟩ := hq.2 ⟨v, rfl⟩
              obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
              obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post)
                (t := setVarHOLFinite (ofString "err") v { post with locals := t.locals }) rfl rfl
              refine ⟨evmInvA_setVar _ _ (evmInvA_locals _ hi), ?_, ?_, ?_, hP.2.2.2⟩
              · rw [fL, hlen, eL]; exact hP.1.2.2.2.1
              · rw [fR]; exact hR.trans (le_of_eq (eR.trans hP.1.2.2.1))
              · rw [locN_setVar_ne _ "done" (ofString "err") _ (by decide)]; exact hP.2.1
            · refine Hoare.call0 (Pc := EvmInvA) h2 ?_ ?_
                (fun r t h h' => gaA_other p0 R0 L0 F0 r t h h')
              · intro F t values body callee ret _ hP _ _
                exact evmInvA_entry callee hP.1
              · intro F u callee post v _ hP hq
                obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
                obtain ⟨-, eR, eL, -⟩ := evm_congr (s := u) (t := callEntryStateHOLFinite u callee) rfl rfl
                obtain ⟨fp, fR, fL, fF⟩ := evm_congr (s := post) (t := { post with locals := u.locals }) rfl rfl
                refine ⟨fun _ => Or.inr ⟨evmInvA_locals _ hi, ?_, hP.2.2.2.1⟩, fun h => absurd rfl h⟩
                apply hfin _ (evmInvA_locals _ hi)
                · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.2.2.1)
                · rw [fF, evmFp_done hd, hlen, eL, hP.2.1, hP.2.2.2.2]; omega

private theorem rf_secondwalk
    (bf : TerminatingFunBoundedOn FinishReadyA (ofString "finish_child") K.finish_child)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.frame_epilogue)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.frame_exception)
    (h2 : FrameExceptionSpecA)
    (h3 : FrameEpilogueSpecA)
    (h4 : FinishChildSpecA)
    (p0 R0 L0 F0 : Nat)
    (hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInvA t → Wave8GuestInv.evmR t ≤ R0 →
      evmFp t < F0 → evmPot t < p0) :
    BHoare (GMidA p0 R0 L0 F0) rfSecond (GQA p0) := by
  simp only [rfFirst, rfSecond, rfBody, rfCode, sourceFunctionEntry,
    Guest.Software.guestFn_run_frames,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  refine BHoare.ite ?_ ?_ (fun _ _ => gqA_other p0 _ _ (by simp) (by simp))
  · refine BHoare.seq (R := GPdoneA p0 R0 L0 F0)
      (BHoare.skip fun t hP => ⟨fun _ => ?_, fun h => absurd rfl h⟩) ?_
    · rcases hP.1 with ⟨hp, hd, _⟩ | ⟨_, _, hz⟩
      · exact ⟨hp, hd⟩
      · exact absurd hz (condTrue_local_ne0 hP.2)
    refine BHoare.seq (R := GPepiA R0 L0 F0) ?_ ?_
    · refine BHoare.of_bound ?_ ?_
      · have hb : TerminatingProgBoundedOn (GPdoneA p0 R0 L0 F0) _ _ := TerminatingProgBoundedOn.call_on be none []
          (P := GPdoneA p0 R0 L0 F0)
          (by
            intro F t values body callee ret _ hP _ _
            exact guestInv_callEntry t callee (evmInvA_guestInv t hP.1.1))
        intro F u hc hi
        simpa [InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
          rfWalkCost, rfCharge_op_dispatch, rfCharge_finish_child,
          rfCharge_frame_epilogue, rfCharge_frame_exception] using hb u hc hi
      refine Hoare.call0 (Pc := fun s => EvmInvA s ∧ EvmDone s) h3 ?_ ?_
        (fun r t h h' => ⟨fun hr => absurd hr h, fun _ => gqA_other p0 r t h h'⟩)
      · intro F t values body callee ret _ hP _ _
        exact ⟨evmInvA_entry callee hP.1.1,
          (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2 hP.2⟩
      · intro F t callee post v _ hP hq
        obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
        obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post) (t := { post with locals := t.locals }) rfl rfl
        refine ⟨fun _ => ⟨evmInvA_locals _ hi,
          (evmDone_congr (s := post) (t := { post with locals := t.locals }) rfl rfl).2 hd,
          ?_, ?_, ?_⟩, fun h => absurd rfl h⟩
        · rw [fL, hlen, eL]; exact hP.1.2.2.2.1
        · rw [fR]; exact hR.trans (le_of_eq (eR.trans hP.1.2.2.1))
        · rw [← hP.1.2.2.2.2, evmFp_done hP.2, hP.1.2.2.2.1]
    · refine BHoare.ite ?_ ?_ (fun _ _ => gqA_other p0 _ _ (by simp) (by simp))
      · refine BHoare.seq (R := fun _ => True)
          (BHoare.assign (fun _ _ _ _ => ⟨fun _ => trivial, fun h => absurd rfl h⟩)
            (fun _ _ => ⟨fun h => absurd h (by simp), fun _ => gqA_other p0 _ _ (by simp) (by simp)⟩)) ?_
        refine BHoare.seq (R := fun _ => True)
          (BHoare.assign (fun _ _ _ _ => ⟨fun _ => trivial, fun h => absurd rfl h⟩)
            (fun _ _ => ⟨fun h => absurd h (by simp), fun _ => gqA_other p0 _ _ (by simp) (by simp)⟩)) ?_
        refine BHoare.assign (fun t v _ hv => ?_) (fun _ _ => gqA_other p0 _ _ (by simp) (by simp))
        cases evalAt_const t 0 v hv
        intro _; right
        show locN (setVarHOLFinite (ofString "go") (.val (.word 0)) t) "go" = 0
        rw [locN_setVar_same]; rfl
      · refine BHoare.dec (names := ["go"]) (P' := GPfinA R0 L0 F0) (by decide) ?_ ?_
          (gqA_postLocals p0) (fun _ _ => gqA_other p0 _ _ (by simp) (by simp))
        · intro F t v hP hv
          cases evalAt_const t 0 v hv
          obtain ⟨⟨hi, hd, hlen, hR, hF⟩, hk⟩ := hP
          obtain ⟨-, fR, fL, -⟩ := evm_congr (s := t) (t := setVarHOLFinite _ _ t) rfl rfl
          refine ⟨⟨evmInvA_setVar _ _ hi,
            (evmDone_congr (s := t) (t := setVarHOLFinite _ _ t) rfl rfl).2 hd,
            fL.trans hlen, (le_of_eq fR).trans hR, hF⟩, ?_⟩
          show memW t (globN t "cur_cont" + 16) ≠ 0
          have := condFalse_eq0 hk; simpa using this
        · refine BHoare.of_bound ?_ ?_
          · have hb : TerminatingProgBoundedOn (GPfinA R0 L0 F0) _ _ := TerminatingProgBoundedOn.callHandle_on bf
              (fun t hP => evmInvA_guestInv t hP.1.1) none (ofString "EvmErr") (ofString "err2")
              (TerminatingProgBoundedOn.call_guestInv bx none [(.var .local (ofString "err2"))]) []
              (P := GPfinA R0 L0 F0)
              (by
                intro F t values body callee ret _ hP _ _
                exact ⟨evmInvA_entry callee hP.1.1,
                  (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2
                    hP.1.2.1, hP.2⟩)
            intro F u hc hi
            simpa [InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
              rfWalkCost, rfCharge_op_dispatch, rfCharge_finish_child,
              rfCharge_frame_epilogue, rfCharge_frame_exception,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb u hc hi
          refine Hoare.callH
            (Pc := fun s => EvmInvA s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
            (Ph := GPh4A R0 L0 F0) h4 ?_ ?_ ?_ ?_ (fun r t h h' => gqA_other p0 r t h h')
          · intro F t values body callee ret _ hP _ _
            exact ⟨evmInvA_entry callee hP.1.1,
              (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2
                hP.1.2.1, hP.2⟩
          · intro F t callee post v _ hP hq
            obtain ⟨hi, hlen, hR⟩ := hq (Or.inl ⟨v, rfl⟩)
            obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
            obtain ⟨-, fR, fL, fF⟩ := evm_congr (s := post) (t := { post with locals := t.locals }) rfl rfl
            intro _; left
            refine ⟨evmInvA_locals _ hi, hfin _ (evmInvA_locals _ hi) ?_ ?_⟩
            · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.1.2.2.2.1)
            · rw [fF]
              have h1 := evmFp_le post
              have h2 := hP.1.2.2.2.2
              rw [eL, hP.1.2.2.1] at hlen; omega
          · intro F t callee post v _ hP hq
            obtain ⟨hi, hlen, hR⟩ := hq (Or.inr ⟨v, rfl⟩)
            obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
            obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post)
              (t := setVarHOLFinite (ofString "err2") v { post with locals := t.locals }) rfl rfl
            refine ⟨evmInvA_setVar _ _ (evmInvA_locals _ hi), ?_, ?_, hP.1.2.2.2.2⟩
            · rw [fL, hlen, eL]; exact hP.1.2.2.1
            · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.1.2.2.2.1)
          · refine Hoare.call0 (Pc := EvmInvA) h2 ?_ ?_ (fun r t h h' => gqA_other p0 r t h h')
            · intro F t values body callee ret _ hP _ _
              exact evmInvA_entry callee hP.1
            · intro F u callee post v _ hP hq
              obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
              obtain ⟨-, eR, eL, -⟩ := evm_congr (s := u) (t := callEntryStateHOLFinite u callee) rfl rfl
              obtain ⟨-, fR, fL, fF⟩ := evm_congr (s := post) (t := { post with locals := u.locals }) rfl rfl
              intro _; left
              refine ⟨evmInvA_locals _ hi, hfin _ (evmInvA_locals _ hi) ?_ ?_⟩
              · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.2.2.1)
              · rw [fF, evmFp_done hd, hlen, eL]
                have := hP.2.1; have := hP.2.2.2; omega
  · refine BHoare.skip (fun t hP => fun _ => ?_)
    rcases hP.1 with ⟨_, _, hn⟩ | ⟨hi, hp, _⟩
    · exact absurd (condFalse_local_ne0 hP.2) hn
    · exact Or.inl ⟨hi, hp⟩

private theorem rf_body_walk
    (bf : TerminatingFunBoundedOn FinishReadyA (ofString "finish_child") K.finish_child)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.frame_epilogue)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.frame_exception)
    (bd : TerminatingFunBoundedOn EvmRunA (ofString "op_dispatch") K.op_dispatch)
    (h1 : OpDispatchSpecW)
    (h2 : FrameExceptionSpecA)
    (h3 : FrameEpilogueSpecA)
    (h4 : FinishChildSpecA) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      BHoare (GPreA (evmPot s) (Wave8GuestInv.evmR s) (evmChain s).length (evmFp s)) rfBody (GQA (evmPot s)) := by
  intro F s
  set p0 := evmPot s
  set R0 := Wave8GuestInv.evmR s
  set L0 := (evmChain s).length
  set F0 := evmFp s
  have hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInvA t → Wave8GuestInv.evmR t ≤ R0 →
      evmFp t < F0 → evmPot t < p0 := fun t ht hR hF =>
    lt_of_lt_of_le (evmPot_lt_bound t ht.1 hR hF) (evmPot_ge s)
  rw [rfBody_eq]
  refine BHoare.dec (names := ["go"]) (P' := GP1A p0 R0 L0 F0) (by decide) ?_ ?_
    (gqA_postLocals p0) (fun _ _ => gqA_other p0 _ _ (by simp) (by simp))
  · intro F t v hP hv
    cases evalAt_const t 0 v hv
    refine ⟨gpreA_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
      (evmInvA_setVar _ _ hP.1) hP, ?_⟩
    rw [locN_setVar_same]; rfl
  · exact BHoare.seq
      (rf_firstwalk bx bd h1 h2 p0 R0 L0 F0 hfin)
      (rf_secondwalk bf be bx h2 h3 h4 p0 R0 L0 F0 hfin)

private theorem rf_sum_pair_le {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ l : List Ivl, (l.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum ≤
      l.length * (2 * (2 ^ 64 - 1))
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := memW_lt s (x.1 + 64)
    have h2 := memW_lt s (x.1 + 192)
    have hi := rf_sum_pair_le s xs
    omega

private theorem rf_potential_bounded {F : Type} (s : PanSemStateFiniteExact 64 F) (hi : EvmInvA s) :
    evmPot s < evmPotMax := by
  have hlen := evmInv_len s hi.1
  have hR : Wave8GuestInv.evmR s ≤ Wave8GuestInv.maxChain * (2 * (2 ^ 64 - 1)) :=
    (rf_sum_pair_le s (evmChain s)).trans (Nat.mul_le_mul_right _ hlen)
  have hcap : Wave8GuestInv.evmR s ≤ 2 * Wave8GuestInv.maxChain * 2 ^ 64 := by
    have : 2 * (2 ^ 64 - 1) ≤ 2 * 2 ^ 64 := by omega
    calc Wave8GuestInv.evmR s ≤ Wave8GuestInv.maxChain * (2 * (2 ^ 64 - 1)) := hR
      _ ≤ Wave8GuestInv.maxChain * (2 * 2 ^ 64) := Nat.mul_le_mul_left _ this
      _ = 2 * Wave8GuestInv.maxChain * 2 ^ 64 := by omega
  have hp := evmPot_lt_bound s hi.1 hcap (evmFp_lt s hi.1)
  have hcap_alg : ∀ a b c : Nat, a * (b * c) + b * c = (a + 1) * b * c := fun a b c => by
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  exact lt_of_lt_of_eq hp (hcap_alg (2 * Wave8GuestInv.maxChain * 2 ^ 64) evmPotF evmPotS)

private def rfHeadInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ (EvmInvA s ∨ locN s "go" = 0)

private def rfRank : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat :=
  fun s => if locN s "go" = 0 then 0 else evmPot s + 1

private theorem rf_active_ne {F : Type} {s : PanSemStateFiniteExact 64 F}
    (ha : LoopActive rfCond s) : locN s "go" ≠ 0 :=
  condTrue_local_ne0 ha

private theorem rf_active_inv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hi : rfHeadInv s) (ha : LoopActive rfCond s) : EvmInvA s := by
  rcases hi.2 with hi | hz
  · exact hi
  · exact (rf_active_ne ha hz).elim

def GBodyRunFramesW : Prop :=
  (TerminatingFunBoundedOn FinishReadyA (ofString "finish_child") K.«finish_child») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception») →
  (TerminatingFunBoundedOn EvmRunA (ofString "op_dispatch") K.«op_dispatch») →
  (FinishChildSpecA) →
  (FrameEpilogueSpecA) →
  (FrameExceptionSpecA) →
  (OpDispatchSpecW) →
  TerminatingFunBoundedOn EvmInvA (ofString "run_frames") K.«run_frames»

theorem gbody_run_frames_w : GBodyRunFramesW := by
  intro bf be bx bd hf he hx hd
  have hb : TerminatingProgBoundedOn (fun s => rfHeadInv s ∧ LoopActive rfCond s)
      rfBody (rfWalkCost rfBody) := by
    intro F s hc hi
    exact (rf_body_walk bf be bx bd hd hx he hf s).bounded s hc
      ⟨rf_active_inv hi.1 hi.2, rfl, rfl, rfl, rfl⟩
  have hl : TerminatingProgBoundedOn rfHeadInv (.while rfCond rfBody)
      ((evmPotMax + 1) * (rfWalkCost rfBody + 1)) := by
    refine TerminatingProgBoundedOn.while_rank_stationary_active (P := rfHeadInv) (N := evmPotMax) rfRank ?_ hb ?_ ?_
    · intro F s hi
      exact ⟨guestInv_congr (s := s) rfl rfl rfl rfl hi.1,
        hi.2.elim (fun h => Or.inl (localsFree_evmInvA s _ _ h)) (fun h => Or.inr h)⟩
    · intro F s _ hi ha
      have hp := rf_potential_bounded s (rf_active_inv hi ha)
      simp only [rfRank, if_neg (rf_active_ne ha)]
      omega
    · intro F s hc hi ha hflow
      have hnt : (evaluateHOLFiniteState (decClockHOLFinite s) rfBody).1 ≠ some .timeOut := by
        rcases hflow with h | h <;> rw [h] <;> simp
      have hpre : GPreA (evmPot s) (Wave8GuestInv.evmR s) (evmChain s).length (evmFp s) (decClockHOLFinite s) := by
        obtain ⟨e1, e2, e3, e4⟩ := evm_congr (s := s) (t := decClockHOLFinite s) rfl rfl
        exact ⟨localsFree_evmInvA s s.locals (s.clock - 1) (rf_active_inv hi ha), e1, e2, e3, e4⟩
      have hs := (rf_body_walk bf be bx bd hd hx he hf s).hoare.run (decClockHOLFinite s) hc hpre hnt hflow
      have hg := guestInv_evaluate (decClockHOLFinite s) rfBody
        (guestInv_congr (s := s) rfl rfl rfl rfl hi.1)
      rcases hs with ⟨hpost, hp⟩ | hz
      · refine ⟨⟨hg, Or.inl hpost⟩, Or.inl ?_⟩
        simp only [rfRank, if_neg (rf_active_ne ha)]
        split <;> omega
      · refine ⟨⟨hg, Or.inr hz⟩, Or.inl ?_⟩
        simp only [rfRank, if_pos hz, if_neg (rf_active_ne ha)]
        omega
  have hseq : TerminatingProgBoundedOn rfHeadInv _ _ := TerminatingProgBoundedOn.seq_guestInv_after hl (fun _ hi => hi.1)
    (TerminatingProgBoundedOn.of_clock (fun s => clock_return s (.const 0)))
  have hseq' : TerminatingProgBoundedOn EvmInvA
      (.seq (.while rfCond rfBody) (.return (.const 0)))
      ((evmPotMax + 1) * (rfWalkCost rfBody + 1)) := by
    intro F s hc hi
    simpa only [Nat.add_zero] using hseq s hc ⟨evmInvA_guestInv s hi, Or.inl hi⟩
  refine ⟨[], rfCode, .one, lookup_run_frames, ?_⟩
  rw [rfCode_eq]
  have hb0 : TerminatingProgBoundedOn EvmInvA _ _ := TerminatingProgBoundedOn.dec_on localsFree_evmInvA
    (ofString "go") .one (.const 1) hseq'
  intro F u hc hi
  simpa only [K.run_frames, rfCost_eq] using hb0 u hc hi

end RunFramesProofA

/-! ## 3b. Aligned `frame_epilogue` (re-walk of `StateRestoreEpilogue.frame_epilogue_spec`)

`frame_epilogue` only calls `state_restore`, whose proved body spec keeps every chain frame's
`(ec.1,280)`/`(ec.2,104)` cells, the chain, `ev`, and `frame_mem_ptr`; hence `HeadMemChainWF`. -/

section EpilogueA

open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (evmInv_lc evmChain_lc evmR_lc state_restore_body_spec)
open InitECandidate.Solver.Wave8Contracts.M08 (globN_eq_of_lookup)
open InitECandidate.Solver.Wave8Contracts.M23 (frameWF_bounds)
open InitECandidate.Solver.Wave8GuestInv.R16Shards (IvlUnhit memW_eq_of_ivlUnhit)

/-- `state_restore` keeps every chain frame's `(ec.1,280)`/`(ec.2,104)` cells, the chain, and all
globals other than `heap_ptr`/`journal_n`, so it preserves `HeadMemChainWF`. -/
theorem headMemChainWF_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) (hs : HeadMemChainWF s)
    (hchain : evmChain post = evmChain s)
    (hu : ∀ ec ∈ evmChain s, R16Shards.IvlUnhit s post (ec.1, 280) ∧
      R16Shards.IvlUnhit s post (ec.2, 104))
    (hev : globN post "ev" = globN s "ev")
    (hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr") :
    HeadMemChainWF post := by
  obtain ⟨hAs, S, hInvAt⟩ := hInv
  refine headMemChainWF_of_agree hs hchain ?_ hev hfmp
  intro ec hec
  have hwf := hInvAt.2.2.2.2.1 ec hec
  obtain ⟨he_lt, hc_lt, _, _⟩ := Wave8Contracts.M23.frameWF_bounds hAs.2 hwf
  have he8 : ec.1 % 8 = 0 := (hwf.1 (ec.1, 280) (by simp)).2.1
  have hc8 : ec.2 % 8 = 0 := (hwf.1 (ec.2, 104) (by simp)).2.1
  obtain ⟨hue, huc⟩ := hu ec hec
  exact ⟨R16Shards.memW_eq_of_ivlUnhit hue (by omega) he_lt ⟨by omega, by omega⟩,
    R16Shards.memW_eq_of_ivlUnhit hue (by omega) he_lt ⟨by omega, by omega⟩,
    R16Shards.memW_eq_of_ivlUnhit hue (by omega) he_lt ⟨by omega, by omega⟩,
    R16Shards.memW_eq_of_ivlUnhit huc (by omega) hc_lt ⟨by omega, by omega⟩⟩

/-- Aligned `frame_epilogue` contract: `frame_epilogue_spec` plus `HeadMemChainWF`. -/
theorem frame_epilogue_spec_aligned : FrameEpilogueSpecA := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_epilogue, .one, R16Shards.StateRestoreEpilogue.lookup_frame_epilogue, ?_⟩
  intro F s hcode ⟨⟨hInv, hW⟩, hDone⟩ _ _ v hv
  have hbody : sourceFnBody Guest.Software.guestFn_frame_epilogue =
      .seq (.ite (.cmp .notEqual
          (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 160)]))
          (.const (BitVec.ofNat 64 0)))
        (.call (some (none, none)) (ofString "state_restore")
          [.load .one (.op .add [.var .global (ofString "cur_cont"), .const (BitVec.ofNat 64 24)])])
        .skip) (.return (.const 0)) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780] at hv
  rcases hite : evaluateHOLFiniteState s
      (.ite (.cmp .notEqual
          (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 160)]))
          (.const (BitVec.ofNat 64 0)))
        (.call (some (none, none)) (ofString "state_restore")
          [.load .one (.op .add [.var .global (ofString "cur_cont"), .const (BitVec.ofNat 64 24)])])
        .skip) with ⟨r_ite, m1⟩
  rw [hite] at hv
  cases r_ite with
  | some ri =>
    cases ri with
    | returned u =>
      exfalso; revert hite; rw [evaluateHOLFiniteState_ite]
      split
      · split
        · rw [evaluateHOLFiniteState_skip]; simp
        · rw [evaluateHOLFiniteState_call]
          rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ with _ | _
          · simp
          · dsimp only
            rcases lookupCodeHOLFinite s.code.lookup _ _ with _ | ⟨_, _, _⟩
            · simp
            · dsimp only; split
              · simp
              · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
                rcases res with _ | r
                · simp
                · cases r <;> (dsimp only; try split) <;> simp
      · simp
    | _ => simp at hv
  | none =>
    have hpost_eq : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 =
        emptyLocalsHOLFinite m1 := by
      rw [hbody, evaluateHOLFiniteState_seq_line780, hite]; dsimp only
      rw [evaluateHOLFiniteState_return]
      have hc0 : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
          (.const 0) = some (.val (.word 0)) := rfl
      have hle32 : sizeOfShapeWithContextHOL m1.structs
          (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by simp [shapeOfHOLExact]
      rw [hc0]; dsimp only; rw [if_pos hle32]
    change (EvmInv (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 ∧
      HeadMemChainWF (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2) ∧
      EvmDone (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 ∧
      (evmChain (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2).length =
        (evmChain s).length ∧
      evmR (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 ≤ evmR s
    rw [hpost_eq]
    rw [evaluateHOLFiniteState_ite] at hite
    revert hite
    split
    · split
      · rw [evaluateHOLFiniteState_skip]; intro hm1; injection hm1 with _ hm1_eq; subst hm1_eq
        exact ⟨⟨(R16Shards.StateRestoreEpilogue.evmInv_lc s _ s.clock).2 hInv,
          headMemChainWF_locals s _ _ hW⟩, hDone,
          by rw [emptyLocalsHOLFinite, R16Shards.StateRestoreEpilogue.evmChain_lc s _ s.clock],
          by rw [emptyLocalsHOLFinite, R16Shards.StateRestoreEpilogue.evmR_lc s _ s.clock]⟩
      · intro hm1_call
        obtain ⟨vals, body1, cal1, ret1, rv1, cpost1, _, hl1, hrun1, hm1_eq⟩ :=
          Wave8M19.Htab.call0_flow s _ _ (Or.inl (congrArg Prod.fst hm1_call))
        have hbody1 : body1 = sourceFnBody Guest.Software.guestFn_state_restore := by
          obtain ⟨_, _, hinst⟩ := lookupCode_installed (by rwa [← hcode] : lookupCodeHOLFinite originalRuntimeCode.lookup _ _ = _)
          rw [R16Shards.StateRestoreEpilogue.lookup_state_restore] at hinst
          exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1.symm
        subst hbody1
        have hInv0 := hInv
        obtain ⟨hAs, S, hInvAt⟩ := hInv
        have hInv_ce : EvmInv (callEntryStateHOLFinite s cal1) :=
          (evmInv_lc s cal1 (s.clock - 1)).2 ⟨hAs, S, hInvAt⟩
        obtain ⟨hInv_cp, _, hg_cp, hch_cp, hR_cp, hu_cp⟩ :=
          state_restore_body_spec (callEntryStateHOLFinite s cal1) hcode hInv_ce rv1 (by rw [hrun1])
        have hcpost_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
            (sourceFnBody Guest.Software.guestFn_state_restore)).2 = cpost1 := by rw [hrun1]
        rw [hcpost_eq] at hInv_cp hg_cp hch_cp hR_cp hu_cp
        change evmChain cpost1 = evmChain { s with locals := cal1, clock := s.clock - 1 } at hch_cp
        change ∀ ec ∈ evmChain { s with locals := cal1, clock := s.clock - 1 }, _ at hu_cp
        change evmR cpost1 = evmR { s with locals := cal1, clock := s.clock - 1 } at hR_cp
        rw [evmChain_lc s cal1 (s.clock - 1)] at hch_cp hu_cp
        rw [evmR_lc s cal1 (s.clock - 1)] at hR_cp
        have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
        obtain ⟨hu_ev, hu_cc⟩ := hu_cp _ hhead_mem
        have hev_eq : globN cpost1 "ev" = globN s "ev" :=
          globN_eq_of_lookup (hg_cp (ofString "ev") (by decide))
        have hcc_eq : globN cpost1 "cur_cont" = globN s "cur_cont" :=
          globN_eq_of_lookup (hg_cp (ofString "cur_cont") (by decide))
        have hhead_wf := hInvAt.2.2.2.2.1 (globN s "ev", globN s "cur_cont") hhead_mem
        obtain ⟨he_lt, hc_lt, _, _⟩ := frameWF_bounds hAs.2 hhead_wf
        have hev8 : (globN s "ev") % 8 = 0 := (hhead_wf.1 (globN s "ev", 280) (by simp)).2.1
        have hcc8 : (globN s "cur_cont") % 8 = 0 := (hhead_wf.1 (globN s "cur_cont", 104) (by simp)).2.1
        have hm_cc32 := memW_eq_of_ivlUnhit hu_cc (a := globN s "cur_cont" + 32) (by omega) hc_lt ⟨by omega, by omega⟩
        have hm_ev104 := memW_eq_of_ivlUnhit hu_ev (a := globN s "ev" + 104) (by omega) he_lt ⟨by omega, by omega⟩
        have hm_ev56 := memW_eq_of_ivlUnhit hu_ev (a := globN s "ev" + 56) (by omega) he_lt ⟨by omega, by omega⟩
        have hm_ev0 := memW_eq_of_ivlUnhit hu_ev (a := globN s "ev") (by omega) he_lt ⟨by omega, by omega⟩
        have hm1_eq' : m1 = { cpost1 with locals := s.locals } :=
          (Prod.mk.inj (hm1_call.symm.trans hm1_eq)).2
        have hm1_cpost : emptyLocalsHOLFinite m1 = { cpost1 with locals := HolFiniteMapExact.empty, clock := cpost1.clock } := by
          rw [hm1_eq']; rfl
        have hDone_post : EvmDone (emptyLocalsHOLFinite m1) := by
          rw [hm1_cpost]
          unfold EvmDone at hDone ⊢
          change memW cpost1 (globN cpost1 "cur_cont" + 32) ≠ 0 ∨
            memW cpost1 (globN cpost1 "ev" + 104) = 0 ∨ memW cpost1 (globN cpost1 "ev" + 56) ≤ memW cpost1 (globN cpost1 "ev")
          rw [hev_eq, hcc_eq, hm_cc32, hm_ev104, hm_ev56, hm_ev0]; exact hDone
        have hfmp_eq : globN cpost1 "frame_mem_ptr" = globN s "frame_mem_ptr" :=
          globN_eq_of_lookup (hg_cp (ofString "frame_mem_ptr") (by decide))
        have hW_cp : HeadMemChainWF cpost1 :=
          headMemChainWF_of_unhit hInv0 hW hch_cp hu_cp hev_eq hfmp_eq
        refine ⟨⟨hm1_cpost ▸ (evmInv_lc cpost1 _ cpost1.clock).2 hInv_cp,
          hm1_cpost ▸ headMemChainWF_locals cpost1 _ _ hW_cp⟩, hDone_post, ?_, ?_⟩
        · rw [hm1_cpost, evmChain_lc cpost1 _ cpost1.clock, hch_cp]
        · rw [hm1_cpost, evmR_lc cpost1 _ cpost1.clock, hR_cp]
    · simp

end EpilogueA

/-! ## 3c. Aligned `frame_exception` (re-walk of `R11Shards.frame_exception_exec`)

The R11 walk of `refill_frame_state_gas`, `frame_halt`, and `frame_exception`, with the extra
conclusion `HeadMemChainWF s → HeadMemChainWF post`: every store is in `headAllowedOffsets`,
discharged by `headMemChainWF_of_headAllowed`. -/

section ExceptionA

open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8GuestInv.R11Shards (ResumesR11 evmRR11 not_resumes_err
  store_res_not_resumes updW store_global_off_word memW_updW_same memW_updW_ne evm_head_globals
  refill_body_eq frame_halt_body_eq frame_exception_body_eq one_word_param_of_lookup
  lookup_refill_frame_state_gas lookup_frame_halt lookup_frame_exception headAllowedOffsets
  evmInv_of_head_status_gas_update)

theorem refill_exec_step_A {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (hres : ResumesR11 (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).1) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).2
    EvmInv post ∧ post.globals = s.globals ∧ evmChain post = evmChain s ∧ evmRR11 post ≤ evmRR11 s ∧
      (HeadMemChainWF s → HeadMemChainWF post) := by
  dsimp only
  obtain ⟨he_lt, _, ⟨evw, hevw_lk, hevw_nat⟩, _, hgas_sum⟩ := evm_head_globals hInv
  have hInv0 := hInv
  obtain ⟨hAR, S, _, _, _, _, hFWF, _⟩ := hInv0
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hrec_w := ((hFWF _ hhead).1 (globN s "ev", 280) (by simp)).2
  rw [refill_body_eq, evaluateHOLFiniteState_dec_total] at hres ⊢
  dsimp only at hres ⊢
  revert hres
  rcases hmsg_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 112])) with _ | msgVal
  · dsimp only; intro hres; exact absurd hres not_resumes_err
  · dsimp only
    by_cases hsh_msg : shapeEqHOL .one (shapeOfHOLExact msgVal) = true
    · rw [if_pos hsh_msg]; dsimp only; intro hres
      let s0 := setVarHOLFinite (ofString "msg") msgVal s
      let body0 : ProgHOL 64 :=
        .seq
          (.store (.op .add [.var .global (ofString "ev"), .const 64])
            (.op .add
              [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
               .load .one (.op .add [.var .global (ofString "ev"), .const 192])]))
          (.seq
            (.store (.op .add [.var .global (ofString "ev"), .const 72])
              (.load .one (.op .add [.var .local (ofString "msg"), .const 48])))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))
              (.return (.const 0))))
      change ResumesR11 (evaluateHOLFiniteState s0 body0).1 at hres
      change (let post := { (evaluateHOLFiniteState s0 body0).2 with
        locals := (evaluateHOLFiniteState s0 body0).2.locals.resVarEq
          (ofString "msg", s.locals.lookup (ofString "msg")) };
        EvmInv post ∧ post.globals = s.globals ∧ evmChain post = evmChain s ∧ evmRR11 post ≤ evmRR11 s ∧
          (HeadMemChainWF s → HeadMemChainWF post))
      dsimp only [body0] at hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      cases h1 : evaluateHOLFiniteState s0
          (.store (.op .add [.var .global (ofString "ev"), .const 64])
            (.op .add
              [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
               .load .one (.op .add [.var .global (ofString "ev"), .const 192])])) with
      | mk r1 s1 =>
        rw [h1] at hres; dsimp only at hres ⊢
        rcases r1 with _ | res1
        · obtain ⟨w1, hw1_ev, hs1_eq⟩ := store_global_off_word (t := s0) (post := s1)
            (gname := "ev") (gbase := globN s "ev") (off := 64) hevw_lk hevw_nat (by omega)
            (fun v hv => by
              simp only [evalHOLExact, wordOpHOL] at hv
              revert hv
              rcases @evalListHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a)) _ with _ | vs
              · simp
              · dsimp only; split
                · simp only [Option.map]
                  rcases wordOp .add (vs.map valueWord) with _ | w
                  · simp
                  · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                · simp) h1
          have hw1_sum : w1.toNat = memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
            obtain ⟨wg, hdom64, hmem64⟩ := hrec_w.2.2 8 (by omega)
            obtain ⟨wsp, hdom192, hmem192⟩ := hrec_w.2.2 24 (by omega)
            have h64_eq : globN s "ev" + 8 * 8 = globN s "ev" + 64 := by omega
            have h192_eq : globN s "ev" + 8 * 24 = globN s "ev" + 192 := by omega
            rw [h64_eq] at hdom64 hmem64; rw [h192_eq] at hdom192 hmem192
            have had64 : evw + (64 + 0) = BitVec.ofNat 64 (globN s "ev" + 64) := by
              apply BitVec.eq_of_toNat_eq
              have hz0 : (0 : BitVec 64).toNat = 0 := rfl
              have h64n : (64 : BitVec 64).toNat = 64 := rfl
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, h64n, Nat.add_zero,
                Nat.mod_eq_of_lt (show 64 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
            have had192 : evw + (192 + 0) = BitVec.ofNat 64 (globN s "ev" + 192) := by
              apply BitVec.eq_of_toNat_eq
              have hz0 : (0 : BitVec 64).toNat = 0 := rfl
              have h192n : (192 : BitVec 64).toNat = 192 := rfl
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, h192n, Nat.add_zero,
                Nat.mod_eq_of_lt (show 192 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
            have hsum_ev : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
                (.op .add
                  [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
                   .load .one (.op .add [.var .global (ofString "ev"), .const 192])]) =
                some (.val (.word (wg + (wsp + 0)))) := by
              have hml64 : @memLoadHOLExact 64 _ .one (BitVec.ofNat 64 (globN s "ev" + 64))
                  s0.memaddrs (fun a => Classical.propDecidable (s0.memaddrs a))
                  s0.memory s0.structs = some (.val (.word wg)) := by
                have hd0 : s0.memaddrs (BitVec.ofNat 64 (globN s "ev" + 64)) := hdom64
                have hm0 : s0.memory (BitVec.ofNat 64 (globN s "ev" + 64)) = .word wg := hmem64
                unfold memLoadHOLExact; rw [if_pos hd0, hm0]
              have hml192 : @memLoadHOLExact 64 _ .one (BitVec.ofNat 64 (globN s "ev" + 192))
                  s0.memaddrs (fun a => Classical.propDecidable (s0.memaddrs a))
                  s0.memory s0.structs = some (.val (.word wsp)) := by
                have hd0 : s0.memaddrs (BitVec.ofNat 64 (globN s "ev" + 192)) := hdom192
                have hm0 : s0.memory (BitVec.ofNat 64 (globN s "ev" + 192)) = .word wsp := hmem192
                unfold memLoadHOLExact; rw [if_pos hd0, hm0]
              have hwf0 : isWfShapeExactHOL s0.structs .one = true := rfl
              have hev_s0 : s0.globals.lookup (ofString "ev") = some (.val (.word evw)) := hevw_lk
              simp only [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact,
                hev_s0, hwf0, wordOpHOL, wordOp, valueIsWord, valueWord,
                List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
                had64, had192, hml64, hml192]
            rw [hsum_ev] at hw1_ev
            injection hw1_ev with h_a; injection h_a with h_b; injection h_b with h_c
            have hmw64 : memW s (globN s "ev" + 64) = wg.toNat := by unfold memW; rw [hmem64]
            have hmw192 : memW s (globN s "ev" + 192) = wsp.toNat := by unfold memW; rw [hmem192]
            rw [← h_c, hmw64, hmw192]
            have hz0 : (0 : BitVec 64).toNat = 0 := rfl
            simp only [BitVec.toNat_add, hz0, Nat.add_zero]
            rw [Nat.mod_eq_of_lt wsp.isLt, Nat.mod_eq_of_lt (by rw [← hmw64, ← hmw192]; omega)]
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          cases h2 : evaluateHOLFiniteState s1
              (.store (.op .add [.var .global (ofString "ev"), .const 72])
                (.load .one (.op .add [.var .local (ofString "msg"), .const 48]))) with
          | mk r2 s2 =>
            rw [h2] at hres; dsimp only at hres ⊢
            rcases r2 with _ | res2
            · obtain ⟨w2, _, hs2_eq⟩ := store_global_off_word (t := s1) (post := s2)
                (gname := "ev") (gbase := globN s "ev") (off := 72)
                (by rw [hs1_eq]; exact hevw_lk) hevw_nat (by omega)
                (fun v hv => by
                  have hml_word : ∀ (addr : BitVec 64) dom (dec : DecidablePred dom),
                      @memLoadHOLExact 64 _ .one addr dom dec s1.memory s1.structs = some v →
                      ∃ w : BitVec 64, v = .val (.word w) := by
                    intro addr dom dec hml
                    unfold memLoadHOLExact at hml
                    by_cases hd : dom addr
                    · rw [if_pos hd] at hml; injection hml with hv'
                      cases hm : s1.memory addr with
                      | word w => rw [hm] at hv'; exact ⟨w, hv'.symm⟩
                    · rw [if_neg hd] at hml; cases hml
                  unfold evalHOLExact at hv; revert hv
                  split
                  · split
                    · rename_i addr _; exact hml_word addr _ _
                    · simp
                  · simp) h2
              rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
              cases h3 : evaluateHOLFiniteState s2
                  (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0)) with
              | mk r3 s3 =>
                rw [h3] at hres; dsimp only at hres ⊢
                rcases r3 with _ | res3
                · obtain ⟨w3, hw3_ev, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
                    (gname := "ev") (gbase := globN s "ev") (off := 192)
                    (by rw [hs2_eq, hs1_eq]; exact hevw_lk) hevw_nat (by omega)
                    (fun v hv => by injection hv with hv'; exact ⟨0, hv'.symm⟩) h3
                  have hw3_zero : w3.toNat = 0 := by
                    change some (ValueHOL.val (.word 0)) = some (.val (.word w3)) at hw3_ev
                    injection hw3_ev with ha; injection ha with hb; injection hb with hc
                    rw [← hc]; rfl
                  rw [evaluateHOLFiniteState_return] at hres ⊢
                  dsimp only [evalHOLExact] at hres ⊢
                  have hle32 : sizeOfShapeWithContextHOL s3.structs
                      (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
                    simp [shapeOfHOLExact]
                  rw [if_pos hle32]; dsimp only
                  let post := { (emptyLocalsHOLFinite s3) with
                    locals := (emptyLocalsHOLFinite s3).locals.resVarEq
                      (ofString "msg", s.locals.lookup (ofString "msg")) }
                  have hGp : GuestInv post := by
                    have hmeta : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
                        post.shMemaddrs = s.shMemaddrs ∧ post.baseAddr = s.baseAddr := by
                      simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq, s0, setVarHOLFinite]
                    exact guestInv_congr hmeta.1 hmeta.2.1 hmeta.2.2.1 hmeta.2.2.2 hInv.1.1
                  have hglob : post.globals = s.globals := by
                    simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq, s0, setVarHOLFinite]
                  have hbe : post.be = s.be := by
                    simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq, s0, setVarHOLFinite]
                  have hmem_out : ∀ x : BitVec 64,
                      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
                      post.memory x = s.memory x := by
                    intro x hx
                    change s3.memory x = s.memory x
                    rw [hs3_eq, hs2_eq, hs1_eq]
                    have hn192 : x ≠ BitVec.ofNat 64 (globN s "ev" + 192) := hx _ (by simp [headAllowedOffsets])
                    have hn72 : x ≠ BitVec.ofNat 64 (globN s "ev" + 72) := hx _ (by simp [headAllowedOffsets])
                    have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) := hx _ (by simp [headAllowedOffsets])
                    simp [updW, hn192, hn72, hn64, s0, setVarHOLFinite]
                  have hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
                      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
                    have hm192 : memW post (globN s "ev" + 192) = w3.toNat := by
                      change memW s3 (globN s "ev" + 192) = w3.toNat
                      rw [hs3_eq]; exact memW_updW_same s2 _ w3
                    have hm64 : memW post (globN s "ev" + 64) = w1.toNat := by
                      change memW s3 (globN s "ev" + 64) = w1.toNat
                      rw [hs3_eq, memW_updW_ne s2 _ _ w3 (by omega) (by omega) (by omega),
                          hs2_eq, memW_updW_ne s1 _ _ w2 (by omega) (by omega) (by omega),
                          hs1_eq, memW_updW_same s0 _ w1]
                    rw [hm64, hm192, hw1_sum, hw3_zero]; omega
                  obtain ⟨hEp, hch_eq, hsum_le⟩ :=
                    evmInv_of_head_status_gas_update hInv hGp hglob hbe hmem_out hgas_le
                  exact ⟨hEp, hglob, hch_eq, hsum_le,
                    fun hW => headMemChainWF_of_headAllowed hInv hW hglob hch_eq hmem_out⟩
                · exact absurd hres (store_res_not_resumes h3)
            · exact absurd hres (store_res_not_resumes h2)
        · exact absurd hres (store_res_not_resumes h1)
    · rw [if_neg hsh_msg]; dsimp only; intro hres; exact absurd hres not_resumes_err

theorem frame_halt_exec_step_A {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) {w_err : BitVec 64}
    (hw_err : s.locals.lookup (ofString "err") = some (.val (.word w_err)))
    (hres : ResumesR11 (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_halt)).1) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_halt)).2
    EvmInv post ∧ post.globals = s.globals ∧ evmChain post = evmChain s ∧ evmRR11 post ≤ evmRR11 s ∧
      (HeadMemChainWF s → HeadMemChainWF post) := by
  dsimp only
  obtain ⟨he_lt, _, ⟨evw, hevw_lk, hevw_nat⟩, _, _⟩ := evm_head_globals hInv
  rw [frame_halt_body_eq, evaluateHOLFiniteState_seq_line780] at hres ⊢
  cases h1 : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const 184])
        (.op .add
          [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
           .load .one (.op .add [.var .global (ofString "ev"), .const 64])])) with
  | mk r1 s1 =>
    rw [h1] at hres; dsimp only at hres ⊢
    rcases r1 with _ | res1
    · obtain ⟨w1, _, hs1_eq⟩ := store_global_off_word (t := s) (post := s1)
        (gname := "ev") (gbase := globN s "ev") (off := 184) hevw_lk hevw_nat (by omega)
        (fun v hv => by
          simp only [evalHOLExact, wordOpHOL] at hv; revert hv
          rcases @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) _ with _ | vs
          · simp
          · dsimp only; split
            · simp only [Option.map]
              rcases wordOp .add (vs.map valueWord) with _ | w
              · simp
              · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
            · simp) h1
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      cases h2 : evaluateHOLFiniteState s1
          (.store (.op .add [.var .global (ofString "ev"), .const 64]) (.const 0)) with
      | mk r2 s2 =>
        rw [h2] at hres; dsimp only at hres ⊢
        rcases r2 with _ | res2
        · obtain ⟨w2, hw2_ev, hs2_eq⟩ := store_global_off_word (t := s1) (post := s2)
            (gname := "ev") (gbase := globN s "ev") (off := 64)
            (by rw [hs1_eq]; exact hevw_lk) hevw_nat (by omega)
            (fun v hv => by injection hv with hv'; exact ⟨0, hv'.symm⟩) h2
          have hw2_zero : w2.toNat = 0 := by
            change some (ValueHOL.val (.word 0)) = some (.val (.word w2)) at hw2_ev
            injection hw2_ev with ha; injection ha with hb; injection hb with hc
            rw [← hc]; rfl
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          cases h3 : evaluateHOLFiniteState s2
              (.store (.op .add [.var .global (ofString "ev"), .const 160])
                (.var .local (ofString "err"))) with
          | mk r3 s3 =>
            rw [h3] at hres; dsimp only at hres ⊢
            rcases r3 with _ | res3
            · obtain ⟨w3, _, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
                (gname := "ev") (gbase := globN s "ev") (off := 160)
                (by rw [hs2_eq, hs1_eq]; exact hevw_lk) hevw_nat (by omega)
                (fun v hv => by
                  change s2.locals.lookup (ofString "err") = some v at hv
                  rw [hs2_eq, hs1_eq] at hv; dsimp only at hv; rw [hw_err] at hv
                  injection hv with hv'; exact ⟨w_err, hv'.symm⟩) h3
              rw [evaluateHOLFiniteState_return] at hres ⊢
              dsimp only [evalHOLExact] at hres ⊢
              have hle32 : sizeOfShapeWithContextHOL s3.structs
                  (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
                simp [shapeOfHOLExact]
              rw [if_pos hle32]; dsimp only
              let post := emptyLocalsHOLFinite s3
              have hGp : GuestInv post := by
                have hmeta : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
                    post.shMemaddrs = s.shMemaddrs ∧ post.baseAddr = s.baseAddr := by
                  simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq]
                exact guestInv_congr hmeta.1 hmeta.2.1 hmeta.2.2.1 hmeta.2.2.2 hInv.1.1
              have hglob : post.globals = s.globals := by
                simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq]
              have hbe : post.be = s.be := by
                simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq]
              have hmem_out : ∀ x : BitVec 64,
                  (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
                  post.memory x = s.memory x := by
                intro x hx
                change s3.memory x = s.memory x
                rw [hs3_eq, hs2_eq, hs1_eq]
                have hn160 : x ≠ BitVec.ofNat 64 (globN s "ev" + 160) := hx _ (by simp [headAllowedOffsets])
                have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) := hx _ (by simp [headAllowedOffsets])
                have hn184 : x ≠ BitVec.ofNat 64 (globN s "ev" + 184) := hx _ (by simp [headAllowedOffsets])
                simp [updW, hn160, hn64, hn184]
              have hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
                  memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
                have hm64 : memW post (globN s "ev" + 64) = w2.toNat := by
                  change memW s3 (globN s "ev" + 64) = w2.toNat
                  rw [hs3_eq, memW_updW_ne s2 _ _ w3 (by omega) (by omega) (by omega),
                      hs2_eq, memW_updW_same s1 _ w2]
                have hm192 : memW post (globN s "ev" + 192) = memW s (globN s "ev" + 192) := by
                  change memW s3 (globN s "ev" + 192) = memW s (globN s "ev" + 192)
                  rw [hs3_eq, memW_updW_ne s2 _ _ w3 (by omega) (by omega) (by omega),
                      hs2_eq, memW_updW_ne s1 _ _ w2 (by omega) (by omega) (by omega),
                      hs1_eq, memW_updW_ne s _ _ w1 (by omega) (by omega) (by omega)]
                rw [hm64, hw2_zero, hm192]; omega
              obtain ⟨hEp, hch_eq, hsum_le⟩ :=
                evmInv_of_head_status_gas_update hInv hGp hglob hbe hmem_out hgas_le
              exact ⟨hEp, hglob, hch_eq, hsum_le,
                fun hW => headMemChainWF_of_headAllowed hInv hW hglob hch_eq hmem_out⟩
            · exact absurd hres (store_res_not_resumes h3)
        · exact absurd hres (store_res_not_resumes h2)
    · exact absurd hres (store_res_not_resumes h1)

private theorem call0_returned_inv {F : Type} {s post_call : PanSemStateFiniteExact 64 F}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) fname args) = (none, post_call)) :
    ∃ values body callee ret v cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), cpost) ∧
      post_call = { cpost with locals := s.locals } := by
  rw [evaluateHOLFiniteState_call] at hcall
  revert hcall
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · simp
    · dsimp only
      by_cases hz : s.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, cpost⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned v =>
            dsimp only; split
            · intro h; injection h with _ hp
              exact ⟨values, body, callee, ret, v, cpost, rfl, hl, hrun, hp.symm⟩
            · simp
          | _ => simp

private theorem evmChain_congr_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmChain { s with locals := L, clock := k } = evmChain s := by
  have hcf : ∀ (fuel e c : Nat),
      evmChainFrom { s with locals := L, clock := k } fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih => intros; simp only [evmChainFrom, ih]; rfl
  exact hcf _ _ _

private theorem evmRR11_congr_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmRR11 { s with locals := L, clock := k } = evmRR11 s := by
  unfold evmRR11; rw [evmChain_congr_lc s L k]; rfl

private theorem evmInv_congr_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : EvmInv s) :
    EvmInv { s with locals := L, clock := k } := by
  have hf : ∀ (nodes : Nat) (Fr : List Nat) (head : Nat),
      FreeChain { s with locals := L, clock := k } nodes head Fr ↔ FreeChain s nodes head Fr := by
    intro nodes Fr; induction Fr with
    | nil => intro _; exact Iff.rfl
    | cons _ rest ih => intro _; exact and_congr Iff.rfl (ih _)
  have hw : ∀ t, HtabWF { s with locals := L, clock := k } t ↔ HtabWF s t := by
    intro t; simp only [HtabWF, hf]; exact Iff.rfl
  have ht : ∀ S, TablesTyped { s with locals := L, clock := k } S ↔ TablesTyped s S := by
    intro S; simp only [TablesTyped, hw]; exact Iff.rfl
  have hwt : ∀ S, WorldTyped { s with locals := L, clock := k } S ↔ WorldTyped s S := by
    intro S; simp only [WorldTyped, ht]; exact Iff.rfl
  have hch : evmChain { s with locals := L, clock := k } = evmChain s := evmChain_congr_lc s L k
  have har : ArenaReady { s with locals := L, clock := k } ↔ ArenaReady s :=
    ⟨fun h0 => ⟨guestInv_congr (s := { s with locals := L, clock := k }) rfl rfl rfl rfl h0.1, h0.2⟩,
     fun h0 => ⟨guestInv_with_locals_clock s L k h0.1, h0.2⟩⟩
  simp only [EvmInv, FrameWF, MsgOwned, hwt, har, hch] at h ⊢
  exact h

private theorem seq_returned_inv {F : Type} {s : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64}
    {v : ValueHOL 64}
    (h : (evaluateHOLFiniteState s (.seq p1 p2)).1 = some (.returned v))
    (hn1 : ∀ u, (evaluateHOLFiniteState s p1).1 ≠ some (.returned u)) :
    ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
      evaluateHOLFiniteState m p2 = evaluateHOLFiniteState s (.seq p1 p2) := by
  have hseq := evaluateHOLFiniteState_seq_line780 s p1 p2
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  rw [hr1] at hseq
  cases r1 with
  | none => exact ⟨m, rfl, hseq.symm⟩
  | some r =>
    rw [hseq] at h
    dsimp only at h
    injection h with hr; subst hr
    exact absurd hr1 (fun h' => hn1 v (by rw [h']))

private theorem call0_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F) (fn : MlS)
    (args : List (ExpHOL 64)) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | _
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fn _ with _ | ⟨_, _, _⟩
    · simp
    · dsimp only; split
      · simp
      · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned _ => dsimp only; split <;> simp
          | _ => simp

private theorem store_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64)
    (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.store d e)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split <;> simp
    · simp
  · simp

private theorem ite_ne_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {c : ExpHOL 64} {y n : ProgHOL 64}
    (hy : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t y).1 ≠ some (.returned u))
    (hn : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t n).1 ≠ some (.returned u))
    (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.ite c y n)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn s u
    · exact hy s u
  · simp

private theorem seq_ne_returned {p1 p2 : ProgHOL 64}
    (h1 : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t p1).1 ≠ some (.returned u))
    (h2 : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t p2).1 ≠ some (.returned u))
    {F : Type} (s : PanSemStateFiniteExact 64 F) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  cases r1 with
  | none => exact h2 m u
  | some r =>
    dsimp only; intro hr
    exact h1 s u (by rw [h]; exact hr)

theorem frame_exception_exec_A {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (w_emp w_err : BitVec 64) (hw_emp : GlobalWord s "evm_empty" w_emp)
    (hw_err : s.locals.lookup (ofString "err") = some (.val (.word w_err)))
    (v : ValueHOL 64)
    (hv : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_exception)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_exception)).2
    EvmInv post ∧ EvmDone post ∧
      (evmChain post).length = (evmChain s).length ∧ evmRR11 post ≤ evmRR11 s ∧
      (HeadMemChainWF s → HeadMemChainWF post) := by
  dsimp only
  rw [frame_exception_body_eq] at hv ⊢
  -- Step 1: call `refill_frame_state_gas`
  obtain ⟨m1, hs1_call, hrest1⟩ := seq_returned_inv hv (call0_ne_returned s _ _)
  have hpost_eq1 := congrArg Prod.snd hrest1.symm
  rw [← hrest1] at hv; rw [hpost_eq1]; clear hrest1 hpost_eq1
  obtain ⟨vals1, body1, cal1, ret1, rv1, cpost1, _, hl1, hrun1, hm1_eq⟩ := call0_returned_inv hs1_call
  have hcode_lk1 : s.code.lookup (ofString "refill_frame_state_gas") =
      some ([], sourceFnBody Guest.Software.guestFn_refill_frame_state_gas, .one) := by
    rw [hcode]; exact lookup_refill_frame_state_gas
  have hbody1 : body1 = sourceFnBody Guest.Software.guestFn_refill_frame_state_gas :=
    lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ _ _ _ _ _ hcode_lk1 hl1
  subst hbody1
  have hInv_ce1 : EvmInv (callEntryStateHOLFinite s cal1) := evmInv_congr_lc s cal1 (s.clock - 1) hInv
  have hres1 : ResumesR11 (evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
      (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).1 := by
    rw [hrun1]; exact Or.inl ⟨rv1, rfl⟩
  obtain ⟨hInv_cp1, hglob_cp1, hch_cp1, hR_cp1, hW_cp1⟩ := refill_exec_step_A hInv_ce1 hres1
  have hcpost1_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
      (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).2 = cpost1 := by
    rw [hrun1]
  rw [hcpost1_eq] at hInv_cp1 hglob_cp1 hch_cp1 hR_cp1 hW_cp1
  subst hm1_eq
  let s1 := ({ cpost1 with locals := s.locals } : PanSemStateFiniteExact 64 F)
  have hInv1 : EvmInv s1 := evmInv_congr_lc cpost1 s.locals cpost1.clock hInv_cp1
  have hglob1 : s1.globals = s.globals := hglob_cp1
  have hW1 : HeadMemChainWF s → HeadMemChainWF s1 := fun hW =>
    (headMemChainWF_congr (s := cpost1) (t := s1) rfl rfl).2
      (hW_cp1 ((headMemChainWF_congr (s := s) (t := callEntryStateHOLFinite s cal1) rfl rfl).2 hW))
  have hch1 : evmChain s1 = evmChain s := by
    have h1 : evmChain s1 = evmChain cpost1 := evmChain_congr_lc cpost1 s.locals cpost1.clock
    have h2 : evmChain (callEntryStateHOLFinite s cal1) = evmChain s := evmChain_congr_lc s cal1 (s.clock - 1)
    exact h1.trans (hch_cp1.trans h2)
  have hR1 : evmRR11 s1 ≤ evmRR11 s := by
    have h1 : evmRR11 s1 = evmRR11 cpost1 := evmRR11_congr_lc cpost1 s.locals cpost1.clock
    have h2 : evmRR11 (callEntryStateHOLFinite s cal1) = evmRR11 s := evmRR11_congr_lc s cal1 (s.clock - 1)
    omega
  have hcode1 : s1.code = originalRuntimeCode := by
    have hm := (PanRunBounded.evaluateHOLFiniteState_metadata s
      (.call (some (none, none)) (ofString "refill_frame_state_gas") [])).1
    rw [hs1_call] at hm; exact hm.trans hcode
  -- Step 2: `ite (err != 1) ... ...`
  have hite_noret : ∀ u, (evaluateHOLFiniteState s1
      (.ite (.cmp .notEqual (.var .local (ofString "err")) (.const 1))
        (.seq (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")])
          (.seq (.store (.op .add [.var .global (ofString "ev"), .const 120]) (.var .global (ofString "evm_empty")))
            (.store (.op .add [.var .global (ofString "ev"), .const 128]) (.const 0))))
        (.store (.op .add [.var .global (ofString "ev"), .const 160]) (.var .local (ofString "err"))))).1 ≠ some (.returned u) :=
    ite_ne_returned
      (seq_ne_returned (fun t u => call0_ne_returned t _ _ u)
        (seq_ne_returned (fun t u => store_ne_returned t _ _ u) (fun t u => store_ne_returned t _ _ u)))
      (fun t u => store_ne_returned t _ _ u)
  obtain ⟨s2, hs2_ite, hrest2⟩ := seq_returned_inv hv hite_noret
  have hpost_eq2 := congrArg Prod.snd hrest2.symm
  rw [← hrest2] at hv; rw [hpost_eq2]; clear hrest2 hpost_eq2
  -- Show `EvmInv s2 ∧ s2.globals = s1.globals ∧ evmChain s2 = evmChain s1 ∧ evmRR11 s2 ≤ evmRR11 s1`
  have hs2_props : EvmInv s2 ∧ s2.globals = s1.globals ∧ evmChain s2 = evmChain s1 ∧ evmRR11 s2 ≤ evmRR11 s1 ∧
      (HeadMemChainWF s1 → HeadMemChainWF s2) := by
    obtain ⟨he_lt1, _, ⟨evw1, hevw1_lk, hevw1_nat⟩, _, _⟩ := evm_head_globals hInv1
    have herr_s1 : s1.locals.lookup (ofString "err") = some (.val (.word w_err)) := hw_err
    rw [evaluateHOLFiniteState_ite] at hs2_ite
    have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "err")) (.const 1)) =
        some (.val (.word (if w_err ≠ 1 then 1 else 0))) := by
      simp [evalHOLExact, herr_s1, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp] at hs2_ite; dsimp only at hs2_ite
    by_cases hw1 : w_err = 1
    · -- `err == 1`: runs `store (ev + 160) err`
      subst hw1; simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hs2_ite
      obtain ⟨w160, _, rfl⟩ := store_global_off_word (t := s1) (post := s2)
        (gname := "ev") (gbase := globN s1 "ev") (off := 160) hevw1_lk hevw1_nat (by omega)
        (fun v0 hv0 => by
          change s1.locals.lookup (ofString "err") = some v0 at hv0
          rw [herr_s1] at hv0; injection hv0 with hv'; exact ⟨1, hv'.symm⟩) hs2_ite
      let post2 := { s1 with memory := updW s1.memory (BitVec.ofNat 64 (globN s1 "ev" + 160)) w160 }
      have hGp2 : GuestInv post2 := guestInv_congr (s := s1) rfl rfl rfl rfl hInv1.1.1
      have hmem2 : ∀ x : BitVec 64,
          (∀ addr ∈ headAllowedOffsets (globN s1 "ev") (globN s1 "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
          post2.memory x = s1.memory x := by
        intro x hx
        have hn160 : x ≠ BitVec.ofNat 64 (globN s1 "ev" + 160) := hx _ (by simp [headAllowedOffsets])
        simp [post2, updW, hn160]
      have hgas2 : memW post2 (globN s1 "ev" + 64) + memW post2 (globN s1 "ev" + 192) ≤
          memW s1 (globN s1 "ev" + 64) + memW s1 (globN s1 "ev" + 192) := by
        rw [memW_updW_ne s1 _ _ w160 (by omega) (by omega) (by omega),
            memW_updW_ne s1 _ _ w160 (by omega) (by omega) (by omega)]
      obtain ⟨hEp2, hch2, hR2⟩ := evmInv_of_head_status_gas_update hInv1 hGp2 rfl rfl hmem2 hgas2
      exact ⟨hEp2, rfl, hch2, hR2, fun hW => headMemChainWF_of_headAllowed hInv1 hW rfl hch2 hmem2⟩
    · -- `err != 1`: runs `call frame_halt [err]; store (ev+120) evm_empty; store (ev+128) 0`
      have h10 : ((1 : BitVec 64) = 0) = False := by decide
      simp only [ne_eq, hw1, not_false_eq_true, ↓reduceIte, h10] at hs2_ite
      rw [evaluateHOLFiniteState_seq_line780] at hs2_ite
      rcases hfh : evaluateHOLFiniteState s1
          (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")]) with ⟨rfh, mfh⟩
      rw [hfh] at hs2_ite
      rcases rfh with _ | r_bad
      · dsimp only at hs2_ite
        obtain ⟨vals_fh, body_fh, cal_fh, ret_fh, rv_fh, cpost_fh, hargs_fh, hl_fh, hrun_fh, hmfh_eq⟩ :=
          call0_returned_inv hfh
        subst hmfh_eq
        have hcode1_fh : s1.code.lookup (ofString "frame_halt") =
            some ([(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_halt, .one) := by
          rw [hcode1]; exact lookup_frame_halt
        have hbody_fh : body_fh = sourceFnBody Guest.Software.guestFn_frame_halt :=
          lookupCodeHOLFinite_installed_body s1.code.lookup _ _ _ _ _ _ _ _ hcode1_fh hl_fh
        subst hbody_fh
        have hret_fh : ret_fh = .one := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            s1.code.lookup (ofString "frame_halt") vals_fh (sourceFnBody Guest.Software.guestFn_frame_halt)
            cal_fh ret_fh hl_fh
          simp only [Flapjack.lookupCodeHOLExact, hcode1_fh] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst hret_fh
        obtain ⟨w_ce_err, hw_ce_err⟩ := one_word_param_of_lookup lookup_frame_halt
          ⟨vals_fh, by rwa [hcode1] at hl_fh⟩
        have hInv_ce_fh : EvmInv (callEntryStateHOLFinite s1 cal_fh) :=
          evmInv_congr_lc s1 cal_fh (s1.clock - 1) hInv1
        have hres_fh : ResumesR11 (evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal_fh)
            (sourceFnBody Guest.Software.guestFn_frame_halt)).1 := by
          rw [hrun_fh]; exact Or.inl ⟨rv_fh, rfl⟩
        obtain ⟨hInv_cp_fh, hglob_cp_fh, hch_cp_fh, hR_cp_fh, hW_cp_fh⟩ :=
          frame_halt_exec_step_A hInv_ce_fh hw_ce_err hres_fh
        have hcpost_fh_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal_fh)
            (sourceFnBody Guest.Software.guestFn_frame_halt)).2 = cpost_fh := by
          rw [hrun_fh]
        rw [hcpost_fh_eq] at hInv_cp_fh hglob_cp_fh hch_cp_fh hR_cp_fh hW_cp_fh
        let sfh := ({ cpost_fh with locals := s1.locals } : PanSemStateFiniteExact 64 F)
        have hInv_fh : EvmInv sfh := evmInv_congr_lc cpost_fh s1.locals cpost_fh.clock hInv_cp_fh
        have hglob_fh : sfh.globals = s1.globals := hglob_cp_fh
        have hch_fh : evmChain sfh = evmChain s1 := by
          have h1 : evmChain sfh = evmChain cpost_fh := evmChain_congr_lc cpost_fh s1.locals cpost_fh.clock
          have h2 : evmChain (callEntryStateHOLFinite s1 cal_fh) = evmChain s1 := evmChain_congr_lc s1 cal_fh (s1.clock - 1)
          exact h1.trans (hch_cp_fh.trans h2)
        have hR_fh : evmRR11 sfh ≤ evmRR11 s1 := by
          have h1 : evmRR11 sfh = evmRR11 cpost_fh := evmRR11_congr_lc cpost_fh s1.locals cpost_fh.clock
          have h2 : evmRR11 (callEntryStateHOLFinite s1 cal_fh) = evmRR11 s1 := evmRR11_congr_lc s1 cal_fh (s1.clock - 1)
          omega
        -- Now two stores: `ev + 120 := evm_empty` and `ev + 128 := 0`
        rw [evaluateHOLFiniteState_seq_line780] at hs2_ite
        rcases hst120 : evaluateHOLFiniteState sfh
            (.store (.op .add [.var .global (ofString "ev"), .const 120])
              (.var .global (ofString "evm_empty"))) with ⟨r120, s120⟩
        rw [hst120] at hs2_ite
        rcases r120 with _ | _
        · dsimp only at hs2_ite
          have hev_sfh : globN sfh "ev" = globN s1 "ev" := by simp [globN, hglob_fh]
          have hcc_sfh : globN sfh "cur_cont" = globN s1 "cur_cont" := by simp [globN, hglob_fh]
          have hemp_sfh : sfh.globals.lookup (ofString "evm_empty") = some (.val (.word w_emp)) := by
            rw [hglob_fh, hglob1]; exact hw_emp
          obtain ⟨w120, _, hs120_eq⟩ := store_global_off_word (t := sfh) (post := s120)
            (gname := "ev") (gbase := globN s1 "ev") (off := 120)
            (by rw [hglob_fh]; exact hevw1_lk) hevw1_nat (by omega)
            (fun v0 hv0 => by
              change sfh.globals.lookup (ofString "evm_empty") = some v0 at hv0
              rw [hemp_sfh] at hv0; injection hv0 with hv'; exact ⟨w_emp, hv'.symm⟩) hst120
          obtain ⟨w128, _, hs2_eq⟩ := store_global_off_word (t := s120) (post := s2)
            (gname := "ev") (gbase := globN s1 "ev") (off := 128)
            (by rw [hs120_eq, hglob_fh]; exact hevw1_lk) hevw1_nat (by omega)
            (fun v0 hv0 => by
              simp [evalHOLExact] at hv0; exact ⟨0, hv0.symm⟩) hs2_ite
          have hGp_s2 : GuestInv s2 := by
            rw [hs2_eq, hs120_eq]
            exact guestInv_congr (s := sfh) rfl rfl rfl rfl hInv_fh.1.1
          have hglob_s2 : s2.globals = sfh.globals := by rw [hs2_eq, hs120_eq]
          have hbe_s2 : s2.be = sfh.be := by rw [hs2_eq, hs120_eq]
          have hmem_s2 : ∀ x : BitVec 64,
              (∀ addr ∈ headAllowedOffsets (globN sfh "ev") (globN sfh "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
              s2.memory x = sfh.memory x := by
            intro x hx
            rw [hs2_eq, hs120_eq]
            have hn120 : x ≠ BitVec.ofNat 64 (globN s1 "ev" + 120) := by
              rw [← hev_sfh]; exact hx _ (by simp [headAllowedOffsets])
            have hn128 : x ≠ BitVec.ofNat 64 (globN s1 "ev" + 128) := by
              rw [← hev_sfh]; exact hx _ (by simp [headAllowedOffsets])
            simp [updW, hn120, hn128]
          have hgas_s2 : memW s2 (globN sfh "ev" + 64) + memW s2 (globN sfh "ev" + 192) ≤
              memW sfh (globN sfh "ev" + 64) + memW sfh (globN sfh "ev" + 192) := by
            rw [hev_sfh, hs2_eq,
                memW_updW_ne s120 _ _ w128 (by omega) (by omega) (by omega),
                memW_updW_ne s120 _ _ w128 (by omega) (by omega) (by omega),
                hs120_eq,
                memW_updW_ne sfh _ _ w120 (by omega) (by omega) (by omega),
                memW_updW_ne sfh _ _ w120 (by omega) (by omega) (by omega)]
          obtain ⟨hEp_s2, hch_s2, hR_s2⟩ :=
            evmInv_of_head_status_gas_update hInv_fh hGp_s2 hglob_s2 hbe_s2 hmem_s2 hgas_s2
          have hW_fh : HeadMemChainWF s1 → HeadMemChainWF sfh := fun hW =>
            (headMemChainWF_congr (s := cpost_fh) (t := sfh) rfl rfl).2
              (hW_cp_fh ((headMemChainWF_congr (s := s1) (t := callEntryStateHOLFinite s1 cal_fh) rfl rfl).2 hW))
          exact ⟨hEp_s2, hglob_s2.trans hglob_fh, hch_s2.trans hch_fh, le_trans hR_s2 hR_fh,
            fun hW => headMemChainWF_of_headAllowed hInv_fh (hW_fh hW) hglob_s2 hch_s2 hmem_s2⟩
        · cases hs2_ite
      · cases hs2_ite
  -- Step 3: `store (cur_cont + 32) 1; return 0`
  obtain ⟨hInv2, hglob2, hch2, hR2, hW2⟩ := hs2_props
  obtain ⟨s3, hs3_st, hrest3⟩ := seq_returned_inv hv (store_ne_returned s2 _ _)
  have hpost_eq3 := congrArg Prod.snd hrest3.symm
  rw [← hrest3] at hv; rw [hpost_eq3]; clear hrest3 hpost_eq3
  obtain ⟨he_lt2, hc_lt2, _, ⟨ccw2, hccw2_lk, hccw2_nat⟩, _⟩ := evm_head_globals hInv2
  obtain ⟨w32, hw32_eval, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
    (gname := "cur_cont") (gbase := globN s2 "cur_cont") (off := 32) hccw2_lk hccw2_nat (by omega)
    (fun v0 hv0 => by simp [evalHOLExact] at hv0; exact ⟨1, hv0.symm⟩) hs3_st
  have hw32_eq1 : w32 = 1 := by
    simp [evalHOLExact] at hw32_eval
    exact hw32_eval.symm
  rw [evaluateHOLFiniteState_return] at hv ⊢
  have hc0 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.const 0) = some (.val (.word 0)) := rfl
  rw [hc0] at hv ⊢; dsimp only at hv ⊢
  have hle32 : sizeOfShapeWithContextHOL s3.structs
      (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hle32]; dsimp only
  let post := emptyLocalsHOLFinite s3
  have hGp_post : GuestInv post := by
    simp only [post, emptyLocalsHOLFinite, hs3_eq]
    exact guestInv_congr (s := s2) rfl rfl rfl rfl hInv2.1.1
  have hglob_post : post.globals = s2.globals := by simp [post, emptyLocalsHOLFinite, hs3_eq]
  have hbe_post : post.be = s2.be := by simp [post, emptyLocalsHOLFinite, hs3_eq]
  have hmem_post : ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s2 "ev") (globN s2 "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
      post.memory x = s2.memory x := by
    intro x hx
    change s3.memory x = s2.memory x
    rw [hs3_eq]
    have hn32 : x ≠ BitVec.ofNat 64 (globN s2 "cur_cont" + 32) := hx _ (by simp [headAllowedOffsets])
    simp [updW, hn32]
  have hgas_post : memW post (globN s2 "ev" + 64) + memW post (globN s2 "ev" + 192) ≤
      memW s2 (globN s2 "ev" + 64) + memW s2 (globN s2 "ev" + 192) := by
    have hdisj_ec2 : Disj (globN s2 "ev", 280) (globN s2 "cur_cont", 104) := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hP2, _⟩ := hInv2
      have hfl := List.pairwise_flatten.mp hP2
      have hmem0 : (globN s2 "ev", globN s2 "cur_cont") ∈ evmChain s2 := by simp [evmChain, evmChainFrom]
      have hp0 := hfl.1 _ (List.mem_map_of_mem hmem0)
      exact (List.pairwise_cons.mp (List.pairwise_append.mp hp0).1).1 _ (by simp)
    have hne64 : globN s2 "ev" + 64 ≠ globN s2 "cur_cont" + 32 := by
      unfold Disj at hdisj_ec2; dsimp only at hdisj_ec2
      rcases hdisj_ec2 with h | h | h | h <;> omega
    have hne192 : globN s2 "ev" + 192 ≠ globN s2 "cur_cont" + 32 := by
      unfold Disj at hdisj_ec2; dsimp only at hdisj_ec2
      rcases hdisj_ec2 with h | h | h | h <;> omega
    change memW s3 (globN s2 "ev" + 64) + memW s3 (globN s2 "ev" + 192) ≤ _
    rw [hs3_eq,
        memW_updW_ne s2 _ _ w32 (by omega) (by omega) hne64,
        memW_updW_ne s2 _ _ w32 (by omega) (by omega) hne192]
  obtain ⟨hEp_post, hch_post, hR_post⟩ :=
    evmInv_of_head_status_gas_update hInv2 hGp_post hglob_post hbe_post hmem_post hgas_post
  have hdone_post : EvmDone post := by
    left
    have hcc_post : globN post "cur_cont" = globN s2 "cur_cont" := by simp [globN, hglob_post]
    rw [hcc_post]
    change memW s3 (globN s2 "cur_cont" + 32) ≠ 0
    rw [hs3_eq, memW_updW_same, hw32_eq1]
    decide
  exact ⟨hEp_post, hdone_post, by rw [hch_post, hch2, hch1], le_trans hR_post (le_trans hR2 hR1),
    fun hW => headMemChainWF_of_headAllowed hInv2 (hW2 (hW1 hW)) hglob_post hch_post hmem_post⟩

/-- Aligned `frame_exception` contract: `frame_exception_spec` plus `HeadMemChainWF` (every
write of `frame_exception` lies in `headAllowedOffsets`, read by no cell of the invariant). -/
theorem frame_exception_spec_aligned : FrameExceptionSpecA := by
  refine ⟨[(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_exception, .one,
    lookup_frame_exception, ?_⟩
  intro F s hcode ⟨hInv, hW⟩ hex _ v hv
  obtain ⟨w_err, hw_err⟩ := one_word_param_of_lookup lookup_frame_exception hex
  obtain ⟨w_emp, hw_emp⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
  obtain ⟨h1, h2, h3, h4, h5⟩ := frame_exception_exec_A s hcode hInv w_emp w_err hw_emp hw_err v hv
  exact ⟨⟨h1, h5 hW⟩, h2, h3, h4⟩

end ExceptionA

/-! ## 3d. Aligned `finish_child` from its unaligned contract and its frame-memory footprint -/

/-- The unaligned `finish_child` contract (`ContractParts.C00.finish_child_spec`, shape only). -/
def FinishChildSpecU : Prop :=
  FunSpec FinishReady
    (fun s r post => ((∃ v, r = some (.returned v)) ∨ IsEvmErr r) →
      EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧
        Wave8GuestInv.evmR post ≤ Wave8GuestInv.evmR s)
    (ofString "finish_child")

/-- Frame-memory footprint of `finish_child` (`Guest/SoftwareAst.lean:18572`): the chain loses
its head, `ev := ld(rec)`, `frame_mem_release(ld(rec+56))` sets `frame_mem_ptr` to the child's
recorded mark, and no `+24/+32/+40` frame cell or `+56` continuation cell of a surviving frame
is written (`memcpy` writes inside the parent's EVM memory, `stack_push` the parent's stack). -/
def FinishChildMemSpec : Prop :=
  FunSpec FinishReadyA
    (fun s r post => ((∃ v, r = some (.returned v)) ∨ IsEvmErr r) →
      evmChain post = (evmChain s).tail ∧
      (∀ ec ∈ evmChain post, memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
        memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧ memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
        memW post (ec.2 + 56) = memW s (ec.2 + 56)) ∧
      globN post "ev" = memW s (globN s "cur_cont") ∧
      globN post "frame_mem_ptr" = memW s (globN s "cur_cont" + 56))
    (ofString "finish_child")

theorem funSpec_same_body {fname : MlS} {ps ps' : List (MlS × ShapeHOL)} {b b' : ProgHOL 64} {rt rt' : ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some (ps, b, rt))
    (hl' : originalRuntimeCode.lookup fname = some (ps', b', rt')) :
    ps' = ps ∧ b' = b ∧ rt' = rt := by
  rw [hl] at hl'
  simp only [Option.some.injEq, Prod.mk.injEq] at hl'
  exact ⟨hl'.1.symm, hl'.2.1.symm, hl'.2.2.symm⟩

/-- `FinishChildSpecA` from the unaligned contract and the footprint, via `headMemChainWF_pop`. -/
theorem finish_child_spec_aligned (hu : FinishChildSpecU) (hm : FinishChildMemSpec) :
    FinishChildSpecA := by
  obtain ⟨ps, b, rt, hl, hrun⟩ := hu
  obtain ⟨ps', b', rt', hl', hrun'⟩ := hm
  obtain ⟨rfl, rfl, rfl⟩ := funSpec_same_body hl hl'
  refine ⟨_, _, _, hl, fun s hc hP hex hnt hr => ?_⟩
  have h1 := hrun s hc ⟨hP.1.1, hP.2.1, hP.2.2⟩ hex hnt hr
  obtain ⟨hch, hmem, hev, hfmp⟩ := hrun' s hc hP hex hnt hr
  exact ⟨⟨h1.1, headMemChainWF_pop hP.1.2 hP.2.2 hch hmem hev hfmp⟩, h1.2.1, h1.2.2⟩

/-! ## 3e. Entry establishment -/

/-- An `EvmStep` that keeps `ev` and `frame_mem_ptr` (not in its write set `gw`) and the cells
read by the invariant preserves it (`depth0_prepare`, `frame_start`). -/
theorem headMemChainWF_of_evmStep {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {gw : List String} (hs : HeadMemChainWF s) (hstep : EvmStep gw s post)
    (hev_gw : ofString "ev" ∉ gw.map ofString)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hcells : ∀ ec ∈ evmChain s, memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧ memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56)) :
    HeadMemChainWF post := by
  obtain ⟨_, _, hkept, hchain⟩ := hstep
  have hev : globN post "ev" = globN s "ev" := by
    unfold globN; rw [hkept _ hev_gw]
  have hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [hkept _ hfmp_gw]
  exact headMemChainWF_of_agree hs hchain hcells hev hfmp

/-- The invariant's cells are kept by `fname` on every resuming outcome from a `P` entry. -/
def ChainCellsKept (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun s r post => Resumes r → ∀ ec ∈ evmChain s,
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧ memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧ memW post (ec.2 + 56) = memW s (ec.2 + 56))
    fname

/-- Aligned `EvmKeeps`: an `EvmKeeps` callee whose write set omits `ev`/`frame_mem_ptr` and that
keeps the chain cells carries `HeadMemChainWF`. -/
theorem evmKeeps_aligned {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {gw : List String} {fname : MlS} (hk : EvmKeeps P gw fname) (hc : ChainCellsKept P fname)
    (hev_gw : ofString "ev" ∉ gw.map ofString)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString) :
    FunSpec (fun s => P s ∧ HeadMemChainWF s)
      (fun s r post => Resumes r → EvmStep gw s post ∧ HeadMemChainWF post) fname := by
  obtain ⟨ps, b, rt, hl, hrun⟩ := hk
  obtain ⟨ps', b', rt', hl', hrun'⟩ := hc
  obtain ⟨rfl, rfl, rfl⟩ := funSpec_same_body hl hl'
  refine ⟨_, _, _, hl, fun s hcode hP hex hnt hr => ?_⟩
  have hst := hrun s hcode hP.1 hex hnt hr
  exact ⟨hst, headMemChainWF_of_evmStep hP.2 hst hev_gw hfmp_gw (hrun' s hcode hP.1 hex hnt hr)⟩

/-- Frame-memory effect of `frame_open(msg, 0)` (`frame_new`, `Guest/SoftwareAst.lean:15370`):
the new head `e` has `e+32 = 0` (`memzero`), `e+40 = 1024` and `e+24 = frame_mem_alloc(1024)`,
which leaves `frame_mem_ptr = e+24 + 1024`; the new continuation has kind `cur_cont+16 = 0`. -/
def FrameOpenMemSpec : Prop :=
  FunSpec FrameOpenReady
    (fun _ r post => Resumes r →
      memW post (globN post "cur_cont" + 16) = 0 ∧
      memW post (globN post "ev" + 32) = 0 ∧ memW post (globN post "ev" + 40) = 1024 ∧
      memW post (globN post "ev" + 24) + 1024 = globN post "frame_mem_ptr")
    (ofString "frame_open")

/-- Entry establishment at `frame_open`: on every resuming outcome the depth-0 invariant holds. -/
theorem frame_open_headMemChainWF (hm : FrameOpenMemSpec) :
    KeepsOn FrameOpenReady HeadMemChainWF (ofString "frame_open") := by
  obtain ⟨ps, b, rt, hl, hrun⟩ := hm
  refine ⟨_, _, _, hl, fun s hcode hP hex hnt hr => ?_⟩
  obtain ⟨hk, h32, h40, hend⟩ := hrun s hcode hP hex hnt hr
  refine headMemChainWF_depth0 _ hk (by rw [h32]) (by rw [h40]) ?_
  rw [h40]; exact hend

/-- `frame_open` aligned: `fk_frame_open` plus the frame-memory effect. -/
theorem frame_open_aligned (hk : KeepsOn FrameOpenReady EvmMsgReady (ofString "frame_open"))
    (hm : FrameOpenMemSpec) :
    KeepsOn FrameOpenReady (fun s => EvmMsgReady s ∧ HeadMemChainWF s) (ofString "frame_open") := by
  obtain ⟨ps, b, rt, hl, hrun⟩ := hk
  obtain ⟨ps', b', rt', hl', hrun'⟩ := frame_open_headMemChainWF hm
  obtain ⟨rfl, rfl, rfl⟩ := funSpec_same_body hl hl'
  exact ⟨_, _, _, hl, fun s hcode hP hex hnt hres =>
    ⟨hrun s hcode hP hex hnt hres, hrun' s hcode hP hex hnt hres⟩⟩

/-- Option A entry precondition: `FrameOpenReady` plus an explicit bound on the message's code
length `msg+120` (EIP-170 / witness code lengths are `< 2^32`), which bounds the
`compute_jumpdests` bitmap that `frame_new` carves from scratch. -/
def FrameOpenReadyB : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => FrameOpenReady s ∧ memW s (locN s "msg" + 120) < 2 ^ 40

/-- Bounded frame-memory effect of `frame_open(msg, 0)` (Option A). -/
def FrameOpenMemSpecB : Prop :=
  FunSpec FrameOpenReadyB
    (fun _ r post => Resumes r →
      memW post (globN post "cur_cont" + 16) = 0 ∧
      memW post (globN post "ev" + 32) = 0 ∧ memW post (globN post "ev" + 40) = 1024 ∧
      memW post (globN post "ev" + 24) + 1024 = globN post "frame_mem_ptr")
    (ofString "frame_open")

/-- The unbounded spec implies the bounded one. -/
theorem frameOpenMemSpecB_of (hm : FrameOpenMemSpec) : FrameOpenMemSpecB := by
  obtain ⟨ps, b, rt, hl, hrun⟩ := hm
  exact ⟨_, _, _, hl, fun s hcode hP hex hnt => hrun s hcode hP.1 hex hnt⟩

/-- Entry establishment at `frame_open` from the bounded spec. -/
theorem frame_open_headMemChainWF_B (hm : FrameOpenMemSpecB) :
    KeepsOn FrameOpenReadyB HeadMemChainWF (ofString "frame_open") := by
  obtain ⟨ps, b, rt, hl, hrun⟩ := hm
  refine ⟨_, _, _, hl, fun s hcode hP hex hnt hr => ?_⟩
  obtain ⟨hk, h32, h40, hend⟩ := hrun s hcode hP hex hnt hr
  refine headMemChainWF_depth0 _ hk (by rw [h32]) (by rw [h40]) ?_
  rw [h40]; exact hend

/-- `frame_open` aligned under the Option A bound: `fk_frame_open` plus the bounded effect. -/
theorem frame_open_aligned_B (hk : KeepsOn FrameOpenReady EvmMsgReady (ofString "frame_open"))
    (hm : FrameOpenMemSpecB) :
    KeepsOn FrameOpenReadyB (fun s => EvmMsgReady s ∧ HeadMemChainWF s) (ofString "frame_open") := by
  obtain ⟨ps, b, rt, hl, hrun⟩ := hk
  obtain ⟨ps', b', rt', hl', hrun'⟩ := frame_open_headMemChainWF_B hm
  obtain ⟨rfl, rfl, rfl⟩ := funSpec_same_body hl hl'
  exact ⟨_, _, _, hl, fun s hcode hP hex hnt hres =>
    ⟨hrun s hcode hP.1 hex hnt hres, hrun' s hcode hP hex hnt hres⟩⟩

/-! ## 3f. Head-safe stores and the `process_message` entry composition -/

/-- An address the invariant never reads: a head-record word other than `+24/+32/+40`, or a
head-continuation word other than `+56`. -/
def HeadSafeAddr (e0 c0 a : Nat) : Prop :=
  (∃ k, a = e0 + k ∧ k < 280 ∧ k ≠ 24 ∧ k ≠ 32 ∧ k ≠ 40) ∨ (∃ k, a = c0 + k ∧ k < 104 ∧ k ≠ 56)

/-- Generalised `headMemChainWF_of_headAllowed`: writes confined to `HeadSafeAddr` addresses
(e.g. `process_message`'s `cur_cont+24 := snapshot`, `ev+200 := 0`) keep the invariant. -/
theorem headMemChainWF_of_headSafe {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hE : EvmInv s) (hs : HeadMemChainWF s)
    (hglob : post.globals = s.globals)
    (hchain : evmChain post = evmChain s)
    (hmem_out : ∀ x : BitVec 64, ¬ HeadSafeAddr (globN s "ev") (globN s "cur_cont") x.toNat →
      post.memory x = s.memory x) :
    HeadMemChainWF post := by
  have hev : globN post "ev" = globN s "ev" := by simp [globN, hglob]
  have hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by simp [globN, hglob]
  obtain ⟨_, S, _, hrest⟩ := hE
  dsimp only at hrest
  obtain ⟨_, _, _, hFWF, _, _, hPair, _⟩ := hrest
  obtain ⟨tl, hcs⟩ : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl :=
    ⟨_, evmChain_cons s⟩
  have hSE : scratchEnd = 2965299200 := rfl
  have hhead := hFWF _ (head_mem_evmChain s)
  have he_in := (hhead.1 (globN s "ev", 280) (by simp)).1.2
  have hc_in := (hhead.1 (globN s "cur_cont", 104) (by simp)).1.2
  dsimp only at he_in hc_in
  rw [hcs, List.map_cons, List.flatten_cons, List.pairwise_append] at hPair
  obtain ⟨hP0, _, hcross⟩ := hPair
  have hdec : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
    unfold frameObjects at hP0
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hP0).1).1 _ (by simp)
  have hsafe : ∀ a : Nat, a < 2 ^ 64 →
      ¬ HeadSafeAddr (globN s "ev") (globN s "cur_cont") a → memW post a = memW s a := by
    intro a hlt hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact hne
  refine headMemChainWF_of_agree hs hchain ?_ hev hfmp
  intro ec hec
  rw [hcs] at hec
  rcases List.mem_cons.mp hec with rfl | htl
  · unfold Disj at hdec; dsimp only at hdec
    rw [hSE] at he_in hc_in
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply hsafe <;> (try dsimp only) <;> (try omega) <;>
      (rintro (⟨k, hk, _⟩ | ⟨k, hk, _⟩) <;> omega)
  · have hFec := hFWF ec (by rw [hcs]; exact List.mem_cons_of_mem _ htl)
    have hr_in := (hFec.1 (ec.1, 280) (by simp)).1.2
    have hk_in := (hFec.1 (ec.2, 104) (by simp)).1.2
    dsimp only at hr_in hk_in
    have hmemb : ∀ o ∈ [(ec.1, 280), (ec.2, 104)],
        o ∈ ((tl.map (frameObjects s)).flatten) := by
      intro o ho
      exact List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map_of_mem htl,
        by unfold frameObjects; simp only [List.mem_cons, List.mem_append] at ho ⊢; tauto⟩
    have hA : (globN s "ev", 280) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
      unfold frameObjects; simp
    have hB : (globN s "cur_cont", 104) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
      unfold frameObjects; simp
    have d1 := hcross _ hA _ (hmemb (ec.1, 280) (by simp))
    have d2 := hcross _ hB _ (hmemb (ec.1, 280) (by simp))
    have d3 := hcross _ hA _ (hmemb (ec.2, 104) (by simp))
    have d4 := hcross _ hB _ (hmemb (ec.2, 104) (by simp))
    unfold Disj at d1 d2 d3 d4; dsimp only at d1 d2 d3 d4
    rw [hSE] at he_in hc_in hr_in hk_in
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply hsafe <;> (try omega) <;>
      (rintro (⟨k, hk, _⟩ | ⟨k, hk, _⟩) <;> omega)

/-- A single word store at a head-safe address (`process_message`'s `cur_cont+24 := snapshot`). -/
theorem headMemChainWF_store_headSafe {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hE : EvmInv s) (hs : HeadMemChainWF s) {x : BitVec 64}
    (hx : HeadSafeAddr (globN s "ev") (globN s "cur_cont") x.toNat)
    (hglob : post.globals = s.globals)
    (hchain : evmChain post = evmChain s)
    (hmem : ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a) :
    HeadMemChainWF post :=
  headMemChainWF_of_headSafe hE hs hglob hchain fun a ha =>
    hmem a (fun h => ha (h ▸ hx))

theorem headSafe_cur_cont_24 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    HeadSafeAddr (globN s "ev") (globN s "cur_cont") (globN s "cur_cont" + 24) :=
  Or.inr ⟨24, rfl, by omega, by omega⟩

theorem headSafe_ev_200 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    HeadSafeAddr (globN s "ev") (globN s "cur_cont") (globN s "ev" + 200) :=
  Or.inl ⟨200, rfl, by omega, by omega, by omega, by omega⟩

/-- State-level entry composition along `process_message` (`Guest/SoftwareAst.lean:18803`):
`frame_open` gives the depth-0 facts at `s1`; `depth0_prepare` (`s1 → s2`) and `frame_start`
(`s3 → s4`) are `EvmStep`s keeping `ev`/`frame_mem_ptr` and the chain cells; the store
`cur_cont+24 := snapshot` (`s2 → s3`) is head-safe. Then `run_frames` is entered with
`HeadMemChainWF s4`. -/
theorem process_message_entry_headMemChainWF {F : Type}
    {s1 s2 s3 s4 : PanSemStateFiniteExact 64 F} {gw1 gw2 : List String}
    (hk : memW s1 (globN s1 "cur_cont" + 16) = 0)
    (h32 : memW s1 (globN s1 "ev" + 32) = 0) (h40 : memW s1 (globN s1 "ev" + 40) = 1024)
    (hend : memW s1 (globN s1 "ev" + 24) + 1024 = globN s1 "frame_mem_ptr")
    (hst1 : EvmStep gw1 s1 s2)
    (hev1 : ofString "ev" ∉ gw1.map ofString) (hfm1 : ofString "frame_mem_ptr" ∉ gw1.map ofString)
    (hc1 : ∀ ec ∈ evmChain s1, memW s2 (ec.1 + 24) = memW s1 (ec.1 + 24) ∧
      memW s2 (ec.1 + 32) = memW s1 (ec.1 + 32) ∧ memW s2 (ec.1 + 40) = memW s1 (ec.1 + 40) ∧
      memW s2 (ec.2 + 56) = memW s1 (ec.2 + 56))
    {x : BitVec 64} (hx : x.toNat = globN s2 "cur_cont" + 24)
    (hg2 : s3.globals = s2.globals) (hch2 : evmChain s3 = evmChain s2)
    (hm2 : ∀ a : BitVec 64, a ≠ x → s3.memory a = s2.memory a)
    (hst3 : EvmStep gw2 s3 s4)
    (hev3 : ofString "ev" ∉ gw2.map ofString) (hfm3 : ofString "frame_mem_ptr" ∉ gw2.map ofString)
    (hc3 : ∀ ec ∈ evmChain s3, memW s4 (ec.1 + 24) = memW s3 (ec.1 + 24) ∧
      memW s4 (ec.1 + 32) = memW s3 (ec.1 + 32) ∧ memW s4 (ec.1 + 40) = memW s3 (ec.1 + 40) ∧
      memW s4 (ec.2 + 56) = memW s3 (ec.2 + 56)) :
    EvmInv s4 ∧ HeadMemChainWF s4 := by
  have hw1 : HeadMemChainWF s1 :=
    headMemChainWF_depth0 _ hk (by rw [h32]) (by rw [h40]) (by rw [h40]; exact hend)
  have hw2 := headMemChainWF_of_evmStep hw1 hst1 hev1 hfm1 hc1
  have hw3 : HeadMemChainWF s3 :=
    headMemChainWF_store_headSafe hst1.1 hw2 (by rw [hx]; exact headSafe_cur_cont_24 s2) hg2 hch2 hm2
  exact ⟨hst3.1, headMemChainWF_of_evmStep hw3 hst3 hev3 hfm3 hc3⟩

theorem ev_not_mem_depth0_gw :
    ofString "ev" ∉ (["heap_ptr", "journal_n", "scratch_ptr"] : List String).map ofString := by
  decide

theorem fmp_not_mem_depth0_gw :
    ofString "frame_mem_ptr" ∉ (["heap_ptr", "journal_n", "scratch_ptr"] : List String).map ofString := by
  decide

theorem ev_not_mem_frameStart_gw :
    ofString "ev" ∉ (["bn_expw", "bn_gamma", "heap_ptr", "journal_n", "scratch_ptr"] : List String).map ofString := by
  decide

theorem fmp_not_mem_frameStart_gw :
    ofString "frame_mem_ptr" ∉ (["bn_expw", "bn_gamma", "heap_ptr", "journal_n", "scratch_ptr"] : List String).map ofString := by
  decide

/-! ## 3g. `frame_mem_alloc`: the frame-memory step of `frame_new` and `extend_memory` -/

/-- Entry of `frame_mem_alloc(n)`: `n`, `frame_mem_ptr`, `scratch_ptr` are words. -/
def FrameMemAllocPre : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => (∃ n : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word n))) ∧
    (∃ p : BitVec 64, s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word p))) ∧
    (∃ sp : BitVec 64, s.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)))

/-- `frame_mem_alloc(n)` (`Guest/SoftwareAst.lean:~110`): on return, the result is the old
`frame_mem_ptr`, and the only change is `frame_mem_ptr := (p + n + 7) & ~7` (with the two
range checks passed). This is the frame-memory step of `frame_new` (`n = 1024`) and of
`extend_memory`. -/
theorem frame_mem_alloc_spec :
    FunSpec FrameMemAllocPre
      (OnReturn fun s post => ∃ n p sp : BitVec 64,
        s.locals.lookup (ofString "n") = some (.val (.word n)) ∧
        s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word p)) ∧
        s.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) ∧
        ¬ ((sp - p).toNat < n.toNat) ∧
        ¬ (sp.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat) ∧
        post = { s with
          globals := s.globals.update (ofString "frame_mem_ptr",
            .val (.word ((p + (n + 7)) &&& ((0 : BitVec 64) - 8))))
          locals := post.locals
          clock := post.clock })
      (ofString "frame_mem_alloc") := by
  refine ⟨_, _, _, R16Shards.OpHandlers.lookup_frame_mem_alloc, fun s hc hP _ _ v hv => ?_⟩
  obtain ⟨⟨n, hn⟩, ⟨p, hp⟩, ⟨sp, hsp⟩⟩ := hP
  obtain ⟨_, h1, h2, h3⟩ := R16Shards.OpHandlers.frame_mem_alloc_body_run s p sp n hc hp hsp hn v hv
  exact ⟨n, p, sp, hn, hp, hsp, h1, h2, h3⟩

/-- Arithmetic of a `frame_mem_alloc(n)` from an 8-aligned `p ≤ sp ≤ scratchEnd`: the new
pointer is `p + ⌈n⌉₈`; for `n = 1024` it is exactly `p + 1024`. -/
theorem frame_mem_alloc_1024 (p sp : BitVec 64)
    (hp_le_sp : p.toNat ≤ sp.toNat) (hsp_le : sp.toNat ≤ scratchEnd) (hp_al : p.toNat % 8 = 0)
    (hcmp1 : ¬ ((sp - p).toNat < (1024 : BitVec 64).toNat))
    (hcmp2 : ¬ (sp.toNat < ((p + ((1024 : BitVec 64) + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    ((p + ((1024 : BitVec 64) + 7)) &&& ((0 : BitVec 64) - 8)).toNat = p.toNat + 1024 := by
  have h := (R16Shards.OpHandlers.frame_mem_alloc_arith p sp 1024 hp_le_sp hsp_le hp_al hcmp1 hcmp2).1
  rw [h]; rfl

/-! ## 3h. `frame_mem_ptr` is untouched by every helper outside `badFrameMem` -/

section FmpKeep
open InitECandidate.Solver.GuestCodeLookup

/-- Whole-program check (with `GuestGlobalKeep.keepsG`): every function outside
`GuestFrameMemKeep.badFrameMem` never assigns the global `frame_mem_ptr` and only calls such
functions. -/
theorem program_check_fmp_global :
    (functionsHOL sourceDeclarations).all
      (fun entry => !(InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem entry.1) ||
        InitECandidate.Solver.GuestGlobalKeep.keepsG (ofString "frame_mem_ptr")
          InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem entry.2.2.1) = true := by
  unfold sourceDeclarations
  rw [InitECandidate.Solver.FrontendCodecComputation.declToHOL_function_eq]
  kernel_rfl

theorem good_fmp_hgood : ∀ function,
    InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem function = true →
    ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      InitECandidate.Solver.GuestGlobalKeep.keepsG (ofString "frame_mem_ptr")
        InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem body = true := by
  intro f hf values body callee rs h
  obtain ⟨params, rs', hc⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed h
  have hm := InitECandidate.Solver.GuestGlobalKeep.originalRuntimeCode_mem hc
  have := List.all_eq_true.1 program_check_fmp_global _ hm
  simpa [hf] using this

/-- Calling any function outside `badFrameMem` (e.g. `compute_jumpdests`, `lst_new_scratch`,
`htab_new_scratch`, `htab_count`, `state_snapshot`) leaves the global `frame_mem_ptr`
unchanged, whatever the outcome. -/
theorem good_body_keeps_fmp {F : Type} {function : MlS}
    (hf : InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem function = true)
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
      some (body, callee, rs))
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state body).2.globals.lookup (ofString "frame_mem_ptr") =
      state.globals.lookup (ofString "frame_mem_ptr") :=
  InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG _ _ good_fmp_hgood body
    (good_fmp_hgood function hf values body callee rs h) state code

theorem goodFrameMem_frame_new_helpers :
    InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem (ofString "compute_jumpdests") = true ∧
    InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem (ofString "lst_new_scratch") = true ∧
    InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem (ofString "htab_new_scratch") = true ∧
    InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem (ofString "htab_count") = true ∧
    InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem (ofString "state_snapshot") = true ∧
    InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem (ofString "depth0_prepare") = true ∧
    InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem (ofString "frame_start") = true := by
  decide

end FmpKeep

/-! ## 3h'. `memzero`: zero-fill of `[dst, dst+n)` plus its write frame, at an explicit call -/

section MemzeroZero
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup

/-- `memzero(d, n)` called from `s0` (an `ArenaReady` state) on a normal return: every aligned
word of `[d, d+n)` reads `0`, and the call only wrote memory inside `[d, d+n)` (globals, code and
domain unchanged). Composes `Wave8Contracts.M29.zv_memzero` (zeroing) with
`Wave8Contracts.M28.memzero_body_frame` (write frame). -/
theorem memzero_call_zero {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hcode : s0.code = originalRuntimeCode) (hAR : ArenaReady s0) (d n : BitVec 64)
    (rv : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s0
        ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word d))).update
          (ofString "n", .val (.word n)))) (sourceFnBody Guest.Software.guestFn_memzero) =
        (some (.returned rv), post)) :
    (∀ a, d.toNat ≤ a → a + 8 ≤ d.toNat + n.toNat → a % 8 = 0 → memW post a = 0) ∧
    Wave8Contracts.M28.MemzeroWriteFrame (callEntryStateHOLFinite s0
        ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word d))).update
          (ofString "n", .val (.word n)))) post (d.toNat, n.toNat) := by
  have hml := pan_two_word_lookup s0.code.lookup (ofString "memzero")
    (ofString "dst") (ofString "n") (sourceFnBody Guest.Software.guestFn_memzero)
    d n (by decide) (by rw [hcode]; exact lookup_memzero)
  set E := callEntryStateHOLFinite s0
    ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word d))).update
      (ofString "n", .val (.word n))) with hE
  have hEc : E.code = originalRuntimeCode := hcode
  have hEAR : ArenaReady E :=
    ⟨guestInv_callEntry _ _ hAR.1, hAR.2⟩
  have hdst : locN E "dst" = d.toNat := by
    simp [hE, locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide]
  have hnn : locN E "n" = n.toNat := by
    simp [hE, locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨ps, b, rt, hl, hspec⟩ := Wave8Contracts.M29.zv_memzero
  rw [lookup_memzero] at hl
  obtain ⟨rfl, rfl, rfl⟩ : ps = _ ∧ b = _ ∧ rt = _ := by
    simp only [Option.some.injEq, Prod.mk.injEq] at hl; exact ⟨hl.1.symm, hl.2.1.symm, hl.2.2.symm⟩
  have hz := hspec E hEc hEAR ⟨[.val (.word d), .val (.word n)], by
      rw [hcode] at hml; exact hml⟩ (by rw [hrun]; simp)
  rw [hrun, hdst, hnn] at hz
  have hfr := Wave8Contracts.M28.memzero_body_frame E hEc hEAR.1
    (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
  rw [hrun, hdst, hnn] at hfr
  exact ⟨hz rv rfl, hfr⟩

end MemzeroZero

/-! ## 3i. `lst_new_scratch`: exact run (frame-memory footprint for `frame_new`) -/

section LstNew
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

theorem lookup_lst_new_scratch :
    originalRuntimeCode.lookup (ofString "lst_new_scratch") =
      some ([(ofString "esz", .one), (ofString "cap", .one)],
        sourceFnBody Guest.Software.guestFn_lst_new_scratch, .one) :=
  lookup_of_guestAst_getElem 409 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_new_scratch) rfl

@[local simp] private theorem lnm1 : (ofString "l" = ofString "esz") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem lnm2 : (ofString "l" = ofString "cap") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem lnm3 : (ofString "p" = ofString "l") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem lnm4 : (ofString "p" = ofString "cap") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem lnm5 : (ofString "p" = ofString "esz") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem lnm6 : (ofString "scratch_ptr" = ofString "frame_mem_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide

local macro "evs" : tactic => `(tactic| ((simp [ev, evalHOLExact, evalListHOLExact,
  HolFiniteMapExact.lookup_update, FUPDATE, wordOpHOL, wordOp, valueIsWord, valueWord,
  panOpHOL, lnm1, lnm2, lnm3, lnm4, lnm5, lnm6]) <;> first | assumption | rfl))

attribute [local irreducible] Ret in
/-- `lst_new_scratch(esz, cap)`: two scratch allocations (`24` bytes for the header `l`, then
`esz*cap` bytes for the payload `p`) and three stores into the fresh header. Memory changes only
at `l`, `l+8`, `l+16`; the only global that changes is `scratch_ptr`, which ends at `p`. -/
theorem lst_new_scratch_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (esz cap p0 f : BitVec 64)
    (he : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hc : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hp : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word p0)))
    (hf : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f))) :
    Ret s (sourceFnBody Guest.Software.guestFn_lst_new_scratch) (fun v post =>
      ∃ l q : BitVec 64, v = .val (.word l) ∧
        l = (p0 - 24) &&& ((0 : BitVec 64) - 8) ∧
        q = (l - esz * cap) &&& ((0 : BitVec 64) - 8) ∧
        f.toNat ≤ q.toNat ∧ f.toNat ≤ l.toNat ∧
        ¬ ((p0 - f).toNat < (24 : BitVec 64).toNat) ∧
        ¬ ((l - f).toNat < (esz * cap).toNat) ∧
        post.globals = (s.globals.update (ofString "scratch_ptr", .val (.word l))).update
          (ofString "scratch_ptr", .val (.word q)) ∧
        post.memory = updW (updW (updW s.memory (l + 0) q) (l + 8) 0) (l + 16) cap ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_lst_new_scratch =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_lst_new_scratch).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_lst_new_scratch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Ret.of_NS
  apply HtabC00Ports.ns_scratch_alloc hcode 24 (by evs) p0 f hp hf
  intro hc1 hd1
  generalize hL : (p0 - 24) &&& ((0 : BitVec 64) - 8) = l at *
  apply HtabC00Ports.ns_scratch_alloc hcode (esz * cap)
    (by simp [ev, evalHOLExact, evalListHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
      panOpHOL, valueIsWord, valueWord, he, hc, lnm1, lnm2]) l f (by evs) (by evs)
  intro hc2 hd2
  generalize hQ : (l - esz * cap) &&& ((0 : BitVec 64) - 8) = q at *
  apply Ret.ns_storeW (l + 0) q (by evs) (by evs); intro _
  apply Ret.ns_storeW (l + 8) 0 (by evs) (by evs); intro _
  apply Ret.ns_storeW (l + 16) cap (by evs) (by evs); intro _
  apply Ret.ns_ret
  intro val hval
  simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE] at hval
  subst hval
  refine ⟨l, q, rfl, rfl, hQ.symm, by omega, by omega, hc1, hc2, ?_, ?_, rfl, rfl⟩ <;> rfl

end LstNew

/-! ## 3j. `htab_count`: read-only run -/

section HtabCount
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

theorem lookup_htab_count :
    originalRuntimeCode.lookup (ofString "htab_count") =
      some ([(ofString "t", .one)], sourceFnBody Guest.Software.guestFn_htab_count, .one) :=
  lookup_of_guestAst_getElem 141 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_count) rfl

attribute [local irreducible] Ret in
/-- `htab_count(t)` is the single load `return ld(t+24)`: on return, memory, globals, code and
the domain are unchanged (only locals are emptied). -/
theorem htab_count_run {F : Type} (s : PanSemStateFiniteExact 64 F) :
    Ret s (sourceFnBody Guest.Software.guestFn_htab_count) (fun _ post =>
      post.globals = s.globals ∧ post.memory = s.memory ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_htab_count =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_htab_count).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_htab_count,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Ret.of_NS
  apply Ret.ns_ret
  intro _ _
  exact ⟨rfl, rfl, rfl, rfl⟩

end HtabCount

/-! ## 3k. `finish_child` leaves: `frame_mem_release`, `scratch_release`, `pc_add` -/

section FinishLeaves
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

theorem lookup_frame_mem_release :
    originalRuntimeCode.lookup (ofString "frame_mem_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_frame_mem_release, .one) :=
  lookup_of_guestAst_getElem 12 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_mem_release) rfl

theorem lookup_scratch_release :
    originalRuntimeCode.lookup (ofString "scratch_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_scratch_release, .one) :=
  lookup_of_guestAst_getElem 15 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_release) rfl

theorem lookup_pc_add :
    originalRuntimeCode.lookup (ofString "pc_add") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_pc_add, .one) :=
  lookup_of_guestAst_getElem 468 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pc_add) rfl

/-- A global assignment followed by `b`: on success the state is `setKvarHOLFinite .global`. -/
theorem Ret.seq_assignGlobal {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hb : ∀ val, ev s e = some val → isValidValueHOLFinite s .global x val = true →
      Ret (setKvarHOLFinite .global x val s) b Φ) :
    Ret s (.seq (.assign .global x e) b) Φ := by
  refine Ret.seq ?_ ?_
  · intro v hv
    rw [evaluateHOLFiniteState_assign] at hv
    split at hv
    · simp at hv
    · split at hv <;> simp at hv
  · intro t ht
    rw [evaluateHOLFiniteState_assign] at ht
    split at ht
    · simp at ht
    · rename_i val hval
      split at ht
      · rename_i hvld
        injection ht with _ hteq; rw [← hteq]; exact hb val hval hvld
      · simp at ht

attribute [local irreducible] Ret in
/-- `frame_mem_release(m)` is `frame_mem_ptr := m; return 0`: on return the globals are those of
the entry state with `frame_mem_ptr` set to the argument; memory, code and domain unchanged. -/
theorem frame_mem_release_run {F : Type} (s : PanSemStateFiniteExact 64 F) (m : ValueHOL 64)
    (hm : s.locals.lookup (ofString "m") = some m) :
    Ret s (sourceFnBody Guest.Software.guestFn_frame_mem_release) (fun _ post =>
      post.globals = s.globals.update (ofString "frame_mem_ptr", m) ∧
        post.memory = s.memory ∧ post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_frame_mem_release =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_frame_mem_release).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_frame_mem_release,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.seq_assignGlobal fun val hval _ => ?_
  have hv : val = m := by
    simp [ev, evalHOLExact, hm] at hval; exact hval.symm
  subst hv
  refine Ret.ret fun _ _ => ?_
  exact ⟨rfl, rfl, rfl, rfl⟩

attribute [local irreducible] Ret in
/-- `scratch_release(m)` is `scratch_ptr := m; return 0`. -/
theorem scratch_release_run {F : Type} (s : PanSemStateFiniteExact 64 F) (m : ValueHOL 64)
    (hm : s.locals.lookup (ofString "m") = some m) :
    Ret s (sourceFnBody Guest.Software.guestFn_scratch_release) (fun _ post =>
      post.globals = s.globals.update (ofString "scratch_ptr", m) ∧
        post.memory = s.memory ∧ post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_scratch_release =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_scratch_release).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_scratch_release,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.seq_assignGlobal fun val hval _ => ?_
  have hv : val = m := by
    simp [ev, evalHOLExact, hm] at hval; exact hval.symm
  subst hv
  refine Ret.ret fun _ _ => ?_
  exact ⟨rfl, rfl, rfl, rfl⟩

@[local simp] private theorem pcm1 : (ofString "n" = ofString "ev") = False := by
  simp only [eq_iff_iff, iff_false]; decide

attribute [local irreducible] Ret in
/-- `pc_add(n)` is `st ev+0, ld(ev+0) + n; return 0`: one word store at `ev`. -/
theorem pc_add_run {F : Type} (s : PanSemStateFiniteExact 64 F) (e pc n : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hpc : s.memory e = .word pc) (hdom : s.memaddrs e) :
    Ret s (sourceFnBody Guest.Software.guestFn_pc_add) (fun _ post =>
      post.globals = s.globals ∧ post.memory = updW s.memory e (pc + n) ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_pc_add =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_pc_add).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_pc_add,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Ret.of_NS
  apply Ret.ns_storeW e (pc + n)
    (by simp [ev, evalHOLExact, evalListHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord, he])
    (by
      simp [ev, evalHOLExact, evalListHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord, he, hn]
      have hl : ∀ inst : DecidablePred (NS s s.locals s.globals s.memory s.clock).toExact.memaddrs,
          @memLoadHOLExact 64 _ ShapeHOL.one e (NS s s.locals s.globals s.memory s.clock).toExact.memaddrs inst
          s.memory (NS s s.locals s.globals s.memory s.clock).structs =
            some (ValueHOL.val (HolWordLab.word pc)) := by
        intro inst
        simp only [memLoadHOLExact]
        rw [if_pos (show (NS s s.locals s.globals s.memory s.clock).memaddrs e from hdom), hpc]
      erw [hl]
      simp [valueWord])
  intro _
  apply Ret.ns_ret
  intro _ _
  exact ⟨rfl, rfl, rfl, rfl⟩

end FinishLeaves

/-! ## 3l. Call combinators and the `finish_child` release tail -/

section FinishTail
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

theorem call00_noRet {F : Type} (s : PanSemStateFiniteExact 64 F)
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

/-- A plain call `f(args)` followed by `cont`: on resumption the state is the callee's returned
state with the caller's locals restored. -/
theorem Ret.seq_call00 {F : Type} {s : PanSemStateFiniteExact 64 F} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hk : ∀ values body callee ret v cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
        some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned v), cpost) →
      Ret { cpost with locals := s.locals } cont Φ) :
    Ret s (.seq (.call (some (none, none)) fname args) cont) Φ := by
  refine Ret.seq (fun v hv => False.elim (call00_noRet s fname args v hv)) ?_
  intro t ht
  obtain ⟨values, body, callee, ret, v, cpost, h1, h2, h3, h4⟩ :=
    Wave8M19.Htab.call0_flow s fname args (Or.inl (by rw [ht]))
  rw [ht] at h4
  injection h4 with _ h5
  rw [h5]
  exact hk values body callee ret v cpost h1 h2 h3

@[local simp] private theorem ftm1 : (ofString "scratch_ptr" = ofString "ev") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem ftm2 : (ofString "frame_mem_ptr" = ofString "ev") = False := by
  simp only [eq_iff_iff, iff_false]; decide

/-- Run a one-word-argument call whose body `Ret`-spec is given. -/
theorem Ret.seq_call1W {F : Type} {s : PanSemStateFiniteExact 64 F} {fname p : MlS}
    {e : ExpHOL 64} {fbody cont : ProgHOL 64} {w : BitVec 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p, .one)], fbody, .one))
    (he : ev s e = some (.val (.word w)))
    (Ψ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (hbody : Ret (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (p, .val (.word w))))
      fbody Ψ)
    (hk : ∀ v cpost, Ψ v cpost → Ret { cpost with locals := s.locals } cont Φ) :
    Ret s (.seq (.call (some (none, none)) fname [e]) cont) Φ := by
  refine Ret.seq_call00 fun values body callee ret v cpost h1 h2 h3 => ?_
  have hv : values = [.val (.word w)] := by
    simp only [evalListHOLFinite, evalListHOLExact] at h1
    unfold ev at he
    rw [he] at h1; simp at h1; exact h1.symm
  subst hv
  have hl := pan_one_word_lookup s.code.lookup fname p fbody w (by rw [hcode]; exact hlook)
  rw [hl] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  exact hk v cpost (by have := hbody v (by rw [h3]); rw [h3] at this; exact this)

@[local simp] private theorem ftm3 : (ofString "child_mark" = ofString "child_mem_mark") = False := by
  simp only [eq_iff_iff, iff_false]; decide

/-- The tail of `finish_child`: `scratch_release(child_mark); frame_mem_release(child_mem_mark);
pc_add(1); return 0`. On return `frame_mem_ptr = child_mem_mark`, `scratch_ptr = child_mark`,
`ev` is unchanged and memory changes only at `ev` (the pc word). -/
theorem finish_child_tail {F : Type} (t : PanSemStateFiniteExact 64 F)
    (hcode : t.code = originalRuntimeCode) (cm cmm e pc : BitVec 64)
    (hcm : t.locals.lookup (ofString "child_mark") = some (.val (.word cm)))
    (hcmm : t.locals.lookup (ofString "child_mem_mark") = some (.val (.word cmm)))
    (he : t.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hpc : t.memory e = .word pc) (hdom : t.memaddrs e) :
    Ret t (.seq (.call (some (none, none)) (ofString "scratch_release")
        [.var .local (ofString "child_mark")])
      (.seq (.call (some (none, none)) (ofString "frame_mem_release")
          [.var .local (ofString "child_mem_mark")])
        (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1])
          (.return (.const 0))))) (fun _ post =>
      post.globals = (t.globals.update (ofString "scratch_ptr", .val (.word cm))).update
        (ofString "frame_mem_ptr", .val (.word cmm)) ∧
      post.memory = updW t.memory e (pc + 1) ∧ post.code = t.code ∧
      post.memaddrs = t.memaddrs) := by
  refine Ret.seq_call1W (w := cm) hcode lookup_scratch_release
    (by simp [ev, evalHOLExact, hcm]) _ (scratch_release_run _ (.val (.word cm)) (by
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])) ?_
  rintro _ c1 ⟨hg1, hm1, hc1, hd1⟩
  simp only [callEntryStateHOLFinite] at hg1 hm1 hc1 hd1
  refine Ret.seq_call1W (w := cmm) (by simp [hc1, hcode]) lookup_frame_mem_release
    (by simp [ev, evalHOLExact, hcmm]) _ (frame_mem_release_run _ (.val (.word cmm)) (by
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])) ?_
  rintro _ c2 ⟨hg2, hm2, hc2, hd2⟩
  simp only [callEntryStateHOLFinite] at hg2 hm2 hc2 hd2
  refine Ret.seq_call1W (w := 1) (by simp [hc2, hc1, hcode]) lookup_pc_add
    (by simp [ev, evalHOLExact]) _ (pc_add_run _ e pc 1 (by
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [callEntryStateHOLFinite, hg2, hg1, HolFiniteMapExact.lookup_update, FUPDATE, he])
      (by simp [callEntryStateHOLFinite, hm2, hm1, hpc])
      (by simp [callEntryStateHOLFinite, hd2, hd1, hdom])) ?_
  rintro _ c3 ⟨hg3, hm3, hc3, hd3⟩
  simp only [callEntryStateHOLFinite] at hg3 hm3 hc3 hd3
  refine Ret.ret fun _ _ => ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [emptyLocalsHOLFinite, hg3, hg2, hg1]
  · simp [emptyLocalsHOLFinite, hm3, hm2, hm1]
  · simp [emptyLocalsHOLFinite, hc3, hc2, hc1]
  · simp [emptyLocalsHOLFinite, hd3, hd2, hd1]

end FinishTail

section ComputeJumpdests
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

/-- Byte length of the `compute_jumpdests` bitmap for code length `n`. -/
def jdLen (n : BitVec 64) : BitVec 64 := ((n + 63) >>> (6 : Nat)) * 8 + 8

/-- Non-local frame: globals, code and domain unchanged; memory unchanged off the cells hitting
`ivl`. -/
def CJFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) (ivl : Ivl) : Prop :=
  t.globals = s.globals ∧ t.code = s.code ∧ t.memaddrs = s.memaddrs ∧
    ∀ a : BitVec 64, ¬ CellHits a.toNat ivl → t.memory a = s.memory a

theorem cjf_of {F : Type} {s t : PanSemStateFiniteExact 64 F} {ivl : Ivl}
    (hg : t.globals = s.globals) (hc : t.code = s.code) (hm : t.memaddrs = s.memaddrs)
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat ivl → t.memory a = s.memory a) :
    CJFrame s t ivl := ⟨hg, hc, hm, hmem⟩

theorem CJFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) (ivl : Ivl) :
    CJFrame s s ivl := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem CJFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F} {ivl : Ivl}
    (h1 : CJFrame s t ivl) (h2 : CJFrame t u ivl) : CJFrame s u ivl :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    fun a ha => (h2.2.2.2 a ha).trans (h1.2.2.2 a ha)⟩

theorem Ret.named {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ S, S = s → Ret S p Φ) : Ret s p Φ := h s rfl

theorem Flw.of_locOnly {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hp : locOnly p = true) (h : ∀ r t, LocFrame s t → Ψ r t) : Flw s p Ψ :=
  fun _ => h _ _ (locFrame_eval p hp s)

theorem ev_op_word {F : Type} (s : PanSemStateFiniteExact 64 F) (o : BinOp)
    (args : List (ExpHOL 64)) (v : ValueHOL 64) (h : ev s (.op o args) = some v) :
    ∃ w, v = .val (.word w) := by
  simp only [ev, evalHOLExact] at h
  split at h
  · split at h
    · obtain ⟨w, _, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨w, rfl⟩
    · cases h
  · cases h

/-- Invariant rule for `while cond body; b`: the loop never returns, and every normal exit is an
`I` state. -/
theorem Ret.seq_while_inv {F : Type} {s : PanSemStateFiniteExact 64 F} {cond : ExpHOL 64}
    {body b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (I : PanSemStateFiniteExact 64 F → Prop) (hI : I s) (hNR : NoRet body)
    (hstep : ∀ u, I u → InitECandidate.Solver.Wave8M19.LoopActive cond u → u.clock ≠ 0 →
      Flw (decClockHOLFinite u) body (fun _ t => I t))
    (hk : ∀ t, I t → Ret t b Φ) : Ret s (.seq (.while cond body) b) Φ := by
  refine Ret.seq (fun v hv => absurd hv
    (while_noRet cond body (fun st v => hNR st v) s.clock s le_rfl v)) ?_
  intro t ht
  have h := while_inv_act I cond body (fun u hu ha hc hf => hstep u hu ha hc hf)
    s.clock s le_rfl hI (by rw [ht])
  rw [ht] at h
  exact hk t h

theorem jdLen_toNat (nw : BitVec 64) (hnb : nw.toNat < 2 ^ 40) :
    (jdLen nw).toNat = (nw.toNat + 63) / 64 * 8 + 8 := by
  unfold jdLen
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  have h63 : (63 : BitVec 64).toNat = 63 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, h8, h63]
  omega

theorem cj_hit (q a nw : BitVec 64) (ha : a.toNat < nw.toNat) (hnb : nw.toNat < 2 ^ 40)
    (hq : q.toNat + (jdLen nw).toNat < 2 ^ 64) :
    CellHits (q + (a >>> (6 : Nat)) * 8).toNat (q.toNat, (jdLen nw).toNat) := by
  have hL := jdLen_toNat nw hnb
  have hA : ((a >>> (6 : Nat)) * 8).toNat = a.toNat / 64 * 8 := by
    have h8 : (8 : BitVec 64).toNat = 8 := rfl
    simp only [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h8]
    omega
  have hx : (q + (a >>> (6 : Nat)) * 8).toNat = q.toNat + a.toNat / 64 * 8 := by
    rw [BitVec.toNat_add, hA]; apply Nat.mod_eq_of_lt; omega
  unfold CellHits
  rw [hx, hL]
  constructor <;> omega


@[local simp] private theorem cjn1 : (ofString "op" = ofString "bm") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem cjn2 : (ofString "op" = ofString "n") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem cjn3 : (ofString "op" = ofString "pc") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem cjn4 : (ofString "adv" = ofString "bm") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem cjn5 : (ofString "adv" = ofString "n") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem cjn6 : (ofString "adv" = ofString "pc") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem cjn7 : (ofString "pc" = ofString "bm") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem cjn8 : (ofString "pc" = ofString "n") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem cjn9 : (ofString "bm" = ofString "n") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem cjn10 : (ofString "n" = ofString "dst") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem cjn11 : (ofString "scratch_ptr" = ofString "frame_mem_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide


theorem cj_args {F : Type} (s : PanSemStateFiniteExact 64 F) (q nw : BitVec 64)
    (hb : s.locals.lookup (ofString "bm") = some (.val (.word q)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw))) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [ExpHOL.var VarKind.local (ofString "bm"),
              ExpHOL.op BinOp.add
                [ExpHOL.panop PanOp.mul
                    [ExpHOL.shift Shift.lsr
                        (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "n"), ExpHOL.const 63#64])
                        (ExpHOL.const 6#64),
                      ExpHOL.const 8#64],
                  ExpHOL.const 8#64]] = some [.val (.word q), .val (.word (jdLen nw))] := by
  rw [evalListHOLFinite_eq_toExact]
  simp [evalListHOLExact, evalHOLExact, hb, hn, wordOpHOL, wordOp, valueIsWord, valueWord,
    panOpHOL, jdLen, wordShiftHOL]

theorem cj_active {F : Type} (t : PanSemStateFiniteExact 64 F) (nw : BitVec 64)
    (hn : t.locals.lookup (ofString "n") = some (.val (.word nw)))
    (h : InitECandidate.Solver.Wave8M19.LoopActive
      (.cmp .lower (.var .local (ofString "pc")) (.var .local (ofString "n"))) t) :
    ∃ pc : BitVec 64, t.locals.lookup (ofString "pc") = some (.val (.word pc)) ∧
      pc.toNat < nw.toNat := by
  obtain ⟨c, hc, hnz⟩ := h
  change evalAt t _ = _ at hc
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp t .lower _ _ c hc
  simp [evalAt, evalHOLExact, hn] at ha hb
  subst hb
  refine ⟨a, ha, ?_⟩
  subst hcw
  by_contra hge
  apply hnz
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
  omega

theorem CJFrame.of_store {F : Type} {s : PanSemStateFiniteExact 64 F} {ivl : Ivl}
    (a w : BitVec 64) (ha : CellHits a.toNat ivl) :
    CJFrame s { s with memory := updW s.memory a w } ivl := by
  refine ⟨rfl, rfl, rfl, fun b hb => ?_⟩
  have : b ≠ a := by rintro rfl; exact hb ha
  exact updW_ne _ _ _ _ this

theorem CJFrame.of_loc {F : Type} {s t : PanSemStateFiniteExact 64 F} {ivl : Ivl}
    (h : LocFrame s t) : CJFrame s t ivl := by
  rw [h]; exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Loop invariant of `compute_jumpdests`. -/
def CJInv {F : Type} (S1 : PanSemStateFiniteExact 64 F) (ivl : Ivl) (q nw : BitVec 64)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  CJFrame S1 t ivl ∧ t.locals.lookup (ofString "bm") = some (.val (.word q)) ∧
    t.locals.lookup (ofString "n") = some (.val (.word nw))

theorem CJInv.resVar {F : Type} {S1 t : PanSemStateFiniteExact 64 F} {ivl : Ivl} {q nw : BitVec 64}
    (x : MlS) (o : Option (ValueHOL 64)) (h1 : ofString "bm" ≠ x) (h2 : ofString "n" ≠ x)
    (h : CJInv S1 ivl q nw t) :
    CJInv S1 ivl q nw { t with locals := HolFiniteMapExact.resVarEq t.locals (x, o) } :=
  ⟨h.1.trans ⟨rfl, rfl, rfl, fun _ _ => rfl⟩,
    by rw [resVarEq_lookup_ne _ _ _ _ h1]; exact h.2.1,
    by rw [resVarEq_lookup_ne _ _ _ _ h2]; exact h.2.2⟩

theorem CJInv.setVar {F : Type} {S1 t : PanSemStateFiniteExact 64 F} {ivl : Ivl} {q nw : BitVec 64}
    (x : MlS) (v : ValueHOL 64) (h1 : x ≠ ofString "bm") (h2 : x ≠ ofString "n")
    (h : CJInv S1 ivl q nw t) : CJInv S1 ivl q nw (setVarHOLFinite x v t) :=
  ⟨h.1.trans ⟨rfl, rfl, rfl, fun _ _ => rfl⟩,
    by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h.2.1],
    by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h2, h.2.2]⟩

theorem Flw.keepLoc {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop} (x y : MlS)
    (hp : locOnly p = true)
    (hx : InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.notAssignedLocal x p = true)
    (hy : InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.notAssignedLocal y p = true)
    (h : ∀ r t, LocFrame s t → t.locals.lookup x = s.locals.lookup x →
      t.locals.lookup y = s.locals.lookup y → Ψ r t) : Flw s p Ψ := by
  intro hf
  have hn : ∀ z, InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.notAssignedLocal z p = true →
      (evaluateHOLFiniteState s p).2.locals.lookup z = s.locals.lookup z := by
    intro z hz
    apply InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.evaluate_notAssignedLocal p hz s
    rcases hf with h | h | h <;> rw [h] <;> rfl
  exact h _ _ (locFrame_eval p hp s) (hn x hx) (hn y hy)

macro "cjnr" : tactic => `(tactic| repeat (first | apply NoRet.dec' | apply NoRet.seq | apply NoRet.ite | exact NoRet.store' | exact NoRet.assign | exact NoRet.skip))

attribute [local irreducible] Ret in
theorem compute_jumpdests_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s) (nw p f : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hp : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)))
    (hfp : f.toNat ≤ p.toNat) (hnb : nw.toNat < 2 ^ 40) :
    Ret s (sourceFnBody Guest.Software.guestFn_compute_jumpdests) (fun v post =>
      ∃ q : BitVec 64, v = .val (.word q) ∧
        q = (p - jdLen nw) &&& ((0 : BitVec 64) - 8) ∧
        ¬ ((p - f).toNat < (jdLen nw).toNat) ∧ ¬ (q.toNat < f.toNat) ∧
        q.toNat + (jdLen nw).toNat ≤ p.toNat ∧
        post.globals = s.globals.update (ofString "scratch_ptr", .val (.word q)) ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
        ∀ a : BitVec 64, ¬ CellHits a.toNat (q.toNat, (jdLen nw).toNat) →
          post.memory a = s.memory a) := by
  have hb : sourceFnBody Guest.Software.guestFn_compute_jumpdests =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_compute_jumpdests).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_compute_jumpdests,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine HtabC00Ports.decCall_scratch_alloc hcode (jdLen nw)
    (by simp [ev, evalHOLExact, evalListHOLExact, hn, wordOpHOL, wordOp, valueIsWord, valueWord,
      panOpHOL, jdLen, wordShiftHOL]) p f hp hf ?_
  intro hc1 hc2
  generalize hQ : (p - jdLen nw) &&& ((0 : BitVec 64) - 8) = q at *
  have hL := jdLen_toNat nw hnb
  have hqle : q.toNat + (jdLen nw).toNat ≤ p.toNat := by
    have h1 := and_neg8_toNat (p - jdLen nw)
    rw [hQ] at h1
    have h0 : (p - f).toNat = p.toNat - f.toNat := by
      rw [BitVec.toNat_sub]; have := p.isLt; have := f.isLt; omega
    have h2 : (p - jdLen nw).toNat = p.toNat - (jdLen nw).toNat := by
      rw [BitVec.toNat_sub]; have := p.isLt; have := (jdLen nw).isLt; omega
    have := Nat.div_mul_le_self (p - jdLen nw).toNat 8
    omega
  have hqlt : q.toNat + (jdLen nw).toNat < 2 ^ 64 := by have := p.isLt; omega
  generalize hS1 : setVarHOLFinite (ofString "bm") (.val (.word q))
    { s with globals := s.globals.update (ofString "scratch_ptr", .val (.word q)),
             clock := s.clock - 1 } = S1
  have hS1b : S1.locals.lookup (ofString "bm") = some (.val (.word q)) := by
    rw [← hS1]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hS1n : S1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    rw [← hS1]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn]
  have hS1c : S1.code = originalRuntimeCode := by rw [← hS1]; exact hcode
  have hS1G : GuestInv S1 := by rw [← hS1]; exact guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hS1g : S1.globals = s.globals.update (ofString "scratch_ptr", .val (.word q)) := by
    rw [← hS1]; rfl
  have hS1co : S1.code = s.code := by rw [← hS1]; rfl
  have hS1m : S1.memaddrs = s.memaddrs := by rw [← hS1]; rfl
  have hS1mem : S1.memory = s.memory := by rw [← hS1]; rfl
  clear hS1
  -- Final postcondition from a frame relative to `S1`.
  refine Ret.mono (Φ := fun v t => ∃ q' : BitVec 64, v = .val (.word q') ∧ q' = q ∧
      CJFrame S1 t (q.toNat, (jdLen nw).toNat)) ?_ ?_
  rotate_left
  · intro v t ⟨q', hv', hq', hfr⟩
    subst hq'
    refine ⟨q', hv', rfl, hc1, hc2, hqle, ?_, ?_, ?_, ?_⟩
    · exact hfr.1.trans hS1g
    · exact hfr.2.1.trans hS1co
    · exact hfr.2.2.1.trans hS1m
    · intro a ha; exact (hfr.2.2.2 a ha).trans (by rw [hS1mem])
  apply Ret.seq_call00
  intro values body callee ret v cpost h1 h2 h3
  rw [cj_args S1 q nw hS1b hS1n] at h1
  cases h1
  have hml := pan_two_word_lookup S1.code.lookup (ofString "memzero")
    (ofString "dst") (ofString "n") (sourceFnBody Guest.Software.guestFn_memzero)
    q (jdLen nw) (by decide) (by rw [hS1c]; exact lookup_memzero)
  rw [hml] at h2
  obtain ⟨hbody_m, hrest_m⟩ := Prod.mk.inj (Option.some.inj h2.symm)
  obtain ⟨hcal_m, hret_m⟩ := Prod.mk.inj hrest_m
  subst hbody_m hcal_m hret_m
  have hfr := Wave8Contracts.M28.memzero_body_frame (callEntryStateHOLFinite S1
      ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word q))).update
        (ofString "n", .val (.word (jdLen nw))))) hS1c (guestInv_callEntry _ _ hS1G)
    (by rw [h3]; exact Or.inl ⟨v, rfl⟩)
  rw [h3] at hfr
  have hdst : locN (callEntryStateHOLFinite S1
      ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word q))).update
        (ofString "n", .val (.word (jdLen nw))))) "dst" = q.toNat := by
    simp [locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hnn : locN (callEntryStateHOLFinite S1
      ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word q))).update
        (ofString "n", .val (.word (jdLen nw))))) "n" = (jdLen nw).toNat := by
    simp [locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [hdst, hnn] at hfr
  have hF2 : CJFrame S1 { cpost with locals := S1.locals } (q.toNat, (jdLen nw).toNat) := by
    obtain ⟨hc, hm, _, _, _, hg, _, _, hout, _⟩ := hfr
    refine ⟨hg, hc, hm, fun a ha => ?_⟩
    exact hout a (by simpa using ha) (by simp [CellHits])
  have hS2b : ({ cpost with locals := S1.locals } : PanSemStateFiniteExact 64 F).locals.lookup
      (ofString "bm") = some (.val (.word q)) := hS1b
  have hS2n : ({ cpost with locals := S1.locals } : PanSemStateFiniteExact 64 F).locals.lookup
      (ofString "n") = some (.val (.word nw)) := hS1n
  generalize { cpost with locals := S1.locals } = S2 at hF2 hS2b hS2n ⊢
  apply Ret.dec
  intro pv _
  have hS3b : (setVarHOLFinite (ofString "pc") pv S2).locals.lookup (ofString "bm") =
      some (.val (.word q)) := by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2b]
  have hS3n : (setVarHOLFinite (ofString "pc") pv S2).locals.lookup (ofString "n") =
      some (.val (.word nw)) := by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2n]
  have hF3 : CJFrame S1 (setVarHOLFinite (ofString "pc") pv S2) (q.toNat, (jdLen nw).toNat) :=
    hF2.trans ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  generalize setVarHOLFinite (ofString "pc") pv S2 = S3 at hS3b hS3n hF3 ⊢
  refine Ret.seq_while_inv (CJInv S1 (q.toNat, (jdLen nw).toNat) q nw) ⟨hF3, hS3b, hS3n⟩
    (by cjnr) ?_ ?_
  · intro u hu hact _
    obtain ⟨pc, hpc, hpcn⟩ := cj_active u nw hu.2.2 hact
    have hU : CJInv S1 (q.toNat, (jdLen nw).toNat) q nw (decClockHOLFinite u) :=
      ⟨hu.1.trans ⟨rfl, rfl, rfl, fun _ _ => rfl⟩, hu.2.1, hu.2.2⟩
    have hUpc : (decClockHOLFinite u).locals.lookup (ofString "pc") = some (.val (.word pc)) := hpc
    generalize decClockHOLFinite u = U at hU hUpc ⊢
    apply Flw.dec; intro ov _
    apply Flw.dec; intro av _
    apply Flw.seq
    have hV := CJInv.setVar (ofString "adv") av (by simp) (by simp)
      (CJInv.setVar (ofString "op") ov (by simp) (by simp) hU)
    have hVpc : (setVarHOLFinite (ofString "adv") av (setVarHOLFinite (ofString "op") ov U)).locals.lookup
        (ofString "pc") = some (.val (.word pc)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hUpc]
    have hVb := hV.2.1
    generalize setVarHOLFinite (ofString "adv") av (setVarHOLFinite (ofString "op") ov U) = V at hV hVpc hVb ⊢
    refine Flw.mono (Ψ1 := fun _ t => CJInv S1 (q.toNat, (jdLen nw).toNat) q nw t) ?_ ?_
    · apply Flw.ite; intro w _; constructor
      · intro _
        refine Flw.storeV (Ψ := fun _ t => CJInv S1 (q.toNat, (jdLen nw).toNat) q nw t)
          (fun v hv => ev_op_word _ _ _ _ hv) ?_
        intro a w' ha _ _
        have hae : a = q + (pc >>> (6 : Nat)) * 8 := by
          simp [ev, evalHOLExact, evalListHOLExact, hVb, hVpc, wordOpHOL, wordOp, valueIsWord,
            valueWord, panOpHOL, wordShiftHOL] at ha
          exact ha.symm
        subst hae
        exact ⟨hV.1.trans (CJFrame.of_store _ _ (cj_hit q pc nw hpcn hnb hqlt)), hV.2.1, hV.2.2⟩
      · intro _
        refine Flw.keepLoc (Ψ := fun _ t => CJInv S1 (q.toNat, (jdLen nw).toNat) q nw t)
          (ofString "bm") (ofString "n") rfl (by decide) (by decide) ?_
        intro r t hl hb hn
        exact ⟨hV.1.trans (CJFrame.of_loc hl), hb.trans hV.2.1, hn.trans hV.2.2⟩
    · intro r t ht
      constructor
      · intro _
        apply Flw.assign
        intro v _
        exact CJInv.resVar _ _ (Ne.symm (by simp)) (Ne.symm (by simp))
          (CJInv.resVar _ _ (Ne.symm (by simp)) (Ne.symm (by simp))
          (CJInv.setVar _ _ (by simp) (by simp) ht))
      · intro _
        exact CJInv.resVar _ _ (Ne.symm (by simp)) (Ne.symm (by simp))
          (CJInv.resVar _ _ (Ne.symm (by simp)) (Ne.symm (by simp)) ht)
  · intro t ⟨htF, htb, _⟩
    apply Ret.ret
    intro val hval
    simp [ev, evalHOLExact, htb] at hval
    subst hval
    exact ⟨q, rfl, rfl, htF.trans ⟨rfl, rfl, rfl, fun _ _ => rfl⟩⟩
end ComputeJumpdests

/-! ## 3n. `frame_open` never raises a catchable exception -/

section FrameOpenNoRaise
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)
open InitECandidate.Solver.GuestGlobalKeep (lookupCode_installed)

def frameOpenCallees (f : MlS) : Bool :=
  f == ofString "trap_with" || f == ofString "scratch_mark" || f == ofString "frame_mem_mark" ||
  f == ofString "scratch_alloc" || f == ofString "memzero" || f == ofString "frame_mem_alloc" ||
  f == ofString "compute_jumpdests" || f == ofString "lst_new_scratch" ||
  f == ofString "htab_new_scratch" || f == ofString "htab_count" || f == ofString "frame_new" ||
  f == ofString "frame_open"

theorem frameOpenCallees_good :
    ∀ f, frameOpenCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise frameOpenCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [frameOpenCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 14 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_scratch_mark) rfl
    change originalRuntimeCode.lookup (ofString "scratch_mark") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 11 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_frame_mem_mark) rfl
    change originalRuntimeCode.lookup (ofString "frame_mem_mark") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_scratch_alloc) rfl
    change originalRuntimeCode.lookup (ofString "scratch_alloc") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memzero) rfl
    change originalRuntimeCode.lookup (ofString "memzero") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 10 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_frame_mem_alloc) rfl
    change originalRuntimeCode.lookup (ofString "frame_mem_alloc") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 463 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_compute_jumpdests) rfl
    change originalRuntimeCode.lookup (ofString "compute_jumpdests") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 409 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_lst_new_scratch) rfl
    change originalRuntimeCode.lookup (ofString "lst_new_scratch") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 129 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_scratch) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_scratch") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 141 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_count) rfl
    change originalRuntimeCode.lookup (ofString "htab_count") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 467 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_frame_new) rfl
    change originalRuntimeCode.lookup (ofString "frame_new") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 578 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_frame_open) rfl
    change originalRuntimeCode.lookup (ofString "frame_open") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl


/-- A `frame_open` body run never ends in a catchable exception: every `Resumes` outcome is a
return. -/
theorem frame_open_resumes_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) {values body callee rs}
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "frame_open") values =
      some (body, callee, rs))
    (hres : Resumes (evaluateHOLFiniteState s body).1) :
    ∃ v, (evaluateHOLFiniteState s body).1 = some (.returned v) := by
  rcases hres with h | ⟨e, v, he, hne⟩
  · exact h
  · exact absurd he (evaluate_noCatchableRaise frameOpenCallees frameOpenCallees_good body
      (frameOpenCallees_good _ (by decide) values body callee rs hl) s hcode e v hne)

end FrameOpenNoRaise

/-! ## 3o. Arena arithmetic helpers (ported from R13 `Common` / `WkBlockTxEnc.Common`) -/

theorem hb_scratch_alloc_arith (sp fp n : BitVec 64)
    (hfp_le_sp : fp.toNat ≤ sp.toNat) (hsp_al : sp.toNat % 8 = 0)
    (hcmp1 : ¬ ((sp - fp).toNat < n.toNat))
    (hcmp2 : ¬ (((sp - n) &&& ((0 : BitVec 64) - 8)).toNat < fp.toNat)) :
    let q := (sp - n) &&& ((0 : BitVec 64) - 8)
    q.toNat % 8 = 0 ∧ fp.toNat ≤ q.toNat ∧ q.toNat ≤ sp.toNat ∧
    q.toNat + (n.toNat + 7) / 8 * 8 = sp.toNat ∧
    q.toNat + n.toNat ≤ sp.toNat := by
  intro q
  have hsp_lt := sp.isLt
  have hfp_lt := fp.isLt
  have hsub_pf : (sp - fp).toNat = sp.toNat - fp.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hn_le_gap : n.toNat ≤ sp.toNat - fp.toNat := by omega
  have hn_le_sp : n.toNat ≤ sp.toNat := by omega
  have hsub_pn : (sp - n).toNat = sp.toNat - n.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hq_nat : q.toNat = (sp.toNat - n.toNat) / 8 * 8 := by
    have h := InitECandidate.Solver.GuestTrapAndLookup.and_neg8_toNat (sp - n)
    rw [hsub_pn] at h; exact h
  have hq_ge_fp : fp.toNat ≤ q.toNat := Nat.le_of_not_lt hcmp2
  exact ⟨by omega, hq_ge_fp, by omega, by omega, by omega⟩

theorem hb_arenaReady_update_scratch_ptr {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {q : BitVec 64}
    (hG : GuestInv post) (hA : ArenaOK s)
    (hg : post.globals = s.globals.update (ofString "scratch_ptr", .val (.word q)))
    (hq_lo : globN s "frame_mem_ptr" ≤ q.toNat) (hq_hi : q.toNat ≤ scratchEnd)
    (hq8 : q.toNat % 8 = 0) :
    ArenaReady post := by
  have hhp : globN post "heap_ptr" = globN s "heap_ptr" := by
    unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide]
  have hfp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hsp : globN post "scratch_ptr" = q.toNat := by
    unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine ⟨hG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    globalsWord_update (ofString "scratch_ptr") q hg hA.2.2.2.2.2.2.2.2⟩
  · rw [hhp]; exact hA.1
  · rw [hhp]; exact hA.2.1
  · rw [hfp]; exact hA.2.2.1
  · rw [hfp, hsp]; exact hq_lo
  · rw [hsp]; exact hq_hi
  · rw [hhp]; exact hA.2.2.2.2.2.1
  · rw [hfp]; exact hA.2.2.2.2.2.2.1
  · rw [hsp]; exact hq8


/-! ## 3p. `frame_new` leaf callees: `scratch_mark` / `frame_mem_mark` -/

section FrameNewLeaves
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

attribute [local irreducible] Ret in
/-- `scratch_mark()` is `return global scratch_ptr`: no state change besides locals. -/
theorem scratch_mark_run {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hp : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word p))) :
    Ret s (sourceFnBody Guest.Software.guestFn_scratch_mark) (fun v post =>
      v = .val (.word p) ∧ post.globals = s.globals ∧
        post.memory = s.memory ∧ post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_scratch_mark =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_scratch_mark).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_scratch_mark,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.ret fun val hval => ?_
  have hv : val = .val (.word p) := by
    simp [ev, evalHOLExact, hp] at hval; exact hval.symm
  exact ⟨hv, rfl, rfl, rfl, rfl⟩

attribute [local irreducible] Ret in
/-- `frame_mem_mark()` is `return global frame_mem_ptr`: no state change besides locals. -/
theorem frame_mem_mark_run {F : Type} (s : PanSemStateFiniteExact 64 F) (f : BitVec 64)
    (hf : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f))) :
    Ret s (sourceFnBody Guest.Software.guestFn_frame_mem_mark) (fun v post =>
      v = .val (.word f) ∧ post.globals = s.globals ∧
        post.memory = s.memory ∧ post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_frame_mem_mark =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_frame_mem_mark).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_frame_mem_mark,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.ret fun val hval => ?_
  have hv : val = .val (.word f) := by
    simp [ev, evalHOLExact, hf] at hval; exact hval.symm
  exact ⟨hv, rfl, rfl, rfl, rfl⟩


end FrameNewLeaves

/-! ## 3m. `frame_new(msg)` body run -/

section FrameNewRun
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

/-- `Φ` ignores locals. -/
def LocIns {F : Type} (Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ v (t : PanSemStateFiniteExact 64 F) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    Φ v t → Φ v { t with locals := L }

theorem Ret.decCall_spec {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname : MlS}
    {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hΦ : LocIns Φ)
    (vals : List (ValueHOL 64)) (fbody : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some vals)
    (hl : lookupCodeHOLFinite s.code.lookup fname vals = some (fbody, callee, rs))
    (Ψ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (hbody : Ret (callEntryStateHOLFinite s callee) fbody Ψ)
    (hk : ∀ v post, Ψ v post → Ret (setVarHOLFinite x v { post with locals := s.locals }) cont Φ) :
    Ret s (.decCall x sh fname args cont) Φ := by
  refine Ret.decCall_gen fun values body cal ret v post h1 h2 h3 => ?_
  rw [hargs] at h1; cases h1
  rw [hl] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  have hΨ := hbody v (by rw [h3])
  rw [h3] at hΨ
  exact Ret.mono (hk v post hΨ) (fun w t h => hΦ w t _ h)

theorem Ret.seq_call_spec {F : Type} {s : PanSemStateFiniteExact 64 F} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (vals : List (ValueHOL 64)) (fbody : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some vals)
    (hl : lookupCodeHOLFinite s.code.lookup fname vals = some (fbody, callee, rs))
    (Ψ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (hbody : Ret (callEntryStateHOLFinite s callee) fbody Ψ)
    (hk : ∀ v post, Ψ v post → Ret { post with locals := s.locals } cont Φ) :
    Ret s (.seq (.call (some (none, none)) fname args) cont) Φ := by
  refine Ret.seq_call00 fun values body cal ret v post h1 h2 h3 => ?_
  rw [hargs] at h1; cases h1
  rw [hl] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  have hΨ := hbody v (by rw [h3])
  rw [h3] at hΨ
  exact hk v post hΨ

theorem callAssign_noRet {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS)
    (fname : MlS) (args : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (some (.local, x), none)) fname args)).1 ≠
      some (.returned v) := by
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
            · rw [if_pos hsh]
              split <;> simp
            · rw [if_neg hsh]; simp
          | _ => simp

theorem callAssign_inv {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {x fname : MlS} {args : List (ExpHOL 64)}
    (h : evaluateHOLFiniteState s (.call (some (some (.local, x), none)) fname args) = (none, t)) :
    ∃ values body callee retShape rv post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), post) ∧
      t = setVarHOLFinite x rv { post with locals := s.locals } := by
  rw [evaluateHOLFiniteState_call] at h
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at h; simp at h
  · rw [hargs] at h; dsimp only at h
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, retShape⟩
    · rw [hl] at h; simp at h
    · have hl' : lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) := hl
      rw [hl] at h; dsimp only at h
      split at h
      · simp at h
      · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post) := hrun
        rw [hrun] at h
        rcases r with _ | r'
        · simp at h
        · cases r' with
          | returned rv =>
            dsimp only at h
            split at h
            · split at h
              · injection h with _ ht
                exact ⟨values, body, callee, retShape, rv, post, rfl, hl', hrun', ht.symm⟩
              · simp at h
            · simp at h
          | _ => simp at h

theorem Ret.seq_callAssign_spec {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (vals : List (ValueHOL 64)) (fbody : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some vals)
    (hl : lookupCodeHOLFinite s.code.lookup fname vals = some (fbody, callee, rs))
    (Ψ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (hbody : Ret (callEntryStateHOLFinite s callee) fbody Ψ)
    (hk : ∀ v post, Ψ v post → Ret (setVarHOLFinite x v { post with locals := s.locals }) cont Φ) :
    Ret s (.seq (.call (some (some (.local, x), none)) fname args) cont) Φ := by
  refine Ret.seq (fun v hv => False.elim (callAssign_noRet s x fname args v hv)) ?_
  intro t ht
  obtain ⟨values, body, cal, ret, rv, post, h1, h2, h3, h4⟩ :=
    callAssign_inv ht
  rw [hargs] at h1; cases h1
  rw [hl] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  have hΨ := hbody rv (by rw [h3])
  rw [h3] at hΨ
  rw [h4]
  exact hk rv post hΨ

/-- A store of a word-valued expression. -/
theorem Ret.seq_storeWv {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a : BitVec 64) (hd : ev s d = some (.val (.word a)))
    (hw : ∀ v, ev s e = some v → ∃ w, v = .val (.word w))
    (hb : ∀ w, ev s e = some (.val (.word w)) → s.memaddrs a →
      Ret { s with memory := updW s.memory a w } b Φ) :
    Ret s (.seq (.store d e) b) Φ := by
  apply Ret.seq_store
  intro a' val m hd' he' hm
  rw [hd] at hd'
  simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hd'
  subst hd'
  obtain ⟨w, rfl⟩ := hw _ he'
  obtain ⟨hdom, rfl⟩ := stores_word _ hm
  exact hb w he' hdom

theorem ev_addr {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (a k : BitVec 64)
    (h : s.locals.lookup x = some (.val (.word a))) :
    ev s (.op .add [.var .local x, .const k]) = some (.val (.word (a + k))) := by
  simp [ev, evalHOLExact, evalListHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord, h]

theorem ev_loc {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) :
    ev s (.var .local x) = s.locals.lookup x := by
  simp [ev, evalHOLExact]

theorem ev_glob {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) :
    ev s (.var .global x) = s.globals.lookup x := by
  simp [ev, evalHOLExact]

theorem ev_const {F : Type} (s : PanSemStateFiniteExact 64 F) (k : BitVec 64) :
    ev s (.const k) = some (.val (.word k)) := by
  simp [ev, evalHOLExact]

theorem ev_load_isWord {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    ∀ v, ev s (.load .one e) = some v → ∃ w, v = .val (.word w) :=
  fun v h => ev_load_word s e v h

theorem lk0 {F : Type} {s : PanSemStateFiniteExact 64 F} {fname : MlS} {fb : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([], fb, .one))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {rs : ShapeHOL} (hv : vals = [])
    (h2 : lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs)) :
    body = fb ∧ callee = HolFiniteMapExact.empty := by
  subst hv
  rw [hcode, pan_zero_arg_lookup _ _ _ _ hlook] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨h2.1.symm, h2.2.1.symm⟩

theorem lk1 {F : Type} {s : PanSemStateFiniteExact 64 F} {fname p : MlS} {fb : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p, .one)], fb, .one)) (w : BitVec 64)
    {vals : List (ValueHOL 64)} {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {rs : ShapeHOL} (hv : vals = [.val (.word w)])
    (h2 : lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs)) :
    body = fb ∧ callee = HolFiniteMapExact.empty.update (p, .val (.word w)) := by
  subst hv
  rw [hcode, pan_one_word_lookup _ _ _ _ _ hlook] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨h2.1.symm, h2.2.1.symm⟩

theorem lk2 {F : Type} {s : PanSemStateFiniteExact 64 F} {fname p1 p2 : MlS} {fb : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode) (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], fb, .one))
    (w1 w2 : BitVec 64)
    {vals : List (ValueHOL 64)} {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {rs : ShapeHOL} (hv : vals = [.val (.word w1), .val (.word w2)])
    (h2 : lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs)) :
    body = fb ∧ callee = (HolFiniteMapExact.empty.update (p1, .val (.word w1))).update
      (p2, .val (.word w2)) := by
  subst hv
  rw [hcode, pan_two_word_lookup _ _ _ _ _ _ _ hne hlook] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨h2.1.symm, h2.2.1.symm⟩

/-- `decCall` with a locals-insensitive postcondition. -/
theorem Ret.decCallL {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname : MlS}
    {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hΦ : LocIns Φ)
    (hk : ∀ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Ret (setVarHOLFinite x v { post with locals := s.locals }) cont Φ) :
    Ret s (.decCall x sh fname args cont) Φ :=
  Ret.decCall_gen fun values body callee ret v post h1 h2 h3 =>
    Ret.mono (hk values body callee ret v post h1 h2 h3) (fun w t h => hΦ w t _ h)

/-- Arena re-establishment after `scratch_ptr`/`frame_mem_ptr` moves. -/
theorem arenaReady_of_sp_fmp {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hG : GuestInv t) (hA : ArenaOK s)
    (hk : ∀ k, k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
      t.globals.lookup k = s.globals.lookup k)
    (sp fp : BitVec 64)
    (hsp : t.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)))
    (hfp : t.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)))
    (h1 : scratchStart ≤ fp.toNat) (h2 : fp.toNat ≤ sp.toNat) (h3 : sp.toNat ≤ scratchEnd)
    (h4 : fp.toNat % 8 = 0) (h5 : sp.toNat % 8 = 0) : ArenaReady t := by
  have hhp : globN t "heap_ptr" = globN s "heap_ptr" := by
    unfold globN; rw [hk _ (by decide) (by decide)]
  have gsp : globN t "scratch_ptr" = sp.toNat := by unfold globN; rw [hsp]
  have gfp : globN t "frame_mem_ptr" = fp.toNat := by unfold globN; rw [hfp]
  refine ⟨hG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hhp]; exact hA.1
  · rw [hhp]; exact hA.2.1
  · rw [gfp]; exact h1
  · rw [gfp, gsp]; exact h2
  · rw [gsp]; exact h3
  · rw [hhp]; exact hA.2.2.2.2.2.1
  · rw [gfp]; exact h4
  · rw [gsp]; exact h5
  · refine globalsWord_frame ["scratch_ptr", "frame_mem_ptr"] (fun k hkm => ?_) (fun n _ hn => ?_)
      hA.2.2.2.2.2.2.2.2
    · simp only [List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at hkm
      exact (hk k hkm.1 hkm.2).symm
    · simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with hn | hn
      · exact ⟨sp, by unfold GlobalWord; rw [hn]; exact hsp⟩
      · exact ⟨fp, by unfold GlobalWord; rw [hn]; exact hfp⟩

theorem lookup_compute_jumpdests :
    originalRuntimeCode.lookup (ofString "compute_jumpdests") =
      some ([(ofString "code", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_compute_jumpdests, .one) :=
  lookup_of_guestAst_getElem 463 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_compute_jumpdests) rfl

theorem evalList2_inv {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : ExpHOL 64)
    {values : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) [a, b] =
      some values) :
    ∃ v1 v2, values = [v1, v2] ∧ ev s a = some v1 ∧ ev s b = some v2 := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp only [evalListHOLExact] at h
  revert h
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a
    with _ | v1
  · simp
  · rcases h2 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) b
      with _ | v2
    · simp
    · simp only [Option.some.injEq]
      intro h
      exact ⟨v1, v2, h.symm, h1, h2⟩

theorem evalList1_inv {F : Type} (s : PanSemStateFiniteExact 64 F) (a : ExpHOL 64)
    {values : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) [a] =
      some values) :
    ∃ v1, values = [v1] ∧ ev s a = some v1 := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp only [evalListHOLExact] at h
  revert h
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a
    with _ | v1
  · simp
  · simp only [Option.some.injEq]
    intro h
    exact ⟨v1, h.symm, h1⟩

theorem evalList0_inv {F : Type} (s : PanSemStateFiniteExact 64 F)
    {values : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) [] =
      some values) : values = [] := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp only [evalListHOLExact, Option.some.injEq] at h
  exact h.symm

theorem ofNat_add_toNat (e : BitVec 64) (k : Nat) :
    BitVec.ofNat 64 (e.toNat + k) = e + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

theorem memW_word {F : Type} (t : PanSemStateFiniteExact 64 F) (e : BitVec 64) (k : Nat)
    (w : BitVec 64) (h : t.memory (e + BitVec.ofNat 64 k) = .word w) :
    memW t (e.toNat + k) = w.toNat := by
  unfold memW; rw [ofNat_add_toNat, h]

/-- Distinct addresses by numeric value (no wrap-around). -/
theorem addr_ne (a b : BitVec 64) (i j : Nat) (hi : a.toNat + i < 2 ^ 64) (hj : b.toNat + j < 2 ^ 64)
    (hne : a.toNat + i ≠ b.toNat + j) :
    a + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (a := j) (by omega),
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact hne this

/-- A cell `a ≥ hi` is not hit by an interval ending at or below `hi`. -/
theorem not_hits_above (a : Nat) (i : Ivl) (h : i.1 + i.2 ≤ a) : ¬ CellHits a i := by
  unfold CellHits; omega

theorem toNat_add_ofNat (e : BitVec 64) (k : Nat) (h : e.toNat + k < 2 ^ 64) :
    (e + BitVec.ofNat 64 k).toNat = e.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

theorem arenaReady_locals {F : Type} (t : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (h : ArenaReady t) :
    ArenaReady { t with locals := L } :=
  ⟨guestInv_congr (s := t) rfl rfl rfl rfl h.1, arenaOK_congr (s := t) rfl h.2⟩

/-- Postcondition of a `frame_new(msg)` body run. -/
def FNPost {F : Type} (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ e : BitVec 64, v = .val (.word e) ∧ ArenaReady post ∧
    globN post "scratch_ptr" ≤ e.toNat ∧ e.toNat + 280 ≤ scratchEnd ∧ e.toNat % 8 = 0 ∧
    memW post (e.toNat + 32) = 0 ∧ memW post (e.toNat + 40) = 1024 ∧
    memW post (e.toNat + 24) + 1024 = globN post "frame_mem_ptr"

theorem fnPost_locIns {F : Type} : LocIns (F := F) FNPost := by
  intro v t L ⟨e, h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨e, h1, arenaReady_locals t L h2, h3, h4, h5, h6, h7, h8⟩

theorem scratchEnd_lt : scratchEnd + 1024 < 2 ^ 64 := by
  rw [R11Shards.scratchEnd_val]; decide

theorem Ret.apply {F : Type} {X post : PanSemStateFiniteExact 64 F} {b : ProgHOL 64}
    {Ψ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} {v : ValueHOL 64}
    (h : Ret X b Ψ) (h3 : evaluateHOLFiniteState X b = (some (.returned v), post)) : Ψ v post := by
  have := h v (by rw [h3]); rwa [h3] at this

theorem guestInv_post {F : Type} {X post : PanSemStateFiniteExact 64 F} {b : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} (hG : GuestInv X)
    (h3 : evaluateHOLFiniteState X b = (r, post)) : GuestInv post := by
  have := guestInv_evaluate X b hG; rwa [h3] at this

theorem glob_of_words {F : Type} (s : PanSemStateFiniteExact 64 F) (hA : ArenaOK s)
    (n : String) (hn : n ∈ guestGlobalNames) :
    ∃ w : BitVec 64, s.globals.lookup (ofString n) = some (.val (.word w)) ∧
      globN s n = w.toNat := by
  obtain ⟨w, hw⟩ := hA.2.2.2.2.2.2.2.2 n hn
  exact ⟨w, hw, by unfold globN; rw [hw]⟩

theorem ev_load_val {F : Type} (S : PanSemStateFiniteExact 64 F) (x : MlS) (a k : BitVec 64)
    (hx : S.locals.lookup x = some (.val (.word a))) (v : ValueHOL 64)
    (h : ev S (.load .one (.op .add [.var .local x, .const k])) = some v) :
    v = .val (S.memory (a + k)) := by
  have hd := ev_addr S x a k hx
  simp only [ev] at h hd
  rw [evalHOLExact] at h
  simp only [hd, memLoadHOLExact] at h
  split at h
  · split at h
    · exact (Option.some.inj h).symm
    · cases h
  · cases h

/-- Store at `x + k` with a word value; the continuation sees a fresh state. -/
theorem Ret.storeOff {F : Type} {S : PanSemStateFiniteExact 64 F} {x : MlS} {eb k : BitVec 64}
    {val : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hx : S.locals.lookup x = some (.val (.word eb)))
    (hw : ∀ v, ev S val = some v → ∃ w, v = .val (.word w))
    (hb : ∀ (w : BitVec 64) (S' : PanSemStateFiniteExact 64 F), ev S val = some (.val (.word w)) →
      S'.locals = S.locals →
      S'.globals = S.globals → S'.code = S.code → (GuestInv S → GuestInv S') →
      S'.memory = updW S.memory (eb + k) w → Ret S' b Φ) :
    Ret S (.seq (.store (.op .add [.var .local x, .const k]) val) b) Φ :=
  Ret.seq_storeWv _ (ev_addr S x eb k hx) hw (fun w hv _ =>
    hb w _ hv rfl rfl rfl (fun h => guestInv_congr (s := S) rfl rfl rfl rfl h) rfl)

theorem memW_upd_ne {F : Type} {S S' : PanSemStateFiniteExact 64 F} {a w : BitVec 64} (b : Nat)
    (hm : S'.memory = updW S.memory a w) (h : BitVec.ofNat 64 b ≠ a) : memW S' b = memW S b := by
  unfold memW; rw [hm, updW_ne _ _ _ _ h]

theorem memW_upd_eq {F : Type} {S S' : PanSemStateFiniteExact 64 F} (e : BitVec 64) (k : Nat)
    (w : BitVec 64) (hm : S'.memory = updW S.memory (e + BitVec.ofNat 64 k) w) :
    memW S' (e.toNat + k) = w.toNat := by
  unfold memW; rw [hm, ofNat_add_toNat, updW_eq]

/-- The `frame_new` invariant after the `memzero`. -/
def FNI {F : Type} (t : PanSemStateFiniteExact 64 F) (m e : BitVec 64) (nw v24 v40 fmp : Nat) :
    Prop :=
  t.code = originalRuntimeCode ∧ ArenaReady t ∧ globN t "scratch_ptr" ≤ e.toNat ∧
    globN t "frame_mem_ptr" = fmp ∧ memW t (e.toNat + 24) = v24 ∧ memW t (e.toNat + 32) = 0 ∧
    memW t (e.toNat + 40) = v40 ∧ memW t (m.toNat + 120) = nw ∧
    m.toNat + 176 ≤ globN t "heap_ptr" ∧ e.toNat + 280 ≤ scratchEnd ∧
    t.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
    t.locals.lookup (ofString "e") = some (.val (.word e))

theorem globN_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : t.globals = s.globals)
    (n : String) : globN t n = globN s n := by unfold globN; rw [h]

theorem memW_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : t.memory = s.memory)
    (n : Nat) : memW t n = memW s n := by unfold memW; rw [h]

theorem memW_of {F : Type} {s t : PanSemStateFiniteExact 64 F} (n : Nat)
    (h : t.memory (BitVec.ofNat 64 n) = s.memory (BitVec.ofNat 64 n)) : memW t n = memW s n := by
  unfold memW; rw [h]

theorem scratchEnd_lt64 : scratchEnd + 1024 < 2 ^ 64 := by
  rw [R11Shards.scratchEnd_val]; decide

theorem FNI.facts {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) :
    e.toNat + 280 < 2 ^ 64 ∧ m.toNat + 176 ≤ scratchStart ∧ scratchStart ≤ e.toNat := by
  obtain ⟨-, ⟨-, hA⟩, h3, -, -, -, -, -, h9, h10, -, -⟩ := h
  have := scratchEnd_lt64
  have h1 := hA.2.1; have h2 := hA.2.2.1; have h4 := hA.2.2.2.1
  refine ⟨by omega, ?_, by omega⟩
  have : heapLimit = scratchStart := rfl
  omega

theorem toNat_ofNat_lt (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Generic step: a new state with the same frame cells and invariants. -/
theorem FNI.step {F : Type} {t t' : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) (hc : t'.code = t.code)
    (hAR : ArenaReady t') (hsp : globN t' "scratch_ptr" ≤ e.toNat)
    (hheap : globN t "heap_ptr" ≤ globN t' "heap_ptr") (fmp' : Nat)
    (hfp : globN t' "frame_mem_ptr" = fmp')
    (hmem : ∀ j, j = 24 ∨ j = 32 ∨ j = 40 → t'.memory (BitVec.ofNat 64 (e.toNat + j)) =
      t.memory (BitVec.ofNat 64 (e.toNat + j)))
    (h120 : t'.memory (BitVec.ofNat 64 (m.toNat + 120)) = t.memory (BitVec.ofNat 64 (m.toNat + 120)))
    (hmsg : t'.locals.lookup (ofString "msg") = t.locals.lookup (ofString "msg"))
    (he : t'.locals.lookup (ofString "e") = t.locals.lookup (ofString "e")) :
    FNI t' m e nw v24 v40 fmp' := by
  obtain ⟨h1, -, -, -, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨hc.trans h1, hAR, hsp, hfp, (memW_of _ (hmem 24 (by simp))).trans h5,
    (memW_of _ (hmem 32 (by simp))).trans h6, (memW_of _ (hmem 40 (by simp))).trans h7,
    (memW_of _ h120).trans h8, by omega, h10, hmsg.trans h11, he.trans h12⟩

theorem setVar_lookup_ne {F : Type} (x y : MlS) (v : ValueHOL 64) (t : PanSemStateFiniteExact 64 F)
    (h : y ≠ x) : (setVarHOLFinite x v t).locals.lookup y = t.locals.lookup y := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h]

theorem setVar_lookup_eq {F : Type} (x : MlS) (v : ValueHOL 64) (t : PanSemStateFiniteExact 64 F) :
    (setVarHOLFinite x v t).locals.lookup x = some v := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem arenaReady_setVar {F : Type} (x : MlS) (v : ValueHOL 64) (t : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (h : ArenaReady t) :
    ArenaReady (setVarHOLFinite x v { t with locals := L }) :=
  arenaReady_locals t _ h

/-- Store at `e + k` for `k ∉ {24, 32, 40}`, `k < 280`. -/
theorem FNI.storeStep {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp)
    (k : Nat) (hk : k < 280) (hk8 : k % 8 = 0) (h24 : k ≠ 24) (h32 : k ≠ 32) (h40 : k ≠ 40)
    {val : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hw : ∀ v, ev t val = some v → ∃ w, v = .val (.word w))
    (hb : ∀ t' : PanSemStateFiniteExact 64 F, FNI t' m e nw v24 v40 fmp → t'.locals = t.locals →
      t'.globals = t.globals → Ret t' b Φ) :
    Ret t (.seq (.store (.op .add [.var .local (ofString "e"), .const (BitVec.ofNat 64 k)]) val) b) Φ := by
  obtain ⟨hsz, hme, hse⟩ := h.facts
  refine Ret.storeOff h.2.2.2.2.2.2.2.2.2.2.2 hw fun w t' _ hl hg hc hG hm => hb t' ?_ hl hg
  have hne : ∀ n, n + 8 ≤ e.toNat + k ∨ e.toNat + k + 8 ≤ n → n < 2 ^ 64 →
      BitVec.ofNat 64 n ≠ e + BitVec.ofNat 64 k := by
    intro n hn hlt heq
    have := congrArg BitVec.toNat heq
    rw [toNat_ofNat_lt n hlt, toNat_add_ofNat e k (by omega)] at this
    omega
  refine h.step hc ⟨hG h.2.1.1, arenaOK_congr hg h.2.1.2⟩ ?_ (by rw [globN_congr hg]) _
    (by rw [globN_congr hg]; exact h.2.2.2.1) (fun j hj => ?_) ?_ (by rw [hl]) (by rw [hl])
  · rw [globN_congr hg]; exact h.2.2.1
  · rw [hm, updW_ne _ _ _ _ (hne _ (by omega) (by omega))]
  · rw [hm, updW_ne _ _ _ _ (hne _ (by omega) (by omega))]

theorem FNI.storeStepAt {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) (k : Nat) (hk : k = 24 ∨ k = 40)
    (w : BitVec 64)
    {val : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hw : ev t val = some (.val (.word w)))
    (hb : ∀ t' : PanSemStateFiniteExact 64 F,
      FNI t' m e nw (if k = 24 then w.toNat else v24) (if k = 40 then w.toNat else v40) fmp →
      t'.locals = t.locals → t'.globals = t.globals → Ret t' b Φ) :
    Ret t (.seq (.store (.op .add [.var .local (ofString "e"), .const (BitVec.ofNat 64 k)]) val) b) Φ := by
  obtain ⟨hsz, hme, hse⟩ := h.facts
  refine Ret.storeOff h.2.2.2.2.2.2.2.2.2.2.2
    (fun v hv => ⟨w, by rw [hw] at hv; exact (Option.some.inj hv).symm⟩)
    fun w' t' hv hl hg hc hG hm => ?_
  have hww : w' = w := by
    rw [hw] at hv; simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hv
    exact hv.symm
  subst hww
  refine hb t' ?_ hl hg
  have hne : ∀ n, n + 8 ≤ e.toNat + k ∨ e.toNat + k + 8 ≤ n → n < 2 ^ 64 →
      BitVec.ofNat 64 n ≠ e + BitVec.ofNat 64 k := by
    intro n hn hlt heq
    have := congrArg BitVec.toNat heq
    rw [toNat_ofNat_lt n hlt, toNat_add_ofNat e k (by omega)] at this
    omega
  have hrd : ∀ j, j < 280 → j % 8 = 0 → memW t' (e.toNat + j) =
      if j = k then w'.toNat else memW t (e.toNat + j) := by
    intro j hj hj8
    split
    · subst j; exact memW_upd_eq e k w' hm
    · exact memW_upd_ne _ hm (hne _ (by omega) (by omega))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨hc.trans h1, ⟨hG h2.1, arenaOK_congr hg h2.2⟩, by rw [globN_congr hg]; exact h3,
    by rw [globN_congr hg]; exact h4, ?_, ?_, ?_, ?_, by rw [globN_congr hg]; exact h9, h10,
    by rw [hl]; exact h11, by rw [hl]; exact h12⟩
  · rw [hrd 24 (by omega) (by omega)]; rcases hk with rfl | rfl <;> simp [h5]
  · rw [hrd 32 (by omega) (by omega)]; rcases hk with rfl | rfl <;> simp [h6]
  · rw [hrd 40 (by omega) (by omega)]; rcases hk with rfl | rfl <;> simp [h7]
  · rw [memW_upd_ne _ hm (hne _ (by omega) (by omega))]; exact h8

/-- A call step: the continuation state is `setVar x v {post with locals := t.locals}`. -/
theorem FNI.callStep {F : Type} {t post : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) (x : MlS) (v : ValueHOL 64)
    (hx1 : ofString "msg" ≠ x) (hx2 : ofString "e" ≠ x)
    (hc : post.code = t.code) (hAR : ArenaReady post) (hsp : globN post "scratch_ptr" ≤ e.toNat)
    (hheap : globN t "heap_ptr" ≤ globN post "heap_ptr") (fmp' : Nat)
    (hfp : globN post "frame_mem_ptr" = fmp')
    (hmem : ∀ j, j = 24 ∨ j = 32 ∨ j = 40 → post.memory (BitVec.ofNat 64 (e.toNat + j)) =
      t.memory (BitVec.ofNat 64 (e.toNat + j)))
    (h120 : post.memory (BitVec.ofNat 64 (m.toNat + 120)) =
      t.memory (BitVec.ofNat 64 (m.toNat + 120))) :
    FNI (setVarHOLFinite x v { post with locals := t.locals }) m e nw v24 v40 fmp' :=
  h.step (t' := setVarHOLFinite x v { post with locals := t.locals }) hc
    (arenaReady_locals _ _ (arenaReady_locals post t.locals hAR)) hsp hheap fmp' hfp hmem h120
    (setVar_lookup_ne x _ v _ hx1) (setVar_lookup_ne x _ v _ hx2)

theorem FNI.words {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) :
    ∃ sp fp : BitVec 64, t.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) ∧
      t.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)) ∧
      globN t "scratch_ptr" = sp.toNat ∧ globN t "frame_mem_ptr" = fp.toNat := by
  obtain ⟨sp, h1, h2⟩ := glob_of_words t h.2.1.2 "scratch_ptr" (by decide)
  obtain ⟨fp, h3, h4⟩ := glob_of_words t h.2.1.2 "frame_mem_ptr" (by decide)
  exact ⟨sp, fp, h1, h3, h2, h4⟩

/-- `x := scratch_alloc(arg)` step. -/
theorem FNI.scratchAlloc {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) (x : MlS)
    (hx1 : ofString "msg" ≠ x) (hx2 : ofString "e" ≠ x) {arg : ExpHOL 64} (nv : BitVec 64)
    (harg : ev t arg = some (.val (.word nv))) {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hΦ : LocIns Φ)
    (hb : ∀ (t' : PanSemStateFiniteExact 64 F) (q : BitVec 64), FNI t' m e nw v24 v40 fmp →
      t'.locals.lookup x = some (.val (.word q)) →
      (∀ y, y ≠ x → t'.locals.lookup y = t.locals.lookup y) → Ret t' cont Φ) :
    Ret t (.decCall x .one (ofString "scratch_alloc") [arg] cont) Φ := by
  obtain ⟨sp, fp, hsp, hfp, gsp, gfp⟩ := h.words
  have hA := h.2.1.2
  have hfs : fp.toNat ≤ sp.toNat := by have := hA.2.2.2.1; omega
  have hsa : sp.toNat % 8 = 0 := by have := hA.2.2.2.2.2.2.2.1; omega
  refine Ret.mono (HtabC00Ports.decCall_scratch_alloc h.1 nv harg sp fp hsp hfp ?_)
    (fun v t h => hΦ v t _ h)
  intro hc1 hc2
  obtain ⟨qa, qf, qs, -, -⟩ := hb_scratch_alloc_arith sp fp nv hfs hsa hc1 hc2
  generalize (sp - nv) &&& ((0 : BitVec 64) - 8) = q at *
  generalize hT : setVarHOLFinite x (.val (.word q)) { t with
      globals := t.globals.update (ofString "scratch_ptr", .val (.word q)),
      clock := t.clock - 1 } = T
  have Tg : T.globals = t.globals.update (ofString "scratch_ptr", .val (.word q)) := by rw [← hT]; rfl
  have Tm : T.memory = t.memory := by rw [← hT]; rfl
  have Tc : T.code = t.code := by rw [← hT]; rfl
  have hG : GuestInv T := by rw [← hT]; exact guestInv_congr (s := t) rfl rfl rfl rfl h.2.1.1
  have hsq : T.globals.lookup (ofString "scratch_ptr") = some (.val (.word q)) := by
    rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hfq : T.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)) := by
    rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]; exact hfp
  have hkg : ∀ k, k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
      T.globals.lookup k = t.globals.lookup k := by
    intro k h1 _; rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1]
  have hse : sp.toNat ≤ scratchEnd := by have := hA.2.2.2.2.1; omega
  have hss : scratchStart ≤ fp.toNat := by have := hA.2.2.1; omega
  have hfa : fp.toNat % 8 = 0 := by have := hA.2.2.2.2.2.2.1; omega
  have hxl : T.locals.lookup x = some (.val (.word q)) := by rw [← hT]; exact setVar_lookup_eq _ _ _
  have hyl : ∀ y, y ≠ x → T.locals.lookup y = t.locals.lookup y := by
    intro y hy; rw [← hT]; exact setVar_lookup_ne _ _ _ _ hy
  refine Ret.mono (hb T q ?_ hxl hyl) (fun v t h => hΦ v t _ h)
  have hh : globN T "heap_ptr" = globN t "heap_ptr" := by
    unfold globN; rw [hkg _ (by decide) (by decide)]
  refine h.step Tc (arenaReady_of_sp_fmp hG hA hkg q fp hsq hfq hss qf (by omega) hfa qa) ?_
    (le_of_eq hh.symm) _ (by rw [← h.2.2.2.1]; unfold globN; rw [hfq, hfp]) (fun _ _ => by rw [Tm]) (by rw [Tm]) (hyl _ hx1)
    (hyl _ hx2)
  have : globN t "scratch_ptr" ≤ e.toNat := h.2.2.1
  have : globN T "scratch_ptr" = q.toNat := by unfold globN; rw [hsq]
  omega

/-- `mem := frame_mem_alloc(1024)` step: `mem` is the old `frame_mem_ptr`, which advances by 1024. -/
theorem FNI.frameMemAlloc {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hΦ : LocIns Φ)
    (hb : ∀ (t' : PanSemStateFiniteExact 64 F) (p : BitVec 64), p.toNat = fmp →
      FNI t' m e nw v24 v40 (fmp + 1024) →
      t'.locals.lookup (ofString "mem") = some (.val (.word p)) →
      (∀ y, y ≠ ofString "mem" → t'.locals.lookup y = t.locals.lookup y) → Ret t' cont Φ) :
    Ret t (.decCall (ofString "mem") .one (ofString "frame_mem_alloc")
      [.const (BitVec.ofNat 64 1024)] cont) Φ := by
  obtain ⟨sp, fp, hsp, hfp, gsp, gfp⟩ := h.words
  have hA := h.2.1.2
  have hfs : fp.toNat ≤ sp.toNat := by have := hA.2.2.2.1; omega
  have hse : sp.toNat ≤ scratchEnd := by have := hA.2.2.2.2.1; omega
  have hss : scratchStart ≤ fp.toNat := by have := hA.2.2.1; omega
  have hfa : fp.toNat % 8 = 0 := by have := hA.2.2.2.2.2.2.1; omega
  have hsa : sp.toNat % 8 = 0 := by have := hA.2.2.2.2.2.2.2.1; omega
  refine Ret.decCallL hΦ fun vals body cal ret v post h1 h2 h3 => ?_
  have hv : vals = [.val (.word 1024)] := by
    obtain ⟨v1, rfl, he1⟩ := evalList1_inv _ _ h1
    simp [ev, evalHOLExact] at he1
    rw [← he1]; rfl
  obtain ⟨rfl, rfl⟩ := lk1 h.1 R16Shards.OpHandlers.lookup_frame_mem_alloc 1024 hv h2
  have hr := R16Shards.OpHandlers.frame_mem_alloc_body_run
    (callEntryStateHOLFinite t (HolFiniteMapExact.empty.update (ofString "n", .val (.word 1024))))
    fp sp 1024 h.1 hfp hsp (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  simp only at hr
  rw [h3] at hr
  obtain ⟨rfl, hc1, hc2, hpost⟩ := hr _ rfl
  have hq := frame_mem_alloc_1024 fp sp hfs hse hfa hc1 hc2
  generalize (fp + ((1024 : BitVec 64) + 7)) &&& ((0 : BitVec 64) - 8) = q at hq hc2 hpost
  simp only at hpost
  generalize hT : setVarHOLFinite (ofString "mem") (.val (.word fp)) { post with locals := t.locals } = T
  have Tg : T.globals = t.globals.update (ofString "frame_mem_ptr", .val (.word q)) := by
    rw [← hT, hpost]; rfl
  have Tm : T.memory = t.memory := by rw [← hT, hpost]; rfl
  have Tc : T.code = t.code := by rw [← hT, hpost]; rfl
  have hG : GuestInv T := by
    rw [← hT, hpost]; exact guestInv_congr (s := t) rfl rfl rfl rfl h.2.1.1
  have hsq : T.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) := by
    rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]; exact hsp
  have hfq : T.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word q)) := by
    rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hkg : ∀ k, k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
      T.globals.lookup k = t.globals.lookup k := by
    intro k _ h2; rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h2]
  have hxl : T.locals.lookup (ofString "mem") = some (.val (.word fp)) := by
    rw [← hT]; exact setVar_lookup_eq _ _ _
  have hyl : ∀ y, y ≠ ofString "mem" → T.locals.lookup y = t.locals.lookup y := by
    intro y hy; rw [← hT]; exact setVar_lookup_ne _ _ _ _ hy
  have hfmp : fp.toNat = fmp := gfp.symm.trans h.2.2.2.1
  refine hb T fp hfmp ?_ hxl hyl
  have hh : globN T "heap_ptr" = globN t "heap_ptr" := by
    unfold globN; rw [hkg _ (by decide) (by decide)]
  have hc2' : q.toNat ≤ sp.toNat := by omega
  refine h.step Tc (arenaReady_of_sp_fmp hG hA hkg sp q hsq hfq (by omega) hc2' hse
    (by omega) hsa) ?_ (le_of_eq hh.symm) _ ?_ (fun _ _ => by rw [Tm]) (by rw [Tm])
    (hyl _ (by decide)) (hyl _ (by decide))
  · have : globN T "scratch_ptr" = sp.toNat := by unfold globN; rw [hsq]
    rw [this, ← gsp]; exact h.2.2.1
  · have : globN T "frame_mem_ptr" = q.toNat := by unfold globN; rw [hfq]
    omega

theorem ev_load_msg {F : Type} {t : PanSemStateFiniteExact 64 F} {m : BitVec 64}
    (hm : t.locals.lookup (ofString "msg") = some (.val (.word m))) (k : BitVec 64) (v : ValueHOL 64)
    (h : ev t (.load .one (.op .add [.var .local (ofString "msg"), .const k])) = some v) :
    ∃ w, v = .val (.word w) ∧ t.memory (m + k) = .word w := by
  have := ev_load_val t _ m k hm v h
  rcases hw : t.memory (m + k) with ⟨w⟩
  exact ⟨w, by rw [this, hw], rfl⟩

/-- A frame for a callee writing only inside `[lo, hi)` with `m + 128 ≤ lo` and `hi ≤ e`. -/
theorem FNI.cells_of_frame {F : Type} {t t' : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) (lo len : Nat)
    (hlo : m.toNat + 128 ≤ lo) (hhi : lo + len ≤ e.toNat)
    (hf : ∀ a : BitVec 64, ¬ CellHits a.toNat (lo, len) → t'.memory a = t.memory a) :
    (∀ j, j = 24 ∨ j = 32 ∨ j = 40 → t'.memory (BitVec.ofNat 64 (e.toNat + j)) =
      t.memory (BitVec.ofNat 64 (e.toNat + j))) ∧
    t'.memory (BitVec.ofNat 64 (m.toNat + 120)) = t.memory (BitVec.ofNat 64 (m.toNat + 120)) := by
  obtain ⟨hsz, hme, hse⟩ := h.facts
  refine ⟨fun j hj => hf _ ?_, hf _ ?_⟩
  · rw [toNat_ofNat_lt _ (by omega)]; unfold CellHits; omega
  · rw [toNat_ofNat_lt _ (by omega)]; unfold CellHits; omega

/-- `jd := compute_jumpdests(ld(msg+112), ld(msg+120))` step. -/
theorem FNI.computeJumpdests {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) (hnw : nw < 2 ^ 40) {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hΦ : LocIns Φ)
    (hb : ∀ (t' : PanSemStateFiniteExact 64 F) (q : BitVec 64), FNI t' m e nw v24 v40 fmp →
      t'.locals.lookup (ofString "jd") = some (.val (.word q)) →
      (∀ y, y ≠ ofString "jd" → t'.locals.lookup y = t.locals.lookup y) → Ret t' cont Φ) :
    Ret t (.decCall (ofString "jd") .one (ofString "compute_jumpdests")
      [.load .one (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 112)]),
       .load .one (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 120)])] cont) Φ := by
  obtain ⟨sp, fp, hsp, hfp, gsp, gfp⟩ := h.words
  obtain ⟨hsz, hme, hse⟩ := h.facts
  have hA := h.2.1.2
  have hfs : fp.toNat ≤ sp.toNat := by have := hA.2.2.2.1; omega
  have hss : scratchStart ≤ fp.toNat := by have := hA.2.2.1; omega
  have hspe : sp.toNat ≤ e.toNat := gsp ▸ h.2.2.1
  refine Ret.decCallL hΦ fun vals body cal ret v post h1 h2 h3 => ?_
  obtain ⟨v1, v2, rfl, he1, he2⟩ := evalList2_inv _ _ _ h1
  obtain ⟨w1, rfl, -⟩ := ev_load_msg h.2.2.2.2.2.2.2.2.2.2.1 _ _ he1
  obtain ⟨w2, rfl, hw2⟩ := ev_load_msg h.2.2.2.2.2.2.2.2.2.2.1 _ _ he2
  have hn : w2.toNat < 2 ^ 40 := by
    have h8 := h.2.2.2.2.2.2.2.1
    unfold memW at h8
    rw [ofNat_add_toNat, hw2] at h8
    simp only at h8
    omega
  obtain ⟨rfl, rfl⟩ := lk2 h.1 (by decide) lookup_compute_jumpdests w1 w2 rfl h2
  obtain ⟨q, rfl, hqeq, -, hqf, hqp, hg, hc, -, hmem⟩ := Ret.apply
    (compute_jumpdests_run (callEntryStateHOLFinite t _) h.1 (guestInv_callEntry _ _ h.2.1.1) w2 sp fp
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hsp hfp hfs hn) h3
  have hGp := guestInv_post (guestInv_callEntry _ _ h.2.1.1) h3
  generalize hT : setVarHOLFinite (ofString "jd") (.val (.word q)) { post with locals := t.locals } = T
  have Tg : T.globals = t.globals.update (ofString "scratch_ptr", .val (.word q)) := by
    rw [← hT]; exact hg
  have Tc : T.code = t.code := by rw [← hT]; exact hc
  have Tm : ∀ a : BitVec 64, ¬ CellHits a.toNat (q.toNat, (jdLen w2).toNat) → T.memory a = t.memory a := by
    intro a ha; rw [← hT]; exact hmem a ha
  have hG : GuestInv T := by rw [← hT]; exact guestInv_congr (s := post) rfl rfl rfl rfl hGp
  have hsq : T.globals.lookup (ofString "scratch_ptr") = some (.val (.word q)) := by
    rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hfq : T.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)) := by
    rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]; exact hfp
  have hkg : ∀ k, k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
      T.globals.lookup k = t.globals.lookup k := by
    intro k h1 _; rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1]
  have hxl : T.locals.lookup (ofString "jd") = some (.val (.word q)) := by
    rw [← hT]; exact setVar_lookup_eq _ _ _
  have hyl : ∀ y, y ≠ ofString "jd" → T.locals.lookup y = t.locals.lookup y := by
    intro y hy; rw [← hT]; exact setVar_lookup_ne _ _ _ _ hy
  refine hb T q ?_ hxl hyl
  have hh : globN T "heap_ptr" = globN t "heap_ptr" := by
    unfold globN; rw [hkg _ (by decide) (by decide)]
  have hqa : q.toNat % 8 = 0 := by
    rw [hqeq, and_neg8_toNat]; omega
  have hse' : sp.toNat ≤ scratchEnd := by have := hA.2.2.2.2.1; omega
  have hfa : fp.toNat % 8 = 0 := by have := hA.2.2.2.2.2.2.1; omega
  obtain ⟨hc24, hc120⟩ := h.cells_of_frame q.toNat (jdLen w2).toNat (by omega) (by omega) Tm
  refine h.step Tc (arenaReady_of_sp_fmp hG hA hkg q fp hsq hfq hss (by omega) (by omega)
    hfa hqa) ?_ (le_of_eq hh.symm) _ ?_ hc24 hc120 (hyl _ (by decide)) (hyl _ (by decide))
  · have : globN T "scratch_ptr" = q.toNat := by unfold globN; rw [hsq]
    omega
  · have : globN T "frame_mem_ptr" = fp.toNat := by unfold globN; rw [hfq]
    rw [this, ← gfp]; exact h.2.2.2.1

/-- `logs := lst_new_scratch(8, 4)` step. -/
theorem FNI.lstNewScratch {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hΦ : LocIns Φ)
    (hb : ∀ (t' : PanSemStateFiniteExact 64 F) (q : BitVec 64), FNI t' m e nw v24 v40 fmp →
      t'.locals.lookup (ofString "logs") = some (.val (.word q)) →
      (∀ y, y ≠ ofString "logs" → t'.locals.lookup y = t.locals.lookup y) → Ret t' cont Φ) :
    Ret t (.decCall (ofString "logs") .one (ofString "lst_new_scratch")
      [.const (BitVec.ofNat 64 8), .const (BitVec.ofNat 64 4)] cont) Φ := by
  obtain ⟨sp, fp, hsp, hfp, gsp, gfp⟩ := h.words
  obtain ⟨hsz, hme, hse⟩ := h.facts
  have hA := h.2.1.2
  have hfs : fp.toNat ≤ sp.toNat := by have := hA.2.2.2.1; omega
  have hss : scratchStart ≤ fp.toNat := by have := hA.2.2.1; omega
  have hsa : sp.toNat % 8 = 0 := by have := hA.2.2.2.2.2.2.2.1; omega
  have hspe : sp.toNat ≤ e.toNat := gsp ▸ h.2.2.1
  refine Ret.decCallL hΦ fun vals body cal ret v post h1 h2 h3 => ?_
  have hv : vals = [.val (.word 8), .val (.word 4)] := by
    obtain ⟨v1, v2, rfl, he1, he2⟩ := evalList2_inv _ _ _ h1
    simp [ev, evalHOLExact] at he1 he2
    rw [← he1, ← he2]; rfl
  obtain ⟨rfl, rfl⟩ := lk2 h.1 (by decide) lookup_lst_new_scratch 8 4 hv h2
  obtain ⟨l, q, rfl, hl, hq, hqf, hlf, hc1, hc2, hg, hm, hc, -⟩ := Ret.apply
    (lst_new_scratch_run (callEntryStateHOLFinite t _) h.1 8 4 sp fp
      (by simp (config := {decide := true}) [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hsp hfp) h3
  have hGp := guestInv_post (guestInv_callEntry _ _ h.2.1.1) h3
  have hla : l.toNat % 8 = 0 ∧ l.toNat + 24 ≤ sp.toNat := by
    have hsub : (sp - 24).toNat = sp.toNat - 24 := by
      have : ¬ ((sp - fp).toNat < (24 : BitVec 64).toNat) := hc1
      have h24 : (24 : BitVec 64).toNat = 24 := rfl
      rw [BitVec.toNat_sub] at this ⊢; rw [h24] at this ⊢; omega
    rw [hl, and_neg8_toNat, hsub]; omega
  have hqa : q.toNat % 8 = 0 ∧ q.toNat ≤ l.toNat := by
    have h32 : ((8 : BitVec 64) * 4).toNat = 32 := rfl
    have hsub : (l - 8 * 4).toNat = l.toNat - 32 := by
      have : ¬ ((l - fp).toNat < ((8 : BitVec 64) * 4).toNat) := hc2
      rw [BitVec.toNat_sub] at this ⊢; rw [h32] at this; rw [show ((8 : BitVec 64) * 4).toNat = 32 from rfl]
      omega
    rw [hq, and_neg8_toNat, hsub]; omega
  generalize hT : setVarHOLFinite (ofString "logs") (.val (.word l)) { post with locals := t.locals } = T
  have Tg : T.globals = (t.globals.update (ofString "scratch_ptr", .val (.word l))).update
      (ofString "scratch_ptr", .val (.word q)) := by rw [← hT]; exact hg
  have Tc : T.code = t.code := by rw [← hT]; exact hc
  have Tm : T.memory = updW (updW (updW t.memory (l + 0) q) (l + 8) 0) (l + 16) 4 := by
    rw [← hT]; exact hm
  have hG : GuestInv T := by rw [← hT]; exact guestInv_congr (s := post) rfl rfl rfl rfl hGp
  have hsq : T.globals.lookup (ofString "scratch_ptr") = some (.val (.word q)) := by
    rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hfq : T.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)) := by
    rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]; exact hfp
  have hkg : ∀ k, k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
      T.globals.lookup k = t.globals.lookup k := by
    intro k h1 _; rw [Tg]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1]
  have hxl : T.locals.lookup (ofString "logs") = some (.val (.word l)) := by
    rw [← hT]; exact setVar_lookup_eq _ _ _
  have hyl : ∀ y, y ≠ ofString "logs" → T.locals.lookup y = t.locals.lookup y := by
    intro y hy; rw [← hT]; exact setVar_lookup_ne _ _ _ _ hy
  refine hb T l ?_ hxl hyl
  have hh : globN T "heap_ptr" = globN t "heap_ptr" := by
    unfold globN; rw [hkg _ (by decide) (by decide)]
  have hse' : sp.toNat ≤ scratchEnd := by have := hA.2.2.2.2.1; omega
  have hfa : fp.toNat % 8 = 0 := by have := hA.2.2.2.2.2.2.1; omega
  have Tm' : ∀ a : BitVec 64, ¬ CellHits a.toNat (l.toNat, 24) → T.memory a = t.memory a := by
    intro a ha
    have hne : ∀ k : Nat, k < 24 → a ≠ l + BitVec.ofNat 64 k := by
      intro k hk heq; apply ha; rw [heq, toNat_add_ofNat l k (by omega)]; unfold CellHits; omega
    rw [Tm, updW_ne _ _ _ _ (by simpa using hne 16 (by omega)),
      updW_ne _ _ _ _ (by simpa using hne 8 (by omega)),
      updW_ne _ _ _ _ (by simpa using hne 0 (by omega))]
  obtain ⟨hc24, hc120⟩ := h.cells_of_frame l.toNat 24 (by omega) (by omega) Tm'
  refine h.step Tc (arenaReady_of_sp_fmp hG hA hkg q fp hsq hfq hss hqf (by omega)
    hfa hqa.1) ?_ (le_of_eq hh.symm) _ ?_ hc24 hc120 (hyl _ (by decide)) (hyl _ (by decide))
  · have : globN T "scratch_ptr" = q.toNat := by unfold globN; rw [hsq]
    omega
  · have : globN T "frame_mem_ptr" = fp.toNat := by unfold globN; rw [hfq]
    rw [this, ← gfp]; exact h.2.2.2.1

/-- `del := htab_new_scratch(20, 4)` step. -/
theorem FNI.htabNewScratch {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hΦ : LocIns Φ)
    (hb : ∀ (t' : PanSemStateFiniteExact 64 F) (q : BitVec 64), FNI t' m e nw v24 v40 fmp →
      t'.locals.lookup (ofString "del") = some (.val (.word q)) →
      (∀ y, y ≠ ofString "del" → t'.locals.lookup y = t.locals.lookup y) → Ret t' cont Φ) :
    Ret t (.decCall (ofString "del") .one (ofString "htab_new_scratch")
      [.const (BitVec.ofNat 64 20), .const (BitVec.ofNat 64 4)] cont) Φ := by
  obtain ⟨sp, fp, hsp, hfp, gsp, gfp⟩ := h.words
  obtain ⟨hsz, hme, hse⟩ := h.facts
  refine Ret.decCallL hΦ fun vals body cal ret v post h1 h2 h3 => ?_
  have hv : vals = [.val (.word 20), .val (.word 4)] := by
    obtain ⟨v1, v2, rfl, he1, he2⟩ := evalList2_inv _ _ _ h1
    simp [ev, evalHOLExact] at he1 he2
    rw [← he1, ← he2]; rfl
  obtain ⟨rfl, rfl⟩ := lk2 h.1 (by decide) HtabC00Ports.lookup_htab_new_scratch 20 4 hv h2
  have hAR0 : ArenaReady (callEntryStateHOLFinite t
      ((HolFiniteMapExact.empty.update (ofString "key_len", .val (.word 20))).update
        (ofString "cap", .val (.word 4)))) := ⟨guestInv_callEntry _ _ h.2.1.1, arenaOK_congr (s := t) rfl h.2.1.2⟩
  obtain ⟨w, rfl, hARp, hgrow, -, -, -, -, hfo, hkeep⟩ := Ret.apply
    (HtabC00Ports.htab_new_scratch_run (callEntryStateHOLFinite t _) h.1 20 4 sp fp
      (by simp (config := {decide := true}) [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hsp hfp hAR0
      (by decide) (by decide)) h3
  generalize hT : setVarHOLFinite (ofString "del") (.val (.word w)) { post with locals := t.locals } = T
  have hGl : ∀ n, globN T n = globN post n := fun n => by rw [← hT]; rfl
  have hxl : T.locals.lookup (ofString "del") = some (.val (.word w)) := by
    rw [← hT]; exact setVar_lookup_eq _ _ _
  have hyl : ∀ y, y ≠ ofString "del" → T.locals.lookup y = t.locals.lookup y := by
    intro y hy; rw [← hT]; exact setVar_lookup_ne _ _ _ _ hy
  refine hb T w ?_ hxl hyl
  have hsp0 : globN (callEntryStateHOLFinite t
      ((HolFiniteMapExact.empty.update (ofString "key_len", .val (.word 20))).update
        (ofString "cap", .val (.word 4)))) "scratch_ptr" = globN t "scratch_ptr" := rfl
  have hhp0 : globN (callEntryStateHOLFinite t
      ((HolFiniteMapExact.empty.update (ofString "key_len", .val (.word 20))).update
        (ofString "cap", .val (.word 4)))) "heap_ptr" = globN t "heap_ptr" := rfl
  have hspe := h.2.2.1
  have hheap := h.2.2.2.2.2.2.2.2.1
  have hmemf : ∀ a : BitVec 64, ((e.toNat ≤ a.toNat ∧ a.toNat < e.toNat + 280) ∨
      (m.toNat + 120 = a.toNat)) → T.memory a = t.memory a := by
    intro a ha
    have g1 := hgrow.2; rw [hsp0] at g1
    have g2 := hgrow.1; rw [hhp0] at g2
    have g3 := hARp.2.2.1; have g4 := hARp.2.2.2.2.1; have g5 := hARp.2.2.2.1
    have g6 : heapLimit = scratchStart := rfl
    rw [← hT]
    refine hfo a ?_ ?_
    · intro i hi
      simp only [List.mem_singleton] at hi; subst hi
      unfold CellHits; rw [hsp0]; omega
    · unfold CellHits; rw [hhp0]; omega
  have Tc : T.code = t.code := by
    rw [← hT]; exact hARp.1.1.trans h.1.symm
  refine h.step Tc (by rw [← hT]; exact arenaReady_locals _ _ (arenaReady_locals post t.locals hARp))
    ?_ ?_ _ ?_ (fun j hj => hmemf _ (Or.inl ?_)) (hmemf _ (Or.inr ?_))
    (hyl _ (by decide)) (hyl _ (by decide))
  · rw [hGl]; have := hgrow.2; rw [hsp0] at this; omega
  · rw [hGl]; have := hgrow.1; rw [hhp0] at this; omega
  · rw [hGl, ← h.2.2.2.1]; unfold globN
    rw [← hkeep _ (by simp (config := {decide := true}))]; rfl
  · rw [toNat_ofNat_lt _ (by omega)]; omega
  · rw [toNat_ofNat_lt _ (by omega)]

theorem evalList_load_msg {F : Type} {t : PanSemStateFiniteExact 64 F} {m : BitVec 64}
    (hm : t.locals.lookup (ofString "msg") = some (.val (.word m))) (k : BitVec 64) :
    ∃ w, evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.load .one (.op .add [.var .local (ofString "msg"), .const k])] = some [.val (.word w)] ∨
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.load .one (.op .add [.var .local (ofString "msg"), .const k])] = none := by
  rcases hv : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.load .one (.op .add [.var .local (ofString "msg"), .const k])] with _ | vs
  · exact ⟨0, Or.inr rfl⟩
  · obtain ⟨v1, rfl, he⟩ := evalList1_inv _ _ hv
    obtain ⟨w, rfl, -⟩ := ev_load_msg hm k v1 he
    exact ⟨w, Or.inl rfl⟩

attribute [local irreducible] Ret in
theorem htab_count_word {F : Type} (s : PanSemStateFiniteExact 64 F) :
    Ret s (sourceFnBody Guest.Software.guestFn_htab_count) (fun v _ => ∃ w, v = .val (.word w)) := by
  have hb : sourceFnBody Guest.Software.guestFn_htab_count =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_htab_count).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_htab_count,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Ret.of_NS
  apply Ret.ns_ret
  intro val hval
  exact ev_load_word _ _ _ hval

theorem htab_count_post {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) (w : BitVec 64) (x : MlS)
    (hx1 : ofString "msg" ≠ x) (hx2 : ofString "e" ≠ x) (rv : ValueHOL 64)
    (post : PanSemStateFiniteExact 64 F)
    (h3 : evaluateHOLFiniteState (callEntryStateHOLFinite t
      (HolFiniteMapExact.empty.update (ofString "t", .val (.word w))))
      (sourceFnBody Guest.Software.guestFn_htab_count) = (some (.returned rv), post)) :
    FNI (setVarHOLFinite x rv { post with locals := t.locals }) m e nw v24 v40 fmp := by
  obtain ⟨hg, hm, hc, -⟩ := Ret.apply (htab_count_run (callEntryStateHOLFinite t _)) h3
  have hGp := guestInv_post (guestInv_callEntry _ _ h.2.1.1) h3
  refine h.step (t' := setVarHOLFinite x rv { post with locals := t.locals }) hc
    ⟨guestInv_congr (s := post) rfl rfl rfl rfl hGp, arenaOK_congr (s := t) hg h.2.1.2⟩
    ?_ (le_of_eq (globN_congr hg _).symm) _ ?_ (fun _ _ => by
      show post.memory _ = _; rw [hm]; rfl) (by show post.memory _ = _; rw [hm]; rfl)
    (setVar_lookup_ne _ _ _ _ hx1) (setVar_lookup_ne _ _ _ _ hx2)
  · rw [globN_congr (t := setVarHOLFinite x rv { post with locals := t.locals }) (s := t) hg]
    exact h.2.2.1
  · rw [globN_congr (t := setVarHOLFinite x rv { post with locals := t.locals }) (s := t) hg]
    exact h.2.2.2.1

/-- `acc_n := htab_count(ld(msg+k))` (declaration form). -/
theorem FNI.htabCountDec {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) (k : BitVec 64) {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hΦ : LocIns Φ)
    (hb : ∀ (t' : PanSemStateFiniteExact 64 F) (v : BitVec 64), FNI t' m e nw v24 v40 fmp →
      t'.locals.lookup (ofString "acc_n") = some (.val (.word v)) →
      (∀ y, y ≠ ofString "acc_n" → t'.locals.lookup y = t.locals.lookup y) → Ret t' cont Φ) :
    Ret t (.decCall (ofString "acc_n") .one (ofString "htab_count")
      [.load .one (.op .add [.var .local (ofString "msg"), .const k])] cont) Φ := by
  refine Ret.decCallL hΦ fun vals body cal ret v post h1 h2 h3 => ?_
  obtain ⟨v1, rfl, he⟩ := evalList1_inv _ _ h1
  obtain ⟨w, rfl, -⟩ := ev_load_msg h.2.2.2.2.2.2.2.2.2.2.1 k v1 he
  obtain ⟨rfl, rfl⟩ := lk1 h.1 lookup_htab_count w rfl h2
  obtain ⟨u, rfl⟩ := Ret.apply (htab_count_word _) h3
  exact hb _ u (htab_count_post h w _ (by decide) (by decide) _ post h3) (setVar_lookup_eq _ _ _)
    (fun y hy => setVar_lookup_ne _ _ _ _ hy)

/-- `acc_n := htab_count(ld(msg+k))` (assignment form). -/
theorem FNI.htabCountAssign {F : Type} {t : PanSemStateFiniteExact 64 F} {m e : BitVec 64}
    {nw v24 v40 fmp : Nat} (h : FNI t m e nw v24 v40 fmp) (k : BitVec 64) {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hb : ∀ (t' : PanSemStateFiniteExact 64 F) (v : BitVec 64), FNI t' m e nw v24 v40 fmp →
      t'.locals.lookup (ofString "acc_n") = some (.val (.word v)) →
      (∀ y, y ≠ ofString "acc_n" → t'.locals.lookup y = t.locals.lookup y) → Ret t' cont Φ) :
    Ret t (.seq (.call (some (some (.local, ofString "acc_n"), none)) (ofString "htab_count")
      [.load .one (.op .add [.var .local (ofString "msg"), .const k])]) cont) Φ := by
  refine Ret.seq (fun v hv => False.elim (callAssign_noRet t _ _ _ v hv)) ?_
  intro t2 ht
  obtain ⟨values, body, cal, ret, rv, post, h1, h2, h3, h4⟩ := callAssign_inv ht
  obtain ⟨v1, rfl, he⟩ := evalList1_inv _ _ h1
  obtain ⟨w, rfl, -⟩ := ev_load_msg h.2.2.2.2.2.2.2.2.2.2.1 k v1 he
  obtain ⟨rfl, rfl⟩ := lk1 h.1 lookup_htab_count w rfl h2
  rw [h4]
  obtain ⟨u, rfl⟩ := Ret.apply (htab_count_word _) h3
  exact hb _ u (htab_count_post h w _ (by decide) (by decide) _ post h3) (setVar_lookup_eq _ _ _)
    (fun y hy => setVar_lookup_ne _ _ _ _ hy)

attribute [local irreducible] Ret in
theorem frame_new_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s) (m : BitVec 64)
    (hm : s.locals.lookup (ofString "msg") = some (.val (.word m)))
    (hmlo : m.toNat + 176 ≤ globN s "heap_ptr") (hnb : memW s (m.toNat + 120) < 2 ^ 40) :
    Ret s (sourceFnBody Guest.Software.guestFn_frame_new) FNPost := by
  have hb : sourceFnBody Guest.Software.guestFn_frame_new =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_frame_new).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_frame_new,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  obtain ⟨sp0, hsp0, gsp0⟩ := glob_of_words s hAR.2 "scratch_ptr" (by decide)
  obtain ⟨fp0, hfp0, gfp0⟩ := glob_of_words s hAR.2 "frame_mem_ptr" (by decide)
  have hA := hAR.2
  have hfs : fp0.toNat ≤ sp0.toNat := by have := hA.2.2.2.1; omega
  have hse : sp0.toNat ≤ scratchEnd := by have := hA.2.2.2.2.1; omega
  have hss : scratchStart ≤ fp0.toNat := by have := hA.2.2.1; omega
  have hsa : sp0.toNat % 8 = 0 := by have := hA.2.2.2.2.2.2.2.1; omega
  have hfa : fp0.toNat % 8 = 0 := by have := hA.2.2.2.2.2.2.1; omega
  -- scratch_mark
  refine Ret.decCallL fnPost_locIns fun vals body cal ret v post h1 h2 h3 => ?_
  obtain ⟨rfl, rfl⟩ := lk0 hcode lookup_scratch_mark (evalList0_inv _ h1) h2
  obtain ⟨rfl, hg1, hmem1, hc1, hma1⟩ := Ret.apply (scratch_mark_run (callEntryStateHOLFinite s _) sp0 hsp0) h3
  have hG1 := guestInv_post (guestInv_callEntry _ _ hAR.1) h3
  generalize hS1 : setVarHOLFinite (ofString "stack_mark") (.val (.word sp0))
    { post with locals := s.locals } = S1
  have S1g : S1.globals = s.globals := by rw [← hS1]; exact hg1
  have S1m : S1.memory = s.memory := by rw [← hS1]; exact hmem1
  have S1c : S1.code = originalRuntimeCode := by rw [← hS1]; exact hc1.trans hcode
  have S1G : GuestInv S1 := by rw [← hS1]; exact guestInv_congr (s := post) rfl rfl rfl rfl hG1
  have S1l : ∀ x, x ≠ ofString "stack_mark" → S1.locals.lookup x = s.locals.lookup x := by
    intro x hx; rw [← hS1]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]
  have S1sm : S1.locals.lookup (ofString "stack_mark") = some (.val (.word sp0)) := by
    rw [← hS1]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  clear hS1 hg1 hmem1 hc1 hma1 hG1 h1 h2 h3
  -- frame_mem_mark
  refine Ret.decCallL fnPost_locIns fun vals body cal ret v post h1 h2 h3 => ?_
  obtain ⟨rfl, rfl⟩ := lk0 S1c lookup_frame_mem_mark (evalList0_inv _ h1) h2
  obtain ⟨rfl, hg2, hmem2, hc2, hma2⟩ := Ret.apply
    (frame_mem_mark_run (callEntryStateHOLFinite S1 _) fp0 (by rw [show (callEntryStateHOLFinite S1 HolFiniteMapExact.empty).globals = S1.globals from rfl, S1g]; exact hfp0)) h3
  have hG2 := guestInv_post (guestInv_callEntry _ _ S1G) h3
  generalize hS2 : setVarHOLFinite (ofString "mem_mark") (.val (.word fp0))
    { post with locals := S1.locals } = S2
  have S2g : S2.globals = s.globals := by rw [← hS2]; exact hg2.trans S1g
  have S2m : S2.memory = s.memory := by rw [← hS2]; exact hmem2.trans S1m
  have S2c : S2.code = originalRuntimeCode := by rw [← hS2]; exact hc2.trans S1c
  have S2G : GuestInv S2 := by rw [← hS2]; exact guestInv_congr (s := post) rfl rfl rfl rfl hG2
  have S2msg : S2.locals.lookup (ofString "msg") = some (.val (.word m)) := by
    rw [← hS2]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [S1l _ (by decide)]; exact hm
  have S2sm : S2.locals.lookup (ofString "stack_mark") = some (.val (.word sp0)) := by
    rw [← hS2]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]; exact S1sm
  have S2mm : S2.locals.lookup (ofString "mem_mark") = some (.val (.word fp0)) := by
    rw [← hS2]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  clear hS2 hg2 hmem2 hc2 hma2 hG2 h1 h2 h3 S1l S1sm S1g S1m S1c S1G
  -- e := scratch_alloc(280)
  apply Ret.mono (Φ := FNPost) ?_ (fun v t h => h)
  refine HtabC00Ports.decCall_scratch_alloc S2c 280 (by simp [ev, evalHOLExact]) sp0 fp0
    (by rw [S2g]; exact hsp0) (by rw [S2g]; exact hfp0) ?_
  intro hc1 hc2
  refine Ret.mono (Φ := FNPost) ?_ (fun v t h => fnPost_locIns v t _ h)
  obtain ⟨ea, efp, esp, eadd, -⟩ := hb_scratch_alloc_arith sp0 fp0 280 hfs hsa hc1 hc2
  generalize hE : (sp0 - 280) &&& ((0 : BitVec 64) - 8) = e at *
  have e280 : e.toNat + 280 ≤ sp0.toNat := by
    have : (280 : BitVec 64).toNat = 280 := rfl
    omega
  generalize hS3 : setVarHOLFinite (ofString "e") (.val (.word e))
    { S2 with globals := S2.globals.update (ofString "scratch_ptr", .val (.word e)),
              clock := S2.clock - 1 } = S3
  have S3g : S3.globals = s.globals.update (ofString "scratch_ptr", .val (.word e)) := by
    rw [← hS3, ← S2g]; rfl
  have S3m : S3.memory = s.memory := by rw [← hS3]; exact S2m
  have S3c : S3.code = originalRuntimeCode := by rw [← hS3]; exact S2c
  have S3G : GuestInv S3 := by rw [← hS3]; exact guestInv_congr (s := S2) rfl rfl rfl rfl S2G
  have S3sp : S3.globals.lookup (ofString "scratch_ptr") = some (.val (.word e)) := by
    rw [S3g]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have S3fp : S3.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp0)) := by
    rw [S3g]; simp [HolFiniteMapExact.lookup_update, FUPDATE]; exact hfp0
  have S3e : S3.locals.lookup (ofString "e") = some (.val (.word e)) := by
    rw [← hS3]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have S3msg : S3.locals.lookup (ofString "msg") = some (.val (.word m)) := by
    rw [← hS3]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]; exact S2msg
  have S3sm : S3.locals.lookup (ofString "stack_mark") = some (.val (.word sp0)) := by
    rw [← hS3]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]; exact S2sm
  have S3mm : S3.locals.lookup (ofString "mem_mark") = some (.val (.word fp0)) := by
    rw [← hS3]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]; exact S2mm
  have S3AR : ArenaReady S3 :=
    arenaReady_of_sp_fmp S3G hA (fun k h1 h2 => by rw [S3g]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1])
      e fp0 S3sp S3fp hss efp (by omega) hfa ea
  clear hS3 S2g S2m S2c S2G S2msg S2sm S2mm
  -- memzero(e, 280)
  refine Ret.seq_call00 fun vals body cal ret v post h1 h2 h3 => ?_
  have hv : vals = [.val (.word e), .val (.word 280)] := by
    obtain ⟨v1, v2, rfl, he1, he2⟩ := evalList2_inv _ _ _ h1
    simp [ev, evalHOLExact, S3e] at he1 he2
    rw [← he1, ← he2]; rfl
  obtain ⟨rfl, rfl⟩ := lk2 S3c (by decide) lookup_memzero e 280 hv h2
  obtain ⟨hz, hfr⟩ := memzero_call_zero S3 S3c S3AR e 280 v post h3
  obtain ⟨fc, fm, -, -, -, fg, -, -, fout, -⟩ := hfr
  generalize hS4 : { post with locals := S3.locals } = S4
  have S4g : S4.globals = S3.globals := by rw [← hS4]; exact fg
  have S4c : S4.code = originalRuntimeCode := by rw [← hS4]; exact fc.trans S3c
  have S4ma : S4.memaddrs = S3.memaddrs := by rw [← hS4]; exact fm
  have S4G : GuestInv S4 := by
    rw [← hS4]; exact guestInv_congr (s := post) rfl rfl rfl rfl (guestInv_post (guestInv_callEntry _ _ S3G) h3)
  have S4l : S4.locals = S3.locals := by rw [← hS4]
  have S4z : ∀ a, e.toNat ≤ a → a + 8 ≤ e.toNat + 280 → a % 8 = 0 → memW S4 a = 0 := by
    intro a h1 h2 h3; rw [← hS4]; exact hz a h1 (by simpa using h2) h3
  have S4out : ∀ a : BitVec 64, ¬ CellHits a.toNat (e.toNat, 280) → S4.memory a = S3.memory a := by
    intro a ha; rw [← hS4]; exact fout a (by simpa using ha) (by simp [CellHits])
  have S4AR : ArenaReady S4 := ⟨S4G, arenaOK_congr (s := S3) S4g S3AR.2⟩
  have hsz : e.toNat + 280 < 2 ^ 64 := by have := scratchEnd_lt64; omega
  have S4w : ∀ j, j < 280 → j % 8 = 0 → memW S4 (e.toNat + j) = 0 :=
    fun j hj h8 => S4z _ (by omega) (by omega) (by omega)
  have S4mm : memW S4 (m.toNat + 120) = memW s (m.toNat + 120) := by
    unfold memW
    have hl1 := hA.2.1; have hl2 : heapLimit = scratchStart := rfl
    have := scratchEnd_lt64
    rw [S4out _ (by rw [toNat_ofNat_lt _ (by omega)]; unfold CellHits; omega), S3m]
  have hheap : m.toNat + 176 ≤ globN S4 "heap_ptr" := by
    have : globN S4 "heap_ptr" = globN s "heap_ptr" := by
      unfold globN; rw [S4g, S3g]; simp (config := {decide := true}) [HolFiniteMapExact.lookup_update, FUPDATE]
    omega
  have I4 : FNI S4 m e (memW s (m.toNat + 120)) 0 0 fp0.toNat := by
    refine ⟨S4c, S4AR, ?_, ?_, S4w 24 (by omega) (by omega), S4w 32 (by omega) (by omega),
      S4w 40 (by omega) (by omega), S4mm, hheap, by omega, by rw [S4l]; exact S3msg,
      by rw [S4l]; exact S3e⟩
    · unfold globN; rw [S4g, S3sp]
    · unfold globN; rw [S4g, S3fp]
  clear hS4 h1 h2 h3 hz fc fm fg fout hv S4z S4out S4w
  -- stk := scratch_alloc(32*32)
  refine I4.scratchAlloc _ (by decide) (by decide) 1024 (by rw [show (1024 : BitVec 64) = 32 * 32 from rfl]; simp [ev, evalHOLExact, evalListHOLExact, panOpHOL, valueIsWord, valueWord]) fnPost_locIns
    fun t5 stk I5 h5stk h5l => ?_
  refine I5.storeStep 208 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ev_var_word _ _ sp0 (by rw [h5l _ (by decide), S4l]; exact S3sm) v hv)
    fun t6 I6 h6l _ => ?_
  refine I6.storeStep 8 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ev_var_word _ _ stk (by rw [h6l]; exact h5stk) v hv) fun t7 I7 h7l _ => ?_
  refine I7.storeStep 232 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ⟨32, by simp [ev, evalHOLExact] at hv; rw [← hv]; rfl⟩) fun t8 I8 h8l _ => ?_
  -- mem := frame_mem_alloc(1024)
  refine I8.frameMemAlloc fnPost_locIns fun t9 p hp I9 h9mem h9l => ?_
  refine I9.storeStep 224 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ev_var_word _ _ fp0 (by rw [h9l _ (by decide), h8l, h7l, h6l, h5l _ (by decide), S4l]; exact S3mm) v hv)
    fun t10 I10 h10l _ => ?_
  refine I10.storeStepAt 24 (Or.inl rfl) p (by rw [ev_loc, h10l, h9mem]) fun t11 I11 h11l _ => ?_
  refine I11.storeStepAt 40 (Or.inr rfl) 1024 (ev_const _ _) fun t12 I12 h12l _ => ?_
  simp only [show ((40 : Nat) = 24) = False by decide, show ((24 : Nat) = 40) = False by decide, if_false] at I12
  have hmsg : ∀ t' : PanSemStateFiniteExact 64 F, FNI t' m e (memW s (m.toNat + 120)) p.toNat
      (1024 : BitVec 64).toNat (fp0.toNat + 1024) →
      t'.locals.lookup (ofString "msg") = some (.val (.word m)) := fun t' I => I.2.2.2.2.2.2.2.2.2.2.1
  have hldw : ∀ (t' : PanSemStateFiniteExact 64 F) (k : BitVec 64),
      FNI t' m e (memW s (m.toNat + 120)) p.toNat (1024 : BitVec 64).toNat (fp0.toNat + 1024) →
      ∀ v, ev t' (.load .one (.op .add [.var .local (ofString "msg"), .const k])) = some v →
        ∃ w, v = .val (.word w) := fun t' k I => ev_load_isWord t' _
  refine I12.storeStep 48 (by omega) (by omega) (by omega) (by omega) (by omega) (hldw _ _ I12)
    fun t13 I13 _ _ => ?_
  refine I13.storeStep 56 (by omega) (by omega) (by omega) (by omega) (by omega) (hldw _ _ I13)
    fun t14 I14 _ _ => ?_
  refine I14.storeStep 64 (by omega) (by omega) (by omega) (by omega) (by omega) (hldw _ _ I14)
    fun t15 I15 _ _ => ?_
  refine I15.storeStep 72 (by omega) (by omega) (by omega) (by omega) (by omega) (hldw _ _ I15)
    fun t16 I16 _ _ => ?_
  -- jd := compute_jumpdests
  refine I16.computeJumpdests hnb fnPost_locIns fun t17 jd I17 h17jd _ => ?_
  refine I17.storeStep 80 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ev_var_word _ _ jd h17jd v hv) fun t18 I18 _ _ => ?_
  -- logs := lst_new_scratch(8, 4)
  refine I18.lstNewScratch fnPost_locIns fun t19 lg I19 h19 _ => ?_
  refine I19.storeStep 88 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ev_var_word _ _ lg h19 v hv) fun t20 I20 _ _ => ?_
  refine I20.storeStep 104 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ⟨1, by simp [ev, evalHOLExact] at hv; rw [← hv]; rfl⟩) fun t21 I21 _ _ => ?_
  refine I21.storeStep 112 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ev_var_word _ _ m (hmsg _ I21) v hv) fun t22 I22 _ _ => ?_
  -- del := htab_new_scratch(20, 4)
  refine I22.htabNewScratch fnPost_locIns fun t23 dl I23 h23 _ => ?_
  refine I23.storeStep 136 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ev_var_word _ _ dl h23 v hv) fun t24 I24 _ _ => ?_
  refine I24.storeStep 168 (by omega) (by omega) (by omega) (by omega) (by omega) (hldw _ _ I24)
    fun t25 I25 _ _ => ?_
  refine I25.storeStep 176 (by omega) (by omega) (by omega) (by omega) (by omega) (hldw _ _ I25)
    fun t26 I26 _ _ => ?_
  -- acc_n := htab_count(...) ×2
  refine I26.htabCountDec _ fnPost_locIns fun t27 a1 I27 h27 _ => ?_
  refine I27.storeStep 264 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ev_var_word _ _ a1 h27 v hv) fun t28 I28 _ _ => ?_
  refine I28.htabCountAssign _ fun t29 a2 I29 h29 _ => ?_
  refine I29.storeStep 272 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ev_var_word _ _ a2 h29 v hv) fun t30 I30 _ _ => ?_
  have hgw : ∀ (t' : PanSemStateFiniteExact 64 F),
      FNI t' m e (memW s (m.toNat + 120)) p.toNat (1024 : BitVec 64).toNat (fp0.toNat + 1024) →
      ∀ v, ev t' (.var .global (ofString "evm_empty")) = some v → ∃ w, v = .val (.word w) := by
    intro t' I v hv
    obtain ⟨w, hw⟩ := I.2.1.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
    rw [ev_glob] at hv; unfold GlobalWord at hw; rw [hw] at hv
    exact ⟨w, (Option.some.inj hv).symm⟩
  refine I30.storeStep 120 (by omega) (by omega) (by omega) (by omega) (by omega) (hgw _ I30)
    fun t31 I31 _ _ => ?_
  refine I31.storeStep 144 (by omega) (by omega) (by omega) (by omega) (by omega) (hgw _ I31)
    fun t32 I32 _ _ => ?_
  refine I32.storeStep 216 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun v hv => ⟨0, by simp [ev, evalHOLExact] at hv; rw [← hv]; rfl⟩) fun t33 I33 _ _ => ?_
  -- return e
  refine Ret.ret fun val hval => ?_
  rw [ev_loc, I33.2.2.2.2.2.2.2.2.2.2.2] at hval
  cases hval
  obtain ⟨-, hAR33, hsp33, hfp33, h24, h32, h40, -, -, h280, -, -⟩ := I33
  refine ⟨e, rfl, arenaReady_locals _ _ hAR33, hsp33, h280, ea, h32, ?_, ?_⟩
  · exact h40
  · show memW t33 (e.toNat + 24) + 1024 = globN t33 "frame_mem_ptr"
    rw [h24, hfp33, hp]; simp

end FrameNewRun

/-! ## 4. The required statement -/

/-- `run_frames` is bounded by `K.run_frames` from every `EvmInv ∧ HeadMemChainWF` entry, given
the bounds of the four callees and their aligned contracts (the aligned `op_dispatch` contract
takes `EvmInv ∧ HeadMemChainWF ∧ ¬ EvmDone`). -/
theorem gbody_run_frames_aligned
    (bf : TerminatingFunBoundedOn FinishReadyA (ofString "finish_child") K.«finish_child»)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue»)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception»)
    (bd : TerminatingFunBoundedOn EvmRunA (ofString "op_dispatch") K.«op_dispatch»)
    (hf : FinishChildSpecA) (he : FrameEpilogueSpecA) (hx : FrameExceptionSpecA)
    (hd : OpDispatchSpecA) :
    TerminatingFunBoundedOn (fun s => EvmInv s ∧ HeadMemChainWF s) (ofString "run_frames")
      K.«run_frames» :=
  gbody_run_frames_w bf be bx bd hf he hx (opDispatchSpecW_of_A hd)

/-- `gbody_run_frames_aligned` with the aligned epilogue contract discharged. -/
theorem gbody_run_frames_aligned'
    (bf : TerminatingFunBoundedOn FinishReadyA (ofString "finish_child") K.«finish_child»)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue»)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception»)
    (bd : TerminatingFunBoundedOn EvmRunA (ofString "op_dispatch") K.«op_dispatch»)
    (hf : FinishChildSpecA) (hx : FrameExceptionSpecA) (hd : OpDispatchSpecA) :
    TerminatingFunBoundedOn (fun s => EvmInv s ∧ HeadMemChainWF s) (ofString "run_frames")
      K.«run_frames» :=
  gbody_run_frames_aligned bf be bx bd hf frame_epilogue_spec_aligned hx hd

/-- `gbody_run_frames_aligned` with the aligned epilogue and exception contracts discharged:
only the aligned `finish_child` and `op_dispatch` contracts remain as hypotheses. -/
theorem gbody_run_frames_aligned''
    (bf : TerminatingFunBoundedOn FinishReadyA (ofString "finish_child") K.«finish_child»)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue»)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception»)
    (bd : TerminatingFunBoundedOn EvmRunA (ofString "op_dispatch") K.«op_dispatch»)
    (hf : FinishChildSpecA) (hd : OpDispatchSpecA) :
    TerminatingFunBoundedOn (fun s => EvmInv s ∧ HeadMemChainWF s) (ofString "run_frames")
      K.«run_frames» :=
  gbody_run_frames_aligned bf be bx bd hf frame_epilogue_spec_aligned
    frame_exception_spec_aligned hd

/-- `gbody_run_frames_aligned''` with the aligned `finish_child` contract derived from the
unaligned `finish_child_spec` shape and its frame-memory footprint (`FinishChildMemSpec`). -/
theorem gbody_run_frames_aligned_fc
    (bf : TerminatingFunBoundedOn FinishReadyA (ofString "finish_child") K.«finish_child»)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue»)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception»)
    (bd : TerminatingFunBoundedOn EvmRunA (ofString "op_dispatch") K.«op_dispatch»)
    (hfu : FinishChildSpecU) (hfm : FinishChildMemSpec) (hd : OpDispatchSpecA) :
    TerminatingFunBoundedOn (fun s => EvmInv s ∧ HeadMemChainWF s) (ofString "run_frames")
      K.«run_frames» :=
  gbody_run_frames_aligned'' bf be bx bd (finish_child_spec_aligned hfu hfm) hd

/-- Every frame-function bound that holds under the unaligned guard also holds under the
aligned one. -/
theorem finishReadyA_bound
    (h : TerminatingFunBoundedOn FinishReady (ofString "finish_child") K.«finish_child») :
    TerminatingFunBoundedOn FinishReadyA (ofString "finish_child") K.«finish_child» :=
  h.mono (fun _ hs => ⟨hs.1.1, hs.2.1, hs.2.2⟩)

theorem evmRunA_bound
    (h : TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.«op_dispatch») :
    TerminatingFunBoundedOn EvmRunA (ofString "op_dispatch") K.«op_dispatch» :=
  h.mono (fun _ hs => ⟨hs.1.1, hs.2⟩)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
