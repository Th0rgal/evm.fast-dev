import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmGBody
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group04
import InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
import InitECandidate.Solver.GuestGlobalKeep
import InitECandidate.Solver.GuestFrameMemKeep
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M28.ww_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.zv_memzero
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChild

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

/-! ## 3n. `frame_open(msg, 0)` body run and `FrameOpenMemSpecB` -/

section FrameOpenRun
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

/-- Postcondition of a `frame_open(msg, kind)` body run with `kind = 0`. -/
def FOPost {F : Type} (_v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) : Prop :=
  memW post (globN post "cur_cont" + 16) = 0 ∧
  memW post (globN post "ev" + 32) = 0 ∧ memW post (globN post "ev" + 40) = 1024 ∧
  memW post (globN post "ev" + 24) + 1024 = globN post "frame_mem_ptr"

theorem foPost_locIns {F : Type} : LocIns (F := F) FOPost := fun _ _ _ h => h

theorem memW_upd_off {F : Type} {S S' : PanSemStateFiniteExact 64 F} {q w : BitVec 64} (j n : Nat)
    (hm : S'.memory = updW S.memory (q + BitVec.ofNat 64 j) w)
    (h1 : q.toNat + j + 8 ≤ n ∨ n + 8 ≤ q.toNat + j) (h2 : n < 2 ^ 64) (h3 : q.toNat + j < 2 ^ 64) :
    memW S' n = memW S n := by
  refine memW_upd_ne n hm ?_
  intro heq
  have := congrArg BitVec.toNat heq
  rw [toNat_ofNat_lt n h2, toNat_add_ofNat q j h3] at this
  omega

attribute [local irreducible] Ret in
theorem frame_open_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s) (m k : BitVec 64)
    (hm : s.locals.lookup (ofString "msg") = some (.val (.word m)))
    (hk : s.locals.lookup (ofString "kind") = some (.val (.word k))) (hk0 : k.toNat = 0)
    (hmlo : m.toNat + 176 ≤ globN s "heap_ptr") (hnb : memW s (m.toNat + 120) < 2 ^ 40) :
    Ret s (sourceFnBody Guest.Software.guestFn_frame_open) FOPost := by
  have hb : sourceFnBody Guest.Software.guestFn_frame_open =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_frame_open).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_frame_open,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  -- parent := ev
  refine Ret.dec fun pv hpv => ?_
  refine Ret.mono (Φ := FOPost) ?_ (fun v t h => h)
  generalize hS1 : setVarHOLFinite (ofString "parent") pv s = S1
  have S1c : S1.code = originalRuntimeCode := by rw [← hS1]; exact hcode
  have S1G : GuestInv S1 := by rw [← hS1]; exact guestInv_congr (s := s) rfl rfl rfl rfl hAR.1
  have S1g : S1.globals = s.globals := by rw [← hS1]; rfl
  have S1m : S1.memory = s.memory := by rw [← hS1]; rfl
  have S1msg : S1.locals.lookup (ofString "msg") = some (.val (.word m)) := by
    rw [← hS1]; rw [setVar_lookup_ne _ _ _ _ (by decide)]; exact hm
  have S1k : S1.locals.lookup (ofString "kind") = some (.val (.word k)) := by
    rw [← hS1]; rw [setVar_lookup_ne _ _ _ _ (by decide)]; exact hk
  have S1p : S1.locals.lookup (ofString "parent") = some pv := by
    rw [← hS1]; exact setVar_lookup_eq _ _ _
  obtain ⟨evw, hevw, -⟩ := glob_of_words s hAR.2 "ev" (by decide)
  rw [ev_glob, hevw] at hpv
  cases hpv
  clear hS1
  -- child := frame_new(msg)
  refine Ret.decCallL foPost_locIns fun vals body cal ret v post h1 h2 h3 => ?_
  have hv : vals = [.val (.word m)] := by
    obtain ⟨v1, rfl, he1⟩ := evalList1_inv _ _ h1
    rw [ev_loc, S1msg] at he1; rw [← Option.some.inj he1]
  obtain ⟨rfl, rfl⟩ := lk1 S1c lookup_frame_new m hv h2
  obtain ⟨e, rfl, hAR2, hsp2, he280, hea, h32, h40, h24⟩ := Ret.apply
    (frame_new_run (callEntryStateHOLFinite S1 _) S1c
      ⟨guestInv_callEntry _ _ S1G, arenaOK_congr (s := s) S1g hAR.2⟩ m
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by rw [show globN (callEntryStateHOLFinite S1 (HolFiniteMapExact.empty.update
            (ofString "msg", .val (.word m)))) "heap_ptr" = globN s "heap_ptr" from
            globN_congr S1g _]; exact hmlo)
      (by rw [show memW (callEntryStateHOLFinite S1 (HolFiniteMapExact.empty.update
            (ofString "msg", .val (.word m)))) (m.toNat + 120) = memW s (m.toNat + 120) from
            memW_congr S1m _]; exact hnb)) h3
  generalize hT2 : setVarHOLFinite (ofString "child") (.val (.word e))
    { post with locals := S1.locals } = T2
  have T2AR : ArenaReady T2 := by rw [← hT2]; exact arenaReady_setVar _ _ post _ hAR2
  have T2c : T2.code = originalRuntimeCode := T2AR.1.1
  have T2g : T2.globals = post.globals := by rw [← hT2]; rfl
  have T2m : T2.memory = post.memory := by rw [← hT2]; rfl
  have T2child : T2.locals.lookup (ofString "child") = some (.val (.word e)) := by
    rw [← hT2]; exact setVar_lookup_eq _ _ _
  have T2l : ∀ y, y ≠ ofString "child" → T2.locals.lookup y = S1.locals.lookup y := by
    intro y hy; rw [← hT2]; exact setVar_lookup_ne _ _ _ _ hy
  have T2sp : globN T2 "scratch_ptr" ≤ e.toNat := by rw [globN_congr T2g]; exact hsp2
  have T2fmp : memW T2 (e.toNat + 24) + 1024 = globN T2 "frame_mem_ptr" := by
    rw [memW_congr T2m, globN_congr T2g]; exact h24
  have T232 : memW T2 (e.toNat + 32) = 0 := by rw [memW_congr T2m]; exact h32
  have T240 : memW T2 (e.toNat + 40) = 1024 := by rw [memW_congr T2m]; exact h40
  clear hT2 h1 h2 h3 hv h24 h32 h40 hsp2
  -- rec := scratch_alloc(104)
  have hA := T2AR.2
  obtain ⟨sp, hsp, gsp⟩ := glob_of_words T2 hA "scratch_ptr" (by decide)
  obtain ⟨fp, hfp, gfp⟩ := glob_of_words T2 hA "frame_mem_ptr" (by decide)
  have hfs : fp.toNat ≤ sp.toNat := by have := hA.2.2.2.1; omega
  have hse : sp.toNat ≤ scratchEnd := by have := hA.2.2.2.2.1; omega
  have hss : scratchStart ≤ fp.toNat := by have := hA.2.2.1; omega
  have hsa : sp.toNat % 8 = 0 := by have := hA.2.2.2.2.2.2.2.1; omega
  have hfa : fp.toNat % 8 = 0 := by have := hA.2.2.2.2.2.2.1; omega
  apply Ret.mono (Φ := FOPost) ?_ (fun v t h => h)
  refine HtabC00Ports.decCall_scratch_alloc T2c 104 (by simp [ev, evalHOLExact]) sp fp hsp hfp ?_
  intro hc1 hc2
  refine Ret.mono (Φ := FOPost) ?_ (fun v t h => foPost_locIns v t _ h)
  obtain ⟨qa, qfp, qsp, -, qadd⟩ := hb_scratch_alloc_arith sp fp 104 hfs hsa hc1 hc2
  generalize hQ : (sp - 104) &&& ((0 : BitVec 64) - 8) = q at *
  have q104 : q.toNat + 104 ≤ e.toNat := by
    have : (104 : BitVec 64).toNat = 104 := rfl
    omega
  generalize hT3 : setVarHOLFinite (ofString "rec") (.val (.word q))
    { T2 with globals := T2.globals.update (ofString "scratch_ptr", .val (.word q)),
              clock := T2.clock - 1 } = T3
  have T3g : T3.globals = T2.globals.update (ofString "scratch_ptr", .val (.word q)) := by
    rw [← hT3]; rfl
  have T3m : T3.memory = T2.memory := by rw [← hT3]; rfl
  have T3c : T3.code = originalRuntimeCode := by rw [← hT3]; exact T2c
  have T3G : GuestInv T3 := by rw [← hT3]; exact guestInv_congr (s := T2) rfl rfl rfl rfl T2AR.1
  have T3sp : T3.globals.lookup (ofString "scratch_ptr") = some (.val (.word q)) := by
    rw [T3g]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have T3fp : T3.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)) := by
    rw [T3g]; simp [HolFiniteMapExact.lookup_update, FUPDATE]; exact hfp
  have T3rec : T3.locals.lookup (ofString "rec") = some (.val (.word q)) := by
    rw [← hT3]; exact setVar_lookup_eq _ _ _
  have T3l : ∀ y, y ≠ ofString "rec" → T3.locals.lookup y = T2.locals.lookup y := by
    intro y hy; rw [← hT3]; exact setVar_lookup_ne _ _ _ _ hy
  have T3AR : ArenaReady T3 :=
    arenaReady_of_sp_fmp T3G hA (fun k h1 h2 => by rw [T3g]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1])
      q fp T3sp T3fp hss qfp (by omega) hfa qa
  have T3fmpG : globN T3 "frame_mem_ptr" = globN T2 "frame_mem_ptr" := by
    unfold globN; rw [T3fp, hfp]
  have T3evG : T3.globals.lookup (ofString "ev") = T2.globals.lookup (ofString "ev") := by
    rw [T3g]; simp (config := {decide := true}) [HolFiniteMapExact.lookup_update, FUPDATE]
  clear hT3
  -- memzero(rec, 104)
  refine Ret.seq_call00 fun vals body cal ret v post h1 h2 h3 => ?_
  have hv : vals = [.val (.word q), .val (.word 104)] := by
    obtain ⟨v1, v2, rfl, he1, he2⟩ := evalList2_inv _ _ _ h1
    simp [ev, evalHOLExact, T3rec] at he1 he2
    rw [← he1, ← he2]; rfl
  obtain ⟨rfl, rfl⟩ := lk2 T3c (by decide) lookup_memzero q 104 hv h2
  obtain ⟨-, hfr⟩ := memzero_call_zero T3 T3c T3AR q 104 v post h3
  obtain ⟨fc, fm, -, -, -, fg, -, -, fout, -⟩ := hfr
  generalize hT4 : { post with locals := T3.locals } = T4
  have T4g : T4.globals = T3.globals := by rw [← hT4]; exact fg
  have T4c : T4.code = originalRuntimeCode := by rw [← hT4]; exact fc.trans T3c
  have T4G : GuestInv T4 := by
    rw [← hT4]; exact guestInv_congr (s := post) rfl rfl rfl rfl (guestInv_post (guestInv_callEntry _ _ T3G) h3)
  have T4l : T4.locals = T3.locals := by rw [← hT4]
  have hsz : e.toNat + 280 < 2 ^ 64 := by have := scratchEnd_lt64; omega
  have T4out : ∀ n, q.toNat + 104 ≤ n → n < 2 ^ 64 → memW T4 n = memW T3 n := by
    intro n hn1 hn2
    apply memW_of
    have ha : ¬ CellHits (BitVec.ofNat 64 n).toNat (q.toNat, 104) := by
      rw [toNat_ofNat_lt n hn2]; unfold CellHits; omega
    rw [← hT4]; exact fout _ (by simpa using ha) (by simp [CellHits])
  clear hT4 h1 h2 h3 hv fc fm fg fout
  -- stores at rec+0, +8, +16, +40
  have hqx : q.toNat + 104 < 2 ^ 64 := by omega
  have hwg : ∀ (X : PanSemStateFiniteExact 64 F) (n : String), ArenaOK X → n ∈ guestGlobalNames →
      ∀ v, ev X (.var .global (ofString n)) = some v → ∃ w, v = .val (.word w) := by
    intro X n hX hn v hv
    obtain ⟨w, hw, -⟩ := glob_of_words X hX n hn
    rw [ev_glob, hw] at hv; exact ⟨w, (Option.some.inj hv).symm⟩
  refine Ret.storeOff (by rw [T4l]; exact T3rec)
    (fun v hv => by
      refine ⟨evw, ?_⟩
      rw [ev_loc, T4l, T3l _ (by decide), T2l _ (by decide), S1p] at hv
      exact (Option.some.inj hv).symm)
    fun w5 T5 _ T5l T5g T5c T5G T5m => ?_
  refine Ret.storeOff (by rw [T5l, T4l]; exact T3rec)
    (hwg T5 "cur_cont" (arenaOK_congr (s := T3) (T5g.trans T4g) T3AR.2) (by decide))
    fun w6 T6 _ T6l T6g T6c T6G T6m => ?_
  refine Ret.storeOff (by rw [T6l, T5l, T4l]; exact T3rec)
    (fun v hv => by
      refine ⟨k, ?_⟩
      rw [ev_loc, T6l, T5l, T4l, T3l _ (by decide), T2l _ (by decide), S1k] at hv
      exact (Option.some.inj hv).symm)
    fun w7 T7 hv7 T7l T7g T7c T7G T7m => ?_
  have hw7 : w7 = k := by
    rw [ev_loc, T6l, T5l, T4l, T3l _ (by decide), T2l _ (by decide), S1k] at hv7
    simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hv7
    exact hv7.symm
  subst w7
  refine Ret.storeOff (by rw [T7l, T6l, T5l, T4l]; exact T3rec)
    (fun v hv => by
      refine ⟨m, ?_⟩
      rw [ev_loc, T7l, T6l, T5l, T4l, T3l _ (by decide), T2l _ (by decide), S1msg] at hv
      exact (Option.some.inj hv).symm)
    fun w8 T8 _ T8l T8g T8c T8G T8m => ?_
  -- ev := child; cur_cont := rec
  refine Ret.seq_assignGlobal fun ev1 hev1 _ => ?_
  rw [ev_loc, T8l, T7l, T6l, T5l, T4l, T3l _ (by decide), T2child] at hev1
  cases hev1
  refine Ret.seq_assignGlobal fun ev2 hev2 _ => ?_
  have hev2' : ev2 = .val (.word q) := by
    simp only [ev_loc, setKvarHOLFinite, setGlobalHOLFinite] at hev2
    rw [T8l, T7l, T6l, T5l, T4l, T3rec] at hev2
    exact (Option.some.inj hev2).symm
  subst hev2'
  refine Ret.ret fun _ _ => ?_
  -- final memory/global bookkeeping
  have Gall : T8.globals = T3.globals := T8g.trans (T7g.trans (T6g.trans (T5g.trans T4g)))
  have hmT8 : ∀ n, q.toNat + 104 ≤ n → n < 2 ^ 64 → memW T8 n = memW T2 n := by
    intro n h1 h2
    rw [memW_upd_off 40 n T8m (by omega) h2 (by omega), memW_upd_off 16 n T7m (by omega) h2 (by omega),
      memW_upd_off 8 n T6m (by omega) h2 (by omega), memW_upd_off 0 n T5m (by omega) h2 (by omega),
      T4out n h1 h2, memW_congr T3m]
  have h16 : memW T8 (q.toNat + 16) = 0 := by
    rw [memW_upd_off 40 _ T8m (by omega) (by omega) (by omega), memW_upd_eq q 16 k T7m, hk0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show memW T8 (globN _ "cur_cont" + 16) = 0
    have : globN (emptyLocalsHOLFinite (setKvarHOLFinite .global (ofString "cur_cont") (.val (.word q))
        (setKvarHOLFinite .global (ofString "ev") (.val (.word e)) T8))) "cur_cont" = q.toNat := by
      unfold globN; simp [emptyLocalsHOLFinite, setKvarHOLFinite, setGlobalHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE]
    rw [this]; exact h16
  all_goals
    have hE : globN (emptyLocalsHOLFinite (setKvarHOLFinite .global (ofString "cur_cont") (.val (.word q))
        (setKvarHOLFinite .global (ofString "ev") (.val (.word e)) T8))) "ev" = e.toNat := by
      unfold globN; simp (config := {decide := true}) [emptyLocalsHOLFinite, setKvarHOLFinite,
        setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hF : globN (emptyLocalsHOLFinite (setKvarHOLFinite .global (ofString "cur_cont") (.val (.word q))
        (setKvarHOLFinite .global (ofString "ev") (.val (.word e)) T8))) "frame_mem_ptr" =
        globN T2 "frame_mem_ptr" := by
      rw [← T3fmpG]; unfold globN
      simp (config := {decide := true}) [emptyLocalsHOLFinite, setKvarHOLFinite,
        setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Gall]
    have hM : ∀ n, memW (emptyLocalsHOLFinite (setKvarHOLFinite .global (ofString "cur_cont")
        (.val (.word q)) (setKvarHOLFinite .global (ofString "ev") (.val (.word e)) T8))) n =
        memW T8 n := fun n => rfl
    rw [hE, hM]
    try rw [hF]
  · rw [hmT8 _ (by omega) (by omega)]; exact T232
  · rw [hmT8 _ (by omega) (by omega)]; exact T240
  · rw [hmT8 _ (by omega) (by omega)]; exact T2fmp

theorem fo_param_words_two {F : Type} (s : PanSemStateFiniteExact 64 F)
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

/-- `FrameOpenMemSpecB` discharged: the bounded frame-memory effect of `frame_open(msg, 0)`. -/
theorem frameOpenMemSpecB : FrameOpenMemSpecB := by
  refine ⟨_, _, _, lookup_frame_open, fun s hcode hP hex hnt hr => ?_⟩
  obtain ⟨⟨hMR, hkind⟩, hnb⟩ := hP
  obtain ⟨w1, hw1⟩ := hex
  obtain ⟨⟨m, hm⟩, ⟨k, hk⟩⟩ := fo_param_words_two s (p1 := "msg") (p2 := "kind") (by decide)
    lookup_frame_open ⟨w1, by rw [← hcode] at hw1 ⊢; exact hw1⟩
  have hlm : locN s "msg" = m.toNat := by unfold locN; rw [hm]
  have hlk : locN s "kind" = k.toNat := by unfold locN; rw [hk]
  have hAR0 := hMR.1
  obtain ⟨-, S, -, -, -, hIns, -⟩ := hMR
  have hmlo : m.toNat + 176 ≤ globN s "heap_ptr" := by have := hIns.2; rw [hlm] at this; exact this
  rw [hlm] at hnb
  obtain ⟨v, hv⟩ := frame_open_resumes_returned s hcode hw1 hr
  have := frame_open_run s hcode hAR0 m k hm hk (by rw [← hlk]; exact hkind) hmlo hnb v hv
  exact this

/-- `frame_open_aligned_B` with the bounded frame-memory effect discharged (`frameOpenMemSpecB`):
only the unaligned `fk_frame_open` contract remains. -/
theorem frame_open_aligned_B' (hk : KeepsOn FrameOpenReady EvmMsgReady (ofString "frame_open")) :
    KeepsOn FrameOpenReadyB (fun s => EvmMsgReady s ∧ HeadMemChainWF s) (ofString "frame_open") :=
  frame_open_aligned_B hk frameOpenMemSpecB

/-- Entry establishment at `frame_open`, unconditional. -/
theorem frame_open_headMemChainWF_B' :
    KeepsOn FrameOpenReadyB HeadMemChainWF (ofString "frame_open") :=
  frame_open_headMemChainWF_B frameOpenMemSpecB

end FrameOpenRun

section FinishLeaves2
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

theorem lookup_incorporate_child_on_error :
    originalRuntimeCode.lookup (ofString "incorporate_child_on_error") =
      some ([(ofString "child", .one)],
        sourceFnBody Guest.Software.guestFn_incorporate_child_on_error, .one) :=
  lookup_of_guestAst_getElem 591 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_incorporate_child_on_error) rfl

theorem ev_globOff {F : Type} (s : PanSemStateFiniteExact 64 F) (g : MlS) (a k : BitVec 64)
    (h : s.globals.lookup g = some (.val (.word a))) :
    ev s (.op .add [.var .global g, .const k]) = some (.val (.word (a + k))) := by
  simp [ev, evalHOLExact, evalListHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord, h]

/-- A store at `global g + k` of a sum: memory becomes an `updW` at `a + k`. -/
theorem Ret.storeGlobOff {F : Type} {S : PanSemStateFiniteExact 64 F} {g : MlS} {a k : BitVec 64}
    {args : List (ExpHOL 64)} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hg : S.globals.lookup g = some (.val (.word a)))
    (hb : ∀ (w : BitVec 64), Ret { S with memory := updW S.memory (a + k) w } b Φ) :
    Ret S (.seq (.store (.op .add [.var .global g, .const k]) (.op .add args)) b) Φ :=
  Ret.seq_storeWv _ (ev_globOff S g a k hg) (fun v hv => ev_op_word S _ _ v hv)
    (fun w _ _ => hb w)

attribute [local irreducible] Ret in
/-- `incorporate_child_on_error(child)` writes only the words `ev+64`, `ev+72`, `ev+184`. -/
theorem incorporate_child_on_error_run {F : Type} (s : PanSemStateFiniteExact 64 F) (e : BitVec 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e))) :
    Ret s (sourceFnBody Guest.Software.guestFn_incorporate_child_on_error) (fun _ post =>
      post.globals = s.globals ∧ (∃ w1 w2 w3 : BitVec 64, post.memory =
        updW (updW (updW s.memory (e + 64) w1) (e + 72) w2) (e + 184) w3) ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_incorporate_child_on_error =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_incorporate_child_on_error).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_incorporate_child_on_error,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.storeGlobOff he fun w1 => ?_
  refine Ret.storeGlobOff he fun w2 => ?_
  refine Ret.storeGlobOff he fun w3 => ?_
  refine Ret.ret fun _ _ => ?_
  exact ⟨rfl, ⟨w1, w2, w3, rfl⟩, rfl, rfl⟩

end FinishLeaves2

section FinishLeaves3
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

theorem fl_lookup_min :
    originalRuntimeCode.lookup (ofString "min") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_min, .one) :=
  lookup_of_guestAst_getElem 31 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_min) rfl

theorem fl_lookup_credit_state_gas_refund :
    originalRuntimeCode.lookup (ofString "credit_state_gas_refund") =
      some ([(ofString "amount", .one)],
        sourceFnBody Guest.Software.guestFn_credit_state_gas_refund, .one) :=
  lookup_of_guestAst_getElem 450 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_credit_state_gas_refund) rfl

theorem min_locOnly : locOnly (sourceFnBody Guest.Software.guestFn_min) = true := by
  decide

/-- A store at `global g + k` of any operator expression. -/
theorem Ret.storeGlobOp {F : Type} {S : PanSemStateFiniteExact 64 F} {g : MlS} {a k : BitVec 64}
    {o : BinOp} {args : List (ExpHOL 64)} {b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hg : S.globals.lookup g = some (.val (.word a)))
    (hb : ∀ (w : BitVec 64), Ret { S with memory := updW S.memory (a + k) w } b Φ) :
    Ret S (.seq (.store (.op .add [.var .global g, .const k]) (.op o args)) b) Φ :=
  Ret.seq_storeWv _ (ev_globOff S g a k hg) (fun v hv => ev_op_word S _ _ v hv)
    (fun w _ _ => hb w)

/-- A `decCall` of `min`: the continuation runs from a state with the caller's globals, memory,
code and domain. -/
theorem Ret.decCall_min {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (hk : ∀ (t : PanSemStateFiniteExact 64 F), t.globals = s.globals → t.memory = s.memory →
      t.code = s.code → t.memaddrs = s.memaddrs →
      Ret t cont (fun w u =>
        Φ w { u with locals := HolFiniteMapExact.resVarEq u.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x sh (ofString "min") args cont) Φ := by
  refine Ret.decCall_gen fun values body callee ret v post _ h2 h3 => ?_
  have hlk : s.code.lookup (ofString "min") = some ([(ofString "a", .one), (ofString "b", .one)],
      sourceFnBody Guest.Software.guestFn_min, .one) := by rw [hcode]; exact fl_lookup_min
  have hb := InitECandidate.Solver.PanRunBounded.lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ _ _ _ _ _ hlk h2
  subst hb
  have hlf := locFrame_eval _ min_locOnly (callEntryStateHOLFinite s callee)
  rw [h3] at hlf
  unfold LocFrame at hlf
  simp only at hlf
  have hpg : post.globals = s.globals := (congrArg PanSemStateFiniteExact.globals hlf).trans rfl
  have hpm : post.memory = s.memory := (congrArg PanSemStateFiniteExact.memory hlf).trans rfl
  have hpc : post.code = s.code := (congrArg PanSemStateFiniteExact.code hlf).trans rfl
  have hpd : post.memaddrs = s.memaddrs := (congrArg PanSemStateFiniteExact.memaddrs hlf).trans rfl
  exact hk _ (by simp [setVarHOLFinite, hpg]) (by simp [setVarHOLFinite, hpm])
    (by simp [setVarHOLFinite, hpc]) (by simp [setVarHOLFinite, hpd])

attribute [local irreducible] Ret in
/-- `credit_state_gas_refund(amount)` writes only the words `ev+64`, `ev+192`, `ev+72`. -/
theorem credit_state_gas_refund_run {F : Type} (s : PanSemStateFiniteExact 64 F) (e : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e))) :
    Ret s (sourceFnBody Guest.Software.guestFn_credit_state_gas_refund) (fun _ post =>
      post.globals = s.globals ∧ (∃ w1 w2 w3 : BitVec 64, post.memory =
        updW (updW (updW s.memory (e + 64) w1) (e + 192) w2) (e + 72) w3) ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_credit_state_gas_refund =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_credit_state_gas_refund).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_credit_state_gas_refund,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.dec fun sv _ => ?_
  refine Ret.decCall_min (by simpa [setVarHOLFinite] using hcode) fun t hg hm hc hd => ?_
  have hgs : (setVarHOLFinite (ofString "spilled") sv s).globals = s.globals := rfl
  have hms : (setVarHOLFinite (ofString "spilled") sv s).memory = s.memory := rfl
  have hcs : (setVarHOLFinite (ofString "spilled") sv s).code = s.code := rfl
  have hds : (setVarHOLFinite (ofString "spilled") sv s).memaddrs = s.memaddrs := rfl
  have he' : t.globals.lookup (ofString "ev") = some (.val (.word e)) := by rw [hg, hgs]; exact he
  refine Ret.storeGlobOp he' fun w1 => ?_
  refine Ret.storeGlobOp he' fun w2 => ?_
  refine Ret.storeGlobOp he' fun w3 => ?_
  refine Ret.ret fun _ _ => ?_
  refine ⟨?_, ⟨w1, w2, w3, ?_⟩, ?_, ?_⟩
  · simp only [emptyLocalsHOLFinite]; rw [hg, hgs]
  · simp only [emptyLocalsHOLFinite]; rw [hm, hms]; rfl
  · simp only [emptyLocalsHOLFinite]; rw [hc, hcs]
  · simp only [emptyLocalsHOLFinite]; rw [hd, hds]

end FinishLeaves3

section SetRetdataRun
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

theorem srd_eval_seq_assoc {F : Type} (s : PanSemStateFiniteExact 64 F) (a b c : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq (.seq a b) c) = evaluateHOLFiniteState s (.seq a (.seq b c)) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s a with ⟨r, t⟩
  cases r with
  | none =>
    dsimp only
  | some _ => rfl

theorem Ret.seq_assoc {F : Type} {s : PanSemStateFiniteExact 64 F} {a b c : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : Ret s (.seq a (.seq b c)) Φ) : Ret s (.seq (.seq a b) c) Φ := by
  intro v hv
  rw [srd_eval_seq_assoc] at hv ⊢
  exact h v hv

theorem ev_load_glob {F : Type} (S : PanSemStateFiniteExact 64 F) (g : MlS) (a k : BitVec 64)
    (hg : S.globals.lookup g = some (.val (.word a))) (v : ValueHOL 64)
    (h : ev S (.load .one (.op .add [.var .global g, .const k])) = some v) :
    v = .val (S.memory (a + k)) := by
  have hd := ev_globOff S g a k hg
  simp only [ev] at h hd
  rw [evalHOLExact] at h
  simp only [hd, memLoadHOLExact] at h
  split at h
  · split at h
    · exact (Option.some.inj h).symm
    · cases h
  · cases h

/-- The `set_retdata` tail: `memcpy(dst, p, n); ev+152 := n; return 0`. -/
theorem srd_tail {F : Type} (X : PanSemStateFiniteExact 64 F) (d pv nw e : BitVec 64)
    (hA : ArenaReady X)
    (hd : X.locals.lookup (ofString "dst") = some (.val (.word d)))
    (hp : X.locals.lookup (ofString "p") = some (.val (.word pv)))
    (hn : X.locals.lookup (ofString "n") = some (.val (.word nw)))
    (he : X.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hd_nw : d.toNat + nw.toNat < 2 ^ 64) (hn_small : nw.toNat + 32 < 2 ^ 63) :
    Ret X (.seq (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "dst"), .var .local (ofString "p"), .var .local (ofString "n")])
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const 152]) (.var .local (ofString "n")))
        (.return (.const 0))))
      (fun _ post => post.code = X.code ∧ post.memaddrs = X.memaddrs ∧ ArenaReady post ∧
        post.globals = X.globals ∧
        ∀ a : BitVec 64, ¬ CellHits a.toNat (d.toNat, nw.toNat) → a ≠ e + 152 →
          post.memory a = X.memory a) := by
  intro v0 hv0
  refine (SoloHtabSet.Ret.seq_memcpy_frame (cont := .seq (.store (.op .add [.var .global (ofString "ev"), .const 152]) (.var .local (ofString "n")))
        (.return (.const 0))) (Φ := fun _ post => post.code = X.code ∧ post.memaddrs = X.memaddrs ∧ ArenaReady post ∧
        post.globals = X.globals ∧
        ∀ a : BitVec 64, ¬ CellHits a.toNat (d.toNat, nw.toNat) → a ≠ e + 152 →
          post.memory a = X.memory a) hA d pv nw hd_nw hn_small
    (by simp [evalHOLExact, hd]) (by simp [evalHOLExact, hp])
    (by simp [evalHOLExact, hn]) ?_ : SoloHtabSet.Ret _ _ _) v0 hv0
  intro s' hA' hmc hloc
  have key : Ret s' (.seq (.store (.op .add [.var .global (ofString "ev"), .const 152])
      (.var .local (ofString "n"))) (.return (.const 0)))
      (fun _ post => post.code = X.code ∧ post.memaddrs = X.memaddrs ∧ ArenaReady post ∧
        post.globals = X.globals ∧
        ∀ a : BitVec 64, ¬ CellHits a.toNat (d.toNat, nw.toNat) → a ≠ e + 152 →
          post.memory a = X.memory a) := by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hmc
    refine Ret.seq_storeWv _ (ev_globOff s' _ e 152 (by rw [c6]; exact he))
      (fun v hv => ⟨nw, by simpa [ev, evalHOLExact, hloc, hn] using hv.symm⟩) fun w _ _ => ?_
    refine Ret.ret fun _ _ => ?_
    refine ⟨c1, c2, ⟨guestInv_congr (s := s') rfl rfl rfl rfl hA'.1, arenaOK_congr (s := s') rfl hA'.2⟩,
      c6, ?_⟩
    intro a ha hne
    simp only [emptyLocalsHOLFinite]
    rw [updW_ne _ _ _ _ hne]
    exact c7 a (by simpa using ha) (by simp [CellHits])
  exact key

/-- Footprint of `set_retdata(p, n)` from `s` with `ev = e`: only the copy window `(d, n)` and the
words `e+144/152/216` change, and `d` is the old buffer (when `n ≤ cap`) or a fresh heap block. -/
def SrdPost {F : Type} (s : PanSemStateFiniteExact 64 F) (e nw : BitVec 64)
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ ArenaReady post ∧
  (∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = s.globals.lookup k) ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
  ∃ d : BitVec 64,
    (nw = 0 ∨ (s.memory (e + 144) = .word d ∧ ∃ cap : BitVec 64, s.memory (e + 216) = .word cap ∧
        nw.toNat ≤ cap.toNat) ∨
      (globN s "heap_ptr" ≤ d.toNat ∧ d.toNat + nw.toNat ≤ globN post "heap_ptr")) ∧
    ∀ a : BitVec 64, ¬ CellHits a.toNat (d.toNat, nw.toNat) → a ≠ e + 144 → a ≠ e + 152 →
      a ≠ e + 216 → post.memory a = s.memory a

theorem srdPost_locals {F : Type} {s post : PanSemStateFiniteExact 64 F} {e nw : BitVec 64}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (h : SrdPost s e nw post) :
    SrdPost s e nw { post with locals := L } :=
  ⟨h.1, h.2.1, arenaReady_locals _ _ h.2.2.1, h.2.2.2⟩

theorem arenaReady_mem {F : Type} (t : PanSemStateFiniteExact 64 F) (m : BitVec 64 → HolWordLab 64)
    (h : ArenaReady t) : ArenaReady { t with memory := m } :=
  ⟨guestInv_congr (s := t) rfl rfl rfl rfl h.1, arenaOK_congr (s := t) rfl h.2⟩

theorem srd_cmp {F : Type} (t : PanSemStateFiniteExact 64 F) (op : Cmp) (x y : MlS) (a b w : BitVec 64)
    (hx : t.locals.lookup x = some (.val (.word a))) (hy : t.locals.lookup y = some (.val (.word b)))
    (h : ev t (.cmp op (.var .local x) (.var .local y)) = some (.val (.word w))) :
    w = if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b then 1 else 0 := by
  obtain ⟨a', b', ha, hb, hcw⟩ := evalAt_cmp t op _ _ w h
  simp [evalAt, evalHOLExact, hx, hy] at ha hb
  subst ha hb; exact hcw

theorem srd_cmp0 {F : Type} (t : PanSemStateFiniteExact 64 F) (op : Cmp) (x : MlS) (a w : BitVec 64)
    (hx : t.locals.lookup x = some (.val (.word a)))
    (h : ev t (.cmp op (.var .local x) (.const 0)) = some (.val (.word w))) :
    w = if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a 0 then 1 else 0 := by
  obtain ⟨a', b', ha, hb, hcw⟩ := evalAt_cmp t op _ _ w h
  simp [evalAt, evalHOLExact, hx] at ha hb
  subst ha hb; exact hcw

/-- `x := alloc(n + 8); cont`, with the continuation state given explicitly. -/
theorem srd_alloc {F : Type} {X : PanSemStateFiniteExact 64 F} {x : MlS} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hA : ArenaReady X) (nw : BitVec 64)
    (hn : X.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hk : ∀ hp q : BitVec 64, hp.toNat = globN X "heap_ptr" →
      hp.toNat + (nw + 8).toNat ≤ q.toNat → q.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat →
      q.toNat % 8 = 0 →
      Ret (setVarHOLFinite x (.val (.word hp))
        { X with
          globals := X.globals.update (ofString "heap_ptr", .val (.word q))
          clock := X.clock - 1 }) cont Φ) :
    Ret X (.seq (.call (some (some (.local, x), none)) (ofString "alloc")
      [.op .add [.var .local (ofString "n"), .const 8]]) cont) Φ := by
  obtain ⟨hp, hhp_g, hhp_nat, _, hhp_hi, _⟩ := SoloHtabSet.arenaReady_heap_word hA
  have hl := pan_one_word_lookup X.code.lookup (ofString "alloc") (ofString "n") _ (nw + 8)
    (by rw [hA.1.code]; exact SoloHtabSet.lookup_alloc_fn)
  generalize hq : (hp + ((nw + 8) + 7)) &&& ((0 : BitVec 64) - 8) = q
  let E := callEntryStateHOLFinite X (HolFiniteMapExact.empty.update (ofString "n", .val (.word (nw + 8))))
  refine Ret.seq_callAssign_spec [.val (.word (nw + 8))] _ _ _
    (by rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hn, wordOpHOL, wordOp, valueIsWord, valueWord]) hl
    (fun v post =>
      v = .val (.word hp) ∧ hp.toNat + (nw + 8).toNat ≤ q.toNat ∧
      q.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat ∧ q.toNat % 8 = 0 ∧
      post = { E with
        globals := X.globals.update (ofString "heap_ptr", .val (.word q))
        locals := post.locals })
    (fun v hv => by
      have := SoloHtabSet.alloc_body_run E hp (nw + 8) hA.1.code hhp_hi hhp_g
        (by simp [E, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) v hv
      rw [hq] at this; exact this) ?_
  rintro v post ⟨rfl, h1, h2, h3, hpost⟩
  have : { post with locals := X.locals } =
      { X with
        globals := X.globals.update (ofString "heap_ptr", .val (.word q))
        clock := X.clock - 1 } := by
    rw [hpost]; rfl
  rw [this]
  exact hk hp _ hhp_nat h1 h2 h3

attribute [local irreducible] Ret in
/-- `set_retdata(p, n)`: memory changes only in the copy window and at `ev+144/152/216`. -/
theorem set_retdata_run {F : Type} (s : PanSemStateFiniteExact 64 F) (e pv nw : BitVec 64)
    (hA : ArenaReady s) (hcode : s.code = originalRuntimeCode)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pv)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hn_small : nw.toNat + 32 < 2 ^ 63)
    (hbuf : ∀ d0 cap : BitVec 64, s.memory (e + 144) = .word d0 → s.memory (e + 216) = .word cap →
      nw.toNat ≤ cap.toNat → d0.toNat + nw.toNat < 2 ^ 64) :
    Ret s (sourceFnBody Guest.Software.guestFn_set_retdata) (fun _ post => SrdPost s e nw post) := by
  have hb : sourceFnBody Guest.Software.guestFn_set_retdata =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_set_retdata).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_set_retdata,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.seq_ite fun w hw => ⟨fun hnz => ?_, fun hz => ?_⟩
  · -- `n = 0`
    have hw' := srd_cmp0 s .equal _ nw w hn hw
    have hn0 : nw = 0 := by
      by_contra hne
      apply hnz; rw [hw']
      simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      simp
      exact hne
    obtain ⟨ee, hee, _⟩ := glob_of_words s hA.2 "evm_empty" (by decide)
    refine Ret.seq_assoc ?_
    refine Ret.seq_storeWv _ (ev_globOff s _ e 144 he)
      (fun v hv => ⟨ee, by simpa [ev, evalHOLExact, hee] using hv.symm⟩) fun w1 _ _ => ?_
    refine Ret.seq_assoc ?_
    refine Ret.seq_storeWv _ (ev_globOff _ _ e 152 he)
      (fun v hv => ⟨0, by simpa [ev, evalHOLExact] using hv.symm⟩) fun w2 _ _ => ?_
    refine Ret.seq_assoc ?_
    refine Ret.seq_storeWv _ (ev_globOff _ _ e 216 he)
      (fun v hv => ⟨0, by simpa [ev, evalHOLExact] using hv.symm⟩) fun w3 _ _ => ?_
    refine Ret.seq_return fun _ _ => ?_
    simp only [emptyLocalsHOLFinite]
    refine ⟨rfl, rfl, ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, arenaOK_congr (s := s) rfl hA.2⟩,
      fun _ _ => rfl, le_refl _, 0, Or.inl hn0, ?_⟩
    intro a _ h1 h2 h3
    show updW (updW (updW s.memory (e + 144) w1) (e + 152) w2) (e + 216) w3 a = _
    rw [updW_ne _ _ _ _ h3, updW_ne _ _ _ _ h2, updW_ne _ _ _ _ h1]
  · -- `n ≠ 0`
    have hw' := srd_cmp0 s .equal _ nw w hn hw
    have hnz : nw ≠ 0 := by
      intro h0; subst h0
      rw [hw'] at hz
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hz
    refine Ret.seq_skip ?_
    refine Ret.dec fun v1 hv1 => ?_
    have hv1' := ev_load_glob s _ e 216 he v1 hv1
    subst hv1'
    rcases hcapm : s.memory (e + 216) with ⟨capw⟩
    let S1 := setVarHOLFinite (ofString "cap") (.val (.word capw)) s
    refine Ret.mono (Φ := fun _ t => SrdPost s e nw t) ?_
      (fun _ t h => srdPost_locals _ h)
    refine Ret.dec fun v2 hv2 => ?_
    have hv2' := ev_load_glob S1 _ e 144 (by simpa [S1, setVarHOLFinite] using he) v2 hv2
    subst hv2'
    rcases hdm : S1.memory (e + 144) with ⟨d0⟩
    have hdm0 : s.memory (e + 144) = .word d0 := hdm
    refine Ret.mono (Φ := fun _ t => SrdPost s e nw t) ?_
      (fun _ t h => srdPost_locals _ h)
    let S2 := setVarHOLFinite (ofString "dst") (.val (.word d0)) S1
    have hS2c : S2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
      simp (config := {decide := true}) [S2, S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hS2n : S2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp (config := {decide := true}) [S2, S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn]
    have hS2p : S2.locals.lookup (ofString "p") = some (.val (.word pv)) := by
      simp (config := {decide := true}) [S2, S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp]
    have hS2e : S2.globals.lookup (ofString "ev") = some (.val (.word e)) := he
    have hS2A : ArenaReady S2 := arenaReady_locals s _ hA
    show Ret S2 _ _
    refine Ret.seq_ite fun cw hcw => ⟨fun hcnz => ?_, fun hcz => ?_⟩
    · -- `cap < n`: reallocate
      refine Ret.seq_assoc ?_
      refine srd_alloc hS2A nw hS2n fun hp q hhp h1 h2 h3 => ?_
      have hn8 : (nw + 8).toNat = nw.toNat + 8 := by
        rw [BitVec.toNat_add]; simp; omega
      have hS2h : globN S2 "heap_ptr" = globN s "heap_ptr" := rfl
      have hhpq : globN s "heap_ptr" ≤ q.toNat := by omega
      obtain ⟨hAq, hgq, hkeep⟩ := SoloHtabSet.arenaReady_upd_heap hA hhpq h2 h3
      refine Ret.seq_assoc ?_
      refine Ret.seq_storeWv _ (ev_globOff _ _ e 144 (by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]; exact he))
        (fun v hv => ⟨hp, by simpa (config := {decide := true}) [ev, evalHOLExact, setVarHOLFinite,
          HolFiniteMapExact.lookup_update, FUPDATE] using hv.symm⟩) fun w1 hw1 _ => ?_
      refine Ret.seq_storeWv _ (ev_globOff _ _ e 216 (by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]; exact he))
        (fun v hv => ⟨nw, by simpa (config := {decide := true}) [ev, evalHOLExact, setVarHOLFinite,
          HolFiniteMapExact.lookup_update, FUPDATE, hS2n] using hv.symm⟩) fun w2 hw2 _ => ?_
      have hw1' : w1 = hp := by
        simpa (config := {decide := true}) [ev, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hw1.symm
      have hw2' : w2 = nw := by
        simpa (config := {decide := true}) [ev, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2n]
          using hw2.symm
      subst w1 w2
      refine Ret.mono (srd_tail _ hp pv nw e ?_ ?_ ?_ ?_ ?_ ?_ hn_small) ?_
      · exact ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, arenaOK_congr rfl hAq.2⟩
      · simp (config := {decide := true}) [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · simp (config := {decide := true}) [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2p]
      · simp (config := {decide := true}) [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2n]
      · simp [HolFiniteMapExact.lookup_update, FUPDATE]; exact he
      · have : q.toNat < 2 ^ 64 := q.isLt
        omega
      · rintro _ post ⟨pc, pd, pA, pg, pm⟩
        refine ⟨pc, pd, pA, fun k hk => ?_, ?_, hp, Or.inr (Or.inr ⟨?_, ?_⟩), ?_⟩
        · rw [pg]; exact (hkeep k (by simpa using hk)).symm
        · have : globN post "heap_ptr" = q.toNat := by
            unfold globN; rw [pg]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          omega
        · omega
        · have : globN post "heap_ptr" = q.toNat := by
            unfold globN; rw [pg]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          omega
        · intro a ha h144 h152 h216
          rw [pm a ha h152]
          show updW (updW s.memory (e + 144) hp) (e + 216) nw a = _
          rw [updW_ne _ _ _ _ h216, updW_ne _ _ _ _ h144]
    · -- `n ≤ cap`: reuse the buffer
      have hcw' := srd_cmp S2 .lower _ _ capw nw cw hS2c hS2n hcw
      have hle : nw.toNat ≤ capw.toNat := by
        by_contra hlt
        rw [hcw'] at hcz
        simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at hcz
        split at hcz
        · exact absurd hcz (by decide)
        · rename_i hdc
          simp at hdc
          omega
      refine Ret.seq_skip ?_
      refine Ret.mono (srd_tail S2 d0 pv nw e hS2A
        (by simp [S2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        hS2p hS2n hS2e (hbuf d0 capw hdm0 hcapm hle) hn_small) ?_
      rintro _ post ⟨pc, pd, pA, pg, pm⟩
      refine ⟨pc, pd, pA, fun k _ => by rw [pg]; rfl, by unfold globN; rw [pg]; rfl, d0,
        Or.inr (Or.inl ⟨hdm0, capw, hcapm, hle⟩), ?_⟩
      intro a ha _ h152 _
      exact pm a ha h152

end SetRetdataRun

section StackPushRun
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

/-- Four consecutive word updates at `a, a+8, a+16, a+24`. -/
def updW4 (m : BitVec 64 → HolWordLab 64) (a w0 w1 w2 w3 : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  updW (updW (updW (updW m a w0) (a + 8) w1) (a + 8 + 8) w2) (a + 8 + 8 + 8) w3

/-- A 4-word struct store followed by the rest. -/
theorem Ret.seq_store4 {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a w0 w1 w2 w3 : BitVec 64) (hd : ev s d = some (.val (.word a)))
    (he : ev s e = some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hb : Ret { s with memory := updW4 s.memory a w0 w1 w2 w3 } b Φ) :
    Ret s (.seq (.store d e) b) Φ := by
  apply Ret.seq_store
  intro a' val m hd' he' hm
  rw [hd] at hd'
  simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hd'
  subst hd'
  rw [he] at he'
  cases he'
  have hbw : panBytesInWord 64 = 8#64 := rfl
  simp only [flattenHOL, List.map, List.flatten, List.flatMap, List.append, panMemStoresHOL,
    panMemStoreHOL, hbw] at hm
  split_ifs at hm <;> simp only [Option.some.injEq, reduceCtorEq] at hm
  subst hm
  exact hb

theorem memLoad_one_word (a : BitVec 64) (dom : BitVec 64 → Prop) (m : BitVec 64 → HolWordLab 64)
    (ctx : StructContextHOLM) (w : BitVec 64) (hd : dom a) (hm : m a = .word w) :
    ∀ inst : DecidablePred dom, @memLoadHOLExact 64 _ .one a dom inst m ctx = some (.val (.word w)) := by
  intro inst
  unfold memLoadHOLExact; rw [if_pos hd, hm]

theorem ev_stkslot {F : Type} (t : PanSemStateFiniteExact 64 F) (e stk sp : BitVec 64)
    (he : t.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hsp : t.locals.lookup (ofString "sp") = some (.val (.word sp)))
    (hd : t.memaddrs (e + 8)) (hm : t.memory (e + 8) = .word stk) :
    ev t (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 8]),
      .panop .mul [.var .local (ofString "sp"), .const 32]]) = some (.val (.word (stk + sp * 32))) := by
  have hd' := ev_globOff t _ e 8 he
  have hml := memLoad_one_word (e + 8) t.memaddrs t.memory t.structs stk hd hm
    (fun a => Classical.propDecidable (t.memaddrs a))
  have hld : ev t (.load .one (.op .add [.var .global (ofString "ev"), .const 8])) =
      some (.val (.word stk)) := by
    simp only [ev] at hd' ⊢
    rw [evalHOLExact]
    simp only [hd']
    exact hml
  have hmul : ev t (.panop .mul [.var .local (ofString "sp"), .const 32]) =
      some (.val (.word (sp * 32))) := by
    simp [ev, evalHOLExact, evalListHOLExact, hsp, panOpHOL, valueIsWord, valueWord]
  simp only [ev] at hld hmul ⊢
  rw [evalHOLExact, evalListHOLExact, hld, evalListHOLExact, hmul, evalListHOLExact]
  simp [wordOpHOL, wordOp, valueIsWord, valueWord]

attribute [local irreducible] Ret in
/-- `stack_push(v)` on a frame with room (`sp + 1 ≤ cap ≤ 1024`): writes the four words of `v`
at `stk + 32*sp` and `sp + 1` at `ev+16`; nothing else changes. -/
theorem stack_push_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e sp cap stk w0 w1 w2 w3 : BitVec 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hv : s.locals.lookup (ofString "v") =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hsp : s.memory (e + 16) = .word sp) (hcap : s.memory (e + 232) = .word cap)
    (hstk : s.memory (e + 8) = .word stk) (hd8 : s.memaddrs (e + 8))
    (hroom : sp.toNat + 1 ≤ cap.toNat) (hcap_le : cap.toNat ≤ 1024) :
    Ret s (sourceFnBody Guest.Software.guestFn_stack_push)
      (fun _ post => post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
        post.shMemaddrs = s.shMemaddrs ∧ post.baseAddr = s.baseAddr ∧ post.be = s.be ∧
        post.globals = s.globals ∧
        post.memory = updW (updW4 s.memory (stk + sp * 32) w0 w1 w2 w3) (e + 16) (sp + 1)) := by
  have hb : sourceFnBody Guest.Software.guestFn_stack_push =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_stack_push).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_stack_push,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.dec fun v1 hv1 => ?_
  have h1 := ev_load_glob s _ e 16 he v1 hv1
  rw [hsp] at h1; subst h1
  refine Ret.dec fun v2 hv2 => ?_
  have h2 := ev_load_glob _ _ e 232 he v2 hv2
  rw [hcap] at h2
  subst h2
  refine Ret.seq_ite fun c hc => ⟨fun hcz => ?_, fun _ => ?_⟩
  · exfalso
    obtain ⟨a, b, ha, hb', hcw⟩ := evalAt_cmp _ _ _ _ c hc
    simp (config := {decide := true}) [evalAt, evalHOLExact, setVarHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE] at ha hb'
    subst ha hb'
    apply hcz; rw [hcw]
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    omega
  refine Ret.seq_skip ?_
  refine Ret.seq_ite fun c hc => ⟨fun hcz => ?_, fun _ => ?_⟩
  · exfalso
    obtain ⟨a, b, ha, hb', hcw⟩ := evalAt_cmp _ _ _ _ c hc
    simp (config := {decide := true}) [evalAt, evalHOLExact, setVarHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE] at ha hb'
    subst ha hb'
    apply hcz; rw [hcw]
    have : sp ≠ 1024#64 := by
      intro h; subst h; simp at hroom; omega
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  refine Ret.seq_skip ?_
  refine Ret.seq_store4 (stk + sp * 32) w0 w1 w2 w3 ?_ ?_ ?_
  · exact ev_stkslot _ e stk sp he (by simpa (config := {decide := true}) [setVarHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE]) hd8 hstk
  · simp (config := {decide := true}) [ev, evalHOLExact, setVarHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE, hv]
  refine Ret.seq_storeWv (e + 16) (ev_globOff _ _ e 16 he)
    (fun v hv => ⟨sp + 1, by simpa (config := {decide := true}) [ev, evalHOLExact,
      evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, wordOpHOL,
      wordOp, valueIsWord, valueWord] using hv.symm⟩) fun w hw _ => ?_
  have hw' : w = sp + 1 := by
    simpa (config := {decide := true}) [ev, evalHOLExact, evalListHOLExact, setVarHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE, wordOpHOL, wordOp, valueIsWord, valueWord] using hw.symm
  subst hw'
  refine Ret.ret fun _ _ => ?_
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end StackPushRun

section FinishLeaves4
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

/-- A store at `global g + k` of any word-valued expression. -/
theorem Ret.storeGlobAny {F : Type} {S : PanSemStateFiniteExact 64 F} {g : MlS} {a k : BitVec 64}
    {x : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hg : S.globals.lookup g = some (.val (.word a)))
    (hx : ∀ v, ev S x = some v → ∃ w, v = .val (.word w))
    (hb : ∀ (w : BitVec 64), Ret { S with memory := updW S.memory (a + k) w } b Φ) :
    Ret S (.seq (.store (.op .add [.var .global g, .const k]) x) b) Φ :=
  Ret.seq_storeWv _ (ev_globOff S g a k hg) hx (fun w _ _ => hb w)

theorem ev_load_word {F : Type} (S : PanSemStateFiniteExact 64 F) (y : ExpHOL 64) (v : ValueHOL 64)
    (h : ev S (.load .one y) = some v) : ∃ w, v = .val (.word w) := by
  simp only [ev] at h
  rw [evalHOLExact] at h
  split at h
  · split at h
    · rename_i a _
      rw [memLoadHOLExact] at h
      split at h
      · cases hm : S.toExact.memory a with
        | word w => rw [hm] at h; exact ⟨w, (Option.some.inj h).symm⟩
      · cases h
    · cases h
  · cases h

attribute [local irreducible] Ret in
/-- `refill_frame_state_gas()` writes only `ev+64`, `ev+72`, `ev+192`. -/
theorem refill_frame_state_gas_run {F : Type} (s : PanSemStateFiniteExact 64 F) (e : BitVec 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e))) :
    Ret s (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas) (fun _ post =>
      post.globals = s.globals ∧ (∃ w1 w2 w3 : BitVec 64, post.memory =
        updW (updW (updW s.memory (e + 64) w1) (e + 72) w2) (e + 192) w3) ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_refill_frame_state_gas =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_refill_frame_state_gas).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_refill_frame_state_gas,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.dec fun mv _ => ?_
  refine Ret.storeGlobOp he fun w1 => ?_
  refine Ret.storeGlobAny he (fun v hv => ev_load_word _ _ v hv) fun w2 => ?_
  refine Ret.storeGlobAny he (fun v hv => ⟨0, by simpa [ev, evalHOLExact] using hv.symm⟩) fun w3 => ?_
  refine Ret.ret fun _ _ => ?_
  exact ⟨rfl, ⟨w1, w2, w3, rfl⟩, rfl, rfl⟩

attribute [local irreducible] Ret in
/-- `frame_halt(err)` writes only `ev+184`, `ev+64`, `ev+160`. -/
theorem frame_halt_run {F : Type} (s : PanSemStateFiniteExact 64 F) (e ew : BitVec 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (herr : s.locals.lookup (ofString "err") = some (.val (.word ew))) :
    Ret s (sourceFnBody Guest.Software.guestFn_frame_halt) (fun _ post =>
      post.globals = s.globals ∧ (∃ w1 w2 w3 : BitVec 64, post.memory =
        updW (updW (updW s.memory (e + 184) w1) (e + 64) w2) (e + 160) w3) ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_frame_halt =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_frame_halt).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_frame_halt,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.storeGlobOp he fun w1 => ?_
  refine Ret.storeGlobAny he (fun v hv => ⟨0, by simpa [ev, evalHOLExact] using hv.symm⟩) fun w2 => ?_
  refine Ret.storeGlobAny he (fun v hv => ⟨ew, by simpa [ev, evalHOLExact, herr] using hv.symm⟩)
    fun w3 => ?_
  refine Ret.ret fun _ _ => ?_
  exact ⟨rfl, ⟨w1, w2, w3, rfl⟩, rfl, rfl⟩

end FinishLeaves4

section RollbackRun
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

private theorem rb_foldl_lookup_preserved {α β : Type} [DecidableEq α]
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

private theorem rb_zip_fst_ne {α β γ : Type}
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

theorem rb_param_at {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fn : MlS) (pre : List (MlS × ShapeHOL)) (pk : MlS) (sk : ShapeHOL)
    (post : List (MlS × ShapeHOL)) (body : ProgHOL width) (rs : ShapeHOL)
    (hafter : ∀ q ∈ post, q.1 ≠ pk)
    (hlookup : code fn = some (pre ++ (pk, sk) :: post, body, rs))
    {vpre : List (ValueHOL width)} {vk : ValueHOL width} {vpost : List (ValueHOL width)}
    (hlen : vpre.length = pre.length)
    {foundBody : ProgHOL width} {locals : HolFiniteMapExact MlS (ValueHOL width)}
    {foundRs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn (vpre ++ vk :: vpost) =
      some (foundBody, locals, foundRs)) :
    foundBody = body ∧ locals.lookup pk = some vk := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
  split at hfound
  · cases hfound
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hfound
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hlookup] at raw
    dsimp only at raw
    split at raw
    · have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨rfl, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨rfl, _⟩
      refine ⟨rfl, ?_⟩
      dsimp only
      have hzip : (List.map Prod.fst (pre ++ (pk, sk) :: post)).zip (vpre ++ vk :: vpost) =
          (pre.map Prod.fst).zip vpre ++ (pk, vk) :: (post.map Prod.fst).zip vpost := by
        rw [List.map_append, List.map_cons, List.zip_append (by simp [hlen]), List.zip_cons_cons]
      rw [hzip, List.foldl_append, List.foldl_cons]
      rw [rb_foldl_lookup_preserved ((post.map Prod.fst).zip vpost) _ pk
        (rb_zip_fst_ne post vpost pk hafter)]
      simp
    · cases raw

theorem rb_evalList_cons_inv {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64)
    (es : List (ExpHOL 64)) {values : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (e :: es) =
      some values) :
    ∃ v vs, values = v :: vs ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
        some v := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp only [evalListHOLExact] at h
  revert h
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e
    with _ | v
  · simp
  · rcases hes : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) es with _ | vs
    · simp
    · simp only [Option.some.injEq]
      intro h
      exact ⟨v, vs, h.symm, rfl⟩

theorem rb_evalAt_loadL' {F : Type} (t : PanSemStateFiniteExact 64 F) (l : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString l), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (locN t l + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hl : t.locals.lookup (ofString l) with _ | v
  · simp [hl] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [locN, memW, hl, hadd, h.2]
    · simp [hl, valueIsWord] at h
    · simp [hl, valueIsWord] at h

theorem rb_evalAt_loadL {F : Type} (t : PanSemStateFiniteExact 64 F) (l : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString l), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (locN t l + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hl : t.locals.lookup (ofString l) with _ | w
    · simp [hl] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hl, valueIsWord] at h
      · simp [hl, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  exact ⟨a, rfl, rb_evalAt_loadL' t l k a h⟩

theorem rb_ivlUnhit_of_frameOutside {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk : ∀ j ∈ keep, j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ Disj i j)
    (hf1 : fresh.1 % 8 = 0) (hf2 : fresh.2 % 8 = 0) (hf : Disj i fresh) :
    Wave8Contracts.M08.IvlUnhit s post i := by
  intro a ha8 hin1 hin2
  apply hfr a
  · intro j hj hcj
    obtain ⟨hj1, hj2, hd⟩ := hk j hj
    rcases j with ⟨j1, j2⟩
    rcases i with ⟨i1, i2⟩
    obtain ⟨hcj1, hcj2⟩ := hcj
    unfold Disj at hd
    dsimp only at hj1 hj2 hin1 hin2 hcj1 hcj2 hd
    rcases hd with h | h | h | h <;> omega
  · intro hcf
    rcases fresh with ⟨f1, f2⟩
    rcases i with ⟨i1, i2⟩
    obtain ⟨hcf1, hcf2⟩ := hcf
    have hd := hf
    unfold Disj at hd
    dsimp only at hf1 hf2 hin1 hin2 hcf1 hcf2 hd
    rcases hd with h | h | h | h <;> omega

/-- One `htab_truncate(ld(child+k), ...)` call: the `HtabExit` facts transported to the caller. -/
theorem rb_trunc_call {F : Type} (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (k : BitVec 64) (rest : List (ExpHOL 64)) (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL) (v : ValueHOL 64)
    (cpost : PanSemStateFiniteExact 64 F)
    (h1 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "child"), .const k]) :: rest) = some values)
    (h2 : lookupCodeHOLFinite s.code.lookup (ofString "htab_truncate") values = some (body, callee, ret))
    (h3 : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), cpost))
    (hA : ArenaReady s) (hwf : HtabWF s (memW s (locN s "child" + k.toNat)))
    (hal : ∀ i ∈ htabFootprint s (memW s (locN s "child" + k.toNat)), Allocated s i) :
    let t := memW s (locN s "child" + k.toNat)
    let fresh : Ivl := (globN s "heap_ptr", globN cpost "heap_ptr" - globN s "heap_ptr")
    ArenaReady cpost ∧ HtabWF cpost t ∧ globN s "heap_ptr" ≤ globN cpost "heap_ptr" ∧
    (∀ i ∈ htabFootprint cpost t, Allocated cpost i ∧
      ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
    FrameOutside s cpost (htabFootprint s t) fresh ∧
    (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString → s.globals.lookup k = cpost.globals.lookup k) ∧
    cpost.code = s.code ∧ cpost.memaddrs = s.memaddrs := by
  obtain ⟨tv, vs, rfl, htv⟩ := rb_evalList_cons_inv s _ _ h1
  obtain ⟨w, rfl, hw⟩ := rb_evalAt_loadL s "child" k tv htv
  obtain ⟨_, hct⟩ := rb_param_at s.code.lookup (ofString "htab_truncate") []
    (ofString "t") .one [(ofString "n", .one)] _ _
    (by simp only [List.mem_singleton]; rintro _ rfl; decide)
    (by rw [hcode]; simpa using HtabC00Ports.lookup_htab_truncate) (vpre := []) (by simp) h2
  have hlocT : locN (callEntryStateHOLFinite s callee) "t" = memW s (locN s "child" + k.toNat) := by
    have : locN (callEntryStateHOLFinite s callee) "t" = w.toNat := by
      simp only [locN, callEntryStateHOLFinite, hct]
    exact this.trans hw
  have hPc : HtabArgWF (callEntryStateHOLFinite s callee) := by
    refine ⟨(arenaReady_with_locals s callee (s.clock - 1)).2 hA, ?_, ?_⟩
    · rw [hlocT]; exact (htabWF_with_locals s callee (s.clock - 1) _).2 hwf
    · rw [hlocT]; exact hal
  have hQ := HtabC00Ports.FunSpec.at_lookup HtabC00Ports.htab_truncate_spec s hcode _ body callee ret
    h2 hPc (by rw [h3]; simp)
  rw [h3] at hQ
  have hx := hQ v rfl
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
  rw [h3] at hmeta
  obtain ⟨hAR, hWF, _, _, hgrow, hfp, hfr, hglob⟩ := hx
  rw [hlocT] at hWF hfp hfr
  exact ⟨hAR, hWF, hgrow, hfp, hfr, hglob, hmeta.1, hmeta.2.1⟩

theorem rb_cellHits_inside {a : Nat} {i : Ivl} {lo hi : Nat} (h : CellHits a i) (hin : Inside i lo hi)
    (hle : lo ≤ hi) : CellHits a (lo, hi - lo) := by
  unfold CellHits at h ⊢; unfold Inside at hin; dsimp only at h hin ⊢; omega

theorem rb_allocated_mono {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hglob : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k)
    {i : Ivl} (hi : Allocated s i) : Allocated post i := by
  have hscr : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    have hg := hglob (ofString "scratch_ptr") (by decide)
    simp only [globN, hg]
  rcases hi with hi | hi
  · exact Or.inl ⟨hi.1, Nat.le_trans hi.2 hgrow⟩
  · exact Or.inr ⟨by rw [hscr]; exact hi.1, hi.2⟩

/-- The write frame of `rollback_child_access(child)`. -/
def RbPost {F : Type} (s post : PanSemStateFiniteExact 64 F) (c : Nat) : Prop :=
  post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ ArenaReady post ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
  (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString → s.globals.lookup k = post.globals.lookup k) ∧
  ∀ a : BitVec 64,
    (∀ i ∈ htabFootprint s (memW s (c + 168)) ++ htabFootprint s (memW s (c + 176)),
      ¬ CellHits a.toNat i) →
    ¬ CellHits a.toNat (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") →
    post.memory a = s.memory a

attribute [local irreducible] Ret in
theorem rollback_child_access_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hR : RollbackReadyAt s (locN s "child")) :
    Ret s (sourceFnBody Guest.Software.guestFn_rollback_child_access)
      (fun _ post => RbPost s post (locN s "child")) := by
  have hb : sourceFnBody Guest.Software.guestFn_rollback_child_access =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_rollback_child_access).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_rollback_child_access,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  obtain ⟨hA_s, hal_c, hw_c, htabs, hsep⟩ := hR
  obtain ⟨hwf_168, hal_168⟩ := htabs 168 (by simp)
  obtain ⟨hwf_176, hal_176⟩ := htabs 176 (by simp)
  set c := locN s "child" with hcdef
  set t1 := memW s (c + 168) with ht1
  set t2 := memW s (c + 176) with ht2
  refine Ret.seq_call00 fun values body callee ret v cpost h1 h2 h3 => ?_
  obtain ⟨hAR1, hWF1, hgrow1, hfp1, hfr1, hglob1, hcode1, hdom1⟩ :=
    rb_trunc_call s hcode (BitVec.ofNat 64 168) _ values body callee ret v cpost h1 h2 h3 hA_s
      hwf_168 (fun i hi => (hal_168 i hi).1)
  have hc_hi : c + 280 ≤ 2 ^ 64 := by
    have h1 : heapLimit ≤ heapEnd := by decide
    have h2 : scratchEnd ≤ heapEnd := by decide
    have h3 : heapEnd ≤ 2 ^ 64 := by decide
    rcases hal_c with ⟨_, hi⟩ | ⟨_, hi⟩
    · have := hA_s.2.2.1; omega
    · have := hA_s.2.2.2.2.2.1; omega
  have hf1 : (globN s "heap_ptr") % 8 = 0 := hA_s.2.2.2.2.2.2.1
  have hf2 : (globN cpost "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have hp8 : (globN cpost "heap_ptr") % 8 = 0 := hAR1.2.2.2.2.2.2.1
    omega
  have hdf : ∀ {i : Ivl}, Allocated s i →
      Disj i (globN s "heap_ptr", globN cpost "heap_ptr" - globN s "heap_ptr") := fun hi =>
    Wave8Contracts.M08.disj_symm (Wave8Contracts.M08.disj_allocated_fresh_heap
      (f := (globN s "heap_ptr", globN cpost "heap_ptr" - globN s "heap_ptr")) hA_s.2 hAR1.2 hi
      ⟨le_refl _, by dsimp only; omega⟩)
  have hu_c : Wave8Contracts.M08.IvlUnhit s cpost (c, 280) :=
    rb_ivlUnhit_of_frameOutside hfr1
      (fun j hj => ⟨(hwf_168.1 j hj).2.1, (hwf_168.1 j hj).2.2.1, (hal_168 j hj).2⟩)
      hf1 hf2 (hdf hal_c)
  have hc8 : c % 8 = 0 := hw_c.1
  have hm176 : memW cpost (c + 176) = t2 :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_c (by omega) hc_hi ⟨by omega, by omega⟩
  set mid := { cpost with locals := s.locals } with hmid
  have hmid_c : locN mid "child" = c := rfl
  have hmid_t2 : memW mid (c + 176) = t2 := hm176
  -- footprint of `t2` in `mid` and its well-formedness
  have hmidfp : ∀ i ∈ htabFootprint mid t2, Allocated mid i ∧
      ((∃ j ∈ htabFootprint s t1 ++ htabFootprint s t2, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s "heap_ptr") (globN cpost "heap_ptr")) := by
    rcases hsep with heq | hdisj
    · intro i hi
      have hi' : i ∈ htabFootprint cpost t1 := by show i ∈ htabFootprint cpost t1; rw [heq]; exact hi
      obtain ⟨hal, hin⟩ := hfp1 i hi'
      refine ⟨hal, ?_⟩
      rcases hin with ⟨j, hj, hij⟩ | hin
      · exact Or.inl ⟨j, List.mem_append_left _ hj, hij⟩
      · right; unfold Inside at hin ⊢; dsimp only at hin; omega
    · have hu_t2 : ∀ i ∈ htabFootprint s t2, Wave8Contracts.M08.IvlUnhit s cpost i := by
        intro i hi
        exact rb_ivlUnhit_of_frameOutside hfr1
          (fun j hj => ⟨(hwf_168.1 j hj).2.1, (hwf_168.1 j hj).2.2.1, Wave8Contracts.M08.disj_symm (hdisj j hj i hi)⟩)
          hf1 hf2 (hdf (hal_176 i hi).1)
      have ht2_fp : (t2, 88) ∈ htabFootprint s t2 := by simp [htabFootprint]
      have ht2_8 : t2 % 8 = 0 := (hwf_176.1 _ ht2_fp).2.1
      have ht2_hi : t2 + 88 ≤ 2 ^ 64 := by
        have := (hwf_176.1 _ ht2_fp).1.2
        have h3 : heapEnd ≤ 2 ^ 64 := by decide
        dsimp only at this; omega
      obtain ⟨_, hfp_eq⟩ := Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit ht2_8 ht2_hi
        (hu_t2 _ ht2_fp)
      intro i hi
      have hi' : i ∈ htabFootprint s t2 := by
        have : htabFootprint mid t2 = htabFootprint cpost t2 := rfl
        rw [this, hfp_eq] at hi; exact hi
      refine ⟨rb_allocated_mono hgrow1 hglob1
        (hal_176 i hi').1, Or.inl ⟨i, List.mem_append_right _ hi', le_refl _, le_refl _⟩⟩
  have hmidwf : HtabWF mid t2 := by
    rcases hsep with heq | hdisj
    · have : HtabWF cpost t2 := by show HtabWF cpost t2; rw [← heq]; exact hWF1
      exact (htabWF_with_locals cpost s.locals cpost.clock t2).2 this
    · have hu_t2 : ∀ i ∈ htabFootprint s t2, Wave8Contracts.M08.IvlUnhit s cpost i := by
        intro i hi
        exact rb_ivlUnhit_of_frameOutside hfr1
          (fun j hj => ⟨(hwf_168.1 j hj).2.1, (hwf_168.1 j hj).2.2.1, Wave8Contracts.M08.disj_symm (hdisj j hj i hi)⟩)
          hf1 hf2 (hdf (hal_176 i hi).1)
      exact (htabWF_with_locals cpost s.locals cpost.clock t2).2
        (Wave8Contracts.M08.htabWF_congr_unhit hA_s.1 hAR1.1 hwf_176 hu_t2)
  have hmidA : ArenaReady mid := (arenaReady_with_locals cpost s.locals cpost.clock).2 hAR1
  have hmidcode : mid.code = originalRuntimeCode := hcode1.trans hcode
  refine Ret.seq_call00 fun values' body' callee' ret' v' cpost' h1' h2' h3' => ?_
  obtain ⟨hAR2, _, hgrow2, _, hfr2, hglob2, hcode2, hdom2⟩ :=
    rb_trunc_call mid hmidcode (BitVec.ofNat 64 176) _ values' body' callee' ret' v' cpost'
      h1' h2' h3' hmidA (by show HtabWF mid (memW mid (c + 176)); rw [hmid_t2]; exact hmidwf)
      (by show ∀ i ∈ htabFootprint mid (memW mid (c + 176)), Allocated mid i
          rw [hmid_t2]; intro i hi; exact (hmidfp i hi).1)
  refine Ret.ret fun _ _ => ?_
  have hhp_mid : globN mid "heap_ptr" = globN cpost "heap_ptr" := rfl
  refine ⟨hcode2.trans hcode1, hdom2.trans hdom1,
    (arenaReady_with_locals cpost' _ _).2 hAR2, le_trans hgrow1 hgrow2,
    fun k hk => (hglob1 k hk).trans (hglob2 k hk), ?_⟩
  intro a hkeep hfresh
  change ¬ CellHits a.toNat (globN s "heap_ptr", globN cpost' "heap_ptr" - globN s "heap_ptr") at hfresh
  show cpost'.memory a = s.memory a
  have hg2 : globN cpost "heap_ptr" ≤ globN cpost' "heap_ptr" := hgrow2
  have hle12 := le_trans hgrow1 hgrow2
  have e1 : cpost'.memory a = mid.memory a := by
    apply hfr2 a
    · intro i hi hci
      change i ∈ htabFootprint mid (memW mid (c + 176)) at hi
      rw [hmid_t2] at hi
      rcases (hmidfp i hi).2 with ⟨j, hj, hij⟩ | hin
      · exact hkeep j hj (by unfold CellHits at hci ⊢; unfold Inside at hij; omega)
      · exact hfresh (by unfold CellHits at hci ⊢; unfold Inside at hin; dsimp only; omega)
    · intro hc; apply hfresh
      unfold CellHits at hc ⊢; dsimp only at hc ⊢; rw [hhp_mid] at hc; omega
  have e2 : cpost.memory a = s.memory a := by
    apply hfr1 a
    · intro i hi hci; exact hkeep i (List.mem_append_left _ hi) hci
    · intro hc; apply hfresh
      unfold CellHits at hc ⊢; dsimp only at hc ⊢; omega
  exact e1.trans e2

end RollbackRun

section ReadOnlyRun
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

/-- `address_to_u256(a)` is read-only: on a normal return only locals/clock change. -/
theorem address_to_u256_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) :
    Ret s (sourceFnBody Guest.Software.guestFn_address_to_u256) (fun _ post =>
      post = { s with locals := post.locals, clock := post.clock }) := by
  intro v hv
  have hsafe := R14Shards.OpHandlersA.evaluate_readOnlyProg R14Shards.OpHandlersA.opRoCallees
    R14Shards.OpHandlersA.opRoCallees_good
    (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_address_to_u256).body) rfl s hcode
  exact hsafe.to_resumes (Or.inl ⟨v, hv⟩)

end ReadOnlyRun

section StateRestoreRun
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

/-- `state_restore(snap)` from an `EvmInv` entry: on return `EvmInv` holds, the chain is kept,
and no frame record `(e, 280)` or continuation record `(c, 104)` of the chain is written. -/
theorem state_restore_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hInv : EvmInv s) :
    Ret s (sourceFnBody Guest.Software.guestFn_state_restore) (fun _ post =>
      EvmInv post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
      Wave8Contracts.M23.GlobalsKept ["heap_ptr", "journal_n"] s post ∧
      evmChain post = evmChain s ∧
      (∀ ec ∈ evmChain s, ∀ a : BitVec 64, a.toNat % 8 = 0 →
        (CellHits a.toNat (ec.1, 280) ∨ CellHits a.toNat (ec.2, 104)) →
        post.memory a = s.memory a)) := by
  intro v hv
  obtain ⟨h1, h2, h3, h4, _, h6⟩ :=
    R16Shards.StateRestoreEpilogue.state_restore_body_spec s hcode hInv v hv
  refine ⟨h1, h2, h3, h4, fun ec hec a ha8 hin => ?_⟩
  obtain ⟨hu1, hu2⟩ := h6 ec hec
  rcases hin with h | h
  · exact hu1 a ha8 h
  · exact hu2 a ha8 h

end StateRestoreRun

section ChargeRun
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

theorem Ret.seq_raise_cg {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS} {x : ExpHOL 64}
    {rest : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} :
    Ret s (.seq (.raise n x) rest) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise] at hv
  revert hv
  split
  · rename_i sh val _ _
    by_cases hc : shapeOfHOLExact val = sh ∧ sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact val) ≤ 32
    · simp only [if_pos hc]; simp
    · simp only [if_neg hc]; simp
  · simp

attribute [local irreducible] Ret in
/-- `charge_gas(amount)` writes only `ev+64`, `ev+184`. -/
theorem charge_gas_run {F : Type} (s : PanSemStateFiniteExact 64 F) (e : BitVec 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e))) :
    Ret s (sourceFnBody Guest.Software.guestFn_charge_gas) (fun _ post =>
      post.globals = s.globals ∧ (∃ w1 w2 : BitVec 64, post.memory =
        updW (updW s.memory (e + 64) w1) (e + 184) w2) ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_charge_gas =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_charge_gas).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_charge_gas,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.dec fun mv _ => ?_
  refine Ret.seq_ite fun w _ => ⟨fun _ => Ret.seq_raise_cg, fun _ => ?_⟩
  refine Ret.seq (Ret.skip_noret) fun t ht => ?_
  rw [evaluateHOLFiniteState_skip] at ht
  cases ht
  refine Ret.storeGlobOp he fun w1 => ?_
  refine Ret.storeGlobAny he (fun v hv => ev_op_word _ _ _ v hv) fun w2 => ?_
  refine Ret.ret fun _ _ => ?_
  exact ⟨rfl, ⟨w1, w2, rfl⟩, rfl, rfl⟩

theorem fl_lookup_add_sat :
    originalRuntimeCode.lookup (ofString "add_sat") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_add_sat, .one) :=
  lookup_of_guestAst_getElem 441 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_sat) rfl

theorem add_sat_locOnly : locOnly (sourceFnBody Guest.Software.guestFn_add_sat) = true := by
  decide

theorem Ret.decCall_addsat {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (hk : ∀ (t : PanSemStateFiniteExact 64 F), t.globals = s.globals → t.memory = s.memory →
      t.code = s.code → t.memaddrs = s.memaddrs →
      Ret t cont (fun w u =>
        Φ w { u with locals := HolFiniteMapExact.resVarEq u.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x sh (ofString "add_sat") args cont) Φ := by
  refine Ret.decCall_gen fun values body callee ret v post _ h2 h3 => ?_
  have hlk : s.code.lookup (ofString "add_sat") = some ([(ofString "a", .one), (ofString "b", .one)],
      sourceFnBody Guest.Software.guestFn_add_sat, .one) := by rw [hcode]; exact fl_lookup_add_sat
  have hb := InitECandidate.Solver.PanRunBounded.lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ _ _ _ _ _ hlk h2
  subst hb
  have hlf := locFrame_eval _ add_sat_locOnly (callEntryStateHOLFinite s callee)
  rw [h3] at hlf
  unfold LocFrame at hlf
  simp only at hlf
  have hpg : post.globals = s.globals := (congrArg PanSemStateFiniteExact.globals hlf).trans rfl
  have hpm : post.memory = s.memory := (congrArg PanSemStateFiniteExact.memory hlf).trans rfl
  have hpc : post.code = s.code := (congrArg PanSemStateFiniteExact.code hlf).trans rfl
  have hpd : post.memaddrs = s.memaddrs := (congrArg PanSemStateFiniteExact.memaddrs hlf).trans rfl
  exact hk _ (by simp [setVarHOLFinite, hpg]) (by simp [setVarHOLFinite, hpm])
    (by simp [setVarHOLFinite, hpc]) (by simp [setVarHOLFinite, hpd])

theorem Ret.seq_return_cg {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {rest : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev s e = some val → Φ val (emptyLocalsHOLFinite s)) :
    Ret s (.seq (.return e) rest) Φ := by
  refine Ret.seq (Ret.ret h) fun t ht => ?_
  exfalso
  rw [evaluateHOLFiniteState_return] at ht
  revert ht
  split <;> (try split) <;> simp

attribute [local irreducible] Ret in
/-- `charge_state_gas(amount)` writes only `ev+72`, `ev+64`, `ev+192`. -/
theorem charge_state_gas_run {F : Type} (s : PanSemStateFiniteExact 64 F) (e : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e))) :
    Ret s (sourceFnBody Guest.Software.guestFn_charge_state_gas) (fun _ post =>
      post.globals = s.globals ∧ (∀ a : BitVec 64, a ≠ e + 72 → a ≠ e + 64 → a ≠ e + 192 →
        post.memory a = s.memory a) ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs) := by
  have hb : sourceFnBody Guest.Software.guestFn_charge_state_gas =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_charge_state_gas).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_charge_state_gas,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.dec fun v1 _ => ?_
  refine Ret.dec fun v2 _ => ?_
  refine Ret.seq_ite fun w _ => ⟨fun _ => ?_, fun _ => ?_⟩
  · refine Ret.seq_assoc (Ret.storeGlobOp he fun w1 => Ret.seq_return_cg fun _ _ => ?_)
    refine ⟨rfl, fun a h1 _ _ => ?_, rfl, rfl⟩
    simp only [emptyLocalsHOLFinite, setVarHOLFinite, updW]
    split <;> simp_all
  · refine Ret.seq Ret.skip_noret fun t ht => ?_
    rw [evaluateHOLFiniteState_skip] at ht
    cases ht
    refine Ret.decCall_addsat (by simpa [setVarHOLFinite] using hcode) fun t hg hm hc hd => ?_
    have he' : t.globals.lookup (ofString "ev") = some (.val (.word e)) := by
      rw [hg]; simpa [setVarHOLFinite] using he
    refine Ret.seq_ite fun w' _ => ⟨fun _ => ?_, fun _ => ?_⟩
    · refine Ret.seq (Ret.dec fun rv _ => ?_) fun t2 ht2 => ?_
      swap
      · exact Ret.seq_raise_cg
      have he'' : (setVarHOLFinite (ofString "rem") rv t).globals.lookup (ofString "ev") =
          some (.val (.word e)) := by simpa [setVarHOLFinite] using he'
      refine Ret.storeGlobAny he'' (fun v hv => ⟨0, by simpa [ev, evalHOLExact] using hv.symm⟩) fun w1 => ?_
      refine Ret.storeGlobOp he'' fun w2 => ?_
      refine Ret.storeGlobOp he'' fun w3 => ?_
      refine Ret.ret fun _ _ => ?_
      refine ⟨by simpa [emptyLocalsHOLFinite, setVarHOLFinite] using hg,
        fun a h1 h2 h3 => ?_, by simpa [emptyLocalsHOLFinite, setVarHOLFinite] using hc,
        by simpa [emptyLocalsHOLFinite, setVarHOLFinite] using hd⟩
      have hm' := congrFun hm a
      simp only [emptyLocalsHOLFinite, setVarHOLFinite, updW] at hm' ⊢
      split <;> [simp_all; skip]
      split <;> [simp_all; skip]
      split <;> [simp_all; skip]
      simpa using hm'
    · refine Ret.seq Ret.skip_noret fun t' ht' => ?_
      rw [evaluateHOLFiniteState_skip] at ht'
      cases ht'
      exact Ret.seq_raise_cg

end ChargeRun

section LstPushRun
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

theorem Flw.decCall_gen' {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname : MlS}
    {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hk : ∀ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Flw (setVarHOLFinite x v { post with locals := s.locals }) cont
        (fun r t => Ψ r { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Flw s (.decCall x sh fname args cont) Ψ := by
  intro hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hf ⊢
  revert hf
  split
  · intro hf; rcases hf with h | h | h <;> cases h
  · rename_i values hargs
    split
    · intro hf; rcases hf with h | h | h <;> cases h
    · rename_i body callee ret hl
      split
      · intro hf; rcases hf with h | h | h <;> cases h
      · dsimp only
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        dsimp only
        rcases r with _ | r
        · intro hf; rcases hf with h | h | h <;> cases h
        · cases r with
          | returned w =>
            dsimp only
            split
            · intro hf
              exact hk values body callee ret w post hargs hl hrun hf
            · intro hf; rcases hf with h | h | h <;> cases h
          | _ => intro hf; rcases hf with h | h | h <;> cases h


theorem Flw.seq_call00 {F : Type} {s : PanSemStateFiniteExact 64 F} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hk : ∀ values body callee ret v cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
        some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned v), cpost) →
      Flw { cpost with locals := s.locals } cont Ψ) :
    Flw s (.seq (.call (some (none, none)) fname args) cont) Ψ := by
  refine Flw.seq fun hf => ?_
  have hnb := call0_noRetBrk s fname args
  have hflow : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
      (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = some .continue := by
    rcases hf with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hnb.1.2
  obtain ⟨values, body, callee, ret, v, cpost, h1, h2, h3, h4⟩ := call0_flow s fname args hflow
  rw [h4]
  exact ⟨fun _ => hk values body callee ret v cpost h1 h2 h3, fun h => absurd rfl h⟩

theorem ev_load_loc {F : Type} (S : PanSemStateFiniteExact 64 F) (x : MlS) (a k : BitVec 64)
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

theorem ev_mul_loc {F : Type} (S : PanSemStateFiniteExact 64 F) (x y : MlS) (a b : BitVec 64)
    (hx : S.locals.lookup x = some (.val (.word a))) (hy : S.locals.lookup y = some (.val (.word b))) :
    ev S (.panop .mul [.var .local x, .var .local y]) = some (.val (.word (a * b))) := by
  simp [ev, evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, panOpHOL]


/-- `x := alloc(arg); cont` in `Flw` form, from an `ArenaReady` state. -/
theorem Flw.decCall_alloc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x : MlS} {arg : ExpHOL 64} {cont : ProgHOL 64}
    {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hA : ArenaReady s)
    (nv : BitVec 64) (harg : ev s arg = some (.val (.word nv)))
    (hk : ∀ (hp q : BitVec 64),
      hp.toNat = globN s "heap_ptr" →
      hp.toNat + nv.toNat ≤ q.toNat →
      q.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat →
      q.toNat % 8 = 0 → ∀ k : Nat,
      Flw (setVarHOLFinite x (.val (.word hp))
          { s with globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := k }) cont
        (fun r t => Ψ r { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Flw s (.decCall x .one (ofString "alloc") [arg] cont) Ψ := by
  obtain ⟨hp, hhp_g, hhp_nat, _, hhp_hi, _⟩ := SoloHtabSet.arenaReady_heap_word hA
  refine Flw.decCall_gen' fun values body callee ret v post h1 h2 h3 => ?_
  have hv : values = [.val (.word nv)] := by
    simp only [evalListHOLFinite, evalListHOLExact] at h1
    unfold ev at harg
    rw [harg] at h1; simp at h1; exact h1.symm
  subst hv
  have hl := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n") _ nv
    (by rw [hA.1.code]; exact SoloHtabSet.lookup_alloc_fn)
  rw [hl] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  let E := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))
  have := SoloHtabSet.alloc_body_run E hp nv hA.1.code hhp_hi hhp_g
    (by simp [E, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) v (by rw [h3])
  rw [h3] at this
  obtain ⟨rfl, hq1, hq2, hq3, hpost⟩ := this
  dsimp only at hpost
  have heq : { post with locals := s.locals } =
      { s with globals := s.globals.update (ofString "heap_ptr",
          .val (.word ((hp + (nv + 7)) &&& ((0 : BitVec 64) - 8)))), clock := post.clock } := by
    rw [hpost]; rfl
  rw [heq]
  exact hk hp _ hhp_nat hq1 hq2 hq3 post.clock

/-- `memcpy(ed, es, en); cont` in `Flw` form (frame only). -/
theorem Flw.seq_memcpy_frame {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ed es en : ExpHOL 64} {cont : ProgHOL 64}
    {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (dst src n : BitVec 64)
    (hd_nw : dst.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hed : ev s ed = some (.val (.word dst)))
    (hes : ev s es = some (.val (.word src)))
    (hen : ev s en = some (.val (.word n)))
    (hk : ∀ s' : PanSemStateFiniteExact 64 F,
      SoloHtabSet.MemCopyFrame s s' dst n.toNat → s'.locals = s.locals → Flw s' cont Ψ) :
    Flw s (.seq (.call (some (none, none)) (ofString "memcpy") [ed, es, en]) cont) Ψ := by
  refine Flw.seq_call00 fun values body callee ret v post h1 h2 h3 => ?_
  have hv : values = [.val (.word dst), .val (.word src), .val (.word n)] := by
    simp only [evalListHOLFinite, evalListHOLExact] at h1
    unfold ev at hed hes hen
    rw [hed, hes, hen] at h1; simp at h1; exact h1.symm
  subst hv
  have hl := pan_three_word_lookup s.code.lookup (ofString "memcpy") (ofString "dst") (ofString "src")
    (ofString "n") _ dst src n (by decide) (by decide) (by decide) (by rw [hcode]; exact SoloHtabSet.lookup_memcpy_fn)
  rw [hl] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  let entry := callEntryStateHOLFinite s
    (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst))).update
      (ofString "src", .val (.word src))).update (ofString "n", .val (.word n)))
  have hspec := SoloHtabSet.memcpy_body_frame entry dst n hd_nw hn_small
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    v (by rw [h3])
  rw [h3] at hspec
  obtain ⟨_, c1, c2, c3, c4, c5, c6, c7⟩ := hspec
  exact hk _ ⟨c1, c2, c3, c4, c5, c6, c7⟩ rfl


theorem ev_load_loc_eq {F : Type} (S : PanSemStateFiniteExact 64 F) (x : MlS) (a k w : BitVec 64)
    (hx : S.locals.lookup x = some (.val (.word a))) (hd : S.memaddrs (a + k))
    (hm : S.memory (a + k) = .word w) :
    ev S (.load .one (.op .add [.var .local x, .const k])) = some (.val (.word w)) := by
  have hd' := ev_addr S x a k hx
  simp only [ev] at hd' ⊢
  rw [evalHOLExact, hd']
  simp only [memLoadHOLExact]
  rw [if_pos hd]
  simp [hm]

theorem ev_add2 {F : Type} (S : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64) (a b : BitVec 64)
    (h1 : ev S e1 = some (.val (.word a))) (h2 : ev S e2 = some (.val (.word b))) :
    ev S (.op .add [e1, e2]) = some (.val (.word (a + b))) := by
  simp only [ev] at h1 h2 ⊢
  simp [evalHOLExact, evalListHOLExact, h1, h2, wordOpHOL, wordOp, valueIsWord, valueWord]

theorem lst_push_tail {F : Type} (T : PanSemStateFiniteExact 64 F) (l esz n arr : BitVec 64)
    (hl : T.locals.lookup (ofString "l") = some (.val (.word l)))
    (hesz : T.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hn : T.locals.lookup (ofString "n") = some (.val (.word n)))
    (harr : T.memory l = .word arr) (hdl : T.memaddrs l) :
    Ret T (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
        (.op .add [.var .local (ofString "n"), .const 1]))
      (.return (.op .add [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
        .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])))
      (fun v post => post.code = T.code ∧ post.memaddrs = T.memaddrs ∧ post.globals = T.globals ∧
        post.be = T.be ∧ post.shMemaddrs = T.shMemaddrs ∧ post.baseAddr = T.baseAddr ∧
        post.memory = updW T.memory (l + 8) (n + 1) ∧ v = .val (.word (arr + n * esz))) := by
  refine Ret.seq_storeWv _ (ev_addr T _ l 8 hl)
    (fun v hv => ⟨n + 1, by
      simpa [ev, evalHOLExact, evalListHOLExact, hn, wordOpHOL, wordOp, valueIsWord, valueWord]
        using hv.symm⟩) fun w hw _ => ?_
  have hw' : w = n + 1 := by
    simp [ev, evalHOLExact, evalListHOLExact, hn, wordOpHOL, wordOp, valueIsWord, valueWord] at hw
    exact hw.symm
  subst hw'
  refine Ret.ret fun val hval => ?_
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hne : l + 0 ≠ l + 8 := by bv_omega
  have h1 := ev_load_loc_eq { T with memory := updW T.memory (l + 8) (n + 1) } _ l 0 arr hl
    (by simpa using hdl) (by show updW T.memory (l + 8) (n + 1) (l + 0) = _
                             rw [updW_ne _ _ _ _ hne]; simpa using harr)
  have h2 := ev_mul_loc { T with memory := updW T.memory (l + 8) (n + 1) } _ _ n esz hn hesz
  rw [ev_add2 _ _ _ _ _ h1 h2] at hval
  exact (Option.some.inj hval).symm


theorem ev_mulE {F : Type} (S : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64) (a b : BitVec 64)
    (h1 : ev S e1 = some (.val (.word a))) (h2 : ev S e2 = some (.val (.word b))) :
    ev S (.panop .mul [e1, e2]) = some (.val (.word (a * b))) := by
  simp only [ev] at h1 h2 ⊢
  simp [evalHOLExact, evalListHOLExact, h1, h2, valueIsWord, valueWord, panOpHOL]

/-- Postcondition of `lst_push(l, esz)` from `s` (with `n = ld(l+8)`, `cap = ld(l+16)`). -/
def LstPushPost {F : Type} (s : PanSemStateFiniteExact 64 F) (l esz n cap : BitVec 64)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) : Prop :=
  post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
  post.baseAddr = s.baseAddr ∧ post.be = s.be ∧
  (∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = s.globals.lookup k) ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧ ArenaReady post ∧
  ∃ arr d : BitVec 64, ∃ len : Nat,
    post.memory l = .word arr ∧ v = .val (.word (arr + n * esz)) ∧
    post.memory (l + 8) = .word (n + 1) ∧
    ((n.toNat < cap.toNat ∧ len = 0 ∧ d = 0 ∧ s.memory l = .word arr ∧ post.memory (l + 16) = .word cap) ∨
     (n = cap ∧ arr = d ∧ len = esz.toNat * n.toNat ∧ globN s "heap_ptr" ≤ d.toNat ∧
       d.toNat + 2 * (esz.toNat * cap.toNat) ≤ globN post "heap_ptr" ∧
       post.memory (l + 16) = .word (cap * 2))) ∧
    ∀ a : BitVec 64, ¬ CellHits a.toNat (d.toNat, len) → a ≠ l → a ≠ l + 8 → a ≠ l + 16 →
      post.memory a = s.memory a

theorem lstPushPost_locals {F : Type} {s post : PanSemStateFiniteExact 64 F} {l esz n cap : BitVec 64}
    {v : ValueHOL 64} (L : HolFiniteMapExact MlS (ValueHOL 64)) (h : LstPushPost s l esz n cap v post) :
    LstPushPost s l esz n cap v { post with locals := L } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    arenaReady_locals _ _ h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

attribute [local irreducible] Ret in
theorem lst_push_run {F : Type} (s : PanSemStateFiniteExact 64 F) (l esz n cap : BitVec 64)
    (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hesz : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hmn : s.memory (l + 8) = .word n) (hmc : s.memory (l + 16) = .word cap)
    (hd0 : s.memaddrs l) (hd8 : s.memaddrs (l + 8)) (hd16 : s.memaddrs (l + 16))
    (hle : n.toNat ≤ cap.toNat) (hcap : n.toNat < 2 ^ 59) (hesz8 : esz.toNat ≤ 8) :
    Ret s (sourceFnBody Guest.Software.guestFn_lst_push)
      (fun v post => LstPushPost s l esz n cap v post) := by
  have hb : sourceFnBody Guest.Software.guestFn_lst_push =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_lst_push).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_lst_push,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.mono (Φ := fun v t => LstPushPost s l esz n cap v t) ?_
    (fun _ t h => lstPushPost_locals _ h)
  refine Ret.dec fun v1 hv1 => ?_
  have hv1' : v1 = .val (.word n) := by rw [ev_load_loc s _ l 8 hl v1 hv1, hmn]
  subst hv1'
  let S1 := setVarHOLFinite (ofString "n") (.val (.word n)) s
  refine Ret.mono (Φ := fun v t => LstPushPost s l esz n cap v t) ?_
    (fun _ t h => lstPushPost_locals _ h)
  refine Ret.dec fun v2 hv2 => ?_
  have hS1l : S1.locals.lookup (ofString "l") = some (.val (.word l)) := by
    simp (config := {decide := true}) [S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl]
  have hv2' : v2 = .val (.word cap) := by rw [ev_load_loc S1 _ l 16 hS1l v2 hv2]; exact congrArg _ hmc
  subst hv2'
  let S2 := setVarHOLFinite (ofString "cap") (.val (.word cap)) S1
  have hS2l : S2.locals.lookup (ofString "l") = some (.val (.word l)) := by
    simp (config := {decide := true}) [S2, S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl]
  have hS2e : S2.locals.lookup (ofString "esz") = some (.val (.word esz)) := by
    simp (config := {decide := true}) [S2, S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hesz]
  have hS2n : S2.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp (config := {decide := true}) [S2, S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hS2c : S2.locals.lookup (ofString "cap") = some (.val (.word cap)) := by
    simp (config := {decide := true}) [S2, S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine Ret.mono (Φ := fun v t => LstPushPost s l esz n cap v t) ?_
    (fun _ t h => lstPushPost_locals _ h)
  show Ret S2 _ _
  rcases hm0 : s.memory l with ⟨arr0⟩
  refine Ret.seq_ite fun cw hcw => ⟨fun hcnz => ?_, fun hcz => ?_⟩
  · -- grow
    have hcw' := srd_cmp S2 .notLower _ _ n cap cw hS2n hS2c hcw
    have hge : cap.toNat ≤ n.toNat := by
      by_contra hlt
      apply hcnz; rw [hcw']
      simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      simp; omega
    have hnc : n = cap := BitVec.eq_of_toNat_eq (by omega)
    replace hcap : cap.toNat < 2 ^ 59 := by rw [← hnc]; exact hcap
    have hS2A : ArenaReady S2 := arenaReady_locals s _ hA
    have hmulT : (esz * cap).toNat = esz.toNat * cap.toNat := by
      rw [BitVec.toNat_mul]; apply Nat.mod_eq_of_lt
      have : esz.toNat * cap.toNat ≤ 8 * 2 ^ 59 := Nat.mul_le_mul hesz8 (by omega)
      omega
    have hnvT : (esz * cap * 2).toNat = 2 * (esz.toNat * cap.toNat) := by
      rw [BitVec.toNat_mul, hmulT]; apply (Nat.mod_eq_of_lt _).trans (by simp; ring)
      have : esz.toNat * cap.toNat ≤ 8 * 2 ^ 59 := Nat.mul_le_mul hesz8 (by omega)
      simp; omega
    refine Ret.seq_flw (NoRet.decCall (NoRet.seq NoRet.call0 (NoRet.seq NoRet.store' NoRet.store'))) ?_
    refine Flw.decCall_alloc hS2A (esz * cap * 2)
      (ev_mulE _ _ _ _ _ (ev_mul_loc S2 _ _ esz cap hS2e hS2c) (ev_const _ _))
      fun hp q hhp hq1 hq2 hq3 k => ?_
    rw [hnvT] at hq1
    have hhp' : hp.toNat = globN s "heap_ptr" := hhp
    let X := setVarHOLFinite (ofString "np") (.val (.word hp))
      { S2 with globals := S2.globals.update (ofString "heap_ptr", .val (.word q)), clock := k }
    have hXl : X.locals.lookup (ofString "l") = some (.val (.word l)) := by
      simp (config := {decide := true}) [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2l]
    have hXe : X.locals.lookup (ofString "esz") = some (.val (.word esz)) := by
      simp (config := {decide := true}) [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2e]
    have hXn : X.locals.lookup (ofString "n") = some (.val (.word n)) := by
      simp (config := {decide := true}) [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2n]
    have hXc : X.locals.lookup (ofString "cap") = some (.val (.word cap)) := by
      simp (config := {decide := true}) [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2c]
    have hXp : X.locals.lookup (ofString "np") = some (.val (.word hp)) := by
      simp [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hcmax : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
    have hmulN : (esz * n).toNat = esz.toNat * n.toNat := by rw [hnc]; exact hmulT
    have hsmall : esz.toNat * n.toNat ≤ 8 * 2 ^ 59 := Nat.mul_le_mul hesz8 (by omega)
    show Flw X _ _
    have hcmx : q.toNat ≤ 2952790016 := hcmax ▸ hq2
    have hnN : n.toNat = cap.toNat := by rw [hnc]
    refine Flw.seq_memcpy_frame hA.1.code hp arr0 (esz * n) (by rw [hmulN]; omega)
      (by rw [hmulN]; omega)
      (by rw [ev_loc]; exact hXp)
      (ev_load_loc_eq X _ l 0 arr0 hXl (by show s.memaddrs (l + 0); simpa using hd0)
        (by show s.memory (l + 0) = _; simpa using hm0))
      (ev_mul_loc X _ _ esz n hXe hXn) fun s' hmc hloc => ?_
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hmc
    have h's l' : s'.locals.lookup l' = X.locals.lookup l' := by rw [hloc]
    refine Flw.seq (Flw.storeW (l + 0) hp (ev_addr s' _ l 0 (by rw [h's]; exact hXl))
      (by rw [ev_loc, h's]; exact hXp) fun _ => ⟨fun _ => ?_, fun h => absurd rfl h⟩)
    refine Flw.storeW (l + 16) (cap * 2) (ev_addr _ _ l 16 (by rw [h's]; exact hXl))
      (ev_mulE _ _ _ _ _ (by rw [ev_loc]; exact (h's _).trans hXc) (ev_const _ _)) fun _ => ?_
    intro _
    let T : PanSemStateFiniteExact 64 F :=
      { s' with memory := updW (updW s'.memory (l + 0) hp) (l + 16) (cap * 2) }
    let L' := HolFiniteMapExact.resVarEq T.locals (ofString "np", S2.locals.lookup (ofString "np"))
    let T' : PanSemStateFiniteExact 64 F := { T with locals := L' }
    show Ret T' _ _
    have hT'l k (hk : k ≠ ofString "np") : T'.locals.lookup k = X.locals.lookup k := by
      show L'.lookup k = _
      simp only [L', T]
      rw [InitECandidate.Solver.PanRunBounded.resVarEq_lookup, if_neg hk, hloc]
    have hT'm : T'.memory l = .word hp := by
      show updW (updW s'.memory (l + 0) hp) (l + 16) (cap * 2) l = _
      have h0 : (l + 0 : BitVec 64) = l := by bv_omega
      rw [updW_ne _ _ _ _ (by bv_omega), h0, updW_eq]
    refine Ret.mono (lst_push_tail T' l esz n hp (by rw [hT'l _ (by decide)]; exact hXl)
      (by rw [hT'l _ (by decide)]; exact hXe) (by rw [hT'l _ (by decide)]; exact hXn) hT'm
      (by show s'.memaddrs l; rw [c2]; exact hd0)) ?_
    rintro v post ⟨pc, pd, pg, pb, psh, pba, pm, rfl⟩
    have hpg : post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
      rw [pg]; exact c6
    have hhq : globN s "heap_ptr" ≤ q.toNat := by omega
    obtain ⟨hAq, hgq, hkeep⟩ := SoloHtabSet.arenaReady_upd_heap hA hhq hq2 hq3
    have hgpost : globN post "heap_ptr" = q.toNat := by
      unfold globN; rw [hpg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    refine ⟨pc.trans c1, pd.trans c2, psh.trans c3, pba.trans c4, pb.trans c5,
      fun k hk => by rw [hpg]; exact (hkeep k (by simpa using hk)).symm, by omega,
      ⟨guestInv_congr (s := s) (pc.trans c1) (pd.trans c2) (psh.trans c3) (pba.trans c4) hA.1,
        arenaOK_congr hpg hAq.2⟩,
      hp, hp, esz.toNat * n.toNat, ?_, rfl, ?_, Or.inr ⟨hnc, rfl, rfl, by omega, ?_, ?_⟩, ?_⟩
    · rw [pm, updW_ne _ _ _ _ (by bv_omega)]; exact hT'm
    · rw [pm, updW_eq]
    · rw [hgpost]; omega
    · rw [pm, updW_ne _ _ _ _ (by bv_omega)]
      show updW (updW s'.memory (l + 0) hp) (l + 16) (cap * 2) (l + 16) = _
      rw [updW_eq]
    · intro a ha h0 h8 h16
      rw [pm, updW_ne _ _ _ _ h8]
      show updW (updW s'.memory (l + 0) hp) (l + 16) (cap * 2) a = _
      rw [updW_ne _ _ _ _ h16, updW_ne _ _ _ _ (by simpa using h0)]
      have := c7 a (by
          intro i hi; simp at hi; subst hi
          rw [Nat.mod_eq_of_lt (by omega)]; exact ha)
        (by simp [CellHits])
      exact this

  · -- no growth
    have hcw' := srd_cmp S2 .notLower _ _ n cap cw hS2n hS2c hcw
    have hlt : n.toNat < cap.toNat := by
      by_contra hge
      rw [hcw'] at hcz
      simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at hcz
      simp at hcz; omega
    refine Ret.seq_skip ?_
    refine Ret.mono (lst_push_tail S2 l esz n arr0 hS2l hS2e hS2n hm0 hd0) ?_
    rintro v post ⟨pc, pd, pg, pb, psh, pba, pm, rfl⟩
    refine ⟨pc, pd, psh, pba, pb, fun k _ => by rw [pg]; rfl, by unfold globN; rw [pg]; rfl,
      ⟨guestInv_congr (s := s) pc pd psh pba hA.1, arenaOK_congr pg hA.2⟩,
      arr0, 0, 0, ?_, rfl, ?_, Or.inl ⟨hlt, rfl, rfl, hm0, ?_⟩, ?_⟩
    · rw [pm, updW_ne _ _ _ _ (by bv_omega)]; exact hm0
    · rw [pm, updW_eq]
    · rw [pm, updW_ne _ _ _ _ (by bv_omega)]; exact hmc
    · intro a _ _ h8 _
      rw [pm, updW_ne _ _ _ _ h8]; rfl


theorem fl_lookup_lst_push :
    originalRuntimeCode.lookup (ofString "lst_push") =
      some ([(ofString "l", .one), (ofString "esz", .one)],
        sourceFnBody Guest.Software.guestFn_lst_push, .one) :=
  lookup_of_guestAst_getElem 410 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_push) rfl

/-- Post of `log_append` from `s`, pushing onto list `L`. Independent of locals. -/
def LogAppendPost {F : Type} (s : PanSemStateFiniteExact 64 F) (L : BitVec 64)
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ ArenaReady post ∧
  (∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = s.globals.lookup k) ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
  ∃ (slot d : BitVec 64) (len : Nat),
    (len = 0 ∨ (globN s "heap_ptr" ≤ d.toNat ∧ d.toNat + len ≤ globN post "heap_ptr")) ∧
    ∀ a : BitVec 64, ¬ CellHits a.toNat (d.toNat, len) → a ≠ L → a ≠ L + 8 → a ≠ L + 16 →
      a ≠ slot → post.memory a = s.memory a

theorem logAppendPost_locIns {F : Type} (s : PanSemStateFiniteExact 64 F) (L : BitVec 64) :
    LocIns (fun (_ : ValueHOL 64) t => LogAppendPost s L t) := by
  intro v t M ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, arenaReady_locals t M h3, h4, h5, h6⟩

attribute [local irreducible] Ret in
/-- `log_append(e, log)`: pushes onto the logs list `L = ld(e+88)` and stores `log` in the new
slot; memory changes only in the fresh backing array, at `L+0/8/16` and at the slot. -/
theorem log_append_run {F : Type} (s : PanSemStateFiniteExact 64 F) (e L lg n cap : BitVec 64)
    (hA : ArenaReady s)
    (he : s.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : s.locals.lookup (ofString "log") = some (.val (.word lg)))
    (hd88 : s.memaddrs (e + 88)) (hmL : s.memory (e + 88) = .word L)
    (hmn : s.memory (L + 8) = .word n) (hmc : s.memory (L + 16) = .word cap)
    (hd0 : s.memaddrs L) (hd8 : s.memaddrs (L + 8)) (hd16 : s.memaddrs (L + 16))
    (hle : n.toNat ≤ cap.toNat) (hcap : n.toNat < 2 ^ 59) :
    Ret s (sourceFnBody Guest.Software.guestFn_log_append)
      (fun _ post => LogAppendPost s L post) := by
  have hb : sourceFnBody Guest.Software.guestFn_log_append =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_log_append).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_log_append,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.decCallL (logAppendPost_locIns s L) fun vals body cal ret v post h1 h2 h3 => ?_
  have hv : vals = [.val (.word L), .val (.word 8)] := by
    obtain ⟨v1, v2, rfl, he1, he2⟩ := evalList2_inv _ _ _ h1
    have e1 := he1.symm.trans (ev_load_loc_eq s _ e _ L he hd88 hmL)
    have e2 := he2.symm.trans (ev_const s _)
    rw [Option.some.inj e1, Option.some.inj e2]; rfl
  obtain ⟨rfl, rfl⟩ := lk2 hA.1.code (by decide) fl_lookup_lst_push L 8 hv h2
  have hAE : ArenaReady (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "l", .val (.word L))).update
        (ofString "esz", .val (.word 8)))) :=
    ⟨guestInv_callEntry _ _ hA.1, arenaOK_congr (s := s) rfl hA.2⟩
  obtain ⟨pc, pd, psh, pba, pb, pg, phm, pA, arr, d, len, _, rfl, _, halt, pm⟩ := Ret.apply
    (lst_push_run (callEntryStateHOLFinite s _) L 8 n cap hAE
      (by simp (config := {decide := true}) [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hmn hmc hd0 hd8 hd16 hle hcap (by decide)) h3
  generalize hX : setVarHOLFinite (ofString "slot") (.val (.word (arr + n * 8)))
    { post with locals := s.locals } = X
  have hXlg : X.locals.lookup (ofString "log") = some (.val (.word lg)) := by
    rw [← hX]
    simp (config := {decide := true}) [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlg]
  have hXs : X.locals.lookup (ofString "slot") = some (.val (.word (arr + n * 8))) := by
    rw [← hX]; exact setVar_lookup_eq _ _ _
  have hXg : X.globals = post.globals := by rw [← hX]; rfl
  have hXm : X.memory = post.memory := by rw [← hX]; rfl
  have hXc : X.code = post.code := by rw [← hX]; rfl
  have hXd : X.memaddrs = post.memaddrs := by rw [← hX]; rfl
  have hXA : ArenaReady X := by rw [← hX]; exact arenaReady_setVar _ _ _ _ pA
  refine Ret.seq_storeWv (arr + n * 8) (by rw [ev_loc]; exact hXs)
    (fun v hv => ⟨lg, by rw [ev_loc, hXlg] at hv; exact (Option.some.inj hv).symm⟩) fun w _ _ => ?_
  refine Ret.ret fun _ _ => ?_
  have hgN : ∀ g, globN (emptyLocalsHOLFinite { X with memory := updW X.memory (arr + n * 8) w }) g =
      globN post g := fun g => by unfold globN; rw [← hXg]; rfl
  refine ⟨hXc.trans pc, hXd.trans pd,
    arenaReady_locals _ _ (arenaReady_mem X _ hXA), fun k hk => ?_, ?_, arr + n * 8, d, len, ?_, ?_⟩
  · show X.globals.lookup k = _; rw [hXg]; exact pg k hk
  · rw [hgN]; exact phm
  · rw [hgN]
    rcases halt with ⟨_, h0, _, _, _⟩ | ⟨hnc, _, hl, h1, h2, _⟩
    · exact Or.inl h0
    · refine Or.inr ⟨h1, ?_⟩
      have h8 : (8 : BitVec 64).toNat = 8 := rfl
      have hnc' : n.toNat = cap.toNat := by rw [hnc]
      rw [h8] at hl h2
      omega
  · intro a ha h0 h8 h16 hs
    show updW X.memory (arr + n * 8) w a = _
    rw [updW_ne _ _ _ _ hs, hXm]
    exact pm a ha h0 h8 h16

end LstPushRun

section LogAppend2
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

/-- Rich post of `log_append` onto list header `L` holding `(arr0, n, cap)`: the header becomes
`(arr', n+1, cap')` with `n < cap'`, the array is either unchanged or a fresh heap block, and
memory changes only at the header and inside the new array `[arr', arr' + 8 cap')`. -/
def LogAppendPost2 {F : Type} (s : PanSemStateFiniteExact 64 F) (L arr0 n cap : BitVec 64)
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ ArenaReady post ∧
  (∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = s.globals.lookup k) ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
  ∃ arr' cap' : BitVec 64,
    post.memory L = .word arr' ∧ post.memory (L + 8) = .word (n + 1) ∧
    post.memory (L + 16) = .word cap' ∧ n.toNat < cap'.toNat ∧ cap'.toNat < 2 ^ 60 ∧
    ((arr' = arr0 ∧ cap' = cap) ∨
      (globN s "heap_ptr" ≤ arr'.toNat ∧ arr'.toNat + 8 * cap'.toNat ≤ globN post "heap_ptr" ∧
        cap'.toNat = 2 * n.toNat)) ∧
    arr'.toNat + 8 * cap'.toNat ≤ 2 ^ 64 ∧
    ∀ a : BitVec 64, ¬ CellHits a.toNat (arr'.toNat, 8 * cap'.toNat) → a ≠ L → a ≠ L + 8 →
      a ≠ L + 16 → post.memory a = s.memory a

theorem logAppendPost2_locIns {F : Type} (s : PanSemStateFiniteExact 64 F) (L arr0 n cap : BitVec 64) :
    LocIns (fun (_ : ValueHOL 64) t => LogAppendPost2 s L arr0 n cap t) := by
  intro v t M ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, arenaReady_locals t M h3, h4, h5, h6⟩

theorem slot_hits (arr n cap : BitVec 64) (hn : n.toNat < cap.toNat)
    (hw : arr.toNat + 8 * cap.toNat ≤ 2 ^ 64) :
    CellHits (arr + n * 8).toNat (arr.toNat, 8 * cap.toNat) := by
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  have : (arr + n * 8).toNat = arr.toNat + 8 * n.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, h8]
    rw [Nat.mod_eq_of_lt (a := n.toNat * 8) (by omega)]; omega
  unfold CellHits; simp only; omega

attribute [local irreducible] Ret in
theorem log_append_run2 {F : Type} (s : PanSemStateFiniteExact 64 F) (e L lg arr0 n cap : BitVec 64)
    (hA : ArenaReady s)
    (he : s.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : s.locals.lookup (ofString "log") = some (.val (.word lg)))
    (hd88 : s.memaddrs (e + 88)) (hmL : s.memory (e + 88) = .word L)
    (hma : s.memory L = .word arr0)
    (hmn : s.memory (L + 8) = .word n) (hmc : s.memory (L + 16) = .word cap)
    (hd0 : s.memaddrs L) (hd8 : s.memaddrs (L + 8)) (hd16 : s.memaddrs (L + 16))
    (hle : n.toNat ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 59)
    (hw : arr0.toNat + 8 * cap.toNat ≤ 2 ^ 64) (hLw : L.toNat + 24 ≤ 2 ^ 64)
    (hLd : L.toNat + 24 ≤ arr0.toNat ∨ arr0.toNat + 8 * cap.toNat ≤ L.toNat)
    (hLh : L.toNat + 24 ≤ globN s "heap_ptr" ∨ heapLimit ≤ L.toNat) (hc1 : 1 ≤ cap.toNat) :
    Ret s (sourceFnBody Guest.Software.guestFn_log_append)
      (fun _ post => LogAppendPost2 s L arr0 n cap post) := by
  have hb : sourceFnBody Guest.Software.guestFn_log_append =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_log_append).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_log_append,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.decCallL (logAppendPost2_locIns s L arr0 n cap) fun vals body cal ret v post h1 h2 h3 => ?_
  have hv : vals = [.val (.word L), .val (.word 8)] := by
    obtain ⟨v1, v2, rfl, he1, he2⟩ := evalList2_inv _ _ _ h1
    have e1 := he1.symm.trans (ev_load_loc_eq s _ e _ L he hd88 hmL)
    have e2 := he2.symm.trans (ev_const s _)
    rw [Option.some.inj e1, Option.some.inj e2]; rfl
  obtain ⟨rfl, rfl⟩ := lk2 hA.1.code (by decide) fl_lookup_lst_push L 8 hv h2
  have hAE : ArenaReady (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "l", .val (.word L))).update
        (ofString "esz", .val (.word 8)))) :=
    ⟨guestInv_callEntry _ _ hA.1, arenaOK_congr (s := s) rfl hA.2⟩
  obtain ⟨pc, pd, psh, pba, pb, pg, phm, pA, arr, d, len, pmL, rfl, pm8, halt, pm⟩ := Ret.apply
    (lst_push_run (callEntryStateHOLFinite s _) L 8 n cap hAE
      (by simp (config := {decide := true}) [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hmn hmc hd0 hd8 hd16 hle (by omega) (by decide)) h3
  generalize hX : setVarHOLFinite (ofString "slot") (.val (.word (arr + n * 8)))
    { post with locals := s.locals } = X
  have hXlg : X.locals.lookup (ofString "log") = some (.val (.word lg)) := by
    rw [← hX]
    simp (config := {decide := true}) [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlg]
  have hXs : X.locals.lookup (ofString "slot") = some (.val (.word (arr + n * 8))) := by
    rw [← hX]; exact setVar_lookup_eq _ _ _
  have hXg : X.globals = post.globals := by rw [← hX]; rfl
  have hXm : X.memory = post.memory := by rw [← hX]; rfl
  have hXc : X.code = post.code := by rw [← hX]; rfl
  have hXd : X.memaddrs = post.memaddrs := by rw [← hX]; rfl
  have hXA : ArenaReady X := by rw [← hX]; exact arenaReady_setVar _ _ _ _ pA
  refine Ret.seq_storeWv (arr + n * 8) (by rw [ev_loc]; exact hXs)
    (fun v hv => ⟨lg, by rw [ev_loc, hXlg] at hv; exact (Option.some.inj hv).symm⟩) fun w _ _ => ?_
  refine Ret.ret fun _ _ => ?_
  have hgN : ∀ g, globN (emptyLocalsHOLFinite { X with memory := updW X.memory (arr + n * 8) w }) g =
      globN post g := fun g => by unfold globN; rw [← hXg]; rfl
  have hgE : globN (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "l", .val (.word L))).update
        (ofString "esz", .val (.word 8)))) "heap_ptr" = globN s "heap_ptr" := rfl
  rw [hgE] at phm
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  have hcm : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
  have hpl : globN post "heap_ptr" ≤ 2952790016 := pA.2.2.1
  have hL8 : (L + 8).toNat = L.toNat + 8 := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by rw [h8]; omega)
  have hL16 : (L + 16).toNat = L.toNat + 16 := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by have : (16 : BitVec 64).toNat = 16 := rfl; omega)
  -- slot avoids the header whenever the array interval avoids it
  have hslot : ∀ (arr c : BitVec 64), n.toNat < c.toNat → arr.toNat + 8 * c.toNat ≤ 2 ^ 64 →
      (L.toNat + 24 ≤ arr.toNat ∨ arr.toNat + 8 * c.toNat ≤ L.toNat) →
      arr + n * 8 ≠ L ∧ arr + n * 8 ≠ L + 8 ∧ arr + n * 8 ≠ L + 16 := by
    intro arr c hn hw' hd
    have hs : (arr + n * 8).toNat = arr.toNat + 8 * n.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_mul, h8]
      rw [Nat.mod_eq_of_lt (a := n.toNat * 8) (by omega)]; omega
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      have := congrArg BitVec.toNat h <;> simp only [hs, hL8, hL16] at this <;> omega
  rcases halt with ⟨hlt, rfl, rfl, hma', hm16⟩ | ⟨hnc, rfl, rfl, h1, h2, hm16⟩
  · -- no growth
    have harr : arr = arr0 := by
      have := hma'.symm.trans hma
      cases this; rfl
    subst harr
    obtain ⟨s0, s8, s16⟩ := hslot arr cap hlt hw hLd
    refine ⟨hXc.trans pc, hXd.trans pd, arenaReady_locals _ _ (arenaReady_mem X _ hXA),
      fun k hk => ?_, by rw [hgN]; exact phm, arr, cap, ?_, ?_, ?_, hlt, by omega, Or.inl ⟨rfl, rfl⟩,
      hw, ?_⟩
    · show X.globals.lookup k = _; rw [hXg]; exact pg k hk
    · show updW X.memory _ w L = _; rw [updW_ne _ _ _ _ (Ne.symm s0), hXm]; exact pmL
    · show updW X.memory _ w (L + 8) = _; rw [updW_ne _ _ _ _ (Ne.symm s8), hXm]; exact pm8
    · show updW X.memory _ w (L + 16) = _; rw [updW_ne _ _ _ _ (Ne.symm s16), hXm]; exact hm16
    · intro a ha h0 h8' h16
      have hs : a ≠ arr + n * 8 := fun h => ha (h ▸ slot_hits arr n cap hlt hw)
      show updW X.memory (arr + n * 8) w a = _
      rw [updW_ne _ _ _ _ hs, hXm]
      exact pm a (fun h => by have h2 := h.2; simp at h2) h0 h8' h16
  · -- growth: n = cap, new array of 2 cap words
    subst hnc
    rw [hgE] at h1; simp only [h8] at h2
    have hc2 : (n * 2).toNat = 2 * n.toNat := by
      rw [BitVec.toNat_mul]; have : (2 : BitVec 64).toNat = 2 := rfl
      rw [this]; exact (Nat.mod_eq_of_lt (by omega)).trans (by ring)
    have hw2 : arr.toNat + 8 * (n * 2).toNat ≤ 2 ^ 64 := by rw [hc2]; omega
    have hlt2 : n.toNat < (n * 2).toNat := by
      rw [hc2]
      have : 0 < n.toNat := by
        rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
        · exfalso; omega
        · exact h0
      omega
    have hd' : L.toNat + 24 ≤ arr.toNat ∨ arr.toNat + 8 * (n * 2).toNat ≤ L.toNat := by
      rw [hc2]
      rcases hLh with h | h
      · left; omega
      · right; unfold heapLimit at h; have : scratchStart = 2952790016 := rfl; omega
    obtain ⟨s0, s8, s16⟩ := hslot arr (n * 2) hlt2 hw2 hd'
    refine ⟨hXc.trans pc, hXd.trans pd, arenaReady_locals _ _ (arenaReady_mem X _ hXA),
      fun k hk => ?_, by rw [hgN]; exact phm, arr, n * 2, ?_, ?_, ?_, hlt2, by rw [hc2]; omega,
      Or.inr ⟨h1, by rw [hgN, hc2]; omega, hc2⟩, hw2, ?_⟩
    · show X.globals.lookup k = _; rw [hXg]; exact pg k hk
    · show updW X.memory _ w L = _; rw [updW_ne _ _ _ _ (Ne.symm s0), hXm]; exact pmL
    · show updW X.memory _ w (L + 8) = _; rw [updW_ne _ _ _ _ (Ne.symm s8), hXm]; exact pm8
    · show updW X.memory _ w (L + 16) = _; rw [updW_ne _ _ _ _ (Ne.symm s16), hXm]; exact hm16
    · intro a ha h0 h8' h16
      have hs : a ≠ arr + n * 8 := fun h => ha (h ▸ slot_hits arr n (n * 2) hlt2 hw2)
      show updW X.memory (arr + n * 8) w a = _
      rw [updW_ne _ _ _ _ hs, hXm]
      refine pm a (fun h => ha ?_) h0 h8' h16
      unfold CellHits at h ⊢; simp only [h8] at h ⊢; rw [hc2]; omega

end LogAppend2

section LogLoop
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

theorem fl_lookup_log_append :
    originalRuntimeCode.lookup (ofString "log_append") =
      some ([(ofString "e", .one), (ofString "log", .one)],
        sourceFnBody Guest.Software.guestFn_log_append, .one) :=
  lookup_of_guestAst_getElem 523 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_log_append) rfl

/-- Invariant of the `log_append` loop of `incorporate_child_on_success`: the parent's logs list
`L` (at `e+88`) holds `n0 + i` entries in an array that is the original one or fresh heap; memory
changes only at the header, in the original array and in fresh heap. -/
def LAInv {F : Type} (s : PanSemStateFiniteExact 64 F) (L arr0 cap0 n0 nc : BitVec 64)
    (u : PanSemStateFiniteExact 64 F) : Prop :=
  u.code = s.code ∧ u.memaddrs = s.memaddrs ∧ ArenaReady u ∧
  (∀ k : MlS, k ≠ ofString "heap_ptr" → u.globals.lookup k = s.globals.lookup k) ∧
  globN s "heap_ptr" ≤ globN u "heap_ptr" ∧
  u.locals.lookup (ofString "n") = some (.val (.word nc)) ∧
  ∃ i arr cap : BitVec 64, u.locals.lookup (ofString "i") = some (.val (.word i)) ∧
    i.toNat ≤ nc.toNat ∧
    u.memory L = .word arr ∧ u.memory (L + 8) = .word (n0 + i) ∧ u.memory (L + 16) = .word cap ∧
    (n0 + i).toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 59 ∧ 1 ≤ cap.toNat ∧
    arr.toNat + 8 * cap.toNat ≤ 2 ^ 64 ∧
    ((arr = arr0 ∧ cap = cap0) ∨
      (globN s "heap_ptr" ≤ arr.toNat ∧ arr.toNat + 8 * cap.toNat ≤ globN u "heap_ptr")) ∧
    ∀ a : BitVec 64, ¬ CellHits a.toNat (arr0.toNat, 8 * cap0.toNat) →
      ¬ CellHits a.toNat (globN s "heap_ptr", globN u "heap_ptr" - globN s "heap_ptr") →
      a ≠ L → a ≠ L + 8 → a ≠ L + 16 → u.memory a = s.memory a

theorem la_active {F : Type} (t : PanSemStateFiniteExact 64 F) (i nc : BitVec 64)
    (hi : t.locals.lookup (ofString "i") = some (.val (.word i)))
    (hn : t.locals.lookup (ofString "n") = some (.val (.word nc)))
    (hle : i.toNat ≤ nc.toNat) (hnc : nc.toNat < 2 ^ 63)
    (h : InitECandidate.Solver.Wave8M19.LoopActive
      (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) t) :
    i.toNat < nc.toNat := by
  obtain ⟨c, hc, hnz⟩ := h
  change evalAt t _ = _ at hc
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp t .less _ _ c hc
  simp [evalAt, evalHOLExact, hn, hi] at ha hb
  subst ha hb hcw
  by_contra hge
  apply hnz
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Flapjack.Compiler.Encoders.Asm.holAsmSignedLess]
  intro h1; split at h1 <;> omega

attribute [local irreducible] Ret in
theorem la_step {F : Type} (s : PanSemStateFiniteExact 64 F) (e L arr0 cap0 n0 nc : BitVec 64)
    (a2 : ExpHOL 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hd88 : s.memaddrs (e + 88)) (hm88 : s.memory (e + 88) = .word L)
    (h88 : ¬ CellHits (e + 88).toNat (arr0.toNat, 8 * cap0.toNat) ∧
      ((e + 88).toNat + 8 ≤ globN s "heap_ptr" ∨ heapLimit ≤ (e + 88).toNat) ∧
      e + 88 ≠ L ∧ e + 88 ≠ L + 8 ∧ e + 88 ≠ L + 16)
    (hd0 : s.memaddrs L) (hd8 : s.memaddrs (L + 8)) (hd16 : s.memaddrs (L + 16))
    (hLw : L.toNat + 24 ≤ 2 ^ 64)
    (hLd : L.toNat + 24 ≤ arr0.toNat ∨ arr0.toNat + 8 * cap0.toNat ≤ L.toNat)
    (hLh : L.toNat + 24 ≤ globN s "heap_ptr" ∨ heapLimit ≤ L.toNat)
    (hsum : n0.toNat + nc.toNat < 2 ^ 58)
    (ha2 : ∀ (t : PanSemStateFiniteExact 64 F) v, ev t a2 = some v → ∃ w, v = .val (.word w))
    (u : PanSemStateFiniteExact 64 F) (hu : LAInv s L arr0 cap0 n0 nc u)
    (hact : InitECandidate.Solver.Wave8M19.LoopActive
      (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) u) :
    Flw (decClockHOLFinite u)
      (.seq (.call (some (none, none)) (ofString "log_append") [.var .global (ofString "ev"), a2])
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun _ t => LAInv s L arr0 cap0 n0 nc t) := by
  obtain ⟨uc, ud, uA, ug, uh, un, i, arr, cap, ui, hile, umL, um8, um16, hle, hcap, hc1, hw,
    hold, ufr⟩ := hu
  have hilt := la_active u i nc ui un hile (by omega) hact
  have hcl : ∀ k, k < 2 ^ 59 → True := fun _ _ => trivial
  have hn0i : (n0 + i).toNat = n0.toNat + i.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hHL : heapLimit = 2952790016 := rfl
  have hhu : globN u "heap_ptr" ≤ 2952790016 := uA.2.2.1
  -- the frame of `u` gives the `e+88` cell
  have hfr88 : u.memory (e + 88) = .word L := by
    rw [ufr _ h88.1 (by unfold CellHits; simp only; rcases h88.2.1 with h | h <;> omega)
      h88.2.2.1 h88.2.2.2.1 h88.2.2.2.2]; exact hm88
  have hLd' : L.toNat + 24 ≤ arr.toNat ∨ arr.toNat + 8 * cap.toNat ≤ L.toNat := by
    rcases hold with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
    · exact hLd
    · rcases hLh with h | h <;> omega
  generalize hU : decClockHOLFinite u = U
  have hUc : U.code = u.code := by rw [← hU]; rfl
  have hUd : U.memaddrs = u.memaddrs := by rw [← hU]; rfl
  have hUm : U.memory = u.memory := by rw [← hU]; rfl
  have hUg : U.globals = u.globals := by rw [← hU]; rfl
  have hUl : U.locals = u.locals := by rw [← hU]; rfl
  have hUA : ArenaReady U := by
    rw [← hU]; exact ⟨guestInv_congr (s := u) rfl rfl rfl rfl uA.1, arenaOK_congr (s := u) rfl uA.2⟩
  have hgU : ∀ g, globN U g = globN u g := fun g => by unfold globN; rw [hUg]
  have hUe : U.globals.lookup (ofString "ev") = some (.val (.word e)) := by
    rw [hUg, ug _ (by decide)]; exact he
  refine Flw.seq_call00 fun values body callee ret v cpost h1 h2 h3 => ?_
  obtain ⟨v1, v2, rfl, he1, he2⟩ := evalList2_inv _ _ _ h1
  have hv1 : v1 = .val (.word e) := by
    simp [ev, evalHOLExact, hUe] at he1; exact he1.symm
  obtain ⟨lg, rfl⟩ := ha2 U v2 he2
  subst hv1
  obtain ⟨rfl, rfl⟩ := lk2 (hUc.trans uA.1.code) (by decide) fl_lookup_log_append e lg rfl h2
  have hAE : ArenaReady (callEntryStateHOLFinite U
      ((HolFiniteMapExact.empty.update (ofString "e", .val (.word e))).update
        (ofString "log", .val (.word lg)))) :=
    ⟨guestInv_callEntry _ _ hUA.1, arenaOK_congr (s := U) rfl hUA.2⟩
  have hgE : ∀ g, globN (callEntryStateHOLFinite U
      ((HolFiniteMapExact.empty.update (ofString "e", .val (.word e))).update
        (ofString "log", .val (.word lg)))) g = globN u g := fun g => by
    rw [← hgU g]; rfl
  have hcap' : cap.toNat < 2 ^ 59 := hcap
  obtain ⟨pc, pd, pA, pg, ph, arr', cap', pmL, pm8, pm16, plt, _, pold, pw, pfr⟩ := Ret.apply
    (log_append_run2 (callEntryStateHOLFinite U _) e L lg arr (n0 + i) cap hAE
      (by simp (config := {decide := true}) [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by change U.memaddrs _; rw [hUd, ud]; exact hd88)
      (by change U.memory _ = _; rw [hUm]; exact hfr88)
      (by change U.memory _ = _; rw [hUm]; exact umL)
      (by change U.memory _ = _; rw [hUm]; exact um8)
      (by change U.memory _ = _; rw [hUm]; exact um16)
      (by change U.memaddrs _; rw [hUd, ud]; exact hd0)
      (by change U.memaddrs _; rw [hUd, ud]; exact hd8)
      (by change U.memaddrs _; rw [hUd, ud]; exact hd16)
      hle hcap' hw hLw hLd' (by rw [hgE]; rcases hLh with h | h <;> [left; right] <;> omega) hc1) h3
  rw [hgE] at ph pold
  apply Flw.assign
  intro v hv
  have hvi : v = .val (.word (i + 1)) := by
    rw [ev_addr _ (ofString "i") i 1 (by change U.locals.lookup _ = _; rw [hUl]; exact ui)] at hv
    exact (Option.some.inj hv).symm
  subst hvi
  have hpg : ∀ g, globN (setVarHOLFinite (ofString "i") (.val (.word (i + 1)))
      { cpost with locals := U.locals }) g = globN cpost g := fun g => by unfold globN; rfl
  have hi1 : (i + 1).toNat = i.toNat + 1 := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega)
  have hn1 : n0 + (i + 1) = n0 + i + 1 := by rw [BitVec.add_assoc]
  refine ⟨pc.trans (hUc.trans uc), pd.trans (hUd.trans ud),
    arenaReady_setVar _ _ _ _ pA, fun k hk => ?_, by rw [hpg]; omega, ?_,
    i + 1, arr', cap', ?_, by omega, pmL, by rw [hn1]; exact pm8, pm16, ?_, ?_, by omega, pw, ?_, ?_⟩
  · change cpost.globals.lookup k = _
    rw [pg k hk]; change U.globals.lookup k = _; rw [hUg]; exact ug k hk
  · simp (config := {decide := true}) [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hUl, un]
  · exact setVar_lookup_eq _ _ _
  · rw [hn1, BitVec.toNat_add]; rw [Nat.mod_eq_of_lt (by simp; omega)]; simp; omega
  · rcases pold with ⟨rfl, rfl⟩ | ⟨_, _, hc2⟩
    · exact hcap
    · omega
  · rw [hpg]
    rcases pold with ⟨rfl, rfl⟩ | ⟨h1, h2, _⟩
    · rcases hold with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by omega⟩
    · exact Or.inr ⟨by omega, h2⟩
  · intro a ha0 hah h0 h8 h16
    rw [hpg] at hah
    change cpost.memory a = _
    have hna : ¬ CellHits a.toNat (arr'.toNat, 8 * cap'.toNat) := by
      intro hc
      unfold CellHits at hc ha0 hah; simp only at hc ha0 hah
      rcases pold with ⟨rfl, rfl⟩ | ⟨h1, h2, _⟩
      · rcases hold with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
        · exact ha0 hc
        · omega
      · omega
    rw [pfr a hna h0 h8 h16]
    change U.memory a = _; rw [hUm]
    refine ufr a ha0 ?_ h0 h8 h16
    unfold CellHits at hah ⊢; simp only at hah ⊢; omega

end LogLoop

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

/-! The pop only needs preservation at the byte keys actually queried by the
world and frame invariants. String-name inequality is insufficient for this. -/
open EvmEkFk in
theorem evmInvAt_of_pop_keys {F : Type} {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hne : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hAp : ArenaReady post) (hm : post.memory = s.memory)
    (hdom : post.memaddrs = s.memaddrs) (hbe : post.be = s.be)
    (hev : globN post "ev" = memW s (globN s "cur_cont"))
    (hcc : globN post "cur_cont" = memW s (globN s "cur_cont" + 8))
    (hg : ∀ name : String, ofString name ≠ ofString "ev" →
      ofString name ≠ ofString "cur_cont" → globN post name = globN s name) :
    ∃ S' : List Nat,
      (∀ t ∈ S', t ∈ S) ∧
      ((S' = S ∧ ¬ DelExclusive s S (evmChain s) 0 (memW s (globN s "ev" + 136))) ∨
        (S' = S.filter (· != memW s (globN s "ev" + 136)) ∧
        DelExclusive s S (evmChain s) 0 (memW s (globN s "ev" + 136)))) ∧
      InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S' ∧
      evmChain post = (evmChain s).tail ∧
      R11Shards.OpDispatchSpec.evmR post +
        (memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) =
        R11Shards.OpDispatchSpec.evmR s := by
  have hmw : ∀ a, memW post a = memW s a := fun a => by unfold memW; rw [hm]
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  have hch_post : evmChain post = (evmChain s).tail :=
    evmChain_pop_eq_tail hne hch_last hm hev hcc
  have hcons := evmChain_cons_of_cont_ne_zero hne
  set chTail := evmChainFrom s maxChain (memW s (globN s "cur_cont"))
    (memW s (globN s "cur_cont" + 8))
  have htail_eq : (evmChain s).tail = chTail := by rw [hcons]; rfl
  have htail_ne : (evmChain s).tail ≠ [] := by
    rw [htail_eq]; dsimp only [chTail]
    have hmc : maxChain = (maxChain - 1) + 1 := by decide
    rw [hmc]; simp [evmChainFrom]
  have hlen_cons : (evmChain s).length = (evmChain s).tail.length + 1 := by
    conv_lhs => rw [hcons]
    simp [← htail_eq]
  have h01 : 0 + 1 < (evmChain s).length := by
    have : 0 < (evmChain s).tail.length := List.length_pos_of_ne_nil htail_ne
    omega
  have hch0_eq : (evmChain s)[0]'(by omega) = (globN s "ev", globN s "cur_cont") := by simp [hcons]
  set t0 := memW s (globN s "ev" + 136)
  have ht0_ch0 : memW s (((evmChain s)[0]'(by omega)).1 + 136) = t0 := by rw [hch0_eq]
  open Classical in
  let S' : List Nat := if DelExclusive s S (evmChain s) 0 t0 then S.filter (· != t0) else S
  have hS'_sub : ∀ t ∈ S', t ∈ S := by
    intro t ht; dsimp only [S'] at ht; split at ht
    · exact (List.mem_filter.mp ht).1
    · exact ht
  have hS'_cases : (S' = S ∧ ¬ DelExclusive s S (evmChain s) 0 t0) ∨
      (S' = S.filter (· != t0) ∧ DelExclusive s S (evmChain s) 0 t0) := by
    dsimp only [S']; split
    · rename_i hD; exact Or.inr ⟨rfl, hD⟩
    · rename_i hnD; exact Or.inl ⟨rfl, hnD⟩
  have hW_S' : WorldTyped s S' := by
    rcases hS'_cases with ⟨hEq, _⟩ | ⟨hEq, hD0⟩
    · rw [hEq]; exact hW
    · rw [hEq]; exact worldTyped_filter_del hW hD0 hRoles (by omega) ht0_ch0
  have hwtr_S' : worldTableRefs s S' = worldTableRefs s S := by
    rcases hS'_cases with ⟨hEq, _⟩ | ⟨hEq, hD0⟩
    · rw [hEq]
    · rw [hEq]; exact worldTableRefs_filter_del_eq hD0.1
  have hframe_in_S' : ∀ ec ∈ (evmChain s).tail, ∀ k ∈ ([136, 168, 176] : List Nat),
      memW s (ec.1 + k) ∈ S' := by
    intro ec hec k hk
    have hinS : memW s (ec.1 + k) ∈ S := by
      have hFW := hFW_all ec (List.mem_of_mem_tail hec)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact hFW.2.2.2.2.2.2.2.1
      · exact hFW.2.2.2.2.2.2.2.2.1
      · exact hFW.2.2.2.2.2.2.2.2.2.1
    rcases hS'_cases with ⟨hEq, _⟩ | ⟨hEq, hD0⟩
    · rw [hEq]; exact hinS
    · rw [hEq]
      refine List.mem_filter.mpr ⟨hinS, bne_iff_ne.mpr ?_⟩
      intro heq
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hec
      have hj_s : j + 1 < (evmChain s).length := by omega
      have hget_j : (evmChain s)[j + 1] = ((evmChain s).tail)[j] := by simp [List.getElem_tail]
      have := (hD0.2 (j + 1) hj_s k hk (by rw [hget_j]; exact heq)).2
      omega
  have htail_sub : ∀ ec ∈ (evmChain s).tail, ec ∈ evmChain s := fun _ h => List.mem_of_mem_tail h
  have hcg : ∀ g ∈ InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals,
      globN post g = globN s g := by
    intro g hg_in
    have hn : ofString g ≠ ofString "ev" ∧ ofString g ≠ ofString "cur_cont" := by
      revert g hg_in; decide
    exact hg g hn.1 hn.2
  obtain ⟨Nd_w, hWT⟩ := (worldTyped_iff_with s S').mp hW_S'
  have hcell_w : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S' Nd_w := by
    refine ⟨hbe, hdom, hAs.1.memaddrs, ?_, ?_, ?_⟩
    · intro a _; rw [hm]
    · intro a _ _ _; rw [hm]
    · intro b _ _; unfold memB; rw [hm, hbe]
  have hhh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hg "heap_ptr" (by decide) (by decide)]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hg "scratch_ptr" (by decide) (by decide)]
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [InitECandidate.Solver.Wave8Contracts.M23.blockOutObjects_eq hAs.2 hWT.2.2.1 hcell_w
          (hg "bo" (by decide) (by decide)),
        InitECandidate.Solver.Wave8Contracts.M23.balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell_w
          (hg "bal_accounts" (by decide) (by decide)),
        hg "journal" (by decide) (by decide), hg "journal_cap" (by decide) (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hn : ofString gn.1 ≠ ofString "ev" ∧ ofString gn.1 ≠ ofString "cur_cont" := by revert gn hgn; decide
    rw [hg gn.1 hn.1 hn.2]
  have hFT_post : FixedTyped post := InitECandidate.Solver.Wave8Contracts.M23.fixedTyped_of_eq hAp hWT.2.2.1 hhh hsc hfeq
  obtain ⟨hWT_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
    hAs hAp hhh hsc hcg hcell_w hWT ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S' := (worldTyped_iff_with post S').mpr ⟨Nd_w, hWT_post⟩
  have hfp_eq : ∀ t, htabFootprint post t = htabFootprint s t := by intro t; unfold htabFootprint hdr; simp only [hmw]
  have hfo_eq : ∀ ec, frameObjects post ec = frameObjects s ec := by
    intro ec
    unfold frameObjects frameLogs frameRet frameLogObjects logOwnedIvls logRecordIvls
    simp only [hmw, hg "vm_system_address" (by decide) (by decide)]
  have hfs_eq : ∀ ec, frameScratch post ec = frameScratch s ec := by intro ec; unfold frameScratch; simp only [hmw]
  have hwok : ∀ {o : Ivl}, WordsOK s o → WordsOK post o := by
    intro o ⟨h1, h2, hk⟩
    refine ⟨h1, h2, fun k hklt => ?_⟩
    obtain ⟨w, hdom_k, hmem_k⟩ := hk k hklt
    exact ⟨w, by rwa [hdom], by rwa [hm]⟩
  have hwtr_post : worldTableRefs post S' = worldTableRefs s S' := by
    have hgtr : globalTableRoots.map (globN post) = globalTableRoots.map (globN s) := by
      apply List.map_congr_left
      intro g hgi
      have hn : ofString g ≠ ofString "ev" ∧ ofString g ≠ ofString "cur_cont" := by revert g hgi; decide
      exact hg g hn.1 hn.2
    unfold worldTableRefs recordSlots balRecords htabValues hdr nodeF
    simp only [hmw, hgtr, hg "ws" (by decide) (by decide), hg "bs" (by decide) (by decide),
      hg "ts" (by decide) (by decide), hg "bal_accounts" (by decide) (by decide),
      hg "journal" (by decide) (by decide), hg "journal_n" (by decide) (by decide)]
  have hwr_post : worldRoleSlots post = worldRoleSlots s := by
    unfold worldRoleSlots recRoles nestRoles balRecords
    simp only [hmw, hg "ws" (by decide) (by decide), hg "bs" (by decide) (by decide),
      hg "ts" (by decide) (by decide), hg "bal_accounts" (by decide) (by decide),
      hg "bal_idx_accts" (by decide) (by decide), hg "bal_idx_stor" (by decide) (by decide)]
    unfold htabValues hdr nodeF
    simp only [hmw]
  have hjr_post : journalRoleSlots post = journalRoleSlots s := by
    unfold journalRoleSlots journalRole
    simp only [hmw, hg "journal_n" (by decide) (by decide), hg "journal" (by decide) (by decide), hg "ts" (by decide) (by decide)]
  have hfrs_post : frameRoleSlots post ((evmChain s).tail) = frameRoleSlots s ((evmChain s).tail) := by unfold frameRoleSlots; simp only [hmw]
  have hR_sum : R11Shards.OpDispatchSpec.evmR post +
      (memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) = R11Shards.OpDispatchSpec.evmR s := by
    unfold R11Shards.OpDispatchSpec.evmR
    rw [hch_post]
    conv_rhs => rw [hcons]
    simp only [List.map_cons, List.sum_cons, htail_eq, hmw]
    omega
  refine ⟨S', hS'_sub, hS'_cases, ⟨hW_post, ?_⟩, hch_post, hR_sum⟩
  dsimp only; rw [hch_post]
  refine ⟨htail_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcons, List.length_cons] at hch_len
    rw [htail_eq]; omega
  · obtain ⟨ecL, hecL, hk0⟩ := hch_last
    rw [hcons, List.getLast?_cons_of_ne_nil (htail_eq ▸ htail_ne)] at hecL
    exact ⟨ecL, by rwa [htail_eq], by rw [hmw]; exact hk0⟩
  · intro ec hec
    have hFW := hFW_all ec (htail_sub ec hec)
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, _, _, _, c11, c12, c13, c14, c15, c16, c17⟩ := hFW
    have c8' : memW s (ec.1 + 136) ∈ S' := hframe_in_S' ec hec 136 (by simp)
    have c9' : memW s (ec.1 + 168) ∈ S' := hframe_in_S' ec hec 168 (by simp)
    have c10' : memW s (ec.1 + 176) ∈ S' := hframe_in_S' ec hec 176 (by simp)
    unfold FrameWF; dsimp only
    simp only [hmw, hg "scratch_ptr" (by decide) (by decide), hg "frame_mem_ptr" (by decide) (by decide),
      hg "heap_ptr" (by decide) (by decide), hg "evm_empty" (by decide) (by decide)]
    have hfl_eq : frameLogs post ec = frameLogs s ec := by unfold frameLogs; simp [hmw]
    have hfr_eq : frameRet post ec = frameRet s ec := by unfold frameRet; simp [hmw]
    rw [hfl_eq, hfr_eq]
    refine ⟨fun i hi => ⟨(c1 i hi).1, hwok (c1 i hi).2⟩, c2, hwok c3,
      c4, c5, c6, c7, c8', c9', c10', c11, c12, c13, hwok c14, ?_, ?_, ?_⟩
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, hwok hw⟩
    · rcases c16 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨hwok hw_l, InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hhh hsc hal_l,
          by simpa [hmw] using hlt28, by simpa [hmw] using hle_cap, fun i hi => ?_⟩
        rw [hmw] at hi
        obtain ⟨⟨w_i, hdom_i, hmem_i⟩, hle⟩ := hent i hi
        refine ⟨⟨w_i, by simpa [hmw] using (hdom ▸ hdom_i), by simpa [hmw] using (hm ▸ hmem_i)⟩, ?_⟩
        unfold LogEntryOK at hle ⊢
        simp only [hmw, hg "heap_ptr" (by decide) (by decide)]
        exact ⟨hwok hle.1, hle.2⟩
    · obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
      have hTr_m' : TriesTypedWith s S' Nd_m := by
        refine ⟨hTr_m.1, fun o ho => ⟨fun t ht => (hTr_m.2.1 o ho).1 t (hS'_sub t ht), (hTr_m.2.1 o ho).2⟩,
          fun hnz => ⟨(hTr_m.2.2 hnz).1, fun hin => (hTr_m.2.2 hnz).2 (hS'_sub _ hin)⟩⟩
      have hcell_m : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S' Nd_m := by
        refine ⟨hbe, hdom, hAs.1.memaddrs, ?_, ?_, ?_⟩
        · intro a _; rw [hm]
        · intro a _ _ _; rw [hm]
        · intro b _ _; unfold memB; rw [hm, hbe]
      obtain ⟨hWT_m_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
        hAs hAp hhh hsc hcg hcell_m ⟨hW_S'.1, hW_S'.2.1, hW_S'.2.2.1, hTr_m'⟩
        ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
      refine ⟨InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hhh hsc hal_m, hwok hw_m,
        fun t ht i hi => by rw [hfp_eq] at hi; exact hdt t (hS'_sub t ht) i hi,
        by rw [hfeq]; exact hdf,
        fun ec' hec' o ho => by rw [hch_post] at hec'; rw [hfo_eq] at ho; exact hdfo ec' (htail_sub ec' hec') o ho,
        Nd_m, hWT_m_post.2.2.2, fun o ho j hj => ?_⟩
      rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_m'.1 hcell_m] at hj
      exact hdj_m o ho j hj
  · intro ec hec
    have hec_tail : ec ∈ (evmChain s).tail := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [hmw, hmw]
    exact hFR_all ec hec_tail
  · intro i hi
    have hi_s : (i + 1) + 1 < (evmChain s).length := by omega
    have hrw := hRW (i + 1) hi_s
    have hget0 : ((evmChain s).tail)[i] = (evmChain s)[i + 1] := by simp [List.getElem_tail]
    have hget1 : ((evmChain s).tail)[i + 1] = (evmChain s)[i + 2] := by simp [List.getElem_tail]
    simp only [hmw, hget0, hget1]
    exact hrw
  · rw [show ((evmChain s).tail.map (frameObjects post)) = ((evmChain s).tail.map (frameObjects s)) from
      List.map_congr_left (fun ec _ => hfo_eq ec)]
    conv at hFO_pw => rw [hcons, List.map_cons, List.flatten_cons]
    rw [htail_eq]
    exact (List.pairwise_append.mp hFO_pw).2.1
  · intro ec hec o ho
    rw [hfo_eq] at ho
    obtain ⟨hd1, hd2⟩ := hFO_disj ec (htail_sub ec hec) o ho
    exact ⟨fun t ht i hi => by rw [hfp_eq] at hi; exact hd1 t (hS'_sub t ht) i hi,
      fun j hj => by rw [hfeq] at hj; exact hd2 j hj⟩
  · obtain ⟨Nd_a, hTr_a, hdj_a⟩ := hAT
    have hTr_a' : TriesTypedWith s S' Nd_a := by
      refine ⟨hTr_a.1, fun o ho => ⟨fun t ht => (hTr_a.2.1 o ho).1 t (hS'_sub t ht), (hTr_a.2.1 o ho).2⟩,
        fun hnz => ⟨(hTr_a.2.2 hnz).1, fun hin => (hTr_a.2.2 hnz).2 (hS'_sub _ hin)⟩⟩
    have hcell_a : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S' Nd_a := by
      refine ⟨hbe, hdom, hAs.1.memaddrs, ?_, ?_, ?_⟩
      · intro a _; rw [hm]
      · intro a _ _ _; rw [hm]
      · intro b _ _; unfold memB; rw [hm, hbe]
    obtain ⟨hWT_a_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
      hAs hAp hhh hsc hcg hcell_a ⟨hW_S'.1, hW_S'.2.1, hW_S'.2.2.1, hTr_a'⟩
      ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
    refine ⟨Nd_a, hWT_a_post.2.2.2, fun o ho j hj => ?_⟩
    rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_a'.1 hcell_a] at hj
    obtain ⟨os, hos, ho'⟩ := List.mem_flatten.mp ho
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp hos
    rw [hfo_eq] at ho'
    exact hdj_a o (List.mem_flatten.mpr ⟨frameObjects s ec,
      List.mem_map.mpr ⟨ec, htail_sub ec hec, rfl⟩, ho'⟩) j hj
  · intro i hi
    have hi_s : (i + 1) + 1 < (evmChain s).length := by omega
    have hM := hMarks (i + 1) hi_s
    have hget_i : ((evmChain s).tail)[i] = (evmChain s)[i + 1] := by simp [List.getElem_tail]
    dsimp only at hM ⊢
    simp only [hget_i, hmw, hfs_eq, hfeq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_s : j + 1 < (evmChain s).length := by omega
      have hget_j : ((evmChain s).tail)[j] = (evmChain s)[j + 1] := by simp [List.getElem_tail]
      have hfl_j : frameLogs post (((evmChain s).tail)[j]) = frameLogs s ((evmChain s)[j + 1]) := by
        rw [hget_j]; unfold frameLogs; simp [hmw]
      rw [hfo_eq, hfl_j, hget_j]
      exact m5 (j + 1) hj_s (by omega)
    · intro t ht'
      have ht := hS'_sub t ht'
      rw [hfp_eq t]
      rcases m8 t ht with ⟨htake_in, hdelEx⟩ | hfp_in
      · have htake_split : ((evmChain s).take (i + 2)).map (fun ec => memW s (ec.1 + 136)) =
            t0 :: (((evmChain s).tail.take (i + 1)).map (fun ec => memW s (ec.1 + 136))) := by
          conv_lhs => rw [hcons, List.take_succ_cons, List.map_cons]
          simp [htail_eq, t0]
        rw [htake_split, List.mem_cons] at htake_in
        by_cases hmem_tail : t ∈ ((evmChain s).tail.take (i + 1)).map (fun ec => memW s (ec.1 + 136))
        · left
          refine ⟨hmem_tail, ?_⟩
          unfold DelExclusive
          rw [hwtr_post, hwtr_S']
          refine ⟨hdelEx.1, fun j hj k hk heq => ?_⟩
          rw [hmw] at heq
          have hj_s : j + 1 < (evmChain s).length := by omega
          have hget_j : (evmChain s)[j + 1] = ((evmChain s).tail)[j] := by simp [List.getElem_tail]
          obtain ⟨hk136, hjle⟩ := hdelEx.2 (j + 1) hj_s k hk (by rw [hget_j]; exact heq)
          exact ⟨hk136, by omega⟩
        · rcases htake_in with rfl | hmem_t
          · have hD0 : DelExclusive s S (evmChain s) 0 t0 := by
              refine ⟨hdelEx.1, fun j hj k hk heq => ?_⟩
              obtain ⟨hk136, hjle⟩ := hdelEx.2 j hj k hk heq
              refine ⟨hk136, ?_⟩
              by_cases hj0 : j = 0
              · omega
              · exfalso; apply hmem_tail
                have hjm1 : j - 1 < i + 1 := by omega
                have hjm1_len : j - 1 < (evmChain s).tail.length := by omega
                have hget : ((evmChain s).tail)[j - 1] = (evmChain s)[j] := by
                  simp [List.getElem_tail, Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
                apply List.mem_map.mpr
                refine ⟨((evmChain s).tail)[j - 1], ?_, ?_⟩
                · rw [List.mem_take_iff_getElem]
                  exact ⟨j - 1, by omega, rfl⟩
                · rw [hget, ← hk136]; exact heq
            have ht0_in : t0 ∈ S.filter (· != t0) := by
              have hEq' : S' = S.filter (· != t0) := if_pos hD0
              rw [← hEq']; exact ht'
            exact absurd rfl (bne_iff_ne.mp (List.mem_filter.mp ht0_in).2)
          · exact absurd hmem_t hmem_tail
      · exact Or.inr hfp_in
  · rw [hwr_post, hfrs_post, hjr_post]
    have hfrs_sub : ∀ a ∈ frameRoleSlots s ((evmChain s).tail), a ∈ frameRoleSlots s (evmChain s) := by
      intro a ha; unfold frameRoleSlots at ha ⊢
      obtain ⟨ec, hec, ha'⟩ := List.mem_flatMap.mp ha
      exact List.mem_flatMap.mpr ⟨ec, htail_sub ec hec, ha'⟩
    have hsl_sub : ∀ a ∈ worldRoleSlots s ++ frameRoleSlots s ((evmChain s).tail),
        a ∈ worldRoleSlots s ++ frameRoleSlots s (evmChain s) := by
      intro a ha
      rcases List.mem_append.mp ha with hwr | hfr
      · exact List.mem_append_left _ hwr
      · exact List.mem_append_right _ (hfrs_sub a hfr)
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨haS, hkl⟩ := hRoles.1 a (by
        rcases List.mem_append.mp ha with hsl | hjr
        · exact List.mem_append_left _ (hsl_sub a hsl)
        · exact List.mem_append_right _ hjr)
      have haS' : a.1 ∈ S' := by
        rcases List.mem_append.mp ha with hsl | hjr
        · rcases List.mem_append.mp hsl with hwr | hfr
          · exact (hW_S'.1.2.2.2.2.2.2.2.2.2.2.2.1 a (List.mem_append_left _ hwr)).1
          · unfold frameRoleSlots at hfr
            obtain ⟨ec, hec, ha'⟩ := List.mem_flatMap.mp hfr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
            rcases ha' with rfl | rfl | rfl
            · exact hframe_in_S' ec hec 136 (by simp)
            · exact hframe_in_S' ec hec 168 (by simp)
            · exact hframe_in_S' ec hec 176 (by simp)
        · exact (hW_S'.1.2.2.2.2.2.2.2.2.2.2.2.1 a (List.mem_append_right _ hjr)).1
      have hhdr_eq : hdr post a.1 0 = hdr s a.1 0 := by unfold hdr; simp [hmw]
      exact ⟨haS', hhdr_eq.trans hkl⟩
    · have hpw_all := List.pairwise_append.mp hRoles.2.1
      have hpw_frs : (frameRoleSlots s ((evmChain s).tail)).Pairwise
          (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := by
        have hfrs_cons : frameRoleSlots s (evmChain s) =
            frameRoleSlots s [(globN s "ev", globN s "cur_cont")] ++ frameRoleSlots s ((evmChain s).tail) := by
          unfold frameRoleSlots
          conv_lhs => rw [hcons, List.flatMap_cons]
          simp [htail_eq]
        have hpw2 := hpw_all.2.1
        rw [hfrs_cons] at hpw2
        exact (List.pairwise_append.mp hpw2).2.1
      exact List.pairwise_append.mpr ⟨hpw_all.1, hpw_frs, fun a ha b hb => hpw_all.2.2 a ha b (hfrs_sub b hb)⟩
    · intro a ha b hb
      exact hRoles.2.2 a ha b (by
        rcases List.mem_append.mp hb with hsl | hjr
        · exact List.mem_append_left _ (hsl_sub b hsl)
        · exact List.mem_append_right _ hjr)
  · have hsum_le : ((evmChain s).tail.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum ≤
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      conv_rhs => rw [hcons, List.map_cons, List.sum_cons]
      simp only [htail_eq, hmw]
      omega
    omega

open EvmEkFk in
theorem releaseReadyAt_of_pop_keys {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S S' : List Nat}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hne : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hm : post.memory = s.memory)
    (hg : ∀ name : String, ofString name ≠ ofString "ev" →
      ofString name ≠ ofString "cur_cont" → globN post name = globN s name)
    (hch_post : evmChain post = (evmChain s).tail)
    (hS'_sub : ∀ t ∈ S', t ∈ S)
    (hS'_cases : (S' = S ∧ ¬ DelExclusive s S (evmChain s) 0 (memW s (globN s "ev" + 136))) ∨
      (S' = S.filter (· != memW s (globN s "ev" + 136)) ∧
      DelExclusive s S (evmChain s) 0 (memW s (globN s "ev" + 136)))) :
    ReleaseReadyAt post S' (memW s (globN s "cur_cont" + 48))
      (memW s (globN s "cur_cont" + 56)) := by
  have hmw : ∀ a, memW post a = memW s a := fun a => by unfold memW; rw [hm]
  obtain ⟨hW, _, _, _, hFW_all, _, _, _, _, _, hMarks, _, _⟩ := hInv
  have hcons := evmChain_cons_of_cont_ne_zero hne
  have htail_ne : (evmChain s).tail ≠ [] := by
    rw [hcons]
    have hmc : maxChain = (maxChain - 1) + 1 := by decide
    dsimp only [List.tail]; rw [hmc]; simp [evmChainFrom]
  have h01 : 0 + 1 < (evmChain s).length := by
    have hpos : 0 < (evmChain s).tail.length := List.length_pos_of_ne_nil htail_ne
    have hlen_cons : (evmChain s).length = (evmChain s).tail.length + 1 := by
      conv_lhs => rw [hcons]
      conv_rhs => rw [hcons]
      rfl
    omega
  have hch0_eq : (evmChain s)[0]'(by omega) = (globN s "ev", globN s "cur_cont") := by simp [hcons]
  have hM0 := hMarks 0 h01
  dsimp only at hM0
  rw [hch0_eq] at hM0
  dsimp only at hM0
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM0
  have he0_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by rw [hcons]; exact List.mem_cons_self
  have hFW0 := hFW_all _ he0_mem
  have he0_scr := (hFW0.1 (globN s "ev", 280) (by simp)).1
  have he0_fmem := hFW0.2.1
  have he0_le_cm : globN s "ev" + 280 ≤ memW s (globN s "cur_cont" + 48) := m6 (globN s "ev", 280) (by simp [frameScratch])
  have hcmm_le_cm : memW s (globN s "cur_cont" + 56) ≤ memW s (globN s "cur_cont" + 48) := by
    have hfmp_le_sc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.2.1
    have h24_le_fmp : memW s (globN s "ev" + 24) ≤ globN s "frame_mem_ptr" := by dsimp only [Inside] at he0_fmem; omega
    have hsc_le_e0 : globN s "scratch_ptr" ≤ globN s "ev" := he0_scr.1
    omega
  have hhp_eq : globN post "heap_ptr" = globN s "heap_ptr" := hg "heap_ptr" (by decide) (by decide)
  have hfs_eq : ∀ ec, frameScratch post ec = frameScratch s ec := by intro ec; unfold frameScratch; simp only [hmw]
  have hfl_eq : ∀ ec, frameLogs post ec = frameLogs s ec := by intro ec; unfold frameLogs; simp only [hmw]
  have hfp_eq : ∀ t, htabFootprint post t = htabFootprint s t := by intro t; unfold htabFootprint hdr; simp only [hmw]
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects blockOutObjects balObjects balRecords lstObjects htabValues hdr nodeF
    simp only [hmw, hg "bo" (by decide) (by decide), hg "bal_accounts" (by decide) (by decide),
      hg "journal" (by decide) (by decide), hg "journal_cap" (by decide) (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hn : ofString gn.1 ≠ ofString "ev" ∧ ofString gn.1 ≠ ofString "cur_cont" := by revert gn hgn; decide
    rw [hg gn.1 hn.1 hn.2]
  have htail_j : ∀ ec ∈ (evmChain s).tail, ∃ (j : Nat) (hj : j < (evmChain s).length),
      0 < j ∧ (evmChain s)[j] = ec := by
    intro ec hec
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hec
    have hk1 : k + 1 < (evmChain s).length := by rw [hcons] at hk ⊢; simp at hk ⊢; omega
    exact ⟨k + 1, hk1, by omega, by simp [List.getElem_tail]⟩
  have hgap : heapLimit ≤ globN s "scratch_ptr" := by
    have h1 := hAs.2.2.2.1
    have h2 := hAs.2.2.2.2.1
    rw [InitECandidate.Solver.Wave8Contracts.M23.heapLimit_val,
        InitECandidate.Solver.Wave8Contracts.M23.scratchStart_val] at *
    omega
  refine ⟨m1, m2, hcmm_le_cm, m3, m4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ec hec o ho
    rw [hch_post] at hec; rw [hfs_eq] at ho
    obtain ⟨j, hj, hj0, rfl⟩ := htail_j ec hec
    exact (m5 j hj hj0).1 o ho
  · intro ec hec
    rw [hch_post] at hec
    obtain ⟨j, hj, hj0, rfl⟩ := htail_j ec hec
    have hfo3 : (frameObjects s (evmChain s)[j])[3]! =
        (memW s ((evmChain s)[j].1 + 24), memW s ((evmChain s)[j].1 + 40)) := by simp [frameObjects]
    have hin := (m5 j hj hj0).2.1
    rw [hfo3] at hin
    simpa [hmw] using hin
  · intro ec hec
    rw [hch_post] at hec; rw [hfl_eq, hhp_eq]
    obtain ⟨j, hj, hj0, rfl⟩ := htail_j ec hec
    have hFWj := hFW_all _ (List.getElem_mem hj)
    rcases (m5 j hj hj0).2.2.1 with h_hl | h_cm
    · rcases hFWj.2.2.2.2.2.2.2.2.2.2.2.2.1 with h_hp | h_sc
      · exact Or.inl h_hp
      · exfalso
        have hpos : 0 < (frameLogs s (evmChain s)[j]).2 := by
          unfold frameLogs; dsimp only; have := hFWj.2.2.2.2.2.2.2.2.2.2.1; omega
        dsimp only [Inside] at h_hl h_sc
        omega
    · exact Or.inr h_cm
  · intro ec hec
    rw [hch_post] at hec; rw [hmw, hhp_eq]
    obtain ⟨j, hj, hj0, rfl⟩ := htail_j ec hec
    have hFWj := hFW_all _ (List.getElem_mem hj)
    rcases (m5 j hj hj0).2.2.2 with h_hl | h_cm
    · rcases hFWj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with h_hp | h_sc
      · exact Or.inl h_hp
      · exfalso
        dsimp only [Inside] at h_hl h_sc
        omega
    · exact Or.inr h_cm
  · intro t ht' o ho
    rw [hfp_eq] at ho; rw [hhp_eq]
    have ht : t ∈ S := hS'_sub t ht'
    have hfp_alloc : Allocated s o := ((hW.1.2.1 t ht).2 o ho).1
    have hpos_o : 0 < o.2 := by
      unfold htabFootprint at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      have hWFt := (hW.1.2.1 t ht).1
      have hk1 : 1 ≤ hdr s t 0 := hWFt.2.2.1
      have hstr : hdr s t 1 = (hdr s t 0 + 7) / 8 * 8 := hWFt.2.2.2.2.1
      have hstr_pos : 1 ≤ hdr s t 1 := by rw [hstr]; omega
      have hnc : 2 ≤ hdr s t 10 := hWFt.2.2.2.2.2.1
      rcases ho with rfl | rfl | rfl | rfl
      · dsimp only; omega
      · dsimp only; exact Nat.mul_pos (by omega) hstr_pos
      · dsimp only; omega
      · dsimp only; omega
    rcases m8 t ht with ⟨htake, hD0⟩ | hloc
    · exfalso
      have htake0 : ((evmChain s).take 1).map (fun ec => memW s (ec.1 + 136)) =
          [memW s (globN s "ev" + 136)] := by rw [hcons]; simp
      rw [htake0, List.mem_singleton] at htake
      subst htake
      rcases hS'_cases with ⟨_, hnD⟩ | ⟨hEq, _⟩
      · exact hnD hD0
      · rw [hEq] at ht'
        exact absurd rfl (bne_iff_ne.mp (List.mem_filter.mp ht').2)
    · rcases hloc o ho with h_hl | h_cm
      · rcases hfp_alloc with h_hp | h_sc
        · exact Or.inl h_hp
        · exfalso
          dsimp only [Inside] at h_hl h_sc
          omega
      · exact Or.inr h_cm
  · intro o ho
    rw [hfix_eq] at ho
    rw [hhp_eq]
    rcases m9 o ho with hz | h_hl | h_cm
    · exact Or.inl hz
    · by_cases hz : o.2 = 0
      · exact Or.inl hz
      · rcases hW.2.2.1.1 o ho with hz' | ⟨hal, _⟩
        · exact Or.inl hz'
        · rcases hal with h_hp | h_sc
          · exact Or.inr (Or.inl h_hp)
          · exfalso
            dsimp only [Inside] at h_hl h_sc
            omega
    · exact Or.inr (Or.inr h_cm)

/-! ### Exact gas accounting for error incorporation -/

open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8M19.Htab

def readW {F : Type} (s : PanSemStateFiniteExact 64 F) (a : BitVec 64) : BitVec 64 :=
  match s.memory a with | .word w => w

theorem ev_add_loads {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e c k : BitVec 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hc : s.locals.lookup (ofString "child") = some (.val (.word c)))
    (w : BitVec 64)
    (h : ev s (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const k]),
      .load .one (.op .add [.var .local (ofString "child"), .const k])]) = some (.val (.word w))) :
    w = readW s (e + k) + readW s (c + k) := by
  cases h1 : s.memory (e + k) with
  | word w1 =>
    cases h2 : s.memory (c + k) with
    | word w2 =>
      by_cases hd1 : s.memaddrs (e + k) <;> by_cases hd2 : s.memaddrs (c + k) <;>
        simp [ev, evalHOLExact, evalListHOLExact, he, hc, memLoadHOLExact,
          wordOpHOL, wordOp, valueIsWord, valueWord, h1, h2, hd1, hd2] at h
      simpa [readW, h1, h2] using h.symm

/-- Unlike the write-frame lemma, this records the actual three modular sums. -/
theorem incorporate_child_on_error_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e c : BitVec 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hc : s.locals.lookup (ofString "child") = some (.val (.word c)))
    (hsep : c + 72 ≠ e + 64 ∧ c + 184 ≠ e + 64 ∧ c + 184 ≠ e + 72) :
    Ret s (sourceFnBody Guest.Software.guestFn_incorporate_child_on_error) (fun _ post =>
      post.globals = s.globals ∧ post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
      post.be = s.be ∧ post.memory =
        updW (updW (updW s.memory (e + 64)
          (readW s (e + 64) + readW s (c + 64))) (e + 72)
          (readW s (e + 72) + readW s (c + 72))) (e + 184)
          (readW s (e + 184) + readW s (c + 184))) := by
  have hb : sourceFnBody Guest.Software.guestFn_incorporate_child_on_error =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_incorporate_child_on_error).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_incorporate_child_on_error,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.seq_storeWv _ (ev_globOff s _ e 64 he) (fun v hv => ev_op_word s _ _ v hv) ?_
  intro w1 hw1 _
  have hw1' := ev_add_loads s e c 64 he hc w1 hw1
  subst w1
  refine Ret.seq_storeWv _ (ev_globOff _ _ e 72 he) (fun v hv => ev_op_word _ _ _ v hv) ?_
  intro w2 hw2 _
  have hw2' := ev_add_loads _ e c 72 (by exact he) (by exact hc) w2 hw2
  simp only [readW, updW, if_neg (show e + 72 ≠ e + 64 by bv_omega),
    if_neg hsep.1] at hw2'
  subst w2
  refine Ret.seq_storeWv _ (ev_globOff _ _ e 184 he) (fun v hv => ev_op_word _ _ _ v hv) ?_
  intro w3 hw3 _
  have hw3' := ev_add_loads _ e c 184 (by exact he) (by exact hc) w3 hw3
  simp only [readW, updW, if_neg (show e + 184 ≠ e + 72 by bv_omega),
    if_neg (show e + 184 ≠ e + 64 by bv_omega), if_neg hsep.2.1,
    if_neg hsep.2.2] at hw3'
  subst w3
  refine Ret.ret fun _ _ => ?_
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem incorporate_child_on_error_head_gas {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (e c : BitVec 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hc : s.locals.lookup (ofString "child") = some (.val (.word c)))
    (hsep : c + 72 ≠ e + 64 ∧ c + 184 ≠ e + 64 ∧ c + 184 ≠ e + 72)
    (v : ValueHOL 64)
    (hr : evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_incorporate_child_on_error) = (some (.returned v), post)) :
    (readW post (e + 64)).toNat + (readW post (e + 192)).toNat ≤
      (readW s (e + 64)).toNat + (readW s (c + 64)).toNat +
        (readW s (e + 192)).toNat := by
  obtain ⟨_, _, _, _, hm⟩ := Ret.apply (incorporate_child_on_error_exact s e c he hc hsep) hr
  have h64 : readW post (e + 64) = readW s (e + 64) + readW s (c + 64) := by
    simp [readW, hm, updW]
  have h192 : readW post (e + 192) = readW s (e + 192) := by
    simp [readW, hm, updW]
  rw [h64, h192, BitVec.toNat_add]
  exact Nat.add_le_add_right (Nat.mod_le _ _) _

theorem readW_toNat {F : Type} (s : PanSemStateFiniteExact 64 F) (a : BitVec 64) :
    (readW s a).toNat = memW s a.toNat := by
  simp only [memW, BitVec.ofNat_toNat, readW]
  cases s.memory a
  rfl

/-- Error incorporation consumes at most the child's regular-gas credit. -/
theorem incorporate_child_on_error_gas {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (e c : BitVec 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hc : s.locals.lookup (ofString "child") = some (.val (.word c)))
    (hsep : c + 72 ≠ e + 64 ∧ c + 184 ≠ e + 64 ∧ c + 184 ≠ e + 72)
    (heB : e.toNat + 200 ≤ 2 ^ 64) (hcB : c.toNat + 72 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hr : evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_incorporate_child_on_error) = (some (.returned v), post)) :
    memW post (e.toNat + 64) + memW post (e.toNat + 192) ≤
      memW s (e.toNat + 64) + memW s (c.toNat + 64) + memW s (e.toNat + 192) := by
  have h := incorporate_child_on_error_head_gas s post e c he hc hsep v hr
  simp only [readW_toNat] at h
  change memW post (e + (64 : BitVec 64)).toNat + memW post (e + (192 : BitVec 64)).toNat ≤
    memW s (e + (64 : BitVec 64)).toNat + memW s (c + (64 : BitVec 64)).toNat +
      memW s (e + (192 : BitVec 64)).toNat at h
  have h64 : (64 : BitVec 64).toNat = 64 := rfl
  have h192 : (192 : BitVec 64).toNat = 192 := rfl
  simp only [BitVec.toNat_add, h64, h192] at h
  rw [Nat.mod_eq_of_lt (show e.toNat + 64 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show e.toNat + 192 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c.toNat + 64 < 2 ^ 64 by omega)] at h
  exact h


theorem list_array_cell_ne_header (arr l : BitVec 64) (cap i : Nat)
    (hi : i < cap) (hw : arr.toNat + 8 * cap ≤ 2 ^ 64)
    (hlw : l.toNat + 24 ≤ 2 ^ 64)
    (hsep : l.toNat + 24 ≤ arr.toNat ∨ arr.toNat + 8 * cap ≤ l.toNat) :
    BitVec.ofNat 64 (arr.toNat + 8 * i) ≠ l ∧
    BitVec.ofNat 64 (arr.toNat + 8 * i) ≠ l + 8 ∧
    BitVec.ofNat 64 (arr.toNat + 8 * i) ≠ l + 16 := by
  have ha : (BitVec.ofNat 64 (arr.toNat + 8 * i)).toNat = arr.toNat + 8 * i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h8 : (l + 8).toNat = l.toNat + 8 := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by change l.toNat + 8 < 2 ^ 64; omega)
  have h16 : (l + 16).toNat = l.toNat + 16 := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by change l.toNat + 16 < 2 ^ 64; omega)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    have he := congrArg BitVec.toNat h <;> simp only [ha, h8, h16] at he <;> omega

/-- The existing push postcondition already retains contents in the no-growth branch. -/
theorem lstPushPost_prefix_no_growth {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {l arr0 n cap : BitVec 64} {v : ValueHOL 64}
    (h : LstPushPost s l 8 n cap v post)
    (hma : s.memory l = .word arr0) (hlt : n.toNat < cap.toNat)
    (hw : arr0.toNat + 8 * cap.toNat ≤ 2 ^ 64) (hlw : l.toNat + 24 ≤ 2 ^ 64)
    (hsep : l.toNat + 24 ≤ arr0.toNat ∨ arr0.toNat + 8 * cap.toNat ≤ l.toNat) :
    post.memory l = .word arr0 ∧
      ∀ i, i < n.toNat → memW post (arr0.toNat + 8 * i) = memW s (arr0.toNat + 8 * i) := by
  obtain ⟨_, _, _, _, _, _, _, _, arr, d, len, hml, _, _, halt, hkeep⟩ := h
  rcases halt with ⟨_, rfl, rfl, hm, _⟩ | ⟨heq, _⟩
  · have ha : arr = arr0 := by simpa using hm.symm.trans hma
    subst arr
    refine ⟨hml, ?_⟩
    intro i hi
    obtain ⟨h0, h8, h16⟩ := list_array_cell_ne_header arr0 l cap.toNat i (by omega) hw hlw hsep
    have hm := hkeep (BitVec.ofNat 64 (arr0.toNat + 8 * i))
      (by simp [CellHits]) h0 h8 h16
    unfold memW
    rw [hm]
  · have : n.toNat = cap.toNat := congrArg BitVec.toNat heq
    omega

/-- Header stores following a growth copy preserve all copied entries. -/
theorem lst_push_growth_prefix {F : Type} {s copied : PanSemStateFiniteExact 64 F}
    (l dst src n : BitVec 64)
    (hcopy : SoloHtabSet.MemCopyRel s copied dst src (8 * n.toNat) (8 * n.toNat))
    (hd8 : dst.toNat % 8 = 0) (hs8 : src.toNat % 8 = 0)
    (hdw : dst.toNat + 8 * n.toNat < 2 ^ 64)
    (hsw : src.toNat + 8 * n.toNat < 2 ^ 64)
    (hlw : l.toNat + 24 ≤ 2 ^ 64)
    (hsep : l.toNat + 24 ≤ dst.toNat ∨ dst.toNat + 8 * n.toNat ≤ l.toNat) :
    ∀ i, i < n.toNat →
      memW { copied with memory := updW (updW (updW copied.memory l dst) (l + 16) (n * 2)) (l + 8) (n + 1) }
        (dst.toNat + 8 * i) = memW s (src.toNat + 8 * i) := by
  intro i hi
  obtain ⟨h0, h8, h16⟩ := list_array_cell_ne_header dst l n.toNat i hi (by omega) hlw hsep
  have hc := SoloHtabSet.memW_copied_of_memCopyRel hcopy hd8 hs8 (by omega)
    (show 8 * i + 8 ≤ 8 * n.toNat by omega) hdw hsw
  unfold memW at hc ⊢
  dsimp only
  rw [updW_ne _ _ _ _ h8, updW_ne _ _ _ _ h16, updW_ne _ _ _ _ h0]
  exact hc

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge

/-! ## Copied `htab_union_into` spec (from `R16Shards/HtabUnionIntoSpec.lean`, not importable)
and the `htab_item` read-only fact (from `Deliveries/M15`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge.RbM15

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- Outcome specification of a function body from its callee-entry state
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
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

/-- The outcomes after which the caller resumes (return, or a catchable exception)
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

/-- `fname` changes nothing but locals and clock
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def ReadOnlyFn (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r post => Resumes r → post = { s with locals := post.locals, clock := post.clock })
    fname

/-- `t` agrees with `s` on every field except `locals` and `clock`. -/
def LocFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

theorem LocFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrame s s := by
  cases s; rfl

theorem LocFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrame s t) (h2 : LocFrame t u) : LocFrame s u := by
  unfold LocFrame at *
  rw [h2]; rw [h1]

theorem LocFrame.with_locals_clock {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    LocFrame s { t with locals := locals, clock := k } := by
  unfold LocFrame at h ⊢
  rw [h]

/-- Syntactic predicate for programs that perform no memory store, shared-memory write/global load,
global assignment, or FFI call, calling only `decCall` callees approved by `good`. -/
def readOnlyProg (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => readOnlyProg good body
  | .seq first second => readOnlyProg good first && readOnlyProg good second
  | .ite _ yes no => readOnlyProg good yes && readOnlyProg good no
  | .while _ body => readOnlyProg good body
  | .decCall _ _ fname _ cont => good fname && readOnlyProg good cont
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem evaluate_readOnlyProg {F : Type} (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg good body = true)
    (program : ProgHOL 64) (supported : readOnlyProg good program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    LocFrame state (evaluateHOLFiniteState state program).2 := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; exact LocFrame.refl state
  | «break» => rw [evaluateHOLFiniteState_break]; exact LocFrame.refl state
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact LocFrame.refl state
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact LocFrame.refl state
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split
      · rfl
      · exact LocFrame.refl state
    · exact LocFrame.refl state
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact LocFrame.refl state
    · split
      · rfl
      · exact LocFrame.refl state
  | assign kind name value =>
    cases kind with
    | global => simp [shape, readOnlyProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact LocFrame.refl state
      · split
        · rfl
        · exact LocFrame.refl state
  | dec name kind initializer body =>
    have child : readOnlyProg good body = true := by simpa only [shape, readOnlyProg] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact LocFrame.refl state
    · rename_i val _
      split
      · have ih := evaluate_readOnlyProg good hgood body child (setVarHOLFinite name val state) code
        unfold LocFrame at ih ⊢
        dsimp only
        rw [ih]; rfl
      · exact LocFrame.refl state
  | seq first second =>
    have children : readOnlyProg good first = true ∧ readOnlyProg good second = true := by
      simpa only [shape, readOnlyProg, Bool.and_eq_true] using supported
    have ih1 := evaluate_readOnlyProg good hgood first children.1 state code
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at ih1 remaining meta'
      dsimp only at ih1 remaining meta' ⊢
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        exact ih1.trans (evaluate_readOnlyProg good hgood second children.2 middle (meta'.1.trans code))
      | some _ => exact ih1
  | ite condition yes no =>
    have children : readOnlyProg good yes = true ∧ readOnlyProg good no = true := by
      simpa only [shape, readOnlyProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_readOnlyProg good hgood no children.2 state code
      · exact evaluate_readOnlyProg good hgood yes children.1 state code
    · exact LocFrame.refl state
  | «while» condition body =>
    have child : readOnlyProg good body = true := by simpa only [shape, readOnlyProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_readOnlyProg good hgood body child (decClockHOLFinite state) code
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at ih1 remaining meta'
            dsimp only at ih1 remaining meta' ⊢
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            have ih1' : LocFrame state middle := by
              unfold LocFrame at ih1 ⊢
              rw [ih1]; rfl
            cases result with
            | none =>
              exact ih1'.trans (evaluate_readOnlyProg good hgood (.while condition body)
                (by simpa [readOnlyProg] using child) middle mCode)
            | some result =>
              cases result with
              | «continue» =>
                exact ih1'.trans (evaluate_readOnlyProg good hgood (.while condition body)
                  (by simpa [readOnlyProg] using child) middle mCode)
              | «break» => exact ih1'
              | returned _ => exact ih1'
              | exception _ _ => exact ih1'
              | finalFfi _ => exact ih1'
              | error => exact ih1'
              | timeOut => exact ih1'
      · exact LocFrame.refl state
    · exact LocFrame.refl state
  | decCall name kind function arguments continuation =>
    have children : good function = true ∧ readOnlyProg good continuation = true := by
      simpa only [shape, readOnlyProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases hargs : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
    · exact LocFrame.refl state
    · dsimp only
      rcases found : lookupCodeHOLFinite state.code.lookup function values with _ | ⟨body, callee, rs⟩
      · exact LocFrame.refl state
      · dsimp only
        have found' : lookupCodeHOLFinite originalRuntimeCode.lookup function values =
            some (body, callee, rs) := by rwa [← code]
        have bodyOk := hgood function children.1 values body callee rs found'
        split
        · rfl
        · rename_i nonzero
          have ih := evaluate_readOnlyProg good hgood body bodyOk
            (callEntryStateHOLFinite state callee) code
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata
            (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
          | mk res st =>
            rw [hrun] at ih meta' cl
            dsimp only at ih meta' cl ⊢
            change st.clock ≤ state.clock - 1 at cl
            have small : st.clock < state.clock := by omega
            have stCode : st.code = originalRuntimeCode := meta'.1.trans code
            have ih' : LocFrame state st := by
              unfold LocFrame at ih ⊢
              rw [ih]; rfl
            cases res with
            | none => exact ih'
            | some r =>
              cases r with
              | returned v =>
                dsimp only
                split
                · set resumed := setVarHOLFinite name v { st with locals := state.locals }
                  have smallR : resumed.clock < state.clock := small
                  have rCode : resumed.code = originalRuntimeCode := stCode
                  have ihR : LocFrame state resumed := ih'.with_locals_clock _ _
                  have ih2 := evaluate_readOnlyProg good hgood continuation children.2 resumed rCode
                  exact (ihR.trans ih2).with_locals_clock _ _
                · exact ih'
              | timeOut => exact ih'.with_locals_clock _ _
              | «break» => exact ih'
              | «continue» => exact ih'
              | error => exact ih'.with_locals_clock _ _
              | exception _ _ => exact ih'.with_locals_clock _ _
              | finalFfi _ => exact ih'.with_locals_clock _ _
  | _ => simp [shape, readOnlyProg] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl smaller
      | omega
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr ⟨h, by simp +arith⟩)
      | exact Or.inr ⟨rfl, by simp +arith⟩

theorem readOnlyFn_of_guestAst (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg good body = true)
    (hbody : readOnlyProg good
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) =
        true) :
    ReadOnlyFn (ofString (extractFn d).name) :=
  ⟨_, _, _, lookup_of_guestAst_getElem i hi (extractFn d) hd,
    fun s hcode _ _ _ _ => evaluate_readOnlyProg good hgood _ hbody s hcode⟩

/-- Callees invoked via `decCall` by `htab_get` and `htab_has`. -/
def htabGetCallees (f : MlS) : Bool :=
  f == ofString "htab_find_leaf" || f == ofString "memeq"

theorem htabGetCallees_good :
    ∀ function, htabGetCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg htabGetCallees body = true := by
  intro function hfn values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [htabGetCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with rfl | rfl
  · have hl := lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_htab_find_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_find_leaf") = _ at hl
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]
    rfl
  · have hl := lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_memeq) rfl
    change originalRuntimeCode.lookup (ofString "memeq") = _ at hl
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]
    rfl

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge.RbM15

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge.RbM15
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
theorem rb_ro_htab_item : ReadOnlyFn (ofString "htab_item") :=
  readOnlyFn_of_guestAst 143 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_item rfl
    (fun _ => false) (fun _ h => by cases h) rfl
end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge.RbM15

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.UXT

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

namespace HtabUnionInto

def ExitR {F : Type} (t : Nat) (s post : PanSemStateFiniteExact 64 F) : Prop :=
  let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
  ArenaReady post ∧ HtabWF post t ∧
  hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
  (∀ i ∈ htabFootprint post t, Allocated post i ∧
    ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
  FrameOutside s post (htabFootprint s t) fresh ∧
  (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString → s.globals.lookup k = post.globals.lookup k)

theorem ExitR.toUnionExit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : ExitR (locN s "dst") s post) : UnionExit s post := by
  obtain ⟨hA, hW, hk0, hk1, hh, hfp, hfr, hg⟩ := h
  exact ⟨hA, hW, hk0, hk1, hh, fun i hi => (hfp i hi).1, hfr, hg⟩

theorem ExitR.refl {F : Type} (t : Nat) (s : PanSemStateFiniteExact 64 F) (hA : ArenaReady s)
    (hW : HtabWF s t) (hal : ∀ i ∈ htabFootprint s t, Allocated s i) : ExitR t s s := by
  refine ⟨hA, hW, rfl, rfl, le_refl _, fun i hi => ⟨hal i hi, Or.inl ⟨i, hi, le_refl _, le_refl _⟩⟩,
    fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem ExitR.trans {F : Type} {t : Nat} {a b c : PanSemStateFiniteExact 64 F}
    (hab : ExitR t a b) (hbc : ExitR t b c) : ExitR t a c := by
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

theorem freeChain_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k nodes : Nat) :
    ∀ (Fr : List Nat) (head : Nat),
      FreeChain { s with locals := locals, clock := k } nodes head Fr ↔ FreeChain s nodes head Fr
  | [], _ => Iff.rfl
  | _ :: rest, _ => by
    simp only [FreeChain]
    exact and_congr Iff.rfl (freeChain_with_locals s locals k nodes rest _)

theorem htabWF_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k t : Nat) :
    HtabWF { s with locals := locals, clock := k } t ↔ HtabWF s t := by
  simp only [HtabWF, freeChain_with_locals]
  exact Iff.rfl

theorem arenaReady_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ArenaReady { s with locals := locals, clock := k } ↔ ArenaReady s :=
  ⟨fun h => ⟨guestInv_congr (s := { s with locals := locals, clock := k }) rfl rfl rfl rfl h.1, h.2⟩,
   fun h => ⟨guestInv_with_locals_clock s locals k h.1, h.2⟩⟩

theorem exitR_locals {F : Type} (t : Nat) (a b : PanSemStateFiniteExact 64 F)
    (L1 L2 : HolFiniteMapExact MlS (ValueHOL 64)) (k1 k2 : Nat) :
    ExitR t { a with locals := L1, clock := k1 } { b with locals := L2, clock := k2 } ↔
      ExitR t a b := by
  simp only [ExitR, arenaReady_with_locals, htabWF_with_locals]
  exact Iff.rfl

theorem lookup_htab_set :
    originalRuntimeCode.lookup (ofString "htab_set") =
      some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
        sourceFnBody Guest.Software.guestFn_htab_set, .one) :=
  lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_set) rfl

theorem lookup_htab_union_into :
    originalRuntimeCode.lookup (ofString "htab_union_into") =
      some ([(ofString "dst", .one), (ofString "src", .one)],
        sourceFnBody Guest.Software.guestFn_htab_union_into, .one) :=
  lookup_of_guestAst_getElem 400 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_union_into) rfl

theorem at_lookup {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
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
  have hret := lookupCodeHOLFinite_installed_return state fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  subst hret
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
      some (body', (callEntryStateHOLFinite state callee).locals, ret') := by
    rw [← hcode]
    exact hl
  exact hspec _ hcode hPc ⟨values, hl'⟩ hnt

theorem locN_congr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (n : String)
    (h : locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    locN { s with locals := locals, clock := k } n = locN s n := by
  simp only [locN, h]

theorem localsOnly_unionArgWF : LocalsOnly ["dst"] UnionArgWF := by
  intro F s locals k hl hP
  have hd := locN_congr s locals k "dst" (hl "dst" (by simp))
  simp only [UnionArgWF, htabWF_with_locals, arenaReady_with_locals] at hP ⊢
  rw [hd]
  exact hP

def UInv {F : Type} (s0 u : PanSemStateFiniteExact 64 F) : Prop :=
  u.code = originalRuntimeCode ∧
  u.locals.lookup (ofString "dst") = s0.locals.lookup (ofString "dst") ∧
  UnionArgWF u ∧ ExitR (locN s0 "dst") s0 u

theorem decCall_flow {F : Type} (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (sh : ShapeHOL) (f : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState s (.decCall x sh f args cont)).1) :
    ∃ values body' callee ret rv cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup f values = some (body', callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' = (some (.returned rv), cpost) ∧
      Wave8M19.Htab.FlowR (evaluateHOLFiniteState (setVarHOLFinite x rv { cpost with locals := s.locals }) cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x sh f args cont)).2 =
        { (evaluateHOLFiniteState (setVarHOLFinite x rv { cpost with locals := s.locals }) cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState (setVarHOLFinite x rv { cpost with locals := s.locals }) cont).2.locals
            (x, s.locals.lookup x) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hflow ⊢
  revert hflow
  split
  · intro hf; rcases hf with h | h | h <;> cases h
  · rename_i values hargs
    split
    · intro hf; rcases hf with h | h | h <;> cases h
    · rename_i body' callee ret hl
      split
      · intro hf; rcases hf with h | h | h <;> cases h
      · dsimp only
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨r, cpost⟩
        rcases r with _ | r
        · intro hf; rcases hf with h | h | h <;> cases h
        · cases r with
          | returned rv =>
            dsimp only
            split
            · intro hf
              exact ⟨values, body', callee, ret, rv, cpost, hargs, hl, hrun, hf, rfl⟩
            · intro hf; rcases hf with h | h | h <;> cases h
          | _ => intro hf; rcases hf with h | h | h <;> cases h

theorem assign_local_flow {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (e : ExpHOL 64)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState s (.assign .local x e)).1) :
    ∃ v, Wave8M19.Htab.ev s e = some v ∧
      evaluateHOLFiniteState s (.assign .local x e) = (none, setVarHOLFinite x v s) := by
  rw [evaluateHOLFiniteState_assign] at hflow ⊢
  revert hflow
  split
  · intro hf; rcases hf with h | h | h <;> cases h
  · rename_i v hv
    split
    · intro _; exact ⟨v, hv, rfl⟩
    · intro hf; rcases hf with h | h | h <;> cases h

theorem seq_flow_split {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState s (.seq a b)).1) :
    (∃ mid, evaluateHOLFiniteState s a = (none, mid) ∧
      Wave8M19.Htab.FlowR (evaluateHOLFiniteState mid b).1 ∧
      evaluateHOLFiniteState s (.seq a b) = evaluateHOLFiniteState mid b) ∨
    ((evaluateHOLFiniteState s a).1 ≠ none ∧
      Wave8M19.Htab.FlowR (evaluateHOLFiniteState s a).1 ∧
      evaluateHOLFiniteState s (.seq a b) = evaluateHOLFiniteState s a) := by
  rw [evaluateHOLFiniteState_seq_line780] at hflow ⊢
  rcases ha : evaluateHOLFiniteState s a with ⟨r, mid⟩
  simp only [ha] at hflow ⊢
  cases r with
  | none => exact Or.inl ⟨mid, rfl, hflow, rfl⟩
  | some _ => exact Or.inr ⟨by simp [ha], by simpa [ha] using hflow, rfl⟩

theorem ite_flow_split {F : Type} (s : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (y n : ProgHOL 64)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState s (.ite c y n)).1) :
    (Wave8M19.Htab.FlowR (evaluateHOLFiniteState s y).1 ∧
      evaluateHOLFiniteState s (.ite c y n) = evaluateHOLFiniteState s y) ∨
    (Wave8M19.Htab.FlowR (evaluateHOLFiniteState s n).1 ∧
      evaluateHOLFiniteState s (.ite c y n) = evaluateHOLFiniteState s n) := by
  rw [evaluateHOLFiniteState_ite] at hflow ⊢
  revert hflow
  split
  · split
    · intro hf; exact Or.inr ⟨hf, rfl⟩
    · intro hf; exact Or.inl ⟨hf, rfl⟩
  · intro hf; rcases hf with h | h | h <;> cases h

theorem call_htab_set_step
    (hset : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set"))
    {F : Type} (st : PanSemStateFiniteExact 64 F) (rest : List (ExpHOL 64))
    (hcode : st.code = originalRuntimeCode) (hU : UnionArgWF st)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: rest))).1) :
    let post := (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: rest))).2
    post.code = originalRuntimeCode ∧
    post.locals = st.locals ∧
    UnionArgWF post ∧
    ExitR (locN st "dst") st post := by
  intro post
  have hnr := Wave8M19.Htab.call0_noRetBrk st (ofString "htab_set") (.var .local (ofString "dst") :: rest)
  have hflow2 : (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: rest))).1 = none ∨
    (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: rest))).1 = some .continue := by
    rcases hflow with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hnr.1.2
  obtain ⟨values, body', callee, ret, v, cpost, hargs, hl, hrun, heq⟩ :=
    Wave8M19.Htab.call0_flow st _ _ hflow2
  obtain ⟨tv, vs, rfl, htv⟩ := Wave8M19.Htab.evalList_cons_inv st _ _ hargs
  obtain ⟨_, hct⟩ := Wave8M19.Htab.lookupCodeHOLFinite_param_at st.code.lookup (ofString "htab_set") []
    (ofString "t") .one [(ofString "key", .one), (ofString "value", .one)] _ _
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> decide)
    (by rw [hcode]; simpa using lookup_htab_set) (vpre := []) (by simp) hl
  have hcalleeT : callee.lookup (ofString "t") = st.locals.lookup (ofString "dst") := by
    rw [hct]
    simp only [evalHOLExact] at htv
    exact htv.symm
  have htE : locN (callEntryStateHOLFinite st callee) "t" = locN st "dst" := by
    simp only [locN, callEntryStateHOLFinite, hcalleeT]
  have hE : HtabArgWF (callEntryStateHOLFinite st callee) := by
    obtain ⟨hA, hW, hal⟩ := hU
    refine ⟨(arenaReady_with_locals st callee (st.clock - 1)).2 hA, ?_, ?_⟩
    · rw [htE]; exact (htabWF_with_locals st callee (st.clock - 1) _).2 hW
    · rw [htE]; exact hal
  have hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body').1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hx := at_lookup hset st hcode _ body' callee ret hl hE hnt
  rw [hrun] at hx
  have hx' : ExitR (locN (callEntryStateHOLFinite st callee) "t")
      (callEntryStateHOLFinite st callee) cpost := hx v rfl
  rw [htE] at hx'
  have hpost : post = { cpost with locals := st.locals } := congrArg Prod.snd heq
  have hxR : ExitR (locN st "dst") st post := by
    have h2 : ExitR (locN st "dst") { st with locals := callee, clock := st.clock - 1 }
        { cpost with locals := cpost.locals, clock := cpost.clock } := hx'
    rw [exitR_locals] at h2
    rw [hpost]
    show ExitR (locN st "dst") { st with locals := st.locals, clock := st.clock }
      { cpost with locals := st.locals, clock := cpost.clock }
    rw [exitR_locals]
    exact h2
  have hAR := hxR.1
  have hWF := hxR.2.1
  have hfoot := hxR.2.2.2.2.2.1
  have hcodeP : post.code = originalRuntimeCode :=
    (PanRunBounded.evaluateHOLFiniteState_metadata st _).1.trans hcode
  refine ⟨hcodeP, by rw [hpost], ?_, hxR⟩
  have hdst_post : locN post "dst" = locN st "dst" := by
    simp only [locN, hpost]
  refine ⟨hAR, ?_, ?_⟩
  · rw [hdst_post]; exact hWF
  · rw [hdst_post]; intro i hi; exact (hfoot i hi).1

theorem union_iter
    (hset : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set"))
    (itemArgs : List (ExpHOL 64)) (cond : ExpHOL 64) (setRest : List (ExpHOL 64))
    (incExp : ExpHOL 64)
    {F : Type} (s0 x : PanSemStateFiniteExact 64 F)
    (hx : UInv s0 x)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState (decClockHOLFinite x)
      (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
        (.seq
          (.ite cond
            (.call (some (none, none)) (ofString "htab_set")
              (.var .local (ofString "dst") :: setRest))
            .skip)
          (.assign .local (ofString "i") incExp)))).1) :
    UInv s0 (evaluateHOLFiniteState (decClockHOLFinite x)
      (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
        (.seq
          (.ite cond
            (.call (some (none, none)) (ofString "htab_set")
              (.var .local (ofString "dst") :: setRest))
            .skip)
          (.assign .local (ofString "i") incExp)))).2 := by
  obtain ⟨hxcode, hxdst, hxU, hxR⟩ := hx
  obtain ⟨values, body', callee, ret, rv, cpost, hargs, hl, hrun, hcont, hpost⟩ :=
    decCall_flow (decClockHOLFinite x) _ _ _ _ _ hflow
  have hro : FunSpec GuestInv
      (fun s r post => InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge.RbM15.Resumes r →
        post = { s with locals := post.locals, clock := post.clock })
      (ofString "htab_item") := InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge.RbM15.rb_ro_htab_item
  have hceG : GuestInv (callEntryStateHOLFinite (decClockHOLFinite x) callee) :=
    guestInv_with_locals_clock x callee _ hxU.1.1
  have hnt_item : (evaluateHOLFiniteState (callEntryStateHOLFinite (decClockHOLFinite x) callee) body').1 ≠
      some .timeOut := by rw [hrun]; simp
  have hitem := at_lookup hro (decClockHOLFinite x) hxcode values body' callee ret hl hceG hnt_item
  rw [hrun] at hitem
  have hcpost_eq : cpost = { x with locals := cpost.locals, clock := cpost.clock } :=
    hitem (Or.inl ⟨rv, rfl⟩)
  set s1 := setVarHOLFinite (ofString "s") rv { cpost with locals := x.locals } with hs1
  have hs1_eq : s1 = { x with locals := (x.locals.update (ofString "s", rv)), clock := cpost.clock } := by
    rw [hs1, hcpost_eq]; rfl
  have hs1_code : s1.code = originalRuntimeCode := by rw [hs1_eq]; exact hxcode
  have hs1_dst : s1.locals.lookup (ofString "dst") = s0.locals.lookup (ofString "dst") := by
    rw [hs1_eq]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "s" ≠ ofString "dst" by decide, hxdst]
  have hs1_U : UnionArgWF s1 := by
    rw [hs1_eq]
    exact localsOnly_unionArgWF x _ _ (fun n hn => by
      simp at hn; subst hn
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "s" ≠ ofString "dst" by decide]) hxU
  have hs1_R : ExitR (locN s0 "dst") s0 s1 := by
    rw [hs1_eq]
    have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
        { x with locals := x.locals.update (ofString "s", rv), clock := cpost.clock } := by
      rw [exitR_locals]; exact hxR
    exact h2
  set iteProg : ProgHOL 64 := .ite cond
    (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: setRest))
    .skip
  have h_ite_step : ∀ mid,
      Wave8M19.Htab.FlowR (evaluateHOLFiniteState s1 iteProg).1 →
      mid = (evaluateHOLFiniteState s1 iteProg).2 →
      mid.code = originalRuntimeCode ∧
      mid.locals = s1.locals ∧
      UnionArgWF mid ∧
      ExitR (locN s0 "dst") s0 mid := by
    intro mid hif hmid_eq
    rcases ite_flow_split s1 _ _ _ hif with ⟨hyf, hyeq⟩ | ⟨hnf, hneq⟩
    · dsimp only [iteProg] at hmid_eq
      rw [hyeq] at hmid_eq
      subst hmid_eq
      obtain ⟨hcd, hlc, hUp, hRp⟩ := call_htab_set_step hset s1 _ hs1_code hs1_U hyf
      have hdst1 : locN s1 "dst" = locN s0 "dst" := by simp only [locN, hs1_dst]
      rw [hdst1] at hRp
      exact ⟨hcd, hlc, hUp, hs1_R.trans hRp⟩
    · dsimp only [iteProg] at hmid_eq
      rw [hneq, evaluateHOLFiniteState_skip] at hmid_eq
      subst hmid_eq
      exact ⟨hs1_code, rfl, hs1_U, hs1_R⟩
  have hpost' : (evaluateHOLFiniteState (decClockHOLFinite x)
      (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
        (.seq iteProg (.assign .local (ofString "i") incExp)))).2 =
      { (evaluateHOLFiniteState s1 (.seq iteProg (.assign .local (ofString "i") incExp))).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState s1 (.seq iteProg (.assign .local (ofString "i") incExp))).2.locals
          (ofString "s", x.locals.lookup (ofString "s")) } := by
    exact hpost
  rcases seq_flow_split s1 iteProg (.assign .local (ofString "i") incExp) hcont with
    ⟨mid, hmid_none, hbf, hseq_eq⟩ | ⟨_, hif, hseq_eq⟩
  · obtain ⟨hm_code, hm_loc, hm_U, hm_R⟩ :=
      h_ite_step mid (Or.inl (by rw [hmid_none])) (by rw [hmid_none])
    obtain ⟨iv, _, hasg_eq⟩ := assign_local_flow mid _ _ hbf
    let mid_i := setVarHOLFinite (ofString "i") iv mid
    let fin_L := HolFiniteMapExact.resVarEq mid_i.locals (ofString "s", x.locals.lookup (ofString "s"))
    have hfin_eq : (evaluateHOLFiniteState (decClockHOLFinite x)
        (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
          (.seq iteProg (.assign .local (ofString "i") incExp)))).2 =
        { mid with locals := fin_L } := by
      rw [hpost', hseq_eq, hasg_eq]
      rfl
    rw [hfin_eq]
    refine ⟨hm_code, ?_, ?_, ?_⟩
    · dsimp only [fin_L, mid_i]
      rw [PanRunBounded.resVarEq_lookup]
      simp [show ofString "dst" ≠ ofString "s" by decide, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "dst" by decide,
        hm_loc, hs1_dst]
    · exact localsOnly_unionArgWF mid fin_L mid.clock (fun n hn => by
        simp at hn; subst hn
        dsimp only [fin_L, mid_i]
        rw [PanRunBounded.resVarEq_lookup]
        simp [show ofString "dst" ≠ ofString "s" by decide, setVarHOLFinite,
          HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "dst" by decide]) hm_U
    · have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
          { mid with locals := fin_L, clock := mid.clock } := by
        rw [exitR_locals]; exact hm_R
      exact h2
  · let mid := (evaluateHOLFiniteState s1 iteProg).2
    obtain ⟨hm_code, hm_loc, hm_U, hm_R⟩ := h_ite_step mid hif rfl
    let fin_L := HolFiniteMapExact.resVarEq mid.locals (ofString "s", x.locals.lookup (ofString "s"))
    have hfin_eq : (evaluateHOLFiniteState (decClockHOLFinite x)
        (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
          (.seq iteProg (.assign .local (ofString "i") incExp)))).2 =
        { mid with locals := fin_L } := by
      rw [hpost', hseq_eq]
    rw [hfin_eq]
    refine ⟨hm_code, ?_, ?_, ?_⟩
    · dsimp only [fin_L]
      rw [PanRunBounded.resVarEq_lookup]
      simp [show ofString "dst" ≠ ofString "s" by decide, hm_loc, hs1_dst]
    · exact localsOnly_unionArgWF mid fin_L mid.clock (fun n hn => by
        simp at hn; subst hn
        dsimp only [fin_L]
        rw [PanRunBounded.resVarEq_lookup]
        simp [show ofString "dst" ≠ ofString "s" by decide]) hm_U
    · have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
          { mid with locals := fin_L, clock := mid.clock } := by
        rw [exitR_locals]; exact hm_R
      exact h2

theorem htab_union_into_spec_of
    (hset : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set")) :
    FunSpec UnionArgWF (OnReturn UnionExit) (ofString "htab_union_into") := by
  refine ⟨_, _, _, lookup_htab_union_into, ?_⟩
  intro F s0 hcode hP _ _ v hv
  have hb : sourceFnBody Guest.Software.guestFn_htab_union_into =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_htab_union_into).body := rfl
  suffices key : Wave8M19.Htab.Ret s0 (sourceFnBody Guest.Software.guestFn_htab_union_into)
      (fun _ post => UnionExit s0 post) from key v hv
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_htab_union_into,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Wave8M19.Htab.Ret.dec
  intro capv _
  set s1 := setVarHOLFinite (ofString "cap") capv s0 with hs1
  apply Wave8M19.Htab.Ret.dec
  intro iv _
  set s2 := setVarHOLFinite (ofString "i") iv s1 with hs2
  have hI2 : UInv s0 s2 := by
    refine ⟨hcode, ?_, ?_, ?_⟩
    · simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "dst" by decide, show ofString "cap" ≠ ofString "dst" by decide]
    · exact LocalsOnly.setVar localsOnly_unionArgWF
        (by simp only [List.mem_singleton]; rintro _ rfl; decide) iv s1
        (LocalsOnly.setVar localsOnly_unionArgWF
          (by simp only [List.mem_singleton]; rintro _ rfl; decide) capv s0 hP)
    · have h0 : ExitR (locN s0 "dst") s0 s0 := ExitR.refl _ s0 hP.1 hP.2.1 hP.2.2
      have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
          { s0 with locals := s2.locals, clock := s0.clock } := by
        rw [exitR_locals]; exact h0
      exact h2
  apply Wave8M19.Htab.Ret.seq
  · intro w hw
    exfalso
    have hnr : Wave8M19.Htab.NoRet
        (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .local (ofString "src"), .var .local (ofString "i")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
              (.call (some (none, none)) (ofString "htab_set")
                [.var .local (ofString "dst"),
                 .rfield 1 (.var .local (ofString "s")),
                 .rfield 2 (.var .local (ofString "s"))])
              .skip)
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1])))) :=
      Wave8M19.Htab.NoRet.decCall (Wave8M19.Htab.NoRet.seq
        (Wave8M19.Htab.NoRet.ite Wave8M19.Htab.NoRet.call0 Wave8M19.Htab.NoRet.skip)
        Wave8M19.Htab.NoRet.assign)
    exact Wave8M19.Htab.while_noRet _ _ (fun st v => hnr st v) _ s2 le_rfl w hw
  · intro u hu
    apply Wave8M19.Htab.Ret.ret
    intro val _
    have hIu : UInv s0 u := by
      have := Wave8M19.Htab.while_inv (UInv s0) _ _
        (fun x hx _ hfl => union_iter hset _ _ _ _ s0 x hx hfl) s2.clock s2 le_rfl hI2 (by rw [hu])
      rw [hu] at this
      exact this
    obtain ⟨_, _, _, hR⟩ := hIu
    apply ExitR.toUnionExit
    have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
        { u with locals := u.locals, clock := u.clock } := hR
    rw [← exitR_locals (L1 := s0.locals) (k1 := s0.clock)
      (L2 := HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite u).locals
          (ofString "i", s1.locals.lookup (ofString "i")))
        (ofString "cap", s0.locals.lookup (ofString "cap")))
      (k2 := u.clock)] at h2
    exact h2

end HtabUnionInto

theorem rb_htab_union_into_spec :
    FunSpec UnionArgWF (OnReturn UnionExit) (ofString "htab_union_into") :=
  HtabUnionInto.htab_union_into_spec_of InitECandidate.Solver.Wave8GuestInv.SoloHtabSet.htab_set_spec_proof

end InitECandidate.Solver.Wave8GuestInv.R16Shards.UXT

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8M19.Htab

/-! ### `incorporate_child_on_success` write frame -/

section IcsRun
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8M19.Htab

theorem fl_lookup_ics :
    originalRuntimeCode.lookup (ofString "incorporate_child_on_success") =
      some ([(ofString "child", .one)],
        sourceFnBody Guest.Software.guestFn_incorporate_child_on_success, .one) :=
  lookup_of_guestAst_getElem 592 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_incorporate_child_on_success) rfl

/-- Frame of the straight-line prefix of `incorporate_child_on_success`: only the parent record
words `e+64`, `e+72`, `e+184`, `e+192` change. -/
def ICSW {F : Type} (s u : PanSemStateFiniteExact 64 F) (e c : BitVec 64) : Prop :=
  u.code = s.code ∧ u.memaddrs = s.memaddrs ∧ u.globals = s.globals ∧ GuestInv u ∧
  u.locals.lookup (ofString "child") = some (.val (.word c)) ∧
  ∀ a : BitVec 64, a ≠ e + 64 → a ≠ e + 72 → a ≠ e + 184 → a ≠ e + 192 → u.memory a = s.memory a

theorem icsw_store {F : Type} {s u : PanSemStateFiniteExact 64 F} {e c : BitVec 64} (k w : BitVec 64)
    (hk : k = 64 ∨ k = 72 ∨ k = 184 ∨ k = 192) (h : ICSW s u e c) :
    ICSW s { u with memory := updW u.memory (e + k) w } e c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, guestInv_congr (s := u) rfl rfl rfl rfl h4, h5, fun a a1 a2 a3 a4 => ?_⟩
  have hne : a ≠ e + k := by rcases hk with rfl | rfl | rfl | rfl <;> assumption
  change updW u.memory (e + k) w a = _
  rw [updW_ne _ _ _ _ hne]; exact h6 a a1 a2 a3 a4

theorem icsw_setVar {F : Type} {s u : PanSemStateFiniteExact 64 F} {e c : BitVec 64} (x : MlS)
    (v : ValueHOL 64) (hx : x ≠ ofString "child") (h : ICSW s u e c) :
    ICSW s (setVarHOLFinite x v u) e c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, guestInv_congr (s := u) rfl rfl rfl rfl h4, ?_, h6⟩
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h5]
  intro h; exact absurd h hx

/-- Write frame of `incorporate_child_on_success`. -/
def ICSPost {F : Type} (s : PanSemStateFiniteExact 64 F) (keep : List Ivl)
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ ArenaReady post ∧
  (∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = s.globals.lookup k) ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
  FrameOutside s post keep (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")

theorem icsPost_locIns {F : Type} (s : PanSemStateFiniteExact 64 F) (keep : List Ivl) :
    LocIns (fun (_ : ValueHOL 64) t => ICSPost s keep t) := by
  intro v t M ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, arenaReady_locals t M h3, h4, h5, h6⟩

theorem ne_off_of_not_hits {a e : BitVec 64} {n : Nat} (k : BitVec 64) (hk : k.toNat < n)
    (he : e.toNat + n ≤ 2 ^ 64) (h : ¬ CellHits a.toNat (e.toNat, n)) : a ≠ e + k := by
  rintro rfl
  apply h
  have : (e + k).toNat = e.toNat + k.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  unfold CellHits; rw [this]; omega

attribute [local irreducible] Ret in
theorem ics_prefix {F : Type} (s : PanSemStateFiniteExact 64 F) (e c : BitVec 64) (rest : ProgHOL 64)
    (Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (hcode : s.code = originalRuntimeCode)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hc : s.locals.lookup (ofString "child") = some (.val (.word c)))
    (hG : GuestInv s)
    (hk : ∀ X, ICSW s X e c → Ret X rest Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "incorporate_child_on_error")
      [.var .local (ofString "child")]) rest) Φ := by
  refine Ret.seq_call00 fun values body callee ret v cpost h1 h2 h3 => ?_
  obtain ⟨v1, rfl, he1⟩ := evalList1_inv _ _ h1
  rw [ev_loc, hc] at he1
  obtain ⟨rfl, rfl⟩ := lk1 hcode lookup_incorporate_child_on_error c
    (by rw [← Option.some.inj he1]) h2
  obtain ⟨pg, ⟨w1, w2, w3, pm⟩, pc, pd⟩ := Ret.apply
    (incorporate_child_on_error_run (callEntryStateHOLFinite s _) e he) h3
  apply hk
  refine ⟨pc, pd, pg, guestInv_congr (s := cpost) rfl rfl rfl rfl
    (guestInv_post (guestInv_callEntry _ _ hG) h3), hc, fun a a1 a2 a3 _ => ?_⟩
  change cpost.memory a = _
  rw [pm, updW_ne _ _ _ _ a3, updW_ne _ _ _ _ a2, updW_ne _ _ _ _ a1]; rfl

/-- Preserve the child's gas credit when entering the success-incorporation prefix. -/
theorem modular_repay_gas_le (g spill repay : BitVec 64)
    (hr : repay.toNat ≤ spill.toNat) :
    (g + repay).toNat + (spill - repay).toNat ≤ g.toNat + spill.toNat := by
  have hsub : (spill - repay).toNat = spill.toNat - repay.toNat :=
    BitVec.toNat_sub_of_le hr
  rw [BitVec.toNat_add, hsub]
  have hm := Nat.mod_le (g.toNat + repay.toNat) (2 ^ 64)
  omega

attribute [local irreducible] Ret in
/-- The error-incorporation call supplies both its write frame and gas credit. -/
theorem ics_prefix_gas {F : Type} (s : PanSemStateFiniteExact 64 F) (e c : BitVec 64)
    (rest : ProgHOL 64) (Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (hcode : s.code = originalRuntimeCode)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hc : s.locals.lookup (ofString "child") = some (.val (.word c)))
    (hG : GuestInv s)
    (hsep : c + 72 ≠ e + 64 ∧ c + 184 ≠ e + 64 ∧ c + 184 ≠ e + 72)
    (hk : ∀ X, ICSW s X e c →
      (readW X (e + 64)).toNat + (readW X (e + 192)).toNat ≤
        (readW s (e + 64)).toNat + (readW s (c + 64)).toNat +
          (readW s (e + 192)).toNat → Ret X rest Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "incorporate_child_on_error")
      [.var .local (ofString "child")]) rest) Φ := by
  refine Ret.seq_call00 fun values body callee ret v cpost h1 h2 h3 => ?_
  obtain ⟨v1, rfl, he1⟩ := evalList1_inv _ _ h1
  rw [ev_loc, hc] at he1
  obtain ⟨rfl, rfl⟩ := lk1 hcode lookup_incorporate_child_on_error c
    (by rw [← Option.some.inj he1]) h2
  have hchild : (callEntryStateHOLFinite s
      (HolFiniteMapExact.empty.update (ofString "child", .val (.word c)))).locals.lookup
      (ofString "child") = some (.val (.word c)) := by
    simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨pg, pc, pd, _, pm⟩ := Ret.apply
    (incorporate_child_on_error_exact (callEntryStateHOLFinite s _) e c he hchild hsep) h3
  apply hk
  · refine ⟨pc, pd, pg, guestInv_congr (s := cpost) rfl rfl rfl rfl
      (guestInv_post (guestInv_callEntry _ _ hG) h3), hc, fun a a1 a2 a3 _ => ?_⟩
    change cpost.memory a = _
    rw [pm, updW_ne _ _ _ _ a3, updW_ne _ _ _ _ a2, updW_ne _ _ _ _ a1]; rfl
  · exact incorporate_child_on_error_head_gas (callEntryStateHOLFinite s _) cpost e c
      he hchild hsep v h3

/-- Write frame of the `incorporate_child_on_success` tail (from the `ev+96` store on). -/
def ICSTail {F : Type} (X : PanSemStateFiniteExact 64 F) (e : BitVec 64) (T : Nat)
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  post.code = X.code ∧ post.memaddrs = X.memaddrs ∧ ArenaReady post ∧
  (∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = X.globals.lookup k) ∧
  globN X "heap_ptr" ≤ globN post "heap_ptr" ∧
  ∀ a : BitVec 64, a ≠ e + 96 → (∀ i ∈ htabFootprint X T, ¬ CellHits a.toNat i) →
    ¬ CellHits a.toNat (globN X "heap_ptr", globN post "heap_ptr" - globN X "heap_ptr") →
    post.memory a = X.memory a

theorem ivlUnhit_updW {F : Type} (X : PanSemStateFiniteExact 64 F) (b w : BitVec 64) (i : Ivl)
    (h : ¬ CellHits b.toNat i) :
    Wave8Contracts.M08.IvlUnhit X { X with memory := updW X.memory b w } i := by
  intro a _ h1 h2
  have : a ≠ b := by
    rintro rfl; apply h; unfold CellHits; omega
  change updW X.memory b w a = _
  rw [updW_ne _ _ _ _ this]

attribute [local irreducible] Ret in
theorem ics_tail {F : Type} (X : PanSemStateFiniteExact 64 F) (e tw : BitVec 64)
    (hcode : X.code = originalRuntimeCode)
    (he : X.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hA : ArenaReady X) (htw : X.memory (e + 136) = .word tw)
    (hwf : HtabWF X tw.toNat) (hal : ∀ i ∈ htabFootprint X tw.toNat, Allocated X i)
    (h96 : ∀ i ∈ htabFootprint X tw.toNat, ¬ CellHits (e + 96).toNat i) :
    Ret X (.seq (.store (.op .add [.var .global (ofString "ev"), .const 96])
        (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 96]),
          .load .one (.op .add [.var .local (ofString "child"), .const 96])]))
      (.seq (.call (some (none, none)) (ofString "htab_union_into")
          [.load .one (.op .add [.var .global (ofString "ev"), .const 136]),
           .load .one (.op .add [.var .local (ofString "child"), .const 136])])
        (.return (.const 0))))
      (fun _ post => ICSTail X e tw.toNat post) := by
  refine Ret.storeGlobOp he fun w => ?_
  generalize hX' : ({ X with memory := updW X.memory (e + 96) w } : PanSemStateFiniteExact 64 F) = X'
  have hX'c : X'.code = X.code := by rw [← hX']
  have hX'd : X'.memaddrs = X.memaddrs := by rw [← hX']
  have hX'g : X'.globals = X.globals := by rw [← hX']
  have hX'l : X'.locals = X.locals := by rw [← hX']
  have hun : ∀ i ∈ htabFootprint X tw.toNat, Wave8Contracts.M08.IvlUnhit X X' i := fun i hi => by
    rw [← hX']; exact ivlUnhit_updW X _ w i (h96 i hi)
  have hG' : GuestInv X' := guestInv_congr hX'c hX'd (by rw [← hX']) (by rw [← hX']) hA.1
  have hA' : ArenaReady X' := ⟨hG', arenaOK_congr hX'g hA.2⟩
  have ht_fp : ((tw.toNat, 88) : Ivl) ∈ htabFootprint X tw.toNat := by simp [htabFootprint]
  have ht8 : tw.toNat % 8 = 0 := (hwf.1 _ ht_fp).2.1
  have hthi : tw.toNat + 88 ≤ 2 ^ 64 := by
    have := (hwf.1 _ ht_fp).1; unfold Inside at this
    have : heapEnd ≤ 2 ^ 64 := by decide
    simp only at *; omega
  have hfpeq := (Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit ht8 hthi (hun _ ht_fp)).2
  have hwf' : HtabWF X' tw.toNat := Wave8Contracts.M08.htabWF_congr_unhit hA.1 hG' hwf hun
  have hal' : ∀ i ∈ htabFootprint X' tw.toNat, Allocated X' i := by
    rw [hfpeq]; intro i hi
    have := hal i hi
    unfold Allocated at this ⊢
    simp only [globN, hX'g] at this ⊢; exact this
  have h136 : X'.memory (e + 136) = .word tw := by
    rw [← hX']; change updW X.memory (e + 96) w (e + 136) = _
    rw [updW_ne _ _ _ _ (by bv_omega)]; exact htw
  have he' : X'.globals.lookup (ofString "ev") = some (.val (.word e)) := by rw [hX'g]; exact he
  refine Ret.seq_call00 fun values body callee ret v cpost h1 h2 h3 => ?_
  obtain ⟨v1, v2, rfl, hv1, _⟩ := evalList2_inv _ _ _ h1
  have hv1' := ev_load_glob X' _ e 136 he' v1 hv1
  rw [h136] at hv1'
  subst hv1'
  obtain ⟨_, hdst⟩ := rb_param_at X'.code.lookup (ofString "htab_union_into") []
    (ofString "dst") .one [(ofString "src", .one)] _ _
    (by simp only [List.mem_singleton]; rintro _ rfl; decide)
    (by rw [hX'c, hcode]; simpa using UXT.HtabUnionInto.lookup_htab_union_into) (vpre := []) (by simp) h2
  have hlocT : locN (callEntryStateHOLFinite X' callee) "dst" = tw.toNat := by
    simp only [locN, callEntryStateHOLFinite, hdst]
  have hPc : UnionArgWF (callEntryStateHOLFinite X' callee) := by
    refine ⟨(arenaReady_with_locals X' callee (X'.clock - 1)).2 hA', ?_, ?_⟩
    · rw [hlocT]; exact (htabWF_with_locals X' callee (X'.clock - 1) _).2 hwf'
    · rw [hlocT]; exact hal'
  have hQ := HtabC00Ports.FunSpec.at_lookup UXT.rb_htab_union_into_spec X' (by rw [hX'c, hcode])
    _ body callee ret h2 hPc (by rw [h3]; simp)
  rw [h3] at hQ
  have hx := hQ v rfl
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite X' callee) body
  rw [h3] at hmeta
  obtain ⟨hAR, _, _, _, hgrow, _, hfr, hglob⟩ := hx
  rw [hlocT] at hfr
  refine Ret.ret fun val _ => ?_
  refine ⟨hmeta.1.trans hX'c, hmeta.2.1.trans hX'd, ?_, ?_, ?_, ?_⟩
  · exact arenaReady_locals _ _ (arenaReady_locals _ _ hAR)
  · intro k hk
    have := hglob k (by simpa using hk)
    change cpost.globals.lookup k = _
    rw [← this]; change X'.globals.lookup k = _; rw [hX'g]
  · have : globN (callEntryStateHOLFinite X' callee) "heap_ptr" = globN X "heap_ptr" := by
      simp only [globN, callEntryStateHOLFinite, hX'g]
    rw [this] at hgrow; exact hgrow
  · intro a ha hk hf
    have hgX : globN (callEntryStateHOLFinite X' callee) "heap_ptr" = globN X "heap_ptr" := by
      simp only [globN, callEntryStateHOLFinite, hX'g]
    have h1 := hfr a (by
        intro i hi
        have hi' : i ∈ htabFootprint X' tw.toNat := hi
        rw [hfpeq] at hi'; exact hk i hi')
      (by rw [hgX]; exact hf)
    change cpost.memory a = _
    rw [h1]; change X'.memory a = _
    rw [← hX']; change updW X.memory (e + 96) w a = _
    rw [updW_ne _ _ _ _ ha]

theorem Ret.dec_ins {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hΦ : LocIns Φ)
    (h : ∀ val, ev s init = some val → Ret (setVarHOLFinite x val s) body Φ) :
    Ret s (.dec x sh init body) Φ :=
  Ret.dec fun val hv => Ret.mono (h val hv) fun v t ht => hΦ v t _ ht


theorem noHit_of_disj {a : Nat} {i j : Ivl} (hd : Disj i j) (hj : 0 < j.2)
    (hi : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    ¬ CellHits a j := by
  obtain ⟨i1, i2⟩ := i; obtain ⟨j1, j2⟩ := j
  unfold Disj at hd; unfold CellHits; dsimp only at hd hi ⊢; omega

theorem tn_add (e : BitVec 64) (k : Nat) (hk : k < 2 ^ 64) (h : e.toNat + k < 2 ^ 64) :
    (e + BitVec.ofNat 64 k).toNat = e.toNat + k := toNat_add_ofNat e k h

theorem child_error_separated (e c : BitVec 64)
    (he : e.toNat + 280 ≤ 2 ^ 64) (hc : c.toNat + 280 ≤ 2 ^ 64)
    (hd : Disj (e.toNat, 280) (c.toNat, 280)) :
    c + 72 ≠ e + 64 ∧ c + 184 ≠ e + 64 ∧ c + 184 ≠ e + 72 := by
  have hne (i j : Nat) (hi : i < 280) (hj : j < 280) :
      c + BitVec.ofNat 64 i ≠ e + BitVec.ofNat 64 j := by
    intro h
    have hn := congrArg BitVec.toNat h
    rw [tn_add c i (by omega) (by omega), tn_add e j (by omega) (by omega)] at hn
    unfold Disj at hd
    dsimp only at hd
    omega
  exact ⟨hne 72 64 (by omega) (by omega), hne 184 64 (by omega) (by omega),
    hne 184 72 (by omega) (by omega)⟩

/-- Disjoint child/parent records discharge all cross-store separation obligations. -/
theorem incorporate_child_on_error_gas_of_disj {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (e c : BitVec 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hc : s.locals.lookup (ofString "child") = some (.val (.word c)))
    (heB : e.toNat + 280 ≤ 2 ^ 64) (hcB : c.toNat + 280 ≤ 2 ^ 64)
    (hd : Disj (e.toNat, 280) (c.toNat, 280))
    (v : ValueHOL 64)
    (hr : evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_incorporate_child_on_error) = (some (.returned v), post)) :
    memW post (e.toNat + 64) + memW post (e.toNat + 192) ≤
      memW s (e.toNat + 64) + memW s (c.toNat + 64) + memW s (e.toNat + 192) :=
  incorporate_child_on_error_gas s post e c he hc (child_error_separated e c heB hcB hd)
    (by omega) (by omega) v hr


theorem noHit_mono {a x y w z : Nat} (h : ¬ CellHits a (x, z - x)) (h1 : x ≤ y) (h2 : y ≤ w)
    (h3 : w ≤ z) : ¬ CellHits a (y, w - y) := by
  unfold CellHits at h ⊢; dsimp only at h ⊢; omega

theorem noFresh_of_alloc {F : Type} {s : PanSemStateFiniteExact 64 F} {i : Ivl} {a h1 : Nat}
    (hA : ArenaOK s) (hi : Allocated s i) (ha : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2)
    (hh : h1 ≤ globN s "scratch_ptr")
    (hh0 : globN s "heap_ptr" ≤ h1) : ¬ CellHits a (globN s "heap_ptr", h1 - globN s "heap_ptr") := by
  obtain ⟨i1, i2⟩ := i
  obtain ⟨_, _, _, _, _⟩ := hA
  unfold CellHits; dsimp only at ha ⊢
  rcases hi with hi | hi <;> (unfold Inside at hi; dsimp only at hi; omega)

theorem htab_fp_pos {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat} (h : HtabWF s t) :
    ∀ i ∈ htabFootprint s t, 0 < i.2 := by
  obtain ⟨_, _, hk1, _, hk2, _⟩ := h
  intro i hi
  simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> dsimp only
  · omega
  · rw [hk2]; apply Nat.mul_pos (by omega); omega
  · omega
  · omega

/-- The success tail's log-count store and table union preserve both gas words. -/
theorem icsTail_gas {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e : BitVec 64} {T : Nat} (h : ICSTail s e T post)
    (heB : e.toNat + 200 ≤ 2 ^ 64) (heS : heapLimit ≤ e.toNat)
    (hwf : HtabWF s T)
    (hdisj : ∀ i ∈ htabFootprint s T, Disj (e.toNat, 280) i) :
    readW post (e + 64) = readW s (e + 64) ∧
      readW post (e + 192) = readW s (e + 192) := by
  have hbound : globN post "heap_ptr" ≤ heapLimit := h.2.2.1.2.2.1
  have hkeep (k : Nat) (hk : k = 64 ∨ k = 192) :
      post.memory (e + BitVec.ofNat 64 k) = s.memory (e + BitVec.ofNat 64 k) := by
    have hkb : k < 200 := by omega
    have hkn : (e + BitVec.ofNat 64 k).toNat = e.toNat + k :=
      tn_add e k (by omega) (by omega)
    apply h.2.2.2.2.2
    · rcases hk with rfl | rfl <;> bv_omega
    · intro i hi
      apply noHit_of_disj (hdisj i hi)
      · exact htab_fp_pos hwf i hi
      · rw [hkn]; dsimp only; omega
    · unfold CellHits
      rw [hkn]
      dsimp only
      have hhp := h.2.2.2.2.1
      omega
  constructor
  · change readW post (e + BitVec.ofNat 64 64) = readW s (e + BitVec.ofNat 64 64)
    unfold readW; rw [hkeep 64 (Or.inl rfl)]
  · change readW post (e + BitVec.ofNat 64 192) = readW s (e + BitVec.ofNat 64 192)
    unfold readW; rw [hkeep 192 (Or.inr rfl)]

/-- Appending child logs preserves the parent's two gas words, including when
the append loop reallocates its backing array. -/
theorem laInv_gas {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e L arr cap n nc : BitVec 64} (h : LAInv s L arr cap n nc post)
    (heB : e.toNat + 200 ≤ 2 ^ 64) (heS : heapLimit ≤ e.toNat)
    (hLB : L.toNat + 24 ≤ 2 ^ 64)
    (hcap : 0 < cap.toNat)
    (hL : Disj (e.toNat, 280) (L.toNat, 24))
    (hA : Disj (e.toNat, 280) (arr.toNat, 8 * cap.toNat)) :
    readW post (e + 64) = readW s (e + 64) ∧
      readW post (e + 192) = readW s (e + 192) := by
  have ne_of_not_hits {a x : BitVec 64} {b n : Nat} (hn : ¬ CellHits a.toNat (b, n))
      (hx : b ≤ x.toNat ∧ x.toNat + 8 ≤ b + n) : a ≠ x := by
    rintro rfl; apply hn; unfold CellHits; omega
  obtain ⟨_, _, hAR, _, hhp, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfr⟩ := h
  have hbound : globN post "heap_ptr" ≤ heapLimit := hAR.2.2.1
  have hkeep (k : Nat) (hk : k = 64 ∨ k = 192) :
      post.memory (e + BitVec.ofNat 64 k) = s.memory (e + BitVec.ofNat 64 k) := by
    have hkb : k < 200 := by omega
    have hkn : (e + BitVec.ofNat 64 k).toNat = e.toNat + k :=
      tn_add e k (by omega) (by omega)
    have hL0 : ¬ CellHits (e + BitVec.ofNat 64 k).toNat (L.toNat, 24) :=
      noHit_of_disj hL (by dsimp only; omega) (by rw [hkn]; dsimp only; omega)
    apply hfr
    · exact noHit_of_disj hA (by dsimp only; omega) (by rw [hkn]; dsimp only; omega)
    · unfold CellHits; rw [hkn]; dsimp only; omega
    · exact ne_of_not_hits hL0 (by omega)
    · apply ne_of_not_hits hL0
      change L.toNat ≤ (L + BitVec.ofNat 64 8).toNat ∧
        (L + BitVec.ofNat 64 8).toNat + 8 ≤ L.toNat + 24
      rw [tn_add L 8 (by omega) (by omega)]; omega
    · apply ne_of_not_hits hL0
      change L.toNat ≤ (L + BitVec.ofNat 64 16).toNat ∧
        (L + BitVec.ofNat 64 16).toNat + 8 ≤ L.toNat + 24
      rw [tn_add L 16 (by omega) (by omega)]; omega
  constructor
  · change readW post (e + BitVec.ofNat 64 64) = readW s (e + BitVec.ofNat 64 64)
    unfold readW; rw [hkeep 64 (Or.inl rfl)]
  · change readW post (e + BitVec.ofNat 64 192) = readW s (e + BitVec.ofNat 64 192)
    unfold readW; rw [hkeep 192 (Or.inr rfl)]

/-- A log-array reallocation stays below the heap pointer; without reallocation
the saved scratch-release mark remains valid for the original backing array. -/
theorem laInv_logs_release {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {L arr cap n nc : BitVec 64} (h : LAInv s L arr cap n nc post)
    {cm : Nat}
    (hold : Inside (arr.toNat, 8 * cap.toNat) sourceBase (globN s "heap_ptr") ∨
      Inside (arr.toNat, 8 * cap.toNat) cm scratchEnd)
    (hsource : sourceBase ≤ globN s "heap_ptr") :
    Inside ((readW post L).toNat, 8 * (readW post (L + 16)).toNat)
      sourceBase (globN post "heap_ptr") ∨
    Inside ((readW post L).toNat, 8 * (readW post (L + 16)).toNat) cm scratchEnd := by
  obtain ⟨_, _, _, _, hhp, _, i, arr', cap', _, _, hm0, _, hm16, _, _, _, _, hloc, _⟩ := h
  simp only [readW, hm0, hm16]
  rcases hloc with ⟨rfl, rfl⟩ | ⟨hlo, hhi⟩
  · rcases hold with ⟨hlo, hhi⟩ | hs
    · exact Or.inl ⟨hlo, hhi.trans hhp⟩
    · exact Or.inr hs
  · exact Or.inl ⟨hsource.trans hlo, hhi⟩

/-- Frame of a full `incorporate_child_on_success` run. -/
def ICSFrame {F : Type} (s : PanSemStateFiniteExact 64 F) (e L arr0 cap0 tw : BitVec 64)
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ ArenaReady post ∧
  (∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = s.globals.lookup k) ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
  ∀ a : BitVec 64, ¬ CellHits a.toNat (e.toNat + 64, 136) → ¬ CellHits a.toNat (L.toNat, 24) →
    ¬ CellHits a.toNat (arr0.toNat, 8 * cap0.toNat) →
    (∀ i ∈ htabFootprint s tw.toNat, ¬ CellHits a.toNat i) →
    ¬ CellHits a.toNat (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") →
    post.memory a = s.memory a

theorem icsFrame_locIns {F : Type} (s : PanSemStateFiniteExact 64 F) (e L arr0 cap0 tw : BitVec 64) :
    LocIns (fun (_ : ValueHOL 64) t => ICSFrame s e L arr0 cap0 tw t) := by
  intro v t M ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, arenaReady_locals t M h3, h4, h5, h6⟩

theorem ne_of_not_hits {a x : BitVec 64} {b n : Nat} (h : ¬ CellHits a.toNat (b, n))
    (hx : b ≤ x.toNat ∧ x.toNat + 8 ≤ b + n) : a ≠ x := by
  rintro rfl; apply h; unfold CellHits; omega

attribute [local irreducible] Ret in
theorem incorporate_child_on_success_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e c L arr0 cap0 n0 cl nc tw : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hc : s.locals.lookup (ofString "child") = some (.val (.word c)))
    (hA : ArenaReady s)
    (hm88 : s.memory (e + 88) = .word L) (hd88 : s.memaddrs (e + 88))
    (hmL : s.memory L = .word arr0) (hmL8 : s.memory (L + 8) = .word n0)
    (hmL16 : s.memory (L + 16) = .word cap0)
    (hdL0 : s.memaddrs L) (hdL8 : s.memaddrs (L + 8)) (hdL16 : s.memaddrs (L + 16))
    (hmc : s.memory (c + 88) = .word cl) (hmn : s.memory (cl + 8) = .word nc)
    (hm136 : s.memory (e + 136) = .word tw)
    (he200 : e.toNat + 200 ≤ 2 ^ 64) (heS : heapLimit ≤ e.toNat)
    (hLw : L.toNat + 24 ≤ 2 ^ 64) (hLE : Disj (L.toNat, 24) (e.toNat + 64, 136))
    (hAE : Disj (arr0.toNat, 8 * cap0.toNat) (e.toNat + 64, 136))
    (hLA : L.toNat + 24 ≤ arr0.toNat ∨ arr0.toNat + 8 * cap0.toNat ≤ L.toNat)
    (hLh : L.toNat + 24 ≤ globN s "heap_ptr" ∨ heapLimit ≤ L.toNat)
    (hcE : c.toNat + 96 ≤ 2 ^ 64 ∧ Disj (c.toNat + 88, 8) (e.toNat + 64, 136))
    (hclE : cl.toNat + 16 ≤ 2 ^ 64 ∧ Disj (cl.toNat + 8, 8) (e.toNat + 64, 136))
    (hn0c : n0.toNat ≤ cap0.toNat) (hcap : cap0.toNat < 2 ^ 59) (hcap1 : 1 ≤ cap0.toNat)
    (harr : arr0.toNat + 8 * cap0.toNat ≤ 2 ^ 64)
    (hsum : n0.toNat + nc.toNat < 2 ^ 58)
    (hwf : HtabWF s tw.toNat) (hal : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hfpE : ∀ i ∈ htabFootprint s tw.toNat, Disj i (e.toNat + 64, 136))
    (hfpL : ∀ i ∈ htabFootprint s tw.toNat, Disj i (L.toNat, 24))
    (hfpA : ∀ i ∈ htabFootprint s tw.toNat, Disj i (arr0.toNat, 8 * cap0.toNat)) :
    Ret s (sourceFnBody Guest.Software.guestFn_incorporate_child_on_success)
      (fun _ post => ICSFrame s e L arr0 cap0 tw post) := by
  have hb : sourceFnBody Guest.Software.guestFn_incorporate_child_on_success =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_incorporate_child_on_success).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_incorporate_child_on_success,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  have hΦ := icsFrame_locIns s e L arr0 cap0 tw
  refine ics_prefix s e c _ _ hcode he hc hA.1 fun X hX => ?_
  have hXg : X.globals.lookup (ofString "ev") = some (.val (.word e)) := by rw [hX.2.2.1]; exact he
  refine Ret.storeGlobOp hXg fun w1 => ?_
  have hX1 := icsw_store 192 w1 (by simp) hX
  refine Ret.dec_ins hΦ fun vrep _ => ?_
  have hX2 := icsw_setVar (ofString "rep") vrep (by decide) hX1
  refine Ret.seq_flw (NoRet.ite NoRet.assign NoRet.skip)
    (Flw.mono (Ψ1 := fun _ t => ICSW s t e c) ?_ ?_)
  · exact Flw.ite fun w _ => ⟨fun _ => Flw.assign fun v _ => icsw_setVar _ v (by decide) hX2,
      fun _ => Flw.skip hX2⟩
  intro _ Y hY _
  have hYg : Y.globals.lookup (ofString "ev") = some (.val (.word e)) := by rw [hY.2.2.1]; exact he
  refine Ret.storeGlobOp hYg fun w2 => ?_
  refine Ret.storeGlobOp hYg fun w3 => ?_
  refine Ret.storeGlobOp hYg fun w4 => ?_
  have hY3 := icsw_store 192 w4 (by simp) (icsw_store 72 w3 (by simp) (icsw_store 64 w2 (by simp) hY))
  generalize hZ0 : ({ { { Y with memory := updW Y.memory (e + 64) w2 } with
    memory := updW (updW Y.memory (e + 64) w2) (e + 72) w3 } with
    memory := updW (updW (updW Y.memory (e + 64) w2) (e + 72) w3) (e + 192) w4 } :
      PanSemStateFiniteExact 64 F) = Z0 at hY3 ⊢
  obtain ⟨hZc, hZd, hZg, hZG, hZl, hZm⟩ := hY3
  have hE64 : (e + 64).toNat = e.toNat + 64 := tn_add e 64 (by omega) (by omega)
  have hE72 : (e + 72).toNat = e.toNat + 72 := tn_add e 72 (by omega) (by omega)
  have hE184 : (e + 184).toNat = e.toNat + 184 := tn_add e 184 (by omega) (by omega)
  have hE192 : (e + 192).toNat = e.toNat + 192 := tn_add e 192 (by omega) (by omega)
  -- cells outside `(e+64, 136)` are untouched in `Z0`
  have hZo : ∀ a : BitVec 64, ¬ CellHits a.toNat (e.toNat + 64, 136) → Z0.memory a = s.memory a := by
    intro a ha
    refine hZm a ?_ ?_ ?_ ?_ <;> refine ne_of_not_hits ha ?_
    · rw [hE64]; omega
    · rw [hE72]; omega
    · rw [hE184]; omega
    · rw [hE192]; omega
  have hZ88 : Z0.memory (e + 88) = .word L := by
    rw [hZm _ (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)]; exact hm88
  have hcl : Z0.memory (c + 88) = .word cl := by
    have h1 : (c + 88).toNat = c.toNat + 88 := tn_add c 88 (by omega) (by omega)
    rw [hZo _ (noHit_of_disj hcE.2 (by simp) (by rw [h1]; simp))]
    exact hmc
  have hncl : Z0.memory (cl + 8) = .word nc := by
    have h1 : (cl + 8).toNat = cl.toNat + 8 := tn_add cl 8 (by omega) (by omega)
    rw [hZo _ (noHit_of_disj hclE.2 (by simp) (by rw [h1]; simp))]
    exact hmn
  refine Ret.dec_ins hΦ fun vcl hvcl => ?_
  rw [ev_load_loc Z0 _ c 88 hZl vcl hvcl, hcl] at *
  clear hvcl
  refine Ret.dec_ins hΦ fun vn hvn => ?_
  have hcl' : (setVarHOLFinite (ofString "cl") (.val (.word cl)) Z0).locals.lookup (ofString "cl") =
    some (.val (.word cl)) := setVar_lookup_eq _ _ _
  have := ev_load_loc _ _ cl 8 hcl' vn hvn
  rw [show (setVarHOLFinite (ofString "cl") (.val (.word cl)) Z0).memory = Z0.memory from rfl,
    hncl] at this
  subst this; clear hvn
  refine Ret.dec_ins hΦ fun vp _ => ?_
  refine Ret.dec_ins hΦ fun vi hvi => ?_
  rw [ev_const] at hvi; cases hvi
  generalize hW : setVarHOLFinite (ofString "i") (.val (.word 0)) (setVarHOLFinite (ofString "p") vp
    (setVarHOLFinite (ofString "n") (.val (.word nc))
      (setVarHOLFinite (ofString "cl") (.val (.word cl)) Z0))) = W
  have hWm : W.memory = Z0.memory := by rw [← hW]; rfl
  have hWc : W.code = Z0.code := by rw [← hW]; rfl
  have hWd : W.memaddrs = Z0.memaddrs := by rw [← hW]; rfl
  have hWg : W.globals = Z0.globals := by rw [← hW]; rfl
  have hWi : W.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    rw [← hW]; exact setVar_lookup_eq _ _ _
  have hWn : W.locals.lookup (ofString "n") = some (.val (.word nc)) := by
    rw [← hW, setVar_lookup_ne _ _ _ _ (by decide), setVar_lookup_ne _ _ _ _ (by decide)]
    exact setVar_lookup_eq _ _ _
  have hWchild : W.locals.lookup (ofString "child") = some (.val (.word c)) := by
    rw [← hW, setVar_lookup_ne _ _ _ _ (by decide), setVar_lookup_ne _ _ _ _ (by decide),
      setVar_lookup_ne _ _ _ _ (by decide), setVar_lookup_ne _ _ _ _ (by decide)]
    exact hZl
  have hWG : GuestInv W := guestInv_congr hWc hWd (by rw [← hW]; rfl) (by rw [← hW]; rfl) hZG
  have hWA : ArenaReady W := ⟨hWG, arenaOK_congr (hWg.trans hZg) hA.2⟩
  have hWgl : W.globals = s.globals := hWg.trans hZg
  have hgW : globN W "heap_ptr" = globN s "heap_ptr" := by simp only [globN, hWgl]
  have hWo : ∀ a : BitVec 64, ¬ CellHits a.toNat (e.toNat + 64, 136) → W.memory a = s.memory a :=
    fun a ha => by rw [hWm]; exact hZo a ha
  have hL8 : (L + 8).toNat = L.toNat + 8 := tn_add L 8 (by omega) (by omega)
  have hL16 : (L + 16).toNat = L.toNat + 16 := tn_add L 16 (by omega) (by omega)
  have hLo : ∀ k : Nat, k ≤ 16 → ¬ CellHits (L.toNat + k) (e.toNat + 64, 136) := fun k hk =>
    noHit_of_disj hLE (by simp) (by simp only; omega)
  have hWL0 : W.memory L = .word arr0 := by rw [hWo _ (by simpa using hLo 0 (by omega))]; exact hmL
  have hWL8 : W.memory (L + 8) = .word n0 := by rw [hWo _ (by rw [hL8]; exact hLo 8 (by omega))]; exact hmL8
  have hWL16 : W.memory (L + 16) = .word cap0 := by
    rw [hWo _ (by rw [hL16]; exact hLo 16 (by omega))]; exact hmL16
  have hWe : W.globals.lookup (ofString "ev") = some (.val (.word e)) := by rw [hWgl]; exact he
  have hE88 : (e + 88).toNat = e.toNat + 88 := tn_add e 88 (by omega) (by omega)
  have hLE' := hLE
  unfold Disj at hLE'; dsimp only at hLE'
  have hne0 : e + 88 ≠ L := fun h => by
    have := congrArg BitVec.toNat h; rw [hE88] at this; omega
  have hne8 : e + 88 ≠ L + 8 := fun h => by
    have := congrArg BitVec.toNat h; rw [hE88, hL8] at this; omega
  have hne16 : e + 88 ≠ L + 16 := fun h => by
    have := congrArg BitVec.toNat h; rw [hE88, hL16] at this; omega
  have hI0 : LAInv W L arr0 cap0 n0 nc W := by
    refine ⟨rfl, rfl, hWA, fun _ _ => rfl, le_refl _, hWn, 0, arr0, cap0, hWi, by simp, hWL0,
      by rw [show n0 + (0 : BitVec 64) = n0 from by bv_omega]; exact hWL8, hWL16, by simpa using hn0c, hcap, hcap1, harr,
      Or.inl ⟨rfl, rfl⟩, fun _ _ _ _ _ _ => rfl⟩
  refine Ret.seq_while_inv (LAInv W L arr0 cap0 n0 nc) hI0 (NoRet.seq NoRet.call0 NoRet.assign)
    (fun u hu hact _ => la_step W e L arr0 cap0 n0 nc _ hWe (by rw [hWd, hZd]; exact hd88)
      (by rw [hWm, hZ88]) ⟨?_, Or.inr (by rw [hE88]; omega), hne0, hne8, hne16⟩
      (by rw [hWd, hZd]; exact hdL0) (by rw [hWd, hZd]; exact hdL8) (by rw [hWd, hZd]; exact hdL16)
      hLw hLA (by rw [hgW]; exact hLh) hsum (fun t v hv => ev_load_word t _ v hv) u hu hact) ?_
  · exact noHit_of_disj (Wave8Contracts.M08.disj_symm hAE) (by simp only; omega)
      (by rw [hE88]; simp only; omega)
  intro T hT
  obtain ⟨uc, ud, uA, ug, uh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ufr⟩ := hT
  have hHL : heapLimit = scratchStart := rfl
  have hspT : globN T "scratch_ptr" = globN s "scratch_ptr" := by
    have := ug (ofString "scratch_ptr") (by decide)
    simp only [globN, this, hWgl]
  have hpT : globN T "heap_ptr" ≤ globN s "scratch_ptr" := by
    have := uA.2; obtain ⟨_, h2, h3, h4, _⟩ := this; rw [hHL] at h2; omega
  rw [hgW] at uh ufr
  have hTs : ∀ a : BitVec 64, ¬ CellHits a.toNat (e.toNat + 64, 136) → ¬ CellHits a.toNat (L.toNat, 24) →
      ¬ CellHits a.toNat (arr0.toNat, 8 * cap0.toNat) →
      ¬ CellHits a.toNat (globN s "heap_ptr", globN T "heap_ptr" - globN s "heap_ptr") →
      T.memory a = s.memory a := by
    intro a hE hL hAr hF
    rw [ufr a hAr hF (ne_of_not_hits hL (by omega))
      (ne_of_not_hits hL (by rw [hL8]; omega))
      (ne_of_not_hits hL (by rw [hL16]; omega))]
    exact hWo a hE
  have hun : ∀ i ∈ htabFootprint s tw.toNat, Wave8Contracts.M08.IvlUnhit s T i := by
    intro i hi a _ h1 h2
    have hin : i.1 ≤ a.toNat ∧ a.toNat + 8 ≤ i.1 + i.2 := ⟨h1, h2⟩
    exact hTs a (noHit_of_disj (hfpE i hi) (by simp) hin) (noHit_of_disj (hfpL i hi) (by simp) hin)
      (noHit_of_disj (hfpA i hi) (by simp only; omega) hin)
      (noFresh_of_alloc hA.2 (hal i hi) hin hpT uh)
  have ht_fp : ((tw.toNat, 88) : Ivl) ∈ htabFootprint s tw.toNat := by simp [htabFootprint]
  have ht8 : tw.toNat % 8 = 0 := (hwf.1 _ ht_fp).2.1
  have hthi : tw.toNat + 88 ≤ 2 ^ 64 := by
    have := (hwf.1 _ ht_fp).1; unfold Inside at this
    have : heapEnd ≤ 2 ^ 64 := by decide
    simp only at *; omega
  have hfpeq := (Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit ht8 hthi (hun _ ht_fp)).2
  have hwfT : HtabWF T tw.toNat := Wave8Contracts.M08.htabWF_congr_unhit hA.1 uA.1 hwf hun
  have halT : ∀ i ∈ htabFootprint T tw.toNat, Allocated T i := by
    rw [hfpeq]; intro i hi
    rcases hal i hi with h | h
    · exact Or.inl ⟨h.1, Nat.le_trans h.2 uh⟩
    · exact Or.inr (by rw [hspT]; exact h)
  have hE96 : (e + 96).toNat = e.toNat + 96 := tn_add e 96 (by omega) (by omega)
  have hE136 : (e + 136).toNat = e.toNat + 136 := tn_add e 136 (by omega) (by omega)
  have h96 : ∀ i ∈ htabFootprint T tw.toNat, ¬ CellHits (e + 96).toNat i := by
    rw [hfpeq]; intro i hi
    exact noHit_of_disj (Wave8Contracts.M08.disj_symm (hfpE i hi)) (htab_fp_pos hwf i hi)
      (by rw [hE96]; simp only; omega)
  have hT136 : T.memory (e + 136) = .word tw := by
    have hW136 : W.memory (e + 136) = .word tw := by
      rw [hWm, hZm _ (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)]; exact hm136
    rw [ufr _ (noHit_of_disj (Wave8Contracts.M08.disj_symm hAE) (by simp only; omega)
        (by rw [hE136]; simp only; omega))
      (by have := uA.2.2.1; rw [hHL] at this heS; unfold CellHits; rw [hE136]; dsimp only; omega)
      (fun h => by have := congrArg BitVec.toNat h; rw [hE136] at this; omega)
      (fun h => by have := congrArg BitVec.toNat h; rw [hE136, hL8] at this; omega)
      (fun h => by have := congrArg BitVec.toNat h; rw [hE136, hL16] at this; omega)]
    exact hW136
  have hTe : T.globals.lookup (ofString "ev") = some (.val (.word e)) := by
    rw [ug _ (by decide)]; exact hWe
  have hTcode : T.code = originalRuntimeCode := by rw [uc, hWc, hZc, hcode]
  refine Ret.mono (ics_tail T e tw hTcode hTe uA hT136 hwfT halT h96) ?_
  intro _ post ⟨pc, pd, pA, pg, ph, pm⟩
  have hgT : ∀ k : MlS, k ≠ ofString "heap_ptr" → T.globals.lookup k = s.globals.lookup k :=
    fun k hk => by rw [ug k hk, hWgl]
  refine ⟨pc.trans (uc.trans (hWc.trans (hZc))), pd.trans (ud.trans (hWd.trans hZd)), pA,
    fun k hk => (pg k hk).trans (hgT k hk), Nat.le_trans uh ph, ?_⟩
  intro a hE hL hAr hfp hF
  have hF1 : ¬ CellHits a.toNat (globN s "heap_ptr", globN T "heap_ptr" - globN s "heap_ptr") :=
    noHit_mono hF (Nat.le_refl _) uh ph
  have hF2 : ¬ CellHits a.toNat (globN T "heap_ptr", globN post "heap_ptr" - globN T "heap_ptr") :=
    noHit_mono hF uh ph (Nat.le_refl _)
  rw [pm a (ne_of_not_hits hE (by rw [hE96]; omega)) (by rw [hfpeq]; exact hfp) hF2]
  exact hTs a hE hL hAr hF1

/-- Every allocated object separated from the success-incorporation write
footprint is untouched, including across fresh heap allocation. -/
theorem icsFrame_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e L arr cap tw : BitVec 64} (h : ICSFrame s e L arr cap tw post)
    (hA : ArenaReady s) {i : Ivl} (hi : Allocated s i)
    (hE : Disj i (e.toNat + 64, 136))
    (hL : Disj i (L.toNat, 24))
    (hAr : Disj i (arr.toNat, 8 * cap.toNat)) (hcap : 0 < cap.toNat)
    (hwf : HtabWF s tw.toNat)
    (hT : ∀ j ∈ htabFootprint s tw.toNat, Disj i j) :
    Wave8Contracts.M08.IvlUnhit s post i := by
  intro a _ h1 h2
  have hin : i.1 ≤ a.toNat ∧ a.toNat + 8 ≤ i.1 + i.2 := ⟨h1, h2⟩
  apply h.2.2.2.2.2
  · exact noHit_of_disj hE (by simp) hin
  · exact noHit_of_disj hL (by simp) hin
  · exact noHit_of_disj hAr (by dsimp only; omega) hin
  · intro j hj; exact noHit_of_disj (hT j hj) (htab_fp_pos hwf j hj) hin
  · apply noFresh_of_alloc hA.2 hi hin _ h.2.2.2.2.1
    have hp := h.2.2.1.2.2.1
    have hs := hA.2.2.2.1
    have hs' := hA.2.2.2.2.1
    have heq : heapLimit = scratchStart := rfl
    rw [heq] at hp
    omega

/-- Cell-level success frame, allowing protected alignment cells in the same
parent record as the gas writes. -/
theorem icsFrame_memW {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e L arr cap tw : BitVec 64} (h : ICSFrame s e L arr cap tw post)
    (hA : ArenaReady s) {i : Ivl} (hi : Allocated s i) {a : Nat}
    (ha : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) (hab : a < 2 ^ 64)
    (hE : ¬ CellHits a (e.toNat + 64, 136))
    (hL : ¬ CellHits a (L.toNat, 24))
    (hAr : ¬ CellHits a (arr.toNat, 8 * cap.toNat))
    (hT : ∀ j ∈ htabFootprint s tw.toNat, ¬ CellHits a j) :
    memW post a = memW s a := by
  apply memW_of
  apply h.2.2.2.2.2
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using hE
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using hL
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using hAr
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using hT
  · have hp := h.2.2.1.2.2.1
    have hs := hA.2.2.2.1
    have hs' := hA.2.2.2.2.1
    have heq : heapLimit = scratchStart := rfl
    rw [heq] at hp
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using
      noFresh_of_alloc hA.2 hi ha (by omega) h.2.2.2.2.1

/-- Arena bounds are stronger than the explicit log-count bound: even the
backing-array capacity is below `2^25`. -/
theorem frameWF_logs_count_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} {ec : Ivl} (hA : ArenaOK s) (hf : FrameWF s S ec) :
    memW s (memW s (ec.1 + 88) + 8) < 2 ^ 25 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlen, hloc, _⟩ := hf
  have hhp := hA.2.1
  have hsp := hA.2.2.1
  have hfmsp := hA.2.2.2.1
  rcases hloc with h | h
  · unfold Inside frameLogs at h
    have hsb := R11Shards.sourceBase_val
    have hhl := R11Shards.heapLimit_val
    dsimp only at h
    omega
  · unfold Inside frameLogs at h
    have hss := R11Shards.scratchStart_val
    have hse := R11Shards.scratchEnd_val
    dsimp only at h
    omega

/-- Parent and child log counts jointly satisfy `LogsListOK`'s strict bound,
using their allocated backing-array bounds rather than separate count limits. -/
theorem frameWF_logs_combined_count_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} {ec₁ ec₂ : Ivl} (hA : ArenaOK s)
    (h₁ : FrameWF s S ec₁) (h₂ : FrameWF s S ec₂) :
    memW s (memW s (ec₁.1 + 88) + 8) +
      memW s (memW s (ec₂.1 + 88) + 8) < 2 ^ 28 := by
  have h₁b := frameWF_logs_count_bound hA h₁
  have h₂b := frameWF_logs_count_bound hA h₂
  omega

/-- Normal loop exit fixes the exact combined log count, without modular
wraparound. -/
theorem laInv_exit_count {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {L arr cap n nc : BitVec 64} (h : LAInv s L arr cap n nc post)
    (hnc : nc.toNat < 2 ^ 63)
    (hsum : n.toNat + nc.toNat < 2 ^ 64)
    (hexit : evalAt post (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "n"))) = some (.val (.word 0))) :
    (readW post (L + 8)).toNat = n.toNat + nc.toNat := by
  obtain ⟨_, _, _, _, _, hn, i, ar, cp, hi, hle, _, hm8, _⟩ := h
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp post .less _ _ 0 hexit
  simp [evalAt, evalHOLExact, hn, hi] at ha hb
  subst ha hb
  have hieq : i.toNat = nc.toNat := by
    by_contra hh
    have hlt : i.toNat < nc.toNat := by omega
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      Flapjack.Compiler.Encoders.Asm.holAsmSignedLess] at hcw
    split at hcw <;> omega
  simp only [readW, hm8, BitVec.toNat_add, hieq, Nat.mod_eq_of_lt hsum]

/-- Table union leaves the separated parent log header unchanged. -/
theorem icsTail_logHeader {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e L : BitVec 64} {T : Nat} (h : ICSTail s e T post)
    (hA : ArenaReady s) (hL : Allocated s (L.toNat, 24))
    (hLB : L.toNat + 24 ≤ 2 ^ 64)
    (hE : ¬ CellHits (e + 96).toNat (L.toNat, 24))
    (hT : ∀ j ∈ htabFootprint s T, Disj (L.toNat, 24) j)
    (hwf : HtabWF s T) :
    readW post L = readW s L ∧
      readW post (L + 8) = readW s (L + 8) ∧
      readW post (L + 16) = readW s (L + 16) := by
  have hkeep (k : Nat) (hk : k ≤ 16) :
      readW post (L + BitVec.ofNat 64 k) = readW s (L + BitVec.ofNat 64 k) := by
    have hkn : (L + BitVec.ofNat 64 k).toNat = L.toNat + k :=
      tn_add L k (by omega) (by omega)
    have hin : L.toNat ≤ (L + BitVec.ofNat 64 k).toNat ∧
        (L + BitVec.ofNat 64 k).toNat + 8 ≤ L.toNat + 24 := by rw [hkn]; omega
    unfold readW
    rw [h.2.2.2.2.2 _ (Ne.symm (ne_of_not_hits hE hin))
      (fun j hj => noHit_of_disj (hT j hj) (htab_fp_pos hwf j hj) hin) ?_]
    have hp := h.2.2.1.2.2.1
    have hs := hA.2.2.2.1
    have hs' := hA.2.2.2.2.1
    have heq : heapLimit = scratchStart := rfl
    rw [heq] at hp
    exact noFresh_of_alloc hA.2 hL hin (by omega) h.2.2.2.2.1
  exact ⟨by simpa using hkeep 0 (by omega), hkeep 8 (by omega), hkeep 16 (by omega)⟩

/-- Compose log-loop release bounds with the table-union tail. Both an
unchanged scratch array and a freshly allocated heap array remain releasable. -/
theorem laInv_icsTail_logs_release {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {e L arr cap n nc : BitVec 64}
    {T cm : Nat} (hloop : LAInv s L arr cap n nc mid)
    (htail : ICSTail mid e T post)
    (hL : Allocated mid (L.toNat, 24)) (hLB : L.toNat + 24 ≤ 2 ^ 64)
    (hE : ¬ CellHits (e + 96).toNat (L.toNat, 24))
    (hT : ∀ j ∈ htabFootprint mid T, Disj (L.toNat, 24) j)
    (hwf : HtabWF mid T)
    (hold : Inside (arr.toNat, 8 * cap.toNat) sourceBase (globN s "heap_ptr") ∨
      Inside (arr.toNat, 8 * cap.toNat) cm scratchEnd)
    (hsource : sourceBase ≤ globN s "heap_ptr") :
    Inside ((readW post L).toNat, 8 * (readW post (L + 16)).toNat)
      sourceBase (globN post "heap_ptr") ∨
    Inside ((readW post L).toNat, 8 * (readW post (L + 16)).toNat) cm scratchEnd := by
  obtain ⟨h0, _, h16⟩ := icsTail_logHeader htail hloop.2.2.1 hL hLB hE hT hwf
  rw [h0, h16]
  rcases laInv_logs_release hloop hold hsource with hh | hh
  · exact Or.inl ⟨hh.1, hh.2.trans htail.2.2.2.2.1⟩
  · exact Or.inr hh

/-- The exact combined log count survives the table-union tail. -/
theorem laInv_icsTail_exit_count {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {e L arr cap n nc : BitVec 64}
    {T : Nat} (hloop : LAInv s L arr cap n nc mid)
    (htail : ICSTail mid e T post)
    (hL : Allocated mid (L.toNat, 24)) (hLB : L.toNat + 24 ≤ 2 ^ 64)
    (hE : ¬ CellHits (e + 96).toNat (L.toNat, 24))
    (hT : ∀ j ∈ htabFootprint mid T, Disj (L.toNat, 24) j)
    (hwf : HtabWF mid T) (hnc : nc.toNat < 2 ^ 63)
    (hsum : n.toNat + nc.toNat < 2 ^ 64)
    (hexit : evalAt mid (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "n"))) = some (.val (.word 0))) :
    (readW post (L + 8)).toNat = n.toNat + nc.toNat := by
  obtain ⟨_, h8, _⟩ := icsTail_logHeader htail hloop.2.2.1 hL hLB hE hT hwf
  rw [h8]
  exact laInv_exit_count hloop hnc hsum hexit

/-- An exact count in a nonnull valid log list satisfies the invariant's
strict count bound. -/
theorem logsListOK_count_of_readW {F : Type} {post : PanSemStateFiniteExact 64 F}
    {L : BitVec 64} {n : Nat} (hL : L.toNat ≠ 0)
    (hLB : L.toNat + 16 ≤ 2 ^ 64)
    (hcount : (readW post (L + 8)).toNat = n)
    (hlogs : LogsListOK post L.toNat) : n < 2 ^ 28 := by
  rcases hlogs with hz | hh
  · exact False.elim (hL hz)
  · have hc := hh.2.2.1
    rw [readW_toNat] at hcount
    change memW post (L + BitVec.ofNat 64 8).toNat = n at hcount
    rw [tn_add L 8 (by omega) (by omega)] at hcount
    simpa only [hcount] using hc

/-- The success write frame preserves all four protected cells of every live
frame.  Separation follows from the input invariant, including for the parent
record that also contains the gas writes. -/
theorem icsFrame_chainCells {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e L arr cap tw : BitVec 64} (h : ICSFrame s e L arr cap tw post)
    (hI : EvmInv s)
    (he : e.toNat = globN s "ev")
    (hL : L.toNat = memW s (e.toNat + 88))
    (harr : arr.toNat = memW s L.toNat)
    (hcap : cap.toNat = memW s (L.toNat + 16))
    {S : List Nat} (hInv : Wave8Contracts.M23.EvmInvAt s S)
    (ht : tw.toNat ∈ S) : EvmEkFk.ChainCellsAgree s post := by
  obtain ⟨_, _, _, hFW, _, _, hPair, hSep, _⟩ := hInv.2
  let E := globN s "ev"
  let C := globN s "cur_cont"
  have hhead := head_mem_evmChain s
  have hcs : evmChain s = (E, C) :: (evmChain s).tail := evmChain_cons s
  have hL' : L.toNat = memW s (E + 88) := by simpa [E, he] using hL
  have hLogs : frameLogs s (E, C) = (arr.toNat, 8 * cap.toNat) := by
    simp only [frameLogs]
    rw [← hL', ← harr, ← hcap]
  rw [hcs, List.map_cons, List.flatten_cons, List.pairwise_append] at hPair
  obtain ⟨hP0, _, hcross⟩ := hPair
  have hP : ((E, 280) :: (C, 104) ::
      [(memW s (E + 8), 32 * memW s (E + 232)),
       (memW s (E + 24), memW s (E + 40)), (L.toNat, 24),
       (arr.toNat, 8 * cap.toNat), frameRet s (E, C)]).Pairwise Disj := by
    have := (List.pairwise_append.mp hP0).1
    simpa only [frameObjects, List.pairwise_append, hLogs, ← hL'] using this
  obtain ⟨hEsep, hP⟩ := List.pairwise_cons.mp hP
  obtain ⟨hCsep, _⟩ := List.pairwise_cons.mp hP
  have hcap0 : 0 < cap.toNat := by
    have hf := hFW (E, C) hhead
    have hh := hf.2.2.2.2.2.2.2.2.2.2.1
    have hh' : 1 ≤ cap.toNat := by simpa only [← hL', ← hcap] using hh
    omega
  have hmemTail (ec : Ivl) (hc : ec ∈ (evmChain s).tail) (i : Ivl)
      (hi : i ∈ frameObjects s ec) :
      i ∈ (((evmChain s).tail.map (frameObjects s)).flatten) :=
    List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hc, hi⟩
  intro ec hec
  have hf := hFW ec hec
  have hbounds := Wave8Contracts.M23.frameWF_bounds hI.1.2 hf
  have halloc (i : Ivl) (hi : i ∈ [(ec.1, 280), (ec.2, 104)]) : Allocated s i := by
    apply Or.inr
    exact (hf.1 i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; tauto)).1
  have hds (i : Ivl) (hi : i ∈ [(ec.1, 280), (ec.2, 104)]) :
      Disj i (L.toNat, 24) ∧ Disj i (arr.toNat, 8 * cap.toNat) := by
    rw [hcs] at hec
    rcases List.mem_cons.mp hec with rfl | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ⟨hEsep _ (by simp), hEsep _ (by simp)⟩
      · exact ⟨hCsep _ (by simp), hCsep _ (by simp)⟩
    · have hit := hmemTail ec hc i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> simp [frameObjects])
      constructor
      · exact Wave8Contracts.M08.disj_symm (hcross _ (by simp [frameObjects, ← hL']) i hit)
      · exact Wave8Contracts.M08.disj_symm (hcross _ (by simp [frameObjects, hLogs]) i hit)
  have hkeep (i : Ivl) (hi : i ∈ [(ec.1, 280), (ec.2, 104)])
      (a : Nat) (ha : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) (hab : a < 2 ^ 64)
      (hEa : ¬ CellHits a (e.toNat + 64, 136)) : memW post a = memW s a := by
    obtain ⟨hdiL, hdiA⟩ := hds i hi
    apply icsFrame_memW h hI.1 (halloc i hi) ha hab hEa
    · exact noHit_of_disj hdiL (by simp) ha
    · exact noHit_of_disj hdiA (by dsimp only; omega) ha
    · intro j hj
      apply noHit_of_disj ((hSep ec hec i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> simp [frameObjects])).1 tw.toNat ht j hj)
      · exact htab_fp_pos (hInv.1.1.2.1 tw.toNat ht).1 j hj
      · exact ha
  have hEa (a : Nat) (i : Ivl) (hi : i ∈ [(ec.1, 280), (ec.2, 104)])
      (ha : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2)
      (hheadsafe : ec = (E, C) → ¬ CellHits a (E + 64, 136)) :
      ¬ CellHits a (e.toNat + 64, 136) := by
    rw [he]
    rw [hcs] at hec
    rcases List.mem_cons.mp hec with rfl | hc
    · exact hheadsafe rfl
    · have hd := Wave8Contracts.M08.disj_symm
        (hcross (E, 280) (by simp [frameObjects]) i (hmemTail ec hc i (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> simp [frameObjects])))
      have hn := noHit_of_disj hd (by simp) ha
      unfold CellHits at hn ⊢; dsimp only at hn ⊢; omega
  have hrec (k : Nat) (hk : k = 24 ∨ k = 32 ∨ k = 40) :
      memW post (ec.1 + k) = memW s (ec.1 + k) := by
    apply hkeep (ec.1, 280) (by simp) _ (by dsimp only; omega) (by omega)
    apply hEa _ (ec.1, 280) (by simp) (by dsimp only; omega)
    intro hh; subst ec; unfold CellHits; dsimp only; omega
  refine ⟨hrec 24 (by simp), hrec 32 (by simp), hrec 40 (by simp), ?_⟩
  apply hkeep (ec.2, 104) (by simp) _ (by dsimp only; omega) (by omega)
  apply hEa _ (ec.2, 104) (by simp) (by dsimp only; omega)
  intro hh; subst ec
  have hd := Wave8Contracts.M08.disj_symm (hEsep (C, 104) (by simp))
  have hn := noHit_of_disj hd (by simp) (show C ≤ C + 56 ∧ C + 56 + 8 ≤ C + 104 by omega)
  unfold CellHits at hn ⊢; dsimp only at hn ⊢; omega

end IcsRun

theorem chain_cells_ne_head_pc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : EvmInv s) :
    ∀ ec ∈ evmChain s,
      BitVec.ofNat 64 (ec.1 + 24) ≠ BitVec.ofNat 64 (globN s "ev") ∧
      BitVec.ofNat 64 (ec.1 + 32) ≠ BitVec.ofNat 64 (globN s "ev") ∧
      BitVec.ofNat 64 (ec.1 + 40) ≠ BitVec.ofNat 64 (globN s "ev") ∧
      BitVec.ofNat 64 (ec.2 + 56) ≠ BitVec.ofNat 64 (globN s "ev") := by
  obtain ⟨_, S, _, hrest⟩ := hi
  dsimp only at hrest
  obtain ⟨_, _, _, hFW, _, _, hPair, _⟩ := hrest
  let e := globN s "ev"
  let c := globN s "cur_cont"
  have hhead := hFW _ (head_mem_evmChain s)
  have heB := (hhead.1 (e, 280) (by simp [e])).1.2
  have hcB := (hhead.1 (c, 104) (by simp [c])).1.2
  dsimp only at heB hcB
  have hbound : scratchEnd < 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
  have hneq (a : Nat) (ha : a < 2 ^ 64) (hne : a ≠ e) :
      BitVec.ofNat 64 a ≠ BitVec.ofNat 64 e := by
    intro hx
    have hh := congrArg BitVec.toNat hx
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega)] at hh
    exact hne hh
  have hcs : evmChain s = (e, c) :: (evmChain s).tail := evmChain_cons s
  rw [hcs, List.map_cons, List.flatten_cons, List.pairwise_append] at hPair
  obtain ⟨hP0, _, hcross⟩ := hPair
  have hdc : Disj (e, 280) (c, 104) := by
    unfold frameObjects at hP0
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hP0).1).1 _ (by simp)
  intro ec hec
  rw [hcs] at hec
  rcases List.mem_cons.mp hec with rfl | ht
  · unfold Disj at hdc; dsimp only at hdc ⊢
    refine ⟨hneq _ (by omega) (by omega), hneq _ (by omega) (by omega),
      hneq _ (by omega) (by omega), hneq _ (by omega) (by omega)⟩
  · have hF := hFW ec (by rw [hcs]; exact List.mem_cons_of_mem _ ht)
    have hrB := (hF.1 (ec.1, 280) (by simp)).1.2
    have hkB := (hF.1 (ec.2, 104) (by simp)).1.2
    dsimp only at hrB hkB
    have hmem (i : Ivl) (hm : i ∈ frameObjects s ec) :
        i ∈ (((evmChain s).tail.map (frameObjects s)).flatten) :=
      List.mem_flatten.mpr ⟨frameObjects s ec, List.mem_map_of_mem ht, hm⟩
    have hd1 := hcross (e, 280) (by simp [frameObjects])
      (ec.1, 280) (hmem _ (by simp [frameObjects]))
    have hd2 := hcross (e, 280) (by simp [frameObjects])
      (ec.2, 104) (hmem _ (by simp [frameObjects]))
    unfold Disj at hd1 hd2; dsimp only at hd1 hd2
    exact ⟨hneq _ (by omega) (by omega), hneq _ (by omega) (by omega),
      hneq _ (by omega) (by omega), hneq _ (by omega) (by omega)⟩

/-- Error incorporation's three head writes avoid every chain alignment cell. -/
theorem chain_cells_ne_head_error {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : EvmInv s) (k : Nat) (hk : k ∈ [64, 72, 184]) :
    ∀ ec ∈ evmChain s,
      BitVec.ofNat 64 (ec.1 + 24) ≠ BitVec.ofNat 64 (globN s "ev" + k) ∧
      BitVec.ofNat 64 (ec.1 + 32) ≠ BitVec.ofNat 64 (globN s "ev" + k) ∧
      BitVec.ofNat 64 (ec.1 + 40) ≠ BitVec.ofNat 64 (globN s "ev" + k) ∧
      BitVec.ofNat 64 (ec.2 + 56) ≠ BitVec.ofNat 64 (globN s "ev" + k) := by
  have hkbound : k < 280 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  have hkne : k ≠ 24 ∧ k ≠ 32 ∧ k ≠ 40 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  obtain ⟨_, S, _, hrest⟩ := hi
  dsimp only at hrest
  obtain ⟨_, _, _, hFW, _, _, hPair, _⟩ := hrest
  let e := globN s "ev"
  let c := globN s "cur_cont"
  have hhead := hFW _ (head_mem_evmChain s)
  have heB := (hhead.1 (e, 280) (by simp [e])).1.2
  have hcB := (hhead.1 (c, 104) (by simp [c])).1.2
  dsimp only at heB hcB
  have hbound : scratchEnd < 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
  have hneq (a : Nat) (ha : a < 2 ^ 64) (hne : a ≠ e + k) :
      BitVec.ofNat 64 a ≠ BitVec.ofNat 64 (e + k) := by
    intro hx
    have hh := congrArg BitVec.toNat hx
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (show e + k < 2 ^ 64 by omega)] at hh
    exact hne hh
  have hcs : evmChain s = (e, c) :: (evmChain s).tail := evmChain_cons s
  rw [hcs, List.map_cons, List.flatten_cons, List.pairwise_append] at hPair
  obtain ⟨hP0, _, hcross⟩ := hPair
  have hdc : Disj (e, 280) (c, 104) := by
    unfold frameObjects at hP0
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hP0).1).1 _ (by simp)
  intro ec hec
  rw [hcs] at hec
  rcases List.mem_cons.mp hec with rfl | ht
  · unfold Disj at hdc; dsimp only at hdc
    refine ⟨hneq _ (by omega) (by omega), hneq _ (by omega) (by omega),
      hneq _ (by omega) (by omega), hneq _ (by omega) (by omega)⟩
  · have hF := hFW ec (by rw [hcs]; exact List.mem_cons_of_mem _ ht)
    have hrB := (hF.1 (ec.1, 280) (by simp)).1.2
    have hkB := (hF.1 (ec.2, 104) (by simp)).1.2
    dsimp only at hrB hkB
    have hmem (i : Ivl) (hm : i ∈ frameObjects s ec) :
        i ∈ (((evmChain s).tail.map (frameObjects s)).flatten) :=
      List.mem_flatten.mpr ⟨frameObjects s ec, List.mem_map_of_mem ht, hm⟩
    have hd1 := hcross (e, 280) (by simp [frameObjects])
      (ec.1, 280) (hmem _ (by simp [frameObjects]))
    have hd2 := hcross (e, 280) (by simp [frameObjects])
      (ec.2, 104) (hmem _ (by simp [frameObjects]))
    unfold Disj at hd1 hd2; dsimp only at hd1 hd2
    exact ⟨hneq _ (by omega) (by omega), hneq _ (by omega) (by omega),
      hneq _ (by omega) (by omega), hneq _ (by omega) (by omega)⟩

/-- The error incorporation callee preserves the chain's memory contract. -/
theorem incorporate_child_on_error_cells {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (e : BitVec 64)
    (hi : EvmInv s)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (v : ValueHOL 64)
    (hr : evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_incorporate_child_on_error) = (some (.returned v), post)) :
    EvmEkFk.ChainCellsAgree s post := by
  obtain ⟨_, ⟨w1, w2, w3, hm⟩, _, _⟩ :=
    Ret.apply (incorporate_child_on_error_run s e he) hr
  have heq : BitVec.ofNat 64 (globN s "ev") = e := by simp [globN, he]
  have h64 := chain_cells_ne_head_error s hi 64 (by simp)
  have h72 := chain_cells_ne_head_error s hi 72 (by simp)
  have h184 := chain_cells_ne_head_error s hi 184 (by simp)
  rw [BitVec.ofNat_add (globN s "ev") 64, heq] at h64
  rw [BitVec.ofNat_add (globN s "ev") 72, heq] at h72
  rw [BitVec.ofNat_add (globN s "ev") 184, heq] at h184
  intro ec hec
  obtain ⟨h1, h2, h3, h4⟩ := h64 ec hec
  obtain ⟨h5, h6, h7, h8⟩ := h72 ec hec
  obtain ⟨h9, h10, h11, h12⟩ := h184 ec hec
  have hkeep (a : Nat) (ha : BitVec.ofNat 64 a ≠ e + 64)
      (hb : BitVec.ofNat 64 a ≠ e + 72) (hc : BitVec.ofNat 64 a ≠ e + 184) :
      memW post a = memW s a := by
    unfold memW
    rw [hm, updW_ne _ _ _ _ hc, updW_ne _ _ _ _ hb, updW_ne _ _ _ _ ha]
  exact ⟨hkeep _ h1 h5 h9, hkeep _ h2 h6 h10,
    hkeep _ h3 h7 h11, hkeep _ h4 h8 h12⟩

/-- The concrete cleanup restores the saved frame-memory mark and preserves
every chain alignment cell.  The only memory write is the parent's pc. -/
theorem finish_child_cleanup_cells {F : Type} (t post : PanSemStateFiniteExact 64 F)
    (hcode : t.code = originalRuntimeCode) (hi : EvmInv t)
    (cm cmm e pc : BitVec 64) (v : ValueHOL 64)
    (hcm : t.locals.lookup (ofString "child_mark") = some (.val (.word cm)))
    (hcmm : t.locals.lookup (ofString "child_mem_mark") = some (.val (.word cmm)))
    (he : t.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hpc : t.memory e = .word pc) (hdom : t.memaddrs e)
    (hr : evaluateHOLFiniteState t EvmEkFk.fcCleanup = (some (.returned v), post)) :
    EvmEkFk.ChainCellsAgree t post ∧
    globN post "ev" = globN t "ev" ∧
    globN post "frame_mem_ptr" = cmm.toNat ∧
    globN post "scratch_ptr" = cm.toNat := by
  have htail := Ret.apply (finish_child_tail t hcode cm cmm e pc hcm hcmm he hpc hdom) hr
  obtain ⟨hg, hm, _, _⟩ := htail
  have heAddr : BitVec.ofNat 64 (globN t "ev") = e := by simp [globN, he]
  have hsafe := chain_cells_ne_head_pc t hi
  rw [heAddr] at hsafe
  have hcells : EvmEkFk.ChainCellsAgree t post := by
    intro ec hec
    obtain ⟨h24, h32, h40, h56⟩ := hsafe ec hec
    have hkeep (a : Nat) (ha : BitVec.ofNat 64 a ≠ e) : memW post a = memW t a := by
      unfold memW
      rw [hm, updW_ne _ _ _ _ ha]
    exact ⟨hkeep _ h24, hkeep _ h32, hkeep _ h40, hkeep _ h56⟩
  have hn1 : ofString "frame_mem_ptr" ≠ ofString "ev" := by decide
  have hn2 : ofString "scratch_ptr" ≠ ofString "ev" := by decide
  have hn3 : ofString "frame_mem_ptr" ≠ ofString "scratch_ptr" := by decide
  refine ⟨hcells, ?_, ?_, ?_⟩ <;>
    simp [globN, hg, HolFiniteMapExact.lookup_update, FUPDATE, hn1, hn2, hn3]

/-! ## Create-finish prelude interface

The frame-start/finish-child leaf is independent of this bridge.  Transport its
chain invariant explicitly, so callers can use `CreateFinishSpecs` without
identifying two separately recursive definitions by reduction.
-/

/-- Before releasing the frame-memory mark, the surviving parent already has
the original chain's alignment and links, and its end equals the saved mark.
No relation to the current `frame_mem_ptr` is needed at this intermediate point. -/
theorem finish_child_parent_alignment {F : Type}
    {s st : PanSemStateFiniteExact 64 F} (hs : HeadMemChainWF s)
    (hk : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hchain : evmChain st = (evmChain s).tail)
    (hmem : ∀ ec ∈ evmChain st, memW st (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW st (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW st (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW st (ec.2 + 56) = memW s (ec.2 + 56))
    (hev : globN st "ev" = memW s (globN s "cur_cont")) :
    (∀ ec ∈ evmChain st,
      memW st (ec.1 + 32) % 32 = 0 ∧ memW st (ec.1 + 40) % 8 = 0) ∧
    ChainLinks (memW st) (evmChain st) ∧
    memW st (globN st "ev" + 24) + memW st (globN st "ev" + 40) =
      memW s (globN s "cur_cont" + 56) := by
  have hcs := evmChain_cons s
  rw [if_neg hk] at hcs
  refine ⟨?_, ?_, ?_⟩
  · intro ec hec
    have hm := hmem ec hec
    rw [hm.2.1, hm.2.2.1]
    exact hs.1 ec (List.mem_of_mem_tail (hchain ▸ hec))
  · have hfull : evmChain s =
        (globN s "ev", globN s "cur_cont") :: (evmChain s).tail := evmChain_cons s
    have hl := hs.2.2
    rw [hfull] at hl
    have ht := chainLinks_tail _ _ _ hl
    rw [← hchain] at ht
    exact chainLinks_transport _ _ _ (fun ec hec =>
      ⟨(hmem ec hec).1, (hmem ec hec).2.2.1, (hmem ec hec).2.2.2⟩) ht
  · have hm := hmem _ (head_mem_evmChain st)
    rw [hm.1, hm.2.2.1, hev]
    have hl := hs.2.2
    rw [hcs, maxChain_succ, evmChainFrom_succ] at hl
    exact hl.1

/-- Releasing the child's two arena marks establishes the aligned parent
invariant before the final pc increment.  The memory/chain facts are those
obtained after the finish-child branches; the restored head end is the saved
child frame-memory mark. -/
theorem finish_child_release_aligned {F : Type}
    (st : PanSemStateFiniteExact 64 F) (cmw cmmw : BitVec 64) {S : List Nat}
    (hAs : ArenaReady st)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt st S)
    (hRel : EvmEkFk.ReleaseReadyAt st S cmw.toNat cmmw.toNat)
    (hcm : st.locals.lookup (ofString "child_mark") = some (.val (.word cmw)))
    (hcmm : st.locals.lookup (ofString "child_mem_mark") = some (.val (.word cmmw)))
    (halign : ∀ ec ∈ evmChain st,
      memW st (ec.1 + 32) % 32 = 0 ∧ memW st (ec.1 + 40) % 8 = 0)
    (hlinks : ChainLinks (memW st) (evmChain st))
    (hend : memW st (globN st "ev" + 24) + memW st (globN st "ev" + 40) = cmmw.toNat)
    (hnt : (evaluateHOLFiniteState st EvmEkFk.fcCleanup).1 ≠ some .timeOut) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState st EvmEkFk.fcCleanup =
        evaluateHOLFiniteState mid
          (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
            (.return (.const 0#64))) ∧
      EvmInvA mid ∧ mid.memory = st.memory ∧
      evmChain mid = evmChain st ∧
      globN mid "frame_mem_ptr" = cmmw.toNat ∧
      R11Shards.OpDispatchSpec.evmR mid = R11Shards.OpDispatchSpec.evmR st := by
  obtain ⟨mid, heval, _, hm, _, _, _, hfmp, hg, hAmid, hImid, hch, hR, _⟩ :=
    EvmEkFk.release_pair_step st (.var .local (ofString "child_mark"))
      (.var .local (ofString "child_mem_mark")) cmw cmmw hAs hInv hRel
      (by simp [evalHOLExact, hcm]) (by intro g ck; simp [evalHOLExact, hcmm]) hnt
  have hmw : memW mid = memW st := by
    funext a; unfold memW; rw [hm]
  have hev : globN mid "ev" = globN st "ev" := by
    unfold globN
    rw [hg _ (by decide) (by decide)]
  have hAligned : HeadMemChainWF mid := by
    unfold HeadMemChainWF
    rw [hch, hmw, hev, hfmp]
    exact ⟨halign, hend, hlinks⟩
  exact ⟨mid, heval, ⟨⟨hAmid, S, hImid⟩, hAligned⟩, hm, hch, hfmp, hR⟩

/-- Compose parent-cell transport with the concrete release pair. -/
theorem finish_child_release_from_parent {F : Type}
    {s st : PanSemStateFiniteExact 64 F} (cmw cmmw : BitVec 64) {S : List Nat}
    (hs : HeadMemChainWF s) (hk : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hAs : ArenaReady st)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt st S)
    (hRel : EvmEkFk.ReleaseReadyAt st S cmw.toNat cmmw.toNat)
    (hcm : st.locals.lookup (ofString "child_mark") = some (.val (.word cmw)))
    (hcmm : st.locals.lookup (ofString "child_mem_mark") = some (.val (.word cmmw)))
    (hchain : evmChain st = (evmChain s).tail)
    (hmem : ∀ ec ∈ evmChain st, memW st (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW st (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW st (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW st (ec.2 + 56) = memW s (ec.2 + 56))
    (hev : globN st "ev" = memW s (globN s "cur_cont"))
    (hmark : cmmw.toNat = memW s (globN s "cur_cont" + 56))
    (hnt : (evaluateHOLFiniteState st EvmEkFk.fcCleanup).1 ≠ some .timeOut) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState st EvmEkFk.fcCleanup =
        evaluateHOLFiniteState mid
          (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
            (.return (.const 0#64))) ∧
      EvmInvA mid ∧
      evmChain mid = (evmChain s).tail ∧
      EvmEkFk.ChainCellsAgree st mid ∧
      globN mid "ev" = memW s (globN s "cur_cont") ∧
      globN mid "frame_mem_ptr" = memW s (globN s "cur_cont" + 56) ∧
      R11Shards.OpDispatchSpec.evmR mid = R11Shards.OpDispatchSpec.evmR st := by
  obtain ⟨halign, hlinks, hend⟩ := finish_child_parent_alignment hs hk hchain hmem hev
  obtain ⟨mid, heval, hi, hm, hch, hfmp, hR⟩ :=
    finish_child_release_aligned st cmw cmmw hAs hInv hRel hcm hcmm halign hlinks
      (hend.trans hmark.symm) hnt
  have hevMid : globN mid "ev" = globN st "ev" := by
    have hh := congrArg List.head? hch
    rw [evmChain_cons, evmChain_cons] at hh
    exact (Prod.mk.inj (Option.some.inj hh)).1
  exact ⟨mid, heval, hi, hch.trans hchain,
    EvmEkFk.chainCellsAgree_of_memory_eq hm, hevMid.trans hev, hfmp.trans hmark, hR⟩

/-- The final pc increment preserves the aligned invariant and all chain cells. -/
theorem pc_add_body_aligned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hi : EvmInvA s) (hc : s.code = originalRuntimeCode)
    (e pc n : BitVec 64) (v : ValueHOL 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hp : s.memory e = .word pc) (hd : s.memaddrs e)
    (hex : ∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "pc_add") values =
      some (sourceFnBody Guest.Software.guestFn_pc_add, s.locals, .one))
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_pc_add) =
      (some (.returned v), post)) :
    EvmInvA post ∧ evmChain post = evmChain s ∧
    R11Shards.OpDispatchSpec.evmR post ≤ R11Shards.OpDispatchSpec.evmR s ∧
    EvmEkFk.ChainCellsAgree s post ∧ post.globals = s.globals := by
  obtain ⟨ps, body, rt, hl, hs⟩ := R14Shards.OpHandlersA.eps_pc_add
  obtain ⟨rfl, rfl, rfl⟩ := funSpec_same_body lookup_pc_add hl
  have hspec := (hs s hc hi.1 trivial hex (by rw [hr]; simp)).1 v (by rw [hr])
  rw [hr] at hspec
  dsimp only at hspec
  obtain ⟨hI, hch, hR, hg⟩ := hspec
  obtain ⟨_, hm, _, _⟩ := Ret.apply (pc_add_run s e pc n hn he hp hd) hr
  have heAddr : BitVec.ofNat 64 (globN s "ev") = e := by simp [globN, he]
  have hsafe := chain_cells_ne_head_pc s hi.1
  rw [heAddr] at hsafe
  have hcells : EvmEkFk.ChainCellsAgree s post := by
    intro ec hec
    obtain ⟨h24, h32, h40, h56⟩ := hsafe ec hec
    have hkeep (a : Nat) (ha : BitVec.ofNat 64 a ≠ e) : memW post a = memW s a := by
      unfold memW; rw [hm, updW_ne _ _ _ _ ha]
    exact ⟨hkeep _ h24, hkeep _ h32, hkeep _ h40, hkeep _ h56⟩
  have hA := headMemChainWF_of_agree hi.2 hch hcells
    (show globN post "ev" = globN s "ev" by simp [globN, hg])
    (show globN post "frame_mem_ptr" = globN s "frame_mem_ptr" by simp [globN, hg])
  exact ⟨⟨hI, hA⟩, hch, hR, hcells, hg⟩

/-- Lift the aligned pc increment through its call and final return. -/
theorem pc_add_return_aligned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : EvmInvA s) (hc : s.code = originalRuntimeCode)
    (e pc : BitVec 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hp : s.memory e = .word pc) (hd : s.memaddrs e) :
    Ret s (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
      (.return (.const 0#64))) (fun _ post =>
      EvmInvA post ∧ evmChain post = evmChain s ∧
      R11Shards.OpDispatchSpec.evmR post ≤ R11Shards.OpDispatchSpec.evmR s ∧
      EvmEkFk.ChainCellsAgree s post ∧ post.globals = s.globals) := by
  refine Ret.seq_call00 fun values body callee ret v post hargs hl hr => ?_
  have hv : values = [.val (.word (1#64))] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact] using hargs.symm
  subst values
  have hl0 := pan_one_word_lookup s.code.lookup (ofString "pc_add") (ofString "n")
    _ (1#64) (by rw [hc]; exact lookup_pc_add)
  rw [hl0] at hl
  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hl
  let ce := callEntryStateHOLFinite s
    (HolFiniteMapExact.empty.update (ofString "n", .val (.word (1#64))))
  obtain ⟨hI, hch, hR, hcells, hg⟩ := pc_add_body_aligned ce post
    (localsFree_evmInvA s _ _ hi) hc e pc 1 v
    (by simp [ce, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    he hp hd
    ⟨[.val (.word (1#64))], pan_one_word_lookup originalRuntimeCode.lookup
      (ofString "pc_add") (ofString "n") _ 1 lookup_pc_add⟩ hr
  have hch0 : evmChain ce = evmChain s :=
    R11Shards.OpDispatchSpec.evmChain_congr (s := s) (t := ce) rfl rfl
  have hR0 : R11Shards.OpDispatchSpec.evmR ce = R11Shards.OpDispatchSpec.evmR s :=
    (R11Shards.OpDispatchSpec.evm_congr (s := s) (t := ce) rfl rfl).2.1
  have hchRest : evmChain (emptyLocalsHOLFinite { post with locals := s.locals }) = evmChain post :=
    R11Shards.OpDispatchSpec.evmChain_congr (s := post)
      (t := emptyLocalsHOLFinite { post with locals := s.locals }) rfl rfl
  have hRRest : R11Shards.OpDispatchSpec.evmR (emptyLocalsHOLFinite { post with locals := s.locals }) =
      R11Shards.OpDispatchSpec.evmR post :=
    (R11Shards.OpDispatchSpec.evm_congr (s := post)
      (t := emptyLocalsHOLFinite { post with locals := s.locals }) rfl rfl).2.1
  refine Ret.ret fun _ _ => ?_
  refine ⟨localsFree_evmInvA post _ _ hI, ?_, ?_, ?_, hg⟩
  · exact hchRest.trans (hch.trans hch0)
  · exact hRRest.le.trans (hR.trans_eq hR0)
  · intro ec hec
    exact hcells ec (hch0.symm ▸ hec)

/-- The concrete cleanup restores the aligned parent invariant through both releases
and the final pc increment. -/
theorem finish_child_cleanup_aligned {F : Type}
    (st post : PanSemStateFiniteExact 64 F) (cmw cmmw e pc : BitVec 64) {S : List Nat}
    (hAs : ArenaReady st)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt st S)
    (hRel : EvmEkFk.ReleaseReadyAt st S cmw.toNat cmmw.toNat)
    (hcm : st.locals.lookup (ofString "child_mark") = some (.val (.word cmw)))
    (hcmm : st.locals.lookup (ofString "child_mem_mark") = some (.val (.word cmmw)))
    (halign : ∀ ec ∈ evmChain st,
      memW st (ec.1 + 32) % 32 = 0 ∧ memW st (ec.1 + 40) % 8 = 0)
    (hlinks : ChainLinks (memW st) (evmChain st))
    (hend : memW st (globN st "ev" + 24) + memW st (globN st "ev" + 40) = cmmw.toNat)
    (he : st.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hp : st.memory e = .word pc) (hd : st.memaddrs e)
    (v : ValueHOL 64)
    (hr : evaluateHOLFiniteState st EvmEkFk.fcCleanup = (some (.returned v), post)) :
    EvmInvA post ∧ evmChain post = evmChain st ∧
    EvmEkFk.ChainCellsAgree st post ∧
    globN post "ev" = globN st "ev" ∧
    globN post "frame_mem_ptr" = cmmw.toNat ∧
    R11Shards.OpDispatchSpec.evmR post ≤ R11Shards.OpDispatchSpec.evmR st := by
  have hnt : (evaluateHOLFiniteState st EvmEkFk.fcCleanup).1 ≠ some .timeOut := by rw [hr]; simp
  obtain ⟨mid, heval, _, hm, hd', _, _, hfmp, hg, hAmid, hImid, hch, hR, _⟩ :=
    EvmEkFk.release_pair_step st (.var .local (ofString "child_mark"))
      (.var .local (ofString "child_mem_mark")) cmw cmmw hAs hInv hRel
      (by simp [evalHOLExact, hcm]) (by intro g ck; simp [evalHOLExact, hcmm]) hnt
  have hev : globN mid "ev" = globN st "ev" := by
    unfold globN; rw [hg _ (by decide) (by decide)]
  have hmw : memW mid = memW st := by funext a; unfold memW; rw [hm]
  have hA : HeadMemChainWF mid := by
    unfold HeadMemChainWF; rw [hch, hmw, hev, hfmp]; exact ⟨halign, hend, hlinks⟩
  have hret := pc_add_return_aligned mid ⟨⟨hAmid, S, hImid⟩, hA⟩ hAmid.1.code e pc
    (by rw [hg _ (by decide) (by decide)]; exact he)
    (by rw [hm]; exact hp) (by rw [hd']; exact hd)
  have hrmid : evaluateHOLFiniteState mid
      (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
        (.return (.const 0#64))) = (some (.returned v), post) := heval.symm.trans hr
  obtain ⟨hi, hcp, hrp, hcells, hgp⟩ := Ret.apply hret hrmid
  refine ⟨hi, hcp.trans hch, ?_, ?_, ?_, hrp.trans_eq hR⟩
  · intro ec hec
    have hh := hcells ec (hch.symm ▸ hec)
    simpa only [hmw] using hh
  · exact (show globN post "ev" = globN mid "ev" by simp [globN, hgp]).trans hev
  · exact (show globN post "frame_mem_ptr" = globN mid "frame_mem_ptr" by simp [globN, hgp]).trans hfmp

/-- The invariant supplies the parent's global word and allocated pc cell. -/
theorem finish_child_cleanup_from_invariants {F : Type}
    (st post : PanSemStateFiniteExact 64 F) (cmw cmmw : BitVec 64) {S : List Nat}
    (hAs : ArenaReady st)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt st S)
    (hRel : EvmEkFk.ReleaseReadyAt st S cmw.toNat cmmw.toNat)
    (hcm : st.locals.lookup (ofString "child_mark") = some (.val (.word cmw)))
    (hcmm : st.locals.lookup (ofString "child_mem_mark") = some (.val (.word cmmw)))
    (halign : ∀ ec ∈ evmChain st,
      memW st (ec.1 + 32) % 32 = 0 ∧ memW st (ec.1 + 40) % 8 = 0)
    (hlinks : ChainLinks (memW st) (evmChain st))
    (hend : memW st (globN st "ev" + 24) + memW st (globN st "ev" + 40) = cmmw.toNat)
    (v : ValueHOL 64)
    (hr : evaluateHOLFiniteState st EvmEkFk.fcCleanup = (some (.returned v), post)) :
    EvmInvA post ∧ evmChain post = evmChain st ∧
    EvmEkFk.ChainCellsAgree st post ∧
    globN post "ev" = globN st "ev" ∧
    globN post "frame_mem_ptr" = cmmw.toNat ∧
    R11Shards.OpDispatchSpec.evmR post ≤ R11Shards.OpDispatchSpec.evmR st := by
  have hFW := hInv.2.2.2.2.1 _ (head_mem_evmChain st)
  have hw := hFW.1 (globN st "ev", 280) (by simp)
  obtain ⟨pc, hd, hm⟩ := hw.2.2.2 0 (by norm_num)
  obtain ⟨e, he⟩ := hAs.2.2.2.2.2.2.2.2.2 "ev" (by decide)
  have heq : BitVec.ofNat 64 (globN st "ev") = e := by
    simp [globN, GlobalWord] at he ⊢
    rw [he]
    simp
  exact finish_child_cleanup_aligned st post cmw cmmw
    (BitVec.ofNat 64 (globN st "ev")) pc hAs hInv hRel hcm hcmm halign hlinks hend
    (by rw [heq]; exact he) (by simpa using hm) (by simpa using hd) v hr

/-- Expose the concrete two-global pop before the finish-child branches. -/
theorem finish_child_pop_assignments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (parent next : BitVec 64)
    (hp : s.locals.lookup (ofString "parent") = some (.val (.word parent)))
    (he : s.isValidValueHOLFinite .global (ofString "ev") (.val (.word parent)) = true)
    (hn : @evalHOLExact 64 F _
      (setGlobalHOLFinite (ofString "ev") (.val (.word parent)) s).toExact
      (fun a => Classical.propDecidable
        ((setGlobalHOLFinite (ofString "ev") (.val (.word parent)) s).memaddrs a))
      (.load .one (.op .add [.var .local (ofString "rec"), .const 8#64])) =
        some (.val (.word next)))
    (hc : (setGlobalHOLFinite (ofString "ev") (.val (.word parent)) s).isValidValueHOLFinite
      .global (ofString "cur_cont") (.val (.word next)) = true) :
    evaluateHOLFiniteState s EvmEkFk.fcAfterPrelude =
      evaluateHOLFiniteState
        (setGlobalHOLFinite (ofString "cur_cont") (.val (.word next))
          (setGlobalHOLFinite (ofString "ev") (.val (.word parent)) s))
        (.seq EvmEkFk.fcBranches EvmEkFk.fcCleanup) := by
  rw [EvmEkFk.fcAfterPrelude_eq, evaluateHOLFiniteState_seq_line780,
    evaluateHOLFiniteState_assign]
  simp only [evalHOLExact, hp, he, ↓reduceIte, setKvarHOLFinite]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
  simp only [hn, hc, ↓reduceIte, setKvarHOLFinite]

/-- Word-valued head globals make both pop assignments shape-valid. -/
theorem finish_child_pop_global_valid {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hi : EvmInv s) (parent next : BitVec 64) :
    s.isValidValueHOLFinite .global (ofString "ev") (.val (.word parent)) = true ∧
    (setGlobalHOLFinite (ofString "ev") (.val (.word parent)) s).isValidValueHOLFinite
      .global (ofString "cur_cont") (.val (.word next)) = true := by
  obtain ⟨_, _, ⟨ew, he, _⟩, ⟨cw, hc, _⟩, _⟩ := R11Shards.evm_head_globals hi
  constructor
  · simp [isValidValueHOLFinite, lookupKvarHOLExact, he, shapeOfHOLExact, shapeEqHOL]
  · simp [isValidValueHOLFinite, lookupKvarHOLExact,
      setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hc,
      shapeOfHOLExact, shapeEqHOL, show ofString "ev" ≠ ofString "cur_cont" by decide]

/-- The prelude supplies the parent local and both assignment-validity facts. -/
theorem finish_child_pop_of_prelude {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (hpre : EvmEkFk.PreludeRel s0 s) (next : BitVec 64)
    (hn : @evalHOLExact 64 F _
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) s).toExact
      (fun a => Classical.propDecidable
        ((setGlobalHOLFinite (ofString "ev")
          (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) s).memaddrs a))
      (.load .one (.op .add [.var .local (ofString "rec"), .const 8#64])) =
        some (.val (.word next))) :
    evaluateHOLFiniteState s EvmEkFk.fcAfterPrelude =
      evaluateHOLFiniteState
        (setGlobalHOLFinite (ofString "cur_cont") (.val (.word next))
          (setGlobalHOLFinite (ofString "ev")
            (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) s))
        (.seq EvmEkFk.fcBranches EvmEkFk.fcCleanup) := by
  obtain ⟨he, hc⟩ := finish_child_pop_global_valid hpre.inv
    (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))) next
  exact finish_child_pop_assignments s _ next hpre.locals_ok.parent_lk he hn hc

/-- The surviving continuation pointer can be loaded after the prelude, even
after assigning the parent to `ev`. -/
theorem finish_child_prelude_cont_load {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (hpre : EvmEkFk.PreludeRel s0 s) (parent : BitVec 64) :
    let t := setGlobalHOLFinite (ofString "ev") (.val (.word parent)) s
    @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "rec"), .const 8#64])) =
      some (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8))))) := by
  classical
  dsimp only
  have hhead := congrArg List.head? hpre.chain_eq
  rw [evmChain_cons, evmChain_cons] at hhead
  have hcc : globN s "cur_cont" = globN s0 "cur_cont" :=
    (Prod.mk.inj (Option.some.inj hhead)).2
  have hrec := hpre.locals_ok.rec_lk
  rw [← hcc] at hrec
  have hFW := hpre.inv.2.choose_spec.2.2.2.2.1 _ (head_mem_evmChain s)
  have hwords := hFW.1 (globN s "cur_cont", 104) (by simp)
  obtain ⟨w, hd, hm⟩ := hwords.2.2.2 1 (by norm_num)
  have hadd : BitVec.ofNat 64 (globN s "cur_cont") + (8#64) =
      BitVec.ofNat 64 (globN s "cur_cont" + 8) := by rw [← BitVec.ofNat_add]
  have hadd0 : BitVec.ofNat 64 (globN s "cur_cont") + (8#64 + 0#64) =
      BitVec.ofNat 64 (globN s "cur_cont" + 8) := by simpa using hadd
  have hmem : memW s (globN s "cur_cont" + 8) = w.toNat := by
    unfold memW
    change (match s.memory (BitVec.ofNat 64 (globN s "cur_cont" + 8)) with
      | .word v => v.toNat) = _
    rw [hm]
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
    (.load .one (.op .add [.var .local (ofString "rec"), .const 8#64])) = _
  simp only [evalHOLExact, evalListHOLExact, hrec,
    isWfShapeExactHOL, memLoadHOLExact, ↓reduceIte, valueIsWord, valueWord,
    wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr, Bool.and_self]
  change (if s.memaddrs (BitVec.ofNat 64 (globN s "cur_cont") + (8#64 + 0#64)) then
    some (ValueHOL.val (s.memory (BitVec.ofNat 64 (globN s "cur_cont") + (8#64 + 0#64)))) else none) = _
  rw [hadd0]
  simp only [hd, ↓reduceIte, hm, hmem, BitVec.ofNat_toNat]
  rfl

/-- Execute both post-prelude pop assignments with no evaluation premises. -/
theorem finish_child_pop_step {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (hpre : EvmEkFk.PreludeRel s0 s) :
    evaluateHOLFiniteState s EvmEkFk.fcAfterPrelude =
      evaluateHOLFiniteState
        (setGlobalHOLFinite (ofString "cur_cont")
          (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))))
          (setGlobalHOLFinite (ofString "ev")
            (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) s))
        (.seq EvmEkFk.fcBranches EvmEkFk.fcCleanup) := by
  exact finish_child_pop_of_prelude hpre _ (finish_child_prelude_cont_load hpre _)

/-- Popping the two frame globals preserves the arena for arbitrary pointer words. -/
theorem finish_child_pop_arena {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (parent next : BitVec 64) :
    ArenaReady (setGlobalHOLFinite (ofString "cur_cont") (.val (.word next))
      (setGlobalHOLFinite (ofString "ev") (.val (.word parent)) s)) := by
  have ha : ∀ (u : PanSemStateFiniteExact 64 F) (n : String) (w : BitVec 64),
      n = "ev" ∨ n = "cur_cont" → ArenaReady u →
      ArenaReady (setGlobalHOLFinite (ofString n) (.val (.word w)) u) := by
    intro u n w hn hu
    have hnheap : ofString n ≠ ofString "heap_ptr" := by rcases hn with rfl | rfl <;> decide
    have hnframe : ofString n ≠ ofString "frame_mem_ptr" := by rcases hn with rfl | rfl <;> decide
    have hnscratch : ofString n ≠ ofString "scratch_ptr" := by rcases hn with rfl | rfl <;> decide
    refine ⟨guestInv_congr (s := u) rfl rfl rfl rfl hu.1, ?_⟩
    have hp : globN (setGlobalHOLFinite (ofString n) (.val (.word w)) u) "heap_ptr" = globN u "heap_ptr" := by
      simp [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE, hnheap]
    have hf : globN (setGlobalHOLFinite (ofString n) (.val (.word w)) u) "frame_mem_ptr" = globN u "frame_mem_ptr" := by
      simp [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE, hnframe]
    have hs : globN (setGlobalHOLFinite (ofString n) (.val (.word w)) u) "scratch_ptr" = globN u "scratch_ptr" := by
      simp [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE, hnscratch]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hw⟩ := hu.2
    unfold ArenaOK
    rw [hp, hf, hs]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, globalsWord_update _ w rfl hw⟩
  exact ha _ "cur_cont" next (Or.inr rfl) (ha s "ev" parent (Or.inl rfl) hA)

/-- Other globals are preserved when their actual byte-string keys are distinct. -/
theorem finish_child_pop_other_global {F : Type} (s : PanSemStateFiniteExact 64 F)
    (parent next : BitVec 64) (name : String)
    (he : ofString name ≠ ofString "ev")
    (hc : ofString name ≠ ofString "cur_cont") :
    globN (setGlobalHOLFinite (ofString "cur_cont") (.val (.word next))
      (setGlobalHOLFinite (ofString "ev") (.val (.word parent)) s)) name =
      globN s name := by
  simp [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm he, Ne.symm hc]

/-- The finish-child branches fall through or raise; they cannot bypass cleanup
by returning directly. -/
theorem fcBranches_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) :
    (evaluateHOLFiniteState s EvmEkFk.fcBranches).1 ≠ some (.returned v) := by
  unfold EvmEkFk.fcBranches EvmEkFk.fcAfterPrelude EvmEkFk.fcCore
    EvmEkFk.fcBody EvmEkFk.fcDropDecls EvmEkFk.fcLeftSeq EvmEkFk.fcRightSeq
    sourceFnBody sourceFunctionEntry Guest.Software.guestFn_finish_child
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural
  repeat' first
    | apply EvmEkFk.ite_ne_returned_fc
    | apply EvmEkFk.dec_ne_returned_fc
    | apply EvmEkFk.seq_ne_returned_fc
    | apply EvmEkFk.decCall_ne_returned_fc
    | exact fun t u => EvmEkFk.call0_ne_returned_fc t _ _ u
    | exact fun t u => EvmEkFk.skip_ne_returned_fc t u

/-- Both saved release marks survive every normal branch fallthrough. -/
theorem finish_child_branches_marks {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hr : evaluateHOLFiniteState s EvmEkFk.fcBranches = (none, post)) :
    post.locals.lookup (ofString "child_mark") = s.locals.lookup (ofString "child_mark") ∧
    post.locals.lookup (ofString "child_mem_mark") = s.locals.lookup (ofString "child_mem_mark") := by
  have hkeep (n : String)
      (hn : InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.notAssignedLocal
        (ofString n) EvmEkFk.fcBranches = true) :
      post.locals.lookup (ofString n) = s.locals.lookup (ofString n) := by
    have h := InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.evaluate_notAssignedLocal
      EvmEkFk.fcBranches hn s (by rw [hr]; rfl)
    simpa only [hr] using h
  exact ⟨hkeep "child_mark" (by kernel_rfl), hkeep "child_mem_mark" (by kernel_rfl)⟩

/-- Every returning branch-and-cleanup run has a fallthrough branch state. -/
theorem fcBranches_cleanup_returned {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {v : ValueHOL 64}
    (hr : evaluateHOLFiniteState s (.seq EvmEkFk.fcBranches EvmEkFk.fcCleanup) =
      (some (.returned v), post)) :
    ∃ mid, evaluateHOLFiniteState s EvmEkFk.fcBranches = (none, mid) ∧
      evaluateHOLFiniteState mid EvmEkFk.fcCleanup = (some (.returned v), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hb : evaluateHOLFiniteState s EvmEkFk.fcBranches with ⟨r, mid⟩
  rw [hb] at hr
  cases r with
  | none => exact ⟨mid, rfl, hr⟩
  | some r =>
    have hh := congrArg Prod.fst hr
    dsimp only at hh
    have he : r = .returned v := Option.some.inj hh
    subst r
    exact False.elim (fcBranches_ne_returned s v (by rw [hb]))

/-- A returning post-prelude run factors through the concrete pop, the branch
fallthrough state, and the cleanup return. -/
theorem finish_child_afterPrelude_returned {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F} {v : ValueHOL 64}
    (hpre : EvmEkFk.PreludeRel s0 s)
    (hr : evaluateHOLFiniteState s EvmEkFk.fcAfterPrelude = (some (.returned v), post)) :
    ∃ mid,
      evaluateHOLFiniteState
        (setGlobalHOLFinite (ofString "cur_cont")
          (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))))
          (setGlobalHOLFinite (ofString "ev")
            (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) s))
        EvmEkFk.fcBranches = (none, mid) ∧
      evaluateHOLFiniteState mid EvmEkFk.fcCleanup = (some (.returned v), post) := by
  rw [finish_child_pop_step hpre] at hr
  exact fcBranches_cleanup_returned hr

/-- The prelude preserves the parent pointers encoded by its nonempty chain tail. -/
theorem finish_child_prelude_parent {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} (hpre : EvmEkFk.PreludeRel s0 s)
    (hk0 : memW s0 (globN s0 "cur_cont" + 16) ≠ 0) :
    memW s (globN s "cur_cont" + 16) ≠ 0 ∧
    memW s (globN s "cur_cont") = memW s0 (globN s0 "cur_cont") ∧
    memW s (globN s "cur_cont" + 8) = memW s0 (globN s0 "cur_cont" + 8) := by
  have ht0 : (evmChain s0).tail ≠ [] := by
    rw [EvmEkFk.evmChain_cons_of_cont_ne_zero hk0]
    dsimp only [List.tail]
    have hm : maxChain = (maxChain - 1) + 1 := by decide
    rw [hm]
    simp [evmChainFrom]
  have hk : memW s (globN s "cur_cont" + 16) ≠ 0 := by
    intro hz
    apply ht0
    rw [← hpre.chain_eq, evmChain_cons, if_pos hz]
    rfl
  have ht := congrArg (fun l : List Ivl => l.tail.head?) hpre.chain_eq
  rw [EvmEkFk.evmChain_cons_of_cont_ne_zero hk,
    EvmEkFk.evmChain_cons_of_cont_ne_zero hk0] at ht
  have hm : maxChain = (maxChain - 1) + 1 := by decide
  simp only [List.tail_cons] at ht
  rw [hm] at ht
  simp only [evmChainFrom, List.head?_cons] at ht
  exact ⟨hk, (Prod.mk.inj (Option.some.inj ht)).1,
    (Prod.mk.inj (Option.some.inj ht)).2⟩

/-- The concrete two-global pop establishes the parent invariant and both release
marks, with no string-name preservation hypothesis. -/
theorem finish_child_pop_state_invariants {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hne : memW s (globN s "cur_cont" + 16) ≠ 0) :
    let post := setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont"))))) s)
    ArenaReady post ∧ ∃ S' : List Nat,
      (∀ t ∈ S', t ∈ S) ∧
      InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S' ∧
      EvmEkFk.ReleaseReadyAt post S' (memW s (globN s "cur_cont" + 48))
        (memW s (globN s "cur_cont" + 56)) ∧
      evmChain post = (evmChain s).tail ∧
      (evmChain post).length + 1 = (evmChain s).length ∧
      R11Shards.OpDispatchSpec.evmR post +
        (memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) =
        R11Shards.OpDispatchSpec.evmR s := by
  dsimp only
  have hAp := finish_child_pop_arena hAs
    (BitVec.ofNat 64 (memW s (globN s "cur_cont")))
    (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))
  have hg := finish_child_pop_other_global s
    (BitVec.ofNat 64 (memW s (globN s "cur_cont")))
    (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))
  have hev : globN (setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont"))))) s)) "ev" =
      memW s (globN s "cur_cont") := by
    simp only [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
      if_neg (show ofString "cur_cont" ≠ ofString "ev" from by decide),
      if_pos rfl, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (memW_lt s _)
  have hcc : globN (setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont"))))) s)) "cur_cont" =
      memW s (globN s "cur_cont" + 8) := by
    simp only [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
      if_pos rfl, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (memW_lt s _)
  obtain ⟨S', hsub, hcases, hIp, hch, hR⟩ :=
    evmInvAt_of_pop_keys hAs hInv hne hAp rfl rfl rfl hev hcc hg
  have hRel := releaseReadyAt_of_pop_keys hAs hInv hne (by rfl) hg hch hsub hcases
  refine ⟨hAp, S', hsub, hIp, hRel, hch, ?_, hR⟩
  rw [hch, EvmEkFk.evmChain_cons_of_cont_ne_zero hne]
  simp

/-- Compose prelude preservation with the concrete parent pop. -/
theorem finish_child_prelude_pop_invariants {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F}
    (hpre : EvmEkFk.PreludeRel s0 s)
    (hk0 : memW s0 (globN s0 "cur_cont" + 16) ≠ 0) :
    let post := setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) s)
    ArenaReady post ∧ ∃ S' : List Nat,
      InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S' ∧
      EvmEkFk.ReleaseReadyAt post S' (memW s (globN s "cur_cont" + 48))
        (memW s (globN s "cur_cont" + 56)) ∧
      evmChain post = (evmChain s0).tail ∧
      (evmChain post).length + 1 = (evmChain s0).length ∧
      R11Shards.OpDispatchSpec.evmR post +
        (memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) ≤
        R11Shards.OpDispatchSpec.evmR s0 := by
  obtain ⟨hk, hp, _⟩ := finish_child_prelude_parent hpre hk0
  obtain ⟨S, hI⟩ := hpre.inv.2
  have hA : ArenaReady s := hpre.inv.1
  obtain ⟨hAp, S', _, hIp, hRel, hch, hlen, hR⟩ :=
    finish_child_pop_state_invariants hA hI hk
  dsimp only
  rw [← hp]
  refine ⟨hAp, S', hIp, hRel, hch.trans (congrArg List.tail hpre.chain_eq), ?_, ?_⟩
  · simpa only [hpre.chain_eq] using hlen
  · exact hR.le.trans hpre.r_le

/-- Parent memory alignment and links are already available immediately after
the concrete global pop, before restoring the frame-memory pointer. -/
theorem finish_child_pop_alignment {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : HeadMemChainWF s) (hInv : EvmInv s)
    (hk : memW s (globN s "cur_cont" + 16) ≠ 0) :
    let post := setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont"))))) s)
    (∀ ec ∈ evmChain post,
      memW post (ec.1 + 32) % 32 = 0 ∧ memW post (ec.1 + 40) % 8 = 0) ∧
    ChainLinks (memW post) (evmChain post) ∧
    memW post (globN post "ev" + 24) + memW post (globN post "ev" + 40) =
      memW s (globN s "cur_cont" + 56) := by
  dsimp only
  have hev : globN (setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont"))))) s)) "ev" =
      memW s (globN s "cur_cont") := by
    simp only [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
      if_neg (show ofString "cur_cont" ≠ ofString "ev" from by decide),
      if_pos rfl, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (memW_lt s _)
  have hcc : globN (setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont"))))) s)) "cur_cont" =
      memW s (globN s "cur_cont" + 8) := by
    simp only [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
      if_pos rfl, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (memW_lt s _)
  have hch := EvmEkFk.evmChain_pop_eq_tail hk hInv.2.choose_spec.2.2.2.1 (by rfl) hev hcc
  exact finish_child_parent_alignment hs hk hch (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩) hev

/-- Transport alignment through the prelude's preserved chain cells. -/
theorem finish_child_prelude_alignment {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F}
    (hpre : EvmEkFk.PreludeRel s0 s) (hs : HeadMemChainWF s0)
    (hfmp : globN s "frame_mem_ptr" = globN s0 "frame_mem_ptr") :
    HeadMemChainWF s := by
  apply headMemChainWF_of_agree hs hpre.chain_eq hpre.cells
  · have hh := congrArg List.head? hpre.chain_eq
    rw [evmChain_cons, evmChain_cons] at hh
    exact (Prod.mk.inj (Option.some.inj hh)).1
  · exact hfmp

/-- Alignment and links after executing the prelude and concrete pop. -/
theorem finish_child_prelude_pop_alignment {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F}
    (hpre : EvmEkFk.PreludeRel s0 s) (hs : HeadMemChainWF s0)
    (hfmp : globN s "frame_mem_ptr" = globN s0 "frame_mem_ptr")
    (hk0 : memW s0 (globN s0 "cur_cont" + 16) ≠ 0) :
    let post := setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s (globN s "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) s)
    (∀ ec ∈ evmChain post,
      memW post (ec.1 + 32) % 32 = 0 ∧ memW post (ec.1 + 40) % 8 = 0) ∧
    ChainLinks (memW post) (evmChain post) ∧
    memW post (globN post "ev" + 24) + memW post (globN post "ev" + 40) =
      memW s (globN s "cur_cont" + 56) := by
  obtain ⟨hk, hp, _⟩ := finish_child_prelude_parent hpre hk0
  dsimp only
  rw [← hp]
  exact finish_child_pop_alignment (finish_child_prelude_alignment hpre hs hfmp) hpre.inv hk

/-- Close the joint finish-child postcondition once the branches establish the
parent invariant, release readiness, preserved chain cells, and gas bound. -/
theorem finish_child_cleanup_finishPost {F : Type}
    (s0 st post : PanSemStateFiniteExact 64 F) (cmw cmmw : BitVec 64) {S : List Nat}
    (hAs : ArenaReady st)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt st S)
    (hRel : EvmEkFk.ReleaseReadyAt st S cmw.toNat cmmw.toNat)
    (hcm : st.locals.lookup (ofString "child_mark") = some (.val (.word cmw)))
    (hcmm : st.locals.lookup (ofString "child_mem_mark") = some (.val (.word cmmw)))
    (hs : HeadMemChainWF s0)
    (hk : memW s0 (globN s0 "cur_cont" + 16) ≠ 0)
    (hchain : evmChain st = (evmChain s0).tail)
    (hlen : (evmChain st).length + 1 = (evmChain s0).length)
    (hcells : ∀ ec ∈ evmChain st,
      memW st (ec.1 + 24) = memW s0 (ec.1 + 24) ∧
      memW st (ec.1 + 32) = memW s0 (ec.1 + 32) ∧
      memW st (ec.1 + 40) = memW s0 (ec.1 + 40) ∧
      memW st (ec.2 + 56) = memW s0 (ec.2 + 56))
    (hev : globN st "ev" = memW s0 (globN s0 "cur_cont"))
    (hmark : cmmw.toNat = memW s0 (globN s0 "cur_cont" + 56))
    (hgas : R11Shards.OpDispatchSpec.evmR st ≤ R11Shards.OpDispatchSpec.evmR s0)
    (v : ValueHOL 64)
    (hr : evaluateHOLFiniteState st EvmEkFk.fcCleanup = (some (.returned v), post)) :
    EvmInvA post ∧ EvmEkFk.FinishPost s0 (some (.returned v)) post := by
  obtain ⟨halign, hlinks, hend⟩ := finish_child_parent_alignment hs hk hchain hcells hev
  obtain ⟨hIp, hchp, hcp, hevp, hfmp, hRp⟩ :=
    finish_child_cleanup_from_invariants st post cmw cmmw hAs hInv hRel hcm hcmm
      halign hlinks (hend.trans hmark.symm) v hr
  refine ⟨hIp, fun _ => ⟨hIp.1, ?_, hRp.trans hgas, hchp.trans hchain, ?_,
    hevp.trans hev, hfmp.trans hmark⟩⟩
  · rw [hchp]; exact hlen
  · intro ec hec
    have hmem := hcp ec (hchp ▸ hec)
    have hmem0 := hcells ec (hchp ▸ hec)
    exact ⟨hmem.1.trans hmem0.1, hmem.2.1.trans hmem0.2.1,
      hmem.2.2.1.trans hmem0.2.2.1, hmem.2.2.2.trans hmem0.2.2.2⟩

theorem chainLinks_iff_finishChild (m : Nat → Nat) (xs : List Ivl) :
    ChainLinks m xs ↔ EvmEkFk.ChainLinks m xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b tail =>
      exact and_congr Iff.rfl ih

theorem headMemChainWF_iff_finishChild {F : Type} (s : PanSemStateFiniteExact 64 F) :
    HeadMemChainWF s ↔ EvmEkFk.HeadMemChainWF s := by
  exact and_congr Iff.rfl (and_congr Iff.rfl (chainLinks_iff_finishChild _ _))

theorem finishReadyA_iff_finishChild {F : Type} (s : PanSemStateFiniteExact 64 F) :
    FinishReadyA s ↔ EvmEkFk.FinishReadyA s := by
  exact and_congr (and_congr Iff.rfl (headMemChainWF_iff_finishChild s)) Iff.rfl

/-- Transport the independent finish-child leaf's memory contract into this bridge. -/
theorem finishChildMemSpec_of_leaf (h : EvmEkFk.FinishChildMemSpec) :
    FinishChildMemSpec := by
  obtain ⟨ps, body, rt, hl, hr⟩ := h
  refine ⟨ps, body, rt, hl, fun s hc hs hex hnt => ?_⟩
  exact hr s hc ((finishReadyA_iff_finishChild s).mp hs) hex hnt

/-- `FinishPost` is the single joint postcondition used by the finish-child
body proof. Project its memory footprint without an aligned output assumption. -/
theorem finishChildMemSpec_of_finishPost
    (h : FunSpec FinishReadyA EvmEkFk.FinishPost (ofString "finish_child")) :
    FinishChildMemSpec := by
  obtain ⟨ps, body, rt, hl, hr⟩ := h
  refine ⟨ps, body, rt, hl, fun s hc hs hex hnt hres => ?_⟩
  obtain ⟨_, _, _, hchain, hcells, hev, hfmp⟩ := hr s hc hs hex hnt hres
  exact ⟨hchain, hcells, hev, hfmp⟩

/-- Project the unaligned contract from the same joint body postcondition. -/
theorem finishChildSpecU_of_finishPost
    (h : FunSpec FinishReady EvmEkFk.FinishPost (ofString "finish_child")) :
    FinishChildSpecU := by
  obtain ⟨ps, body, rt, hl, hr⟩ := h
  refine ⟨ps, body, rt, hl, fun s hc hs hex hnt hres => ?_⟩
  obtain ⟨hi, hlen, hgas, _⟩ := hr s hc hs hex hnt hres
  exact ⟨hi, hlen, hgas⟩

/-- One unaligned joint finish-child proof discharges both finish-child
contracts required by the aligned `run_frames` bound. -/
theorem gbody_run_frames_aligned_of_finishPost
    (bf : TerminatingFunBoundedOn FinishReadyA (ofString "finish_child") K.«finish_child»)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue»)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception»)
    (bd : TerminatingFunBoundedOn EvmRunA (ofString "op_dispatch") K.«op_dispatch»)
    (hf : FunSpec FinishReady EvmEkFk.FinishPost (ofString "finish_child"))
    (hd : OpDispatchSpecA) :
    TerminatingFunBoundedOn (fun s => EvmInv s ∧ HeadMemChainWF s)
      (ofString "run_frames") K.«run_frames» := by
  apply gbody_run_frames_aligned_fc bf be bx bd (finishChildSpecU_of_finishPost hf) _ hd
  apply finishChildMemSpec_of_finishPost
  obtain ⟨ps, body, rt, hl, hr⟩ := hf
  exact ⟨ps, body, rt, hl, fun s hc hs hex hnt =>
    hr s hc ⟨hs.1.1, hs.2.1, hs.2.2⟩ hex hnt⟩

/-- The create-finish prelude preserves the aligned chain invariant whenever it
falls through.  Its callee requirements are exactly `CreateFinishSpecs`. -/
theorem fcPrelude_headMemChainWF (hCF : EvmEkFk.CreateFinishSpecs) {F : Type}
    {s0 s1 : PanSemStateFiniteExact 64 F}
    (hRel : EvmEkFk.PreludeRel s0 s1) (hAligned : HeadMemChainWF s0)
    (hcode : s1.code = originalRuntimeCode)
    (hfmp : globN s1 "frame_mem_ptr" = globN s0 "frame_mem_ptr")
    (hnt : (evaluateHOLFiniteState s1 EvmEkFk.fcPrelude).1 ≠ some .timeOut)
    (hflow : (evaluateHOLFiniteState s1 EvmEkFk.fcPrelude).1 = none) :
    HeadMemChainWF (evaluateHOLFiniteState s1 EvmEkFk.fcPrelude).2 := by
  have hpost := (EvmEkFk.fcPrelude_step hCF hRel hnt).1 hflow
  apply headMemChainWF_of_agree hAligned hpost.chain_eq hpost.cells
  · have hh := congrArg List.head? hpost.chain_eq
    rw [evmChain_cons, evmChain_cons] at hh
    exact (Prod.mk.inj (Option.some.inj hh)).1
  · have hg := InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG
      (ofString "frame_mem_ptr") InitECandidate.Solver.GuestFrameMemKeep.goodFrameMem
      good_fmp_hgood EvmEkFk.fcPrelude (by kernel_rfl) s1 hcode
    unfold globN
    rw [hg]
    exact hfmp

/-- Restoring caller locals preserves the destination table supplied by union. -/
theorem unionExit_restore_tables {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : UnionExit s post) (L : HolFiniteMapExact MlS (ValueHOL 64)) :
    HtabWF { post with locals := L } (locN s "dst") ∧
      ∀ i ∈ htabFootprint { post with locals := L } (locN s "dst"),
        Allocated { post with locals := L } i := by
  refine ⟨(htabWF_with_locals post L post.clock _).2 h.2.1, ?_⟩
  intro i hi
  exact h.2.2.2.2.2.1 i hi

attribute [local irreducible] Ret in
/-- The success tail retains the destination table invariant as well as its write frame. -/
theorem ics_tail_tables {F : Type} (X : PanSemStateFiniteExact 64 F) (e tw : BitVec 64)
    (hcode : X.code = originalRuntimeCode)
    (he : X.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hA : ArenaReady X) (htw : X.memory (e + 136) = .word tw)
    (hwf : HtabWF X tw.toNat) (hal : ∀ i ∈ htabFootprint X tw.toNat, Allocated X i)
    (h96 : ∀ i ∈ htabFootprint X tw.toNat, ¬ CellHits (e + 96).toNat i) :
    Ret X (.seq (.store (.op .add [.var .global (ofString "ev"), .const 96])
        (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 96]),
          .load .one (.op .add [.var .local (ofString "child"), .const 96])]))
      (.seq (.call (some (none, none)) (ofString "htab_union_into")
          [.load .one (.op .add [.var .global (ofString "ev"), .const 136]),
           .load .one (.op .add [.var .local (ofString "child"), .const 136])])
        (.return (.const 0))))
      (fun _ post => ICSTail X e tw.toNat post ∧ HtabWF post tw.toNat ∧
        ∀ i ∈ htabFootprint post tw.toNat, Allocated post i) := by
  refine Ret.storeGlobOp he fun w => ?_
  let Y := { X with memory := updW X.memory (e + 96) w }
  have hun : ∀ i ∈ htabFootprint X tw.toNat, Wave8Contracts.M08.IvlUnhit X Y i :=
    fun i hi => ivlUnhit_updW X _ w i (h96 i hi)
  have hG : GuestInv Y := guestInv_congr (s := X) rfl rfl rfl rfl hA.1
  have hAY : ArenaReady Y := ⟨hG, arenaOK_congr (s := X) rfl hA.2⟩
  have ht_fp : ((tw.toNat, 88) : Ivl) ∈ htabFootprint X tw.toNat := by simp [htabFootprint]
  have ht8 : tw.toNat % 8 = 0 := (hwf.1 _ ht_fp).2.1
  have hthi : tw.toNat + 88 ≤ 2 ^ 64 := by
    have := (hwf.1 _ ht_fp).1
    unfold Inside at this
    have : heapEnd ≤ 2 ^ 64 := by decide
    simp only at *; omega
  have hfpeq := (Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit ht8 hthi (hun _ ht_fp)).2
  have hwfY : HtabWF Y tw.toNat := Wave8Contracts.M08.htabWF_congr_unhit hA.1 hG hwf hun
  have halY : ∀ i ∈ htabFootprint Y tw.toNat, Allocated Y i := by
    rw [hfpeq]; exact hal
  have h136 : Y.memory (e + 136) = .word tw := by
    change updW X.memory (e + 96) w (e + 136) = _
    rw [updW_ne _ _ _ _ (by bv_omega)]; exact htw
  refine Ret.seq_call00 fun values body callee ret v cpost h1 h2 h3 => ?_
  obtain ⟨v1, v2, rfl, hv1, _⟩ := evalList2_inv Y _ _ h1
  have hv1' := ev_load_glob Y _ e 136 he v1 hv1
  rw [h136] at hv1'
  subst hv1'
  obtain ⟨_, hdst⟩ := rb_param_at Y.code.lookup (ofString "htab_union_into") []
    (ofString "dst") .one [(ofString "src", .one)] _ _
    (by simp only [List.mem_singleton]; rintro _ rfl; decide)
    (by rw [show Y.code = originalRuntimeCode from hcode];
        simpa using UXT.HtabUnionInto.lookup_htab_union_into) (vpre := []) (by simp) h2
  have hlocT : locN (callEntryStateHOLFinite Y callee) "dst" = tw.toNat := by
    simp only [locN, callEntryStateHOLFinite, hdst]
  have hPc : UnionArgWF (callEntryStateHOLFinite Y callee) := by
    refine ⟨(arenaReady_with_locals Y callee (Y.clock - 1)).2 hAY, ?_, ?_⟩
    · rw [hlocT]; exact (htabWF_with_locals Y callee (Y.clock - 1) _).2 hwfY
    · rw [hlocT]; exact halY
  have hQ := HtabC00Ports.FunSpec.at_lookup UXT.rb_htab_union_into_spec Y hcode
    _ body callee ret h2 hPc (by rw [h3]; simp)
  rw [h3] at hQ
  have hx := hQ v rfl
  have ht := unionExit_restore_tables hx (emptyLocalsHOLFinite cpost).locals
  rw [hlocT] at ht
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite Y callee) body
  rw [h3] at hmeta
  obtain ⟨hAR, _, _, _, hgrow, _, hfr, hglob⟩ := hx
  rw [hlocT] at hfr
  refine Ret.ret fun val _ => ⟨?_, ht⟩
  refine ⟨hmeta.1, hmeta.2.1, ?_, ?_, hgrow, ?_⟩
  · exact arenaReady_locals _ _ (arenaReady_locals _ _ hAR)
  · intro k hk
    exact (hglob k (by simpa using hk)).symm
  · intro a ha hk hf
    have h1 := hfr a (by
        intro i hi
        have hi' : i ∈ htabFootprint Y tw.toNat := hi
        rw [hfpeq] at hi'; exact hk i hi') hf
    change cpost.memory a = _
    rw [h1]
    change updW X.memory (e + 96) w a = _
    rw [updW_ne _ _ _ _ ha]

/-- Prefix and child-suffix contents reconstruct the appended log-list invariant. -/
theorem logsListOK_of_append_contents {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {L child n nc : Nat}
    (hp : LogsListOK s L) (hc : LogsListOK s child)
    (hn : memW s (L + 8) = n) (hnc : memW s (child + 8) = nc)
    (hpn : L ≠ 0) (hcn : child ≠ 0)
    (hwords : WordsOK post (L, 24)) (halloc : Allocated post (L, 24))
    (hcount : memW post (L + 8) = n + nc)
    (hbound : n + nc < 2 ^ 28)
    (hcap : n + nc ≤ memW post (L + 16))
    (hslots : ∀ i, i < n + nc → WordAt post (memW post L + 8 * i))
    (hprefix : ∀ i, i < n →
      memW post (memW post L + 8 * i) = memW s (memW s L + 8 * i))
    (hsuffix : ∀ i, i < nc →
      memW post (memW post L + 8 * (n + i)) = memW s (memW s child + 8 * i))
    (hkeepP : ∀ i, i < n →
      LogEntryOK post (memW s (memW s L + 8 * i)))
    (hkeepC : ∀ i, i < nc →
      LogEntryOK post (memW s (memW s child + 8 * i))) :
    LogsListOK post L := by
  rcases hp with hz | ⟨_, _, _, _, hp⟩
  · exact False.elim (hpn hz)
  rcases hc with hz | ⟨_, _, _, _, hc⟩
  · exact False.elim (hcn hz)
  refine Or.inr ⟨hwords, halloc, by omega, by omega, ?_⟩
  intro i hi
  rw [hcount] at hi
  refine ⟨hslots i hi, ?_⟩
  by_cases hip : i < n
  · rw [hprefix i hip]
    exact hkeepP i hip
  · have his : i - n < nc := by omega
    have hieq : i = n + (i - n) := by omega
    rw [hieq, hsuffix (i - n) his]
    exact hkeepC (i - n) his

/-- Heap growth preserves a log entry once its five record fields and words survive. -/
theorem logEntryOK_of_record_preserved {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {log : Nat}
    (h : LogEntryOK s log) (hheap : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hwords : WordsOK post (log, 40))
    (hfields : ∀ k ∈ [0, 8, 16, 24, 32], memW post (log + k) = memW s (log + k)) :
    LogEntryOK post log := by
  have h0 := hfields 0 (by simp)
  have h8 := hfields 8 (by simp)
  have h16 := hfields 16 (by simp)
  have h24 := hfields 24 (by simp)
  have h32 := hfields 32 (by simp)
  simp only [Nat.add_zero] at h0
  unfold LogEntryOK at h ⊢
  rw [h0, h8, h16, h24, h32]
  obtain ⟨_, hr, ht, hn, ha, hb, hc⟩ := h
  exact ⟨hwords, ⟨hr.1, hr.2.trans hheap⟩, ht, hn,
    ⟨ha.1, ha.2.trans hheap⟩, ⟨hb.1, hb.2.trans hheap⟩,
    ⟨hc.1, hc.2.trans hheap⟩⟩

/-- A separated allocated cell survives the success tail's store and union. -/
theorem icsTail_memW {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e : BitVec 64} {T : Nat} (h : ICSTail s e T post)
    (hA : ArenaReady s) {i : Ivl} (hi : Allocated s i) {a : Nat}
    (ha : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) (hab : a < 2 ^ 64)
    (hE : ¬ CellHits (e + 96).toNat i)
    (hT : ∀ j ∈ htabFootprint s T, Disj i j) (hwf : HtabWF s T) :
    memW post a = memW s a := by
  apply memW_of
  apply h.2.2.2.2.2
  · apply Ne.symm
    apply ne_of_not_hits hE
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using ha
  · intro j hj
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using
      noHit_of_disj (hT j hj) (htab_fp_pos hwf j hj) ha
  · have hp := h.2.2.1.2.2.1
    have hs := hA.2.2.2.1
    have hs' := hA.2.2.2.2.1
    have heq : heapLimit = scratchStart := rfl
    rw [heq] at hp
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using
      noFresh_of_alloc hA.2 hi ha (by omega) h.2.2.2.2.1

/-- The table-union tail preserves separated log records and their payload bounds. -/
theorem icsTail_logEntryOK {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e : BitVec 64} {T log : Nat} (h : ICSTail s e T post)
    (hA : ArenaReady s) (hlog : LogEntryOK s log)
    (hE : ¬ CellHits (e + 96).toNat (log, 40))
    (hT : ∀ j ∈ htabFootprint s T, Disj (log, 40) j) (hwf : HtabWF s T) :
    LogEntryOK post log := by
  have hal : Allocated s (log, 40) := Or.inl hlog.2.1
  have hbound : log + 40 ≤ 2 ^ 64 := by
    have hh := hA.2.2.1
    have hb : heapLimit < 2 ^ 64 := by decide
    have hl := hlog.2.1.2
    dsimp only at hl
    omega
  have hkeep (a : Nat) (ha : log ≤ a ∧ a + 8 ≤ log + 40) :
      memW post a = memW s a :=
    icsTail_memW h hA hal ha (by omega) hE hT hwf
  apply logEntryOK_of_record_preserved hlog h.2.2.2.2.1
  · obtain ⟨ha, hn, hw⟩ := hlog.1
    refine ⟨ha, hn, fun k hk => ?_⟩
    obtain ⟨w, hd, hm⟩ := hw k hk
    refine ⟨w, ?_, ?_⟩
    · rw [h.2.1]; exact hd
    · have heq := h.2.2.2.2.2 (BitVec.ofNat 64 (log + 8 * k))
        (Ne.symm (ne_of_not_hits hE (by
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show log + 8 * k < 2 ^ 64 by omega)]
          omega)))
        (fun j hj => by
          simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show log + 8 * k < 2 ^ 64 by omega)] using
            noHit_of_disj (hT j hj) (htab_fp_pos hwf j hj)
              (show log ≤ log + 8 * k ∧ log + 8 * k + 8 ≤ log + 40 by omega))
        (by
          have hp := h.2.2.1.2.2.1
          have hs := hA.2.2.2.1
          have hs' := hA.2.2.2.2.1
          have heq : heapLimit = scratchStart := rfl
          rw [heq] at hp
          simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show log + 8 * k < 2 ^ 64 by omega)] using
            noFresh_of_alloc hA.2 hal
              (show log ≤ log + 8 * k ∧ log + 8 * k + 8 ≤ log + 40 by omega)
              (by omega) h.2.2.2.2.1)
      exact heq.trans hm
  · intro k hk
    have hk' : k ≤ 32 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    exact hkeep _ (by omega)

/-- Preserve all words of an allocated interval separated from the success tail. -/
theorem icsTail_wordsOK {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e : BitVec 64} {T : Nat} {i : Ivl} (h : ICSTail s e T post)
    (hA : ArenaReady s) (hi : Allocated s i) (hw : WordsOK s i)
    (hib : i.1 + i.2 ≤ 2 ^ 64)
    (hE : ¬ CellHits (e + 96).toNat i)
    (hT : ∀ j ∈ htabFootprint s T, Disj i j) (hwf : HtabWF s T) :
    WordsOK post i := by
  obtain ⟨ha, hn, hw⟩ := hw
  refine ⟨ha, hn, fun k hk => ?_⟩
  obtain ⟨w, hd, hm⟩ := hw k hk
  have hak : i.1 ≤ i.1 + 8 * k ∧ i.1 + 8 * k + 8 ≤ i.1 + i.2 := by omega
  have hab : i.1 + 8 * k < 2 ^ 64 := by omega
  refine ⟨w, by rw [h.2.1]; exact hd, ?_⟩
  apply Eq.trans _ hm
  apply h.2.2.2.2.2
  · apply Ne.symm
    exact ne_of_not_hits hE (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using hak)
  · intro j hj
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using
      noHit_of_disj (hT j hj) (htab_fp_pos hwf j hj) hak
  · have hp := h.2.2.1.2.2.1
    have hs := hA.2.2.2.1
    have hs' := hA.2.2.2.2.1
    have heq : heapLimit = scratchStart := rfl
    rw [heq] at hp
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using
      noFresh_of_alloc hA.2 hi hak (by omega) h.2.2.2.2.1

/-- Once the append loop establishes its contents, table union preserves the
whole parent log-list invariant, including every referenced log record. -/
theorem icsTail_logsListOK {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e L : BitVec 64} {T : Nat} (h : ICSTail s e T post)
    (hA : ArenaReady s) (hlogs : LogsListOK s L.toNat)
    (hL : Allocated s (L.toNat, 24)) (hLB : L.toNat + 24 ≤ 2 ^ 64)
    (hE : ¬ CellHits (e + 96).toNat (L.toNat, 24))
    (hT : ∀ j ∈ htabFootprint s T, Disj (L.toNat, 24) j)
    (hwf : HtabWF s T)
    (harr : Allocated s (memW s L.toNat, 8 * memW s (L.toNat + 16)))
    (harrW : WordsOK s (memW s L.toNat, 8 * memW s (L.toNat + 16)))
    (harrB : memW s L.toNat + 8 * memW s (L.toNat + 16) ≤ 2 ^ 64)
    (harrE : ¬ CellHits (e + 96).toNat (memW s L.toNat, 8 * memW s (L.toNat + 16)))
    (harrT : ∀ j ∈ htabFootprint s T,
      Disj (memW s L.toNat, 8 * memW s (L.toNat + 16)) j)
    (hlogE : ∀ i, i < memW s (L.toNat + 8) →
      ¬ CellHits (e + 96).toNat (memW s (memW s L.toNat + 8 * i), 40))
    (hlogT : ∀ i, i < memW s (L.toNat + 8) → ∀ j ∈ htabFootprint s T,
      Disj (memW s (memW s L.toNat + 8 * i), 40) j) :
    LogsListOK post L.toNat := by
  rcases hlogs with hz | ⟨hwords, _, hcount, hcap, hentries⟩
  · exact Or.inl hz
  have hdrKeep (k : Nat) (hk : k ≤ 16) :
      memW post (L.toNat + k) = memW s (L.toNat + k) :=
    icsTail_memW h hA hL (by dsimp only; omega) (by omega) hE hT hwf
  have h0 := hdrKeep 0 (by omega)
  simp only [Nat.add_zero] at h0
  have h8 := hdrKeep 8 (by omega)
  have h16 := hdrKeep 16 (by omega)
  have harrWp := icsTail_wordsOK h hA harr harrW harrB harrE harrT hwf
  have halloc : Allocated post (L.toNat, 24) := by
    apply Wave8Contracts.M23.allocated_mono h.2.2.2.2.1 _ hL
    unfold globN
    rw [h.2.2.2.1 _ (by decide)]
  refine Or.inr ⟨icsTail_wordsOK h hA hL hwords hLB hE hT hwf,
    halloc, by rwa [h8], by rwa [h8, h16], ?_⟩
  intro i hi
  rw [h8] at hi
  have hiCap : i < memW s (L.toNat + 16) := by omega
  obtain ⟨hslot, hlog⟩ := hentries i hi
  have hs := icsTail_memW h hA harr
    (show memW s L.toNat ≤ memW s L.toNat + 8 * i ∧
      memW s L.toNat + 8 * i + 8 ≤ memW s L.toNat + 8 * memW s (L.toNat + 16) by omega)
    (by omega) harrE harrT hwf
  rw [h0, hs]
  refine ⟨?_, icsTail_logEntryOK h hA hlog (hlogE i hi) (hlogT i hi) hwf⟩
  obtain ⟨_, _, hw⟩ := harrWp
  exact hw i (by dsimp only; omega)

/-- Content-preserving copy rule for the list-growth branch. -/
theorem Flw.seq_memcpy_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ed es en : ExpHOL 64} {cont : ProgHOL 64}
    {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (dst src n : BitVec 64)
    (hd_nw : dst.toNat + n.toNat < 2 ^ 64)
    (hs_nw : src.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hdisj : Disj (dst.toNat, n.toNat) (src.toNat, n.toNat))
    (hed : ev s ed = some (.val (.word dst)))
    (hes : ev s es = some (.val (.word src)))
    (hen : ev s en = some (.val (.word n)))
    (hk : ∀ s' : PanSemStateFiniteExact 64 F,
      SoloHtabSet.MemCopyRel s s' dst src n.toNat n.toNat →
      s'.locals = s.locals → Flw s' cont Ψ) :
    Flw s (.seq (.call (some (none, none)) (ofString "memcpy") [ed, es, en]) cont) Ψ := by
  refine Flw.seq_call00 fun values body callee ret v post h1 h2 h3 => ?_
  have hv : values = [.val (.word dst), .val (.word src), .val (.word n)] := by
    simp only [evalListHOLFinite, evalListHOLExact] at h1
    unfold ev at hed hes hen
    rw [hed, hes, hen] at h1; simp at h1; exact h1.symm
  subst hv
  have hl := pan_three_word_lookup s.code.lookup (ofString "memcpy") (ofString "dst") (ofString "src")
    (ofString "n") _ dst src n (by decide) (by decide) (by decide)
    (by rw [hcode]; exact SoloHtabSet.lookup_memcpy_fn)
  rw [hl] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  let entry := callEntryStateHOLFinite s
    (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst))).update
      (ofString "src", .val (.word src))).update (ofString "n", .val (.word n)))
  have hspec := SoloHtabSet.memcpy_body_spec entry dst src n hd_nw hs_nw hn_small hdisj
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "src" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    v (by rw [h3])
  rw [h3] at hspec
  obtain ⟨_, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hspec
  exact hk _ ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ rfl

/-- Aligned list reallocation retains every complete copied entry. -/
theorem Flw.seq_memcpy_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ed es en : ExpHOL 64} {cont : ProgHOL 64}
    {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (dst src n : BitVec 64)
    (hd_nw : dst.toNat + n.toNat < 2 ^ 64)
    (hs_nw : src.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hdisj : Disj (dst.toNat, n.toNat) (src.toNat, n.toNat))
    (hd8 : dst.toNat % 8 = 0) (hs8 : src.toNat % 8 = 0)
    (hed : ev s ed = some (.val (.word dst)))
    (hes : ev s es = some (.val (.word src)))
    (hen : ev s en = some (.val (.word n)))
    (hk : ∀ s' : PanSemStateFiniteExact 64 F,
      SoloHtabSet.MemCopyRel s s' dst src n.toNat n.toNat →
      (∀ i, 8 * i + 8 ≤ n.toNat →
        memW s' (dst.toNat + 8 * i) = memW s (src.toNat + 8 * i)) →
      s'.locals = s.locals → Flw s' cont Ψ) :
    Flw s (.seq (.call (some (none, none)) (ofString "memcpy") [ed, es, en]) cont) Ψ := by
  refine Flw.seq_memcpy_disj (cont := cont) (Ψ := Ψ) hcode dst src n
    hd_nw hs_nw hn_small hdisj hed hes hen ?_
  intro s' hr hl
  apply hk s' hr _ hl
  intro i hi
  exact SoloHtabSet.memW_copied_of_memCopyRel hr hd8 hs8 (by omega) hi hd_nw hs_nw

theorem log_slot_toNat (arr n : BitVec 64)
    (h : arr.toNat + 8 * n.toNat < 2 ^ 64) :
    (arr + n * 8).toNat = arr.toNat + 8 * n.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul]
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [h8, Nat.mod_eq_of_lt (show n.toNat * 8 < 2 ^ 64 by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Appending one entry leaves the existing prefix intact. -/
theorem log_store_prefix {F : Type} (s : PanSemStateFiniteExact 64 F)
    (arr n lg : BitVec 64) (h : arr.toNat + 8 * n.toNat < 2 ^ 64)
    (i : Nat) (hi : i < n.toNat) :
    memW { s with memory := updW s.memory (arr + n * 8) lg }
      (arr.toNat + 8 * i) = memW s (arr.toNat + 8 * i) := by
  unfold memW
  dsimp only
  rw [updW_ne _ _ _ _ (by
    intro he
    have he' := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show arr.toNat + 8 * i < 2 ^ 64 by omega),
      log_slot_toNat arr n h] at he'
    omega)]

/-- The append store installs the exact new log pointer. -/
theorem log_store_new {F : Type} (s : PanSemStateFiniteExact 64 F)
    (arr n lg : BitVec 64) (h : arr.toNat + 8 * n.toNat < 2 ^ 64) :
    memW { s with memory := updW s.memory (arr + n * 8) lg }
      (arr.toNat + 8 * n.toNat) = lg.toNat := by
  have he : BitVec.ofNat 64 (arr.toNat + 8 * n.toNat) = arr + n * 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, log_slot_toNat arr n h]
  unfold memW
  dsimp only
  rw [he, updW_eq]

/-- One append extends the child suffix while retaining the parent's prefix. -/
theorem append_contents_step (old child current next : Nat → Nat) (n i : Nat)
    (hp : ∀ k, k < n → current k = old k)
    (hs : ∀ k, k < i → current (n + k) = child k)
    (hkeep : ∀ k, k < n + i → next k = current k)
    (hnew : next (n + i) = child i) :
    (∀ k, k < n → next k = old k) ∧
      ∀ k, k < i + 1 → next (n + k) = child k := by
  constructor
  · intro k hk
    exact (hkeep k (by omega)).trans (hp k hk)
  · intro k hk
    by_cases hki : k < i
    · exact (hkeep (n + k) (by omega)).trans (hs k hki)
    · have : k = i := by omega
      subst k
      exact hnew

/-- The growth-copy continuation receives the prefix after all three header stores. -/
theorem Flw.seq_memcpy_header_contents {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ed es en : ExpHOL 64} {cont : ProgHOL 64}
    {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (l dst src n : BitVec 64)
    (hdw : dst.toNat + 8 * n.toNat < 2 ^ 64)
    (hsw : src.toNat + 8 * n.toNat < 2 ^ 64)
    (hn : 8 * n.toNat + 32 < 2 ^ 63)
    (hlen : (n * 8).toNat = 8 * n.toNat)
    (hdisj : Disj (dst.toNat, 8 * n.toNat) (src.toNat, 8 * n.toNat))
    (hd8 : dst.toNat % 8 = 0) (hs8 : src.toNat % 8 = 0)
    (hlw : l.toNat + 24 ≤ 2 ^ 64)
    (hsep : l.toNat + 24 ≤ dst.toNat ∨ dst.toNat + 8 * n.toNat ≤ l.toNat)
    (hed : ev s ed = some (.val (.word dst)))
    (hes : ev s es = some (.val (.word src)))
    (hen : ev s en = some (.val (.word (n * 8))))
    (hk : ∀ copied : PanSemStateFiniteExact 64 F,
      SoloHtabSet.MemCopyRel s copied dst src (8 * n.toNat) (8 * n.toNat) →
      copied.locals = s.locals →
      (∀ i, i < n.toNat →
        memW { copied with memory := updW (updW (updW copied.memory l dst) (l + 16) (n * 2)) (l + 8) (n + 1) }
          (dst.toNat + 8 * i) = memW s (src.toNat + 8 * i)) →
      Flw copied cont Ψ) :
    Flw s (.seq (.call (some (none, none)) (ofString "memcpy") [ed, es, en]) cont) Ψ := by
  refine Flw.seq_memcpy_disj (cont := cont) (Ψ := Ψ) hcode dst src (n * 8)
    (by rw [hlen]; exact hdw) (by rw [hlen]; exact hsw)
    (by rw [hlen]; exact hn) (by simpa only [hlen] using hdisj) hed hes hen ?_
  intro copied hc hl
  rw [hlen] at hc
  exact hk copied hc hl (lst_push_growth_prefix l dst src n hc hd8 hs8 hdw hsw hlw hsep)

theorem lst_push_run_no_growth_contents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (l arr0 n cap : BitVec 64) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hesz : s.locals.lookup (ofString "esz") = some (.val (.word 8)))
    (hma : s.memory l = .word arr0)
    (hmn : s.memory (l + 8) = .word n) (hmc : s.memory (l + 16) = .word cap)
    (hd0 : s.memaddrs l) (hd8 : s.memaddrs (l + 8)) (hd16 : s.memaddrs (l + 16))
    (hlt : n.toNat < cap.toNat) (hcap : n.toNat < 2 ^ 59)
    (hw : arr0.toNat + 8 * cap.toNat ≤ 2 ^ 64) (hlw : l.toNat + 24 ≤ 2 ^ 64)
    (hsep : l.toNat + 24 ≤ arr0.toNat ∨ arr0.toNat + 8 * cap.toNat ≤ l.toNat) :
    Ret s (sourceFnBody Guest.Software.guestFn_lst_push)
      (fun v post => LstPushPost s l 8 n cap v post ∧
        post.memory l = .word arr0 ∧
        ∀ i, i < n.toNat → memW post (arr0.toNat + 8 * i) = memW s (arr0.toNat + 8 * i)) := by
  refine Ret.mono (lst_push_run s l 8 n cap hA hl hesz hmn hmc hd0 hd8 hd16
    (by omega) hcap (by decide)) ?_
  intro v post hp
  exact ⟨hp, lstPushPost_prefix_no_growth hp hma hlt hw hlw hsep⟩

theorem log_append_store_contents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (arr n lg : BitVec 64) (old : Nat → Nat)
    (hw : arr.toNat + 8 * n.toNat < 2 ^ 64)
    (hp : ∀ i, i < n.toNat → memW s (arr.toNat + 8 * i) = old i) :
    (∀ i, i < n.toNat →
      memW { s with memory := updW s.memory (arr + n * 8) lg } (arr.toNat + 8 * i) = old i) ∧
    memW { s with memory := updW s.memory (arr + n * 8) lg }
      (arr.toNat + 8 * n.toNat) = lg.toNat := by
  exact ⟨fun i hi => (log_store_prefix s arr n lg hw i hi).trans (hp i hi),
    log_store_new s arr n lg hw⟩

def PushContents {F : Type} (s : PanSemStateFiniteExact 64 F) (l arr0 n : BitVec 64)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ arr : BitVec 64, post.memory l = .word arr ∧ v = .val (.word (arr + n * 8)) ∧
    arr.toNat % 8 = 0 ∧
    ∀ i, i < n.toNat → memW post (arr.toNat + 8 * i) = memW s (arr0.toNat + 8 * i)

attribute [local irreducible] Ret in
theorem lst_push_run_contents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (l arr0 n cap : BitVec 64) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hesz : s.locals.lookup (ofString "esz") = some (.val (.word 8)))
    (hma : s.memory l = .word arr0)
    (hmn : s.memory (l + 8) = .word n) (hmc : s.memory (l + 16) = .word cap)
    (hd0 : s.memaddrs l) (hle : n.toNat ≤ cap.toNat) (hcap : n.toNat < 2 ^ 59)
    (ha8 : arr0.toNat % 8 = 0)
    (hw : arr0.toNat + 8 * n.toNat < 2 ^ 64)
    (hold : arr0.toNat + 8 * n.toNat ≤ globN s "heap_ptr" ∨ heapLimit ≤ arr0.toNat)
    (hLw : l.toNat + 24 ≤ 2 ^ 64)
    (hsep : l.toNat + 24 ≤ arr0.toNat ∨ arr0.toNat + 8 * n.toNat ≤ l.toNat)
    (hLh : l.toNat + 24 ≤ globN s "heap_ptr" ∨ heapLimit ≤ l.toNat) :
    Ret s (sourceFnBody Guest.Software.guestFn_lst_push) (PushContents s l arr0 n) := by
  have hb : sourceFnBody Guest.Software.guestFn_lst_push =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_lst_push).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_lst_push,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.mono (Φ := PushContents s l arr0 n) ?_ (fun _ _ h => h)
  refine Ret.dec fun v1 hv1 => ?_
  have hv1' : v1 = .val (.word n) := by rw [ev_load_loc s _ l 8 hl v1 hv1, hmn]
  subst hv1'
  let S1 := setVarHOLFinite (ofString "n") (.val (.word n)) s
  refine Ret.mono (Φ := PushContents s l arr0 n) ?_ (fun _ _ h => h)
  refine Ret.dec fun v2 hv2 => ?_
  have hS1l : S1.locals.lookup (ofString "l") = some (.val (.word l)) := by
    simp (config := {decide := true}) [S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl]
  have hv2' : v2 = .val (.word cap) := by rw [ev_load_loc S1 _ l 16 hS1l v2 hv2]; exact congrArg _ hmc
  subst hv2'
  let S2 := setVarHOLFinite (ofString "cap") (.val (.word cap)) S1
  have hS2l : S2.locals.lookup (ofString "l") = some (.val (.word l)) := by
    simp (config := {decide := true}) [S2, S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl]
  have hS2e : S2.locals.lookup (ofString "esz") = some (.val (.word 8)) := by
    simp (config := {decide := true}) [S2, S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hesz]
  have hS2n : S2.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp (config := {decide := true}) [S2, S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hS2c : S2.locals.lookup (ofString "cap") = some (.val (.word cap)) := by
    simp (config := {decide := true}) [S2, S1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine Ret.mono (Φ := PushContents s l arr0 n) ?_ (fun _ _ h => h)
  show Ret S2 _ _
  refine Ret.seq_ite fun cw hcw => ⟨fun hcnz => ?_, fun hcz => ?_⟩
  · have hcw' := srd_cmp S2 .notLower _ _ n cap cw hS2n hS2c hcw
    have hge : cap.toNat ≤ n.toNat := by
      by_contra hlt
      apply hcnz; rw [hcw']
      simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      simp; omega
    have hnc : n = cap := BitVec.eq_of_toNat_eq (by omega)
    have hmul : ((8 : BitVec 64) * n).toNat = 8 * n.toNat := by
      rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by change 8 * n.toNat < 2 ^ 64; omega)
    have hmul2 : ((8 : BitVec 64) * cap * 2).toNat = 16 * n.toNat := by
      rw [← hnc, BitVec.toNat_mul, hmul]
      change (8 * n.toNat * 2) % 2 ^ 64 = _
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    refine Ret.seq_flw (NoRet.decCall (NoRet.seq NoRet.call0 (NoRet.seq NoRet.store' NoRet.store'))) ?_
    refine Flw.decCall_alloc (arenaReady_locals s _ hA) (8 * cap * 2)
      (ev_mulE _ _ _ _ _ (ev_mul_loc S2 _ _ 8 cap hS2e hS2c) (ev_const _ _))
      fun hp q hhp hq1 hq2 hq3 k => ?_
    rw [hmul2] at hq1
    have hhp' : hp.toNat = globN s "heap_ptr" := hhp
    have hqm : q.toNat ≤ 2952790016 := hq2
    have hsep' : l.toNat + 24 ≤ hp.toNat ∨ hp.toNat + 8 * n.toNat ≤ l.toNat := by
      rcases hLh with h | h
      · left; omega
      · right; change 2952790016 ≤ l.toNat at h; omega
    let X := setVarHOLFinite (ofString "np") (.val (.word hp))
      { S2 with globals := S2.globals.update (ofString "heap_ptr", .val (.word q)), clock := k }
    have hXl : X.locals.lookup (ofString "l") = some (.val (.word l)) := by
      simp (config := {decide := true}) [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2l]
    have hXe : X.locals.lookup (ofString "esz") = some (.val (.word 8)) := by
      simp (config := {decide := true}) [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2e]
    have hXn : X.locals.lookup (ofString "n") = some (.val (.word n)) := by
      simp (config := {decide := true}) [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2n]
    have hXc : X.locals.lookup (ofString "cap") = some (.val (.word cap)) := by
      simp (config := {decide := true}) [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hS2c]
    have hXp : X.locals.lookup (ofString "np") = some (.val (.word hp)) := by
      simp [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    show Flw X _ _
    refine Flw.seq_memcpy_disj hA.1.code hp arr0 (8 * n)
      (by rw [hmul]; omega) (by rw [hmul]; exact hw)
      (by rw [hmul]; omega) (by
        unfold Disj; simp only [hmul]
        rcases hold with hold | hold
        · exact Or.inr (Or.inr (Or.inr (by omega)))
        · apply Or.inr; apply Or.inr; apply Or.inl
          change 2952790016 ≤ arr0.toNat at hold
          have hqbound : q.toNat ≤ 2952790016 := hqm
          omega)
      (by rw [ev_loc]; exact hXp)
      (ev_load_loc_eq X _ l 0 arr0 hXl (by show s.memaddrs (l + 0); simpa using hd0)
        (by show s.memory (l + 0) = _; simpa using hma))
      (ev_mul_loc X _ _ 8 n hXe hXn) fun copied hc hloc => ?_
    have h's l' : copied.locals.lookup l' = X.locals.lookup l' := by rw [hloc]
    have hprefix := lst_push_growth_prefix l hp arr0 n (by simpa only [hmul] using hc)
      (by rw [hhp']; exact hA.2.2.2.2.2.2.1) ha8 (by omega) hw hLw hsep'
    refine Flw.seq (Flw.storeW (l + 0) hp (ev_addr copied _ l 0 (by rw [h's]; exact hXl))
      (by rw [ev_loc, h's]; exact hXp) fun _ => ⟨fun _ => ?_, fun h => absurd rfl h⟩)
    refine Flw.storeW (l + 16) (cap * 2) (ev_addr _ _ l 16 (by rw [h's]; exact hXl))
      (ev_mulE _ _ _ _ _ (by rw [ev_loc]; exact (h's _).trans hXc) (ev_const _ _)) fun _ => ?_
    intro _
    let T : PanSemStateFiniteExact 64 F :=
      { copied with memory := updW (updW copied.memory (l + 0) hp) (l + 16) (cap * 2) }
    let L' := HolFiniteMapExact.resVarEq T.locals (ofString "np", S2.locals.lookup (ofString "np"))
    let T' : PanSemStateFiniteExact 64 F := { T with locals := L' }
    show Ret T' _ _
    have hT'l k (hk : k ≠ ofString "np") : T'.locals.lookup k = X.locals.lookup k := by
      show L'.lookup k = _
      simp only [L', T]
      rw [InitECandidate.Solver.PanRunBounded.resVarEq_lookup, if_neg hk, hloc]
    have hT'm : T'.memory l = .word hp := by
      change updW (updW copied.memory (l + 0) hp) (l + 16) (cap * 2) l = _
      rw [updW_ne _ _ _ _ (by bv_omega), show l + 0 = l by bv_omega, updW_eq]
    refine Ret.mono (lst_push_tail T' l 8 n hp (by rw [hT'l _ (by decide)]; exact hXl)
      (by rw [hT'l _ (by decide)]; exact hXe) (by rw [hT'l _ (by decide)]; exact hXn) hT'm
      (by show copied.memaddrs l; rw [hc.2.1]; exact hd0)) ?_
    rintro v post ⟨_, _, _, _, _, _, pm, rfl⟩
    refine ⟨hp, ?_, rfl, ?_, ?_⟩
    · rw [pm, updW_ne _ _ _ _ (by bv_omega)]; exact hT'm
    · rw [hhp']; exact hA.2.2.2.2.2.2.1
    · intro i hi
      unfold memW
      rw [pm]
      simpa only [memW, T', T, X, S2, S1, setVarHOLFinite,
        show l + 0 = l by bv_omega, ← hnc] using hprefix i hi
  · refine Ret.seq_skip ?_
    refine Ret.mono (lst_push_tail S2 l 8 n arr0 hS2l hS2e hS2n hma hd0) ?_
    rintro v post ⟨_, _, _, _, _, _, pm, rfl⟩
    refine ⟨arr0, ?_, rfl, ha8, ?_⟩
    · rw [pm, updW_ne _ _ _ _ (by bv_omega)]; exact hma
    · intro i hi
      obtain ⟨_, h8, _⟩ := list_array_cell_ne_header arr0 l n.toNat i hi (by omega) hLw hsep
      unfold memW
      rw [pm, updW_ne _ _ _ _ h8]
      rfl

attribute [local irreducible] Ret in
theorem log_append_no_growth_contents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e L lg arr n cap : BitVec 64) (hA : ArenaReady s)
    (he : s.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : s.locals.lookup (ofString "log") = some (.val (.word lg)))
    (hd88 : s.memaddrs (e + 88)) (hmL : s.memory (e + 88) = .word L)
    (hma : s.memory L = .word arr)
    (hmn : s.memory (L + 8) = .word n) (hmc : s.memory (L + 16) = .word cap)
    (hd0 : s.memaddrs L) (hd8 : s.memaddrs (L + 8)) (hd16 : s.memaddrs (L + 16))
    (hlt : n.toNat < cap.toNat) (hcap : n.toNat < 2 ^ 59)
    (hw : arr.toNat + 8 * cap.toNat ≤ 2 ^ 64) (hLw : L.toNat + 24 ≤ 2 ^ 64)
    (hsep : L.toNat + 24 ≤ arr.toNat ∨ arr.toNat + 8 * cap.toNat ≤ L.toNat) :
    Ret s (sourceFnBody Guest.Software.guestFn_log_append)
      (fun _ post =>
        (∀ i, i < n.toNat → memW post (arr.toNat + 8 * i) = memW s (arr.toNat + 8 * i)) ∧
        memW post (arr.toNat + 8 * n.toNat) = lg.toNat) := by
  have hb : sourceFnBody Guest.Software.guestFn_log_append =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_log_append).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_log_append,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.decCallL (by intro v t M h; exact h) fun vals body cal ret v post h1 h2 h3 => ?_
  have hv : vals = [.val (.word L), .val (.word 8)] := by
    obtain ⟨v1, v2, rfl, he1, he2⟩ := evalList2_inv _ _ _ h1
    have e1 := he1.symm.trans (ev_load_loc_eq s _ e _ L he hd88 hmL)
    have e2 := he2.symm.trans (ev_const s _)
    rw [Option.some.inj e1, Option.some.inj e2]; rfl
  obtain ⟨rfl, rfl⟩ := lk2 hA.1.code (by decide) fl_lookup_lst_push L 8 hv h2
  have hAE : ArenaReady (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "l", .val (.word L))).update
        (ofString "esz", .val (.word 8)))) :=
    ⟨guestInv_callEntry _ _ hA.1, arenaOK_congr (s := s) rfl hA.2⟩
  obtain ⟨hp, _, hprefix⟩ := Ret.apply
    (lst_push_run_no_growth_contents (callEntryStateHOLFinite s _) L arr n cap hAE
      (by simp (config := {decide := true}) [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hma hmn hmc hd0 hd8 hd16 hlt hcap hw hLw hsep) h3
  obtain ⟨_, _, _, _, _, _, _, _, arr', d, len, _, hv, _, halt, _⟩ := hp
  have harr : arr' = arr := by
    rcases halt with ⟨_, _, _, hm, _⟩ | ⟨hnc, _⟩
    · simpa using hm.symm.trans hma
    · have := congrArg BitVec.toNat hnc; omega
  subst arr'
  subst v
  let X := setVarHOLFinite (ofString "slot") (.val (.word (arr + n * 8)))
    { post with locals := s.locals }
  have hXs : X.locals.lookup (ofString "slot") = some (.val (.word (arr + n * 8))) := setVar_lookup_eq _ _ _
  have hXlg : X.locals.lookup (ofString "log") = some (.val (.word lg)) := by
    simp (config := {decide := true}) [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlg]
  show Ret X _ _
  refine Ret.seq_storeWv (arr + n * 8) (by rw [ev_loc]; exact hXs)
    (fun v hv => ⟨lg, by rw [ev_loc, hXlg] at hv; exact (Option.some.inj hv).symm⟩) fun w hw' _ => ?_
  have hwl : w = lg := by rw [ev_loc, hXlg] at hw'; simpa using hw'.symm
  subst w
  refine Ret.ret fun _ _ => ?_
  exact log_append_store_contents X arr n lg (fun i => memW s (arr.toNat + 8 * i))
    (by omega) hprefix

attribute [local irreducible] Ret in
/-- Exact log contents after append, uniformly through in-place and copying growth. -/
theorem log_append_run_contents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e L lg arr0 n cap : BitVec 64) (hA : ArenaReady s)
    (he : s.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : s.locals.lookup (ofString "log") = some (.val (.word lg)))
    (hd88 : s.memaddrs (e + 88)) (hmL : s.memory (e + 88) = .word L)
    (hma : s.memory L = .word arr0)
    (hmn : s.memory (L + 8) = .word n) (hmc : s.memory (L + 16) = .word cap)
    (hd0 : s.memaddrs L) (hd8 : s.memaddrs (L + 8)) (hd16 : s.memaddrs (L + 16))
    (hle : n.toNat ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 59)
    (ha8 : arr0.toNat % 8 = 0)
    (hw : arr0.toNat + 8 * cap.toNat ≤ 2 ^ 64)
    (hold : arr0.toNat + 8 * n.toNat ≤ globN s "heap_ptr" ∨
      (heapLimit ≤ arr0.toNat ∧ arr0.toNat + 8 * n.toNat < 2 ^ 64))
    (hLw : L.toNat + 24 ≤ 2 ^ 64)
    (hsep : L.toNat + 24 ≤ arr0.toNat ∨ arr0.toNat + 8 * cap.toNat ≤ L.toNat)
    (hLh : L.toNat + 24 ≤ globN s "heap_ptr" ∨ heapLimit ≤ L.toNat)
    (hc1 : 1 ≤ cap.toNat) :
    Ret s (sourceFnBody Guest.Software.guestFn_log_append)
      (fun _ post => ∃ arr : BitVec 64, post.memory L = .word arr ∧ arr.toNat % 8 = 0 ∧
        (∀ i, i < n.toNat →
          memW post (arr.toNat + 8 * i) = memW s (arr0.toNat + 8 * i)) ∧
        memW post (arr.toNat + 8 * n.toNat) = lg.toNat) := by
  have hb : sourceFnBody Guest.Software.guestFn_log_append =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_log_append).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_log_append,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.decCallL (by intro v t M h; exact h) fun vals body cal ret v post h1 h2 h3 => ?_
  have hv : vals = [.val (.word L), .val (.word 8)] := by
    obtain ⟨v1, v2, rfl, he1, he2⟩ := evalList2_inv _ _ _ h1
    have e1 := he1.symm.trans (ev_load_loc_eq s _ e _ L he hd88 hmL)
    have e2 := he2.symm.trans (ev_const s _)
    rw [Option.some.inj e1, Option.some.inj e2]; rfl
  obtain ⟨rfl, rfl⟩ := lk2 hA.1.code (by decide) fl_lookup_lst_push L 8 hv h2
  have hAE : ArenaReady (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "l", .val (.word L))).update
        (ofString "esz", .val (.word 8)))) :=
    ⟨guestInv_callEntry _ _ hA.1, arenaOK_congr (s := s) rfl hA.2⟩
  have hp := Ret.apply
    (lst_push_run (callEntryStateHOLFinite s _) L 8 n cap hAE
      (by simp (config := {decide := true}) [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hmn hmc hd0 hd8 hd16 hle (by omega) (by decide)) h3
  obtain ⟨arr, pmL, hv, halign, hprefix⟩ := Ret.apply
    (lst_push_run_contents (callEntryStateHOLFinite s _) L arr0 n cap hAE
      (by simp (config := {decide := true}) [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hma hmn hmc hd0 hle (by omega) ha8
      (by
        rcases hold with hold | hold
        · have hh := hA.2.2.1; change globN s "heap_ptr" ≤ 2952790016 at hh; omega
        · exact hold.2)
      (hold.imp id And.left) hLw (by rcases hsep with h | h <;> [left; right] <;> omega) hLh) h3
  obtain ⟨_, _, _, _, _, _, _, pA, arr', d, len, pmL', _, _, halt, _⟩ := hp
  have harr : arr' = arr := by have h := pmL'.symm.trans pmL; cases h; rfl
  subst arr'
  have hbound : arr.toNat + 8 * n.toNat < 2 ^ 64 := by
    rcases halt with ⟨hlt, _, _, hm, _⟩ | ⟨rfl, had, _, _, hg, _⟩
    · have ha : arr = arr0 := by have h := hm.symm.trans hma; cases h; rfl
      subst arr; omega
    · have hh := pA.2.2.1
      change globN post "heap_ptr" ≤ 2952790016 at hh
      change d.toNat + 2 * (8 * n.toNat) ≤ globN post "heap_ptr" at hg
      rw [had]
      omega
  have hslot : arr + n * 8 ≠ L := by
    intro h
    have hn := congrArg BitVec.toNat h
    rw [log_slot_toNat arr n hbound] at hn
    rcases halt with ⟨_, _, _, hm, _⟩ | ⟨_, had, _, hg, hb, _⟩
    · have ha : arr = arr0 := by have h := hm.symm.trans hma; cases h; rfl
      subst arr; rcases hsep with h | h <;> omega
    · have hh := pA.2.2.1
      change globN post "heap_ptr" ≤ 2952790016 at hh
      have hg' : globN s "heap_ptr" ≤ d.toNat := hg
      have hb' : d.toNat + 2 * (8 * cap.toNat) ≤ globN post "heap_ptr" := hb
      subst d
      rcases hLh with h | h
      · omega
      · change 2952790016 ≤ L.toNat at h; omega
  subst v
  let X := setVarHOLFinite (ofString "slot") (.val (.word (arr + n * 8)))
    { post with locals := s.locals }
  have hXs : X.locals.lookup (ofString "slot") = some (.val (.word (arr + n * 8))) := setVar_lookup_eq _ _ _
  have hXlg : X.locals.lookup (ofString "log") = some (.val (.word lg)) := by
    simp (config := {decide := true}) [X, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlg]
  show Ret X _ _
  refine Ret.seq_storeWv (arr + n * 8) (by rw [ev_loc]; exact hXs)
    (fun v hv => ⟨lg, by rw [ev_loc, hXlg] at hv; exact (Option.some.inj hv).symm⟩) fun w hw' _ => ?_
  have hwl : w = lg := by rw [ev_loc, hXlg] at hw'; simpa using hw'.symm
  subst w
  refine Ret.ret fun _ _ => ⟨arr, ?_, halign, ?_⟩
  · change updW X.memory (arr + n * 8) lg L = _
    rw [updW_ne _ _ _ _ (Ne.symm hslot)]; exact pmL
  · exact log_append_store_contents X arr n lg (fun i => memW s (arr0.toNat + 8 * i))
      hbound hprefix

/-- Contents component of the child-log loop invariant.  It follows the current
array through reallocations while indexing both segments in the entry state. -/
def LAContents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L arr0 n0 : BitVec 64) (child : Nat → Nat) (i : Nat)
    (u : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ arr : BitVec 64, u.memory L = .word arr ∧ arr.toNat % 8 = 0 ∧
    (∀ k, k < n0.toNat → memW u (arr.toNat + 8 * k) = memW s (arr0.toNat + 8 * k)) ∧
    ∀ k, k < i → memW u (arr.toNat + 8 * (n0.toNat + k)) = child k

theorem laContents_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L arr0 n0 : BitVec 64) (child : Nat → Nat)
    (hm : s.memory L = .word arr0) (ha8 : arr0.toNat % 8 = 0) :
    LAContents s L arr0 n0 child 0 s := by
  exact ⟨arr0, hm, ha8, fun _ _ => rfl, fun _ h => by omega⟩

theorem laContents_locals {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {L arr0 n0 : BitVec 64} {child : Nat → Nat} {i : Nat}
    (h : LAContents s L arr0 n0 child i u) (M : HolFiniteMapExact MlS (ValueHOL 64)) :
    LAContents s L arr0 n0 child i { u with locals := M } := h

/-- A uniform append extends the contents invariant by exactly one child log. -/
theorem laContents_step {F : Type} {s u post : PanSemStateFiniteExact 64 F}
    {L arr0 n0 arr n lg : BitVec 64} {child : Nat → Nat} {i : Nat}
    (h : LAContents s L arr0 n0 child i u)
    (hm : u.memory L = .word arr) (hn : n.toNat = n0.toNat + i)
    (hlg : lg.toNat = child i)
    (hp : ∃ next : BitVec 64, post.memory L = .word next ∧ next.toNat % 8 = 0 ∧
      (∀ k, k < n.toNat →
        memW post (next.toNat + 8 * k) = memW u (arr.toNat + 8 * k)) ∧
      memW post (next.toNat + 8 * n.toNat) = lg.toNat) :
    LAContents s L arr0 n0 child (i + 1) post := by
  obtain ⟨old, hold, _, hprefix, hsuffix⟩ := h
  have heq : old = arr := by have he := hold.symm.trans hm; cases he; rfl
  subst old
  obtain ⟨next, hnext, halign, hkeep, hnew⟩ := hp
  refine ⟨next, hnext, halign, ?_⟩
  apply append_contents_step
    (fun k => memW s (arr0.toNat + 8 * k)) child
    (fun k => memW u (arr.toNat + 8 * k))
    (fun k => memW post (next.toNat + 8 * k)) n0.toNat i hprefix hsuffix
  · intro k hk
    exact hkeep k (by omega)
  · simpa only [hn, hlg] using hnew

/-- Strengthened loop invariant: retain the allocation/frame invariant and the
exact parent prefix and appended child suffix at the local loop index. -/
def LAInvContents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L arr0 cap0 n0 nc : BitVec 64) (child : Nat → Nat)
    (u : PanSemStateFiniteExact 64 F) : Prop :=
  LAInv s L arr0 cap0 n0 nc u ∧
    ∀ i : BitVec 64, u.locals.lookup (ofString "i") = some (.val (.word i)) →
      LAContents s L arr0 n0 child i.toNat u

theorem laInvContents_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L arr0 cap0 n0 nc : BitVec 64) (child : Nat → Nat)
    (h : LAInv s L arr0 cap0 n0 nc s)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word 0)))
    (hm : s.memory L = .word arr0) (ha8 : arr0.toNat % 8 = 0) :
    LAInvContents s L arr0 cap0 n0 nc child s := by
  refine ⟨h, fun i hli => ?_⟩
  have heq : i = 0 := by have he := hli.symm.trans hi; cases he; rfl
  subst i
  exact laContents_init s L arr0 n0 child hm ha8

attribute [local irreducible] Ret in
/-- The contents and footprint results describe the same deterministic append
run, so the loop can consume them jointly without losing either component. -/
theorem log_append_run_contents_step {F : Type} (s u : PanSemStateFiniteExact 64 F)
    (e L lg arr0 arr n0 n cap : BitVec 64) (child : Nat → Nat) (i : Nat)
    (hcontents : LAContents s L arr0 n0 child i u)
    (hn : n.toNat = n0.toNat + i) (hlgChild : lg.toNat = child i)
    (hA : ArenaReady u)
    (he : u.locals.lookup (ofString "e") = some (.val (.word e)))
    (hlg : u.locals.lookup (ofString "log") = some (.val (.word lg)))
    (hd88 : u.memaddrs (e + 88)) (hmL : u.memory (e + 88) = .word L)
    (hma : u.memory L = .word arr)
    (hmn : u.memory (L + 8) = .word n) (hmc : u.memory (L + 16) = .word cap)
    (hd0 : u.memaddrs L) (hd8 : u.memaddrs (L + 8)) (hd16 : u.memaddrs (L + 16))
    (hle : n.toNat ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 59)
    (ha8 : arr.toNat % 8 = 0)
    (hw : arr.toNat + 8 * cap.toNat ≤ 2 ^ 64)
    (hold : arr.toNat + 8 * n.toNat ≤ globN u "heap_ptr" ∨
      (heapLimit ≤ arr.toNat ∧ arr.toNat + 8 * n.toNat < 2 ^ 64))
    (hLw : L.toNat + 24 ≤ 2 ^ 64)
    (hsep : L.toNat + 24 ≤ arr.toNat ∨ arr.toNat + 8 * cap.toNat ≤ L.toNat)
    (hLh : L.toNat + 24 ≤ globN u "heap_ptr" ∨ heapLimit ≤ L.toNat)
    (hc1 : 1 ≤ cap.toNat) :
    Ret u (sourceFnBody Guest.Software.guestFn_log_append)
      (fun _ post => LogAppendPost2 u L arr n cap post ∧
        LAContents s L arr0 n0 child (i + 1) post) := by
  have hframe := log_append_run2 u e L lg arr n cap hA he hlg hd88 hmL
    hma hmn hmc hd0 hd8 hd16 hle hcap hw hLw hsep hLh hc1
  have hcontent := log_append_run_contents u e L lg arr n cap hA he hlg hd88 hmL
    hma hmn hmc hd0 hd8 hd16 hle hcap ha8 hw hold hLw hsep hLh hc1
  unfold Ret at hframe hcontent ⊢
  intro v hr
  exact ⟨hframe v hr, laContents_step hcontents hma hn hlgChild (hcontent v hr)⟩

/-- At normal exit the strengthened invariant contains the complete child
suffix, including when the last iteration reallocated the parent array. -/
theorem laInvContents_exit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {L arr cap n nc : BitVec 64} {child : Nat → Nat}
    (h : LAInvContents s L arr cap n nc child post)
    (hnc : nc.toNat < 2 ^ 63)
    (hexit : evalAt post (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "n"))) = some (.val (.word 0))) :
    LAContents s L arr n child nc.toNat post := by
  obtain ⟨_, _, _, _, _, hn, i, ar, cp, hi, hle, _⟩ := h.1
  have hc := h.2 i hi
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp post .less _ _ 0 hexit
  simp [evalAt, evalHOLExact, hn, hi] at ha hb
  subst ha hb
  have hieq : i.toNat = nc.toNat := by
    by_contra hh
    have hlt : i.toNat < nc.toNat := by omega
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      Flapjack.Compiler.Encoders.Asm.holAsmSignedLess] at hcw
    split at hcw <;> omega
  rwa [hieq] at hc

/-- The loop's exact contents discharge both segments of the appended-list
reconstruction, leaving only allocation, word validity and record preservation. -/
theorem laContents_logsListOK {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {L arr n : BitVec 64} {child nc : Nat}
    (h : LAContents s L arr n
      (fun i => memW s (memW s child + 8 * i)) nc post)
    (hma : memW s L.toNat = arr.toNat)
    (hp : LogsListOK s L.toNat) (hc : LogsListOK s child)
    (hn : memW s (L.toNat + 8) = n.toNat)
    (hnc : memW s (child + 8) = nc)
    (hpn : L.toNat ≠ 0) (hcn : child ≠ 0)
    (hwords : WordsOK post (L.toNat, 24)) (halloc : Allocated post (L.toNat, 24))
    (hcount : memW post (L.toNat + 8) = n.toNat + nc)
    (hbound : n.toNat + nc < 2 ^ 28)
    (hcap : n.toNat + nc ≤ memW post (L.toNat + 16))
    (hslots : ∀ i, i < n.toNat + nc → WordAt post (memW post L.toNat + 8 * i))
    (hkeepP : ∀ i, i < n.toNat →
      LogEntryOK post (memW s (memW s L.toNat + 8 * i)))
    (hkeepC : ∀ i, i < nc →
      LogEntryOK post (memW s (memW s child + 8 * i))) :
    LogsListOK post L.toNat := by
  obtain ⟨next, hm, _, hprefix, hsuffix⟩ := h
  have hnext : memW post L.toNat = next.toNat := by
    simpa only [memW, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      congrArg (fun w => match w with | .word v => v.toNat) hm
  apply logsListOK_of_append_contents hp hc hn hnc hpn hcn hwords halloc
    hcount hbound hcap hslots _ _ hkeepP hkeepC
  · simpa only [hnext, hma] using hprefix
  · simpa only [hnext] using hsuffix

attribute [local irreducible] Ret in
/-- Execute the call and counter increment of one child-log iteration.  The
callee post is transported across both caller-local restoration and assignment. -/
theorem laContents_iteration {F : Type} (s u : PanSemStateFiniteExact 64 F)
    (e L arr0 n0 i : BitVec 64) (child : Nat → Nat) (a2 : ExpHOL 64)
    (hcode : u.code = originalRuntimeCode)
    (he : u.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hi : u.locals.lookup (ofString "i") = some (.val (.word i)))
    (hiw : i.toNat + 1 < 2 ^ 64)
    (ha2 : ∀ v, ev u a2 = some v → ∃ lg : BitVec 64, v = .val (.word lg))
    (hcall : ∀ lg : BitVec 64, ev u a2 = some (.val (.word lg)) →
      Ret (callEntryStateHOLFinite u
        ((HolFiniteMapExact.empty.update (ofString "e", .val (.word e))).update
          (ofString "log", .val (.word lg))))
        (sourceFnBody Guest.Software.guestFn_log_append)
        (fun _ post => LAContents s L arr0 n0 child (i.toNat + 1) post)) :
    Flw u
      (.seq (.call (some (none, none)) (ofString "log_append") [.var .global (ofString "ev"), a2])
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun _ post => ∀ j : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word j)) →
        LAContents s L arr0 n0 child j.toNat post) := by
  refine Flw.seq_call00 fun values body callee ret v cpost h1 h2 h3 => ?_
  obtain ⟨v1, v2, rfl, he1, he2⟩ := evalList2_inv _ _ _ h1
  have hv1 : v1 = .val (.word e) := by
    simp [ev, evalHOLExact, he] at he1
    exact he1.symm
  obtain ⟨lg, hv2⟩ := ha2 v2 he2
  subst v1 v2
  obtain ⟨rfl, rfl⟩ := lk2 hcode (by decide) fl_lookup_log_append e lg rfl h2
  have hcontents := Ret.apply (hcall lg he2) h3
  apply Flw.assign
  intro v hv
  have hvi : v = .val (.word (i + 1)) := by
    rw [ev_addr { cpost with locals := u.locals } (ofString "i") i 1 hi] at hv
    exact (Option.some.inj hv).symm
  subst v
  intro j hj
  have hji : j = i + 1 := by
    rw [setVar_lookup_eq] at hj
    have hh := Option.some.inj hj
    cases hh
    rfl
  subst j
  have hin : (i + 1).toNat = i.toNat + 1 := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hiw
  rw [hin]
  exact laContents_locals hcontents _

/-- Strengthen the executable allocation/frame step with exact log contents.
The contents premise is the append-callee obligation; the original `la_step`
continues to discharge all allocation and memory-footprint obligations. -/
theorem la_step_contents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e L arr0 cap0 n0 nc : BitVec 64) (child : Nat → Nat) (a2 : ExpHOL 64)
    (he : s.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hd88 : s.memaddrs (e + 88)) (hm88 : s.memory (e + 88) = .word L)
    (h88 : ¬ CellHits (e + 88).toNat (arr0.toNat, 8 * cap0.toNat) ∧
      ((e + 88).toNat + 8 ≤ globN s "heap_ptr" ∨ heapLimit ≤ (e + 88).toNat) ∧
      e + 88 ≠ L ∧ e + 88 ≠ L + 8 ∧ e + 88 ≠ L + 16)
    (hd0 : s.memaddrs L) (hd8 : s.memaddrs (L + 8)) (hd16 : s.memaddrs (L + 16))
    (hLw : L.toNat + 24 ≤ 2 ^ 64)
    (hLd : L.toNat + 24 ≤ arr0.toNat ∨ arr0.toNat + 8 * cap0.toNat ≤ L.toNat)
    (hLh : L.toNat + 24 ≤ globN s "heap_ptr" ∨ heapLimit ≤ L.toNat)
    (hsum : n0.toNat + nc.toNat < 2 ^ 58)
    (ha2 : ∀ (t : PanSemStateFiniteExact 64 F) v, ev t a2 = some v → ∃ w, v = .val (.word w))
    (u : PanSemStateFiniteExact 64 F) (hu : LAInvContents s L arr0 cap0 n0 nc child u)
    (hact : InitECandidate.Solver.Wave8M19.LoopActive
      (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) u)
    (hcall : ∀ (i lg : BitVec 64),
      u.locals.lookup (ofString "i") = some (.val (.word i)) →
      ev (decClockHOLFinite u) a2 = some (.val (.word lg)) →
      Ret (callEntryStateHOLFinite (decClockHOLFinite u)
        ((HolFiniteMapExact.empty.update (ofString "e", .val (.word e))).update
          (ofString "log", .val (.word lg))))
        (sourceFnBody Guest.Software.guestFn_log_append)
        (fun _ post => LAContents s L arr0 n0 child (i.toNat + 1) post)) :
    Flw (decClockHOLFinite u)
      (.seq (.call (some (none, none)) (ofString "log_append") [.var .global (ofString "ev"), a2])
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun _ post => LAInvContents s L arr0 cap0 n0 nc child post) := by
  have hframe := la_step s e L arr0 cap0 n0 nc a2 he hd88 hm88 h88
    hd0 hd8 hd16 hLw hLd hLh hsum ha2 u hu.1 hact
  obtain ⟨uc, ud, uA, ug, uh, un, i, arr, cap, ui, hile, rest⟩ := hu.1
  have hilt := la_active u i nc ui un hile (by omega) hact
  have hue : (decClockHOLFinite u).globals.lookup (ofString "ev") = some (.val (.word e)) := by
    change u.globals.lookup _ = _
    rw [ug _ (by decide)]
    exact he
  have hcontents := laContents_iteration s (decClockHOLFinite u) e L arr0 n0 i child a2
    uA.1.code hue ui (by omega) (ha2 (decClockHOLFinite u))
    (fun lg hlg => hcall i lg ui hlg)
  exact Flw.and hframe hcontents

/-- The strengthened invariant is retained by the complete executable loop,
so the success-tail continuation receives both contents and the write frame. -/
theorem la_loop_contents {F : Type} (s u : PanSemStateFiniteExact 64 F)
    (L arr0 cap0 n0 nc : BitVec 64) (child : Nat → Nat) (a2 : ExpHOL 64)
    (cont : ProgHOL 64)
    (Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (hinit : LAInvContents s L arr0 cap0 n0 nc child u)
    (hstep : ∀ t, LAInvContents s L arr0 cap0 n0 nc child t →
      InitECandidate.Solver.Wave8M19.LoopActive
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) t →
      t.clock ≠ 0 →
      Flw (decClockHOLFinite t)
        (.seq (.call (some (none, none)) (ofString "log_append") [.var .global (ofString "ev"), a2])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
        (fun _ post => LAInvContents s L arr0 cap0 n0 nc child post))
    (hk : ∀ t, LAInvContents s L arr0 cap0 n0 nc child t → Ret t cont Φ) :
    Ret u
      (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n")))
        (.seq (.call (some (none, none)) (ofString "log_append") [.var .global (ofString "ev"), a2])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))) cont) Φ := by
  exact Ret.seq_while_inv (LAInvContents s L arr0 cap0 n0 nc child) hinit
    (NoRet.seq NoRet.call0 NoRet.assign) hstep hk

/-- The original-or-fresh array alternative supplies the copy-separation
premise needed by the contents theorem at every iteration. -/
theorem laInv_array_copy_region {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {L arr0 cap0 n0 nc arr n cap : BitVec 64}
    (h : LAInv s L arr0 cap0 n0 nc u)
    (hma : u.memory L = .word arr)
    (hmn : u.memory (L + 8) = .word n)
    (hmc : u.memory (L + 16) = .word cap)
    (hold : arr0.toNat + 8 * cap0.toNat ≤ globN s "heap_ptr" ∨
      (heapLimit ≤ arr0.toNat ∧ arr0.toNat + 8 * cap0.toNat < 2 ^ 64)) :
    arr.toNat + 8 * n.toNat ≤ globN u "heap_ptr" ∨
      (heapLimit ≤ arr.toNat ∧ arr.toNat + 8 * n.toNat < 2 ^ 64) := by
  obtain ⟨_, _, _, _, hh, _, i, ar, cp, _, _, hmar, hmnr, hmcr,
    hle, _, _, _, hregion, _⟩ := h
  have har : ar = arr := by have he := hmar.symm.trans hma; cases he; rfl
  have hcp : cp = cap := by have he := hmcr.symm.trans hmc; cases he; rfl
  have hn : n0 + i = n := by have he := hmnr.symm.trans hmn; cases he; rfl
  subst ar cp
  rw [hn] at hle
  rcases hregion with ⟨rfl, rfl⟩ | ⟨_, hbound⟩
  · rcases hold with hold | ⟨hold, hb⟩
    · left; omega
    · right; exact ⟨hold, by omega⟩
  · left; omega

/-- Recover alignment of the current backing array directly from contents. -/
theorem laContents_array_aligned {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {L arr0 n0 arr : BitVec 64} {child : Nat → Nat} {i : Nat}
    (h : LAContents s L arr0 n0 child i u) (hm : u.memory L = .word arr) :
    arr.toNat % 8 = 0 := by
  obtain ⟨old, hold, ha8, _⟩ := h
  have heq : old = arr := by have he := hold.symm.trans hm; cases he; rfl
  simpa only [heq] using ha8

/-- A child source cell separated from the parent's original array and header
survives every append iteration, whether it lies in old heap or scratch. -/
theorem laInv_source_memW {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {L arr0 cap0 n0 nc : BitVec 64} {a : Nat}
    (h : LAInv s L arr0 cap0 n0 nc u) (hab : a < 2 ^ 64)
    (harr : ¬ CellHits a (arr0.toNat, 8 * cap0.toNat))
    (hregion : a + 8 ≤ globN s "heap_ptr" ∨ heapLimit ≤ a)
    (h0 : BitVec.ofNat 64 a ≠ L) (h8 : BitVec.ofNat 64 a ≠ L + 8)
    (h16 : BitVec.ofNat 64 a ≠ L + 16) : memW u a = memW s a := by
  obtain ⟨_, _, hA, _, hh, _, _, _, _, _, _, _, _, _, _, _, _, _, hfr⟩ := h
  have hheap : globN u "heap_ptr" ≤ 2952790016 := hA.2.2.1
  have hnot : ¬ CellHits a (globN s "heap_ptr", globN u "heap_ptr" - globN s "heap_ptr") := by
    unfold CellHits
    dsimp only
    rcases hregion with hregion | hregion
    · omega
    · change 2952790016 ≤ a at hregion
      omega
  unfold memW
  rw [hfr.2 _ (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using harr)
    (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hab] using hnot) h0 h8 h16]

attribute [local irreducible] Ret in
/-- Discharge the append-callee contents obligation using the active invariant.
Only the source-load identity and the protected `e+88` cell are supplied by the
surrounding success-handler frame; current array bounds come from `LAInv`. -/
theorem laInv_append_callee_contents {F : Type} (s u : PanSemStateFiniteExact 64 F)
    (e L arr0 cap0 n0 nc i lg : BitVec 64) (child : Nat → Nat)
    (h : LAInvContents s L arr0 cap0 n0 nc child u)
    (hi : u.locals.lookup (ofString "i") = some (.val (.word i)))
    (hlg : lg.toNat = child i.toNat)
    (hd88 : s.memaddrs (e + 88)) (hm88 : u.memory (e + 88) = .word L)
    (hd0 : s.memaddrs L) (hd8 : s.memaddrs (L + 8)) (hd16 : s.memaddrs (L + 16))
    (hLw : L.toNat + 24 ≤ 2 ^ 64)
    (hLd : L.toNat + 24 ≤ arr0.toNat ∨ arr0.toNat + 8 * cap0.toNat ≤ L.toNat)
    (hLh : L.toNat + 24 ≤ globN s "heap_ptr" ∨ heapLimit ≤ L.toNat)
    (hold : arr0.toNat + 8 * cap0.toNat ≤ globN s "heap_ptr" ∨
      (heapLimit ≤ arr0.toNat ∧ arr0.toNat + 8 * cap0.toNat < 2 ^ 64))
    (hsum : n0.toNat + nc.toNat < 2 ^ 58) :
    Ret (callEntryStateHOLFinite (decClockHOLFinite u)
      ((HolFiniteMapExact.empty.update (ofString "e", .val (.word e))).update
        (ofString "log", .val (.word lg))))
      (sourceFnBody Guest.Software.guestFn_log_append)
      (fun _ post => LAContents s L arr0 n0 child (i.toNat + 1) post) := by
  obtain ⟨uc, ud, uA, ug, uh, un, j, arr, cap, uj, hjle, hmL, hm8, hm16,
    hle, hcap, hc1, hw, hregion, hfr⟩ := h.1
  have hji : j = i := by have he := uj.symm.trans hi; cases he; rfl
  subst j
  have hcontents := h.2 i hi
  have ha8 := laContents_array_aligned hcontents hmL
  have hcopy := laInv_array_copy_region h.1 hmL hm8 hm16 hold
  have hsep : L.toNat + 24 ≤ arr.toNat ∨ arr.toNat + 8 * cap.toNat ≤ L.toNat := by
    rcases hregion with ⟨rfl, rfl⟩ | ⟨hb, he⟩
    · exact hLd
    · have hheap : globN u "heap_ptr" ≤ 2952790016 := uA.2.2.1
      rcases hLh with hh | hh
      · left; omega
      · right; change 2952790016 ≤ L.toNat at hh; omega
  let E := callEntryStateHOLFinite (decClockHOLFinite u)
    ((HolFiniteMapExact.empty.update (ofString "e", .val (.word e))).update
      (ofString "log", .val (.word lg)))
  have hEA : ArenaReady E :=
    ⟨guestInv_callEntry _ _ (guestInv_congr (s := u) rfl rfl rfl rfl uA.1),
      arenaOK_congr (s := u) rfl uA.2⟩
  have hCE : LAContents s L arr0 n0 child i.toNat E := hcontents
  have hrun := log_append_run_contents_step s E e L lg arr0 arr n0 (n0 + i) cap
    child i.toNat hCE (by rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega))
    hlg hEA
    (by simp (config := {decide := true}) [E, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (by simp [E, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (by change u.memaddrs _; rw [ud]; exact hd88)
    hm88 hmL hm8 hm16
    (by change u.memaddrs _; rw [ud]; exact hd0)
    (by change u.memaddrs _; rw [ud]; exact hd8)
    (by change u.memaddrs _; rw [ud]; exact hd16)
    hle hcap ha8 hw hcopy hLw hsep
    (by change L.toNat + 24 ≤ globN u "heap_ptr" ∨ heapLimit ≤ L.toNat
        rcases hLh with hh | hh
        · left; omega
        · exact Or.inr hh) hc1
  exact Ret.mono hrun (fun _ _ hp => hp.2)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
