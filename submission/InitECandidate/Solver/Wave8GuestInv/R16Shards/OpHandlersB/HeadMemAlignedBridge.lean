import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmGBody
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group04
import InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue

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
