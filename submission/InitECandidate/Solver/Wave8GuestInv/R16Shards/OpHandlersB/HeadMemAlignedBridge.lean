import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmGBody
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group04

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
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s))
    (ofString "op_dispatch")

def FrameExceptionSpecA : Prop :=
  FunSpec EvmInvA
    (OnReturn fun s post => EvmInvA post ∧ EvmDone post ∧
      (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
    (ofString "frame_exception")

def FrameEpilogueSpecA : Prop :=
  FunSpec (fun s => EvmInvA s ∧ EvmDone s)
    (OnReturn fun s post => EvmInvA post ∧ EvmDone post ∧
      (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
    (ofString "frame_epilogue")

def FinishChildSpecA : Prop :=
  FunSpec (fun s => EvmInvA s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
    (fun s r post => ((∃ v, r = some (.returned v)) ∨ IsEvmErr r) →
      EvmInvA post ∧ (evmChain post).length + 1 = (evmChain s).length ∧ evmR post ≤ evmR s)
    (ofString "finish_child")

/-- `OpDispatchSpecA` in the `EvmInvA ∧ ¬ EvmDone` shape used by the walk. -/
def OpDispatchSpecW : Prop :=
  FunSpec (fun s => EvmInvA s ∧ ¬ EvmDone s)
    (fun s r post =>
      ((∃ v, r = some (.returned v)) → EvmInvA post ∧ evmPot post < evmPot s) ∧
      (IsEvmErr r → EvmInvA post ∧ (evmChain post).length = (evmChain s).length ∧
        evmR post ≤ evmR s))
    (ofString "op_dispatch")

theorem opDispatchSpecW_of_A (h : OpDispatchSpecA) : OpDispatchSpecW := by
  obtain ⟨ps, body, ret, hl, hrun⟩ := h
  exact ⟨ps, body, ret, hl, fun s hc hP hex hnt => hrun s hc ⟨hP.1.1, hP.1.2, hP.2⟩ hex hnt⟩

/-! ## 3. The `run_frames` walk under `EvmInvA` (port of `EvmGBody.RunFramesProof`) -/

section RunFramesGlueA

variable (p0 R0 L0 F0 : Nat)

/-- Loop-head facts carried through the body: the potential components of the head. -/
def GPreA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInvA t ∧ evmPot t = p0 ∧ evmR t = R0 ∧ (evmChain t).length = L0 ∧ evmFp t = F0

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
  fun t => EvmInvA t ∧ (evmChain t).length = L0 ∧ evmR t ≤ R0 ∧ locN t "done" = 0 ∧
    F0 = 2 * L0 + 1

/-- The done branch, before `frame_epilogue`. -/
def GPdoneA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPreA p0 R0 L0 F0 t ∧ EvmDone t

/-- After `frame_epilogue`. -/
def GPepiA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInvA t ∧ EvmDone t ∧ (evmChain t).length = L0 ∧ evmR t ≤ R0 ∧ 2 * L0 ≤ F0

/-- At the `finish_child` call. -/
def GPfinA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPepiA R0 L0 F0 t ∧ memW t (globN t "cur_cont" + 16) ≠ 0

/-- In the `EvmErr` handler of `finish_child`. -/
def GPh4A : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInvA t ∧ (evmChain t).length + 1 = L0 ∧ evmR t ≤ R0 ∧ 2 * L0 ≤ F0

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
    (hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInvA t → evmR t ≤ R0 →
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
    (hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInvA t → evmR t ≤ R0 →
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
      BHoare (GPreA (evmPot s) (evmR s) (evmChain s).length (evmFp s)) rfBody (GQA (evmPot s)) := by
  intro F s
  set p0 := evmPot s
  set R0 := evmR s
  set L0 := (evmChain s).length
  set F0 := evmFp s
  have hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInvA t → evmR t ≤ R0 →
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
  have hR : evmR s ≤ Wave8GuestInv.maxChain * (2 * (2 ^ 64 - 1)) :=
    (rf_sum_pair_le s (evmChain s)).trans (Nat.mul_le_mul_right _ hlen)
  have hcap : evmR s ≤ 2 * Wave8GuestInv.maxChain * 2 ^ 64 := by
    have : 2 * (2 ^ 64 - 1) ≤ 2 * 2 ^ 64 := by omega
    calc evmR s ≤ Wave8GuestInv.maxChain * (2 * (2 ^ 64 - 1)) := hR
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
      have hpre : GPreA (evmPot s) (evmR s) (evmChain s).length (evmFp s) (decClockHOLFinite s) := by
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
