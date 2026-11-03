import InitECandidate.Solver.Wave8GuestInv.Primitives
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.Common
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_scratch_alloc
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M28.ww_memzero
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P02
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_InitProofs
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves

/-! Zero-sorry proofs of `ww__resolve_step` and `sp__resolve_step` (`ContractParts/C08.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.nameCheck false
set_option linter.unnecessarySeqFocus false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.ResolveDecodeStep

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Contracts.M26
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-- Composable `ArenaReady` write-frame invariant allowing both heap growth `[hp0, heapLimit)`
and free-scratch growth `[fp0, sp0)` while keeping `frame_mem_ptr = fp0` and all globals outside
`["heap_ptr", "scratch_ptr"]` fixed. -/
def StepFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady s ∧
  globN s0 "heap_ptr" ≤ globN s "heap_ptr" ∧
  globN s "frame_mem_ptr" = globN s0 "frame_mem_ptr" ∧
  globN s "scratch_ptr" ≤ globN s0 "scratch_ptr" ∧
  FrameOutside s0 s
    [(globN s0 "frame_mem_ptr", globN s0 "scratch_ptr" - globN s0 "frame_mem_ptr")]
    (globN s0 "heap_ptr", heapLimit - globN s0 "heap_ptr") ∧
  ∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString →
    s0.globals.lookup k = s.globals.lookup k

theorem stepFrame_refl {F : Type} {s : PanSemStateFiniteExact 64 F} (hA : ArenaReady s) :
    StepFrame s s :=
  ⟨hA, le_rfl, rfl, le_rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem stepFrame_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (h : StepFrame s0 s) (L : HolFiniteMapExact MlS (ValueHOL 64)) (c : Nat) :
    StepFrame s0 { s with locals := L, clock := c } :=
  ⟨localsFree_arenaReady s L c h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem stepFrame_trans {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    (h1 : StepFrame a b) (h2 : StepFrame b c) : StepFrame a c := by
  refine ⟨h2.1, Nat.le_trans h1.2.1 h2.2.1, h2.2.2.1.trans h1.2.2.1,
    Nat.le_trans h2.2.2.2.1 h1.2.2.2.1, ?_, ?_⟩
  · intro x hkeep hfresh
    have hkb : ∀ i ∈ [(globN b "frame_mem_ptr", globN b "scratch_ptr" - globN b "frame_mem_ptr")],
        ¬ CellHits x.toNat i := by
      intro i hi hch; simp only [List.mem_singleton] at hi; subst hi
      apply hkeep (globN a "frame_mem_ptr", globN a "scratch_ptr" - globN a "frame_mem_ptr")
        (List.mem_singleton.mpr rfl)
      unfold CellHits at hch ⊢; have := h1.2.2.1; have := h1.2.2.2.1; omega
    have hfb : ¬ CellHits x.toNat (globN b "heap_ptr", heapLimit - globN b "heap_ptr") := by
      intro hch; apply hfresh; unfold CellHits at hch ⊢
      have := h1.2.1; have := h1.1.2.2.1; omega
    exact (h2.2.2.2.2.1 x hkb hfb).trans (h1.2.2.2.2.1 x hkeep hfresh)
  · intro k hk
    exact (h1.2.2.2.2.2 k hk).trans (h2.2.2.2.2.2 k hk)

theorem stepFrame_to_ww {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : StepFrame s post) :
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    FrameOutside s post
      ([] ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
    ∀ k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString,
      s.globals.lookup k = post.globals.lookup k :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem stepFrame_of_ww_sub {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {gw : List String}
    (hsub : ∀ x ∈ gw, x ∈ ["heap_ptr", "scratch_ptr"])
    (hAR : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hfo : FrameOutside s post
      ([] ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    (hgl : ∀ k ∉ gw.map ofString, s.globals.lookup k = post.globals.lookup k) :
    StepFrame s post := by
  have hfp_not : ofString "frame_mem_ptr" ∉ gw.map ofString := by
    intro hm
    rcases List.mem_map.mp hm with ⟨x, hx, heq⟩
    have hx' := hsub x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl <;> revert heq <;> decide
  have hfp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [← hgl _ hfp_not]
  refine ⟨hAR, hhp, hfp_eq, hsp, hfo, ?_⟩
  intro k hk
  refine hgl k (fun hm => hk ?_)
  rcases List.mem_map.mp hm with ⟨x, hx, rfl⟩
  exact List.mem_map.mpr ⟨x, hsub x hx, rfl⟩

def FlowsOrResumes (r : Option (PanSemResultExact 64)) : Prop :=
  r = none ∨ r = some .break ∨ r = some .continue ∨ Resumes r

def StepFlowProg (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → ArenaReady s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowsOrResumes (evaluateHOLFiniteState s prog).1 →
    StepFrame s (evaluateHOLFiniteState s prog).2

theorem StepFlowProg.skip : StepFlowProg .skip := by
  intro _ s _ hAR _ _; rw [evaluateHOLFiniteState_skip]; exact stepFrame_refl hAR

theorem StepFlowProg.ret (e : ExpHOL 64) : StepFlowProg (.return e) := by
  intro _ s _ hAR _ _
  rw [evaluateHOLFiniteState_return]
  split
  · exact stepFrame_refl hAR
  · split
    · exact stepFrame_locals_clock (stepFrame_refl hAR) _ s.clock
    · exact stepFrame_refl hAR

theorem StepFlowProg.raise (eid : MlS) (e : ExpHOL 64) : StepFlowProg (.raise eid e) := by
  intro _ s _ hAR _ _
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · exact stepFrame_locals_clock (stepFrame_refl hAR) _ s.clock
    · exact stepFrame_refl hAR
  · exact stepFrame_refl hAR

theorem StepFlowProg.assign_local (name : MlS) (e : ExpHOL 64) :
    StepFlowProg (.assign .local name e) := by
  intro _ s _ hAR _ _
  rw [evaluateHOLFiniteState_assign]
  split
  · exact stepFrame_refl hAR
  · split
    · exact stepFrame_locals_clock (stepFrame_refl hAR) _ s.clock
    · exact stepFrame_refl hAR

theorem StepFlowProg.seq {a b : ProgHOL 64}
    (ha : StepFlowProg a) (hb : StepFlowProg b) :
    StepFlowProg (.seq a b) := by
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s a with ⟨r1, mid⟩
  simp only [hr1] at hnt hfr ⊢
  cases r1 with
  | none =>
    have h1 := ha s hc hAR (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at h1; dsimp only at h1 hnt hfr ⊢
    exact stepFrame_trans h1 (hb mid h1.1.1.code h1.1 hnt hfr)
  | some _ =>
    have h1 := ha s hc hAR (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at h1; exact h1

theorem StepFlowProg.ite (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (hy : StepFlowProg yes) (hn : StepFlowProg no) :
    StepFlowProg (.ite cond yes no) := by
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · split at hnt
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hn s hc hAR hnt hfr
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hy s hc hAR hnt hfr
  · exact stepFrame_refl hAR

theorem StepFlowProg.dec (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64)
    {body : ProgHOL 64} (hb : StepFlowProg body) :
    StepFlowProg (.dec name sh init body) := by
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · exact stepFrame_refl hAR
  · rename_i v _
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
      have hAR' : ArenaReady (setVarHOLFinite name v s) :=
        ⟨guestInv_setVar name v s hAR.1, hAR.2⟩
      have hpre : StepFrame s (setVarHOLFinite name v s) :=
        stepFrame_locals_clock (stepFrame_refl hAR) _ s.clock
      exact stepFrame_locals_clock (stepFrame_trans hpre (hb _ hc hAR' hnt hfr)) _ _
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte]; exact stepFrame_refl hAR

theorem StepFlowProg.while_loop (cond : ExpHOL 64) {body : ProgHOL 64}
    (hbody : StepFlowProg body) :
    StepFlowProg (.while cond body) := by
  intro F s hc hAR hnt hfr
  generalize hk : s.clock = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    subst hk
    rw [evaluateHOLFiniteState_while_total] at hnt hfr ⊢
    revert hnt hfr
    split <;> intro hnt hfr
    · rename_i w _
      by_cases hnz : w = 0
      · subst hnz; simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact stepFrame_refl hAR
      · rw [if_pos hnz] at hnt hfr ⊢
        by_cases hclk : s.clock = 0
        · rw [if_pos hclk] at hnt; simp at hnt
        · rw [if_neg hclk] at hnt hfr ⊢
          dsimp only at hnt hfr ⊢
          rw [fixClockHOLFinite_evaluateState] at hnt hfr ⊢
          have hARd : ArenaReady (decClockHOLFinite s) :=
            localsFree_arenaReady s s.locals (s.clock - 1) hAR
          have hdecF : StepFrame s (decClockHOLFinite s) :=
            stepFrame_locals_clock (stepFrame_refl hAR) _ _
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          simp only [hrun] at hrem hnt hfr ⊢
          change mid.clock ≤ s.clock - 1 at hrem
          have hlt : mid.clock < s.clock := by omega
          cases r1 with
          | none =>
            have hb1 := hbody (decClockHOLFinite s) hc hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl rfl)
            rw [hrun] at hb1; dsimp only at hb1
            exact stepFrame_trans (stepFrame_trans hdecF hb1)
              (ih mid.clock hlt mid hb1.1.1.code hb1.1 hnt hfr rfl)
          | some res =>
            cases res with
            | «continue» =>
              have hb1 := hbody (decClockHOLFinite s) hc hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hrun] at hb1; dsimp only at hb1
              exact stepFrame_trans (stepFrame_trans hdecF hb1)
                (ih mid.clock hlt mid hb1.1.1.code hb1.1 hnt hfr rfl)
            | «break» =>
              have hb1 := hbody (decClockHOLFinite s) hc hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inl rfl))
              rw [hrun] at hb1; exact stepFrame_trans hdecF hb1
            | timeOut => simp at hnt
            | returned v =>
              have hb1 := hbody (decClockHOLFinite s) hc hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hrun] at hb1; exact stepFrame_trans hdecF hb1
            | exception e v =>
              have hres : Resumes (some (.exception e v)) := by
                rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
              have hb1 := hbody (decClockHOLFinite s) hc hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr hres)))
              rw [hrun] at hb1; exact stepFrame_trans hdecF hb1
            | error =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
            | finalFfi _ =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
    · exact stepFrame_refl hAR

theorem stepFrame_of_ro {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s) (heq : post = { s with locals := post.locals, clock := post.clock }) :
    StepFrame s post := by
  rw [heq]; exact stepFrame_locals_clock (stepFrame_refl hAR) _ _

theorem StepFlowProg.call0_ro {fname : MlS} (hf : ReadOnlyFn fname) (args : List (ExpHOL 64)) :
    StepFlowProg (.call (some (none, none)) fname args) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact stepFrame_refl hAR
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact stepFrame_refl hAR
    · simp only [hl] at hnt hfr ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        let entry := callEntryStateHOLFinite s callee
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', entry.locals, ret') := ⟨vals, by simpa [hc, entry, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hfr ⊢
            split
            · have hro := hspec entry hc (guestInv_callEntry s callee hAR.1) hex
                (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              dsimp only [entry] at hro; rw [hrun] at hro; dsimp only at hro
              have hp : post = { s with locals := post.locals, clock := post.clock } := by
                rw [hro]; cases s; rfl
              exact stepFrame_locals_clock (stepFrame_of_ro hAR hp) _ _
            · rename_i hbad; rw [if_neg hbad] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hro := hspec entry hc (guestInv_callEntry s callee hAR.1) hex
              (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact hres)
            dsimp only [entry] at hro; rw [hrun] at hro; dsimp only at hro
            have hp : post = { s with locals := post.locals, clock := post.clock } := by
              rw [hro]; cases s; rfl
            exact stepFrame_locals_clock (stepFrame_of_ro hAR hp) _ _
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

theorem StepFlowProg.decCall_ro {fname : MlS} (hf : ReadOnlyFn fname)
    (name : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : StepFlowProg cont) :
    StepFlowProg (.decCall name sh fname args cont) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_decCall_total] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact stepFrame_refl hAR
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact stepFrame_refl hAR
    · simp only [hl] at hnt hfr ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        try dsimp only at hnt hfr ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt hfr ⊢
        let entry := callEntryStateHOLFinite s callee
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', entry.locals, ret') := ⟨vals, by simpa [hc, entry, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hro := hspec entry hc (guestInv_callEntry s callee hAR.1) hex
                (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              dsimp only [entry] at hro; rw [hrun] at hro; dsimp only at hro
              have hp : post = { s with locals := post.locals, clock := post.clock } := by
                rw [hro]; cases s; rfl
              let cstate := setVarHOLFinite name v { post with locals := s.locals }
              have hcstate : cstate = { s with locals := cstate.locals, clock := post.clock } := by
                dsimp only [cstate, setVarHOLFinite]; rw [hp]
              have hpre : StepFrame s cstate := stepFrame_of_ro hAR hcstate
              exact stepFrame_locals_clock (stepFrame_trans hpre (hcont cstate hpre.1.1.code hpre.1 hnt hfr)) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hro := hspec entry hc (guestInv_callEntry s callee hAR.1) hex
              (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact hres)
            dsimp only [entry] at hro; rw [hrun] at hro; dsimp only at hro
            have hp : post = { s with locals := post.locals, clock := post.clock } := by
              rw [hro]; cases s; rfl
            exact stepFrame_locals_clock (stepFrame_of_ro hAR hp) _ _
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

theorem StepFlowProg.decCall_ww {fname : MlS} {gw : List String}
    (hsub : ∀ x ∈ gw, x ∈ ["heap_ptr", "scratch_ptr"])
    (hf : WritesWithin (fun _ => []) gw fname)
    (name : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : StepFlowProg cont) :
    StepFlowProg (.decCall name sh fname args cont) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_decCall_total] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact stepFrame_refl hAR
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact stepFrame_refl hAR
    · simp only [hl] at hnt hfr ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        try dsimp only at hnt hfr ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt hfr ⊢
        let entry := callEntryStateHOLFinite s callee
        have hARe : ArenaReady entry := localsFree_arenaReady s callee (s.clock - 1) hAR
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', entry.locals, ret') := ⟨vals, by simpa [hc, entry, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
                (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              dsimp only [entry] at hARp hhp hsp hfo hgl
              rw [hrun] at hARp hhp hsp hfo hgl
              have hsf1 : StepFrame entry post := stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl
              have hsf_s : StepFrame s post :=
                stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hAR) _ _) hsf1
              let cstate := setVarHOLFinite name v { post with locals := s.locals }
              have hpre : StepFrame s cstate := stepFrame_locals_clock hsf_s cstate.locals post.clock
              exact stepFrame_locals_clock (stepFrame_trans hpre (hcont cstate hpre.1.1.code hpre.1 hnt hfr)) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
              (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact hres)
            dsimp only [entry] at hARp hhp hsp hfo hgl
            rw [hrun] at hARp hhp hsp hfo hgl
            have hsf1 : StepFrame entry post := stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl
            have hsf_s : StepFrame s post :=
              stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hAR) _ _) hsf1
            exact stepFrame_locals_clock hsf_s _ post.clock
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

theorem StepFlowProg.handledCall_ww {fname : MlS} {gw : List String}
    (hsub : ∀ x ∈ gw, x ∈ ["heap_ptr", "scratch_ptr"])
    (hf : WritesWithin (fun _ => []) gw fname)
    (destVar : MlS) (eid evar : MlS) (hntrap_eid : eid ≠ ofString "TrapErr") {handler : ProgHOL 64}
    (hhand : StepFlowProg handler) (args : List (ExpHOL 64)) :
    StepFlowProg (.call (some (some (.local, destVar), some (eid, evar, handler))) fname args) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hc hAR hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact stepFrame_refl hAR
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact stepFrame_refl hAR
    · simp only [hl] at hnt hfr ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        let entry := callEntryStateHOLFinite s callee
        have hARe : ArenaReady entry := localsFree_arenaReady s callee (s.clock - 1) hAR
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', entry.locals, ret') := ⟨vals, by simpa [hc, entry, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            split
            · try dsimp only at hnt hfr ⊢
              split
              · obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
                  (by dsimp only [entry]; rw [hrun]; simp) (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨v, rfl⟩)
                dsimp only [entry] at hARp hhp hsp hfo hgl
                rw [hrun] at hARp hhp hsp hfo hgl
                have hsf_s : StepFrame s post :=
                  stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hAR) _ _)
                    (stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl)
                exact stepFrame_locals_clock hsf_s _ post.clock
              · rename_i hbad; rw [if_neg hbad] at hfr
                rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
            · rename_i hbad; rw [if_neg hbad] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception exId exVal =>
            dsimp only at hnt hfr ⊢
            by_cases heq : exId = eid
            · subst exId
              rw [if_pos rfl] at hnt hfr ⊢
              have hsf_s : StepFrame s post := by
                obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
                  (by dsimp only [entry]; rw [hrun]; simp)
                  (by dsimp only [entry]; rw [hrun]; exact Or.inr ⟨eid, exVal, rfl, hntrap_eid⟩)
                dsimp only [entry] at hARp hhp hsp hfo hgl
                rw [hrun] at hARp hhp hsp hfo hgl
                exact stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hAR) _ _)
                  (stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl)
              rcases hes : s.eshapes.lookup eid with _ | declSh
              · simp only [hes] at hfr
                rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
              · simp only [hes] at hnt hfr ⊢
                by_cases hsh : (shapeEqHOL (shapeOfHOLExact exVal) declSh &&
                    isValidValueHOLExact s.toExact .local evar exVal) = true
                · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
                  let hstate := setVarHOLFinite evar exVal { post with locals := s.locals }
                  have hpre : StepFrame s hstate := stepFrame_locals_clock hsf_s hstate.locals post.clock
                  exact stepFrame_locals_clock (stepFrame_trans hpre (hhand hstate hpre.1.1.code hpre.1 hnt hfr)) _ _
                · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
                  rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
            · rw [if_neg heq] at hnt hfr ⊢
              have hres : Resumes (some (.exception exId exVal)) := by
                rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
              have hntrap : exId ≠ ofString "TrapErr" := by
                rcases hres with ⟨_, h⟩ | ⟨e', v', h, hnt⟩
                · simp at h
                · injection h with h; injection h with he1 _; exact he1 ▸ hnt
              obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
                (by dsimp only [entry]; rw [hrun]; simp)
                (by dsimp only [entry]; rw [hrun]; exact Or.inr ⟨exId, exVal, rfl, hntrap⟩)
              dsimp only [entry] at hARp hhp hsp hfo hgl
              rw [hrun] at hARp hhp hsp hfo hgl
              have hsf_s : StepFrame s post :=
                stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hAR) _ _)
                  (stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl)
              exact stepFrame_locals_clock hsf_s _ post.clock
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private theorem lookupCode_one_word {fname p1 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 : BitVec 64,
      vals = [.val (.word w1)] ∧
      L.lookup p1 = some (.val (.word w1)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | _⟩
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    exact ⟨w1, rfl, by rw [← hx]; simp⟩
  · simp at hx

private theorem decCall_alloc_resumes_inv {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (szExp : ExpHOL 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hnt : (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [szExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [szExp] cont)).1) :
    ∃ hp sz q : BitVec 64, ∃ mid : PanSemStateFiniteExact 64 F,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) ∧
      hp.toNat = globN s "heap_ptr" ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) szExp = some (.val (.word sz)) ∧
      q = (hp + (sz + 7)) &&& ((0 : BitVec 64) - 8) ∧
      q.toNat = hp.toNat + (sz.toNat + 7) / 8 * 8 ∧
      hp.toNat ≤ q.toNat ∧ q.toNat ≤ heapLimit ∧ q.toNat % 8 = 0 ∧
      mid.code = originalRuntimeCode ∧ ArenaReady mid ∧
      mid.memory = s.memory ∧ mid.be = s.be ∧
      mid.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
      mid.locals = s.locals.update (x, .val (.word hp)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [szExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ := InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.arenaOK_globals s hA
  have hlook : originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
    lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_alloc) rfl
  rw [evaluateHOLFiniteState_decCall_total] at hnt hres ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [szExp] with _ | vals
  · simp only [hargs] at hres; exact absurd hres not_resumes_error
  · simp only [hargs] at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vals with _ | ⟨body', callee, ret'⟩
    · simp only [hl] at hres; exact absurd hres not_resumes_error
    · simp only [hl] at hnt hres ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc") _ _ body'
        _ ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s (ofString "alloc") _ _ _
        _ ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "alloc") vals =
          some (sourceFnBody Guest.Software.guestFn_alloc, callee, .one) := by simpa [hc] using hl
      obtain ⟨sz, rfl, hsz_c⟩ := lookupCode_one_word hlook hl'
      have hsz_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) szExp =
          some (.val (.word sz)) := by
        rw [evalListHOLFinite_eq_toExact] at hargs
        simp only [evalListHOLExact] at hargs
        rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) szExp with _ | v1
        · simp [he] at hargs
        · simp [he] at hargs; subst hargs; rfl
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hres ⊢
        let entry := callEntryStateHOLFinite s callee
        have hal_res : Resumes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
          rcases hr : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, pa⟩
          dsimp only [entry] at hr hnt hres ⊢
          rw [hr] at hnt hres
          dsimp only at hnt hres ⊢
          cases ra with
          | none => exact absurd hres not_resumes_error
          | some r =>
            cases r with
            | returned v => exact Or.inl ⟨v, rfl⟩
            | exception eid ev =>
              dsimp only [fixClockHOLFinite] at hres
              rcases hres with ⟨_, h⟩ | ⟨e', v', h, hne⟩
              · simp at h
              · cases h
                exact Or.inr ⟨eid, ev, Eq.refl _, hne⟩
            | _ => exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp [fixClockHOLFinite] at h
        obtain ⟨hal_ret, hal_post, hnot_cMax⟩ :=
          evaluate_alloc_body_resumes entry hp sz hc hhp hsz_c hal_res
        rcases hr : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, pa⟩
        dsimp only [entry] at hr hal_ret hal_post
        rw [hr] at hal_ret hal_post
        dsimp only at hal_ret hal_post
        subst hal_ret
        simp only [hr, fixClockHOLFinite] at hnt hres ⊢
        have hsh_hp : (shapeEqHOL (shapeOfHOLExact (.val (.word hp))) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word hp))) .one) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_hp] at hnt hres ⊢
        dsimp only at hnt hres ⊢
        let q : BitVec 64 := (hp + (sz + 7)) &&& ((0 : BitVec 64) - 8)
        have hnot_sub : ¬ ((cMax - hp).toNat < sz.toNat) := by
          intro hcmp1
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
          have hr' := hr
          rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hr'; dsimp only at hr'
          have hpev : @evalHOLExact 64 F _ (callEntryStateHOLFinite s callee).toExact
              (fun a => Classical.propDecidable ((callEntryStateHOLFinite s callee).memaddrs a))
              (.var .global (ofString "heap_ptr")) = some (.val (.word hp)) := hhp
          have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word hp))) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [hpev] at hr'; simp only [hsh1, ↓reduceIte] at hr'
          rw [evaluateHOLFiniteState_seq_line780] at hr'
          let ps := setVarHOLFinite (ofString "p") (.val (.word hp)) (callEntryStateHOLFinite s callee)
          have hev_c : @evalHOLExact 64 F _ ps.toExact (fun a => Classical.propDecidable (ps.memaddrs a))
              (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")]) (.var .local (ofString "n"))) =
              some (.val (.word (if (cMax - hp).toNat < sz.toNat then 1 else 0))) := by
            have hpl : ps.locals.lookup (ofString "p") = some (.val (.word hp)) := by
              simp [ps, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hnl : ps.locals.lookup (ofString "n") = some (.val (.word sz)) := by
              simp [ps, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsz_c,
                show ofString "p" ≠ ofString "n" by decide]
            simp only [evalHOLExact, evalListHOLExact, hpl, hnl, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]; rfl
          have hite_tr : evaluateHOLFiniteState ps
              (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")]) (.var .local (ofString "n")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
              evaluateHOLFiniteState ps (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
            rw [evaluateHOLFiniteState_ite, hev_c, if_pos hcmp1]; simp
          rw [hite_tr] at hr'
          have hnr_tr := evaluate_call_trap_with_no_resumes ps 1 hc
          have hnn_tr := evaluate_call_trap_with_no_none ps 1 hc
          rcases htr : evaluateHOLFiniteState ps (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨rt, st⟩
          rw [htr] at hr' hnr_tr hnn_tr
          cases rt with
          | none => exact hnn_tr rfl
          | some r => injection hr' with hr_eq _; rw [hr_eq] at hnr_tr; exact hnr_tr (Or.inl ⟨_, rfl⟩)
        have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
        have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
        obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ :=
          InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.alloc_arith hp sz hhp_hi hhp_al hnot_sub hnot_cMax
        change q.toNat = _ at hq_eq
        let mid := setVarHOLFinite x (.val (.word hp))
          { pa with locals := s.locals,
                    clock := if (callEntryStateHOLFinite s callee).clock < pa.clock
                             then (callEntryStateHOLFinite s callee).clock else pa.clock }
        have hmid_eq : mid =
            { s with locals := s.locals.update (x, .val (.word hp)),
                     globals := s.globals.update (ofString "heap_ptr", .val (.word q)),
                     clock := mid.clock } := by
          dsimp only [mid, setVarHOLFinite]; rw [hal_post]; rfl
        have hmid_AR : ArenaReady mid := by
          rw [hmid_eq]
          refine ⟨⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩, ?_⟩
          unfold ArenaOK
          have h1 : globN { s with locals := s.locals.update (x, .val (.word hp)), globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := mid.clock } "heap_ptr" = q.toNat := by
            simp [globN, HolFiniteMapExact.lookup_update, FUPDATE]
          have h2 : globN { s with locals := s.locals.update (x, .val (.word hp)), globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := mid.clock } "frame_mem_ptr" = globN s "frame_mem_ptr" := by
            simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
          have h3 : globN { s with locals := s.locals.update (x, .val (.word hp)), globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := mid.clock } "scratch_ptr" = globN s "scratch_ptr" := by
            simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
          rw [h1, h2, h3]
          have hsb : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
          exact ⟨by omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1,
            hA.2.2.2.2.2.2.2.1,
            globalsWord_update (s := s) (ofString "heap_ptr") q rfl hA.2.2.2.2.2.2.2.2⟩
        refine ⟨hp, sz, q, mid, hhp, hhp_eq, hsz_ev, rfl, hq_eq, hp_le_q, hq_hi, hq_al,
          by rw [hmid_eq]; exact hc, hmid_AR,
          by rw [hmid_eq], by rw [hmid_eq], by rw [hmid_eq], by rw [hmid_eq],
          hnt, hres, rfl⟩

private theorem lookup_node_new_hashed_r10 :
    originalRuntimeCode.lookup (ofString "node_new_hashed") =
      some ([(ofString "hash", .one)], sourceFnBody Guest.Software.guestFn_node_new_hashed, .one) :=
  lookup_of_guestAst_getElem 255 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_hashed) rfl

private structure PureMemFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) (fresh : Ivl) : Prop where
  code       : s.code = s0.code
  memaddrs   : s.memaddrs = s0.memaddrs
  shMemaddrs : s.shMemaddrs = s0.shMemaddrs
  baseAddr   : s.baseAddr = s0.baseAddr
  globals    : s.globals = s0.globals
  frame      : FrameOutside s0 s [] fresh

private theorem pureMemFrame_refl {F : Type} (s : PanSemStateFiniteExact 64 F) (fresh : Ivl) :
    PureMemFrame s s fresh :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

private theorem pureMemFrame_return {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (fresh : Ivl) :
    PureMemFrame s (evaluateHOLFiniteState s (.return e)).2 fresh := by
  rw [evaluateHOLFiniteState_return]
  split
  · exact pureMemFrame_refl s fresh
  · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

private theorem pureMemFrame_seq_storeW {F : Type} {s : PanSemStateFiniteExact 64 F}
    {d e : ExpHOL 64} {rest : ProgHOL 64} {fresh : Ivl} (addr w : BitVec 64)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) d =
      some (.val (.word addr)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w)))
    (hin : CellHits addr.toNat fresh)
    (hrest : ∀ M, PureMemFrame { s with memory := M }
      (evaluateHOLFiniteState { s with memory := M } rest).2 fresh) :
    PureMemFrame s (evaluateHOLFiniteState s (.seq (.store d e) rest)).2 fresh := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store, hd, he]; dsimp only
  rcases hm : @panMemStoresHOL 64 _ addr (flattenHOL (.val (.word w))) s.memaddrs
      (fun x => Classical.propDecidable (s.memaddrs x)) s.memory with _ | mem'
  · exact pureMemFrame_refl s fresh
  · obtain ⟨_, rfl⟩ := stores_word _ hm
    dsimp only
    have hr := hrest (updW s.memory addr w)
    refine ⟨hr.code, hr.memaddrs, hr.shMemaddrs, hr.baseAddr, hr.globals, ?_⟩
    intro a hkeep hfresh
    rw [hr.frame a hkeep hfresh]
    have hne : a ≠ addr := by rintro rfl; exact hfresh hin
    simp [updW, hne]

theorem ww_node_new_hashed_aux :
    WritesWithin (fun _ => []) ["heap_ptr"] (ofString "node_new_hashed") := by
  refine ⟨_, _, _, lookup_node_new_hashed_r10, ?_⟩
  intro F s hc hAR hlookup hnt hres
  obtain ⟨vals, hvals⟩ := hlookup
  obtain ⟨wh, _, hwh_s⟩ := lookupCode_one_word lookup_node_new_hashed_r10 hvals
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_hashed =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 32#64]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0#64]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16#64]) (.const 0#64))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24#64]) (.var .local (ofString "hash")))
                (.return (.var .local (ofString "nd"))))))) := rfl
  rw [hbody] at hnt hres ⊢
  obtain ⟨hp, sz, q, mid, _, hhp_eq, hsz_ev, _, hq_eq, hp_le_q, hq_hi, _,
      _, hmid_AR, hmid_mem, _, hmid_glob, hmid_loc, _, _, hpost_eq⟩ :=
    decCall_alloc_resumes_inv s (ofString "nd") _ _ hc hAR hnt hres
  have hsz32 : sz = 32#64 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hsz32
  have h32_nat : (32#64).toNat = 32 := rfl
  rw [h32_nat] at hq_eq
  rw [hpost_eq]
  let fresh : Ivl := (globN s "heap_ptr", heapLimit - globN s "heap_ptr")
  have hcell : ∀ off : BitVec 64, off.toNat ≤ 24 → CellHits (hp + off).toNat fresh := by
    intro off hoff
    have hhe : heapLimit < 2 ^ 64 := by decide
    have htn : (hp + off).toNat = hp.toNat + off.toNat := by
      simp only [BitVec.toNat_add]; omega
    unfold CellHits; dsimp only [fresh]; rw [htn, ← hhp_eq]; omega
  have hnd_add : ∀ (t : PanSemStateFiniteExact 64 F) (off : BitVec 64), t.locals = mid.locals →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.op .add [.var .local (ofString "nd"), .const off]) = some (.val (.word (hp + off))) := by
    intro t off htl
    simp [evalHOLExact, evalListHOLExact, htl, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  have hpmf : PureMemFrame mid (evaluateHOLFiniteState mid
      (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0#64]) (.const 0#64))
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8#64]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24#64]) (.var .local (ofString "hash")))
              (.return (.var .local (ofString "nd")))))))).2 fresh := by
    refine pureMemFrame_seq_storeW (hp + 0#64) 0#64 (hnd_add _ _ rfl) rfl (hcell 0#64 (by decide)) fun M1 => ?_
    refine pureMemFrame_seq_storeW (hp + 8#64) 0#64 (hnd_add _ _ rfl) rfl (hcell 8#64 (by decide)) fun M2 => ?_
    refine pureMemFrame_seq_storeW (hp + 16#64) 0#64 (hnd_add _ _ rfl) rfl (hcell 16#64 (by decide)) fun M3 => ?_
    refine pureMemFrame_seq_storeW (hp + 24#64) wh (hnd_add _ _ rfl)
      (by simp [evalHOLExact, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE, hwh_s,
            show ofString "nd" ≠ ofString "hash" by decide])
      (hcell 24#64 (by decide)) fun M4 => ?_
    exact pureMemFrame_return _ _ fresh
  set fin := (evaluateHOLFiniteState mid
      (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0#64]) (.const 0#64))
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8#64]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24#64]) (.var .local (ofString "hash")))
              (.return (.var .local (ofString "nd")))))))).2
  have hfin_AR : ArenaReady { fin with locals := fin.locals.resVarEq (ofString "nd", s.locals.lookup (ofString "nd")) } :=
    localsFree_arenaReady fin _ fin.clock
      ⟨guestInv_congr hpmf.code hpmf.memaddrs hpmf.shMemaddrs hpmf.baseAddr hmid_AR.1,
       arenaOK_congr hpmf.globals hmid_AR.2⟩
  refine ⟨hfin_AR, ?_, ?_, ?_, ?_⟩
  · rw [← hhp_eq]; simp [globN, hpmf.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL]; exact hp_le_q
  · simp [globN, hpmf.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  · intro a _ hfresh
    exact (hpmf.frame a (fun _ h => nomatch h) hfresh).trans (congrFun hmid_mem a)
  · intro k hk
    have hne : k ≠ ofString "heap_ptr" := by simpa using hk
    simp [hpmf.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL, hne, Ne.symm hne]

theorem rt_node_new_hashed_aux :
    Returns ArenaReady (fun s post nd => FreshBlock s post nd 32) (ofString "node_new_hashed") := by
  refine ⟨_, _, _, lookup_node_new_hashed_r10, ?_⟩
  intro F s hc hAR hlookup _hnt v hret
  obtain ⟨vals, hvals⟩ := hlookup
  obtain ⟨wh, _, hwh_s⟩ := lookupCode_one_word lookup_node_new_hashed_r10 hvals
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ := arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_hashed =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 32#64]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0#64]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16#64]) (.const 0#64))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24#64]) (.var .local (ofString "hash")))
                (.return (.var .local (ofString "nd"))))))) := rfl
  have hrun : Ret s (sourceFnBody Guest.Software.guestFn_node_new_hashed)
      (fun val post => ∃ w : BitVec 64, val = .val (.word w) ∧
        ArenaReady post ∧ AllocatorGrows s post ∧ FreshBlock s post w.toNat 32) := by
    rw [hbody]
    apply Ret.of_NS
    refine Ret.ns_alloc hc 32#64 rfl hp hhp ?_
    intro hcmp1 hcmp2
    set q : BitVec 64 := (hp + (32#64 + 7)) &&& ((0 : BitVec 64) - 8)
    set L1 := s.locals.update (ofString "nd", .val (.word hp))
    set G1 := s.globals.update (ofString "heap_ptr", .val (.word q))
    have hnd_ev : ∀ M off, ev (NS s L1 G1 M (s.clock - 1))
        (.op .add [.var .local (ofString "nd"), .const off]) = some (.val (.word (hp + off))) := fun _ _ => by
      simp [ev, evalHOLExact, evalListHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    refine Ret.ns_storeW (hp + 0#64) 0#64 (hnd_ev _ _) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 8#64) 0#64 (hnd_ev _ _) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 16#64) 0#64 (hnd_ev _ _) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 24#64) wh (hnd_ev _ _)
      (by simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE, hwh_s,
            show ofString "nd" ≠ ofString "hash" by decide]) fun _ => ?_
    refine Ret.ns_ret fun val hval => ?_
    have hv : val = .val (.word hp) := by
      simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE] at hval; exact hval.symm
    subst hv
    refine ⟨hp, rfl, ?_⟩
    set M4 := updW (updW (updW (updW s.memory (hp + 0#64) 0#64) (hp + 8#64) 0#64) (hp + 16#64) 0#64) (hp + 24#64) wh
    set post : PanSemStateFiniteExact 64 F :=
      { (NS s (emptyLocalsHOLFinite (NS s L1 G1 M4 (s.clock - 1))).locals G1 M4 (s.clock - 1)) with
        locals := HolFiniteMapExact.resVarEq
          (emptyLocalsHOLFinite (NS s L1 G1 M4 (s.clock - 1))).locals
          (ofString "nd", s.locals.lookup (ofString "nd")) }
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ :=
      InitECandidate.Solver.Wave8GuestInv.R10Shards.P02.alloc_arith hp 32#64 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = _ at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    change q.toNat % 8 = 0 at hq_al
    change hp.toNat ≤ q.toNat at hp_le_q
    have h32 : ((32#64).toNat + 7) / 8 * 8 = 32 := by decide
    rw [h32] at hq_eq
    change ArenaReady post ∧ AllocatorGrows s post ∧ FreshBlock s post hp.toNat 32
    have hpost_hp : globN post "heap_ptr" = q.toNat := by
      simp [post, NS, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      simp [post, NS, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
      simp [post, NS, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hG_post : GuestInv post := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
    have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
    have hlim_le_he : heapLimit ≤ heapEnd := by decide
    have hA_post : ArenaOK post := by
      unfold ArenaOK; rw [hpost_hp, hpost_fp, hpost_sp]
      exact ⟨by omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1,
        hA.2.2.2.2.2.2.2.1,
        globalsWord_update (s := s) (t := post) (ofString "heap_ptr") q rfl hA.2.2.2.2.2.2.2.2⟩
    refine ⟨⟨hG_post, hA_post⟩, ⟨by rw [hpost_hp, ← hhp_eq]; exact hp_le_q, by rw [hpost_sp]⟩,
      hhp_al, ?_, ?_⟩
    · change Inside (hp.toNat, 32) (globN s "heap_ptr") (globN post "heap_ptr")
      rw [← hhp_eq, hpost_hp]; exact ⟨le_rfl, le_of_eq hq_eq.symm⟩
    · change WordsOK post (hp.toNat, 32)
      exact wordsOK_of_guestInv post hG_post hp.toNat 32 hhp_al (by decide) hsb_le (by omega)
  exact hrun v hret

theorem «ww__resolve_step» :
    WritesWithin (fun _ => [])
    ["heap_ptr", "scratch_ptr"] (ofString "_resolve_step") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 260 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__resolve_step) rfl, ?_⟩
  intro F s hc hAR _ hnt hres
  have hsub_sp : ∀ x ∈ (["scratch_ptr"] : List String), x ∈ ["heap_ptr", "scratch_ptr"] := by
    intro x hx; simp at hx; subst hx; simp
  have hsub_hp : ∀ x ∈ (["heap_ptr"] : List String), x ∈ ["heap_ptr", "scratch_ptr"] := by
    intro x hx; simp at hx; subst hx; simp
  have hf : StepFlowProg
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn__resolve_step).body) := by
    dsimp only [Guest.Software.guestFn__resolve_step, extractFn,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, Option.map]
    exact StepFlowProg.dec _ _ _
      (StepFlowProg.dec _ _ _
        (StepFlowProg.seq
          (StepFlowProg.handledCall_ww hsub_sp R10Shards.P02.ww_rlp_item _ _ _ (by decide)
            (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _) _)
          (StepFlowProg.seq
            (StepFlowProg.ite _
              (StepFlowProg.seq
                (StepFlowProg.ite _ (StepFlowProg.ret _) StepFlowProg.skip)
                (StepFlowProg.seq
                  (StepFlowProg.ite _ (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _) StepFlowProg.skip)
                  (StepFlowProg.decCall_ro R11Adapters.ReadOnlyLeaves.«ro_nodedb_lookup» _ _ _
                    (StepFlowProg.seq
                      (StepFlowProg.ite _
                        (StepFlowProg.decCall_ww hsub_hp ww_node_new_hashed_aux _ _ _
                          (StepFlowProg.ret _))
                        StepFlowProg.skip)
                      (StepFlowProg.ret _)))))
              StepFlowProg.skip)
            (StepFlowProg.ret _))))
  exact stepFrame_to_ww (hf s hc hAR hnt (Or.inr (Or.inr (Or.inr hres))))

private theorem shape_comb4_words {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true) :
    ∃ a b c d : BitVec 64,
      v = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] := by
  rcases v with _ | fs | _ <;> simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  rcases f0 with ⟨⟨i0⟩⟩ | _ | _ <;>
    rcases f1 with ⟨⟨i1⟩⟩ | _ | _ <;>
    rcases f2 with ⟨⟨i2⟩⟩ | _ | _ <;>
    rcases f3 with ⟨⟨i3⟩⟩ | _ | _ <;>
    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  exact ⟨i0, i1, i2, i3, rfl⟩

private theorem shape_comb3_words {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one]) = true) :
    ∃ a b c : BitVec 64,
      v = .rStruct [.val (.word a), .val (.word b), .val (.word c)] := by
  rcases v with _ | fs | _ <;> simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | _⟩⟩⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  rcases f0 with ⟨⟨i0⟩⟩ | _ | _ <;>
    rcases f1 with ⟨⟨i1⟩⟩ | _ | _ <;>
    rcases f2 with ⟨⟨i2⟩⟩ | _ | _ <;>
    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  exact ⟨i0, i1, i2, rfl⟩

private theorem return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

private theorem call0_mpt_fail_ne_none_ne_ret {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (cExp : ExpHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_fail") [cExp])).1 ≠ none ∧
    ∀ u, (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_fail") [cExp])).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · rename_i b_mf c_mf r_mf hl_mf
      have hlook_mf : originalRuntimeCode.lookup (ofString "mpt_fail") =
          some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
        lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_mpt_fail) rfl
      have hb_mf := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ b_mf _ r_mf _ c_mf
        (by rw [hc]; exact hlook_mf) hl_mf
      subst hb_mf
      split
      · simp
      · have hbody_mf : sourceFnBody Guest.Software.guestFn_mpt_fail =
            .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0#64)) := rfl
        have hmfn : (evaluateHOLFiniteState (callEntryStateHOLFinite s c_mf)
            (sourceFnBody Guest.Software.guestFn_mpt_fail)).1 ≠ none := by
          rw [hbody_mf, evaluateHOLFiniteState_seq_line780]
          rcases evaluateHOLFiniteState _ (.raise _ _) with ⟨rm, tm⟩
          cases rm with
          | some _ => simp
          | none => dsimp only; exact return_ne_none tm _
        have hmfr : ∀ w, (evaluateHOLFiniteState (callEntryStateHOLFinite s c_mf)
            (sourceFnBody Guest.Software.guestFn_mpt_fail)).1 ≠ some (.returned w) := by
          intro w
          rw [hbody_mf, evaluateHOLFiniteState_seq_line780]
          rcases hr1 : evaluateHOLFiniteState _ (.raise _ _) with ⟨rm, tm⟩
          cases rm with
          | some rm' =>
            dsimp only
            intro hret_w
            rw [evaluateHOLFiniteState_raise] at hr1
            split at hr1
            · dsimp only at hr1
              split at hr1
              · injection hr1 with hr1' _; injection hr1' with hr1''; subst hr1''; simp at hret_w
              · injection hr1 with hr1' _; injection hr1' with hr1''; subst hr1''; simp at hret_w
            · injection hr1 with hr1' _; injection hr1' with hr1''; subst hr1''; simp at hret_w
          | none =>
            exfalso
            rw [evaluateHOLFiniteState_raise] at hr1
            split at hr1
            · dsimp only at hr1; split at hr1 <;> simp at hr1
            · simp at hr1
        rcases hr_mf : evaluateHOLFiniteState (callEntryStateHOLFinite s c_mf)
            (sourceFnBody Guest.Software.guestFn_mpt_fail) with ⟨rmf, _⟩
        rw [hr_mf] at hmfn hmfr
        cases rmf with
        | none => exact absurd rfl hmfn
        | some rmf' =>
          refine ⟨?_, fun u => ?_⟩
          · cases rmf' with
            | returned rv => exact absurd rfl (hmfr rv)
            | _ => dsimp only; (repeat' split) <;> simp
          · cases rmf' <;> dsimp only <;> (repeat' split) <;> simp

theorem «sp__resolve_step» :
    ResolvesNode (ofString "_resolve_step") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 260 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__resolve_step) rfl, ?_⟩
  intro F s hc hAR hlookup hnt v hret
  obtain ⟨vals, hvals⟩ := hlookup
  have hlook_rs : originalRuntimeCode.lookup (ofString "_resolve_step") =
      some ([(ofString "db", .one), (ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn__resolve_step, .comb [.one, .one, .one, .one]) :=
    lookup_of_guestAst_getElem 260 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn__resolve_step) rfl
  have hthree_words : ∃ wdb wp wn : BitVec 64,
      s.locals.lookup (ofString "db") = some (.val (.word wdb)) ∧
      s.locals.lookup (ofString "p") = some (.val (.word wp)) ∧
      s.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup _ vals _ s.locals _ hvals
    simp only [lookupCodeHOLExact, hlook_rs] at hx
    rcases vals with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩⟩ <;> try (simp at hx)
    rcases v0 with ⟨⟨w0⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;>
      rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, _, hL, _⟩ := hx
    refine ⟨w0, w1, w2, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [show ofString "db" ≠ ofString "p" by decide,
        show ofString "db" ≠ ofString "n" by decide,
        show ofString "p" ≠ ofString "n" by decide,
        show ofString "p" ≠ ofString "db" by decide,
        show ofString "n" ≠ ofString "db" by decide,
        show ofString "n" ≠ ofString "p" by decide])
  obtain ⟨_, wp, wn, _, hwp_s, hwn_s⟩ := hthree_words
  have hcall_noret : ∀ (t : PanSemStateFiniteExact 64 F) f args (u : ValueHOL 64),
      (evaluateHOLFiniteState t (.call (some (none, none)) f args)).1 ≠ some (.returned u) := by
    intro t f args u
    rw [evaluateHOLFiniteState_call]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite t _) _ with ⟨r, _⟩
          rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  have hhandled_noret : ∀ (t : PanSemStateFiniteExact 64 F) dv eid evar f args fargs (u : ValueHOL 64),
      (evaluateHOLFiniteState t (.call (some (some (.local, dv),
        some (eid, evar, .call (some (none, none)) f fargs))) (ofString "rlp_item") args)).1 ≠
        some (.returned u) := by
    intro t dv eid evar f args fargs u
    rw [evaluateHOLFiniteState_call]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite t _) _ with ⟨r, _⟩
          cases r with
          | none => simp
          | some r' =>
            cases r' with
            | exception exId exVal =>
              dsimp only
              split
              · split
                · try dsimp only
                  split
                  · exact hcall_noret _ f fargs u
                  · simp
                · simp
              · simp
            | _ => dsimp only; (repeat' split) <;> simp
  dsimp only [Guest.Software.guestFn__resolve_step, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    List.map, Option.map] at hnt hret ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt hret ⊢; dsimp only at hnt hret ⊢
  have hit_init : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64]) =
      some (.rStruct [.val (.word 0#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]) := rfl
  rw [hit_init] at hnt hret ⊢; dsimp only at hnt hret ⊢
  have hsh_it : shapeEqHOL (.comb [.one, .one, .one, .one])
      (shapeOfHOLExact (.rStruct [.val (.word 0#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)])) = true := by
    simp [shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]
  rw [if_pos hsh_it] at hnt hret ⊢; dsimp only at hnt hret ⊢
  set s1 := setVarHOLFinite (ofString "it")
    (.rStruct [.val (.word 0#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]) s
  rw [evaluateHOLFiniteState_dec_total] at hnt hret ⊢; dsimp only at hnt hret ⊢
  have he_init : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.const 0#64) = some (.val (.word 0#64)) := rfl
  rw [he_init] at hnt hret ⊢; dsimp only at hnt hret ⊢
  have hsh_e : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh_e] at hnt hret ⊢; dsimp only at hnt hret ⊢
  set s2 := setVarHOLFinite (ofString "e") (.val (.word 0#64)) s1
  have hs2_c : s2.code = originalRuntimeCode := hc
  have hs2_AR : ArenaReady s2 := localsFree_arenaReady s s2.locals s.clock hAR
  have hs2_hp : globN s2 "heap_ptr" = globN s "heap_ptr" := rfl
  have hs2_p : s2.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwp_s,
      show ofString "e" ≠ ofString "p" by decide, show ofString "it" ≠ ofString "p" by decide]
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwn_s,
      show ofString "e" ≠ ofString "n" by decide, show ofString "it" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hnt hret ⊢
  set c_rlp := ProgHOL.call (some (some (.local, ofString "it"),
      some (ofString "RlpErr", ofString "e", .call (some (none, none)) (ofString "mpt_fail") [.const 3#64])))
    (ofString "rlp_item") [.var .local (ofString "p"), .var .local (ofString "n")]
  have hsf_rlp : StepFlowProg c_rlp :=
    StepFlowProg.handledCall_ww (by intro x hx; simp at hx; subst hx; simp) R10Shards.P02.ww_rlp_item
      _ _ _ (by decide) (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _) _
  rcases h1 : evaluateHOLFiniteState s2 c_rlp with ⟨r1, s3⟩
  have h1_def : evaluateHOLFiniteState s2
    (.call (some (some (.local, ofString "it"),
      some (ofString "RlpErr", ofString "e", .call (some (none, none)) (ofString "mpt_fail") [.const 3#64])))
      (ofString "rlp_item") [.var .local (ofString "p"), .var .local (ofString "n")]) = (r1, s3) := h1
  simp only [h1, h1_def] at hnt hret ⊢
  cases r1 with
  | some _ => exact absurd hret (by rw [← h1]; exact hhandled_noret s2 _ _ _ _ _ _ v)
  | none =>
    dsimp only at hnt hret ⊢
    have hsf3 := hsf_rlp s2 hs2_c hs2_AR (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    rw [h1] at hsf3; dsimp only at hsf3
    have hs3_pn_it : s3.locals.lookup (ofString "p") = some (.val (.word wp)) ∧
        s3.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
        ∃ i0 i1 i2 i3 : BitVec 64,
          s3.locals.lookup (ofString "it") =
            some (.rStruct [.val (.word i0), .val (.word i1), .val (.word i2), .val (.word i3)]) := by
      have h1' := h1
      dsimp only [c_rlp] at h1'
      rw [evaluateHOLFiniteState_call] at h1'
      have hargs_r : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
          [.var .local (ofString "p"), .var .local (ofString "n")] =
          some [.val (.word wp), .val (.word wn)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hs2_p, hs2_n]
      rw [hargs_r] at h1'; dsimp only at h1'
      rcases hl_r : lookupCodeHOLFinite s2.code.lookup (ofString "rlp_item")
          [.val (.word wp), .val (.word wn)] with _ | ⟨br, cr, rr⟩
      · simp [hl_r] at h1'
      · rw [hl_r] at h1'; dsimp only at h1'
        have hlook_ri : originalRuntimeCode.lookup (ofString "rlp_item") =
            some ([(ofString "p", .one), (ofString "len", .one)],
              sourceFnBody Guest.Software.guestFn_rlp_item, .comb [.one, .one, .one, .one]) :=
          lookup_of_guestAst_getElem 107 (by rw [guestAst_len]; decide)
            (extractFn Guest.Software.guestFn_rlp_item) rfl
        have hbr := lookupCodeHOLFinite_installed_body s2.code.lookup _ _ _ br _ rr _ cr
          (by rw [hs2_c]; exact hlook_ri) hl_r
        subst hbr
        have hrr := lookupCodeHOLFinite_installed_return s2 _ _ _ _ _ rr _ cr
          (by rw [hs2_c]; exact hlook_ri) hl_r
        subst hrr
        split at h1'
        · simp at h1'
        · rcases hrun_r : evaluateHOLFiniteState (callEntryStateHOLFinite s2 cr)
              (sourceFnBody Guest.Software.guestFn_rlp_item) with ⟨rr_res, pr⟩
          rw [hrun_r] at h1'
          cases rr_res with
          | none => simp at h1'
          | some rr_val =>
            cases rr_val with
            | returned rv =>
              dsimp only at h1'
              split at h1'
              · rename_i hsh_rv
                split at h1'
                · injection h1' with _ hs3_eq; subst hs3_eq
                  obtain ⟨i0, i1, i2, i3, rfl⟩ := shape_comb4_words hsh_rv
                  refine ⟨?_, ?_, i0, i1, i2, i3, ?_⟩
                  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_p,
                      show ofString "it" ≠ ofString "p" by decide]
                  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_n,
                      show ofString "it" ≠ ofString "n" by decide]
                  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                · simp at h1'
              · simp at h1'
            | exception exId exVal =>
              dsimp only at h1'
              split at h1'
              · split at h1'
                · split at h1'
                  · have hc_pr : pr.code = originalRuntimeCode :=
                      (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s2 cr)
                        (sourceFnBody Guest.Software.guestFn_rlp_item)).1
                        |>.trans hs2_c |> fun h => by rw [hrun_r] at h; exact h
                    have hnn := (call0_mpt_fail_ne_none_ne_ret
                      (setVarHOLFinite (ofString "e") exVal { pr with locals := s2.locals }) hc_pr (.const 3#64)).1
                    exact absurd (congrArg Prod.fst h1') hnn
                  · simp at h1'
                · simp at h1'
              · simp at h1'
            | _ => simp at h1'
    obtain ⟨hs3_p, hs3_n, i0, i1, i2, i3, hs3_it⟩ := hs3_pn_it
    rw [evaluateHOLFiniteState_seq_line780] at hnt hret ⊢
    have hev_it0 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0#64)) =
        some (.val (.word (if i0 = 0#64 then 1#64 else 0#64))) := by
      simp only [evalHOLExact, evalListHOLExact, hs3_it, Compiler.Encoders.Asm.wordCmpHOL]
      by_cases h : i0 = 0#64 <;> simp [h]
    by_cases hi0 : i0 = 0#64
    · subst hi0
      have hite_it0 : ∀ thn els, evaluateHOLFiniteState s3
          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0#64)) thn els) =
          evaluateHOLFiniteState s3 thn := fun thn els => by
        rw [evaluateHOLFiniteState_ite, hev_it0]; simp
      rw [hite_it0] at hnt hret ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt hret ⊢
      have hev_it2_0 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
          (.cmp .equal (.rfield 2 (.var .local (ofString "it"))) (.const 0#64)) =
          some (.val (.word (if i2 = 0#64 then 1#64 else 0#64))) := by
        simp only [evalHOLExact, evalListHOLExact, hs3_it, Compiler.Encoders.Asm.wordCmpHOL]
        by_cases h : i2 = 0#64 <;> simp [h]
      by_cases hi2_0 : i2 = 0#64
      · subst hi2_0
        have hite_it2_0 : evaluateHOLFiniteState s3
            (.ite (.cmp .equal (.rfield 2 (.var .local (ofString "it"))) (.const 0#64))
              (.return (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64]))
              .skip) =
            evaluateHOLFiniteState s3 (.return (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64])) := by
          rw [evaluateHOLFiniteState_ite, hev_it2_0]; simp
        simp only [hite_it2_0] at hret ⊢
        rcases hret_pair : evaluateHOLFiniteState s3 (.return (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64])) with ⟨rr0, pr0⟩
        simp only [hret_pair] at hret
        rw [evaluateHOLFiniteState_return] at hret_pair
        have hret0 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64]) =
            some (.rStruct [.val (.word 0#64), .val (.word 0#64), .val (.word 0#64), .val (.word 0#64)]) := rfl
        rw [hret0] at hret_pair; dsimp only at hret_pair
        split at hret_pair
        · injection hret_pair with hrr0 _; subst hrr0
          dsimp only at hret
          injection hret with hret'; injection hret' with hv_eq; subst hv_eq
          exact ⟨0#64, 0#64, 0#64, 0#64, rfl, fun _ => Or.inl rfl⟩
        · injection hret_pair with hrr0 _; subst hrr0; simp at hret
      · have hite_it2_0 : evaluateHOLFiniteState s3
            (.ite (.cmp .equal (.rfield 2 (.var .local (ofString "it"))) (.const 0#64))
              (.return (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64]))
              .skip) = (none, s3) := by
          rw [evaluateHOLFiniteState_ite, hev_it2_0, if_neg hi2_0]
          simp [evaluateHOLFiniteState_skip]
        simp only [hite_it2_0] at hnt hret ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt hret ⊢
        have hev_it2_32 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.cmp .notEqual (.rfield 2 (.var .local (ofString "it"))) (.const 32#64)) =
            some (.val (.word (if i2 ≠ 32#64 then 1#64 else 0#64))) := by
          simp only [evalHOLExact, evalListHOLExact, hs3_it, Compiler.Encoders.Asm.wordCmpHOL]
          by_cases h : i2 = 32#64 <;> simp [h]
        by_cases hi2_32 : i2 = 32#64
        · subst hi2_32
          have hite_it2_32 : evaluateHOLFiniteState s3
              (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "it"))) (.const 32#64))
                (.call (some (none, none)) (ofString "mpt_fail") [.const 10#64])
                .skip) = (none, s3) := by
            rw [evaluateHOLFiniteState_ite, hev_it2_32]
            simp [evaluateHOLFiniteState_skip]
          simp only [hite_it2_32] at hnt hret ⊢
          set cont_r := ProgHOL.seq
            (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0#64))
              (.decCall (ofString "hn") .one (ofString "node_new_hashed")
                [.rfield 1 (.var .local (ofString "it"))]
                (.return (.rstruct [.const 0#64, .var .local (ofString "hn"), .const 0#64, .const 0#64])))
              .skip)
            (.return (.rstruct [.const 1#64, .rfield 1 (.var .local (ofString "r")),
              .rfield 2 (.var .local (ofString "r")), .rfield 1 (.var .local (ofString "it"))]))
          set dc_nd := ProgHOL.decCall (ofString "r") (.comb [.one, .one, .one]) (ofString "nodedb_lookup")
            [.var .local (ofString "db"), .rfield 1 (.var .local (ofString "it"))] cont_r
          have hdc_nd_nn : (evaluateHOLFiniteState s3 dc_nd).1 ≠ none := by
            dsimp only [dc_nd]; rw [evaluateHOLFiniteState_decCall_total]
            rcases evalListHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a))
                [.var .local (ofString "db"), .rfield 1 (.var .local (ofString "it"))] with _ | vs_nd
            · simp
            · simp only
              rcases lookupCodeHOLFinite s3.code.lookup (ofString "nodedb_lookup") vs_nd with _ | ⟨bnd, cnd, rnd⟩
              · simp
              · simp only; split
                · simp
                · rcases hr_nd : evaluateHOLFiniteState (callEntryStateHOLFinite s3 cnd) bnd with ⟨rnd_r, _⟩
                  simp only [hr_nd]
                  cases rnd_r with
                  | none => simp
                  | some rndv =>
                    cases rndv with
                    | returned _ =>
                      dsimp only [fixClockHOLFinite]; split
                      · dsimp only [cont_r]; rw [evaluateHOLFiniteState_seq_line780]
                        rcases evaluateHOLFiniteState _ _ with ⟨rc1, tc1⟩
                        cases rc1 with
                        | some _ => simp
                        | none => dsimp only; exact return_ne_none tc1 _
                      · simp
                    | _ => simp [fixClockHOLFinite]
          rcases hdnd : evaluateHOLFiniteState s3 dc_nd with ⟨rdnd, pdnd⟩
          have hdnd_def : evaluateHOLFiniteState s3
            (.decCall (ofString "r") (.comb [.one, .one, .one]) (ofString "nodedb_lookup")
              [.var .local (ofString "db"), .rfield 1 (.var .local (ofString "it"))] cont_r) = (rdnd, pdnd) := hdnd
          simp only [hdnd, hdnd_def] at hnt hret ⊢
          cases rdnd with
          | none => exact absurd (congrArg Prod.fst hdnd) hdc_nd_nn
          | some rdnd_v =>
            dsimp only at hnt hret ⊢
            injection hret with hret_eq; subst hret_eq
            dsimp only [dc_nd] at hdnd
            rw [evaluateHOLFiniteState_decCall_total] at hdnd
            rcases hargs_nd : evalListHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a))
                [.var .local (ofString "db"), .rfield 1 (.var .local (ofString "it"))] with _ | v_nd
            · rw [hargs_nd] at hdnd; simp at hdnd
            · rw [hargs_nd] at hdnd; dsimp only at hdnd
              rcases hl_nd : lookupCodeHOLFinite s3.code.lookup (ofString "nodedb_lookup") v_nd with _ | ⟨b_nd, c_nd, r_nd⟩
              · rw [hl_nd] at hdnd; simp at hdnd
              · rw [hl_nd] at hdnd; dsimp only at hdnd
                obtain ⟨p_nd, b_nd0, r_nd0, hlook_nd, hspec_nd⟩ := R11Adapters.ReadOnlyLeaves.«ro_nodedb_lookup»
                have hb_eq := lookupCodeHOLFinite_installed_body s3.code.lookup _ p_nd b_nd0 b_nd r_nd0 r_nd v_nd c_nd
                  (by rw [hsf3.1.1.code]; exact hlook_nd) hl_nd
                have hr_eq := lookupCodeHOLFinite_installed_return s3 _ p_nd b_nd0 b_nd r_nd0 r_nd v_nd c_nd
                  (by rw [hsf3.1.1.code]; exact hlook_nd) hl_nd
                subst hb_eq
                subst hr_eq
                split at hdnd
                · simp at hdnd
                · rw [fixClockHOLFinite_evaluateState] at hdnd
                  rcases hrun_nd : evaluateHOLFiniteState (callEntryStateHOLFinite s3 c_nd) b_nd with ⟨res_nd, post_nd⟩
                  simp only [hrun_nd] at hdnd
                  cases res_nd with
                  | none => simp at hdnd
                  | some rnd =>
                    cases rnd with
                    | returned v_r =>
                      dsimp only at hdnd
                      by_cases hsh_r : (shapeEqHOL (shapeOfHOLExact v_r) (.comb [.one, .one, .one]) &&
                          shapeEqHOL (shapeOfHOLExact v_r) r_nd) = true
                      · simp only [hsh_r, ↓reduceIte] at hdnd
                        have hsh_r1 : shapeEqHOL (shapeOfHOLExact v_r) (.comb [.one, .one, .one]) = true :=
                          (Bool.and_eq_true _ _).mp hsh_r |>.1
                        obtain ⟨r0, r1w, r2w, rfl⟩ := shape_comb3_words hsh_r1
                        have hro_nd := hspec_nd (callEntryStateHOLFinite s3 c_nd) hsf3.1.1.code
                          (guestInv_callEntry s3 c_nd hsf3.1.1)
                          ⟨v_nd, by simpa [hsf3.1.1.code, callEntryStateHOLFinite] using hl_nd⟩
                          (by rw [hrun_nd]; simp) (by rw [hrun_nd]; exact Or.inl ⟨_, rfl⟩)
                        rw [hrun_nd] at hro_nd; dsimp only at hro_nd
                        set s4 := setVarHOLFinite (ofString "r")
                          (.rStruct [.val (.word r0), .val (.word r1w), .val (.word r2w)])
                          { post_nd with locals := s3.locals }
                        have hs4_eq : s4 = { s3 with locals := s4.locals, clock := post_nd.clock } := by
                          dsimp only [s4, setVarHOLFinite]; rw [hro_nd]; cases s3; rfl
                        have hs4_AR : ArenaReady s4 := by
                          rw [hs4_eq]; exact localsFree_arenaReady s3 s4.locals post_nd.clock hsf3.1
                        have hs4_r : s4.locals.lookup (ofString "r") =
                            some (.rStruct [.val (.word r0), .val (.word r1w), .val (.word r2w)]) := by
                          simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                        have hs4_it : s4.locals.lookup (ofString "it") =
                            some (.rStruct [.val (.word 0#64), .val (.word i1), .val (.word 32#64), .val (.word i3)]) := by
                          simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_it,
                            show ofString "r" ≠ ofString "it" by decide]
                        dsimp only [cont_r] at hdnd
                        rw [evaluateHOLFiniteState_seq_line780] at hdnd
                        have hev_r0 : @evalHOLExact 64 F _ s4.toExact
                            (fun a => Classical.propDecidable (s4.memaddrs a))
                            (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0#64)) =
                            some (.val (.word (if r0 = 0#64 then 1#64 else 0#64))) := by
                          simp only [evalHOLExact, evalListHOLExact, hs4_r, Compiler.Encoders.Asm.wordCmpHOL]
                          by_cases h : r0 = 0#64 <;> simp [h]
                        by_cases hr0_z : r0 = 0#64
                        · subst hr0_z
                          set dc_hn := ProgHOL.decCall (ofString "hn") .one (ofString "node_new_hashed")
                            [.rfield 1 (.var .local (ofString "it"))]
                            (.return (.rstruct [.const 0#64, .var .local (ofString "hn"), .const 0#64, .const 0#64]))
                          have hite_r0 : evaluateHOLFiniteState s4
                              (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0#64)) dc_hn .skip) =
                              evaluateHOLFiniteState s4 dc_hn := by
                            rw [evaluateHOLFiniteState_ite, hev_r0]; simp
                          rw [hite_r0] at hdnd
                          have hdc_nn : (evaluateHOLFiniteState s4 dc_hn).1 ≠ none := by
                            dsimp only [dc_hn]; rw [evaluateHOLFiniteState_decCall_total]
                            rcases evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
                              [.rfield 1 (.var .local (ofString "it"))] with _ | vs_h
                            · simp
                            · simp only
                              rcases lookupCodeHOLFinite s4.code.lookup (ofString "node_new_hashed") vs_h with _ | ⟨bh, ch, rh⟩
                              · simp
                              · simp only; split
                                · simp
                                · rcases hr_h : evaluateHOLFiniteState (callEntryStateHOLFinite s4 ch) bh with ⟨rh_r, _⟩
                                  simp only [hr_h]
                                  cases rh_r with
                                  | none => simp
                                  | some rhv =>
                                    cases rhv with
                                    | returned _ =>
                                      dsimp only [fixClockHOLFinite]; split
                                      · dsimp only; exact return_ne_none _ _
                                      · simp
                                    | _ => simp [fixClockHOLFinite]
                          rcases hdh : evaluateHOLFiniteState s4 dc_hn with ⟨rdh, pdh⟩
                          rw [hdh] at hdnd
                          cases rdh with
                          | none => exact absurd (congrArg Prod.fst hdh) hdc_nn
                          | some rdh_v =>
                            dsimp only at hdnd
                            injection hdnd with hrc_eq hpdnd_eq
                            injection hrc_eq with hret_eq; subst hret_eq hpdnd_eq
                            dsimp only [dc_hn] at hdh
                            rw [evaluateHOLFiniteState_decCall_total] at hdh
                            have hargs_hn : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
                                [.rfield 1 (.var .local (ofString "it"))] = some [.val (.word i1)] := by
                              rw [evalListHOLFinite_eq_toExact]
                              simp [evalListHOLExact, evalHOLExact, hs4_it]
                            rw [hargs_hn] at hdh; dsimp only at hdh
                            have hl_hn := pan_one_word_lookup s4.code.lookup (ofString "node_new_hashed")
                              (ofString "hash") (sourceFnBody Guest.Software.guestFn_node_new_hashed) i1
                              (by rw [hs4_AR.1.code]; exact lookup_node_new_hashed_r10)
                            rw [hl_hn] at hdh; dsimp only at hdh
                            split at hdh
                            · simp at hdh
                            · rw [fixClockHOLFinite_evaluateState] at hdh
                              let ent_hn := callEntryStateHOLFinite s4
                                (HolFiniteMapExact.empty.update (ofString "hash", .val (.word i1)))
                              rcases hrun_hn : evaluateHOLFiniteState ent_hn
                                  (sourceFnBody Guest.Software.guestFn_node_new_hashed) with ⟨r_hn, p_hn⟩
                              dsimp only [ent_hn] at hrun_hn
                              rw [hrun_hn] at hdh
                              cases r_hn with
                              | none => simp at hdh
                              | some r_hn' =>
                                cases r_hn' with
                                | returned v_hn =>
                                  dsimp only at hdh
                                  split at hdh
                                  · obtain ⟨p_hn0, b_hn0, r_hn0, hlook_hn0, hspec_rt⟩ := rt_node_new_hashed_aux
                                    have hhn_eq : (p_hn0, b_hn0, r_hn0) =
                                        ([(ofString "hash", .one)], sourceFnBody Guest.Software.guestFn_node_new_hashed, .one) :=
                                      Option.some.inj (hlook_hn0.symm.trans lookup_node_new_hashed_r10)
                                    rcases Prod.mk.inj hhn_eq with ⟨_, hhn_eq2⟩
                                    rcases Prod.mk.inj hhn_eq2 with ⟨rfl, rfl⟩
                                    have hrt := hspec_rt ent_hn hs4_AR.1.code
                                      (localsFree_arenaReady s4 _ _ hs4_AR)
                                      ⟨[.val (.word i1)], by
                                        simpa [hs4_AR.1.code, ent_hn, callEntryStateHOLFinite] using hl_hn⟩
                                      (by dsimp only [ent_hn]; rw [hrun_hn]; simp)
                                      v_hn (by dsimp only [ent_hn]; rw [hrun_hn])
                                    obtain ⟨ndw, rfl, hAR_phn, _, hFB_hn⟩ := hrt
                                    dsimp only [ent_hn] at hAR_phn hFB_hn
                                    rw [hrun_hn] at hAR_phn hFB_hn; dsimp only at hAR_phn hFB_hn
                                    set s5 := setVarHOLFinite (ofString "hn") (.val (.word ndw))
                                      { p_hn with locals := s4.locals }
                                    rw [evaluateHOLFiniteState_return] at hdh
                                    have hev_ret_hn : @evalHOLExact 64 F _ s5.toExact
                                        (fun a => Classical.propDecidable (s5.memaddrs a))
                                        (.rstruct [.const 0#64, .var .local (ofString "hn"), .const 0#64, .const 0#64]) =
                                        some (.rStruct [.val (.word 0#64), .val (.word ndw), .val (.word 0#64), .val (.word 0#64)]) := by
                                      simp [s5, setVarHOLFinite, evalHOLExact, evalListHOLExact,
                                        HolFiniteMapExact.lookup_update, FUPDATE]
                                    rw [hev_ret_hn] at hdh; dsimp only at hdh
                                    split at hdh
                                    · simp at hdh
                                      obtain ⟨rfl, hpdh_eq⟩ := hdh
                                      subst hpdh_eq
                                      refine ⟨0#64, ndw, 0#64, 0#64, rfl, fun _ => Or.inr ?_⟩
                                      obtain ⟨hnd_al, ⟨hnd_lo, hnd_hi⟩, hnd_wok⟩ := hFB_hn
                                      have hent_hp : globN ent_hn "heap_ptr" = globN s3 "heap_ptr" := by
                                        have hg_eq : ent_hn.globals = s3.globals := by
                                          dsimp only [ent_hn, callEntryStateHOLFinite]; rw [hs4_eq]
                                        unfold globN; rw [hg_eq]
                                      have hs_le_ent : globN s "heap_ptr" ≤ globN ent_hn "heap_ptr" := by
                                        rw [hent_hp, ← hs2_hp]; exact hsf3.2.1
                                      refine ⟨hnd_al, ⟨Nat.le_trans hs_le_ent hnd_lo, hnd_hi⟩, ?_⟩
                                      exact ⟨hnd_wok.1, hnd_wok.2.1, fun k hk => hnd_wok.2.2 k hk⟩
                                    · simp at hdh
                                  · simp at hdh
                                | _ => simp at hdh
                        · have hite_r0 : evaluateHOLFiniteState s4
                              (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0#64))
                                (.decCall (ofString "hn") .one (ofString "node_new_hashed")
                                  [.rfield 1 (.var .local (ofString "it"))]
                                  (.return (.rstruct [.const 0#64, .var .local (ofString "hn"), .const 0#64, .const 0#64])))
                                .skip) = (none, s4) := by
                            rw [evaluateHOLFiniteState_ite, hev_r0, if_neg hr0_z]
                            simp [evaluateHOLFiniteState_skip]
                          rw [hite_r0] at hdnd; dsimp only at hdnd
                          rw [evaluateHOLFiniteState_return] at hdnd
                          have hev_ret1 : @evalHOLExact 64 F _ s4.toExact
                              (fun a => Classical.propDecidable (s4.memaddrs a))
                              (.rstruct [.const 1#64, .rfield 1 (.var .local (ofString "r")),
                                .rfield 2 (.var .local (ofString "r")), .rfield 1 (.var .local (ofString "it"))]) =
                              some (.rStruct [.val (.word 1#64), .val (.word r1w), .val (.word r2w), .val (.word i1)]) := by
                            simp [evalHOLExact, evalListHOLExact, hs4_r, hs4_it]
                          rw [hev_ret1] at hdnd; dsimp only at hdnd
                          split at hdnd
                          · simp at hdnd
                            obtain ⟨rfl, _⟩ := hdnd
                            exact ⟨1#64, r1w, r2w, i1, rfl, fun h => by simp at h⟩
                          · simp at hdnd
                      · simp only [hsh_r, Bool.false_eq_true, ↓reduceIte] at hdnd; simp at hdnd
                    | _ => simp at hdnd
        · have hi2_ne : i2 ≠ 32#64 := hi2_32
          have hite_it2_32 : evaluateHOLFiniteState s3
              (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "it"))) (.const 32#64))
                (.call (some (none, none)) (ofString "mpt_fail") [.const 10#64])
                .skip) =
              evaluateHOLFiniteState s3 (.call (some (none, none)) (ofString "mpt_fail") [.const 10#64]) := by
            rw [evaluateHOLFiniteState_ite, hev_it2_32, if_pos hi2_ne]; simp
          simp only [hite_it2_32] at hret
          obtain ⟨hnn_mf, hnr_mf⟩ := call0_mpt_fail_ne_none_ne_ret s3 hsf3.1.1.code (.const 10#64)
          rcases hmf : evaluateHOLFiniteState s3 (.call (some (none, none)) (ofString "mpt_fail") [.const 10#64]) with ⟨rmf, _⟩
          rw [hmf] at hnn_mf hnr_mf hret
          cases rmf with
          | none => exact absurd rfl hnn_mf
          | some rmf' => dsimp only at hret; exact absurd hret (hnr_mf v)
    · have hite_it0 : ∀ thn, evaluateHOLFiniteState s3
          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0#64)) thn .skip) =
          (none, s3) := fun thn => by
        rw [evaluateHOLFiniteState_ite, hev_it0, if_neg hi0]
        simp [evaluateHOLFiniteState_skip]
      simp only [hite_it0] at hnt hret ⊢
      rcases hret_end : evaluateHOLFiniteState s3
          (.return (.rstruct [.const 1#64, .var .local (ofString "p"), .var .local (ofString "n"), .const 0#64])) with ⟨rre, pre⟩
      simp only [hret_end] at hret
      rw [evaluateHOLFiniteState_return] at hret_end
      have hev_end : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
          (.rstruct [.const 1#64, .var .local (ofString "p"), .var .local (ofString "n"), .const 0#64]) =
          some (.rStruct [.val (.word 1#64), .val (.word wp), .val (.word wn), .val (.word 0#64)]) := by
        simp [evalHOLExact, evalListHOLExact, hs3_p, hs3_n]
      rw [hev_end] at hret_end; dsimp only at hret_end
      split at hret_end
      · injection hret_end with hrre _; subst hrre
        injection hret with hret'; injection hret' with hv_eq; subst hv_eq
        exact ⟨1#64, wp, wn, 0#64, rfl, fun h => by simp at h⟩
      · injection hret_end with hrre _; subst hrre; simp at hret

end InitECandidate.Solver.Wave8GuestInv.R16Shards.ResolveDecodeStep
