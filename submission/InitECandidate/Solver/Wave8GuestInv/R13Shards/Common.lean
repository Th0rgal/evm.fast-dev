import InitECandidate.Solver.Wave8GuestInv.ContractParts.C04
import InitECandidate.Solver.GuestTrapAlign
import InitECandidate.Solver.HeapPotential
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M28.ww_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_get

/-! Shared composable `WWFrame` combinators for `WritesWithin`, `ResolvesNode`, and `PushesFrame`
in shard `R13-M1r2-DecodeRlp`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R13

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Composable `WWFrame` relation -/

structure WWFrame {F : Type} (R : List Ivl) (gw : List String)
    (s post : PanSemStateFiniteExact 64 F) : Prop where
  arena   : ArenaReady post
  hp_le   : globN s "heap_ptr" ≤ globN post "heap_ptr"
  fp_eq   : globN post "frame_mem_ptr" = globN s "frame_mem_ptr"
  sp_le   : globN post "scratch_ptr" ≤ globN s "scratch_ptr"
  frame   : FrameOutside s post
              (R ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
              (globN s "heap_ptr", heapLimit - globN s "heap_ptr")
  globals : ∀ k : MlS, k ∉ gw.map ofString → s.globals.lookup k = post.globals.lookup k

theorem WWFrame.refl {F : Type} (R : List Ivl) (gw : List String)
    {s : PanSemStateFiniteExact 64 F} (hAR : ArenaReady s) :
    WWFrame R gw s s :=
  ⟨hAR, le_rfl, rfl, le_rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem WWFrame.with_locals_clock {F : Type} {R : List Ivl} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F}
    (h : WWFrame R gw s post) (L : HolFiniteMapExact MlS (ValueHOL 64)) (c : Nat) :
    WWFrame R gw s { post with locals := L, clock := c } :=
  ⟨localsFree_arenaReady post L c h.arena, h.hp_le, h.fp_eq, h.sp_le, h.frame, h.globals⟩

theorem WWFrame.mono {F : Type} {R1 R2 : List Ivl} {gw1 gw2 : List String}
    {s post : PanSemStateFiniteExact 64 F}
    (h : WWFrame R1 gw1 s post)
    (hR : ∀ i ∈ R1,
      (∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit) ∨
      (globN s "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s "scratch_ptr"))
    (hgw : ∀ k ∈ gw1, k ∈ gw2) :
    WWFrame R2 gw2 s post := by
  refine ⟨h.arena, h.hp_le, h.fp_eq, h.sp_le, ?_, ?_⟩
  · intro a hkeep hfresh
    apply h.frame a ?_ hfresh
    intro i hi hch
    obtain ⟨hc1, hc2⟩ := hch
    rcases List.mem_append.1 hi with hiR1 | hiGap
    · rcases hR i hiR1 with ⟨j, hj, h1, h2⟩ | ⟨hh1, hh2⟩ | ⟨hg1, hg2⟩
      · exact hkeep j (List.mem_append_left _ hj) ⟨by omega, by omega⟩
      · exact hfresh ⟨by dsimp only; omega, by dsimp only; omega⟩
      · exact hkeep (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")
          (List.mem_append_right _ (List.mem_singleton.2 rfl))
          ⟨by dsimp only; omega, by dsimp only; omega⟩
    · exact hkeep i (List.mem_append_right _ hiGap) ⟨hc1, hc2⟩
  · intro k hk
    apply h.globals k
    intro hmem
    obtain ⟨nm, hnm, rfl⟩ := List.mem_map.1 hmem
    exact hk (List.mem_map.2 ⟨nm, hgw nm hnm, rfl⟩)

theorem WWFrame.trans {F : Type} {R : List Ivl} {gw : List String}
    {a b c : PanSemStateFiniteExact 64 F}
    (h1 : WWFrame R gw a b) (h2 : WWFrame R gw b c) :
    WWFrame R gw a c := by
  refine ⟨h2.arena, Nat.le_trans h1.hp_le h2.hp_le, h2.fp_eq.trans h1.fp_eq,
    Nat.le_trans h2.sp_le h1.sp_le, ?_, ?_⟩
  · intro x hkeep hfresh
    have hkeep_b : ∀ i ∈ R ++ [(globN b "frame_mem_ptr", globN b "scratch_ptr" - globN b "frame_mem_ptr")],
        ¬ CellHits x.toNat i := by
      intro i hi hch
      rcases List.mem_append.1 hi with hiR | hiGap
      · exact hkeep i (List.mem_append_left _ hiR) hch
      · simp only [List.mem_singleton] at hiGap; subst hiGap
        apply hkeep (globN a "frame_mem_ptr", globN a "scratch_ptr" - globN a "frame_mem_ptr")
          (List.mem_append_right _ (List.mem_singleton.2 rfl))
        unfold CellHits at hch ⊢
        have := h1.fp_eq; have := h1.sp_le
        dsimp only at hch ⊢; omega
    have hfresh_b : ¬ CellHits x.toNat (globN b "heap_ptr", heapLimit - globN b "heap_ptr") := by
      intro hch
      apply hfresh
      unfold CellHits at hch ⊢
      have := h1.hp_le; have := h1.arena.2.2.1
      dsimp only at hch ⊢; omega
    exact (h2.frame x hkeep_b hfresh_b).trans (h1.frame x hkeep hfresh)
  · intro k hk
    exact (h1.globals k hk).trans (h2.globals k hk)

theorem WWFrame.to_writesWithin_post {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F}
    (h : WWFrame (R s) gw s post) :
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    FrameOutside s post
      (R s ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
    ∀ k : MlS, k ∉ gw.map ofString → s.globals.lookup k = post.globals.lookup k :=
  ⟨h.arena, h.hp_le, h.sp_le, h.frame, h.globals⟩

/-! ## 2. Ordinary domain and arena helpers -/

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd :=
  InitECandidate.Solver.Wave8Contracts.M28.ordinaryDomain_iff x

theorem ordinaryDomain_of_nat (a : Nat) (hlo : sourceBase ≤ a) (hhi : a < heapEnd)
    (hal : a % 8 = 0) : ordinaryDomain (BitVec.ofNat 64 a) :=
  InitECandidate.Solver.Wave8Contracts.M28.ordinaryDomain_of_nat a hlo hhi hal

theorem wordsOK_of_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (p len : Nat) (hp : p % 8 = 0) (hlen : len % 8 = 0)
    (hlo : sourceBase ≤ p) (hhi : p + len ≤ heapEnd) :
    WordsOK s (p, len) :=
  InitECandidate.Solver.Wave8Contracts.M28.wordsOK_of_guestInv s hG p len hp hlen hlo hhi

theorem arenaOK_globals {F : Type} (s : PanSemStateFiniteExact 64 F) (hA : ArenaOK s) :
    ∃ hp fp sp : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) ∧
      hp.toNat = globN s "heap_ptr" ∧
      s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)) ∧
      fp.toNat = globN s "frame_mem_ptr" ∧
      s.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) ∧
      sp.toNat = globN s "scratch_ptr" :=
  InitECandidate.Solver.Wave8Contracts.M28.arenaOK_globals s hA

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

/-! ## 3. `FlowsOrResumes`, `ReadOnlyProg`, and `WWProg` -/

def FlowsOrResumes (r : Option (PanSemResultExact 64)) : Prop :=
  r = none ∨ r = some .break ∨ r = some .continue ∨ Resumes r

def ReadOnlyProg (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → GuestInv s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowsOrResumes (evaluateHOLFiniteState s prog).1 →
    (evaluateHOLFiniteState s prog).2 =
      { s with
        locals := (evaluateHOLFiniteState s prog).2.locals
        clock := (evaluateHOLFiniteState s prog).2.clock }

theorem state_eq_with_locals_clock {F : Type} {a b : PanSemStateFiniteExact 64 F}
    (h : a = { b with locals := a.locals, clock := a.clock })
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat) :
    { a with locals := locals, clock := clock } = { b with locals := locals, clock := clock } := by
  cases a; cases b
  dsimp only at h
  injection h with _ hg hst hc he hm hma hsh _ hbe hffi hba hta
  subst hg hst hc he hm hma hsh hbe hffi hba hta
  rfl

theorem state_trans_locals_clock {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    (h1 : mid = { s with locals := mid.locals, clock := mid.clock })
    (h2 : post = { mid with locals := post.locals, clock := post.clock }) :
    post = { s with locals := post.locals, clock := post.clock } := by
  rw [h2]
  exact state_eq_with_locals_clock h1 post.locals post.clock

theorem ReadOnlyProg.skip : ReadOnlyProg .skip := by
  intro _ s _ _ _ _; simp only [evaluateHOLFiniteState_skip]

theorem ReadOnlyProg.ret (e : ExpHOL 64) : ReadOnlyProg (.return e) := by
  intro _ s _ _ _ _
  simp only [evaluateHOLFiniteState_return]
  split
  · rfl
  · split <;> [simp [emptyLocalsHOLFinite]; rfl]

theorem ReadOnlyProg.raise (eid : MlS) (e : ExpHOL 64) : ReadOnlyProg (.raise eid e) := by
  intro _ s _ _ _ _
  simp only [evaluateHOLFiniteState_raise]
  split
  · split <;> [simp [emptyLocalsHOLFinite]; rfl]
  · rfl

theorem ReadOnlyProg.assign_local (name : MlS) (e : ExpHOL 64) :
    ReadOnlyProg (.assign .local name e) := by
  intro _ s _ _ _ _
  simp only [evaluateHOLFiniteState_assign]
  split
  · rfl
  · split
    · simp [setKvarHOLFinite, setVarHOLFinite]
    · rfl

theorem ReadOnlyProg.dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64)
    {body : ProgHOL 64} (hbody : ReadOnlyProg body) :
    ReadOnlyProg (.dec name shape init body) := by
  intro F s hcode hG hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · rfl
  · rename_i v hv
    by_cases hsh : shapeEqHOL shape (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
      have hb := hbody (setVarHOLFinite name v s) hcode (guestInv_setVar name v s hG) hnt hfr
      have hset : setVarHOLFinite name v s =
          { s with locals := (setVarHOLFinite name v s).locals, clock := s.clock } := by
        cases s; rfl
      exact state_eq_with_locals_clock (state_trans_locals_clock hset hb) _ _
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte]

theorem ReadOnlyProg.seq {first second : ProgHOL 64}
    (h1 : ReadOnlyProg first) (h2 : ReadOnlyProg second) :
    ReadOnlyProg (.seq first second) := by
  intro F s hcode hG hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s first).1
  have hGmid := guestInv_evaluate s first hG
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hGmid hnt hfr ⊢
  change mid.code = s.code at hmeta
  cases r1 with
  | none =>
    have hb1 := h1 s hcode hG (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hb1
    dsimp only at hb1 hnt hfr ⊢
    exact state_trans_locals_clock hb1 (h2 mid (hmeta.trans hcode) hGmid hnt hfr)
  | some r =>
    have hb1 := h1 s hcode hG (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hb1; exact hb1

theorem ReadOnlyProg.ite (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (hyes : ReadOnlyProg yes) (hno : ReadOnlyProg no) :
    ReadOnlyProg (.ite cond yes no) := by
  intro F s hcode hG hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · split at hnt
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hno s hcode hG hnt hfr
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hyes s hcode hG hnt hfr
  · cases s; rfl

theorem ReadOnlyProg.while_loop (cond : ExpHOL 64) {body : ProgHOL 64}
    (hbody : ReadOnlyProg body) :
    ReadOnlyProg (.while cond body) := by
  intro F s hcode hG hnt hfr
  generalize hk : s.clock = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    subst hk
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hfr ⊢
    revert hnt hfr
    split <;> intro hnt hfr
    · rename_i w hw
      by_cases hnz : w = 0
      · subst hnz; simp only [ne_eq, not_true_eq_false, ↓reduceIte]
      · rw [if_pos hnz] at hnt hfr ⊢
        by_cases hclk : s.clock = 0
        · rw [if_pos hclk] at hnt; simp at hnt
        · rw [if_neg hclk] at hnt hfr ⊢
          have hGd : GuestInv (decClockHOLFinite s) := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body).1
          have hGmid := guestInv_evaluate (decClockHOLFinite s) body hGd
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          simp only [hrun] at hmeta hGmid hrem hnt hfr ⊢
          change mid.code = s.code at hmeta
          change mid.clock ≤ s.clock - 1 at hrem
          have hlt : mid.clock < s.clock := by omega
          have hdecEq : decClockHOLFinite s =
              { s with locals := s.locals, clock := (decClockHOLFinite s).clock } := by
            cases s; rfl
          cases r1 with
          | none =>
            have hb1 := hbody (decClockHOLFinite s) hcode hGd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl rfl)
            rw [hrun] at hb1
            exact state_trans_locals_clock (state_trans_locals_clock hdecEq hb1)
              (ih mid.clock hlt mid (hmeta.trans hcode) hGmid hnt hfr rfl)
          | some res =>
            cases res with
            | «continue» =>
              have hb1 := hbody (decClockHOLFinite s) hcode hGd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hrun] at hb1
              exact state_trans_locals_clock (state_trans_locals_clock hdecEq hb1)
                (ih mid.clock hlt mid (hmeta.trans hcode) hGmid hnt hfr rfl)
            | «break» =>
              have hb1 := hbody (decClockHOLFinite s) hcode hGd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inl rfl))
              rw [hrun] at hb1; exact state_trans_locals_clock hdecEq hb1
            | timeOut => simp at hnt
            | returned v =>
              have hb1 := hbody (decClockHOLFinite s) hcode hGd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hrun] at hb1; exact state_trans_locals_clock hdecEq hb1
            | exception e v =>
              have hres : Resumes (some (.exception e v)) := by
                rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
              have hb1 := hbody (decClockHOLFinite s) hcode hGd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr hres)))
              rw [hrun] at hb1; exact state_trans_locals_clock hdecEq hb1
            | error =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
            | finalFfi _ =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
    · rfl

theorem ReadOnlyProg.call0 {fname : MlS} (hf : ReadOnlyFn fname) (args : List (ExpHOL 64)) :
    ReadOnlyProg (.call (some (none, none)) fname args) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hcode hG hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rfl
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rfl
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return s fname params body' body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hret_eq
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
            · simp only [hsh, ↓reduceIte] at hfr ⊢
              have hro := hspec (callEntryStateHOLFinite s callee) hcode
                (guestInv_callEntry s callee hG) hex (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              rw [hrun] at hro; dsimp only at hro
              exact state_eq_with_locals_clock (state_trans_locals_clock hentryEq hro) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            dsimp only at hfr ⊢
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hro := hspec (callEntryStateHOLFinite s callee) hcode
              (guestInv_callEntry s callee hG) hex (by rw [hrun]; simp) (by rw [hrun]; exact hres)
            rw [hrun] at hro; dsimp only at hro
            exact state_eq_with_locals_clock (state_trans_locals_clock hentryEq hro) _ _
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

theorem ReadOnlyProg.decCall {fname : MlS} (hf : ReadOnlyFn fname)
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : ReadOnlyProg cont) :
    ReadOnlyProg (.decCall name shape fname args cont) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hcode hG hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rfl
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rfl
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return s fname params body' body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hret_eq
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hro := hspec (callEntryStateHOLFinite s callee) hcode
                (guestInv_callEntry s callee hG) hex (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              rw [hrun] at hro; dsimp only at hro
              have hpost : post = { s with locals := post.locals, clock := post.clock } :=
                state_trans_locals_clock hentryEq hro
              let cstate := setVarHOLFinite name v { post with locals := s.locals }
              have hcstateEq : cstate = { s with locals := cstate.locals, clock := cstate.clock } := by
                have h2 : cstate = { post with locals := cstate.locals, clock := post.clock } := by
                  dsimp only [cstate]; cases post; rfl
                exact state_trans_locals_clock hpost h2
              have hGcstate : GuestInv cstate := by
                have hGpost := guestInv_evaluate (callEntryStateHOLFinite s callee) body' (guestInv_callEntry s callee hG)
                rw [hrun] at hGpost
                exact guestInv_setVar name v _ (guestInv_with_locals_clock post s.locals post.clock hGpost)
              have hbcont := hcont cstate hGcstate.code hGcstate hnt hfr
              exact state_eq_with_locals_clock (state_trans_locals_clock hcstateEq hbcont) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hro := hspec (callEntryStateHOLFinite s callee) hcode
              (guestInv_callEntry s callee hG) hex (by rw [hrun]; simp) (by rw [hrun]; exact hres)
            rw [hrun] at hro; dsimp only at hro
            exact state_eq_with_locals_clock (state_trans_locals_clock hentryEq hro) _ post.clock
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

theorem readOnlyFn_of_guestAst
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64))
    (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hprog : ReadOnlyProg
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)) :
    ReadOnlyFn (ofString (extractFn d).name) := by
  refine ⟨(extractFn d).params.map InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural (extractFn d).returnShape,
    lookup_of_guestAst_getElem i hi (extractFn d) hd, ?_⟩
  intro F s hcode hG _hlookup hnt hres
  exact hprog s hcode hG hnt (Or.inr (Or.inr (Or.inr hres)))

/-! ## 4. Basic ReadOnlyFn instances (`mpt_fail`, `rlp_fail`, `rlp_read_length`, `rlp_item_header`, `rlp_item_total_unchecked`, `nodedb_lookup`) -/

theorem ro_mpt_fail : ReadOnlyFn (ofString "mpt_fail") := by
  refine readOnlyFn_of_guestAst 246 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mpt_fail rfl ?_
  dsimp only [Guest.Software.guestFn_mpt_fail, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.seq (ReadOnlyProg.raise _ _) (ReadOnlyProg.ret _)

theorem ro_rlp_fail : ReadOnlyFn (ofString "rlp_fail") := by
  refine readOnlyFn_of_guestAst 105 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_fail rfl ?_
  dsimp only [Guest.Software.guestFn_rlp_fail, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.seq (ReadOnlyProg.raise _ _) (ReadOnlyProg.ret _)

theorem ro_rlp_read_length : ReadOnlyFn (ofString "rlp_read_length") := by
  refine readOnlyFn_of_guestAst 106 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_read_length rfl ?_
  dsimp only [Guest.Software.guestFn_rlp_read_length, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.seq
    (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
    (ReadOnlyProg.dec _ _ _
      (ReadOnlyProg.dec _ _ _
        (ReadOnlyProg.seq
          (ReadOnlyProg.while_loop _
            (ReadOnlyProg.seq (ReadOnlyProg.assign_local _ _) (ReadOnlyProg.assign_local _ _)))
          (ReadOnlyProg.ret _))))

theorem ro_rlp_item_header : ReadOnlyFn (ofString "rlp_item_header") := by
  refine readOnlyFn_of_guestAst 109 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_item_header rfl ?_
  dsimp only [Guest.Software.guestFn_rlp_item_header, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.seq
    (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
    (ReadOnlyProg.dec _ _ _
      (ReadOnlyProg.seq
        (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
        (ReadOnlyProg.seq
          (ReadOnlyProg.ite _
            (ReadOnlyProg.dec _ _ _
              (ReadOnlyProg.seq
                (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                (ReadOnlyProg.seq
                  (ReadOnlyProg.ite _
                    (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                    ReadOnlyProg.skip)
                  (ReadOnlyProg.ret _))))
            ReadOnlyProg.skip)
          (ReadOnlyProg.seq
            (ReadOnlyProg.ite _
              (ReadOnlyProg.dec _ _ _
                (ReadOnlyProg.seq
                  (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                  (ReadOnlyProg.decCall ro_rlp_read_length _ _ _
                    (ReadOnlyProg.seq
                      (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                      (ReadOnlyProg.seq
                        (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                        (ReadOnlyProg.ret _))))))
              ReadOnlyProg.skip)
            (ReadOnlyProg.seq
              (ReadOnlyProg.ite _
                (ReadOnlyProg.dec _ _ _
                  (ReadOnlyProg.seq
                    (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                    (ReadOnlyProg.ret _)))
                ReadOnlyProg.skip)
              (ReadOnlyProg.dec _ _ _
                (ReadOnlyProg.seq
                  (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                  (ReadOnlyProg.decCall ro_rlp_read_length _ _ _
                    (ReadOnlyProg.seq
                      (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                      (ReadOnlyProg.seq
                        (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                        (ReadOnlyProg.ret _)))))))))))

theorem ro_rlp_item_total_unchecked : ReadOnlyFn (ofString "rlp_item_total_unchecked") := by
  refine readOnlyFn_of_guestAst 114 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_item_total_unchecked rfl ?_
  dsimp only [Guest.Software.guestFn_rlp_item_total_unchecked, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.dec _ _ _
    (ReadOnlyProg.seq
      (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
      (ReadOnlyProg.seq
        (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
        (ReadOnlyProg.seq
          (ReadOnlyProg.ite _
            (ReadOnlyProg.dec _ _ _
              (ReadOnlyProg.decCall ro_rlp_read_length _ _ _
                (ReadOnlyProg.ret _)))
            ReadOnlyProg.skip)
          (ReadOnlyProg.seq
            (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
            (ReadOnlyProg.dec _ _ _
              (ReadOnlyProg.decCall ro_rlp_read_length _ _ _
                (ReadOnlyProg.ret _)))))))

theorem ro_htab_get : ReadOnlyFn (ofString "htab_get") :=
  InitECandidate.Solver.Wave8Contracts.M15.ro_htab_get

theorem ro_nodedb_lookup : ReadOnlyFn (ofString "nodedb_lookup") := by
  refine readOnlyFn_of_guestAst 254 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_nodedb_lookup rfl ?_
  dsimp only [Guest.Software.guestFn_nodedb_lookup, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.decCall ro_htab_get _ _ _
    (ReadOnlyProg.seq
      (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
      (ReadOnlyProg.ret _))

/-! ## 5. Exact `alloc` and `scratch_alloc` resume lemmas -/

theorem evaluate_call_trap_with_not_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    ¬ Resumes (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 := by
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const codeVal] =
      some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlookup := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal (by rw [hcode]; exact lookup_trap_with)
  rw [hargs]; dsimp only; rw [hlookup]; dsimp only
  split
  · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hbody] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | exception eid ev =>
        rintro (⟨_, h⟩ | ⟨e', v', h, hne⟩)
        · simp at h
        · injection h with h'; injection h' with he1 he2; subst he1 he2
          exact hout.2.2 eid ev hne rfl
      | _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

theorem alloc_arith (p n : BitVec 64)
    (hp_hi : p.toNat ≤ heapLimit) (hp_al : p.toNat % 8 = 0)
    (hcmp1 : ¬ ((cMax - p).toNat < n.toNat))
    (hcmp2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    q.toNat = p.toNat + (n.toNat + 7) / 8 * 8 ∧
    q.toNat ≤ heapLimit ∧ q.toNat % 8 = 0 ∧ p.toNat ≤ q.toNat ∧
    p.toNat + n.toNat ≤ q.toNat := by
  intro q
  have hcMax : cMax.toNat = 2952790016 := rfl
  have hlim : heapLimit = 2952790016 := by decide
  have hsub : (cMax - p).toNat = 2952790016 - p.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hn_le : n.toNat ≤ 2952790016 - p.toNat := by omega
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  have hn7 : (n + 7).toNat = n.toNat + 7 := by
    rw [BitVec.toNat_add, h7]; omega
  have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by
    rw [BitVec.toNat_add, hn7]; omega
  have hq_nat : q.toNat = (p + (n + 7)).toNat / 8 * 8 := and_neg8_toNat (p + (n + 7))
  rw [hsum] at hq_nat
  have hq_le : q.toNat ≤ cMax.toNat := Nat.le_of_not_lt hcmp2
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem alloc_body_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    Resumes out.1 →
      ∃ n : BitVec 64,
        state.locals.lookup (ofString "n") = some (.val (.word n)) ∧
        let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
        out.1 = some (.returned (.val (.word p))) ∧
        ¬ ((cMax - p).toNat < n.toNat) ∧ ¬ (cMax.toNat < q.toNat) ∧
        out.2 = { state with
          globals := state.globals.update (ofString "heap_ptr", .val (.word q))
          locals := out.2.locals } := by
  dsimp only
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
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only; rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only; rw [if_pos hsh_p]; dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_eq : pState.locals.lookup (ofString "n") = state.locals.lookup (ofString "n") := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "n" by decide]
  have hcode_p : pState.code = originalRuntimeCode := hcode
  rcases hn : state.locals.lookup (ofString "n") with _ | vn
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    have hnone : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
          (.var .local (ofString "n"))) = none := by
      simp [evalHOLExact, evalListHOLExact, hp_loc, hn_eq, hn]
    rw [hnone]; intro hr; exact absurd hr not_resumes_error
  · rcases vn with ⟨⟨n⟩⟩ | _ | _
    · have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
        rw [hn_eq, hn]
      rw [evaluateHOLFiniteState_seq_line780]
      have hev1 : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n"))) =
          some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
        simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
          Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
        rfl
      by_cases hcmp1 : (cMax - p).toNat < n.toNat
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
            evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
        rw [hite1]
        have hno_none := evaluate_call_trap_with_no_none pState 1 hcode_p
        have hno_res := evaluate_call_trap_with_not_resumes pState 1 hcode_p
        rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
        rw [htr] at hno_none hno_res
        cases r1 with
        | none => exact absurd rfl hno_none
        | some _ => intro hr; exact absurd hr hno_res
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, pState) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
        rw [hite1]; dsimp only
        rw [evaluateHOLFiniteState_dec_total]
        let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
        have hq_eval : @evalHOLExact 64 F _ pState.toExact
            (fun a => Classical.propDecidable (pState.memaddrs a))
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
          simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
            wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
          exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
        dsimp only; rw [hq_eval]
        have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        dsimp only; rw [if_pos hsh_q]; dsimp only
        let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
        have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
            show ofString "q" ≠ ofString "p" by decide]
        have hcode_q : qState.code = originalRuntimeCode := hcode
        rw [evaluateHOLFiniteState_seq_line780]
        have hev2 : @evalHOLExact 64 F _ qState.toExact
            (fun a => Classical.propDecidable (qState.memaddrs a))
            (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
            some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
          simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
        by_cases hcmp2 : cMax.toNat < q.toNat
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
              evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
          rw [hite2]
          have hno_none := evaluate_call_trap_with_no_none qState 1 hcode_q
          have hno_res := evaluate_call_trap_with_not_resumes qState 1 hcode_q
          rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
          rw [htr] at hno_none hno_res
          cases r2 with
          | none => exact absurd rfl hno_none
          | some _ => intro hr; exact absurd hr hno_res
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, qState) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
          rw [hite2]; dsimp only
          have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lookup
          have heval_end : evaluateHOLFiniteState qState
              (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p")))) =
              (some (.returned (.val (.word p))),
                emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
              shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
              evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
          rw [heval_end]
          intro _
          exact ⟨n, rfl, rfl, hcmp1, hcmp2, rfl⟩
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      have hnone : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n"))) = none := by
        simp [evalHOLExact, evalListHOLExact, hp_loc, hn_eq, hn, valueIsWord]
      rw [hnone]; intro hr; exact absurd hr not_resumes_error
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      have hnone : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n"))) = none := by
        simp [evalHOLExact, evalListHOLExact, hp_loc, hn_eq, hn, valueIsWord]
      rw [hnone]; intro hr; exact absurd hr not_resumes_error

theorem scratch_alloc_arith (sp fp n : BitVec 64)
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
    have h := and_neg8_toNat (sp - n)
    rw [hsub_pn] at h; exact h
  have hq_ge_fp : fp.toNat ≤ q.toNat := Nat.le_of_not_lt hcmp2
  exact ⟨by omega, hq_ge_fp, by omega, by omega, by omega⟩

theorem scratch_alloc_body_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p f : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf_lookup : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)
    Resumes out.1 →
      ∃ n : BitVec 64,
        state.locals.lookup (ofString "n") = some (.val (.word n)) ∧
        let q := (p - n) &&& ((0 : BitVec 64) - 8)
        out.1 = some (.returned (.val (.word q))) ∧
        ¬ ((p - f).toNat < n.toNat) ∧ ¬ (q.toNat < f.toNat) ∧
        out.2 = { state with
          globals := state.globals.update (ofString "scratch_ptr", .val (.word q))
          locals := out.2.locals } := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_scratch_alloc =
      .dec (ofString "p") .one (.var .global (ofString "scratch_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const 7])
                .skip)
              (.seq
                (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "scratch_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only; rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only; rw [if_pos hsh_p]; dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_eq : pState.locals.lookup (ofString "n") = state.locals.lookup (ofString "n") := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "n" by decide]
  have hf_g : pState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) := hf_lookup
  have hcode_p : pState.code = originalRuntimeCode := hcode
  rcases hn : state.locals.lookup (ofString "n") with _ | vn
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    have hnone : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
          (.var .local (ofString "n"))) = none := by
      simp [evalHOLExact, evalListHOLExact, hp_loc, hn_eq, hn, hf_g]
    rw [hnone]; intro hr; exact absurd hr not_resumes_error
  · rcases vn with ⟨⟨n⟩⟩ | _ | _
    · have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
        rw [hn_eq, hn]
      rw [evaluateHOLFiniteState_seq_line780]
      have hev1 : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n"))) =
          some (.val (.word (if (p - f).toNat < n.toNat then 1 else 0))) := by
        simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc, hf_g,
          Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
        simp [wordOpHOL, wordOp, valueIsWord, valueWord]
      by_cases hcmp1 : (p - f).toNat < n.toNat
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 7]) .skip) =
            evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 7]) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
        rw [hite1]
        have hno_none := evaluate_call_trap_with_no_none pState 7 hcode_p
        have hno_res := evaluate_call_trap_with_not_resumes pState 7 hcode_p
        rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r1, s1⟩
        rw [htr] at hno_none hno_res
        cases r1 with
        | none => exact absurd rfl hno_none
        | some _ => intro hr; exact absurd hr hno_res
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 7]) .skip) = (none, pState) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
        rw [hite1]; dsimp only
        rw [evaluateHOLFiniteState_dec_total]
        let q : BitVec 64 := (p - n) &&& ((0 : BitVec 64) - 8)
        have hq_eval : @evalHOLExact 64 F _ pState.toExact
            (fun a => Classical.propDecidable (pState.memaddrs a))
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
          simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
            wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
          have h2 : AndOp.and ((0 : BitVec 64) - 8) (~~~0) = (0 : BitVec 64) - 8 := by decide
          simp only [h2]; rfl
        dsimp only; rw [hq_eval]
        have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        dsimp only; rw [if_pos hsh_q]; dsimp only
        let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
        have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
            show ofString "q" ≠ ofString "p" by decide]
        have hcode_q : qState.code = originalRuntimeCode := hcode
        rw [evaluateHOLFiniteState_seq_line780]
        have hev2 : @evalHOLExact 64 F _ qState.toExact
            (fun a => Classical.propDecidable (qState.memaddrs a))
            (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr"))) =
            some (.val (.word (if q.toNat < f.toNat then 1 else 0))) := by
          have hf_q : qState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) := hf_lookup
          simp only [evalHOLExact, hq_loc, hf_q, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
            decide_eq_true_eq]
        by_cases hcmp2 : q.toNat < f.toNat
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const 7]) .skip) =
              evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 7]) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
          rw [hite2]
          have hno_none := evaluate_call_trap_with_no_none qState 7 hcode_q
          have hno_res := evaluate_call_trap_with_not_resumes qState 7 hcode_q
          rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r2, s2⟩
          rw [htr] at hno_none hno_res
          cases r2 with
          | none => exact absurd rfl hno_none
          | some _ => intro hr; exact absurd hr hno_res
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const 7]) .skip) = (none, qState) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
          rw [hite2]; dsimp only
          have hp_g : qState.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)) := hp_lookup
          have heval_end : evaluateHOLFiniteState qState
              (.seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q")))) =
              (some (.returned (.val (.word q))),
                emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word q)) qState)) := by
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
              shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
              evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
          rw [heval_end]
          intro _
          exact ⟨n, rfl, rfl, hcmp1, hcmp2, rfl⟩
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      have hnone : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n"))) = none := by
        simp [evalHOLExact, evalListHOLExact, hp_loc, hn_eq, hn, hf_g, valueIsWord]
      rw [hnone]; intro hr; exact absurd hr not_resumes_error
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      have hnone : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n"))) = none := by
        simp [evalHOLExact, evalListHOLExact, hp_loc, hn_eq, hn, hf_g, valueIsWord]
      rw [hnone]; intro hr; exact absurd hr not_resumes_error

/-! ## 6. Word and byte store `WWFrame` steps -/

theorem wwFrame_store_word {F : Type} {R : List Ivl} {gw : List String}
    {s : PanSemStateFiniteExact 64 F} (hAR : ArenaReady s)
    (dst val : ExpHOL 64)
    (hval : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs addr →
      (∃ i ∈ R, i.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ i.1 + i.2) ∨
      (globN s "heap_ptr" ≤ addr.toNat ∧ addr.toNat + 8 ≤ heapLimit) ∨
      (globN s "frame_mem_ptr" ≤ addr.toNat ∧ addr.toNat + 8 ≤ globN s "scratch_ptr")) :
    WWFrame R gw s (evaluateHOLFiniteState s (.store dst val)).2 := by
  rw [evaluateHOLFiniteState_store]
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · exact WWFrame.refl R gw hAR
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _ <;> try exact WWFrame.refl R gw hAR
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | vv
    · exact WWFrame.refl R gw hAR
    · obtain ⟨w, rfl⟩ := hval vv hv
      dsimp only
      split
      · rename_i mem' hmem
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
        by_cases hdom : s.memaddrs addr
        · simp only [hdom, ↓reduceIte, Option.some.injEq] at hmem
          subst hmem
          have hloc := hin addr hdst hdom
          refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hAR.1, hAR.2⟩,
            le_rfl, rfl, le_rfl, ?_, fun _ _ => rfl⟩
          intro a hkeep hfresh
          dsimp only
          have hne : a ≠ addr := by
            rintro rfl
            rcases hloc with ⟨i, hi, h1, h2⟩ | ⟨hh1, hh2⟩ | ⟨hg1, hg2⟩
            · exact hkeep i (List.mem_append_left _ hi) ⟨by omega, by omega⟩
            · exact hfresh ⟨by dsimp only; omega, by dsimp only; omega⟩
            · exact hkeep (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")
                (List.mem_append_right _ (List.mem_singleton.2 rfl))
                ⟨by dsimp only; omega, by dsimp only; omega⟩
          rw [if_neg hne]
        · simp [hdom] at hmem
      · exact WWFrame.refl R gw hAR

theorem wwFrame_storeByte {F : Type} {R : List Ivl} {gw : List String}
    {s : PanSemStateFiniteExact 64 F} (hAR : ArenaReady s)
    (dst val : ExpHOL 64)
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs (panByteAlignHOL addr) →
      (∃ i ∈ R, i.1 ≤ addr.toNat ∧ addr.toNat < i.1 + i.2) ∨
      (globN s "heap_ptr" ≤ addr.toNat ∧ addr.toNat < heapLimit) ∨
      (globN s "frame_mem_ptr" ≤ addr.toNat ∧ addr.toNat < globN s "scratch_ptr")) :
    WWFrame R gw s (evaluateHOLFiniteState s (.storeByte dst val)).2 := by
  rw [evaluateHOLFiniteState_storeByte]
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · exact WWFrame.refl R gw hAR
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _ <;> try exact WWFrame.refl R gw hAR
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | vv
    · exact WWFrame.refl R gw hAR
    · rcases vv with ⟨⟨w⟩⟩ | _ | _ <;> try exact WWFrame.refl R gw hAR
      dsimp only
      split
      · rename_i mem' hmem
        unfold panMemStoreByteWord8HOL at hmem
        dsimp only at hmem
        cases s.memory (panByteAlignHOL addr) with
        | word cell =>
          by_cases hdom : s.memaddrs (panByteAlignHOL addr)
          · simp only [hdom, ↓reduceIte, Option.some.injEq] at hmem
            subst hmem
            have hloc := hin addr hdst hdom
            have hal := panByteAlign_toNat64 addr
            refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hAR.1, hAR.2⟩,
              le_rfl, rfl, le_rfl, ?_, fun _ _ => rfl⟩
            intro a hkeep hfresh
            dsimp only
            have hne : a ≠ panByteAlignHOL addr := by
              rintro rfl
              rcases hloc with ⟨i, hi, h1, h2⟩ | ⟨hh1, hh2⟩ | ⟨hg1, hg2⟩
              · exact hkeep i (List.mem_append_left _ hi) ⟨by rw [hal]; omega, by rw [hal]; omega⟩
              · exact hfresh ⟨by dsimp only; rw [hal]; omega, by dsimp only; rw [hal]; omega⟩
              · exact hkeep (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")
                  (List.mem_append_right _ (List.mem_singleton.2 rfl))
                  ⟨by dsimp only; rw [hal]; omega, by dsimp only; rw [hal]; omega⟩
            rw [if_neg hne]
          · simp [hdom] at hmem
      · exact WWFrame.refl R gw hAR

end InitECandidate.Solver.Wave8GuestInv.R13
