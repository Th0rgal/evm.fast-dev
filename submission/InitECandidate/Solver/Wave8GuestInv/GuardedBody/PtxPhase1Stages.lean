import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Steps
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Semantics
import InitECandidate.Solver.Wave8GuestInv.Expressions
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def IntrinsicOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ a b c : BitVec 64, s.locals.lookup (ofString "intrinsic") =
    some (.rStruct [.val (.word a), .val (.word b), .val (.word c)]) ∧ a.toNat ≤ 16777216

def StageP (n : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxReadyStrong s ∧ (0 < n → SenderOK s) ∧ (1 < n → IntrinsicOK s) ∧
    (2 < n → locN s "regular_budget" ≤ 16777216) ∧ (3 < n → locN s "mgas" ≤ 16777216)

def stageNames (n : Nat) : List String :=
  ["tx", "index"] ++ (if 0 < n then ["sender"] else []) ++
    (if 1 < n then ["intrinsic"] else []) ++ (if 2 < n then ["regular_budget"] else []) ++
    (if 3 < n then ["mgas"] else [])

theorem localsOnly_stage (n : Nat) : LocalsOnly (stageNames n) (StageP n) := by
  intro F s locals k hl h
  have ht := hl "tx" (by simp [stageNames])
  have hi := hl "index" (by simp [stageNames])
  refine ⟨txReadyStrong_with_locals s locals k ht hi h.1, ?_, ?_, ?_, ?_⟩
  · intro hn
    have hs := hl "sender" (by simp [stageNames, hn])
    have he := locN_congr s locals k "sender" hs
    unfold SenderOK
    rw [he]
    exact h.2.1 hn
  · intro hn
    have hs := hl "intrinsic" (by simp [stageNames, hn])
    unfold IntrinsicOK
    simp only [hs]
    exact h.2.2.1 hn
  · intro hn
    have hs := hl "regular_budget" (by simp [stageNames, hn])
    rw [locN_congr s locals k "regular_budget" hs]
    exact h.2.2.2.1 hn
  · intro hn
    have hs := hl "mgas" (by simp [stageNames, hn])
    rw [locN_congr s locals k "mgas" hs]
    exact h.2.2.2.2 hn

theorem stage0 {F : Type} {s : PanSemStateFiniteExact 64 F} (h : TxReadyStrong s) : StageP 0 s :=
  ⟨h, by omega, by omega, by omega, by omega⟩

theorem stage4_validated {F : Type} {s : PanSemStateFiniteExact 64 F} (h : StageP 4 s) :
    PtxValidated s := ⟨h.1, (h.2.1 (by omega)).1, (h.2.1 (by omega)).2, h.2.2.2.2 (by omega)⟩

theorem stage_grows {F : Type} {s post : PanSemStateFiniteExact 64 F} {n : Nat}
    (h : StageP n s) (hr : TxReadyStrong post)
    (hl : post.locals = s.locals) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr") : StageP n post := by
  have hloc : ∀ k, locN post k = locN s k := by intro k; simp only [locN, hl]
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · intro hn
    exact senderOK_grows h.1.1.1.1.1 hr.1.1.1.1 hhp (hloc "sender") (h.2.1 hn)
  · intro hn
    unfold IntrinsicOK
    rw [hl]
    exact h.2.2.1 hn
  · intro hn; rw [hloc]; exact h.2.2.2.1 hn
  · intro hn; rw [hloc]; exact h.2.2.2.2 hn

theorem stage_after_readOnly {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {n : Nat}
    (h : StageP n s)
    (hr : post = {callEntryStateHOLFinite s callee with locals := post.locals, clock := post.clock}) :
    StageP n {post with locals := s.locals} := by
  have he : ({post with locals := s.locals} : PanSemStateFiniteExact 64 F) =
      {s with locals := s.locals, clock := post.clock} := by rw [hr]; rfl
  rw [he]
  exact localsOnly_stage n s s.locals post.clock (fun _ _ => rfl) h

theorem resume_ro_stage {fname name : MlS} {n : Nat}
    (hro : ReadOnlyFn fname) (hne : ∀ k ∈ stageNames n, ofString k ≠ name)
    (args : List (ExpHOL 64)) : DecCallResumeOn (StageP n) (StageP n) name fname args := by
  intro F s vs body callee ret v post hc hP hargs hl hrun
  have hspec := funSpec_at_lookup hro s hc vs body callee ret hl
    (guestInv_callEntry s callee hP.1.1.1.1.1) (by rw [hrun]; simp)
  rw [hrun] at hspec
  have hro' := hspec (Or.inl ⟨v, rfl⟩)
  exact LocalsOnly.setVar (localsOnly_stage n) hne v _ (stage_after_readOnly hP hro')

theorem hoare_call_ro_stage {fname : MlS} {n : Nat}
    (hro : ReadOnlyFn fname) (args : List (ExpHOL 64)) :
    Hoare (StageP n) (.call (some (none, none)) fname args) (fun r t => r = none → StageP n t) := by
  refine Hoare.call0 hro ?_ ?_ (fun _ _ hn _ he => (hn he).elim)
  · intro F s vs body callee ret hc hP hargs hl
    exact guestInv_callEntry s callee hP.1.1.1.1.1
  · intro F s callee post v hc hP hspec _
    exact stage_after_readOnly hP (hspec (Or.inl ⟨v, rfl⟩))

theorem worldOK_callEntry {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : WorldOK s) (callee : HolFiniteMapExact MlS (ValueHOL 64)) :
    WorldOK (callEntryStateHOLFinite s callee) := by
  obtain ⟨ha, S, hw⟩ := h
  exact ⟨(arenaReady_with_locals s callee (s.clock - 1)).mpr ha, S,
    (worldTyped_with_locals s callee (s.clock - 1) S).mpr hw⟩

theorem stage_after_scratchStep {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {n : Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hstep : WorldStep R gw keep Q (callEntryStateHOLFinite s callee) r post) (h : StageP n s)
    {gs : List (String × Nat)} (hgs : ScratchSet gs)
    (hR : R (callEntryStateHOLFinite s callee) = gs.map (fun g => (globN s g.1, g.2)))
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep) :
    StageP n {post with locals := s.locals} := by
  have hs : WorldStep (fun _ => R (callEntryStateHOLFinite s callee)) gw keep NoExtra s r post :=
    worldStep_with_locals hstep s.locals s.clock
  apply stage_grows h
    (txReadyStrong_scratchStep hs h.1 hgs hR hbo_gw hjcap_gw hbo_keep hoffs) rfl
  exact hstep.2.1

theorem resume_scratch_stage {fname name : MlS} {n : Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hwk : WorldKeeps WorldOK R gw keep Q fname)
    {gs : List (String × Nat)} (hgs : ScratchSet gs)
    (hR : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), R s = gs.map (fun g => (globN s g.1, g.2)))
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep)
    (hne : ∀ k ∈ stageNames n, ofString k ≠ name)
    (args : List (ExpHOL 64)) : DecCallResumeOn (StageP n) (StageP n) name fname args := by
  intro F s vs body callee ret v post hc hP hargs hl hrun
  have hs := funSpec_at_lookup hwk s hc vs body callee ret hl
    (worldOK_callEntry hP.1.1.1 callee) (by rw [hrun]; simp)
  rw [hrun] at hs
  have hs' := hs (Or.inl ⟨v, rfl⟩)
  apply LocalsOnly.setVar (localsOnly_stage n) hne v
  exact stage_after_scratchStep hs' hP hgs (hR _) hbo_gw hjcap_gw hbo_keep hoffs

theorem hoare_call_scratch_stage {fname : MlS} {n : Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hwk : WorldKeeps WorldOK R gw keep Q fname)
    {gs : List (String × Nat)} (hgs : ScratchSet gs)
    (hR : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), R s = gs.map (fun g => (globN s g.1, g.2)))
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep)
    (args : List (ExpHOL 64)) :
    Hoare (StageP n) (.call (some (none, none)) fname args) (fun r t => r = none → StageP n t) := by
  refine Hoare.call0 hwk ?_ ?_ (fun _ _ hn _ he => (hn he).elim)
  · intro F s vs body callee ret hc hP hargs hl
    exact worldOK_callEntry hP.1.1.1 callee
  · intro F s callee post v hc hP hspec _
    exact stage_after_scratchStep (hspec (Or.inl ⟨v, rfl⟩)) hP hgs (hR _)
      hbo_gw hjcap_gw hbo_keep hoffs

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
