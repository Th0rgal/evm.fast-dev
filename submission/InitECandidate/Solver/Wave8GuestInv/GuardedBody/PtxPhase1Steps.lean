import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Geometry
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

def ScratchSet (gs : List (String × Nat)) : Prop :=
  ∀ g ∈ gs, g ∈ globalBuffers ∧ g ∉ typedRecords ∧ 0 < g.2 ∧ g.2 ≤ sourceBase

theorem bo_mem_typed {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hn : globN s "bo" ≠ 0) : (globN s "bo", 88) ∈ worldTypedIvls s S Nd := by
  apply mem_normalized (hn := by simp)
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
    (List.mem_map.mpr ⟨("bo", 88), by simp [typedRecords], by simp [hn]⟩)))))

theorem txReadyStrong_scratchStep {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hstep : WorldStep R gw keep Q s r post) (h : TxReadyStrong s)
    {gs : List (String × Nat)} (hgs : ScratchSet gs)
    (hR : R s = gs.map (fun g => (globN s g.1, g.2)))
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep) :
    TxReadyStrong {post with locals := s.locals} := by
  obtain ⟨S, Nd, hW, hT⟩ := h.2.2.2.2.2
  have hrSafe : IvlsDisj (R s) (worldTypedIvls s S Nd) := by
    intro i hi j hj
    rw [hR] at hi
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hgb, hgt, hgn, hsmall⟩ := hgs g hg
    exact buffer_disj_typed h.1.1.1.2 hW hgb hgt hgn hsmall j hj
  apply txReadyStrong_worldStep hstep h.1.1.1 (txEnv_of_ready h) h.2.1 hW hT
    hbo_gw hjcap_gw hbo_keep hoffs
    (fun i hi => hrSafe i hi _ (bo_mem_typed h.1.2.1))
    ?_ hrSafe ?_ ?_
  · intro i hi hz
    rw [hR] at hi
    obtain ⟨g, hg, he⟩ := List.mem_map.mp hi
    have hgn := (hgs g hg).2.2.1
    have he2 := congrArg Prod.snd he
    dsimp at he2
    omega
  · intro i hi
    rw [hR] at hi
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hgb, _, hgn, hsmall⟩ := hgs g hg
    exact input_disj_buffer hT.2.1.1 hT.2.2.1 hgb hgn hsmall
  · intro ht hn i hi
    rw [hR] at hi
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hgb, _, hgn, hsmall⟩ := hgs g hg
    have hr := (hT.2.2.2 ht).2.1 hn
    exact input_disj_buffer hr.2.1.1 hr.2.2 hgb hgn hsmall

/-- Data kept in the sender buffer; its contents need no framing for this phase. -/
def SenderOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  Inside (locN s "sender", 24) sourceBase (globN s "heap_ptr") ∧
  WordsOK s (locN s "sender", 24)

theorem senderOK_grows {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hg : GuestInv s) (hg' : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hl : locN post "sender" = locN s "sender") (h : SenderOK s) : SenderOK post := by
  unfold SenderOK
  rw [hl]
  exact ⟨⟨h.1.1, h.1.2.trans hhp⟩, wordsOK_transfer hg hg' h.2⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
