import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Calls

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

theorem txReadyStrong_of_parts {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) (hV : TxValid s)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) (hT : TxAccessListOK s S Nd) :
    TxReadyStrong s :=
  ⟨⟨worldOK_of_parts hA hW, hE.bo_nz, hE.bo24, hE.bo32, hE.idx_lt⟩,
    hV, hE.jcap_nz, hE.bo40, hE.bo72, S, Nd, hW, hT⟩

theorem txValid_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (ht : locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx"))
    (h : TxValid s) : TxValid {s with locals := locals, clock := k} := by
  have he := locN_congr s locals k "tx" ht
  unfold TxValid
  rw [he]
  exact h

theorem txReadyStrong_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (ht : locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx"))
    (hi : locals.lookup (ofString "index") = s.locals.lookup (ofString "index"))
    (h : TxReadyStrong s) : TxReadyStrong {s with locals := locals, clock := k} := by
  obtain ⟨S, Nd, hW, hT⟩ := h.2.2.2.2.2
  apply txReadyStrong_of_parts
    ((arenaReady_with_locals s locals k).mpr h.1.1.1)
    (txEnv_with_locals s locals k hi (txEnv_of_ready h))
    (txValid_with_locals s locals k ht h.2.1)
    ((worldTypedWith_with_locals s locals k S Nd).mpr hW)
  exact txAccessListOK_with_locals s locals k ht hT

theorem bo_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hF : FixedTyped s) (hn : globN s "bo" ≠ 0) :
    Allocated s (globN s "bo", 88) ∧ WordsOK s (globN s "bo", 88) := by
  have hm := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords])
  simp only [hn, if_false] at hm
  exact (hF.1 _ hm).resolve_left (by simp)

/-- Transaction inputs survive a framed world update, with caller locals restored. -/
theorem txReadyStrong_worldStep {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hstep : WorldStep R gw keep Q s r post)
    (hA : ArenaReady s) (hE : TxEnv s) (hV : TxValid s)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) (hT : TxAccessListOK s S Nd)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep)
    (hR_bo : ∀ i ∈ R s, Disj i (globN s "bo", 88))
    (hR0 : ∀ i ∈ R s, i.2 = 0 → i.1 % 8 = 0)
    (hRt : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (htx_R : ∀ i ∈ R s, Disj (locN s "tx", 384) i)
    (hrecs_R : memW s (locN s "tx") ≠ 0 → 0 < memW s (locN s "tx" + 216) →
      ∀ i ∈ R s, Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) i) :
    TxReadyStrong {post with locals := s.locals} := by
  obtain ⟨S', Nd', _, hW', hgrow, hframe, _⟩ := hstep.2.2.2.2 S Nd hW hRt
  have hE' := txEnv_preserved_by_worldStep hstep hbo_gw hjcap_gw hbo_keep hoffs hR_bo
    (bo_words hW.2.2.1 hE.bo_nz).2.1 hR0 hE (locals := s.locals) rfl
  have hT' := txAccessListOK_survives_step hA.2 hstep.2.1 hW hR0 hgrow hframe hT
    htx_R hrecs_R (locals := s.locals) rfl
  have hV' : TxValid {post with locals := s.locals} := by
    apply txValid_of_header_preserved hA.1
      (guestInv_with_locals_clock post s.locals post.clock hstep.1.1) hV rfl
    obtain ⟨_, _, hu⟩ := heap_ivl_survives_step hA.2 hstep.2.1
      (worldOwned_zero_aligned hW) hR0 hgrow hframe hT.1 (by simp) hT.2.1 hT.2.2.1 htx_R
    intro k hk
    have hhi := (ivl_allocated_bound hA.2 (Or.inl hT.2.1)).2
    exact memW_eq_of_ivlUnhit hu (by have := hT.1; omega) hhi
      ⟨by dsimp; omega, by dsimp; omega⟩
  exact txReadyStrong_of_parts
    ((arenaReady_with_locals post s.locals post.clock).mpr hstep.1) hE' hV'
    ((worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hW') hT'

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
