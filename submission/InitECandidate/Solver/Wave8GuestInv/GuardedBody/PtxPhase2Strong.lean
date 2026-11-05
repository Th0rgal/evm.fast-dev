import InitECandidate.Solver.Wave8GuestInv.R13Shards.PtxPhase45R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase1R11

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Shape information needed by the untyped stores of Phase 2. `price` is
the four-word fee value, whereas `mgas` and `reservoir` are scalar words. -/
structure PtxPhase2LocalShapes {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
  scalar : ∀ name ∈ (["tx", "index", "sender", "mgas", "reservoir"] : List String),
    ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))
  price : ∃ a b c d : BitVec 64, s.locals.lookup (ofString "price") =
    some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)])
  enc : ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
    some (.rStruct [.val (.word a), .val (.word b)])
  intrinsic : ∃ a b c : BitVec 64, s.locals.lookup (ofString "intrinsic") =
    some (.rStruct [.val (.word a), .val (.word b), .val (.word c)])

/-- R11 entry interface for the strengthened Phase 2 proof. -/
def PtxValidatedStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PtxValidated s ∧ PtxPhase2LocalShapes s

theorem ptxValidatedStrong_mgas {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : PtxValidatedStrong s) :
    ∃ w : BitVec 64, s.locals.lookup (ofString "mgas") = some (.val (.word w)) ∧
      w.toNat ≤ 16777216 := by
  obtain ⟨w, hw⟩ := h.2.scalar "mgas" (by simp)
  refine ⟨w, hw, ?_⟩
  have hb := h.1.2.2.2
  simpa [locN, hw] using hb

theorem ptxValidatedStrong_price_length {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : PtxValidatedStrong s) {v : ValueHOL 64}
    (hv : s.locals.lookup (ofString "price") = some v) :
    (flattenHOL v).length = 4 := by
  obtain ⟨a, b, c, d, hp⟩ := h.2.price
  rw [hp] at hv
  cases hv
  simp [flattenHOL]

theorem ptxPhase2LocalShapes_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ name ∈ (["tx", "index", "sender", "mgas", "reservoir", "price", "enc", "intrinsic"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (h : PtxPhase2LocalShapes s) :
    PtxPhase2LocalShapes { s with locals := locals, clock := clock } := by
  constructor
  · intro name hn
    obtain ⟨w, hw⟩ := h.scalar name hn
    refine ⟨w, ?_⟩
    change locals.lookup (ofString name) = _
    rw [hl name (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; tauto)]
    exact hw
  · simpa only [hl "price" (by simp)] using h.price
  · simpa only [hl "enc" (by simp)] using h.enc
  · simpa only [hl "intrinsic" (by simp)] using h.intrinsic

/-- Preserve the scalar witness produced by `min`, which the original
Phase 1 stage predicate retained only through its numeric projection. -/
theorem phase1_resume_min_word (h : PtxCallees) :
    DecCallResumeOn (R16Shards.PtxP1.StageP 3)
      (fun s => R16Shards.PtxP1.StageP 4 s ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "mgas") = some (.val (.word w)))
      (ofString "mgas") (ofString "min")
      [.var .local (ofString "regular_budget"), .var .local (ofString "execution_gas")] := by
  intro F s vs body callee ret v post hc hP ha hl hb
  have hstage := R16Shards.PtxP1.resume_min h s vs body callee ret v post hc hP ha hl hb
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.rv_min s hc vs body callee ret hl
    (guestInv_callEntry s callee hP.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hs
  obtain ⟨w, hv, _⟩ := hs v rfl
  subst v
  refine ⟨hstage, w, ?_⟩
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Shape facts concern only caller locals and therefore survive calls whose
memory/world postconditions are proved separately. -/
theorem ptxPhase2LocalShapes_restore {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (h : PtxPhase2LocalShapes s) :
    PtxPhase2LocalShapes { post with locals := s.locals } := by
  exact ⟨h.scalar, h.price, h.enc, h.intrinsic⟩

theorem ptxPhase2LocalShapes_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PtxPhase2LocalShapes s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["tx", "index", "sender", "mgas", "reservoir", "price", "enc", "intrinsic"] : List String),
      ofString n ≠ name) :
    PtxPhase2LocalShapes (setVarHOLFinite name v s) := by
  apply ptxPhase2LocalShapes_with_locals s _ s.clock _ h
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]

/-- The scalar gas witness survives the caller-local restoration at every
subsequent call, including the balance-return assignment. -/
theorem phase1_mgas_word_resume {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (h : ∃ w : BitVec 64, s.locals.lookup (ofString "mgas") = some (.val (.word w)))
    (name : MlS) (v : ValueHOL 64) (hne : name ≠ ofString "mgas") :
    ∃ w : BitVec 64,
      (setVarHOLFinite name v { post with locals := s.locals }).locals.lookup (ofString "mgas") =
        some (.val (.word w)) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne] using hw⟩

end InitECandidate.Solver.Wave8GuestInv.R13Shards
