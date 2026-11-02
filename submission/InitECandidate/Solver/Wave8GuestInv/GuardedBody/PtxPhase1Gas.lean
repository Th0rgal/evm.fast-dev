import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Recover
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

open Flapjack.Compiler.Encoders.Asm
theorem resume_validate (h : PtxCallees) :
    DecCallResumeOn (StageP 1) (StageP 2) (ofString "intrinsic") (ofString "validate_transaction")
      [.var .local (ofString "tx"),.var .local (ofString "sender")] := by
  intro F s vs body callee ret v post hc hP ha hl hb
  have hkeep := resume_ro_stage (n := 1) h.ro_validate_transaction
    (name := ofString "intrinsic") (by decide) _ s vs body callee ret v post hc hP ha hl hb
  have hs := funSpec_at_lookup h.rv_validate_transaction s hc vs body callee ret hl
    (guestInv_callEntry s callee hP.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hs
  obtain ⟨a,b,c,hv,hle⟩ := hs v rfl
  subst v
  refine ⟨hkeep.1,fun _ => hkeep.2.1 (by omega),?_,by omega,by omega⟩
  intro _
  exact ⟨a,b,c,by simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE],hle⟩

def regularBudgetExp : ExpHOL 64 :=
  .op .sub [.const 16777216,.rfield 0 (.var .local (ofString "intrinsic"))]

theorem locN_set_word {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (w : BitVec 64) :
    locN (setVarHOLFinite (ofString name) (.val (.word w)) s) name = w.toNat := by
  simp [locN,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

theorem declare_regular_budget_aux {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (cap : BitVec 64) (hc : cap.toNat = 16777216) (hP : StageP 2 s)
    (he : evalAt s (.op .sub [.const cap,.rfield 0 (.var .local (ofString "intrinsic"))]) = some v) :
    StageP 3 (setVarHOLFinite (ofString "regular_budget") v s) := by
  obtain ⟨a,b,c,hi,hle⟩ := hP.2.2.1 (by omega)
  have hv : v = .val (.word (cap - a)) := by
    simpa [evalAt,evalHOLExact,evalListHOLExact,hi,valueIsWord,valueWord,wordOpHOL,wordOp] using he.symm
  subst v
  have hkeep := LocalsOnly.setVar (localsOnly_stage 2) (name := ofString "regular_budget")
    (by decide) (.val (.word (cap - a))) s hP
  refine ⟨hkeep.1,(fun _ => hkeep.2.1 (by omega)),(fun _ => hkeep.2.2.1 (by omega)),?_,by omega⟩
  intro _
  rw [locN_set_word]
  have ha : a ≤ cap := by change a.toNat ≤ cap.toNat; omega
  rw [BitVec.toNat_sub_of_le ha]
  omega

theorem declare_regular_budget {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hP : StageP 2 s) (he : evalAt s regularBudgetExp = some v) :
    StageP 3 (setVarHOLFinite (ofString "regular_budget") v s) :=
  declare_regular_budget_aux s v (16777216#64) rfl hP he

theorem resume_min (h : PtxCallees) :
    DecCallResumeOn (StageP 3) (StageP 4) (ofString "mgas") (ofString "min")
      [.var .local (ofString "regular_budget"),.var .local (ofString "execution_gas")] := by
  intro F s vs body callee ret v post hc hP ha hl hb
  obtain ⟨v1,v2,he1,he2,hpa,hpb⟩ := params_two_values s (ofString "min") (ofString "a") (ofString "b")
    .one .one _ .one (by rw [hc]; exact lookup_min)
    (.var .local (ofString "regular_budget")) (.var .local (ofString "execution_gas")) vs body callee ret ha hl
  have hca : locN (callEntryStateHOLFinite s callee) "a" = locN s "regular_budget" := by
    simp only [locN,callEntryStateHOLFinite,hpa,
      show s.locals.lookup (ofString "regular_budget") = some v1 from he1]
  have hkeep := resume_ro_stage (n := 3) h.ro_min (name := ofString "mgas") (by decide) _
    s vs body callee ret v post hc hP ha hl hb
  have hs := funSpec_at_lookup h.rv_min s hc vs body callee ret hl
    (guestInv_callEntry s callee hP.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hs
  obtain ⟨w,hv,hle⟩ := hs v rfl
  subst v
  refine ⟨hkeep.1,(fun _ => hkeep.2.1 (by omega)),(fun _ => hkeep.2.2.1 (by omega)),
    (fun _ => hkeep.2.2.2.1 (by omega)),?_⟩
  intro _
  have hw : locN (setVarHOLFinite (ofString "mgas") (.val (.word w)) {post with locals := s.locals})
      "mgas" = w.toNat := by simp [locN,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  rw [hw]
  change w.toNat ≤ locN (callEntryStateHOLFinite s callee) "a" at hle
  rw [hca] at hle
  exact hle.trans (hP.2.2.2.1 (by omega))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
