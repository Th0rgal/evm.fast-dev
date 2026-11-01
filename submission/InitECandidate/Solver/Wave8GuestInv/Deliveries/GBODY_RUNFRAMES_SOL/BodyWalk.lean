import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.FirstWalk
import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.SecondWalk
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.RunFramesRace
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

theorem body_walk
    (bf : TerminatingFunBoundedOn FinishReady (ofString "finish_child") K.finish_child)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.frame_epilogue)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.frame_exception)
    (bd : TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.op_dispatch)
    (h1 : FunSpec (fun s => EvmInv s ∧ ¬ EvmDone s)
      (fun s r post =>
        ((∃ v, r = some (.returned v)) → EvmInv post ∧ evmPot post < evmPot s) ∧
        (IsEvmErr r → EvmInv post ∧ (evmChain post).length = (evmChain s).length ∧
          evmR post ≤ evmR s))
      (ofString "op_dispatch"))
    (h2 : FunSpec EvmInv
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_exception"))
    (h3 : FunSpec (fun s => EvmInv s ∧ EvmDone s)
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_epilogue"))
    (h4 : FunSpec (fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
      (fun s r post => ((∃ v, r = some (.returned v)) ∨ IsEvmErr r) →
        EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "finish_child")) :
    ∀ c b, some (rfCond, rfBody) = some (c, b) →
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → EvmInv s →
      BHoare (GPre (evmPot s) (evmR s) (evmChain s).length (evmFp s)) b (GQ (evmPot s)) := by
  intro c b hcb F s hcode hinv
  have hb : b = rfBody := by
    rw [rfLoop_eq] at hcb
    exact (congrArg Prod.snd (Option.some.inj hcb)).symm
  subst b
  set p0 := evmPot s
  set R0 := evmR s
  set L0 := (evmChain s).length
  set F0 := evmFp s
  have hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInv t → evmR t ≤ R0 →
      evmFp t < F0 → evmPot t < p0 := fun t ht hR hF =>
    lt_of_lt_of_le (evmPot_lt_bound t ht hR hF) (evmPot_ge s)
  rw [rfBody_eq]
  refine BHoare.dec (names := ["go"]) (P' := GP1 p0 R0 L0 F0) (by decide) ?_ ?_
    (gq_postLocals p0) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
  · intro F t v hP hv
    cases evalAt_const t 0 v hv
    refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
      (evmInv_setVar _ _ hP.1) hP, ?_⟩
    rw [locN_setVar_same]; rfl
  · exact BHoare.seq
      (firstwalk bf be bx bd h1 h2 h3 h4 p0 R0 L0 F0 hfin)
      (secondwalk bf be bx bd h1 h2 h3 h4 p0 R0 L0 F0 hfin)

end InitECandidate.Solver.Wave8GuestInv.RunFramesRace
