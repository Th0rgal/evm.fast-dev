import InitECandidate.Solver.Wave8GuestInv.GuardedBody.RunFramesStep01
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.RunFramesStep02
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.RunFramesStep03
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.RunFramesStep04
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.RunFramesStep05
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.RunFramesStep06
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

open InitECandidate.Solver.Wave8GuestInv.RunFramesRace
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
      (runFramesStep01 p0 R0 L0 F0 hfin (runFramesStep02 bf be bx bd h1 h2 h3 h4 p0 R0 L0 F0 hfin (runFramesStep03 p0 R0 L0 F0)))
      (runFramesStep04 bf be bx bd h1 h2 h3 h4 p0 R0 L0 F0 hfin (runFramesStep06 p0 R0 L0 F0 hfin) (runFramesStep05 bf be bx bd h1 h2 h3 h4 p0 R0 L0 F0 hfin))

theorem runStep
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
      LoopActive c s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) b).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) b).1 = some .continue) →
      (EvmInv (evaluateHOLFiniteState (decClockHOLFinite s) b).2 ∧
        evmPot (evaluateHOLFiniteState (decClockHOLFinite s) b).2 < evmPot s) ∨
      locN (evaluateHOLFiniteState (decClockHOLFinite s) b).2 "go" = 0 := by
  intro c b hcb F s hc hi ha hflow
  have key := body_walk bf be bx bd h1 h2 h3 h4 c b hcb s hc hi
  have hnt : (evaluateHOLFiniteState (decClockHOLFinite s) b).1 ≠ some .timeOut := by
    rcases hflow with h | h <;> rw [h] <;> simp
  have hpre : GPre (evmPot s) (evmR s) (evmChain s).length (evmFp s) (decClockHOLFinite s) := by
    obtain ⟨e1, e2, e3, e4⟩ := evm_congr (s := s) (t := decClockHOLFinite s) rfl rfl
    exact ⟨localsFree_evmInv s s.locals (s.clock - 1) hi, e1, e2, e3, e4⟩
  exact key.hoare.run (decClockHOLFinite s) hc hpre hnt hflow

theorem sum_pair_le {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ l : List Ivl, (l.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum ≤
      l.length * (2 * (2 ^ 64 - 1))
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := memW_lt s (x.1 + 64)
    have h2 := memW_lt s (x.1 + 192)
    have hi := sum_pair_le s xs
    omega

theorem cap_algebra (a b c : Nat) : a * (b * c) + b * c = (a + 1) * b * c := by
  simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]

theorem potential_bounded {F : Type} (s : PanSemStateFiniteExact 64 F) (hi : EvmInv s) :
    evmPot s < evmPotMax := by
  have hlen := evmInv_len s hi
  have hR : evmR s ≤ maxChain * (2 * (2 ^ 64 - 1)) :=
    (sum_pair_le s (evmChain s)).trans (Nat.mul_le_mul_right _ hlen)
  have hcap : evmR s ≤ 2 * maxChain * 2 ^ 64 := by
    simp only [maxChain] at hR ⊢
    omega
  have hp := evmPot_lt_bound s hi hcap (evmFp_lt s hi)
  apply lt_of_lt_of_eq hp
  exact cap_algebra (2 * maxChain * 2 ^ 64) evmPotF evmPotS


/-- `go = 0` remains a legitimate loop exit after restoring the outer frame globals. -/
def HeadInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ (EvmInv s ∨ locN s "go" = 0)

def rank : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat :=
  fun s => if locN s "go" = 0 then 0 else evmPot s + 1

theorem active_ne {F : Type} {s : PanSemStateFiniteExact 64 F}
    (ha : LoopActive rfCond s) : locN s "go" ≠ 0 :=
  condTrue_local_ne0 ha

theorem active_inv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hi : HeadInv s) (ha : LoopActive rfCond s) : EvmInv s := by
  rcases hi.2 with hi | hz
  · exact hi
  · exact (active_ne ha hz).elim

-- The exact conditional goal, with contract types defined above from frozen rev9.
def GBodyRunFrames : Prop :=
  TerminatingFunBoundedOn FinishReady (ofString "finish_child") K.finish_child →
  TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.frame_epilogue →
  TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.frame_exception →
  TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.op_dispatch →
  FinishSpec → EpilogueSpec → ExceptionSpec → DispatchSpec →
  TerminatingFunBoundedOn EvmInv (ofString "run_frames") K.run_frames

theorem gbody_run_frames : GBodyRunFrames := by
  intro bf be bx bd hf he hx hd
  have hb : TerminatingProgBoundedOn (fun s => HeadInv s ∧ LoopActive rfCond s)
      rfBody (walkCost rfBody) := by
    intro F s hc hi
    have hkey := body_walk bf be bx bd hd hx he hf rfCond rfBody rfLoop_eq s hc
      (active_inv hi.1 hi.2)
    exact hkey.bounded s hc ⟨active_inv hi.1 hi.2, rfl, rfl, rfl, rfl⟩
  have hl : TerminatingProgBoundedOn HeadInv (.while rfCond rfBody)
      ((evmPotMax + 1) * (walkCost rfBody + 1)) := by
    refine TerminatingProgBoundedOn.while_rank_stationary_active (P := HeadInv) (N := evmPotMax) rank ?_ hb ?_ ?_
    · intro F s hi
      exact ⟨guestInv_congr (s := s) rfl rfl rfl rfl hi.1,
        hi.2.elim (fun h => Or.inl (localsFree_evmInv s _ _ h)) (fun h => Or.inr h)⟩
    · intro F s hc hi ha
      have hp := potential_bounded s (active_inv hi ha)
      simp only [rank, if_neg (active_ne ha)]
      omega
    · intro F s hc hi ha hflow
      have hs := runStep bf be bx bd hd hx he hf rfCond rfBody rfLoop_eq s hc
        (active_inv hi ha) ha hflow
      have hg := guestInv_evaluate (decClockHOLFinite s) rfBody
        (guestInv_congr (s := s) rfl rfl rfl rfl hi.1)
      rcases hs with ⟨hpost, hp⟩ | hz
      · refine ⟨⟨hg, Or.inl hpost⟩, Or.inl ?_⟩
        simp only [rank, if_neg (active_ne ha)]
        split <;> omega
      · refine ⟨⟨hg, Or.inr hz⟩, Or.inl ?_⟩
        simp only [rank, if_pos hz, if_neg (active_ne ha)]
        omega
  have hseq : TerminatingProgBoundedOn HeadInv _ _ := TerminatingProgBoundedOn.seq_guestInv_after hl (fun _ hi => hi.1)
    (TerminatingProgBoundedOn.of_clock (fun s => clock_return s (.const 0)))
  have hseq' : TerminatingProgBoundedOn EvmInv
      (.seq (.while rfCond rfBody) (.return (.const 0)))
      ((evmPotMax + 1) * (walkCost rfBody + 1)) := by
    intro F s hc hi
    simpa only [Nat.add_zero] using hseq s hc ⟨evmInv_guestInv s hi, Or.inl hi⟩
  refine ⟨[], rfCode, .one, lookup_run_frames, ?_⟩
  rw [rfCode_eq]
  have hb : TerminatingProgBoundedOn EvmInv _ _ := TerminatingProgBoundedOn.dec_on localsFree_evmInv
    (ofString "go") .one (.const 1) hseq'
  intro F u hc hi
  simpa only [K.run_frames, rfCost_eq] using hb u hc hi


end InitECandidate.Solver.Wave8GuestInv.GuardedBody
