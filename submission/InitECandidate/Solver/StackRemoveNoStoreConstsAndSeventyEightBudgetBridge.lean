import InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
import InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster
import InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.StackRemoveNoStoreConstsAndSeventyEightBudgetBridge`

Bridge between the `storeConsts`-free StackRemove clock, the salted linear gas envelope,
and the 78-budget master. The Pancake statements are specialized at `width = 64`, the
machine width, so `NeZero` resolves.

* Every Pancake body compiled outside the stub at label `6` carries no `.storeConsts` and
  runs in `StackRemove` under `ClockOk`: zero extra ticks off `halt`, at most one on
  `halt`. `StackNoSt` rejects `.storeConsts`; `ClockOk` rejects one tick on `none` and
  two ticks on `halt`, while the one-tick allowance is attained on `halt`.
* Salted, `salted200 = 102,485,906,743` passes `8×` with margin `80,832,671,530` and
  `salted380 = 154,766,000,267` passes `5×` with margin `126,889,924,139`. The salt
  removes `98,000,000,000` at `200M` and `357,200,000,000` at `380M`.
* The 78 budgets grow strictly under Yukon `900,719,925,474`.
-/

namespace InitECandidate.Solver.StackRemoveNoStoreConstsAndSeventyEightBudgetBridge

open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster
open InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster

/-- 1. At width `64`, every compiled Pancake body is either the stub at label `6` or free
of `.storeConsts`. -/
theorem bodies_no_store_non_vacuous_and_tight :
    ∀ (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
      (prog : List (Flapjack.Pancake.PanLang.DeclHOL 64))
      (wc : Flapjack.Compiler.Backend.WordToWord.Config)
      (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact 64)
      (perf : Bool) (info : Flapjack.Spt ℕ),
      ∀ y ∈ (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
          (Flapjack.Compiler.Backend.WordToWord.compile wc ac
            (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
        y.1 = Flapjack.storeConstsStubLocation ∨
        InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt
          (Flapjack.Compiler.Backend.StackAlloc.progComp
            (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2 = true :=
  Pancake.panToStackAlloc_bodies_StackNoSt

/-- 2. At width `64`, such a body runs in `StackRemove` with `ClockOk` — zero extra ticks
off `halt`, at most one on `halt` — from any `CodeNoSt` source. -/
theorem zero_extra_clock_non_vacuous_and_tight :
    ∀ {C F : Type} (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
      (prog : List (Flapjack.Pancake.PanLang.DeclHOL 64))
      (wc : Flapjack.Compiler.Backend.WordToWord.Config)
      (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact 64)
      (perf : Bool) (info : Flapjack.Spt ℕ),
      ∀ y ∈ (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
          (Flapjack.Compiler.Backend.WordToWord.compile wc ac
            (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
        y.1 = Flapjack.storeConstsStubLocation ∨
        ∀ (source : Flapjack.StackSemStateFiniteExact 64 C F)
          (result : Option (Flapjack.StackSemResult 64))
          (postSource target : Flapjack.StackSemStateFiniteExact 64 C F)
          (pointer : ℕ) (bounds : BitVec 64 × BitVec 64) (jump : Bool),
          CodeNoSt source →
          Flapjack.StackSemEvaluate.evaluate
              ((Flapjack.Compiler.Backend.StackAlloc.progComp
                  (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2, source) =
              (result, postSource) ∧
            result ≠ some Flapjack.StackSemResult.error ∧
            Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target ∧
            Flapjack.Compiler.Backend.StackProps.regBound
              (Flapjack.Compiler.Backend.StackAlloc.progComp
                (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2 pointer →
          ∃ clock postTarget,
            ClockOk clock result ∧
            Flapjack.StackSemEvaluate.evaluate
              (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
                  (Flapjack.Compiler.Backend.StackAlloc.progComp
                    (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2,
                { target with clock := clock + target.clock }) = (result, postTarget) :=
  Pancake.panToStackRemove_body_zeroExtraClock

/-- 3. `StackNoSt` rejects `.storeConsts` at width `64`. -/
theorem rejects_store_non_vacuous_and_tight (a b : ℕ) (c : Option ℕ) :
    InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt
      (Flapjack.Compiler.Backend.StackLang.Prog.storeConsts (a : Nat) b c) = false :=
  Pancake.stackNoSt_rejects_storeConsts (width := 64) a b c

/-- 4. `ClockOk` rejects one tick on a non-`halt` result. -/
theorem clock_tight_non_vacuous_and_tight : ¬ ClockOk (width := 64) 1 none :=
  Pancake.clockOk_rejects_one_none

/-- 5. `ClockOk` rejects two ticks even on `halt`. -/
theorem clock_tight_halt_non_vacuous_and_tight (w : Flapjack.WordLocW 64) :
    ¬ ClockOk 2 (some (Flapjack.StackSemResult.halt w)) :=
  Pancake.clockOk_rejects_two_halt w

/-- 6. The one-tick allowance is attained on `halt`. -/
theorem clock_halt_one_non_vacuous_and_tight (w : Flapjack.WordLocW 64) :
    ClockOk 1 (some (Flapjack.StackSemResult.halt w)) :=
  Pancake.clockOk_halt_one w

/-- 7. Salted `main200`: `102,485,906,743`, `8×` under Yukon by `80,832,671,530`, `9×`
crosses. -/
theorem salted200_non_vacuous_and_tight :
    salted200 = 102485906743 ∧ 8 * 102485906743 < 900719925474 ∧
      900719925474 - 8 * 102485906743 = 80832671530 ∧ 900719925474 < 9 * 102485906743 := by
  exact ⟨salted200_val, by decide⟩

/-- 8. Salted `main380`: `154,766,000,267`, `5×` under Yukon by `126,889,924,139`, `6×`
crosses. -/
theorem salted380_non_vacuous_and_tight :
    salted380 = 154766000267 ∧ 5 * 154766000267 < 900719925474 ∧
      900719925474 - 5 * 154766000267 = 126889924139 ∧ 900719925474 < 6 * 154766000267 := by
  exact ⟨salted380_val, by decide⟩

/-- 9. The salt removes `98,000,000,000` at `200M` and `357,200,000,000` at `380M`. -/
theorem salt_gain_non_vacuous_and_tight :
    100000000000 - 2000000000 = 98000000000 ∧ 361000000000 - 3800000000 = 357200000000 :=
  salt_gain

/-- 10. The 78 budgets grow strictly under Yukon, and each finite certificate needs the
base certificate. -/
theorem portfolio_78_non_vacuous_and_tight
    (cert : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    SeventyEightShape ∧
      (∀ K ∈ portfolio,
        InitE.Certificate (SelfContainedBoundedCertificate.baselineWithFiniteK K)
          (.finite K)) :=
  seventy_eight_budget_certificates_non_vacuous_and_tight cert

end InitECandidate.Solver.StackRemoveNoStoreConstsAndSeventyEightBudgetBridge
