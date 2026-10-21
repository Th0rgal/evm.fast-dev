import InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
import InitECandidate.Solver.SaltedLinearGasEnvelopeAndSeventyEightBudgetBridge
import InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# StackRemoveZeroExtraClockSaltedGasAndSeventyEightBudgetBridge

Wave 5 bridge (W5_216). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.StackRemoveZeroExtraClockSaltedGasAndSeventyEightBudgetBridge

open InitECandidate.Solver.SaltedLinearGasEnvelopeAndSeventyEightBudgetBridge
open InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Every non-stub body compiled from Pancake reaches StackRemove storeConsts-free. -/
theorem panToStackAlloc_bodies_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (info : Flapjack.Spt Nat) :
    ∀ y ∈ (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
        (Flapjack.Compiler.Backend.WordToWord.compile wc ac
          (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = Flapjack.storeConstsStubLocation ∨
      InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt
        (Flapjack.Compiler.Backend.StackAlloc.progComp
          (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2 = true :=
  InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Pancake.panToStackAlloc_bodies_StackNoSt
    arch prog wc ac perf info

/-- 2. StackNoSt rejects storeConsts and CodeNoSt fails as soon as one code entry holds it. -/
theorem rejects_storeConsts_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (a b : Nat) (c : Option Nat)
    (s : Flapjack.StackSemStateFiniteExact width C F) (k : Nat)
    (hk : Flapjack.sptLookup k s.code =
      some (.storeConsts a b c : Flapjack.Compiler.Backend.StackLang.HolProg width)) :
    InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt
      (.storeConsts a b c : Flapjack.Compiler.Backend.StackLang.HolProg width) = false ∧
    ¬ InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CodeNoSt s :=
  ⟨InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Pancake.stackNoSt_rejects_storeConsts
      a b c,
   InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Pancake.codeNoSt_rejects
      s k a b c hk⟩

/-- 3. ClockOk allows one tick only on a final halt: one tick on none is rejected, and two ticks
are rejected even on halt. -/
theorem clockOk_tight_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] (w : Flapjack.WordLocW width) :
    ¬ InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.ClockOk (width := width) 1 none ∧
    ¬ InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.ClockOk 2 (some (.halt w)) :=
  ⟨InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Pancake.clockOk_rejects_one_none,
   InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Pancake.clockOk_rejects_two_halt w⟩

/-- 4. Salted main totals: 102_485_906_743 passes 8x and 154_766_000_267 passes 5x. -/
theorem salted_totals_seventy_eight_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.salted200 =
        102485906743 ∧
    InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.salted380 =
        154766000267 :=
  ⟨salted_totals_and_slopes_bridge_non_vacuous_and_tight.1,
   salted_totals_and_slopes_bridge_non_vacuous_and_tight.2.2.1⟩

/-- 5. The salt alone removes 98_000_000_000 (200M) and 357_200_000_000 (380M), and the verdicts
survive up to 6_052 and 7_678 ticks per unit. -/
theorem salt_gain_and_slack_seventy_eight_bridge_non_vacuous_and_tight :
    (100000000000 - 2000000000 = 98000000000 ∧
      361000000000 - 3800000000 = 357200000000) ∧
    (8 * (200485906743 - 100000000000 + 6052 * 2000000) < yukon ∧
      5 * (511966000267 - 361000000000 + 7678 * 3800000) < yukon) :=
  salt_gain_and_slack_bridge_non_vacuous_and_tight

/-- 6. Salted gas envelopes: 58_088_992_805 at 200M and 110_369_086_329 at 380M. -/
theorem salted_env_seventy_eight_bridge_non_vacuous_and_tight :
    156088992805 - 100000000000 + 2000000000 = 58088992805 ∧
    467569086329 - 361000000000 + 3800000000 = 110369086329 :=
  salted_env_bridge_non_vacuous_and_tight

/-- 7. The 78-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem seventy_eight_portfolio_zero_extra_clock_bridge_non_vacuous_and_tight :
    SeventyEightShape ∧ yukon = 900719925474 ∧
    CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.portfolio.length = 78 ∧
    (∀ K ∈ CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.portfolio, K < yukon) :=
  seventy_eight_portfolio_under_yukon_non_vacuous_and_tight

/-- 8. Every one of the 78 budgets carries a finite certificate, from one base certificate. -/
theorem seventy_eight_certificates_zero_extra_clock_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventyEightShape ∧
    (∀ K ∈ CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  seventy_eight_certificates_bridge_non_vacuous_and_tight cert

/-- 9. End to end: every non-stub Pancake body simulates with zero extra clock, except at most
one tick on a final halt. -/
theorem panToStackRemove_body_zeroExtraClock_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (info : Flapjack.Spt Nat) :
    ∀ y ∈ (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
        (Flapjack.Compiler.Backend.WordToWord.compile wc ac
          (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = Flapjack.storeConstsStubLocation ∨
      ∀ (source : Flapjack.StackSemStateFiniteExact width C F)
        (result : Option (Flapjack.StackSemResult width))
        (postSource target : Flapjack.StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool),
        InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CodeNoSt source →
        Flapjack.StackSemEvaluate.evaluate
            ((Flapjack.Compiler.Backend.StackAlloc.progComp
              (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target ∧
          Flapjack.Compiler.Backend.StackProps.regBound
            (Flapjack.Compiler.Backend.StackAlloc.progComp
              (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2 pointer →
        ∃ clock postTarget,
          InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.ClockOk clock result ∧
          Flapjack.StackSemEvaluate.evaluate
            (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
              (Flapjack.Compiler.Backend.StackAlloc.progComp
                (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2,
              {target with clock := clock + target.clock}) = (result, postTarget) :=
  InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Pancake.panToStackRemove_body_zeroExtraClock
    arch prog wc ac perf info

/-- 10. Grand bridge: zero extra clock on every non-stub body, both salted totals under Yukon,
and the 78-budget portfolio with finite certificates. -/
theorem stack_remove_zero_extra_clock_salted_gas_and_seventy_eight_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (info : Flapjack.Spt Nat)
    (cert : CertificateAt 1212035192) :
    (∀ y ∈ (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
        (Flapjack.Compiler.Backend.WordToWord.compile wc ac
          (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = Flapjack.storeConstsStubLocation ∨
      InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt
        (Flapjack.Compiler.Backend.StackAlloc.progComp
          (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2 = true) ∧
    (InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.salted200 =
        102485906743 ∧
      InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.salted380 =
        154766000267) ∧
    (SeventyEightShape ∧
      ∀ K ∈ CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨panToStackAlloc_bodies_bridge_non_vacuous_and_tight arch prog wc ac perf info,
   ⟨salted_totals_and_slopes_bridge_non_vacuous_and_tight.1,
    salted_totals_and_slopes_bridge_non_vacuous_and_tight.2.2.1⟩,
   seventy_eight_certificates_bridge_non_vacuous_and_tight cert⟩

end InitECandidate.Solver.StackRemoveZeroExtraClockSaltedGasAndSeventyEightBudgetBridge
