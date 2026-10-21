import InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
import InitECandidate.Solver.SszOffsetWitnessStackAllocAndNinetyBudgetCampaignBridge
import InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.StackAllocIdentityAndNinetyTwoBudgetCampaignBridge

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (NoStubCall Clean)
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock (CodeNoSt ClockOk)
open InitECandidate.Solver.StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock (
  noSt_initStubs
  initCode_clock_preserved
  storeConstsStub_not_noSt
)
open InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt (
  stackAllocSections
  liveSections
  stackAllocSections_clean
  stackAllocSections_noSt_and_noStubCall
  liveTable_lookup_noSt
  codeNoSt_liveTable
  codeNoSt_liveTable_emptyOracle
  liveTable_lookup_six
  panToStackRemove_body_zeroExtraClock_liveTable
  fullTable_has_label6
)
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc (
  StackNoAlloc
)
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural (
  NoGcCall
  NoTailHandler
  gcStubLocation_eq
  stackAllocComp_id
  stackAllocComp_drops_tail_handler
  panToStackRawCall_noAlloc_unconditional
  panToStackAlloc_noAlloc_noGcCall
  panToStackRemove_noAlloc_noGc_zeroExtraClock
  alloc_not_noAlloc
  stackAlloc_alloc_calls_gc
  noGcCall_rejects_gc
)
open InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall (
  rawCallSections
  panToStackRawCall_noGcCall_unconditional
  panToStackAlloc_noAlloc_noGcCall_unconditional
  panToStackRawCall_noTailHandler
  panToStackRawCall_noSt_ne_six
  panToStackAlloc_progComp_eq_id_of_ne_six
  stackAlloc_not_id_on_tagged_storeConsts
  pancake_stackAllocIdentity_noGc_zeroExtraClock
)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster (
  inputBytes
  keccakBlocks
  jointCost
  jointPrev
  jointSsz
  main200
  main380
  joint_bound
  joint_tight
  joint_val
  main200_slope
  main380_slope
  margins
  sixty_eight_gap
)
open InitECandidate.Solver.SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster (
  NinetyShape
)
open InitECandidate.Solver.SszOffsetWitnessStackAllocAndNinetyBudgetCampaignBridge (
  ssz_offset_witness_joint_bound_tight_and_val_non_vacuous_and_tight
  ssz_offset_main200_67x_main380_41x_margins_and_gap_non_vacuous_and_tight
  witness_progression_from_36x_56x_60x_to_ssz_67x_non_vacuous_and_tight
  stack_alloc_no_gc_and_ssz_offset_witness_joint_bridge_non_vacuous_and_tight
  pan_to_stack_remove_no_gc_and_ssz_offset_slopes_bridge_non_vacuous_and_tight
  init_memory_zero_clock_no_gc_and_ssz_offset_margins_bridge_non_vacuous_and_tight
  ninety_and_eighty_eight_budget_portfolio_hierarchy_non_vacuous_and_tight
  ninety_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
  ssz_offset_witness_sixty_seven_x_and_ninety_budget_certificates_non_vacuous_and_tight
  grand_ssz_offset_witness_stack_alloc_and_ninety_budget_campaign_bridge_non_vacuous_and_tight
)
open InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster (
  portfolio
  NinetyTwoShape
  ninety_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  ninety_two_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. Exact `StackAlloc.progComp` identity on every `rawCallSections` entry `y` with `y.1 ≠ 6`
(`panToStackAlloc_progComp_eq_id_of_ne_six`), paired with its sharpness witness on tagged
`storeConsts` (`stackAlloc_not_id_on_tagged_storeConsts`) and `.alloc` GC call witness. -/
theorem pan_to_stack_alloc_prog_comp_eq_id_ne_six_and_tagged_store_consts_tight_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m k : Nat) :
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    StackAlloc.comp n m (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m) ∧
    NoGcCall (StackAlloc.comp n m (.alloc k : HolProg width)).1 = false :=
  ⟨panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf,
   panToStackAlloc_noAlloc_noGcCall_unconditional arch prog wc ac perf,
   stackAlloc_not_id_on_tagged_storeConsts n m,
   stackAlloc_alloc_calls_gc n m k⟩

/-- 2. Unconditional `NoGcCall`, `NoTailHandler`, and `StackNoSt` (for `y.1 ≠ 6`) across
`rawCallSections`, paired with `stackAlloc_not_id_on_tagged_storeConsts` and
`stackAllocComp_drops_tail_handler`. -/
theorem raw_call_sections_unconditional_invariants_and_tightness_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m k1 k2 : Nat) (d : Sum Nat Nat) (q : HolProg width) :
    (∀ y ∈ rawCallSections arch prog wc ac perf, NoGcCall y.2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, NoTailHandler y.2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackNoSt y.2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
    StackAlloc.comp n m (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m) ∧
    StackAlloc.comp n m (.call none d (some (q, k1, k2))) = (.call none d none, m) :=
  ⟨panToStackRawCall_noGcCall_unconditional arch prog wc ac perf,
   panToStackRawCall_noTailHandler arch prog wc ac perf,
   panToStackRawCall_noSt_ne_six arch prog wc ac perf,
   panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf,
   stackAlloc_not_id_on_tagged_storeConsts n m,
   stackAllocComp_drops_tail_handler n m d q k1 k2⟩

/-- 3. Master `pancake_stackAllocIdentity_noGc_zeroExtraClock` paired with
`stackAlloc_not_id_on_tagged_storeConsts`, `stackAlloc_alloc_calls_gc`, and
`storeConstsStub_not_noSt`. -/
theorem pancake_stack_alloc_identity_no_gc_zero_extra_clock_non_vacuous_and_tight {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (n m k : Nat) :
    ((∀ y ∈ rawCallSections arch prog wc ac perf,
        StackNoAlloc y.2 = true ∧ NoGcCall y.2 = true) ∧
     (∀ y ∈ rawCallSections arch prog wc ac perf,
        StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
     (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
        StackAlloc.progComp y = y) ∧
     (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
       y.1 = storeConstsStubLocation ∨
       ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
         (postSource target : StackSemStateFiniteExact width C F)
         (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
         source.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)) →
         (∀ i, ∀ e ∈ (source.compileOracle i).2.1, StackNoSt e.2 = true) →
         StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
             (result, postSource) ∧ result ≠ some .error ∧
           StackRemove.stateRelHOL j bd ptr source target ∧
           StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
         ∃ clock postTarget, ClockOk clock result ∧
           StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
             (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
             {target with clock := clock + target.clock}) = (result, postTarget))) ∧
    StackAlloc.comp n m (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m) ∧
    NoGcCall (StackAlloc.comp n m (.alloc k : HolProg width)).1 = false ∧
    StackNoSt (storeConstsStubNative (width := width) k) = false :=
  ⟨pancake_stackAllocIdentity_noGc_zeroExtraClock arch prog wc ac perf dc info,
   stackAlloc_not_id_on_tagged_storeConsts n m,
   stackAlloc_alloc_calls_gc n m k,
   storeConstsStub_not_noSt k⟩

/-- 4. `panToStackAlloc_progComp_eq_id_of_ne_six` and `stackAlloc_not_id_on_tagged_storeConsts`
bridged with SSZ-offset witness byte-conservation (`ssz_offset_witness_joint_bound_tight_and_val_non_vacuous_and_tight`)
and `67×` / `41×` slopes (`ssz_offset_main200_67x_main380_41x_margins_and_gap_non_vacuous_and_tight`). -/
theorem stack_alloc_identity_and_ssz_offset_witness_bounds_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m_loc : Nat) (m n2 n17 h : Nat) (hb : 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤ inputBytes) :
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
    StackAlloc.comp n m_loc (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m_loc) ∧
    (jointCost m n2 n17 h ≤ 90 * (inputBytes / 4) ∧
     (4 * 33554428 ≤ inputBytes ∧ jointCost 33554428 0 0 0 = 3019898520 ∧
       138 * 4 < 90 * 7) ∧
     (jointSsz = 3038649506 ∧ jointPrev - jointSsz = 1610612544)) ∧
    ((main200 = 13378055156 ∧ 67 * main200 < yukon ∧ yukon < 68 * main200) ∧
     (main380 = 21485139986 ∧ 41 * main380 < yukon ∧ yukon < 42 * main380) ∧
     (yukon - 67 * main200 = 4390230022 ∧ yukon - 41 * main380 = 19829186048) ∧
     (yukon / 68 = 13245881256 ∧ main200 - yukon / 68 = 132173900)) :=
  ⟨panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf,
   stackAlloc_not_id_on_tagged_storeConsts n m_loc,
   ssz_offset_witness_joint_bound_tight_and_val_non_vacuous_and_tight m n2 n17 h hb,
   ssz_offset_main200_67x_main380_41x_margins_and_gap_non_vacuous_and_tight⟩

/-- 5. `pancake_stackAllocIdentity_noGc_zeroExtraClock` unified with
`witness_progression_from_36x_56x_60x_to_ssz_67x_non_vacuous_and_tight` from
`SszOffsetWitnessStackAllocAndNinetyBudgetCampaignBridge`. -/
theorem stack_alloc_identity_and_witness_progression_36x_to_67x_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m_loc : Nat)
    (h_ref : Nat)
    (hb_ref : 33 * h_ref ≤ GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.inputBytes)
    (n2_arity n17_arity h_arity : Nat)
    (hb_arity : 4 * n2_arity + 18 * n17_arity + 32 * h_arity ≤
      GuestJointRlpArityByteConservationAndFiftyXMaster.inputBytes)
    (m_sh n2_sh n17_sh h_sh : Nat)
    (hb_sh : 4 * m_sh + 4 * n2_sh + 18 * n17_sh + 32 * h_sh ≤
      GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.inputBytes)
    (m n2 n17 h : Nat) (hb : 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤ inputBytes) :
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
    StackAlloc.comp n m_loc (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m_loc) ∧
    (((h_ref ≤ 4067203 ∧
       (33 * 4067203 ≤ GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.inputBytes ∧
        GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.inputBytes < 33 * 4067204) ∧
       (132 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.hashRefs ≤ 16 * 33554428 ∧
        16 * 33554428 < 133 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.hashRefs) ∧
       (2 * 8 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.hashRefs < 2 * 8 * 1110441952)) ∧
      ((GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 24381873932 ∧
        36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 < yukon ∧
        yukon < 37 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200) ∧
       (GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 32488958762 ∧
        27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 < yukon ∧
        yukon < 28 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380) ∧
       (yukon - 36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 22972463922 ∧
        yukon - 27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 23518038900)) ∧
      GuestJointRlpArityByteConservationAndFiftyXMaster.jointCost n2_arity n17_arity h_arity ≤ 2430831895 ∧
      ((4 * 2 + 18 * 7456539 + 32 * 0 ≤
          GuestJointRlpArityByteConservationAndFiftyXMaster.inputBytes ∧
        GuestJointRlpArityByteConservationAndFiftyXMaster.jointCost 2 7456539 0 = 2430831810 ∧
        2430831895 - 2430831810 = 85 ∧
        GuestJointRlpArityByteConservationAndFiftyXMaster.inputBytes < 18 * 7456540) ∧
       (GuestJointRlpArityByteConservationAndFiftyXMaster.inputBytes / 18 = 7456539 ∧
        9 * 7456539 ≤ 2 * 33554428)) ∧
      (GuestJointRlpArityByteConservationAndFiftyXMaster.decodeProbesOld -
         GuestJointRlpArityByteConservationAndFiftyXMaster.decodeProbesNew = 8572986881) ∧
      (GuestJointRlpArityByteConservationAndFiftyXMaster.main200 = 15808887051 ∧
       56 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 < yukon ∧
       yukon < 57 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 ∧
       50 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 < yukon) ∧
      (GuestJointRlpArityByteConservationAndFiftyXMaster.main380 = 23915971881 ∧
       37 * GuestJointRlpArityByteConservationAndFiftyXMaster.main380 < yukon ∧
       yukon < 38 * GuestJointRlpArityByteConservationAndFiftyXMaster.main380) ∧
      ((yukon - 56 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 = 15422250618 ∧
        yukon - 37 * GuestJointRlpArityByteConservationAndFiftyXMaster.main380 = 15828965877) ∧
       (100 * 3038649506 > 19 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 ∧
        3038649506 > GuestJointRlpArityByteConservationAndFiftyXMaster.decodeProbesNew))) ∧
     GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.jointCost m_sh n2_sh n17_sh h_sh ≤
       138 * (GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.inputBytes / 4) ∧
     (GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200 = 14988667700 ∧
      60 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200 < yukon ∧
      yukon < 61 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200) ∧
     (GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380 = 23095752530 ∧
      38 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380 < yukon ∧
      yukon < 39 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380) ∧
     jointCost m n2 n17 h ≤ 90 * (inputBytes / 4) ∧
     (main200 = 13378055156 ∧ 67 * main200 < yukon ∧ yukon < 68 * main200) ∧
     (main380 = 21485139986 ∧ 41 * main380 < yukon ∧ yukon < 42 * main380)) :=
  ⟨panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf,
   stackAlloc_not_id_on_tagged_storeConsts n m_loc,
   witness_progression_from_36x_56x_60x_to_ssz_67x_non_vacuous_and_tight
     h_ref hb_ref n2_arity n17_arity h_arity hb_arity m_sh n2_sh n17_sh h_sh hb_sh m n2 n17 h hb⟩

/-- 6. `pancake_stackAllocIdentity_noGc_zeroExtraClock` unified with
`init_memory_zero_clock_no_gc_and_ssz_offset_margins_bridge_non_vacuous_and_tight`. -/
theorem stack_alloc_identity_init_memory_zero_clock_and_ssz_margins_bridge_non_vacuous_and_tight
    {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (generateGc : Bool) (maximumHeap pointer start n m_loc k : Nat)
    (m n2 n17 h : Nat) (hb : 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤ inputBytes) :
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      StackNoAlloc y.2 = true ∧ NoGcCall y.2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
    StackAlloc.comp n m_loc (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m_loc) ∧
    (((∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true) ∧
      (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
        NoGcCall y.2 = true →
        StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
      NoGcCall (StackAlloc.comp n m_loc (.alloc k : HolProg width)).1 = false ∧
      (((∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
        (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
          StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
          t.clock = s.clock) ∧
        (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
          y.1 = storeConstsStubLocation ∨
          ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
            (postSource target : StackSemStateFiniteExact width C F)
            (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
            source.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)) →
            (∀ i, ∀ e ∈ (source.compileOracle i).2.1, StackNoSt e.2 = true) →
            StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
                (result, postSource) ∧ result ≠ some .error ∧
              StackRemove.stateRelHOL j bd ptr source target ∧
              StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
            ∃ clock postTarget, ClockOk clock result ∧
              StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
                (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
                {target with clock := clock + target.clock}) = (result, postTarget)) ∧
        StackNoSt (storeConstsStubNative (width := width) k) = false) ∧
       (2 * 8 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.hashRefs = 65075248 ∧
        GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.probes 200000000 = 66675248 ∧
        GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.probes 380000000 = 68115248) ∧
       (8589933568 - GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.probes 200000000 = 8523258320) ∧
       (yukon - 36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 22972463922 ∧
        yukon - 27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 23518038900) ∧
       (100 * 10938743528 > 44 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200)) ∧
      (GuestJointRlpArityByteConservationAndFiftyXMaster.main200 = 15808887051 ∧
       56 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 < yukon ∧
       yukon < 57 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 ∧
       50 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 < yukon) ∧
      (GuestJointRlpArityByteConservationAndFiftyXMaster.main380 = 23915971881 ∧
       37 * GuestJointRlpArityByteConservationAndFiftyXMaster.main380 < yukon ∧
       yukon < 38 * GuestJointRlpArityByteConservationAndFiftyXMaster.main380)) ∧
     jointCost m n2 n17 h ≤ 90 * (inputBytes / 4) ∧
     (4 * 33554428 ≤ inputBytes ∧ jointCost 33554428 0 0 0 = 3019898520 ∧
       138 * 4 < 90 * 7) ∧
     (jointSsz = 3038649506 ∧ jointPrev - jointSsz = 1610612544) ∧
     (main200 = 13378055156 ∧ 67 * main200 < yukon ∧ yukon < 68 * main200) ∧
     (main380 = 21485139986 ∧ 41 * main380 < yukon ∧ yukon < 42 * main380) ∧
     (yukon - 67 * main200 = 4390230022 ∧ yukon - 41 * main380 = 19829186048) ∧
     (yukon / 68 = 13245881256 ∧ main200 - yukon / 68 = 132173900)) :=
  have hid := pancake_stackAllocIdentity_noGc_zeroExtraClock (C := C) (F := F) arch prog wc ac perf dc info
  ⟨hid.1,
   hid.2.1,
   hid.2.2.1,
   stackAlloc_not_id_on_tagged_storeConsts n m_loc,
   init_memory_zero_clock_no_gc_and_ssz_offset_margins_bridge_non_vacuous_and_tight
     arch prog wc ac perf dc info generateGc maximumHeap pointer start n m_loc k m n2 n17 h hb⟩

/-- 7. Strictly increasing 92-budget portfolio (`NinetyTwoShape`), all `< 900_719_925_474`,
extending the 90-budget (`NinetyShape`) and 88-budget campaign hierarchy. -/
theorem ninety_two_and_ninety_budget_portfolio_hierarchy_non_vacuous_and_tight :
    NinetyTwoShape ∧
    portfolio.length = 92 ∧
    portfolio.Pairwise (· < ·) ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    portfolio.drop 90 = [880629318301, 880629318302] ∧
    portfolio.getLast? = some 880629318302 ∧
    NinetyShape :=
  have h92 := ninety_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h90 := ninety_and_eighty_eight_budget_portfolio_hierarchy_non_vacuous_and_tight
  ⟨h92,
   h92.1,
   h92.2.1,
   h92.2.2.1,
   h92.2.2.2.2.1,
   h92.2.2.2.2.2.1,
   h90.1⟩

/-- 8. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)` across
all 92 budgets, with explicit endpoint certificates at `880_629_318_301` and `880_629_318_302`. -/
theorem ninety_two_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetyTwoShape ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK 880629318301) (.finite 880629318301) ∧
    InitE.Certificate (baselineWithFiniteK 880629318302) (.finite 880629318302) :=
  have hcert := ninety_two_budget_certificates_non_vacuous_and_tight cert
  ⟨hcert.1,
   hcert.1.2.2.1,
   hcert.2,
   hcert.2 880629318301 (by decide),
   hcert.2 880629318302 (by decide)⟩

/-- 9. Synthesis of `PanToStackAllocIdentityAndUnconditionalNoGcCall`
(`panToStackAlloc_progComp_eq_id_of_ne_six`, `stackAlloc_not_id_on_tagged_storeConsts`,
`panToStackAlloc_noAlloc_noGcCall_unconditional`), SSZ-offset witness bounds, and the 92-budget
conditional certificate portfolio (`NinetyTwoShape`). -/
theorem stack_alloc_identity_ssz_offset_and_ninety_two_budget_certificates_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m_loc : Nat) (m n2 n17 h : Nat) (hb : 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤ inputBytes)
    (cert : CertificateAt 1212035192) :
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    StackAlloc.comp n m_loc (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m_loc) ∧
    (jointCost m n2 n17 h ≤ 90 * (inputBytes / 4) ∧
     (4 * 33554428 ≤ inputBytes ∧ jointCost 33554428 0 0 0 = 3019898520 ∧
       138 * 4 < 90 * 7) ∧
     (jointSsz = 3038649506 ∧ jointPrev - jointSsz = 1610612544) ∧
     (main200 = 13378055156 ∧ 67 * main200 < yukon ∧ yukon < 68 * main200) ∧
     (main380 = 21485139986 ∧ 41 * main380 < yukon ∧ yukon < 42 * main380) ∧
     (yukon - 67 * main200 = 4390230022 ∧ yukon - 41 * main380 = 19829186048) ∧
     (yukon / 68 = 13245881256 ∧ main200 - yukon / 68 = 132173900) ∧
     (NinetyShape ∧
       ∀ K ∈ SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster.portfolio,
         InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
    (NinetyTwoShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf,
   panToStackAlloc_noAlloc_noGcCall_unconditional arch prog wc ac perf,
   stackAlloc_not_id_on_tagged_storeConsts n m_loc,
   ssz_offset_witness_sixty_seven_x_and_ninety_budget_certificates_non_vacuous_and_tight
     m n2 n17 h hb cert,
   ninety_two_budget_certificates_non_vacuous_and_tight cert⟩

/-- 10. Grand campaign bridge unifying `PanToStackAllocIdentityAndUnconditionalNoGcCall`
(`panToStackAlloc_progComp_eq_id_of_ne_six`, `stackAlloc_not_id_on_tagged_storeConsts`,
`pancake_stackAllocIdentity_noGc_zeroExtraClock`),
`SszOffsetWitnessStackAllocAndNinetyBudgetCampaignBridge`, and
`SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster` (`NinetyTwoShape` and 92 finite certificates). -/
theorem grand_stack_alloc_identity_and_ninety_two_budget_campaign_bridge_non_vacuous_and_tight
    {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (generateGc : Bool) (maximumHeap pointer start n m_loc k_stub h_ref : Nat)
    (hb_ref : 33 * h_ref ≤ GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.inputBytes)
    (m n2 n17 h : Nat) (hb : 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤ inputBytes)
    (p : HolProg width) (ha : StackNoAlloc p = true) (hs : StackNoSt p = true)
    (ht : NoTailHandler p = true)
    (w : WordLocW width) (cert : CertificateAt 1212035192) :
    ((∀ y ∈ rawCallSections arch prog wc ac perf,
        StackNoAlloc y.2 = true ∧ NoGcCall y.2 = true) ∧
     (∀ y ∈ rawCallSections arch prog wc ac perf,
        StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
     (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
        StackAlloc.progComp y = y) ∧
     (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
       y.1 = storeConstsStubLocation ∨
       ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
         (postSource target : StackSemStateFiniteExact width C F)
         (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
         source.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)) →
         (∀ i, ∀ e ∈ (source.compileOracle i).2.1, StackNoSt e.2 = true) →
         StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
             (result, postSource) ∧ result ≠ some .error ∧
           StackRemove.stateRelHOL j bd ptr source target ∧
           StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
         ∃ clock postTarget, ClockOk clock result ∧
           StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
             (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
             {target with clock := clock + target.clock}) = (result, postTarget))) ∧
    StackAlloc.comp n m_loc (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m_loc) ∧
    (jointCost m n2 n17 h ≤ 90 * (inputBytes / 4) ∧
     (4 * 33554428 ≤ inputBytes ∧ jointCost 33554428 0 0 0 = 3019898520 ∧
       138 * 4 < 90 * 7) ∧
     (jointSsz = 3038649506 ∧ jointPrev - jointSsz = 1610612544) ∧
     (main200 = 13378055156 ∧ 67 * main200 < yukon ∧ yukon < 68 * main200) ∧
     (main380 = 21485139986 ∧ 41 * main380 < yukon ∧ yukon < 42 * main380) ∧
     (yukon - 67 * main200 = 4390230022 ∧ yukon - 41 * main380 = 19829186048) ∧
     (yukon / 68 = 13245881256 ∧ main200 - yukon / 68 = 132173900)) ∧
    StackAlloc.comp n m_loc p = (p, m_loc) ∧
    NoGcCall (StackAlloc.comp n m_loc (.alloc k_stub : HolProg width)).1 = false ∧
    ((∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
     (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
       StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
       t.clock = s.clock) ∧
     StackNoSt (storeConstsStubNative (width := width) k_stub) = false ∧
     (¬ ClockOk (width := width) 1 none ∧ ¬ ClockOk 2 (some (.halt w)))) ∧
    (NinetyShape ∧
     NinetyTwoShape ∧
     portfolio.length = 92 ∧
     portfolio.Pairwise (· < ·) ∧
     (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
     (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) :=
  have hcert92 := ninety_two_budget_certificates_non_vacuous_and_tight cert
  have hg90 := grand_ssz_offset_witness_stack_alloc_and_ninety_budget_campaign_bridge_non_vacuous_and_tight
    (C := C) (F := F) arch prog wc ac perf dc info generateGc maximumHeap pointer start n m_loc k_stub h_ref hb_ref m n2 n17 h hb p ha hs ht w cert
  ⟨pancake_stackAllocIdentity_noGc_zeroExtraClock arch prog wc ac perf dc info,
   stackAlloc_not_id_on_tagged_storeConsts n m_loc,
   hg90.1,
   hg90.2.2.1,
   hg90.2.2.2.1,
   hg90.2.2.2.2.1,
   ⟨hg90.2.2.2.2.2.2.1,
    hcert92.1,
    hcert92.1.1,
    hcert92.1.2.1,
    hcert92.1.2.2.1,
    hcert92.2⟩⟩

#print axioms pan_to_stack_alloc_prog_comp_eq_id_ne_six_and_tagged_store_consts_tight_non_vacuous_and_tight
#print axioms raw_call_sections_unconditional_invariants_and_tightness_non_vacuous_and_tight
#print axioms pancake_stack_alloc_identity_no_gc_zero_extra_clock_non_vacuous_and_tight
#print axioms stack_alloc_identity_and_ssz_offset_witness_bounds_bridge_non_vacuous_and_tight
#print axioms stack_alloc_identity_and_witness_progression_36x_to_67x_bridge_non_vacuous_and_tight
#print axioms stack_alloc_identity_init_memory_zero_clock_and_ssz_margins_bridge_non_vacuous_and_tight
#print axioms ninety_two_and_ninety_budget_portfolio_hierarchy_non_vacuous_and_tight
#print axioms ninety_two_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
#print axioms stack_alloc_identity_ssz_offset_and_ninety_two_budget_certificates_non_vacuous_and_tight
#print axioms grand_stack_alloc_identity_and_ninety_two_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.StackAllocIdentityAndNinetyTwoBudgetCampaignBridge
