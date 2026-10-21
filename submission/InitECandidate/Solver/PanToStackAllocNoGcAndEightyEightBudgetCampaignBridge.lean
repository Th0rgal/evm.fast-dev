import InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural
import InitECandidate.Solver.ByteCoupledWitnessDeadStub6AndEightyFourBudgetCampaignBridge
import InitECandidate.Solver.JointRlpArityFiftySixXAndEightyEightBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.PanToStackAllocNoGcAndEightyEightBudgetCampaignBridge

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
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster (
  inputBytes
  hashRefs
  probes
  refs_bound
  refs_tight
  ratio
  probe_vals
  decode_dominates
  tree_no_coupling
)
open InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster (
  jointCost
  decodeProbesOld
  decodeProbesNew
)
open InitECandidate.Solver.SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster (
  clockOk_rejects_non_vacuous_and_tight
)
open InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster (
  EightyFourShape
)
open InitECandidate.Solver.ByteCoupledWitnessDeadStub6AndEightyFourBudgetCampaignBridge (
  byte_coupled_refs_bound_tight_and_ratio_non_vacuous_and_tight
  byte_coupled_probe_vals_gain_and_decode_dominates_non_vacuous_and_tight
  byte_coupled_main200_36x_and_main380_27x_slopes_and_margins_non_vacuous_and_tight
  salted_nodedb_to_byte_coupled_witness_progression_non_vacuous_and_tight
  dead_stub6_clean_sections_and_byte_coupled_witness_bridge_non_vacuous_and_tight
  live_table_zero_extra_clock_and_byte_coupled_margins_bridge_non_vacuous_and_tight
  eighty_four_and_eighty_two_budget_portfolio_hierarchy_non_vacuous_and_tight
  eighty_four_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
  byte_coupled_witness_thirty_five_x_and_eighty_four_budget_certificates_non_vacuous_and_tight
  grand_byte_coupled_witness_dead_stub6_and_eighty_four_budget_campaign_bridge_non_vacuous_and_tight
)
open InitECandidate.Solver.JointRlpArityFiftySixXAndEightyEightBudgetMaster (
  portfolio
  EightyEightShape
  joint_tight_and_branch_count_non_vacuous_and_tight
  gain_non_vacuous_and_tight
  main200_slope_non_vacuous_and_tight
  main380_slope_non_vacuous_and_tight
  margins_and_build_dominates_non_vacuous_and_tight
  joint_bound_non_vacuous_and_tight
  eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  eighty_eight_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. Unconditional `StackNoAlloc` across `StackRawCall.compile` (`panToStackRawCall_noAlloc_unconditional`),
GC-free `StackAlloc.progComp` (`panToStackAlloc_noAlloc_noGcCall`), and tightness witnesses
(`alloc_not_noAlloc`, `stackAlloc_alloc_calls_gc`, `noGcCall_rejects_gc`). -/
theorem pan_to_stack_raw_call_no_alloc_and_no_gc_call_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m k : Nat) :
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true) ∧
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      NoGcCall y.2 = true →
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    gcStubLocation = 4 ∧
    StackNoAlloc (.alloc k : HolProg width) = false ∧
    NoGcCall (StackAlloc.comp n m (.alloc k : HolProg width)).1 = false ∧
    NoGcCall (.call none (.inl gcStubLocation) none : HolProg width) = false :=
  ⟨panToStackRawCall_noAlloc_unconditional arch prog wc ac perf,
   panToStackAlloc_noAlloc_noGcCall arch prog wc ac perf,
   gcStubLocation_eq,
   alloc_not_noAlloc k,
   stackAlloc_alloc_calls_gc n m k,
   noGcCall_rejects_gc⟩

/-- 2. Structural identity of `StackAlloc.comp` on `.alloc`/`storeConsts`-free code without tail
handlers (`stackAllocComp_id`), paired with tail-handler erasure (`stackAllocComp_drops_tail_handler`)
and `.alloc` GC call counterexample (`stackAlloc_alloc_calls_gc`). -/
theorem stack_alloc_comp_id_and_alloc_calls_gc_tight_non_vacuous_and_tight
    (n m k k1 k2 : Nat) (d : Sum Nat Nat) (p q : HolProg width)
    (ha : StackNoAlloc p = true) (hs : StackNoSt p = true) (ht : NoTailHandler p = true) :
    StackAlloc.comp n m p = (p, m) ∧
    StackAlloc.comp n m (.call none d (some (q, k1, k2))) = (.call none d none, m) ∧
    NoGcCall (StackAlloc.comp n m (.alloc k : HolProg width)).1 = false ∧
    StackNoAlloc (.alloc k : HolProg width) = false :=
  ⟨stackAllocComp_id n m p ha hs ht,
   stackAllocComp_drops_tail_handler n m d q k1 k2,
   stackAlloc_alloc_calls_gc n m k,
   alloc_not_noAlloc k⟩

/-- 3. End-to-end `panToStackRemove_noAlloc_noGc_zeroExtraClock` master theorem paired with
`stackAlloc_alloc_calls_gc` and `storeConstsStub_not_noSt`. -/
theorem pan_to_stack_remove_no_alloc_no_gc_zero_extra_clock_non_vacuous_and_tight {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (n m k : Nat) :
    ((∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true) ∧
     (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
       NoGcCall y.2 = true →
       StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
     (∀ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 ≠ storeConstsStubLocation →
       StackNoSt e.2 = true ∧ Clean e.2 = true) ∧
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
    NoGcCall (StackAlloc.comp n m (.alloc k : HolProg width)).1 = false ∧
    StackNoSt (storeConstsStubNative (width := width) k) = false :=
  ⟨panToStackRemove_noAlloc_noGc_zeroExtraClock arch prog wc ac perf dc info,
   stackAlloc_alloc_calls_gc n m k,
   storeConstsStub_not_noSt k⟩

/-- 4. Joint RLP arity byte-conservation (`joint_bound`, `joint_tight_and_branch_count`, `gain`,
`main200_slope` at `56×`, `main380_slope` at `37×`, `margins_and_build_dominates`) unified with
byte-coupled witness resolve bounds (`36×` / `27×`) from
`ByteCoupledWitnessDeadStub6AndEightyFourBudgetCampaignBridge`. -/
theorem byte_coupled_36x_to_joint_rlp_arity_56x_progression_non_vacuous_and_tight
    (h_ref : Nat) (hb_ref : 33 * h_ref ≤ inputBytes)
    (n2 n17 h_arity : Nat)
    (hb_arity : 4 * n2 + 18 * n17 + 32 * h_arity ≤
      GuestJointRlpArityByteConservationAndFiftyXMaster.inputBytes) :
    (h_ref ≤ 4067203 ∧
     (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
     (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
     (2 * 8 * hashRefs < 2 * 8 * 1110441952)) ∧
    ((GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 24381873932 ∧
      36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 < yukon ∧
      yukon < 37 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200) ∧
     (GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 32488958762 ∧
      27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 < yukon ∧
      yukon < 28 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380) ∧
     (yukon - 36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 22972463922 ∧
      yukon - 27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 23518038900)) ∧
    jointCost n2 n17 h_arity ≤ 2430831895 ∧
    ((4 * 2 + 18 * 7456539 + 32 * 0 ≤
        GuestJointRlpArityByteConservationAndFiftyXMaster.inputBytes ∧
      jointCost 2 7456539 0 = 2430831810 ∧
      2430831895 - 2430831810 = 85 ∧
      GuestJointRlpArityByteConservationAndFiftyXMaster.inputBytes < 18 * 7456540) ∧
     (GuestJointRlpArityByteConservationAndFiftyXMaster.inputBytes / 18 = 7456539 ∧
      9 * 7456539 ≤ 2 * 33554428)) ∧
    (decodeProbesOld - decodeProbesNew = 8572986881) ∧
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
      3038649506 > decodeProbesNew)) :=
  ⟨byte_coupled_refs_bound_tight_and_ratio_non_vacuous_and_tight h_ref hb_ref,
   byte_coupled_main200_36x_and_main380_27x_slopes_and_margins_non_vacuous_and_tight,
   joint_bound_non_vacuous_and_tight n2 n17 h_arity hb_arity,
   joint_tight_and_branch_count_non_vacuous_and_tight,
   gain_non_vacuous_and_tight,
   main200_slope_non_vacuous_and_tight,
   main380_slope_non_vacuous_and_tight,
   margins_and_build_dominates_non_vacuous_and_tight⟩

/-- 5. `panToStackRawCall_noAlloc_unconditional`, `panToStackAlloc_noAlloc_noGcCall`,
`stackAllocComp_id`, and `stackAlloc_alloc_calls_gc` bridged with
`dead_stub6_clean_sections_and_byte_coupled_witness_bridge_non_vacuous_and_tight`. -/
theorem no_alloc_no_gc_and_dead_stub6_byte_coupled_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (n m k h : Nat) (hb : 33 * h ≤ inputBytes)
    (p : HolProg width) (ha : StackNoAlloc p = true) (hs : StackNoSt p = true)
    (ht : NoTailHandler p = true) :
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true) ∧
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      NoGcCall y.2 = true →
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    StackAlloc.comp n m p = (p, m) ∧
    NoGcCall (StackAlloc.comp n m (.alloc k : HolProg width)).1 = false ∧
    (((∀ e ∈ stackAllocSections arch prog wc ac perf dc,
         e.1 = storeConstsStubLocation ∨ Clean e.2 = true) ∧
       (∀ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 ≠ storeConstsStubLocation →
         StackNoSt e.2 = true ∧ NoStubCall e.2 = true ∧ Clean e.2 = true) ∧
       ((∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = storeConstsStubLocation) ∧
        sptLookup storeConstsStubLocation
          (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none) ∧
       StackNoSt (storeConstsStubNative (width := width) k) = false) ∧
      (h ≤ 4067203 ∧ (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204)) ∧
      (GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 24381873932 ∧
       36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 < yukon ∧
       yukon < 37 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200) ∧
      (GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 32488958762 ∧
       27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 < yukon ∧
       yukon < 28 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380)) :=
  ⟨panToStackRawCall_noAlloc_unconditional arch prog wc ac perf,
   panToStackAlloc_noAlloc_noGcCall arch prog wc ac perf,
   stackAllocComp_id n m p ha hs ht,
   stackAlloc_alloc_calls_gc n m k,
   dead_stub6_clean_sections_and_byte_coupled_witness_bridge_non_vacuous_and_tight
     arch prog wc ac perf dc h k hb⟩

/-- 6. `panToStackRemove_noAlloc_noGc_zeroExtraClock` unified with
`live_table_zero_extra_clock_and_byte_coupled_margins_bridge_non_vacuous_and_tight` and
joint RLP arity `56×` / `37×` slopes. -/
theorem no_alloc_no_gc_zero_extra_clock_and_byte_coupled_margins_bridge_non_vacuous_and_tight {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (generateGc : Bool) (maximumHeap pointer start n m k : Nat) :
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true) ∧
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      NoGcCall y.2 = true →
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    NoGcCall (StackAlloc.comp n m (.alloc k : HolProg width)).1 = false ∧
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
     (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧ probes 380000000 = 68115248) ∧
     (8589933568 - probes 200000000 = 8523258320) ∧
     (yukon - 36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 22972463922 ∧
      yukon - 27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 23518038900) ∧
     (100 * 10938743528 > 44 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200)) ∧
    (GuestJointRlpArityByteConservationAndFiftyXMaster.main200 = 15808887051 ∧
     56 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 < yukon ∧
     yukon < 57 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 ∧
     50 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 < yukon) ∧
    (GuestJointRlpArityByteConservationAndFiftyXMaster.main380 = 23915971881 ∧
     37 * GuestJointRlpArityByteConservationAndFiftyXMaster.main380 < yukon ∧
     yukon < 38 * GuestJointRlpArityByteConservationAndFiftyXMaster.main380) :=
  ⟨panToStackRawCall_noAlloc_unconditional arch prog wc ac perf,
   panToStackAlloc_noAlloc_noGcCall arch prog wc ac perf,
   stackAlloc_alloc_calls_gc n m k,
   live_table_zero_extra_clock_and_byte_coupled_margins_bridge_non_vacuous_and_tight
     arch prog wc ac perf dc info generateGc maximumHeap pointer start k,
   main200_slope_non_vacuous_and_tight,
   main380_slope_non_vacuous_and_tight⟩

/-- 7. Strictly increasing 88-budget portfolio (`EightyEightShape`), all `< 900_719_925_474`,
extending the 84-budget (`EightyFourShape`) and 82-budget campaign hierarchy. -/
theorem eighty_eight_and_eighty_four_budget_portfolio_hierarchy_non_vacuous_and_tight :
    EightyEightShape ∧
    portfolio.length = 88 ∧
    portfolio.Pairwise (· < ·) ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    portfolio.drop 86 = [880629318297, 880629318298] ∧
    portfolio.getLast? = some 880629318298 ∧
    EightyFourShape :=
  have h88 := eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h84 := eighty_four_and_eighty_two_budget_portfolio_hierarchy_non_vacuous_and_tight
  ⟨h88,
   h88.1,
   h88.2.1,
   h88.2.2.1,
   h88.2.2.2.2.1,
   h88.2.2.2.2.2.1,
   h84.1⟩

/-- 8. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)` across
all 88 budgets, with explicit endpoint certificates at `880_629_318_297` and `880_629_318_298`. -/
theorem eighty_eight_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyEightShape ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK 880629318297) (.finite 880629318297) ∧
    InitE.Certificate (baselineWithFiniteK 880629318298) (.finite 880629318298) :=
  have hcert := eighty_eight_budget_certificates_non_vacuous_and_tight cert
  ⟨hcert.1,
   hcert.1.2.2.1,
   hcert.2,
   hcert.2 880629318297 (by decide),
   hcert.2 880629318298 (by decide)⟩

/-- 9. Synthesis of `PanToStackRawCallNoAllocAndStackAllocStructural`
(`panToStackRawCall_noAlloc_unconditional`, `panToStackAlloc_noAlloc_noGcCall`,
`stackAllocComp_id`, `stackAlloc_alloc_calls_gc`) with the 88-budget conditional certificate
portfolio and byte-coupled witness bounds. -/
theorem pan_to_stack_alloc_no_gc_and_eighty_eight_budget_certificates_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m k h : Nat) (hb : 33 * h ≤ inputBytes)
    (p : HolProg width) (ha : StackNoAlloc p = true) (hs : StackNoSt p = true)
    (ht : NoTailHandler p = true) (cert : CertificateAt 1212035192) :
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true) ∧
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      NoGcCall y.2 = true →
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    StackAlloc.comp n m p = (p, m) ∧
    NoGcCall (StackAlloc.comp n m (.alloc k : HolProg width)).1 = false ∧
    (h ≤ 4067203 ∧
     (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
     (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
     (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
       probes 380000000 = 68115248) ∧
     (8589933568 - probes 200000000 = 8523258320) ∧
     (GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 24381873932 ∧
      36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 < yukon ∧
      yukon < 37 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200) ∧
     (GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 32488958762 ∧
      27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 < yukon ∧
      yukon < 28 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380) ∧
     (yukon - 36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 22972463922 ∧
      yukon - 27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 23518038900) ∧
     (100 * 10938743528 > 44 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200) ∧
     (EightyFourShape ∧
       ∀ K ∈ SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.portfolio,
         InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
    (EightyEightShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨panToStackRawCall_noAlloc_unconditional arch prog wc ac perf,
   panToStackAlloc_noAlloc_noGcCall arch prog wc ac perf,
   stackAllocComp_id n m p ha hs ht,
   stackAlloc_alloc_calls_gc n m k,
   byte_coupled_witness_thirty_five_x_and_eighty_four_budget_certificates_non_vacuous_and_tight
     h hb cert,
   eighty_eight_budget_certificates_non_vacuous_and_tight cert⟩

/-- 10. Grand campaign bridge unifying `PanToStackRawCallNoAllocAndStackAllocStructural`
(`panToStackRawCall_noAlloc_unconditional`, `panToStackAlloc_noAlloc_noGcCall`,
`panToStackRemove_noAlloc_noGc_zeroExtraClock`, `stackAllocComp_id`, `stackAlloc_alloc_calls_gc`),
`ByteCoupledWitnessDeadStub6AndEightyFourBudgetCampaignBridge`, and
`JointRlpArityFiftySixXAndEightyEightBudgetMaster` (`EightyEightShape` and 88 finite certificates). -/
theorem grand_pan_to_stack_alloc_no_gc_and_eighty_eight_budget_campaign_bridge_non_vacuous_and_tight
    {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (generateGc : Bool) (maximumHeap pointer start n m k_stub h : Nat)
    (hb : 33 * h ≤ inputBytes)
    (p : HolProg width) (ha : StackNoAlloc p = true) (hs : StackNoSt p = true)
    (ht : NoTailHandler p = true)
    (w : WordLocW width) (cert : CertificateAt 1212035192) :
    ((∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true) ∧
     (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
       NoGcCall y.2 = true →
       StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
     (∀ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 ≠ storeConstsStubLocation →
       StackNoSt e.2 = true ∧ Clean e.2 = true) ∧
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
    StackAlloc.comp n m p = (p, m) ∧
    NoGcCall (StackAlloc.comp n m (.alloc k_stub : HolProg width)).1 = false ∧
    (h ≤ 4067203 ∧
     (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
     (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
     (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
       probes 380000000 = 68115248) ∧
     (8589933568 - probes 200000000 = 8523258320) ∧
     (GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 24381873932 ∧
      36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 < yukon ∧
      yukon < 37 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200) ∧
     (GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 32488958762 ∧
      27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 < yukon ∧
      yukon < 28 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380) ∧
     (yukon - 36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 22972463922 ∧
      yukon - 27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 23518038900) ∧
     (100 * 10938743528 > 44 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200)) ∧
    ((∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
     (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
       StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
       t.clock = s.clock) ∧
     StackNoSt (storeConstsStubNative (width := width) k_stub) = false ∧
     (¬ ClockOk (width := width) 1 none ∧ ¬ ClockOk 2 (some (.halt w)))) ∧
    (EightyFourShape ∧
     EightyEightShape ∧
     portfolio.length = 88 ∧
     portfolio.Pairwise (· < ·) ∧
     (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
     (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) :=
  have hcert88 := eighty_eight_budget_certificates_non_vacuous_and_tight cert
  have hg84 := grand_byte_coupled_witness_dead_stub6_and_eighty_four_budget_campaign_bridge_non_vacuous_and_tight
    (C := C) (F := F) arch prog wc ac perf dc info generateGc maximumHeap pointer start k_stub h hb w cert
  ⟨panToStackRemove_noAlloc_noGc_zeroExtraClock arch prog wc ac perf dc info,
   stackAllocComp_id n m p ha hs ht,
   stackAlloc_alloc_calls_gc n m k_stub,
   hg84.1,
   ⟨hg84.2.1.2.2.2.1,
    hg84.2.1.2.2.2.2.1,
    hg84.2.1.2.2.2.2.2.1,
    hg84.2.1.2.2.2.2.2.2⟩,
   ⟨hg84.2.2.2.1,
    hcert88.1,
    hcert88.1.1,
    hcert88.1.2.1,
    hcert88.1.2.2.1,
    hcert88.2⟩⟩

#print axioms pan_to_stack_raw_call_no_alloc_and_no_gc_call_non_vacuous_and_tight
#print axioms stack_alloc_comp_id_and_alloc_calls_gc_tight_non_vacuous_and_tight
#print axioms pan_to_stack_remove_no_alloc_no_gc_zero_extra_clock_non_vacuous_and_tight
#print axioms byte_coupled_36x_to_joint_rlp_arity_56x_progression_non_vacuous_and_tight
#print axioms no_alloc_no_gc_and_dead_stub6_byte_coupled_bridge_non_vacuous_and_tight
#print axioms no_alloc_no_gc_zero_extra_clock_and_byte_coupled_margins_bridge_non_vacuous_and_tight
#print axioms eighty_eight_and_eighty_four_budget_portfolio_hierarchy_non_vacuous_and_tight
#print axioms eighty_eight_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
#print axioms pan_to_stack_alloc_no_gc_and_eighty_eight_budget_certificates_non_vacuous_and_tight
#print axioms grand_pan_to_stack_alloc_no_gc_and_eighty_eight_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.PanToStackAllocNoGcAndEightyEightBudgetCampaignBridge
