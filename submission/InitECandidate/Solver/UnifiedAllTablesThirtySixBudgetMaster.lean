import InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope
import InitECandidate.Solver.FiveAddrTablesThirtySixBudgetMaster
import InitECandidate.Solver.UnconditionalNoStoreConstsAndFiveAddrMaster

set_option autoImplicit false
namespace InitECandidate.Solver.UnifiedAllTablesThirtySixBudgetMaster
open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open _root_.InitECandidate.Solver.GuestMergeTxUnionEnvelope (locCoup mergeLin)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope (F G kPanUnifiedAllTables)
open SelfContainedBoundedCertificate UnrolledTwelveCandidatePortfolio
abbrev portfolio := FiveAddrTablesThirtySixBudgetMaster.portfolio
abbrev mergeSlope3UnrolledK := FiveAddrTablesThirtySixBudgetMaster.mergeSlope3UnrolledK
abbrev mergeSlope3K := FiveAddrTablesThirtySixBudgetMaster.mergeSlope3K
abbrev mergeSlope6UnrolledK := FiveAddrTablesThirtySixBudgetMaster.mergeSlope6UnrolledK
abbrev mergeSlope6K := FiveAddrTablesThirtySixBudgetMaster.mergeSlope6K

theorem values_non_vacuous_and_tight :
    mergeSlope3UnrolledK = 408348416306 ∧ mergeSlope3K = 408348430106 ∧
    mergeSlope6UnrolledK = 816696823280 ∧ mergeSlope6K = 816696837080 ∧
    mergeSlope6K < 900719925474 :=
  MultiAddressMergeThirtySixBudgetMaster.values_non_vacuous_and_tight

theorem portfolio_non_vacuous_and_tight :
    portfolio.length = 36 ∧ portfolio.Pairwise (· < ·) ∧
    (∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < yukon) :=
  MultiAddressMergeThirtySixBudgetMaster.portfolio_non_vacuous_and_tight

theorem thirty_two_coverage_non_vacuous_and_tight :
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified, k ∈ portfolio) ∧
    ThirtyTwoBudgetJointAbsorptionMaster.absorbedPortfolio.length = 32 :=
  MultiAddressMergeThirtySixBudgetMaster.thirty_two_coverage_non_vacuous_and_tight

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) :=
  MultiAddressMergeThirtySixBudgetMaster.portfolio_certificates_non_vacuous_and_tight (hc := hc)

theorem mergeSlope3UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3UnrolledK) (.finite mergeSlope3UnrolledK) :=
  MultiAddressMergeThirtySixBudgetMaster.mergeSlope3UnrolledK_certificate_non_vacuous_and_tight (hc := hc)

theorem mergeSlope3K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3K) (.finite mergeSlope3K) :=
  MultiAddressMergeThirtySixBudgetMaster.mergeSlope3K_certificate_non_vacuous_and_tight (hc := hc)

theorem mergeSlope6UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6UnrolledK) (.finite mergeSlope6UnrolledK) :=
  MultiAddressMergeThirtySixBudgetMaster.mergeSlope6UnrolledK_certificate_non_vacuous_and_tight (hc := hc)

theorem mergeSlope6K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6K) (.finite mergeSlope6K) :=
  MultiAddressMergeThirtySixBudgetMaster.mergeSlope6K_certificate_non_vacuous_and_tight (hc := hc)

theorem per_address_split_non_vacuous_and_tight (l : List (Nat × Nat)) :
    (l.map (fun p => p.1 * (p.2 + p.1))).sum ≤
      (l.map Prod.fst).sum * ((l.map Prod.snd).sum + (l.map Prod.fst).sum) :=
  MultiAddressMergeThirtySixBudgetMaster.per_address_split_non_vacuous_and_tight (l := l)

theorem per_address_tight_non_vacuous_and_tight (d w : Nat) :
    ([(d, w)].map (fun p => p.1 * (p.2 + p.1))).sum =
      ([(d, w)].map Prod.fst).sum * (([(d, w)].map Prod.snd).sum + ([(d, w)].map Prod.fst).sum) :=
  MultiAddressMergeThirtySixBudgetMaster.per_address_tight_non_vacuous_and_tight (d := d) (w := w)

theorem five_offsets_non_vacuous_and_tight (bs A : Nat) :
    ([bs+8, bs+16, bs+24, bs+40, bs+48].map (fun _ => A*A)).sum = 5*(A*A) :=
  FiveAddrTablesThirtySixBudgetMaster.five_offsets_non_vacuous_and_tight bs A

theorem unified_five_var_coupled_envelope_non_vacuous_and_tight (D R A C W : Nat)
    (h : 21*D + 20*R + 26*A + 21*C + W ≤ S) :
    F D R A C W ≤ 95238095238 :=
  GuestUnifiedAllTablesMasterEnvelope.unified_coupled_le D R A C W h

theorem unified_five_var_merge_envelope_non_vacuous_and_tight (D R A C W : Nat)
    (h : 20*(D+R+A) + 6*A + 21*C + (W+(D+R+A)) ≤ S) :
    G D R A C W ≤ 100000000000 :=
  GuestUnifiedAllTablesMasterEnvelope.unified_merge_le D R A C W h

theorem coupled_attained_non_vacuous_and_tight :
    21*47619 + 20*0 + 26*0 + 21*0 + 1000001 = S ∧
    F 47619 0 0 0 1000001 = 95238095238 :=
  GuestUnifiedAllTablesMasterEnvelope.unified_coupled_tight

theorem merge_attained_non_vacuous_and_tight :
    G 50000 0 0 0 950000 = 100000000000 ∧
    G 2000 48000 0 0 950000 = 100000000000 ∧
    20*(2000+48000+0)+6*0+21*0+(950000+(2000+48000+0)) = S :=
  GuestUnifiedAllTablesMasterEnvelope.unified_merge_tight

theorem cold_corner_non_vacuous_and_tight :
    F 0 0 0 95238 0 = 9070276644 ∧ F 0 0 0 95238 0 ≤ 9070294784 := by decide

theorem source_clock_non_vacuous_and_tight : kPanUnifiedAllTables = 136116135658 :=
  GuestUnifiedAllTablesMasterEnvelope.kPanUnified_val.1

theorem slopes_non_vacuous_and_tight (k : Nat) :
    6*kPanUnifiedAllTables < yukon ∧ (k*kPanUnifiedAllTables < yukon ↔ k ≤ 6) :=
  GuestUnifiedAllTablesMasterEnvelope.slopes k

theorem all_tables_master_non_vacuous_and_tight (D R A C W Tloc Tlin : Nat)
    (h : 20*(D+R+A)+6*A+21*C+(W+(D+R+A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables :=
  GuestUnifiedAllTablesMasterEnvelope.kPanUnified_master D R A C W Tloc Tlin h hloc hlin

/-- All charged address-table squares are absorbed simultaneously. -/
theorem address_tables_sum_non_vacuous_and_tight (bs ts A : Nat) :
    ([bs+8,bs+16,bs+24,bs+40,bs+48].map (fun _ => A*A)).sum +
    ([ts+8,ts+16,ts+24,ts+32,ts+40].map (fun _ => A*A)).sum ≤ 12*(A*A) := by
  simp; omega

/-- The cold table and both address families fit the same five-variable envelope. -/
theorem simultaneous_absorption_non_vacuous_and_tight (bs ts D R A C W : Nat)
    (h : 20*(D+R+A)+6*A+21*C+(W+(D+R+A)) ≤ S) :
    2*((D+R+A)*(W+(D+R+A))) + C*(W+(D+R+A)+C) +
    ([bs+8,bs+16,bs+24,bs+40,bs+48].map (fun _ => A*A)).sum +
    ([ts+8,ts+16,ts+24,ts+32,ts+40].map (fun _ => A*A)).sum ≤ 100000000000 := by
  have he := unified_five_var_merge_envelope_non_vacuous_and_tight D R A C W h
  have ha := address_tables_sum_non_vacuous_and_tight bs ts A
  unfold G at he
  omega

theorem four_tiers_non_vacuous_and_tight (D R A C W Tloc Tlin : Nat)
    (h : 20*(D+R+A)+6*A+21*C+(W+(D+R+A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    let cost := linear + Tloc + G D R A C W + Tlin
    9332+3*cost ≤ 408348416306 ∧ 23132+3*cost ≤ 408348430106 ∧
    9332+6*cost ≤ 816696823280 ∧ 23132+6*cost ≤ 816696837080 ∧
    816696837080 < 900719925474 := by
  have hm := all_tables_master_non_vacuous_and_tight D R A C W Tloc Tlin h hloc hlin
  have hv := source_clock_non_vacuous_and_tight
  dsimp only
  omega

/-- The explicitly summed address tables preserve all four target budgets. -/
theorem simultaneous_four_tiers_non_vacuous_and_tight (bs ts D R A C W Tloc Tlin : Nat)
    (h : 20*(D+R+A)+6*A+21*C+(W+(D+R+A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    let cost := linear + Tloc +
      (2*((D+R+A)*(W+(D+R+A))) + C*(W+(D+R+A)+C) +
      ([bs+8,bs+16,bs+24,bs+40,bs+48].map (fun _ => A*A)).sum +
      ([ts+8,ts+16,ts+24,ts+32,ts+40].map (fun _ => A*A)).sum) + Tlin
    9332+3*cost ≤ 408348416306 ∧ 23132+3*cost ≤ 408348430106 ∧
    9332+6*cost ≤ 816696823280 ∧ 23132+6*cost ≤ 816696837080 ∧
    (portfolio.length = 36 ∧ ∀ k ∈ portfolio, k < yukon) := by
  have ha := simultaneous_absorption_non_vacuous_and_tight bs ts D R A C W h
  have hp := portfolio_non_vacuous_and_tight
  have hsum : linear + locCoup + 100000000000 + mergeLin = 136116135658 := by decide
  dsimp only
  refine ⟨by omega, by omega, by omega, by omega, hp.1, ?_⟩
  exact fun k hk => (hp.2.2 k hk).2

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open WordPassesPreserveNoStoreConsts PanToStackNoStoreConsts
variable {width : Nat} [NeZero width]

theorem panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true :=
  UnconditionalNoStoreConstsAndFiveAddrMaster.panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f

theorem flatten_storeConsts_empty_non_vacuous_and_tight (tail : Bool) (s b : Nat) (stub : Option Nat)
    (sid next : Nat) (cs bs : List Nat) :
    StackToLab.flattenHOL tail (.storeConsts s b stub : HolProg width) sid next cs bs =
      (.list [], false, next) :=
  PanToStackToLabUnconditionalNoStoreConsts.flatten_storeConsts_empty (tail := tail) (s := s) (b := b) (stub := stub) (sid := sid) (next := next) (cs := cs) (bs := bs)

/-- Arithmetic envelope, all 36 budgets, and unconditional backend preservation. -/
theorem integrated_master_non_vacuous_and_tight (D R A C W Tloc Tlin : Nat)
    (h : 20*(D+R+A)+6*A+21*C+(W+(D+R+A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    (linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables) ∧
    (portfolio.length = 36 ∧ ∀ k ∈ portfolio, k < yukon) ∧
    (∀ (tail : Bool) (s b : Nat) (stub : Option Nat) (sid next : Nat) (cs bs : List Nat),
      StackToLab.flattenHOL tail (.storeConsts s b stub : HolProg width) sid next cs bs =
        (.list [], false, next)) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) := by
  exact ⟨all_tables_master_non_vacuous_and_tight D R A C W Tloc Tlin h hloc hlin,
    ⟨portfolio_non_vacuous_and_tight.1,
      fun k hk => (portfolio_non_vacuous_and_tight.2.2 k hk).2⟩,
    flatten_storeConsts_empty_non_vacuous_and_tight,
    panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight
      arch prog wc ac perf info j bd ptr f⟩

#print axioms simultaneous_four_tiers_non_vacuous_and_tight
#print axioms values_non_vacuous_and_tight
#print axioms portfolio_non_vacuous_and_tight
#print axioms thirty_two_coverage_non_vacuous_and_tight
#print axioms portfolio_certificates_non_vacuous_and_tight
#print axioms mergeSlope3UnrolledK_certificate_non_vacuous_and_tight
#print axioms mergeSlope3K_certificate_non_vacuous_and_tight
#print axioms mergeSlope6UnrolledK_certificate_non_vacuous_and_tight
#print axioms mergeSlope6K_certificate_non_vacuous_and_tight
#print axioms per_address_split_non_vacuous_and_tight
#print axioms per_address_tight_non_vacuous_and_tight
#print axioms five_offsets_non_vacuous_and_tight
#print axioms unified_five_var_coupled_envelope_non_vacuous_and_tight
#print axioms unified_five_var_merge_envelope_non_vacuous_and_tight
#print axioms coupled_attained_non_vacuous_and_tight
#print axioms merge_attained_non_vacuous_and_tight
#print axioms cold_corner_non_vacuous_and_tight
#print axioms source_clock_non_vacuous_and_tight
#print axioms slopes_non_vacuous_and_tight
#print axioms all_tables_master_non_vacuous_and_tight
#print axioms address_tables_sum_non_vacuous_and_tight
#print axioms simultaneous_absorption_non_vacuous_and_tight
#print axioms four_tiers_non_vacuous_and_tight
#print axioms panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight
#print axioms flatten_storeConsts_empty_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.UnifiedAllTablesThirtySixBudgetMaster
