import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqColumnProducts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang

theorem fqMulColumn0_factors : fqMulColumn0 =
    montLowerColumn "m0" (montFactorExprs fqProducts0) fqMulColumn1 := rfl


theorem fqMulColumn1_factors : fqMulColumn1 =
    montLowerColumn "m1" (montFactorExprs fqProducts1) fqMulColumn2 := rfl


theorem fqMulColumn2_factors : fqMulColumn2 =
    montLowerColumn "m2" (montFactorExprs fqProducts2) fqMulColumn3 := rfl


theorem fqMulColumn3_factors : fqMulColumn3 =
    montLowerColumn "m3" (montFactorExprs fqProducts3) fqMulColumn4 := rfl


theorem fqMulColumn4_factors : fqMulColumn4 =
    montLowerColumn "m4" (montFactorExprs fqProducts4) fqMulColumn5 := rfl


theorem fqMulColumn5_factors : fqMulColumn5 =
    montLowerColumn "m5" (montFactorExprs fqProducts5) fqMulColumn6 := rfl


theorem fqMulColumn6_factors : fqMulColumn6 =
    montLowerColumn "m6" (montFactorExprs fqProducts6) fqMulColumn7 := rfl


theorem fqMulColumn7_factors : fqMulColumn7 =
    montLowerColumn "m7" (montFactorExprs fqProducts7) fqMulColumn8 := rfl


theorem fqMulColumn8_factors : fqMulColumn8 =
    montUpperColumn "u0" (montFactorExprs fqProducts8) fqMulColumn9 := rfl


theorem fqMulColumn9_factors : fqMulColumn9 =
    montUpperColumn "u1" (montFactorExprs fqProducts9) fqMulColumn10 := rfl


theorem fqMulColumn10_factors : fqMulColumn10 =
    montUpperColumn "u2" (montFactorExprs fqProducts10) fqMulColumn11 := rfl


theorem fqMulColumn11_factors : fqMulColumn11 =
    montUpperColumn "u3" (montFactorExprs fqProducts11) fqMulColumn12 := rfl


theorem fqMulColumn12_factors : fqMulColumn12 =
    montUpperColumn "u4" (montFactorExprs fqProducts12) fqMulColumn13 := rfl


theorem fqMulColumn13_factors : fqMulColumn13 =
    montUpperColumn "u5" (montFactorExprs fqProducts13) fqMulColumn14 := rfl


theorem fqMulColumn14_factors : fqMulColumn14 =
    montUpperColumn "u6" (montFactorExprs fqProducts14) fqMulFinish := rfl


end InitECandidate.Solver.Wave8GuestInv.Arith
