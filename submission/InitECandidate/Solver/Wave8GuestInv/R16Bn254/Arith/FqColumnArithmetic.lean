import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqConvolution
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqColumnProducts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang

theorem montProductSum_cons (x y : BitVec 64) (rest : List (BitVec 64 × BitVec 64)) :
    montProductSum ((x,y) :: rest) = x.toNat * y.toNat + montProductSum rest := rfl

theorem montProductSum_nil : montProductSum [] = 0 := rfl


theorem fqPrimeWord1_toNat : (1008765974 : BitVec 64).toNat = 1008765974 := by decide


theorem fqPrimeWord2_toNat : (1752287885 : BitVec 64).toNat = 1752287885 := by decide


theorem fqPrimeWord3_toNat : (2541841041 : BitVec 64).toNat = 2541841041 := by decide


theorem fqPrimeWord4_toNat : (2172737629 : BitVec 64).toNat = 2172737629 := by decide


theorem fqPrimeWord5_toNat : (3092268470 : BitVec 64).toNat = 3092268470 := by decide


theorem fqPrimeWord6_toNat : (3778125865 : BitVec 64).toNat = 3778125865 := by decide


theorem fqPrimeWord7_toNat : (811880050 : BitVec 64).toNat = 811880050 := by decide


theorem fqProducts0_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts0) + (m 0).toNat * 3632069959 =
      fqConvolution0 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts0, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_nil]
  all_goals unfold fqConvolution0
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts1_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts1) + (m 1).toNat * 3632069959 =
      fqConvolution1 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts1, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord1_toNat]
  all_goals unfold fqConvolution1
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts2_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts2) + (m 2).toNat * 3632069959 =
      fqConvolution2 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts2, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord1_toNat, fqPrimeWord2_toNat]
  all_goals unfold fqConvolution2
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts3_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts3) + (m 3).toNat * 3632069959 =
      fqConvolution3 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts3, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord1_toNat, fqPrimeWord2_toNat, fqPrimeWord3_toNat]
  all_goals unfold fqConvolution3
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts4_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts4) + (m 4).toNat * 3632069959 =
      fqConvolution4 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts4, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord1_toNat, fqPrimeWord2_toNat, fqPrimeWord3_toNat, fqPrimeWord4_toNat]
  all_goals unfold fqConvolution4
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts5_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts5) + (m 5).toNat * 3632069959 =
      fqConvolution5 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts5, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord1_toNat, fqPrimeWord2_toNat, fqPrimeWord3_toNat, fqPrimeWord4_toNat, fqPrimeWord5_toNat]
  all_goals unfold fqConvolution5
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts6_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts6) + (m 6).toNat * 3632069959 =
      fqConvolution6 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts6, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord1_toNat, fqPrimeWord2_toNat, fqPrimeWord3_toNat, fqPrimeWord4_toNat, fqPrimeWord5_toNat, fqPrimeWord6_toNat]
  all_goals unfold fqConvolution6
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts7_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts7) + (m 7).toNat * 3632069959 =
      fqConvolution7 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts7, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord1_toNat, fqPrimeWord2_toNat, fqPrimeWord3_toNat, fqPrimeWord4_toNat, fqPrimeWord5_toNat, fqPrimeWord6_toNat, fqPrimeWord7_toNat]
  all_goals unfold fqConvolution7
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts8_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts8) =
      fqConvolution8 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts8, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord1_toNat, fqPrimeWord2_toNat, fqPrimeWord3_toNat, fqPrimeWord4_toNat, fqPrimeWord5_toNat, fqPrimeWord6_toNat, fqPrimeWord7_toNat]
  all_goals unfold fqConvolution8
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts9_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts9) =
      fqConvolution9 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts9, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord2_toNat, fqPrimeWord3_toNat, fqPrimeWord4_toNat, fqPrimeWord5_toNat, fqPrimeWord6_toNat, fqPrimeWord7_toNat]
  all_goals unfold fqConvolution9
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts10_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts10) =
      fqConvolution10 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts10, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord3_toNat, fqPrimeWord4_toNat, fqPrimeWord5_toNat, fqPrimeWord6_toNat, fqPrimeWord7_toNat]
  all_goals unfold fqConvolution10
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts11_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts11) =
      fqConvolution11 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts11, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord4_toNat, fqPrimeWord5_toNat, fqPrimeWord6_toNat, fqPrimeWord7_toNat]
  all_goals unfold fqConvolution11
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts12_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts12) =
      fqConvolution12 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts12, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord5_toNat, fqPrimeWord6_toNat, fqPrimeWord7_toNat]
  all_goals unfold fqConvolution12
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts13_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts13) =
      fqConvolution13 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts13, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord6_toNat, fqPrimeWord7_toNat]
  all_goals unfold fqConvolution13
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


theorem fqProducts14_convolution (a b m : Fin 8 → BitVec 64) :
    montProductSum (montFactorValues a b m fqProducts14) =
      fqConvolution14 (fun i => (a i).toNat) (fun i => (b i).toNat) (fun i => (m i).toNat) := by
  simp only [montFactorValues, fqProducts14, List.map_cons, List.map_nil, montFactorValue]
  all_goals rw [montProductSum_cons, montProductSum_cons, montProductSum_nil, fqPrimeWord7_toNat]
  all_goals unfold fqConvolution14
  all_goals simp only [Nat.add_zero, Nat.add_assoc]


end InitECandidate.Solver.Wave8GuestInv.Arith
