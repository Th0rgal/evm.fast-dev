import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulScopedFrame

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

theorem montRaw_bound_left (radix modulus a b correction raw : Nat)
    (hr : 0 < radix) (hm : 0 < modulus)
    (ha : a < modulus) (hb : b < radix) (hk : correction < radix)
    (hidentity : radix * raw = a * b + correction * modulus) :
    raw < 2 * modulus := by
  rw [Nat.mul_comm a b] at hidentity
  exact montRaw_bound radix modulus b a correction raw hr hm hb ha hk hidentity

theorem fqMontReduction_correct_left (a b correction raw : Nat)
    (ha : a < fqModulus.toNat) (hb : b < 2 ^ 256) (hk : correction < 2 ^ 256)
    (hidentity : 2 ^ 256 * raw = a * b + correction * fqModulus.toNat) :
    raw < 2 ^ 256 ∧ montFinalReduce raw fqModulus.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * montFinalReduce raw fqModulus.toNat) (a * b) := by
  have hp : 0 < fqModulus.toNat := Nat.lt_trans (by decide) fqModulus_gt_one
  have hraw := montRaw_bound_left _ _ _ _ _ _ (by decide) hp ha hb hk hidentity
  refine ⟨hraw.trans fqModulus_double_lt_radix, montFinalReduce_lt _ _ hraw, ?_⟩
  apply ((montFinalReduce_modEq raw fqModulus.toNat).mul_left (2 ^ 256)).trans
  change (2 ^ 256 * raw) % fqModulus.toNat = (a * b) % fqModulus.toNat
  rw [hidentity]
  simp

theorem fqColumns_correct_left (a b : Limbs256) (m : Fin 8 → Nat)
    (carry : Fin 16 → Nat) (digits : Fin 7 → Nat)
    (ha : a.toNat < fqModulus.toNat)
    (hm : ∀ i, m i < 2 ^ 32)
    (hzero : carry 0 = 0)
    (h0 : 4294967296 * carry 1 = carry 0 + fqConvolution0 (limbs256Digits a) (limbs256Digits b) m)
    (h1 : 4294967296 * carry 2 = carry 1 + fqConvolution1 (limbs256Digits a) (limbs256Digits b) m)
    (h2 : 4294967296 * carry 3 = carry 2 + fqConvolution2 (limbs256Digits a) (limbs256Digits b) m)
    (h3 : 4294967296 * carry 4 = carry 3 + fqConvolution3 (limbs256Digits a) (limbs256Digits b) m)
    (h4 : 4294967296 * carry 5 = carry 4 + fqConvolution4 (limbs256Digits a) (limbs256Digits b) m)
    (h5 : 4294967296 * carry 6 = carry 5 + fqConvolution5 (limbs256Digits a) (limbs256Digits b) m)
    (h6 : 4294967296 * carry 7 = carry 6 + fqConvolution6 (limbs256Digits a) (limbs256Digits b) m)
    (h7 : 4294967296 * carry 8 = carry 7 + fqConvolution7 (limbs256Digits a) (limbs256Digits b) m)
    (h8 : digits 0 + 4294967296 * carry 9 = carry 8 + fqConvolution8 (limbs256Digits a) (limbs256Digits b) m)
    (h9 : digits 1 + 4294967296 * carry 10 = carry 9 + fqConvolution9 (limbs256Digits a) (limbs256Digits b) m)
    (h10 : digits 2 + 4294967296 * carry 11 = carry 10 + fqConvolution10 (limbs256Digits a) (limbs256Digits b) m)
    (h11 : digits 3 + 4294967296 * carry 12 = carry 11 + fqConvolution11 (limbs256Digits a) (limbs256Digits b) m)
    (h12 : digits 4 + 4294967296 * carry 13 = carry 12 + fqConvolution12 (limbs256Digits a) (limbs256Digits b) m)
    (h13 : digits 5 + 4294967296 * carry 14 = carry 13 + fqConvolution13 (limbs256Digits a) (limbs256Digits b) m)
    (h14 : digits 6 + 4294967296 * carry 15 = carry 14 + fqConvolution14 (limbs256Digits a) (limbs256Digits b) m)
    : let raw := digits 0 * 1 + digits 1 * 4294967296 + digits 2 * 18446744073709551616 +
        digits 3 * 79228162514264337593543950336 +
        digits 4 * 340282366920938463463374607431768211456 +
        digits 5 * 1461501637330902918203684832716283019655932542976 +
        digits 6 * 6277101735386680763835789423207666416102355444464034512896 +
        carry 15 * 26959946667150639794667015087019630673637144422540572481103610249216
      raw < 2 ^ 256 ∧ montFinalReduce raw fqModulus.toNat < fqModulus.toNat ∧
        Nat.ModEq fqModulus.toNat (2 ^ 256 * montFinalReduce raw fqModulus.toNat)
          (a.toNat * b.toNat) := by
  have ht := fqColumns_telescope
    (fqConvolutionColumns (limbs256Digits a) (limbs256Digits b) m) carry digits
    hzero h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  rw [fqConvolutionColumns_eq, limbs256Digits_value, limbs256Digits_value] at ht
  exact fqMontReduction_correct_left a.toNat b.toNat (montRadix8 m) _ ha
    (by simpa only [limbs256Digits_value] using
      montRadix8_lt (limbs256Digits b) (limbs256Digits_lt b))
    (montRadix8_lt m hm) ht

theorem fqMulColumns_returned_left {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (A B : Limbs256) (ret : ValueHOL 64) (hcode : s.code = originalRuntimeCode)
    (hA : A.toNat < fqModulus.toNat)
    (hs : MontSlots s (limbs256Words A) (limbs256Words B)
      (fun _ => 0) (fun _ => 0) 0 0 0)
    (he : evaluateHOLFiniteState s fqMulColumn0 = (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * out.toNat) (A.toNat * B.toNat) := by
  let a := limbs256Words A
  let b := limbs256Words B
  let m0 : Fin 8 → BitVec 64 := fun _ => 0
  let u0 : Fin 7 → BitVec 64 := fun _ => 0
  have ha : ∀ i, (a i).toNat < 2 ^ 32 := limbs256Words_lt A
  have hb : ∀ i, (b i).toNat < 2 ^ 32 := limbs256Words_lt B
  have hm0 : ∀ i, (m0 i).toNat < 2 ^ 32 := by intro i; decide
  have hu0 : ∀ i, (u0 i).toNat < 2 ^ 32 := by intro i; decide
  have hc0 : (0#64).toNat < 32 * 2 ^ 32 := by decide
  have hS0 : MontSlots s a b m0 u0 0 0 0 := hs
  have hCode0 := hcode
  obtain ⟨d0, c1, s1, hS1, hC1, hE0, hd0, hc1, hEq0⟩ :=
    montLowerStep_bounded hS0 "m0" 0 (by rfl) fqProducts0 (by decide)
      (fqColumnFactors_bounded 0) ha hb hm0 hc0 fqMulColumn1
  let m1 := Function.update m0 0 d0
  change MontSlots s1 a b m1 u0 c1 0 0 at hS1
  have hm1 : ∀ i, (m1 i).toNat < 2 ^ 32 := montUpdate_lt m0 0 d0 hm0 hd0
  have hCode1 : s1.code = originalRuntimeCode := hC1.trans hCode0
  rw [fqMulColumn0_factors, hE0] at he
  obtain ⟨d1, c2, s2, hS2, hC2, hE1, hd1, hc2, hEq1⟩ :=
    montLowerStep_bounded hS1 "m1" 1 (by rfl) fqProducts1 (by decide)
      (fqColumnFactors_bounded 1) ha hb hm1 hc1 fqMulColumn2
  let m2 := Function.update m1 1 d1
  change MontSlots s2 a b m2 u0 c2 0 0 at hS2
  have hm2 : ∀ i, (m2 i).toNat < 2 ^ 32 := montUpdate_lt m1 1 d1 hm1 hd1
  have hCode2 : s2.code = originalRuntimeCode := hC2.trans hCode1
  rw [fqMulColumn1_factors, hE1] at he
  obtain ⟨d2, c3, s3, hS3, hC3, hE2, hd2, hc3, hEq2⟩ :=
    montLowerStep_bounded hS2 "m2" 2 (by rfl) fqProducts2 (by decide)
      (fqColumnFactors_bounded 2) ha hb hm2 hc2 fqMulColumn3
  let m3 := Function.update m2 2 d2
  change MontSlots s3 a b m3 u0 c3 0 0 at hS3
  have hm3 : ∀ i, (m3 i).toNat < 2 ^ 32 := montUpdate_lt m2 2 d2 hm2 hd2
  have hCode3 : s3.code = originalRuntimeCode := hC3.trans hCode2
  rw [fqMulColumn2_factors, hE2] at he
  obtain ⟨d3, c4, s4, hS4, hC4, hE3, hd3, hc4, hEq3⟩ :=
    montLowerStep_bounded hS3 "m3" 3 (by rfl) fqProducts3 (by decide)
      (fqColumnFactors_bounded 3) ha hb hm3 hc3 fqMulColumn4
  let m4 := Function.update m3 3 d3
  change MontSlots s4 a b m4 u0 c4 0 0 at hS4
  have hm4 : ∀ i, (m4 i).toNat < 2 ^ 32 := montUpdate_lt m3 3 d3 hm3 hd3
  have hCode4 : s4.code = originalRuntimeCode := hC4.trans hCode3
  rw [fqMulColumn3_factors, hE3] at he
  obtain ⟨d4, c5, s5, hS5, hC5, hE4, hd4, hc5, hEq4⟩ :=
    montLowerStep_bounded hS4 "m4" 4 (by rfl) fqProducts4 (by decide)
      (fqColumnFactors_bounded 4) ha hb hm4 hc4 fqMulColumn5
  let m5 := Function.update m4 4 d4
  change MontSlots s5 a b m5 u0 c5 0 0 at hS5
  have hm5 : ∀ i, (m5 i).toNat < 2 ^ 32 := montUpdate_lt m4 4 d4 hm4 hd4
  have hCode5 : s5.code = originalRuntimeCode := hC5.trans hCode4
  rw [fqMulColumn4_factors, hE4] at he
  obtain ⟨d5, c6, s6, hS6, hC6, hE5, hd5, hc6, hEq5⟩ :=
    montLowerStep_bounded hS5 "m5" 5 (by rfl) fqProducts5 (by decide)
      (fqColumnFactors_bounded 5) ha hb hm5 hc5 fqMulColumn6
  let m6 := Function.update m5 5 d5
  change MontSlots s6 a b m6 u0 c6 0 0 at hS6
  have hm6 : ∀ i, (m6 i).toNat < 2 ^ 32 := montUpdate_lt m5 5 d5 hm5 hd5
  have hCode6 : s6.code = originalRuntimeCode := hC6.trans hCode5
  rw [fqMulColumn5_factors, hE5] at he
  obtain ⟨d6, c7, s7, hS7, hC7, hE6, hd6, hc7, hEq6⟩ :=
    montLowerStep_bounded hS6 "m6" 6 (by rfl) fqProducts6 (by decide)
      (fqColumnFactors_bounded 6) ha hb hm6 hc6 fqMulColumn7
  let m7 := Function.update m6 6 d6
  change MontSlots s7 a b m7 u0 c7 0 0 at hS7
  have hm7 : ∀ i, (m7 i).toNat < 2 ^ 32 := montUpdate_lt m6 6 d6 hm6 hd6
  have hCode7 : s7.code = originalRuntimeCode := hC7.trans hCode6
  rw [fqMulColumn6_factors, hE6] at he
  obtain ⟨d7, c8, s8, hS8, hC8, hE7, hd7, hc8, hEq7⟩ :=
    montLowerStep_bounded hS7 "m7" 7 (by rfl) fqProducts7 (by decide)
      (fqColumnFactors_bounded 7) ha hb hm7 hc7 fqMulColumn8
  let m8 := Function.update m7 7 d7
  change MontSlots s8 a b m8 u0 c8 0 0 at hS8
  have hm8 : ∀ i, (m8 i).toNat < 2 ^ 32 := montUpdate_lt m7 7 d7 hm7 hd7
  have hCode8 : s8.code = originalRuntimeCode := hC8.trans hCode7
  rw [fqMulColumn7_factors, hE7] at he
  obtain ⟨d8, c9, s9, hS9, hC9, hE8, hd8, hc9, hEq8⟩ :=
    montUpperStep_bounded hS8 "u0" 0 (by rfl) fqProducts8 (by decide)
      (fqColumnFactors_bounded 8) ha hb hm8 hc8 fqMulColumn9
  let u1 := Function.update u0 0 d8
  change MontSlots s9 a b m8 u1 c9 0 0 at hS9
  have hu1 : ∀ i, (u1 i).toNat < 2 ^ 32 := montUpdate_lt u0 0 d8 hu0 hd8
  have hCode9 : s9.code = originalRuntimeCode := hC9.trans hCode8
  rw [fqMulColumn8_factors, hE8] at he
  obtain ⟨d9, c10, s10, hS10, hC10, hE9, hd9, hc10, hEq9⟩ :=
    montUpperStep_bounded hS9 "u1" 1 (by rfl) fqProducts9 (by decide)
      (fqColumnFactors_bounded 9) ha hb hm8 hc9 fqMulColumn10
  let u2 := Function.update u1 1 d9
  change MontSlots s10 a b m8 u2 c10 0 0 at hS10
  have hu2 : ∀ i, (u2 i).toNat < 2 ^ 32 := montUpdate_lt u1 1 d9 hu1 hd9
  have hCode10 : s10.code = originalRuntimeCode := hC10.trans hCode9
  rw [fqMulColumn9_factors, hE9] at he
  obtain ⟨d10, c11, s11, hS11, hC11, hE10, hd10, hc11, hEq10⟩ :=
    montUpperStep_bounded hS10 "u2" 2 (by rfl) fqProducts10 (by decide)
      (fqColumnFactors_bounded 10) ha hb hm8 hc10 fqMulColumn11
  let u3 := Function.update u2 2 d10
  change MontSlots s11 a b m8 u3 c11 0 0 at hS11
  have hu3 : ∀ i, (u3 i).toNat < 2 ^ 32 := montUpdate_lt u2 2 d10 hu2 hd10
  have hCode11 : s11.code = originalRuntimeCode := hC11.trans hCode10
  rw [fqMulColumn10_factors, hE10] at he
  obtain ⟨d11, c12, s12, hS12, hC12, hE11, hd11, hc12, hEq11⟩ :=
    montUpperStep_bounded hS11 "u3" 3 (by rfl) fqProducts11 (by decide)
      (fqColumnFactors_bounded 11) ha hb hm8 hc11 fqMulColumn12
  let u4 := Function.update u3 3 d11
  change MontSlots s12 a b m8 u4 c12 0 0 at hS12
  have hu4 : ∀ i, (u4 i).toNat < 2 ^ 32 := montUpdate_lt u3 3 d11 hu3 hd11
  have hCode12 : s12.code = originalRuntimeCode := hC12.trans hCode11
  rw [fqMulColumn11_factors, hE11] at he
  obtain ⟨d12, c13, s13, hS13, hC13, hE12, hd12, hc13, hEq12⟩ :=
    montUpperStep_bounded hS12 "u4" 4 (by rfl) fqProducts12 (by decide)
      (fqColumnFactors_bounded 12) ha hb hm8 hc12 fqMulColumn13
  let u5 := Function.update u4 4 d12
  change MontSlots s13 a b m8 u5 c13 0 0 at hS13
  have hu5 : ∀ i, (u5 i).toNat < 2 ^ 32 := montUpdate_lt u4 4 d12 hu4 hd12
  have hCode13 : s13.code = originalRuntimeCode := hC13.trans hCode12
  rw [fqMulColumn12_factors, hE12] at he
  obtain ⟨d13, c14, s14, hS14, hC14, hE13, hd13, hc14, hEq13⟩ :=
    montUpperStep_bounded hS13 "u5" 5 (by rfl) fqProducts13 (by decide)
      (fqColumnFactors_bounded 13) ha hb hm8 hc13 fqMulColumn14
  let u6 := Function.update u5 5 d13
  change MontSlots s14 a b m8 u6 c14 0 0 at hS14
  have hu6 : ∀ i, (u6 i).toNat < 2 ^ 32 := montUpdate_lt u5 5 d13 hu5 hd13
  have hCode14 : s14.code = originalRuntimeCode := hC14.trans hCode13
  rw [fqMulColumn13_factors, hE13] at he
  obtain ⟨d14, c15, s15, hS15, hC15, hE14, hd14, hc15, hEq14⟩ :=
    montUpperStep_bounded hS14 "u6" 6 (by rfl) fqProducts14 (by decide)
      (fqColumnFactors_bounded 14) ha hb hm8 hc14 fqMulFinish
  let u7 := Function.update u6 6 d14
  change MontSlots s15 a b m8 u7 c15 0 0 at hS15
  have hu7 : ∀ i, (u7 i).toNat < 2 ^ 32 := montUpdate_lt u6 6 d14 hu6 hd14
  have hCode15 : s15.code = originalRuntimeCode := hC15.trans hCode14
  rw [fqMulColumn14_factors, hE14] at he
  have haNat : (fun i => (a i).toNat) = limbs256Digits A := funext (limbs256Words_toNat A)
  have hbNat : (fun i => (b i).toNat) = limbs256Digits B := funext (limbs256Words_toNat B)
  have hvals0 : montFactorValues a b m0 fqProducts0 = montFactorValues a b m8 fqProducts0 := by
    simp [montFactorValues, fqProducts0, montFactorValue, m1, m2, m3, m4, m5, m6, m7, m8]
  have hdm0 : m8 0 = d0 := by simp [m1, m2, m3, m4, m5, m6, m7, m8]
  have hprod0 : montProductSum (montFactorValues a b m0 fqProducts0) + d0.toNat * 3632069959 =
      fqConvolution0 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hvals0, ← hdm0, fqProducts0_convolution, haNat, hbNat]
  have hcol0 : 4294967296 * c1.toNat = (0#64).toNat + fqConvolution0 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    calc
      _ = montProductSum (montFactorValues a b m0 fqProducts0) + (0#64).toNat +
          d0.toNat * 3632069959 := hEq0
      _ = (0#64).toNat + (montProductSum (montFactorValues a b m0 fqProducts0) +
          d0.toNat * 3632069959) := by ac_rfl
      _ = _ := congrArg (fun x => (0#64).toNat + x) hprod0
  have hvals1 : montFactorValues a b m1 fqProducts1 = montFactorValues a b m8 fqProducts1 := by
    simp [montFactorValues, fqProducts1, montFactorValue, m1, m2, m3, m4, m5, m6, m7, m8]
  have hdm1 : m8 1 = d1 := by simp [m1, m2, m3, m4, m5, m6, m7, m8]
  have hprod1 : montProductSum (montFactorValues a b m1 fqProducts1) + d1.toNat * 3632069959 =
      fqConvolution1 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hvals1, ← hdm1, fqProducts1_convolution, haNat, hbNat]
  have hcol1 : 4294967296 * c2.toNat = c1.toNat + fqConvolution1 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    calc
      _ = montProductSum (montFactorValues a b m1 fqProducts1) + c1.toNat +
          d1.toNat * 3632069959 := hEq1
      _ = c1.toNat + (montProductSum (montFactorValues a b m1 fqProducts1) +
          d1.toNat * 3632069959) := by ac_rfl
      _ = _ := congrArg (fun x => c1.toNat + x) hprod1
  have hvals2 : montFactorValues a b m2 fqProducts2 = montFactorValues a b m8 fqProducts2 := by
    simp [montFactorValues, fqProducts2, montFactorValue, m1, m2, m3, m4, m5, m6, m7, m8]
  have hdm2 : m8 2 = d2 := by simp [m1, m2, m3, m4, m5, m6, m7, m8]
  have hprod2 : montProductSum (montFactorValues a b m2 fqProducts2) + d2.toNat * 3632069959 =
      fqConvolution2 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hvals2, ← hdm2, fqProducts2_convolution, haNat, hbNat]
  have hcol2 : 4294967296 * c3.toNat = c2.toNat + fqConvolution2 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    calc
      _ = montProductSum (montFactorValues a b m2 fqProducts2) + c2.toNat +
          d2.toNat * 3632069959 := hEq2
      _ = c2.toNat + (montProductSum (montFactorValues a b m2 fqProducts2) +
          d2.toNat * 3632069959) := by ac_rfl
      _ = _ := congrArg (fun x => c2.toNat + x) hprod2
  have hvals3 : montFactorValues a b m3 fqProducts3 = montFactorValues a b m8 fqProducts3 := by
    simp [montFactorValues, fqProducts3, montFactorValue, m1, m2, m3, m4, m5, m6, m7, m8]
  have hdm3 : m8 3 = d3 := by simp [m1, m2, m3, m4, m5, m6, m7, m8]
  have hprod3 : montProductSum (montFactorValues a b m3 fqProducts3) + d3.toNat * 3632069959 =
      fqConvolution3 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hvals3, ← hdm3, fqProducts3_convolution, haNat, hbNat]
  have hcol3 : 4294967296 * c4.toNat = c3.toNat + fqConvolution3 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    calc
      _ = montProductSum (montFactorValues a b m3 fqProducts3) + c3.toNat +
          d3.toNat * 3632069959 := hEq3
      _ = c3.toNat + (montProductSum (montFactorValues a b m3 fqProducts3) +
          d3.toNat * 3632069959) := by ac_rfl
      _ = _ := congrArg (fun x => c3.toNat + x) hprod3
  have hvals4 : montFactorValues a b m4 fqProducts4 = montFactorValues a b m8 fqProducts4 := by
    simp [montFactorValues, fqProducts4, montFactorValue, m1, m2, m3, m4, m5, m6, m7, m8]
  have hdm4 : m8 4 = d4 := by simp [m1, m2, m3, m4, m5, m6, m7, m8]
  have hprod4 : montProductSum (montFactorValues a b m4 fqProducts4) + d4.toNat * 3632069959 =
      fqConvolution4 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hvals4, ← hdm4, fqProducts4_convolution, haNat, hbNat]
  have hcol4 : 4294967296 * c5.toNat = c4.toNat + fqConvolution4 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    calc
      _ = montProductSum (montFactorValues a b m4 fqProducts4) + c4.toNat +
          d4.toNat * 3632069959 := hEq4
      _ = c4.toNat + (montProductSum (montFactorValues a b m4 fqProducts4) +
          d4.toNat * 3632069959) := by ac_rfl
      _ = _ := congrArg (fun x => c4.toNat + x) hprod4
  have hvals5 : montFactorValues a b m5 fqProducts5 = montFactorValues a b m8 fqProducts5 := by
    simp [montFactorValues, fqProducts5, montFactorValue, m1, m2, m3, m4, m5, m6, m7, m8]
  have hdm5 : m8 5 = d5 := by simp [m1, m2, m3, m4, m5, m6, m7, m8]
  have hprod5 : montProductSum (montFactorValues a b m5 fqProducts5) + d5.toNat * 3632069959 =
      fqConvolution5 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hvals5, ← hdm5, fqProducts5_convolution, haNat, hbNat]
  have hcol5 : 4294967296 * c6.toNat = c5.toNat + fqConvolution5 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    calc
      _ = montProductSum (montFactorValues a b m5 fqProducts5) + c5.toNat +
          d5.toNat * 3632069959 := hEq5
      _ = c5.toNat + (montProductSum (montFactorValues a b m5 fqProducts5) +
          d5.toNat * 3632069959) := by ac_rfl
      _ = _ := congrArg (fun x => c5.toNat + x) hprod5
  have hvals6 : montFactorValues a b m6 fqProducts6 = montFactorValues a b m8 fqProducts6 := by
    simp [montFactorValues, fqProducts6, montFactorValue, m1, m2, m3, m4, m5, m6, m7, m8]
  have hdm6 : m8 6 = d6 := by simp [m1, m2, m3, m4, m5, m6, m7, m8]
  have hprod6 : montProductSum (montFactorValues a b m6 fqProducts6) + d6.toNat * 3632069959 =
      fqConvolution6 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hvals6, ← hdm6, fqProducts6_convolution, haNat, hbNat]
  have hcol6 : 4294967296 * c7.toNat = c6.toNat + fqConvolution6 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    calc
      _ = montProductSum (montFactorValues a b m6 fqProducts6) + c6.toNat +
          d6.toNat * 3632069959 := hEq6
      _ = c6.toNat + (montProductSum (montFactorValues a b m6 fqProducts6) +
          d6.toNat * 3632069959) := by ac_rfl
      _ = _ := congrArg (fun x => c6.toNat + x) hprod6
  have hvals7 : montFactorValues a b m7 fqProducts7 = montFactorValues a b m8 fqProducts7 := by
    simp [montFactorValues, fqProducts7, montFactorValue, m1, m2, m3, m4, m5, m6, m7, m8]
  have hdm7 : m8 7 = d7 := by simp [m1, m2, m3, m4, m5, m6, m7, m8]
  have hprod7 : montProductSum (montFactorValues a b m7 fqProducts7) + d7.toNat * 3632069959 =
      fqConvolution7 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hvals7, ← hdm7, fqProducts7_convolution, haNat, hbNat]
  have hcol7 : 4294967296 * c8.toNat = c7.toNat + fqConvolution7 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    calc
      _ = montProductSum (montFactorValues a b m7 fqProducts7) + c7.toNat +
          d7.toNat * 3632069959 := hEq7
      _ = c7.toNat + (montProductSum (montFactorValues a b m7 fqProducts7) +
          d7.toNat * 3632069959) := by ac_rfl
      _ = _ := congrArg (fun x => c7.toNat + x) hprod7
  have hud0 : u7 0 = d8 := by simp [u1, u2, u3, u4, u5, u6, u7]
  have hcol8 : (u7 0).toNat + 4294967296 * c9.toNat = c8.toNat +
      fqConvolution8 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hud0]
    calc
      _ = montProductSum (montFactorValues a b m8 fqProducts8) + c8.toNat := hEq8
      _ = _ := by rw [fqProducts8_convolution, haNat, hbNat, Nat.add_comm]
  have hud1 : u7 1 = d9 := by simp [u1, u2, u3, u4, u5, u6, u7]
  have hcol9 : (u7 1).toNat + 4294967296 * c10.toNat = c9.toNat +
      fqConvolution9 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hud1]
    calc
      _ = montProductSum (montFactorValues a b m8 fqProducts9) + c9.toNat := hEq9
      _ = _ := by rw [fqProducts9_convolution, haNat, hbNat, Nat.add_comm]
  have hud2 : u7 2 = d10 := by simp [u1, u2, u3, u4, u5, u6, u7]
  have hcol10 : (u7 2).toNat + 4294967296 * c11.toNat = c10.toNat +
      fqConvolution10 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hud2]
    calc
      _ = montProductSum (montFactorValues a b m8 fqProducts10) + c10.toNat := hEq10
      _ = _ := by rw [fqProducts10_convolution, haNat, hbNat, Nat.add_comm]
  have hud3 : u7 3 = d11 := by simp [u1, u2, u3, u4, u5, u6, u7]
  have hcol11 : (u7 3).toNat + 4294967296 * c12.toNat = c11.toNat +
      fqConvolution11 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hud3]
    calc
      _ = montProductSum (montFactorValues a b m8 fqProducts11) + c11.toNat := hEq11
      _ = _ := by rw [fqProducts11_convolution, haNat, hbNat, Nat.add_comm]
  have hud4 : u7 4 = d12 := by simp [u1, u2, u3, u4, u5, u6, u7]
  have hcol12 : (u7 4).toNat + 4294967296 * c13.toNat = c12.toNat +
      fqConvolution12 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hud4]
    calc
      _ = montProductSum (montFactorValues a b m8 fqProducts12) + c12.toNat := hEq12
      _ = _ := by rw [fqProducts12_convolution, haNat, hbNat, Nat.add_comm]
  have hud5 : u7 5 = d13 := by simp [u1, u2, u3, u4, u5, u6, u7]
  have hcol13 : (u7 5).toNat + 4294967296 * c14.toNat = c13.toNat +
      fqConvolution13 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hud5]
    calc
      _ = montProductSum (montFactorValues a b m8 fqProducts13) + c13.toNat := hEq13
      _ = _ := by rw [fqProducts13_convolution, haNat, hbNat, Nat.add_comm]
  have hud6 : u7 6 = d14 := by simp [u1, u2, u3, u4, u5, u6, u7]
  have hcol14 : (u7 6).toNat + 4294967296 * c15.toNat = c14.toNat +
      fqConvolution14 (limbs256Digits A) (limbs256Digits B) (fun i => (m8 i).toNat) := by
    rw [hud6]
    calc
      _ = montProductSum (montFactorValues a b m8 fqProducts14) + c14.toNat := hEq14
      _ = _ := by rw [fqProducts14_convolution, haNat, hbNat, Nat.add_comm]
  let carries : Fin 16 → Nat := fun i => match i.val with
    | 0 => 0
    | 1 => c1.toNat
    | 2 => c2.toNat
    | 3 => c3.toNat
    | 4 => c4.toNat
    | 5 => c5.toNat
    | 6 => c6.toNat
    | 7 => c7.toNat
    | 8 => c8.toNat
    | 9 => c9.toNat
    | 10 => c10.toNat
    | 11 => c11.toNat
    | 12 => c12.toNat
    | 13 => c13.toNat
    | 14 => c14.toNat
    | _ => c15.toNat
  let digits : Fin 7 → Nat := fun i => (u7 i).toNat
  have hresult := fqColumns_correct_left A B (fun i => (m8 i).toNat) carries digits hA hm8
    (by rfl) hcol0 hcol1 hcol2 hcol3 hcol4 hcol5 hcol6 hcol7
    hcol8 hcol9 hcol10 hcol11 hcol12 hcol13 hcol14
  let outputWords : Fin 8 → BitVec 64 := fun i => match i.val with
    | 0 => u7 0
    | 1 => u7 1
    | 2 => u7 2
    | 3 => u7 3
    | 4 => u7 4
    | 5 => u7 5
    | 6 => u7 6
    | _ => c15
  have hraw : montRadix8 (fun i => (outputWords i).toNat) < 2 ^ 256 := by
    simpa [montRadix8, outputWords, carries, digits] using hresult.1
  have hlast : c15.toNat < 2 ^ 32 :=
    montFinalDigit_lt (fun i => (outputWords i).toNat) hraw
  have houtput : ∀ i, (outputWords i).toNat < 2 ^ 32 := by
    intro i
    fin_cases i
    · exact hu7 0
    · exact hu7 1
    · exact hu7 2
    · exact hu7 3
    · exact hu7 4
    · exact hu7 5
    · exact hu7 6
    · exact hlast
  obtain ⟨out, hret, hvalue⟩ := fqMulFinish_returned (s := s15) outputWords ret hCode15 houtput
    (by exact hS15.uWords 0) (by exact hS15.uWords 1) (by exact hS15.uWords 2)
    (by exact hS15.uWords 3) (by exact hS15.uWords 4) (by exact hS15.uWords 5)
    (by exact hS15.uWords 6) hS15.carryWord he
  refine ⟨out, hret, ?_, ?_⟩
  · rw [hvalue]
    simpa [montRadix8, outputWords, carries, digits] using hresult.2.1
  · rw [hvalue]
    simpa [montRadix8, outputWords, carries, digits] using hresult.2.2

theorem fqMul_returned_canonical_left {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (A B : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some A.toValue)
    (hb : s.locals.lookup (ofString "b") = some B.toValue)
    (hA : A.toNat < fqModulus.toNat)
    (he : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_mul) =
      (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * out.toNat) (A.toNat * B.toNat) := by
  rw [fqMul_source_eq] at he
  change evaluateHOLFiniteState s (montDeclareWords fqMulInitializers fqMulColumn0) = _ at he
  have htrace := fqInitializers_trace s A B ha hb
  obtain ⟨inner, hcolumns⟩ := montInitTrace_returned htrace fqMulColumn0 ret he
  exact fqMulColumns_returned_left
    (s := montSetWords s (fqInitAssignments A B fqInitSpecs)) A B ret
    ((montSetWords_code s _).trans hc) hA (fqInitialState_slots s A B) hcolumns

theorem fqMul_callee_returned_left {F : Type} {s bpost : PanSemStateFiniteExact 64 F}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (A B : Limbs256) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (hA : A.toNat < fqModulus.toNat)
    (hlk : lookupCodeHOLFinite s.code.lookup (ofString "fq_mul") [A.toValue, B.toValue] =
      some (body, callee, rs))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned ret), bpost)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * out.toNat) (A.toNat * B.toNat) := by
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "fq_mul") (ofString "a") (ofString "b")
    arithU256Shape arithU256Shape arithU256Shape
    (arithSourceBody Guest.Software.guestFn_fq_mul) A.toValue B.toValue
    (by decide) arith_lookup_fq_mul hlk
  exact fqMul_returned_canonical_left
    (s := callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", A.toValue)).update
      (ofString "b", B.toValue))) A B ret hc
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hA hr

theorem fqMul_decCall_none_frame_left {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64) (A B : Limbs256)
    (hc : s.code = originalRuntimeCode) (hA : A.toNat < fqModulus.toNat)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [A.toValue, B.toValue])
    (hr : evaluateHOLFiniteState s (.decCall temp arithU256Shape (ofString "fq_mul") args cont) =
      (none, post)) :
    ∃ (out : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * out.toNat) (A.toNat * B.toNat) ∧
      resumed.locals = s.locals.update (temp, out.toValue) ∧ resumed.code = s.code ∧
      resumed.memory = s.memory ∧ resumed.memaddrs = s.memaddrs ∧
      evaluateHOLFiniteState resumed cont = (none, inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp, s.locals.lookup temp) ∧
      post.memory = inner.memory := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    he, hlk, hclock, hrun, hshape, hlocals, hcode, hcont, hpost, hresumed, hfinal⟩ :=
    arith_decCall_none_state hr
  have hv : values = [A.toValue, B.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  obtain ⟨out, hret, hbound, hprod⟩ := fqMul_callee_returned_left A B value hc hA hlk hrun
  have hpbody : MemoryPure body := fqMul_function_memoryPure [A.toValue, B.toValue] body callee rs
    (by simpa only [hc] using hlk)
  have hmem := hpbody (callEntryStateHOLFinite s callee) hc
  have hdomain := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).2.1
  rw [hrun] at hmem hdomain
  refine ⟨out, resumed, inner, hbound, hprod, ?_, hcode, ?_, ?_, hcont, hpost, ?_⟩
  · simpa only [hret] using hlocals
  · rw [hresumed]; exact hmem
  · rw [hresumed]; exact hdomain
  · rw [hfinal]

end InitECandidate.Solver.Wave8GuestInv.Arith
