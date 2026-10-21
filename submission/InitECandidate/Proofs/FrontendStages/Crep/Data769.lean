import InitECandidate.Proofs.FrontendStages.Crep.Translate753
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody769_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_ecrecover" []

def crepBody769_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_0

def crepBody769_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody769_3 : CrepProg (BitVec 64) :=
.seq crepBody769_1 crepBody769_2

def crepBody769_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody769_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 1#64)) crepBody769_3 crepBody769_4

def crepBody769_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_sha256" []

def crepBody769_7 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_6

def crepBody769_8 : CrepProg (BitVec 64) :=
.seq crepBody769_7 crepBody769_2

def crepBody769_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 2#64)) crepBody769_8 crepBody769_4

def crepBody769_10 : CrepProg (BitVec 64) :=
.seq crepBody769_5 crepBody769_9

def crepBody769_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_ripemd160" []

def crepBody769_12 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_11

def crepBody769_13 : CrepProg (BitVec 64) :=
.seq crepBody769_12 crepBody769_2

def crepBody769_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 3#64)) crepBody769_13 crepBody769_4

def crepBody769_15 : CrepProg (BitVec 64) :=
.seq crepBody769_10 crepBody769_14

def crepBody769_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_identity" []

def crepBody769_17 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_16

def crepBody769_18 : CrepProg (BitVec 64) :=
.seq crepBody769_17 crepBody769_2

def crepBody769_19 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 4#64)) crepBody769_18 crepBody769_4

def crepBody769_20 : CrepProg (BitVec 64) :=
.seq crepBody769_15 crepBody769_19

def crepBody769_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_alt_bn128_add" []

def crepBody769_22 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_21

def crepBody769_23 : CrepProg (BitVec 64) :=
.seq crepBody769_22 crepBody769_2

def crepBody769_24 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 6#64)) crepBody769_23 crepBody769_4

def crepBody769_25 : CrepProg (BitVec 64) :=
.seq crepBody769_20 crepBody769_24

def crepBody769_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_alt_bn128_mul" []

def crepBody769_27 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_26

def crepBody769_28 : CrepProg (BitVec 64) :=
.seq crepBody769_27 crepBody769_2

def crepBody769_29 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 7#64)) crepBody769_28 crepBody769_4

def crepBody769_30 : CrepProg (BitVec 64) :=
.seq crepBody769_25 crepBody769_29

def crepBody769_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_alt_bn128_pairing_check" []

def crepBody769_32 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_31

def crepBody769_33 : CrepProg (BitVec 64) :=
.seq crepBody769_32 crepBody769_2

def crepBody769_34 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 8#64)) crepBody769_33 crepBody769_4

def crepBody769_35 : CrepProg (BitVec 64) :=
.seq crepBody769_30 crepBody769_34

def crepBody769_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_modexp" []

def crepBody769_37 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_36

def crepBody769_38 : CrepProg (BitVec 64) :=
.seq crepBody769_37 crepBody769_2

def crepBody769_39 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 5#64)) crepBody769_38 crepBody769_4

def crepBody769_40 : CrepProg (BitVec 64) :=
.seq crepBody769_35 crepBody769_39

def crepBody769_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_blake2f" []

def crepBody769_42 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_41

def crepBody769_43 : CrepProg (BitVec 64) :=
.seq crepBody769_42 crepBody769_2

def crepBody769_44 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 9#64)) crepBody769_43 crepBody769_4

def crepBody769_45 : CrepProg (BitVec 64) :=
.seq crepBody769_40 crepBody769_44

def crepBody769_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_kzg_point_evaluation" []

def crepBody769_47 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_46

def crepBody769_48 : CrepProg (BitVec 64) :=
.seq crepBody769_47 crepBody769_2

def crepBody769_49 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 10#64)) crepBody769_48 crepBody769_4

def crepBody769_50 : CrepProg (BitVec 64) :=
.seq crepBody769_45 crepBody769_49

def crepBody769_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_bls_g1_add" []

def crepBody769_52 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_51

def crepBody769_53 : CrepProg (BitVec 64) :=
.seq crepBody769_52 crepBody769_2

def crepBody769_54 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 11#64)) crepBody769_53 crepBody769_4

def crepBody769_55 : CrepProg (BitVec 64) :=
.seq crepBody769_50 crepBody769_54

def crepBody769_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_bls_g1_msm" []

def crepBody769_57 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_56

def crepBody769_58 : CrepProg (BitVec 64) :=
.seq crepBody769_57 crepBody769_2

def crepBody769_59 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 12#64)) crepBody769_58 crepBody769_4

def crepBody769_60 : CrepProg (BitVec 64) :=
.seq crepBody769_55 crepBody769_59

def crepBody769_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_bls_g2_add" []

def crepBody769_62 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_61

def crepBody769_63 : CrepProg (BitVec 64) :=
.seq crepBody769_62 crepBody769_2

def crepBody769_64 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 13#64)) crepBody769_63 crepBody769_4

def crepBody769_65 : CrepProg (BitVec 64) :=
.seq crepBody769_60 crepBody769_64

def crepBody769_66 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_bls_g2_msm" []

def crepBody769_67 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_66

def crepBody769_68 : CrepProg (BitVec 64) :=
.seq crepBody769_67 crepBody769_2

def crepBody769_69 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 14#64)) crepBody769_68 crepBody769_4

def crepBody769_70 : CrepProg (BitVec 64) :=
.seq crepBody769_65 crepBody769_69

def crepBody769_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_bls_pairing" []

def crepBody769_72 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_71

def crepBody769_73 : CrepProg (BitVec 64) :=
.seq crepBody769_72 crepBody769_2

def crepBody769_74 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 15#64)) crepBody769_73 crepBody769_4

def crepBody769_75 : CrepProg (BitVec 64) :=
.seq crepBody769_70 crepBody769_74

def crepBody769_76 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_bls_map_fp_to_g1" []

def crepBody769_77 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_76

def crepBody769_78 : CrepProg (BitVec 64) :=
.seq crepBody769_77 crepBody769_2

def crepBody769_79 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 16#64)) crepBody769_78 crepBody769_4

def crepBody769_80 : CrepProg (BitVec 64) :=
.seq crepBody769_75 crepBody769_79

def crepBody769_81 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_bls_map_fp2_to_g2" []

def crepBody769_82 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_81

def crepBody769_83 : CrepProg (BitVec 64) :=
.seq crepBody769_82 crepBody769_2

def crepBody769_84 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 17#64)) crepBody769_83 crepBody769_4

def crepBody769_85 : CrepProg (BitVec 64) :=
.seq crepBody769_80 crepBody769_84

def crepBody769_86 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pre_p256verify" []

def crepBody769_87 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody769_86

def crepBody769_88 : CrepProg (BitVec 64) :=
.seq crepBody769_87 crepBody769_2

def crepBody769_89 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 18#64)) crepBody769_88 crepBody769_4

def crepBody769_90 : CrepProg (BitVec 64) :=
.seq crepBody769_85 crepBody769_89

def crepBody769_91 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 1)

def crepBody769_92 : CrepProg (BitVec 64) :=
.seq crepBody769_91 crepBody769_4

def crepBody769_93 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 99#64) crepBody769_92

def crepBody769_94 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 4#64

def crepBody769_95 : CrepProg (BitVec 64) :=
.seq crepBody769_93 crepBody769_94

def crepBody769_96 : CrepProg (BitVec 64) :=
.seq crepBody769_90 crepBody769_95

def crepBody769_97 : CrepProg (BitVec 64) :=
.seq crepBody769_96 crepBody769_2

def data769 : CrepProg (BitVec 64) := crepBody769_97
def output769 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 117#8, 110#8, 95#8, 112#8, 114#8, 101#8, 99#8, 111#8, 109#8, 112#8, 105#8, 108#8, 101#8], [0], crepProgToHOL data769)
end InitECandidate.Proofs.FrontendStages.Crep
