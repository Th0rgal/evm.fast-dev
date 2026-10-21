import InitECandidate.Proofs.FrontendStages.Crep.Translate616
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody632_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "bn254_init" []

def crepBody632_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody632_0

def crepBody632_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody632_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody632_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 192#64]

def crepBody632_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody632_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 192#64]

def crepBody632_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc" [Flapjack.CrepExp.const 1152#64]

def crepBody632_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "alloc" [Flapjack.CrepExp.const 1152#64]

def crepBody632_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 384#64]

def crepBody632_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "alloc" [Flapjack.CrepExp.const 384#64]

def crepBody632_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "alloc" [Flapjack.CrepExp.const 384#64]

def crepBody632_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "alloc" [Flapjack.CrepExp.const 384#64]

def crepBody632_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "alloc" [Flapjack.CrepExp.const 384#64]

def crepBody632_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "fe_set_one" [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 11]

def crepBody632_15 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody632_14

def crepBody632_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "fe_set_one" [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 12]

def crepBody632_17 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody632_16

def crepBody632_18 : CrepProg (BitVec 64) :=
.seq crepBody632_15 crepBody632_17

def crepBody632_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "bn254_parse_g1" [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 3]

def crepBody632_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody632_21 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody632_20

def crepBody632_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 2#64]

def crepBody632_23 : CrepProg (BitVec 64) :=
.seq crepBody632_21 crepBody632_22

def crepBody632_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody632_25 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.const 0#64)) crepBody632_23 crepBody632_24

def crepBody632_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "bn254_parse_g2"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 64#64],
    Flapjack.CrepExp.var 4]

def crepBody632_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody632_28 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody632_27

def crepBody632_29 : CrepProg (BitVec 64) :=
.seq crepBody632_28 crepBody632_22

def crepBody632_30 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.const 0#64)) crepBody632_29 crepBody632_24

def crepBody632_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "ecp_mul"
  [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.const 4891460686036598785#64, Flapjack.CrepExp.const 2896914383306846353#64,
    Flapjack.CrepExp.const 13281191951274694749#64, Flapjack.CrepExp.const 3486998266802970665#64]

def crepBody632_32 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody632_31

def crepBody632_33 : CrepProg (BitVec 64) :=
.seq crepBody632_30 crepBody632_32

def crepBody632_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "ecp_is_inf" [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 5]

def crepBody632_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody632_36 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody632_35

def crepBody632_37 : CrepProg (BitVec 64) :=
.seq crepBody632_36 crepBody632_22

def crepBody632_38 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 0#64)) crepBody632_37 crepBody632_24

def crepBody632_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "ecp_mul"
  [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.const 4891460686036598785#64, Flapjack.CrepExp.const 2896914383306846353#64,
    Flapjack.CrepExp.const 13281191951274694749#64, Flapjack.CrepExp.const 3486998266802970665#64]

def crepBody632_40 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody632_39

def crepBody632_41 : CrepProg (BitVec 64) :=
.seq crepBody632_38 crepBody632_40

def crepBody632_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "ecp_is_inf" [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 6]

def crepBody632_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody632_44 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody632_43

def crepBody632_45 : CrepProg (BitVec 64) :=
.seq crepBody632_44 crepBody632_22

def crepBody632_46 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.const 0#64)) crepBody632_45 crepBody632_24

def crepBody632_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "ecp_is_inf" [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 3]

def crepBody632_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "ecp_is_inf" [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 4]

def crepBody632_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fq12_twist" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 4]

def crepBody632_50 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody632_49

def crepBody632_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fq12_cast" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 3]

def crepBody632_52 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody632_51

def crepBody632_53 : CrepProg (BitVec 64) :=
.seq crepBody632_50 crepBody632_52

def crepBody632_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "bn254_miller_raw"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody632_55 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody632_54

def crepBody632_56 : CrepProg (BitVec 64) :=
.seq crepBody632_53 crepBody632_55

def crepBody632_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fq12_mul"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 9]

def crepBody632_58 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody632_57

def crepBody632_59 : CrepProg (BitVec 64) :=
.seq crepBody632_56 crepBody632_58

def crepBody632_60 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fq12_mul"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 10]

def crepBody632_61 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody632_60

def crepBody632_62 : CrepProg (BitVec 64) :=
.seq crepBody632_59 crepBody632_61

def crepBody632_63 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 14 (Flapjack.CrepExp.const 1#64)

def crepBody632_64 : CrepProg (BitVec 64) :=
.seq crepBody632_63 crepBody632_24

def crepBody632_65 : CrepProg (BitVec 64) :=
.seq crepBody632_62 crepBody632_64

def crepBody632_66 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.or [Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22])
  (Flapjack.CrepExp.const 0#64)) crepBody632_65 crepBody632_24

def crepBody632_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 15 (Flapjack.CrepExp.var 23)

def crepBody632_68 : CrepProg (BitVec 64) :=
.seq crepBody632_67 crepBody632_24

def crepBody632_69 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 1#64]) crepBody632_68

def crepBody632_70 : CrepProg (BitVec 64) :=
.seq crepBody632_66 crepBody632_69

def crepBody632_71 : CrepProg (BitVec 64) :=
.seq crepBody632_48 crepBody632_70

def crepBody632_72 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody632_71

def crepBody632_73 : CrepProg (BitVec 64) :=
.seq crepBody632_47 crepBody632_72

def crepBody632_74 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody632_73

def crepBody632_75 : CrepProg (BitVec 64) :=
.seq crepBody632_46 crepBody632_74

def crepBody632_76 : CrepProg (BitVec 64) :=
.seq crepBody632_42 crepBody632_75

def crepBody632_77 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody632_76

def crepBody632_78 : CrepProg (BitVec 64) :=
.seq crepBody632_41 crepBody632_77

def crepBody632_79 : CrepProg (BitVec 64) :=
.seq crepBody632_34 crepBody632_78

def crepBody632_80 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody632_79

def crepBody632_81 : CrepProg (BitVec 64) :=
.seq crepBody632_33 crepBody632_80

def crepBody632_82 : CrepProg (BitVec 64) :=
.seq crepBody632_26 crepBody632_81

def crepBody632_83 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody632_82

def crepBody632_84 : CrepProg (BitVec 64) :=
.seq crepBody632_25 crepBody632_83

def crepBody632_85 : CrepProg (BitVec 64) :=
.seq crepBody632_19 crepBody632_84

def crepBody632_86 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody632_85

def crepBody632_87 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 192#64]]) crepBody632_86

def crepBody632_88 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.var 1)) crepBody632_87

def crepBody632_89 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "fq12_inv" [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 12]

def crepBody632_90 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody632_89

def crepBody632_91 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "fq12_mul"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody632_92 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody632_91

def crepBody632_93 : CrepProg (BitVec 64) :=
.seq crepBody632_90 crepBody632_92

def crepBody632_94 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "fq12_pow_words"
  [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 384#64]),
    Flapjack.CrepExp.const 44#64]

def crepBody632_95 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody632_94

def crepBody632_96 : CrepProg (BitVec 64) :=
.seq crepBody632_93 crepBody632_95

def crepBody632_97 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "memzero" [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 384#64]

def crepBody632_98 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody632_97

def crepBody632_99 : CrepProg (BitVec 64) :=
.seq crepBody632_96 crepBody632_98

def crepBody632_100 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.var 18)

def crepBody632_101 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 19)

def crepBody632_102 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 20)

def crepBody632_103 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 21)

def crepBody632_104 : CrepProg (BitVec 64) :=
.seq crepBody632_103 crepBody632_24

def crepBody632_105 : CrepProg (BitVec 64) :=
.seq crepBody632_102 crepBody632_104

def crepBody632_106 : CrepProg (BitVec 64) :=
.seq crepBody632_101 crepBody632_105

def crepBody632_107 : CrepProg (BitVec 64) :=
.seq crepBody632_100 crepBody632_106

def crepBody632_108 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 1011752739694698287#64) crepBody632_107

def crepBody632_109 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 7381016538464732716#64) crepBody632_108

def crepBody632_110 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 754611498739239741#64) crepBody632_109

def crepBody632_111 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 15230403791020821917#64) crepBody632_110

def crepBody632_112 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 9) crepBody632_111

def crepBody632_113 : CrepProg (BitVec 64) :=
.seq crepBody632_99 crepBody632_112

def crepBody632_114 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "memeq"
  [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 384#64]

def crepBody632_115 : CrepProg (BitVec 64) :=
.seq crepBody632_113 crepBody632_114

def crepBody632_116 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 1#64)) crepBody632_115 crepBody632_24

def crepBody632_117 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody632_118 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody632_117

def crepBody632_119 : CrepProg (BitVec 64) :=
.seq crepBody632_116 crepBody632_118

def crepBody632_120 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 16]

def crepBody632_121 : CrepProg (BitVec 64) :=
.seq crepBody632_119 crepBody632_120

def crepBody632_122 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 1#64) crepBody632_121

def crepBody632_123 : CrepProg (BitVec 64) :=
.seq crepBody632_88 crepBody632_122

def crepBody632_124 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody632_123

def crepBody632_125 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody632_124

def crepBody632_126 : CrepProg (BitVec 64) :=
.seq crepBody632_18 crepBody632_125

def crepBody632_127 : CrepProg (BitVec 64) :=
.seq crepBody632_13 crepBody632_126

def crepBody632_128 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody632_127

def crepBody632_129 : CrepProg (BitVec 64) :=
.seq crepBody632_12 crepBody632_128

def crepBody632_130 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody632_129

def crepBody632_131 : CrepProg (BitVec 64) :=
.seq crepBody632_11 crepBody632_130

def crepBody632_132 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody632_131

def crepBody632_133 : CrepProg (BitVec 64) :=
.seq crepBody632_10 crepBody632_132

def crepBody632_134 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody632_133

def crepBody632_135 : CrepProg (BitVec 64) :=
.seq crepBody632_9 crepBody632_134

def crepBody632_136 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody632_135

def crepBody632_137 : CrepProg (BitVec 64) :=
.seq crepBody632_8 crepBody632_136

def crepBody632_138 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody632_137

def crepBody632_139 : CrepProg (BitVec 64) :=
.seq crepBody632_7 crepBody632_138

def crepBody632_140 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody632_139

def crepBody632_141 : CrepProg (BitVec 64) :=
.seq crepBody632_6 crepBody632_140

def crepBody632_142 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody632_141

def crepBody632_143 : CrepProg (BitVec 64) :=
.seq crepBody632_5 crepBody632_142

def crepBody632_144 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody632_143

def crepBody632_145 : CrepProg (BitVec 64) :=
.seq crepBody632_4 crepBody632_144

def crepBody632_146 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody632_145

def crepBody632_147 : CrepProg (BitVec 64) :=
.seq crepBody632_3 crepBody632_146

def crepBody632_148 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody632_147

def crepBody632_149 : CrepProg (BitVec 64) :=
.seq crepBody632_2 crepBody632_148

def crepBody632_150 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody632_149

def crepBody632_151 : CrepProg (BitVec 64) :=
.seq crepBody632_1 crepBody632_150

def data632 : CrepProg (BitVec 64) := crepBody632_151
def output632 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 110#8, 50#8, 53#8, 52#8, 95#8, 112#8, 97#8, 105#8, 114#8, 105#8, 110#8, 103#8, 95#8, 99#8, 104#8, 101#8, 99#8,
    107#8], [0, 1], crepProgToHOL data632)
end InitECandidate.Proofs.FrontendStages.Crep
