import InitECandidate.Proofs.FrontendStages.Crep.Translate294
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody310_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody310_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 12)

def crepBody310_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody310_3 : CrepProg (BitVec 64) :=
.seq crepBody310_1 crepBody310_2

def crepBody310_4 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 40#64) crepBody310_3

def crepBody310_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 6#64

def crepBody310_6 : CrepProg (BitVec 64) :=
.seq crepBody310_4 crepBody310_5

def crepBody310_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 0#64)) crepBody310_6 crepBody310_2

def crepBody310_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "u256_lt"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.const 13822214165235122497#64, Flapjack.CrepExp.const 13451932020343611451#64,
    Flapjack.CrepExp.const 18446744073709551614#64, Flapjack.CrepExp.const 18446744073709551615#64]

def crepBody310_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 13)

def crepBody310_10 : CrepProg (BitVec 64) :=
.seq crepBody310_9 crepBody310_2

def crepBody310_11 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 40#64) crepBody310_10

def crepBody310_12 : CrepProg (BitVec 64) :=
.seq crepBody310_11 crepBody310_5

def crepBody310_13 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.const 0#64)) crepBody310_12 crepBody310_2

def crepBody310_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10]

def crepBody310_15 : CrepProg (BitVec 64) :=
.seq crepBody310_13 crepBody310_14

def crepBody310_16 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 41#64) crepBody310_10

def crepBody310_17 : CrepProg (BitVec 64) :=
.seq crepBody310_16 crepBody310_5

def crepBody310_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 0#64)) crepBody310_17 crepBody310_2

def crepBody310_19 : CrepProg (BitVec 64) :=
.seq crepBody310_15 crepBody310_18

def crepBody310_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "u256_gt"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.const 16134479119472337056#64, Flapjack.CrepExp.const 6725966010171805725#64,
    Flapjack.CrepExp.const 18446744073709551615#64, Flapjack.CrepExp.const 9223372036854775807#64]

def crepBody310_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 14)

def crepBody310_22 : CrepProg (BitVec 64) :=
.seq crepBody310_21 crepBody310_2

def crepBody310_23 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 41#64) crepBody310_22

def crepBody310_24 : CrepProg (BitVec 64) :=
.seq crepBody310_23 crepBody310_5

def crepBody310_25 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 0#64)) crepBody310_24 crepBody310_2

def crepBody310_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "u256_fits_word"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18]

def crepBody310_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "signing_hash_pre155" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2]

def crepBody310_28 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody310_27

def crepBody310_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 27#64]]

def crepBody310_30 : CrepProg (BitVec 64) :=
.seq crepBody310_28 crepBody310_29

def crepBody310_31 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.const 27#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.const 28#64)])) crepBody310_30 crepBody310_2

def crepBody310_32 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 0#64)) crepBody310_31 crepBody310_2

def crepBody310_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24, 25, 26, 27], none)) "u256_add"
  [Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23,
    Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23]

def crepBody310_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([28, 29, 30, 31], none)) "u256_add"
  [Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26, Flapjack.CrepExp.var 27,
    Flapjack.CrepExp.const 35#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody310_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32, 33, 34, 35], none)) "u256_add"
  [Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26, Flapjack.CrepExp.var 27,
    Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody310_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([36], none)) "u256_eq"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.var 28, Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30, Flapjack.CrepExp.var 31]

def crepBody310_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([37], none)) "u256_eq"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.var 32, Flapjack.CrepExp.var 33, Flapjack.CrepExp.var 34, Flapjack.CrepExp.var 35]

def crepBody310_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 38)

def crepBody310_39 : CrepProg (BitVec 64) :=
.seq crepBody310_38 crepBody310_2

def crepBody310_40 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 42#64) crepBody310_39

def crepBody310_41 : CrepProg (BitVec 64) :=
.seq crepBody310_40 crepBody310_5

def crepBody310_42 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 36) (Flapjack.CrepExp.const 0#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 37) (Flapjack.CrepExp.const 0#64))]) crepBody310_41 crepBody310_2

def crepBody310_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([38], none)) "signing_hash_155"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody310_44 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 0#64) crepBody310_43

def crepBody310_45 : CrepProg (BitVec 64) :=
.seq crepBody310_42 crepBody310_44

def crepBody310_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 37]

def crepBody310_47 : CrepProg (BitVec 64) :=
.seq crepBody310_45 crepBody310_46

def crepBody310_48 : CrepProg (BitVec 64) :=
.seq crepBody310_37 crepBody310_47

def crepBody310_49 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody310_48

def crepBody310_50 : CrepProg (BitVec 64) :=
.seq crepBody310_36 crepBody310_49

def crepBody310_51 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody310_50

def crepBody310_52 : CrepProg (BitVec 64) :=
.seq crepBody310_35 crepBody310_51

def crepBody310_53 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.const 0#64) crepBody310_52

def crepBody310_54 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 0#64) crepBody310_53

def crepBody310_55 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 0#64) crepBody310_54

def crepBody310_56 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody310_55

def crepBody310_57 : CrepProg (BitVec 64) :=
.seq crepBody310_34 crepBody310_56

def crepBody310_58 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody310_57

def crepBody310_59 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.const 0#64) crepBody310_58

def crepBody310_60 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody310_59

def crepBody310_61 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody310_60

def crepBody310_62 : CrepProg (BitVec 64) :=
.seq crepBody310_33 crepBody310_61

def crepBody310_63 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody310_62

def crepBody310_64 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody310_63

def crepBody310_65 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody310_64

def crepBody310_66 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody310_65

def crepBody310_67 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody310_66

def crepBody310_68 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody310_67

def crepBody310_69 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody310_68

def crepBody310_70 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 1) crepBody310_69

def crepBody310_71 : CrepProg (BitVec 64) :=
.seq crepBody310_32 crepBody310_70

def crepBody310_72 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 0#64)) crepBody310_71 crepBody310_2

def crepBody310_73 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 20)

def crepBody310_74 : CrepProg (BitVec 64) :=
.seq crepBody310_73 crepBody310_2

def crepBody310_75 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 43#64) crepBody310_74

def crepBody310_76 : CrepProg (BitVec 64) :=
.seq crepBody310_75 crepBody310_5

def crepBody310_77 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 0#64)) crepBody310_76 crepBody310_2

def crepBody310_78 : CrepProg (BitVec 64) :=
.seq crepBody310_72 crepBody310_77

def crepBody310_79 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 1#64) (Flapjack.CrepExp.var 15)) crepBody310_76 crepBody310_2

def crepBody310_80 : CrepProg (BitVec 64) :=
.seq crepBody310_78 crepBody310_79

def crepBody310_81 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "signing_hash_2930" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2]

def crepBody310_82 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody310_81

def crepBody310_83 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 1#64)) crepBody310_82 crepBody310_2

def crepBody310_84 : CrepProg (BitVec 64) :=
.seq crepBody310_80 crepBody310_83

def crepBody310_85 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "signing_hash_1559" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2]

def crepBody310_86 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody310_85

def crepBody310_87 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 2#64)) crepBody310_86 crepBody310_2

def crepBody310_88 : CrepProg (BitVec 64) :=
.seq crepBody310_84 crepBody310_87

def crepBody310_89 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "signing_hash_4844" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2]

def crepBody310_90 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody310_89

def crepBody310_91 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 3#64)) crepBody310_90 crepBody310_2

def crepBody310_92 : CrepProg (BitVec 64) :=
.seq crepBody310_88 crepBody310_91

def crepBody310_93 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "signing_hash_7702" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2]

def crepBody310_94 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody310_93

def crepBody310_95 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 4#64)) crepBody310_94 crepBody310_2

def crepBody310_96 : CrepProg (BitVec 64) :=
.seq crepBody310_92 crepBody310_95

def crepBody310_97 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 15]

def crepBody310_98 : CrepProg (BitVec 64) :=
.seq crepBody310_96 crepBody310_97

def crepBody310_99 : CrepProg (BitVec 64) :=
.seq crepBody310_26 crepBody310_98

def crepBody310_100 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody310_99

def crepBody310_101 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
      Flapjack.CrepExp.const 24#64])) crepBody310_100

def crepBody310_102 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
      Flapjack.CrepExp.const 16#64])) crepBody310_101

def crepBody310_103 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
      Flapjack.CrepExp.const 8#64])) crepBody310_102

def crepBody310_104 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64])) crepBody310_103

def crepBody310_105 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody310_104

def crepBody310_106 : CrepProg (BitVec 64) :=
.seq crepBody310_25 crepBody310_105

def crepBody310_107 : CrepProg (BitVec 64) :=
.seq crepBody310_20 crepBody310_106

def crepBody310_108 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody310_107

def crepBody310_109 : CrepProg (BitVec 64) :=
.seq crepBody310_19 crepBody310_108

def crepBody310_110 : CrepProg (BitVec 64) :=
.seq crepBody310_8 crepBody310_109

def crepBody310_111 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody310_110

def crepBody310_112 : CrepProg (BitVec 64) :=
.seq crepBody310_7 crepBody310_111

def crepBody310_113 : CrepProg (BitVec 64) :=
.seq crepBody310_0 crepBody310_112

def crepBody310_114 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody310_113

def crepBody310_115 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64],
      Flapjack.CrepExp.const 24#64])) crepBody310_114

def crepBody310_116 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64],
      Flapjack.CrepExp.const 16#64])) crepBody310_115

def crepBody310_117 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64],
      Flapjack.CrepExp.const 8#64])) crepBody310_116

def crepBody310_118 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64])) crepBody310_117

def crepBody310_119 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64],
      Flapjack.CrepExp.const 24#64])) crepBody310_118

def crepBody310_120 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64],
      Flapjack.CrepExp.const 16#64])) crepBody310_119

def crepBody310_121 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64],
      Flapjack.CrepExp.const 8#64])) crepBody310_120

def crepBody310_122 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64])) crepBody310_121

def data310 : CrepProg (BitVec 64) := crepBody310_122
def output310 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 105#8, 103#8, 110#8, 97#8, 116#8, 117#8, 114#8, 101#8, 95#8, 114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8,
    121#8, 95#8, 112#8, 97#8, 114#8, 97#8, 109#8, 101#8, 116#8, 101#8, 114#8, 115#8], [0, 1, 2], crepProgToHOL data310)
end InitECandidate.Proofs.FrontendStages.Crep
