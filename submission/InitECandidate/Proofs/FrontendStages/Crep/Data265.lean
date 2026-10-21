import InitECandidate.Proofs.FrontendStages.Crep.Translate249
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody265_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody265_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody265_2 : CrepProg (BitVec 64) :=
.seq crepBody265_0 crepBody265_1

def crepBody265_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "mpt_fail" [Flapjack.CrepExp.const 20#64]

def crepBody265_4 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody265_3

def crepBody265_5 : CrepProg (BitVec 64) :=
.seq crepBody265_2 crepBody265_4

def crepBody265_6 : CrepProg (BitVec 64) :=
.call (some (([3, 4, 5, 6]), some ((1#64), crepBody265_5))) ("rlp_decode_fully") ([Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1])

def crepBody265_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 1#64)) crepBody265_4 crepBody265_1

def crepBody265_8 : CrepProg (BitVec 64) :=
.seq crepBody265_6 crepBody265_7

def crepBody265_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9], none)) "rlp_list_to_slices" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody265_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "mpt_fail" [Flapjack.CrepExp.const 20#64]

def crepBody265_11 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody265_10

def crepBody265_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 4#64)) crepBody265_11 crepBody265_1

def crepBody265_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12, 13, 14], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody265_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody265_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19, 20, 21, 22], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody265_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23, 24, 25, 26], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody265_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "mpt_fail" [Flapjack.CrepExp.const 20#64]

def crepBody265_18 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody265_17

def crepBody265_19 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 23])
  (Flapjack.CrepExp.const 0#64)) crepBody265_18 crepBody265_1

def crepBody265_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "mpt_fail" [Flapjack.CrepExp.const 21#64]

def crepBody265_21 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody265_20

def crepBody265_22 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 8#64) (Flapjack.CrepExp.var 13)) crepBody265_21 crepBody265_1

def crepBody265_23 : CrepProg (BitVec 64) :=
.seq crepBody265_19 crepBody265_22

def crepBody265_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 27 (Flapjack.CrepExp.var 29)

def crepBody265_25 : CrepProg (BitVec 64) :=
.seq crepBody265_24 crepBody265_1

def crepBody265_26 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.var 27) (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 28])]) crepBody265_25

def crepBody265_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 28 (Flapjack.CrepExp.var 29)

def crepBody265_28 : CrepProg (BitVec 64) :=
.seq crepBody265_27 crepBody265_1

def crepBody265_29 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 28, Flapjack.CrepExp.const 1#64]) crepBody265_28

def crepBody265_30 : CrepProg (BitVec 64) :=
.seq crepBody265_26 crepBody265_29

def crepBody265_31 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 28) (Flapjack.CrepExp.var 13)) crepBody265_30

def crepBody265_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 29) (Flapjack.CrepExp.var 30)

def crepBody265_33 : CrepProg (BitVec 64) :=
.seq crepBody265_32 crepBody265_1

def crepBody265_34 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.var 27) crepBody265_33

def crepBody265_35 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 0#64]) crepBody265_34

def crepBody265_36 : CrepProg (BitVec 64) :=
.seq crepBody265_31 crepBody265_35

def crepBody265_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([29], none)) "mpt_fail" [Flapjack.CrepExp.const 22#64]

def crepBody265_38 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody265_37

def crepBody265_39 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 32#64) (Flapjack.CrepExp.var 17)) crepBody265_38 crepBody265_1

def crepBody265_40 : CrepProg (BitVec 64) :=
.seq crepBody265_36 crepBody265_39

def crepBody265_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([29], none)) "memzero"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64],
    Flapjack.CrepExp.const 32#64]

def crepBody265_42 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody265_41

def crepBody265_43 : CrepProg (BitVec 64) :=
.seq crepBody265_40 crepBody265_42

def crepBody265_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 28 (Flapjack.CrepExp.const 0#64)

def crepBody265_45 : CrepProg (BitVec 64) :=
.seq crepBody265_44 crepBody265_1

def crepBody265_46 : CrepProg (BitVec 64) :=
.seq crepBody265_43 crepBody265_45

def crepBody265_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 31) (Flapjack.CrepExp.var 32)

def crepBody265_48 : CrepProg (BitVec 64) :=
.seq crepBody265_47 crepBody265_1

def crepBody265_49 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.load (Flapjack.CrepExp.var 30),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 28]))
      (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 29, Flapjack.CrepExp.const 7#64],
          Flapjack.CrepExp.const 8#64])]) crepBody265_48

def crepBody265_50 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.var 30) crepBody265_49

def crepBody265_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 28 (Flapjack.CrepExp.var 31)

def crepBody265_52 : CrepProg (BitVec 64) :=
.seq crepBody265_51 crepBody265_1

def crepBody265_53 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 28, Flapjack.CrepExp.const 1#64]) crepBody265_52

def crepBody265_54 : CrepProg (BitVec 64) :=
.seq crepBody265_50 crepBody265_53

def crepBody265_55 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 29) (Flapjack.CrepExp.const 3#64),
        Flapjack.CrepExp.const 8#64]]) crepBody265_54

def crepBody265_56 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.var 28]) crepBody265_55

def crepBody265_57 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 28) (Flapjack.CrepExp.var 17)) crepBody265_56

def crepBody265_58 : CrepProg (BitVec 64) :=
.seq crepBody265_46 crepBody265_57

def crepBody265_59 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 128#64])) crepBody265_33

def crepBody265_60 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 40#64]) crepBody265_59

def crepBody265_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([29], none)) "mpt_fail" [Flapjack.CrepExp.const 23#64]

def crepBody265_62 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody265_61

def crepBody265_63 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.const 32#64)) crepBody265_62 crepBody265_1

def crepBody265_64 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.var 20) crepBody265_33

def crepBody265_65 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 40#64]) crepBody265_64

def crepBody265_66 : CrepProg (BitVec 64) :=
.seq crepBody265_63 crepBody265_65

def crepBody265_67 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.const 0#64)) crepBody265_60 crepBody265_66

def crepBody265_68 : CrepProg (BitVec 64) :=
.seq crepBody265_58 crepBody265_67

def crepBody265_69 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 136#64])) crepBody265_33

def crepBody265_70 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 48#64]) crepBody265_69

def crepBody265_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([29], none)) "mpt_fail" [Flapjack.CrepExp.const 24#64]

def crepBody265_72 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody265_71

def crepBody265_73 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 25) (Flapjack.CrepExp.const 32#64)) crepBody265_72 crepBody265_1

def crepBody265_74 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.var 24) crepBody265_33

def crepBody265_75 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 48#64]) crepBody265_74

def crepBody265_76 : CrepProg (BitVec 64) :=
.seq crepBody265_73 crepBody265_75

def crepBody265_77 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 25) (Flapjack.CrepExp.const 0#64)) crepBody265_70 crepBody265_76

def crepBody265_78 : CrepProg (BitVec 64) :=
.seq crepBody265_68 crepBody265_77

def crepBody265_79 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody265_80 : CrepProg (BitVec 64) :=
.seq crepBody265_78 crepBody265_79

def crepBody265_81 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody265_80

def crepBody265_82 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody265_81

def crepBody265_83 : CrepProg (BitVec 64) :=
.seq crepBody265_23 crepBody265_82

def crepBody265_84 : CrepProg (BitVec 64) :=
.seq crepBody265_16 crepBody265_83

def crepBody265_85 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody265_84

def crepBody265_86 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody265_85

def crepBody265_87 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody265_86

def crepBody265_88 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody265_87

def crepBody265_89 : CrepProg (BitVec 64) :=
.seq crepBody265_15 crepBody265_88

def crepBody265_90 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody265_89

def crepBody265_91 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody265_90

def crepBody265_92 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody265_91

def crepBody265_93 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody265_92

def crepBody265_94 : CrepProg (BitVec 64) :=
.seq crepBody265_14 crepBody265_93

def crepBody265_95 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody265_94

def crepBody265_96 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody265_95

def crepBody265_97 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody265_96

def crepBody265_98 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody265_97

def crepBody265_99 : CrepProg (BitVec 64) :=
.seq crepBody265_13 crepBody265_98

def crepBody265_100 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody265_99

def crepBody265_101 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody265_100

def crepBody265_102 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody265_101

def crepBody265_103 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody265_102

def crepBody265_104 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 8) crepBody265_103

def crepBody265_105 : CrepProg (BitVec 64) :=
.seq crepBody265_12 crepBody265_104

def crepBody265_106 : CrepProg (BitVec 64) :=
.seq crepBody265_9 crepBody265_105

def crepBody265_107 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody265_106

def crepBody265_108 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody265_107

def crepBody265_109 : CrepProg (BitVec 64) :=
.seq crepBody265_8 crepBody265_108

def crepBody265_110 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody265_109

def crepBody265_111 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody265_110

def crepBody265_112 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody265_111

def crepBody265_113 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody265_112

def crepBody265_114 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody265_113

def data265 : CrepProg (BitVec 64) := crepBody265_114
def output265 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 102#8, 114#8,
    111#8, 109#8, 95#8, 108#8, 101#8, 97#8, 102#8], [0, 1, 2], crepProgToHOL data265)
end InitECandidate.Proofs.FrontendStages.Crep
