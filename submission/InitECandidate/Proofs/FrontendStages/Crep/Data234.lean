import InitECandidate.Proofs.FrontendStages.Crep.Translate218
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody234_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11], none)) "_decode_step"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody234_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 11)

def crepBody234_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody234_3 : CrepProg (BitVec 64) :=
.seq crepBody234_1 crepBody234_2

def crepBody234_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.const 0#64)

def crepBody234_5 : CrepProg (BitVec 64) :=
.seq crepBody234_4 crepBody234_2

def crepBody234_6 : CrepProg (BitVec 64) :=
.seq crepBody234_3 crepBody234_5

def crepBody234_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 13)

def crepBody234_8 : CrepProg (BitVec 64) :=
.seq crepBody234_7 crepBody234_2

def crepBody234_9 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 3) crepBody234_8

def crepBody234_10 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 0#64]) crepBody234_9

def crepBody234_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 11)

def crepBody234_12 : CrepProg (BitVec 64) :=
.seq crepBody234_11 crepBody234_2

def crepBody234_13 : CrepProg (BitVec 64) :=
.seq crepBody234_10 crepBody234_12

def crepBody234_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.const 1#64)

def crepBody234_15 : CrepProg (BitVec 64) :=
.seq crepBody234_14 crepBody234_2

def crepBody234_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.const 0#64)

def crepBody234_17 : CrepProg (BitVec 64) :=
.seq crepBody234_16 crepBody234_2

def crepBody234_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]))
  (Flapjack.CrepExp.const 1#64)) crepBody234_15 crepBody234_17

def crepBody234_19 : CrepProg (BitVec 64) :=
.seq crepBody234_13 crepBody234_18

def crepBody234_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.const 2#64)

def crepBody234_21 : CrepProg (BitVec 64) :=
.seq crepBody234_20 crepBody234_2

def crepBody234_22 : CrepProg (BitVec 64) :=
.seq crepBody234_19 crepBody234_21

def crepBody234_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody234_6 crepBody234_22

def crepBody234_24 : CrepProg (BitVec 64) :=
.seq crepBody234_0 crepBody234_23

def crepBody234_25 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody234_24

def crepBody234_26 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody234_25

def crepBody234_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12, 13, 14], none)) "_resolve_step"
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody234_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.var 16)

def crepBody234_29 : CrepProg (BitVec 64) :=
.seq crepBody234_28 crepBody234_2

def crepBody234_30 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody234_29

def crepBody234_31 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 80#64]) crepBody234_30

def crepBody234_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 12)

def crepBody234_33 : CrepProg (BitVec 64) :=
.seq crepBody234_32 crepBody234_2

def crepBody234_34 : CrepProg (BitVec 64) :=
.seq crepBody234_31 crepBody234_33

def crepBody234_35 : CrepProg (BitVec 64) :=
.seq crepBody234_34 crepBody234_5

def crepBody234_36 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 14) crepBody234_29

def crepBody234_37 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 80#64]) crepBody234_36

def crepBody234_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 12)

def crepBody234_39 : CrepProg (BitVec 64) :=
.seq crepBody234_38 crepBody234_2

def crepBody234_40 : CrepProg (BitVec 64) :=
.seq crepBody234_37 crepBody234_39

def crepBody234_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 13)

def crepBody234_42 : CrepProg (BitVec 64) :=
.seq crepBody234_41 crepBody234_2

def crepBody234_43 : CrepProg (BitVec 64) :=
.seq crepBody234_40 crepBody234_42

def crepBody234_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.const 1#64)

def crepBody234_45 : CrepProg (BitVec 64) :=
.seq crepBody234_44 crepBody234_2

def crepBody234_46 : CrepProg (BitVec 64) :=
.seq crepBody234_43 crepBody234_45

def crepBody234_47 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 0#64)) crepBody234_35 crepBody234_46

def crepBody234_48 : CrepProg (BitVec 64) :=
.seq crepBody234_27 crepBody234_47

def crepBody234_49 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody234_48

def crepBody234_50 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody234_49

def crepBody234_51 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody234_50

def crepBody234_52 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody234_51

def crepBody234_53 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64])) crepBody234_52

def crepBody234_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.const 0#64)

def crepBody234_55 : CrepProg (BitVec 64) :=
.seq crepBody234_54 crepBody234_2

def crepBody234_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 12)

def crepBody234_57 : CrepProg (BitVec 64) :=
.seq crepBody234_56 crepBody234_2

def crepBody234_58 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 10) crepBody234_57

def crepBody234_59 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64]) crepBody234_58

def crepBody234_60 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64))]) crepBody234_59 crepBody234_2

def crepBody234_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "mpt_fail" [Flapjack.CrepExp.const 8#64]

def crepBody234_62 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody234_61

def crepBody234_63 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody234_62 crepBody234_2

def crepBody234_64 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "mpt_fail" [Flapjack.CrepExp.const 8#64]

def crepBody234_65 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody234_64

def crepBody234_66 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 3#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 0#64))]) crepBody234_65 crepBody234_2

def crepBody234_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "node_new_ext"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 72#64]),
    Flapjack.CrepExp.var 4]

def crepBody234_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody234_69 : CrepProg (BitVec 64) :=
.seq crepBody234_68 crepBody234_2

def crepBody234_70 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 48#64])) crepBody234_69

def crepBody234_71 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64]) crepBody234_70

def crepBody234_72 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 56#64])) crepBody234_69

def crepBody234_73 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 16#64]) crepBody234_72

def crepBody234_74 : CrepProg (BitVec 64) :=
.seq crepBody234_71 crepBody234_73

def crepBody234_75 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 13)

def crepBody234_76 : CrepProg (BitVec 64) :=
.seq crepBody234_75 crepBody234_2

def crepBody234_77 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 0#64])) crepBody234_76

def crepBody234_78 : CrepProg (BitVec 64) :=
.seq crepBody234_74 crepBody234_77

def crepBody234_79 : CrepProg (BitVec 64) :=
.seq crepBody234_78 crepBody234_33

def crepBody234_80 : CrepProg (BitVec 64) :=
.seq crepBody234_67 crepBody234_79

def crepBody234_81 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody234_80

def crepBody234_82 : CrepProg (BitVec 64) :=
.seq crepBody234_66 crepBody234_81

def crepBody234_83 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 0#64])) crepBody234_82

def crepBody234_84 : CrepProg (BitVec 64) :=
.seq crepBody234_63 crepBody234_83

def crepBody234_85 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 4) crepBody234_69

def crepBody234_86 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 32#64,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64]]) crepBody234_85

def crepBody234_87 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 40#64]),
    Flapjack.CrepExp.const 1#64]) crepBody234_69

def crepBody234_88 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 40#64]) crepBody234_87

def crepBody234_89 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody234_88 crepBody234_2

def crepBody234_90 : CrepProg (BitVec 64) :=
.seq crepBody234_86 crepBody234_89

def crepBody234_91 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.var 13)

def crepBody234_92 : CrepProg (BitVec 64) :=
.seq crepBody234_91 crepBody234_2

def crepBody234_93 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 1#64]) crepBody234_92

def crepBody234_94 : CrepProg (BitVec 64) :=
.seq crepBody234_90 crepBody234_93

def crepBody234_95 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 12) crepBody234_69

def crepBody234_96 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 32#64]) crepBody234_95

def crepBody234_97 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 12)

def crepBody234_98 : CrepProg (BitVec 64) :=
.seq crepBody234_97 crepBody234_2

def crepBody234_99 : CrepProg (BitVec 64) :=
.seq crepBody234_96 crepBody234_98

def crepBody234_100 : CrepProg (BitVec 64) :=
.seq crepBody234_99 crepBody234_21

def crepBody234_101 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15, 16, 17], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 13,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 16#64, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 13,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 16#64, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody234_102 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.var 20)

def crepBody234_103 : CrepProg (BitVec 64) :=
.seq crepBody234_102 crepBody234_2

def crepBody234_104 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 15) crepBody234_103

def crepBody234_105 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 160#64]) crepBody234_104

def crepBody234_106 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 16) crepBody234_103

def crepBody234_107 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 168#64]) crepBody234_106

def crepBody234_108 : CrepProg (BitVec 64) :=
.seq crepBody234_105 crepBody234_107

def crepBody234_109 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18 (Flapjack.CrepExp.var 19)

def crepBody234_110 : CrepProg (BitVec 64) :=
.seq crepBody234_109 crepBody234_2

def crepBody234_111 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 1#64]) crepBody234_110

def crepBody234_112 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.const 0#64)) crepBody234_111 crepBody234_2

def crepBody234_113 : CrepProg (BitVec 64) :=
.seq crepBody234_108 crepBody234_112

def crepBody234_114 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 0#64)) crepBody234_113 crepBody234_2

def crepBody234_115 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "mpt_fail" [Flapjack.CrepExp.const 9#64]

def crepBody234_116 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody234_115

def crepBody234_117 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.const 2#64)) crepBody234_116 crepBody234_2

def crepBody234_118 : CrepProg (BitVec 64) :=
.seq crepBody234_114 crepBody234_117

def crepBody234_119 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 48#64])) crepBody234_103

def crepBody234_120 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 8#64]) crepBody234_119

def crepBody234_121 : CrepProg (BitVec 64) :=
.seq crepBody234_118 crepBody234_120

def crepBody234_122 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 56#64])) crepBody234_103

def crepBody234_123 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 16#64]) crepBody234_122

def crepBody234_124 : CrepProg (BitVec 64) :=
.seq crepBody234_121 crepBody234_123

def crepBody234_125 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 19)

def crepBody234_126 : CrepProg (BitVec 64) :=
.seq crepBody234_125 crepBody234_2

def crepBody234_127 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 0#64])) crepBody234_126

def crepBody234_128 : CrepProg (BitVec 64) :=
.seq crepBody234_124 crepBody234_127

def crepBody234_129 : CrepProg (BitVec 64) :=
.seq crepBody234_128 crepBody234_3

def crepBody234_130 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 40#64])) crepBody234_129

def crepBody234_131 : CrepProg (BitVec 64) :=
.seq crepBody234_101 crepBody234_130

def crepBody234_132 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody234_131

def crepBody234_133 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody234_132

def crepBody234_134 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody234_133

def crepBody234_135 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody234_134

def crepBody234_136 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64])) crepBody234_135

def crepBody234_137 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.const 16#64)) crepBody234_100 crepBody234_136

def crepBody234_138 : CrepProg (BitVec 64) :=
.seq crepBody234_94 crepBody234_137

def crepBody234_139 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 32#64])) crepBody234_138

def crepBody234_140 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64])) crepBody234_139

def crepBody234_141 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]))
  (Flapjack.CrepExp.const 1#64)) crepBody234_84 crepBody234_140

def crepBody234_142 : CrepProg (BitVec 64) :=
.seq crepBody234_60 crepBody234_141

def crepBody234_143 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 80#64])) crepBody234_142

def crepBody234_144 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody234_55 crepBody234_143

def crepBody234_145 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 2#64)) crepBody234_53 crepBody234_144

def crepBody234_146 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 1#64)) crepBody234_26 crepBody234_145

def crepBody234_147 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 0#64)) crepBody234_146

def crepBody234_148 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody234_149 : CrepProg (BitVec 64) :=
.seq crepBody234_147 crepBody234_148

def crepBody234_150 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 1#64) crepBody234_149

def crepBody234_151 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody234_150

def crepBody234_152 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 1#64) crepBody234_151

def crepBody234_153 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 2) crepBody234_152

def crepBody234_154 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 1) crepBody234_153

def crepBody234_155 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody234_154

def crepBody234_156 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody234_155

def data234 : CrepProg (BitVec 64) := crepBody234_156
def output234 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 119#8, 105#8, 116#8, 110#8, 101#8, 115#8, 115#8, 95#8, 110#8,
    111#8, 100#8, 101#8, 95#8, 98#8, 111#8, 100#8, 121#8], [0, 1, 2], crepProgToHOL data234)
end InitECandidate.Proofs.FrontendStages.Crep
