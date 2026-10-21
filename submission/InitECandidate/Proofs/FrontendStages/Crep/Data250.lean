import InitECandidate.Proofs.FrontendStages.Crep.Translate234
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody250_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.const 0#64)

def crepBody250_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody250_2 : CrepProg (BitVec 64) :=
.seq crepBody250_0 crepBody250_1

def crepBody250_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.const 0#64)

def crepBody250_4 : CrepProg (BitVec 64) :=
.seq crepBody250_3 crepBody250_1

def crepBody250_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "mpt_fail" [Flapjack.CrepExp.const 2#64]

def crepBody250_6 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody250_5

def crepBody250_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody250_6 crepBody250_1

def crepBody250_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "node_invalidate" [Flapjack.CrepExp.var 0]

def crepBody250_9 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody250_8

def crepBody250_10 : CrepProg (BitVec 64) :=
.seq crepBody250_7 crepBody250_9

def crepBody250_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 0)

def crepBody250_12 : CrepProg (BitVec 64) :=
.seq crepBody250_11 crepBody250_1

def crepBody250_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "memeq"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]]

def crepBody250_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody250_4 crepBody250_1

def crepBody250_15 : CrepProg (BitVec 64) :=
.seq crepBody250_13 crepBody250_14

def crepBody250_16 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody250_15

def crepBody250_17 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64]))
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3])) crepBody250_16 crepBody250_1

def crepBody250_18 : CrepProg (BitVec 64) :=
.seq crepBody250_12 crepBody250_17

def crepBody250_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "common_prefix_length"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]]

def crepBody250_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "scratch_alloc" [Flapjack.CrepExp.const 40#64]

def crepBody250_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 13)

def crepBody250_22 : CrepProg (BitVec 64) :=
.seq crepBody250_21 crepBody250_1

def crepBody250_23 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 4) crepBody250_22

def crepBody250_24 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 0#64]) crepBody250_23

def crepBody250_25 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 0) crepBody250_22

def crepBody250_26 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 8#64]) crepBody250_25

def crepBody250_27 : CrepProg (BitVec 64) :=
.seq crepBody250_24 crepBody250_26

def crepBody250_28 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 2#64) crepBody250_22

def crepBody250_29 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 16#64]) crepBody250_28

def crepBody250_30 : CrepProg (BitVec 64) :=
.seq crepBody250_27 crepBody250_29

def crepBody250_31 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 8) crepBody250_22

def crepBody250_32 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 24#64]) crepBody250_31

def crepBody250_33 : CrepProg (BitVec 64) :=
.seq crepBody250_30 crepBody250_32

def crepBody250_34 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 9) crepBody250_22

def crepBody250_35 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 32#64]) crepBody250_34

def crepBody250_36 : CrepProg (BitVec 64) :=
.seq crepBody250_33 crepBody250_35

def crepBody250_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 11)

def crepBody250_38 : CrepProg (BitVec 64) :=
.seq crepBody250_37 crepBody250_1

def crepBody250_39 : CrepProg (BitVec 64) :=
.seq crepBody250_36 crepBody250_38

def crepBody250_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 0 (Flapjack.CrepExp.var 12)

def crepBody250_41 : CrepProg (BitVec 64) :=
.seq crepBody250_40 crepBody250_1

def crepBody250_42 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64])) crepBody250_41

def crepBody250_43 : CrepProg (BitVec 64) :=
.seq crepBody250_39 crepBody250_42

def crepBody250_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 12)

def crepBody250_45 : CrepProg (BitVec 64) :=
.seq crepBody250_44 crepBody250_1

def crepBody250_46 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 9]) crepBody250_45

def crepBody250_47 : CrepProg (BitVec 64) :=
.seq crepBody250_43 crepBody250_46

def crepBody250_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.const 1#64)

def crepBody250_49 : CrepProg (BitVec 64) :=
.seq crepBody250_48 crepBody250_1

def crepBody250_50 : CrepProg (BitVec 64) :=
.seq crepBody250_47 crepBody250_49

def crepBody250_51 : CrepProg (BitVec 64) :=
.seq crepBody250_20 crepBody250_50

def crepBody250_52 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody250_51

def crepBody250_53 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 9)) crepBody250_12 crepBody250_52

def crepBody250_54 : CrepProg (BitVec 64) :=
.seq crepBody250_19 crepBody250_53

def crepBody250_55 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody250_54

def crepBody250_56 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64])) crepBody250_55

def crepBody250_57 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64])) crepBody250_56

def crepBody250_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody250_59 : CrepProg (BitVec 64) :=
.seq crepBody250_58 crepBody250_1

def crepBody250_60 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody250_59

def crepBody250_61 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64]) crepBody250_60

def crepBody250_62 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 168#64]) crepBody250_60

def crepBody250_63 : CrepProg (BitVec 64) :=
.seq crepBody250_61 crepBody250_62

def crepBody250_64 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "_collapse_branch" [Flapjack.CrepExp.var 0]

def crepBody250_65 : CrepProg (BitVec 64) :=
.seq crepBody250_63 crepBody250_64

def crepBody250_66 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 168#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody250_12 crepBody250_65

def crepBody250_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "scratch_alloc" [Flapjack.CrepExp.const 40#64]

def crepBody250_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody250_69 : CrepProg (BitVec 64) :=
.seq crepBody250_68 crepBody250_1

def crepBody250_70 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 4) crepBody250_69

def crepBody250_71 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 0#64]) crepBody250_70

def crepBody250_72 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 0) crepBody250_69

def crepBody250_73 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]) crepBody250_72

def crepBody250_74 : CrepProg (BitVec 64) :=
.seq crepBody250_71 crepBody250_73

def crepBody250_75 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 3#64) crepBody250_69

def crepBody250_76 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 16#64]) crepBody250_75

def crepBody250_77 : CrepProg (BitVec 64) :=
.seq crepBody250_74 crepBody250_76

def crepBody250_78 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 8) crepBody250_69

def crepBody250_79 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 32#64]) crepBody250_78

def crepBody250_80 : CrepProg (BitVec 64) :=
.seq crepBody250_77 crepBody250_79

def crepBody250_81 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 9)

def crepBody250_82 : CrepProg (BitVec 64) :=
.seq crepBody250_81 crepBody250_1

def crepBody250_83 : CrepProg (BitVec 64) :=
.seq crepBody250_80 crepBody250_82

def crepBody250_84 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 0 (Flapjack.CrepExp.var 10)

def crepBody250_85 : CrepProg (BitVec 64) :=
.seq crepBody250_84 crepBody250_1

def crepBody250_86 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]])) crepBody250_85

def crepBody250_87 : CrepProg (BitVec 64) :=
.seq crepBody250_83 crepBody250_86

def crepBody250_88 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 10)

def crepBody250_89 : CrepProg (BitVec 64) :=
.seq crepBody250_88 crepBody250_1

def crepBody250_90 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody250_89

def crepBody250_91 : CrepProg (BitVec 64) :=
.seq crepBody250_87 crepBody250_90

def crepBody250_92 : CrepProg (BitVec 64) :=
.seq crepBody250_91 crepBody250_49

def crepBody250_93 : CrepProg (BitVec 64) :=
.seq crepBody250_67 crepBody250_92

def crepBody250_94 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody250_93

def crepBody250_95 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3])) crepBody250_94

def crepBody250_96 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 2)) crepBody250_66 crepBody250_95

def crepBody250_97 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 2#64)) crepBody250_57 crepBody250_96

def crepBody250_98 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 1#64)) crepBody250_18 crepBody250_97

def crepBody250_99 : CrepProg (BitVec 64) :=
.seq crepBody250_10 crepBody250_98

def crepBody250_100 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody250_99

def crepBody250_101 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 0#64)) crepBody250_4 crepBody250_100

def crepBody250_102 : CrepProg (BitVec 64) :=
.seq crepBody250_2 crepBody250_101

def crepBody250_103 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody250_102

def crepBody250_104 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "_delete_ext_finish"
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 5]

def crepBody250_105 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 5) crepBody250_59

def crepBody250_106 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 32#64,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64]),
        Flapjack.CrepExp.const 8#64]]) crepBody250_105

def crepBody250_107 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "_collapse_branch" [Flapjack.CrepExp.var 7]

def crepBody250_108 : CrepProg (BitVec 64) :=
.seq crepBody250_106 crepBody250_107

def crepBody250_109 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]))
  (Flapjack.CrepExp.const 2#64)) crepBody250_104 crepBody250_108

def crepBody250_110 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 8)

def crepBody250_111 : CrepProg (BitVec 64) :=
.seq crepBody250_110 crepBody250_1

def crepBody250_112 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 0#64])) crepBody250_111

def crepBody250_113 : CrepProg (BitVec 64) :=
.seq crepBody250_109 crepBody250_112

def crepBody250_114 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64])) crepBody250_113

def crepBody250_115 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody250_114

def crepBody250_116 : CrepProg (BitVec 64) :=
.seq crepBody250_103 crepBody250_115

def crepBody250_117 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 5]

def crepBody250_118 : CrepProg (BitVec 64) :=
.seq crepBody250_116 crepBody250_117

def crepBody250_119 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 1#64) crepBody250_118

def crepBody250_120 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody250_119

def crepBody250_121 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody250_120

def data250 : CrepProg (BitVec 64) := crepBody250_121
def output250 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 109#8, 112#8, 116#8, 95#8, 100#8, 101#8, 108#8, 101#8, 116#8, 101#8, 95#8, 110#8, 111#8, 100#8, 101#8, 95#8,
    98#8, 111#8, 100#8, 121#8], [0, 1, 2, 3], crepProgToHOL data250)
end InitECandidate.Proofs.FrontendStages.Crep
