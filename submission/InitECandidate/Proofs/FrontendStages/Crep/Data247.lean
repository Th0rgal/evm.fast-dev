import InitECandidate.Proofs.FrontendStages.Crep.Translate231
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody247_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.const 0#64)

def crepBody247_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody247_2 : CrepProg (BitVec 64) :=
.seq crepBody247_0 crepBody247_1

def crepBody247_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "node_new_leaf"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3], Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5]

def crepBody247_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "mpt_fail" [Flapjack.CrepExp.const 2#64]

def crepBody247_5 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody247_4

def crepBody247_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 0#64)) crepBody247_5 crepBody247_1

def crepBody247_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "node_invalidate" [Flapjack.CrepExp.var 0]

def crepBody247_8 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody247_7

def crepBody247_9 : CrepProg (BitVec 64) :=
.seq crepBody247_6 crepBody247_8

def crepBody247_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "_insert_into_leaf"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3], Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5]

def crepBody247_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "common_prefix_length"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]]

def crepBody247_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 0)

def crepBody247_13 : CrepProg (BitVec 64) :=
.seq crepBody247_12 crepBody247_1

def crepBody247_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]))

def crepBody247_15 : CrepProg (BitVec 64) :=
.seq crepBody247_14 crepBody247_1

def crepBody247_16 : CrepProg (BitVec 64) :=
.seq crepBody247_13 crepBody247_15

def crepBody247_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64])

def crepBody247_18 : CrepProg (BitVec 64) :=
.seq crepBody247_17 crepBody247_1

def crepBody247_19 : CrepProg (BitVec 64) :=
.seq crepBody247_16 crepBody247_18

def crepBody247_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 16])

def crepBody247_21 : CrepProg (BitVec 64) :=
.seq crepBody247_20 crepBody247_1

def crepBody247_22 : CrepProg (BitVec 64) :=
.seq crepBody247_19 crepBody247_21

def crepBody247_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.const 1#64)

def crepBody247_24 : CrepProg (BitVec 64) :=
.seq crepBody247_23 crepBody247_1

def crepBody247_25 : CrepProg (BitVec 64) :=
.seq crepBody247_22 crepBody247_24

def crepBody247_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "_split_extension"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3], Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 16]

def crepBody247_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "node_new_ext"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody247_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 17)

def crepBody247_29 : CrepProg (BitVec 64) :=
.seq crepBody247_28 crepBody247_1

def crepBody247_30 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 16)) crepBody247_27 crepBody247_29

def crepBody247_31 : CrepProg (BitVec 64) :=
.seq crepBody247_26 crepBody247_30

def crepBody247_32 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody247_31

def crepBody247_33 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.var 15)) crepBody247_25 crepBody247_32

def crepBody247_34 : CrepProg (BitVec 64) :=
.seq crepBody247_11 crepBody247_33

def crepBody247_35 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody247_34

def crepBody247_36 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64])) crepBody247_35

def crepBody247_37 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64])) crepBody247_36

def crepBody247_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 15)

def crepBody247_39 : CrepProg (BitVec 64) :=
.seq crepBody247_38 crepBody247_1

def crepBody247_40 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 4) crepBody247_39

def crepBody247_41 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64]) crepBody247_40

def crepBody247_42 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 5) crepBody247_39

def crepBody247_43 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 168#64]) crepBody247_42

def crepBody247_44 : CrepProg (BitVec 64) :=
.seq crepBody247_41 crepBody247_43

def crepBody247_45 : CrepProg (BitVec 64) :=
.seq crepBody247_44 crepBody247_13

def crepBody247_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 8#64]]))

def crepBody247_47 : CrepProg (BitVec 64) :=
.seq crepBody247_46 crepBody247_1

def crepBody247_48 : CrepProg (BitVec 64) :=
.seq crepBody247_13 crepBody247_47

def crepBody247_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 8#64]])

def crepBody247_50 : CrepProg (BitVec 64) :=
.seq crepBody247_49 crepBody247_1

def crepBody247_51 : CrepProg (BitVec 64) :=
.seq crepBody247_48 crepBody247_50

def crepBody247_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64])

def crepBody247_53 : CrepProg (BitVec 64) :=
.seq crepBody247_52 crepBody247_1

def crepBody247_54 : CrepProg (BitVec 64) :=
.seq crepBody247_51 crepBody247_53

def crepBody247_55 : CrepProg (BitVec 64) :=
.seq crepBody247_54 crepBody247_24

def crepBody247_56 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3])) crepBody247_55

def crepBody247_57 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 2)) crepBody247_45 crepBody247_56

def crepBody247_58 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 2#64)) crepBody247_37 crepBody247_57

def crepBody247_59 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 1#64)) crepBody247_10 crepBody247_58

def crepBody247_60 : CrepProg (BitVec 64) :=
.seq crepBody247_9 crepBody247_59

def crepBody247_61 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody247_60

def crepBody247_62 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 0#64)) crepBody247_3 crepBody247_61

def crepBody247_63 : CrepProg (BitVec 64) :=
.seq crepBody247_2 crepBody247_62

def crepBody247_64 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 9)

def crepBody247_65 : CrepProg (BitVec 64) :=
.seq crepBody247_64 crepBody247_1

def crepBody247_66 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody247_67 : CrepProg (BitVec 64) :=
.seq crepBody247_66 crepBody247_1

def crepBody247_68 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 9) crepBody247_67

def crepBody247_69 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 7) crepBody247_68

def crepBody247_70 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody247_65 crepBody247_69

def crepBody247_71 : CrepProg (BitVec 64) :=
.seq crepBody247_63 crepBody247_70

def crepBody247_72 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 0 (Flapjack.CrepExp.var 10)

def crepBody247_73 : CrepProg (BitVec 64) :=
.seq crepBody247_72 crepBody247_1

def crepBody247_74 : CrepProg (BitVec 64) :=
.seq crepBody247_71 crepBody247_73

def crepBody247_75 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 11)

def crepBody247_76 : CrepProg (BitVec 64) :=
.seq crepBody247_75 crepBody247_1

def crepBody247_77 : CrepProg (BitVec 64) :=
.seq crepBody247_74 crepBody247_76

def crepBody247_78 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 12)

def crepBody247_79 : CrepProg (BitVec 64) :=
.seq crepBody247_78 crepBody247_1

def crepBody247_80 : CrepProg (BitVec 64) :=
.seq crepBody247_77 crepBody247_79

def crepBody247_81 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody247_80

def crepBody247_82 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody247_81

def crepBody247_83 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody247_82

def crepBody247_84 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody247_83

def crepBody247_85 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody247_84

def crepBody247_86 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 6]

def crepBody247_87 : CrepProg (BitVec 64) :=
.seq crepBody247_85 crepBody247_86

def crepBody247_88 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 1#64) crepBody247_87

def crepBody247_89 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody247_88

def crepBody247_90 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody247_89

def data247 : CrepProg (BitVec 64) := crepBody247_90
def output247 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 109#8, 112#8, 116#8, 95#8, 105#8, 110#8, 115#8, 101#8, 114#8, 116#8, 95#8, 110#8, 111#8, 100#8, 101#8], [0, 1, 2, 3, 4, 5], crepProgToHOL data247)
end InitECandidate.Proofs.FrontendStages.Crep
