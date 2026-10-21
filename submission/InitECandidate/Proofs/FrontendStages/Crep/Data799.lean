import InitECandidate.Proofs.FrontendStages.Crep.Translate783
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody799_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 8#64]

def crepBody799_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "memeq"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 0#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 512#64]),
    Flapjack.CrepExp.const 20#64]

def crepBody799_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "memeq"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 520#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody799_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 2#64],
        Flapjack.CrepExp.const 1024#64]]

def crepBody799_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "memcpy"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody799_5 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody799_4

def crepBody799_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 15)

def crepBody799_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody799_8 : CrepProg (BitVec 64) :=
.seq crepBody799_6 crepBody799_7

def crepBody799_9 : CrepProg (BitVec 64) :=
.seq crepBody799_5 crepBody799_8

def crepBody799_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 16)

def crepBody799_11 : CrepProg (BitVec 64) :=
.seq crepBody799_10 crepBody799_7

def crepBody799_12 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 2#64],
    Flapjack.CrepExp.const 1024#64]) crepBody799_11

def crepBody799_13 : CrepProg (BitVec 64) :=
.seq crepBody799_9 crepBody799_12

def crepBody799_14 : CrepProg (BitVec 64) :=
.seq crepBody799_3 crepBody799_13

def crepBody799_15 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody799_14

def crepBody799_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 6)
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 192#64])) crepBody799_15 crepBody799_7

def crepBody799_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "extract_deposit_data"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]]

def crepBody799_18 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody799_17

def crepBody799_19 : CrepProg (BitVec 64) :=
.seq crepBody799_16 crepBody799_18

def crepBody799_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 15)

def crepBody799_21 : CrepProg (BitVec 64) :=
.seq crepBody799_20 crepBody799_7

def crepBody799_22 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 192#64]) crepBody799_21

def crepBody799_23 : CrepProg (BitVec 64) :=
.seq crepBody799_19 crepBody799_22

def crepBody799_24 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 0#64)) crepBody799_23 crepBody799_7

def crepBody799_25 : CrepProg (BitVec 64) :=
.seq crepBody799_2 crepBody799_24

def crepBody799_26 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody799_25

def crepBody799_27 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 16#64]))) crepBody799_26 crepBody799_7

def crepBody799_28 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 0#64)) crepBody799_27 crepBody799_7

def crepBody799_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 14)

def crepBody799_30 : CrepProg (BitVec 64) :=
.seq crepBody799_29 crepBody799_7

def crepBody799_31 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 1#64]) crepBody799_30

def crepBody799_32 : CrepProg (BitVec 64) :=
.seq crepBody799_28 crepBody799_31

def crepBody799_33 : CrepProg (BitVec 64) :=
.seq crepBody799_1 crepBody799_32

def crepBody799_34 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody799_33

def crepBody799_35 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 10,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 8#64]])) crepBody799_34

def crepBody799_36 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 9)) crepBody799_35

def crepBody799_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 12)

def crepBody799_38 : CrepProg (BitVec 64) :=
.seq crepBody799_37 crepBody799_7

def crepBody799_39 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64]) crepBody799_38

def crepBody799_40 : CrepProg (BitVec 64) :=
.seq crepBody799_36 crepBody799_39

def crepBody799_41 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody799_40

def crepBody799_42 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 0#64])) crepBody799_41

def crepBody799_43 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64])) crepBody799_42

def crepBody799_44 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 3,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]])) crepBody799_43

def crepBody799_45 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 2)) crepBody799_44

def crepBody799_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "requests_append"
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody799_47 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody799_46

def crepBody799_48 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 5)) crepBody799_47 crepBody799_7

def crepBody799_49 : CrepProg (BitVec 64) :=
.seq crepBody799_45 crepBody799_48

def crepBody799_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "process_checked_system_transaction"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 480#64])]

def crepBody799_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "requests_append"
  [Flapjack.CrepExp.const 1#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 40#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 48#64])]

def crepBody799_52 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody799_51

def crepBody799_53 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 48#64]))) crepBody799_52 crepBody799_7

def crepBody799_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "process_checked_system_transaction"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 488#64])]

def crepBody799_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "requests_append"
  [Flapjack.CrepExp.const 2#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 40#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 48#64])]

def crepBody799_56 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody799_55

def crepBody799_57 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 48#64]))) crepBody799_56 crepBody799_7

def crepBody799_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "process_checked_system_transaction"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 496#64])]

def crepBody799_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "requests_append"
  [Flapjack.CrepExp.const 3#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 40#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 48#64])]

def crepBody799_60 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody799_59

def crepBody799_61 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 48#64]))) crepBody799_60 crepBody799_7

def crepBody799_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "process_checked_system_transaction"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 504#64])]

def crepBody799_63 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "requests_append"
  [Flapjack.CrepExp.const 4#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 40#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 48#64])]

def crepBody799_64 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody799_63

def crepBody799_65 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 48#64]))) crepBody799_64 crepBody799_7

def crepBody799_66 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody799_67 : CrepProg (BitVec 64) :=
.seq crepBody799_65 crepBody799_66

def crepBody799_68 : CrepProg (BitVec 64) :=
.seq crepBody799_62 crepBody799_67

def crepBody799_69 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody799_68

def crepBody799_70 : CrepProg (BitVec 64) :=
.seq crepBody799_61 crepBody799_69

def crepBody799_71 : CrepProg (BitVec 64) :=
.seq crepBody799_58 crepBody799_70

def crepBody799_72 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody799_71

def crepBody799_73 : CrepProg (BitVec 64) :=
.seq crepBody799_57 crepBody799_72

def crepBody799_74 : CrepProg (BitVec 64) :=
.seq crepBody799_54 crepBody799_73

def crepBody799_75 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody799_74

def crepBody799_76 : CrepProg (BitVec 64) :=
.seq crepBody799_53 crepBody799_75

def crepBody799_77 : CrepProg (BitVec 64) :=
.seq crepBody799_50 crepBody799_76

def crepBody799_78 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody799_77

def crepBody799_79 : CrepProg (BitVec 64) :=
.seq crepBody799_49 crepBody799_78

def crepBody799_80 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody799_79

def crepBody799_81 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody799_80

def crepBody799_82 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody799_81

def crepBody799_83 : CrepProg (BitVec 64) :=
.seq crepBody799_0 crepBody799_82

def crepBody799_84 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody799_83

def crepBody799_85 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64])) crepBody799_84

def crepBody799_86 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody799_85

def crepBody799_87 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 416#64]),
      Flapjack.CrepExp.const 72#64])) crepBody799_86

def data799 : CrepProg (BitVec 64) := crepBody799_87
def output799 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 103#8, 101#8, 110#8, 101#8, 114#8, 97#8, 108#8, 95#8, 112#8,
    117#8, 114#8, 112#8, 111#8, 115#8, 101#8, 95#8, 114#8, 101#8, 113#8, 117#8, 101#8, 115#8, 116#8, 115#8], [], crepProgToHOL data799)
end InitECandidate.Proofs.FrontendStages.Crep
