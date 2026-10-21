import InitECandidate.Proofs.FrontendStages.Crep.Translate238
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody254_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "node_ref_len"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64])]

def crepBody254_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 7)

def crepBody254_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody254_3 : CrepProg (BitVec 64) :=
.seq crepBody254_1 crepBody254_2

def crepBody254_4 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 6]) crepBody254_3

def crepBody254_5 : CrepProg (BitVec 64) :=
.seq crepBody254_0 crepBody254_4

def crepBody254_6 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody254_5

def crepBody254_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 2#64)) crepBody254_6 crepBody254_2

def crepBody254_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "node_ref_len"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64]])]

def crepBody254_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 8)

def crepBody254_10 : CrepProg (BitVec 64) :=
.seq crepBody254_9 crepBody254_2

def crepBody254_11 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 7]) crepBody254_10

def crepBody254_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 8)

def crepBody254_13 : CrepProg (BitVec 64) :=
.seq crepBody254_12 crepBody254_2

def crepBody254_14 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64]) crepBody254_13

def crepBody254_15 : CrepProg (BitVec 64) :=
.seq crepBody254_11 crepBody254_14

def crepBody254_16 : CrepProg (BitVec 64) :=
.seq crepBody254_8 crepBody254_15

def crepBody254_17 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody254_16

def crepBody254_18 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 16#64)) crepBody254_17

def crepBody254_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "rlp_value_encoded_len"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 160#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 168#64])]

def crepBody254_20 : CrepProg (BitVec 64) :=
.seq crepBody254_19 crepBody254_11

def crepBody254_21 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody254_20

def crepBody254_22 : CrepProg (BitVec 64) :=
.seq crepBody254_18 crepBody254_21

def crepBody254_23 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody254_22

def crepBody254_24 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 3#64)) crepBody254_23 crepBody254_2

def crepBody254_25 : CrepProg (BitVec 64) :=
.seq crepBody254_7 crepBody254_24

def crepBody254_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 3]

def crepBody254_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 3]]

def crepBody254_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_encode_list_header" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 3]

def crepBody254_29 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody254_28

def crepBody254_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8], Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5]

def crepBody254_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 10)

def crepBody254_32 : CrepProg (BitVec 64) :=
.seq crepBody254_31 crepBody254_2

def crepBody254_33 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]) crepBody254_32

def crepBody254_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64])]

def crepBody254_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 11)

def crepBody254_36 : CrepProg (BitVec 64) :=
.seq crepBody254_35 crepBody254_2

def crepBody254_37 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 10]) crepBody254_36

def crepBody254_38 : CrepProg (BitVec 64) :=
.seq crepBody254_34 crepBody254_37

def crepBody254_39 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody254_38

def crepBody254_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "node_write_ref"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]]

def crepBody254_41 : CrepProg (BitVec 64) :=
.seq crepBody254_40 crepBody254_37

def crepBody254_42 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody254_41

def crepBody254_43 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 1#64)) crepBody254_39 crepBody254_42

def crepBody254_44 : CrepProg (BitVec 64) :=
.seq crepBody254_33 crepBody254_43

def crepBody254_45 : CrepProg (BitVec 64) :=
.seq crepBody254_30 crepBody254_44

def crepBody254_46 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody254_45

def crepBody254_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "node_write_ref"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]]

def crepBody254_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 11)

def crepBody254_49 : CrepProg (BitVec 64) :=
.seq crepBody254_48 crepBody254_2

def crepBody254_50 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 1#64]) crepBody254_49

def crepBody254_51 : CrepProg (BitVec 64) :=
.seq crepBody254_37 crepBody254_50

def crepBody254_52 : CrepProg (BitVec 64) :=
.seq crepBody254_47 crepBody254_51

def crepBody254_53 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody254_52

def crepBody254_54 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 16#64)) crepBody254_53

def crepBody254_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 160#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 168#64])]

def crepBody254_56 : CrepProg (BitVec 64) :=
.seq crepBody254_55 crepBody254_37

def crepBody254_57 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody254_56

def crepBody254_58 : CrepProg (BitVec 64) :=
.seq crepBody254_54 crepBody254_57

def crepBody254_59 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody254_58

def crepBody254_60 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 3#64)) crepBody254_46 crepBody254_59

def crepBody254_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody254_62 : CrepProg (BitVec 64) :=
.seq crepBody254_61 crepBody254_2

def crepBody254_63 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 7) crepBody254_62

def crepBody254_64 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64]) crepBody254_63

def crepBody254_65 : CrepProg (BitVec 64) :=
.seq crepBody254_60 crepBody254_64

def crepBody254_66 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 8) crepBody254_62

def crepBody254_67 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64]) crepBody254_66

def crepBody254_68 : CrepProg (BitVec 64) :=
.seq crepBody254_65 crepBody254_67

def crepBody254_69 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody254_70 : CrepProg (BitVec 64) :=
.seq crepBody254_68 crepBody254_69

def crepBody254_71 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 6) crepBody254_70

def crepBody254_72 : CrepProg (BitVec 64) :=
.seq crepBody254_29 crepBody254_71

def crepBody254_73 : CrepProg (BitVec 64) :=
.seq crepBody254_27 crepBody254_72

def crepBody254_74 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody254_73

def crepBody254_75 : CrepProg (BitVec 64) :=
.seq crepBody254_26 crepBody254_74

def crepBody254_76 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody254_75

def crepBody254_77 : CrepProg (BitVec 64) :=
.seq crepBody254_25 crepBody254_76

def crepBody254_78 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64])) crepBody254_77

def crepBody254_79 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64])) crepBody254_78

def crepBody254_80 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64])) crepBody254_79

def crepBody254_81 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64])) crepBody254_80

def data254 : CrepProg (BitVec 64) := crepBody254_81
def output254 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 110#8, 111#8, 100#8, 101#8, 95#8, 114#8, 108#8, 112#8, 95#8, 102#8, 105#8, 110#8, 105#8, 115#8, 104#8], [0, 1], crepProgToHOL data254)
end InitECandidate.Proofs.FrontendStages.Crep
