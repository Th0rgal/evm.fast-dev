import InitECandidate.Proofs.FrontendStages.Crep.Translate769
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody785_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody785_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "encode_header" [Flapjack.CrepExp.var 0]

def crepBody785_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody785_3 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody785_2

def crepBody785_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11
  (Flapjack.CrepExp.loadByte
    (Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 6,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 16#64]])))

def crepBody785_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody785_6 : CrepProg (BitVec 64) :=
.seq crepBody785_4 crepBody785_5

def crepBody785_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody785_6 crepBody785_5

def crepBody785_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "rlp_bytes_encoded_len" [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 10]

def crepBody785_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 192#64)])) crepBody785_8 crepBody785_5

def crepBody785_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 13)

def crepBody785_11 : CrepProg (BitVec 64) :=
.seq crepBody785_10 crepBody785_5

def crepBody785_12 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 12]) crepBody785_11

def crepBody785_13 : CrepProg (BitVec 64) :=
.seq crepBody785_9 crepBody785_12

def crepBody785_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 13)

def crepBody785_15 : CrepProg (BitVec 64) :=
.seq crepBody785_14 crepBody785_5

def crepBody785_16 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 1#64]) crepBody785_15

def crepBody785_17 : CrepProg (BitVec 64) :=
.seq crepBody785_13 crepBody785_16

def crepBody785_18 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 10) crepBody785_17

def crepBody785_19 : CrepProg (BitVec 64) :=
.seq crepBody785_7 crepBody785_18

def crepBody785_20 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody785_19

def crepBody785_21 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 6,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 16#64],
      Flapjack.CrepExp.const 8#64])) crepBody785_20

def crepBody785_22 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 7)) crepBody785_21

def crepBody785_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 8]

def crepBody785_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 11)

def crepBody785_25 : CrepProg (BitVec 64) :=
.seq crepBody785_24 crepBody785_5

def crepBody785_26 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 8]) crepBody785_25

def crepBody785_27 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody785_25

def crepBody785_28 : CrepProg (BitVec 64) :=
.seq crepBody785_26 crepBody785_27

def crepBody785_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.const 0#64)

def crepBody785_30 : CrepProg (BitVec 64) :=
.seq crepBody785_29 crepBody785_5

def crepBody785_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "withdrawal_rlp_len"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64]),
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 44#64]]]

def crepBody785_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.var 14)

def crepBody785_33 : CrepProg (BitVec 64) :=
.seq crepBody785_32 crepBody785_5

def crepBody785_34 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]) crepBody785_33

def crepBody785_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 14)

def crepBody785_36 : CrepProg (BitVec 64) :=
.seq crepBody785_35 crepBody785_5

def crepBody785_37 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 1#64]) crepBody785_36

def crepBody785_38 : CrepProg (BitVec 64) :=
.seq crepBody785_34 crepBody785_37

def crepBody785_39 : CrepProg (BitVec 64) :=
.seq crepBody785_31 crepBody785_38

def crepBody785_40 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody785_39

def crepBody785_41 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 11)) crepBody785_40

def crepBody785_42 : CrepProg (BitVec 64) :=
.seq crepBody785_30 crepBody785_41

def crepBody785_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 12]

def crepBody785_44 : CrepProg (BitVec 64) :=
.seq crepBody785_42 crepBody785_43

def crepBody785_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 13)

def crepBody785_46 : CrepProg (BitVec 64) :=
.seq crepBody785_45 crepBody785_5

def crepBody785_47 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 12]) crepBody785_46

def crepBody785_48 : CrepProg (BitVec 64) :=
.seq crepBody785_44 crepBody785_47

def crepBody785_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 5]

def crepBody785_50 : CrepProg (BitVec 64) :=
.seq crepBody785_48 crepBody785_49

def crepBody785_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 10]]

def crepBody785_52 : CrepProg (BitVec 64) :=
.seq crepBody785_50 crepBody785_51

def crepBody785_53 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody785_52

def crepBody785_54 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64])) crepBody785_53

def crepBody785_55 : CrepProg (BitVec 64) :=
.seq crepBody785_28 crepBody785_54

def crepBody785_56 : CrepProg (BitVec 64) :=
.seq crepBody785_23 crepBody785_55

def crepBody785_57 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody785_56

def crepBody785_58 : CrepProg (BitVec 64) :=
.seq crepBody785_22 crepBody785_57

def crepBody785_59 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody785_58

def crepBody785_60 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody785_59

def crepBody785_61 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64])) crepBody785_60

def crepBody785_62 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])) crepBody785_61

def crepBody785_63 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 4) crepBody785_62

def crepBody785_64 : CrepProg (BitVec 64) :=
.seq crepBody785_3 crepBody785_63

def crepBody785_65 : CrepProg (BitVec 64) :=
.seq crepBody785_1 crepBody785_64

def crepBody785_66 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody785_65

def crepBody785_67 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody785_66

def crepBody785_68 : CrepProg (BitVec 64) :=
.seq crepBody785_0 crepBody785_67

def crepBody785_69 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody785_68

def data785 : CrepProg (BitVec 64) := crepBody785_69
def output785 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 111#8, 99#8, 107#8, 95#8, 114#8, 108#8, 112#8, 95#8, 108#8, 101#8, 110#8, 103#8, 116#8, 104#8], [0, 1], crepProgToHOL data785)
end InitECandidate.Proofs.FrontendStages.Crep
