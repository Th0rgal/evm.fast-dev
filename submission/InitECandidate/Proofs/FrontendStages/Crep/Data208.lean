import InitECandidate.Proofs.FrontendStages.Crep.Translate192
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody208_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 1024#64]

def crepBody208_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody208_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2 (Flapjack.CrepExp.var 4)

def crepBody208_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody208_4 : CrepProg (BitVec 64) :=
.seq crepBody208_2 crepBody208_3

def crepBody208_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]) crepBody208_4

def crepBody208_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody208_7 : CrepProg (BitVec 64) :=
.seq crepBody208_5 crepBody208_6

def crepBody208_8 : CrepProg (BitVec 64) :=
.seq crepBody208_7 crepBody208_5

def crepBody208_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.const 20#64]

def crepBody208_10 : CrepProg (BitVec 64) :=
.seq crepBody208_8 crepBody208_9

def crepBody208_11 : CrepProg (BitVec 64) :=
.seq crepBody208_10 crepBody208_5

def crepBody208_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody208_13 : CrepProg (BitVec 64) :=
.seq crepBody208_11 crepBody208_12

def crepBody208_14 : CrepProg (BitVec 64) :=
.seq crepBody208_13 crepBody208_5

def crepBody208_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody208_16 : CrepProg (BitVec 64) :=
.seq crepBody208_14 crepBody208_15

def crepBody208_17 : CrepProg (BitVec 64) :=
.seq crepBody208_16 crepBody208_5

def crepBody208_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody208_19 : CrepProg (BitVec 64) :=
.seq crepBody208_17 crepBody208_18

def crepBody208_20 : CrepProg (BitVec 64) :=
.seq crepBody208_19 crepBody208_5

def crepBody208_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.const 256#64]

def crepBody208_22 : CrepProg (BitVec 64) :=
.seq crepBody208_20 crepBody208_21

def crepBody208_23 : CrepProg (BitVec 64) :=
.seq crepBody208_22 crepBody208_5

def crepBody208_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_put_u256"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody208_25 : CrepProg (BitVec 64) :=
.seq crepBody208_23 crepBody208_24

def crepBody208_26 : CrepProg (BitVec 64) :=
.seq crepBody208_25 crepBody208_5

def crepBody208_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64])]

def crepBody208_28 : CrepProg (BitVec 64) :=
.seq crepBody208_26 crepBody208_27

def crepBody208_29 : CrepProg (BitVec 64) :=
.seq crepBody208_28 crepBody208_5

def crepBody208_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 104#64])]

def crepBody208_31 : CrepProg (BitVec 64) :=
.seq crepBody208_29 crepBody208_30

def crepBody208_32 : CrepProg (BitVec 64) :=
.seq crepBody208_31 crepBody208_5

def crepBody208_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64])]

def crepBody208_34 : CrepProg (BitVec 64) :=
.seq crepBody208_32 crepBody208_33

def crepBody208_35 : CrepProg (BitVec 64) :=
.seq crepBody208_34 crepBody208_5

def crepBody208_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 120#64])]

def crepBody208_37 : CrepProg (BitVec 64) :=
.seq crepBody208_35 crepBody208_36

def crepBody208_38 : CrepProg (BitVec 64) :=
.seq crepBody208_37 crepBody208_5

def crepBody208_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 128#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 136#64])]

def crepBody208_40 : CrepProg (BitVec 64) :=
.seq crepBody208_38 crepBody208_39

def crepBody208_41 : CrepProg (BitVec 64) :=
.seq crepBody208_40 crepBody208_5

def crepBody208_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 144#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody208_43 : CrepProg (BitVec 64) :=
.seq crepBody208_41 crepBody208_42

def crepBody208_44 : CrepProg (BitVec 64) :=
.seq crepBody208_43 crepBody208_5

def crepBody208_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 152#64]),
    Flapjack.CrepExp.const 8#64]

def crepBody208_46 : CrepProg (BitVec 64) :=
.seq crepBody208_44 crepBody208_45

def crepBody208_47 : CrepProg (BitVec 64) :=
.seq crepBody208_46 crepBody208_5

def crepBody208_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_put_u256"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody208_49 : CrepProg (BitVec 64) :=
.seq crepBody208_47 crepBody208_48

def crepBody208_50 : CrepProg (BitVec 64) :=
.seq crepBody208_49 crepBody208_5

def crepBody208_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody208_52 : CrepProg (BitVec 64) :=
.seq crepBody208_50 crepBody208_51

def crepBody208_53 : CrepProg (BitVec 64) :=
.seq crepBody208_52 crepBody208_5

def crepBody208_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 200#64])]

def crepBody208_55 : CrepProg (BitVec 64) :=
.seq crepBody208_53 crepBody208_54

def crepBody208_56 : CrepProg (BitVec 64) :=
.seq crepBody208_55 crepBody208_5

def crepBody208_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 208#64])]

def crepBody208_58 : CrepProg (BitVec 64) :=
.seq crepBody208_56 crepBody208_57

def crepBody208_59 : CrepProg (BitVec 64) :=
.seq crepBody208_58 crepBody208_5

def crepBody208_60 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 216#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody208_61 : CrepProg (BitVec 64) :=
.seq crepBody208_59 crepBody208_60

def crepBody208_62 : CrepProg (BitVec 64) :=
.seq crepBody208_61 crepBody208_5

def crepBody208_63 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 224#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody208_64 : CrepProg (BitVec 64) :=
.seq crepBody208_62 crepBody208_63

def crepBody208_65 : CrepProg (BitVec 64) :=
.seq crepBody208_64 crepBody208_5

def crepBody208_66 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 232#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody208_67 : CrepProg (BitVec 64) :=
.seq crepBody208_66 crepBody208_5

def crepBody208_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 240#64])]

def crepBody208_69 : CrepProg (BitVec 64) :=
.seq crepBody208_67 crepBody208_68

def crepBody208_70 : CrepProg (BitVec 64) :=
.seq crepBody208_69 crepBody208_5

def crepBody208_71 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody208_70 crepBody208_3

def crepBody208_72 : CrepProg (BitVec 64) :=
.seq crepBody208_65 crepBody208_71

def crepBody208_73 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 4]

def crepBody208_74 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "rlp_encode_list_header" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 4]

def crepBody208_75 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody208_74

def crepBody208_76 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]]

def crepBody208_77 : CrepProg (BitVec 64) :=
.seq crepBody208_75 crepBody208_76

def crepBody208_78 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 9#64], Flapjack.CrepExp.var 5]) crepBody208_77

def crepBody208_79 : CrepProg (BitVec 64) :=
.seq crepBody208_73 crepBody208_78

def crepBody208_80 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody208_79

def crepBody208_81 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 9#64]]) crepBody208_80

def crepBody208_82 : CrepProg (BitVec 64) :=
.seq crepBody208_72 crepBody208_81

def crepBody208_83 : CrepProg (BitVec 64) :=
.seq crepBody208_1 crepBody208_82

def crepBody208_84 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody208_83

def crepBody208_85 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 9#64]) crepBody208_84

def crepBody208_86 : CrepProg (BitVec 64) :=
.seq crepBody208_0 crepBody208_85

def crepBody208_87 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody208_86

def data208 : CrepProg (BitVec 64) := crepBody208_87
def output208 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8], [0], crepProgToHOL data208)
end InitECandidate.Proofs.FrontendStages.Crep
