import InitECandidate.Proofs.FrontendStages.Crep.Translate250
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody266_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "rlp_encode_word"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8], Flapjack.CrepExp.var 0]

def crepBody266_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 10)

def crepBody266_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody266_3 : CrepProg (BitVec 64) :=
.seq crepBody266_1 crepBody266_2

def crepBody266_4 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]) crepBody266_3

def crepBody266_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "st_be64"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]),
    Flapjack.CrepExp.var 4]

def crepBody266_6 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody266_5

def crepBody266_7 : CrepProg (BitVec 64) :=
.seq crepBody266_4 crepBody266_6

def crepBody266_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]),
        Flapjack.CrepExp.const 8#64],
    Flapjack.CrepExp.var 3]

def crepBody266_9 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody266_8

def crepBody266_10 : CrepProg (BitVec 64) :=
.seq crepBody266_7 crepBody266_9

def crepBody266_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]),
        Flapjack.CrepExp.const 16#64],
    Flapjack.CrepExp.var 2]

def crepBody266_12 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody266_11

def crepBody266_13 : CrepProg (BitVec 64) :=
.seq crepBody266_10 crepBody266_12

def crepBody266_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]),
        Flapjack.CrepExp.const 24#64],
    Flapjack.CrepExp.var 1]

def crepBody266_15 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody266_14

def crepBody266_16 : CrepProg (BitVec 64) :=
.seq crepBody266_13 crepBody266_15

def crepBody266_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.break 0

def crepBody266_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.loadByte
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]),
        Flapjack.CrepExp.var 10]))
  (Flapjack.CrepExp.const 0#64)) crepBody266_17 crepBody266_2

def crepBody266_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 11)

def crepBody266_20 : CrepProg (BitVec 64) :=
.seq crepBody266_19 crepBody266_2

def crepBody266_21 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 1#64]) crepBody266_20

def crepBody266_22 : CrepProg (BitVec 64) :=
.seq crepBody266_18 crepBody266_21

def crepBody266_23 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 32#64)) crepBody266_22

def crepBody266_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]),
        Flapjack.CrepExp.var 10],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 10]]

def crepBody266_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 12)

def crepBody266_26 : CrepProg (BitVec 64) :=
.seq crepBody266_25 crepBody266_2

def crepBody266_27 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 11]) crepBody266_26

def crepBody266_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8], Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.const 32#64]

def crepBody266_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 13)

def crepBody266_30 : CrepProg (BitVec 64) :=
.seq crepBody266_29 crepBody266_2

def crepBody266_31 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 12]) crepBody266_30

def crepBody266_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8], Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.const 32#64]

def crepBody266_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 14)

def crepBody266_34 : CrepProg (BitVec 64) :=
.seq crepBody266_33 crepBody266_2

def crepBody266_35 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 13]) crepBody266_34

def crepBody266_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 248#64)

def crepBody266_37 : CrepProg (BitVec 64) :=
.seq crepBody266_35 crepBody266_36

def crepBody266_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 2#64])

def crepBody266_39 : CrepProg (BitVec 64) :=
.seq crepBody266_37 crepBody266_38

def crepBody266_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 8]

def crepBody266_41 : CrepProg (BitVec 64) :=
.seq crepBody266_39 crepBody266_40

def crepBody266_42 : CrepProg (BitVec 64) :=
.seq crepBody266_32 crepBody266_41

def crepBody266_43 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody266_42

def crepBody266_44 : CrepProg (BitVec 64) :=
.seq crepBody266_31 crepBody266_43

def crepBody266_45 : CrepProg (BitVec 64) :=
.seq crepBody266_28 crepBody266_44

def crepBody266_46 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody266_45

def crepBody266_47 : CrepProg (BitVec 64) :=
.seq crepBody266_27 crepBody266_46

def crepBody266_48 : CrepProg (BitVec 64) :=
.seq crepBody266_24 crepBody266_47

def crepBody266_49 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody266_48

def crepBody266_50 : CrepProg (BitVec 64) :=
.seq crepBody266_23 crepBody266_49

def crepBody266_51 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody266_50

def crepBody266_52 : CrepProg (BitVec 64) :=
.seq crepBody266_16 crepBody266_51

def crepBody266_53 : CrepProg (BitVec 64) :=
.seq crepBody266_0 crepBody266_52

def crepBody266_54 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody266_53

def crepBody266_55 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 2#64) crepBody266_54

def data266 : CrepProg (BitVec 64) := crepBody266_55
def output266 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8], [0, 1, 2, 3, 4, 5, 6, 7], crepProgToHOL data266)
end InitECandidate.Proofs.FrontendStages.Crep
