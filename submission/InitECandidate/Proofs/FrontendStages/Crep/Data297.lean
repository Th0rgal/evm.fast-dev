import InitECandidate.Proofs.FrontendStages.Crep.Translate281
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody297_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "auth_list_payload_len" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody297_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "rlp_encode_list_header" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]

def crepBody297_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "auth_payload_len" [Flapjack.CrepExp.var 7]

def crepBody297_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "rlp_encode_list_header" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 8]

def crepBody297_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 9)

def crepBody297_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody297_6 : CrepProg (BitVec 64) :=
.seq crepBody297_4 crepBody297_5

def crepBody297_7 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 4]) crepBody297_6

def crepBody297_8 : CrepProg (BitVec 64) :=
.seq crepBody297_3 crepBody297_7

def crepBody297_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 0#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 0#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 0#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 0#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody297_10 : CrepProg (BitVec 64) :=
.seq crepBody297_8 crepBody297_9

def crepBody297_11 : CrepProg (BitVec 64) :=
.seq crepBody297_10 crepBody297_7

def crepBody297_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.const 20#64]

def crepBody297_13 : CrepProg (BitVec 64) :=
.seq crepBody297_11 crepBody297_12

def crepBody297_14 : CrepProg (BitVec 64) :=
.seq crepBody297_13 crepBody297_7

def crepBody297_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 40#64])]

def crepBody297_16 : CrepProg (BitVec 64) :=
.seq crepBody297_14 crepBody297_15

def crepBody297_17 : CrepProg (BitVec 64) :=
.seq crepBody297_16 crepBody297_7

def crepBody297_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 48#64])]

def crepBody297_19 : CrepProg (BitVec 64) :=
.seq crepBody297_17 crepBody297_18

def crepBody297_20 : CrepProg (BitVec 64) :=
.seq crepBody297_19 crepBody297_7

def crepBody297_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody297_22 : CrepProg (BitVec 64) :=
.seq crepBody297_20 crepBody297_21

def crepBody297_23 : CrepProg (BitVec 64) :=
.seq crepBody297_22 crepBody297_7

def crepBody297_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 88#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 88#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 88#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody297_25 : CrepProg (BitVec 64) :=
.seq crepBody297_23 crepBody297_24

def crepBody297_26 : CrepProg (BitVec 64) :=
.seq crepBody297_25 crepBody297_7

def crepBody297_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 9)

def crepBody297_28 : CrepProg (BitVec 64) :=
.seq crepBody297_27 crepBody297_5

def crepBody297_29 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64]) crepBody297_28

def crepBody297_30 : CrepProg (BitVec 64) :=
.seq crepBody297_26 crepBody297_29

def crepBody297_31 : CrepProg (BitVec 64) :=
.seq crepBody297_2 crepBody297_30

def crepBody297_32 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody297_31

def crepBody297_33 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 120#64]]) crepBody297_32

def crepBody297_34 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 2)) crepBody297_33

def crepBody297_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 0]]

def crepBody297_36 : CrepProg (BitVec 64) :=
.seq crepBody297_34 crepBody297_35

def crepBody297_37 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody297_36

def crepBody297_38 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4]) crepBody297_37

def crepBody297_39 : CrepProg (BitVec 64) :=
.seq crepBody297_1 crepBody297_38

def crepBody297_40 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody297_39

def crepBody297_41 : CrepProg (BitVec 64) :=
.seq crepBody297_0 crepBody297_40

def crepBody297_42 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody297_41

def data297 : CrepProg (BitVec 64) := crepBody297_42
def output297 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [116#8, 120#8, 95#8, 112#8, 117#8, 116#8, 95#8, 97#8, 117#8, 116#8, 104#8, 111#8, 114#8, 105#8, 122#8, 97#8, 116#8,
    105#8, 111#8, 110#8, 115#8], [0, 1, 2], crepProgToHOL data297)
end InitECandidate.Proofs.FrontendStages.Crep
