import InitECandidate.Proofs.FrontendStages.Crep.Translate781
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody797_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "state_fresh_tx" []

def crepBody797_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody797_0

def crepBody797_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9, 10, 11, 12], none)) "u256_mul"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.const 1000000000#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.const 0#64]

def crepBody797_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "create_ether"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64],
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody797_4 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody797_3

def crepBody797_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody797_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody797_7 : CrepProg (BitVec 64) :=
.seq crepBody797_5 crepBody797_6

def crepBody797_8 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody797_7

def crepBody797_9 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]) crepBody797_8

def crepBody797_10 : CrepProg (BitVec 64) :=
.seq crepBody797_4 crepBody797_9

def crepBody797_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 13)

def crepBody797_12 : CrepProg (BitVec 64) :=
.seq crepBody797_11 crepBody797_6

def crepBody797_13 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody797_12

def crepBody797_14 : CrepProg (BitVec 64) :=
.seq crepBody797_10 crepBody797_13

def crepBody797_15 : CrepProg (BitVec 64) :=
.seq crepBody797_2 crepBody797_14

def crepBody797_16 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody797_15

def crepBody797_17 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody797_16

def crepBody797_18 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody797_17

def crepBody797_19 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody797_18

def crepBody797_20 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody797_19

def crepBody797_21 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody797_20

def crepBody797_22 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody797_21

def crepBody797_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 36#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 4#64]),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 1#64]))
            (Flapjack.CrepExp.const 8#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 2#64]))
            (Flapjack.CrepExp.const 16#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 3#64]))
            (Flapjack.CrepExp.const 24#64)])
      (Flapjack.CrepExp.const 32#64)]) crepBody797_22

def crepBody797_24 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 44#64]]) crepBody797_23

def crepBody797_25 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 1)) crepBody797_24

def crepBody797_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "incorporate_tx_into_block" []

def crepBody797_27 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody797_26

def crepBody797_28 : CrepProg (BitVec 64) :=
.seq crepBody797_25 crepBody797_27

def crepBody797_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody797_30 : CrepProg (BitVec 64) :=
.seq crepBody797_28 crepBody797_29

def crepBody797_31 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody797_30

def crepBody797_32 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64])) crepBody797_31

def crepBody797_33 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64])) crepBody797_32

def crepBody797_34 : CrepProg (BitVec 64) :=
.seq crepBody797_1 crepBody797_33

def data797 : CrepProg (BitVec 64) := crepBody797_34
def output797 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 119#8, 105#8, 116#8, 104#8, 100#8, 114#8, 97#8, 119#8, 97#8,
    108#8, 115#8], [0], crepProgToHOL data797)
end InitECandidate.Proofs.FrontendStages.Crep
