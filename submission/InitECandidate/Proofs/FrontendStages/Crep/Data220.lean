import InitECandidate.Proofs.FrontendStages.Crep.Translate204
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody220_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 2,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 3]])
  (Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 4#64))

def crepBody220_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 2,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 3],
      Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 15#64])

def crepBody220_2 : CrepProg (BitVec 64) :=
.seq crepBody220_0 crepBody220_1

def crepBody220_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 2,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 3],
      Flapjack.CrepExp.const 2#64])
  (Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 4#64))

def crepBody220_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 2,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 3],
      Flapjack.CrepExp.const 3#64])
  (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 15#64])

def crepBody220_5 : CrepProg (BitVec 64) :=
.seq crepBody220_3 crepBody220_4

def crepBody220_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 2,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 3],
      Flapjack.CrepExp.const 4#64])
  (Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 4#64))

def crepBody220_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 2,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 3],
      Flapjack.CrepExp.const 5#64])
  (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 15#64])

def crepBody220_8 : CrepProg (BitVec 64) :=
.seq crepBody220_6 crepBody220_7

def crepBody220_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 2,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 3],
      Flapjack.CrepExp.const 6#64])
  (Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 4#64))

def crepBody220_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 2,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 3],
      Flapjack.CrepExp.const 7#64])
  (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 15#64])

def crepBody220_11 : CrepProg (BitVec 64) :=
.seq crepBody220_9 crepBody220_10

def crepBody220_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 8)

def crepBody220_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody220_14 : CrepProg (BitVec 64) :=
.seq crepBody220_12 crepBody220_13

def crepBody220_15 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64]) crepBody220_14

def crepBody220_16 : CrepProg (BitVec 64) :=
.seq crepBody220_11 crepBody220_15

def crepBody220_17 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.loadByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 3#64])) crepBody220_16

def crepBody220_18 : CrepProg (BitVec 64) :=
.seq crepBody220_8 crepBody220_17

def crepBody220_19 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.loadByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 2#64])) crepBody220_18

def crepBody220_20 : CrepProg (BitVec 64) :=
.seq crepBody220_5 crepBody220_19

def crepBody220_21 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.loadByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64])) crepBody220_20

def crepBody220_22 : CrepProg (BitVec 64) :=
.seq crepBody220_2 crepBody220_21

def crepBody220_23 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3])) crepBody220_22

def crepBody220_24 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 1)
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64])) crepBody220_23

def crepBody220_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 5)

def crepBody220_26 : CrepProg (BitVec 64) :=
.seq crepBody220_25 crepBody220_13

def crepBody220_27 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody220_26

def crepBody220_28 : CrepProg (BitVec 64) :=
.seq crepBody220_2 crepBody220_27

def crepBody220_29 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3])) crepBody220_28

def crepBody220_30 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 1)) crepBody220_29

def crepBody220_31 : CrepProg (BitVec 64) :=
.seq crepBody220_24 crepBody220_30

def crepBody220_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody220_33 : CrepProg (BitVec 64) :=
.seq crepBody220_31 crepBody220_32

def crepBody220_34 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody220_33

def data220 : CrepProg (BitVec 64) := crepBody220_34
def output220 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [107#8, 101#8, 121#8, 95#8, 116#8, 111#8, 95#8, 110#8, 105#8, 98#8, 98#8, 108#8, 101#8, 115#8], [0, 1, 2], crepProgToHOL data220)
end InitECandidate.Proofs.FrontendStages.Crep
