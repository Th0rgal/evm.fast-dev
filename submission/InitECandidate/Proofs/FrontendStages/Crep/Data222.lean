import InitECandidate.Proofs.FrontendStages.Crep.Translate206
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody222_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 3)
  (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 16#64, Flapjack.CrepExp.var 4])

def crepBody222_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 3)
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.const 16#64,
          Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]],
      Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 0)])

def crepBody222_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.const 1#64)

def crepBody222_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody222_4 : CrepProg (BitVec 64) :=
.seq crepBody222_2 crepBody222_3

def crepBody222_5 : CrepProg (BitVec 64) :=
.seq crepBody222_1 crepBody222_4

def crepBody222_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.const 0#64)) crepBody222_0 crepBody222_5

def crepBody222_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 6])
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.shift Flapjack.Shift.lsl
        (Flapjack.CrepExp.loadByte
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5]))
        (Flapjack.CrepExp.const 4#64),
      Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64])])

def crepBody222_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 7)

def crepBody222_9 : CrepProg (BitVec 64) :=
.seq crepBody222_8 crepBody222_3

def crepBody222_10 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 2#64]) crepBody222_9

def crepBody222_11 : CrepProg (BitVec 64) :=
.seq crepBody222_7 crepBody222_10

def crepBody222_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 7)

def crepBody222_13 : CrepProg (BitVec 64) :=
.seq crepBody222_12 crepBody222_3

def crepBody222_14 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64]) crepBody222_13

def crepBody222_15 : CrepProg (BitVec 64) :=
.seq crepBody222_11 crepBody222_14

def crepBody222_16 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 1)) crepBody222_15

def crepBody222_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 6]

def crepBody222_18 : CrepProg (BitVec 64) :=
.seq crepBody222_16 crepBody222_17

def crepBody222_19 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 1#64) crepBody222_18

def crepBody222_20 : CrepProg (BitVec 64) :=
.seq crepBody222_6 crepBody222_19

def crepBody222_21 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody222_20

def crepBody222_22 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 2#64]) crepBody222_21

def data222 : CrepProg (BitVec 64) := crepBody222_22
def output222 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [110#8, 105#8, 98#8, 98#8, 108#8, 101#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 116#8, 111#8, 95#8, 99#8, 111#8,
    109#8, 112#8, 97#8, 99#8, 116#8], [0, 1, 2, 3], crepProgToHOL data222)
end InitECandidate.Proofs.FrontendStages.Crep
