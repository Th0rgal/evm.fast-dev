import InitECandidate.Proofs.FrontendStages.Crep.Translate551
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody567_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody567_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody567_2 : CrepProg (BitVec 64) :=
.seq crepBody567_0 crepBody567_1

def crepBody567_3 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody567_2

def crepBody567_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64]]) crepBody567_3

def crepBody567_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 5)

def crepBody567_6 : CrepProg (BitVec 64) :=
.seq crepBody567_5 crepBody567_1

def crepBody567_7 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody567_6

def crepBody567_8 : CrepProg (BitVec 64) :=
.seq crepBody567_4 crepBody567_7

def crepBody567_9 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 3)) crepBody567_8

def crepBody567_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.const 0#64)

def crepBody567_11 : CrepProg (BitVec 64) :=
.seq crepBody567_10 crepBody567_1

def crepBody567_12 : CrepProg (BitVec 64) :=
.seq crepBody567_9 crepBody567_11

def crepBody567_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 8)

def crepBody567_14 : CrepProg (BitVec 64) :=
.seq crepBody567_13 crepBody567_1

def crepBody567_15 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.load (Flapjack.CrepExp.var 6),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4]))
      (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 3#64],
          Flapjack.CrepExp.const 8#64])]) crepBody567_14

def crepBody567_16 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 6) crepBody567_15

def crepBody567_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 7)

def crepBody567_18 : CrepProg (BitVec 64) :=
.seq crepBody567_17 crepBody567_1

def crepBody567_19 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody567_18

def crepBody567_20 : CrepProg (BitVec 64) :=
.seq crepBody567_16 crepBody567_19

def crepBody567_21 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 2#64),
        Flapjack.CrepExp.const 8#64]]) crepBody567_20

def crepBody567_22 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64], Flapjack.CrepExp.var 4]) crepBody567_21

def crepBody567_23 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 1)) crepBody567_22

def crepBody567_24 : CrepProg (BitVec 64) :=
.seq crepBody567_12 crepBody567_23

def crepBody567_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody567_26 : CrepProg (BitVec 64) :=
.seq crepBody567_24 crepBody567_25

def crepBody567_27 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody567_26

def crepBody567_28 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.shift Flapjack.Shift.lsr
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 3#64])
  (Flapjack.CrepExp.const 2#64)) crepBody567_27

def data567 : CrepProg (BitVec 64) := crepBody567_28
def output567 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [98#8, 110#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 98#8, 101#8], [0, 1, 2], crepProgToHOL data567)
end InitECandidate.Proofs.FrontendStages.Crep
