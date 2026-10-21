import InitECandidate.Proofs.FrontendStages.Crep.Translate552
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody568_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6
  (Flapjack.CrepExp.op Flapjack.BinOp.and
    [Flapjack.CrepExp.shift Flapjack.Shift.lsr
        (Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.var 0,
              Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 2#64),
                  Flapjack.CrepExp.const 8#64]]))
        (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
          [Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 3#64],
            Flapjack.CrepExp.const 8#64]),
      Flapjack.CrepExp.const 255#64])

def crepBody568_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody568_2 : CrepProg (BitVec 64) :=
.seq crepBody568_0 crepBody568_1

def crepBody568_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 2#64))
  (Flapjack.CrepExp.var 1)) crepBody568_2 crepBody568_1

def crepBody568_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 4])
  (Flapjack.CrepExp.var 6)

def crepBody568_5 : CrepProg (BitVec 64) :=
.seq crepBody568_3 crepBody568_4

def crepBody568_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 7)

def crepBody568_7 : CrepProg (BitVec 64) :=
.seq crepBody568_6 crepBody568_1

def crepBody568_8 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody568_7

def crepBody568_9 : CrepProg (BitVec 64) :=
.seq crepBody568_5 crepBody568_8

def crepBody568_10 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody568_9

def crepBody568_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64], Flapjack.CrepExp.var 4]) crepBody568_10

def crepBody568_12 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 3)) crepBody568_11

def crepBody568_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody568_14 : CrepProg (BitVec 64) :=
.seq crepBody568_12 crepBody568_13

def crepBody568_15 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody568_14

def data568 : CrepProg (BitVec 64) := crepBody568_15
def output568 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [98#8, 110#8, 95#8, 116#8, 111#8, 95#8, 98#8, 101#8], [0, 1, 2, 3], crepProgToHOL data568)
end InitECandidate.Proofs.FrontendStages.Crep
