import InitECandidate.Proofs.FrontendStages.Crep.Translate402
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody418_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody418_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody418_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.op Flapjack.BinOp.or [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3])
  (Flapjack.CrepExp.const 0#64)) crepBody418_0 crepBody418_1

def crepBody418_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 4)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
        Flapjack.CrepExp.const 56#64]))) crepBody418_0 crepBody418_1

def crepBody418_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.op Flapjack.BinOp.and
      [Flapjack.CrepExp.shift Flapjack.Shift.lsr
          (Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 5,
                Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                  [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 6#64),
                    Flapjack.CrepExp.const 8#64]]))
          (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 63#64]),
        Flapjack.CrepExp.const 1#64]]

def crepBody418_5 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 80#64])) crepBody418_4

def crepBody418_6 : CrepProg (BitVec 64) :=
.seq crepBody418_3 crepBody418_5

def crepBody418_7 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 0) crepBody418_6

def crepBody418_8 : CrepProg (BitVec 64) :=
.seq crepBody418_2 crepBody418_7

def data418 : CrepProg (BitVec 64) := crepBody418_8
def output418 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [105#8, 115#8, 95#8, 118#8, 97#8, 108#8, 105#8, 100#8, 95#8, 106#8, 117#8, 109#8, 112#8, 100#8, 101#8, 115#8, 116#8], [0, 1, 2, 3], crepProgToHOL data418)
end InitECandidate.Proofs.FrontendStages.Crep
