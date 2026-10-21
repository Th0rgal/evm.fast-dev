import InitECandidate.Proofs.FrontendStages.Crep.Translate386
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody402_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 2)

def crepBody402_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody402_2 : CrepProg (BitVec 64) :=
.seq crepBody402_0 crepBody402_1

def crepBody402_3 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 4#64) crepBody402_2

def crepBody402_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody402_5 : CrepProg (BitVec 64) :=
.seq crepBody402_3 crepBody402_4

def crepBody402_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 0)) crepBody402_5 crepBody402_1

def crepBody402_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody402_8 : CrepProg (BitVec 64) :=
.seq crepBody402_7 crepBody402_1

def crepBody402_9 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 0]) crepBody402_8

def crepBody402_10 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 64#64]) crepBody402_9

def crepBody402_11 : CrepProg (BitVec 64) :=
.seq crepBody402_6 crepBody402_10

def crepBody402_12 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.var 0]) crepBody402_8

def crepBody402_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 184#64]) crepBody402_12

def crepBody402_14 : CrepProg (BitVec 64) :=
.seq crepBody402_11 crepBody402_13

def crepBody402_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody402_16 : CrepProg (BitVec 64) :=
.seq crepBody402_14 crepBody402_15

def crepBody402_17 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 64#64])) crepBody402_16

def data402 : CrepProg (BitVec 64) := crepBody402_17
def output402 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [99#8, 104#8, 97#8, 114#8, 103#8, 101#8, 95#8, 103#8, 97#8, 115#8], [0], crepProgToHOL data402)
end InitECandidate.Proofs.FrontendStages.Crep
