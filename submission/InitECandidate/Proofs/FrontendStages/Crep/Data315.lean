import InitECandidate.Proofs.FrontendStages.Crep.Translate299
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody315_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2 (Flapjack.CrepExp.var 4)

def crepBody315_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody315_2 : CrepProg (BitVec 64) :=
.seq crepBody315_0 crepBody315_1

def crepBody315_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64]) crepBody315_2

def crepBody315_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]))
  (Flapjack.CrepExp.const 0#64)) crepBody315_3 crepBody315_1

def crepBody315_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 4)

def crepBody315_6 : CrepProg (BitVec 64) :=
.seq crepBody315_5 crepBody315_1

def crepBody315_7 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody315_6

def crepBody315_8 : CrepProg (BitVec 64) :=
.seq crepBody315_4 crepBody315_7

def crepBody315_9 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 1)) crepBody315_8

def crepBody315_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 2,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
          [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2],
            Flapjack.CrepExp.const 4#64]]]

def crepBody315_11 : CrepProg (BitVec 64) :=
.seq crepBody315_9 crepBody315_10

def crepBody315_12 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody315_11

def crepBody315_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody315_12

def data315 : CrepProg (BitVec 64) := crepBody315_13
def output315 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 116#8, 111#8, 107#8, 101#8, 110#8, 115#8, 95#8, 105#8, 110#8, 95#8, 100#8,
    97#8, 116#8, 97#8], [0, 1], crepProgToHOL data315)
end InitECandidate.Proofs.FrontendStages.Crep
