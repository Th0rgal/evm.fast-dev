import InitECandidate.Proofs.FrontendStages.Crep.Translate457
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody473_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.op Flapjack.BinOp.and
      [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 145#64],
        Flapjack.CrepExp.const 255#64]]

def crepBody473_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody473_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.const 90#64) (Flapjack.CrepExp.var 0),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 128#64)])) crepBody473_0 crepBody473_1

def crepBody473_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 1)

def crepBody473_4 : CrepProg (BitVec 64) :=
.seq crepBody473_3 crepBody473_1

def crepBody473_5 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 10#64) crepBody473_4

def crepBody473_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody473_7 : CrepProg (BitVec 64) :=
.seq crepBody473_5 crepBody473_6

def crepBody473_8 : CrepProg (BitVec 64) :=
.seq crepBody473_2 crepBody473_7

def crepBody473_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody473_10 : CrepProg (BitVec 64) :=
.seq crepBody473_8 crepBody473_9

def data473 : CrepProg (BitVec 64) := crepBody473_10
def output473 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 115#8, 105#8, 110#8, 103#8, 108#8, 101#8], [0], crepProgToHOL data473)
end InitECandidate.Proofs.FrontendStages.Crep
