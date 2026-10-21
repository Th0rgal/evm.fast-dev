import InitECandidate.Proofs.FrontendStages.Crep.Translate736
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody752_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 524#64]

def crepBody752_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody752_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 128#64) (Flapjack.CrepExp.var 0)) crepBody752_0 crepBody752_1

def crepBody752_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 400#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.sub
                [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.const 128#64, Flapjack.CrepExp.var 0],
                  Flapjack.CrepExp.const 1#64],
              Flapjack.CrepExp.const 8#64]])]

def crepBody752_4 : CrepProg (BitVec 64) :=
.seq crepBody752_2 crepBody752_3

def data752 : CrepProg (BitVec 64) := crepBody752_4
def output752 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 103#8, 50#8, 95#8, 109#8, 115#8, 109#8, 95#8, 100#8, 105#8, 115#8, 99#8, 111#8, 117#8,
    110#8, 116#8], [0], crepProgToHOL data752)
end InitECandidate.Proofs.FrontendStages.Crep
