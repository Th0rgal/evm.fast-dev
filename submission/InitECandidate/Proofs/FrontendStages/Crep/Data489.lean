import InitECandidate.Proofs.FrontendStages.Crep.Translate473
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody489_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "charge_gas" [Flapjack.CrepExp.const 2#64]

def crepBody489_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody489_0

def crepBody489_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "stack_push"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.load
                  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
                Flapjack.CrepExp.const 112#64]),
          Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.sub
                        [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
                    Flapjack.CrepExp.const 112#64]),
              Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.sub
                        [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
                    Flapjack.CrepExp.const 112#64]),
              Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.sub
                        [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
                    Flapjack.CrepExp.const 112#64]),
              Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody489_3 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody489_2

def crepBody489_4 : CrepProg (BitVec 64) :=
.seq crepBody489_1 crepBody489_3

def crepBody489_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody489_6 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody489_5

def crepBody489_7 : CrepProg (BitVec 64) :=
.seq crepBody489_4 crepBody489_6

def crepBody489_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody489_9 : CrepProg (BitVec 64) :=
.seq crepBody489_7 crepBody489_8

def data489 : CrepProg (BitVec 64) := crepBody489_9
def output489 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [111#8, 112#8, 95#8, 99#8, 97#8, 108#8, 108#8, 118#8, 97#8, 108#8, 117#8, 101#8], [], crepProgToHOL data489)
end InitECandidate.Proofs.FrontendStages.Crep
