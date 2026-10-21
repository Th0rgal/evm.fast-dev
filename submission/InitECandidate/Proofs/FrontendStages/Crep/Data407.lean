import InitECandidate.Proofs.FrontendStages.Crep.Translate391
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody407_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 2)

def crepBody407_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody407_2 : CrepProg (BitVec 64) :=
.seq crepBody407_0 crepBody407_1

def crepBody407_3 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 2#64) crepBody407_2

def crepBody407_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody407_5 : CrepProg (BitVec 64) :=
.seq crepBody407_3 crepBody407_4

def crepBody407_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody407_5 crepBody407_1

def crepBody407_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 1 (Flapjack.CrepExp.var 2)

def crepBody407_8 : CrepProg (BitVec 64) :=
.seq crepBody407_7 crepBody407_1

def crepBody407_9 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64]) crepBody407_8

def crepBody407_10 : CrepProg (BitVec 64) :=
.seq crepBody407_6 crepBody407_9

def crepBody407_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody407_12 : CrepProg (BitVec 64) :=
.seq crepBody407_11 crepBody407_1

def crepBody407_13 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.var 1) crepBody407_12

def crepBody407_14 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 16#64]) crepBody407_13

def crepBody407_15 : CrepProg (BitVec 64) :=
.seq crepBody407_10 crepBody407_14

def crepBody407_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.load
                  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
                Flapjack.CrepExp.const 8#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.sub
                        [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
                    Flapjack.CrepExp.const 8#64]),
              Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.sub
                        [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
                    Flapjack.CrepExp.const 8#64]),
              Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.sub
                        [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
                    Flapjack.CrepExp.const 8#64]),
              Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]],
          Flapjack.CrepExp.const 24#64])]

def crepBody407_17 : CrepProg (BitVec 64) :=
.seq crepBody407_15 crepBody407_16

def crepBody407_18 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 16#64])) crepBody407_17

def data407 : CrepProg (BitVec 64) := crepBody407_18
def output407 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 99#8, 107#8, 95#8, 112#8, 111#8, 112#8], [], crepProgToHOL data407)
end InitECandidate.Proofs.FrontendStages.Crep
