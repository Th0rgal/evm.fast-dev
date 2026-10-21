import InitECandidate.Proofs.FrontendStages.Crep.Translate513
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody529_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "refill_frame_state_gas" []

def crepBody529_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody529_0

def crepBody529_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "frame_halt" [Flapjack.CrepExp.var 0]

def crepBody529_3 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody529_2

def crepBody529_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 2)

def crepBody529_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody529_6 : CrepProg (BitVec 64) :=
.seq crepBody529_4 crepBody529_5

def crepBody529_7 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 264#64])) crepBody529_6

def crepBody529_8 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody529_7

def crepBody529_9 : CrepProg (BitVec 64) :=
.seq crepBody529_3 crepBody529_8

def crepBody529_10 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody529_6

def crepBody529_11 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody529_10

def crepBody529_12 : CrepProg (BitVec 64) :=
.seq crepBody529_9 crepBody529_11

def crepBody529_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.var 0) crepBody529_6

def crepBody529_14 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 160#64]) crepBody529_13

def crepBody529_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 1#64)) crepBody529_12 crepBody529_14

def crepBody529_16 : CrepProg (BitVec 64) :=
.seq crepBody529_1 crepBody529_15

def crepBody529_17 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 1#64) crepBody529_6

def crepBody529_18 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.const 32#64]) crepBody529_17

def crepBody529_19 : CrepProg (BitVec 64) :=
.seq crepBody529_16 crepBody529_18

def crepBody529_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody529_21 : CrepProg (BitVec 64) :=
.seq crepBody529_19 crepBody529_20

def data529 : CrepProg (BitVec 64) := crepBody529_21
def output529 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 101#8, 120#8, 99#8, 101#8, 112#8, 116#8, 105#8, 111#8, 110#8], [0], crepProgToHOL data529)
end InitECandidate.Proofs.FrontendStages.Crep
