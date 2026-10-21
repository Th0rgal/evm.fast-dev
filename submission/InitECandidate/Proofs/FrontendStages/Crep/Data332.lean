import InitECandidate.Proofs.FrontendStages.Crep.Translate316
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody332_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "htab_get" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 0]

def crepBody332_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]]

def crepBody332_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody332_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody332_1 crepBody332_2

def crepBody332_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "decode_witness_to_mpt"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64]),
          Flapjack.CrepExp.const 0#64]),
    Flapjack.CrepExp.var 0]

def crepBody332_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "htab_set"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]]

def crepBody332_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody332_5

def crepBody332_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody332_8 : CrepProg (BitVec 64) :=
.seq crepBody332_6 crepBody332_7

def crepBody332_9 : CrepProg (BitVec 64) :=
.seq crepBody332_4 crepBody332_8

def crepBody332_10 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody332_9

def crepBody332_11 : CrepProg (BitVec 64) :=
.seq crepBody332_3 crepBody332_10

def crepBody332_12 : CrepProg (BitVec 64) :=
.seq crepBody332_0 crepBody332_11

def crepBody332_13 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody332_12

def crepBody332_14 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody332_13

def crepBody332_15 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64]),
      Flapjack.CrepExp.const 32#64])) crepBody332_14

def data332 : CrepProg (BitVec 64) := crepBody332_15
def output332 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [119#8, 115#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 116#8, 114#8, 105#8, 101#8], [0], crepProgToHOL data332)
end InitECandidate.Proofs.FrontendStages.Crep
