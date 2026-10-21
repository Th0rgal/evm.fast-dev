import InitECandidate.Proofs.FrontendStages.Crep.Translate295
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody311_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody311_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody311_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "signature_recovery_parameters"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 4]

def crepBody311_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "secp256k1_recover"
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64],
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64],
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 2]

def crepBody311_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody311_5 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody311_4

def crepBody311_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 7)

def crepBody311_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody311_8 : CrepProg (BitVec 64) :=
.seq crepBody311_6 crepBody311_7

def crepBody311_9 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 46#64) crepBody311_8

def crepBody311_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 6#64

def crepBody311_11 : CrepProg (BitVec 64) :=
.seq crepBody311_9 crepBody311_10

def crepBody311_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody311_11 crepBody311_7

def crepBody311_13 : CrepProg (BitVec 64) :=
.seq crepBody311_5 crepBody311_12

def crepBody311_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody311_15 : CrepProg (BitVec 64) :=
.seq crepBody311_13 crepBody311_14

def crepBody311_16 : CrepProg (BitVec 64) :=
.seq crepBody311_3 crepBody311_15

def crepBody311_17 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody311_16

def crepBody311_18 : CrepProg (BitVec 64) :=
.seq crepBody311_2 crepBody311_17

def crepBody311_19 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody311_18

def crepBody311_20 : CrepProg (BitVec 64) :=
.seq crepBody311_1 crepBody311_19

def crepBody311_21 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody311_20

def crepBody311_22 : CrepProg (BitVec 64) :=
.seq crepBody311_0 crepBody311_21

def crepBody311_23 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody311_22

def data311 : CrepProg (BitVec 64) := crepBody311_23
def output311 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8,
    111#8, 110#8, 95#8, 112#8, 117#8, 98#8, 108#8, 105#8, 99#8, 95#8, 107#8, 101#8, 121#8], [0, 1, 2], crepProgToHOL data311)
end InitECandidate.Proofs.FrontendStages.Crep
