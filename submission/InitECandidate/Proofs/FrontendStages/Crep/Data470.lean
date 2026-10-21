import InitECandidate.Proofs.FrontendStages.Crep.Translate454
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody470_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 15)

def crepBody470_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 16)

def crepBody470_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 17)

def crepBody470_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 18)

def crepBody470_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody470_5 : CrepProg (BitVec 64) :=
.seq crepBody470_3 crepBody470_4

def crepBody470_6 : CrepProg (BitVec 64) :=
.seq crepBody470_2 crepBody470_5

def crepBody470_7 : CrepProg (BitVec 64) :=
.seq crepBody470_1 crepBody470_6

def crepBody470_8 : CrepProg (BitVec 64) :=
.seq crepBody470_0 crepBody470_7

def crepBody470_9 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 13) crepBody470_8

def crepBody470_10 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 12) crepBody470_9

def crepBody470_11 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 11) crepBody470_10

def crepBody470_12 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 10) crepBody470_11

def crepBody470_13 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 4) crepBody470_12

def crepBody470_14 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 9) crepBody470_8

def crepBody470_15 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 8) crepBody470_14

def crepBody470_16 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 7) crepBody470_15

def crepBody470_17 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 6) crepBody470_16

def crepBody470_18 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 5) crepBody470_17

def crepBody470_19 : CrepProg (BitVec 64) :=
.seq crepBody470_13 crepBody470_18

def crepBody470_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody470_21 : CrepProg (BitVec 64) :=
.seq crepBody470_19 crepBody470_20

def crepBody470_22 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 24#64])) crepBody470_21

def crepBody470_23 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 16#64])) crepBody470_22

def crepBody470_24 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64])) crepBody470_23

def crepBody470_25 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 5)) crepBody470_24

def crepBody470_26 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64])) crepBody470_25

def crepBody470_27 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64])) crepBody470_26

def crepBody470_28 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64])) crepBody470_27

def crepBody470_29 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 4)) crepBody470_28

def crepBody470_30 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.op Flapjack.BinOp.sub
          [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64],
            Flapjack.CrepExp.var 1],
        Flapjack.CrepExp.const 32#64]]) crepBody470_29

def crepBody470_31 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.op Flapjack.BinOp.sub
          [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64],
            Flapjack.CrepExp.var 0],
        Flapjack.CrepExp.const 32#64]]) crepBody470_30

def crepBody470_32 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 8#64])) crepBody470_31

def crepBody470_33 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 16#64])) crepBody470_32

def data470 : CrepProg (BitVec 64) := crepBody470_33
def output470 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 116#8, 97#8, 99#8, 107#8, 95#8, 115#8, 119#8, 97#8, 112#8, 95#8, 112#8, 111#8, 115#8, 105#8, 116#8, 105#8,
    111#8, 110#8, 115#8], [0, 1], crepProgToHOL data470)
end InitECandidate.Proofs.FrontendStages.Crep
