import InitECandidate.Proofs.FrontendStages.Crep.Translate387
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody403_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody403_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody403_2 : CrepProg (BitVec 64) :=
.seq crepBody403_0 crepBody403_1

def crepBody403_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 0]) crepBody403_2

def crepBody403_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 72#64]) crepBody403_3

def crepBody403_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody403_6 : CrepProg (BitVec 64) :=
.seq crepBody403_4 crepBody403_5

def crepBody403_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 0)) crepBody403_6 crepBody403_1

def crepBody403_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "add_sat" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody403_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody403_10 : CrepProg (BitVec 64) :=
.seq crepBody403_9 crepBody403_1

def crepBody403_11 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody403_10

def crepBody403_12 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 72#64]) crepBody403_11

def crepBody403_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 4]) crepBody403_10

def crepBody403_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 64#64]) crepBody403_13

def crepBody403_15 : CrepProg (BitVec 64) :=
.seq crepBody403_12 crepBody403_14

def crepBody403_16 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 192#64]),
    Flapjack.CrepExp.var 4]) crepBody403_10

def crepBody403_17 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 192#64]) crepBody403_16

def crepBody403_18 : CrepProg (BitVec 64) :=
.seq crepBody403_15 crepBody403_17

def crepBody403_19 : CrepProg (BitVec 64) :=
.seq crepBody403_18 crepBody403_5

def crepBody403_20 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]) crepBody403_19

def crepBody403_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 0)) crepBody403_20 crepBody403_1

def crepBody403_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 4)

def crepBody403_23 : CrepProg (BitVec 64) :=
.seq crepBody403_22 crepBody403_1

def crepBody403_24 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 4#64) crepBody403_23

def crepBody403_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody403_26 : CrepProg (BitVec 64) :=
.seq crepBody403_24 crepBody403_25

def crepBody403_27 : CrepProg (BitVec 64) :=
.seq crepBody403_21 crepBody403_26

def crepBody403_28 : CrepProg (BitVec 64) :=
.seq crepBody403_27 crepBody403_5

def crepBody403_29 : CrepProg (BitVec 64) :=
.seq crepBody403_8 crepBody403_28

def crepBody403_30 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody403_29

def crepBody403_31 : CrepProg (BitVec 64) :=
.seq crepBody403_7 crepBody403_30

def crepBody403_32 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 64#64])) crepBody403_31

def crepBody403_33 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 72#64])) crepBody403_32

def data403 : CrepProg (BitVec 64) := crepBody403_33
def output403 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 104#8, 97#8, 114#8, 103#8, 101#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 103#8, 97#8, 115#8], [0], crepProgToHOL data403)
end InitECandidate.Proofs.FrontendStages.Crep
