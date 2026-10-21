import InitECandidate.Proofs.FrontendStages.Crep.Translate304
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody320_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "htab_get" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody320_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "trap_with" [Flapjack.CrepExp.const 4#64]

def crepBody320_2 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody320_1

def crepBody320_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody320_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]))
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 208#64]))) crepBody320_2 crepBody320_3

def crepBody320_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.var 5]

def crepBody320_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "memcpy"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 5]

def crepBody320_7 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody320_6

def crepBody320_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody320_9 : CrepProg (BitVec 64) :=
.seq crepBody320_8 crepBody320_3

def crepBody320_10 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 0) crepBody320_9

def crepBody320_11 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 7) crepBody320_10

def crepBody320_12 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 6) crepBody320_9

def crepBody320_13 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]) crepBody320_12

def crepBody320_14 : CrepProg (BitVec 64) :=
.seq crepBody320_11 crepBody320_13

def crepBody320_15 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 3) crepBody320_9

def crepBody320_16 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 16#64]) crepBody320_15

def crepBody320_17 : CrepProg (BitVec 64) :=
.seq crepBody320_14 crepBody320_16

def crepBody320_18 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 4) crepBody320_9

def crepBody320_19 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 24#64]) crepBody320_18

def crepBody320_20 : CrepProg (BitVec 64) :=
.seq crepBody320_17 crepBody320_19

def crepBody320_21 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.const 1#64]) crepBody320_9

def crepBody320_22 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]) crepBody320_21

def crepBody320_23 : CrepProg (BitVec 64) :=
.seq crepBody320_20 crepBody320_22

def crepBody320_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "htab_set"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody320_25 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody320_24

def crepBody320_26 : CrepProg (BitVec 64) :=
.seq crepBody320_23 crepBody320_25

def crepBody320_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody320_28 : CrepProg (BitVec 64) :=
.seq crepBody320_26 crepBody320_27

def crepBody320_29 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 200#64]),
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]),
        Flapjack.CrepExp.const 32#64]]) crepBody320_28

def crepBody320_30 : CrepProg (BitVec 64) :=
.seq crepBody320_7 crepBody320_29

def crepBody320_31 : CrepProg (BitVec 64) :=
.seq crepBody320_5 crepBody320_30

def crepBody320_32 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody320_31

def crepBody320_33 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody320_32

def crepBody320_34 : CrepProg (BitVec 64) :=
.seq crepBody320_4 crepBody320_33

def crepBody320_35 : CrepProg (BitVec 64) :=
.seq crepBody320_0 crepBody320_34

def crepBody320_36 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody320_35

def crepBody320_37 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody320_36

def data320 : CrepProg (BitVec 64) := crepBody320_37
def output320 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [106#8, 115#8, 101#8, 116#8], [0, 1, 2], crepProgToHOL data320)
end InitECandidate.Proofs.FrontendStages.Crep
