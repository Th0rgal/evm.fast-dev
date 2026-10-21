import InitECandidate.Proofs.FrontendStages.Crep.Translate305
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody321_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "htab_get" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody321_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody321_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody321_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody321_1 crepBody321_2

def crepBody321_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "trap_with" [Flapjack.CrepExp.const 5#64]

def crepBody321_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody321_4

def crepBody321_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]))
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 208#64]))) crepBody321_5 crepBody321_2

def crepBody321_7 : CrepProg (BitVec 64) :=
.seq crepBody321_3 crepBody321_6

def crepBody321_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody321_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memcpy"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 4]

def crepBody321_10 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody321_9

def crepBody321_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 8)

def crepBody321_12 : CrepProg (BitVec 64) :=
.seq crepBody321_11 crepBody321_2

def crepBody321_13 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 0) crepBody321_12

def crepBody321_14 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 6) crepBody321_13

def crepBody321_15 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 5) crepBody321_12

def crepBody321_16 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64]) crepBody321_15

def crepBody321_17 : CrepProg (BitVec 64) :=
.seq crepBody321_14 crepBody321_16

def crepBody321_18 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 1#64) crepBody321_12

def crepBody321_19 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64]) crepBody321_18

def crepBody321_20 : CrepProg (BitVec 64) :=
.seq crepBody321_17 crepBody321_19

def crepBody321_21 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 3) crepBody321_12

def crepBody321_22 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 24#64]) crepBody321_21

def crepBody321_23 : CrepProg (BitVec 64) :=
.seq crepBody321_20 crepBody321_22

def crepBody321_24 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.const 1#64]) crepBody321_12

def crepBody321_25 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]) crepBody321_24

def crepBody321_26 : CrepProg (BitVec 64) :=
.seq crepBody321_23 crepBody321_25

def crepBody321_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "htab_del" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody321_28 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody321_27

def crepBody321_29 : CrepProg (BitVec 64) :=
.seq crepBody321_26 crepBody321_28

def crepBody321_30 : CrepProg (BitVec 64) :=
.seq crepBody321_29 crepBody321_1

def crepBody321_31 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 200#64]),
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]),
        Flapjack.CrepExp.const 32#64]]) crepBody321_30

def crepBody321_32 : CrepProg (BitVec 64) :=
.seq crepBody321_10 crepBody321_31

def crepBody321_33 : CrepProg (BitVec 64) :=
.seq crepBody321_8 crepBody321_32

def crepBody321_34 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody321_33

def crepBody321_35 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody321_34

def crepBody321_36 : CrepProg (BitVec 64) :=
.seq crepBody321_7 crepBody321_35

def crepBody321_37 : CrepProg (BitVec 64) :=
.seq crepBody321_0 crepBody321_36

def crepBody321_38 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody321_37

def crepBody321_39 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody321_38

def data321 : CrepProg (BitVec 64) := crepBody321_39
def output321 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [106#8, 100#8, 101#8, 108#8], [0, 1], crepProgToHOL data321)
end InitECandidate.Proofs.FrontendStages.Crep
