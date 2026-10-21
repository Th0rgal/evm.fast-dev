import InitECandidate.Proofs.FrontendStages.Crep.Translate625
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody641_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [12, 13] Flapjack.PrimOp.addCarry [14, 15, 16]

def crepBody641_1 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 1#64) crepBody641_0

def crepBody641_2 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.xor
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 1#64]]) crepBody641_1

def crepBody641_3 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 0) crepBody641_2

def crepBody641_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [14, 15] Flapjack.PrimOp.addCarry [16, 17, 18]

def crepBody641_5 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 13) crepBody641_4

def crepBody641_6 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.op Flapjack.BinOp.xor
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 1#64]]) crepBody641_5

def crepBody641_7 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 1) crepBody641_6

def crepBody641_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [16, 17] Flapjack.PrimOp.addCarry [18, 19, 20]

def crepBody641_9 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 15) crepBody641_8

def crepBody641_10 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.xor
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 1#64]]) crepBody641_9

def crepBody641_11 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 2) crepBody641_10

def crepBody641_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [18, 19] Flapjack.PrimOp.addCarry [20, 21, 22]

def crepBody641_13 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 17) crepBody641_12

def crepBody641_14 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.xor
  [Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 1#64]]) crepBody641_13

def crepBody641_15 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 3) crepBody641_14

def crepBody641_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [20, 21] Flapjack.PrimOp.addCarry [22, 23, 24]

def crepBody641_17 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 19) crepBody641_16

def crepBody641_18 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.xor
  [Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 1#64]]) crepBody641_17

def crepBody641_19 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 4) crepBody641_18

def crepBody641_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [22, 23] Flapjack.PrimOp.addCarry [24, 25, 26]

def crepBody641_21 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.var 21) crepBody641_20

def crepBody641_22 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.xor
  [Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 1#64]]) crepBody641_21

def crepBody641_23 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 5) crepBody641_22

def crepBody641_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23]

def crepBody641_25 : CrepProg (BitVec 64) :=
.seq crepBody641_23 crepBody641_24

def crepBody641_26 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody641_25

def crepBody641_27 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody641_26

def crepBody641_28 : CrepProg (BitVec 64) :=
.seq crepBody641_19 crepBody641_27

def crepBody641_29 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody641_28

def crepBody641_30 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody641_29

def crepBody641_31 : CrepProg (BitVec 64) :=
.seq crepBody641_15 crepBody641_30

def crepBody641_32 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody641_31

def crepBody641_33 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody641_32

def crepBody641_34 : CrepProg (BitVec 64) :=
.seq crepBody641_11 crepBody641_33

def crepBody641_35 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody641_34

def crepBody641_36 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody641_35

def crepBody641_37 : CrepProg (BitVec 64) :=
.seq crepBody641_7 crepBody641_36

def crepBody641_38 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody641_37

def crepBody641_39 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody641_38

def crepBody641_40 : CrepProg (BitVec 64) :=
.seq crepBody641_3 crepBody641_39

def crepBody641_41 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody641_40

def crepBody641_42 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody641_41

def data641 : CrepProg (BitVec 64) := crepBody641_42
def output641 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 115#8, 117#8, 98#8, 95#8, 114#8, 97#8, 119#8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], crepProgToHOL data641)
end InitECandidate.Proofs.FrontendStages.Crep
