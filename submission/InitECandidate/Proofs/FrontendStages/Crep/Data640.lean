import InitECandidate.Proofs.FrontendStages.Crep.Translate624
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody640_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [12, 13] Flapjack.PrimOp.addCarry [14, 15, 16]

def crepBody640_1 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody640_0

def crepBody640_2 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 6) crepBody640_1

def crepBody640_3 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 0) crepBody640_2

def crepBody640_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [14, 15] Flapjack.PrimOp.addCarry [16, 17, 18]

def crepBody640_5 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 13) crepBody640_4

def crepBody640_6 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 7) crepBody640_5

def crepBody640_7 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 1) crepBody640_6

def crepBody640_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [16, 17] Flapjack.PrimOp.addCarry [18, 19, 20]

def crepBody640_9 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 15) crepBody640_8

def crepBody640_10 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.var 8) crepBody640_9

def crepBody640_11 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 2) crepBody640_10

def crepBody640_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [18, 19] Flapjack.PrimOp.addCarry [20, 21, 22]

def crepBody640_13 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 17) crepBody640_12

def crepBody640_14 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 9) crepBody640_13

def crepBody640_15 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 3) crepBody640_14

def crepBody640_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [20, 21] Flapjack.PrimOp.addCarry [22, 23, 24]

def crepBody640_17 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 19) crepBody640_16

def crepBody640_18 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.var 10) crepBody640_17

def crepBody640_19 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 4) crepBody640_18

def crepBody640_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.primitive [22, 23] Flapjack.PrimOp.addCarry [24, 25, 26]

def crepBody640_21 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.var 21) crepBody640_20

def crepBody640_22 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.var 11) crepBody640_21

def crepBody640_23 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 5) crepBody640_22

def crepBody640_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23]

def crepBody640_25 : CrepProg (BitVec 64) :=
.seq crepBody640_23 crepBody640_24

def crepBody640_26 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody640_25

def crepBody640_27 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody640_26

def crepBody640_28 : CrepProg (BitVec 64) :=
.seq crepBody640_19 crepBody640_27

def crepBody640_29 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody640_28

def crepBody640_30 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody640_29

def crepBody640_31 : CrepProg (BitVec 64) :=
.seq crepBody640_15 crepBody640_30

def crepBody640_32 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody640_31

def crepBody640_33 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody640_32

def crepBody640_34 : CrepProg (BitVec 64) :=
.seq crepBody640_11 crepBody640_33

def crepBody640_35 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody640_34

def crepBody640_36 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody640_35

def crepBody640_37 : CrepProg (BitVec 64) :=
.seq crepBody640_7 crepBody640_36

def crepBody640_38 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody640_37

def crepBody640_39 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody640_38

def crepBody640_40 : CrepProg (BitVec 64) :=
.seq crepBody640_3 crepBody640_39

def crepBody640_41 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody640_40

def crepBody640_42 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody640_41

def data640 : CrepProg (BitVec 64) := crepBody640_42
def output640 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 97#8, 100#8, 100#8, 95#8, 114#8, 97#8, 119#8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], crepProgToHOL data640)
end InitECandidate.Proofs.FrontendStages.Crep
