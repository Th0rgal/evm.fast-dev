import InitECandidate.Proofs.FrontendStages.Crep.Translate586
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody602_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12, 13, 14, 15], none)) "fq_mul"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11]

def crepBody602_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.var 17)

def crepBody602_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 18)

def crepBody602_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 19)

def crepBody602_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 20)

def crepBody602_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody602_6 : CrepProg (BitVec 64) :=
.seq crepBody602_4 crepBody602_5

def crepBody602_7 : CrepProg (BitVec 64) :=
.seq crepBody602_3 crepBody602_6

def crepBody602_8 : CrepProg (BitVec 64) :=
.seq crepBody602_2 crepBody602_7

def crepBody602_9 : CrepProg (BitVec 64) :=
.seq crepBody602_1 crepBody602_8

def crepBody602_10 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 15) crepBody602_9

def crepBody602_11 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.var 14) crepBody602_10

def crepBody602_12 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 13) crepBody602_11

def crepBody602_13 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 12) crepBody602_12

def crepBody602_14 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 1) crepBody602_13

def crepBody602_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody602_16 : CrepProg (BitVec 64) :=
.seq crepBody602_14 crepBody602_15

def crepBody602_17 : CrepProg (BitVec 64) :=
.seq crepBody602_0 crepBody602_16

def crepBody602_18 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody602_17

def crepBody602_19 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody602_18

def crepBody602_20 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody602_19

def crepBody602_21 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody602_20

def crepBody602_22 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64])) crepBody602_21

def crepBody602_23 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64])) crepBody602_22

def crepBody602_24 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64])) crepBody602_23

def crepBody602_25 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 3)) crepBody602_24

def crepBody602_26 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 24#64])) crepBody602_25

def crepBody602_27 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64])) crepBody602_26

def crepBody602_28 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64])) crepBody602_27

def crepBody602_29 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 2)) crepBody602_28

def crepBody602_30 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 1#64)) crepBody602_29 crepBody602_5

def crepBody602_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "fq2_mul"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody602_32 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody602_31

def crepBody602_33 : CrepProg (BitVec 64) :=
.seq crepBody602_32 crepBody602_15

def crepBody602_34 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 2#64)) crepBody602_33 crepBody602_5

def crepBody602_35 : CrepProg (BitVec 64) :=
.seq crepBody602_30 crepBody602_34

def crepBody602_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "fq12_mul"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody602_37 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody602_36

def crepBody602_38 : CrepProg (BitVec 64) :=
.seq crepBody602_35 crepBody602_37

def crepBody602_39 : CrepProg (BitVec 64) :=
.seq crepBody602_38 crepBody602_15

def data602 : CrepProg (BitVec 64) := crepBody602_39
def output602 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 109#8, 117#8, 108#8], [0, 1, 2, 3], crepProgToHOL data602)
end InitECandidate.Proofs.FrontendStages.Crep
