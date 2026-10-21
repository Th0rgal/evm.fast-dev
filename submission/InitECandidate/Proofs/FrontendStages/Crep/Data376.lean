import InitECandidate.Proofs.FrontendStages.Crep.Translate360
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody376_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "bal_ensure_account" [Flapjack.CrepExp.var 0]

def crepBody376_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody376_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody376_3 : CrepProg (BitVec 64) :=
.seq crepBody376_1 crepBody376_2

def crepBody376_4 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 2) crepBody376_3

def crepBody376_5 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 16#64],
    Flapjack.CrepExp.const 8#64]) crepBody376_4

def crepBody376_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 16#64],
        Flapjack.CrepExp.const 8#64]))
  (Flapjack.CrepExp.var 2)) crepBody376_5 crepBody376_2

def crepBody376_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody376_8 : CrepProg (BitVec 64) :=
.seq crepBody376_6 crepBody376_7

def crepBody376_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 16#64]]))
  (Flapjack.CrepExp.var 1)) crepBody376_8 crepBody376_2

def crepBody376_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 8)

def crepBody376_11 : CrepProg (BitVec 64) :=
.seq crepBody376_10 crepBody376_2

def crepBody376_12 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64]) crepBody376_11

def crepBody376_13 : CrepProg (BitVec 64) :=
.seq crepBody376_9 crepBody376_12

def crepBody376_14 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 5)) crepBody376_13

def crepBody376_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "lst_push" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]

def crepBody376_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody376_17 : CrepProg (BitVec 64) :=
.seq crepBody376_16 crepBody376_2

def crepBody376_18 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 1) crepBody376_17

def crepBody376_19 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 8) crepBody376_18

def crepBody376_20 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 2) crepBody376_17

def crepBody376_21 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]) crepBody376_20

def crepBody376_22 : CrepProg (BitVec 64) :=
.seq crepBody376_19 crepBody376_21

def crepBody376_23 : CrepProg (BitVec 64) :=
.seq crepBody376_22 crepBody376_7

def crepBody376_24 : CrepProg (BitVec 64) :=
.seq crepBody376_15 crepBody376_23

def crepBody376_25 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody376_24

def crepBody376_26 : CrepProg (BitVec 64) :=
.seq crepBody376_14 crepBody376_25

def crepBody376_27 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody376_26

def crepBody376_28 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 0#64])) crepBody376_27

def crepBody376_29 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64])) crepBody376_28

def crepBody376_30 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64])) crepBody376_29

def crepBody376_31 : CrepProg (BitVec 64) :=
.seq crepBody376_0 crepBody376_30

def crepBody376_32 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody376_31

def data376 : CrepProg (BitVec 64) := crepBody376_32
def output376 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [97#8, 100#8, 100#8, 95#8, 110#8, 111#8, 110#8, 99#8, 101#8, 95#8, 99#8, 104#8, 97#8, 110#8, 103#8, 101#8], [0, 1, 2], crepProgToHOL data376)
end InitECandidate.Proofs.FrontendStages.Crep
