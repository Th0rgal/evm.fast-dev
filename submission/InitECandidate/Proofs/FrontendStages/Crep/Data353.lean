import InitECandidate.Proofs.FrontendStages.Crep.Translate337
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody353_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "htab_get" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 0]

def crepBody353_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody353_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody353_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody353_1 crepBody353_2

def crepBody353_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7, 8, 9], none)) "htab_item" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 6]

def crepBody353_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "sk_make" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8]

def crepBody353_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "htab_set"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 1#64]

def crepBody353_7 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody353_6

def crepBody353_8 : CrepProg (BitVec 64) :=
.seq crepBody353_5 crepBody353_7

def crepBody353_9 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody353_8

def crepBody353_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody353_9 crepBody353_2

def crepBody353_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 10)

def crepBody353_12 : CrepProg (BitVec 64) :=
.seq crepBody353_11 crepBody353_2

def crepBody353_13 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64]) crepBody353_12

def crepBody353_14 : CrepProg (BitVec 64) :=
.seq crepBody353_10 crepBody353_13

def crepBody353_15 : CrepProg (BitVec 64) :=
.seq crepBody353_4 crepBody353_14

def crepBody353_16 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody353_15

def crepBody353_17 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody353_16

def crepBody353_18 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody353_17

def crepBody353_19 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 5)) crepBody353_18

def crepBody353_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "jdel" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 0]

def crepBody353_21 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody353_20

def crepBody353_22 : CrepProg (BitVec 64) :=
.seq crepBody353_19 crepBody353_21

def crepBody353_23 : CrepProg (BitVec 64) :=
.seq crepBody353_22 crepBody353_1

def crepBody353_24 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody353_23

def crepBody353_25 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64])) crepBody353_24

def crepBody353_26 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 3) crepBody353_25

def crepBody353_27 : CrepProg (BitVec 64) :=
.seq crepBody353_3 crepBody353_26

def crepBody353_28 : CrepProg (BitVec 64) :=
.seq crepBody353_0 crepBody353_27

def crepBody353_29 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody353_28

def crepBody353_30 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody353_29

def crepBody353_31 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
      Flapjack.CrepExp.const 32#64])) crepBody353_30

def data353 : CrepProg (BitVec 64) := crepBody353_31
def output353 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 115#8, 116#8, 114#8, 111#8, 121#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8], [0], crepProgToHOL data353)
end InitECandidate.Proofs.FrontendStages.Crep
