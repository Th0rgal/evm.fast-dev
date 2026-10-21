import InitECandidate.Proofs.FrontendStages.Crep.Translate369
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody385_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "htab_get"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 216#64]),
    Flapjack.CrepExp.var 0]

def crepBody385_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody385_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody385_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody385_1 crepBody385_2

def crepBody385_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7], none)) "htab_get" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1]

def crepBody385_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody385_1 crepBody385_2

def crepBody385_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "bal_list_remove_idx"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 40#64, Flapjack.CrepExp.var 2]

def crepBody385_7 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody385_6

def crepBody385_8 : CrepProg (BitVec 64) :=
.seq crepBody385_5 crepBody385_7

def crepBody385_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "htab_del" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1]

def crepBody385_10 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody385_9

def crepBody385_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody385_10 crepBody385_2

def crepBody385_12 : CrepProg (BitVec 64) :=
.seq crepBody385_8 crepBody385_11

def crepBody385_13 : CrepProg (BitVec 64) :=
.seq crepBody385_12 crepBody385_1

def crepBody385_14 : CrepProg (BitVec 64) :=
.seq crepBody385_4 crepBody385_13

def crepBody385_15 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody385_14

def crepBody385_16 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody385_15

def crepBody385_17 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 0#64])) crepBody385_16

def crepBody385_18 : CrepProg (BitVec 64) :=
.seq crepBody385_3 crepBody385_17

def crepBody385_19 : CrepProg (BitVec 64) :=
.seq crepBody385_0 crepBody385_18

def crepBody385_20 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody385_19

def crepBody385_21 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody385_20

def data385 : CrepProg (BitVec 64) := crepBody385_21
def output385 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 101#8, 109#8, 111#8, 118#8, 101#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 119#8, 114#8,
    105#8, 116#8, 101#8], [0, 1, 2], crepProgToHOL data385)
end InitECandidate.Proofs.FrontendStages.Crep
