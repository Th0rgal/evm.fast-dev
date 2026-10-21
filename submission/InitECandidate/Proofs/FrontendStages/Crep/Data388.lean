import InitECandidate.Proofs.FrontendStages.Crep.Translate372
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody388_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody388_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody388_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.load (Flapjack.CrepExp.var 1))
  (Flapjack.CrepExp.load (Flapjack.CrepExp.var 0))) crepBody388_0 crepBody388_1

def crepBody388_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody388_4 : CrepProg (BitVec 64) :=
.seq crepBody388_2 crepBody388_3

def crepBody388_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody388_4 crepBody388_1

def crepBody388_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.const 32#64)

def crepBody388_7 : CrepProg (BitVec 64) :=
.seq crepBody388_6 crepBody388_1

def crepBody388_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 2#64)) crepBody388_7 crepBody388_1

def crepBody388_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 5)) crepBody388_0 crepBody388_1

def crepBody388_10 : CrepProg (BitVec 64) :=
.seq crepBody388_9 crepBody388_3

def crepBody388_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)) crepBody388_10 crepBody388_1

def crepBody388_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 7)

def crepBody388_13 : CrepProg (BitVec 64) :=
.seq crepBody388_12 crepBody388_1

def crepBody388_14 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody388_13

def crepBody388_15 : CrepProg (BitVec 64) :=
.seq crepBody388_11 crepBody388_14

def crepBody388_16 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 4])) crepBody388_15

def crepBody388_17 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4])) crepBody388_16

def crepBody388_18 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 3)) crepBody388_17

def crepBody388_19 : CrepProg (BitVec 64) :=
.seq crepBody388_18 crepBody388_3

def crepBody388_20 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody388_19

def crepBody388_21 : CrepProg (BitVec 64) :=
.seq crepBody388_8 crepBody388_20

def crepBody388_22 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 20#64) crepBody388_21

def crepBody388_23 : CrepProg (BitVec 64) :=
.seq crepBody388_5 crepBody388_22

def data388 : CrepProg (BitVec 64) := crepBody388_23
def output388 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [98#8, 97#8, 108#8, 95#8, 115#8, 111#8, 114#8, 116#8, 95#8, 103#8, 116#8], [0, 1, 2], crepProgToHOL data388)
end InitECandidate.Proofs.FrontendStages.Crep
