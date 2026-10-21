import InitECandidate.Proofs.FrontendStages.Crep.Translate186
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody202_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "hdr_uint_field"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64]

def crepBody202_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 4)

def crepBody202_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody202_3 : CrepProg (BitVec 64) :=
.seq crepBody202_1 crepBody202_2

def crepBody202_4 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 4#64) crepBody202_3

def crepBody202_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 3#64

def crepBody202_6 : CrepProg (BitVec 64) :=
.seq crepBody202_4 crepBody202_5

def crepBody202_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 8#64) (Flapjack.CrepExp.var 3)) crepBody202_6 crepBody202_2

def crepBody202_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 6)

def crepBody202_9 : CrepProg (BitVec 64) :=
.seq crepBody202_8 crepBody202_2

def crepBody202_10 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.loadByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 5])]) crepBody202_9

def crepBody202_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 6)

def crepBody202_12 : CrepProg (BitVec 64) :=
.seq crepBody202_11 crepBody202_2

def crepBody202_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody202_12

def crepBody202_14 : CrepProg (BitVec 64) :=
.seq crepBody202_10 crepBody202_13

def crepBody202_15 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 3)) crepBody202_14

def crepBody202_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody202_17 : CrepProg (BitVec 64) :=
.seq crepBody202_15 crepBody202_16

def crepBody202_18 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody202_17

def crepBody202_19 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody202_18

def crepBody202_20 : CrepProg (BitVec 64) :=
.seq crepBody202_7 crepBody202_19

def crepBody202_21 : CrepProg (BitVec 64) :=
.seq crepBody202_0 crepBody202_20

def crepBody202_22 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody202_21

def crepBody202_23 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody202_22

def data202 : CrepProg (BitVec 64) := crepBody202_23
def output202 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [104#8, 100#8, 114#8, 95#8, 119#8, 111#8, 114#8, 100#8, 95#8, 102#8, 105#8, 101#8, 108#8, 100#8], [0, 1], crepProgToHOL data202)
end InitECandidate.Proofs.FrontendStages.Crep
