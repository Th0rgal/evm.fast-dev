import InitECandidate.Proofs.FrontendStages.Crep.Translate523
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody539_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 4)

def crepBody539_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody539_2 : CrepProg (BitVec 64) :=
.seq crepBody539_0 crepBody539_1

def crepBody539_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 11#64) crepBody539_2

def crepBody539_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody539_5 : CrepProg (BitVec 64) :=
.seq crepBody539_3 crepBody539_4

def crepBody539_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 2))
  (Flapjack.CrepExp.const 239#64)) crepBody539_5 crepBody539_1

def crepBody539_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 3)) crepBody539_6 crepBody539_1

def crepBody539_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 4#64) crepBody539_2

def crepBody539_9 : CrepProg (BitVec 64) :=
.seq crepBody539_8 crepBody539_4

def crepBody539_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 65536#64) (Flapjack.CrepExp.var 3)) crepBody539_9 crepBody539_1

def crepBody539_11 : CrepProg (BitVec 64) :=
.seq crepBody539_7 crepBody539_10

def crepBody539_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "words_of" [Flapjack.CrepExp.var 3]

def crepBody539_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "charge_gas"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 6#64, Flapjack.CrepExp.var 4]]

def crepBody539_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody539_13

def crepBody539_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "charge_state_gas"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1530#64]]

def crepBody539_16 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody539_15

def crepBody539_17 : CrepProg (BitVec 64) :=
.seq crepBody539_14 crepBody539_16

def crepBody539_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]]

def crepBody539_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memcpy"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody539_20 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody539_19

def crepBody539_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "set_code"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 3]

def crepBody539_22 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody539_21

def crepBody539_23 : CrepProg (BitVec 64) :=
.seq crepBody539_20 crepBody539_22

def crepBody539_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody539_25 : CrepProg (BitVec 64) :=
.seq crepBody539_23 crepBody539_24

def crepBody539_26 : CrepProg (BitVec 64) :=
.seq crepBody539_18 crepBody539_25

def crepBody539_27 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody539_26

def crepBody539_28 : CrepProg (BitVec 64) :=
.seq crepBody539_17 crepBody539_27

def crepBody539_29 : CrepProg (BitVec 64) :=
.seq crepBody539_12 crepBody539_28

def crepBody539_30 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody539_29

def crepBody539_31 : CrepProg (BitVec 64) :=
.seq crepBody539_11 crepBody539_30

def crepBody539_32 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 128#64])) crepBody539_31

def crepBody539_33 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 120#64])) crepBody539_32

def data539 : CrepProg (BitVec 64) := crepBody539_33
def output539 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 95#8, 102#8, 105#8, 110#8, 105#8, 115#8, 104#8], [0, 1], crepProgToHOL data539)
end InitECandidate.Proofs.FrontendStages.Crep
