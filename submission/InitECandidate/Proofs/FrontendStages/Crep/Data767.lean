import InitECandidate.Proofs.FrontendStages.Crep.Translate751
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody767_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "max" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody767_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9
  (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
    [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 8],
      Flapjack.CrepExp.var 8])

def crepBody767_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody767_3 : CrepProg (BitVec 64) :=
.seq crepBody767_1 crepBody767_2

def crepBody767_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 32#64) (Flapjack.CrepExp.var 7)) crepBody767_3 crepBody767_2

def crepBody767_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "u256_bit_length"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody767_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 11)

def crepBody767_7 : CrepProg (BitVec 64) :=
.seq crepBody767_6 crepBody767_2

def crepBody767_8 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 1#64]) crepBody767_7

def crepBody767_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 10)) crepBody767_8 crepBody767_2

def crepBody767_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 10)

def crepBody767_11 : CrepProg (BitVec 64) :=
.seq crepBody767_10 crepBody767_2

def crepBody767_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.const 16#64,
          Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.var 10])

def crepBody767_13 : CrepProg (BitVec 64) :=
.seq crepBody767_12 crepBody767_2

def crepBody767_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.const 32#64) (Flapjack.CrepExp.var 2)) crepBody767_11 crepBody767_13

def crepBody767_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.const 1#64)

def crepBody767_16 : CrepProg (BitVec 64) :=
.seq crepBody767_15 crepBody767_2

def crepBody767_17 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 1#64)) crepBody767_16 crepBody767_2

def crepBody767_18 : CrepProg (BitVec 64) :=
.seq crepBody767_14 crepBody767_17

def crepBody767_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.const 500#64)

def crepBody767_20 : CrepProg (BitVec 64) :=
.seq crepBody767_19 crepBody767_2

def crepBody767_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.const 500#64)) crepBody767_20 crepBody767_2

def crepBody767_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 12]

def crepBody767_23 : CrepProg (BitVec 64) :=
.seq crepBody767_21 crepBody767_22

def crepBody767_24 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 11]) crepBody767_23

def crepBody767_25 : CrepProg (BitVec 64) :=
.seq crepBody767_18 crepBody767_24

def crepBody767_26 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody767_25

def crepBody767_27 : CrepProg (BitVec 64) :=
.seq crepBody767_9 crepBody767_26

def crepBody767_28 : CrepProg (BitVec 64) :=
.seq crepBody767_5 crepBody767_27

def crepBody767_29 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody767_28

def crepBody767_30 : CrepProg (BitVec 64) :=
.seq crepBody767_4 crepBody767_29

def crepBody767_31 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 16#64) crepBody767_30

def crepBody767_32 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.shift Flapjack.Shift.lsr
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 7#64])
  (Flapjack.CrepExp.const 3#64)) crepBody767_31

def crepBody767_33 : CrepProg (BitVec 64) :=
.seq crepBody767_0 crepBody767_32

def crepBody767_34 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody767_33

def data767 : CrepProg (BitVec 64) := crepBody767_34
def output767 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [109#8, 111#8, 100#8, 101#8, 120#8, 112#8, 95#8, 103#8, 97#8, 115#8], [0, 1, 2, 3, 4, 5, 6], crepProgToHOL data767)
end InitECandidate.Proofs.FrontendStages.Crep
