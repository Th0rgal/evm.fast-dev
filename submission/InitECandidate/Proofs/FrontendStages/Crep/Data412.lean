import InitECandidate.Proofs.FrontendStages.Crep.Translate396
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody412_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody412_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody412_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody412_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody412_1 crepBody412_2

def crepBody412_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "sat_word"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody412_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "sat_word"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody412_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "add_sat" [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10]

def crepBody412_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 18446744073709551615#64, Flapjack.CrepExp.const 0#64]

def crepBody412_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 18446744073709551615#64)) crepBody412_7 crepBody412_2

def crepBody412_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "ceil32" [Flapjack.CrepExp.var 12]

def crepBody412_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "ceil32" [Flapjack.CrepExp.var 11]

def crepBody412_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)) crepBody412_1 crepBody412_2

def crepBody412_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "memory_gas_cost" [Flapjack.CrepExp.var 14]

def crepBody412_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "memory_gas_cost" [Flapjack.CrepExp.var 13]

def crepBody412_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.const 18446744073709551615#64)) crepBody412_7 crepBody412_2

def crepBody412_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 13]]

def crepBody412_16 : CrepProg (BitVec 64) :=
.seq crepBody412_14 crepBody412_15

def crepBody412_17 : CrepProg (BitVec 64) :=
.seq crepBody412_13 crepBody412_16

def crepBody412_18 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody412_17

def crepBody412_19 : CrepProg (BitVec 64) :=
.seq crepBody412_12 crepBody412_18

def crepBody412_20 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody412_19

def crepBody412_21 : CrepProg (BitVec 64) :=
.seq crepBody412_11 crepBody412_20

def crepBody412_22 : CrepProg (BitVec 64) :=
.seq crepBody412_10 crepBody412_21

def crepBody412_23 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody412_22

def crepBody412_24 : CrepProg (BitVec 64) :=
.seq crepBody412_9 crepBody412_23

def crepBody412_25 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody412_24

def crepBody412_26 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 32#64])) crepBody412_25

def crepBody412_27 : CrepProg (BitVec 64) :=
.seq crepBody412_8 crepBody412_26

def crepBody412_28 : CrepProg (BitVec 64) :=
.seq crepBody412_6 crepBody412_27

def crepBody412_29 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody412_28

def crepBody412_30 : CrepProg (BitVec 64) :=
.seq crepBody412_5 crepBody412_29

def crepBody412_31 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody412_30

def crepBody412_32 : CrepProg (BitVec 64) :=
.seq crepBody412_4 crepBody412_31

def crepBody412_33 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody412_32

def crepBody412_34 : CrepProg (BitVec 64) :=
.seq crepBody412_3 crepBody412_33

def crepBody412_35 : CrepProg (BitVec 64) :=
.seq crepBody412_0 crepBody412_34

def crepBody412_36 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody412_35

def data412 : CrepProg (BitVec 64) := crepBody412_36
def output412 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [101#8, 120#8, 116#8, 101#8, 110#8, 100#8, 95#8, 109#8, 101#8, 109#8, 111#8, 114#8, 121#8, 95#8, 99#8, 111#8, 115#8,
    116#8, 49#8], [0, 1, 2, 3, 4, 5, 6, 7], crepProgToHOL data412)
end InitECandidate.Proofs.FrontendStages.Crep
