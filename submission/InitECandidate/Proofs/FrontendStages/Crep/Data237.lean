import InitECandidate.Proofs.FrontendStages.Crep.Translate221
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody237_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memeq"
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 128#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody237_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody237_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody237_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody237_1 crepBody237_2

def crepBody237_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4, 5], none)) "nodedb_lookup" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody237_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "mpt_fail" [Flapjack.CrepExp.const 1#64]

def crepBody237_6 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody237_5

def crepBody237_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody237_6 crepBody237_2

def crepBody237_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "_decode_witness_node"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody237_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody237_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "memcpy"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]

def crepBody237_11 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody237_10

def crepBody237_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody237_13 : CrepProg (BitVec 64) :=
.seq crepBody237_12 crepBody237_2

def crepBody237_14 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 7) crepBody237_13

def crepBody237_15 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 24#64]) crepBody237_14

def crepBody237_16 : CrepProg (BitVec 64) :=
.seq crepBody237_11 crepBody237_15

def crepBody237_17 : CrepProg (BitVec 64) :=
.seq crepBody237_9 crepBody237_16

def crepBody237_18 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody237_17

def crepBody237_19 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody237_18 crepBody237_2

def crepBody237_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 6]

def crepBody237_21 : CrepProg (BitVec 64) :=
.seq crepBody237_19 crepBody237_20

def crepBody237_22 : CrepProg (BitVec 64) :=
.seq crepBody237_8 crepBody237_21

def crepBody237_23 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody237_22

def crepBody237_24 : CrepProg (BitVec 64) :=
.seq crepBody237_7 crepBody237_23

def crepBody237_25 : CrepProg (BitVec 64) :=
.seq crepBody237_4 crepBody237_24

def crepBody237_26 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody237_25

def crepBody237_27 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody237_26

def crepBody237_28 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody237_27

def crepBody237_29 : CrepProg (BitVec 64) :=
.seq crepBody237_3 crepBody237_28

def crepBody237_30 : CrepProg (BitVec 64) :=
.seq crepBody237_0 crepBody237_29

def crepBody237_31 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody237_30

def data237 : CrepProg (BitVec 64) := crepBody237_31
def output237 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 119#8, 105#8, 116#8, 110#8, 101#8, 115#8, 115#8, 95#8, 116#8, 111#8,
    95#8, 109#8, 112#8, 116#8], [0, 1], crepProgToHOL data237)
end InitECandidate.Proofs.FrontendStages.Crep
