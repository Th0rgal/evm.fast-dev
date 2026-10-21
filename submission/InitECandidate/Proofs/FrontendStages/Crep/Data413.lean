import InitECandidate.Proofs.FrontendStages.Crep.Translate397
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody413_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16, 17], none)) "extend_memory_cost1"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody413_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody413_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody413_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.const 18446744073709551615#64)) crepBody413_1 crepBody413_2

def crepBody413_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.var 20)

def crepBody413_5 : CrepProg (BitVec 64) :=
.seq crepBody413_4 crepBody413_2

def crepBody413_6 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 17]) crepBody413_5

def crepBody413_7 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 32#64]) crepBody413_6

def crepBody413_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19, 20], none)) "extend_memory_cost1"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15]

def crepBody413_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.var 22)

def crepBody413_10 : CrepProg (BitVec 64) :=
.seq crepBody413_9 crepBody413_2

def crepBody413_11 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 18) crepBody413_10

def crepBody413_12 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 32#64]) crepBody413_11

def crepBody413_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20]

def crepBody413_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 18446744073709551615#64)) crepBody413_13 crepBody413_2

def crepBody413_15 : CrepProg (BitVec 64) :=
.seq crepBody413_12 crepBody413_14

def crepBody413_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 19],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 20]]

def crepBody413_17 : CrepProg (BitVec 64) :=
.seq crepBody413_15 crepBody413_16

def crepBody413_18 : CrepProg (BitVec 64) :=
.seq crepBody413_8 crepBody413_17

def crepBody413_19 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody413_18

def crepBody413_20 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody413_19

def crepBody413_21 : CrepProg (BitVec 64) :=
.seq crepBody413_7 crepBody413_20

def crepBody413_22 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 32#64])) crepBody413_21

def crepBody413_23 : CrepProg (BitVec 64) :=
.seq crepBody413_3 crepBody413_22

def crepBody413_24 : CrepProg (BitVec 64) :=
.seq crepBody413_0 crepBody413_23

def crepBody413_25 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody413_24

def crepBody413_26 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody413_25

def data413 : CrepProg (BitVec 64) := crepBody413_26
def output413 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [101#8, 120#8, 116#8, 101#8, 110#8, 100#8, 95#8, 109#8, 101#8, 109#8, 111#8, 114#8, 121#8, 95#8, 99#8, 111#8, 115#8,
    116#8, 50#8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], crepProgToHOL data413)
end InitECandidate.Proofs.FrontendStages.Crep
