import InitECandidate.Proofs.FrontendStages.Crep.Translate245
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody261_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 128#64)

def crepBody261_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody261_2 : CrepProg (BitVec 64) :=
.seq crepBody261_0 crepBody261_1

def crepBody261_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody261_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 0#64)) crepBody261_2 crepBody261_3

def crepBody261_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 160#64)

def crepBody261_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody261_7 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody261_6

def crepBody261_8 : CrepProg (BitVec 64) :=
.seq crepBody261_5 crepBody261_7

def crepBody261_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 33#64]

def crepBody261_10 : CrepProg (BitVec 64) :=
.seq crepBody261_8 crepBody261_9

def crepBody261_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody261_10 crepBody261_3

def crepBody261_12 : CrepProg (BitVec 64) :=
.seq crepBody261_4 crepBody261_11

def crepBody261_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "mpt_fail" [Flapjack.CrepExp.const 13#64]

def crepBody261_14 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody261_13

def crepBody261_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody261_14 crepBody261_3

def crepBody261_16 : CrepProg (BitVec 64) :=
.seq crepBody261_12 crepBody261_15

def crepBody261_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "memcpy"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody261_18 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody261_17

def crepBody261_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody261_20 : CrepProg (BitVec 64) :=
.seq crepBody261_18 crepBody261_19

def crepBody261_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 32#64)) crepBody261_20 crepBody261_3

def crepBody261_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "node_hash_cached" [Flapjack.CrepExp.var 0]

def crepBody261_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64], Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.const 32#64]

def crepBody261_24 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody261_23

def crepBody261_25 : CrepProg (BitVec 64) :=
.seq crepBody261_5 crepBody261_24

def crepBody261_26 : CrepProg (BitVec 64) :=
.seq crepBody261_25 crepBody261_9

def crepBody261_27 : CrepProg (BitVec 64) :=
.seq crepBody261_22 crepBody261_26

def crepBody261_28 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody261_27

def crepBody261_29 : CrepProg (BitVec 64) :=
.seq crepBody261_21 crepBody261_28

def crepBody261_30 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64])) crepBody261_29

def crepBody261_31 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64])) crepBody261_30

def crepBody261_32 : CrepProg (BitVec 64) :=
.seq crepBody261_16 crepBody261_31

def data261 : CrepProg (BitVec 64) := crepBody261_32
def output261 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [110#8, 111#8, 100#8, 101#8, 95#8, 119#8, 114#8, 105#8, 116#8, 101#8, 95#8, 114#8, 101#8, 102#8], [0, 1], crepProgToHOL data261)
end InitECandidate.Proofs.FrontendStages.Crep
