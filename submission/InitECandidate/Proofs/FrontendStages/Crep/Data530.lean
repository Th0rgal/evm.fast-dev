import InitECandidate.Proofs.FrontendStages.Crep.Translate514
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody530_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody530_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "move_ether"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody530_2 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody530_1

def crepBody530_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "memeq"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.const 20#64]

def crepBody530_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "emit_transfer_log"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody530_5 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody530_4

def crepBody530_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody530_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody530_5 crepBody530_6

def crepBody530_8 : CrepProg (BitVec 64) :=
.seq crepBody530_3 crepBody530_7

def crepBody530_9 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody530_8

def crepBody530_10 : CrepProg (BitVec 64) :=
.seq crepBody530_2 crepBody530_9

def crepBody530_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody530_10 crepBody530_6

def crepBody530_12 : CrepProg (BitVec 64) :=
.seq crepBody530_0 crepBody530_11

def crepBody530_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody530_12

def crepBody530_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64],
      Flapjack.CrepExp.const 24#64])) crepBody530_13

def crepBody530_15 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64],
      Flapjack.CrepExp.const 16#64])) crepBody530_14

def crepBody530_16 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64],
      Flapjack.CrepExp.const 8#64])) crepBody530_15

def crepBody530_17 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64])) crepBody530_16

def crepBody530_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 136#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody530_17 crepBody530_6

def crepBody530_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "precompile_index" [Flapjack.CrepExp.var 2]

def crepBody530_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "run_precompile" [Flapjack.CrepExp.var 3]

def crepBody530_21 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody530_20

def crepBody530_22 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 168#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody530_21 crepBody530_6

def crepBody530_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody530_24 : CrepProg (BitVec 64) :=
.seq crepBody530_22 crepBody530_23

def crepBody530_25 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody530_24 crepBody530_6

def crepBody530_26 : CrepProg (BitVec 64) :=
.seq crepBody530_19 crepBody530_25

def crepBody530_27 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody530_26

def crepBody530_28 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody530_27 crepBody530_6

def crepBody530_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody530_30 : CrepProg (BitVec 64) :=
.seq crepBody530_28 crepBody530_29

def crepBody530_31 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 104#64])) crepBody530_30

def crepBody530_32 : CrepProg (BitVec 64) :=
.seq crepBody530_18 crepBody530_31

def crepBody530_33 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody530_32

def data530 : CrepProg (BitVec 64) := crepBody530_33
def output530 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 112#8, 114#8, 111#8, 108#8, 111#8, 103#8, 117#8, 101#8], [], crepProgToHOL data530)
end InitECandidate.Proofs.FrontendStages.Crep
