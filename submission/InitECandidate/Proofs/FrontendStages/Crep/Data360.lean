import InitECandidate.Proofs.FrontendStages.Crep.Translate344
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody360_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "get_account" [Flapjack.CrepExp.var 0]

def crepBody360_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "acct_copy" [Flapjack.CrepExp.var 5]

def crepBody360_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7, 8, 9], none)) "u256_add"
  [Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody360_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody360_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 12)

def crepBody360_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 13)

def crepBody360_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 14)

def crepBody360_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody360_8 : CrepProg (BitVec 64) :=
.seq crepBody360_6 crepBody360_7

def crepBody360_9 : CrepProg (BitVec 64) :=
.seq crepBody360_5 crepBody360_8

def crepBody360_10 : CrepProg (BitVec 64) :=
.seq crepBody360_4 crepBody360_9

def crepBody360_11 : CrepProg (BitVec 64) :=
.seq crepBody360_3 crepBody360_10

def crepBody360_12 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 9) crepBody360_11

def crepBody360_13 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 8) crepBody360_12

def crepBody360_14 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 7) crepBody360_13

def crepBody360_15 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 6) crepBody360_14

def crepBody360_16 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]) crepBody360_15

def crepBody360_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "modify_state_commit" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5]

def crepBody360_18 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody360_17

def crepBody360_19 : CrepProg (BitVec 64) :=
.seq crepBody360_16 crepBody360_18

def crepBody360_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody360_21 : CrepProg (BitVec 64) :=
.seq crepBody360_19 crepBody360_20

def crepBody360_22 : CrepProg (BitVec 64) :=
.seq crepBody360_2 crepBody360_21

def crepBody360_23 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody360_22

def crepBody360_24 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody360_23

def crepBody360_25 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody360_24

def crepBody360_26 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody360_25

def crepBody360_27 : CrepProg (BitVec 64) :=
.seq crepBody360_1 crepBody360_26

def crepBody360_28 : CrepProg (BitVec 64) :=
.seq crepBody360_0 crepBody360_27

def crepBody360_29 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody360_28

def data360 : CrepProg (BitVec 64) := crepBody360_29
def output360 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 95#8, 101#8, 116#8, 104#8, 101#8, 114#8], [0, 1, 2, 3, 4], crepProgToHOL data360)
end InitECandidate.Proofs.FrontendStages.Crep
