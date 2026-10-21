import InitECandidate.Proofs.FrontendStages.Crep.Translate347
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody363_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody363_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "keccak256"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody363_2 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody363_1

def crepBody363_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "memeq"
  [Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 136#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody363_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 16#64]

def crepBody363_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody363_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody363_7 : CrepProg (BitVec 64) :=
.seq crepBody363_5 crepBody363_6

def crepBody363_8 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 1) crepBody363_7

def crepBody363_9 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 5) crepBody363_8

def crepBody363_10 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 2) crepBody363_7

def crepBody363_11 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]) crepBody363_10

def crepBody363_12 : CrepProg (BitVec 64) :=
.seq crepBody363_9 crepBody363_11

def crepBody363_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "jset"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 5]

def crepBody363_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody363_13

def crepBody363_15 : CrepProg (BitVec 64) :=
.seq crepBody363_12 crepBody363_14

def crepBody363_16 : CrepProg (BitVec 64) :=
.seq crepBody363_4 crepBody363_15

def crepBody363_17 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody363_16

def crepBody363_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody363_17 crepBody363_6

def crepBody363_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "get_account" [Flapjack.CrepExp.var 0]

def crepBody363_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "acct_copy" [Flapjack.CrepExp.var 5]

def crepBody363_21 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 3) crepBody363_7

def crepBody363_22 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 48#64]) crepBody363_21

def crepBody363_23 : CrepProg (BitVec 64) :=
.seq crepBody363_20 crepBody363_22

def crepBody363_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "modify_state_commit" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5]

def crepBody363_25 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody363_24

def crepBody363_26 : CrepProg (BitVec 64) :=
.seq crepBody363_23 crepBody363_25

def crepBody363_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody363_28 : CrepProg (BitVec 64) :=
.seq crepBody363_26 crepBody363_27

def crepBody363_29 : CrepProg (BitVec 64) :=
.seq crepBody363_19 crepBody363_28

def crepBody363_30 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody363_29

def crepBody363_31 : CrepProg (BitVec 64) :=
.seq crepBody363_18 crepBody363_30

def crepBody363_32 : CrepProg (BitVec 64) :=
.seq crepBody363_3 crepBody363_31

def crepBody363_33 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody363_32

def crepBody363_34 : CrepProg (BitVec 64) :=
.seq crepBody363_2 crepBody363_33

def crepBody363_35 : CrepProg (BitVec 64) :=
.seq crepBody363_0 crepBody363_34

def crepBody363_36 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody363_35

def data363 : CrepProg (BitVec 64) := crepBody363_36
def output363 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [115#8, 101#8, 116#8, 95#8, 99#8, 111#8, 100#8, 101#8], [0, 1, 2], crepProgToHOL data363)
end InitECandidate.Proofs.FrontendStages.Crep
