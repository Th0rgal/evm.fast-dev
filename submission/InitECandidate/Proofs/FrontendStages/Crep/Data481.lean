import InitECandidate.Proofs.FrontendStages.Crep.Translate465
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody481_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody481_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "u256_to_be32"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5]

def crepBody481_2 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody481_1

def crepBody481_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "is_warm_storage_key" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]

def crepBody481_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "charge_gas" [Flapjack.CrepExp.const 100#64]

def crepBody481_5 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody481_4

def crepBody481_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "charge_gas" [Flapjack.CrepExp.const 2100#64]

def crepBody481_7 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody481_6

def crepBody481_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "warm_storage_key" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]

def crepBody481_9 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody481_8

def crepBody481_10 : CrepProg (BitVec 64) :=
.seq crepBody481_7 crepBody481_9

def crepBody481_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody481_5 crepBody481_10

def crepBody481_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9, 10, 11], none)) "get_storage" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]

def crepBody481_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "stack_push"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11]

def crepBody481_14 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody481_13

def crepBody481_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody481_16 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody481_15

def crepBody481_17 : CrepProg (BitVec 64) :=
.seq crepBody481_14 crepBody481_16

def crepBody481_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody481_19 : CrepProg (BitVec 64) :=
.seq crepBody481_17 crepBody481_18

def crepBody481_20 : CrepProg (BitVec 64) :=
.seq crepBody481_12 crepBody481_19

def crepBody481_21 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody481_20

def crepBody481_22 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody481_21

def crepBody481_23 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody481_22

def crepBody481_24 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody481_23

def crepBody481_25 : CrepProg (BitVec 64) :=
.seq crepBody481_11 crepBody481_24

def crepBody481_26 : CrepProg (BitVec 64) :=
.seq crepBody481_3 crepBody481_25

def crepBody481_27 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody481_26

def crepBody481_28 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.load
              (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
            Flapjack.CrepExp.const 112#64]),
      Flapjack.CrepExp.const 32#64])) crepBody481_27

def crepBody481_29 : CrepProg (BitVec 64) :=
.seq crepBody481_2 crepBody481_28

def crepBody481_30 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 280#64])) crepBody481_29

def crepBody481_31 : CrepProg (BitVec 64) :=
.seq crepBody481_0 crepBody481_30

def crepBody481_32 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody481_31

def crepBody481_33 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody481_32

def crepBody481_34 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody481_33

def crepBody481_35 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody481_34

def data481 : CrepProg (BitVec 64) := crepBody481_35
def output481 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 108#8, 111#8, 97#8, 100#8], [], crepProgToHOL data481)
end InitECandidate.Proofs.FrontendStages.Crep
