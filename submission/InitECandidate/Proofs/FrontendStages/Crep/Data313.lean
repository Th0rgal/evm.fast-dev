import InitECandidate.Proofs.FrontendStages.Crep.Translate297
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody313_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "tx_chain_id" [Flapjack.CrepExp.var 0]

def crepBody313_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_mark" []

def crepBody313_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 72#64]

def crepBody313_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 4#64)

def crepBody313_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "recover_transaction_public_key"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]]

def crepBody313_5 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody313_4

def crepBody313_6 : CrepProg (BitVec 64) :=
.seq crepBody313_3 crepBody313_5

def crepBody313_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "sender_address_from_public_key"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1]

def crepBody313_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody313_7

def crepBody313_9 : CrepProg (BitVec 64) :=
.seq crepBody313_6 crepBody313_8

def crepBody313_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 4]

def crepBody313_11 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody313_10

def crepBody313_12 : CrepProg (BitVec 64) :=
.seq crepBody313_9 crepBody313_11

def crepBody313_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody313_14 : CrepProg (BitVec 64) :=
.seq crepBody313_12 crepBody313_13

def crepBody313_15 : CrepProg (BitVec 64) :=
.seq crepBody313_2 crepBody313_14

def crepBody313_16 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody313_15

def crepBody313_17 : CrepProg (BitVec 64) :=
.seq crepBody313_1 crepBody313_16

def crepBody313_18 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody313_17

def crepBody313_19 : CrepProg (BitVec 64) :=
.seq crepBody313_0 crepBody313_18

def crepBody313_20 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody313_19

def crepBody313_21 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody313_20

def data313 : CrepProg (BitVec 64) := crepBody313_21
def output313 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8, 95#8, 115#8, 101#8, 110#8, 100#8, 101#8, 114#8], [0, 1], crepProgToHOL data313)
end InitECandidate.Proofs.FrontendStages.Crep
