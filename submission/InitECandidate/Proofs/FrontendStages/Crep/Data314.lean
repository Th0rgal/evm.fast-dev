import InitECandidate.Proofs.FrontendStages.Crep.Translate298
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody314_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody314_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 72#64]

def crepBody314_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 4#64)

def crepBody314_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "recover_transaction_public_key"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]]

def crepBody314_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody314_3

def crepBody314_5 : CrepProg (BitVec 64) :=
.seq crepBody314_2 crepBody314_4

def crepBody314_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "sender_address_from_public_key"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 2]

def crepBody314_7 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody314_6

def crepBody314_8 : CrepProg (BitVec 64) :=
.seq crepBody314_5 crepBody314_7

def crepBody314_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody314_10 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody314_9

def crepBody314_11 : CrepProg (BitVec 64) :=
.seq crepBody314_8 crepBody314_10

def crepBody314_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody314_13 : CrepProg (BitVec 64) :=
.seq crepBody314_11 crepBody314_12

def crepBody314_14 : CrepProg (BitVec 64) :=
.seq crepBody314_1 crepBody314_13

def crepBody314_15 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody314_14

def crepBody314_16 : CrepProg (BitVec 64) :=
.seq crepBody314_0 crepBody314_15

def crepBody314_17 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody314_16

def data314 : CrepProg (BitVec 64) := crepBody314_17
def output314 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8, 95#8, 115#8, 101#8, 110#8, 100#8, 101#8, 114#8, 95#8, 119#8, 105#8,
    116#8, 104#8, 95#8, 99#8, 104#8, 97#8, 105#8, 110#8, 95#8, 105#8, 100#8], [0, 1, 2], crepProgToHOL data314)
end InitECandidate.Proofs.FrontendStages.Crep
