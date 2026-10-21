import InitECandidate.Proofs.FrontendStages.Crep.Translate531
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody547_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_mark" []

def crepBody547_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody547_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 255#64)

def crepBody547_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64], Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.const 20#64]

def crepBody547_4 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody547_3

def crepBody547_5 : CrepProg (BitVec 64) :=
.seq crepBody547_2 crepBody547_4

def crepBody547_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 21#64],
    Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]

def crepBody547_7 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody547_6

def crepBody547_8 : CrepProg (BitVec 64) :=
.seq crepBody547_5 crepBody547_7

def crepBody547_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "keccak256"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 53#64]]

def crepBody547_10 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody547_9

def crepBody547_11 : CrepProg (BitVec 64) :=
.seq crepBody547_8 crepBody547_10

def crepBody547_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody547_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "keccak256"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 85#64, Flapjack.CrepExp.var 7]

def crepBody547_14 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody547_13

def crepBody547_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "memcpy"
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 12#64],
    Flapjack.CrepExp.const 20#64]

def crepBody547_16 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody547_15

def crepBody547_17 : CrepProg (BitVec 64) :=
.seq crepBody547_14 crepBody547_16

def crepBody547_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "heap_release" [Flapjack.CrepExp.var 5]

def crepBody547_19 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody547_18

def crepBody547_20 : CrepProg (BitVec 64) :=
.seq crepBody547_17 crepBody547_19

def crepBody547_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody547_22 : CrepProg (BitVec 64) :=
.seq crepBody547_20 crepBody547_21

def crepBody547_23 : CrepProg (BitVec 64) :=
.seq crepBody547_12 crepBody547_22

def crepBody547_24 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody547_23

def crepBody547_25 : CrepProg (BitVec 64) :=
.seq crepBody547_11 crepBody547_24

def crepBody547_26 : CrepProg (BitVec 64) :=
.seq crepBody547_1 crepBody547_25

def crepBody547_27 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody547_26

def crepBody547_28 : CrepProg (BitVec 64) :=
.seq crepBody547_0 crepBody547_27

def crepBody547_29 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody547_28

def data547 : CrepProg (BitVec 64) := crepBody547_29
def output547 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 111#8, 109#8, 112#8, 117#8, 116#8, 101#8, 95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 50#8, 95#8, 99#8,
    111#8, 110#8, 116#8, 114#8, 97#8, 99#8, 116#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8], [0, 1, 2, 3, 4], crepProgToHOL data547)
end InitECandidate.Proofs.FrontendStages.Crep
