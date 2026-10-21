import InitECandidate.Proofs.FrontendStages.Crep.Translate615
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody631_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody631_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody631_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "bn254_parse_g1" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]

def crepBody631_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody631_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody631_3

def crepBody631_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody631_6 : CrepProg (BitVec 64) :=
.seq crepBody631_4 crepBody631_5

def crepBody631_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody631_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody631_6 crepBody631_7

def crepBody631_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64],
    Flapjack.CrepExp.const 32#64]

def crepBody631_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "ecp_mul"
  [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody631_11 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody631_10

def crepBody631_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "bn254_g1_to_bytes" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 1]

def crepBody631_13 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody631_12

def crepBody631_14 : CrepProg (BitVec 64) :=
.seq crepBody631_11 crepBody631_13

def crepBody631_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody631_16 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody631_15

def crepBody631_17 : CrepProg (BitVec 64) :=
.seq crepBody631_14 crepBody631_16

def crepBody631_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody631_19 : CrepProg (BitVec 64) :=
.seq crepBody631_17 crepBody631_18

def crepBody631_20 : CrepProg (BitVec 64) :=
.seq crepBody631_9 crepBody631_19

def crepBody631_21 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody631_20

def crepBody631_22 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody631_21

def crepBody631_23 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody631_22

def crepBody631_24 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody631_23

def crepBody631_25 : CrepProg (BitVec 64) :=
.seq crepBody631_8 crepBody631_24

def crepBody631_26 : CrepProg (BitVec 64) :=
.seq crepBody631_2 crepBody631_25

def crepBody631_27 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody631_26

def crepBody631_28 : CrepProg (BitVec 64) :=
.seq crepBody631_1 crepBody631_27

def crepBody631_29 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody631_28

def crepBody631_30 : CrepProg (BitVec 64) :=
.seq crepBody631_0 crepBody631_29

def crepBody631_31 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody631_30

def data631 : CrepProg (BitVec 64) := crepBody631_31
def output631 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 110#8, 50#8, 53#8, 52#8, 95#8, 103#8, 49#8, 95#8, 109#8, 117#8, 108#8], [0, 1], crepProgToHOL data631)
end InitECandidate.Proofs.FrontendStages.Crep
