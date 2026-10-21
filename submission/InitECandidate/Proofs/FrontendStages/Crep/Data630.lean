import InitECandidate.Proofs.FrontendStages.Crep.Translate614
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody630_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody630_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody630_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody630_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "bn254_parse_g1" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]

def crepBody630_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody630_5 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody630_4

def crepBody630_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody630_7 : CrepProg (BitVec 64) :=
.seq crepBody630_5 crepBody630_6

def crepBody630_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody630_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody630_7 crepBody630_8

def crepBody630_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "bn254_parse_g1"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64],
    Flapjack.CrepExp.var 4]

def crepBody630_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody630_12 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody630_11

def crepBody630_13 : CrepProg (BitVec 64) :=
.seq crepBody630_12 crepBody630_6

def crepBody630_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody630_13 crepBody630_8

def crepBody630_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ecp_add"
  [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody630_16 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody630_15

def crepBody630_17 : CrepProg (BitVec 64) :=
.seq crepBody630_14 crepBody630_16

def crepBody630_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "bn254_g1_to_bytes" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 1]

def crepBody630_19 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody630_18

def crepBody630_20 : CrepProg (BitVec 64) :=
.seq crepBody630_17 crepBody630_19

def crepBody630_21 : CrepProg (BitVec 64) :=
.seq crepBody630_20 crepBody630_12

def crepBody630_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody630_23 : CrepProg (BitVec 64) :=
.seq crepBody630_21 crepBody630_22

def crepBody630_24 : CrepProg (BitVec 64) :=
.seq crepBody630_10 crepBody630_23

def crepBody630_25 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody630_24

def crepBody630_26 : CrepProg (BitVec 64) :=
.seq crepBody630_9 crepBody630_25

def crepBody630_27 : CrepProg (BitVec 64) :=
.seq crepBody630_3 crepBody630_26

def crepBody630_28 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody630_27

def crepBody630_29 : CrepProg (BitVec 64) :=
.seq crepBody630_2 crepBody630_28

def crepBody630_30 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody630_29

def crepBody630_31 : CrepProg (BitVec 64) :=
.seq crepBody630_1 crepBody630_30

def crepBody630_32 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody630_31

def crepBody630_33 : CrepProg (BitVec 64) :=
.seq crepBody630_0 crepBody630_32

def crepBody630_34 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody630_33

def data630 : CrepProg (BitVec 64) := crepBody630_34
def output630 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 110#8, 50#8, 53#8, 52#8, 95#8, 103#8, 49#8, 95#8, 97#8, 100#8, 100#8], [0, 1], crepProgToHOL data630)
end InitECandidate.Proofs.FrontendStages.Crep
