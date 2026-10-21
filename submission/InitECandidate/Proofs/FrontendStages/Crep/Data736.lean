import InitECandidate.Proofs.FrontendStages.Crep.Translate720
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody736_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody736_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody736_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "swu_g2" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 1]

def crepBody736_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody736_2

def crepBody736_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "iso_map_g2" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 3]

def crepBody736_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody736_4

def crepBody736_6 : CrepProg (BitVec 64) :=
.seq crepBody736_3 crepBody736_5

def crepBody736_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "g2_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 1632#64],
    Flapjack.CrepExp.const 10#64]

def crepBody736_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody736_7

def crepBody736_9 : CrepProg (BitVec 64) :=
.seq crepBody736_6 crepBody736_8

def crepBody736_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody736_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody736_10

def crepBody736_12 : CrepProg (BitVec 64) :=
.seq crepBody736_9 crepBody736_11

def crepBody736_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody736_14 : CrepProg (BitVec 64) :=
.seq crepBody736_12 crepBody736_13

def crepBody736_15 : CrepProg (BitVec 64) :=
.seq crepBody736_1 crepBody736_14

def crepBody736_16 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody736_15

def crepBody736_17 : CrepProg (BitVec 64) :=
.seq crepBody736_0 crepBody736_16

def crepBody736_18 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody736_17

def data736 : CrepProg (BitVec 64) := crepBody736_18
def output736 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [109#8, 97#8, 112#8, 95#8, 102#8, 112#8, 50#8, 95#8, 116#8, 111#8, 95#8, 103#8, 50#8], [0, 1], crepProgToHOL data736)
end InitECandidate.Proofs.FrontendStages.Crep
