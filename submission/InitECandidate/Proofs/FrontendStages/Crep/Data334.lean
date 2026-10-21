import InitECandidate.Proofs.FrontendStages.Crep.Translate318
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody334_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "memeq"
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 136#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody334_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody334_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody334_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody334_1 crepBody334_2

def crepBody334_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3, 4], none)) "nodedb_lookup"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64]),
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.var 0]

def crepBody334_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody334_6 : CrepProg (BitVec 64) :=
.seq crepBody334_5 crepBody334_2

def crepBody334_7 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 2#64) crepBody334_6

def crepBody334_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 7#64

def crepBody334_9 : CrepProg (BitVec 64) :=
.seq crepBody334_7 crepBody334_8

def crepBody334_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody334_9 crepBody334_2

def crepBody334_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody334_12 : CrepProg (BitVec 64) :=
.seq crepBody334_10 crepBody334_11

def crepBody334_13 : CrepProg (BitVec 64) :=
.seq crepBody334_4 crepBody334_12

def crepBody334_14 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody334_13

def crepBody334_15 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody334_14

def crepBody334_16 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody334_15

def crepBody334_17 : CrepProg (BitVec 64) :=
.seq crepBody334_3 crepBody334_16

def crepBody334_18 : CrepProg (BitVec 64) :=
.seq crepBody334_0 crepBody334_17

def crepBody334_19 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody334_18

def data334 : CrepProg (BitVec 64) := crepBody334_19
def output334 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [119#8, 115#8, 95#8, 103#8, 101#8, 116#8, 95#8, 99#8, 111#8, 100#8, 101#8], [0], crepProgToHOL data334)
end InitECandidate.Proofs.FrontendStages.Crep
