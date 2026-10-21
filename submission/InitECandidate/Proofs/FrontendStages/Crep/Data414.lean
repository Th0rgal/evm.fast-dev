import InitECandidate.Proofs.FrontendStages.Crep.Translate398
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody414_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody414_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody414_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 0#64)) crepBody414_0 crepBody414_1

def crepBody414_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1024#64])

def crepBody414_4 : CrepProg (BitVec 64) :=
.seq crepBody414_3 crepBody414_1

def crepBody414_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 3)) crepBody414_4 crepBody414_1

def crepBody414_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "frame_mem_alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 2]]

def crepBody414_7 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody414_6

def crepBody414_8 : CrepProg (BitVec 64) :=
.seq crepBody414_5 crepBody414_7

def crepBody414_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "memzero"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 2],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 2]]

def crepBody414_10 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody414_9

def crepBody414_11 : CrepProg (BitVec 64) :=
.seq crepBody414_8 crepBody414_10

def crepBody414_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody414_13 : CrepProg (BitVec 64) :=
.seq crepBody414_12 crepBody414_1

def crepBody414_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 4) crepBody414_13

def crepBody414_15 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 40#64]) crepBody414_14

def crepBody414_16 : CrepProg (BitVec 64) :=
.seq crepBody414_11 crepBody414_15

def crepBody414_17 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 2#64]) crepBody414_16

def crepBody414_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)) crepBody414_17 crepBody414_1

def crepBody414_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "memzero"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 1],
    Flapjack.CrepExp.var 0]

def crepBody414_20 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody414_19

def crepBody414_21 : CrepProg (BitVec 64) :=
.seq crepBody414_18 crepBody414_20

def crepBody414_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 5)

def crepBody414_23 : CrepProg (BitVec 64) :=
.seq crepBody414_22 crepBody414_1

def crepBody414_24 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 3) crepBody414_23

def crepBody414_25 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 32#64]) crepBody414_24

def crepBody414_26 : CrepProg (BitVec 64) :=
.seq crepBody414_21 crepBody414_25

def crepBody414_27 : CrepProg (BitVec 64) :=
.seq crepBody414_26 crepBody414_0

def crepBody414_28 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 0]) crepBody414_27

def crepBody414_29 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 40#64])) crepBody414_28

def crepBody414_30 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 32#64])) crepBody414_29

def crepBody414_31 : CrepProg (BitVec 64) :=
.seq crepBody414_2 crepBody414_30

def data414 : CrepProg (BitVec 64) := crepBody414_31
def output414 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [101#8, 120#8, 116#8, 101#8, 110#8, 100#8, 95#8, 109#8, 101#8, 109#8, 111#8, 114#8, 121#8], [0], crepProgToHOL data414)
end InitECandidate.Proofs.FrontendStages.Crep
