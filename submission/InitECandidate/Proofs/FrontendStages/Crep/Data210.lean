import InitECandidate.Proofs.FrontendStages.Crep.Translate194
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody210_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 2)

def crepBody210_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody210_2 : CrepProg (BitVec 64) :=
.seq crepBody210_0 crepBody210_1

def crepBody210_3 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 1#64) crepBody210_2

def crepBody210_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 4#64

def crepBody210_5 : CrepProg (BitVec 64) :=
.seq crepBody210_3 crepBody210_4

def crepBody210_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 256#64) (Flapjack.CrepExp.var 1)) crepBody210_5 crepBody210_1

def crepBody210_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64],
        Flapjack.CrepExp.const 8#64]]

def crepBody210_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64],
        Flapjack.CrepExp.const 32#64]]

def crepBody210_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "decode_header"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody210_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody210_11 : CrepProg (BitVec 64) :=
.seq crepBody210_10 crepBody210_1

def crepBody210_12 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 5) crepBody210_11

def crepBody210_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64]]) crepBody210_12

def crepBody210_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "keccak256"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 3,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64]]]

def crepBody210_15 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody210_14

def crepBody210_16 : CrepProg (BitVec 64) :=
.seq crepBody210_13 crepBody210_15

def crepBody210_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 6)

def crepBody210_18 : CrepProg (BitVec 64) :=
.seq crepBody210_17 crepBody210_1

def crepBody210_19 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody210_18

def crepBody210_20 : CrepProg (BitVec 64) :=
.seq crepBody210_16 crepBody210_19

def crepBody210_21 : CrepProg (BitVec 64) :=
.seq crepBody210_9 crepBody210_20

def crepBody210_22 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody210_21

def crepBody210_23 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 1)) crepBody210_22

def crepBody210_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.const 1#64)

def crepBody210_25 : CrepProg (BitVec 64) :=
.seq crepBody210_24 crepBody210_1

def crepBody210_26 : CrepProg (BitVec 64) :=
.seq crepBody210_23 crepBody210_25

def crepBody210_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "memeq"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 2,
                Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64]]),
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 3,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
          [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64],
            Flapjack.CrepExp.const 32#64]],
    Flapjack.CrepExp.const 32#64]

def crepBody210_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 6)

def crepBody210_29 : CrepProg (BitVec 64) :=
.seq crepBody210_28 crepBody210_1

def crepBody210_30 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 2#64) crepBody210_29

def crepBody210_31 : CrepProg (BitVec 64) :=
.seq crepBody210_30 crepBody210_4

def crepBody210_32 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody210_31 crepBody210_1

def crepBody210_33 : CrepProg (BitVec 64) :=
.seq crepBody210_32 crepBody210_19

def crepBody210_34 : CrepProg (BitVec 64) :=
.seq crepBody210_27 crepBody210_33

def crepBody210_35 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody210_34

def crepBody210_36 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 1)) crepBody210_35

def crepBody210_37 : CrepProg (BitVec 64) :=
.seq crepBody210_26 crepBody210_36

def crepBody210_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody210_39 : CrepProg (BitVec 64) :=
.seq crepBody210_37 crepBody210_38

def crepBody210_40 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody210_39

def crepBody210_41 : CrepProg (BitVec 64) :=
.seq crepBody210_8 crepBody210_40

def crepBody210_42 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody210_41

def crepBody210_43 : CrepProg (BitVec 64) :=
.seq crepBody210_7 crepBody210_42

def crepBody210_44 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody210_43

def crepBody210_45 : CrepProg (BitVec 64) :=
.seq crepBody210_6 crepBody210_44

def data210 : CrepProg (BitVec 64) := crepBody210_45
def output210 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8, 115#8], [0, 1], crepProgToHOL data210)
end InitECandidate.Proofs.FrontendStages.Crep
