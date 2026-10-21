import InitECandidate.Proofs.FrontendStages.Crep.Translate392
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody408_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 6)

def crepBody408_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody408_2 : CrepProg (BitVec 64) :=
.seq crepBody408_0 crepBody408_1

def crepBody408_3 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 3#64) crepBody408_2

def crepBody408_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody408_5 : CrepProg (BitVec 64) :=
.seq crepBody408_3 crepBody408_4

def crepBody408_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 1024#64)) crepBody408_5 crepBody408_1

def crepBody408_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.const 1024#64)

def crepBody408_8 : CrepProg (BitVec 64) :=
.seq crepBody408_7 crepBody408_1

def crepBody408_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 1024#64) (Flapjack.CrepExp.var 6)) crepBody408_8 crepBody408_1

def crepBody408_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "scratch_alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 32#64]]

def crepBody408_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "memcpy"
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64]]

def crepBody408_12 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody408_11

def crepBody408_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody408_14 : CrepProg (BitVec 64) :=
.seq crepBody408_13 crepBody408_1

def crepBody408_15 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 7) crepBody408_14

def crepBody408_16 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 8#64]) crepBody408_15

def crepBody408_17 : CrepProg (BitVec 64) :=
.seq crepBody408_12 crepBody408_16

def crepBody408_18 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 6) crepBody408_14

def crepBody408_19 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 232#64]) crepBody408_18

def crepBody408_20 : CrepProg (BitVec 64) :=
.seq crepBody408_17 crepBody408_19

def crepBody408_21 : CrepProg (BitVec 64) :=
.seq crepBody408_10 crepBody408_20

def crepBody408_22 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody408_21

def crepBody408_23 : CrepProg (BitVec 64) :=
.seq crepBody408_9 crepBody408_22

def crepBody408_24 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 2#64]) crepBody408_23

def crepBody408_25 : CrepProg (BitVec 64) :=
.seq crepBody408_6 crepBody408_24

def crepBody408_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 5)) crepBody408_25 crepBody408_1

def crepBody408_27 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 1024#64)) crepBody408_5 crepBody408_1

def crepBody408_28 : CrepProg (BitVec 64) :=
.seq crepBody408_26 crepBody408_27

def crepBody408_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody408_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 8)

def crepBody408_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 9)

def crepBody408_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 10)

def crepBody408_33 : CrepProg (BitVec 64) :=
.seq crepBody408_32 crepBody408_1

def crepBody408_34 : CrepProg (BitVec 64) :=
.seq crepBody408_31 crepBody408_33

def crepBody408_35 : CrepProg (BitVec 64) :=
.seq crepBody408_30 crepBody408_34

def crepBody408_36 : CrepProg (BitVec 64) :=
.seq crepBody408_29 crepBody408_35

def crepBody408_37 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 3) crepBody408_36

def crepBody408_38 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 2) crepBody408_37

def crepBody408_39 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 1) crepBody408_38

def crepBody408_40 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 0) crepBody408_39

def crepBody408_41 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64]]) crepBody408_40

def crepBody408_42 : CrepProg (BitVec 64) :=
.seq crepBody408_28 crepBody408_41

def crepBody408_43 : CrepProg (BitVec 64) :=
.seq crepBody408_29 crepBody408_1

def crepBody408_44 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody408_43

def crepBody408_45 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 16#64]) crepBody408_44

def crepBody408_46 : CrepProg (BitVec 64) :=
.seq crepBody408_42 crepBody408_45

def crepBody408_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody408_48 : CrepProg (BitVec 64) :=
.seq crepBody408_46 crepBody408_47

def crepBody408_49 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 232#64])) crepBody408_48

def crepBody408_50 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 16#64])) crepBody408_49

def data408 : CrepProg (BitVec 64) := crepBody408_50
def output408 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 99#8, 107#8, 95#8, 112#8, 117#8, 115#8, 104#8], [0, 1, 2, 3], crepProgToHOL data408)
end InitECandidate.Proofs.FrontendStages.Crep
