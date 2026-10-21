import InitECandidate.Proofs.FrontendStages.Crep.Translate232
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody248_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 1 (Flapjack.CrepExp.var 4)

def crepBody248_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody248_2 : CrepProg (BitVec 64) :=
.seq crepBody248_0 crepBody248_1

def crepBody248_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64]) crepBody248_2

def crepBody248_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2 (Flapjack.CrepExp.var 3)

def crepBody248_5 : CrepProg (BitVec 64) :=
.seq crepBody248_4 crepBody248_1

def crepBody248_6 : CrepProg (BitVec 64) :=
.seq crepBody248_3 crepBody248_5

def crepBody248_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]]))
  (Flapjack.CrepExp.const 0#64)) crepBody248_6 crepBody248_1

def crepBody248_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 4)

def crepBody248_9 : CrepProg (BitVec 64) :=
.seq crepBody248_8 crepBody248_1

def crepBody248_10 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody248_9

def crepBody248_11 : CrepProg (BitVec 64) :=
.seq crepBody248_7 crepBody248_10

def crepBody248_12 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 16#64)) crepBody248_11

def crepBody248_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "mpt_fail" [Flapjack.CrepExp.const 12#64]

def crepBody248_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody248_13

def crepBody248_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody248_14 crepBody248_1

def crepBody248_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call none "node_new_leaf"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64]),
    Flapjack.CrepExp.var 4]

def crepBody248_17 : CrepProg (BitVec 64) :=
.seq crepBody248_15 crepBody248_16

def crepBody248_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody248_17 crepBody248_1

def crepBody248_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "mpt_fail" [Flapjack.CrepExp.const 2#64]

def crepBody248_20 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody248_19

def crepBody248_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody248_20 crepBody248_1

def crepBody248_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc" [Flapjack.CrepExp.const 8#64]

def crepBody248_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 2)

def crepBody248_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call none "node_new_ext" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 5]

def crepBody248_25 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 3#64)) crepBody248_24 crepBody248_1

def crepBody248_26 : CrepProg (BitVec 64) :=
.seq crepBody248_23 crepBody248_25

def crepBody248_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "nibbles_concat"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 40#64])]

def crepBody248_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call none "node_new_leaf"
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.const 1#64,
        Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 40#64])],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 56#64])]

def crepBody248_29 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 1#64)) crepBody248_28 crepBody248_1

def crepBody248_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call none "node_new_ext"
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.const 1#64,
        Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 40#64])],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 48#64])]

def crepBody248_31 : CrepProg (BitVec 64) :=
.seq crepBody248_29 crepBody248_30

def crepBody248_32 : CrepProg (BitVec 64) :=
.seq crepBody248_27 crepBody248_31

def crepBody248_33 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody248_32

def crepBody248_34 : CrepProg (BitVec 64) :=
.seq crepBody248_26 crepBody248_33

def crepBody248_35 : CrepProg (BitVec 64) :=
.seq crepBody248_22 crepBody248_34

def crepBody248_36 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody248_35

def crepBody248_37 : CrepProg (BitVec 64) :=
.seq crepBody248_21 crepBody248_36

def crepBody248_38 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 0#64])) crepBody248_37

def crepBody248_39 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64]])) crepBody248_38

def crepBody248_40 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 1#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64))]) crepBody248_39 crepBody248_1

def crepBody248_41 : CrepProg (BitVec 64) :=
.seq crepBody248_18 crepBody248_40

def crepBody248_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 0]

def crepBody248_43 : CrepProg (BitVec 64) :=
.seq crepBody248_41 crepBody248_42

def crepBody248_44 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 168#64])) crepBody248_43

def crepBody248_45 : CrepProg (BitVec 64) :=
.seq crepBody248_12 crepBody248_44

def crepBody248_46 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody248_45

def crepBody248_47 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody248_46

def crepBody248_48 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody248_47

def data248 : CrepProg (BitVec 64) := crepBody248_48
def output248 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 99#8, 111#8, 108#8, 108#8, 97#8, 112#8, 115#8, 101#8, 95#8, 98#8, 114#8, 97#8, 110#8, 99#8, 104#8], [0], crepProgToHOL data248)
end InitECandidate.Proofs.FrontendStages.Crep
