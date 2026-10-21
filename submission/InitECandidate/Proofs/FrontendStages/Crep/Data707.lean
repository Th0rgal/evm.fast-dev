import InitECandidate.Proofs.FrontendStages.Crep.Translate691
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody707_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "bls_fp_decode64" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody707_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody707_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody707_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody707_1 crepBody707_2

def crepBody707_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "bls_fp_decode64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64]]

def crepBody707_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody707_1 crepBody707_2

def crepBody707_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "bls_fp_is_zero"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]

def crepBody707_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "bls_fp_is_zero"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13,
    Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15]

def crepBody707_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.var 19)

def crepBody707_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 20)

def crepBody707_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 21)

def crepBody707_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 22)

def crepBody707_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 32#64])
  (Flapjack.CrepExp.var 23)

def crepBody707_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 40#64])
  (Flapjack.CrepExp.var 24)

def crepBody707_14 : CrepProg (BitVec 64) :=
.seq crepBody707_13 crepBody707_2

def crepBody707_15 : CrepProg (BitVec 64) :=
.seq crepBody707_12 crepBody707_14

def crepBody707_16 : CrepProg (BitVec 64) :=
.seq crepBody707_11 crepBody707_15

def crepBody707_17 : CrepProg (BitVec 64) :=
.seq crepBody707_10 crepBody707_16

def crepBody707_18 : CrepProg (BitVec 64) :=
.seq crepBody707_9 crepBody707_17

def crepBody707_19 : CrepProg (BitVec 64) :=
.seq crepBody707_8 crepBody707_18

def crepBody707_20 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody707_19

def crepBody707_21 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody707_20

def crepBody707_22 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody707_21

def crepBody707_23 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody707_22

def crepBody707_24 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody707_23

def crepBody707_25 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody707_24

def crepBody707_26 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]) crepBody707_25

def crepBody707_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody707_28 : CrepProg (BitVec 64) :=
.seq crepBody707_26 crepBody707_27

def crepBody707_29 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.const 1#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.const 1#64))]) crepBody707_28 crepBody707_2

def crepBody707_30 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 1582556514881692819#64) crepBody707_19

def crepBody707_31 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 6631298214892334189#64) crepBody707_30

def crepBody707_32 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 8632934651105793861#64) crepBody707_31

def crepBody707_33 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 6865905132761471162#64) crepBody707_32

def crepBody707_34 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 17002214543764226050#64) crepBody707_33

def crepBody707_35 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 8505329371266088957#64) crepBody707_34

def crepBody707_36 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]) crepBody707_35

def crepBody707_37 : CrepProg (BitVec 64) :=
.seq crepBody707_29 crepBody707_36

def crepBody707_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call none "g1_on_curve"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15]

def crepBody707_39 : CrepProg (BitVec 64) :=
.seq crepBody707_37 crepBody707_38

def crepBody707_40 : CrepProg (BitVec 64) :=
.seq crepBody707_7 crepBody707_39

def crepBody707_41 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody707_40

def crepBody707_42 : CrepProg (BitVec 64) :=
.seq crepBody707_6 crepBody707_41

def crepBody707_43 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody707_42

def crepBody707_44 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 40#64])) crepBody707_43

def crepBody707_45 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 32#64])) crepBody707_44

def crepBody707_46 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 24#64])) crepBody707_45

def crepBody707_47 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 16#64])) crepBody707_46

def crepBody707_48 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 8#64])) crepBody707_47

def crepBody707_49 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64])) crepBody707_48

def crepBody707_50 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64])) crepBody707_49

def crepBody707_51 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])) crepBody707_50

def crepBody707_52 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])) crepBody707_51

def crepBody707_53 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64])) crepBody707_52

def crepBody707_54 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody707_53

def crepBody707_55 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 1)) crepBody707_54

def crepBody707_56 : CrepProg (BitVec 64) :=
.seq crepBody707_5 crepBody707_55

def crepBody707_57 : CrepProg (BitVec 64) :=
.seq crepBody707_4 crepBody707_56

def crepBody707_58 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody707_57

def crepBody707_59 : CrepProg (BitVec 64) :=
.seq crepBody707_3 crepBody707_58

def crepBody707_60 : CrepProg (BitVec 64) :=
.seq crepBody707_0 crepBody707_59

def crepBody707_61 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody707_60

def data707 : CrepProg (BitVec 64) := crepBody707_61
def output707 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8], [0, 1], crepProgToHOL data707)
end InitECandidate.Proofs.FrontendStages.Crep
