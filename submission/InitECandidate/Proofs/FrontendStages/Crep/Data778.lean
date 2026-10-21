import InitECandidate.Proofs.FrontendStages.Crep.Translate762
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody778_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 5#64, Flapjack.CrepExp.const 16#64]]

def crepBody778_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.const 76#64)

def crepBody778_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody778_3 : CrepProg (BitVec 64) :=
.seq crepBody778_1 crepBody778_2

def crepBody778_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 1#64)) crepBody778_3 crepBody778_2

def crepBody778_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.const 116#64)

def crepBody778_6 : CrepProg (BitVec 64) :=
.seq crepBody778_5 crepBody778_2

def crepBody778_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 2#64)) crepBody778_6 crepBody778_2

def crepBody778_8 : CrepProg (BitVec 64) :=
.seq crepBody778_4 crepBody778_7

def crepBody778_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.const 184#64)

def crepBody778_10 : CrepProg (BitVec 64) :=
.seq crepBody778_9 crepBody778_2

def crepBody778_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 3#64)) crepBody778_10 crepBody778_2

def crepBody778_12 : CrepProg (BitVec 64) :=
.seq crepBody778_8 crepBody778_11

def crepBody778_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.const 68#64)

def crepBody778_14 : CrepProg (BitVec 64) :=
.seq crepBody778_13 crepBody778_2

def crepBody778_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 4#64)) crepBody778_14 crepBody778_2

def crepBody778_16 : CrepProg (BitVec 64) :=
.seq crepBody778_12 crepBody778_15

def crepBody778_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6],
        Flapjack.CrepExp.const 8#64]]

def crepBody778_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 3)

def crepBody778_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64], Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]]

def crepBody778_20 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody778_19

def crepBody778_21 : CrepProg (BitVec 64) :=
.seq crepBody778_18 crepBody778_20

def crepBody778_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody778_23 : CrepProg (BitVec 64) :=
.seq crepBody778_22 crepBody778_2

def crepBody778_24 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 7) crepBody778_23

def crepBody778_25 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64]]) crepBody778_24

def crepBody778_26 : CrepProg (BitVec 64) :=
.seq crepBody778_21 crepBody778_25

def crepBody778_27 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6],
    Flapjack.CrepExp.const 1#64]) crepBody778_23

def crepBody778_28 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64],
    Flapjack.CrepExp.const 8#64]) crepBody778_27

def crepBody778_29 : CrepProg (BitVec 64) :=
.seq crepBody778_26 crepBody778_28

def crepBody778_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2 (Flapjack.CrepExp.var 8)

def crepBody778_31 : CrepProg (BitVec 64) :=
.seq crepBody778_30 crepBody778_2

def crepBody778_32 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64]) crepBody778_31

def crepBody778_33 : CrepProg (BitVec 64) :=
.seq crepBody778_29 crepBody778_32

def crepBody778_34 : CrepProg (BitVec 64) :=
.seq crepBody778_17 crepBody778_33

def crepBody778_35 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody778_34

def crepBody778_36 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody778_35 crepBody778_2

def crepBody778_37 : CrepProg (BitVec 64) :=
.seq crepBody778_16 crepBody778_36

def crepBody778_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 7)

def crepBody778_39 : CrepProg (BitVec 64) :=
.seq crepBody778_38 crepBody778_2

def crepBody778_40 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody778_39

def crepBody778_41 : CrepProg (BitVec 64) :=
.seq crepBody778_37 crepBody778_40

def crepBody778_42 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 192#64) crepBody778_41

def crepBody778_43 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64]])) crepBody778_42

def crepBody778_44 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64]])) crepBody778_43

def crepBody778_45 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 5#64)) crepBody778_44

def crepBody778_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody778_47 : CrepProg (BitVec 64) :=
.seq crepBody778_45 crepBody778_46

def crepBody778_48 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody778_47

def crepBody778_49 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody778_48

def crepBody778_50 : CrepProg (BitVec 64) :=
.seq crepBody778_0 crepBody778_49

def crepBody778_51 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody778_50

def data778 : CrepProg (BitVec 64) := crepBody778_51
def output778 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 101#8, 120#8, 101#8, 99#8, 117#8, 116#8, 105#8, 111#8, 110#8, 95#8,
    114#8, 101#8, 113#8, 117#8, 101#8, 115#8, 116#8, 115#8], [0], crepProgToHOL data778)
end InitECandidate.Proofs.FrontendStages.Crep
