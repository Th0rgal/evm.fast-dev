import InitECandidate.Proofs.FrontendStages.Crep.Translate602
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody618_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memzero" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 1152#64]

def crepBody618_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody618_0

def crepBody618_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12, 13, 14], none)) "fq_mul_small"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.const 9#64]

def crepBody618_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "fq_sub"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody618_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 19 (Flapjack.CrepExp.const 2#64)

def crepBody618_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody618_6 : CrepProg (BitVec 64) :=
.seq crepBody618_4 crepBody618_5

def crepBody618_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody618_6 crepBody618_5

def crepBody618_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 19 (Flapjack.CrepExp.const 3#64)

def crepBody618_9 : CrepProg (BitVec 64) :=
.seq crepBody618_8 crepBody618_5

def crepBody618_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 1#64)) crepBody618_9 crepBody618_5

def crepBody618_11 : CrepProg (BitVec 64) :=
.seq crepBody618_7 crepBody618_10

def crepBody618_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.var 22)

def crepBody618_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 23)

def crepBody618_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 24)

def crepBody618_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 25)

def crepBody618_16 : CrepProg (BitVec 64) :=
.seq crepBody618_15 crepBody618_5

def crepBody618_17 : CrepProg (BitVec 64) :=
.seq crepBody618_14 crepBody618_16

def crepBody618_18 : CrepProg (BitVec 64) :=
.seq crepBody618_13 crepBody618_17

def crepBody618_19 : CrepProg (BitVec 64) :=
.seq crepBody618_12 crepBody618_18

def crepBody618_20 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.var 18) crepBody618_19

def crepBody618_21 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 17) crepBody618_20

def crepBody618_22 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.var 16) crepBody618_21

def crepBody618_23 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 15) crepBody618_22

def crepBody618_24 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 20,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 32#64]]) crepBody618_23

def crepBody618_25 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.var 10) crepBody618_19

def crepBody618_26 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 9) crepBody618_25

def crepBody618_27 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.var 8) crepBody618_26

def crepBody618_28 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 7) crepBody618_27

def crepBody618_29 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 20,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 6#64],
        Flapjack.CrepExp.const 32#64]]) crepBody618_28

def crepBody618_30 : CrepProg (BitVec 64) :=
.seq crepBody618_24 crepBody618_29

def crepBody618_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2 (Flapjack.CrepExp.var 21)

def crepBody618_32 : CrepProg (BitVec 64) :=
.seq crepBody618_31 crepBody618_5

def crepBody618_33 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64]) crepBody618_32

def crepBody618_34 : CrepProg (BitVec 64) :=
.seq crepBody618_30 crepBody618_33

def crepBody618_35 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 384#64]]) crepBody618_34

def crepBody618_36 : CrepProg (BitVec 64) :=
.seq crepBody618_11 crepBody618_35

def crepBody618_37 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody618_36

def crepBody618_38 : CrepProg (BitVec 64) :=
.seq crepBody618_3 crepBody618_37

def crepBody618_39 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody618_38

def crepBody618_40 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody618_39

def crepBody618_41 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody618_40

def crepBody618_42 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody618_41

def crepBody618_43 : CrepProg (BitVec 64) :=
.seq crepBody618_2 crepBody618_42

def crepBody618_44 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody618_43

def crepBody618_45 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody618_44

def crepBody618_46 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody618_45

def crepBody618_47 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody618_46

def crepBody618_48 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 24#64])) crepBody618_47

def crepBody618_49 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 16#64])) crepBody618_48

def crepBody618_50 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 8#64])) crepBody618_49

def crepBody618_51 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 1,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64],
      Flapjack.CrepExp.const 32#64])) crepBody618_50

def crepBody618_52 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64]],
      Flapjack.CrepExp.const 24#64])) crepBody618_51

def crepBody618_53 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64]],
      Flapjack.CrepExp.const 16#64])) crepBody618_52

def crepBody618_54 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64]],
      Flapjack.CrepExp.const 8#64])) crepBody618_53

def crepBody618_55 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 1,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64]])) crepBody618_54

def crepBody618_56 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 3#64)) crepBody618_55

def crepBody618_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody618_58 : CrepProg (BitVec 64) :=
.seq crepBody618_56 crepBody618_57

def crepBody618_59 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody618_58

def crepBody618_60 : CrepProg (BitVec 64) :=
.seq crepBody618_1 crepBody618_59

def data618 : CrepProg (BitVec 64) := crepBody618_60
def output618 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 113#8, 49#8, 50#8, 95#8, 116#8, 119#8, 105#8, 115#8, 116#8], [0, 1], crepProgToHOL data618)
end InitECandidate.Proofs.FrontendStages.Crep
