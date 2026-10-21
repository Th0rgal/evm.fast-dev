import InitECandidate.Proofs.FrontendStages.Crep.Translate547
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody563_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody563_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody563_2 : CrepProg (BitVec 64) :=
.seq crepBody563_0 crepBody563_1

def crepBody563_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 1732584193#64) crepBody563_2

def crepBody563_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 336#64])) crepBody563_3

def crepBody563_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 4023233417#64) crepBody563_2

def crepBody563_6 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 336#64]),
    Flapjack.CrepExp.const 8#64]) crepBody563_5

def crepBody563_7 : CrepProg (BitVec 64) :=
.seq crepBody563_4 crepBody563_6

def crepBody563_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 2562383102#64) crepBody563_2

def crepBody563_9 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 336#64]),
    Flapjack.CrepExp.const 16#64]) crepBody563_8

def crepBody563_10 : CrepProg (BitVec 64) :=
.seq crepBody563_7 crepBody563_9

def crepBody563_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 271733878#64) crepBody563_2

def crepBody563_12 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 336#64]),
    Flapjack.CrepExp.const 24#64]) crepBody563_11

def crepBody563_13 : CrepProg (BitVec 64) :=
.seq crepBody563_10 crepBody563_12

def crepBody563_14 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 3285377520#64) crepBody563_2

def crepBody563_15 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 336#64]),
    Flapjack.CrepExp.const 32#64]) crepBody563_14

def crepBody563_16 : CrepProg (BitVec 64) :=
.seq crepBody563_13 crepBody563_15

def crepBody563_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "ripemd160_block"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 336#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]]

def crepBody563_18 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody563_17

def crepBody563_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 4)

def crepBody563_20 : CrepProg (BitVec 64) :=
.seq crepBody563_19 crepBody563_1

def crepBody563_21 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]) crepBody563_20

def crepBody563_22 : CrepProg (BitVec 64) :=
.seq crepBody563_18 crepBody563_21

def crepBody563_23 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 1)
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64])) crepBody563_22

def crepBody563_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "memzero"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 344#64]),
    Flapjack.CrepExp.const 128#64]

def crepBody563_25 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody563_24

def crepBody563_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "memcpy"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 344#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3], Flapjack.CrepExp.var 4]

def crepBody563_27 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody563_26

def crepBody563_28 : CrepProg (BitVec 64) :=
.seq crepBody563_25 crepBody563_27

def crepBody563_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 344#64]),
      Flapjack.CrepExp.var 4])
  (Flapjack.CrepExp.const 128#64)

def crepBody563_30 : CrepProg (BitVec 64) :=
.seq crepBody563_28 crepBody563_29

def crepBody563_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.const 128#64)

def crepBody563_32 : CrepProg (BitVec 64) :=
.seq crepBody563_31 crepBody563_1

def crepBody563_33 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 56#64)) crepBody563_32 crepBody563_1

def crepBody563_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "st_le64"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub
      [Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.load
              (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 344#64]),
            Flapjack.CrepExp.var 5],
        Flapjack.CrepExp.const 8#64],
    Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 3#64)]

def crepBody563_35 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody563_34

def crepBody563_36 : CrepProg (BitVec 64) :=
.seq crepBody563_33 crepBody563_35

def crepBody563_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "ripemd160_block"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 336#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 344#64])]

def crepBody563_38 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody563_37

def crepBody563_39 : CrepProg (BitVec 64) :=
.seq crepBody563_36 crepBody563_38

def crepBody563_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "ripemd160_block"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 336#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 344#64]),
        Flapjack.CrepExp.const 64#64]]

def crepBody563_41 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody563_40

def crepBody563_42 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 128#64)) crepBody563_41 crepBody563_1

def crepBody563_43 : CrepProg (BitVec 64) :=
.seq crepBody563_39 crepBody563_42

def crepBody563_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.const 0#64)

def crepBody563_45 : CrepProg (BitVec 64) :=
.seq crepBody563_44 crepBody563_1

def crepBody563_46 : CrepProg (BitVec 64) :=
.seq crepBody563_43 crepBody563_45

def crepBody563_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "st_le32"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 2,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64]],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 336#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]])]

def crepBody563_48 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody563_47

def crepBody563_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 6)

def crepBody563_50 : CrepProg (BitVec 64) :=
.seq crepBody563_49 crepBody563_1

def crepBody563_51 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody563_50

def crepBody563_52 : CrepProg (BitVec 64) :=
.seq crepBody563_48 crepBody563_51

def crepBody563_53 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 5#64)) crepBody563_52

def crepBody563_54 : CrepProg (BitVec 64) :=
.seq crepBody563_46 crepBody563_53

def crepBody563_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody563_56 : CrepProg (BitVec 64) :=
.seq crepBody563_54 crepBody563_55

def crepBody563_57 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 64#64) crepBody563_56

def crepBody563_58 : CrepProg (BitVec 64) :=
.seq crepBody563_30 crepBody563_57

def crepBody563_59 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3]) crepBody563_58

def crepBody563_60 : CrepProg (BitVec 64) :=
.seq crepBody563_23 crepBody563_59

def crepBody563_61 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody563_60

def crepBody563_62 : CrepProg (BitVec 64) :=
.seq crepBody563_16 crepBody563_61

def data563 : CrepProg (BitVec 64) := crepBody563_62
def output563 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [114#8, 105#8, 112#8, 101#8, 109#8, 100#8, 49#8, 54#8, 48#8], [0, 1, 2], crepProgToHOL data563)
end InitECandidate.Proofs.FrontendStages.Crep
