import InitECandidate.Proofs.FrontendStages.Crep.Translate572
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody588_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "charge_gas" [Flapjack.CrepExp.const 6900#64]

def crepBody588_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody588_0

def crepBody588_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 8#64]

def crepBody588_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody588_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody588_5 : CrepProg (BitVec 64) :=
.seq crepBody588_3 crepBody588_4

def crepBody588_6 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 2) crepBody588_5

def crepBody588_7 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody588_6

def crepBody588_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody588_5

def crepBody588_9 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody588_8

def crepBody588_10 : CrepProg (BitVec 64) :=
.seq crepBody588_7 crepBody588_9

def crepBody588_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody588_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 160#64)) crepBody588_11 crepBody588_4

def crepBody588_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.const 32#64]

def crepBody588_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9, 10, 11, 12], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 64#64],
    Flapjack.CrepExp.const 32#64]

def crepBody588_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13, 14, 15, 16], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.const 32#64]

def crepBody588_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17, 18, 19, 20], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 128#64],
    Flapjack.CrepExp.const 32#64]

def crepBody588_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "p256_verify"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19,
    Flapjack.CrepExp.var 20]

def crepBody588_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody588_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "memzero" [Flapjack.CrepExp.var 22, Flapjack.CrepExp.const 32#64]

def crepBody588_20 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody588_19

def crepBody588_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 22, Flapjack.CrepExp.const 31#64])
  (Flapjack.CrepExp.const 1#64)

def crepBody588_22 : CrepProg (BitVec 64) :=
.seq crepBody588_20 crepBody588_21

def crepBody588_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 23) (Flapjack.CrepExp.var 24)

def crepBody588_24 : CrepProg (BitVec 64) :=
.seq crepBody588_23 crepBody588_4

def crepBody588_25 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 22) crepBody588_24

def crepBody588_26 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody588_25

def crepBody588_27 : CrepProg (BitVec 64) :=
.seq crepBody588_22 crepBody588_26

def crepBody588_28 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 32#64) crepBody588_24

def crepBody588_29 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody588_28

def crepBody588_30 : CrepProg (BitVec 64) :=
.seq crepBody588_27 crepBody588_29

def crepBody588_31 : CrepProg (BitVec 64) :=
.seq crepBody588_18 crepBody588_30

def crepBody588_32 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody588_31

def crepBody588_33 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.const 1#64)) crepBody588_32 crepBody588_4

def crepBody588_34 : CrepProg (BitVec 64) :=
.seq crepBody588_33 crepBody588_11

def crepBody588_35 : CrepProg (BitVec 64) :=
.seq crepBody588_17 crepBody588_34

def crepBody588_36 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody588_35

def crepBody588_37 : CrepProg (BitVec 64) :=
.seq crepBody588_16 crepBody588_36

def crepBody588_38 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody588_37

def crepBody588_39 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody588_38

def crepBody588_40 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody588_39

def crepBody588_41 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody588_40

def crepBody588_42 : CrepProg (BitVec 64) :=
.seq crepBody588_15 crepBody588_41

def crepBody588_43 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody588_42

def crepBody588_44 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody588_43

def crepBody588_45 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody588_44

def crepBody588_46 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody588_45

def crepBody588_47 : CrepProg (BitVec 64) :=
.seq crepBody588_14 crepBody588_46

def crepBody588_48 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody588_47

def crepBody588_49 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody588_48

def crepBody588_50 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody588_49

def crepBody588_51 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody588_50

def crepBody588_52 : CrepProg (BitVec 64) :=
.seq crepBody588_13 crepBody588_51

def crepBody588_53 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody588_52

def crepBody588_54 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody588_53

def crepBody588_55 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody588_54

def crepBody588_56 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody588_55

def crepBody588_57 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64])) crepBody588_56

def crepBody588_58 : CrepProg (BitVec 64) :=
.seq crepBody588_12 crepBody588_57

def crepBody588_59 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody588_58

def crepBody588_60 : CrepProg (BitVec 64) :=
.seq crepBody588_10 crepBody588_59

def crepBody588_61 : CrepProg (BitVec 64) :=
.seq crepBody588_2 crepBody588_60

def crepBody588_62 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody588_61

def crepBody588_63 : CrepProg (BitVec 64) :=
.seq crepBody588_1 crepBody588_62

def crepBody588_64 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody588_63

def data588 : CrepProg (BitVec 64) := crepBody588_64
def output588 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 112#8, 50#8, 53#8, 54#8, 118#8, 101#8, 114#8, 105#8, 102#8, 121#8], [], crepProgToHOL data588)
end InitECandidate.Proofs.FrontendStages.Crep
