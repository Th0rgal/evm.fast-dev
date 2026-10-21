import InitECandidate.Proofs.FrontendStages.Crep.Translate501
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody517_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody517_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody517_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody517_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody517_1 crepBody517_2

def crepBody517_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc" [Flapjack.CrepExp.const 40#64]

def crepBody517_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody517_6 : CrepProg (BitVec 64) :=
.seq crepBody517_5 crepBody517_2

def crepBody517_7 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 304#64])) crepBody517_6

def crepBody517_8 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 0#64]) crepBody517_7

def crepBody517_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody517_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "memcpy"
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 296#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody517_11 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody517_10

def crepBody517_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "memzero"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.const 12#64]

def crepBody517_13 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody517_12

def crepBody517_14 : CrepProg (BitVec 64) :=
.seq crepBody517_11 crepBody517_13

def crepBody517_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 44#64],
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 20#64]

def crepBody517_16 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody517_15

def crepBody517_17 : CrepProg (BitVec 64) :=
.seq crepBody517_14 crepBody517_16

def crepBody517_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "memzero"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 64#64],
    Flapjack.CrepExp.const 12#64]

def crepBody517_19 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody517_18

def crepBody517_20 : CrepProg (BitVec 64) :=
.seq crepBody517_17 crepBody517_19

def crepBody517_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 76#64],
    Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 20#64]

def crepBody517_22 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody517_21

def crepBody517_23 : CrepProg (BitVec 64) :=
.seq crepBody517_20 crepBody517_22

def crepBody517_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody517_25 : CrepProg (BitVec 64) :=
.seq crepBody517_24 crepBody517_2

def crepBody517_26 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 8) crepBody517_25

def crepBody517_27 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]) crepBody517_26

def crepBody517_28 : CrepProg (BitVec 64) :=
.seq crepBody517_23 crepBody517_27

def crepBody517_29 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 3#64) crepBody517_25

def crepBody517_30 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 16#64]) crepBody517_29

def crepBody517_31 : CrepProg (BitVec 64) :=
.seq crepBody517_28 crepBody517_30

def crepBody517_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody517_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "u256_to_be32"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.var 9]

def crepBody517_34 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody517_33

def crepBody517_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody517_36 : CrepProg (BitVec 64) :=
.seq crepBody517_35 crepBody517_2

def crepBody517_37 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 9) crepBody517_36

def crepBody517_38 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 24#64]) crepBody517_37

def crepBody517_39 : CrepProg (BitVec 64) :=
.seq crepBody517_34 crepBody517_38

def crepBody517_40 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 32#64) crepBody517_36

def crepBody517_41 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 32#64]) crepBody517_40

def crepBody517_42 : CrepProg (BitVec 64) :=
.seq crepBody517_39 crepBody517_41

def crepBody517_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "log_append"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.var 7]

def crepBody517_44 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody517_43

def crepBody517_45 : CrepProg (BitVec 64) :=
.seq crepBody517_42 crepBody517_44

def crepBody517_46 : CrepProg (BitVec 64) :=
.seq crepBody517_45 crepBody517_1

def crepBody517_47 : CrepProg (BitVec 64) :=
.seq crepBody517_32 crepBody517_46

def crepBody517_48 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody517_47

def crepBody517_49 : CrepProg (BitVec 64) :=
.seq crepBody517_31 crepBody517_48

def crepBody517_50 : CrepProg (BitVec 64) :=
.seq crepBody517_9 crepBody517_49

def crepBody517_51 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody517_50

def crepBody517_52 : CrepProg (BitVec 64) :=
.seq crepBody517_8 crepBody517_51

def crepBody517_53 : CrepProg (BitVec 64) :=
.seq crepBody517_4 crepBody517_52

def crepBody517_54 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody517_53

def crepBody517_55 : CrepProg (BitVec 64) :=
.seq crepBody517_3 crepBody517_54

def crepBody517_56 : CrepProg (BitVec 64) :=
.seq crepBody517_0 crepBody517_55

def crepBody517_57 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody517_56

def data517 : CrepProg (BitVec 64) := crepBody517_57
def output517 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [101#8, 109#8, 105#8, 116#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 102#8, 101#8, 114#8, 95#8, 108#8, 111#8, 103#8], [0, 1, 2, 3, 4, 5], crepProgToHOL data517)
end InitECandidate.Proofs.FrontendStages.Crep
