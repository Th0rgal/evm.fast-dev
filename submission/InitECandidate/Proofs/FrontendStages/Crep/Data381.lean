import InitECandidate.Proofs.FrontendStages.Crep.Translate365
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody381_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "st_le64"
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 224#64])]

def crepBody381_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody381_0

def crepBody381_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64], Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.const 20#64]

def crepBody381_3 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody381_2

def crepBody381_4 : CrepProg (BitVec 64) :=
.seq crepBody381_1 crepBody381_3

def crepBody381_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "htab_get"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 232#64]),
    Flapjack.CrepExp.var 1]

def crepBody381_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody381_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody381_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody381_6 crepBody381_7

def crepBody381_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "get_pre_tx_account" [Flapjack.CrepExp.var 0]

def crepBody381_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 80#64]

def crepBody381_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memzero" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 80#64]

def crepBody381_12 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody381_11

def crepBody381_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 48#64],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 136#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody381_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody381_13

def crepBody381_15 : CrepProg (BitVec 64) :=
.seq crepBody381_12 crepBody381_14

def crepBody381_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody381_17 : CrepProg (BitVec 64) :=
.seq crepBody381_16 crepBody381_7

def crepBody381_18 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 1#64) crepBody381_17

def crepBody381_19 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 5) crepBody381_18

def crepBody381_20 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 0#64])) crepBody381_17

def crepBody381_21 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]) crepBody381_20

def crepBody381_22 : CrepProg (BitVec 64) :=
.seq crepBody381_19 crepBody381_21

def crepBody381_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 8)

def crepBody381_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 9)

def crepBody381_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 10)

def crepBody381_26 : CrepProg (BitVec 64) :=
.seq crepBody381_25 crepBody381_7

def crepBody381_27 : CrepProg (BitVec 64) :=
.seq crepBody381_24 crepBody381_26

def crepBody381_28 : CrepProg (BitVec 64) :=
.seq crepBody381_23 crepBody381_27

def crepBody381_29 : CrepProg (BitVec 64) :=
.seq crepBody381_16 crepBody381_28

def crepBody381_30 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64],
      Flapjack.CrepExp.const 24#64])) crepBody381_29

def crepBody381_31 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64],
      Flapjack.CrepExp.const 16#64])) crepBody381_30

def crepBody381_32 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64],
      Flapjack.CrepExp.const 8#64])) crepBody381_31

def crepBody381_33 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64])) crepBody381_32

def crepBody381_34 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 16#64]) crepBody381_33

def crepBody381_35 : CrepProg (BitVec 64) :=
.seq crepBody381_22 crepBody381_34

def crepBody381_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 48#64],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody381_37 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody381_36

def crepBody381_38 : CrepProg (BitVec 64) :=
.seq crepBody381_35 crepBody381_37

def crepBody381_39 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 1#64)) crepBody381_38 crepBody381_7

def crepBody381_40 : CrepProg (BitVec 64) :=
.seq crepBody381_15 crepBody381_39

def crepBody381_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "st_le64"
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 224#64])]

def crepBody381_42 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody381_41

def crepBody381_43 : CrepProg (BitVec 64) :=
.seq crepBody381_40 crepBody381_42

def crepBody381_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64], Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.const 20#64]

def crepBody381_45 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody381_44

def crepBody381_46 : CrepProg (BitVec 64) :=
.seq crepBody381_43 crepBody381_45

def crepBody381_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "htab_set"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 232#64]),
    Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 5]

def crepBody381_48 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody381_47

def crepBody381_49 : CrepProg (BitVec 64) :=
.seq crepBody381_46 crepBody381_48

def crepBody381_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 5]

def crepBody381_51 : CrepProg (BitVec 64) :=
.seq crepBody381_49 crepBody381_50

def crepBody381_52 : CrepProg (BitVec 64) :=
.seq crepBody381_10 crepBody381_51

def crepBody381_53 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody381_52

def crepBody381_54 : CrepProg (BitVec 64) :=
.seq crepBody381_9 crepBody381_53

def crepBody381_55 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody381_54

def crepBody381_56 : CrepProg (BitVec 64) :=
.seq crepBody381_8 crepBody381_55

def crepBody381_57 : CrepProg (BitVec 64) :=
.seq crepBody381_5 crepBody381_56

def crepBody381_58 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody381_57

def crepBody381_59 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody381_58

def crepBody381_60 : CrepProg (BitVec 64) :=
.seq crepBody381_4 crepBody381_59

def crepBody381_61 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 248#64])) crepBody381_60

def data381 : CrepProg (BitVec 64) := crepBody381_61
def output381 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [105#8, 100#8, 120#8, 95#8, 115#8, 116#8, 97#8, 114#8, 116#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8], [0], crepProgToHOL data381)
end InitECandidate.Proofs.FrontendStages.Crep
