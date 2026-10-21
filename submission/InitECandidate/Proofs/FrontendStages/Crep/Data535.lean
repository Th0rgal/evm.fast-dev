import InitECandidate.Proofs.FrontendStages.Crep.Translate519
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody535_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "state_snapshot" []

def crepBody535_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "destroy_storage" [Flapjack.CrepExp.var 9]

def crepBody535_2 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody535_1

def crepBody535_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "mark_account_created" [Flapjack.CrepExp.var 9]

def crepBody535_4 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody535_3

def crepBody535_5 : CrepProg (BitVec 64) :=
.seq crepBody535_2 crepBody535_4

def crepBody535_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "increment_nonce" [Flapjack.CrepExp.var 9]

def crepBody535_7 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody535_6

def crepBody535_8 : CrepProg (BitVec 64) :=
.seq crepBody535_5 crepBody535_7

def crepBody535_9 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64])) crepBody535_8

def crepBody535_10 : CrepProg (BitVec 64) :=
.seq crepBody535_0 crepBody535_9

def crepBody535_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody535_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 2#64)) crepBody535_10 crepBody535_11

def crepBody535_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 9)

def crepBody535_14 : CrepProg (BitVec 64) :=
.seq crepBody535_13 crepBody535_11

def crepBody535_15 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 7#64) crepBody535_14

def crepBody535_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody535_17 : CrepProg (BitVec 64) :=
.seq crepBody535_15 crepBody535_16

def crepBody535_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 1024#64)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 128#64]))) crepBody535_17 crepBody535_11

def crepBody535_19 : CrepProg (BitVec 64) :=
.seq crepBody535_12 crepBody535_18

def crepBody535_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "frame_open" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody535_21 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody535_20

def crepBody535_22 : CrepProg (BitVec 64) :=
.seq crepBody535_19 crepBody535_21

def crepBody535_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "state_snapshot" []

def crepBody535_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody535_25 : CrepProg (BitVec 64) :=
.seq crepBody535_24 crepBody535_11

def crepBody535_26 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 9) crepBody535_25

def crepBody535_27 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.const 24#64]) crepBody535_26

def crepBody535_28 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 8) crepBody535_25

def crepBody535_29 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.const 96#64]) crepBody535_28

def crepBody535_30 : CrepProg (BitVec 64) :=
.seq crepBody535_27 crepBody535_29

def crepBody535_31 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 2) crepBody535_25

def crepBody535_32 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.const 48#64]) crepBody535_31

def crepBody535_33 : CrepProg (BitVec 64) :=
.seq crepBody535_30 crepBody535_32

def crepBody535_34 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 3) crepBody535_25

def crepBody535_35 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.const 56#64]) crepBody535_34

def crepBody535_36 : CrepProg (BitVec 64) :=
.seq crepBody535_33 crepBody535_35

def crepBody535_37 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 4) crepBody535_25

def crepBody535_38 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.const 64#64]) crepBody535_37

def crepBody535_39 : CrepProg (BitVec 64) :=
.seq crepBody535_36 crepBody535_38

def crepBody535_40 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 5) crepBody535_25

def crepBody535_41 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.const 72#64]) crepBody535_40

def crepBody535_42 : CrepProg (BitVec 64) :=
.seq crepBody535_39 crepBody535_41

def crepBody535_43 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 6) crepBody535_25

def crepBody535_44 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.const 80#64]) crepBody535_43

def crepBody535_45 : CrepProg (BitVec 64) :=
.seq crepBody535_42 crepBody535_44

def crepBody535_46 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 7) crepBody535_25

def crepBody535_47 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.const 88#64]) crepBody535_46

def crepBody535_48 : CrepProg (BitVec 64) :=
.seq crepBody535_45 crepBody535_47

def crepBody535_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "frame_start" []

def crepBody535_50 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody535_49

def crepBody535_51 : CrepProg (BitVec 64) :=
.seq crepBody535_48 crepBody535_50

def crepBody535_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody535_53 : CrepProg (BitVec 64) :=
.seq crepBody535_51 crepBody535_52

def crepBody535_54 : CrepProg (BitVec 64) :=
.seq crepBody535_23 crepBody535_53

def crepBody535_55 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody535_54

def crepBody535_56 : CrepProg (BitVec 64) :=
.seq crepBody535_22 crepBody535_55

def crepBody535_57 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody535_56

def data535 : CrepProg (BitVec 64) := crepBody535_57
def output535 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 114#8, 116#8, 95#8, 99#8, 104#8, 105#8, 108#8, 100#8], [0, 1, 2, 3, 4, 5, 6, 7], crepProgToHOL data535)
end InitECandidate.Proofs.FrontendStages.Crep
