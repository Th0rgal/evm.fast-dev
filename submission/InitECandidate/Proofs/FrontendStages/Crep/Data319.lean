import InitECandidate.Proofs.FrontendStages.Crep.Translate303
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody319_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 72#64]

def crepBody319_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody319_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody319_3 : CrepProg (BitVec 64) :=
.seq crepBody319_1 crepBody319_2

def crepBody319_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.var 1) crepBody319_3

def crepBody319_5 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]) crepBody319_4

def crepBody319_6 : CrepProg (BitVec 64) :=
.seq crepBody319_0 crepBody319_5

def crepBody319_7 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody319_6

def crepBody319_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 2)

def crepBody319_9 : CrepProg (BitVec 64) :=
.seq crepBody319_8 crepBody319_2

def crepBody319_10 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64])) crepBody319_9

def crepBody319_11 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.const 0#64]) crepBody319_10

def crepBody319_12 : CrepProg (BitVec 64) :=
.seq crepBody319_7 crepBody319_11

def crepBody319_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_new" [Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.const 64#64]

def crepBody319_14 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.const 8#64]) crepBody319_4

def crepBody319_15 : CrepProg (BitVec 64) :=
.seq crepBody319_14 crepBody319_13

def crepBody319_16 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.const 16#64]) crepBody319_4

def crepBody319_17 : CrepProg (BitVec 64) :=
.seq crepBody319_15 crepBody319_16

def crepBody319_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_new" [Flapjack.CrepExp.const 52#64, Flapjack.CrepExp.const 64#64]

def crepBody319_19 : CrepProg (BitVec 64) :=
.seq crepBody319_17 crepBody319_18

def crepBody319_20 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.const 24#64]) crepBody319_4

def crepBody319_21 : CrepProg (BitVec 64) :=
.seq crepBody319_19 crepBody319_20

def crepBody319_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_new" [Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.const 16#64]

def crepBody319_23 : CrepProg (BitVec 64) :=
.seq crepBody319_21 crepBody319_22

def crepBody319_24 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.const 32#64]) crepBody319_4

def crepBody319_25 : CrepProg (BitVec 64) :=
.seq crepBody319_23 crepBody319_24

def crepBody319_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_new" [Flapjack.CrepExp.const 52#64, Flapjack.CrepExp.const 16#64]

def crepBody319_27 : CrepProg (BitVec 64) :=
.seq crepBody319_25 crepBody319_26

def crepBody319_28 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.const 40#64]) crepBody319_4

def crepBody319_29 : CrepProg (BitVec 64) :=
.seq crepBody319_27 crepBody319_28

def crepBody319_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_new" [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 16#64]

def crepBody319_31 : CrepProg (BitVec 64) :=
.seq crepBody319_29 crepBody319_30

def crepBody319_32 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.const 48#64]) crepBody319_4

def crepBody319_33 : CrepProg (BitVec 64) :=
.seq crepBody319_31 crepBody319_32

def crepBody319_34 : CrepProg (BitVec 64) :=
.seq crepBody319_33 crepBody319_22

def crepBody319_35 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.const 56#64]) crepBody319_4

def crepBody319_36 : CrepProg (BitVec 64) :=
.seq crepBody319_34 crepBody319_35

def crepBody319_37 : CrepProg (BitVec 64) :=
.seq crepBody319_36 crepBody319_26

def crepBody319_38 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.const 64#64]) crepBody319_4

def crepBody319_39 : CrepProg (BitVec 64) :=
.seq crepBody319_37 crepBody319_38

def crepBody319_40 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody319_3

def crepBody319_41 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]) crepBody319_40

def crepBody319_42 : CrepProg (BitVec 64) :=
.seq crepBody319_39 crepBody319_41

def crepBody319_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody319_44 : CrepProg (BitVec 64) :=
.seq crepBody319_42 crepBody319_43

def crepBody319_45 : CrepProg (BitVec 64) :=
.seq crepBody319_13 crepBody319_44

def crepBody319_46 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody319_45

def crepBody319_47 : CrepProg (BitVec 64) :=
.seq crepBody319_12 crepBody319_46

def data319 : CrepProg (BitVec 64) := crepBody319_47
def output319 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 102#8, 114#8, 101#8, 115#8, 104#8, 95#8, 116#8, 120#8], [], crepProgToHOL data319)
end InitECandidate.Proofs.FrontendStages.Crep
