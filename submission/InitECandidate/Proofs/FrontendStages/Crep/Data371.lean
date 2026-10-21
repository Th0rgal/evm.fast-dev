import InitECandidate.Proofs.FrontendStages.Crep.Translate355
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody371_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2], none)) "htab_get"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 216#64]),
    Flapjack.CrepExp.var 0]

def crepBody371_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2]

def crepBody371_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody371_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody371_1 crepBody371_2

def crepBody371_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 40#64]

def crepBody371_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htab_new" [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 8#64]

def crepBody371_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody371_7 : CrepProg (BitVec 64) :=
.seq crepBody371_6 crepBody371_2

def crepBody371_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 4) crepBody371_7

def crepBody371_9 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 0#64]) crepBody371_8

def crepBody371_10 : CrepProg (BitVec 64) :=
.seq crepBody371_9 crepBody371_5

def crepBody371_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]) crepBody371_8

def crepBody371_12 : CrepProg (BitVec 64) :=
.seq crepBody371_10 crepBody371_11

def crepBody371_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "lst_new" [Flapjack.CrepExp.const 40#64, Flapjack.CrepExp.const 4#64]

def crepBody371_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody371_15 : CrepProg (BitVec 64) :=
.seq crepBody371_14 crepBody371_2

def crepBody371_16 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 5) crepBody371_15

def crepBody371_17 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64]) crepBody371_16

def crepBody371_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "lst_new" [Flapjack.CrepExp.const 16#64, Flapjack.CrepExp.const 4#64]

def crepBody371_19 : CrepProg (BitVec 64) :=
.seq crepBody371_17 crepBody371_18

def crepBody371_20 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64]) crepBody371_16

def crepBody371_21 : CrepProg (BitVec 64) :=
.seq crepBody371_19 crepBody371_20

def crepBody371_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "lst_new" [Flapjack.CrepExp.const 24#64, Flapjack.CrepExp.const 2#64]

def crepBody371_23 : CrepProg (BitVec 64) :=
.seq crepBody371_21 crepBody371_22

def crepBody371_24 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 32#64]) crepBody371_16

def crepBody371_25 : CrepProg (BitVec 64) :=
.seq crepBody371_23 crepBody371_24

def crepBody371_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "htab_set"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 216#64]),
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]

def crepBody371_27 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody371_26

def crepBody371_28 : CrepProg (BitVec 64) :=
.seq crepBody371_25 crepBody371_27

def crepBody371_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody371_30 : CrepProg (BitVec 64) :=
.seq crepBody371_28 crepBody371_29

def crepBody371_31 : CrepProg (BitVec 64) :=
.seq crepBody371_13 crepBody371_30

def crepBody371_32 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody371_31

def crepBody371_33 : CrepProg (BitVec 64) :=
.seq crepBody371_12 crepBody371_32

def crepBody371_34 : CrepProg (BitVec 64) :=
.seq crepBody371_5 crepBody371_33

def crepBody371_35 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody371_34

def crepBody371_36 : CrepProg (BitVec 64) :=
.seq crepBody371_4 crepBody371_35

def crepBody371_37 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody371_36

def crepBody371_38 : CrepProg (BitVec 64) :=
.seq crepBody371_3 crepBody371_37

def crepBody371_39 : CrepProg (BitVec 64) :=
.seq crepBody371_0 crepBody371_38

def crepBody371_40 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody371_39

def crepBody371_41 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody371_40

def data371 : CrepProg (BitVec 64) := crepBody371_41
def output371 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 97#8, 108#8, 95#8, 101#8, 110#8, 115#8, 117#8, 114#8, 101#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8,
    116#8], [0], crepProgToHOL data371)
end InitECandidate.Proofs.FrontendStages.Crep
