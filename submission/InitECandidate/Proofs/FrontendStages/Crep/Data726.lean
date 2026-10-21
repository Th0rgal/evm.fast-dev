import InitECandidate.Proofs.FrontendStages.Crep.Translate710
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody726_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "g1_is_inf" [Flapjack.CrepExp.var 1]

def crepBody726_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody726_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody726_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 1#64)) crepBody726_1 crepBody726_2

def crepBody726_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "g2_is_inf" [Flapjack.CrepExp.var 2]

def crepBody726_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 1#64)) crepBody726_1 crepBody726_2

def crepBody726_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_mark" []

def crepBody726_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody726_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc" [Flapjack.CrepExp.const 192#64]

def crepBody726_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "alloc" [Flapjack.CrepExp.const 576#64]

def crepBody726_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "g1_normalize" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 1]

def crepBody726_11 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody726_10

def crepBody726_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "g2_normalize" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 2]

def crepBody726_13 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody726_12

def crepBody726_14 : CrepProg (BitVec 64) :=
.seq crepBody726_11 crepBody726_13

def crepBody726_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "pair_miller_loop"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19,
    Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 7]

def crepBody726_16 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody726_15

def crepBody726_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "fp12_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8]

def crepBody726_18 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody726_17

def crepBody726_19 : CrepProg (BitVec 64) :=
.seq crepBody726_16 crepBody726_18

def crepBody726_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "heap_release" [Flapjack.CrepExp.var 5]

def crepBody726_21 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody726_20

def crepBody726_22 : CrepProg (BitVec 64) :=
.seq crepBody726_19 crepBody726_21

def crepBody726_23 : CrepProg (BitVec 64) :=
.seq crepBody726_22 crepBody726_1

def crepBody726_24 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 40#64])) crepBody726_23

def crepBody726_25 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 32#64])) crepBody726_24

def crepBody726_26 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 24#64])) crepBody726_25

def crepBody726_27 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 16#64])) crepBody726_26

def crepBody726_28 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 8#64])) crepBody726_27

def crepBody726_29 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 48#64])) crepBody726_28

def crepBody726_30 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 40#64])) crepBody726_29

def crepBody726_31 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 32#64])) crepBody726_30

def crepBody726_32 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 24#64])) crepBody726_31

def crepBody726_33 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64])) crepBody726_32

def crepBody726_34 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64])) crepBody726_33

def crepBody726_35 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 6)) crepBody726_34

def crepBody726_36 : CrepProg (BitVec 64) :=
.seq crepBody726_14 crepBody726_35

def crepBody726_37 : CrepProg (BitVec 64) :=
.seq crepBody726_9 crepBody726_36

def crepBody726_38 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody726_37

def crepBody726_39 : CrepProg (BitVec 64) :=
.seq crepBody726_8 crepBody726_38

def crepBody726_40 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody726_39

def crepBody726_41 : CrepProg (BitVec 64) :=
.seq crepBody726_7 crepBody726_40

def crepBody726_42 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody726_41

def crepBody726_43 : CrepProg (BitVec 64) :=
.seq crepBody726_6 crepBody726_42

def crepBody726_44 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody726_43

def crepBody726_45 : CrepProg (BitVec 64) :=
.seq crepBody726_5 crepBody726_44

def crepBody726_46 : CrepProg (BitVec 64) :=
.seq crepBody726_4 crepBody726_45

def crepBody726_47 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody726_46

def crepBody726_48 : CrepProg (BitVec 64) :=
.seq crepBody726_3 crepBody726_47

def crepBody726_49 : CrepProg (BitVec 64) :=
.seq crepBody726_0 crepBody726_48

def crepBody726_50 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody726_49

def data726 : CrepProg (BitVec 64) := crepBody726_50
def output726 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 97#8, 105#8, 114#8, 95#8, 97#8, 99#8, 99#8, 117#8, 109#8, 117#8, 108#8, 97#8, 116#8, 101#8], [0, 1, 2], crepProgToHOL data726)
end InitECandidate.Proofs.FrontendStages.Crep
