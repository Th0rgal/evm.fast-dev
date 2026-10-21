import InitECandidate.Proofs.FrontendStages.Crep.Translate658
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody674_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20, 21, 22, 23, 24, 25], none)) "bls_fp_mul"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody674_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26, 27, 28, 29, 30, 31], none)) "bls_fp_mul"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17,
    Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody674_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 32) (Flapjack.CrepExp.var 33)

def crepBody674_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 32, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 34)

def crepBody674_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 32, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 35)

def crepBody674_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 32, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 36)

def crepBody674_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 32, Flapjack.CrepExp.const 32#64])
  (Flapjack.CrepExp.var 37)

def crepBody674_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 32, Flapjack.CrepExp.const 40#64])
  (Flapjack.CrepExp.var 38)

def crepBody674_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody674_9 : CrepProg (BitVec 64) :=
.seq crepBody674_7 crepBody674_8

def crepBody674_10 : CrepProg (BitVec 64) :=
.seq crepBody674_6 crepBody674_9

def crepBody674_11 : CrepProg (BitVec 64) :=
.seq crepBody674_5 crepBody674_10

def crepBody674_12 : CrepProg (BitVec 64) :=
.seq crepBody674_4 crepBody674_11

def crepBody674_13 : CrepProg (BitVec 64) :=
.seq crepBody674_3 crepBody674_12

def crepBody674_14 : CrepProg (BitVec 64) :=
.seq crepBody674_2 crepBody674_13

def crepBody674_15 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.var 25) crepBody674_14

def crepBody674_16 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.var 24) crepBody674_15

def crepBody674_17 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.var 23) crepBody674_16

def crepBody674_18 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.var 22) crepBody674_17

def crepBody674_19 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.var 21) crepBody674_18

def crepBody674_20 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.var 20) crepBody674_19

def crepBody674_21 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.var 0) crepBody674_20

def crepBody674_22 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.var 31) crepBody674_14

def crepBody674_23 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.var 30) crepBody674_22

def crepBody674_24 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.var 29) crepBody674_23

def crepBody674_25 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.var 28) crepBody674_24

def crepBody674_26 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.var 27) crepBody674_25

def crepBody674_27 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.var 26) crepBody674_26

def crepBody674_28 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]) crepBody674_27

def crepBody674_29 : CrepProg (BitVec 64) :=
.seq crepBody674_21 crepBody674_28

def crepBody674_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody674_31 : CrepProg (BitVec 64) :=
.seq crepBody674_29 crepBody674_30

def crepBody674_32 : CrepProg (BitVec 64) :=
.seq crepBody674_1 crepBody674_31

def crepBody674_33 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody674_32

def crepBody674_34 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.const 0#64) crepBody674_33

def crepBody674_35 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody674_34

def crepBody674_36 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody674_35

def crepBody674_37 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody674_36

def crepBody674_38 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody674_37

def crepBody674_39 : CrepProg (BitVec 64) :=
.seq crepBody674_0 crepBody674_38

def crepBody674_40 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody674_39

def crepBody674_41 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody674_40

def crepBody674_42 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody674_41

def crepBody674_43 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody674_42

def crepBody674_44 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody674_43

def crepBody674_45 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody674_44

def crepBody674_46 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 40#64])) crepBody674_45

def crepBody674_47 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 32#64])) crepBody674_46

def crepBody674_48 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 24#64])) crepBody674_47

def crepBody674_49 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 16#64])) crepBody674_48

def crepBody674_50 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 8#64])) crepBody674_49

def crepBody674_51 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64])) crepBody674_50

def crepBody674_52 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64])) crepBody674_51

def crepBody674_53 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])) crepBody674_52

def crepBody674_54 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])) crepBody674_53

def crepBody674_55 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64])) crepBody674_54

def crepBody674_56 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody674_55

def crepBody674_57 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 1)) crepBody674_56

def data674 : CrepProg (BitVec 64) := crepBody674_57
def output674 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 115#8, 99#8, 97#8, 108#8, 101#8], [0, 1, 2, 3, 4, 5, 6, 7], crepProgToHOL data674)
end InitECandidate.Proofs.FrontendStages.Crep
