import InitECandidate.Proofs.FrontendStages.Crep.Translate650
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody666_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27, 28, 29, 30, 31, 32], none)) "bls_fp_add"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20]

def crepBody666_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([33, 34, 35, 36, 37, 38], none)) "bls_fp_add"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12,
    Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22,
    Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26]

def crepBody666_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 39) (Flapjack.CrepExp.var 40)

def crepBody666_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 39, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 41)

def crepBody666_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 39, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 42)

def crepBody666_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 39, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 43)

def crepBody666_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 39, Flapjack.CrepExp.const 32#64])
  (Flapjack.CrepExp.var 44)

def crepBody666_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 39, Flapjack.CrepExp.const 40#64])
  (Flapjack.CrepExp.var 45)

def crepBody666_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody666_9 : CrepProg (BitVec 64) :=
.seq crepBody666_7 crepBody666_8

def crepBody666_10 : CrepProg (BitVec 64) :=
.seq crepBody666_6 crepBody666_9

def crepBody666_11 : CrepProg (BitVec 64) :=
.seq crepBody666_5 crepBody666_10

def crepBody666_12 : CrepProg (BitVec 64) :=
.seq crepBody666_4 crepBody666_11

def crepBody666_13 : CrepProg (BitVec 64) :=
.seq crepBody666_3 crepBody666_12

def crepBody666_14 : CrepProg (BitVec 64) :=
.seq crepBody666_2 crepBody666_13

def crepBody666_15 : CrepProg (BitVec 64) :=
.dec 45 (Flapjack.CrepExp.var 32) crepBody666_14

def crepBody666_16 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.var 31) crepBody666_15

def crepBody666_17 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.var 30) crepBody666_16

def crepBody666_18 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.var 29) crepBody666_17

def crepBody666_19 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.var 28) crepBody666_18

def crepBody666_20 : CrepProg (BitVec 64) :=
.dec 40 (Flapjack.CrepExp.var 27) crepBody666_19

def crepBody666_21 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.var 0) crepBody666_20

def crepBody666_22 : CrepProg (BitVec 64) :=
.dec 45 (Flapjack.CrepExp.var 38) crepBody666_14

def crepBody666_23 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.var 37) crepBody666_22

def crepBody666_24 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.var 36) crepBody666_23

def crepBody666_25 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.var 35) crepBody666_24

def crepBody666_26 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.var 34) crepBody666_25

def crepBody666_27 : CrepProg (BitVec 64) :=
.dec 40 (Flapjack.CrepExp.var 33) crepBody666_26

def crepBody666_28 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]) crepBody666_27

def crepBody666_29 : CrepProg (BitVec 64) :=
.seq crepBody666_21 crepBody666_28

def crepBody666_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody666_31 : CrepProg (BitVec 64) :=
.seq crepBody666_29 crepBody666_30

def crepBody666_32 : CrepProg (BitVec 64) :=
.seq crepBody666_1 crepBody666_31

def crepBody666_33 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 0#64) crepBody666_32

def crepBody666_34 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody666_33

def crepBody666_35 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody666_34

def crepBody666_36 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.const 0#64) crepBody666_35

def crepBody666_37 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 0#64) crepBody666_36

def crepBody666_38 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 0#64) crepBody666_37

def crepBody666_39 : CrepProg (BitVec 64) :=
.seq crepBody666_0 crepBody666_38

def crepBody666_40 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody666_39

def crepBody666_41 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody666_40

def crepBody666_42 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.const 0#64) crepBody666_41

def crepBody666_43 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody666_42

def crepBody666_44 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody666_43

def crepBody666_45 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody666_44

def crepBody666_46 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 40#64])) crepBody666_45

def crepBody666_47 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 32#64])) crepBody666_46

def crepBody666_48 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 24#64])) crepBody666_47

def crepBody666_49 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 16#64])) crepBody666_48

def crepBody666_50 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 8#64])) crepBody666_49

def crepBody666_51 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 48#64])) crepBody666_50

def crepBody666_52 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 40#64])) crepBody666_51

def crepBody666_53 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64])) crepBody666_52

def crepBody666_54 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 24#64])) crepBody666_53

def crepBody666_55 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64])) crepBody666_54

def crepBody666_56 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64])) crepBody666_55

def crepBody666_57 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 2)) crepBody666_56

def crepBody666_58 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 40#64])) crepBody666_57

def crepBody666_59 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 32#64])) crepBody666_58

def crepBody666_60 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 24#64])) crepBody666_59

def crepBody666_61 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 16#64])) crepBody666_60

def crepBody666_62 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 8#64])) crepBody666_61

def crepBody666_63 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64])) crepBody666_62

def crepBody666_64 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64])) crepBody666_63

def crepBody666_65 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])) crepBody666_64

def crepBody666_66 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])) crepBody666_65

def crepBody666_67 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64])) crepBody666_66

def crepBody666_68 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody666_67

def crepBody666_69 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 1)) crepBody666_68

def data666 : CrepProg (BitVec 64) := crepBody666_69
def output666 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 97#8, 100#8, 100#8], [0, 1, 2], crepProgToHOL data666)
end InitECandidate.Proofs.FrontendStages.Crep
