import InitECandidate.Proofs.FrontendStages.Crep.Translate685
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody701_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9, 10, 11, 12, 13], none)) "bls_fp_neg"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody701_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 26) (Flapjack.CrepExp.var 27)

def crepBody701_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 28)

def crepBody701_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 29)

def crepBody701_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 30)

def crepBody701_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 32#64])
  (Flapjack.CrepExp.var 31)

def crepBody701_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 40#64])
  (Flapjack.CrepExp.var 32)

def crepBody701_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody701_8 : CrepProg (BitVec 64) :=
.seq crepBody701_6 crepBody701_7

def crepBody701_9 : CrepProg (BitVec 64) :=
.seq crepBody701_5 crepBody701_8

def crepBody701_10 : CrepProg (BitVec 64) :=
.seq crepBody701_4 crepBody701_9

def crepBody701_11 : CrepProg (BitVec 64) :=
.seq crepBody701_3 crepBody701_10

def crepBody701_12 : CrepProg (BitVec 64) :=
.seq crepBody701_2 crepBody701_11

def crepBody701_13 : CrepProg (BitVec 64) :=
.seq crepBody701_1 crepBody701_12

def crepBody701_14 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.var 19) crepBody701_13

def crepBody701_15 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.var 18) crepBody701_14

def crepBody701_16 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.var 17) crepBody701_15

def crepBody701_17 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.var 16) crepBody701_16

def crepBody701_18 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.var 15) crepBody701_17

def crepBody701_19 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.var 14) crepBody701_18

def crepBody701_20 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.var 0) crepBody701_19

def crepBody701_21 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.var 25) crepBody701_13

def crepBody701_22 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.var 24) crepBody701_21

def crepBody701_23 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.var 23) crepBody701_22

def crepBody701_24 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.var 22) crepBody701_23

def crepBody701_25 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.var 21) crepBody701_24

def crepBody701_26 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.var 20) crepBody701_25

def crepBody701_27 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64]) crepBody701_26

def crepBody701_28 : CrepProg (BitVec 64) :=
.seq crepBody701_20 crepBody701_27

def crepBody701_29 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
      Flapjack.CrepExp.const 40#64])) crepBody701_28

def crepBody701_30 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
      Flapjack.CrepExp.const 32#64])) crepBody701_29

def crepBody701_31 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
      Flapjack.CrepExp.const 24#64])) crepBody701_30

def crepBody701_32 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
      Flapjack.CrepExp.const 16#64])) crepBody701_31

def crepBody701_33 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
      Flapjack.CrepExp.const 8#64])) crepBody701_32

def crepBody701_34 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody701_33

def crepBody701_35 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64])) crepBody701_34

def crepBody701_36 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])) crepBody701_35

def crepBody701_37 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])) crepBody701_36

def crepBody701_38 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64])) crepBody701_37

def crepBody701_39 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody701_38

def crepBody701_40 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 1)) crepBody701_39

def crepBody701_41 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.var 1)) crepBody701_40 crepBody701_7

def crepBody701_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 15)

def crepBody701_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 16)

def crepBody701_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 17)

def crepBody701_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 18)

def crepBody701_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 32#64])
  (Flapjack.CrepExp.var 19)

def crepBody701_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 40#64])
  (Flapjack.CrepExp.var 20)

def crepBody701_48 : CrepProg (BitVec 64) :=
.seq crepBody701_47 crepBody701_7

def crepBody701_49 : CrepProg (BitVec 64) :=
.seq crepBody701_46 crepBody701_48

def crepBody701_50 : CrepProg (BitVec 64) :=
.seq crepBody701_45 crepBody701_49

def crepBody701_51 : CrepProg (BitVec 64) :=
.seq crepBody701_44 crepBody701_50

def crepBody701_52 : CrepProg (BitVec 64) :=
.seq crepBody701_43 crepBody701_51

def crepBody701_53 : CrepProg (BitVec 64) :=
.seq crepBody701_42 crepBody701_52

def crepBody701_54 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 13) crepBody701_53

def crepBody701_55 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.var 12) crepBody701_54

def crepBody701_56 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 11) crepBody701_55

def crepBody701_57 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 10) crepBody701_56

def crepBody701_58 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 9) crepBody701_57

def crepBody701_59 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 8) crepBody701_58

def crepBody701_60 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]) crepBody701_59

def crepBody701_61 : CrepProg (BitVec 64) :=
.seq crepBody701_41 crepBody701_60

def crepBody701_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody701_63 : CrepProg (BitVec 64) :=
.seq crepBody701_61 crepBody701_62

def crepBody701_64 : CrepProg (BitVec 64) :=
.seq crepBody701_0 crepBody701_63

def crepBody701_65 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody701_64

def crepBody701_66 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody701_65

def crepBody701_67 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody701_66

def crepBody701_68 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody701_67

def crepBody701_69 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody701_68

def crepBody701_70 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody701_69

def crepBody701_71 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 40#64])) crepBody701_70

def crepBody701_72 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 32#64])) crepBody701_71

def crepBody701_73 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 24#64])) crepBody701_72

def crepBody701_74 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 16#64])) crepBody701_73

def crepBody701_75 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 8#64])) crepBody701_74

def crepBody701_76 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64])) crepBody701_75

def data701 : CrepProg (BitVec 64) := crepBody701_76
def output701 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 110#8, 101#8, 103#8], [0, 1], crepProgToHOL data701)
end InitECandidate.Proofs.FrontendStages.Crep
