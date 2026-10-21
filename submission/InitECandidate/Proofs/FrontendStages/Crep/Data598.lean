import InitECandidate.Proofs.FrontendStages.Crep.Translate582
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody598_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19, 20, 21, 22], none)) "fq_mul"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody598_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23, 24, 25, 26], none)) "fq_mul"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18]

def crepBody598_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27, 28, 29, 30], none)) "fq_mul"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18]

def crepBody598_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([31, 32, 33, 34], none)) "fq_mul"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody598_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([35, 36, 37, 38], none)) "fq_sub"
  [Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22,
    Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26]

def crepBody598_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([39, 40, 41, 42], none)) "fq_add"
  [Flapjack.CrepExp.var 27, Flapjack.CrepExp.var 28, Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30,
    Flapjack.CrepExp.var 31, Flapjack.CrepExp.var 32, Flapjack.CrepExp.var 33, Flapjack.CrepExp.var 34]

def crepBody598_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 43) (Flapjack.CrepExp.var 44)

def crepBody598_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 43, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 45)

def crepBody598_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 43, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 46)

def crepBody598_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 43, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 47)

def crepBody598_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody598_11 : CrepProg (BitVec 64) :=
.seq crepBody598_9 crepBody598_10

def crepBody598_12 : CrepProg (BitVec 64) :=
.seq crepBody598_8 crepBody598_11

def crepBody598_13 : CrepProg (BitVec 64) :=
.seq crepBody598_7 crepBody598_12

def crepBody598_14 : CrepProg (BitVec 64) :=
.seq crepBody598_6 crepBody598_13

def crepBody598_15 : CrepProg (BitVec 64) :=
.dec 47 (Flapjack.CrepExp.var 38) crepBody598_14

def crepBody598_16 : CrepProg (BitVec 64) :=
.dec 46 (Flapjack.CrepExp.var 37) crepBody598_15

def crepBody598_17 : CrepProg (BitVec 64) :=
.dec 45 (Flapjack.CrepExp.var 36) crepBody598_16

def crepBody598_18 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.var 35) crepBody598_17

def crepBody598_19 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.var 0) crepBody598_18

def crepBody598_20 : CrepProg (BitVec 64) :=
.dec 47 (Flapjack.CrepExp.var 42) crepBody598_14

def crepBody598_21 : CrepProg (BitVec 64) :=
.dec 46 (Flapjack.CrepExp.var 41) crepBody598_20

def crepBody598_22 : CrepProg (BitVec 64) :=
.dec 45 (Flapjack.CrepExp.var 40) crepBody598_21

def crepBody598_23 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.var 39) crepBody598_22

def crepBody598_24 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]) crepBody598_23

def crepBody598_25 : CrepProg (BitVec 64) :=
.seq crepBody598_19 crepBody598_24

def crepBody598_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody598_27 : CrepProg (BitVec 64) :=
.seq crepBody598_25 crepBody598_26

def crepBody598_28 : CrepProg (BitVec 64) :=
.seq crepBody598_5 crepBody598_27

def crepBody598_29 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.const 0#64) crepBody598_28

def crepBody598_30 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.const 0#64) crepBody598_29

def crepBody598_31 : CrepProg (BitVec 64) :=
.dec 40 (Flapjack.CrepExp.const 0#64) crepBody598_30

def crepBody598_32 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.const 0#64) crepBody598_31

def crepBody598_33 : CrepProg (BitVec 64) :=
.seq crepBody598_4 crepBody598_32

def crepBody598_34 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 0#64) crepBody598_33

def crepBody598_35 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody598_34

def crepBody598_36 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody598_35

def crepBody598_37 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.const 0#64) crepBody598_36

def crepBody598_38 : CrepProg (BitVec 64) :=
.seq crepBody598_3 crepBody598_37

def crepBody598_39 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 0#64) crepBody598_38

def crepBody598_40 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 0#64) crepBody598_39

def crepBody598_41 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody598_40

def crepBody598_42 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody598_41

def crepBody598_43 : CrepProg (BitVec 64) :=
.seq crepBody598_2 crepBody598_42

def crepBody598_44 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.const 0#64) crepBody598_43

def crepBody598_45 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody598_44

def crepBody598_46 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody598_45

def crepBody598_47 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody598_46

def crepBody598_48 : CrepProg (BitVec 64) :=
.seq crepBody598_1 crepBody598_47

def crepBody598_49 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody598_48

def crepBody598_50 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody598_49

def crepBody598_51 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody598_50

def crepBody598_52 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody598_51

def crepBody598_53 : CrepProg (BitVec 64) :=
.seq crepBody598_0 crepBody598_52

def crepBody598_54 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody598_53

def crepBody598_55 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody598_54

def crepBody598_56 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody598_55

def crepBody598_57 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody598_56

def crepBody598_58 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 24#64])) crepBody598_57

def crepBody598_59 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 16#64])) crepBody598_58

def crepBody598_60 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 8#64])) crepBody598_59

def crepBody598_61 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64])) crepBody598_60

def crepBody598_62 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 24#64])) crepBody598_61

def crepBody598_63 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64])) crepBody598_62

def crepBody598_64 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64])) crepBody598_63

def crepBody598_65 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 2)) crepBody598_64

def crepBody598_66 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 24#64])) crepBody598_65

def crepBody598_67 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 16#64])) crepBody598_66

def crepBody598_68 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 8#64])) crepBody598_67

def crepBody598_69 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])) crepBody598_68

def crepBody598_70 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])) crepBody598_69

def crepBody598_71 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64])) crepBody598_70

def crepBody598_72 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody598_71

def crepBody598_73 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 1)) crepBody598_72

def data598 : CrepProg (BitVec 64) := crepBody598_73
def output598 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 113#8, 50#8, 95#8, 109#8, 117#8, 108#8], [0, 1, 2], crepProgToHOL data598)
end InitECandidate.Proofs.FrontendStages.Crep
