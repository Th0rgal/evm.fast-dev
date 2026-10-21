import InitECandidate.Proofs.FrontendStages.Crep.Translate542
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody558_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody558_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody558_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody558_0 crepBody558_1

def crepBody558_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 160#64]

def crepBody558_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody558_5 : CrepProg (BitVec 64) :=
.seq crepBody558_4 crepBody558_1

def crepBody558_6 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.var 1) crepBody558_5

def crepBody558_7 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]) crepBody558_6

def crepBody558_8 : CrepProg (BitVec 64) :=
.seq crepBody558_3 crepBody558_7

def crepBody558_9 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody558_8

def crepBody558_10 : CrepProg (BitVec 64) :=
.seq crepBody558_2 crepBody558_9

def crepBody558_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 128#64]

def crepBody558_12 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 328#64]) crepBody558_6

def crepBody558_13 : CrepProg (BitVec 64) :=
.seq crepBody558_11 crepBody558_12

def crepBody558_14 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody558_13

def crepBody558_15 : CrepProg (BitVec 64) :=
.seq crepBody558_10 crepBody558_14

def crepBody558_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 40#64]

def crepBody558_17 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 336#64]) crepBody558_6

def crepBody558_18 : CrepProg (BitVec 64) :=
.seq crepBody558_16 crepBody558_17

def crepBody558_19 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody558_18

def crepBody558_20 : CrepProg (BitVec 64) :=
.seq crepBody558_15 crepBody558_19

def crepBody558_21 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 344#64]) crepBody558_6

def crepBody558_22 : CrepProg (BitVec 64) :=
.seq crepBody558_11 crepBody558_21

def crepBody558_23 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody558_22

def crepBody558_24 : CrepProg (BitVec 64) :=
.seq crepBody558_20 crepBody558_23

def crepBody558_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 2)

def crepBody558_26 : CrepProg (BitVec 64) :=
.seq crepBody558_25 crepBody558_1

def crepBody558_27 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 18364758544493064720#64) crepBody558_26

def crepBody558_28 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 0#64]) crepBody558_27

def crepBody558_29 : CrepProg (BitVec 64) :=
.seq crepBody558_24 crepBody558_28

def crepBody558_30 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 10079716825146989895#64) crepBody558_26

def crepBody558_31 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 8#64]) crepBody558_30

def crepBody558_32 : CrepProg (BitVec 64) :=
.seq crepBody558_29 crepBody558_31

def crepBody558_33 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 14248650839231647395#64) crepBody558_26

def crepBody558_34 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 16#64]) crepBody558_33

def crepBody558_35 : CrepProg (BitVec 64) :=
.seq crepBody558_32 crepBody558_34

def crepBody558_36 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 2764919063900629905#64) crepBody558_26

def crepBody558_37 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 24#64]) crepBody558_36

def crepBody558_38 : CrepProg (BitVec 64) :=
.seq crepBody558_35 crepBody558_37

def crepBody558_39 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 16099105460569216260#64) crepBody558_26

def crepBody558_40 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 32#64]) crepBody558_39

def crepBody558_41 : CrepProg (BitVec 64) :=
.seq crepBody558_38 crepBody558_40

def crepBody558_42 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 14096706008221550565#64) crepBody558_26

def crepBody558_43 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 40#64]) crepBody558_42

def crepBody558_44 : CrepProg (BitVec 64) :=
.seq crepBody558_41 crepBody558_43

def crepBody558_45 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 2419779895833949110#64) crepBody558_26

def crepBody558_46 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 48#64]) crepBody558_45

def crepBody558_47 : CrepProg (BitVec 64) :=
.seq crepBody558_44 crepBody558_46

def crepBody558_48 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 15279073663851639135#64) crepBody558_26

def crepBody558_49 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 56#64]) crepBody558_48

def crepBody558_50 : CrepProg (BitVec 64) :=
.seq crepBody558_47 crepBody558_49

def crepBody558_51 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 16895767220870911080#64) crepBody558_26

def crepBody558_52 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 64#64]) crepBody558_51

def crepBody558_53 : CrepProg (BitVec 64) :=
.seq crepBody558_50 crepBody558_52

def crepBody558_54 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 13344426445381913340#64) crepBody558_26

def crepBody558_55 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 72#64]) crepBody558_54

def crepBody558_56 : CrepProg (BitVec 64) :=
.seq crepBody558_53 crepBody558_55

def crepBody558_57 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 9905384649541406699#64) crepBody558_26

def crepBody558_58 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 80#64]) crepBody558_57

def crepBody558_59 : CrepProg (BitVec 64) :=
.seq crepBody558_56 crepBody558_58

def crepBody558_60 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 14806603881112131687#64) crepBody558_26

def crepBody558_61 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 88#64]) crepBody558_60

def crepBody558_62 : CrepProg (BitVec 64) :=
.seq crepBody558_59 crepBody558_61

def crepBody558_63 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 6324581712619534043#64) crepBody558_26

def crepBody558_64 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 96#64]) crepBody558_63

def crepBody558_65 : CrepProg (BitVec 64) :=
.seq crepBody558_62 crepBody558_64

def crepBody558_66 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 14224731476766686923#64) crepBody558_26

def crepBody558_67 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 104#64]) crepBody558_66

def crepBody558_68 : CrepProg (BitVec 64) :=
.seq crepBody558_65 crepBody558_67

def crepBody558_69 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 7317203453406000633#64) crepBody558_26

def crepBody558_70 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 112#64]) crepBody558_69

def crepBody558_71 : CrepProg (BitVec 64) :=
.seq crepBody558_68 crepBody558_70

def crepBody558_72 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 7849414023404435864#64) crepBody558_26

def crepBody558_73 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 120#64]) crepBody558_72

def crepBody558_74 : CrepProg (BitVec 64) :=
.seq crepBody558_71 crepBody558_73

def crepBody558_75 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 13688264971095146457#64) crepBody558_26

def crepBody558_76 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 128#64]) crepBody558_75

def crepBody558_77 : CrepProg (BitVec 64) :=
.seq crepBody558_74 crepBody558_76

def crepBody558_78 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 6331469388073975673#64) crepBody558_26

def crepBody558_79 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 136#64]) crepBody558_78

def crepBody558_80 : CrepProg (BitVec 64) :=
.seq crepBody558_77 crepBody558_79

def crepBody558_81 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 10330303817214507103#64) crepBody558_26

def crepBody558_82 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 144#64]) crepBody558_81

def crepBody558_83 : CrepProg (BitVec 64) :=
.seq crepBody558_80 crepBody558_82

def crepBody558_84 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 13537634492463488088#64) crepBody558_26

def crepBody558_85 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.const 152#64]) crepBody558_84

def crepBody558_86 : CrepProg (BitVec 64) :=
.seq crepBody558_83 crepBody558_85

def crepBody558_87 : CrepProg (BitVec 64) :=
.seq crepBody558_86 crepBody558_0

def data558 : CrepProg (BitVec 64) := crepBody558_87
def output558 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 105#8, 112#8, 101#8, 109#8, 100#8, 49#8, 54#8, 48#8, 95#8, 105#8, 110#8, 105#8, 116#8], [], crepProgToHOL data558)
end InitECandidate.Proofs.FrontendStages.Crep
