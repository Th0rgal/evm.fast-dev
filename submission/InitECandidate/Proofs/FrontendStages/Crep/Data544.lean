import InitECandidate.Proofs.FrontendStages.Crep.Translate528
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody544_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "msg_new_scratch" []

def crepBody544_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.var 20)

def crepBody544_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody544_3 : CrepProg (BitVec 64) :=
.seq crepBody544_1 crepBody544_2

def crepBody544_4 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 0#64])) crepBody544_3

def crepBody544_5 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 0#64]) crepBody544_4

def crepBody544_6 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 8#64])) crepBody544_3

def crepBody544_7 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 8#64]) crepBody544_6

def crepBody544_8 : CrepProg (BitVec 64) :=
.seq crepBody544_5 crepBody544_7

def crepBody544_9 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 0) crepBody544_3

def crepBody544_10 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 16#64]) crepBody544_9

def crepBody544_11 : CrepProg (BitVec 64) :=
.seq crepBody544_8 crepBody544_10

def crepBody544_12 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 1) crepBody544_3

def crepBody544_13 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 24#64]) crepBody544_12

def crepBody544_14 : CrepProg (BitVec 64) :=
.seq crepBody544_11 crepBody544_13

def crepBody544_15 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 2) crepBody544_3

def crepBody544_16 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 32#64]) crepBody544_15

def crepBody544_17 : CrepProg (BitVec 64) :=
.seq crepBody544_14 crepBody544_16

def crepBody544_18 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 3) crepBody544_3

def crepBody544_19 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 40#64]) crepBody544_18

def crepBody544_20 : CrepProg (BitVec 64) :=
.seq crepBody544_17 crepBody544_19

def crepBody544_21 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 4) crepBody544_3

def crepBody544_22 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 48#64]) crepBody544_21

def crepBody544_23 : CrepProg (BitVec 64) :=
.seq crepBody544_20 crepBody544_22

def crepBody544_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 21)

def crepBody544_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 22)

def crepBody544_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 23)

def crepBody544_27 : CrepProg (BitVec 64) :=
.seq crepBody544_26 crepBody544_2

def crepBody544_28 : CrepProg (BitVec 64) :=
.seq crepBody544_25 crepBody544_27

def crepBody544_29 : CrepProg (BitVec 64) :=
.seq crepBody544_24 crepBody544_28

def crepBody544_30 : CrepProg (BitVec 64) :=
.seq crepBody544_1 crepBody544_29

def crepBody544_31 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.var 8) crepBody544_30

def crepBody544_32 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 7) crepBody544_31

def crepBody544_33 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 6) crepBody544_32

def crepBody544_34 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 5) crepBody544_33

def crepBody544_35 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 56#64]) crepBody544_34

def crepBody544_36 : CrepProg (BitVec 64) :=
.seq crepBody544_23 crepBody544_35

def crepBody544_37 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 9) crepBody544_3

def crepBody544_38 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 88#64]) crepBody544_37

def crepBody544_39 : CrepProg (BitVec 64) :=
.seq crepBody544_36 crepBody544_38

def crepBody544_40 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 10) crepBody544_3

def crepBody544_41 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 96#64]) crepBody544_40

def crepBody544_42 : CrepProg (BitVec 64) :=
.seq crepBody544_39 crepBody544_41

def crepBody544_43 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 11) crepBody544_3

def crepBody544_44 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 104#64]) crepBody544_43

def crepBody544_45 : CrepProg (BitVec 64) :=
.seq crepBody544_42 crepBody544_44

def crepBody544_46 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 12) crepBody544_3

def crepBody544_47 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 112#64]) crepBody544_46

def crepBody544_48 : CrepProg (BitVec 64) :=
.seq crepBody544_45 crepBody544_47

def crepBody544_49 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 13) crepBody544_3

def crepBody544_50 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 120#64]) crepBody544_49

def crepBody544_51 : CrepProg (BitVec 64) :=
.seq crepBody544_48 crepBody544_50

def crepBody544_52 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 128#64]),
    Flapjack.CrepExp.const 1#64]) crepBody544_3

def crepBody544_53 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 128#64]) crepBody544_52

def crepBody544_54 : CrepProg (BitVec 64) :=
.seq crepBody544_51 crepBody544_53

def crepBody544_55 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 14) crepBody544_3

def crepBody544_56 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 136#64]) crepBody544_55

def crepBody544_57 : CrepProg (BitVec 64) :=
.seq crepBody544_54 crepBody544_56

def crepBody544_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 19 (Flapjack.CrepExp.const 1#64)

def crepBody544_59 : CrepProg (BitVec 64) :=
.seq crepBody544_58 crepBody544_2

def crepBody544_60 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 144#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody544_59 crepBody544_2

def crepBody544_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.var 21)

def crepBody544_62 : CrepProg (BitVec 64) :=
.seq crepBody544_61 crepBody544_2

def crepBody544_63 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 19) crepBody544_62

def crepBody544_64 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 144#64]) crepBody544_63

def crepBody544_65 : CrepProg (BitVec 64) :=
.seq crepBody544_60 crepBody544_64

def crepBody544_66 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 168#64])) crepBody544_62

def crepBody544_67 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 152#64]) crepBody544_66

def crepBody544_68 : CrepProg (BitVec 64) :=
.seq crepBody544_65 crepBody544_67

def crepBody544_69 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 176#64])) crepBody544_62

def crepBody544_70 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 160#64]) crepBody544_69

def crepBody544_71 : CrepProg (BitVec 64) :=
.seq crepBody544_68 crepBody544_70

def crepBody544_72 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 16) crepBody544_62

def crepBody544_73 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 168#64]) crepBody544_72

def crepBody544_74 : CrepProg (BitVec 64) :=
.seq crepBody544_71 crepBody544_73

def crepBody544_75 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 18]

def crepBody544_76 : CrepProg (BitVec 64) :=
.seq crepBody544_74 crepBody544_75

def crepBody544_77 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.var 15) crepBody544_76

def crepBody544_78 : CrepProg (BitVec 64) :=
.seq crepBody544_57 crepBody544_77

def crepBody544_79 : CrepProg (BitVec 64) :=
.seq crepBody544_0 crepBody544_78

def crepBody544_80 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody544_79

def crepBody544_81 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody544_80

def data544 : CrepProg (BitVec 64) := crepBody544_81
def output544 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 104#8, 105#8, 108#8, 100#8, 95#8, 109#8, 101#8, 115#8, 115#8, 97#8, 103#8, 101#8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], crepProgToHOL data544)
end InitECandidate.Proofs.FrontendStages.Crep
