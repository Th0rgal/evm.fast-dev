import InitECandidate.Proofs.FrontendStages.Crep.Translate548
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody564_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody564_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody564_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody564_0 crepBody564_1

def crepBody564_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 80#64]

def crepBody564_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody564_5 : CrepProg (BitVec 64) :=
.seq crepBody564_4 crepBody564_1

def crepBody564_6 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.var 1) crepBody564_5

def crepBody564_7 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]) crepBody564_6

def crepBody564_8 : CrepProg (BitVec 64) :=
.seq crepBody564_3 crepBody564_7

def crepBody564_9 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody564_8

def crepBody564_10 : CrepProg (BitVec 64) :=
.seq crepBody564_2 crepBody564_9

def crepBody564_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody564_12 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 360#64]) crepBody564_6

def crepBody564_13 : CrepProg (BitVec 64) :=
.seq crepBody564_11 crepBody564_12

def crepBody564_14 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody564_13

def crepBody564_15 : CrepProg (BitVec 64) :=
.seq crepBody564_10 crepBody564_14

def crepBody564_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 128#64]

def crepBody564_17 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 368#64]) crepBody564_6

def crepBody564_18 : CrepProg (BitVec 64) :=
.seq crepBody564_16 crepBody564_17

def crepBody564_19 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody564_18

def crepBody564_20 : CrepProg (BitVec 64) :=
.seq crepBody564_15 crepBody564_19

def crepBody564_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 2)

def crepBody564_22 : CrepProg (BitVec 64) :=
.seq crepBody564_21 crepBody564_1

def crepBody564_23 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 18364758544493064720#64) crepBody564_22

def crepBody564_24 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.const 0#64]) crepBody564_23

def crepBody564_25 : CrepProg (BitVec 64) :=
.seq crepBody564_20 crepBody564_24

def crepBody564_26 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 3853709921291437230#64) crepBody564_22

def crepBody564_27 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.const 8#64]) crepBody564_26

def crepBody564_28 : CrepProg (BitVec 64) :=
.seq crepBody564_25 crepBody564_27

def crepBody564_29 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 5266788149650328715#64) crepBody564_22

def crepBody564_30 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.const 16#64]) crepBody564_29

def crepBody564_31 : CrepProg (BitVec 64) :=
.seq crepBody564_28 crepBody564_30

def crepBody564_32 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 10305543691612001175#64) crepBody564_22

def crepBody564_33 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.const 24#64]) crepBody564_32

def crepBody564_34 : CrepProg (BitVec 64) :=
.seq crepBody564_31 crepBody564_33

def crepBody564_35 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 15242093322790139145#64) crepBody564_22

def crepBody564_36 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.const 32#64]) crepBody564_35

def crepBody564_37 : CrepProg (BitVec 64) :=
.seq crepBody564_34 crepBody564_36

def crepBody564_38 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 10515720223929181890#64) crepBody564_22

def crepBody564_39 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.const 40#64]) crepBody564_38

def crepBody564_40 : CrepProg (BitVec 64) :=
.seq crepBody564_37 crepBody564_39

def crepBody564_41 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 13270197634454188380#64) crepBody564_22

def crepBody564_42 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.const 48#64]) crepBody564_41

def crepBody564_43 : CrepProg (BitVec 64) :=
.seq crepBody564_40 crepBody564_42

def crepBody564_44 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 11702690517083809725#64) crepBody564_22

def crepBody564_45 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.const 56#64]) crepBody564_44

def crepBody564_46 : CrepProg (BitVec 64) :=
.seq crepBody564_43 crepBody564_45

def crepBody564_47 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 6503616966983130870#64) crepBody564_22

def crepBody564_48 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.const 64#64]) crepBody564_47

def crepBody564_49 : CrepProg (BitVec 64) :=
.seq crepBody564_46 crepBody564_48

def crepBody564_50 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 991893350865389610#64) crepBody564_22

def crepBody564_51 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.const 72#64]) crepBody564_50

def crepBody564_52 : CrepProg (BitVec 64) :=
.seq crepBody564_49 crepBody564_51

def crepBody564_53 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 7640891576956012808#64) crepBody564_22

def crepBody564_54 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 360#64]),
    Flapjack.CrepExp.const 0#64]) crepBody564_53

def crepBody564_55 : CrepProg (BitVec 64) :=
.seq crepBody564_52 crepBody564_54

def crepBody564_56 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 13503953896175478587#64) crepBody564_22

def crepBody564_57 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 360#64]),
    Flapjack.CrepExp.const 8#64]) crepBody564_56

def crepBody564_58 : CrepProg (BitVec 64) :=
.seq crepBody564_55 crepBody564_57

def crepBody564_59 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 4354685564936845355#64) crepBody564_22

def crepBody564_60 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 360#64]),
    Flapjack.CrepExp.const 16#64]) crepBody564_59

def crepBody564_61 : CrepProg (BitVec 64) :=
.seq crepBody564_58 crepBody564_60

def crepBody564_62 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 11912009170470909681#64) crepBody564_22

def crepBody564_63 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 360#64]),
    Flapjack.CrepExp.const 24#64]) crepBody564_62

def crepBody564_64 : CrepProg (BitVec 64) :=
.seq crepBody564_61 crepBody564_63

def crepBody564_65 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 5840696475078001361#64) crepBody564_22

def crepBody564_66 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 360#64]),
    Flapjack.CrepExp.const 32#64]) crepBody564_65

def crepBody564_67 : CrepProg (BitVec 64) :=
.seq crepBody564_64 crepBody564_66

def crepBody564_68 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 11170449401992604703#64) crepBody564_22

def crepBody564_69 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 360#64]),
    Flapjack.CrepExp.const 40#64]) crepBody564_68

def crepBody564_70 : CrepProg (BitVec 64) :=
.seq crepBody564_67 crepBody564_69

def crepBody564_71 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 2270897969802886507#64) crepBody564_22

def crepBody564_72 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 360#64]),
    Flapjack.CrepExp.const 48#64]) crepBody564_71

def crepBody564_73 : CrepProg (BitVec 64) :=
.seq crepBody564_70 crepBody564_72

def crepBody564_74 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 6620516959819538809#64) crepBody564_22

def crepBody564_75 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 360#64]),
    Flapjack.CrepExp.const 56#64]) crepBody564_74

def crepBody564_76 : CrepProg (BitVec 64) :=
.seq crepBody564_73 crepBody564_75

def crepBody564_77 : CrepProg (BitVec 64) :=
.seq crepBody564_76 crepBody564_0

def data564 : CrepProg (BitVec 64) := crepBody564_77
def output564 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [98#8, 108#8, 97#8, 107#8, 101#8, 50#8, 95#8, 105#8, 110#8, 105#8, 116#8], [], crepProgToHOL data564)
end InitECandidate.Proofs.FrontendStages.Crep
