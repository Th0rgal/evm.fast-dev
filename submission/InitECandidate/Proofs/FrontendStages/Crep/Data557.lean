import InitECandidate.Proofs.FrontendStages.Crep.Translate541
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody557_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody557_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memzero" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]

def crepBody557_2 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody557_1

def crepBody557_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "account_deployable"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64])]

def crepBody557_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 5)

def crepBody557_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody557_6 : CrepProg (BitVec 64) :=
.seq crepBody557_4 crepBody557_5

def crepBody557_7 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 12#64) crepBody557_6

def crepBody557_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]) crepBody557_7

def crepBody557_9 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64])) crepBody557_6

def crepBody557_10 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64]) crepBody557_9

def crepBody557_11 : CrepProg (BitVec 64) :=
.seq crepBody557_8 crepBody557_10

def crepBody557_12 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64])) crepBody557_6

def crepBody557_13 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 64#64]) crepBody557_12

def crepBody557_14 : CrepProg (BitVec 64) :=
.seq crepBody557_11 crepBody557_13

def crepBody557_15 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 264#64])) crepBody557_6

def crepBody557_16 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64]) crepBody557_15

def crepBody557_17 : CrepProg (BitVec 64) :=
.seq crepBody557_14 crepBody557_16

def crepBody557_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 1]

def crepBody557_19 : CrepProg (BitVec 64) :=
.seq crepBody557_17 crepBody557_18

def crepBody557_20 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody557_19 crepBody557_5

def crepBody557_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "process_create_message" [Flapjack.CrepExp.var 0]

def crepBody557_22 : CrepProg (BitVec 64) :=
.seq crepBody557_20 crepBody557_21

def crepBody557_23 : CrepProg (BitVec 64) :=
.seq crepBody557_3 crepBody557_22

def crepBody557_24 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody557_23

def crepBody557_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "process_message" [Flapjack.CrepExp.var 0]

def crepBody557_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody557_24 crepBody557_25

def crepBody557_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody557_28 : CrepProg (BitVec 64) :=
.seq crepBody557_27 crepBody557_5

def crepBody557_29 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64])) crepBody557_28

def crepBody557_30 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64]) crepBody557_29

def crepBody557_31 : CrepProg (BitVec 64) :=
.seq crepBody557_26 crepBody557_30

def crepBody557_32 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 160#64])) crepBody557_28

def crepBody557_33 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]) crepBody557_32

def crepBody557_34 : CrepProg (BitVec 64) :=
.seq crepBody557_31 crepBody557_33

def crepBody557_35 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 120#64])) crepBody557_28

def crepBody557_36 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64]) crepBody557_35

def crepBody557_37 : CrepProg (BitVec 64) :=
.seq crepBody557_34 crepBody557_36

def crepBody557_38 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 128#64])) crepBody557_28

def crepBody557_39 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64]) crepBody557_38

def crepBody557_40 : CrepProg (BitVec 64) :=
.seq crepBody557_37 crepBody557_39

def crepBody557_41 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 72#64])) crepBody557_28

def crepBody557_42 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64]) crepBody557_41

def crepBody557_43 : CrepProg (BitVec 64) :=
.seq crepBody557_40 crepBody557_42

def crepBody557_44 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 184#64])) crepBody557_28

def crepBody557_45 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 64#64]) crepBody557_44

def crepBody557_46 : CrepProg (BitVec 64) :=
.seq crepBody557_43 crepBody557_45

def crepBody557_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "frame_state_gas_used" [Flapjack.CrepExp.var 2]

def crepBody557_48 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 200#64])]) crepBody557_6

def crepBody557_49 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 72#64]) crepBody557_48

def crepBody557_50 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 88#64])) crepBody557_6

def crepBody557_51 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64]) crepBody557_50

def crepBody557_52 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 136#64])) crepBody557_6

def crepBody557_53 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64]) crepBody557_52

def crepBody557_54 : CrepProg (BitVec 64) :=
.seq crepBody557_51 crepBody557_53

def crepBody557_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.const 0#64)

def crepBody557_56 : CrepProg (BitVec 64) :=
.seq crepBody557_55 crepBody557_5

def crepBody557_57 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody557_56 crepBody557_5

def crepBody557_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody557_59 : CrepProg (BitVec 64) :=
.seq crepBody557_58 crepBody557_5

def crepBody557_60 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 4) crepBody557_59

def crepBody557_61 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64]) crepBody557_60

def crepBody557_62 : CrepProg (BitVec 64) :=
.seq crepBody557_57 crepBody557_61

def crepBody557_63 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 96#64])) crepBody557_62

def crepBody557_64 : CrepProg (BitVec 64) :=
.seq crepBody557_54 crepBody557_63

def crepBody557_65 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 160#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody557_64 crepBody557_5

def crepBody557_66 : CrepProg (BitVec 64) :=
.seq crepBody557_49 crepBody557_65

def crepBody557_67 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 208#64])) crepBody557_6

def crepBody557_68 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 80#64]) crepBody557_67

def crepBody557_69 : CrepProg (BitVec 64) :=
.seq crepBody557_66 crepBody557_68

def crepBody557_70 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 224#64])) crepBody557_6

def crepBody557_71 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]) crepBody557_70

def crepBody557_72 : CrepProg (BitVec 64) :=
.seq crepBody557_69 crepBody557_71

def crepBody557_73 : CrepProg (BitVec 64) :=
.seq crepBody557_72 crepBody557_18

def crepBody557_74 : CrepProg (BitVec 64) :=
.seq crepBody557_47 crepBody557_73

def crepBody557_75 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody557_74

def crepBody557_76 : CrepProg (BitVec 64) :=
.seq crepBody557_46 crepBody557_75

def crepBody557_77 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody557_76

def crepBody557_78 : CrepProg (BitVec 64) :=
.seq crepBody557_2 crepBody557_77

def crepBody557_79 : CrepProg (BitVec 64) :=
.seq crepBody557_0 crepBody557_78

def crepBody557_80 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody557_79

def data557 : CrepProg (BitVec 64) := crepBody557_80
def output557 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 109#8, 101#8, 115#8, 115#8, 97#8, 103#8, 101#8, 95#8, 99#8,
    97#8, 108#8, 108#8], [0], crepProgToHOL data557)
end InitECandidate.Proofs.FrontendStages.Crep
