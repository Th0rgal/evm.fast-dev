import InitECandidate.Proofs.FrontendStages.Crep.Translate405
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody421_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "scratch_mark" []

def crepBody421_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "frame_mem_mark" []

def crepBody421_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "scratch_alloc" [Flapjack.CrepExp.const 280#64]

def crepBody421_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "memzero" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 280#64]

def crepBody421_4 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody421_3

def crepBody421_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "scratch_alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 32#64]]

def crepBody421_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody421_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody421_8 : CrepProg (BitVec 64) :=
.seq crepBody421_6 crepBody421_7

def crepBody421_9 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 1) crepBody421_8

def crepBody421_10 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 208#64]) crepBody421_9

def crepBody421_11 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 4) crepBody421_8

def crepBody421_12 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]) crepBody421_11

def crepBody421_13 : CrepProg (BitVec 64) :=
.seq crepBody421_10 crepBody421_12

def crepBody421_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 32#64) crepBody421_8

def crepBody421_15 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 232#64]) crepBody421_14

def crepBody421_16 : CrepProg (BitVec 64) :=
.seq crepBody421_13 crepBody421_15

def crepBody421_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "frame_mem_alloc" [Flapjack.CrepExp.const 1024#64]

def crepBody421_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody421_19 : CrepProg (BitVec 64) :=
.seq crepBody421_18 crepBody421_7

def crepBody421_20 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 2) crepBody421_19

def crepBody421_21 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 224#64]) crepBody421_20

def crepBody421_22 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 5) crepBody421_19

def crepBody421_23 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64]) crepBody421_22

def crepBody421_24 : CrepProg (BitVec 64) :=
.seq crepBody421_21 crepBody421_23

def crepBody421_25 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 1024#64) crepBody421_19

def crepBody421_26 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 40#64]) crepBody421_25

def crepBody421_27 : CrepProg (BitVec 64) :=
.seq crepBody421_24 crepBody421_26

def crepBody421_28 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64])) crepBody421_19

def crepBody421_29 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 48#64]) crepBody421_28

def crepBody421_30 : CrepProg (BitVec 64) :=
.seq crepBody421_27 crepBody421_29

def crepBody421_31 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 120#64])) crepBody421_19

def crepBody421_32 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 56#64]) crepBody421_31

def crepBody421_33 : CrepProg (BitVec 64) :=
.seq crepBody421_30 crepBody421_32

def crepBody421_34 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64])) crepBody421_19

def crepBody421_35 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]) crepBody421_34

def crepBody421_36 : CrepProg (BitVec 64) :=
.seq crepBody421_33 crepBody421_35

def crepBody421_37 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64])) crepBody421_19

def crepBody421_38 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 72#64]) crepBody421_37

def crepBody421_39 : CrepProg (BitVec 64) :=
.seq crepBody421_36 crepBody421_38

def crepBody421_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "compute_jumpdests"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 120#64])]

def crepBody421_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 8)

def crepBody421_42 : CrepProg (BitVec 64) :=
.seq crepBody421_41 crepBody421_7

def crepBody421_43 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 6) crepBody421_42

def crepBody421_44 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 80#64]) crepBody421_43

def crepBody421_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "lst_new_scratch" [Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 4#64]

def crepBody421_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody421_47 : CrepProg (BitVec 64) :=
.seq crepBody421_46 crepBody421_7

def crepBody421_48 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 7) crepBody421_47

def crepBody421_49 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 88#64]) crepBody421_48

def crepBody421_50 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 1#64) crepBody421_47

def crepBody421_51 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 104#64]) crepBody421_50

def crepBody421_52 : CrepProg (BitVec 64) :=
.seq crepBody421_49 crepBody421_51

def crepBody421_53 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 0) crepBody421_47

def crepBody421_54 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 112#64]) crepBody421_53

def crepBody421_55 : CrepProg (BitVec 64) :=
.seq crepBody421_52 crepBody421_54

def crepBody421_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "htab_new_scratch" [Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.const 4#64]

def crepBody421_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody421_58 : CrepProg (BitVec 64) :=
.seq crepBody421_57 crepBody421_7

def crepBody421_59 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 8) crepBody421_58

def crepBody421_60 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 136#64]) crepBody421_59

def crepBody421_61 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 152#64])) crepBody421_58

def crepBody421_62 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 168#64]) crepBody421_61

def crepBody421_63 : CrepProg (BitVec 64) :=
.seq crepBody421_60 crepBody421_62

def crepBody421_64 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64])) crepBody421_58

def crepBody421_65 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 176#64]) crepBody421_64

def crepBody421_66 : CrepProg (BitVec 64) :=
.seq crepBody421_63 crepBody421_65

def crepBody421_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "htab_count"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 152#64])]

def crepBody421_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody421_69 : CrepProg (BitVec 64) :=
.seq crepBody421_68 crepBody421_7

def crepBody421_70 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 9) crepBody421_69

def crepBody421_71 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 264#64]) crepBody421_70

def crepBody421_72 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "htab_count"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64])]

def crepBody421_73 : CrepProg (BitVec 64) :=
.seq crepBody421_71 crepBody421_72

def crepBody421_74 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 272#64]) crepBody421_70

def crepBody421_75 : CrepProg (BitVec 64) :=
.seq crepBody421_73 crepBody421_74

def crepBody421_76 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 264#64])) crepBody421_69

def crepBody421_77 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 120#64]) crepBody421_76

def crepBody421_78 : CrepProg (BitVec 64) :=
.seq crepBody421_75 crepBody421_77

def crepBody421_79 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 144#64]) crepBody421_76

def crepBody421_80 : CrepProg (BitVec 64) :=
.seq crepBody421_78 crepBody421_79

def crepBody421_81 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody421_69

def crepBody421_82 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 216#64]) crepBody421_81

def crepBody421_83 : CrepProg (BitVec 64) :=
.seq crepBody421_80 crepBody421_82

def crepBody421_84 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody421_85 : CrepProg (BitVec 64) :=
.seq crepBody421_83 crepBody421_84

def crepBody421_86 : CrepProg (BitVec 64) :=
.seq crepBody421_67 crepBody421_85

def crepBody421_87 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody421_86

def crepBody421_88 : CrepProg (BitVec 64) :=
.seq crepBody421_66 crepBody421_87

def crepBody421_89 : CrepProg (BitVec 64) :=
.seq crepBody421_56 crepBody421_88

def crepBody421_90 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody421_89

def crepBody421_91 : CrepProg (BitVec 64) :=
.seq crepBody421_55 crepBody421_90

def crepBody421_92 : CrepProg (BitVec 64) :=
.seq crepBody421_45 crepBody421_91

def crepBody421_93 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody421_92

def crepBody421_94 : CrepProg (BitVec 64) :=
.seq crepBody421_44 crepBody421_93

def crepBody421_95 : CrepProg (BitVec 64) :=
.seq crepBody421_40 crepBody421_94

def crepBody421_96 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody421_95

def crepBody421_97 : CrepProg (BitVec 64) :=
.seq crepBody421_39 crepBody421_96

def crepBody421_98 : CrepProg (BitVec 64) :=
.seq crepBody421_17 crepBody421_97

def crepBody421_99 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody421_98

def crepBody421_100 : CrepProg (BitVec 64) :=
.seq crepBody421_16 crepBody421_99

def crepBody421_101 : CrepProg (BitVec 64) :=
.seq crepBody421_5 crepBody421_100

def crepBody421_102 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody421_101

def crepBody421_103 : CrepProg (BitVec 64) :=
.seq crepBody421_4 crepBody421_102

def crepBody421_104 : CrepProg (BitVec 64) :=
.seq crepBody421_2 crepBody421_103

def crepBody421_105 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody421_104

def crepBody421_106 : CrepProg (BitVec 64) :=
.seq crepBody421_1 crepBody421_105

def crepBody421_107 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody421_106

def crepBody421_108 : CrepProg (BitVec 64) :=
.seq crepBody421_0 crepBody421_107

def crepBody421_109 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody421_108

def data421 : CrepProg (BitVec 64) := crepBody421_109
def output421 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 110#8, 101#8, 119#8], [0], crepProgToHOL data421)
end InitECandidate.Proofs.FrontendStages.Crep
