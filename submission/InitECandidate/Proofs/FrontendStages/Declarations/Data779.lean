import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify763
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body779_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp0", Flapjack.Exp.var Flapjack.VarKind.local "rx"]

def body779_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp1", Flapjack.Exp.var Flapjack.VarKind.local "ry"]

def body779_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp2", Flapjack.Exp.var Flapjack.VarKind.local "tmp1"]

def body779_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp1",
    Flapjack.Exp.var Flapjack.VarKind.local "rx"]

def body779_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp3"]

def body779_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp3",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp0"]

def body779_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp3",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp2"]

def body779_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp3",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp3"]

def body779_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp4", Flapjack.Exp.var Flapjack.VarKind.local "tmp0",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp0"]

def body779_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp4", Flapjack.Exp.var Flapjack.VarKind.local "tmp4",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp0"]

def body779_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp6", Flapjack.Exp.var Flapjack.VarKind.local "rx",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp4"]

def body779_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp5", Flapjack.Exp.var Flapjack.VarKind.local "tmp4"]

def body779_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "zsq", Flapjack.Exp.var Flapjack.VarKind.local "rz"]

def body779_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "nx", Flapjack.Exp.var Flapjack.VarKind.local "tmp5",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp3"]

def body779_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "nx", Flapjack.Exp.var Flapjack.VarKind.local "nx",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp3"]

def body779_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "ry"]

def body779_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz"]

def body779_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp1"]

def body779_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "zsq"]

def body779_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "ry", Flapjack.Exp.var Flapjack.VarKind.local "tmp3",
    Flapjack.Exp.var Flapjack.VarKind.local "nx"]

def body779_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "ry", Flapjack.Exp.var Flapjack.VarKind.local "ry",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp4"]

def body779_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp2", Flapjack.Exp.var Flapjack.VarKind.local "tmp2",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp2"]

def body779_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "ry", Flapjack.Exp.var Flapjack.VarKind.local "ry",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp2"]

def body779_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "rx", Flapjack.Exp.var Flapjack.VarKind.local "nx"]

def body779_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp4",
    Flapjack.Exp.var Flapjack.VarKind.local "zsq"]

def body779_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_neg"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "co", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "tmp3"]

def body779_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp6", Flapjack.Exp.var Flapjack.VarKind.local "tmp6"]

def body779_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp6", Flapjack.Exp.var Flapjack.VarKind.local "tmp6",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp0"]

def body779_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp6", Flapjack.Exp.var Flapjack.VarKind.local "tmp6",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp5"]

def body779_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp1", Flapjack.Exp.var Flapjack.VarKind.local "tmp1",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp1"]

def body779_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "co", Flapjack.Exp.const 192#64],
    Flapjack.Exp.var Flapjack.VarKind.local "tmp6", Flapjack.Exp.var Flapjack.VarKind.local "tmp1"]

def body779_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp0", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "zsq"]

def body779_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "co", Flapjack.Exp.var Flapjack.VarKind.local "tmp0",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp0"]

def body779_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body779_34 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body779_35 : Prog (BitVec 64) :=
.seq body779_33 body779_34

def body779_36 : Prog (BitVec 64) :=
.seq body779_32 body779_35

def body779_37 : Prog (BitVec 64) :=
.seq body779_31 body779_36

def body779_38 : Prog (BitVec 64) :=
.seq body779_30 body779_37

def body779_39 : Prog (BitVec 64) :=
.seq body779_29 body779_38

def body779_40 : Prog (BitVec 64) :=
.seq body779_29 body779_39

def body779_41 : Prog (BitVec 64) :=
.seq body779_28 body779_40

def body779_42 : Prog (BitVec 64) :=
.seq body779_27 body779_41

def body779_43 : Prog (BitVec 64) :=
.seq body779_26 body779_42

def body779_44 : Prog (BitVec 64) :=
.seq body779_25 body779_43

def body779_45 : Prog (BitVec 64) :=
.seq body779_7 body779_44

def body779_46 : Prog (BitVec 64) :=
.seq body779_24 body779_45

def body779_47 : Prog (BitVec 64) :=
.seq body779_23 body779_46

def body779_48 : Prog (BitVec 64) :=
.seq body779_22 body779_47

def body779_49 : Prog (BitVec 64) :=
.seq body779_21 body779_48

def body779_50 : Prog (BitVec 64) :=
.seq body779_21 body779_49

def body779_51 : Prog (BitVec 64) :=
.seq body779_21 body779_50

def body779_52 : Prog (BitVec 64) :=
.seq body779_20 body779_51

def body779_53 : Prog (BitVec 64) :=
.seq body779_19 body779_52

def body779_54 : Prog (BitVec 64) :=
.seq body779_18 body779_53

def body779_55 : Prog (BitVec 64) :=
.seq body779_17 body779_54

def body779_56 : Prog (BitVec 64) :=
.seq body779_16 body779_55

def body779_57 : Prog (BitVec 64) :=
.seq body779_15 body779_56

def body779_58 : Prog (BitVec 64) :=
.seq body779_14 body779_57

def body779_59 : Prog (BitVec 64) :=
.seq body779_13 body779_58

def body779_60 : Prog (BitVec 64) :=
.seq body779_12 body779_59

def body779_61 : Prog (BitVec 64) :=
.seq body779_11 body779_60

def body779_62 : Prog (BitVec 64) :=
.seq body779_10 body779_61

def body779_63 : Prog (BitVec 64) :=
.seq body779_9 body779_62

def body779_64 : Prog (BitVec 64) :=
.seq body779_8 body779_63

def body779_65 : Prog (BitVec 64) :=
.seq body779_7 body779_64

def body779_66 : Prog (BitVec 64) :=
.seq body779_6 body779_65

def body779_67 : Prog (BitVec 64) :=
.seq body779_5 body779_66

def body779_68 : Prog (BitVec 64) :=
.seq body779_4 body779_67

def body779_69 : Prog (BitVec 64) :=
.seq body779_3 body779_68

def body779_70 : Prog (BitVec 64) :=
.seq body779_2 body779_69

def body779_71 : Prog (BitVec 64) :=
.seq body779_1 body779_70

def body779_72 : Prog (BitVec 64) :=
.seq body779_0 body779_71

def body779_73 : Prog (BitVec 64) :=
.dec ("rz") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 192#64]) body779_72

def body779_74 : Prog (BitVec 64) :=
.dec ("ry") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 96#64]) body779_73

def body779_75 : Prog (BitVec 64) :=
.dec ("rx") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "rp") body779_74

def body779_76 : Prog (BitVec 64) :=
.dec ("nx") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 768#64]) body779_75

def body779_77 : Prog (BitVec 64) :=
.dec ("zsq") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 672#64]) body779_76

def body779_78 : Prog (BitVec 64) :=
.dec ("tmp6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body779_77

def body779_79 : Prog (BitVec 64) :=
.dec ("tmp5") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) body779_78

def body779_80 : Prog (BitVec 64) :=
.dec ("tmp4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) body779_79

def body779_81 : Prog (BitVec 64) :=
.dec ("tmp3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body779_80

def body779_82 : Prog (BitVec 64) :=
.dec ("tmp2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) body779_81

def body779_83 : Prog (BitVec 64) :=
.dec ("tmp1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) body779_82

def body779_84 : Prog (BitVec 64) :=
.dec ("tmp0") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body779_83

def body779_85 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 9#64]]) body779_84

def body779_86 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body779_85

def body779_87 : Prog (BitVec 64) :=
.seq body779_0 body779_1

def body779_88 : Prog (BitVec 64) :=
.seq body779_87 body779_2

def body779_89 : Prog (BitVec 64) :=
.seq body779_88 body779_3

def body779_90 : Prog (BitVec 64) :=
.seq body779_89 body779_4

def body779_91 : Prog (BitVec 64) :=
.seq body779_90 body779_5

def body779_92 : Prog (BitVec 64) :=
.seq body779_91 body779_6

def body779_93 : Prog (BitVec 64) :=
.seq body779_92 body779_7

def body779_94 : Prog (BitVec 64) :=
.seq body779_93 body779_8

def body779_95 : Prog (BitVec 64) :=
.seq body779_94 body779_9

def body779_96 : Prog (BitVec 64) :=
.seq body779_95 body779_10

def body779_97 : Prog (BitVec 64) :=
.seq body779_96 body779_11

def body779_98 : Prog (BitVec 64) :=
.seq body779_97 body779_12

def body779_99 : Prog (BitVec 64) :=
.seq body779_98 body779_13

def body779_100 : Prog (BitVec 64) :=
.seq body779_99 body779_14

def body779_101 : Prog (BitVec 64) :=
.seq body779_100 body779_15

def body779_102 : Prog (BitVec 64) :=
.seq body779_101 body779_16

def body779_103 : Prog (BitVec 64) :=
.seq body779_102 body779_17

def body779_104 : Prog (BitVec 64) :=
.seq body779_103 body779_18

def body779_105 : Prog (BitVec 64) :=
.seq body779_104 body779_19

def body779_106 : Prog (BitVec 64) :=
.seq body779_105 body779_20

def body779_107 : Prog (BitVec 64) :=
.seq body779_106 body779_21

def body779_108 : Prog (BitVec 64) :=
.seq body779_107 body779_21

def body779_109 : Prog (BitVec 64) :=
.seq body779_108 body779_21

def body779_110 : Prog (BitVec 64) :=
.seq body779_109 body779_22

def body779_111 : Prog (BitVec 64) :=
.seq body779_110 body779_23

def body779_112 : Prog (BitVec 64) :=
.seq body779_111 body779_24

def body779_113 : Prog (BitVec 64) :=
.seq body779_112 body779_7

def body779_114 : Prog (BitVec 64) :=
.seq body779_113 body779_25

def body779_115 : Prog (BitVec 64) :=
.seq body779_114 body779_26

def body779_116 : Prog (BitVec 64) :=
.seq body779_115 body779_27

def body779_117 : Prog (BitVec 64) :=
.seq body779_116 body779_28

def body779_118 : Prog (BitVec 64) :=
.seq body779_117 body779_29

def body779_119 : Prog (BitVec 64) :=
.seq body779_118 body779_29

def body779_120 : Prog (BitVec 64) :=
.seq body779_119 body779_30

def body779_121 : Prog (BitVec 64) :=
.seq body779_120 body779_31

def body779_122 : Prog (BitVec 64) :=
.seq body779_121 body779_32

def body779_123 : Prog (BitVec 64) :=
.seq body779_122 body779_33

def body779_124 : Prog (BitVec 64) :=
.seq body779_123 body779_34

def body779_125 : Prog (BitVec 64) :=
.dec ("rz") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 192#64]) body779_124

def body779_126 : Prog (BitVec 64) :=
.dec ("ry") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 96#64]) body779_125

def body779_127 : Prog (BitVec 64) :=
.dec ("rx") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "rp") body779_126

def body779_128 : Prog (BitVec 64) :=
.dec ("nx") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 768#64]) body779_127

def body779_129 : Prog (BitVec 64) :=
.dec ("zsq") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 672#64]) body779_128

def body779_130 : Prog (BitVec 64) :=
.dec ("tmp6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body779_129

def body779_131 : Prog (BitVec 64) :=
.dec ("tmp5") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) body779_130

def body779_132 : Prog (BitVec 64) :=
.dec ("tmp4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) body779_131

def body779_133 : Prog (BitVec 64) :=
.dec ("tmp3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body779_132

def body779_134 : Prog (BitVec 64) :=
.dec ("tmp2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) body779_133

def body779_135 : Prog (BitVec 64) :=
.dec ("tmp1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) body779_134

def body779_136 : Prog (BitVec 64) :=
.dec ("tmp0") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body779_135

def body779_137 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 9#64]]) body779_136

def body779_138 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body779_137

def originalData779 : Decl (BitVec 64) :=
.function { name := "pair_doubling_step", inline := false, exported := false, params := [("rp", Flapjack.Shape.one), ("co", Flapjack.Shape.one)], body := body779_86, returnShape := (Flapjack.Shape.one) }
def simplifiedData779 : Decl (BitVec 64) :=
.function { name := "pair_doubling_step", inline := false, exported := false, params := [("rp", Flapjack.Shape.one), ("co", Flapjack.Shape.one)], body := body779_138, returnShape := (Flapjack.Shape.one) }
def original779 := Pancake.PanLang.declToHOL originalData779
def simplified779 := Pancake.PanLang.declToHOL simplifiedData779
end InitECandidate.Proofs.FrontendStages.Declarations
