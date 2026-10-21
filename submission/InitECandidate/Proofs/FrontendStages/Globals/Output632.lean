import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data632
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate613
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody632_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "a0"])

def globalBody632_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "L"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "L",
      Flapjack.Exp.op Flapjack.BinOp.and
        [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 4294967295#64]])

def globalBody632_2 : Prog (BitVec 64) :=
.seq globalBody632_0 globalBody632_1

def globalBody632_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "H"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "H",
      Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "p") (Flapjack.Exp.const 32#64)])

def globalBody632_4 : Prog (BitVec 64) :=
.seq globalBody632_2 globalBody632_3

def globalBody632_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "L"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "L", Flapjack.Exp.var Flapjack.VarKind.local "Lc",
      Flapjack.Exp.var Flapjack.VarKind.local "Lc"])

def globalBody632_6 : Prog (BitVec 64) :=
.seq globalBody632_4 globalBody632_5

def globalBody632_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "H"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "H", Flapjack.Exp.var Flapjack.VarKind.local "Hc",
      Flapjack.Exp.var Flapjack.VarKind.local "Hc"])

def globalBody632_8 : Prog (BitVec 64) :=
.seq globalBody632_6 globalBody632_7

def globalBody632_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "Lc" (Flapjack.Exp.const 0#64)

def globalBody632_10 : Prog (BitVec 64) :=
.seq globalBody632_8 globalBody632_9

def globalBody632_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "Hc" (Flapjack.Exp.const 0#64)

def globalBody632_12 : Prog (BitVec 64) :=
.seq globalBody632_10 globalBody632_11

def globalBody632_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "L", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody632_14 : Prog (BitVec 64) :=
.seq globalBody632_12 globalBody632_13

def globalBody632_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d0"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_16 : Prog (BitVec 64) :=
.seq globalBody632_14 globalBody632_15

def globalBody632_17 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "col") (Flapjack.Exp.const 32#64),
      Flapjack.Exp.var Flapjack.VarKind.local "H"])

def globalBody632_18 : Prog (BitVec 64) :=
.seq globalBody632_16 globalBody632_17

def globalBody632_19 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "L" (Flapjack.Exp.const 0#64)

def globalBody632_20 : Prog (BitVec 64) :=
.seq globalBody632_18 globalBody632_19

def globalBody632_21 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "H" (Flapjack.Exp.const 0#64)

def globalBody632_22 : Prog (BitVec 64) :=
.seq globalBody632_20 globalBody632_21

def globalBody632_23 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "a1"])

def globalBody632_24 : Prog (BitVec 64) :=
.seq globalBody632_22 globalBody632_23

def globalBody632_25 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "Lc"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "Lc",
      Flapjack.Exp.op Flapjack.BinOp.and
        [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 4294967295#64]])

def globalBody632_26 : Prog (BitVec 64) :=
.seq globalBody632_24 globalBody632_25

def globalBody632_27 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "Hc"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "Hc",
      Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "p") (Flapjack.Exp.const 32#64)])

def globalBody632_28 : Prog (BitVec 64) :=
.seq globalBody632_26 globalBody632_27

def globalBody632_29 : Prog (BitVec 64) :=
.seq globalBody632_28 globalBody632_5

def globalBody632_30 : Prog (BitVec 64) :=
.seq globalBody632_29 globalBody632_7

def globalBody632_31 : Prog (BitVec 64) :=
.seq globalBody632_30 globalBody632_9

def globalBody632_32 : Prog (BitVec 64) :=
.seq globalBody632_31 globalBody632_11

def globalBody632_33 : Prog (BitVec 64) :=
.seq globalBody632_32 globalBody632_13

def globalBody632_34 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d1"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_35 : Prog (BitVec 64) :=
.seq globalBody632_33 globalBody632_34

def globalBody632_36 : Prog (BitVec 64) :=
.seq globalBody632_35 globalBody632_17

def globalBody632_37 : Prog (BitVec 64) :=
.seq globalBody632_36 globalBody632_19

def globalBody632_38 : Prog (BitVec 64) :=
.seq globalBody632_37 globalBody632_21

def globalBody632_39 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "a2"])

def globalBody632_40 : Prog (BitVec 64) :=
.seq globalBody632_38 globalBody632_39

def globalBody632_41 : Prog (BitVec 64) :=
.seq globalBody632_40 globalBody632_25

def globalBody632_42 : Prog (BitVec 64) :=
.seq globalBody632_41 globalBody632_27

def globalBody632_43 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "a1"])

def globalBody632_44 : Prog (BitVec 64) :=
.seq globalBody632_42 globalBody632_43

def globalBody632_45 : Prog (BitVec 64) :=
.seq globalBody632_44 globalBody632_1

def globalBody632_46 : Prog (BitVec 64) :=
.seq globalBody632_45 globalBody632_3

def globalBody632_47 : Prog (BitVec 64) :=
.seq globalBody632_46 globalBody632_5

def globalBody632_48 : Prog (BitVec 64) :=
.seq globalBody632_47 globalBody632_7

def globalBody632_49 : Prog (BitVec 64) :=
.seq globalBody632_48 globalBody632_9

def globalBody632_50 : Prog (BitVec 64) :=
.seq globalBody632_49 globalBody632_11

def globalBody632_51 : Prog (BitVec 64) :=
.seq globalBody632_50 globalBody632_13

def globalBody632_52 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d2"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_53 : Prog (BitVec 64) :=
.seq globalBody632_51 globalBody632_52

def globalBody632_54 : Prog (BitVec 64) :=
.seq globalBody632_53 globalBody632_17

def globalBody632_55 : Prog (BitVec 64) :=
.seq globalBody632_54 globalBody632_19

def globalBody632_56 : Prog (BitVec 64) :=
.seq globalBody632_55 globalBody632_21

def globalBody632_57 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "a3"])

def globalBody632_58 : Prog (BitVec 64) :=
.seq globalBody632_56 globalBody632_57

def globalBody632_59 : Prog (BitVec 64) :=
.seq globalBody632_58 globalBody632_25

def globalBody632_60 : Prog (BitVec 64) :=
.seq globalBody632_59 globalBody632_27

def globalBody632_61 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "a2"])

def globalBody632_62 : Prog (BitVec 64) :=
.seq globalBody632_60 globalBody632_61

def globalBody632_63 : Prog (BitVec 64) :=
.seq globalBody632_62 globalBody632_25

def globalBody632_64 : Prog (BitVec 64) :=
.seq globalBody632_63 globalBody632_27

def globalBody632_65 : Prog (BitVec 64) :=
.seq globalBody632_64 globalBody632_5

def globalBody632_66 : Prog (BitVec 64) :=
.seq globalBody632_65 globalBody632_7

def globalBody632_67 : Prog (BitVec 64) :=
.seq globalBody632_66 globalBody632_9

def globalBody632_68 : Prog (BitVec 64) :=
.seq globalBody632_67 globalBody632_11

def globalBody632_69 : Prog (BitVec 64) :=
.seq globalBody632_68 globalBody632_13

def globalBody632_70 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d3"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_71 : Prog (BitVec 64) :=
.seq globalBody632_69 globalBody632_70

def globalBody632_72 : Prog (BitVec 64) :=
.seq globalBody632_71 globalBody632_17

def globalBody632_73 : Prog (BitVec 64) :=
.seq globalBody632_72 globalBody632_19

def globalBody632_74 : Prog (BitVec 64) :=
.seq globalBody632_73 globalBody632_21

def globalBody632_75 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "a4"])

def globalBody632_76 : Prog (BitVec 64) :=
.seq globalBody632_74 globalBody632_75

def globalBody632_77 : Prog (BitVec 64) :=
.seq globalBody632_76 globalBody632_25

def globalBody632_78 : Prog (BitVec 64) :=
.seq globalBody632_77 globalBody632_27

def globalBody632_79 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "a3"])

def globalBody632_80 : Prog (BitVec 64) :=
.seq globalBody632_78 globalBody632_79

def globalBody632_81 : Prog (BitVec 64) :=
.seq globalBody632_80 globalBody632_25

def globalBody632_82 : Prog (BitVec 64) :=
.seq globalBody632_81 globalBody632_27

def globalBody632_83 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "a2"])

def globalBody632_84 : Prog (BitVec 64) :=
.seq globalBody632_82 globalBody632_83

def globalBody632_85 : Prog (BitVec 64) :=
.seq globalBody632_84 globalBody632_1

def globalBody632_86 : Prog (BitVec 64) :=
.seq globalBody632_85 globalBody632_3

def globalBody632_87 : Prog (BitVec 64) :=
.seq globalBody632_86 globalBody632_5

def globalBody632_88 : Prog (BitVec 64) :=
.seq globalBody632_87 globalBody632_7

def globalBody632_89 : Prog (BitVec 64) :=
.seq globalBody632_88 globalBody632_9

def globalBody632_90 : Prog (BitVec 64) :=
.seq globalBody632_89 globalBody632_11

def globalBody632_91 : Prog (BitVec 64) :=
.seq globalBody632_90 globalBody632_13

def globalBody632_92 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d4"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_93 : Prog (BitVec 64) :=
.seq globalBody632_91 globalBody632_92

def globalBody632_94 : Prog (BitVec 64) :=
.seq globalBody632_93 globalBody632_17

def globalBody632_95 : Prog (BitVec 64) :=
.seq globalBody632_94 globalBody632_19

def globalBody632_96 : Prog (BitVec 64) :=
.seq globalBody632_95 globalBody632_21

def globalBody632_97 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "a5"])

def globalBody632_98 : Prog (BitVec 64) :=
.seq globalBody632_96 globalBody632_97

def globalBody632_99 : Prog (BitVec 64) :=
.seq globalBody632_98 globalBody632_25

def globalBody632_100 : Prog (BitVec 64) :=
.seq globalBody632_99 globalBody632_27

def globalBody632_101 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "a4"])

def globalBody632_102 : Prog (BitVec 64) :=
.seq globalBody632_100 globalBody632_101

def globalBody632_103 : Prog (BitVec 64) :=
.seq globalBody632_102 globalBody632_25

def globalBody632_104 : Prog (BitVec 64) :=
.seq globalBody632_103 globalBody632_27

def globalBody632_105 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "a3"])

def globalBody632_106 : Prog (BitVec 64) :=
.seq globalBody632_104 globalBody632_105

def globalBody632_107 : Prog (BitVec 64) :=
.seq globalBody632_106 globalBody632_25

def globalBody632_108 : Prog (BitVec 64) :=
.seq globalBody632_107 globalBody632_27

def globalBody632_109 : Prog (BitVec 64) :=
.seq globalBody632_108 globalBody632_5

def globalBody632_110 : Prog (BitVec 64) :=
.seq globalBody632_109 globalBody632_7

def globalBody632_111 : Prog (BitVec 64) :=
.seq globalBody632_110 globalBody632_9

def globalBody632_112 : Prog (BitVec 64) :=
.seq globalBody632_111 globalBody632_11

def globalBody632_113 : Prog (BitVec 64) :=
.seq globalBody632_112 globalBody632_13

def globalBody632_114 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d5"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_115 : Prog (BitVec 64) :=
.seq globalBody632_113 globalBody632_114

def globalBody632_116 : Prog (BitVec 64) :=
.seq globalBody632_115 globalBody632_17

def globalBody632_117 : Prog (BitVec 64) :=
.seq globalBody632_116 globalBody632_19

def globalBody632_118 : Prog (BitVec 64) :=
.seq globalBody632_117 globalBody632_21

def globalBody632_119 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "a6"])

def globalBody632_120 : Prog (BitVec 64) :=
.seq globalBody632_118 globalBody632_119

def globalBody632_121 : Prog (BitVec 64) :=
.seq globalBody632_120 globalBody632_25

def globalBody632_122 : Prog (BitVec 64) :=
.seq globalBody632_121 globalBody632_27

def globalBody632_123 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "a5"])

def globalBody632_124 : Prog (BitVec 64) :=
.seq globalBody632_122 globalBody632_123

def globalBody632_125 : Prog (BitVec 64) :=
.seq globalBody632_124 globalBody632_25

def globalBody632_126 : Prog (BitVec 64) :=
.seq globalBody632_125 globalBody632_27

def globalBody632_127 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "a4"])

def globalBody632_128 : Prog (BitVec 64) :=
.seq globalBody632_126 globalBody632_127

def globalBody632_129 : Prog (BitVec 64) :=
.seq globalBody632_128 globalBody632_25

def globalBody632_130 : Prog (BitVec 64) :=
.seq globalBody632_129 globalBody632_27

def globalBody632_131 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "a3"])

def globalBody632_132 : Prog (BitVec 64) :=
.seq globalBody632_130 globalBody632_131

def globalBody632_133 : Prog (BitVec 64) :=
.seq globalBody632_132 globalBody632_1

def globalBody632_134 : Prog (BitVec 64) :=
.seq globalBody632_133 globalBody632_3

def globalBody632_135 : Prog (BitVec 64) :=
.seq globalBody632_134 globalBody632_5

def globalBody632_136 : Prog (BitVec 64) :=
.seq globalBody632_135 globalBody632_7

def globalBody632_137 : Prog (BitVec 64) :=
.seq globalBody632_136 globalBody632_9

def globalBody632_138 : Prog (BitVec 64) :=
.seq globalBody632_137 globalBody632_11

def globalBody632_139 : Prog (BitVec 64) :=
.seq globalBody632_138 globalBody632_13

def globalBody632_140 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d6"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_141 : Prog (BitVec 64) :=
.seq globalBody632_139 globalBody632_140

def globalBody632_142 : Prog (BitVec 64) :=
.seq globalBody632_141 globalBody632_17

def globalBody632_143 : Prog (BitVec 64) :=
.seq globalBody632_142 globalBody632_19

def globalBody632_144 : Prog (BitVec 64) :=
.seq globalBody632_143 globalBody632_21

def globalBody632_145 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "a7"])

def globalBody632_146 : Prog (BitVec 64) :=
.seq globalBody632_144 globalBody632_145

def globalBody632_147 : Prog (BitVec 64) :=
.seq globalBody632_146 globalBody632_25

def globalBody632_148 : Prog (BitVec 64) :=
.seq globalBody632_147 globalBody632_27

def globalBody632_149 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "a6"])

def globalBody632_150 : Prog (BitVec 64) :=
.seq globalBody632_148 globalBody632_149

def globalBody632_151 : Prog (BitVec 64) :=
.seq globalBody632_150 globalBody632_25

def globalBody632_152 : Prog (BitVec 64) :=
.seq globalBody632_151 globalBody632_27

def globalBody632_153 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "a5"])

def globalBody632_154 : Prog (BitVec 64) :=
.seq globalBody632_152 globalBody632_153

def globalBody632_155 : Prog (BitVec 64) :=
.seq globalBody632_154 globalBody632_25

def globalBody632_156 : Prog (BitVec 64) :=
.seq globalBody632_155 globalBody632_27

def globalBody632_157 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "a4"])

def globalBody632_158 : Prog (BitVec 64) :=
.seq globalBody632_156 globalBody632_157

def globalBody632_159 : Prog (BitVec 64) :=
.seq globalBody632_158 globalBody632_25

def globalBody632_160 : Prog (BitVec 64) :=
.seq globalBody632_159 globalBody632_27

def globalBody632_161 : Prog (BitVec 64) :=
.seq globalBody632_160 globalBody632_5

def globalBody632_162 : Prog (BitVec 64) :=
.seq globalBody632_161 globalBody632_7

def globalBody632_163 : Prog (BitVec 64) :=
.seq globalBody632_162 globalBody632_9

def globalBody632_164 : Prog (BitVec 64) :=
.seq globalBody632_163 globalBody632_11

def globalBody632_165 : Prog (BitVec 64) :=
.seq globalBody632_164 globalBody632_13

def globalBody632_166 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d7"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_167 : Prog (BitVec 64) :=
.seq globalBody632_165 globalBody632_166

def globalBody632_168 : Prog (BitVec 64) :=
.seq globalBody632_167 globalBody632_17

def globalBody632_169 : Prog (BitVec 64) :=
.seq globalBody632_168 globalBody632_19

def globalBody632_170 : Prog (BitVec 64) :=
.seq globalBody632_169 globalBody632_21

def globalBody632_171 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "a7"])

def globalBody632_172 : Prog (BitVec 64) :=
.seq globalBody632_170 globalBody632_171

def globalBody632_173 : Prog (BitVec 64) :=
.seq globalBody632_172 globalBody632_25

def globalBody632_174 : Prog (BitVec 64) :=
.seq globalBody632_173 globalBody632_27

def globalBody632_175 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "a6"])

def globalBody632_176 : Prog (BitVec 64) :=
.seq globalBody632_174 globalBody632_175

def globalBody632_177 : Prog (BitVec 64) :=
.seq globalBody632_176 globalBody632_25

def globalBody632_178 : Prog (BitVec 64) :=
.seq globalBody632_177 globalBody632_27

def globalBody632_179 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "a5"])

def globalBody632_180 : Prog (BitVec 64) :=
.seq globalBody632_178 globalBody632_179

def globalBody632_181 : Prog (BitVec 64) :=
.seq globalBody632_180 globalBody632_25

def globalBody632_182 : Prog (BitVec 64) :=
.seq globalBody632_181 globalBody632_27

def globalBody632_183 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "a4"])

def globalBody632_184 : Prog (BitVec 64) :=
.seq globalBody632_182 globalBody632_183

def globalBody632_185 : Prog (BitVec 64) :=
.seq globalBody632_184 globalBody632_1

def globalBody632_186 : Prog (BitVec 64) :=
.seq globalBody632_185 globalBody632_3

def globalBody632_187 : Prog (BitVec 64) :=
.seq globalBody632_186 globalBody632_5

def globalBody632_188 : Prog (BitVec 64) :=
.seq globalBody632_187 globalBody632_7

def globalBody632_189 : Prog (BitVec 64) :=
.seq globalBody632_188 globalBody632_9

def globalBody632_190 : Prog (BitVec 64) :=
.seq globalBody632_189 globalBody632_11

def globalBody632_191 : Prog (BitVec 64) :=
.seq globalBody632_190 globalBody632_13

def globalBody632_192 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d8"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_193 : Prog (BitVec 64) :=
.seq globalBody632_191 globalBody632_192

def globalBody632_194 : Prog (BitVec 64) :=
.seq globalBody632_193 globalBody632_17

def globalBody632_195 : Prog (BitVec 64) :=
.seq globalBody632_194 globalBody632_19

def globalBody632_196 : Prog (BitVec 64) :=
.seq globalBody632_195 globalBody632_21

def globalBody632_197 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "a7"])

def globalBody632_198 : Prog (BitVec 64) :=
.seq globalBody632_196 globalBody632_197

def globalBody632_199 : Prog (BitVec 64) :=
.seq globalBody632_198 globalBody632_25

def globalBody632_200 : Prog (BitVec 64) :=
.seq globalBody632_199 globalBody632_27

def globalBody632_201 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "a6"])

def globalBody632_202 : Prog (BitVec 64) :=
.seq globalBody632_200 globalBody632_201

def globalBody632_203 : Prog (BitVec 64) :=
.seq globalBody632_202 globalBody632_25

def globalBody632_204 : Prog (BitVec 64) :=
.seq globalBody632_203 globalBody632_27

def globalBody632_205 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "a5"])

def globalBody632_206 : Prog (BitVec 64) :=
.seq globalBody632_204 globalBody632_205

def globalBody632_207 : Prog (BitVec 64) :=
.seq globalBody632_206 globalBody632_25

def globalBody632_208 : Prog (BitVec 64) :=
.seq globalBody632_207 globalBody632_27

def globalBody632_209 : Prog (BitVec 64) :=
.seq globalBody632_208 globalBody632_5

def globalBody632_210 : Prog (BitVec 64) :=
.seq globalBody632_209 globalBody632_7

def globalBody632_211 : Prog (BitVec 64) :=
.seq globalBody632_210 globalBody632_9

def globalBody632_212 : Prog (BitVec 64) :=
.seq globalBody632_211 globalBody632_11

def globalBody632_213 : Prog (BitVec 64) :=
.seq globalBody632_212 globalBody632_13

def globalBody632_214 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d9"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_215 : Prog (BitVec 64) :=
.seq globalBody632_213 globalBody632_214

def globalBody632_216 : Prog (BitVec 64) :=
.seq globalBody632_215 globalBody632_17

def globalBody632_217 : Prog (BitVec 64) :=
.seq globalBody632_216 globalBody632_19

def globalBody632_218 : Prog (BitVec 64) :=
.seq globalBody632_217 globalBody632_21

def globalBody632_219 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "a7"])

def globalBody632_220 : Prog (BitVec 64) :=
.seq globalBody632_218 globalBody632_219

def globalBody632_221 : Prog (BitVec 64) :=
.seq globalBody632_220 globalBody632_25

def globalBody632_222 : Prog (BitVec 64) :=
.seq globalBody632_221 globalBody632_27

def globalBody632_223 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "a6"])

def globalBody632_224 : Prog (BitVec 64) :=
.seq globalBody632_222 globalBody632_223

def globalBody632_225 : Prog (BitVec 64) :=
.seq globalBody632_224 globalBody632_25

def globalBody632_226 : Prog (BitVec 64) :=
.seq globalBody632_225 globalBody632_27

def globalBody632_227 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "a5"])

def globalBody632_228 : Prog (BitVec 64) :=
.seq globalBody632_226 globalBody632_227

def globalBody632_229 : Prog (BitVec 64) :=
.seq globalBody632_228 globalBody632_1

def globalBody632_230 : Prog (BitVec 64) :=
.seq globalBody632_229 globalBody632_3

def globalBody632_231 : Prog (BitVec 64) :=
.seq globalBody632_230 globalBody632_5

def globalBody632_232 : Prog (BitVec 64) :=
.seq globalBody632_231 globalBody632_7

def globalBody632_233 : Prog (BitVec 64) :=
.seq globalBody632_232 globalBody632_9

def globalBody632_234 : Prog (BitVec 64) :=
.seq globalBody632_233 globalBody632_11

def globalBody632_235 : Prog (BitVec 64) :=
.seq globalBody632_234 globalBody632_13

def globalBody632_236 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d10"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_237 : Prog (BitVec 64) :=
.seq globalBody632_235 globalBody632_236

def globalBody632_238 : Prog (BitVec 64) :=
.seq globalBody632_237 globalBody632_17

def globalBody632_239 : Prog (BitVec 64) :=
.seq globalBody632_238 globalBody632_19

def globalBody632_240 : Prog (BitVec 64) :=
.seq globalBody632_239 globalBody632_21

def globalBody632_241 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "a7"])

def globalBody632_242 : Prog (BitVec 64) :=
.seq globalBody632_240 globalBody632_241

def globalBody632_243 : Prog (BitVec 64) :=
.seq globalBody632_242 globalBody632_25

def globalBody632_244 : Prog (BitVec 64) :=
.seq globalBody632_243 globalBody632_27

def globalBody632_245 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "a6"])

def globalBody632_246 : Prog (BitVec 64) :=
.seq globalBody632_244 globalBody632_245

def globalBody632_247 : Prog (BitVec 64) :=
.seq globalBody632_246 globalBody632_25

def globalBody632_248 : Prog (BitVec 64) :=
.seq globalBody632_247 globalBody632_27

def globalBody632_249 : Prog (BitVec 64) :=
.seq globalBody632_248 globalBody632_5

def globalBody632_250 : Prog (BitVec 64) :=
.seq globalBody632_249 globalBody632_7

def globalBody632_251 : Prog (BitVec 64) :=
.seq globalBody632_250 globalBody632_9

def globalBody632_252 : Prog (BitVec 64) :=
.seq globalBody632_251 globalBody632_11

def globalBody632_253 : Prog (BitVec 64) :=
.seq globalBody632_252 globalBody632_13

def globalBody632_254 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d11"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_255 : Prog (BitVec 64) :=
.seq globalBody632_253 globalBody632_254

def globalBody632_256 : Prog (BitVec 64) :=
.seq globalBody632_255 globalBody632_17

def globalBody632_257 : Prog (BitVec 64) :=
.seq globalBody632_256 globalBody632_19

def globalBody632_258 : Prog (BitVec 64) :=
.seq globalBody632_257 globalBody632_21

def globalBody632_259 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "a7"])

def globalBody632_260 : Prog (BitVec 64) :=
.seq globalBody632_258 globalBody632_259

def globalBody632_261 : Prog (BitVec 64) :=
.seq globalBody632_260 globalBody632_25

def globalBody632_262 : Prog (BitVec 64) :=
.seq globalBody632_261 globalBody632_27

def globalBody632_263 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "a6"])

def globalBody632_264 : Prog (BitVec 64) :=
.seq globalBody632_262 globalBody632_263

def globalBody632_265 : Prog (BitVec 64) :=
.seq globalBody632_264 globalBody632_1

def globalBody632_266 : Prog (BitVec 64) :=
.seq globalBody632_265 globalBody632_3

def globalBody632_267 : Prog (BitVec 64) :=
.seq globalBody632_266 globalBody632_5

def globalBody632_268 : Prog (BitVec 64) :=
.seq globalBody632_267 globalBody632_7

def globalBody632_269 : Prog (BitVec 64) :=
.seq globalBody632_268 globalBody632_9

def globalBody632_270 : Prog (BitVec 64) :=
.seq globalBody632_269 globalBody632_11

def globalBody632_271 : Prog (BitVec 64) :=
.seq globalBody632_270 globalBody632_13

def globalBody632_272 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d12"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_273 : Prog (BitVec 64) :=
.seq globalBody632_271 globalBody632_272

def globalBody632_274 : Prog (BitVec 64) :=
.seq globalBody632_273 globalBody632_17

def globalBody632_275 : Prog (BitVec 64) :=
.seq globalBody632_274 globalBody632_19

def globalBody632_276 : Prog (BitVec 64) :=
.seq globalBody632_275 globalBody632_21

def globalBody632_277 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "a7"])

def globalBody632_278 : Prog (BitVec 64) :=
.seq globalBody632_276 globalBody632_277

def globalBody632_279 : Prog (BitVec 64) :=
.seq globalBody632_278 globalBody632_25

def globalBody632_280 : Prog (BitVec 64) :=
.seq globalBody632_279 globalBody632_27

def globalBody632_281 : Prog (BitVec 64) :=
.seq globalBody632_280 globalBody632_5

def globalBody632_282 : Prog (BitVec 64) :=
.seq globalBody632_281 globalBody632_7

def globalBody632_283 : Prog (BitVec 64) :=
.seq globalBody632_282 globalBody632_9

def globalBody632_284 : Prog (BitVec 64) :=
.seq globalBody632_283 globalBody632_11

def globalBody632_285 : Prog (BitVec 64) :=
.seq globalBody632_284 globalBody632_13

def globalBody632_286 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d13"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_287 : Prog (BitVec 64) :=
.seq globalBody632_285 globalBody632_286

def globalBody632_288 : Prog (BitVec 64) :=
.seq globalBody632_287 globalBody632_17

def globalBody632_289 : Prog (BitVec 64) :=
.seq globalBody632_288 globalBody632_19

def globalBody632_290 : Prog (BitVec 64) :=
.seq globalBody632_289 globalBody632_21

def globalBody632_291 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "a7"])

def globalBody632_292 : Prog (BitVec 64) :=
.seq globalBody632_290 globalBody632_291

def globalBody632_293 : Prog (BitVec 64) :=
.seq globalBody632_292 globalBody632_1

def globalBody632_294 : Prog (BitVec 64) :=
.seq globalBody632_293 globalBody632_3

def globalBody632_295 : Prog (BitVec 64) :=
.seq globalBody632_294 globalBody632_5

def globalBody632_296 : Prog (BitVec 64) :=
.seq globalBody632_295 globalBody632_7

def globalBody632_297 : Prog (BitVec 64) :=
.seq globalBody632_296 globalBody632_9

def globalBody632_298 : Prog (BitVec 64) :=
.seq globalBody632_297 globalBody632_11

def globalBody632_299 : Prog (BitVec 64) :=
.seq globalBody632_298 globalBody632_13

def globalBody632_300 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d14"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody632_301 : Prog (BitVec 64) :=
.seq globalBody632_299 globalBody632_300

def globalBody632_302 : Prog (BitVec 64) :=
.seq globalBody632_301 globalBody632_17

def globalBody632_303 : Prog (BitVec 64) :=
.seq globalBody632_302 globalBody632_19

def globalBody632_304 : Prog (BitVec 64) :=
.seq globalBody632_303 globalBody632_21

def globalBody632_305 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d15" (Flapjack.Exp.var Flapjack.VarKind.local "c")

def globalBody632_306 : Prog (BitVec 64) :=
.seq globalBody632_304 globalBody632_305

def globalBody632_307 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.shift Flapjack.Shift.asr (Flapjack.Exp.var Flapjack.VarKind.local "t0") (Flapjack.Exp.const 32#64))

def globalBody632_308 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody632_309 : Prog (BitVec 64) :=
.seq globalBody632_307 globalBody632_308

def globalBody632_310 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.shift Flapjack.Shift.asr (Flapjack.Exp.var Flapjack.VarKind.local "col") (Flapjack.Exp.const 32#64))

def globalBody632_311 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody632_312 : Prog (BitVec 64) :=
.seq globalBody632_310 globalBody632_311

def globalBody632_313 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t3", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody632_314 : Prog (BitVec 64) :=
.seq globalBody632_310 globalBody632_313

def globalBody632_315 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t4", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody632_316 : Prog (BitVec 64) :=
.seq globalBody632_310 globalBody632_315

def globalBody632_317 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t5", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody632_318 : Prog (BitVec 64) :=
.seq globalBody632_310 globalBody632_317

def globalBody632_319 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t6", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody632_320 : Prog (BitVec 64) :=
.seq globalBody632_310 globalBody632_319

def globalBody632_321 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t7", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody632_322 : Prog (BitVec 64) :=
.seq globalBody632_310 globalBody632_321

def globalBody632_323 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r"
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sa"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sa"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "sa"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "sa")])

def globalBody632_324 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "sa")])

def globalBody632_325 : Prog (BitVec 64) :=
.seq globalBody632_323 globalBody632_324

def globalBody632_326 : Prog (BitVec 64) :=
.decCall ("sa") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add_carry") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) globalBody632_325

def globalBody632_327 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "c") (Flapjack.Exp.const 0#64)) globalBody632_326

def globalBody632_328 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "u256_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
        Flapjack.Exp.const 18446744069414584321#64]]

def globalBody632_329 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "ltp"])

def globalBody632_330 : Prog (BitVec 64) :=
.seq globalBody632_328 globalBody632_329

def globalBody632_331 : Prog (BitVec 64) :=
.decCall ("ltp") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) globalBody632_330

def globalBody632_332 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "c")) globalBody632_331

def globalBody632_333 : Prog (BitVec 64) :=
.seq globalBody632_327 globalBody632_332

def globalBody632_334 : Prog (BitVec 64) :=
Flapjack.Prog.call none "p256_fp_reduce" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def globalBody632_335 : Prog (BitVec 64) :=
.seq globalBody632_333 globalBody632_334

def globalBody632_336 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.var Flapjack.VarKind.local "v0",
        Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "v1")
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.var Flapjack.VarKind.local "v2",
        Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "v3")
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.var Flapjack.VarKind.local "v4",
        Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "v5")
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.var Flapjack.VarKind.local "v6",
        Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "v7")
          (Flapjack.Exp.const 32#64)]]) globalBody632_335

def globalBody632_337 : Prog (BitVec 64) :=
.seq globalBody632_310 globalBody632_336

def globalBody632_338 : Prog (BitVec 64) :=
.dec ("v7") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody632_337

def globalBody632_339 : Prog (BitVec 64) :=
.seq globalBody632_322 globalBody632_338

def globalBody632_340 : Prog (BitVec 64) :=
.dec ("v6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody632_339

def globalBody632_341 : Prog (BitVec 64) :=
.seq globalBody632_320 globalBody632_340

def globalBody632_342 : Prog (BitVec 64) :=
.dec ("v5") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody632_341

def globalBody632_343 : Prog (BitVec 64) :=
.seq globalBody632_318 globalBody632_342

def globalBody632_344 : Prog (BitVec 64) :=
.dec ("v4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody632_343

def globalBody632_345 : Prog (BitVec 64) :=
.seq globalBody632_316 globalBody632_344

def globalBody632_346 : Prog (BitVec 64) :=
.dec ("v3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody632_345

def globalBody632_347 : Prog (BitVec 64) :=
.seq globalBody632_314 globalBody632_346

def globalBody632_348 : Prog (BitVec 64) :=
.dec ("v2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody632_347

def globalBody632_349 : Prog (BitVec 64) :=
.seq globalBody632_312 globalBody632_348

def globalBody632_350 : Prog (BitVec 64) :=
.dec ("v1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody632_349

def globalBody632_351 : Prog (BitVec 64) :=
.seq globalBody632_309 globalBody632_350

def globalBody632_352 : Prog (BitVec 64) :=
.dec ("v0") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.const 4294967295#64]) globalBody632_351

def globalBody632_353 : Prog (BitVec 64) :=
.dec ("t7") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.sub
              [Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "d7", Flapjack.Exp.var Flapjack.VarKind.local "d15",
                    Flapjack.Exp.var Flapjack.VarKind.local "d15", Flapjack.Exp.var Flapjack.VarKind.local "d15",
                    Flapjack.Exp.var Flapjack.VarKind.local "d8"],
                Flapjack.Exp.var Flapjack.VarKind.local "d10"],
            Flapjack.Exp.var Flapjack.VarKind.local "d11"],
        Flapjack.Exp.var Flapjack.VarKind.local "d12"],
    Flapjack.Exp.var Flapjack.VarKind.local "d13"]) globalBody632_352

def globalBody632_354 : Prog (BitVec 64) :=
.dec ("t6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "d6", Flapjack.Exp.var Flapjack.VarKind.local "d14",
            Flapjack.Exp.var Flapjack.VarKind.local "d14", Flapjack.Exp.var Flapjack.VarKind.local "d15",
            Flapjack.Exp.var Flapjack.VarKind.local "d15", Flapjack.Exp.var Flapjack.VarKind.local "d14",
            Flapjack.Exp.var Flapjack.VarKind.local "d13"],
        Flapjack.Exp.var Flapjack.VarKind.local "d8"],
    Flapjack.Exp.var Flapjack.VarKind.local "d9"]) globalBody632_353

def globalBody632_355 : Prog (BitVec 64) :=
.dec ("t5") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "d5", Flapjack.Exp.var Flapjack.VarKind.local "d13",
            Flapjack.Exp.var Flapjack.VarKind.local "d13", Flapjack.Exp.var Flapjack.VarKind.local "d14",
            Flapjack.Exp.var Flapjack.VarKind.local "d14", Flapjack.Exp.var Flapjack.VarKind.local "d15"],
        Flapjack.Exp.var Flapjack.VarKind.local "d10"],
    Flapjack.Exp.var Flapjack.VarKind.local "d11"]) globalBody632_354

def globalBody632_356 : Prog (BitVec 64) :=
.dec ("t4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "d4", Flapjack.Exp.var Flapjack.VarKind.local "d12",
            Flapjack.Exp.var Flapjack.VarKind.local "d12", Flapjack.Exp.var Flapjack.VarKind.local "d13",
            Flapjack.Exp.var Flapjack.VarKind.local "d13", Flapjack.Exp.var Flapjack.VarKind.local "d14"],
        Flapjack.Exp.var Flapjack.VarKind.local "d9"],
    Flapjack.Exp.var Flapjack.VarKind.local "d10"]) globalBody632_355

def globalBody632_357 : Prog (BitVec 64) :=
.dec ("t3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "d3", Flapjack.Exp.var Flapjack.VarKind.local "d11",
                Flapjack.Exp.var Flapjack.VarKind.local "d11", Flapjack.Exp.var Flapjack.VarKind.local "d12",
                Flapjack.Exp.var Flapjack.VarKind.local "d12", Flapjack.Exp.var Flapjack.VarKind.local "d13"],
            Flapjack.Exp.var Flapjack.VarKind.local "d15"],
        Flapjack.Exp.var Flapjack.VarKind.local "d8"],
    Flapjack.Exp.var Flapjack.VarKind.local "d9"]) globalBody632_356

def globalBody632_358 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "d2", Flapjack.Exp.var Flapjack.VarKind.local "d10",
                Flapjack.Exp.var Flapjack.VarKind.local "d11"],
            Flapjack.Exp.var Flapjack.VarKind.local "d13"],
        Flapjack.Exp.var Flapjack.VarKind.local "d14"],
    Flapjack.Exp.var Flapjack.VarKind.local "d15"]) globalBody632_357

def globalBody632_359 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.sub
              [Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "d1", Flapjack.Exp.var Flapjack.VarKind.local "d9",
                    Flapjack.Exp.var Flapjack.VarKind.local "d10"],
                Flapjack.Exp.var Flapjack.VarKind.local "d12"],
            Flapjack.Exp.var Flapjack.VarKind.local "d13"],
        Flapjack.Exp.var Flapjack.VarKind.local "d14"],
    Flapjack.Exp.var Flapjack.VarKind.local "d15"]) globalBody632_358

def globalBody632_360 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.sub
              [Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "d0", Flapjack.Exp.var Flapjack.VarKind.local "d8",
                    Flapjack.Exp.var Flapjack.VarKind.local "d9"],
                Flapjack.Exp.var Flapjack.VarKind.local "d11"],
            Flapjack.Exp.var Flapjack.VarKind.local "d12"],
        Flapjack.Exp.var Flapjack.VarKind.local "d13"],
    Flapjack.Exp.var Flapjack.VarKind.local "d14"]) globalBody632_359

def globalBody632_361 : Prog (BitVec 64) :=
.seq globalBody632_306 globalBody632_360

def globalBody632_362 : Prog (BitVec 64) :=
.dec ("d15") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_361

def globalBody632_363 : Prog (BitVec 64) :=
.dec ("d14") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_362

def globalBody632_364 : Prog (BitVec 64) :=
.dec ("d13") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_363

def globalBody632_365 : Prog (BitVec 64) :=
.dec ("d12") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_364

def globalBody632_366 : Prog (BitVec 64) :=
.dec ("d11") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_365

def globalBody632_367 : Prog (BitVec 64) :=
.dec ("d10") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_366

def globalBody632_368 : Prog (BitVec 64) :=
.dec ("d9") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_367

def globalBody632_369 : Prog (BitVec 64) :=
.dec ("d8") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_368

def globalBody632_370 : Prog (BitVec 64) :=
.dec ("d7") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_369

def globalBody632_371 : Prog (BitVec 64) :=
.dec ("d6") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_370

def globalBody632_372 : Prog (BitVec 64) :=
.dec ("d5") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_371

def globalBody632_373 : Prog (BitVec 64) :=
.dec ("d4") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_372

def globalBody632_374 : Prog (BitVec 64) :=
.dec ("d3") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_373

def globalBody632_375 : Prog (BitVec 64) :=
.dec ("d2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_374

def globalBody632_376 : Prog (BitVec 64) :=
.dec ("d1") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_375

def globalBody632_377 : Prog (BitVec 64) :=
.dec ("d0") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_376

def globalBody632_378 : Prog (BitVec 64) :=
.dec ("col") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_377

def globalBody632_379 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_378

def globalBody632_380 : Prog (BitVec 64) :=
.dec ("Hc") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_379

def globalBody632_381 : Prog (BitVec 64) :=
.dec ("Lc") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_380

def globalBody632_382 : Prog (BitVec 64) :=
.dec ("H") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_381

def globalBody632_383 : Prog (BitVec 64) :=
.dec ("L") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_382

def globalBody632_384 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody632_383

def globalBody632_385 : Prog (BitVec 64) :=
.dec ("a7") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody632_384

def globalBody632_386 : Prog (BitVec 64) :=
.dec ("a6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody632_385

def globalBody632_387 : Prog (BitVec 64) :=
.dec ("a5") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody632_386

def globalBody632_388 : Prog (BitVec 64) :=
.dec ("a4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody632_387

def globalBody632_389 : Prog (BitVec 64) :=
.dec ("a3") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody632_388

def globalBody632_390 : Prog (BitVec 64) :=
.dec ("a2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody632_389

def globalBody632_391 : Prog (BitVec 64) :=
.dec ("a1") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody632_390

def globalBody632_392 : Prog (BitVec 64) :=
.dec ("a0") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody632_391

def globalData632 : Decl (BitVec 64) :=
.function { name := "p256_fp_sqr", inline := false, exported := false, params := [("a", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := globalBody632_392, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput632 := Pancake.PanLang.declToHOL globalData632
end InitECandidate.Proofs.FrontendStages.Declarations
