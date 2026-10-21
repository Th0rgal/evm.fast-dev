import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data631
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate612
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody631_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody631_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "L"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "L",
      Flapjack.Exp.op Flapjack.BinOp.and
        [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 4294967295#64]])

def globalBody631_2 : Prog (BitVec 64) :=
.seq globalBody631_0 globalBody631_1

def globalBody631_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "H"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "H",
      Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "p") (Flapjack.Exp.const 32#64)])

def globalBody631_4 : Prog (BitVec 64) :=
.seq globalBody631_2 globalBody631_3

def globalBody631_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "L", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody631_6 : Prog (BitVec 64) :=
.seq globalBody631_4 globalBody631_5

def globalBody631_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d0"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_8 : Prog (BitVec 64) :=
.seq globalBody631_6 globalBody631_7

def globalBody631_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "col") (Flapjack.Exp.const 32#64),
      Flapjack.Exp.var Flapjack.VarKind.local "H"])

def globalBody631_10 : Prog (BitVec 64) :=
.seq globalBody631_8 globalBody631_9

def globalBody631_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "L" (Flapjack.Exp.const 0#64)

def globalBody631_12 : Prog (BitVec 64) :=
.seq globalBody631_10 globalBody631_11

def globalBody631_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "H" (Flapjack.Exp.const 0#64)

def globalBody631_14 : Prog (BitVec 64) :=
.seq globalBody631_12 globalBody631_13

def globalBody631_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody631_16 : Prog (BitVec 64) :=
.seq globalBody631_14 globalBody631_15

def globalBody631_17 : Prog (BitVec 64) :=
.seq globalBody631_16 globalBody631_1

def globalBody631_18 : Prog (BitVec 64) :=
.seq globalBody631_17 globalBody631_3

def globalBody631_19 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody631_20 : Prog (BitVec 64) :=
.seq globalBody631_18 globalBody631_19

def globalBody631_21 : Prog (BitVec 64) :=
.seq globalBody631_20 globalBody631_1

def globalBody631_22 : Prog (BitVec 64) :=
.seq globalBody631_21 globalBody631_3

def globalBody631_23 : Prog (BitVec 64) :=
.seq globalBody631_22 globalBody631_5

def globalBody631_24 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d1"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_25 : Prog (BitVec 64) :=
.seq globalBody631_23 globalBody631_24

def globalBody631_26 : Prog (BitVec 64) :=
.seq globalBody631_25 globalBody631_9

def globalBody631_27 : Prog (BitVec 64) :=
.seq globalBody631_26 globalBody631_11

def globalBody631_28 : Prog (BitVec 64) :=
.seq globalBody631_27 globalBody631_13

def globalBody631_29 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody631_30 : Prog (BitVec 64) :=
.seq globalBody631_28 globalBody631_29

def globalBody631_31 : Prog (BitVec 64) :=
.seq globalBody631_30 globalBody631_1

def globalBody631_32 : Prog (BitVec 64) :=
.seq globalBody631_31 globalBody631_3

def globalBody631_33 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody631_34 : Prog (BitVec 64) :=
.seq globalBody631_32 globalBody631_33

def globalBody631_35 : Prog (BitVec 64) :=
.seq globalBody631_34 globalBody631_1

def globalBody631_36 : Prog (BitVec 64) :=
.seq globalBody631_35 globalBody631_3

def globalBody631_37 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody631_38 : Prog (BitVec 64) :=
.seq globalBody631_36 globalBody631_37

def globalBody631_39 : Prog (BitVec 64) :=
.seq globalBody631_38 globalBody631_1

def globalBody631_40 : Prog (BitVec 64) :=
.seq globalBody631_39 globalBody631_3

def globalBody631_41 : Prog (BitVec 64) :=
.seq globalBody631_40 globalBody631_5

def globalBody631_42 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d2"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_43 : Prog (BitVec 64) :=
.seq globalBody631_41 globalBody631_42

def globalBody631_44 : Prog (BitVec 64) :=
.seq globalBody631_43 globalBody631_9

def globalBody631_45 : Prog (BitVec 64) :=
.seq globalBody631_44 globalBody631_11

def globalBody631_46 : Prog (BitVec 64) :=
.seq globalBody631_45 globalBody631_13

def globalBody631_47 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody631_48 : Prog (BitVec 64) :=
.seq globalBody631_46 globalBody631_47

def globalBody631_49 : Prog (BitVec 64) :=
.seq globalBody631_48 globalBody631_1

def globalBody631_50 : Prog (BitVec 64) :=
.seq globalBody631_49 globalBody631_3

def globalBody631_51 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody631_52 : Prog (BitVec 64) :=
.seq globalBody631_50 globalBody631_51

def globalBody631_53 : Prog (BitVec 64) :=
.seq globalBody631_52 globalBody631_1

def globalBody631_54 : Prog (BitVec 64) :=
.seq globalBody631_53 globalBody631_3

def globalBody631_55 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody631_56 : Prog (BitVec 64) :=
.seq globalBody631_54 globalBody631_55

def globalBody631_57 : Prog (BitVec 64) :=
.seq globalBody631_56 globalBody631_1

def globalBody631_58 : Prog (BitVec 64) :=
.seq globalBody631_57 globalBody631_3

def globalBody631_59 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody631_60 : Prog (BitVec 64) :=
.seq globalBody631_58 globalBody631_59

def globalBody631_61 : Prog (BitVec 64) :=
.seq globalBody631_60 globalBody631_1

def globalBody631_62 : Prog (BitVec 64) :=
.seq globalBody631_61 globalBody631_3

def globalBody631_63 : Prog (BitVec 64) :=
.seq globalBody631_62 globalBody631_5

def globalBody631_64 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d3"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_65 : Prog (BitVec 64) :=
.seq globalBody631_63 globalBody631_64

def globalBody631_66 : Prog (BitVec 64) :=
.seq globalBody631_65 globalBody631_9

def globalBody631_67 : Prog (BitVec 64) :=
.seq globalBody631_66 globalBody631_11

def globalBody631_68 : Prog (BitVec 64) :=
.seq globalBody631_67 globalBody631_13

def globalBody631_69 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody631_70 : Prog (BitVec 64) :=
.seq globalBody631_68 globalBody631_69

def globalBody631_71 : Prog (BitVec 64) :=
.seq globalBody631_70 globalBody631_1

def globalBody631_72 : Prog (BitVec 64) :=
.seq globalBody631_71 globalBody631_3

def globalBody631_73 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody631_74 : Prog (BitVec 64) :=
.seq globalBody631_72 globalBody631_73

def globalBody631_75 : Prog (BitVec 64) :=
.seq globalBody631_74 globalBody631_1

def globalBody631_76 : Prog (BitVec 64) :=
.seq globalBody631_75 globalBody631_3

def globalBody631_77 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody631_78 : Prog (BitVec 64) :=
.seq globalBody631_76 globalBody631_77

def globalBody631_79 : Prog (BitVec 64) :=
.seq globalBody631_78 globalBody631_1

def globalBody631_80 : Prog (BitVec 64) :=
.seq globalBody631_79 globalBody631_3

def globalBody631_81 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody631_82 : Prog (BitVec 64) :=
.seq globalBody631_80 globalBody631_81

def globalBody631_83 : Prog (BitVec 64) :=
.seq globalBody631_82 globalBody631_1

def globalBody631_84 : Prog (BitVec 64) :=
.seq globalBody631_83 globalBody631_3

def globalBody631_85 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody631_86 : Prog (BitVec 64) :=
.seq globalBody631_84 globalBody631_85

def globalBody631_87 : Prog (BitVec 64) :=
.seq globalBody631_86 globalBody631_1

def globalBody631_88 : Prog (BitVec 64) :=
.seq globalBody631_87 globalBody631_3

def globalBody631_89 : Prog (BitVec 64) :=
.seq globalBody631_88 globalBody631_5

def globalBody631_90 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d4"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_91 : Prog (BitVec 64) :=
.seq globalBody631_89 globalBody631_90

def globalBody631_92 : Prog (BitVec 64) :=
.seq globalBody631_91 globalBody631_9

def globalBody631_93 : Prog (BitVec 64) :=
.seq globalBody631_92 globalBody631_11

def globalBody631_94 : Prog (BitVec 64) :=
.seq globalBody631_93 globalBody631_13

def globalBody631_95 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody631_96 : Prog (BitVec 64) :=
.seq globalBody631_94 globalBody631_95

def globalBody631_97 : Prog (BitVec 64) :=
.seq globalBody631_96 globalBody631_1

def globalBody631_98 : Prog (BitVec 64) :=
.seq globalBody631_97 globalBody631_3

def globalBody631_99 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody631_100 : Prog (BitVec 64) :=
.seq globalBody631_98 globalBody631_99

def globalBody631_101 : Prog (BitVec 64) :=
.seq globalBody631_100 globalBody631_1

def globalBody631_102 : Prog (BitVec 64) :=
.seq globalBody631_101 globalBody631_3

def globalBody631_103 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody631_104 : Prog (BitVec 64) :=
.seq globalBody631_102 globalBody631_103

def globalBody631_105 : Prog (BitVec 64) :=
.seq globalBody631_104 globalBody631_1

def globalBody631_106 : Prog (BitVec 64) :=
.seq globalBody631_105 globalBody631_3

def globalBody631_107 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody631_108 : Prog (BitVec 64) :=
.seq globalBody631_106 globalBody631_107

def globalBody631_109 : Prog (BitVec 64) :=
.seq globalBody631_108 globalBody631_1

def globalBody631_110 : Prog (BitVec 64) :=
.seq globalBody631_109 globalBody631_3

def globalBody631_111 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody631_112 : Prog (BitVec 64) :=
.seq globalBody631_110 globalBody631_111

def globalBody631_113 : Prog (BitVec 64) :=
.seq globalBody631_112 globalBody631_1

def globalBody631_114 : Prog (BitVec 64) :=
.seq globalBody631_113 globalBody631_3

def globalBody631_115 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody631_116 : Prog (BitVec 64) :=
.seq globalBody631_114 globalBody631_115

def globalBody631_117 : Prog (BitVec 64) :=
.seq globalBody631_116 globalBody631_1

def globalBody631_118 : Prog (BitVec 64) :=
.seq globalBody631_117 globalBody631_3

def globalBody631_119 : Prog (BitVec 64) :=
.seq globalBody631_118 globalBody631_5

def globalBody631_120 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d5"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_121 : Prog (BitVec 64) :=
.seq globalBody631_119 globalBody631_120

def globalBody631_122 : Prog (BitVec 64) :=
.seq globalBody631_121 globalBody631_9

def globalBody631_123 : Prog (BitVec 64) :=
.seq globalBody631_122 globalBody631_11

def globalBody631_124 : Prog (BitVec 64) :=
.seq globalBody631_123 globalBody631_13

def globalBody631_125 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody631_126 : Prog (BitVec 64) :=
.seq globalBody631_124 globalBody631_125

def globalBody631_127 : Prog (BitVec 64) :=
.seq globalBody631_126 globalBody631_1

def globalBody631_128 : Prog (BitVec 64) :=
.seq globalBody631_127 globalBody631_3

def globalBody631_129 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody631_130 : Prog (BitVec 64) :=
.seq globalBody631_128 globalBody631_129

def globalBody631_131 : Prog (BitVec 64) :=
.seq globalBody631_130 globalBody631_1

def globalBody631_132 : Prog (BitVec 64) :=
.seq globalBody631_131 globalBody631_3

def globalBody631_133 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody631_134 : Prog (BitVec 64) :=
.seq globalBody631_132 globalBody631_133

def globalBody631_135 : Prog (BitVec 64) :=
.seq globalBody631_134 globalBody631_1

def globalBody631_136 : Prog (BitVec 64) :=
.seq globalBody631_135 globalBody631_3

def globalBody631_137 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody631_138 : Prog (BitVec 64) :=
.seq globalBody631_136 globalBody631_137

def globalBody631_139 : Prog (BitVec 64) :=
.seq globalBody631_138 globalBody631_1

def globalBody631_140 : Prog (BitVec 64) :=
.seq globalBody631_139 globalBody631_3

def globalBody631_141 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody631_142 : Prog (BitVec 64) :=
.seq globalBody631_140 globalBody631_141

def globalBody631_143 : Prog (BitVec 64) :=
.seq globalBody631_142 globalBody631_1

def globalBody631_144 : Prog (BitVec 64) :=
.seq globalBody631_143 globalBody631_3

def globalBody631_145 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody631_146 : Prog (BitVec 64) :=
.seq globalBody631_144 globalBody631_145

def globalBody631_147 : Prog (BitVec 64) :=
.seq globalBody631_146 globalBody631_1

def globalBody631_148 : Prog (BitVec 64) :=
.seq globalBody631_147 globalBody631_3

def globalBody631_149 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody631_150 : Prog (BitVec 64) :=
.seq globalBody631_148 globalBody631_149

def globalBody631_151 : Prog (BitVec 64) :=
.seq globalBody631_150 globalBody631_1

def globalBody631_152 : Prog (BitVec 64) :=
.seq globalBody631_151 globalBody631_3

def globalBody631_153 : Prog (BitVec 64) :=
.seq globalBody631_152 globalBody631_5

def globalBody631_154 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d6"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_155 : Prog (BitVec 64) :=
.seq globalBody631_153 globalBody631_154

def globalBody631_156 : Prog (BitVec 64) :=
.seq globalBody631_155 globalBody631_9

def globalBody631_157 : Prog (BitVec 64) :=
.seq globalBody631_156 globalBody631_11

def globalBody631_158 : Prog (BitVec 64) :=
.seq globalBody631_157 globalBody631_13

def globalBody631_159 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody631_160 : Prog (BitVec 64) :=
.seq globalBody631_158 globalBody631_159

def globalBody631_161 : Prog (BitVec 64) :=
.seq globalBody631_160 globalBody631_1

def globalBody631_162 : Prog (BitVec 64) :=
.seq globalBody631_161 globalBody631_3

def globalBody631_163 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody631_164 : Prog (BitVec 64) :=
.seq globalBody631_162 globalBody631_163

def globalBody631_165 : Prog (BitVec 64) :=
.seq globalBody631_164 globalBody631_1

def globalBody631_166 : Prog (BitVec 64) :=
.seq globalBody631_165 globalBody631_3

def globalBody631_167 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody631_168 : Prog (BitVec 64) :=
.seq globalBody631_166 globalBody631_167

def globalBody631_169 : Prog (BitVec 64) :=
.seq globalBody631_168 globalBody631_1

def globalBody631_170 : Prog (BitVec 64) :=
.seq globalBody631_169 globalBody631_3

def globalBody631_171 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody631_172 : Prog (BitVec 64) :=
.seq globalBody631_170 globalBody631_171

def globalBody631_173 : Prog (BitVec 64) :=
.seq globalBody631_172 globalBody631_1

def globalBody631_174 : Prog (BitVec 64) :=
.seq globalBody631_173 globalBody631_3

def globalBody631_175 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody631_176 : Prog (BitVec 64) :=
.seq globalBody631_174 globalBody631_175

def globalBody631_177 : Prog (BitVec 64) :=
.seq globalBody631_176 globalBody631_1

def globalBody631_178 : Prog (BitVec 64) :=
.seq globalBody631_177 globalBody631_3

def globalBody631_179 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody631_180 : Prog (BitVec 64) :=
.seq globalBody631_178 globalBody631_179

def globalBody631_181 : Prog (BitVec 64) :=
.seq globalBody631_180 globalBody631_1

def globalBody631_182 : Prog (BitVec 64) :=
.seq globalBody631_181 globalBody631_3

def globalBody631_183 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody631_184 : Prog (BitVec 64) :=
.seq globalBody631_182 globalBody631_183

def globalBody631_185 : Prog (BitVec 64) :=
.seq globalBody631_184 globalBody631_1

def globalBody631_186 : Prog (BitVec 64) :=
.seq globalBody631_185 globalBody631_3

def globalBody631_187 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody631_188 : Prog (BitVec 64) :=
.seq globalBody631_186 globalBody631_187

def globalBody631_189 : Prog (BitVec 64) :=
.seq globalBody631_188 globalBody631_1

def globalBody631_190 : Prog (BitVec 64) :=
.seq globalBody631_189 globalBody631_3

def globalBody631_191 : Prog (BitVec 64) :=
.seq globalBody631_190 globalBody631_5

def globalBody631_192 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d7"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_193 : Prog (BitVec 64) :=
.seq globalBody631_191 globalBody631_192

def globalBody631_194 : Prog (BitVec 64) :=
.seq globalBody631_193 globalBody631_9

def globalBody631_195 : Prog (BitVec 64) :=
.seq globalBody631_194 globalBody631_11

def globalBody631_196 : Prog (BitVec 64) :=
.seq globalBody631_195 globalBody631_13

def globalBody631_197 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody631_198 : Prog (BitVec 64) :=
.seq globalBody631_196 globalBody631_197

def globalBody631_199 : Prog (BitVec 64) :=
.seq globalBody631_198 globalBody631_1

def globalBody631_200 : Prog (BitVec 64) :=
.seq globalBody631_199 globalBody631_3

def globalBody631_201 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody631_202 : Prog (BitVec 64) :=
.seq globalBody631_200 globalBody631_201

def globalBody631_203 : Prog (BitVec 64) :=
.seq globalBody631_202 globalBody631_1

def globalBody631_204 : Prog (BitVec 64) :=
.seq globalBody631_203 globalBody631_3

def globalBody631_205 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody631_206 : Prog (BitVec 64) :=
.seq globalBody631_204 globalBody631_205

def globalBody631_207 : Prog (BitVec 64) :=
.seq globalBody631_206 globalBody631_1

def globalBody631_208 : Prog (BitVec 64) :=
.seq globalBody631_207 globalBody631_3

def globalBody631_209 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody631_210 : Prog (BitVec 64) :=
.seq globalBody631_208 globalBody631_209

def globalBody631_211 : Prog (BitVec 64) :=
.seq globalBody631_210 globalBody631_1

def globalBody631_212 : Prog (BitVec 64) :=
.seq globalBody631_211 globalBody631_3

def globalBody631_213 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody631_214 : Prog (BitVec 64) :=
.seq globalBody631_212 globalBody631_213

def globalBody631_215 : Prog (BitVec 64) :=
.seq globalBody631_214 globalBody631_1

def globalBody631_216 : Prog (BitVec 64) :=
.seq globalBody631_215 globalBody631_3

def globalBody631_217 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody631_218 : Prog (BitVec 64) :=
.seq globalBody631_216 globalBody631_217

def globalBody631_219 : Prog (BitVec 64) :=
.seq globalBody631_218 globalBody631_1

def globalBody631_220 : Prog (BitVec 64) :=
.seq globalBody631_219 globalBody631_3

def globalBody631_221 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody631_222 : Prog (BitVec 64) :=
.seq globalBody631_220 globalBody631_221

def globalBody631_223 : Prog (BitVec 64) :=
.seq globalBody631_222 globalBody631_1

def globalBody631_224 : Prog (BitVec 64) :=
.seq globalBody631_223 globalBody631_3

def globalBody631_225 : Prog (BitVec 64) :=
.seq globalBody631_224 globalBody631_5

def globalBody631_226 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d8"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_227 : Prog (BitVec 64) :=
.seq globalBody631_225 globalBody631_226

def globalBody631_228 : Prog (BitVec 64) :=
.seq globalBody631_227 globalBody631_9

def globalBody631_229 : Prog (BitVec 64) :=
.seq globalBody631_228 globalBody631_11

def globalBody631_230 : Prog (BitVec 64) :=
.seq globalBody631_229 globalBody631_13

def globalBody631_231 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody631_232 : Prog (BitVec 64) :=
.seq globalBody631_230 globalBody631_231

def globalBody631_233 : Prog (BitVec 64) :=
.seq globalBody631_232 globalBody631_1

def globalBody631_234 : Prog (BitVec 64) :=
.seq globalBody631_233 globalBody631_3

def globalBody631_235 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody631_236 : Prog (BitVec 64) :=
.seq globalBody631_234 globalBody631_235

def globalBody631_237 : Prog (BitVec 64) :=
.seq globalBody631_236 globalBody631_1

def globalBody631_238 : Prog (BitVec 64) :=
.seq globalBody631_237 globalBody631_3

def globalBody631_239 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody631_240 : Prog (BitVec 64) :=
.seq globalBody631_238 globalBody631_239

def globalBody631_241 : Prog (BitVec 64) :=
.seq globalBody631_240 globalBody631_1

def globalBody631_242 : Prog (BitVec 64) :=
.seq globalBody631_241 globalBody631_3

def globalBody631_243 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody631_244 : Prog (BitVec 64) :=
.seq globalBody631_242 globalBody631_243

def globalBody631_245 : Prog (BitVec 64) :=
.seq globalBody631_244 globalBody631_1

def globalBody631_246 : Prog (BitVec 64) :=
.seq globalBody631_245 globalBody631_3

def globalBody631_247 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody631_248 : Prog (BitVec 64) :=
.seq globalBody631_246 globalBody631_247

def globalBody631_249 : Prog (BitVec 64) :=
.seq globalBody631_248 globalBody631_1

def globalBody631_250 : Prog (BitVec 64) :=
.seq globalBody631_249 globalBody631_3

def globalBody631_251 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody631_252 : Prog (BitVec 64) :=
.seq globalBody631_250 globalBody631_251

def globalBody631_253 : Prog (BitVec 64) :=
.seq globalBody631_252 globalBody631_1

def globalBody631_254 : Prog (BitVec 64) :=
.seq globalBody631_253 globalBody631_3

def globalBody631_255 : Prog (BitVec 64) :=
.seq globalBody631_254 globalBody631_5

def globalBody631_256 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d9"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_257 : Prog (BitVec 64) :=
.seq globalBody631_255 globalBody631_256

def globalBody631_258 : Prog (BitVec 64) :=
.seq globalBody631_257 globalBody631_9

def globalBody631_259 : Prog (BitVec 64) :=
.seq globalBody631_258 globalBody631_11

def globalBody631_260 : Prog (BitVec 64) :=
.seq globalBody631_259 globalBody631_13

def globalBody631_261 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody631_262 : Prog (BitVec 64) :=
.seq globalBody631_260 globalBody631_261

def globalBody631_263 : Prog (BitVec 64) :=
.seq globalBody631_262 globalBody631_1

def globalBody631_264 : Prog (BitVec 64) :=
.seq globalBody631_263 globalBody631_3

def globalBody631_265 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody631_266 : Prog (BitVec 64) :=
.seq globalBody631_264 globalBody631_265

def globalBody631_267 : Prog (BitVec 64) :=
.seq globalBody631_266 globalBody631_1

def globalBody631_268 : Prog (BitVec 64) :=
.seq globalBody631_267 globalBody631_3

def globalBody631_269 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody631_270 : Prog (BitVec 64) :=
.seq globalBody631_268 globalBody631_269

def globalBody631_271 : Prog (BitVec 64) :=
.seq globalBody631_270 globalBody631_1

def globalBody631_272 : Prog (BitVec 64) :=
.seq globalBody631_271 globalBody631_3

def globalBody631_273 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody631_274 : Prog (BitVec 64) :=
.seq globalBody631_272 globalBody631_273

def globalBody631_275 : Prog (BitVec 64) :=
.seq globalBody631_274 globalBody631_1

def globalBody631_276 : Prog (BitVec 64) :=
.seq globalBody631_275 globalBody631_3

def globalBody631_277 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody631_278 : Prog (BitVec 64) :=
.seq globalBody631_276 globalBody631_277

def globalBody631_279 : Prog (BitVec 64) :=
.seq globalBody631_278 globalBody631_1

def globalBody631_280 : Prog (BitVec 64) :=
.seq globalBody631_279 globalBody631_3

def globalBody631_281 : Prog (BitVec 64) :=
.seq globalBody631_280 globalBody631_5

def globalBody631_282 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d10"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_283 : Prog (BitVec 64) :=
.seq globalBody631_281 globalBody631_282

def globalBody631_284 : Prog (BitVec 64) :=
.seq globalBody631_283 globalBody631_9

def globalBody631_285 : Prog (BitVec 64) :=
.seq globalBody631_284 globalBody631_11

def globalBody631_286 : Prog (BitVec 64) :=
.seq globalBody631_285 globalBody631_13

def globalBody631_287 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody631_288 : Prog (BitVec 64) :=
.seq globalBody631_286 globalBody631_287

def globalBody631_289 : Prog (BitVec 64) :=
.seq globalBody631_288 globalBody631_1

def globalBody631_290 : Prog (BitVec 64) :=
.seq globalBody631_289 globalBody631_3

def globalBody631_291 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody631_292 : Prog (BitVec 64) :=
.seq globalBody631_290 globalBody631_291

def globalBody631_293 : Prog (BitVec 64) :=
.seq globalBody631_292 globalBody631_1

def globalBody631_294 : Prog (BitVec 64) :=
.seq globalBody631_293 globalBody631_3

def globalBody631_295 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody631_296 : Prog (BitVec 64) :=
.seq globalBody631_294 globalBody631_295

def globalBody631_297 : Prog (BitVec 64) :=
.seq globalBody631_296 globalBody631_1

def globalBody631_298 : Prog (BitVec 64) :=
.seq globalBody631_297 globalBody631_3

def globalBody631_299 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody631_300 : Prog (BitVec 64) :=
.seq globalBody631_298 globalBody631_299

def globalBody631_301 : Prog (BitVec 64) :=
.seq globalBody631_300 globalBody631_1

def globalBody631_302 : Prog (BitVec 64) :=
.seq globalBody631_301 globalBody631_3

def globalBody631_303 : Prog (BitVec 64) :=
.seq globalBody631_302 globalBody631_5

def globalBody631_304 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d11"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_305 : Prog (BitVec 64) :=
.seq globalBody631_303 globalBody631_304

def globalBody631_306 : Prog (BitVec 64) :=
.seq globalBody631_305 globalBody631_9

def globalBody631_307 : Prog (BitVec 64) :=
.seq globalBody631_306 globalBody631_11

def globalBody631_308 : Prog (BitVec 64) :=
.seq globalBody631_307 globalBody631_13

def globalBody631_309 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody631_310 : Prog (BitVec 64) :=
.seq globalBody631_308 globalBody631_309

def globalBody631_311 : Prog (BitVec 64) :=
.seq globalBody631_310 globalBody631_1

def globalBody631_312 : Prog (BitVec 64) :=
.seq globalBody631_311 globalBody631_3

def globalBody631_313 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody631_314 : Prog (BitVec 64) :=
.seq globalBody631_312 globalBody631_313

def globalBody631_315 : Prog (BitVec 64) :=
.seq globalBody631_314 globalBody631_1

def globalBody631_316 : Prog (BitVec 64) :=
.seq globalBody631_315 globalBody631_3

def globalBody631_317 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody631_318 : Prog (BitVec 64) :=
.seq globalBody631_316 globalBody631_317

def globalBody631_319 : Prog (BitVec 64) :=
.seq globalBody631_318 globalBody631_1

def globalBody631_320 : Prog (BitVec 64) :=
.seq globalBody631_319 globalBody631_3

def globalBody631_321 : Prog (BitVec 64) :=
.seq globalBody631_320 globalBody631_5

def globalBody631_322 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d12"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_323 : Prog (BitVec 64) :=
.seq globalBody631_321 globalBody631_322

def globalBody631_324 : Prog (BitVec 64) :=
.seq globalBody631_323 globalBody631_9

def globalBody631_325 : Prog (BitVec 64) :=
.seq globalBody631_324 globalBody631_11

def globalBody631_326 : Prog (BitVec 64) :=
.seq globalBody631_325 globalBody631_13

def globalBody631_327 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody631_328 : Prog (BitVec 64) :=
.seq globalBody631_326 globalBody631_327

def globalBody631_329 : Prog (BitVec 64) :=
.seq globalBody631_328 globalBody631_1

def globalBody631_330 : Prog (BitVec 64) :=
.seq globalBody631_329 globalBody631_3

def globalBody631_331 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody631_332 : Prog (BitVec 64) :=
.seq globalBody631_330 globalBody631_331

def globalBody631_333 : Prog (BitVec 64) :=
.seq globalBody631_332 globalBody631_1

def globalBody631_334 : Prog (BitVec 64) :=
.seq globalBody631_333 globalBody631_3

def globalBody631_335 : Prog (BitVec 64) :=
.seq globalBody631_334 globalBody631_5

def globalBody631_336 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d13"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_337 : Prog (BitVec 64) :=
.seq globalBody631_335 globalBody631_336

def globalBody631_338 : Prog (BitVec 64) :=
.seq globalBody631_337 globalBody631_9

def globalBody631_339 : Prog (BitVec 64) :=
.seq globalBody631_338 globalBody631_11

def globalBody631_340 : Prog (BitVec 64) :=
.seq globalBody631_339 globalBody631_13

def globalBody631_341 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody631_342 : Prog (BitVec 64) :=
.seq globalBody631_340 globalBody631_341

def globalBody631_343 : Prog (BitVec 64) :=
.seq globalBody631_342 globalBody631_1

def globalBody631_344 : Prog (BitVec 64) :=
.seq globalBody631_343 globalBody631_3

def globalBody631_345 : Prog (BitVec 64) :=
.seq globalBody631_344 globalBody631_5

def globalBody631_346 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d14"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody631_347 : Prog (BitVec 64) :=
.seq globalBody631_345 globalBody631_346

def globalBody631_348 : Prog (BitVec 64) :=
.seq globalBody631_347 globalBody631_9

def globalBody631_349 : Prog (BitVec 64) :=
.seq globalBody631_348 globalBody631_11

def globalBody631_350 : Prog (BitVec 64) :=
.seq globalBody631_349 globalBody631_13

def globalBody631_351 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d15" (Flapjack.Exp.var Flapjack.VarKind.local "c")

def globalBody631_352 : Prog (BitVec 64) :=
.seq globalBody631_350 globalBody631_351

def globalBody631_353 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.shift Flapjack.Shift.asr (Flapjack.Exp.var Flapjack.VarKind.local "t0") (Flapjack.Exp.const 32#64))

def globalBody631_354 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody631_355 : Prog (BitVec 64) :=
.seq globalBody631_353 globalBody631_354

def globalBody631_356 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.shift Flapjack.Shift.asr (Flapjack.Exp.var Flapjack.VarKind.local "col") (Flapjack.Exp.const 32#64))

def globalBody631_357 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody631_358 : Prog (BitVec 64) :=
.seq globalBody631_356 globalBody631_357

def globalBody631_359 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t3", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody631_360 : Prog (BitVec 64) :=
.seq globalBody631_356 globalBody631_359

def globalBody631_361 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t4", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody631_362 : Prog (BitVec 64) :=
.seq globalBody631_356 globalBody631_361

def globalBody631_363 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t5", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody631_364 : Prog (BitVec 64) :=
.seq globalBody631_356 globalBody631_363

def globalBody631_365 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t6", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody631_366 : Prog (BitVec 64) :=
.seq globalBody631_356 globalBody631_365

def globalBody631_367 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t7", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody631_368 : Prog (BitVec 64) :=
.seq globalBody631_356 globalBody631_367

def globalBody631_369 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r"
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sa"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sa"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "sa"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "sa")])

def globalBody631_370 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "sa")])

def globalBody631_371 : Prog (BitVec 64) :=
.seq globalBody631_369 globalBody631_370

def globalBody631_372 : Prog (BitVec 64) :=
.decCall ("sa") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add_carry") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) globalBody631_371

def globalBody631_373 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "c") (Flapjack.Exp.const 0#64)) globalBody631_372

def globalBody631_374 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "u256_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
        Flapjack.Exp.const 18446744069414584321#64]]

def globalBody631_375 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "ltp"])

def globalBody631_376 : Prog (BitVec 64) :=
.seq globalBody631_374 globalBody631_375

def globalBody631_377 : Prog (BitVec 64) :=
.decCall ("ltp") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) globalBody631_376

def globalBody631_378 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "c")) globalBody631_377

def globalBody631_379 : Prog (BitVec 64) :=
.seq globalBody631_373 globalBody631_378

def globalBody631_380 : Prog (BitVec 64) :=
Flapjack.Prog.call none "p256_fp_reduce" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def globalBody631_381 : Prog (BitVec 64) :=
.seq globalBody631_379 globalBody631_380

def globalBody631_382 : Prog (BitVec 64) :=
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
          (Flapjack.Exp.const 32#64)]]) globalBody631_381

def globalBody631_383 : Prog (BitVec 64) :=
.seq globalBody631_356 globalBody631_382

def globalBody631_384 : Prog (BitVec 64) :=
.dec ("v7") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody631_383

def globalBody631_385 : Prog (BitVec 64) :=
.seq globalBody631_368 globalBody631_384

def globalBody631_386 : Prog (BitVec 64) :=
.dec ("v6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody631_385

def globalBody631_387 : Prog (BitVec 64) :=
.seq globalBody631_366 globalBody631_386

def globalBody631_388 : Prog (BitVec 64) :=
.dec ("v5") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody631_387

def globalBody631_389 : Prog (BitVec 64) :=
.seq globalBody631_364 globalBody631_388

def globalBody631_390 : Prog (BitVec 64) :=
.dec ("v4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody631_389

def globalBody631_391 : Prog (BitVec 64) :=
.seq globalBody631_362 globalBody631_390

def globalBody631_392 : Prog (BitVec 64) :=
.dec ("v3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody631_391

def globalBody631_393 : Prog (BitVec 64) :=
.seq globalBody631_360 globalBody631_392

def globalBody631_394 : Prog (BitVec 64) :=
.dec ("v2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody631_393

def globalBody631_395 : Prog (BitVec 64) :=
.seq globalBody631_358 globalBody631_394

def globalBody631_396 : Prog (BitVec 64) :=
.dec ("v1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64]) globalBody631_395

def globalBody631_397 : Prog (BitVec 64) :=
.seq globalBody631_355 globalBody631_396

def globalBody631_398 : Prog (BitVec 64) :=
.dec ("v0") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.const 4294967295#64]) globalBody631_397

def globalBody631_399 : Prog (BitVec 64) :=
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
    Flapjack.Exp.var Flapjack.VarKind.local "d13"]) globalBody631_398

def globalBody631_400 : Prog (BitVec 64) :=
.dec ("t6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "d6", Flapjack.Exp.var Flapjack.VarKind.local "d14",
            Flapjack.Exp.var Flapjack.VarKind.local "d14", Flapjack.Exp.var Flapjack.VarKind.local "d15",
            Flapjack.Exp.var Flapjack.VarKind.local "d15", Flapjack.Exp.var Flapjack.VarKind.local "d14",
            Flapjack.Exp.var Flapjack.VarKind.local "d13"],
        Flapjack.Exp.var Flapjack.VarKind.local "d8"],
    Flapjack.Exp.var Flapjack.VarKind.local "d9"]) globalBody631_399

def globalBody631_401 : Prog (BitVec 64) :=
.dec ("t5") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "d5", Flapjack.Exp.var Flapjack.VarKind.local "d13",
            Flapjack.Exp.var Flapjack.VarKind.local "d13", Flapjack.Exp.var Flapjack.VarKind.local "d14",
            Flapjack.Exp.var Flapjack.VarKind.local "d14", Flapjack.Exp.var Flapjack.VarKind.local "d15"],
        Flapjack.Exp.var Flapjack.VarKind.local "d10"],
    Flapjack.Exp.var Flapjack.VarKind.local "d11"]) globalBody631_400

def globalBody631_402 : Prog (BitVec 64) :=
.dec ("t4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "d4", Flapjack.Exp.var Flapjack.VarKind.local "d12",
            Flapjack.Exp.var Flapjack.VarKind.local "d12", Flapjack.Exp.var Flapjack.VarKind.local "d13",
            Flapjack.Exp.var Flapjack.VarKind.local "d13", Flapjack.Exp.var Flapjack.VarKind.local "d14"],
        Flapjack.Exp.var Flapjack.VarKind.local "d9"],
    Flapjack.Exp.var Flapjack.VarKind.local "d10"]) globalBody631_401

def globalBody631_403 : Prog (BitVec 64) :=
.dec ("t3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "d3", Flapjack.Exp.var Flapjack.VarKind.local "d11",
                Flapjack.Exp.var Flapjack.VarKind.local "d11", Flapjack.Exp.var Flapjack.VarKind.local "d12",
                Flapjack.Exp.var Flapjack.VarKind.local "d12", Flapjack.Exp.var Flapjack.VarKind.local "d13"],
            Flapjack.Exp.var Flapjack.VarKind.local "d15"],
        Flapjack.Exp.var Flapjack.VarKind.local "d8"],
    Flapjack.Exp.var Flapjack.VarKind.local "d9"]) globalBody631_402

def globalBody631_404 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "d2", Flapjack.Exp.var Flapjack.VarKind.local "d10",
                Flapjack.Exp.var Flapjack.VarKind.local "d11"],
            Flapjack.Exp.var Flapjack.VarKind.local "d13"],
        Flapjack.Exp.var Flapjack.VarKind.local "d14"],
    Flapjack.Exp.var Flapjack.VarKind.local "d15"]) globalBody631_403

def globalBody631_405 : Prog (BitVec 64) :=
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
    Flapjack.Exp.var Flapjack.VarKind.local "d15"]) globalBody631_404

def globalBody631_406 : Prog (BitVec 64) :=
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
    Flapjack.Exp.var Flapjack.VarKind.local "d14"]) globalBody631_405

def globalBody631_407 : Prog (BitVec 64) :=
.seq globalBody631_352 globalBody631_406

def globalBody631_408 : Prog (BitVec 64) :=
.dec ("d15") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_407

def globalBody631_409 : Prog (BitVec 64) :=
.dec ("d14") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_408

def globalBody631_410 : Prog (BitVec 64) :=
.dec ("d13") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_409

def globalBody631_411 : Prog (BitVec 64) :=
.dec ("d12") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_410

def globalBody631_412 : Prog (BitVec 64) :=
.dec ("d11") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_411

def globalBody631_413 : Prog (BitVec 64) :=
.dec ("d10") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_412

def globalBody631_414 : Prog (BitVec 64) :=
.dec ("d9") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_413

def globalBody631_415 : Prog (BitVec 64) :=
.dec ("d8") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_414

def globalBody631_416 : Prog (BitVec 64) :=
.dec ("d7") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_415

def globalBody631_417 : Prog (BitVec 64) :=
.dec ("d6") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_416

def globalBody631_418 : Prog (BitVec 64) :=
.dec ("d5") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_417

def globalBody631_419 : Prog (BitVec 64) :=
.dec ("d4") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_418

def globalBody631_420 : Prog (BitVec 64) :=
.dec ("d3") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_419

def globalBody631_421 : Prog (BitVec 64) :=
.dec ("d2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_420

def globalBody631_422 : Prog (BitVec 64) :=
.dec ("d1") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_421

def globalBody631_423 : Prog (BitVec 64) :=
.dec ("d0") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_422

def globalBody631_424 : Prog (BitVec 64) :=
.dec ("col") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_423

def globalBody631_425 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_424

def globalBody631_426 : Prog (BitVec 64) :=
.dec ("H") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_425

def globalBody631_427 : Prog (BitVec 64) :=
.dec ("L") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_426

def globalBody631_428 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody631_427

def globalBody631_429 : Prog (BitVec 64) :=
.dec ("b7") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b"))
  (Flapjack.Exp.const 32#64)) globalBody631_428

def globalBody631_430 : Prog (BitVec 64) :=
.dec ("b6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b"), Flapjack.Exp.const 4294967295#64]) globalBody631_429

def globalBody631_431 : Prog (BitVec 64) :=
.dec ("b5") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b"))
  (Flapjack.Exp.const 32#64)) globalBody631_430

def globalBody631_432 : Prog (BitVec 64) :=
.dec ("b4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b"), Flapjack.Exp.const 4294967295#64]) globalBody631_431

def globalBody631_433 : Prog (BitVec 64) :=
.dec ("b3") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b"))
  (Flapjack.Exp.const 32#64)) globalBody631_432

def globalBody631_434 : Prog (BitVec 64) :=
.dec ("b2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b"), Flapjack.Exp.const 4294967295#64]) globalBody631_433

def globalBody631_435 : Prog (BitVec 64) :=
.dec ("b1") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b"))
  (Flapjack.Exp.const 32#64)) globalBody631_434

def globalBody631_436 : Prog (BitVec 64) :=
.dec ("b0") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b"), Flapjack.Exp.const 4294967295#64]) globalBody631_435

def globalBody631_437 : Prog (BitVec 64) :=
.dec ("a7") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody631_436

def globalBody631_438 : Prog (BitVec 64) :=
.dec ("a6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody631_437

def globalBody631_439 : Prog (BitVec 64) :=
.dec ("a5") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody631_438

def globalBody631_440 : Prog (BitVec 64) :=
.dec ("a4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody631_439

def globalBody631_441 : Prog (BitVec 64) :=
.dec ("a3") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody631_440

def globalBody631_442 : Prog (BitVec 64) :=
.dec ("a2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody631_441

def globalBody631_443 : Prog (BitVec 64) :=
.dec ("a1") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody631_442

def globalBody631_444 : Prog (BitVec 64) :=
.dec ("a0") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody631_443

def globalData631 : Decl (BitVec 64) :=
.function { name := "p256_fp_mul", inline := false, exported := false, params := [("a", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("b", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := globalBody631_444, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput631 := Pancake.PanLang.declToHOL globalData631
end InitECandidate.Proofs.FrontendStages.Declarations
