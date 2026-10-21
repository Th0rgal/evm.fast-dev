import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data649
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate631
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody649_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody649_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "L"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "L",
      Flapjack.Exp.op Flapjack.BinOp.and
        [Flapjack.Exp.var Flapjack.VarKind.local "pr", Flapjack.Exp.const 4294967295#64]])

def globalBody649_2 : Prog (BitVec 64) :=
.seq globalBody649_0 globalBody649_1

def globalBody649_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "H"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "H",
      Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "pr") (Flapjack.Exp.const 32#64)])

def globalBody649_4 : Prog (BitVec 64) :=
.seq globalBody649_2 globalBody649_3

def globalBody649_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "L", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody649_6 : Prog (BitVec 64) :=
.seq globalBody649_4 globalBody649_5

def globalBody649_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "dg"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody649_8 : Prog (BitVec 64) :=
.seq globalBody649_6 globalBody649_7

def globalBody649_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "m0"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "dg", Flapjack.Exp.const 3834012553#64],
      Flapjack.Exp.const 4294967295#64])

def globalBody649_10 : Prog (BitVec 64) :=
.seq globalBody649_8 globalBody649_9

def globalBody649_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m0", Flapjack.Exp.const 3632069959#64])

def globalBody649_12 : Prog (BitVec 64) :=
.seq globalBody649_10 globalBody649_11

def globalBody649_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "col2"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "dg",
      Flapjack.Exp.op Flapjack.BinOp.and
        [Flapjack.Exp.var Flapjack.VarKind.local "pr", Flapjack.Exp.const 4294967295#64]])

def globalBody649_14 : Prog (BitVec 64) :=
.seq globalBody649_12 globalBody649_13

def globalBody649_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "col") (Flapjack.Exp.const 32#64),
      Flapjack.Exp.var Flapjack.VarKind.local "H",
      Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "col2") (Flapjack.Exp.const 32#64),
      Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "pr") (Flapjack.Exp.const 32#64)])

def globalBody649_16 : Prog (BitVec 64) :=
.seq globalBody649_14 globalBody649_15

def globalBody649_17 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "L" (Flapjack.Exp.const 0#64)

def globalBody649_18 : Prog (BitVec 64) :=
.seq globalBody649_16 globalBody649_17

def globalBody649_19 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "H" (Flapjack.Exp.const 0#64)

def globalBody649_20 : Prog (BitVec 64) :=
.seq globalBody649_18 globalBody649_19

def globalBody649_21 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody649_22 : Prog (BitVec 64) :=
.seq globalBody649_20 globalBody649_21

def globalBody649_23 : Prog (BitVec 64) :=
.seq globalBody649_22 globalBody649_1

def globalBody649_24 : Prog (BitVec 64) :=
.seq globalBody649_23 globalBody649_3

def globalBody649_25 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody649_26 : Prog (BitVec 64) :=
.seq globalBody649_24 globalBody649_25

def globalBody649_27 : Prog (BitVec 64) :=
.seq globalBody649_26 globalBody649_1

def globalBody649_28 : Prog (BitVec 64) :=
.seq globalBody649_27 globalBody649_3

def globalBody649_29 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m0", Flapjack.Exp.const 1008765974#64])

def globalBody649_30 : Prog (BitVec 64) :=
.seq globalBody649_28 globalBody649_29

def globalBody649_31 : Prog (BitVec 64) :=
.seq globalBody649_30 globalBody649_1

def globalBody649_32 : Prog (BitVec 64) :=
.seq globalBody649_31 globalBody649_3

def globalBody649_33 : Prog (BitVec 64) :=
.seq globalBody649_32 globalBody649_5

def globalBody649_34 : Prog (BitVec 64) :=
.seq globalBody649_33 globalBody649_7

def globalBody649_35 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "m1"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "dg", Flapjack.Exp.const 3834012553#64],
      Flapjack.Exp.const 4294967295#64])

def globalBody649_36 : Prog (BitVec 64) :=
.seq globalBody649_34 globalBody649_35

def globalBody649_37 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.const 3632069959#64])

def globalBody649_38 : Prog (BitVec 64) :=
.seq globalBody649_36 globalBody649_37

def globalBody649_39 : Prog (BitVec 64) :=
.seq globalBody649_38 globalBody649_13

def globalBody649_40 : Prog (BitVec 64) :=
.seq globalBody649_39 globalBody649_15

def globalBody649_41 : Prog (BitVec 64) :=
.seq globalBody649_40 globalBody649_17

def globalBody649_42 : Prog (BitVec 64) :=
.seq globalBody649_41 globalBody649_19

def globalBody649_43 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody649_44 : Prog (BitVec 64) :=
.seq globalBody649_42 globalBody649_43

def globalBody649_45 : Prog (BitVec 64) :=
.seq globalBody649_44 globalBody649_1

def globalBody649_46 : Prog (BitVec 64) :=
.seq globalBody649_45 globalBody649_3

def globalBody649_47 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody649_48 : Prog (BitVec 64) :=
.seq globalBody649_46 globalBody649_47

def globalBody649_49 : Prog (BitVec 64) :=
.seq globalBody649_48 globalBody649_1

def globalBody649_50 : Prog (BitVec 64) :=
.seq globalBody649_49 globalBody649_3

def globalBody649_51 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody649_52 : Prog (BitVec 64) :=
.seq globalBody649_50 globalBody649_51

def globalBody649_53 : Prog (BitVec 64) :=
.seq globalBody649_52 globalBody649_1

def globalBody649_54 : Prog (BitVec 64) :=
.seq globalBody649_53 globalBody649_3

def globalBody649_55 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m0", Flapjack.Exp.const 1752287885#64])

def globalBody649_56 : Prog (BitVec 64) :=
.seq globalBody649_54 globalBody649_55

def globalBody649_57 : Prog (BitVec 64) :=
.seq globalBody649_56 globalBody649_1

def globalBody649_58 : Prog (BitVec 64) :=
.seq globalBody649_57 globalBody649_3

def globalBody649_59 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.const 1008765974#64])

def globalBody649_60 : Prog (BitVec 64) :=
.seq globalBody649_58 globalBody649_59

def globalBody649_61 : Prog (BitVec 64) :=
.seq globalBody649_60 globalBody649_1

def globalBody649_62 : Prog (BitVec 64) :=
.seq globalBody649_61 globalBody649_3

def globalBody649_63 : Prog (BitVec 64) :=
.seq globalBody649_62 globalBody649_5

def globalBody649_64 : Prog (BitVec 64) :=
.seq globalBody649_63 globalBody649_7

def globalBody649_65 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "m2"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "dg", Flapjack.Exp.const 3834012553#64],
      Flapjack.Exp.const 4294967295#64])

def globalBody649_66 : Prog (BitVec 64) :=
.seq globalBody649_64 globalBody649_65

def globalBody649_67 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m2", Flapjack.Exp.const 3632069959#64])

def globalBody649_68 : Prog (BitVec 64) :=
.seq globalBody649_66 globalBody649_67

def globalBody649_69 : Prog (BitVec 64) :=
.seq globalBody649_68 globalBody649_13

def globalBody649_70 : Prog (BitVec 64) :=
.seq globalBody649_69 globalBody649_15

def globalBody649_71 : Prog (BitVec 64) :=
.seq globalBody649_70 globalBody649_17

def globalBody649_72 : Prog (BitVec 64) :=
.seq globalBody649_71 globalBody649_19

def globalBody649_73 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody649_74 : Prog (BitVec 64) :=
.seq globalBody649_72 globalBody649_73

def globalBody649_75 : Prog (BitVec 64) :=
.seq globalBody649_74 globalBody649_1

def globalBody649_76 : Prog (BitVec 64) :=
.seq globalBody649_75 globalBody649_3

def globalBody649_77 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody649_78 : Prog (BitVec 64) :=
.seq globalBody649_76 globalBody649_77

def globalBody649_79 : Prog (BitVec 64) :=
.seq globalBody649_78 globalBody649_1

def globalBody649_80 : Prog (BitVec 64) :=
.seq globalBody649_79 globalBody649_3

def globalBody649_81 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody649_82 : Prog (BitVec 64) :=
.seq globalBody649_80 globalBody649_81

def globalBody649_83 : Prog (BitVec 64) :=
.seq globalBody649_82 globalBody649_1

def globalBody649_84 : Prog (BitVec 64) :=
.seq globalBody649_83 globalBody649_3

def globalBody649_85 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody649_86 : Prog (BitVec 64) :=
.seq globalBody649_84 globalBody649_85

def globalBody649_87 : Prog (BitVec 64) :=
.seq globalBody649_86 globalBody649_1

def globalBody649_88 : Prog (BitVec 64) :=
.seq globalBody649_87 globalBody649_3

def globalBody649_89 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m0", Flapjack.Exp.const 2541841041#64])

def globalBody649_90 : Prog (BitVec 64) :=
.seq globalBody649_88 globalBody649_89

def globalBody649_91 : Prog (BitVec 64) :=
.seq globalBody649_90 globalBody649_1

def globalBody649_92 : Prog (BitVec 64) :=
.seq globalBody649_91 globalBody649_3

def globalBody649_93 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.const 1752287885#64])

def globalBody649_94 : Prog (BitVec 64) :=
.seq globalBody649_92 globalBody649_93

def globalBody649_95 : Prog (BitVec 64) :=
.seq globalBody649_94 globalBody649_1

def globalBody649_96 : Prog (BitVec 64) :=
.seq globalBody649_95 globalBody649_3

def globalBody649_97 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m2", Flapjack.Exp.const 1008765974#64])

def globalBody649_98 : Prog (BitVec 64) :=
.seq globalBody649_96 globalBody649_97

def globalBody649_99 : Prog (BitVec 64) :=
.seq globalBody649_98 globalBody649_1

def globalBody649_100 : Prog (BitVec 64) :=
.seq globalBody649_99 globalBody649_3

def globalBody649_101 : Prog (BitVec 64) :=
.seq globalBody649_100 globalBody649_5

def globalBody649_102 : Prog (BitVec 64) :=
.seq globalBody649_101 globalBody649_7

def globalBody649_103 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "m3"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "dg", Flapjack.Exp.const 3834012553#64],
      Flapjack.Exp.const 4294967295#64])

def globalBody649_104 : Prog (BitVec 64) :=
.seq globalBody649_102 globalBody649_103

def globalBody649_105 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m3", Flapjack.Exp.const 3632069959#64])

def globalBody649_106 : Prog (BitVec 64) :=
.seq globalBody649_104 globalBody649_105

def globalBody649_107 : Prog (BitVec 64) :=
.seq globalBody649_106 globalBody649_13

def globalBody649_108 : Prog (BitVec 64) :=
.seq globalBody649_107 globalBody649_15

def globalBody649_109 : Prog (BitVec 64) :=
.seq globalBody649_108 globalBody649_17

def globalBody649_110 : Prog (BitVec 64) :=
.seq globalBody649_109 globalBody649_19

def globalBody649_111 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody649_112 : Prog (BitVec 64) :=
.seq globalBody649_110 globalBody649_111

def globalBody649_113 : Prog (BitVec 64) :=
.seq globalBody649_112 globalBody649_1

def globalBody649_114 : Prog (BitVec 64) :=
.seq globalBody649_113 globalBody649_3

def globalBody649_115 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody649_116 : Prog (BitVec 64) :=
.seq globalBody649_114 globalBody649_115

def globalBody649_117 : Prog (BitVec 64) :=
.seq globalBody649_116 globalBody649_1

def globalBody649_118 : Prog (BitVec 64) :=
.seq globalBody649_117 globalBody649_3

def globalBody649_119 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody649_120 : Prog (BitVec 64) :=
.seq globalBody649_118 globalBody649_119

def globalBody649_121 : Prog (BitVec 64) :=
.seq globalBody649_120 globalBody649_1

def globalBody649_122 : Prog (BitVec 64) :=
.seq globalBody649_121 globalBody649_3

def globalBody649_123 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody649_124 : Prog (BitVec 64) :=
.seq globalBody649_122 globalBody649_123

def globalBody649_125 : Prog (BitVec 64) :=
.seq globalBody649_124 globalBody649_1

def globalBody649_126 : Prog (BitVec 64) :=
.seq globalBody649_125 globalBody649_3

def globalBody649_127 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody649_128 : Prog (BitVec 64) :=
.seq globalBody649_126 globalBody649_127

def globalBody649_129 : Prog (BitVec 64) :=
.seq globalBody649_128 globalBody649_1

def globalBody649_130 : Prog (BitVec 64) :=
.seq globalBody649_129 globalBody649_3

def globalBody649_131 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m0", Flapjack.Exp.const 2172737629#64])

def globalBody649_132 : Prog (BitVec 64) :=
.seq globalBody649_130 globalBody649_131

def globalBody649_133 : Prog (BitVec 64) :=
.seq globalBody649_132 globalBody649_1

def globalBody649_134 : Prog (BitVec 64) :=
.seq globalBody649_133 globalBody649_3

def globalBody649_135 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.const 2541841041#64])

def globalBody649_136 : Prog (BitVec 64) :=
.seq globalBody649_134 globalBody649_135

def globalBody649_137 : Prog (BitVec 64) :=
.seq globalBody649_136 globalBody649_1

def globalBody649_138 : Prog (BitVec 64) :=
.seq globalBody649_137 globalBody649_3

def globalBody649_139 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m2", Flapjack.Exp.const 1752287885#64])

def globalBody649_140 : Prog (BitVec 64) :=
.seq globalBody649_138 globalBody649_139

def globalBody649_141 : Prog (BitVec 64) :=
.seq globalBody649_140 globalBody649_1

def globalBody649_142 : Prog (BitVec 64) :=
.seq globalBody649_141 globalBody649_3

def globalBody649_143 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m3", Flapjack.Exp.const 1008765974#64])

def globalBody649_144 : Prog (BitVec 64) :=
.seq globalBody649_142 globalBody649_143

def globalBody649_145 : Prog (BitVec 64) :=
.seq globalBody649_144 globalBody649_1

def globalBody649_146 : Prog (BitVec 64) :=
.seq globalBody649_145 globalBody649_3

def globalBody649_147 : Prog (BitVec 64) :=
.seq globalBody649_146 globalBody649_5

def globalBody649_148 : Prog (BitVec 64) :=
.seq globalBody649_147 globalBody649_7

def globalBody649_149 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "m4"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "dg", Flapjack.Exp.const 3834012553#64],
      Flapjack.Exp.const 4294967295#64])

def globalBody649_150 : Prog (BitVec 64) :=
.seq globalBody649_148 globalBody649_149

def globalBody649_151 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m4", Flapjack.Exp.const 3632069959#64])

def globalBody649_152 : Prog (BitVec 64) :=
.seq globalBody649_150 globalBody649_151

def globalBody649_153 : Prog (BitVec 64) :=
.seq globalBody649_152 globalBody649_13

def globalBody649_154 : Prog (BitVec 64) :=
.seq globalBody649_153 globalBody649_15

def globalBody649_155 : Prog (BitVec 64) :=
.seq globalBody649_154 globalBody649_17

def globalBody649_156 : Prog (BitVec 64) :=
.seq globalBody649_155 globalBody649_19

def globalBody649_157 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody649_158 : Prog (BitVec 64) :=
.seq globalBody649_156 globalBody649_157

def globalBody649_159 : Prog (BitVec 64) :=
.seq globalBody649_158 globalBody649_1

def globalBody649_160 : Prog (BitVec 64) :=
.seq globalBody649_159 globalBody649_3

def globalBody649_161 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody649_162 : Prog (BitVec 64) :=
.seq globalBody649_160 globalBody649_161

def globalBody649_163 : Prog (BitVec 64) :=
.seq globalBody649_162 globalBody649_1

def globalBody649_164 : Prog (BitVec 64) :=
.seq globalBody649_163 globalBody649_3

def globalBody649_165 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody649_166 : Prog (BitVec 64) :=
.seq globalBody649_164 globalBody649_165

def globalBody649_167 : Prog (BitVec 64) :=
.seq globalBody649_166 globalBody649_1

def globalBody649_168 : Prog (BitVec 64) :=
.seq globalBody649_167 globalBody649_3

def globalBody649_169 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody649_170 : Prog (BitVec 64) :=
.seq globalBody649_168 globalBody649_169

def globalBody649_171 : Prog (BitVec 64) :=
.seq globalBody649_170 globalBody649_1

def globalBody649_172 : Prog (BitVec 64) :=
.seq globalBody649_171 globalBody649_3

def globalBody649_173 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody649_174 : Prog (BitVec 64) :=
.seq globalBody649_172 globalBody649_173

def globalBody649_175 : Prog (BitVec 64) :=
.seq globalBody649_174 globalBody649_1

def globalBody649_176 : Prog (BitVec 64) :=
.seq globalBody649_175 globalBody649_3

def globalBody649_177 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody649_178 : Prog (BitVec 64) :=
.seq globalBody649_176 globalBody649_177

def globalBody649_179 : Prog (BitVec 64) :=
.seq globalBody649_178 globalBody649_1

def globalBody649_180 : Prog (BitVec 64) :=
.seq globalBody649_179 globalBody649_3

def globalBody649_181 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m0", Flapjack.Exp.const 3092268470#64])

def globalBody649_182 : Prog (BitVec 64) :=
.seq globalBody649_180 globalBody649_181

def globalBody649_183 : Prog (BitVec 64) :=
.seq globalBody649_182 globalBody649_1

def globalBody649_184 : Prog (BitVec 64) :=
.seq globalBody649_183 globalBody649_3

def globalBody649_185 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.const 2172737629#64])

def globalBody649_186 : Prog (BitVec 64) :=
.seq globalBody649_184 globalBody649_185

def globalBody649_187 : Prog (BitVec 64) :=
.seq globalBody649_186 globalBody649_1

def globalBody649_188 : Prog (BitVec 64) :=
.seq globalBody649_187 globalBody649_3

def globalBody649_189 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m2", Flapjack.Exp.const 2541841041#64])

def globalBody649_190 : Prog (BitVec 64) :=
.seq globalBody649_188 globalBody649_189

def globalBody649_191 : Prog (BitVec 64) :=
.seq globalBody649_190 globalBody649_1

def globalBody649_192 : Prog (BitVec 64) :=
.seq globalBody649_191 globalBody649_3

def globalBody649_193 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m3", Flapjack.Exp.const 1752287885#64])

def globalBody649_194 : Prog (BitVec 64) :=
.seq globalBody649_192 globalBody649_193

def globalBody649_195 : Prog (BitVec 64) :=
.seq globalBody649_194 globalBody649_1

def globalBody649_196 : Prog (BitVec 64) :=
.seq globalBody649_195 globalBody649_3

def globalBody649_197 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m4", Flapjack.Exp.const 1008765974#64])

def globalBody649_198 : Prog (BitVec 64) :=
.seq globalBody649_196 globalBody649_197

def globalBody649_199 : Prog (BitVec 64) :=
.seq globalBody649_198 globalBody649_1

def globalBody649_200 : Prog (BitVec 64) :=
.seq globalBody649_199 globalBody649_3

def globalBody649_201 : Prog (BitVec 64) :=
.seq globalBody649_200 globalBody649_5

def globalBody649_202 : Prog (BitVec 64) :=
.seq globalBody649_201 globalBody649_7

def globalBody649_203 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "m5"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "dg", Flapjack.Exp.const 3834012553#64],
      Flapjack.Exp.const 4294967295#64])

def globalBody649_204 : Prog (BitVec 64) :=
.seq globalBody649_202 globalBody649_203

def globalBody649_205 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m5", Flapjack.Exp.const 3632069959#64])

def globalBody649_206 : Prog (BitVec 64) :=
.seq globalBody649_204 globalBody649_205

def globalBody649_207 : Prog (BitVec 64) :=
.seq globalBody649_206 globalBody649_13

def globalBody649_208 : Prog (BitVec 64) :=
.seq globalBody649_207 globalBody649_15

def globalBody649_209 : Prog (BitVec 64) :=
.seq globalBody649_208 globalBody649_17

def globalBody649_210 : Prog (BitVec 64) :=
.seq globalBody649_209 globalBody649_19

def globalBody649_211 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody649_212 : Prog (BitVec 64) :=
.seq globalBody649_210 globalBody649_211

def globalBody649_213 : Prog (BitVec 64) :=
.seq globalBody649_212 globalBody649_1

def globalBody649_214 : Prog (BitVec 64) :=
.seq globalBody649_213 globalBody649_3

def globalBody649_215 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody649_216 : Prog (BitVec 64) :=
.seq globalBody649_214 globalBody649_215

def globalBody649_217 : Prog (BitVec 64) :=
.seq globalBody649_216 globalBody649_1

def globalBody649_218 : Prog (BitVec 64) :=
.seq globalBody649_217 globalBody649_3

def globalBody649_219 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody649_220 : Prog (BitVec 64) :=
.seq globalBody649_218 globalBody649_219

def globalBody649_221 : Prog (BitVec 64) :=
.seq globalBody649_220 globalBody649_1

def globalBody649_222 : Prog (BitVec 64) :=
.seq globalBody649_221 globalBody649_3

def globalBody649_223 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody649_224 : Prog (BitVec 64) :=
.seq globalBody649_222 globalBody649_223

def globalBody649_225 : Prog (BitVec 64) :=
.seq globalBody649_224 globalBody649_1

def globalBody649_226 : Prog (BitVec 64) :=
.seq globalBody649_225 globalBody649_3

def globalBody649_227 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody649_228 : Prog (BitVec 64) :=
.seq globalBody649_226 globalBody649_227

def globalBody649_229 : Prog (BitVec 64) :=
.seq globalBody649_228 globalBody649_1

def globalBody649_230 : Prog (BitVec 64) :=
.seq globalBody649_229 globalBody649_3

def globalBody649_231 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody649_232 : Prog (BitVec 64) :=
.seq globalBody649_230 globalBody649_231

def globalBody649_233 : Prog (BitVec 64) :=
.seq globalBody649_232 globalBody649_1

def globalBody649_234 : Prog (BitVec 64) :=
.seq globalBody649_233 globalBody649_3

def globalBody649_235 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody649_236 : Prog (BitVec 64) :=
.seq globalBody649_234 globalBody649_235

def globalBody649_237 : Prog (BitVec 64) :=
.seq globalBody649_236 globalBody649_1

def globalBody649_238 : Prog (BitVec 64) :=
.seq globalBody649_237 globalBody649_3

def globalBody649_239 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m0", Flapjack.Exp.const 3778125865#64])

def globalBody649_240 : Prog (BitVec 64) :=
.seq globalBody649_238 globalBody649_239

def globalBody649_241 : Prog (BitVec 64) :=
.seq globalBody649_240 globalBody649_1

def globalBody649_242 : Prog (BitVec 64) :=
.seq globalBody649_241 globalBody649_3

def globalBody649_243 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.const 3092268470#64])

def globalBody649_244 : Prog (BitVec 64) :=
.seq globalBody649_242 globalBody649_243

def globalBody649_245 : Prog (BitVec 64) :=
.seq globalBody649_244 globalBody649_1

def globalBody649_246 : Prog (BitVec 64) :=
.seq globalBody649_245 globalBody649_3

def globalBody649_247 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m2", Flapjack.Exp.const 2172737629#64])

def globalBody649_248 : Prog (BitVec 64) :=
.seq globalBody649_246 globalBody649_247

def globalBody649_249 : Prog (BitVec 64) :=
.seq globalBody649_248 globalBody649_1

def globalBody649_250 : Prog (BitVec 64) :=
.seq globalBody649_249 globalBody649_3

def globalBody649_251 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m3", Flapjack.Exp.const 2541841041#64])

def globalBody649_252 : Prog (BitVec 64) :=
.seq globalBody649_250 globalBody649_251

def globalBody649_253 : Prog (BitVec 64) :=
.seq globalBody649_252 globalBody649_1

def globalBody649_254 : Prog (BitVec 64) :=
.seq globalBody649_253 globalBody649_3

def globalBody649_255 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m4", Flapjack.Exp.const 1752287885#64])

def globalBody649_256 : Prog (BitVec 64) :=
.seq globalBody649_254 globalBody649_255

def globalBody649_257 : Prog (BitVec 64) :=
.seq globalBody649_256 globalBody649_1

def globalBody649_258 : Prog (BitVec 64) :=
.seq globalBody649_257 globalBody649_3

def globalBody649_259 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m5", Flapjack.Exp.const 1008765974#64])

def globalBody649_260 : Prog (BitVec 64) :=
.seq globalBody649_258 globalBody649_259

def globalBody649_261 : Prog (BitVec 64) :=
.seq globalBody649_260 globalBody649_1

def globalBody649_262 : Prog (BitVec 64) :=
.seq globalBody649_261 globalBody649_3

def globalBody649_263 : Prog (BitVec 64) :=
.seq globalBody649_262 globalBody649_5

def globalBody649_264 : Prog (BitVec 64) :=
.seq globalBody649_263 globalBody649_7

def globalBody649_265 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "m6"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "dg", Flapjack.Exp.const 3834012553#64],
      Flapjack.Exp.const 4294967295#64])

def globalBody649_266 : Prog (BitVec 64) :=
.seq globalBody649_264 globalBody649_265

def globalBody649_267 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m6", Flapjack.Exp.const 3632069959#64])

def globalBody649_268 : Prog (BitVec 64) :=
.seq globalBody649_266 globalBody649_267

def globalBody649_269 : Prog (BitVec 64) :=
.seq globalBody649_268 globalBody649_13

def globalBody649_270 : Prog (BitVec 64) :=
.seq globalBody649_269 globalBody649_15

def globalBody649_271 : Prog (BitVec 64) :=
.seq globalBody649_270 globalBody649_17

def globalBody649_272 : Prog (BitVec 64) :=
.seq globalBody649_271 globalBody649_19

def globalBody649_273 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a0", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody649_274 : Prog (BitVec 64) :=
.seq globalBody649_272 globalBody649_273

def globalBody649_275 : Prog (BitVec 64) :=
.seq globalBody649_274 globalBody649_1

def globalBody649_276 : Prog (BitVec 64) :=
.seq globalBody649_275 globalBody649_3

def globalBody649_277 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody649_278 : Prog (BitVec 64) :=
.seq globalBody649_276 globalBody649_277

def globalBody649_279 : Prog (BitVec 64) :=
.seq globalBody649_278 globalBody649_1

def globalBody649_280 : Prog (BitVec 64) :=
.seq globalBody649_279 globalBody649_3

def globalBody649_281 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody649_282 : Prog (BitVec 64) :=
.seq globalBody649_280 globalBody649_281

def globalBody649_283 : Prog (BitVec 64) :=
.seq globalBody649_282 globalBody649_1

def globalBody649_284 : Prog (BitVec 64) :=
.seq globalBody649_283 globalBody649_3

def globalBody649_285 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody649_286 : Prog (BitVec 64) :=
.seq globalBody649_284 globalBody649_285

def globalBody649_287 : Prog (BitVec 64) :=
.seq globalBody649_286 globalBody649_1

def globalBody649_288 : Prog (BitVec 64) :=
.seq globalBody649_287 globalBody649_3

def globalBody649_289 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody649_290 : Prog (BitVec 64) :=
.seq globalBody649_288 globalBody649_289

def globalBody649_291 : Prog (BitVec 64) :=
.seq globalBody649_290 globalBody649_1

def globalBody649_292 : Prog (BitVec 64) :=
.seq globalBody649_291 globalBody649_3

def globalBody649_293 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody649_294 : Prog (BitVec 64) :=
.seq globalBody649_292 globalBody649_293

def globalBody649_295 : Prog (BitVec 64) :=
.seq globalBody649_294 globalBody649_1

def globalBody649_296 : Prog (BitVec 64) :=
.seq globalBody649_295 globalBody649_3

def globalBody649_297 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody649_298 : Prog (BitVec 64) :=
.seq globalBody649_296 globalBody649_297

def globalBody649_299 : Prog (BitVec 64) :=
.seq globalBody649_298 globalBody649_1

def globalBody649_300 : Prog (BitVec 64) :=
.seq globalBody649_299 globalBody649_3

def globalBody649_301 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b0"])

def globalBody649_302 : Prog (BitVec 64) :=
.seq globalBody649_300 globalBody649_301

def globalBody649_303 : Prog (BitVec 64) :=
.seq globalBody649_302 globalBody649_1

def globalBody649_304 : Prog (BitVec 64) :=
.seq globalBody649_303 globalBody649_3

def globalBody649_305 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m0", Flapjack.Exp.const 811880050#64])

def globalBody649_306 : Prog (BitVec 64) :=
.seq globalBody649_304 globalBody649_305

def globalBody649_307 : Prog (BitVec 64) :=
.seq globalBody649_306 globalBody649_1

def globalBody649_308 : Prog (BitVec 64) :=
.seq globalBody649_307 globalBody649_3

def globalBody649_309 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.const 3778125865#64])

def globalBody649_310 : Prog (BitVec 64) :=
.seq globalBody649_308 globalBody649_309

def globalBody649_311 : Prog (BitVec 64) :=
.seq globalBody649_310 globalBody649_1

def globalBody649_312 : Prog (BitVec 64) :=
.seq globalBody649_311 globalBody649_3

def globalBody649_313 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m2", Flapjack.Exp.const 3092268470#64])

def globalBody649_314 : Prog (BitVec 64) :=
.seq globalBody649_312 globalBody649_313

def globalBody649_315 : Prog (BitVec 64) :=
.seq globalBody649_314 globalBody649_1

def globalBody649_316 : Prog (BitVec 64) :=
.seq globalBody649_315 globalBody649_3

def globalBody649_317 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m3", Flapjack.Exp.const 2172737629#64])

def globalBody649_318 : Prog (BitVec 64) :=
.seq globalBody649_316 globalBody649_317

def globalBody649_319 : Prog (BitVec 64) :=
.seq globalBody649_318 globalBody649_1

def globalBody649_320 : Prog (BitVec 64) :=
.seq globalBody649_319 globalBody649_3

def globalBody649_321 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m4", Flapjack.Exp.const 2541841041#64])

def globalBody649_322 : Prog (BitVec 64) :=
.seq globalBody649_320 globalBody649_321

def globalBody649_323 : Prog (BitVec 64) :=
.seq globalBody649_322 globalBody649_1

def globalBody649_324 : Prog (BitVec 64) :=
.seq globalBody649_323 globalBody649_3

def globalBody649_325 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m5", Flapjack.Exp.const 1752287885#64])

def globalBody649_326 : Prog (BitVec 64) :=
.seq globalBody649_324 globalBody649_325

def globalBody649_327 : Prog (BitVec 64) :=
.seq globalBody649_326 globalBody649_1

def globalBody649_328 : Prog (BitVec 64) :=
.seq globalBody649_327 globalBody649_3

def globalBody649_329 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m6", Flapjack.Exp.const 1008765974#64])

def globalBody649_330 : Prog (BitVec 64) :=
.seq globalBody649_328 globalBody649_329

def globalBody649_331 : Prog (BitVec 64) :=
.seq globalBody649_330 globalBody649_1

def globalBody649_332 : Prog (BitVec 64) :=
.seq globalBody649_331 globalBody649_3

def globalBody649_333 : Prog (BitVec 64) :=
.seq globalBody649_332 globalBody649_5

def globalBody649_334 : Prog (BitVec 64) :=
.seq globalBody649_333 globalBody649_7

def globalBody649_335 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "m7"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "dg", Flapjack.Exp.const 3834012553#64],
      Flapjack.Exp.const 4294967295#64])

def globalBody649_336 : Prog (BitVec 64) :=
.seq globalBody649_334 globalBody649_335

def globalBody649_337 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m7", Flapjack.Exp.const 3632069959#64])

def globalBody649_338 : Prog (BitVec 64) :=
.seq globalBody649_336 globalBody649_337

def globalBody649_339 : Prog (BitVec 64) :=
.seq globalBody649_338 globalBody649_13

def globalBody649_340 : Prog (BitVec 64) :=
.seq globalBody649_339 globalBody649_15

def globalBody649_341 : Prog (BitVec 64) :=
.seq globalBody649_340 globalBody649_17

def globalBody649_342 : Prog (BitVec 64) :=
.seq globalBody649_341 globalBody649_19

def globalBody649_343 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a1", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody649_344 : Prog (BitVec 64) :=
.seq globalBody649_342 globalBody649_343

def globalBody649_345 : Prog (BitVec 64) :=
.seq globalBody649_344 globalBody649_1

def globalBody649_346 : Prog (BitVec 64) :=
.seq globalBody649_345 globalBody649_3

def globalBody649_347 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody649_348 : Prog (BitVec 64) :=
.seq globalBody649_346 globalBody649_347

def globalBody649_349 : Prog (BitVec 64) :=
.seq globalBody649_348 globalBody649_1

def globalBody649_350 : Prog (BitVec 64) :=
.seq globalBody649_349 globalBody649_3

def globalBody649_351 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody649_352 : Prog (BitVec 64) :=
.seq globalBody649_350 globalBody649_351

def globalBody649_353 : Prog (BitVec 64) :=
.seq globalBody649_352 globalBody649_1

def globalBody649_354 : Prog (BitVec 64) :=
.seq globalBody649_353 globalBody649_3

def globalBody649_355 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody649_356 : Prog (BitVec 64) :=
.seq globalBody649_354 globalBody649_355

def globalBody649_357 : Prog (BitVec 64) :=
.seq globalBody649_356 globalBody649_1

def globalBody649_358 : Prog (BitVec 64) :=
.seq globalBody649_357 globalBody649_3

def globalBody649_359 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody649_360 : Prog (BitVec 64) :=
.seq globalBody649_358 globalBody649_359

def globalBody649_361 : Prog (BitVec 64) :=
.seq globalBody649_360 globalBody649_1

def globalBody649_362 : Prog (BitVec 64) :=
.seq globalBody649_361 globalBody649_3

def globalBody649_363 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody649_364 : Prog (BitVec 64) :=
.seq globalBody649_362 globalBody649_363

def globalBody649_365 : Prog (BitVec 64) :=
.seq globalBody649_364 globalBody649_1

def globalBody649_366 : Prog (BitVec 64) :=
.seq globalBody649_365 globalBody649_3

def globalBody649_367 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b1"])

def globalBody649_368 : Prog (BitVec 64) :=
.seq globalBody649_366 globalBody649_367

def globalBody649_369 : Prog (BitVec 64) :=
.seq globalBody649_368 globalBody649_1

def globalBody649_370 : Prog (BitVec 64) :=
.seq globalBody649_369 globalBody649_3

def globalBody649_371 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.const 811880050#64])

def globalBody649_372 : Prog (BitVec 64) :=
.seq globalBody649_370 globalBody649_371

def globalBody649_373 : Prog (BitVec 64) :=
.seq globalBody649_372 globalBody649_1

def globalBody649_374 : Prog (BitVec 64) :=
.seq globalBody649_373 globalBody649_3

def globalBody649_375 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m2", Flapjack.Exp.const 3778125865#64])

def globalBody649_376 : Prog (BitVec 64) :=
.seq globalBody649_374 globalBody649_375

def globalBody649_377 : Prog (BitVec 64) :=
.seq globalBody649_376 globalBody649_1

def globalBody649_378 : Prog (BitVec 64) :=
.seq globalBody649_377 globalBody649_3

def globalBody649_379 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m3", Flapjack.Exp.const 3092268470#64])

def globalBody649_380 : Prog (BitVec 64) :=
.seq globalBody649_378 globalBody649_379

def globalBody649_381 : Prog (BitVec 64) :=
.seq globalBody649_380 globalBody649_1

def globalBody649_382 : Prog (BitVec 64) :=
.seq globalBody649_381 globalBody649_3

def globalBody649_383 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m4", Flapjack.Exp.const 2172737629#64])

def globalBody649_384 : Prog (BitVec 64) :=
.seq globalBody649_382 globalBody649_383

def globalBody649_385 : Prog (BitVec 64) :=
.seq globalBody649_384 globalBody649_1

def globalBody649_386 : Prog (BitVec 64) :=
.seq globalBody649_385 globalBody649_3

def globalBody649_387 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m5", Flapjack.Exp.const 2541841041#64])

def globalBody649_388 : Prog (BitVec 64) :=
.seq globalBody649_386 globalBody649_387

def globalBody649_389 : Prog (BitVec 64) :=
.seq globalBody649_388 globalBody649_1

def globalBody649_390 : Prog (BitVec 64) :=
.seq globalBody649_389 globalBody649_3

def globalBody649_391 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m6", Flapjack.Exp.const 1752287885#64])

def globalBody649_392 : Prog (BitVec 64) :=
.seq globalBody649_390 globalBody649_391

def globalBody649_393 : Prog (BitVec 64) :=
.seq globalBody649_392 globalBody649_1

def globalBody649_394 : Prog (BitVec 64) :=
.seq globalBody649_393 globalBody649_3

def globalBody649_395 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m7", Flapjack.Exp.const 1008765974#64])

def globalBody649_396 : Prog (BitVec 64) :=
.seq globalBody649_394 globalBody649_395

def globalBody649_397 : Prog (BitVec 64) :=
.seq globalBody649_396 globalBody649_1

def globalBody649_398 : Prog (BitVec 64) :=
.seq globalBody649_397 globalBody649_3

def globalBody649_399 : Prog (BitVec 64) :=
.seq globalBody649_398 globalBody649_5

def globalBody649_400 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "u0"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody649_401 : Prog (BitVec 64) :=
.seq globalBody649_399 globalBody649_400

def globalBody649_402 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "col") (Flapjack.Exp.const 32#64),
      Flapjack.Exp.var Flapjack.VarKind.local "H"])

def globalBody649_403 : Prog (BitVec 64) :=
.seq globalBody649_401 globalBody649_402

def globalBody649_404 : Prog (BitVec 64) :=
.seq globalBody649_403 globalBody649_17

def globalBody649_405 : Prog (BitVec 64) :=
.seq globalBody649_404 globalBody649_19

def globalBody649_406 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a2", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody649_407 : Prog (BitVec 64) :=
.seq globalBody649_405 globalBody649_406

def globalBody649_408 : Prog (BitVec 64) :=
.seq globalBody649_407 globalBody649_1

def globalBody649_409 : Prog (BitVec 64) :=
.seq globalBody649_408 globalBody649_3

def globalBody649_410 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody649_411 : Prog (BitVec 64) :=
.seq globalBody649_409 globalBody649_410

def globalBody649_412 : Prog (BitVec 64) :=
.seq globalBody649_411 globalBody649_1

def globalBody649_413 : Prog (BitVec 64) :=
.seq globalBody649_412 globalBody649_3

def globalBody649_414 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody649_415 : Prog (BitVec 64) :=
.seq globalBody649_413 globalBody649_414

def globalBody649_416 : Prog (BitVec 64) :=
.seq globalBody649_415 globalBody649_1

def globalBody649_417 : Prog (BitVec 64) :=
.seq globalBody649_416 globalBody649_3

def globalBody649_418 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody649_419 : Prog (BitVec 64) :=
.seq globalBody649_417 globalBody649_418

def globalBody649_420 : Prog (BitVec 64) :=
.seq globalBody649_419 globalBody649_1

def globalBody649_421 : Prog (BitVec 64) :=
.seq globalBody649_420 globalBody649_3

def globalBody649_422 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody649_423 : Prog (BitVec 64) :=
.seq globalBody649_421 globalBody649_422

def globalBody649_424 : Prog (BitVec 64) :=
.seq globalBody649_423 globalBody649_1

def globalBody649_425 : Prog (BitVec 64) :=
.seq globalBody649_424 globalBody649_3

def globalBody649_426 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b2"])

def globalBody649_427 : Prog (BitVec 64) :=
.seq globalBody649_425 globalBody649_426

def globalBody649_428 : Prog (BitVec 64) :=
.seq globalBody649_427 globalBody649_1

def globalBody649_429 : Prog (BitVec 64) :=
.seq globalBody649_428 globalBody649_3

def globalBody649_430 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m2", Flapjack.Exp.const 811880050#64])

def globalBody649_431 : Prog (BitVec 64) :=
.seq globalBody649_429 globalBody649_430

def globalBody649_432 : Prog (BitVec 64) :=
.seq globalBody649_431 globalBody649_1

def globalBody649_433 : Prog (BitVec 64) :=
.seq globalBody649_432 globalBody649_3

def globalBody649_434 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m3", Flapjack.Exp.const 3778125865#64])

def globalBody649_435 : Prog (BitVec 64) :=
.seq globalBody649_433 globalBody649_434

def globalBody649_436 : Prog (BitVec 64) :=
.seq globalBody649_435 globalBody649_1

def globalBody649_437 : Prog (BitVec 64) :=
.seq globalBody649_436 globalBody649_3

def globalBody649_438 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m4", Flapjack.Exp.const 3092268470#64])

def globalBody649_439 : Prog (BitVec 64) :=
.seq globalBody649_437 globalBody649_438

def globalBody649_440 : Prog (BitVec 64) :=
.seq globalBody649_439 globalBody649_1

def globalBody649_441 : Prog (BitVec 64) :=
.seq globalBody649_440 globalBody649_3

def globalBody649_442 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m5", Flapjack.Exp.const 2172737629#64])

def globalBody649_443 : Prog (BitVec 64) :=
.seq globalBody649_441 globalBody649_442

def globalBody649_444 : Prog (BitVec 64) :=
.seq globalBody649_443 globalBody649_1

def globalBody649_445 : Prog (BitVec 64) :=
.seq globalBody649_444 globalBody649_3

def globalBody649_446 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m6", Flapjack.Exp.const 2541841041#64])

def globalBody649_447 : Prog (BitVec 64) :=
.seq globalBody649_445 globalBody649_446

def globalBody649_448 : Prog (BitVec 64) :=
.seq globalBody649_447 globalBody649_1

def globalBody649_449 : Prog (BitVec 64) :=
.seq globalBody649_448 globalBody649_3

def globalBody649_450 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m7", Flapjack.Exp.const 1752287885#64])

def globalBody649_451 : Prog (BitVec 64) :=
.seq globalBody649_449 globalBody649_450

def globalBody649_452 : Prog (BitVec 64) :=
.seq globalBody649_451 globalBody649_1

def globalBody649_453 : Prog (BitVec 64) :=
.seq globalBody649_452 globalBody649_3

def globalBody649_454 : Prog (BitVec 64) :=
.seq globalBody649_453 globalBody649_5

def globalBody649_455 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "u1"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody649_456 : Prog (BitVec 64) :=
.seq globalBody649_454 globalBody649_455

def globalBody649_457 : Prog (BitVec 64) :=
.seq globalBody649_456 globalBody649_402

def globalBody649_458 : Prog (BitVec 64) :=
.seq globalBody649_457 globalBody649_17

def globalBody649_459 : Prog (BitVec 64) :=
.seq globalBody649_458 globalBody649_19

def globalBody649_460 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a3", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody649_461 : Prog (BitVec 64) :=
.seq globalBody649_459 globalBody649_460

def globalBody649_462 : Prog (BitVec 64) :=
.seq globalBody649_461 globalBody649_1

def globalBody649_463 : Prog (BitVec 64) :=
.seq globalBody649_462 globalBody649_3

def globalBody649_464 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody649_465 : Prog (BitVec 64) :=
.seq globalBody649_463 globalBody649_464

def globalBody649_466 : Prog (BitVec 64) :=
.seq globalBody649_465 globalBody649_1

def globalBody649_467 : Prog (BitVec 64) :=
.seq globalBody649_466 globalBody649_3

def globalBody649_468 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody649_469 : Prog (BitVec 64) :=
.seq globalBody649_467 globalBody649_468

def globalBody649_470 : Prog (BitVec 64) :=
.seq globalBody649_469 globalBody649_1

def globalBody649_471 : Prog (BitVec 64) :=
.seq globalBody649_470 globalBody649_3

def globalBody649_472 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody649_473 : Prog (BitVec 64) :=
.seq globalBody649_471 globalBody649_472

def globalBody649_474 : Prog (BitVec 64) :=
.seq globalBody649_473 globalBody649_1

def globalBody649_475 : Prog (BitVec 64) :=
.seq globalBody649_474 globalBody649_3

def globalBody649_476 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b3"])

def globalBody649_477 : Prog (BitVec 64) :=
.seq globalBody649_475 globalBody649_476

def globalBody649_478 : Prog (BitVec 64) :=
.seq globalBody649_477 globalBody649_1

def globalBody649_479 : Prog (BitVec 64) :=
.seq globalBody649_478 globalBody649_3

def globalBody649_480 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m3", Flapjack.Exp.const 811880050#64])

def globalBody649_481 : Prog (BitVec 64) :=
.seq globalBody649_479 globalBody649_480

def globalBody649_482 : Prog (BitVec 64) :=
.seq globalBody649_481 globalBody649_1

def globalBody649_483 : Prog (BitVec 64) :=
.seq globalBody649_482 globalBody649_3

def globalBody649_484 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m4", Flapjack.Exp.const 3778125865#64])

def globalBody649_485 : Prog (BitVec 64) :=
.seq globalBody649_483 globalBody649_484

def globalBody649_486 : Prog (BitVec 64) :=
.seq globalBody649_485 globalBody649_1

def globalBody649_487 : Prog (BitVec 64) :=
.seq globalBody649_486 globalBody649_3

def globalBody649_488 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m5", Flapjack.Exp.const 3092268470#64])

def globalBody649_489 : Prog (BitVec 64) :=
.seq globalBody649_487 globalBody649_488

def globalBody649_490 : Prog (BitVec 64) :=
.seq globalBody649_489 globalBody649_1

def globalBody649_491 : Prog (BitVec 64) :=
.seq globalBody649_490 globalBody649_3

def globalBody649_492 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m6", Flapjack.Exp.const 2172737629#64])

def globalBody649_493 : Prog (BitVec 64) :=
.seq globalBody649_491 globalBody649_492

def globalBody649_494 : Prog (BitVec 64) :=
.seq globalBody649_493 globalBody649_1

def globalBody649_495 : Prog (BitVec 64) :=
.seq globalBody649_494 globalBody649_3

def globalBody649_496 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m7", Flapjack.Exp.const 2541841041#64])

def globalBody649_497 : Prog (BitVec 64) :=
.seq globalBody649_495 globalBody649_496

def globalBody649_498 : Prog (BitVec 64) :=
.seq globalBody649_497 globalBody649_1

def globalBody649_499 : Prog (BitVec 64) :=
.seq globalBody649_498 globalBody649_3

def globalBody649_500 : Prog (BitVec 64) :=
.seq globalBody649_499 globalBody649_5

def globalBody649_501 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "u2"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody649_502 : Prog (BitVec 64) :=
.seq globalBody649_500 globalBody649_501

def globalBody649_503 : Prog (BitVec 64) :=
.seq globalBody649_502 globalBody649_402

def globalBody649_504 : Prog (BitVec 64) :=
.seq globalBody649_503 globalBody649_17

def globalBody649_505 : Prog (BitVec 64) :=
.seq globalBody649_504 globalBody649_19

def globalBody649_506 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a4", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody649_507 : Prog (BitVec 64) :=
.seq globalBody649_505 globalBody649_506

def globalBody649_508 : Prog (BitVec 64) :=
.seq globalBody649_507 globalBody649_1

def globalBody649_509 : Prog (BitVec 64) :=
.seq globalBody649_508 globalBody649_3

def globalBody649_510 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody649_511 : Prog (BitVec 64) :=
.seq globalBody649_509 globalBody649_510

def globalBody649_512 : Prog (BitVec 64) :=
.seq globalBody649_511 globalBody649_1

def globalBody649_513 : Prog (BitVec 64) :=
.seq globalBody649_512 globalBody649_3

def globalBody649_514 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody649_515 : Prog (BitVec 64) :=
.seq globalBody649_513 globalBody649_514

def globalBody649_516 : Prog (BitVec 64) :=
.seq globalBody649_515 globalBody649_1

def globalBody649_517 : Prog (BitVec 64) :=
.seq globalBody649_516 globalBody649_3

def globalBody649_518 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b4"])

def globalBody649_519 : Prog (BitVec 64) :=
.seq globalBody649_517 globalBody649_518

def globalBody649_520 : Prog (BitVec 64) :=
.seq globalBody649_519 globalBody649_1

def globalBody649_521 : Prog (BitVec 64) :=
.seq globalBody649_520 globalBody649_3

def globalBody649_522 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m4", Flapjack.Exp.const 811880050#64])

def globalBody649_523 : Prog (BitVec 64) :=
.seq globalBody649_521 globalBody649_522

def globalBody649_524 : Prog (BitVec 64) :=
.seq globalBody649_523 globalBody649_1

def globalBody649_525 : Prog (BitVec 64) :=
.seq globalBody649_524 globalBody649_3

def globalBody649_526 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m5", Flapjack.Exp.const 3778125865#64])

def globalBody649_527 : Prog (BitVec 64) :=
.seq globalBody649_525 globalBody649_526

def globalBody649_528 : Prog (BitVec 64) :=
.seq globalBody649_527 globalBody649_1

def globalBody649_529 : Prog (BitVec 64) :=
.seq globalBody649_528 globalBody649_3

def globalBody649_530 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m6", Flapjack.Exp.const 3092268470#64])

def globalBody649_531 : Prog (BitVec 64) :=
.seq globalBody649_529 globalBody649_530

def globalBody649_532 : Prog (BitVec 64) :=
.seq globalBody649_531 globalBody649_1

def globalBody649_533 : Prog (BitVec 64) :=
.seq globalBody649_532 globalBody649_3

def globalBody649_534 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m7", Flapjack.Exp.const 2172737629#64])

def globalBody649_535 : Prog (BitVec 64) :=
.seq globalBody649_533 globalBody649_534

def globalBody649_536 : Prog (BitVec 64) :=
.seq globalBody649_535 globalBody649_1

def globalBody649_537 : Prog (BitVec 64) :=
.seq globalBody649_536 globalBody649_3

def globalBody649_538 : Prog (BitVec 64) :=
.seq globalBody649_537 globalBody649_5

def globalBody649_539 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "u3"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody649_540 : Prog (BitVec 64) :=
.seq globalBody649_538 globalBody649_539

def globalBody649_541 : Prog (BitVec 64) :=
.seq globalBody649_540 globalBody649_402

def globalBody649_542 : Prog (BitVec 64) :=
.seq globalBody649_541 globalBody649_17

def globalBody649_543 : Prog (BitVec 64) :=
.seq globalBody649_542 globalBody649_19

def globalBody649_544 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a5", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody649_545 : Prog (BitVec 64) :=
.seq globalBody649_543 globalBody649_544

def globalBody649_546 : Prog (BitVec 64) :=
.seq globalBody649_545 globalBody649_1

def globalBody649_547 : Prog (BitVec 64) :=
.seq globalBody649_546 globalBody649_3

def globalBody649_548 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody649_549 : Prog (BitVec 64) :=
.seq globalBody649_547 globalBody649_548

def globalBody649_550 : Prog (BitVec 64) :=
.seq globalBody649_549 globalBody649_1

def globalBody649_551 : Prog (BitVec 64) :=
.seq globalBody649_550 globalBody649_3

def globalBody649_552 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b5"])

def globalBody649_553 : Prog (BitVec 64) :=
.seq globalBody649_551 globalBody649_552

def globalBody649_554 : Prog (BitVec 64) :=
.seq globalBody649_553 globalBody649_1

def globalBody649_555 : Prog (BitVec 64) :=
.seq globalBody649_554 globalBody649_3

def globalBody649_556 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m5", Flapjack.Exp.const 811880050#64])

def globalBody649_557 : Prog (BitVec 64) :=
.seq globalBody649_555 globalBody649_556

def globalBody649_558 : Prog (BitVec 64) :=
.seq globalBody649_557 globalBody649_1

def globalBody649_559 : Prog (BitVec 64) :=
.seq globalBody649_558 globalBody649_3

def globalBody649_560 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m6", Flapjack.Exp.const 3778125865#64])

def globalBody649_561 : Prog (BitVec 64) :=
.seq globalBody649_559 globalBody649_560

def globalBody649_562 : Prog (BitVec 64) :=
.seq globalBody649_561 globalBody649_1

def globalBody649_563 : Prog (BitVec 64) :=
.seq globalBody649_562 globalBody649_3

def globalBody649_564 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m7", Flapjack.Exp.const 3092268470#64])

def globalBody649_565 : Prog (BitVec 64) :=
.seq globalBody649_563 globalBody649_564

def globalBody649_566 : Prog (BitVec 64) :=
.seq globalBody649_565 globalBody649_1

def globalBody649_567 : Prog (BitVec 64) :=
.seq globalBody649_566 globalBody649_3

def globalBody649_568 : Prog (BitVec 64) :=
.seq globalBody649_567 globalBody649_5

def globalBody649_569 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "u4"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody649_570 : Prog (BitVec 64) :=
.seq globalBody649_568 globalBody649_569

def globalBody649_571 : Prog (BitVec 64) :=
.seq globalBody649_570 globalBody649_402

def globalBody649_572 : Prog (BitVec 64) :=
.seq globalBody649_571 globalBody649_17

def globalBody649_573 : Prog (BitVec 64) :=
.seq globalBody649_572 globalBody649_19

def globalBody649_574 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a6", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody649_575 : Prog (BitVec 64) :=
.seq globalBody649_573 globalBody649_574

def globalBody649_576 : Prog (BitVec 64) :=
.seq globalBody649_575 globalBody649_1

def globalBody649_577 : Prog (BitVec 64) :=
.seq globalBody649_576 globalBody649_3

def globalBody649_578 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b6"])

def globalBody649_579 : Prog (BitVec 64) :=
.seq globalBody649_577 globalBody649_578

def globalBody649_580 : Prog (BitVec 64) :=
.seq globalBody649_579 globalBody649_1

def globalBody649_581 : Prog (BitVec 64) :=
.seq globalBody649_580 globalBody649_3

def globalBody649_582 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m6", Flapjack.Exp.const 811880050#64])

def globalBody649_583 : Prog (BitVec 64) :=
.seq globalBody649_581 globalBody649_582

def globalBody649_584 : Prog (BitVec 64) :=
.seq globalBody649_583 globalBody649_1

def globalBody649_585 : Prog (BitVec 64) :=
.seq globalBody649_584 globalBody649_3

def globalBody649_586 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m7", Flapjack.Exp.const 3778125865#64])

def globalBody649_587 : Prog (BitVec 64) :=
.seq globalBody649_585 globalBody649_586

def globalBody649_588 : Prog (BitVec 64) :=
.seq globalBody649_587 globalBody649_1

def globalBody649_589 : Prog (BitVec 64) :=
.seq globalBody649_588 globalBody649_3

def globalBody649_590 : Prog (BitVec 64) :=
.seq globalBody649_589 globalBody649_5

def globalBody649_591 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "u5"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody649_592 : Prog (BitVec 64) :=
.seq globalBody649_590 globalBody649_591

def globalBody649_593 : Prog (BitVec 64) :=
.seq globalBody649_592 globalBody649_402

def globalBody649_594 : Prog (BitVec 64) :=
.seq globalBody649_593 globalBody649_17

def globalBody649_595 : Prog (BitVec 64) :=
.seq globalBody649_594 globalBody649_19

def globalBody649_596 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "a7", Flapjack.Exp.var Flapjack.VarKind.local "b7"])

def globalBody649_597 : Prog (BitVec 64) :=
.seq globalBody649_595 globalBody649_596

def globalBody649_598 : Prog (BitVec 64) :=
.seq globalBody649_597 globalBody649_1

def globalBody649_599 : Prog (BitVec 64) :=
.seq globalBody649_598 globalBody649_3

def globalBody649_600 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pr"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "m7", Flapjack.Exp.const 811880050#64])

def globalBody649_601 : Prog (BitVec 64) :=
.seq globalBody649_599 globalBody649_600

def globalBody649_602 : Prog (BitVec 64) :=
.seq globalBody649_601 globalBody649_1

def globalBody649_603 : Prog (BitVec 64) :=
.seq globalBody649_602 globalBody649_3

def globalBody649_604 : Prog (BitVec 64) :=
.seq globalBody649_603 globalBody649_5

def globalBody649_605 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "u6"
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "col", Flapjack.Exp.const 4294967295#64])

def globalBody649_606 : Prog (BitVec 64) :=
.seq globalBody649_604 globalBody649_605

def globalBody649_607 : Prog (BitVec 64) :=
.seq globalBody649_606 globalBody649_402

def globalBody649_608 : Prog (BitVec 64) :=
.seq globalBody649_607 globalBody649_17

def globalBody649_609 : Prog (BitVec 64) :=
.seq globalBody649_608 globalBody649_19

def globalBody649_610 : Prog (BitVec 64) :=
Flapjack.Prog.call none "u256_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
        Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]

def globalBody649_611 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody649_612 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "lt") (Flapjack.Exp.const 0#64)) globalBody649_610 globalBody649_611

def globalBody649_613 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "r")

def globalBody649_614 : Prog (BitVec 64) :=
.seq globalBody649_612 globalBody649_613

def globalBody649_615 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) globalBody649_614

def globalBody649_616 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.var Flapjack.VarKind.local "u0",
        Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "u1")
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.var Flapjack.VarKind.local "u2",
        Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "u3")
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.var Flapjack.VarKind.local "u4",
        Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "u5")
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.var Flapjack.VarKind.local "u6",
        Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "c") (Flapjack.Exp.const 32#64)]]) globalBody649_615

def globalBody649_617 : Prog (BitVec 64) :=
.seq globalBody649_609 globalBody649_616

def globalBody649_618 : Prog (BitVec 64) :=
.dec ("u6") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_617

def globalBody649_619 : Prog (BitVec 64) :=
.dec ("u5") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_618

def globalBody649_620 : Prog (BitVec 64) :=
.dec ("u4") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_619

def globalBody649_621 : Prog (BitVec 64) :=
.dec ("u3") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_620

def globalBody649_622 : Prog (BitVec 64) :=
.dec ("u2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_621

def globalBody649_623 : Prog (BitVec 64) :=
.dec ("u1") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_622

def globalBody649_624 : Prog (BitVec 64) :=
.dec ("u0") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_623

def globalBody649_625 : Prog (BitVec 64) :=
.dec ("m7") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_624

def globalBody649_626 : Prog (BitVec 64) :=
.dec ("m6") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_625

def globalBody649_627 : Prog (BitVec 64) :=
.dec ("m5") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_626

def globalBody649_628 : Prog (BitVec 64) :=
.dec ("m4") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_627

def globalBody649_629 : Prog (BitVec 64) :=
.dec ("m3") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_628

def globalBody649_630 : Prog (BitVec 64) :=
.dec ("m2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_629

def globalBody649_631 : Prog (BitVec 64) :=
.dec ("m1") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_630

def globalBody649_632 : Prog (BitVec 64) :=
.dec ("m0") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_631

def globalBody649_633 : Prog (BitVec 64) :=
.dec ("dg") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_632

def globalBody649_634 : Prog (BitVec 64) :=
.dec ("col2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_633

def globalBody649_635 : Prog (BitVec 64) :=
.dec ("col") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_634

def globalBody649_636 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_635

def globalBody649_637 : Prog (BitVec 64) :=
.dec ("H") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_636

def globalBody649_638 : Prog (BitVec 64) :=
.dec ("L") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_637

def globalBody649_639 : Prog (BitVec 64) :=
.dec ("pr") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody649_638

def globalBody649_640 : Prog (BitVec 64) :=
.dec ("b7") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b"))
  (Flapjack.Exp.const 32#64)) globalBody649_639

def globalBody649_641 : Prog (BitVec 64) :=
.dec ("b6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b"), Flapjack.Exp.const 4294967295#64]) globalBody649_640

def globalBody649_642 : Prog (BitVec 64) :=
.dec ("b5") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b"))
  (Flapjack.Exp.const 32#64)) globalBody649_641

def globalBody649_643 : Prog (BitVec 64) :=
.dec ("b4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b"), Flapjack.Exp.const 4294967295#64]) globalBody649_642

def globalBody649_644 : Prog (BitVec 64) :=
.dec ("b3") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b"))
  (Flapjack.Exp.const 32#64)) globalBody649_643

def globalBody649_645 : Prog (BitVec 64) :=
.dec ("b2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b"), Flapjack.Exp.const 4294967295#64]) globalBody649_644

def globalBody649_646 : Prog (BitVec 64) :=
.dec ("b1") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b"))
  (Flapjack.Exp.const 32#64)) globalBody649_645

def globalBody649_647 : Prog (BitVec 64) :=
.dec ("b0") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b"), Flapjack.Exp.const 4294967295#64]) globalBody649_646

def globalBody649_648 : Prog (BitVec 64) :=
.dec ("a7") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody649_647

def globalBody649_649 : Prog (BitVec 64) :=
.dec ("a6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody649_648

def globalBody649_650 : Prog (BitVec 64) :=
.dec ("a5") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody649_649

def globalBody649_651 : Prog (BitVec 64) :=
.dec ("a4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody649_650

def globalBody649_652 : Prog (BitVec 64) :=
.dec ("a3") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody649_651

def globalBody649_653 : Prog (BitVec 64) :=
.dec ("a2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody649_652

def globalBody649_654 : Prog (BitVec 64) :=
.dec ("a1") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.const 32#64)) globalBody649_653

def globalBody649_655 : Prog (BitVec 64) :=
.dec ("a0") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"), Flapjack.Exp.const 4294967295#64]) globalBody649_654

def globalData649 : Decl (BitVec 64) :=
.function { name := "fq_mul", inline := false, exported := false, params := [("a", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("b", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := globalBody649_655, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput649 := Pancake.PanLang.declToHOL globalData649
end InitECandidate.Proofs.FrontendStages.Declarations
