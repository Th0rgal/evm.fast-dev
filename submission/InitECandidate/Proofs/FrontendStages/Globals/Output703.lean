import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data703
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate686
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody703_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_1 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "s" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "pr"),
    Flapjack.Exp.const 0#64]

def globalBody703_2 : Prog (BitVec 64) :=
.seq globalBody703_0 globalBody703_1

def globalBody703_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t0" (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s"))

def globalBody703_4 : Prog (BitVec 64) :=
.seq globalBody703_2 globalBody703_3

def globalBody703_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "pr"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s")])

def globalBody703_6 : Prog (BitVec 64) :=
.seq globalBody703_4 globalBody703_5

def globalBody703_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_8 : Prog (BitVec 64) :=
.seq globalBody703_6 globalBody703_7

def globalBody703_9 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "s" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "pr"),
    Flapjack.Exp.const 0#64]

def globalBody703_10 : Prog (BitVec 64) :=
.seq globalBody703_8 globalBody703_9

def globalBody703_11 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "s2" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s"), Flapjack.Exp.var Flapjack.VarKind.local "c",
    Flapjack.Exp.const 0#64]

def globalBody703_12 : Prog (BitVec 64) :=
.seq globalBody703_10 globalBody703_11

def globalBody703_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t1" (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s2"))

def globalBody703_14 : Prog (BitVec 64) :=
.seq globalBody703_12 globalBody703_13

def globalBody703_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "pr"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2")])

def globalBody703_16 : Prog (BitVec 64) :=
.seq globalBody703_14 globalBody703_15

def globalBody703_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_18 : Prog (BitVec 64) :=
.seq globalBody703_16 globalBody703_17

def globalBody703_19 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "s" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "pr"),
    Flapjack.Exp.const 0#64]

def globalBody703_20 : Prog (BitVec 64) :=
.seq globalBody703_18 globalBody703_19

def globalBody703_21 : Prog (BitVec 64) :=
.seq globalBody703_20 globalBody703_11

def globalBody703_22 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t2" (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s2"))

def globalBody703_23 : Prog (BitVec 64) :=
.seq globalBody703_21 globalBody703_22

def globalBody703_24 : Prog (BitVec 64) :=
.seq globalBody703_23 globalBody703_15

def globalBody703_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_26 : Prog (BitVec 64) :=
.seq globalBody703_24 globalBody703_25

def globalBody703_27 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "s" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.var Flapjack.VarKind.local "t3", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "pr"),
    Flapjack.Exp.const 0#64]

def globalBody703_28 : Prog (BitVec 64) :=
.seq globalBody703_26 globalBody703_27

def globalBody703_29 : Prog (BitVec 64) :=
.seq globalBody703_28 globalBody703_11

def globalBody703_30 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t3" (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s2"))

def globalBody703_31 : Prog (BitVec 64) :=
.seq globalBody703_29 globalBody703_30

def globalBody703_32 : Prog (BitVec 64) :=
.seq globalBody703_31 globalBody703_15

def globalBody703_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_34 : Prog (BitVec 64) :=
.seq globalBody703_32 globalBody703_33

def globalBody703_35 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "s" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.var Flapjack.VarKind.local "t4", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "pr"),
    Flapjack.Exp.const 0#64]

def globalBody703_36 : Prog (BitVec 64) :=
.seq globalBody703_34 globalBody703_35

def globalBody703_37 : Prog (BitVec 64) :=
.seq globalBody703_36 globalBody703_11

def globalBody703_38 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t4" (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s2"))

def globalBody703_39 : Prog (BitVec 64) :=
.seq globalBody703_37 globalBody703_38

def globalBody703_40 : Prog (BitVec 64) :=
.seq globalBody703_39 globalBody703_15

def globalBody703_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_42 : Prog (BitVec 64) :=
.seq globalBody703_40 globalBody703_41

def globalBody703_43 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "s" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.var Flapjack.VarKind.local "t5", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "pr"),
    Flapjack.Exp.const 0#64]

def globalBody703_44 : Prog (BitVec 64) :=
.seq globalBody703_42 globalBody703_43

def globalBody703_45 : Prog (BitVec 64) :=
.seq globalBody703_44 globalBody703_11

def globalBody703_46 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t5" (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s2"))

def globalBody703_47 : Prog (BitVec 64) :=
.seq globalBody703_45 globalBody703_46

def globalBody703_48 : Prog (BitVec 64) :=
.seq globalBody703_47 globalBody703_15

def globalBody703_49 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t6"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t6", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody703_50 : Prog (BitVec 64) :=
.seq globalBody703_48 globalBody703_49

def globalBody703_51 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "m"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.const 9940570264628428797#64])

def globalBody703_52 : Prog (BitVec 64) :=
.seq globalBody703_50 globalBody703_51

def globalBody703_53 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 13402431016077863595#64]

def globalBody703_54 : Prog (BitVec 64) :=
.seq globalBody703_52 globalBody703_53

def globalBody703_55 : Prog (BitVec 64) :=
.seq globalBody703_54 globalBody703_1

def globalBody703_56 : Prog (BitVec 64) :=
.seq globalBody703_55 globalBody703_5

def globalBody703_57 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 2210141511517208575#64]

def globalBody703_58 : Prog (BitVec 64) :=
.seq globalBody703_56 globalBody703_57

def globalBody703_59 : Prog (BitVec 64) :=
.seq globalBody703_58 globalBody703_9

def globalBody703_60 : Prog (BitVec 64) :=
.seq globalBody703_59 globalBody703_11

def globalBody703_61 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t0" (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s2"))

def globalBody703_62 : Prog (BitVec 64) :=
.seq globalBody703_60 globalBody703_61

def globalBody703_63 : Prog (BitVec 64) :=
.seq globalBody703_62 globalBody703_15

def globalBody703_64 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 7435674573564081700#64]

def globalBody703_65 : Prog (BitVec 64) :=
.seq globalBody703_63 globalBody703_64

def globalBody703_66 : Prog (BitVec 64) :=
.seq globalBody703_65 globalBody703_19

def globalBody703_67 : Prog (BitVec 64) :=
.seq globalBody703_66 globalBody703_11

def globalBody703_68 : Prog (BitVec 64) :=
.seq globalBody703_67 globalBody703_13

def globalBody703_69 : Prog (BitVec 64) :=
.seq globalBody703_68 globalBody703_15

def globalBody703_70 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 7239337960414712511#64]

def globalBody703_71 : Prog (BitVec 64) :=
.seq globalBody703_69 globalBody703_70

def globalBody703_72 : Prog (BitVec 64) :=
.seq globalBody703_71 globalBody703_27

def globalBody703_73 : Prog (BitVec 64) :=
.seq globalBody703_72 globalBody703_11

def globalBody703_74 : Prog (BitVec 64) :=
.seq globalBody703_73 globalBody703_22

def globalBody703_75 : Prog (BitVec 64) :=
.seq globalBody703_74 globalBody703_15

def globalBody703_76 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 5412103778470702295#64]

def globalBody703_77 : Prog (BitVec 64) :=
.seq globalBody703_75 globalBody703_76

def globalBody703_78 : Prog (BitVec 64) :=
.seq globalBody703_77 globalBody703_35

def globalBody703_79 : Prog (BitVec 64) :=
.seq globalBody703_78 globalBody703_11

def globalBody703_80 : Prog (BitVec 64) :=
.seq globalBody703_79 globalBody703_30

def globalBody703_81 : Prog (BitVec 64) :=
.seq globalBody703_80 globalBody703_15

def globalBody703_82 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 1873798617647539866#64]

def globalBody703_83 : Prog (BitVec 64) :=
.seq globalBody703_81 globalBody703_82

def globalBody703_84 : Prog (BitVec 64) :=
.seq globalBody703_83 globalBody703_43

def globalBody703_85 : Prog (BitVec 64) :=
.seq globalBody703_84 globalBody703_11

def globalBody703_86 : Prog (BitVec 64) :=
.seq globalBody703_85 globalBody703_38

def globalBody703_87 : Prog (BitVec 64) :=
.seq globalBody703_86 globalBody703_15

def globalBody703_88 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t5"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t6", Flapjack.Exp.var Flapjack.VarKind.local "c"])

def globalBody703_89 : Prog (BitVec 64) :=
.seq globalBody703_87 globalBody703_88

def globalBody703_90 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t6" (Flapjack.Exp.const 0#64)

def globalBody703_91 : Prog (BitVec 64) :=
.seq globalBody703_89 globalBody703_90

def globalBody703_92 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_93 : Prog (BitVec 64) :=
.seq globalBody703_91 globalBody703_92

def globalBody703_94 : Prog (BitVec 64) :=
.seq globalBody703_93 globalBody703_1

def globalBody703_95 : Prog (BitVec 64) :=
.seq globalBody703_94 globalBody703_3

def globalBody703_96 : Prog (BitVec 64) :=
.seq globalBody703_95 globalBody703_5

def globalBody703_97 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_98 : Prog (BitVec 64) :=
.seq globalBody703_96 globalBody703_97

def globalBody703_99 : Prog (BitVec 64) :=
.seq globalBody703_98 globalBody703_9

def globalBody703_100 : Prog (BitVec 64) :=
.seq globalBody703_99 globalBody703_11

def globalBody703_101 : Prog (BitVec 64) :=
.seq globalBody703_100 globalBody703_13

def globalBody703_102 : Prog (BitVec 64) :=
.seq globalBody703_101 globalBody703_15

def globalBody703_103 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_104 : Prog (BitVec 64) :=
.seq globalBody703_102 globalBody703_103

def globalBody703_105 : Prog (BitVec 64) :=
.seq globalBody703_104 globalBody703_19

def globalBody703_106 : Prog (BitVec 64) :=
.seq globalBody703_105 globalBody703_11

def globalBody703_107 : Prog (BitVec 64) :=
.seq globalBody703_106 globalBody703_22

def globalBody703_108 : Prog (BitVec 64) :=
.seq globalBody703_107 globalBody703_15

def globalBody703_109 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_110 : Prog (BitVec 64) :=
.seq globalBody703_108 globalBody703_109

def globalBody703_111 : Prog (BitVec 64) :=
.seq globalBody703_110 globalBody703_27

def globalBody703_112 : Prog (BitVec 64) :=
.seq globalBody703_111 globalBody703_11

def globalBody703_113 : Prog (BitVec 64) :=
.seq globalBody703_112 globalBody703_30

def globalBody703_114 : Prog (BitVec 64) :=
.seq globalBody703_113 globalBody703_15

def globalBody703_115 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_116 : Prog (BitVec 64) :=
.seq globalBody703_114 globalBody703_115

def globalBody703_117 : Prog (BitVec 64) :=
.seq globalBody703_116 globalBody703_35

def globalBody703_118 : Prog (BitVec 64) :=
.seq globalBody703_117 globalBody703_11

def globalBody703_119 : Prog (BitVec 64) :=
.seq globalBody703_118 globalBody703_38

def globalBody703_120 : Prog (BitVec 64) :=
.seq globalBody703_119 globalBody703_15

def globalBody703_121 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_122 : Prog (BitVec 64) :=
.seq globalBody703_120 globalBody703_121

def globalBody703_123 : Prog (BitVec 64) :=
.seq globalBody703_122 globalBody703_43

def globalBody703_124 : Prog (BitVec 64) :=
.seq globalBody703_123 globalBody703_11

def globalBody703_125 : Prog (BitVec 64) :=
.seq globalBody703_124 globalBody703_46

def globalBody703_126 : Prog (BitVec 64) :=
.seq globalBody703_125 globalBody703_15

def globalBody703_127 : Prog (BitVec 64) :=
.seq globalBody703_126 globalBody703_49

def globalBody703_128 : Prog (BitVec 64) :=
.seq globalBody703_127 globalBody703_51

def globalBody703_129 : Prog (BitVec 64) :=
.seq globalBody703_128 globalBody703_53

def globalBody703_130 : Prog (BitVec 64) :=
.seq globalBody703_129 globalBody703_1

def globalBody703_131 : Prog (BitVec 64) :=
.seq globalBody703_130 globalBody703_5

def globalBody703_132 : Prog (BitVec 64) :=
.seq globalBody703_131 globalBody703_57

def globalBody703_133 : Prog (BitVec 64) :=
.seq globalBody703_132 globalBody703_9

def globalBody703_134 : Prog (BitVec 64) :=
.seq globalBody703_133 globalBody703_11

def globalBody703_135 : Prog (BitVec 64) :=
.seq globalBody703_134 globalBody703_61

def globalBody703_136 : Prog (BitVec 64) :=
.seq globalBody703_135 globalBody703_15

def globalBody703_137 : Prog (BitVec 64) :=
.seq globalBody703_136 globalBody703_64

def globalBody703_138 : Prog (BitVec 64) :=
.seq globalBody703_137 globalBody703_19

def globalBody703_139 : Prog (BitVec 64) :=
.seq globalBody703_138 globalBody703_11

def globalBody703_140 : Prog (BitVec 64) :=
.seq globalBody703_139 globalBody703_13

def globalBody703_141 : Prog (BitVec 64) :=
.seq globalBody703_140 globalBody703_15

def globalBody703_142 : Prog (BitVec 64) :=
.seq globalBody703_141 globalBody703_70

def globalBody703_143 : Prog (BitVec 64) :=
.seq globalBody703_142 globalBody703_27

def globalBody703_144 : Prog (BitVec 64) :=
.seq globalBody703_143 globalBody703_11

def globalBody703_145 : Prog (BitVec 64) :=
.seq globalBody703_144 globalBody703_22

def globalBody703_146 : Prog (BitVec 64) :=
.seq globalBody703_145 globalBody703_15

def globalBody703_147 : Prog (BitVec 64) :=
.seq globalBody703_146 globalBody703_76

def globalBody703_148 : Prog (BitVec 64) :=
.seq globalBody703_147 globalBody703_35

def globalBody703_149 : Prog (BitVec 64) :=
.seq globalBody703_148 globalBody703_11

def globalBody703_150 : Prog (BitVec 64) :=
.seq globalBody703_149 globalBody703_30

def globalBody703_151 : Prog (BitVec 64) :=
.seq globalBody703_150 globalBody703_15

def globalBody703_152 : Prog (BitVec 64) :=
.seq globalBody703_151 globalBody703_82

def globalBody703_153 : Prog (BitVec 64) :=
.seq globalBody703_152 globalBody703_43

def globalBody703_154 : Prog (BitVec 64) :=
.seq globalBody703_153 globalBody703_11

def globalBody703_155 : Prog (BitVec 64) :=
.seq globalBody703_154 globalBody703_38

def globalBody703_156 : Prog (BitVec 64) :=
.seq globalBody703_155 globalBody703_15

def globalBody703_157 : Prog (BitVec 64) :=
.seq globalBody703_156 globalBody703_88

def globalBody703_158 : Prog (BitVec 64) :=
.seq globalBody703_157 globalBody703_90

def globalBody703_159 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_160 : Prog (BitVec 64) :=
.seq globalBody703_158 globalBody703_159

def globalBody703_161 : Prog (BitVec 64) :=
.seq globalBody703_160 globalBody703_1

def globalBody703_162 : Prog (BitVec 64) :=
.seq globalBody703_161 globalBody703_3

def globalBody703_163 : Prog (BitVec 64) :=
.seq globalBody703_162 globalBody703_5

def globalBody703_164 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_165 : Prog (BitVec 64) :=
.seq globalBody703_163 globalBody703_164

def globalBody703_166 : Prog (BitVec 64) :=
.seq globalBody703_165 globalBody703_9

def globalBody703_167 : Prog (BitVec 64) :=
.seq globalBody703_166 globalBody703_11

def globalBody703_168 : Prog (BitVec 64) :=
.seq globalBody703_167 globalBody703_13

def globalBody703_169 : Prog (BitVec 64) :=
.seq globalBody703_168 globalBody703_15

def globalBody703_170 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_171 : Prog (BitVec 64) :=
.seq globalBody703_169 globalBody703_170

def globalBody703_172 : Prog (BitVec 64) :=
.seq globalBody703_171 globalBody703_19

def globalBody703_173 : Prog (BitVec 64) :=
.seq globalBody703_172 globalBody703_11

def globalBody703_174 : Prog (BitVec 64) :=
.seq globalBody703_173 globalBody703_22

def globalBody703_175 : Prog (BitVec 64) :=
.seq globalBody703_174 globalBody703_15

def globalBody703_176 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_177 : Prog (BitVec 64) :=
.seq globalBody703_175 globalBody703_176

def globalBody703_178 : Prog (BitVec 64) :=
.seq globalBody703_177 globalBody703_27

def globalBody703_179 : Prog (BitVec 64) :=
.seq globalBody703_178 globalBody703_11

def globalBody703_180 : Prog (BitVec 64) :=
.seq globalBody703_179 globalBody703_30

def globalBody703_181 : Prog (BitVec 64) :=
.seq globalBody703_180 globalBody703_15

def globalBody703_182 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_183 : Prog (BitVec 64) :=
.seq globalBody703_181 globalBody703_182

def globalBody703_184 : Prog (BitVec 64) :=
.seq globalBody703_183 globalBody703_35

def globalBody703_185 : Prog (BitVec 64) :=
.seq globalBody703_184 globalBody703_11

def globalBody703_186 : Prog (BitVec 64) :=
.seq globalBody703_185 globalBody703_38

def globalBody703_187 : Prog (BitVec 64) :=
.seq globalBody703_186 globalBody703_15

def globalBody703_188 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_189 : Prog (BitVec 64) :=
.seq globalBody703_187 globalBody703_188

def globalBody703_190 : Prog (BitVec 64) :=
.seq globalBody703_189 globalBody703_43

def globalBody703_191 : Prog (BitVec 64) :=
.seq globalBody703_190 globalBody703_11

def globalBody703_192 : Prog (BitVec 64) :=
.seq globalBody703_191 globalBody703_46

def globalBody703_193 : Prog (BitVec 64) :=
.seq globalBody703_192 globalBody703_15

def globalBody703_194 : Prog (BitVec 64) :=
.seq globalBody703_193 globalBody703_49

def globalBody703_195 : Prog (BitVec 64) :=
.seq globalBody703_194 globalBody703_51

def globalBody703_196 : Prog (BitVec 64) :=
.seq globalBody703_195 globalBody703_53

def globalBody703_197 : Prog (BitVec 64) :=
.seq globalBody703_196 globalBody703_1

def globalBody703_198 : Prog (BitVec 64) :=
.seq globalBody703_197 globalBody703_5

def globalBody703_199 : Prog (BitVec 64) :=
.seq globalBody703_198 globalBody703_57

def globalBody703_200 : Prog (BitVec 64) :=
.seq globalBody703_199 globalBody703_9

def globalBody703_201 : Prog (BitVec 64) :=
.seq globalBody703_200 globalBody703_11

def globalBody703_202 : Prog (BitVec 64) :=
.seq globalBody703_201 globalBody703_61

def globalBody703_203 : Prog (BitVec 64) :=
.seq globalBody703_202 globalBody703_15

def globalBody703_204 : Prog (BitVec 64) :=
.seq globalBody703_203 globalBody703_64

def globalBody703_205 : Prog (BitVec 64) :=
.seq globalBody703_204 globalBody703_19

def globalBody703_206 : Prog (BitVec 64) :=
.seq globalBody703_205 globalBody703_11

def globalBody703_207 : Prog (BitVec 64) :=
.seq globalBody703_206 globalBody703_13

def globalBody703_208 : Prog (BitVec 64) :=
.seq globalBody703_207 globalBody703_15

def globalBody703_209 : Prog (BitVec 64) :=
.seq globalBody703_208 globalBody703_70

def globalBody703_210 : Prog (BitVec 64) :=
.seq globalBody703_209 globalBody703_27

def globalBody703_211 : Prog (BitVec 64) :=
.seq globalBody703_210 globalBody703_11

def globalBody703_212 : Prog (BitVec 64) :=
.seq globalBody703_211 globalBody703_22

def globalBody703_213 : Prog (BitVec 64) :=
.seq globalBody703_212 globalBody703_15

def globalBody703_214 : Prog (BitVec 64) :=
.seq globalBody703_213 globalBody703_76

def globalBody703_215 : Prog (BitVec 64) :=
.seq globalBody703_214 globalBody703_35

def globalBody703_216 : Prog (BitVec 64) :=
.seq globalBody703_215 globalBody703_11

def globalBody703_217 : Prog (BitVec 64) :=
.seq globalBody703_216 globalBody703_30

def globalBody703_218 : Prog (BitVec 64) :=
.seq globalBody703_217 globalBody703_15

def globalBody703_219 : Prog (BitVec 64) :=
.seq globalBody703_218 globalBody703_82

def globalBody703_220 : Prog (BitVec 64) :=
.seq globalBody703_219 globalBody703_43

def globalBody703_221 : Prog (BitVec 64) :=
.seq globalBody703_220 globalBody703_11

def globalBody703_222 : Prog (BitVec 64) :=
.seq globalBody703_221 globalBody703_38

def globalBody703_223 : Prog (BitVec 64) :=
.seq globalBody703_222 globalBody703_15

def globalBody703_224 : Prog (BitVec 64) :=
.seq globalBody703_223 globalBody703_88

def globalBody703_225 : Prog (BitVec 64) :=
.seq globalBody703_224 globalBody703_90

def globalBody703_226 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_227 : Prog (BitVec 64) :=
.seq globalBody703_225 globalBody703_226

def globalBody703_228 : Prog (BitVec 64) :=
.seq globalBody703_227 globalBody703_1

def globalBody703_229 : Prog (BitVec 64) :=
.seq globalBody703_228 globalBody703_3

def globalBody703_230 : Prog (BitVec 64) :=
.seq globalBody703_229 globalBody703_5

def globalBody703_231 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_232 : Prog (BitVec 64) :=
.seq globalBody703_230 globalBody703_231

def globalBody703_233 : Prog (BitVec 64) :=
.seq globalBody703_232 globalBody703_9

def globalBody703_234 : Prog (BitVec 64) :=
.seq globalBody703_233 globalBody703_11

def globalBody703_235 : Prog (BitVec 64) :=
.seq globalBody703_234 globalBody703_13

def globalBody703_236 : Prog (BitVec 64) :=
.seq globalBody703_235 globalBody703_15

def globalBody703_237 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_238 : Prog (BitVec 64) :=
.seq globalBody703_236 globalBody703_237

def globalBody703_239 : Prog (BitVec 64) :=
.seq globalBody703_238 globalBody703_19

def globalBody703_240 : Prog (BitVec 64) :=
.seq globalBody703_239 globalBody703_11

def globalBody703_241 : Prog (BitVec 64) :=
.seq globalBody703_240 globalBody703_22

def globalBody703_242 : Prog (BitVec 64) :=
.seq globalBody703_241 globalBody703_15

def globalBody703_243 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_244 : Prog (BitVec 64) :=
.seq globalBody703_242 globalBody703_243

def globalBody703_245 : Prog (BitVec 64) :=
.seq globalBody703_244 globalBody703_27

def globalBody703_246 : Prog (BitVec 64) :=
.seq globalBody703_245 globalBody703_11

def globalBody703_247 : Prog (BitVec 64) :=
.seq globalBody703_246 globalBody703_30

def globalBody703_248 : Prog (BitVec 64) :=
.seq globalBody703_247 globalBody703_15

def globalBody703_249 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_250 : Prog (BitVec 64) :=
.seq globalBody703_248 globalBody703_249

def globalBody703_251 : Prog (BitVec 64) :=
.seq globalBody703_250 globalBody703_35

def globalBody703_252 : Prog (BitVec 64) :=
.seq globalBody703_251 globalBody703_11

def globalBody703_253 : Prog (BitVec 64) :=
.seq globalBody703_252 globalBody703_38

def globalBody703_254 : Prog (BitVec 64) :=
.seq globalBody703_253 globalBody703_15

def globalBody703_255 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_256 : Prog (BitVec 64) :=
.seq globalBody703_254 globalBody703_255

def globalBody703_257 : Prog (BitVec 64) :=
.seq globalBody703_256 globalBody703_43

def globalBody703_258 : Prog (BitVec 64) :=
.seq globalBody703_257 globalBody703_11

def globalBody703_259 : Prog (BitVec 64) :=
.seq globalBody703_258 globalBody703_46

def globalBody703_260 : Prog (BitVec 64) :=
.seq globalBody703_259 globalBody703_15

def globalBody703_261 : Prog (BitVec 64) :=
.seq globalBody703_260 globalBody703_49

def globalBody703_262 : Prog (BitVec 64) :=
.seq globalBody703_261 globalBody703_51

def globalBody703_263 : Prog (BitVec 64) :=
.seq globalBody703_262 globalBody703_53

def globalBody703_264 : Prog (BitVec 64) :=
.seq globalBody703_263 globalBody703_1

def globalBody703_265 : Prog (BitVec 64) :=
.seq globalBody703_264 globalBody703_5

def globalBody703_266 : Prog (BitVec 64) :=
.seq globalBody703_265 globalBody703_57

def globalBody703_267 : Prog (BitVec 64) :=
.seq globalBody703_266 globalBody703_9

def globalBody703_268 : Prog (BitVec 64) :=
.seq globalBody703_267 globalBody703_11

def globalBody703_269 : Prog (BitVec 64) :=
.seq globalBody703_268 globalBody703_61

def globalBody703_270 : Prog (BitVec 64) :=
.seq globalBody703_269 globalBody703_15

def globalBody703_271 : Prog (BitVec 64) :=
.seq globalBody703_270 globalBody703_64

def globalBody703_272 : Prog (BitVec 64) :=
.seq globalBody703_271 globalBody703_19

def globalBody703_273 : Prog (BitVec 64) :=
.seq globalBody703_272 globalBody703_11

def globalBody703_274 : Prog (BitVec 64) :=
.seq globalBody703_273 globalBody703_13

def globalBody703_275 : Prog (BitVec 64) :=
.seq globalBody703_274 globalBody703_15

def globalBody703_276 : Prog (BitVec 64) :=
.seq globalBody703_275 globalBody703_70

def globalBody703_277 : Prog (BitVec 64) :=
.seq globalBody703_276 globalBody703_27

def globalBody703_278 : Prog (BitVec 64) :=
.seq globalBody703_277 globalBody703_11

def globalBody703_279 : Prog (BitVec 64) :=
.seq globalBody703_278 globalBody703_22

def globalBody703_280 : Prog (BitVec 64) :=
.seq globalBody703_279 globalBody703_15

def globalBody703_281 : Prog (BitVec 64) :=
.seq globalBody703_280 globalBody703_76

def globalBody703_282 : Prog (BitVec 64) :=
.seq globalBody703_281 globalBody703_35

def globalBody703_283 : Prog (BitVec 64) :=
.seq globalBody703_282 globalBody703_11

def globalBody703_284 : Prog (BitVec 64) :=
.seq globalBody703_283 globalBody703_30

def globalBody703_285 : Prog (BitVec 64) :=
.seq globalBody703_284 globalBody703_15

def globalBody703_286 : Prog (BitVec 64) :=
.seq globalBody703_285 globalBody703_82

def globalBody703_287 : Prog (BitVec 64) :=
.seq globalBody703_286 globalBody703_43

def globalBody703_288 : Prog (BitVec 64) :=
.seq globalBody703_287 globalBody703_11

def globalBody703_289 : Prog (BitVec 64) :=
.seq globalBody703_288 globalBody703_38

def globalBody703_290 : Prog (BitVec 64) :=
.seq globalBody703_289 globalBody703_15

def globalBody703_291 : Prog (BitVec 64) :=
.seq globalBody703_290 globalBody703_88

def globalBody703_292 : Prog (BitVec 64) :=
.seq globalBody703_291 globalBody703_90

def globalBody703_293 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_294 : Prog (BitVec 64) :=
.seq globalBody703_292 globalBody703_293

def globalBody703_295 : Prog (BitVec 64) :=
.seq globalBody703_294 globalBody703_1

def globalBody703_296 : Prog (BitVec 64) :=
.seq globalBody703_295 globalBody703_3

def globalBody703_297 : Prog (BitVec 64) :=
.seq globalBody703_296 globalBody703_5

def globalBody703_298 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_299 : Prog (BitVec 64) :=
.seq globalBody703_297 globalBody703_298

def globalBody703_300 : Prog (BitVec 64) :=
.seq globalBody703_299 globalBody703_9

def globalBody703_301 : Prog (BitVec 64) :=
.seq globalBody703_300 globalBody703_11

def globalBody703_302 : Prog (BitVec 64) :=
.seq globalBody703_301 globalBody703_13

def globalBody703_303 : Prog (BitVec 64) :=
.seq globalBody703_302 globalBody703_15

def globalBody703_304 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_305 : Prog (BitVec 64) :=
.seq globalBody703_303 globalBody703_304

def globalBody703_306 : Prog (BitVec 64) :=
.seq globalBody703_305 globalBody703_19

def globalBody703_307 : Prog (BitVec 64) :=
.seq globalBody703_306 globalBody703_11

def globalBody703_308 : Prog (BitVec 64) :=
.seq globalBody703_307 globalBody703_22

def globalBody703_309 : Prog (BitVec 64) :=
.seq globalBody703_308 globalBody703_15

def globalBody703_310 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_311 : Prog (BitVec 64) :=
.seq globalBody703_309 globalBody703_310

def globalBody703_312 : Prog (BitVec 64) :=
.seq globalBody703_311 globalBody703_27

def globalBody703_313 : Prog (BitVec 64) :=
.seq globalBody703_312 globalBody703_11

def globalBody703_314 : Prog (BitVec 64) :=
.seq globalBody703_313 globalBody703_30

def globalBody703_315 : Prog (BitVec 64) :=
.seq globalBody703_314 globalBody703_15

def globalBody703_316 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_317 : Prog (BitVec 64) :=
.seq globalBody703_315 globalBody703_316

def globalBody703_318 : Prog (BitVec 64) :=
.seq globalBody703_317 globalBody703_35

def globalBody703_319 : Prog (BitVec 64) :=
.seq globalBody703_318 globalBody703_11

def globalBody703_320 : Prog (BitVec 64) :=
.seq globalBody703_319 globalBody703_38

def globalBody703_321 : Prog (BitVec 64) :=
.seq globalBody703_320 globalBody703_15

def globalBody703_322 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_323 : Prog (BitVec 64) :=
.seq globalBody703_321 globalBody703_322

def globalBody703_324 : Prog (BitVec 64) :=
.seq globalBody703_323 globalBody703_43

def globalBody703_325 : Prog (BitVec 64) :=
.seq globalBody703_324 globalBody703_11

def globalBody703_326 : Prog (BitVec 64) :=
.seq globalBody703_325 globalBody703_46

def globalBody703_327 : Prog (BitVec 64) :=
.seq globalBody703_326 globalBody703_15

def globalBody703_328 : Prog (BitVec 64) :=
.seq globalBody703_327 globalBody703_49

def globalBody703_329 : Prog (BitVec 64) :=
.seq globalBody703_328 globalBody703_51

def globalBody703_330 : Prog (BitVec 64) :=
.seq globalBody703_329 globalBody703_53

def globalBody703_331 : Prog (BitVec 64) :=
.seq globalBody703_330 globalBody703_1

def globalBody703_332 : Prog (BitVec 64) :=
.seq globalBody703_331 globalBody703_5

def globalBody703_333 : Prog (BitVec 64) :=
.seq globalBody703_332 globalBody703_57

def globalBody703_334 : Prog (BitVec 64) :=
.seq globalBody703_333 globalBody703_9

def globalBody703_335 : Prog (BitVec 64) :=
.seq globalBody703_334 globalBody703_11

def globalBody703_336 : Prog (BitVec 64) :=
.seq globalBody703_335 globalBody703_61

def globalBody703_337 : Prog (BitVec 64) :=
.seq globalBody703_336 globalBody703_15

def globalBody703_338 : Prog (BitVec 64) :=
.seq globalBody703_337 globalBody703_64

def globalBody703_339 : Prog (BitVec 64) :=
.seq globalBody703_338 globalBody703_19

def globalBody703_340 : Prog (BitVec 64) :=
.seq globalBody703_339 globalBody703_11

def globalBody703_341 : Prog (BitVec 64) :=
.seq globalBody703_340 globalBody703_13

def globalBody703_342 : Prog (BitVec 64) :=
.seq globalBody703_341 globalBody703_15

def globalBody703_343 : Prog (BitVec 64) :=
.seq globalBody703_342 globalBody703_70

def globalBody703_344 : Prog (BitVec 64) :=
.seq globalBody703_343 globalBody703_27

def globalBody703_345 : Prog (BitVec 64) :=
.seq globalBody703_344 globalBody703_11

def globalBody703_346 : Prog (BitVec 64) :=
.seq globalBody703_345 globalBody703_22

def globalBody703_347 : Prog (BitVec 64) :=
.seq globalBody703_346 globalBody703_15

def globalBody703_348 : Prog (BitVec 64) :=
.seq globalBody703_347 globalBody703_76

def globalBody703_349 : Prog (BitVec 64) :=
.seq globalBody703_348 globalBody703_35

def globalBody703_350 : Prog (BitVec 64) :=
.seq globalBody703_349 globalBody703_11

def globalBody703_351 : Prog (BitVec 64) :=
.seq globalBody703_350 globalBody703_30

def globalBody703_352 : Prog (BitVec 64) :=
.seq globalBody703_351 globalBody703_15

def globalBody703_353 : Prog (BitVec 64) :=
.seq globalBody703_352 globalBody703_82

def globalBody703_354 : Prog (BitVec 64) :=
.seq globalBody703_353 globalBody703_43

def globalBody703_355 : Prog (BitVec 64) :=
.seq globalBody703_354 globalBody703_11

def globalBody703_356 : Prog (BitVec 64) :=
.seq globalBody703_355 globalBody703_38

def globalBody703_357 : Prog (BitVec 64) :=
.seq globalBody703_356 globalBody703_15

def globalBody703_358 : Prog (BitVec 64) :=
.seq globalBody703_357 globalBody703_88

def globalBody703_359 : Prog (BitVec 64) :=
.seq globalBody703_358 globalBody703_90

def globalBody703_360 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_361 : Prog (BitVec 64) :=
.seq globalBody703_359 globalBody703_360

def globalBody703_362 : Prog (BitVec 64) :=
.seq globalBody703_361 globalBody703_1

def globalBody703_363 : Prog (BitVec 64) :=
.seq globalBody703_362 globalBody703_3

def globalBody703_364 : Prog (BitVec 64) :=
.seq globalBody703_363 globalBody703_5

def globalBody703_365 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_366 : Prog (BitVec 64) :=
.seq globalBody703_364 globalBody703_365

def globalBody703_367 : Prog (BitVec 64) :=
.seq globalBody703_366 globalBody703_9

def globalBody703_368 : Prog (BitVec 64) :=
.seq globalBody703_367 globalBody703_11

def globalBody703_369 : Prog (BitVec 64) :=
.seq globalBody703_368 globalBody703_13

def globalBody703_370 : Prog (BitVec 64) :=
.seq globalBody703_369 globalBody703_15

def globalBody703_371 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_372 : Prog (BitVec 64) :=
.seq globalBody703_370 globalBody703_371

def globalBody703_373 : Prog (BitVec 64) :=
.seq globalBody703_372 globalBody703_19

def globalBody703_374 : Prog (BitVec 64) :=
.seq globalBody703_373 globalBody703_11

def globalBody703_375 : Prog (BitVec 64) :=
.seq globalBody703_374 globalBody703_22

def globalBody703_376 : Prog (BitVec 64) :=
.seq globalBody703_375 globalBody703_15

def globalBody703_377 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_378 : Prog (BitVec 64) :=
.seq globalBody703_376 globalBody703_377

def globalBody703_379 : Prog (BitVec 64) :=
.seq globalBody703_378 globalBody703_27

def globalBody703_380 : Prog (BitVec 64) :=
.seq globalBody703_379 globalBody703_11

def globalBody703_381 : Prog (BitVec 64) :=
.seq globalBody703_380 globalBody703_30

def globalBody703_382 : Prog (BitVec 64) :=
.seq globalBody703_381 globalBody703_15

def globalBody703_383 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_384 : Prog (BitVec 64) :=
.seq globalBody703_382 globalBody703_383

def globalBody703_385 : Prog (BitVec 64) :=
.seq globalBody703_384 globalBody703_35

def globalBody703_386 : Prog (BitVec 64) :=
.seq globalBody703_385 globalBody703_11

def globalBody703_387 : Prog (BitVec 64) :=
.seq globalBody703_386 globalBody703_38

def globalBody703_388 : Prog (BitVec 64) :=
.seq globalBody703_387 globalBody703_15

def globalBody703_389 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "pr"), none)) "mul64x64"
  [Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "b")]

def globalBody703_390 : Prog (BitVec 64) :=
.seq globalBody703_388 globalBody703_389

def globalBody703_391 : Prog (BitVec 64) :=
.seq globalBody703_390 globalBody703_43

def globalBody703_392 : Prog (BitVec 64) :=
.seq globalBody703_391 globalBody703_11

def globalBody703_393 : Prog (BitVec 64) :=
.seq globalBody703_392 globalBody703_46

def globalBody703_394 : Prog (BitVec 64) :=
.seq globalBody703_393 globalBody703_15

def globalBody703_395 : Prog (BitVec 64) :=
.seq globalBody703_394 globalBody703_49

def globalBody703_396 : Prog (BitVec 64) :=
.seq globalBody703_395 globalBody703_51

def globalBody703_397 : Prog (BitVec 64) :=
.seq globalBody703_396 globalBody703_53

def globalBody703_398 : Prog (BitVec 64) :=
.seq globalBody703_397 globalBody703_1

def globalBody703_399 : Prog (BitVec 64) :=
.seq globalBody703_398 globalBody703_5

def globalBody703_400 : Prog (BitVec 64) :=
.seq globalBody703_399 globalBody703_57

def globalBody703_401 : Prog (BitVec 64) :=
.seq globalBody703_400 globalBody703_9

def globalBody703_402 : Prog (BitVec 64) :=
.seq globalBody703_401 globalBody703_11

def globalBody703_403 : Prog (BitVec 64) :=
.seq globalBody703_402 globalBody703_61

def globalBody703_404 : Prog (BitVec 64) :=
.seq globalBody703_403 globalBody703_15

def globalBody703_405 : Prog (BitVec 64) :=
.seq globalBody703_404 globalBody703_64

def globalBody703_406 : Prog (BitVec 64) :=
.seq globalBody703_405 globalBody703_19

def globalBody703_407 : Prog (BitVec 64) :=
.seq globalBody703_406 globalBody703_11

def globalBody703_408 : Prog (BitVec 64) :=
.seq globalBody703_407 globalBody703_13

def globalBody703_409 : Prog (BitVec 64) :=
.seq globalBody703_408 globalBody703_15

def globalBody703_410 : Prog (BitVec 64) :=
.seq globalBody703_409 globalBody703_70

def globalBody703_411 : Prog (BitVec 64) :=
.seq globalBody703_410 globalBody703_27

def globalBody703_412 : Prog (BitVec 64) :=
.seq globalBody703_411 globalBody703_11

def globalBody703_413 : Prog (BitVec 64) :=
.seq globalBody703_412 globalBody703_22

def globalBody703_414 : Prog (BitVec 64) :=
.seq globalBody703_413 globalBody703_15

def globalBody703_415 : Prog (BitVec 64) :=
.seq globalBody703_414 globalBody703_76

def globalBody703_416 : Prog (BitVec 64) :=
.seq globalBody703_415 globalBody703_35

def globalBody703_417 : Prog (BitVec 64) :=
.seq globalBody703_416 globalBody703_11

def globalBody703_418 : Prog (BitVec 64) :=
.seq globalBody703_417 globalBody703_30

def globalBody703_419 : Prog (BitVec 64) :=
.seq globalBody703_418 globalBody703_15

def globalBody703_420 : Prog (BitVec 64) :=
.seq globalBody703_419 globalBody703_82

def globalBody703_421 : Prog (BitVec 64) :=
.seq globalBody703_420 globalBody703_43

def globalBody703_422 : Prog (BitVec 64) :=
.seq globalBody703_421 globalBody703_11

def globalBody703_423 : Prog (BitVec 64) :=
.seq globalBody703_422 globalBody703_38

def globalBody703_424 : Prog (BitVec 64) :=
.seq globalBody703_423 globalBody703_15

def globalBody703_425 : Prog (BitVec 64) :=
.seq globalBody703_424 globalBody703_88

def globalBody703_426 : Prog (BitVec 64) :=
.seq globalBody703_425 globalBody703_90

def globalBody703_427 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "d")])

def globalBody703_428 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody703_429 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 6 (Flapjack.Exp.var Flapjack.VarKind.local "d"))
  (Flapjack.Exp.const 1#64)) globalBody703_427 globalBody703_428

def globalBody703_430 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "t1",
      Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t3",
      Flapjack.Exp.var Flapjack.VarKind.local "t4", Flapjack.Exp.var Flapjack.VarKind.local "t5"])

def globalBody703_431 : Prog (BitVec 64) :=
.seq globalBody703_429 globalBody703_430

def globalBody703_432 : Prog (BitVec 64) :=
.decCall ("d") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one]) ("bls_fp_sub_raw") ([Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "t1",
      Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t3",
      Flapjack.Exp.var Flapjack.VarKind.local "t4", Flapjack.Exp.var Flapjack.VarKind.local "t5"],
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 13402431016077863595#64, Flapjack.Exp.const 2210141511517208575#64,
      Flapjack.Exp.const 7435674573564081700#64, Flapjack.Exp.const 7239337960414712511#64,
      Flapjack.Exp.const 5412103778470702295#64, Flapjack.Exp.const 1873798617647539866#64]]) globalBody703_431

def globalBody703_433 : Prog (BitVec 64) :=
.seq globalBody703_426 globalBody703_432

def globalBody703_434 : Prog (BitVec 64) :=
.dec ("s2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody703_433

def globalBody703_435 : Prog (BitVec 64) :=
.dec ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody703_434

def globalBody703_436 : Prog (BitVec 64) :=
.dec ("pr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody703_435

def globalBody703_437 : Prog (BitVec 64) :=
.dec ("m") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody703_436

def globalBody703_438 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody703_437

def globalBody703_439 : Prog (BitVec 64) :=
.dec ("t6") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody703_438

def globalBody703_440 : Prog (BitVec 64) :=
.dec ("t5") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody703_439

def globalBody703_441 : Prog (BitVec 64) :=
.dec ("t4") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody703_440

def globalBody703_442 : Prog (BitVec 64) :=
.dec ("t3") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody703_441

def globalBody703_443 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody703_442

def globalBody703_444 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody703_443

def globalBody703_445 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody703_444

def globalData703 : Decl (BitVec 64) :=
.function { name := "bls_fp_mul", inline := false, exported := false, params := [("a",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("b",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := globalBody703_445, returnShape := (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) }
def globalOutput703 := Pancake.PanLang.declToHOL globalData703
end InitECandidate.Proofs.FrontendStages.Declarations
