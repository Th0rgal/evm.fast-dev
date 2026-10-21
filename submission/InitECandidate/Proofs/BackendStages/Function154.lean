import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.StackAnalysis.Data154
import InitECandidate.Proofs.CompilerComputation
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.BackendStages
def stackBody154_0 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 5

def stackBody154_1 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.binop Flapjack.BinOp.or 4 1
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.reg 1)))

def stackBody154_2 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 1 Flapjack.Compiler.Backend.StackLang.StoreName.heapLength

def stackBody154_3 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.shift Flapjack.Shift.lsl 1 1
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 1#64)))

def stackBody154_4 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.opCurrHeap Flapjack.BinOp.add 1 1

def stackBody154_5 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.load 1
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 1 18446744073709551568#64))

def stackBody154_6 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 0 4

def stackBody154_7 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 2 3

def stackBody154_8 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 4 2

def stackBody154_9 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 3 1

def stackBody154_10 : StackLang.HolProg 64 :=
.seq stackBody154_8 stackBody154_9

def stackBody154_11 : StackLang.HolProg 64 :=
.seq stackBody154_7 stackBody154_10

def stackBody154_12 : StackLang.HolProg 64 :=
.seq stackBody154_6 stackBody154_11

def stackBody154_13 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_14 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 137#64)

def stackBody154_15 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_16 : StackLang.HolProg 64 :=
.seq stackBody154_14 stackBody154_15

def stackBody154_17 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 3

def stackBody154_18 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 1#64)

def stackBody154_19 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_20 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.locValue 22 154 3

def stackBody154_21 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 1

def stackBody154_22 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 22 Flapjack.Compiler.Backend.StackLang.StoreName.handler

def stackBody154_23 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 2

def stackBody154_24 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_25 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackGetSize 22

def stackBody154_26 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_27 : StackLang.HolProg 64 :=
.seq stackBody154_25 stackBody154_26

def stackBody154_28 : StackLang.HolProg 64 :=
.seq stackBody154_24 stackBody154_27

def stackBody154_29 : StackLang.HolProg 64 :=
.seq stackBody154_23 stackBody154_28

def stackBody154_30 : StackLang.HolProg 64 :=
.seq stackBody154_22 stackBody154_29

def stackBody154_31 : StackLang.HolProg 64 :=
.seq stackBody154_21 stackBody154_30

def stackBody154_32 : StackLang.HolProg 64 :=
.seq stackBody154_20 stackBody154_31

def stackBody154_33 : StackLang.HolProg 64 :=
.seq stackBody154_19 stackBody154_32

def stackBody154_34 : StackLang.HolProg 64 :=
.seq stackBody154_18 stackBody154_33

def stackBody154_35 : StackLang.HolProg 64 :=
.seq stackBody154_17 stackBody154_34

def stackBody154_36 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 0

def stackBody154_37 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_38 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_39 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 2

def stackBody154_40 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_41 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackFree 3

def stackBody154_42 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 2 2

def stackBody154_43 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 1

def stackBody154_44 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 2

def stackBody154_45 : StackLang.HolProg 64 :=
.seq stackBody154_43 stackBody154_44

def stackBody154_46 : StackLang.HolProg 64 :=
.seq stackBody154_42 stackBody154_45

def stackBody154_47 : StackLang.HolProg 64 :=
.seq stackBody154_41 stackBody154_46

def stackBody154_48 : StackLang.HolProg 64 :=
.seq stackBody154_40 stackBody154_47

def stackBody154_49 : StackLang.HolProg 64 :=
.seq stackBody154_39 stackBody154_48

def stackBody154_50 : StackLang.HolProg 64 :=
.seq stackBody154_38 stackBody154_49

def stackBody154_51 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 2 2

def stackBody154_52 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 1

def stackBody154_53 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 2

def stackBody154_54 : StackLang.HolProg 64 :=
.seq stackBody154_52 stackBody154_53

def stackBody154_55 : StackLang.HolProg 64 :=
.seq stackBody154_51 stackBody154_54

def stackBody154_56 : StackLang.HolProg 64 :=
.call none (Sum.inl 5) none

def stackBody154_57 : StackLang.HolProg 64 :=
.seq stackBody154_55 stackBody154_56

def stackBody154_58 : StackLang.HolProg 64 :=
.call (some (stackBody154_50, 0, 154, 2)) (Sum.inl 150) (some (stackBody154_57, 154, 3))

def stackBody154_59 : StackLang.HolProg 64 :=
.seq stackBody154_37 stackBody154_58

def stackBody154_60 : StackLang.HolProg 64 :=
.seq stackBody154_36 stackBody154_59

def stackBody154_61 : StackLang.HolProg 64 :=
.seq stackBody154_35 stackBody154_60

def stackBody154_62 : StackLang.HolProg 64 :=
.seq stackBody154_16 stackBody154_61

def stackBody154_63 : StackLang.HolProg 64 :=
.seq stackBody154_13 stackBody154_62

def stackBody154_64 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.tick

def stackBody154_65 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 0 Flapjack.Compiler.Backend.StackLang.StoreName.heapLength

def stackBody154_66 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.shift Flapjack.Shift.lsl 0 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 1#64)))

def stackBody154_67 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.opCurrHeap Flapjack.BinOp.add 0 0

def stackBody154_68 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.load 0
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 0 18446744073709551552#64))

def stackBody154_69 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.binop Flapjack.BinOp.add 1 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 32#64)))

def stackBody154_70 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_71 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 3 32#64)

def stackBody154_72 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_73 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_74 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 138#64)

def stackBody154_75 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_76 : StackLang.HolProg 64 :=
.seq stackBody154_74 stackBody154_75

def stackBody154_77 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 3

def stackBody154_78 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 1#64)

def stackBody154_79 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_80 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.locValue 22 154 5

def stackBody154_81 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 1

def stackBody154_82 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 22 Flapjack.Compiler.Backend.StackLang.StoreName.handler

def stackBody154_83 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 2

def stackBody154_84 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_85 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackGetSize 22

def stackBody154_86 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_87 : StackLang.HolProg 64 :=
.seq stackBody154_85 stackBody154_86

def stackBody154_88 : StackLang.HolProg 64 :=
.seq stackBody154_84 stackBody154_87

def stackBody154_89 : StackLang.HolProg 64 :=
.seq stackBody154_83 stackBody154_88

def stackBody154_90 : StackLang.HolProg 64 :=
.seq stackBody154_82 stackBody154_89

def stackBody154_91 : StackLang.HolProg 64 :=
.seq stackBody154_81 stackBody154_90

def stackBody154_92 : StackLang.HolProg 64 :=
.seq stackBody154_80 stackBody154_91

def stackBody154_93 : StackLang.HolProg 64 :=
.seq stackBody154_79 stackBody154_92

def stackBody154_94 : StackLang.HolProg 64 :=
.seq stackBody154_78 stackBody154_93

def stackBody154_95 : StackLang.HolProg 64 :=
.seq stackBody154_77 stackBody154_94

def stackBody154_96 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 0

def stackBody154_97 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_98 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_99 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 2

def stackBody154_100 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_101 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackFree 3

def stackBody154_102 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 2 3

def stackBody154_103 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 2

def stackBody154_104 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 3

def stackBody154_105 : StackLang.HolProg 64 :=
.seq stackBody154_103 stackBody154_104

def stackBody154_106 : StackLang.HolProg 64 :=
.seq stackBody154_102 stackBody154_105

def stackBody154_107 : StackLang.HolProg 64 :=
.seq stackBody154_101 stackBody154_106

def stackBody154_108 : StackLang.HolProg 64 :=
.seq stackBody154_100 stackBody154_107

def stackBody154_109 : StackLang.HolProg 64 :=
.seq stackBody154_99 stackBody154_108

def stackBody154_110 : StackLang.HolProg 64 :=
.seq stackBody154_98 stackBody154_109

def stackBody154_111 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 2 3

def stackBody154_112 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 2

def stackBody154_113 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 3

def stackBody154_114 : StackLang.HolProg 64 :=
.seq stackBody154_112 stackBody154_113

def stackBody154_115 : StackLang.HolProg 64 :=
.seq stackBody154_111 stackBody154_114

def stackBody154_116 : StackLang.HolProg 64 :=
.call none (Sum.inl 5) none

def stackBody154_117 : StackLang.HolProg 64 :=
.seq stackBody154_115 stackBody154_116

def stackBody154_118 : StackLang.HolProg 64 :=
.call (some (stackBody154_110, 0, 154, 4)) (Sum.inl 77) (some (stackBody154_117, 154, 5))

def stackBody154_119 : StackLang.HolProg 64 :=
.seq stackBody154_97 stackBody154_118

def stackBody154_120 : StackLang.HolProg 64 :=
.seq stackBody154_96 stackBody154_119

def stackBody154_121 : StackLang.HolProg 64 :=
.seq stackBody154_95 stackBody154_120

def stackBody154_122 : StackLang.HolProg 64 :=
.seq stackBody154_76 stackBody154_121

def stackBody154_123 : StackLang.HolProg 64 :=
.seq stackBody154_73 stackBody154_122

def stackBody154_124 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.tick

def stackBody154_125 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 0 Flapjack.Compiler.Backend.StackLang.StoreName.heapLength

def stackBody154_126 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.shift Flapjack.Shift.lsl 0 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 1#64)))

def stackBody154_127 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.opCurrHeap Flapjack.BinOp.add 0 0

def stackBody154_128 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.load 0
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 0 18446744073709551552#64))

def stackBody154_129 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.binop Flapjack.BinOp.add 1 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 64#64)))

def stackBody154_130 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_131 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 3 32#64)

def stackBody154_132 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_133 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_134 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 139#64)

def stackBody154_135 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_136 : StackLang.HolProg 64 :=
.seq stackBody154_134 stackBody154_135

def stackBody154_137 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 3

def stackBody154_138 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 1#64)

def stackBody154_139 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_140 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.locValue 22 154 7

def stackBody154_141 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 1

def stackBody154_142 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 22 Flapjack.Compiler.Backend.StackLang.StoreName.handler

def stackBody154_143 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 2

def stackBody154_144 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_145 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackGetSize 22

def stackBody154_146 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_147 : StackLang.HolProg 64 :=
.seq stackBody154_145 stackBody154_146

def stackBody154_148 : StackLang.HolProg 64 :=
.seq stackBody154_144 stackBody154_147

def stackBody154_149 : StackLang.HolProg 64 :=
.seq stackBody154_143 stackBody154_148

def stackBody154_150 : StackLang.HolProg 64 :=
.seq stackBody154_142 stackBody154_149

def stackBody154_151 : StackLang.HolProg 64 :=
.seq stackBody154_141 stackBody154_150

def stackBody154_152 : StackLang.HolProg 64 :=
.seq stackBody154_140 stackBody154_151

def stackBody154_153 : StackLang.HolProg 64 :=
.seq stackBody154_139 stackBody154_152

def stackBody154_154 : StackLang.HolProg 64 :=
.seq stackBody154_138 stackBody154_153

def stackBody154_155 : StackLang.HolProg 64 :=
.seq stackBody154_137 stackBody154_154

def stackBody154_156 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 0

def stackBody154_157 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_158 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_159 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 2

def stackBody154_160 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_161 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackFree 3

def stackBody154_162 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_163 : StackLang.HolProg 64 :=
.seq stackBody154_161 stackBody154_162

def stackBody154_164 : StackLang.HolProg 64 :=
.seq stackBody154_160 stackBody154_163

def stackBody154_165 : StackLang.HolProg 64 :=
.seq stackBody154_159 stackBody154_164

def stackBody154_166 : StackLang.HolProg 64 :=
.seq stackBody154_158 stackBody154_165

def stackBody154_167 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_168 : StackLang.HolProg 64 :=
.call none (Sum.inl 5) none

def stackBody154_169 : StackLang.HolProg 64 :=
.seq stackBody154_167 stackBody154_168

def stackBody154_170 : StackLang.HolProg 64 :=
.call (some (stackBody154_166, 0, 154, 6)) (Sum.inl 77) (some (stackBody154_169, 154, 7))

def stackBody154_171 : StackLang.HolProg 64 :=
.seq stackBody154_157 stackBody154_170

def stackBody154_172 : StackLang.HolProg 64 :=
.seq stackBody154_156 stackBody154_171

def stackBody154_173 : StackLang.HolProg 64 :=
.seq stackBody154_155 stackBody154_172

def stackBody154_174 : StackLang.HolProg 64 :=
.seq stackBody154_136 stackBody154_173

def stackBody154_175 : StackLang.HolProg 64 :=
.seq stackBody154_133 stackBody154_174

def stackBody154_176 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.tick

def stackBody154_177 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 0 Flapjack.Compiler.Backend.StackLang.StoreName.heapLength

def stackBody154_178 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.shift Flapjack.Shift.lsl 0 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 1#64)))

def stackBody154_179 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.opCurrHeap Flapjack.BinOp.add 0 0

def stackBody154_180 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.load 1
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 0 18446744073709551568#64))

def stackBody154_181 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_182 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.load 0
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 0 18446744073709551552#64))

def stackBody154_183 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.binop Flapjack.BinOp.add 2 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 32#64)))

def stackBody154_184 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_185 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_186 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 140#64)

def stackBody154_187 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_188 : StackLang.HolProg 64 :=
.seq stackBody154_186 stackBody154_187

def stackBody154_189 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 3

def stackBody154_190 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 1#64)

def stackBody154_191 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_192 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.locValue 22 154 9

def stackBody154_193 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 1

def stackBody154_194 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 22 Flapjack.Compiler.Backend.StackLang.StoreName.handler

def stackBody154_195 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 2

def stackBody154_196 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_197 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackGetSize 22

def stackBody154_198 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_199 : StackLang.HolProg 64 :=
.seq stackBody154_197 stackBody154_198

def stackBody154_200 : StackLang.HolProg 64 :=
.seq stackBody154_196 stackBody154_199

def stackBody154_201 : StackLang.HolProg 64 :=
.seq stackBody154_195 stackBody154_200

def stackBody154_202 : StackLang.HolProg 64 :=
.seq stackBody154_194 stackBody154_201

def stackBody154_203 : StackLang.HolProg 64 :=
.seq stackBody154_193 stackBody154_202

def stackBody154_204 : StackLang.HolProg 64 :=
.seq stackBody154_192 stackBody154_203

def stackBody154_205 : StackLang.HolProg 64 :=
.seq stackBody154_191 stackBody154_204

def stackBody154_206 : StackLang.HolProg 64 :=
.seq stackBody154_190 stackBody154_205

def stackBody154_207 : StackLang.HolProg 64 :=
.seq stackBody154_189 stackBody154_206

def stackBody154_208 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 0

def stackBody154_209 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_210 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_211 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 2

def stackBody154_212 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_213 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackFree 3

def stackBody154_214 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_215 : StackLang.HolProg 64 :=
.seq stackBody154_213 stackBody154_214

def stackBody154_216 : StackLang.HolProg 64 :=
.seq stackBody154_212 stackBody154_215

def stackBody154_217 : StackLang.HolProg 64 :=
.seq stackBody154_211 stackBody154_216

def stackBody154_218 : StackLang.HolProg 64 :=
.seq stackBody154_210 stackBody154_217

def stackBody154_219 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_220 : StackLang.HolProg 64 :=
.call none (Sum.inl 5) none

def stackBody154_221 : StackLang.HolProg 64 :=
.seq stackBody154_219 stackBody154_220

def stackBody154_222 : StackLang.HolProg 64 :=
.call (some (stackBody154_218, 0, 154, 8)) (Sum.inl 151) (some (stackBody154_221, 154, 9))

def stackBody154_223 : StackLang.HolProg 64 :=
.seq stackBody154_209 stackBody154_222

def stackBody154_224 : StackLang.HolProg 64 :=
.seq stackBody154_208 stackBody154_223

def stackBody154_225 : StackLang.HolProg 64 :=
.seq stackBody154_207 stackBody154_224

def stackBody154_226 : StackLang.HolProg 64 :=
.seq stackBody154_188 stackBody154_225

def stackBody154_227 : StackLang.HolProg 64 :=
.seq stackBody154_185 stackBody154_226

def stackBody154_228 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.tick

def stackBody154_229 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 0 Flapjack.Compiler.Backend.StackLang.StoreName.heapLength

def stackBody154_230 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.shift Flapjack.Shift.lsl 0 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 1#64)))

def stackBody154_231 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.opCurrHeap Flapjack.BinOp.add 0 0

def stackBody154_232 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.load 0
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 0 18446744073709551552#64))

def stackBody154_233 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.binop Flapjack.BinOp.add 1 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 32#64)))

def stackBody154_234 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 2 64#64)

def stackBody154_235 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_236 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_237 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 141#64)

def stackBody154_238 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_239 : StackLang.HolProg 64 :=
.seq stackBody154_237 stackBody154_238

def stackBody154_240 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 3

def stackBody154_241 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 1#64)

def stackBody154_242 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_243 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.locValue 22 154 11

def stackBody154_244 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 1

def stackBody154_245 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 22 Flapjack.Compiler.Backend.StackLang.StoreName.handler

def stackBody154_246 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 2

def stackBody154_247 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_248 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackGetSize 22

def stackBody154_249 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_250 : StackLang.HolProg 64 :=
.seq stackBody154_248 stackBody154_249

def stackBody154_251 : StackLang.HolProg 64 :=
.seq stackBody154_247 stackBody154_250

def stackBody154_252 : StackLang.HolProg 64 :=
.seq stackBody154_246 stackBody154_251

def stackBody154_253 : StackLang.HolProg 64 :=
.seq stackBody154_245 stackBody154_252

def stackBody154_254 : StackLang.HolProg 64 :=
.seq stackBody154_244 stackBody154_253

def stackBody154_255 : StackLang.HolProg 64 :=
.seq stackBody154_243 stackBody154_254

def stackBody154_256 : StackLang.HolProg 64 :=
.seq stackBody154_242 stackBody154_255

def stackBody154_257 : StackLang.HolProg 64 :=
.seq stackBody154_241 stackBody154_256

def stackBody154_258 : StackLang.HolProg 64 :=
.seq stackBody154_240 stackBody154_257

def stackBody154_259 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 0

def stackBody154_260 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_261 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_262 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 2

def stackBody154_263 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_264 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackFree 3

def stackBody154_265 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_266 : StackLang.HolProg 64 :=
.seq stackBody154_264 stackBody154_265

def stackBody154_267 : StackLang.HolProg 64 :=
.seq stackBody154_263 stackBody154_266

def stackBody154_268 : StackLang.HolProg 64 :=
.seq stackBody154_262 stackBody154_267

def stackBody154_269 : StackLang.HolProg 64 :=
.seq stackBody154_261 stackBody154_268

def stackBody154_270 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_271 : StackLang.HolProg 64 :=
.call none (Sum.inl 5) none

def stackBody154_272 : StackLang.HolProg 64 :=
.seq stackBody154_270 stackBody154_271

def stackBody154_273 : StackLang.HolProg 64 :=
.call (some (stackBody154_269, 0, 154, 10)) (Sum.inl 78) (some (stackBody154_272, 154, 11))

def stackBody154_274 : StackLang.HolProg 64 :=
.seq stackBody154_260 stackBody154_273

def stackBody154_275 : StackLang.HolProg 64 :=
.seq stackBody154_259 stackBody154_274

def stackBody154_276 : StackLang.HolProg 64 :=
.seq stackBody154_258 stackBody154_275

def stackBody154_277 : StackLang.HolProg 64 :=
.seq stackBody154_239 stackBody154_276

def stackBody154_278 : StackLang.HolProg 64 :=
.seq stackBody154_236 stackBody154_277

def stackBody154_279 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.tick

def stackBody154_280 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 0 Flapjack.Compiler.Backend.StackLang.StoreName.heapLength

def stackBody154_281 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.shift Flapjack.Shift.lsl 0 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 1#64)))

def stackBody154_282 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.opCurrHeap Flapjack.BinOp.add 0 0

def stackBody154_283 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.load 1
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 0 18446744073709551552#64))

def stackBody154_284 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.binop Flapjack.BinOp.add 2 1
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 32#64)))

def stackBody154_285 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 1 128#64)

def stackBody154_286 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.store8 1
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 2 0#64))

def stackBody154_287 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_288 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.load 0
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 0 18446744073709551552#64))

def stackBody154_289 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.binop Flapjack.BinOp.add 1 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 88#64)))

def stackBody154_290 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 2 512#64)

def stackBody154_291 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_292 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_293 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 142#64)

def stackBody154_294 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_295 : StackLang.HolProg 64 :=
.seq stackBody154_293 stackBody154_294

def stackBody154_296 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 3

def stackBody154_297 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 1#64)

def stackBody154_298 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_299 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.locValue 22 154 13

def stackBody154_300 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 1

def stackBody154_301 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 22 Flapjack.Compiler.Backend.StackLang.StoreName.handler

def stackBody154_302 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 2

def stackBody154_303 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_304 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackGetSize 22

def stackBody154_305 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_306 : StackLang.HolProg 64 :=
.seq stackBody154_304 stackBody154_305

def stackBody154_307 : StackLang.HolProg 64 :=
.seq stackBody154_303 stackBody154_306

def stackBody154_308 : StackLang.HolProg 64 :=
.seq stackBody154_302 stackBody154_307

def stackBody154_309 : StackLang.HolProg 64 :=
.seq stackBody154_301 stackBody154_308

def stackBody154_310 : StackLang.HolProg 64 :=
.seq stackBody154_300 stackBody154_309

def stackBody154_311 : StackLang.HolProg 64 :=
.seq stackBody154_299 stackBody154_310

def stackBody154_312 : StackLang.HolProg 64 :=
.seq stackBody154_298 stackBody154_311

def stackBody154_313 : StackLang.HolProg 64 :=
.seq stackBody154_297 stackBody154_312

def stackBody154_314 : StackLang.HolProg 64 :=
.seq stackBody154_296 stackBody154_313

def stackBody154_315 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 0

def stackBody154_316 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_317 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_318 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 2

def stackBody154_319 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_320 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackFree 3

def stackBody154_321 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_322 : StackLang.HolProg 64 :=
.seq stackBody154_320 stackBody154_321

def stackBody154_323 : StackLang.HolProg 64 :=
.seq stackBody154_319 stackBody154_322

def stackBody154_324 : StackLang.HolProg 64 :=
.seq stackBody154_318 stackBody154_323

def stackBody154_325 : StackLang.HolProg 64 :=
.seq stackBody154_317 stackBody154_324

def stackBody154_326 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_327 : StackLang.HolProg 64 :=
.call none (Sum.inl 5) none

def stackBody154_328 : StackLang.HolProg 64 :=
.seq stackBody154_326 stackBody154_327

def stackBody154_329 : StackLang.HolProg 64 :=
.call (some (stackBody154_325, 0, 154, 12)) (Sum.inl 89) (some (stackBody154_328, 154, 13))

def stackBody154_330 : StackLang.HolProg 64 :=
.seq stackBody154_316 stackBody154_329

def stackBody154_331 : StackLang.HolProg 64 :=
.seq stackBody154_315 stackBody154_330

def stackBody154_332 : StackLang.HolProg 64 :=
.seq stackBody154_314 stackBody154_331

def stackBody154_333 : StackLang.HolProg 64 :=
.seq stackBody154_295 stackBody154_332

def stackBody154_334 : StackLang.HolProg 64 :=
.seq stackBody154_292 stackBody154_333

def stackBody154_335 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.tick

def stackBody154_336 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 0 Flapjack.Compiler.Backend.StackLang.StoreName.heapLength

def stackBody154_337 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.shift Flapjack.Shift.lsl 0 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 1#64)))

def stackBody154_338 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.opCurrHeap Flapjack.BinOp.add 0 0

def stackBody154_339 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.load 1
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 0 18446744073709551568#64))

def stackBody154_340 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_341 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.load 0
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 0 18446744073709551552#64))

def stackBody154_342 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.binop Flapjack.BinOp.add 2 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 32#64)))

def stackBody154_343 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_344 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_345 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 143#64)

def stackBody154_346 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_347 : StackLang.HolProg 64 :=
.seq stackBody154_345 stackBody154_346

def stackBody154_348 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 3

def stackBody154_349 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 1#64)

def stackBody154_350 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_351 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.locValue 22 154 15

def stackBody154_352 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 1

def stackBody154_353 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 22 Flapjack.Compiler.Backend.StackLang.StoreName.handler

def stackBody154_354 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 2

def stackBody154_355 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_356 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackGetSize 22

def stackBody154_357 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_358 : StackLang.HolProg 64 :=
.seq stackBody154_356 stackBody154_357

def stackBody154_359 : StackLang.HolProg 64 :=
.seq stackBody154_355 stackBody154_358

def stackBody154_360 : StackLang.HolProg 64 :=
.seq stackBody154_354 stackBody154_359

def stackBody154_361 : StackLang.HolProg 64 :=
.seq stackBody154_353 stackBody154_360

def stackBody154_362 : StackLang.HolProg 64 :=
.seq stackBody154_352 stackBody154_361

def stackBody154_363 : StackLang.HolProg 64 :=
.seq stackBody154_351 stackBody154_362

def stackBody154_364 : StackLang.HolProg 64 :=
.seq stackBody154_350 stackBody154_363

def stackBody154_365 : StackLang.HolProg 64 :=
.seq stackBody154_349 stackBody154_364

def stackBody154_366 : StackLang.HolProg 64 :=
.seq stackBody154_348 stackBody154_365

def stackBody154_367 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 0

def stackBody154_368 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_369 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_370 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 2

def stackBody154_371 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_372 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackFree 3

def stackBody154_373 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 2 3

def stackBody154_374 : StackLang.HolProg 64 :=
.seq stackBody154_372 stackBody154_373

def stackBody154_375 : StackLang.HolProg 64 :=
.seq stackBody154_371 stackBody154_374

def stackBody154_376 : StackLang.HolProg 64 :=
.seq stackBody154_370 stackBody154_375

def stackBody154_377 : StackLang.HolProg 64 :=
.seq stackBody154_369 stackBody154_376

def stackBody154_378 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 2 3

def stackBody154_379 : StackLang.HolProg 64 :=
.call none (Sum.inl 5) none

def stackBody154_380 : StackLang.HolProg 64 :=
.seq stackBody154_378 stackBody154_379

def stackBody154_381 : StackLang.HolProg 64 :=
.call (some (stackBody154_377, 0, 154, 14)) (Sum.inl 151) (some (stackBody154_380, 154, 15))

def stackBody154_382 : StackLang.HolProg 64 :=
.seq stackBody154_368 stackBody154_381

def stackBody154_383 : StackLang.HolProg 64 :=
.seq stackBody154_367 stackBody154_382

def stackBody154_384 : StackLang.HolProg 64 :=
.seq stackBody154_366 stackBody154_383

def stackBody154_385 : StackLang.HolProg 64 :=
.seq stackBody154_347 stackBody154_384

def stackBody154_386 : StackLang.HolProg 64 :=
.seq stackBody154_344 stackBody154_385

def stackBody154_387 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.tick

def stackBody154_388 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 0 Flapjack.Compiler.Backend.StackLang.StoreName.heapLength

def stackBody154_389 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.shift Flapjack.Shift.lsl 0 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.imm 1#64)))

def stackBody154_390 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.opCurrHeap Flapjack.BinOp.add 0 0

def stackBody154_391 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.mem Flapjack.WordMemOp.load 1
    (Flapjack.Compiler.Encoders.Asm.HolAddr.addr 0 18446744073709551568#64))

def stackBody154_392 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_393 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_394 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 144#64)

def stackBody154_395 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_396 : StackLang.HolProg 64 :=
.seq stackBody154_394 stackBody154_395

def stackBody154_397 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 3

def stackBody154_398 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 22 1#64)

def stackBody154_399 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 0

def stackBody154_400 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.locValue 22 154 17

def stackBody154_401 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 1

def stackBody154_402 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.get 22 Flapjack.Compiler.Backend.StackLang.StoreName.handler

def stackBody154_403 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackStore 22 2

def stackBody154_404 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_405 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackGetSize 22

def stackBody154_406 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_407 : StackLang.HolProg 64 :=
.seq stackBody154_405 stackBody154_406

def stackBody154_408 : StackLang.HolProg 64 :=
.seq stackBody154_404 stackBody154_407

def stackBody154_409 : StackLang.HolProg 64 :=
.seq stackBody154_403 stackBody154_408

def stackBody154_410 : StackLang.HolProg 64 :=
.seq stackBody154_402 stackBody154_409

def stackBody154_411 : StackLang.HolProg 64 :=
.seq stackBody154_401 stackBody154_410

def stackBody154_412 : StackLang.HolProg 64 :=
.seq stackBody154_400 stackBody154_411

def stackBody154_413 : StackLang.HolProg 64 :=
.seq stackBody154_399 stackBody154_412

def stackBody154_414 : StackLang.HolProg 64 :=
.seq stackBody154_398 stackBody154_413

def stackBody154_415 : StackLang.HolProg 64 :=
.seq stackBody154_397 stackBody154_414

def stackBody154_416 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 0

def stackBody154_417 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_418 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_419 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 22 2

def stackBody154_420 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.set Flapjack.Compiler.Backend.StackLang.StoreName.handler 22

def stackBody154_421 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackFree 3

def stackBody154_422 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 0 4

def stackBody154_423 : StackLang.HolProg 64 :=
.seq stackBody154_421 stackBody154_422

def stackBody154_424 : StackLang.HolProg 64 :=
.seq stackBody154_420 stackBody154_423

def stackBody154_425 : StackLang.HolProg 64 :=
.seq stackBody154_419 stackBody154_424

def stackBody154_426 : StackLang.HolProg 64 :=
.seq stackBody154_418 stackBody154_425

def stackBody154_427 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackLoad 0 4

def stackBody154_428 : StackLang.HolProg 64 :=
.call none (Sum.inl 5) none

def stackBody154_429 : StackLang.HolProg 64 :=
.seq stackBody154_427 stackBody154_428

def stackBody154_430 : StackLang.HolProg 64 :=
.call (some (stackBody154_426, 0, 154, 16)) (Sum.inl 152) (some (stackBody154_429, 154, 17))

def stackBody154_431 : StackLang.HolProg 64 :=
.seq stackBody154_417 stackBody154_430

def stackBody154_432 : StackLang.HolProg 64 :=
.seq stackBody154_416 stackBody154_431

def stackBody154_433 : StackLang.HolProg 64 :=
.seq stackBody154_415 stackBody154_432

def stackBody154_434 : StackLang.HolProg 64 :=
.seq stackBody154_396 stackBody154_433

def stackBody154_435 : StackLang.HolProg 64 :=
.seq stackBody154_393 stackBody154_434

def stackBody154_436 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.tick

def stackBody154_437 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 1 0#64)

def stackBody154_438 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody154_439 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackFree 5

def stackBody154_440 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.ret 0

def stackBody154_441 : StackLang.HolProg 64 :=
.seq stackBody154_439 stackBody154_440

def stackBody154_442 : StackLang.HolProg 64 :=
.seq stackBody154_438 stackBody154_441

def stackBody154_443 : StackLang.HolProg 64 :=
.seq stackBody154_437 stackBody154_442

def stackBody154_444 : StackLang.HolProg 64 :=
.seq stackBody154_436 stackBody154_443

def stackBody154_445 : StackLang.HolProg 64 :=
.seq stackBody154_435 stackBody154_444

def stackBody154_446 : StackLang.HolProg 64 :=
.seq stackBody154_392 stackBody154_445

def stackBody154_447 : StackLang.HolProg 64 :=
.seq stackBody154_391 stackBody154_446

def stackBody154_448 : StackLang.HolProg 64 :=
.seq stackBody154_390 stackBody154_447

def stackBody154_449 : StackLang.HolProg 64 :=
.seq stackBody154_389 stackBody154_448

def stackBody154_450 : StackLang.HolProg 64 :=
.seq stackBody154_388 stackBody154_449

def stackBody154_451 : StackLang.HolProg 64 :=
.seq stackBody154_387 stackBody154_450

def stackBody154_452 : StackLang.HolProg 64 :=
.seq stackBody154_386 stackBody154_451

def stackBody154_453 : StackLang.HolProg 64 :=
.seq stackBody154_343 stackBody154_452

def stackBody154_454 : StackLang.HolProg 64 :=
.seq stackBody154_342 stackBody154_453

def stackBody154_455 : StackLang.HolProg 64 :=
.seq stackBody154_341 stackBody154_454

def stackBody154_456 : StackLang.HolProg 64 :=
.seq stackBody154_340 stackBody154_455

def stackBody154_457 : StackLang.HolProg 64 :=
.seq stackBody154_339 stackBody154_456

def stackBody154_458 : StackLang.HolProg 64 :=
.seq stackBody154_338 stackBody154_457

def stackBody154_459 : StackLang.HolProg 64 :=
.seq stackBody154_337 stackBody154_458

def stackBody154_460 : StackLang.HolProg 64 :=
.seq stackBody154_336 stackBody154_459

def stackBody154_461 : StackLang.HolProg 64 :=
.seq stackBody154_335 stackBody154_460

def stackBody154_462 : StackLang.HolProg 64 :=
.seq stackBody154_334 stackBody154_461

def stackBody154_463 : StackLang.HolProg 64 :=
.seq stackBody154_291 stackBody154_462

def stackBody154_464 : StackLang.HolProg 64 :=
.seq stackBody154_290 stackBody154_463

def stackBody154_465 : StackLang.HolProg 64 :=
.seq stackBody154_289 stackBody154_464

def stackBody154_466 : StackLang.HolProg 64 :=
.seq stackBody154_288 stackBody154_465

def stackBody154_467 : StackLang.HolProg 64 :=
.seq stackBody154_287 stackBody154_466

def stackBody154_468 : StackLang.HolProg 64 :=
.seq stackBody154_286 stackBody154_467

def stackBody154_469 : StackLang.HolProg 64 :=
.seq stackBody154_285 stackBody154_468

def stackBody154_470 : StackLang.HolProg 64 :=
.seq stackBody154_284 stackBody154_469

def stackBody154_471 : StackLang.HolProg 64 :=
.seq stackBody154_283 stackBody154_470

def stackBody154_472 : StackLang.HolProg 64 :=
.seq stackBody154_282 stackBody154_471

def stackBody154_473 : StackLang.HolProg 64 :=
.seq stackBody154_281 stackBody154_472

def stackBody154_474 : StackLang.HolProg 64 :=
.seq stackBody154_280 stackBody154_473

def stackBody154_475 : StackLang.HolProg 64 :=
.seq stackBody154_279 stackBody154_474

def stackBody154_476 : StackLang.HolProg 64 :=
.seq stackBody154_278 stackBody154_475

def stackBody154_477 : StackLang.HolProg 64 :=
.seq stackBody154_235 stackBody154_476

def stackBody154_478 : StackLang.HolProg 64 :=
.seq stackBody154_234 stackBody154_477

def stackBody154_479 : StackLang.HolProg 64 :=
.seq stackBody154_233 stackBody154_478

def stackBody154_480 : StackLang.HolProg 64 :=
.seq stackBody154_232 stackBody154_479

def stackBody154_481 : StackLang.HolProg 64 :=
.seq stackBody154_231 stackBody154_480

def stackBody154_482 : StackLang.HolProg 64 :=
.seq stackBody154_230 stackBody154_481

def stackBody154_483 : StackLang.HolProg 64 :=
.seq stackBody154_229 stackBody154_482

def stackBody154_484 : StackLang.HolProg 64 :=
.seq stackBody154_228 stackBody154_483

def stackBody154_485 : StackLang.HolProg 64 :=
.seq stackBody154_227 stackBody154_484

def stackBody154_486 : StackLang.HolProg 64 :=
.seq stackBody154_184 stackBody154_485

def stackBody154_487 : StackLang.HolProg 64 :=
.seq stackBody154_183 stackBody154_486

def stackBody154_488 : StackLang.HolProg 64 :=
.seq stackBody154_182 stackBody154_487

def stackBody154_489 : StackLang.HolProg 64 :=
.seq stackBody154_181 stackBody154_488

def stackBody154_490 : StackLang.HolProg 64 :=
.seq stackBody154_180 stackBody154_489

def stackBody154_491 : StackLang.HolProg 64 :=
.seq stackBody154_179 stackBody154_490

def stackBody154_492 : StackLang.HolProg 64 :=
.seq stackBody154_178 stackBody154_491

def stackBody154_493 : StackLang.HolProg 64 :=
.seq stackBody154_177 stackBody154_492

def stackBody154_494 : StackLang.HolProg 64 :=
.seq stackBody154_176 stackBody154_493

def stackBody154_495 : StackLang.HolProg 64 :=
.seq stackBody154_175 stackBody154_494

def stackBody154_496 : StackLang.HolProg 64 :=
.seq stackBody154_132 stackBody154_495

def stackBody154_497 : StackLang.HolProg 64 :=
.seq stackBody154_131 stackBody154_496

def stackBody154_498 : StackLang.HolProg 64 :=
.seq stackBody154_130 stackBody154_497

def stackBody154_499 : StackLang.HolProg 64 :=
.seq stackBody154_129 stackBody154_498

def stackBody154_500 : StackLang.HolProg 64 :=
.seq stackBody154_128 stackBody154_499

def stackBody154_501 : StackLang.HolProg 64 :=
.seq stackBody154_127 stackBody154_500

def stackBody154_502 : StackLang.HolProg 64 :=
.seq stackBody154_126 stackBody154_501

def stackBody154_503 : StackLang.HolProg 64 :=
.seq stackBody154_125 stackBody154_502

def stackBody154_504 : StackLang.HolProg 64 :=
.seq stackBody154_124 stackBody154_503

def stackBody154_505 : StackLang.HolProg 64 :=
.seq stackBody154_123 stackBody154_504

def stackBody154_506 : StackLang.HolProg 64 :=
.seq stackBody154_72 stackBody154_505

def stackBody154_507 : StackLang.HolProg 64 :=
.seq stackBody154_71 stackBody154_506

def stackBody154_508 : StackLang.HolProg 64 :=
.seq stackBody154_70 stackBody154_507

def stackBody154_509 : StackLang.HolProg 64 :=
.seq stackBody154_69 stackBody154_508

def stackBody154_510 : StackLang.HolProg 64 :=
.seq stackBody154_68 stackBody154_509

def stackBody154_511 : StackLang.HolProg 64 :=
.seq stackBody154_67 stackBody154_510

def stackBody154_512 : StackLang.HolProg 64 :=
.seq stackBody154_66 stackBody154_511

def stackBody154_513 : StackLang.HolProg 64 :=
.seq stackBody154_65 stackBody154_512

def stackBody154_514 : StackLang.HolProg 64 :=
.seq stackBody154_64 stackBody154_513

def stackBody154_515 : StackLang.HolProg 64 :=
.seq stackBody154_63 stackBody154_514

def stackBody154_516 : StackLang.HolProg 64 :=
.seq stackBody154_12 stackBody154_515

def stackBody154_517 : StackLang.HolProg 64 :=
.seq stackBody154_5 stackBody154_516

def stackBody154_518 : StackLang.HolProg 64 :=
.seq stackBody154_4 stackBody154_517

def stackBody154_519 : StackLang.HolProg 64 :=
.seq stackBody154_3 stackBody154_518

def stackBody154_520 : StackLang.HolProg 64 :=
.seq stackBody154_2 stackBody154_519

def stackBody154_521 : StackLang.HolProg 64 :=
.seq stackBody154_1 stackBody154_520

def stackBody154_522 : StackLang.HolProg 64 :=
.seq stackBody154_0 stackBody154_521

def function154 (bitmapPrefix : AppList (BitVec 64)) : StackLang.HolProg 64 × Nat × (AppList (BitVec 64) × Nat) :=
(stackBody154_522, 5,
  Flapjack.AppList.append
    (Flapjack.AppList.append
      (Flapjack.AppList.append
        (Flapjack.AppList.append
          (Flapjack.AppList.append
            (Flapjack.AppList.append
              (Flapjack.AppList.append (Flapjack.AppList.append bitmapPrefix (Flapjack.AppList.list [16#64]))
                (Flapjack.AppList.list [16#64]))
              (Flapjack.AppList.list [16#64]))
            (Flapjack.AppList.list [16#64]))
          (Flapjack.AppList.list [16#64]))
        (Flapjack.AppList.list [16#64]))
      (Flapjack.AppList.list [16#64]))
    (Flapjack.AppList.list [16#64]),
  144)
theorem function154_eq (bitmapPrefix : AppList (BitVec 64)) : WordToStack.Native.compileProgNative riscvConfig false InitECandidate.Proofs.StackAnalysis.optimized154.2.2 InitECandidate.Proofs.StackAnalysis.optimized154.2.1 (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) (bitmapPrefix, 136) = function154 bitmapPrefix := by
  kernel_rfl
#print axioms function154_eq
end InitECandidate.Proofs.BackendStages
