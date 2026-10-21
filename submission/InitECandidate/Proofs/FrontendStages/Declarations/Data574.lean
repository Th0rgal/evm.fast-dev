import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify558
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body574_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_stop" []

def body574_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body574_2 : Prog (BitVec 64) :=
.seq body574_0 body574_1

def body574_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body574_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 0#64)) body574_2 body574_3

def body574_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_add" []

def body574_6 : Prog (BitVec 64) :=
.seq body574_5 body574_1

def body574_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 1#64)) body574_6 body574_3

def body574_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mul" []

def body574_9 : Prog (BitVec 64) :=
.seq body574_8 body574_1

def body574_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 2#64)) body574_9 body574_3

def body574_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sub" []

def body574_12 : Prog (BitVec 64) :=
.seq body574_11 body574_1

def body574_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 3#64)) body574_12 body574_3

def body574_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_div" []

def body574_15 : Prog (BitVec 64) :=
.seq body574_14 body574_1

def body574_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 4#64)) body574_15 body574_3

def body574_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sdiv" []

def body574_18 : Prog (BitVec 64) :=
.seq body574_17 body574_1

def body574_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 5#64)) body574_18 body574_3

def body574_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mod" []

def body574_21 : Prog (BitVec 64) :=
.seq body574_20 body574_1

def body574_22 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 6#64)) body574_21 body574_3

def body574_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_smod" []

def body574_24 : Prog (BitVec 64) :=
.seq body574_23 body574_1

def body574_25 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 7#64)) body574_24 body574_3

def body574_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_addmod" []

def body574_27 : Prog (BitVec 64) :=
.seq body574_26 body574_1

def body574_28 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 8#64)) body574_27 body574_3

def body574_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mulmod" []

def body574_30 : Prog (BitVec 64) :=
.seq body574_29 body574_1

def body574_31 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 9#64)) body574_30 body574_3

def body574_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_exp" []

def body574_33 : Prog (BitVec 64) :=
.seq body574_32 body574_1

def body574_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 10#64)) body574_33 body574_3

def body574_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_signextend" []

def body574_36 : Prog (BitVec 64) :=
.seq body574_35 body574_1

def body574_37 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 11#64)) body574_36 body574_3

def body574_38 : Prog (BitVec 64) :=
.seq body574_34 body574_37

def body574_39 : Prog (BitVec 64) :=
.seq body574_31 body574_38

def body574_40 : Prog (BitVec 64) :=
.seq body574_28 body574_39

def body574_41 : Prog (BitVec 64) :=
.seq body574_25 body574_40

def body574_42 : Prog (BitVec 64) :=
.seq body574_22 body574_41

def body574_43 : Prog (BitVec 64) :=
.seq body574_19 body574_42

def body574_44 : Prog (BitVec 64) :=
.seq body574_16 body574_43

def body574_45 : Prog (BitVec 64) :=
.seq body574_13 body574_44

def body574_46 : Prog (BitVec 64) :=
.seq body574_10 body574_45

def body574_47 : Prog (BitVec 64) :=
.seq body574_7 body574_46

def body574_48 : Prog (BitVec 64) :=
.seq body574_4 body574_47

def body574_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_lt" []

def body574_50 : Prog (BitVec 64) :=
.seq body574_49 body574_1

def body574_51 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 16#64)) body574_50 body574_3

def body574_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_gt" []

def body574_53 : Prog (BitVec 64) :=
.seq body574_52 body574_1

def body574_54 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 17#64)) body574_53 body574_3

def body574_55 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_slt" []

def body574_56 : Prog (BitVec 64) :=
.seq body574_55 body574_1

def body574_57 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 18#64)) body574_56 body574_3

def body574_58 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sgt" []

def body574_59 : Prog (BitVec 64) :=
.seq body574_58 body574_1

def body574_60 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 19#64)) body574_59 body574_3

def body574_61 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_eq" []

def body574_62 : Prog (BitVec 64) :=
.seq body574_61 body574_1

def body574_63 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 20#64)) body574_62 body574_3

def body574_64 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_iszero" []

def body574_65 : Prog (BitVec 64) :=
.seq body574_64 body574_1

def body574_66 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 21#64)) body574_65 body574_3

def body574_67 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_and" []

def body574_68 : Prog (BitVec 64) :=
.seq body574_67 body574_1

def body574_69 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 22#64)) body574_68 body574_3

def body574_70 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_or" []

def body574_71 : Prog (BitVec 64) :=
.seq body574_70 body574_1

def body574_72 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 23#64)) body574_71 body574_3

def body574_73 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_xor" []

def body574_74 : Prog (BitVec 64) :=
.seq body574_73 body574_1

def body574_75 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 24#64)) body574_74 body574_3

def body574_76 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_not" []

def body574_77 : Prog (BitVec 64) :=
.seq body574_76 body574_1

def body574_78 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 25#64)) body574_77 body574_3

def body574_79 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_byte" []

def body574_80 : Prog (BitVec 64) :=
.seq body574_79 body574_1

def body574_81 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 26#64)) body574_80 body574_3

def body574_82 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_shl" []

def body574_83 : Prog (BitVec 64) :=
.seq body574_82 body574_1

def body574_84 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 27#64)) body574_83 body574_3

def body574_85 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_shr" []

def body574_86 : Prog (BitVec 64) :=
.seq body574_85 body574_1

def body574_87 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 28#64)) body574_86 body574_3

def body574_88 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sar" []

def body574_89 : Prog (BitVec 64) :=
.seq body574_88 body574_1

def body574_90 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 29#64)) body574_89 body574_3

def body574_91 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_clz" []

def body574_92 : Prog (BitVec 64) :=
.seq body574_91 body574_1

def body574_93 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 30#64)) body574_92 body574_3

def body574_94 : Prog (BitVec 64) :=
.seq body574_90 body574_93

def body574_95 : Prog (BitVec 64) :=
.seq body574_87 body574_94

def body574_96 : Prog (BitVec 64) :=
.seq body574_84 body574_95

def body574_97 : Prog (BitVec 64) :=
.seq body574_81 body574_96

def body574_98 : Prog (BitVec 64) :=
.seq body574_78 body574_97

def body574_99 : Prog (BitVec 64) :=
.seq body574_75 body574_98

def body574_100 : Prog (BitVec 64) :=
.seq body574_72 body574_99

def body574_101 : Prog (BitVec 64) :=
.seq body574_69 body574_100

def body574_102 : Prog (BitVec 64) :=
.seq body574_66 body574_101

def body574_103 : Prog (BitVec 64) :=
.seq body574_63 body574_102

def body574_104 : Prog (BitVec 64) :=
.seq body574_60 body574_103

def body574_105 : Prog (BitVec 64) :=
.seq body574_57 body574_104

def body574_106 : Prog (BitVec 64) :=
.seq body574_54 body574_105

def body574_107 : Prog (BitVec 64) :=
.seq body574_51 body574_106

def body574_108 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 16#64)) body574_48 body574_107

def body574_109 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 5#64)

def body574_110 : Prog (BitVec 64) :=
.seq body574_108 body574_109

def body574_111 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 32#64)) body574_110 body574_3

def body574_112 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_keccak" []

def body574_113 : Prog (BitVec 64) :=
.seq body574_112 body574_1

def body574_114 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 32#64)) body574_113 body574_3

def body574_115 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_address" []

def body574_116 : Prog (BitVec 64) :=
.seq body574_115 body574_1

def body574_117 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 48#64)) body574_116 body574_3

def body574_118 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_balance" []

def body574_119 : Prog (BitVec 64) :=
.seq body574_118 body574_1

def body574_120 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 49#64)) body574_119 body574_3

def body574_121 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_origin" []

def body574_122 : Prog (BitVec 64) :=
.seq body574_121 body574_1

def body574_123 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 50#64)) body574_122 body574_3

def body574_124 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_caller" []

def body574_125 : Prog (BitVec 64) :=
.seq body574_124 body574_1

def body574_126 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 51#64)) body574_125 body574_3

def body574_127 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_callvalue" []

def body574_128 : Prog (BitVec 64) :=
.seq body574_127 body574_1

def body574_129 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 52#64)) body574_128 body574_3

def body574_130 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_calldataload" []

def body574_131 : Prog (BitVec 64) :=
.seq body574_130 body574_1

def body574_132 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 53#64)) body574_131 body574_3

def body574_133 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_calldatasize" []

def body574_134 : Prog (BitVec 64) :=
.seq body574_133 body574_1

def body574_135 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 54#64)) body574_134 body574_3

def body574_136 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_calldatacopy" []

def body574_137 : Prog (BitVec 64) :=
.seq body574_136 body574_1

def body574_138 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 55#64)) body574_137 body574_3

def body574_139 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_codesize" []

def body574_140 : Prog (BitVec 64) :=
.seq body574_139 body574_1

def body574_141 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 56#64)) body574_140 body574_3

def body574_142 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_codecopy" []

def body574_143 : Prog (BitVec 64) :=
.seq body574_142 body574_1

def body574_144 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 57#64)) body574_143 body574_3

def body574_145 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_gasprice" []

def body574_146 : Prog (BitVec 64) :=
.seq body574_145 body574_1

def body574_147 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 58#64)) body574_146 body574_3

def body574_148 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_extcodesize" []

def body574_149 : Prog (BitVec 64) :=
.seq body574_148 body574_1

def body574_150 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 59#64)) body574_149 body574_3

def body574_151 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_extcodecopy" []

def body574_152 : Prog (BitVec 64) :=
.seq body574_151 body574_1

def body574_153 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 60#64)) body574_152 body574_3

def body574_154 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_returndatasize" []

def body574_155 : Prog (BitVec 64) :=
.seq body574_154 body574_1

def body574_156 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 61#64)) body574_155 body574_3

def body574_157 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_returndatacopy" []

def body574_158 : Prog (BitVec 64) :=
.seq body574_157 body574_1

def body574_159 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 62#64)) body574_158 body574_3

def body574_160 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_extcodehash" []

def body574_161 : Prog (BitVec 64) :=
.seq body574_160 body574_1

def body574_162 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 63#64)) body574_161 body574_3

def body574_163 : Prog (BitVec 64) :=
.seq body574_159 body574_162

def body574_164 : Prog (BitVec 64) :=
.seq body574_156 body574_163

def body574_165 : Prog (BitVec 64) :=
.seq body574_153 body574_164

def body574_166 : Prog (BitVec 64) :=
.seq body574_150 body574_165

def body574_167 : Prog (BitVec 64) :=
.seq body574_147 body574_166

def body574_168 : Prog (BitVec 64) :=
.seq body574_144 body574_167

def body574_169 : Prog (BitVec 64) :=
.seq body574_141 body574_168

def body574_170 : Prog (BitVec 64) :=
.seq body574_138 body574_169

def body574_171 : Prog (BitVec 64) :=
.seq body574_135 body574_170

def body574_172 : Prog (BitVec 64) :=
.seq body574_132 body574_171

def body574_173 : Prog (BitVec 64) :=
.seq body574_129 body574_172

def body574_174 : Prog (BitVec 64) :=
.seq body574_126 body574_173

def body574_175 : Prog (BitVec 64) :=
.seq body574_123 body574_174

def body574_176 : Prog (BitVec 64) :=
.seq body574_120 body574_175

def body574_177 : Prog (BitVec 64) :=
.seq body574_117 body574_176

def body574_178 : Prog (BitVec 64) :=
.seq body574_114 body574_177

def body574_179 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_blockhash" []

def body574_180 : Prog (BitVec 64) :=
.seq body574_179 body574_1

def body574_181 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 64#64)) body574_180 body574_3

def body574_182 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_coinbase" []

def body574_183 : Prog (BitVec 64) :=
.seq body574_182 body574_1

def body574_184 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 65#64)) body574_183 body574_3

def body574_185 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_timestamp" []

def body574_186 : Prog (BitVec 64) :=
.seq body574_185 body574_1

def body574_187 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 66#64)) body574_186 body574_3

def body574_188 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_number" []

def body574_189 : Prog (BitVec 64) :=
.seq body574_188 body574_1

def body574_190 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 67#64)) body574_189 body574_3

def body574_191 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_prevrandao" []

def body574_192 : Prog (BitVec 64) :=
.seq body574_191 body574_1

def body574_193 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 68#64)) body574_192 body574_3

def body574_194 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_gaslimit" []

def body574_195 : Prog (BitVec 64) :=
.seq body574_194 body574_1

def body574_196 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 69#64)) body574_195 body574_3

def body574_197 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_chainid" []

def body574_198 : Prog (BitVec 64) :=
.seq body574_197 body574_1

def body574_199 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 70#64)) body574_198 body574_3

def body574_200 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_selfbalance" []

def body574_201 : Prog (BitVec 64) :=
.seq body574_200 body574_1

def body574_202 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 71#64)) body574_201 body574_3

def body574_203 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_basefee" []

def body574_204 : Prog (BitVec 64) :=
.seq body574_203 body574_1

def body574_205 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 72#64)) body574_204 body574_3

def body574_206 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_blobhash" []

def body574_207 : Prog (BitVec 64) :=
.seq body574_206 body574_1

def body574_208 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 73#64)) body574_207 body574_3

def body574_209 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_blobbasefee" []

def body574_210 : Prog (BitVec 64) :=
.seq body574_209 body574_1

def body574_211 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 74#64)) body574_210 body574_3

def body574_212 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_slotnum" []

def body574_213 : Prog (BitVec 64) :=
.seq body574_212 body574_1

def body574_214 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 75#64)) body574_213 body574_3

def body574_215 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_pop" []

def body574_216 : Prog (BitVec 64) :=
.seq body574_215 body574_1

def body574_217 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 80#64)) body574_216 body574_3

def body574_218 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mload" []

def body574_219 : Prog (BitVec 64) :=
.seq body574_218 body574_1

def body574_220 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 81#64)) body574_219 body574_3

def body574_221 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mstore" []

def body574_222 : Prog (BitVec 64) :=
.seq body574_221 body574_1

def body574_223 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 82#64)) body574_222 body574_3

def body574_224 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mstore8" []

def body574_225 : Prog (BitVec 64) :=
.seq body574_224 body574_1

def body574_226 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 83#64)) body574_225 body574_3

def body574_227 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sload" []

def body574_228 : Prog (BitVec 64) :=
.seq body574_227 body574_1

def body574_229 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 84#64)) body574_228 body574_3

def body574_230 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sstore" []

def body574_231 : Prog (BitVec 64) :=
.seq body574_230 body574_1

def body574_232 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 85#64)) body574_231 body574_3

def body574_233 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_jump" []

def body574_234 : Prog (BitVec 64) :=
.seq body574_233 body574_1

def body574_235 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 86#64)) body574_234 body574_3

def body574_236 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_jumpi" []

def body574_237 : Prog (BitVec 64) :=
.seq body574_236 body574_1

def body574_238 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 87#64)) body574_237 body574_3

def body574_239 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_pc" []

def body574_240 : Prog (BitVec 64) :=
.seq body574_239 body574_1

def body574_241 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 88#64)) body574_240 body574_3

def body574_242 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_msize" []

def body574_243 : Prog (BitVec 64) :=
.seq body574_242 body574_1

def body574_244 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 89#64)) body574_243 body574_3

def body574_245 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_gas" []

def body574_246 : Prog (BitVec 64) :=
.seq body574_245 body574_1

def body574_247 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 90#64)) body574_246 body574_3

def body574_248 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_jumpdest" []

def body574_249 : Prog (BitVec 64) :=
.seq body574_248 body574_1

def body574_250 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 91#64)) body574_249 body574_3

def body574_251 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_tload" []

def body574_252 : Prog (BitVec 64) :=
.seq body574_251 body574_1

def body574_253 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 92#64)) body574_252 body574_3

def body574_254 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_tstore" []

def body574_255 : Prog (BitVec 64) :=
.seq body574_254 body574_1

def body574_256 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 93#64)) body574_255 body574_3

def body574_257 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mcopy" []

def body574_258 : Prog (BitVec 64) :=
.seq body574_257 body574_1

def body574_259 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 94#64)) body574_258 body574_3

def body574_260 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_push" [Flapjack.Exp.const 0#64]

def body574_261 : Prog (BitVec 64) :=
.seq body574_260 body574_1

def body574_262 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 95#64)) body574_261 body574_3

def body574_263 : Prog (BitVec 64) :=
.seq body574_259 body574_262

def body574_264 : Prog (BitVec 64) :=
.seq body574_256 body574_263

def body574_265 : Prog (BitVec 64) :=
.seq body574_253 body574_264

def body574_266 : Prog (BitVec 64) :=
.seq body574_250 body574_265

def body574_267 : Prog (BitVec 64) :=
.seq body574_247 body574_266

def body574_268 : Prog (BitVec 64) :=
.seq body574_244 body574_267

def body574_269 : Prog (BitVec 64) :=
.seq body574_241 body574_268

def body574_270 : Prog (BitVec 64) :=
.seq body574_238 body574_269

def body574_271 : Prog (BitVec 64) :=
.seq body574_235 body574_270

def body574_272 : Prog (BitVec 64) :=
.seq body574_232 body574_271

def body574_273 : Prog (BitVec 64) :=
.seq body574_229 body574_272

def body574_274 : Prog (BitVec 64) :=
.seq body574_226 body574_273

def body574_275 : Prog (BitVec 64) :=
.seq body574_223 body574_274

def body574_276 : Prog (BitVec 64) :=
.seq body574_220 body574_275

def body574_277 : Prog (BitVec 64) :=
.seq body574_217 body574_276

def body574_278 : Prog (BitVec 64) :=
.seq body574_214 body574_277

def body574_279 : Prog (BitVec 64) :=
.seq body574_211 body574_278

def body574_280 : Prog (BitVec 64) :=
.seq body574_208 body574_279

def body574_281 : Prog (BitVec 64) :=
.seq body574_205 body574_280

def body574_282 : Prog (BitVec 64) :=
.seq body574_202 body574_281

def body574_283 : Prog (BitVec 64) :=
.seq body574_199 body574_282

def body574_284 : Prog (BitVec 64) :=
.seq body574_196 body574_283

def body574_285 : Prog (BitVec 64) :=
.seq body574_193 body574_284

def body574_286 : Prog (BitVec 64) :=
.seq body574_190 body574_285

def body574_287 : Prog (BitVec 64) :=
.seq body574_187 body574_286

def body574_288 : Prog (BitVec 64) :=
.seq body574_184 body574_287

def body574_289 : Prog (BitVec 64) :=
.seq body574_181 body574_288

def body574_290 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 64#64)) body574_178 body574_289

def body574_291 : Prog (BitVec 64) :=
.seq body574_290 body574_109

def body574_292 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 96#64)) body574_291 body574_3

def body574_293 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_push"
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "op", Flapjack.Exp.const 95#64]]

def body574_294 : Prog (BitVec 64) :=
.seq body574_293 body574_1

def body574_295 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 128#64)) body574_294 body574_3

def body574_296 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_dup"
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "op", Flapjack.Exp.const 128#64]]

def body574_297 : Prog (BitVec 64) :=
.seq body574_296 body574_1

def body574_298 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 144#64)) body574_297 body574_3

def body574_299 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_swap"
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "op", Flapjack.Exp.const 143#64]]

def body574_300 : Prog (BitVec 64) :=
.seq body574_299 body574_1

def body574_301 : Prog (BitVec 64) :=
.seq body574_298 body574_300

def body574_302 : Prog (BitVec 64) :=
.seq body574_295 body574_301

def body574_303 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 160#64)) body574_302 body574_3

def body574_304 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_log"
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "op", Flapjack.Exp.const 160#64]]

def body574_305 : Prog (BitVec 64) :=
.seq body574_304 body574_1

def body574_306 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 165#64)) body574_305 body574_3

def body574_307 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_dupn" []

def body574_308 : Prog (BitVec 64) :=
.seq body574_307 body574_1

def body574_309 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 230#64)) body574_308 body574_3

def body574_310 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_swapn" []

def body574_311 : Prog (BitVec 64) :=
.seq body574_310 body574_1

def body574_312 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 231#64)) body574_311 body574_3

def body574_313 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_exchange" []

def body574_314 : Prog (BitVec 64) :=
.seq body574_313 body574_1

def body574_315 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 232#64)) body574_314 body574_3

def body574_316 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_create" []

def body574_317 : Prog (BitVec 64) :=
.seq body574_316 body574_1

def body574_318 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 240#64)) body574_317 body574_3

def body574_319 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_call" []

def body574_320 : Prog (BitVec 64) :=
.seq body574_319 body574_1

def body574_321 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 241#64)) body574_320 body574_3

def body574_322 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_callcode" []

def body574_323 : Prog (BitVec 64) :=
.seq body574_322 body574_1

def body574_324 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 242#64)) body574_323 body574_3

def body574_325 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_return" []

def body574_326 : Prog (BitVec 64) :=
.seq body574_325 body574_1

def body574_327 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 243#64)) body574_326 body574_3

def body574_328 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_delegatecall" []

def body574_329 : Prog (BitVec 64) :=
.seq body574_328 body574_1

def body574_330 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 244#64)) body574_329 body574_3

def body574_331 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_create2" []

def body574_332 : Prog (BitVec 64) :=
.seq body574_331 body574_1

def body574_333 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 245#64)) body574_332 body574_3

def body574_334 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_staticcall" []

def body574_335 : Prog (BitVec 64) :=
.seq body574_334 body574_1

def body574_336 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 250#64)) body574_335 body574_3

def body574_337 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_revert" []

def body574_338 : Prog (BitVec 64) :=
.seq body574_337 body574_1

def body574_339 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 253#64)) body574_338 body574_3

def body574_340 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_selfdestruct" []

def body574_341 : Prog (BitVec 64) :=
.seq body574_340 body574_1

def body574_342 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 255#64)) body574_341 body574_3

def body574_343 : Prog (BitVec 64) :=
.seq body574_109 body574_1

def body574_344 : Prog (BitVec 64) :=
.seq body574_342 body574_343

def body574_345 : Prog (BitVec 64) :=
.seq body574_339 body574_344

def body574_346 : Prog (BitVec 64) :=
.seq body574_336 body574_345

def body574_347 : Prog (BitVec 64) :=
.seq body574_333 body574_346

def body574_348 : Prog (BitVec 64) :=
.seq body574_330 body574_347

def body574_349 : Prog (BitVec 64) :=
.seq body574_327 body574_348

def body574_350 : Prog (BitVec 64) :=
.seq body574_324 body574_349

def body574_351 : Prog (BitVec 64) :=
.seq body574_321 body574_350

def body574_352 : Prog (BitVec 64) :=
.seq body574_318 body574_351

def body574_353 : Prog (BitVec 64) :=
.seq body574_315 body574_352

def body574_354 : Prog (BitVec 64) :=
.seq body574_312 body574_353

def body574_355 : Prog (BitVec 64) :=
.seq body574_309 body574_354

def body574_356 : Prog (BitVec 64) :=
.seq body574_306 body574_355

def body574_357 : Prog (BitVec 64) :=
.seq body574_303 body574_356

def body574_358 : Prog (BitVec 64) :=
.seq body574_292 body574_357

def body574_359 : Prog (BitVec 64) :=
.seq body574_111 body574_358

def body574_360 : Prog (BitVec 64) :=
.seq body574_4 body574_7

def body574_361 : Prog (BitVec 64) :=
.seq body574_360 body574_10

def body574_362 : Prog (BitVec 64) :=
.seq body574_361 body574_13

def body574_363 : Prog (BitVec 64) :=
.seq body574_362 body574_16

def body574_364 : Prog (BitVec 64) :=
.seq body574_363 body574_19

def body574_365 : Prog (BitVec 64) :=
.seq body574_364 body574_22

def body574_366 : Prog (BitVec 64) :=
.seq body574_365 body574_25

def body574_367 : Prog (BitVec 64) :=
.seq body574_366 body574_28

def body574_368 : Prog (BitVec 64) :=
.seq body574_367 body574_31

def body574_369 : Prog (BitVec 64) :=
.seq body574_368 body574_34

def body574_370 : Prog (BitVec 64) :=
.seq body574_369 body574_37

def body574_371 : Prog (BitVec 64) :=
.seq body574_51 body574_54

def body574_372 : Prog (BitVec 64) :=
.seq body574_371 body574_57

def body574_373 : Prog (BitVec 64) :=
.seq body574_372 body574_60

def body574_374 : Prog (BitVec 64) :=
.seq body574_373 body574_63

def body574_375 : Prog (BitVec 64) :=
.seq body574_374 body574_66

def body574_376 : Prog (BitVec 64) :=
.seq body574_375 body574_69

def body574_377 : Prog (BitVec 64) :=
.seq body574_376 body574_72

def body574_378 : Prog (BitVec 64) :=
.seq body574_377 body574_75

def body574_379 : Prog (BitVec 64) :=
.seq body574_378 body574_78

def body574_380 : Prog (BitVec 64) :=
.seq body574_379 body574_81

def body574_381 : Prog (BitVec 64) :=
.seq body574_380 body574_84

def body574_382 : Prog (BitVec 64) :=
.seq body574_381 body574_87

def body574_383 : Prog (BitVec 64) :=
.seq body574_382 body574_90

def body574_384 : Prog (BitVec 64) :=
.seq body574_383 body574_93

def body574_385 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 16#64)) body574_370 body574_384

def body574_386 : Prog (BitVec 64) :=
.seq body574_385 body574_109

def body574_387 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 32#64)) body574_386 body574_3

def body574_388 : Prog (BitVec 64) :=
.seq body574_114 body574_117

def body574_389 : Prog (BitVec 64) :=
.seq body574_388 body574_120

def body574_390 : Prog (BitVec 64) :=
.seq body574_389 body574_123

def body574_391 : Prog (BitVec 64) :=
.seq body574_390 body574_126

def body574_392 : Prog (BitVec 64) :=
.seq body574_391 body574_129

def body574_393 : Prog (BitVec 64) :=
.seq body574_392 body574_132

def body574_394 : Prog (BitVec 64) :=
.seq body574_393 body574_135

def body574_395 : Prog (BitVec 64) :=
.seq body574_394 body574_138

def body574_396 : Prog (BitVec 64) :=
.seq body574_395 body574_141

def body574_397 : Prog (BitVec 64) :=
.seq body574_396 body574_144

def body574_398 : Prog (BitVec 64) :=
.seq body574_397 body574_147

def body574_399 : Prog (BitVec 64) :=
.seq body574_398 body574_150

def body574_400 : Prog (BitVec 64) :=
.seq body574_399 body574_153

def body574_401 : Prog (BitVec 64) :=
.seq body574_400 body574_156

def body574_402 : Prog (BitVec 64) :=
.seq body574_401 body574_159

def body574_403 : Prog (BitVec 64) :=
.seq body574_402 body574_162

def body574_404 : Prog (BitVec 64) :=
.seq body574_181 body574_184

def body574_405 : Prog (BitVec 64) :=
.seq body574_404 body574_187

def body574_406 : Prog (BitVec 64) :=
.seq body574_405 body574_190

def body574_407 : Prog (BitVec 64) :=
.seq body574_406 body574_193

def body574_408 : Prog (BitVec 64) :=
.seq body574_407 body574_196

def body574_409 : Prog (BitVec 64) :=
.seq body574_408 body574_199

def body574_410 : Prog (BitVec 64) :=
.seq body574_409 body574_202

def body574_411 : Prog (BitVec 64) :=
.seq body574_410 body574_205

def body574_412 : Prog (BitVec 64) :=
.seq body574_411 body574_208

def body574_413 : Prog (BitVec 64) :=
.seq body574_412 body574_211

def body574_414 : Prog (BitVec 64) :=
.seq body574_413 body574_214

def body574_415 : Prog (BitVec 64) :=
.seq body574_414 body574_217

def body574_416 : Prog (BitVec 64) :=
.seq body574_415 body574_220

def body574_417 : Prog (BitVec 64) :=
.seq body574_416 body574_223

def body574_418 : Prog (BitVec 64) :=
.seq body574_417 body574_226

def body574_419 : Prog (BitVec 64) :=
.seq body574_418 body574_229

def body574_420 : Prog (BitVec 64) :=
.seq body574_419 body574_232

def body574_421 : Prog (BitVec 64) :=
.seq body574_420 body574_235

def body574_422 : Prog (BitVec 64) :=
.seq body574_421 body574_238

def body574_423 : Prog (BitVec 64) :=
.seq body574_422 body574_241

def body574_424 : Prog (BitVec 64) :=
.seq body574_423 body574_244

def body574_425 : Prog (BitVec 64) :=
.seq body574_424 body574_247

def body574_426 : Prog (BitVec 64) :=
.seq body574_425 body574_250

def body574_427 : Prog (BitVec 64) :=
.seq body574_426 body574_253

def body574_428 : Prog (BitVec 64) :=
.seq body574_427 body574_256

def body574_429 : Prog (BitVec 64) :=
.seq body574_428 body574_259

def body574_430 : Prog (BitVec 64) :=
.seq body574_429 body574_262

def body574_431 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 64#64)) body574_403 body574_430

def body574_432 : Prog (BitVec 64) :=
.seq body574_431 body574_109

def body574_433 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 96#64)) body574_432 body574_3

def body574_434 : Prog (BitVec 64) :=
.seq body574_387 body574_433

def body574_435 : Prog (BitVec 64) :=
.seq body574_295 body574_298

def body574_436 : Prog (BitVec 64) :=
.seq body574_435 body574_299

def body574_437 : Prog (BitVec 64) :=
.seq body574_436 body574_1

def body574_438 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 160#64)) body574_437 body574_3

def body574_439 : Prog (BitVec 64) :=
.seq body574_434 body574_438

def body574_440 : Prog (BitVec 64) :=
.seq body574_439 body574_306

def body574_441 : Prog (BitVec 64) :=
.seq body574_440 body574_309

def body574_442 : Prog (BitVec 64) :=
.seq body574_441 body574_312

def body574_443 : Prog (BitVec 64) :=
.seq body574_442 body574_315

def body574_444 : Prog (BitVec 64) :=
.seq body574_443 body574_318

def body574_445 : Prog (BitVec 64) :=
.seq body574_444 body574_321

def body574_446 : Prog (BitVec 64) :=
.seq body574_445 body574_324

def body574_447 : Prog (BitVec 64) :=
.seq body574_446 body574_327

def body574_448 : Prog (BitVec 64) :=
.seq body574_447 body574_330

def body574_449 : Prog (BitVec 64) :=
.seq body574_448 body574_333

def body574_450 : Prog (BitVec 64) :=
.seq body574_449 body574_336

def body574_451 : Prog (BitVec 64) :=
.seq body574_450 body574_339

def body574_452 : Prog (BitVec 64) :=
.seq body574_451 body574_342

def body574_453 : Prog (BitVec 64) :=
.seq body574_452 body574_109

def body574_454 : Prog (BitVec 64) :=
.seq body574_453 body574_1

def originalData574 : Decl (BitVec 64) :=
.function { name := "op_dispatch", inline := false, exported := false, params := [("op", Flapjack.Shape.one)], body := body574_359, returnShape := (Flapjack.Shape.one) }
def simplifiedData574 : Decl (BitVec 64) :=
.function { name := "op_dispatch", inline := false, exported := false, params := [("op", Flapjack.Shape.one)], body := body574_454, returnShape := (Flapjack.Shape.one) }
def original574 := Pancake.PanLang.declToHOL originalData574
def simplified574 := Pancake.PanLang.declToHOL simplifiedData574
end InitECandidate.Proofs.FrontendStages.Declarations
