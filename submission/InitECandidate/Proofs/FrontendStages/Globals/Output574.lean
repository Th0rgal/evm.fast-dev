import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data574
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate554
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody574_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_stop" []

def globalBody574_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody574_2 : Prog (BitVec 64) :=
.seq globalBody574_0 globalBody574_1

def globalBody574_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody574_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 0#64)) globalBody574_2 globalBody574_3

def globalBody574_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_add" []

def globalBody574_6 : Prog (BitVec 64) :=
.seq globalBody574_5 globalBody574_1

def globalBody574_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 1#64)) globalBody574_6 globalBody574_3

def globalBody574_8 : Prog (BitVec 64) :=
.seq globalBody574_4 globalBody574_7

def globalBody574_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mul" []

def globalBody574_10 : Prog (BitVec 64) :=
.seq globalBody574_9 globalBody574_1

def globalBody574_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 2#64)) globalBody574_10 globalBody574_3

def globalBody574_12 : Prog (BitVec 64) :=
.seq globalBody574_8 globalBody574_11

def globalBody574_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sub" []

def globalBody574_14 : Prog (BitVec 64) :=
.seq globalBody574_13 globalBody574_1

def globalBody574_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 3#64)) globalBody574_14 globalBody574_3

def globalBody574_16 : Prog (BitVec 64) :=
.seq globalBody574_12 globalBody574_15

def globalBody574_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_div" []

def globalBody574_18 : Prog (BitVec 64) :=
.seq globalBody574_17 globalBody574_1

def globalBody574_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 4#64)) globalBody574_18 globalBody574_3

def globalBody574_20 : Prog (BitVec 64) :=
.seq globalBody574_16 globalBody574_19

def globalBody574_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sdiv" []

def globalBody574_22 : Prog (BitVec 64) :=
.seq globalBody574_21 globalBody574_1

def globalBody574_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 5#64)) globalBody574_22 globalBody574_3

def globalBody574_24 : Prog (BitVec 64) :=
.seq globalBody574_20 globalBody574_23

def globalBody574_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mod" []

def globalBody574_26 : Prog (BitVec 64) :=
.seq globalBody574_25 globalBody574_1

def globalBody574_27 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 6#64)) globalBody574_26 globalBody574_3

def globalBody574_28 : Prog (BitVec 64) :=
.seq globalBody574_24 globalBody574_27

def globalBody574_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_smod" []

def globalBody574_30 : Prog (BitVec 64) :=
.seq globalBody574_29 globalBody574_1

def globalBody574_31 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 7#64)) globalBody574_30 globalBody574_3

def globalBody574_32 : Prog (BitVec 64) :=
.seq globalBody574_28 globalBody574_31

def globalBody574_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_addmod" []

def globalBody574_34 : Prog (BitVec 64) :=
.seq globalBody574_33 globalBody574_1

def globalBody574_35 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 8#64)) globalBody574_34 globalBody574_3

def globalBody574_36 : Prog (BitVec 64) :=
.seq globalBody574_32 globalBody574_35

def globalBody574_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mulmod" []

def globalBody574_38 : Prog (BitVec 64) :=
.seq globalBody574_37 globalBody574_1

def globalBody574_39 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 9#64)) globalBody574_38 globalBody574_3

def globalBody574_40 : Prog (BitVec 64) :=
.seq globalBody574_36 globalBody574_39

def globalBody574_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_exp" []

def globalBody574_42 : Prog (BitVec 64) :=
.seq globalBody574_41 globalBody574_1

def globalBody574_43 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 10#64)) globalBody574_42 globalBody574_3

def globalBody574_44 : Prog (BitVec 64) :=
.seq globalBody574_40 globalBody574_43

def globalBody574_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_signextend" []

def globalBody574_46 : Prog (BitVec 64) :=
.seq globalBody574_45 globalBody574_1

def globalBody574_47 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 11#64)) globalBody574_46 globalBody574_3

def globalBody574_48 : Prog (BitVec 64) :=
.seq globalBody574_44 globalBody574_47

def globalBody574_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_lt" []

def globalBody574_50 : Prog (BitVec 64) :=
.seq globalBody574_49 globalBody574_1

def globalBody574_51 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 16#64)) globalBody574_50 globalBody574_3

def globalBody574_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_gt" []

def globalBody574_53 : Prog (BitVec 64) :=
.seq globalBody574_52 globalBody574_1

def globalBody574_54 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 17#64)) globalBody574_53 globalBody574_3

def globalBody574_55 : Prog (BitVec 64) :=
.seq globalBody574_51 globalBody574_54

def globalBody574_56 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_slt" []

def globalBody574_57 : Prog (BitVec 64) :=
.seq globalBody574_56 globalBody574_1

def globalBody574_58 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 18#64)) globalBody574_57 globalBody574_3

def globalBody574_59 : Prog (BitVec 64) :=
.seq globalBody574_55 globalBody574_58

def globalBody574_60 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sgt" []

def globalBody574_61 : Prog (BitVec 64) :=
.seq globalBody574_60 globalBody574_1

def globalBody574_62 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 19#64)) globalBody574_61 globalBody574_3

def globalBody574_63 : Prog (BitVec 64) :=
.seq globalBody574_59 globalBody574_62

def globalBody574_64 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_eq" []

def globalBody574_65 : Prog (BitVec 64) :=
.seq globalBody574_64 globalBody574_1

def globalBody574_66 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 20#64)) globalBody574_65 globalBody574_3

def globalBody574_67 : Prog (BitVec 64) :=
.seq globalBody574_63 globalBody574_66

def globalBody574_68 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_iszero" []

def globalBody574_69 : Prog (BitVec 64) :=
.seq globalBody574_68 globalBody574_1

def globalBody574_70 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 21#64)) globalBody574_69 globalBody574_3

def globalBody574_71 : Prog (BitVec 64) :=
.seq globalBody574_67 globalBody574_70

def globalBody574_72 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_and" []

def globalBody574_73 : Prog (BitVec 64) :=
.seq globalBody574_72 globalBody574_1

def globalBody574_74 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 22#64)) globalBody574_73 globalBody574_3

def globalBody574_75 : Prog (BitVec 64) :=
.seq globalBody574_71 globalBody574_74

def globalBody574_76 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_or" []

def globalBody574_77 : Prog (BitVec 64) :=
.seq globalBody574_76 globalBody574_1

def globalBody574_78 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 23#64)) globalBody574_77 globalBody574_3

def globalBody574_79 : Prog (BitVec 64) :=
.seq globalBody574_75 globalBody574_78

def globalBody574_80 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_xor" []

def globalBody574_81 : Prog (BitVec 64) :=
.seq globalBody574_80 globalBody574_1

def globalBody574_82 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 24#64)) globalBody574_81 globalBody574_3

def globalBody574_83 : Prog (BitVec 64) :=
.seq globalBody574_79 globalBody574_82

def globalBody574_84 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_not" []

def globalBody574_85 : Prog (BitVec 64) :=
.seq globalBody574_84 globalBody574_1

def globalBody574_86 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 25#64)) globalBody574_85 globalBody574_3

def globalBody574_87 : Prog (BitVec 64) :=
.seq globalBody574_83 globalBody574_86

def globalBody574_88 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_byte" []

def globalBody574_89 : Prog (BitVec 64) :=
.seq globalBody574_88 globalBody574_1

def globalBody574_90 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 26#64)) globalBody574_89 globalBody574_3

def globalBody574_91 : Prog (BitVec 64) :=
.seq globalBody574_87 globalBody574_90

def globalBody574_92 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_shl" []

def globalBody574_93 : Prog (BitVec 64) :=
.seq globalBody574_92 globalBody574_1

def globalBody574_94 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 27#64)) globalBody574_93 globalBody574_3

def globalBody574_95 : Prog (BitVec 64) :=
.seq globalBody574_91 globalBody574_94

def globalBody574_96 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_shr" []

def globalBody574_97 : Prog (BitVec 64) :=
.seq globalBody574_96 globalBody574_1

def globalBody574_98 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 28#64)) globalBody574_97 globalBody574_3

def globalBody574_99 : Prog (BitVec 64) :=
.seq globalBody574_95 globalBody574_98

def globalBody574_100 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sar" []

def globalBody574_101 : Prog (BitVec 64) :=
.seq globalBody574_100 globalBody574_1

def globalBody574_102 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 29#64)) globalBody574_101 globalBody574_3

def globalBody574_103 : Prog (BitVec 64) :=
.seq globalBody574_99 globalBody574_102

def globalBody574_104 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_clz" []

def globalBody574_105 : Prog (BitVec 64) :=
.seq globalBody574_104 globalBody574_1

def globalBody574_106 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 30#64)) globalBody574_105 globalBody574_3

def globalBody574_107 : Prog (BitVec 64) :=
.seq globalBody574_103 globalBody574_106

def globalBody574_108 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 16#64)) globalBody574_48 globalBody574_107

def globalBody574_109 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 5#64)

def globalBody574_110 : Prog (BitVec 64) :=
.seq globalBody574_108 globalBody574_109

def globalBody574_111 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 32#64)) globalBody574_110 globalBody574_3

def globalBody574_112 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_keccak" []

def globalBody574_113 : Prog (BitVec 64) :=
.seq globalBody574_112 globalBody574_1

def globalBody574_114 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 32#64)) globalBody574_113 globalBody574_3

def globalBody574_115 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_address" []

def globalBody574_116 : Prog (BitVec 64) :=
.seq globalBody574_115 globalBody574_1

def globalBody574_117 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 48#64)) globalBody574_116 globalBody574_3

def globalBody574_118 : Prog (BitVec 64) :=
.seq globalBody574_114 globalBody574_117

def globalBody574_119 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_balance" []

def globalBody574_120 : Prog (BitVec 64) :=
.seq globalBody574_119 globalBody574_1

def globalBody574_121 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 49#64)) globalBody574_120 globalBody574_3

def globalBody574_122 : Prog (BitVec 64) :=
.seq globalBody574_118 globalBody574_121

def globalBody574_123 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_origin" []

def globalBody574_124 : Prog (BitVec 64) :=
.seq globalBody574_123 globalBody574_1

def globalBody574_125 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 50#64)) globalBody574_124 globalBody574_3

def globalBody574_126 : Prog (BitVec 64) :=
.seq globalBody574_122 globalBody574_125

def globalBody574_127 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_caller" []

def globalBody574_128 : Prog (BitVec 64) :=
.seq globalBody574_127 globalBody574_1

def globalBody574_129 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 51#64)) globalBody574_128 globalBody574_3

def globalBody574_130 : Prog (BitVec 64) :=
.seq globalBody574_126 globalBody574_129

def globalBody574_131 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_callvalue" []

def globalBody574_132 : Prog (BitVec 64) :=
.seq globalBody574_131 globalBody574_1

def globalBody574_133 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 52#64)) globalBody574_132 globalBody574_3

def globalBody574_134 : Prog (BitVec 64) :=
.seq globalBody574_130 globalBody574_133

def globalBody574_135 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_calldataload" []

def globalBody574_136 : Prog (BitVec 64) :=
.seq globalBody574_135 globalBody574_1

def globalBody574_137 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 53#64)) globalBody574_136 globalBody574_3

def globalBody574_138 : Prog (BitVec 64) :=
.seq globalBody574_134 globalBody574_137

def globalBody574_139 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_calldatasize" []

def globalBody574_140 : Prog (BitVec 64) :=
.seq globalBody574_139 globalBody574_1

def globalBody574_141 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 54#64)) globalBody574_140 globalBody574_3

def globalBody574_142 : Prog (BitVec 64) :=
.seq globalBody574_138 globalBody574_141

def globalBody574_143 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_calldatacopy" []

def globalBody574_144 : Prog (BitVec 64) :=
.seq globalBody574_143 globalBody574_1

def globalBody574_145 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 55#64)) globalBody574_144 globalBody574_3

def globalBody574_146 : Prog (BitVec 64) :=
.seq globalBody574_142 globalBody574_145

def globalBody574_147 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_codesize" []

def globalBody574_148 : Prog (BitVec 64) :=
.seq globalBody574_147 globalBody574_1

def globalBody574_149 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 56#64)) globalBody574_148 globalBody574_3

def globalBody574_150 : Prog (BitVec 64) :=
.seq globalBody574_146 globalBody574_149

def globalBody574_151 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_codecopy" []

def globalBody574_152 : Prog (BitVec 64) :=
.seq globalBody574_151 globalBody574_1

def globalBody574_153 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 57#64)) globalBody574_152 globalBody574_3

def globalBody574_154 : Prog (BitVec 64) :=
.seq globalBody574_150 globalBody574_153

def globalBody574_155 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_gasprice" []

def globalBody574_156 : Prog (BitVec 64) :=
.seq globalBody574_155 globalBody574_1

def globalBody574_157 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 58#64)) globalBody574_156 globalBody574_3

def globalBody574_158 : Prog (BitVec 64) :=
.seq globalBody574_154 globalBody574_157

def globalBody574_159 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_extcodesize" []

def globalBody574_160 : Prog (BitVec 64) :=
.seq globalBody574_159 globalBody574_1

def globalBody574_161 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 59#64)) globalBody574_160 globalBody574_3

def globalBody574_162 : Prog (BitVec 64) :=
.seq globalBody574_158 globalBody574_161

def globalBody574_163 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_extcodecopy" []

def globalBody574_164 : Prog (BitVec 64) :=
.seq globalBody574_163 globalBody574_1

def globalBody574_165 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 60#64)) globalBody574_164 globalBody574_3

def globalBody574_166 : Prog (BitVec 64) :=
.seq globalBody574_162 globalBody574_165

def globalBody574_167 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_returndatasize" []

def globalBody574_168 : Prog (BitVec 64) :=
.seq globalBody574_167 globalBody574_1

def globalBody574_169 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 61#64)) globalBody574_168 globalBody574_3

def globalBody574_170 : Prog (BitVec 64) :=
.seq globalBody574_166 globalBody574_169

def globalBody574_171 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_returndatacopy" []

def globalBody574_172 : Prog (BitVec 64) :=
.seq globalBody574_171 globalBody574_1

def globalBody574_173 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 62#64)) globalBody574_172 globalBody574_3

def globalBody574_174 : Prog (BitVec 64) :=
.seq globalBody574_170 globalBody574_173

def globalBody574_175 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_extcodehash" []

def globalBody574_176 : Prog (BitVec 64) :=
.seq globalBody574_175 globalBody574_1

def globalBody574_177 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 63#64)) globalBody574_176 globalBody574_3

def globalBody574_178 : Prog (BitVec 64) :=
.seq globalBody574_174 globalBody574_177

def globalBody574_179 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_blockhash" []

def globalBody574_180 : Prog (BitVec 64) :=
.seq globalBody574_179 globalBody574_1

def globalBody574_181 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 64#64)) globalBody574_180 globalBody574_3

def globalBody574_182 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_coinbase" []

def globalBody574_183 : Prog (BitVec 64) :=
.seq globalBody574_182 globalBody574_1

def globalBody574_184 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 65#64)) globalBody574_183 globalBody574_3

def globalBody574_185 : Prog (BitVec 64) :=
.seq globalBody574_181 globalBody574_184

def globalBody574_186 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_timestamp" []

def globalBody574_187 : Prog (BitVec 64) :=
.seq globalBody574_186 globalBody574_1

def globalBody574_188 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 66#64)) globalBody574_187 globalBody574_3

def globalBody574_189 : Prog (BitVec 64) :=
.seq globalBody574_185 globalBody574_188

def globalBody574_190 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_number" []

def globalBody574_191 : Prog (BitVec 64) :=
.seq globalBody574_190 globalBody574_1

def globalBody574_192 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 67#64)) globalBody574_191 globalBody574_3

def globalBody574_193 : Prog (BitVec 64) :=
.seq globalBody574_189 globalBody574_192

def globalBody574_194 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_prevrandao" []

def globalBody574_195 : Prog (BitVec 64) :=
.seq globalBody574_194 globalBody574_1

def globalBody574_196 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 68#64)) globalBody574_195 globalBody574_3

def globalBody574_197 : Prog (BitVec 64) :=
.seq globalBody574_193 globalBody574_196

def globalBody574_198 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_gaslimit" []

def globalBody574_199 : Prog (BitVec 64) :=
.seq globalBody574_198 globalBody574_1

def globalBody574_200 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 69#64)) globalBody574_199 globalBody574_3

def globalBody574_201 : Prog (BitVec 64) :=
.seq globalBody574_197 globalBody574_200

def globalBody574_202 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_chainid" []

def globalBody574_203 : Prog (BitVec 64) :=
.seq globalBody574_202 globalBody574_1

def globalBody574_204 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 70#64)) globalBody574_203 globalBody574_3

def globalBody574_205 : Prog (BitVec 64) :=
.seq globalBody574_201 globalBody574_204

def globalBody574_206 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_selfbalance" []

def globalBody574_207 : Prog (BitVec 64) :=
.seq globalBody574_206 globalBody574_1

def globalBody574_208 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 71#64)) globalBody574_207 globalBody574_3

def globalBody574_209 : Prog (BitVec 64) :=
.seq globalBody574_205 globalBody574_208

def globalBody574_210 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_basefee" []

def globalBody574_211 : Prog (BitVec 64) :=
.seq globalBody574_210 globalBody574_1

def globalBody574_212 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 72#64)) globalBody574_211 globalBody574_3

def globalBody574_213 : Prog (BitVec 64) :=
.seq globalBody574_209 globalBody574_212

def globalBody574_214 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_blobhash" []

def globalBody574_215 : Prog (BitVec 64) :=
.seq globalBody574_214 globalBody574_1

def globalBody574_216 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 73#64)) globalBody574_215 globalBody574_3

def globalBody574_217 : Prog (BitVec 64) :=
.seq globalBody574_213 globalBody574_216

def globalBody574_218 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_blobbasefee" []

def globalBody574_219 : Prog (BitVec 64) :=
.seq globalBody574_218 globalBody574_1

def globalBody574_220 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 74#64)) globalBody574_219 globalBody574_3

def globalBody574_221 : Prog (BitVec 64) :=
.seq globalBody574_217 globalBody574_220

def globalBody574_222 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_slotnum" []

def globalBody574_223 : Prog (BitVec 64) :=
.seq globalBody574_222 globalBody574_1

def globalBody574_224 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 75#64)) globalBody574_223 globalBody574_3

def globalBody574_225 : Prog (BitVec 64) :=
.seq globalBody574_221 globalBody574_224

def globalBody574_226 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_pop" []

def globalBody574_227 : Prog (BitVec 64) :=
.seq globalBody574_226 globalBody574_1

def globalBody574_228 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 80#64)) globalBody574_227 globalBody574_3

def globalBody574_229 : Prog (BitVec 64) :=
.seq globalBody574_225 globalBody574_228

def globalBody574_230 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mload" []

def globalBody574_231 : Prog (BitVec 64) :=
.seq globalBody574_230 globalBody574_1

def globalBody574_232 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 81#64)) globalBody574_231 globalBody574_3

def globalBody574_233 : Prog (BitVec 64) :=
.seq globalBody574_229 globalBody574_232

def globalBody574_234 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mstore" []

def globalBody574_235 : Prog (BitVec 64) :=
.seq globalBody574_234 globalBody574_1

def globalBody574_236 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 82#64)) globalBody574_235 globalBody574_3

def globalBody574_237 : Prog (BitVec 64) :=
.seq globalBody574_233 globalBody574_236

def globalBody574_238 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mstore8" []

def globalBody574_239 : Prog (BitVec 64) :=
.seq globalBody574_238 globalBody574_1

def globalBody574_240 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 83#64)) globalBody574_239 globalBody574_3

def globalBody574_241 : Prog (BitVec 64) :=
.seq globalBody574_237 globalBody574_240

def globalBody574_242 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sload" []

def globalBody574_243 : Prog (BitVec 64) :=
.seq globalBody574_242 globalBody574_1

def globalBody574_244 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 84#64)) globalBody574_243 globalBody574_3

def globalBody574_245 : Prog (BitVec 64) :=
.seq globalBody574_241 globalBody574_244

def globalBody574_246 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_sstore" []

def globalBody574_247 : Prog (BitVec 64) :=
.seq globalBody574_246 globalBody574_1

def globalBody574_248 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 85#64)) globalBody574_247 globalBody574_3

def globalBody574_249 : Prog (BitVec 64) :=
.seq globalBody574_245 globalBody574_248

def globalBody574_250 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_jump" []

def globalBody574_251 : Prog (BitVec 64) :=
.seq globalBody574_250 globalBody574_1

def globalBody574_252 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 86#64)) globalBody574_251 globalBody574_3

def globalBody574_253 : Prog (BitVec 64) :=
.seq globalBody574_249 globalBody574_252

def globalBody574_254 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_jumpi" []

def globalBody574_255 : Prog (BitVec 64) :=
.seq globalBody574_254 globalBody574_1

def globalBody574_256 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 87#64)) globalBody574_255 globalBody574_3

def globalBody574_257 : Prog (BitVec 64) :=
.seq globalBody574_253 globalBody574_256

def globalBody574_258 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_pc" []

def globalBody574_259 : Prog (BitVec 64) :=
.seq globalBody574_258 globalBody574_1

def globalBody574_260 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 88#64)) globalBody574_259 globalBody574_3

def globalBody574_261 : Prog (BitVec 64) :=
.seq globalBody574_257 globalBody574_260

def globalBody574_262 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_msize" []

def globalBody574_263 : Prog (BitVec 64) :=
.seq globalBody574_262 globalBody574_1

def globalBody574_264 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 89#64)) globalBody574_263 globalBody574_3

def globalBody574_265 : Prog (BitVec 64) :=
.seq globalBody574_261 globalBody574_264

def globalBody574_266 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_gas" []

def globalBody574_267 : Prog (BitVec 64) :=
.seq globalBody574_266 globalBody574_1

def globalBody574_268 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 90#64)) globalBody574_267 globalBody574_3

def globalBody574_269 : Prog (BitVec 64) :=
.seq globalBody574_265 globalBody574_268

def globalBody574_270 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_jumpdest" []

def globalBody574_271 : Prog (BitVec 64) :=
.seq globalBody574_270 globalBody574_1

def globalBody574_272 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 91#64)) globalBody574_271 globalBody574_3

def globalBody574_273 : Prog (BitVec 64) :=
.seq globalBody574_269 globalBody574_272

def globalBody574_274 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_tload" []

def globalBody574_275 : Prog (BitVec 64) :=
.seq globalBody574_274 globalBody574_1

def globalBody574_276 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 92#64)) globalBody574_275 globalBody574_3

def globalBody574_277 : Prog (BitVec 64) :=
.seq globalBody574_273 globalBody574_276

def globalBody574_278 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_tstore" []

def globalBody574_279 : Prog (BitVec 64) :=
.seq globalBody574_278 globalBody574_1

def globalBody574_280 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 93#64)) globalBody574_279 globalBody574_3

def globalBody574_281 : Prog (BitVec 64) :=
.seq globalBody574_277 globalBody574_280

def globalBody574_282 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_mcopy" []

def globalBody574_283 : Prog (BitVec 64) :=
.seq globalBody574_282 globalBody574_1

def globalBody574_284 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 94#64)) globalBody574_283 globalBody574_3

def globalBody574_285 : Prog (BitVec 64) :=
.seq globalBody574_281 globalBody574_284

def globalBody574_286 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_push" [Flapjack.Exp.const 0#64]

def globalBody574_287 : Prog (BitVec 64) :=
.seq globalBody574_286 globalBody574_1

def globalBody574_288 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 95#64)) globalBody574_287 globalBody574_3

def globalBody574_289 : Prog (BitVec 64) :=
.seq globalBody574_285 globalBody574_288

def globalBody574_290 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 64#64)) globalBody574_178 globalBody574_289

def globalBody574_291 : Prog (BitVec 64) :=
.seq globalBody574_290 globalBody574_109

def globalBody574_292 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 96#64)) globalBody574_291 globalBody574_3

def globalBody574_293 : Prog (BitVec 64) :=
.seq globalBody574_111 globalBody574_292

def globalBody574_294 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_push"
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "op", Flapjack.Exp.const 95#64]]

def globalBody574_295 : Prog (BitVec 64) :=
.seq globalBody574_294 globalBody574_1

def globalBody574_296 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 128#64)) globalBody574_295 globalBody574_3

def globalBody574_297 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_dup"
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "op", Flapjack.Exp.const 128#64]]

def globalBody574_298 : Prog (BitVec 64) :=
.seq globalBody574_297 globalBody574_1

def globalBody574_299 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 144#64)) globalBody574_298 globalBody574_3

def globalBody574_300 : Prog (BitVec 64) :=
.seq globalBody574_296 globalBody574_299

def globalBody574_301 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_swap"
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "op", Flapjack.Exp.const 143#64]]

def globalBody574_302 : Prog (BitVec 64) :=
.seq globalBody574_300 globalBody574_301

def globalBody574_303 : Prog (BitVec 64) :=
.seq globalBody574_302 globalBody574_1

def globalBody574_304 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 160#64)) globalBody574_303 globalBody574_3

def globalBody574_305 : Prog (BitVec 64) :=
.seq globalBody574_293 globalBody574_304

def globalBody574_306 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_log"
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "op", Flapjack.Exp.const 160#64]]

def globalBody574_307 : Prog (BitVec 64) :=
.seq globalBody574_306 globalBody574_1

def globalBody574_308 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 165#64)) globalBody574_307 globalBody574_3

def globalBody574_309 : Prog (BitVec 64) :=
.seq globalBody574_305 globalBody574_308

def globalBody574_310 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_dupn" []

def globalBody574_311 : Prog (BitVec 64) :=
.seq globalBody574_310 globalBody574_1

def globalBody574_312 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 230#64)) globalBody574_311 globalBody574_3

def globalBody574_313 : Prog (BitVec 64) :=
.seq globalBody574_309 globalBody574_312

def globalBody574_314 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_swapn" []

def globalBody574_315 : Prog (BitVec 64) :=
.seq globalBody574_314 globalBody574_1

def globalBody574_316 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 231#64)) globalBody574_315 globalBody574_3

def globalBody574_317 : Prog (BitVec 64) :=
.seq globalBody574_313 globalBody574_316

def globalBody574_318 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_exchange" []

def globalBody574_319 : Prog (BitVec 64) :=
.seq globalBody574_318 globalBody574_1

def globalBody574_320 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 232#64)) globalBody574_319 globalBody574_3

def globalBody574_321 : Prog (BitVec 64) :=
.seq globalBody574_317 globalBody574_320

def globalBody574_322 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_create" []

def globalBody574_323 : Prog (BitVec 64) :=
.seq globalBody574_322 globalBody574_1

def globalBody574_324 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 240#64)) globalBody574_323 globalBody574_3

def globalBody574_325 : Prog (BitVec 64) :=
.seq globalBody574_321 globalBody574_324

def globalBody574_326 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_call" []

def globalBody574_327 : Prog (BitVec 64) :=
.seq globalBody574_326 globalBody574_1

def globalBody574_328 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 241#64)) globalBody574_327 globalBody574_3

def globalBody574_329 : Prog (BitVec 64) :=
.seq globalBody574_325 globalBody574_328

def globalBody574_330 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_callcode" []

def globalBody574_331 : Prog (BitVec 64) :=
.seq globalBody574_330 globalBody574_1

def globalBody574_332 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 242#64)) globalBody574_331 globalBody574_3

def globalBody574_333 : Prog (BitVec 64) :=
.seq globalBody574_329 globalBody574_332

def globalBody574_334 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_return" []

def globalBody574_335 : Prog (BitVec 64) :=
.seq globalBody574_334 globalBody574_1

def globalBody574_336 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 243#64)) globalBody574_335 globalBody574_3

def globalBody574_337 : Prog (BitVec 64) :=
.seq globalBody574_333 globalBody574_336

def globalBody574_338 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_delegatecall" []

def globalBody574_339 : Prog (BitVec 64) :=
.seq globalBody574_338 globalBody574_1

def globalBody574_340 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 244#64)) globalBody574_339 globalBody574_3

def globalBody574_341 : Prog (BitVec 64) :=
.seq globalBody574_337 globalBody574_340

def globalBody574_342 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_create2" []

def globalBody574_343 : Prog (BitVec 64) :=
.seq globalBody574_342 globalBody574_1

def globalBody574_344 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 245#64)) globalBody574_343 globalBody574_3

def globalBody574_345 : Prog (BitVec 64) :=
.seq globalBody574_341 globalBody574_344

def globalBody574_346 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_staticcall" []

def globalBody574_347 : Prog (BitVec 64) :=
.seq globalBody574_346 globalBody574_1

def globalBody574_348 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 250#64)) globalBody574_347 globalBody574_3

def globalBody574_349 : Prog (BitVec 64) :=
.seq globalBody574_345 globalBody574_348

def globalBody574_350 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_revert" []

def globalBody574_351 : Prog (BitVec 64) :=
.seq globalBody574_350 globalBody574_1

def globalBody574_352 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 253#64)) globalBody574_351 globalBody574_3

def globalBody574_353 : Prog (BitVec 64) :=
.seq globalBody574_349 globalBody574_352

def globalBody574_354 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "op_selfdestruct" []

def globalBody574_355 : Prog (BitVec 64) :=
.seq globalBody574_354 globalBody574_1

def globalBody574_356 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 255#64)) globalBody574_355 globalBody574_3

def globalBody574_357 : Prog (BitVec 64) :=
.seq globalBody574_353 globalBody574_356

def globalBody574_358 : Prog (BitVec 64) :=
.seq globalBody574_357 globalBody574_109

def globalBody574_359 : Prog (BitVec 64) :=
.seq globalBody574_358 globalBody574_1

def globalData574 : Decl (BitVec 64) :=
.function { name := "op_dispatch", inline := false, exported := false, params := [("op", Flapjack.Shape.one)], body := globalBody574_359, returnShape := (Flapjack.Shape.one) }
def globalOutput574 := Pancake.PanLang.declToHOL globalData574
end InitECandidate.Proofs.FrontendStages.Declarations
