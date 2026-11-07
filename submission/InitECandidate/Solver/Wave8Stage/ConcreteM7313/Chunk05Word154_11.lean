import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154Support

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154.Block11
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition Chunk05Stack151 Chunk05Word154

def p3810 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 16965 16961 (Flapjack.WordRegImm.imm 32#64)))

def p3811 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 16969 16965 (Flapjack.WordRegImm.imm 32#64)))

def p3812 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(16973, 16285)]

def p3813 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 16977 16973 (Flapjack.WordRegImm.imm 10#64)))

def p3814 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(16981, 16973)]

def p3815 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 16985 16981 (Flapjack.WordRegImm.imm 13#64)))

def p3816 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(16989, 16981)]

def p3817 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 16993 16989 (Flapjack.WordRegImm.imm 19#64)))

def p3818 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 16997 16985 (Flapjack.WordRegImm.reg 16993)))

def p3819 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17001 16977 (Flapjack.WordRegImm.reg 16997)))

def p3820 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17005, 16989)]

def p3821 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17009 17005 (Flapjack.WordRegImm.imm 15#64)))

def p3822 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17013, 17005)]

def p3823 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17017 17013 (Flapjack.WordRegImm.imm 17#64)))

def p3824 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17021 17009 (Flapjack.WordRegImm.reg 17017)))

def p3825 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17025 17001 (Flapjack.WordRegImm.reg 17021)))

def p3826 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17029, 14933)]

def p3827 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17033 17025 (Flapjack.WordRegImm.reg 17029)))

def p3828 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17037, 13701)]

def p3829 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17041 17037 (Flapjack.WordRegImm.imm 3#64)))

def p3830 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17045, 17037)]

def p3831 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17049 17045 (Flapjack.WordRegImm.imm 14#64)))

def p3832 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17053, 17045)]

def p3833 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17057 17053 (Flapjack.WordRegImm.imm 18#64)))

def p3834 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17061 17049 (Flapjack.WordRegImm.reg 17057)))

def p3835 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17065 17041 (Flapjack.WordRegImm.reg 17061)))

def p3836 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17069, 17053)]

def p3837 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17073 17069 (Flapjack.WordRegImm.imm 25#64)))

def p3838 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17077, 17069)]

def p3839 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17081 17077 (Flapjack.WordRegImm.imm 7#64)))

def p3840 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17085 17073 (Flapjack.WordRegImm.reg 17081)))

def p3841 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17089 17065 (Flapjack.WordRegImm.reg 17085)))

def p3842 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17093 17033 (Flapjack.WordRegImm.reg 17089)))

def p3843 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17097, 16661)]

def p3844 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17101 17093 (Flapjack.WordRegImm.reg 17097)))

def p3845 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17105 17101 (Flapjack.WordRegImm.imm 32#64)))

def p3846 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17109 17105 (Flapjack.WordRegImm.imm 32#64)))

def p3847 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17125, 16789), (17121, 16709), (17117, 17109)]

def p3848 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17129 17121 (Flapjack.WordRegImm.reg 17125)))

def p3849 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17133, 16845)]

def p3850 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 17137 17129 (Flapjack.WordRegImm.reg 17133)))

def p3851 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17141, 17121)]

def p3852 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17145 17137 (Flapjack.WordRegImm.reg 17141)))

def p3853 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17149 17117 (Flapjack.WordRegImm.reg 17145)))

def p3854 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17153, 17133)]

def p3855 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17157 17153 (Flapjack.WordRegImm.imm 7#64)))

def p3856 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17161, 17153)]

def p3857 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17165 17161 (Flapjack.WordRegImm.imm 25#64)))

def p3858 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17169 17157 (Flapjack.WordRegImm.reg 17165)))

def p3859 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17173, 17161)]

def p3860 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17177 17173 (Flapjack.WordRegImm.imm 21#64)))

def p3861 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17181, 17173)]

def p3862 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17185 17181 (Flapjack.WordRegImm.imm 11#64)))

def p3863 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17189 17177 (Flapjack.WordRegImm.reg 17185)))

def p3864 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17193 17169 (Flapjack.WordRegImm.reg 17189)))

def p3865 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17197, 17181)]

def p3866 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17201 17197 (Flapjack.WordRegImm.imm 26#64)))

def p3867 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17205, 17197)]

def p3868 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17209 17205 (Flapjack.WordRegImm.imm 6#64)))

def p3869 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17213 17201 (Flapjack.WordRegImm.reg 17209)))

def p3870 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17217 17193 (Flapjack.WordRegImm.reg 17213)))

def p3871 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17221 17149 (Flapjack.WordRegImm.reg 17217)))

def p3872 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17225, 16725)]

def p3873 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17229 17221 (Flapjack.WordRegImm.reg 17225)))

def p3874 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 17233 18446744072760349091#64)

def p3875 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17237 17229 (Flapjack.WordRegImm.reg 17233)))

def p3876 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17245, 16849), (17241, 17237)]

def p3877 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17249 17241 (Flapjack.WordRegImm.reg 17245)))

def p3878 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17253 17249 (Flapjack.WordRegImm.imm 32#64)))

def p3879 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17257 17253 (Flapjack.WordRegImm.imm 32#64)))

def p3880 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17281, 16969), (17277, 16937), (17273, 16869), (17265, 16877), (17261, 17257)]

def p3881 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17285 17277 (Flapjack.WordRegImm.reg 17281)))

def p3882 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 17289 17273 (Flapjack.WordRegImm.reg 17285)))

def p3883 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17293, 17277)]

def p3884 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17297 17289 (Flapjack.WordRegImm.reg 17293)))

def p3885 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17301, 17281)]

def p3886 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17305 17301 (Flapjack.WordRegImm.imm 10#64)))

def p3887 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17309, 17301)]

def p3888 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17313 17309 (Flapjack.WordRegImm.imm 22#64)))

def p3889 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17317 17305 (Flapjack.WordRegImm.reg 17313)))

def p3890 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17321, 17309)]

def p3891 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17325 17321 (Flapjack.WordRegImm.imm 19#64)))

def p3892 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17329, 17321)]

def p3893 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17333 17329 (Flapjack.WordRegImm.imm 13#64)))

def p3894 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17337 17325 (Flapjack.WordRegImm.reg 17333)))

def p3895 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17341 17317 (Flapjack.WordRegImm.reg 17337)))

def p3896 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17345, 17329)]

def p3897 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17349 17345 (Flapjack.WordRegImm.imm 30#64)))

def p3898 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17353, 17345)]

def p3899 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17357 17353 (Flapjack.WordRegImm.imm 2#64)))

def p3900 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17361 17349 (Flapjack.WordRegImm.reg 17357)))

def p3901 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17365 17341 (Flapjack.WordRegImm.reg 17361)))

def p3902 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17369 17297 (Flapjack.WordRegImm.reg 17365)))

def p3903 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17373, 17241)]

def p3904 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17377 17369 (Flapjack.WordRegImm.reg 17373)))

def p3905 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17381 17377 (Flapjack.WordRegImm.imm 32#64)))

def p3906 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17385 17381 (Flapjack.WordRegImm.imm 32#64)))

def p3907 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17389, 16701)]

def p3908 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17393 17389 (Flapjack.WordRegImm.imm 10#64)))

def p3909 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17397, 17389)]

def p3910 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17401 17397 (Flapjack.WordRegImm.imm 13#64)))

def p3911 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17405, 17397)]

def p3912 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17409 17405 (Flapjack.WordRegImm.imm 19#64)))

def p3913 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17413 17401 (Flapjack.WordRegImm.reg 17409)))

def p3914 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17417 17393 (Flapjack.WordRegImm.reg 17413)))

def p3915 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17421, 17405)]

def p3916 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17425 17421 (Flapjack.WordRegImm.imm 15#64)))

def p3917 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17429, 17421)]

def p3918 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17433 17429 (Flapjack.WordRegImm.imm 17#64)))

def p3919 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17437 17425 (Flapjack.WordRegImm.reg 17433)))

def p3920 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17441 17417 (Flapjack.WordRegImm.reg 17437)))

def p3921 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17445, 15349)]

def p3922 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17449 17441 (Flapjack.WordRegImm.reg 17445)))

def p3923 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17453, 14117)]

def p3924 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17457 17453 (Flapjack.WordRegImm.imm 3#64)))

def p3925 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17461, 17453)]

def p3926 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17465 17461 (Flapjack.WordRegImm.imm 14#64)))

def p3927 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17469, 17461)]

def p3928 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17473 17469 (Flapjack.WordRegImm.imm 18#64)))

def p3929 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17477 17465 (Flapjack.WordRegImm.reg 17473)))

def p3930 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17481 17457 (Flapjack.WordRegImm.reg 17477)))

def p3931 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17485, 17469)]

def p3932 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17489 17485 (Flapjack.WordRegImm.imm 25#64)))

def p3933 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17493, 17485)]

def p3934 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17497 17493 (Flapjack.WordRegImm.imm 7#64)))

def p3935 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17501 17489 (Flapjack.WordRegImm.reg 17497)))

def p3936 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17505 17481 (Flapjack.WordRegImm.reg 17501)))

def p3937 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17509 17449 (Flapjack.WordRegImm.reg 17505)))

def p3938 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17513, 17077)]

def p3939 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17517 17509 (Flapjack.WordRegImm.reg 17513)))

def p3940 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17521 17517 (Flapjack.WordRegImm.imm 32#64)))

def p3941 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17525 17521 (Flapjack.WordRegImm.imm 32#64)))

def p3942 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17541, 17205), (17537, 17125), (17533, 17525)]

def p3943 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17545 17537 (Flapjack.WordRegImm.reg 17541)))

def p3944 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17549, 17261)]

def p3945 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 17553 17545 (Flapjack.WordRegImm.reg 17549)))

def p3946 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17557, 17537)]

def p3947 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17561 17553 (Flapjack.WordRegImm.reg 17557)))

def p3948 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17565 17533 (Flapjack.WordRegImm.reg 17561)))

def p3949 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17569, 17549)]

def p3950 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17573 17569 (Flapjack.WordRegImm.imm 7#64)))

def p3951 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17577, 17569)]

def p3952 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17581 17577 (Flapjack.WordRegImm.imm 25#64)))

def p3953 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17585 17573 (Flapjack.WordRegImm.reg 17581)))

def p3954 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17589, 17577)]

def p3955 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17593 17589 (Flapjack.WordRegImm.imm 21#64)))

def p3956 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17597, 17589)]

def p3957 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17601 17597 (Flapjack.WordRegImm.imm 11#64)))

def p3958 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17605 17593 (Flapjack.WordRegImm.reg 17601)))

def p3959 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17609 17585 (Flapjack.WordRegImm.reg 17605)))

def p3960 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17613, 17597)]

def p3961 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17617 17613 (Flapjack.WordRegImm.imm 26#64)))

def p3962 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17621, 17613)]

def p3963 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17625 17621 (Flapjack.WordRegImm.imm 6#64)))

def p3964 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17629 17617 (Flapjack.WordRegImm.reg 17625)))

def p3965 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17633 17609 (Flapjack.WordRegImm.reg 17629)))

def p3966 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17637 17565 (Flapjack.WordRegImm.reg 17633)))

def p3967 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17641, 17141)]

def p3968 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17645 17637 (Flapjack.WordRegImm.reg 17641)))

def p3969 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 17649 18446744072930650137#64)

def p3970 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17653 17645 (Flapjack.WordRegImm.reg 17649)))

def p3971 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17661, 17265), (17657, 17653)]

def p3972 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17665 17657 (Flapjack.WordRegImm.reg 17661)))

def p3973 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17669 17665 (Flapjack.WordRegImm.imm 32#64)))

def p3974 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17673 17669 (Flapjack.WordRegImm.imm 32#64)))

def p3975 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17697, 17385), (17693, 17353), (17689, 17285), (17681, 17293), (17677, 17673)]

def p3976 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17701 17693 (Flapjack.WordRegImm.reg 17697)))

def p3977 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 17705 17689 (Flapjack.WordRegImm.reg 17701)))

def p3978 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17709, 17693)]

def p3979 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17713 17705 (Flapjack.WordRegImm.reg 17709)))

def p3980 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17717, 17697)]

def p3981 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17721 17717 (Flapjack.WordRegImm.imm 10#64)))

def p3982 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17725, 17717)]

def p3983 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17729 17725 (Flapjack.WordRegImm.imm 22#64)))

def p3984 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17733 17721 (Flapjack.WordRegImm.reg 17729)))

def p3985 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17737, 17725)]

def p3986 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17741 17737 (Flapjack.WordRegImm.imm 19#64)))

def p3987 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17745, 17737)]

def p3988 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17749 17745 (Flapjack.WordRegImm.imm 13#64)))

def p3989 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17753 17741 (Flapjack.WordRegImm.reg 17749)))

def p3990 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17757 17733 (Flapjack.WordRegImm.reg 17753)))

def p3991 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17761, 17745)]

def p3992 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17765 17761 (Flapjack.WordRegImm.imm 30#64)))

def p3993 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17769, 17761)]

def p3994 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17773 17769 (Flapjack.WordRegImm.imm 2#64)))

def p3995 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17777 17765 (Flapjack.WordRegImm.reg 17773)))

def p3996 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17781 17757 (Flapjack.WordRegImm.reg 17777)))

def p3997 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17785 17713 (Flapjack.WordRegImm.reg 17781)))

def p3998 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17789, 17657)]

def p3999 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17793 17785 (Flapjack.WordRegImm.reg 17789)))

def p4000 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17797 17793 (Flapjack.WordRegImm.imm 32#64)))

def p4001 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17801 17797 (Flapjack.WordRegImm.imm 32#64)))

def p4002 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17805, 17117)]

def p4003 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17809 17805 (Flapjack.WordRegImm.imm 10#64)))

def p4004 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17813, 17805)]

def p4005 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17817 17813 (Flapjack.WordRegImm.imm 13#64)))

def p4006 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17821, 17813)]

def p4007 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17825 17821 (Flapjack.WordRegImm.imm 19#64)))

def p4008 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17829 17817 (Flapjack.WordRegImm.reg 17825)))

def p4009 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17833 17809 (Flapjack.WordRegImm.reg 17829)))

def p4010 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17837, 17821)]

def p4011 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17841 17837 (Flapjack.WordRegImm.imm 15#64)))

def p4012 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17845, 17837)]

def p4013 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17849 17845 (Flapjack.WordRegImm.imm 17#64)))

def p4014 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17853 17841 (Flapjack.WordRegImm.reg 17849)))

def p4015 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17857 17833 (Flapjack.WordRegImm.reg 17853)))

def p4016 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17861, 15765)]

def p4017 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17865 17857 (Flapjack.WordRegImm.reg 17861)))

def p4018 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17869, 14533)]

def p4019 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17873 17869 (Flapjack.WordRegImm.imm 3#64)))

def p4020 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17877, 17869)]

def p4021 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17881 17877 (Flapjack.WordRegImm.imm 14#64)))

def p4022 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17885, 17877)]

def p4023 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17889 17885 (Flapjack.WordRegImm.imm 18#64)))

def p4024 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17893 17881 (Flapjack.WordRegImm.reg 17889)))

def p4025 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17897 17873 (Flapjack.WordRegImm.reg 17893)))

def p4026 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17901, 17885)]

def p4027 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17905 17901 (Flapjack.WordRegImm.imm 25#64)))

def p4028 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17909, 17901)]

def p4029 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17913 17909 (Flapjack.WordRegImm.imm 7#64)))

def p4030 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 17917 17905 (Flapjack.WordRegImm.reg 17913)))

def p4031 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17921 17897 (Flapjack.WordRegImm.reg 17917)))

def p4032 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17925 17865 (Flapjack.WordRegImm.reg 17921)))

def p4033 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17929, 17493)]

def p4034 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17933 17925 (Flapjack.WordRegImm.reg 17929)))

def p4035 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17937 17933 (Flapjack.WordRegImm.imm 32#64)))

def p4036 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17941 17937 (Flapjack.WordRegImm.imm 32#64)))

def p4037 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17957, 17621), (17953, 17541), (17949, 17941)]

def p4038 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17961 17953 (Flapjack.WordRegImm.reg 17957)))

def p4039 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17965, 17677)]

def p4040 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 17969 17961 (Flapjack.WordRegImm.reg 17965)))

def p4041 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17973, 17953)]

def p4042 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 17977 17969 (Flapjack.WordRegImm.reg 17973)))

def p4043 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 17981 17949 (Flapjack.WordRegImm.reg 17977)))

def p4044 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17985, 17965)]

def p4045 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 17989 17985 (Flapjack.WordRegImm.imm 7#64)))

def p4046 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(17993, 17985)]

def p4047 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 17997 17993 (Flapjack.WordRegImm.imm 25#64)))

def p4048 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18001 17989 (Flapjack.WordRegImm.reg 17997)))

def p4049 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18005, 17993)]

def p4050 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18009 18005 (Flapjack.WordRegImm.imm 21#64)))

def p4051 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18013, 18005)]

def p4052 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18017 18013 (Flapjack.WordRegImm.imm 11#64)))

def p4053 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18021 18009 (Flapjack.WordRegImm.reg 18017)))

def p4054 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18025 18001 (Flapjack.WordRegImm.reg 18021)))

def p4055 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18029, 18013)]

def p4056 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18033 18029 (Flapjack.WordRegImm.imm 26#64)))

def p4057 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18037, 18029)]

def p4058 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18041 18037 (Flapjack.WordRegImm.imm 6#64)))

def p4059 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18045 18033 (Flapjack.WordRegImm.reg 18041)))

def p4060 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18049 18025 (Flapjack.WordRegImm.reg 18045)))

def p4061 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18053 17981 (Flapjack.WordRegImm.reg 18049)))

def p4062 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18057, 17557)]

def p4063 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18061 18053 (Flapjack.WordRegImm.reg 18057)))

def p4064 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 18065 18446744073014937124#64)

def p4065 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18069 18061 (Flapjack.WordRegImm.reg 18065)))

def p4066 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18077, 17681), (18073, 18069)]

def p4067 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18081 18073 (Flapjack.WordRegImm.reg 18077)))

def p4068 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18085 18081 (Flapjack.WordRegImm.imm 32#64)))

def p4069 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18089 18085 (Flapjack.WordRegImm.imm 32#64)))

def p4070 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18113, 17801), (18109, 17769), (18105, 17701), (18097, 17709), (18093, 18089)]

def p4071 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18117 18109 (Flapjack.WordRegImm.reg 18113)))

def p4072 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 18121 18105 (Flapjack.WordRegImm.reg 18117)))

def p4073 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18125, 18109)]

def p4074 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18129 18121 (Flapjack.WordRegImm.reg 18125)))

def p4075 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18133, 18113)]

def p4076 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18137 18133 (Flapjack.WordRegImm.imm 10#64)))

def p4077 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18141, 18133)]

def p4078 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18145 18141 (Flapjack.WordRegImm.imm 22#64)))

def p4079 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18149 18137 (Flapjack.WordRegImm.reg 18145)))

def p4080 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18153, 18141)]

def p4081 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18157 18153 (Flapjack.WordRegImm.imm 19#64)))

def p4082 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18161, 18153)]

def p4083 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18165 18161 (Flapjack.WordRegImm.imm 13#64)))

def p4084 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18169 18157 (Flapjack.WordRegImm.reg 18165)))

def p4085 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18173 18149 (Flapjack.WordRegImm.reg 18169)))

def p4086 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18177, 18161)]

def p4087 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18181 18177 (Flapjack.WordRegImm.imm 30#64)))

def p4088 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18185, 18177)]

def p4089 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18189 18185 (Flapjack.WordRegImm.imm 2#64)))

def p4090 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18193 18181 (Flapjack.WordRegImm.reg 18189)))

def p4091 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18197 18173 (Flapjack.WordRegImm.reg 18193)))

def p4092 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18201 18129 (Flapjack.WordRegImm.reg 18197)))

def p4093 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18205, 18073)]

def p4094 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18209 18201 (Flapjack.WordRegImm.reg 18205)))

def p4095 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18213 18209 (Flapjack.WordRegImm.imm 32#64)))

def p4096 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18217 18213 (Flapjack.WordRegImm.imm 32#64)))

def p4097 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18221, 17533)]

def p4098 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18225 18221 (Flapjack.WordRegImm.imm 10#64)))

def p4099 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18229, 18221)]

def p4100 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18233 18229 (Flapjack.WordRegImm.imm 13#64)))

def p4101 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18237, 18229)]

def p4102 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18241 18237 (Flapjack.WordRegImm.imm 19#64)))

def p4103 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18245 18233 (Flapjack.WordRegImm.reg 18241)))

def p4104 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18249 18225 (Flapjack.WordRegImm.reg 18245)))

def p4105 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18253, 18237)]

def p4106 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18257 18253 (Flapjack.WordRegImm.imm 15#64)))

def p4107 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18261, 18253)]

def p4108 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18265 18261 (Flapjack.WordRegImm.imm 17#64)))

def p4109 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18269 18257 (Flapjack.WordRegImm.reg 18265)))

def p4110 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18273 18249 (Flapjack.WordRegImm.reg 18269)))

def p4111 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18277, 16181)]

def p4112 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18281 18273 (Flapjack.WordRegImm.reg 18277)))

def p4113 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18285, 14949)]

def p4114 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18289 18285 (Flapjack.WordRegImm.imm 3#64)))

def p4115 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18293, 18285)]

def p4116 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18297 18293 (Flapjack.WordRegImm.imm 14#64)))

def p4117 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18301, 18293)]

def p4118 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18305 18301 (Flapjack.WordRegImm.imm 18#64)))

def p4119 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18309 18297 (Flapjack.WordRegImm.reg 18305)))

def p4120 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18313 18289 (Flapjack.WordRegImm.reg 18309)))

def p4121 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18317, 18301)]

def p4122 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18321 18317 (Flapjack.WordRegImm.imm 25#64)))

def p4123 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18325, 18317)]

def p4124 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18329 18325 (Flapjack.WordRegImm.imm 7#64)))

def p4125 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18333 18321 (Flapjack.WordRegImm.reg 18329)))

def p4126 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18337 18313 (Flapjack.WordRegImm.reg 18333)))

def p4127 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18341 18281 (Flapjack.WordRegImm.reg 18337)))

def p4128 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18345, 17909)]

def p4129 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18349 18341 (Flapjack.WordRegImm.reg 18345)))

def p4130 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18353 18349 (Flapjack.WordRegImm.imm 32#64)))

def p4131 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18357 18353 (Flapjack.WordRegImm.imm 32#64)))

def p4132 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18373, 18037), (18369, 17957), (18365, 18357)]

def p4133 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18377 18369 (Flapjack.WordRegImm.reg 18373)))

def p4134 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18381, 18093)]

def p4135 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 18385 18377 (Flapjack.WordRegImm.reg 18381)))

def p4136 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18389, 18369)]

def p4137 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18393 18385 (Flapjack.WordRegImm.reg 18389)))

def p4138 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18397 18365 (Flapjack.WordRegImm.reg 18393)))

def p4139 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18401, 18381)]

def p4140 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18405 18401 (Flapjack.WordRegImm.imm 7#64)))

def p4141 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18409, 18401)]

def p4142 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18413 18409 (Flapjack.WordRegImm.imm 25#64)))

def p4143 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18417 18405 (Flapjack.WordRegImm.reg 18413)))

def p4144 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18421, 18409)]

def p4145 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18425 18421 (Flapjack.WordRegImm.imm 21#64)))

def p4146 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18429, 18421)]

def p4147 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18433 18429 (Flapjack.WordRegImm.imm 11#64)))

def p4148 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18437 18425 (Flapjack.WordRegImm.reg 18433)))

def p4149 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18441 18417 (Flapjack.WordRegImm.reg 18437)))

def p4150 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18445, 18429)]

def p4151 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18449 18445 (Flapjack.WordRegImm.imm 26#64)))

def p4152 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18453, 18445)]

def p4153 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18457 18453 (Flapjack.WordRegImm.imm 6#64)))

def p4154 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18461 18449 (Flapjack.WordRegImm.reg 18457)))

def p4155 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18465 18441 (Flapjack.WordRegImm.reg 18461)))

def p4156 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18469 18397 (Flapjack.WordRegImm.reg 18465)))

def p4157 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18473, 17973)]

def p4158 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18477 18469 (Flapjack.WordRegImm.reg 18473)))

def p4159 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 18481 18446744073509156229#64)

def p4160 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18485 18477 (Flapjack.WordRegImm.reg 18481)))

def p4161 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18493, 18097), (18489, 18485)]

def p4162 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18497 18489 (Flapjack.WordRegImm.reg 18493)))

def p4163 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18501 18497 (Flapjack.WordRegImm.imm 32#64)))

def p4164 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18505 18501 (Flapjack.WordRegImm.imm 32#64)))

def p4165 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18529, 18217), (18525, 18185), (18521, 18117), (18513, 18125), (18509, 18505)]

def p4166 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18533 18525 (Flapjack.WordRegImm.reg 18529)))

def p4167 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 18537 18521 (Flapjack.WordRegImm.reg 18533)))

def p4168 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18541, 18525)]

def p4169 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18545 18537 (Flapjack.WordRegImm.reg 18541)))

def p4170 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18549, 18529)]

def p4171 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18553 18549 (Flapjack.WordRegImm.imm 10#64)))

def p4172 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18557, 18549)]

def p4173 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18561 18557 (Flapjack.WordRegImm.imm 22#64)))

def p4174 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18565 18553 (Flapjack.WordRegImm.reg 18561)))

def p4175 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18569, 18557)]

def p4176 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18573 18569 (Flapjack.WordRegImm.imm 19#64)))

def p4177 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18577, 18569)]

def p4178 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18581 18577 (Flapjack.WordRegImm.imm 13#64)))

def p4179 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18585 18573 (Flapjack.WordRegImm.reg 18581)))

def p4180 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18589 18565 (Flapjack.WordRegImm.reg 18585)))

def p4181 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18593, 18577)]

def p4182 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18597 18593 (Flapjack.WordRegImm.imm 30#64)))

def p4183 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18601, 18593)]

def p4184 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18605 18601 (Flapjack.WordRegImm.imm 2#64)))

def p4185 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18609 18597 (Flapjack.WordRegImm.reg 18605)))

def p4186 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18613 18589 (Flapjack.WordRegImm.reg 18609)))

def p4187 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18617 18545 (Flapjack.WordRegImm.reg 18613)))

def p4188 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18621, 18489)]

def p4189 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18625 18617 (Flapjack.WordRegImm.reg 18621)))

def p4190 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18629 18625 (Flapjack.WordRegImm.imm 32#64)))

def p4191 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18633 18629 (Flapjack.WordRegImm.imm 32#64)))

def p4192 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18637, 17949)]

def p4193 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18641 18637 (Flapjack.WordRegImm.imm 10#64)))

def p4194 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18645, 18637)]

def p4195 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18649 18645 (Flapjack.WordRegImm.imm 13#64)))

def p4196 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18653, 18645)]

def p4197 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18657 18653 (Flapjack.WordRegImm.imm 19#64)))

def p4198 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18661 18649 (Flapjack.WordRegImm.reg 18657)))

def p4199 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18665 18641 (Flapjack.WordRegImm.reg 18661)))

def p4200 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18669, 18653)]

def p4201 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18673 18669 (Flapjack.WordRegImm.imm 15#64)))

def p4202 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18677, 18669)]

def p4203 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18681 18677 (Flapjack.WordRegImm.imm 17#64)))

def p4204 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18685 18673 (Flapjack.WordRegImm.reg 18681)))

def p4205 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18689 18665 (Flapjack.WordRegImm.reg 18685)))

def p4206 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18693, 16597)]

def p4207 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18697 18689 (Flapjack.WordRegImm.reg 18693)))

def p4208 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18701, 15365)]

def p4209 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18705 18701 (Flapjack.WordRegImm.imm 3#64)))

def p4210 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18709, 18701)]

def p4211 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18713 18709 (Flapjack.WordRegImm.imm 14#64)))

def p4212 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18717, 18709)]

def p4213 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18721 18717 (Flapjack.WordRegImm.imm 18#64)))

def p4214 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18725 18713 (Flapjack.WordRegImm.reg 18721)))

def p4215 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18729 18705 (Flapjack.WordRegImm.reg 18725)))

def p4216 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18733, 18717)]

def p4217 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18737 18733 (Flapjack.WordRegImm.imm 25#64)))

def p4218 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18741, 18733)]

def p4219 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18745 18741 (Flapjack.WordRegImm.imm 7#64)))

def p4220 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18749 18737 (Flapjack.WordRegImm.reg 18745)))

def p4221 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18753 18729 (Flapjack.WordRegImm.reg 18749)))

def p4222 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18757 18697 (Flapjack.WordRegImm.reg 18753)))

def p4223 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18761, 18325)]

def p4224 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18765 18757 (Flapjack.WordRegImm.reg 18761)))

def p4225 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18769 18765 (Flapjack.WordRegImm.imm 32#64)))

def p4226 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18773 18769 (Flapjack.WordRegImm.imm 32#64)))

def p4227 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18789, 18453), (18785, 18373), (18781, 18773)]

def p4228 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18793 18785 (Flapjack.WordRegImm.reg 18789)))

def p4229 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18797, 18509)]

def p4230 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 18801 18793 (Flapjack.WordRegImm.reg 18797)))

def p4231 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18805, 18785)]

def p4232 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18809 18801 (Flapjack.WordRegImm.reg 18805)))

def p4233 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18813 18781 (Flapjack.WordRegImm.reg 18809)))

def p4234 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18817, 18797)]

def p4235 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18821 18817 (Flapjack.WordRegImm.imm 7#64)))

def p4236 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18825, 18817)]

def p4237 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18829 18825 (Flapjack.WordRegImm.imm 25#64)))

def p4238 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18833 18821 (Flapjack.WordRegImm.reg 18829)))

def p4239 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18837, 18825)]

def p4240 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18841 18837 (Flapjack.WordRegImm.imm 21#64)))

def p4241 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18845, 18837)]

def p4242 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18849 18845 (Flapjack.WordRegImm.imm 11#64)))

def p4243 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18853 18841 (Flapjack.WordRegImm.reg 18849)))

def p4244 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18857 18833 (Flapjack.WordRegImm.reg 18853)))

def p4245 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18861, 18845)]

def p4246 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18865 18861 (Flapjack.WordRegImm.imm 26#64)))

def p4247 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18869, 18861)]

def p4248 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18873 18869 (Flapjack.WordRegImm.imm 6#64)))

def p4249 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18877 18865 (Flapjack.WordRegImm.reg 18873)))

def p4250 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18881 18857 (Flapjack.WordRegImm.reg 18877)))

def p4251 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18885 18813 (Flapjack.WordRegImm.reg 18881)))

def p4252 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18889, 18389)]

def p4253 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18893 18885 (Flapjack.WordRegImm.reg 18889)))

def p4254 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 18897 275423344#64)

def p4255 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18901 18893 (Flapjack.WordRegImm.reg 18897)))

def p4256 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18909, 18513), (18905, 18901)]

def p4257 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 18913 18905 (Flapjack.WordRegImm.reg 18909)))

def p4258 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18917 18913 (Flapjack.WordRegImm.imm 32#64)))

def p4259 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18921 18917 (Flapjack.WordRegImm.imm 32#64)))

def p4260 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18945, 18633), (18941, 18601), (18937, 18533), (18929, 18541), (18925, 18921)]

def p4261 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18949 18941 (Flapjack.WordRegImm.reg 18945)))

def p4262 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 18953 18937 (Flapjack.WordRegImm.reg 18949)))

def p4263 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18957, 18941)]

def p4264 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 18961 18953 (Flapjack.WordRegImm.reg 18957)))

def p4265 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18965, 18945)]

def p4266 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18969 18965 (Flapjack.WordRegImm.imm 10#64)))

def p4267 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18973, 18965)]

def p4268 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18977 18973 (Flapjack.WordRegImm.imm 22#64)))

def p4269 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 18981 18969 (Flapjack.WordRegImm.reg 18977)))

def p4270 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18985, 18973)]

def p4271 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 18989 18985 (Flapjack.WordRegImm.imm 19#64)))

def p4272 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(18993, 18985)]

def p4273 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 18997 18993 (Flapjack.WordRegImm.imm 13#64)))

def p4274 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 19001 18989 (Flapjack.WordRegImm.reg 18997)))

def p4275 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 19005 18981 (Flapjack.WordRegImm.reg 19001)))

def p4276 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19009, 18993)]

def p4277 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 19013 19009 (Flapjack.WordRegImm.imm 30#64)))

def p4278 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19017, 19009)]

def p4279 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 19021 19017 (Flapjack.WordRegImm.imm 2#64)))

def p4280 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 19025 19013 (Flapjack.WordRegImm.reg 19021)))

def p4281 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 19029 19005 (Flapjack.WordRegImm.reg 19025)))

def p4282 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 19033 18961 (Flapjack.WordRegImm.reg 19029)))

def p4283 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19037, 18905)]

def p4284 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 19041 19033 (Flapjack.WordRegImm.reg 19037)))

def p4285 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 19045 19041 (Flapjack.WordRegImm.imm 32#64)))

def p4286 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 19049 19045 (Flapjack.WordRegImm.imm 32#64)))

def p4287 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19053, 18365)]

def p4288 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 19057 19053 (Flapjack.WordRegImm.imm 10#64)))

def p4289 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19061, 19053)]

def p4290 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 19065 19061 (Flapjack.WordRegImm.imm 13#64)))

def p4291 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19069, 19061)]

def p4292 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 19073 19069 (Flapjack.WordRegImm.imm 19#64)))

def p4293 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 19077 19065 (Flapjack.WordRegImm.reg 19073)))

def p4294 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 19081 19057 (Flapjack.WordRegImm.reg 19077)))

def p4295 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19085, 19069)]

def p4296 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 19089 19085 (Flapjack.WordRegImm.imm 15#64)))

def p4297 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19093, 19085)]

def p4298 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 19097 19093 (Flapjack.WordRegImm.imm 17#64)))

def p4299 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 19101 19089 (Flapjack.WordRegImm.reg 19097)))

def p4300 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 19105 19081 (Flapjack.WordRegImm.reg 19101)))

def p4301 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19109, 17013)]

def p4302 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 19113 19105 (Flapjack.WordRegImm.reg 19109)))

def p4303 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19117, 15781)]

def p4304 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 19121 19117 (Flapjack.WordRegImm.imm 3#64)))

def p4305 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19125, 19117)]

def p4306 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 19129 19125 (Flapjack.WordRegImm.imm 14#64)))

def p4307 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(19133, 19125)]

def p4308 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 19137 19133 (Flapjack.WordRegImm.imm 18#64)))

def p4309 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 19141 19129 (Flapjack.WordRegImm.reg 19137)))

def parts : List (WordLangProgHOL (BitVec 64)) := [p3810, p3811, p3812, p3813, p3814, p3815, p3816, p3817, p3818, p3819, p3820, p3821, p3822, p3823, p3824, p3825, p3826, p3827, p3828, p3829, p3830, p3831, p3832, p3833, p3834, p3835, p3836, p3837, p3838, p3839, p3840, p3841, p3842, p3843, p3844, p3845, p3846, p3847, p3848, p3849, p3850, p3851, p3852, p3853, p3854, p3855, p3856, p3857, p3858, p3859, p3860, p3861, p3862, p3863, p3864, p3865, p3866, p3867, p3868, p3869, p3870, p3871, p3872, p3873, p3874, p3875, p3876, p3877, p3878, p3879, p3880, p3881, p3882, p3883, p3884, p3885, p3886, p3887, p3888, p3889, p3890, p3891, p3892, p3893, p3894, p3895, p3896, p3897, p3898, p3899, p3900, p3901, p3902, p3903, p3904, p3905, p3906, p3907, p3908, p3909, p3910, p3911, p3912, p3913, p3914, p3915, p3916, p3917, p3918, p3919, p3920, p3921, p3922, p3923, p3924, p3925, p3926, p3927, p3928, p3929, p3930, p3931, p3932, p3933, p3934, p3935, p3936, p3937, p3938, p3939, p3940, p3941, p3942, p3943, p3944, p3945, p3946, p3947, p3948, p3949, p3950, p3951, p3952, p3953, p3954, p3955, p3956, p3957, p3958, p3959, p3960, p3961, p3962, p3963, p3964, p3965, p3966, p3967, p3968, p3969, p3970, p3971, p3972, p3973, p3974, p3975, p3976, p3977, p3978, p3979, p3980, p3981, p3982, p3983, p3984, p3985, p3986, p3987, p3988, p3989, p3990, p3991, p3992, p3993, p3994, p3995, p3996, p3997, p3998, p3999, p4000, p4001, p4002, p4003, p4004, p4005, p4006, p4007, p4008, p4009, p4010, p4011, p4012, p4013, p4014, p4015, p4016, p4017, p4018, p4019, p4020, p4021, p4022, p4023, p4024, p4025, p4026, p4027, p4028, p4029, p4030, p4031, p4032, p4033, p4034, p4035, p4036, p4037, p4038, p4039, p4040, p4041, p4042, p4043, p4044, p4045, p4046, p4047, p4048, p4049, p4050, p4051, p4052, p4053, p4054, p4055, p4056, p4057, p4058, p4059, p4060, p4061, p4062, p4063, p4064, p4065, p4066, p4067, p4068, p4069, p4070, p4071, p4072, p4073, p4074, p4075, p4076, p4077, p4078, p4079, p4080, p4081, p4082, p4083, p4084, p4085, p4086, p4087, p4088, p4089, p4090, p4091, p4092, p4093, p4094, p4095, p4096, p4097, p4098, p4099, p4100, p4101, p4102, p4103, p4104, p4105, p4106, p4107, p4108, p4109, p4110, p4111, p4112, p4113, p4114, p4115, p4116, p4117, p4118, p4119, p4120, p4121, p4122, p4123, p4124, p4125, p4126, p4127, p4128, p4129, p4130, p4131, p4132, p4133, p4134, p4135, p4136, p4137, p4138, p4139, p4140, p4141, p4142, p4143, p4144, p4145, p4146, p4147, p4148, p4149, p4150, p4151, p4152, p4153, p4154, p4155, p4156, p4157, p4158, p4159, p4160, p4161, p4162, p4163, p4164, p4165, p4166, p4167, p4168, p4169, p4170, p4171, p4172, p4173, p4174, p4175, p4176, p4177, p4178, p4179, p4180, p4181, p4182, p4183, p4184, p4185, p4186, p4187, p4188, p4189, p4190, p4191, p4192, p4193, p4194, p4195, p4196, p4197, p4198, p4199, p4200, p4201, p4202, p4203, p4204, p4205, p4206, p4207, p4208, p4209, p4210, p4211, p4212, p4213, p4214, p4215, p4216, p4217, p4218, p4219, p4220, p4221, p4222, p4223, p4224, p4225, p4226, p4227, p4228, p4229, p4230, p4231, p4232, p4233, p4234, p4235, p4236, p4237, p4238, p4239, p4240, p4241, p4242, p4243, p4244, p4245, p4246, p4247, p4248, p4249, p4250, p4251, p4252, p4253, p4254, p4255, p4256, p4257, p4258, p4259, p4260, p4261, p4262, p4263, p4264, p4265, p4266, p4267, p4268, p4269, p4270, p4271, p4272, p4273, p4274, p4275, p4276, p4277, p4278, p4279, p4280, p4281, p4282, p4283, p4284, p4285, p4286, p4287, p4288, p4289, p4290, p4291, p4292, p4293, p4294, p4295, p4296, p4297, p4298, p4299, p4300, p4301, p4302, p4303, p4304, p4305, p4306, p4307, p4308, p4309]

wave8_kernel_reduce trees := parts.map (fun p => WordAlloc.getClashTree p [])
wave8_kernel_reduce colPs := parts.map (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)))
wave8_kernel_reduce stackOk := colPs.all (everyStackVarHOL stackPred)
wave8_kernel_reduce forcedOk := parts.all (fun p => (WordAlloc.getForced riscvConfig p []).all (forcedPred (oracle154.getD .ln)))
wave8_kernel_reduce progs := parts.map (transform oracle154)
wave8_kernel_reduce maxV := maxListProg progs
wave8_kernel_reduce comp := compList riscvConfig false (22, 13, 12) progs (.nil, 136)

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154.Block11
