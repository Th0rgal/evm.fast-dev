import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154Support

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154.Block01
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition Chunk05Stack151 Chunk05Word154

def p8810 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39149, 39137)]

def p8811 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39153 39149 (Flapjack.WordRegImm.imm 21#64)))

def p8812 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39157, 39149)]

def p8813 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39161 39157 (Flapjack.WordRegImm.imm 11#64)))

def p8814 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39165 39153 (Flapjack.WordRegImm.reg 39161)))

def p8815 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39169 39145 (Flapjack.WordRegImm.reg 39165)))

def p8816 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39173, 39157)]

def p8817 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39177 39173 (Flapjack.WordRegImm.imm 26#64)))

def p8818 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39181, 39173)]

def p8819 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39185 39181 (Flapjack.WordRegImm.imm 6#64)))

def p8820 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39189 39177 (Flapjack.WordRegImm.reg 39185)))

def p8821 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39193 39169 (Flapjack.WordRegImm.reg 39189)))

def p8822 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39197 39125 (Flapjack.WordRegImm.reg 39193)))

def p8823 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39201, 38857)]

def p8824 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39205 39197 (Flapjack.WordRegImm.reg 39201)))

def p8825 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 39209 184740145#64)

def p8826 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39213 39205 (Flapjack.WordRegImm.reg 39209)))

def p8827 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39221, 38977), (39217, 39213)]

def p8828 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39225 39217 (Flapjack.WordRegImm.reg 39221)))

def p8829 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39229 39225 (Flapjack.WordRegImm.imm 32#64)))

def p8830 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39233 39229 (Flapjack.WordRegImm.imm 32#64)))

def p8831 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39257, 39097), (39253, 39065), (39249, 38997), (39241, 39005), (39237, 39233)]

def p8832 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39261 39253 (Flapjack.WordRegImm.reg 39257)))

def p8833 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 39265 39249 (Flapjack.WordRegImm.reg 39261)))

def p8834 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39269, 39253)]

def p8835 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39273 39265 (Flapjack.WordRegImm.reg 39269)))

def p8836 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39277, 39257)]

def p8837 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39281 39277 (Flapjack.WordRegImm.imm 10#64)))

def p8838 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39285, 39277)]

def p8839 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39289 39285 (Flapjack.WordRegImm.imm 22#64)))

def p8840 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39293 39281 (Flapjack.WordRegImm.reg 39289)))

def p8841 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39297, 39285)]

def p8842 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39301 39297 (Flapjack.WordRegImm.imm 19#64)))

def p8843 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39305, 39297)]

def p8844 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39309 39305 (Flapjack.WordRegImm.imm 13#64)))

def p8845 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39313 39301 (Flapjack.WordRegImm.reg 39309)))

def p8846 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39317 39293 (Flapjack.WordRegImm.reg 39313)))

def p8847 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39321, 39305)]

def p8848 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39325 39321 (Flapjack.WordRegImm.imm 30#64)))

def p8849 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39329, 39321)]

def p8850 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39333 39329 (Flapjack.WordRegImm.imm 2#64)))

def p8851 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39337 39325 (Flapjack.WordRegImm.reg 39333)))

def p8852 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39341 39317 (Flapjack.WordRegImm.reg 39337)))

def p8853 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39345 39273 (Flapjack.WordRegImm.reg 39341)))

def p8854 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39349, 39217)]

def p8855 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39353 39345 (Flapjack.WordRegImm.reg 39349)))

def p8856 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39357 39353 (Flapjack.WordRegImm.imm 32#64)))

def p8857 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39361 39357 (Flapjack.WordRegImm.imm 32#64)))

def p8858 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39369, 39181), (39365, 39105)]

def p8859 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39373 39365 (Flapjack.WordRegImm.reg 39369)))

def p8860 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39377, 39237)]

def p8861 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 39381 39373 (Flapjack.WordRegImm.reg 39377)))

def p8862 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39385, 39365)]

def p8863 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39389 39381 (Flapjack.WordRegImm.reg 39385)))

def p8864 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39393, 39377)]

def p8865 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39397 39393 (Flapjack.WordRegImm.imm 7#64)))

def p8866 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39401, 39393)]

def p8867 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39405 39401 (Flapjack.WordRegImm.imm 25#64)))

def p8868 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39409 39397 (Flapjack.WordRegImm.reg 39405)))

def p8869 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39413, 39401)]

def p8870 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39417 39413 (Flapjack.WordRegImm.imm 21#64)))

def p8871 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39421, 39413)]

def p8872 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39425 39421 (Flapjack.WordRegImm.imm 11#64)))

def p8873 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39429 39417 (Flapjack.WordRegImm.reg 39425)))

def p8874 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39433 39409 (Flapjack.WordRegImm.reg 39429)))

def p8875 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39437, 39421)]

def p8876 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39441 39437 (Flapjack.WordRegImm.imm 26#64)))

def p8877 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39445, 39437)]

def p8878 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39449 39445 (Flapjack.WordRegImm.imm 6#64)))

def p8879 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39453 39441 (Flapjack.WordRegImm.reg 39449)))

def p8880 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39457 39433 (Flapjack.WordRegImm.reg 39453)))

def p8881 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39461 39389 (Flapjack.WordRegImm.reg 39457)))

def p8882 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39465, 39121)]

def p8883 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39469 39461 (Flapjack.WordRegImm.reg 39465)))

def p8884 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 39473 1875991719#64)

def p8885 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39477 39469 (Flapjack.WordRegImm.reg 39473)))

def p8886 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39485, 39241), (39481, 39477)]

def p8887 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39489 39481 (Flapjack.WordRegImm.reg 39485)))

def p8888 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39493 39489 (Flapjack.WordRegImm.imm 32#64)))

def p8889 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39497 39493 (Flapjack.WordRegImm.imm 32#64)))

def p8890 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39521, 39361), (39517, 39329), (39513, 39261), (39505, 39269), (39501, 39497)]

def p8891 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39525 39517 (Flapjack.WordRegImm.reg 39521)))

def p8892 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 39529 39513 (Flapjack.WordRegImm.reg 39525)))

def p8893 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39533, 39517)]

def p8894 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39537 39529 (Flapjack.WordRegImm.reg 39533)))

def p8895 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39541, 39521)]

def p8896 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39545 39541 (Flapjack.WordRegImm.imm 10#64)))

def p8897 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39549, 39541)]

def p8898 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39553 39549 (Flapjack.WordRegImm.imm 22#64)))

def p8899 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39557 39545 (Flapjack.WordRegImm.reg 39553)))

def p8900 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39561, 39549)]

def p8901 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39565 39561 (Flapjack.WordRegImm.imm 19#64)))

def p8902 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39569, 39561)]

def p8903 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39573 39569 (Flapjack.WordRegImm.imm 13#64)))

def p8904 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39577 39565 (Flapjack.WordRegImm.reg 39573)))

def p8905 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39581 39557 (Flapjack.WordRegImm.reg 39577)))

def p8906 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39585, 39569)]

def p8907 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39589 39585 (Flapjack.WordRegImm.imm 30#64)))

def p8908 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39593, 39585)]

def p8909 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39597 39593 (Flapjack.WordRegImm.imm 2#64)))

def p8910 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39601 39589 (Flapjack.WordRegImm.reg 39597)))

def p8911 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39605 39581 (Flapjack.WordRegImm.reg 39601)))

def p8912 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39609 39537 (Flapjack.WordRegImm.reg 39605)))

def p8913 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39613, 39481)]

def p8914 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39617 39609 (Flapjack.WordRegImm.reg 39613)))

def p8915 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39621 39617 (Flapjack.WordRegImm.imm 32#64)))

def p8916 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39625 39621 (Flapjack.WordRegImm.imm 32#64)))

def p8917 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39633, 39445), (39629, 39369)]

def p8918 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39637 39629 (Flapjack.WordRegImm.reg 39633)))

def p8919 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39641, 39501)]

def p8920 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 39645 39637 (Flapjack.WordRegImm.reg 39641)))

def p8921 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39649, 39629)]

def p8922 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39653 39645 (Flapjack.WordRegImm.reg 39649)))

def p8923 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39657, 39641)]

def p8924 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39661 39657 (Flapjack.WordRegImm.imm 7#64)))

def p8925 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39665, 39657)]

def p8926 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39669 39665 (Flapjack.WordRegImm.imm 25#64)))

def p8927 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39673 39661 (Flapjack.WordRegImm.reg 39669)))

def p8928 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39677, 39665)]

def p8929 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39681 39677 (Flapjack.WordRegImm.imm 21#64)))

def p8930 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39685, 39677)]

def p8931 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39689 39685 (Flapjack.WordRegImm.imm 11#64)))

def p8932 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39693 39681 (Flapjack.WordRegImm.reg 39689)))

def p8933 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39697 39673 (Flapjack.WordRegImm.reg 39693)))

def p8934 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39701, 39685)]

def p8935 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39705 39701 (Flapjack.WordRegImm.imm 26#64)))

def p8936 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39709, 39701)]

def p8937 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39713 39709 (Flapjack.WordRegImm.imm 6#64)))

def p8938 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39717 39705 (Flapjack.WordRegImm.reg 39713)))

def p8939 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39721 39697 (Flapjack.WordRegImm.reg 39717)))

def p8940 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39725 39653 (Flapjack.WordRegImm.reg 39721)))

def p8941 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39729, 39385)]

def p8942 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39733 39725 (Flapjack.WordRegImm.reg 39729)))

def p8943 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 39737 1377499850#64)

def p8944 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39741 39733 (Flapjack.WordRegImm.reg 39737)))

def p8945 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39749, 39505), (39745, 39741)]

def p8946 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39753 39745 (Flapjack.WordRegImm.reg 39749)))

def p8947 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39757 39753 (Flapjack.WordRegImm.imm 32#64)))

def p8948 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39761 39757 (Flapjack.WordRegImm.imm 32#64)))

def p8949 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39785, 39625), (39781, 39593), (39777, 39525), (39769, 39533), (39765, 39761)]

def p8950 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39789 39781 (Flapjack.WordRegImm.reg 39785)))

def p8951 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 39793 39777 (Flapjack.WordRegImm.reg 39789)))

def p8952 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39797, 39781)]

def p8953 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39801 39793 (Flapjack.WordRegImm.reg 39797)))

def p8954 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39805, 39785)]

def p8955 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39809 39805 (Flapjack.WordRegImm.imm 10#64)))

def p8956 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39813, 39805)]

def p8957 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39817 39813 (Flapjack.WordRegImm.imm 22#64)))

def p8958 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39821 39809 (Flapjack.WordRegImm.reg 39817)))

def p8959 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39825, 39813)]

def p8960 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39829 39825 (Flapjack.WordRegImm.imm 19#64)))

def p8961 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39833, 39825)]

def p8962 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39837 39833 (Flapjack.WordRegImm.imm 13#64)))

def p8963 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39841 39829 (Flapjack.WordRegImm.reg 39837)))

def p8964 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39845 39821 (Flapjack.WordRegImm.reg 39841)))

def p8965 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39849, 39833)]

def p8966 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39853 39849 (Flapjack.WordRegImm.imm 30#64)))

def p8967 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39857, 39849)]

def p8968 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39861 39857 (Flapjack.WordRegImm.imm 2#64)))

def p8969 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39865 39853 (Flapjack.WordRegImm.reg 39861)))

def p8970 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39869 39845 (Flapjack.WordRegImm.reg 39865)))

def p8971 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39873 39801 (Flapjack.WordRegImm.reg 39869)))

def p8972 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39877, 39745)]

def p8973 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39881 39873 (Flapjack.WordRegImm.reg 39877)))

def p8974 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39885 39881 (Flapjack.WordRegImm.imm 32#64)))

def p8975 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39889 39885 (Flapjack.WordRegImm.imm 32#64)))

def p8976 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39897, 39709), (39893, 39633)]

def p8977 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39901 39893 (Flapjack.WordRegImm.reg 39897)))

def p8978 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39905, 39765)]

def p8979 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 39909 39901 (Flapjack.WordRegImm.reg 39905)))

def p8980 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39913, 39893)]

def p8981 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39917 39909 (Flapjack.WordRegImm.reg 39913)))

def p8982 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39921, 39905)]

def p8983 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39925 39921 (Flapjack.WordRegImm.imm 7#64)))

def p8984 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39929, 39921)]

def p8985 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39933 39929 (Flapjack.WordRegImm.imm 25#64)))

def p8986 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39937 39925 (Flapjack.WordRegImm.reg 39933)))

def p8987 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39941, 39929)]

def p8988 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39945 39941 (Flapjack.WordRegImm.imm 21#64)))

def p8989 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39949, 39941)]

def p8990 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39953 39949 (Flapjack.WordRegImm.imm 11#64)))

def p8991 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39957 39945 (Flapjack.WordRegImm.reg 39953)))

def p8992 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39961 39937 (Flapjack.WordRegImm.reg 39957)))

def p8993 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39965, 39949)]

def p8994 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39969 39965 (Flapjack.WordRegImm.imm 26#64)))

def p8995 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39973, 39965)]

def p8996 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39977 39973 (Flapjack.WordRegImm.imm 6#64)))

def p8997 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39981 39969 (Flapjack.WordRegImm.reg 39977)))

def p8998 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39985 39961 (Flapjack.WordRegImm.reg 39981)))

def p8999 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39989 39917 (Flapjack.WordRegImm.reg 39985)))

def p9000 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39993, 39649)]

def p9001 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39997 39989 (Flapjack.WordRegImm.reg 39993)))

def p9002 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 40001 825459761#64)

def p9003 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40005 39997 (Flapjack.WordRegImm.reg 40001)))

def p9004 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40013, 39769), (40009, 40005)]

def p9005 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40017 40009 (Flapjack.WordRegImm.reg 40013)))

def p9006 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40021 40017 (Flapjack.WordRegImm.imm 32#64)))

def p9007 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40025 40021 (Flapjack.WordRegImm.imm 32#64)))

def p9008 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40049, 39889), (40045, 39857), (40041, 39789), (40033, 39797), (40029, 40025)]

def p9009 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40053 40045 (Flapjack.WordRegImm.reg 40049)))

def p9010 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 40057 40041 (Flapjack.WordRegImm.reg 40053)))

def p9011 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40061, 40045)]

def p9012 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40065 40057 (Flapjack.WordRegImm.reg 40061)))

def p9013 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40069, 40049)]

def p9014 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40073 40069 (Flapjack.WordRegImm.imm 10#64)))

def p9015 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40077, 40069)]

def p9016 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40081 40077 (Flapjack.WordRegImm.imm 22#64)))

def p9017 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40085 40073 (Flapjack.WordRegImm.reg 40081)))

def p9018 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40089, 40077)]

def p9019 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40093 40089 (Flapjack.WordRegImm.imm 19#64)))

def p9020 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40097, 40089)]

def p9021 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40101 40097 (Flapjack.WordRegImm.imm 13#64)))

def p9022 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40105 40093 (Flapjack.WordRegImm.reg 40101)))

def p9023 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40109 40085 (Flapjack.WordRegImm.reg 40105)))

def p9024 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40113, 40097)]

def p9025 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40117 40113 (Flapjack.WordRegImm.imm 30#64)))

def p9026 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40121, 40113)]

def p9027 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40125 40121 (Flapjack.WordRegImm.imm 2#64)))

def p9028 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40129 40117 (Flapjack.WordRegImm.reg 40125)))

def p9029 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40133 40109 (Flapjack.WordRegImm.reg 40129)))

def p9030 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40137 40065 (Flapjack.WordRegImm.reg 40133)))

def p9031 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40141, 40009)]

def p9032 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40145 40137 (Flapjack.WordRegImm.reg 40141)))

def p9033 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40149 40145 (Flapjack.WordRegImm.imm 32#64)))

def p9034 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40153 40149 (Flapjack.WordRegImm.imm 32#64)))

def p9035 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40161, 39973), (40157, 39897)]

def p9036 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40165 40157 (Flapjack.WordRegImm.reg 40161)))

def p9037 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40169, 40029)]

def p9038 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 40173 40165 (Flapjack.WordRegImm.reg 40169)))

def p9039 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40177, 40157)]

def p9040 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40181 40173 (Flapjack.WordRegImm.reg 40177)))

def p9041 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40185, 40169)]

def p9042 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40189 40185 (Flapjack.WordRegImm.imm 7#64)))

def p9043 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40193, 40185)]

def p9044 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40197 40193 (Flapjack.WordRegImm.imm 25#64)))

def p9045 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40201 40189 (Flapjack.WordRegImm.reg 40197)))

def p9046 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40205, 40193)]

def p9047 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40209 40205 (Flapjack.WordRegImm.imm 21#64)))

def p9048 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40213, 40205)]

def p9049 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40217 40213 (Flapjack.WordRegImm.imm 11#64)))

def p9050 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40221 40209 (Flapjack.WordRegImm.reg 40217)))

def p9051 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40225 40201 (Flapjack.WordRegImm.reg 40221)))

def p9052 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40229, 40213)]

def p9053 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40233 40229 (Flapjack.WordRegImm.imm 26#64)))

def p9054 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40237, 40229)]

def p9055 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40241 40237 (Flapjack.WordRegImm.imm 6#64)))

def p9056 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40245 40233 (Flapjack.WordRegImm.reg 40241)))

def p9057 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40249 40225 (Flapjack.WordRegImm.reg 40245)))

def p9058 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40253 40181 (Flapjack.WordRegImm.reg 40249)))

def p9059 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40257, 39913)]

def p9060 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40261 40253 (Flapjack.WordRegImm.reg 40257)))

def p9061 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 40265 1859394197#64)

def p9062 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40269 40261 (Flapjack.WordRegImm.reg 40265)))

def p9063 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40277, 40033), (40273, 40269)]

def p9064 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40281 40273 (Flapjack.WordRegImm.reg 40277)))

def p9065 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40285 40281 (Flapjack.WordRegImm.imm 32#64)))

def p9066 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40289 40285 (Flapjack.WordRegImm.imm 32#64)))

def p9067 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40313, 40153), (40309, 40121), (40305, 40053), (40297, 40061), (40293, 40289)]

def p9068 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40317 40309 (Flapjack.WordRegImm.reg 40313)))

def p9069 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 40321 40305 (Flapjack.WordRegImm.reg 40317)))

def p9070 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40325, 40309)]

def p9071 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40329 40321 (Flapjack.WordRegImm.reg 40325)))

def p9072 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40333, 40313)]

def p9073 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40337 40333 (Flapjack.WordRegImm.imm 10#64)))

def p9074 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40341, 40333)]

def p9075 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40345 40341 (Flapjack.WordRegImm.imm 22#64)))

def p9076 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40349 40337 (Flapjack.WordRegImm.reg 40345)))

def p9077 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40353, 40341)]

def p9078 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40357 40353 (Flapjack.WordRegImm.imm 19#64)))

def p9079 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40361, 40353)]

def p9080 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40365 40361 (Flapjack.WordRegImm.imm 13#64)))

def p9081 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40369 40357 (Flapjack.WordRegImm.reg 40365)))

def p9082 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40373 40349 (Flapjack.WordRegImm.reg 40369)))

def p9083 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40377, 40361)]

def p9084 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40381 40377 (Flapjack.WordRegImm.imm 30#64)))

def p9085 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40385, 40377)]

def p9086 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40389 40385 (Flapjack.WordRegImm.imm 2#64)))

def p9087 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40393 40381 (Flapjack.WordRegImm.reg 40389)))

def p9088 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40397 40373 (Flapjack.WordRegImm.reg 40393)))

def p9089 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40401 40329 (Flapjack.WordRegImm.reg 40397)))

def p9090 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40405, 40273)]

def p9091 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40409 40401 (Flapjack.WordRegImm.reg 40405)))

def p9092 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40413 40409 (Flapjack.WordRegImm.imm 32#64)))

def p9093 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40417 40413 (Flapjack.WordRegImm.imm 32#64)))

def p9094 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40425, 40237), (40421, 40161)]

def p9095 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40429 40421 (Flapjack.WordRegImm.reg 40425)))

def p9096 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40433, 40293)]

def p9097 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 40437 40429 (Flapjack.WordRegImm.reg 40433)))

def p9098 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40441, 40421)]

def p9099 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40445 40437 (Flapjack.WordRegImm.reg 40441)))

def p9100 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40449, 40433)]

def p9101 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40453 40449 (Flapjack.WordRegImm.imm 7#64)))

def p9102 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40457, 40449)]

def p9103 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40461 40457 (Flapjack.WordRegImm.imm 25#64)))

def p9104 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40465 40453 (Flapjack.WordRegImm.reg 40461)))

def p9105 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40469, 40457)]

def p9106 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40473 40469 (Flapjack.WordRegImm.imm 21#64)))

def p9107 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40477, 40469)]

def p9108 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40481 40477 (Flapjack.WordRegImm.imm 11#64)))

def p9109 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40485 40473 (Flapjack.WordRegImm.reg 40481)))

def p9110 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40489 40465 (Flapjack.WordRegImm.reg 40485)))

def p9111 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40493, 40477)]

def p9112 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40497 40493 (Flapjack.WordRegImm.imm 26#64)))

def p9113 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40501, 40493)]

def p9114 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40505 40501 (Flapjack.WordRegImm.imm 6#64)))

def p9115 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40509 40497 (Flapjack.WordRegImm.reg 40505)))

def p9116 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40513 40489 (Flapjack.WordRegImm.reg 40509)))

def p9117 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40517 40445 (Flapjack.WordRegImm.reg 40513)))

def p9118 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40521, 40177)]

def p9119 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40525 40517 (Flapjack.WordRegImm.reg 40521)))

def p9120 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 40529 1833138320#64)

def p9121 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40533 40525 (Flapjack.WordRegImm.reg 40529)))

def p9122 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40541, 40297), (40537, 40533)]

def p9123 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40545 40537 (Flapjack.WordRegImm.reg 40541)))

def p9124 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40549 40545 (Flapjack.WordRegImm.imm 32#64)))

def p9125 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40553 40549 (Flapjack.WordRegImm.imm 32#64)))

def p9126 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40577, 40417), (40573, 40385), (40569, 40317), (40561, 40325), (40557, 40553)]

def p9127 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40581 40573 (Flapjack.WordRegImm.reg 40577)))

def p9128 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 40585 40569 (Flapjack.WordRegImm.reg 40581)))

def p9129 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40589, 40573)]

def p9130 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40593 40585 (Flapjack.WordRegImm.reg 40589)))

def p9131 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40597, 40577)]

def p9132 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40601 40597 (Flapjack.WordRegImm.imm 10#64)))

def p9133 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40605, 40597)]

def p9134 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40609 40605 (Flapjack.WordRegImm.imm 22#64)))

def p9135 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40613 40601 (Flapjack.WordRegImm.reg 40609)))

def p9136 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40617, 40605)]

def p9137 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40621 40617 (Flapjack.WordRegImm.imm 19#64)))

def p9138 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40625, 40617)]

def p9139 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40629 40625 (Flapjack.WordRegImm.imm 13#64)))

def p9140 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40633 40621 (Flapjack.WordRegImm.reg 40629)))

def p9141 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40637 40613 (Flapjack.WordRegImm.reg 40633)))

def p9142 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40641, 40625)]

def p9143 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40645 40641 (Flapjack.WordRegImm.imm 30#64)))

def p9144 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40649, 40641)]

def p9145 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40653 40649 (Flapjack.WordRegImm.imm 2#64)))

def p9146 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40657 40645 (Flapjack.WordRegImm.reg 40653)))

def p9147 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40661 40637 (Flapjack.WordRegImm.reg 40657)))

def p9148 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40665 40593 (Flapjack.WordRegImm.reg 40661)))

def p9149 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40669, 40537)]

def p9150 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40673 40665 (Flapjack.WordRegImm.reg 40669)))

def p9151 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40677 40673 (Flapjack.WordRegImm.imm 32#64)))

def p9152 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40681 40677 (Flapjack.WordRegImm.imm 32#64)))

def p9153 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40689, 40501), (40685, 40425)]

def p9154 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40693 40685 (Flapjack.WordRegImm.reg 40689)))

def p9155 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40697, 40557)]

def p9156 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 40701 40693 (Flapjack.WordRegImm.reg 40697)))

def p9157 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40705, 40685)]

def p9158 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40709 40701 (Flapjack.WordRegImm.reg 40705)))

def p9159 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40713, 40697)]

def p9160 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40717 40713 (Flapjack.WordRegImm.imm 7#64)))

def p9161 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40721, 40713)]

def p9162 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40725 40721 (Flapjack.WordRegImm.imm 25#64)))

def p9163 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40729 40717 (Flapjack.WordRegImm.reg 40725)))

def p9164 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40733, 40721)]

def p9165 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40737 40733 (Flapjack.WordRegImm.imm 21#64)))

def p9166 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40741, 40733)]

def p9167 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40745 40741 (Flapjack.WordRegImm.imm 11#64)))

def p9168 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40749 40737 (Flapjack.WordRegImm.reg 40745)))

def p9169 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40753 40729 (Flapjack.WordRegImm.reg 40749)))

def p9170 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40757, 40741)]

def p9171 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40761 40757 (Flapjack.WordRegImm.imm 26#64)))

def p9172 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40765, 40757)]

def p9173 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40769 40765 (Flapjack.WordRegImm.imm 6#64)))

def p9174 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40773 40761 (Flapjack.WordRegImm.reg 40769)))

def p9175 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40777 40753 (Flapjack.WordRegImm.reg 40773)))

def p9176 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40781 40709 (Flapjack.WordRegImm.reg 40777)))

def p9177 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40785, 40441)]

def p9178 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40789 40781 (Flapjack.WordRegImm.reg 40785)))

def p9179 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 40793 18446744072696402418#64)

def p9180 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40797 40789 (Flapjack.WordRegImm.reg 40793)))

def p9181 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40805, 40561), (40801, 40797)]

def p9182 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40809 40801 (Flapjack.WordRegImm.reg 40805)))

def p9183 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40813 40809 (Flapjack.WordRegImm.imm 32#64)))

def p9184 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40817 40813 (Flapjack.WordRegImm.imm 32#64)))

def p9185 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40841, 40681), (40837, 40649), (40833, 40581), (40825, 40589), (40821, 40817)]

def p9186 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40845 40837 (Flapjack.WordRegImm.reg 40841)))

def p9187 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 40849 40833 (Flapjack.WordRegImm.reg 40845)))

def p9188 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40853, 40837)]

def p9189 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40857 40849 (Flapjack.WordRegImm.reg 40853)))

def p9190 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40861, 40841)]

def p9191 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40865 40861 (Flapjack.WordRegImm.imm 10#64)))

def p9192 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40869, 40861)]

def p9193 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40873 40869 (Flapjack.WordRegImm.imm 22#64)))

def p9194 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40877 40865 (Flapjack.WordRegImm.reg 40873)))

def p9195 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40881, 40869)]

def p9196 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40885 40881 (Flapjack.WordRegImm.imm 19#64)))

def p9197 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40889, 40881)]

def p9198 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40893 40889 (Flapjack.WordRegImm.imm 13#64)))

def p9199 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40897 40885 (Flapjack.WordRegImm.reg 40893)))

def p9200 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40901 40877 (Flapjack.WordRegImm.reg 40897)))

def p9201 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40905, 40889)]

def p9202 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40909 40905 (Flapjack.WordRegImm.imm 30#64)))

def p9203 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40913, 40905)]

def p9204 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40917 40913 (Flapjack.WordRegImm.imm 2#64)))

def p9205 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40921 40909 (Flapjack.WordRegImm.reg 40917)))

def p9206 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40925 40901 (Flapjack.WordRegImm.reg 40921)))

def p9207 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40929 40857 (Flapjack.WordRegImm.reg 40925)))

def p9208 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40933, 40801)]

def p9209 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 40937 40929 (Flapjack.WordRegImm.reg 40933)))

def p9210 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40941 40937 (Flapjack.WordRegImm.imm 32#64)))

def p9211 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40945 40941 (Flapjack.WordRegImm.imm 32#64)))

def p9212 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40953, 40765), (40949, 40689)]

def p9213 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40957 40949 (Flapjack.WordRegImm.reg 40953)))

def p9214 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40961, 40821)]

def p9215 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 40965 40957 (Flapjack.WordRegImm.reg 40961)))

def p9216 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40969, 40949)]

def p9217 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 40973 40965 (Flapjack.WordRegImm.reg 40969)))

def p9218 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40977, 40961)]

def p9219 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 40981 40977 (Flapjack.WordRegImm.imm 7#64)))

def p9220 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40985, 40977)]

def p9221 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 40989 40985 (Flapjack.WordRegImm.imm 25#64)))

def p9222 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 40993 40981 (Flapjack.WordRegImm.reg 40989)))

def p9223 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(40997, 40985)]

def p9224 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41001 40997 (Flapjack.WordRegImm.imm 21#64)))

def p9225 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41005, 40997)]

def p9226 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 41009 41005 (Flapjack.WordRegImm.imm 11#64)))

def p9227 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 41013 41001 (Flapjack.WordRegImm.reg 41009)))

def p9228 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41017 40993 (Flapjack.WordRegImm.reg 41013)))

def p9229 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41021, 41005)]

def p9230 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41025 41021 (Flapjack.WordRegImm.imm 26#64)))

def p9231 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41029, 41021)]

def p9232 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 41033 41029 (Flapjack.WordRegImm.imm 6#64)))

def p9233 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 41037 41025 (Flapjack.WordRegImm.reg 41033)))

def p9234 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41041 41017 (Flapjack.WordRegImm.reg 41037)))

def p9235 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 41045 40973 (Flapjack.WordRegImm.reg 41041)))

def p9236 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41049, 40705)]

def p9237 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 41053 41045 (Flapjack.WordRegImm.reg 41049)))

def p9238 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 41057 18446744072078797757#64)

def p9239 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 41061 41053 (Flapjack.WordRegImm.reg 41057)))

def p9240 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41069, 40825), (41065, 41061)]

def p9241 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 41073 41065 (Flapjack.WordRegImm.reg 41069)))

def p9242 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41077 41073 (Flapjack.WordRegImm.imm 32#64)))

def p9243 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 41081 41077 (Flapjack.WordRegImm.imm 32#64)))

def p9244 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41105, 40945), (41101, 40913), (41097, 40845), (41089, 40853), (41085, 41081)]

def p9245 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41109 41101 (Flapjack.WordRegImm.reg 41105)))

def p9246 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 41113 41097 (Flapjack.WordRegImm.reg 41109)))

def p9247 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41117, 41101)]

def p9248 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41121 41113 (Flapjack.WordRegImm.reg 41117)))

def p9249 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41125, 41105)]

def p9250 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41129 41125 (Flapjack.WordRegImm.imm 10#64)))

def p9251 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41133, 41125)]

def p9252 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 41137 41133 (Flapjack.WordRegImm.imm 22#64)))

def p9253 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 41141 41129 (Flapjack.WordRegImm.reg 41137)))

def p9254 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41145, 41133)]

def p9255 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41149 41145 (Flapjack.WordRegImm.imm 19#64)))

def p9256 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41153, 41145)]

def p9257 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 41157 41153 (Flapjack.WordRegImm.imm 13#64)))

def p9258 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 41161 41149 (Flapjack.WordRegImm.reg 41157)))

def p9259 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41165 41141 (Flapjack.WordRegImm.reg 41161)))

def p9260 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41169, 41153)]

def p9261 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41173 41169 (Flapjack.WordRegImm.imm 30#64)))

def p9262 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41177, 41169)]

def p9263 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 41181 41177 (Flapjack.WordRegImm.imm 2#64)))

def p9264 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 41185 41173 (Flapjack.WordRegImm.reg 41181)))

def p9265 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41189 41165 (Flapjack.WordRegImm.reg 41185)))

def p9266 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 41193 41121 (Flapjack.WordRegImm.reg 41189)))

def p9267 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41197, 41065)]

def p9268 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 41201 41193 (Flapjack.WordRegImm.reg 41197)))

def p9269 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41205 41201 (Flapjack.WordRegImm.imm 32#64)))

def p9270 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 41209 41205 (Flapjack.WordRegImm.imm 32#64)))

def p9271 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41217, 41029), (41213, 40953)]

def p9272 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41221 41213 (Flapjack.WordRegImm.reg 41217)))

def p9273 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41225, 41085)]

def p9274 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 41229 41221 (Flapjack.WordRegImm.reg 41225)))

def p9275 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41233, 41213)]

def p9276 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41237 41229 (Flapjack.WordRegImm.reg 41233)))

def p9277 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41241, 41225)]

def p9278 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41245 41241 (Flapjack.WordRegImm.imm 7#64)))

def p9279 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41249, 41241)]

def p9280 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 41253 41249 (Flapjack.WordRegImm.imm 25#64)))

def p9281 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 41257 41245 (Flapjack.WordRegImm.reg 41253)))

def p9282 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41261, 41249)]

def p9283 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41265 41261 (Flapjack.WordRegImm.imm 21#64)))

def p9284 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41269, 41261)]

def p9285 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 41273 41269 (Flapjack.WordRegImm.imm 11#64)))

def p9286 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 41277 41265 (Flapjack.WordRegImm.reg 41273)))

def p9287 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41281 41257 (Flapjack.WordRegImm.reg 41277)))

def p9288 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41285, 41269)]

def p9289 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41289 41285 (Flapjack.WordRegImm.imm 26#64)))

def p9290 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41293, 41285)]

def p9291 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 41297 41293 (Flapjack.WordRegImm.imm 6#64)))

def p9292 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 41301 41289 (Flapjack.WordRegImm.reg 41297)))

def p9293 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41305 41281 (Flapjack.WordRegImm.reg 41301)))

def p9294 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 41309 41237 (Flapjack.WordRegImm.reg 41305)))

def p9295 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41313, 40969)]

def p9296 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 41317 41309 (Flapjack.WordRegImm.reg 41313)))

def p9297 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 41321 18446744072464474342#64)

def p9298 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 41325 41317 (Flapjack.WordRegImm.reg 41321)))

def p9299 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41333, 41089), (41329, 41325)]

def p9300 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 41337 41329 (Flapjack.WordRegImm.reg 41333)))

def p9301 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41341 41337 (Flapjack.WordRegImm.imm 32#64)))

def p9302 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 41345 41341 (Flapjack.WordRegImm.imm 32#64)))

def p9303 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41369, 41209), (41365, 41177), (41361, 41109), (41353, 41117), (41349, 41345)]

def p9304 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41373 41365 (Flapjack.WordRegImm.reg 41369)))

def p9305 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 41377 41361 (Flapjack.WordRegImm.reg 41373)))

def p9306 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41381, 41365)]

def p9307 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 41385 41377 (Flapjack.WordRegImm.reg 41381)))

def p9308 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(41389, 41369)]

def p9309 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41393 41389 (Flapjack.WordRegImm.imm 10#64)))

def parts : List (WordLangProgHOL (BitVec 64)) := [p8810, p8811, p8812, p8813, p8814, p8815, p8816, p8817, p8818, p8819, p8820, p8821, p8822, p8823, p8824, p8825, p8826, p8827, p8828, p8829, p8830, p8831, p8832, p8833, p8834, p8835, p8836, p8837, p8838, p8839, p8840, p8841, p8842, p8843, p8844, p8845, p8846, p8847, p8848, p8849, p8850, p8851, p8852, p8853, p8854, p8855, p8856, p8857, p8858, p8859, p8860, p8861, p8862, p8863, p8864, p8865, p8866, p8867, p8868, p8869, p8870, p8871, p8872, p8873, p8874, p8875, p8876, p8877, p8878, p8879, p8880, p8881, p8882, p8883, p8884, p8885, p8886, p8887, p8888, p8889, p8890, p8891, p8892, p8893, p8894, p8895, p8896, p8897, p8898, p8899, p8900, p8901, p8902, p8903, p8904, p8905, p8906, p8907, p8908, p8909, p8910, p8911, p8912, p8913, p8914, p8915, p8916, p8917, p8918, p8919, p8920, p8921, p8922, p8923, p8924, p8925, p8926, p8927, p8928, p8929, p8930, p8931, p8932, p8933, p8934, p8935, p8936, p8937, p8938, p8939, p8940, p8941, p8942, p8943, p8944, p8945, p8946, p8947, p8948, p8949, p8950, p8951, p8952, p8953, p8954, p8955, p8956, p8957, p8958, p8959, p8960, p8961, p8962, p8963, p8964, p8965, p8966, p8967, p8968, p8969, p8970, p8971, p8972, p8973, p8974, p8975, p8976, p8977, p8978, p8979, p8980, p8981, p8982, p8983, p8984, p8985, p8986, p8987, p8988, p8989, p8990, p8991, p8992, p8993, p8994, p8995, p8996, p8997, p8998, p8999, p9000, p9001, p9002, p9003, p9004, p9005, p9006, p9007, p9008, p9009, p9010, p9011, p9012, p9013, p9014, p9015, p9016, p9017, p9018, p9019, p9020, p9021, p9022, p9023, p9024, p9025, p9026, p9027, p9028, p9029, p9030, p9031, p9032, p9033, p9034, p9035, p9036, p9037, p9038, p9039, p9040, p9041, p9042, p9043, p9044, p9045, p9046, p9047, p9048, p9049, p9050, p9051, p9052, p9053, p9054, p9055, p9056, p9057, p9058, p9059, p9060, p9061, p9062, p9063, p9064, p9065, p9066, p9067, p9068, p9069, p9070, p9071, p9072, p9073, p9074, p9075, p9076, p9077, p9078, p9079, p9080, p9081, p9082, p9083, p9084, p9085, p9086, p9087, p9088, p9089, p9090, p9091, p9092, p9093, p9094, p9095, p9096, p9097, p9098, p9099, p9100, p9101, p9102, p9103, p9104, p9105, p9106, p9107, p9108, p9109, p9110, p9111, p9112, p9113, p9114, p9115, p9116, p9117, p9118, p9119, p9120, p9121, p9122, p9123, p9124, p9125, p9126, p9127, p9128, p9129, p9130, p9131, p9132, p9133, p9134, p9135, p9136, p9137, p9138, p9139, p9140, p9141, p9142, p9143, p9144, p9145, p9146, p9147, p9148, p9149, p9150, p9151, p9152, p9153, p9154, p9155, p9156, p9157, p9158, p9159, p9160, p9161, p9162, p9163, p9164, p9165, p9166, p9167, p9168, p9169, p9170, p9171, p9172, p9173, p9174, p9175, p9176, p9177, p9178, p9179, p9180, p9181, p9182, p9183, p9184, p9185, p9186, p9187, p9188, p9189, p9190, p9191, p9192, p9193, p9194, p9195, p9196, p9197, p9198, p9199, p9200, p9201, p9202, p9203, p9204, p9205, p9206, p9207, p9208, p9209, p9210, p9211, p9212, p9213, p9214, p9215, p9216, p9217, p9218, p9219, p9220, p9221, p9222, p9223, p9224, p9225, p9226, p9227, p9228, p9229, p9230, p9231, p9232, p9233, p9234, p9235, p9236, p9237, p9238, p9239, p9240, p9241, p9242, p9243, p9244, p9245, p9246, p9247, p9248, p9249, p9250, p9251, p9252, p9253, p9254, p9255, p9256, p9257, p9258, p9259, p9260, p9261, p9262, p9263, p9264, p9265, p9266, p9267, p9268, p9269, p9270, p9271, p9272, p9273, p9274, p9275, p9276, p9277, p9278, p9279, p9280, p9281, p9282, p9283, p9284, p9285, p9286, p9287, p9288, p9289, p9290, p9291, p9292, p9293, p9294, p9295, p9296, p9297, p9298, p9299, p9300, p9301, p9302, p9303, p9304, p9305, p9306, p9307, p9308, p9309]

wave8_kernel_reduce trees := parts.map (fun p => WordAlloc.getClashTree p [])
wave8_kernel_reduce colPs := parts.map (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)))
wave8_kernel_reduce stackOk := colPs.all (everyStackVarHOL stackPred)
wave8_kernel_reduce forcedOk := parts.all (fun p => (WordAlloc.getForced riscvConfig p []).all (forcedPred (oracle154.getD .ln)))
wave8_kernel_reduce progs := parts.map (transform oracle154)
wave8_kernel_reduce maxV := maxListProg progs
wave8_kernel_reduce comp := compList riscvConfig false (22, 13, 12) progs (.nil, 136)

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154.Block01
