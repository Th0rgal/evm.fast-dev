import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ClashSupport
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 20000000
namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ClashTree
open Flapjack
noncomputable section
def part5888 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26073, 26045)]

def part5889 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26077 26073 (Flapjack.WordRegImm.imm 16#64)))

def part5890 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26085, 26073), (26081, 25901)]

def part5891 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 26089 (Flapjack.WordLangAddr.addr 26085 16#64))

def part5892 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26093 26081 (Flapjack.WordRegImm.reg 26089)))

def part5893 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 26097 26093 (Flapjack.WordRegImm.imm 32#64)))

def part5894 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 26101 26097 (Flapjack.WordRegImm.imm 32#64)))

def part5895 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26109, 26077), (26105, 26101)]

def part5896 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 26105 (Flapjack.WordLangAddr.addr 26109 0))

def part5897 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26113, 26085)]

def part5898 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26117 26113 (Flapjack.WordRegImm.imm 24#64)))

def part5899 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26125, 26113), (26121, 25873)]

def part5900 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 26129 (Flapjack.WordLangAddr.addr 26125 24#64))

def part5901 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26133 26121 (Flapjack.WordRegImm.reg 26129)))

def part5902 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 26137 26133 (Flapjack.WordRegImm.imm 32#64)))

def part5903 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 26141 26137 (Flapjack.WordRegImm.imm 32#64)))

def part5904 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26149, 26117), (26145, 26141)]

def part5905 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 26145 (Flapjack.WordLangAddr.addr 26149 0))

def part5906 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26153, 26125)]

def part5907 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26157 26153 (Flapjack.WordRegImm.imm 32#64)))

def part5908 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26165, 26153), (26161, 25869)]

def part5909 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 26169 (Flapjack.WordLangAddr.addr 26165 32#64))

def part5910 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26173 26161 (Flapjack.WordRegImm.reg 26169)))

def part5911 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 26177 26173 (Flapjack.WordRegImm.imm 32#64)))

def part5912 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 26181 26177 (Flapjack.WordRegImm.imm 32#64)))

def part5913 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26189, 26157), (26185, 26181)]

def part5914 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 26185 (Flapjack.WordLangAddr.addr 26189 0))

def part5915 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26193, 26165)]

def part5916 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26197 26193 (Flapjack.WordRegImm.imm 40#64)))

def part5917 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26205, 26193), (26201, 25813)]

def part5918 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 26209 (Flapjack.WordLangAddr.addr 26205 40#64))

def part5919 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26213 26201 (Flapjack.WordRegImm.reg 26209)))

def part5920 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 26217 26213 (Flapjack.WordRegImm.imm 32#64)))

def part5921 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 26221 26217 (Flapjack.WordRegImm.imm 32#64)))

def part5922 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26229, 26197), (26225, 26221)]

def part5923 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 26225 (Flapjack.WordLangAddr.addr 26229 0))

def part5924 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26233, 26205)]

def part5925 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26237 26233 (Flapjack.WordRegImm.imm 48#64)))

def part5926 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26245, 26233), (26241, 25733)]

def part5927 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 26249 (Flapjack.WordLangAddr.addr 26245 48#64))

def part5928 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26253 26241 (Flapjack.WordRegImm.reg 26249)))

def part5929 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 26257 26253 (Flapjack.WordRegImm.imm 32#64)))

def part5930 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 26261 26257 (Flapjack.WordRegImm.imm 32#64)))

def part5931 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26269, 26237), (26265, 26261)]

def part5932 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 26265 (Flapjack.WordLangAddr.addr 26269 0))

def part5933 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26273, 26245)]

def part5934 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26277 26273 (Flapjack.WordRegImm.imm 56#64)))

def part5935 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26285, 26273), (26281, 25749)]

def part5936 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 26289 (Flapjack.WordLangAddr.addr 26285 56#64))

def part5937 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 26293 26281 (Flapjack.WordRegImm.reg 26289)))

def part5938 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 26297 26293 (Flapjack.WordRegImm.imm 32#64)))

def part5939 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 26301 26297 (Flapjack.WordRegImm.imm 32#64)))

def part5940 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(26309, 26277), (26305, 26301)]

def part5941 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 26305 (Flapjack.WordLangAddr.addr 26309 0))

def part5942 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 26313 0#64)

def part5943 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 26313)]

def part5944 : Flapjack.WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 197 [2]

wave8_certified_reduce part5888Tree := WordAlloc.getClashTree part5888 []
wave8_certified_reduce part5889Tree := WordAlloc.getClashTree part5889 []
wave8_certified_reduce part5890Tree := WordAlloc.getClashTree part5890 []
wave8_certified_reduce part5891Tree := WordAlloc.getClashTree part5891 []
wave8_certified_reduce part5892Tree := WordAlloc.getClashTree part5892 []
wave8_certified_reduce part5893Tree := WordAlloc.getClashTree part5893 []
wave8_certified_reduce part5894Tree := WordAlloc.getClashTree part5894 []
wave8_certified_reduce part5895Tree := WordAlloc.getClashTree part5895 []
wave8_certified_reduce part5896Tree := WordAlloc.getClashTree part5896 []
wave8_certified_reduce part5897Tree := WordAlloc.getClashTree part5897 []
wave8_certified_reduce part5898Tree := WordAlloc.getClashTree part5898 []
wave8_certified_reduce part5899Tree := WordAlloc.getClashTree part5899 []
wave8_certified_reduce part5900Tree := WordAlloc.getClashTree part5900 []
wave8_certified_reduce part5901Tree := WordAlloc.getClashTree part5901 []
wave8_certified_reduce part5902Tree := WordAlloc.getClashTree part5902 []
wave8_certified_reduce part5903Tree := WordAlloc.getClashTree part5903 []
wave8_certified_reduce part5904Tree := WordAlloc.getClashTree part5904 []
wave8_certified_reduce part5905Tree := WordAlloc.getClashTree part5905 []
wave8_certified_reduce part5906Tree := WordAlloc.getClashTree part5906 []
wave8_certified_reduce part5907Tree := WordAlloc.getClashTree part5907 []
wave8_certified_reduce part5908Tree := WordAlloc.getClashTree part5908 []
wave8_certified_reduce part5909Tree := WordAlloc.getClashTree part5909 []
wave8_certified_reduce part5910Tree := WordAlloc.getClashTree part5910 []
wave8_certified_reduce part5911Tree := WordAlloc.getClashTree part5911 []
wave8_certified_reduce part5912Tree := WordAlloc.getClashTree part5912 []
wave8_certified_reduce part5913Tree := WordAlloc.getClashTree part5913 []
wave8_certified_reduce part5914Tree := WordAlloc.getClashTree part5914 []
wave8_certified_reduce part5915Tree := WordAlloc.getClashTree part5915 []
wave8_certified_reduce part5916Tree := WordAlloc.getClashTree part5916 []
wave8_certified_reduce part5917Tree := WordAlloc.getClashTree part5917 []
wave8_certified_reduce part5918Tree := WordAlloc.getClashTree part5918 []
wave8_certified_reduce part5919Tree := WordAlloc.getClashTree part5919 []
wave8_certified_reduce part5920Tree := WordAlloc.getClashTree part5920 []
wave8_certified_reduce part5921Tree := WordAlloc.getClashTree part5921 []
wave8_certified_reduce part5922Tree := WordAlloc.getClashTree part5922 []
wave8_certified_reduce part5923Tree := WordAlloc.getClashTree part5923 []
wave8_certified_reduce part5924Tree := WordAlloc.getClashTree part5924 []
wave8_certified_reduce part5925Tree := WordAlloc.getClashTree part5925 []
wave8_certified_reduce part5926Tree := WordAlloc.getClashTree part5926 []
wave8_certified_reduce part5927Tree := WordAlloc.getClashTree part5927 []
wave8_certified_reduce part5928Tree := WordAlloc.getClashTree part5928 []
wave8_certified_reduce part5929Tree := WordAlloc.getClashTree part5929 []
wave8_certified_reduce part5930Tree := WordAlloc.getClashTree part5930 []
wave8_certified_reduce part5931Tree := WordAlloc.getClashTree part5931 []
wave8_certified_reduce part5932Tree := WordAlloc.getClashTree part5932 []
wave8_certified_reduce part5933Tree := WordAlloc.getClashTree part5933 []
wave8_certified_reduce part5934Tree := WordAlloc.getClashTree part5934 []
wave8_certified_reduce part5935Tree := WordAlloc.getClashTree part5935 []
wave8_certified_reduce part5936Tree := WordAlloc.getClashTree part5936 []
wave8_certified_reduce part5937Tree := WordAlloc.getClashTree part5937 []
wave8_certified_reduce part5938Tree := WordAlloc.getClashTree part5938 []
wave8_certified_reduce part5939Tree := WordAlloc.getClashTree part5939 []
wave8_certified_reduce part5940Tree := WordAlloc.getClashTree part5940 []
wave8_certified_reduce part5941Tree := WordAlloc.getClashTree part5941 []
wave8_certified_reduce part5942Tree := WordAlloc.getClashTree part5942 []
wave8_certified_reduce part5943Tree := WordAlloc.getClashTree part5943 []
wave8_certified_reduce part5944Tree := WordAlloc.getClashTree part5944 []

end
end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ClashTree
