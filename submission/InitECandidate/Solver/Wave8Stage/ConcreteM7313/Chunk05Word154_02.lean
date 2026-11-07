import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154Support

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154.Block02
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition Chunk05Stack151 Chunk05Word154

def p8310 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(36921, 36909)]

def p8311 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 36925 36921 (Flapjack.WordRegImm.imm 19#64)))

def p8312 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(36929, 36921)]

def p8313 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 36933 36929 (Flapjack.WordRegImm.imm 13#64)))

def p8314 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 36937 36925 (Flapjack.WordRegImm.reg 36933)))

def p8315 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 36941 36917 (Flapjack.WordRegImm.reg 36937)))

def p8316 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(36945, 36929)]

def p8317 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 36949 36945 (Flapjack.WordRegImm.imm 30#64)))

def p8318 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(36953, 36945)]

def p8319 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 36957 36953 (Flapjack.WordRegImm.imm 2#64)))

def p8320 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 36961 36949 (Flapjack.WordRegImm.reg 36957)))

def p8321 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 36965 36941 (Flapjack.WordRegImm.reg 36961)))

def p8322 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 36969 36897 (Flapjack.WordRegImm.reg 36965)))

def p8323 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(36973, 36841)]

def p8324 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 36977 36969 (Flapjack.WordRegImm.reg 36973)))

def p8325 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 36981 36977 (Flapjack.WordRegImm.imm 32#64)))

def p8326 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 36985 36981 (Flapjack.WordRegImm.imm 32#64)))

def p8327 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(36993, 36805), (36989, 36729)]

def p8328 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 36997 36989 (Flapjack.WordRegImm.reg 36993)))

def p8329 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37001, 36861)]

def p8330 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 37005 36997 (Flapjack.WordRegImm.reg 37001)))

def p8331 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37009, 36989)]

def p8332 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37013 37005 (Flapjack.WordRegImm.reg 37009)))

def p8333 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37017, 37001)]

def p8334 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37021 37017 (Flapjack.WordRegImm.imm 7#64)))

def p8335 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37025, 37017)]

def p8336 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37029 37025 (Flapjack.WordRegImm.imm 25#64)))

def p8337 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37033 37021 (Flapjack.WordRegImm.reg 37029)))

def p8338 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37037, 37025)]

def p8339 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37041 37037 (Flapjack.WordRegImm.imm 21#64)))

def p8340 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37045, 37037)]

def p8341 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37049 37045 (Flapjack.WordRegImm.imm 11#64)))

def p8342 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37053 37041 (Flapjack.WordRegImm.reg 37049)))

def p8343 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37057 37033 (Flapjack.WordRegImm.reg 37053)))

def p8344 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37061, 37045)]

def p8345 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37065 37061 (Flapjack.WordRegImm.imm 26#64)))

def p8346 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37069, 37061)]

def p8347 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37073 37069 (Flapjack.WordRegImm.imm 6#64)))

def p8348 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37077 37065 (Flapjack.WordRegImm.reg 37073)))

def p8349 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37081 37057 (Flapjack.WordRegImm.reg 37077)))

def p8350 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37085 37013 (Flapjack.WordRegImm.reg 37081)))

def p8351 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37089, 36745)]

def p8352 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37093 37085 (Flapjack.WordRegImm.reg 37089)))

def p8353 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 37097 18446744072183343666#64)

def p8354 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37101 37093 (Flapjack.WordRegImm.reg 37097)))

def p8355 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37109, 36865), (37105, 37101)]

def p8356 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37113 37105 (Flapjack.WordRegImm.reg 37109)))

def p8357 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37117 37113 (Flapjack.WordRegImm.imm 32#64)))

def p8358 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37121 37117 (Flapjack.WordRegImm.imm 32#64)))

def p8359 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37145, 36985), (37141, 36953), (37137, 36885), (37129, 36893), (37125, 37121)]

def p8360 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37149 37141 (Flapjack.WordRegImm.reg 37145)))

def p8361 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 37153 37137 (Flapjack.WordRegImm.reg 37149)))

def p8362 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37157, 37141)]

def p8363 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37161 37153 (Flapjack.WordRegImm.reg 37157)))

def p8364 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37165, 37145)]

def p8365 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37169 37165 (Flapjack.WordRegImm.imm 10#64)))

def p8366 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37173, 37165)]

def p8367 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37177 37173 (Flapjack.WordRegImm.imm 22#64)))

def p8368 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37181 37169 (Flapjack.WordRegImm.reg 37177)))

def p8369 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37185, 37173)]

def p8370 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37189 37185 (Flapjack.WordRegImm.imm 19#64)))

def p8371 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37193, 37185)]

def p8372 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37197 37193 (Flapjack.WordRegImm.imm 13#64)))

def p8373 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37201 37189 (Flapjack.WordRegImm.reg 37197)))

def p8374 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37205 37181 (Flapjack.WordRegImm.reg 37201)))

def p8375 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37209, 37193)]

def p8376 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37213 37209 (Flapjack.WordRegImm.imm 30#64)))

def p8377 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37217, 37209)]

def p8378 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37221 37217 (Flapjack.WordRegImm.imm 2#64)))

def p8379 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37225 37213 (Flapjack.WordRegImm.reg 37221)))

def p8380 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37229 37205 (Flapjack.WordRegImm.reg 37225)))

def p8381 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37233 37161 (Flapjack.WordRegImm.reg 37229)))

def p8382 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37237, 37105)]

def p8383 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37241 37233 (Flapjack.WordRegImm.reg 37237)))

def p8384 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37245 37241 (Flapjack.WordRegImm.imm 32#64)))

def p8385 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37249 37245 (Flapjack.WordRegImm.imm 32#64)))

def p8386 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37257, 37069), (37253, 36993)]

def p8387 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37261 37253 (Flapjack.WordRegImm.reg 37257)))

def p8388 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37265, 37125)]

def p8389 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 37269 37261 (Flapjack.WordRegImm.reg 37265)))

def p8390 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37273, 37253)]

def p8391 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37277 37269 (Flapjack.WordRegImm.reg 37273)))

def p8392 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37281, 37265)]

def p8393 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37285 37281 (Flapjack.WordRegImm.imm 7#64)))

def p8394 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37289, 37281)]

def p8395 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37293 37289 (Flapjack.WordRegImm.imm 25#64)))

def p8396 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37297 37285 (Flapjack.WordRegImm.reg 37293)))

def p8397 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37301, 37289)]

def p8398 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37305 37301 (Flapjack.WordRegImm.imm 21#64)))

def p8399 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37309, 37301)]

def p8400 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37313 37309 (Flapjack.WordRegImm.imm 11#64)))

def p8401 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37317 37305 (Flapjack.WordRegImm.reg 37313)))

def p8402 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37321 37297 (Flapjack.WordRegImm.reg 37317)))

def p8403 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37325, 37309)]

def p8404 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37329 37325 (Flapjack.WordRegImm.imm 26#64)))

def p8405 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37333, 37325)]

def p8406 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37337 37333 (Flapjack.WordRegImm.imm 6#64)))

def p8407 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37341 37329 (Flapjack.WordRegImm.reg 37337)))

def p8408 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37345 37321 (Flapjack.WordRegImm.reg 37341)))

def p8409 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37349 37277 (Flapjack.WordRegImm.reg 37345)))

def p8410 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37353, 37009)]

def p8411 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37357 37349 (Flapjack.WordRegImm.reg 37353)))

def p8412 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 37361 1873515831#64)

def p8413 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37365 37357 (Flapjack.WordRegImm.reg 37361)))

def p8414 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37373, 37129), (37369, 37365)]

def p8415 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37377 37369 (Flapjack.WordRegImm.reg 37373)))

def p8416 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37381 37377 (Flapjack.WordRegImm.imm 32#64)))

def p8417 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37385 37381 (Flapjack.WordRegImm.imm 32#64)))

def p8418 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37409, 37249), (37405, 37217), (37401, 37149), (37393, 37157), (37389, 37385)]

def p8419 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37413 37405 (Flapjack.WordRegImm.reg 37409)))

def p8420 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 37417 37401 (Flapjack.WordRegImm.reg 37413)))

def p8421 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37421, 37405)]

def p8422 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37425 37417 (Flapjack.WordRegImm.reg 37421)))

def p8423 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37429, 37409)]

def p8424 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37433 37429 (Flapjack.WordRegImm.imm 10#64)))

def p8425 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37437, 37429)]

def p8426 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37441 37437 (Flapjack.WordRegImm.imm 22#64)))

def p8427 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37445 37433 (Flapjack.WordRegImm.reg 37441)))

def p8428 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37449, 37437)]

def p8429 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37453 37449 (Flapjack.WordRegImm.imm 19#64)))

def p8430 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37457, 37449)]

def p8431 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37461 37457 (Flapjack.WordRegImm.imm 13#64)))

def p8432 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37465 37453 (Flapjack.WordRegImm.reg 37461)))

def p8433 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37469 37445 (Flapjack.WordRegImm.reg 37465)))

def p8434 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37473, 37457)]

def p8435 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37477 37473 (Flapjack.WordRegImm.imm 30#64)))

def p8436 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37481, 37473)]

def p8437 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37485 37481 (Flapjack.WordRegImm.imm 2#64)))

def p8438 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37489 37477 (Flapjack.WordRegImm.reg 37485)))

def p8439 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37493 37469 (Flapjack.WordRegImm.reg 37489)))

def p8440 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37497 37425 (Flapjack.WordRegImm.reg 37493)))

def p8441 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37501, 37369)]

def p8442 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37505 37497 (Flapjack.WordRegImm.reg 37501)))

def p8443 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37509 37505 (Flapjack.WordRegImm.imm 32#64)))

def p8444 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37513 37509 (Flapjack.WordRegImm.imm 32#64)))

def p8445 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37521, 37333), (37517, 37257)]

def p8446 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37525 37517 (Flapjack.WordRegImm.reg 37521)))

def p8447 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37529, 37389)]

def p8448 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 37533 37525 (Flapjack.WordRegImm.reg 37529)))

def p8449 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37537, 37517)]

def p8450 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37541 37533 (Flapjack.WordRegImm.reg 37537)))

def p8451 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37545, 37529)]

def p8452 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37549 37545 (Flapjack.WordRegImm.imm 7#64)))

def p8453 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37553, 37545)]

def p8454 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37557 37553 (Flapjack.WordRegImm.imm 25#64)))

def p8455 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37561 37549 (Flapjack.WordRegImm.reg 37557)))

def p8456 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37565, 37553)]

def p8457 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37569 37565 (Flapjack.WordRegImm.imm 21#64)))

def p8458 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37573, 37565)]

def p8459 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37577 37573 (Flapjack.WordRegImm.imm 11#64)))

def p8460 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37581 37569 (Flapjack.WordRegImm.reg 37577)))

def p8461 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37585 37561 (Flapjack.WordRegImm.reg 37581)))

def p8462 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37589, 37573)]

def p8463 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37593 37589 (Flapjack.WordRegImm.imm 26#64)))

def p8464 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37597, 37589)]

def p8465 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37601 37597 (Flapjack.WordRegImm.imm 6#64)))

def p8466 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37605 37593 (Flapjack.WordRegImm.reg 37601)))

def p8467 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37609 37585 (Flapjack.WordRegImm.reg 37605)))

def p8468 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37613 37541 (Flapjack.WordRegImm.reg 37609)))

def p8469 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37617, 37273)]

def p8470 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37621 37613 (Flapjack.WordRegImm.reg 37617)))

def p8471 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 37625 390095120#64)

def p8472 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37629 37621 (Flapjack.WordRegImm.reg 37625)))

def p8473 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37637, 37393), (37633, 37629)]

def p8474 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37641 37633 (Flapjack.WordRegImm.reg 37637)))

def p8475 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37645 37641 (Flapjack.WordRegImm.imm 32#64)))

def p8476 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37649 37645 (Flapjack.WordRegImm.imm 32#64)))

def p8477 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37673, 37513), (37669, 37481), (37665, 37413), (37657, 37421), (37653, 37649)]

def p8478 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37677 37669 (Flapjack.WordRegImm.reg 37673)))

def p8479 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 37681 37665 (Flapjack.WordRegImm.reg 37677)))

def p8480 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37685, 37669)]

def p8481 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37689 37681 (Flapjack.WordRegImm.reg 37685)))

def p8482 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37693, 37673)]

def p8483 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37697 37693 (Flapjack.WordRegImm.imm 10#64)))

def p8484 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37701, 37693)]

def p8485 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37705 37701 (Flapjack.WordRegImm.imm 22#64)))

def p8486 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37709 37697 (Flapjack.WordRegImm.reg 37705)))

def p8487 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37713, 37701)]

def p8488 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37717 37713 (Flapjack.WordRegImm.imm 19#64)))

def p8489 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37721, 37713)]

def p8490 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37725 37721 (Flapjack.WordRegImm.imm 13#64)))

def p8491 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37729 37717 (Flapjack.WordRegImm.reg 37725)))

def p8492 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37733 37709 (Flapjack.WordRegImm.reg 37729)))

def p8493 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37737, 37721)]

def p8494 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37741 37737 (Flapjack.WordRegImm.imm 30#64)))

def p8495 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37745, 37737)]

def p8496 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37749 37745 (Flapjack.WordRegImm.imm 2#64)))

def p8497 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37753 37741 (Flapjack.WordRegImm.reg 37749)))

def p8498 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37757 37733 (Flapjack.WordRegImm.reg 37753)))

def p8499 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37761 37689 (Flapjack.WordRegImm.reg 37757)))

def p8500 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37765, 37633)]

def p8501 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37769 37761 (Flapjack.WordRegImm.reg 37765)))

def p8502 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37773 37769 (Flapjack.WordRegImm.imm 32#64)))

def p8503 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37777 37773 (Flapjack.WordRegImm.imm 32#64)))

def p8504 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37785, 37597), (37781, 37521)]

def p8505 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37789 37781 (Flapjack.WordRegImm.reg 37785)))

def p8506 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37793, 37653)]

def p8507 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 37797 37789 (Flapjack.WordRegImm.reg 37793)))

def p8508 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37801, 37781)]

def p8509 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37805 37797 (Flapjack.WordRegImm.reg 37801)))

def p8510 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37809, 37793)]

def p8511 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37813 37809 (Flapjack.WordRegImm.imm 7#64)))

def p8512 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37817, 37809)]

def p8513 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37821 37817 (Flapjack.WordRegImm.imm 25#64)))

def p8514 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37825 37813 (Flapjack.WordRegImm.reg 37821)))

def p8515 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37829, 37817)]

def p8516 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37833 37829 (Flapjack.WordRegImm.imm 21#64)))

def p8517 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37837, 37829)]

def p8518 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37841 37837 (Flapjack.WordRegImm.imm 11#64)))

def p8519 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37845 37833 (Flapjack.WordRegImm.reg 37841)))

def p8520 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37849 37825 (Flapjack.WordRegImm.reg 37845)))

def p8521 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37853, 37837)]

def p8522 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37857 37853 (Flapjack.WordRegImm.imm 26#64)))

def p8523 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37861, 37853)]

def p8524 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37865 37861 (Flapjack.WordRegImm.imm 6#64)))

def p8525 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37869 37857 (Flapjack.WordRegImm.reg 37865)))

def p8526 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37873 37849 (Flapjack.WordRegImm.reg 37869)))

def p8527 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37877 37805 (Flapjack.WordRegImm.reg 37873)))

def p8528 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37881, 37537)]

def p8529 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37885 37877 (Flapjack.WordRegImm.reg 37881)))

def p8530 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 37889 227333873#64)

def p8531 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37893 37885 (Flapjack.WordRegImm.reg 37889)))

def p8532 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37901, 37657), (37897, 37893)]

def p8533 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 37905 37897 (Flapjack.WordRegImm.reg 37901)))

def p8534 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37909 37905 (Flapjack.WordRegImm.imm 32#64)))

def p8535 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37913 37909 (Flapjack.WordRegImm.imm 32#64)))

def p8536 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37937, 37777), (37933, 37745), (37929, 37677), (37921, 37685), (37917, 37913)]

def p8537 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37941 37933 (Flapjack.WordRegImm.reg 37937)))

def p8538 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 37945 37929 (Flapjack.WordRegImm.reg 37941)))

def p8539 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37949, 37933)]

def p8540 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37953 37945 (Flapjack.WordRegImm.reg 37949)))

def p8541 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37957, 37937)]

def p8542 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37961 37957 (Flapjack.WordRegImm.imm 10#64)))

def p8543 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37965, 37957)]

def p8544 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37969 37965 (Flapjack.WordRegImm.imm 22#64)))

def p8545 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37973 37961 (Flapjack.WordRegImm.reg 37969)))

def p8546 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37977, 37965)]

def p8547 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 37981 37977 (Flapjack.WordRegImm.imm 19#64)))

def p8548 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(37985, 37977)]

def p8549 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 37989 37985 (Flapjack.WordRegImm.imm 13#64)))

def p8550 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 37993 37981 (Flapjack.WordRegImm.reg 37989)))

def p8551 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 37997 37973 (Flapjack.WordRegImm.reg 37993)))

def p8552 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38001, 37985)]

def p8553 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38005 38001 (Flapjack.WordRegImm.imm 30#64)))

def p8554 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38009, 38001)]

def p8555 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38013 38009 (Flapjack.WordRegImm.imm 2#64)))

def p8556 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38017 38005 (Flapjack.WordRegImm.reg 38013)))

def p8557 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38021 37997 (Flapjack.WordRegImm.reg 38017)))

def p8558 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38025 37953 (Flapjack.WordRegImm.reg 38021)))

def p8559 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38029, 37897)]

def p8560 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38033 38025 (Flapjack.WordRegImm.reg 38029)))

def p8561 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38037 38033 (Flapjack.WordRegImm.imm 32#64)))

def p8562 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38041 38037 (Flapjack.WordRegImm.imm 32#64)))

def p8563 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38049, 37861), (38045, 37785)]

def p8564 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38053 38045 (Flapjack.WordRegImm.reg 38049)))

def p8565 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38057, 37917)]

def p8566 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 38061 38053 (Flapjack.WordRegImm.reg 38057)))

def p8567 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38065, 38045)]

def p8568 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38069 38061 (Flapjack.WordRegImm.reg 38065)))

def p8569 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38073, 38057)]

def p8570 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38077 38073 (Flapjack.WordRegImm.imm 7#64)))

def p8571 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38081, 38073)]

def p8572 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38085 38081 (Flapjack.WordRegImm.imm 25#64)))

def p8573 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38089 38077 (Flapjack.WordRegImm.reg 38085)))

def p8574 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38093, 38081)]

def p8575 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38097 38093 (Flapjack.WordRegImm.imm 21#64)))

def p8576 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38101, 38093)]

def p8577 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38105 38101 (Flapjack.WordRegImm.imm 11#64)))

def p8578 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38109 38097 (Flapjack.WordRegImm.reg 38105)))

def p8579 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38113 38089 (Flapjack.WordRegImm.reg 38109)))

def p8580 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38117, 38101)]

def p8581 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38121 38117 (Flapjack.WordRegImm.imm 26#64)))

def p8582 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38125, 38117)]

def p8583 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38129 38125 (Flapjack.WordRegImm.imm 6#64)))

def p8584 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38133 38121 (Flapjack.WordRegImm.reg 38129)))

def p8585 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38137 38113 (Flapjack.WordRegImm.reg 38133)))

def p8586 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38141 38069 (Flapjack.WordRegImm.reg 38137)))

def p8587 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38145, 37801)]

def p8588 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38149 38141 (Flapjack.WordRegImm.reg 38145)))

def p8589 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 38153 18446744072865069933#64)

def p8590 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38157 38149 (Flapjack.WordRegImm.reg 38153)))

def p8591 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38165, 37921), (38161, 38157)]

def p8592 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38169 38161 (Flapjack.WordRegImm.reg 38165)))

def p8593 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38173 38169 (Flapjack.WordRegImm.imm 32#64)))

def p8594 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38177 38173 (Flapjack.WordRegImm.imm 32#64)))

def p8595 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38201, 38041), (38197, 38009), (38193, 37941), (38185, 37949), (38181, 38177)]

def p8596 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38205 38197 (Flapjack.WordRegImm.reg 38201)))

def p8597 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 38209 38193 (Flapjack.WordRegImm.reg 38205)))

def p8598 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38213, 38197)]

def p8599 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38217 38209 (Flapjack.WordRegImm.reg 38213)))

def p8600 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38221, 38201)]

def p8601 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38225 38221 (Flapjack.WordRegImm.imm 10#64)))

def p8602 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38229, 38221)]

def p8603 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38233 38229 (Flapjack.WordRegImm.imm 22#64)))

def p8604 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38237 38225 (Flapjack.WordRegImm.reg 38233)))

def p8605 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38241, 38229)]

def p8606 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38245 38241 (Flapjack.WordRegImm.imm 19#64)))

def p8607 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38249, 38241)]

def p8608 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38253 38249 (Flapjack.WordRegImm.imm 13#64)))

def p8609 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38257 38245 (Flapjack.WordRegImm.reg 38253)))

def p8610 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38261 38237 (Flapjack.WordRegImm.reg 38257)))

def p8611 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38265, 38249)]

def p8612 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38269 38265 (Flapjack.WordRegImm.imm 30#64)))

def p8613 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38273, 38265)]

def p8614 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38277 38273 (Flapjack.WordRegImm.imm 2#64)))

def p8615 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38281 38269 (Flapjack.WordRegImm.reg 38277)))

def p8616 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38285 38261 (Flapjack.WordRegImm.reg 38281)))

def p8617 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38289 38217 (Flapjack.WordRegImm.reg 38285)))

def p8618 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38293, 38161)]

def p8619 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38297 38289 (Flapjack.WordRegImm.reg 38293)))

def p8620 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38301 38297 (Flapjack.WordRegImm.imm 32#64)))

def p8621 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38305 38301 (Flapjack.WordRegImm.imm 32#64)))

def p8622 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38313, 38125), (38309, 38049)]

def p8623 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38317 38309 (Flapjack.WordRegImm.reg 38313)))

def p8624 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38321, 38181)]

def p8625 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 38325 38317 (Flapjack.WordRegImm.reg 38321)))

def p8626 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38329, 38309)]

def p8627 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38333 38325 (Flapjack.WordRegImm.reg 38329)))

def p8628 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38337, 38321)]

def p8629 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38341 38337 (Flapjack.WordRegImm.imm 7#64)))

def p8630 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38345, 38337)]

def p8631 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38349 38345 (Flapjack.WordRegImm.imm 25#64)))

def p8632 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38353 38341 (Flapjack.WordRegImm.reg 38349)))

def p8633 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38357, 38345)]

def p8634 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38361 38357 (Flapjack.WordRegImm.imm 21#64)))

def p8635 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38365, 38357)]

def p8636 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38369 38365 (Flapjack.WordRegImm.imm 11#64)))

def p8637 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38373 38361 (Flapjack.WordRegImm.reg 38369)))

def p8638 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38377 38353 (Flapjack.WordRegImm.reg 38373)))

def p8639 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38381, 38365)]

def p8640 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38385 38381 (Flapjack.WordRegImm.imm 26#64)))

def p8641 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38389, 38381)]

def p8642 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38393 38389 (Flapjack.WordRegImm.imm 6#64)))

def p8643 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38397 38385 (Flapjack.WordRegImm.reg 38393)))

def p8644 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38401 38377 (Flapjack.WordRegImm.reg 38397)))

def p8645 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38405 38333 (Flapjack.WordRegImm.reg 38401)))

def p8646 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38409, 38065)]

def p8647 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38413 38405 (Flapjack.WordRegImm.reg 38409)))

def p8648 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 38417 18446744072648113719#64)

def p8649 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38421 38413 (Flapjack.WordRegImm.reg 38417)))

def p8650 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38429, 38185), (38425, 38421)]

def p8651 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38433 38425 (Flapjack.WordRegImm.reg 38429)))

def p8652 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38437 38433 (Flapjack.WordRegImm.imm 32#64)))

def p8653 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38441 38437 (Flapjack.WordRegImm.imm 32#64)))

def p8654 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38465, 38305), (38461, 38273), (38457, 38205), (38449, 38213), (38445, 38441)]

def p8655 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38469 38461 (Flapjack.WordRegImm.reg 38465)))

def p8656 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 38473 38457 (Flapjack.WordRegImm.reg 38469)))

def p8657 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38477, 38461)]

def p8658 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38481 38473 (Flapjack.WordRegImm.reg 38477)))

def p8659 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38485, 38465)]

def p8660 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38489 38485 (Flapjack.WordRegImm.imm 10#64)))

def p8661 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38493, 38485)]

def p8662 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38497 38493 (Flapjack.WordRegImm.imm 22#64)))

def p8663 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38501 38489 (Flapjack.WordRegImm.reg 38497)))

def p8664 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38505, 38493)]

def p8665 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38509 38505 (Flapjack.WordRegImm.imm 19#64)))

def p8666 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38513, 38505)]

def p8667 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38517 38513 (Flapjack.WordRegImm.imm 13#64)))

def p8668 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38521 38509 (Flapjack.WordRegImm.reg 38517)))

def p8669 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38525 38501 (Flapjack.WordRegImm.reg 38521)))

def p8670 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38529, 38513)]

def p8671 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38533 38529 (Flapjack.WordRegImm.imm 30#64)))

def p8672 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38537, 38529)]

def p8673 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38541 38537 (Flapjack.WordRegImm.imm 2#64)))

def p8674 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38545 38533 (Flapjack.WordRegImm.reg 38541)))

def p8675 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38549 38525 (Flapjack.WordRegImm.reg 38545)))

def p8676 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38553 38481 (Flapjack.WordRegImm.reg 38549)))

def p8677 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38557, 38425)]

def p8678 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38561 38553 (Flapjack.WordRegImm.reg 38557)))

def p8679 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38565 38561 (Flapjack.WordRegImm.imm 32#64)))

def p8680 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38569 38565 (Flapjack.WordRegImm.imm 32#64)))

def p8681 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38577, 38389), (38573, 38313)]

def p8682 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38581 38573 (Flapjack.WordRegImm.reg 38577)))

def p8683 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38585, 38445)]

def p8684 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 38589 38581 (Flapjack.WordRegImm.reg 38585)))

def p8685 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38593, 38573)]

def p8686 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38597 38589 (Flapjack.WordRegImm.reg 38593)))

def p8687 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38601, 38585)]

def p8688 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38605 38601 (Flapjack.WordRegImm.imm 7#64)))

def p8689 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38609, 38601)]

def p8690 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38613 38609 (Flapjack.WordRegImm.imm 25#64)))

def p8691 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38617 38605 (Flapjack.WordRegImm.reg 38613)))

def p8692 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38621, 38609)]

def p8693 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38625 38621 (Flapjack.WordRegImm.imm 21#64)))

def p8694 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38629, 38621)]

def p8695 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38633 38629 (Flapjack.WordRegImm.imm 11#64)))

def p8696 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38637 38625 (Flapjack.WordRegImm.reg 38633)))

def p8697 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38641 38617 (Flapjack.WordRegImm.reg 38637)))

def p8698 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38645, 38629)]

def p8699 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38649 38645 (Flapjack.WordRegImm.imm 26#64)))

def p8700 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38653, 38645)]

def p8701 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38657 38653 (Flapjack.WordRegImm.imm 6#64)))

def p8702 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38661 38649 (Flapjack.WordRegImm.reg 38657)))

def p8703 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38665 38641 (Flapjack.WordRegImm.reg 38661)))

def p8704 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38669 38597 (Flapjack.WordRegImm.reg 38665)))

def p8705 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38673, 38329)]

def p8706 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38677 38669 (Flapjack.WordRegImm.reg 38673)))

def p8707 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 38681 18446744071618771930#64)

def p8708 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38685 38677 (Flapjack.WordRegImm.reg 38681)))

def p8709 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38693, 38449), (38689, 38685)]

def p8710 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38697 38689 (Flapjack.WordRegImm.reg 38693)))

def p8711 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38701 38697 (Flapjack.WordRegImm.imm 32#64)))

def p8712 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38705 38701 (Flapjack.WordRegImm.imm 32#64)))

def p8713 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38729, 38569), (38725, 38537), (38721, 38469), (38713, 38477), (38709, 38705)]

def p8714 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38733 38725 (Flapjack.WordRegImm.reg 38729)))

def p8715 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 38737 38721 (Flapjack.WordRegImm.reg 38733)))

def p8716 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38741, 38725)]

def p8717 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38745 38737 (Flapjack.WordRegImm.reg 38741)))

def p8718 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38749, 38729)]

def p8719 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38753 38749 (Flapjack.WordRegImm.imm 10#64)))

def p8720 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38757, 38749)]

def p8721 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38761 38757 (Flapjack.WordRegImm.imm 22#64)))

def p8722 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38765 38753 (Flapjack.WordRegImm.reg 38761)))

def p8723 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38769, 38757)]

def p8724 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38773 38769 (Flapjack.WordRegImm.imm 19#64)))

def p8725 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38777, 38769)]

def p8726 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38781 38777 (Flapjack.WordRegImm.imm 13#64)))

def p8727 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38785 38773 (Flapjack.WordRegImm.reg 38781)))

def p8728 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38789 38765 (Flapjack.WordRegImm.reg 38785)))

def p8729 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38793, 38777)]

def p8730 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38797 38793 (Flapjack.WordRegImm.imm 30#64)))

def p8731 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38801, 38793)]

def p8732 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38805 38801 (Flapjack.WordRegImm.imm 2#64)))

def p8733 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38809 38797 (Flapjack.WordRegImm.reg 38805)))

def p8734 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38813 38789 (Flapjack.WordRegImm.reg 38809)))

def p8735 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38817 38745 (Flapjack.WordRegImm.reg 38813)))

def p8736 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38821, 38689)]

def p8737 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38825 38817 (Flapjack.WordRegImm.reg 38821)))

def p8738 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38829 38825 (Flapjack.WordRegImm.imm 32#64)))

def p8739 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38833 38829 (Flapjack.WordRegImm.imm 32#64)))

def p8740 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38841, 38653), (38837, 38577)]

def p8741 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38845 38837 (Flapjack.WordRegImm.reg 38841)))

def p8742 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38849, 38709)]

def p8743 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 38853 38845 (Flapjack.WordRegImm.reg 38849)))

def p8744 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38857, 38837)]

def p8745 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38861 38853 (Flapjack.WordRegImm.reg 38857)))

def p8746 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38865, 38849)]

def p8747 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38869 38865 (Flapjack.WordRegImm.imm 7#64)))

def p8748 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38873, 38865)]

def p8749 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38877 38873 (Flapjack.WordRegImm.imm 25#64)))

def p8750 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38881 38869 (Flapjack.WordRegImm.reg 38877)))

def p8751 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38885, 38873)]

def p8752 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38889 38885 (Flapjack.WordRegImm.imm 21#64)))

def p8753 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38893, 38885)]

def p8754 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38897 38893 (Flapjack.WordRegImm.imm 11#64)))

def p8755 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38901 38889 (Flapjack.WordRegImm.reg 38897)))

def p8756 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38905 38881 (Flapjack.WordRegImm.reg 38901)))

def p8757 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38909, 38893)]

def p8758 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38913 38909 (Flapjack.WordRegImm.imm 26#64)))

def p8759 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38917, 38909)]

def p8760 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38921 38917 (Flapjack.WordRegImm.imm 6#64)))

def p8761 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 38925 38913 (Flapjack.WordRegImm.reg 38921)))

def p8762 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38929 38905 (Flapjack.WordRegImm.reg 38925)))

def p8763 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38933 38861 (Flapjack.WordRegImm.reg 38929)))

def p8764 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38937, 38593)]

def p8765 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38941 38933 (Flapjack.WordRegImm.reg 38937)))

def p8766 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 38945 18446744073093555043#64)

def p8767 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38949 38941 (Flapjack.WordRegImm.reg 38945)))

def p8768 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38957, 38713), (38953, 38949)]

def p8769 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 38961 38953 (Flapjack.WordRegImm.reg 38957)))

def p8770 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 38965 38961 (Flapjack.WordRegImm.imm 32#64)))

def p8771 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 38969 38965 (Flapjack.WordRegImm.imm 32#64)))

def p8772 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(38993, 38833), (38989, 38801), (38985, 38733), (38977, 38741), (38973, 38969)]

def p8773 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 38997 38989 (Flapjack.WordRegImm.reg 38993)))

def p8774 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 39001 38985 (Flapjack.WordRegImm.reg 38997)))

def p8775 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39005, 38989)]

def p8776 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39009 39001 (Flapjack.WordRegImm.reg 39005)))

def p8777 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39013, 38993)]

def p8778 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39017 39013 (Flapjack.WordRegImm.imm 10#64)))

def p8779 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39021, 39013)]

def p8780 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39025 39021 (Flapjack.WordRegImm.imm 22#64)))

def p8781 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39029 39017 (Flapjack.WordRegImm.reg 39025)))

def p8782 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39033, 39021)]

def p8783 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39037 39033 (Flapjack.WordRegImm.imm 19#64)))

def p8784 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39041, 39033)]

def p8785 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39045 39041 (Flapjack.WordRegImm.imm 13#64)))

def p8786 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39049 39037 (Flapjack.WordRegImm.reg 39045)))

def p8787 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39053 39029 (Flapjack.WordRegImm.reg 39049)))

def p8788 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39057, 39041)]

def p8789 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39061 39057 (Flapjack.WordRegImm.imm 30#64)))

def p8790 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39065, 39057)]

def p8791 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39069 39065 (Flapjack.WordRegImm.imm 2#64)))

def p8792 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39073 39061 (Flapjack.WordRegImm.reg 39069)))

def p8793 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39077 39053 (Flapjack.WordRegImm.reg 39073)))

def p8794 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39081 39009 (Flapjack.WordRegImm.reg 39077)))

def p8795 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39085, 38953)]

def p8796 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 39089 39081 (Flapjack.WordRegImm.reg 39085)))

def p8797 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39093 39089 (Flapjack.WordRegImm.imm 32#64)))

def p8798 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39097 39093 (Flapjack.WordRegImm.imm 32#64)))

def p8799 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39105, 38917), (39101, 38841)]

def p8800 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39109 39101 (Flapjack.WordRegImm.reg 39105)))

def p8801 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39113, 38973)]

def p8802 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 39117 39109 (Flapjack.WordRegImm.reg 39113)))

def p8803 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39121, 39101)]

def p8804 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 39125 39117 (Flapjack.WordRegImm.reg 39121)))

def p8805 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39129, 39113)]

def p8806 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 39133 39129 (Flapjack.WordRegImm.imm 7#64)))

def p8807 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(39137, 39129)]

def p8808 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 39141 39137 (Flapjack.WordRegImm.imm 25#64)))

def p8809 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 39145 39133 (Flapjack.WordRegImm.reg 39141)))

def parts : List (WordLangProgHOL (BitVec 64)) := [p8310, p8311, p8312, p8313, p8314, p8315, p8316, p8317, p8318, p8319, p8320, p8321, p8322, p8323, p8324, p8325, p8326, p8327, p8328, p8329, p8330, p8331, p8332, p8333, p8334, p8335, p8336, p8337, p8338, p8339, p8340, p8341, p8342, p8343, p8344, p8345, p8346, p8347, p8348, p8349, p8350, p8351, p8352, p8353, p8354, p8355, p8356, p8357, p8358, p8359, p8360, p8361, p8362, p8363, p8364, p8365, p8366, p8367, p8368, p8369, p8370, p8371, p8372, p8373, p8374, p8375, p8376, p8377, p8378, p8379, p8380, p8381, p8382, p8383, p8384, p8385, p8386, p8387, p8388, p8389, p8390, p8391, p8392, p8393, p8394, p8395, p8396, p8397, p8398, p8399, p8400, p8401, p8402, p8403, p8404, p8405, p8406, p8407, p8408, p8409, p8410, p8411, p8412, p8413, p8414, p8415, p8416, p8417, p8418, p8419, p8420, p8421, p8422, p8423, p8424, p8425, p8426, p8427, p8428, p8429, p8430, p8431, p8432, p8433, p8434, p8435, p8436, p8437, p8438, p8439, p8440, p8441, p8442, p8443, p8444, p8445, p8446, p8447, p8448, p8449, p8450, p8451, p8452, p8453, p8454, p8455, p8456, p8457, p8458, p8459, p8460, p8461, p8462, p8463, p8464, p8465, p8466, p8467, p8468, p8469, p8470, p8471, p8472, p8473, p8474, p8475, p8476, p8477, p8478, p8479, p8480, p8481, p8482, p8483, p8484, p8485, p8486, p8487, p8488, p8489, p8490, p8491, p8492, p8493, p8494, p8495, p8496, p8497, p8498, p8499, p8500, p8501, p8502, p8503, p8504, p8505, p8506, p8507, p8508, p8509, p8510, p8511, p8512, p8513, p8514, p8515, p8516, p8517, p8518, p8519, p8520, p8521, p8522, p8523, p8524, p8525, p8526, p8527, p8528, p8529, p8530, p8531, p8532, p8533, p8534, p8535, p8536, p8537, p8538, p8539, p8540, p8541, p8542, p8543, p8544, p8545, p8546, p8547, p8548, p8549, p8550, p8551, p8552, p8553, p8554, p8555, p8556, p8557, p8558, p8559, p8560, p8561, p8562, p8563, p8564, p8565, p8566, p8567, p8568, p8569, p8570, p8571, p8572, p8573, p8574, p8575, p8576, p8577, p8578, p8579, p8580, p8581, p8582, p8583, p8584, p8585, p8586, p8587, p8588, p8589, p8590, p8591, p8592, p8593, p8594, p8595, p8596, p8597, p8598, p8599, p8600, p8601, p8602, p8603, p8604, p8605, p8606, p8607, p8608, p8609, p8610, p8611, p8612, p8613, p8614, p8615, p8616, p8617, p8618, p8619, p8620, p8621, p8622, p8623, p8624, p8625, p8626, p8627, p8628, p8629, p8630, p8631, p8632, p8633, p8634, p8635, p8636, p8637, p8638, p8639, p8640, p8641, p8642, p8643, p8644, p8645, p8646, p8647, p8648, p8649, p8650, p8651, p8652, p8653, p8654, p8655, p8656, p8657, p8658, p8659, p8660, p8661, p8662, p8663, p8664, p8665, p8666, p8667, p8668, p8669, p8670, p8671, p8672, p8673, p8674, p8675, p8676, p8677, p8678, p8679, p8680, p8681, p8682, p8683, p8684, p8685, p8686, p8687, p8688, p8689, p8690, p8691, p8692, p8693, p8694, p8695, p8696, p8697, p8698, p8699, p8700, p8701, p8702, p8703, p8704, p8705, p8706, p8707, p8708, p8709, p8710, p8711, p8712, p8713, p8714, p8715, p8716, p8717, p8718, p8719, p8720, p8721, p8722, p8723, p8724, p8725, p8726, p8727, p8728, p8729, p8730, p8731, p8732, p8733, p8734, p8735, p8736, p8737, p8738, p8739, p8740, p8741, p8742, p8743, p8744, p8745, p8746, p8747, p8748, p8749, p8750, p8751, p8752, p8753, p8754, p8755, p8756, p8757, p8758, p8759, p8760, p8761, p8762, p8763, p8764, p8765, p8766, p8767, p8768, p8769, p8770, p8771, p8772, p8773, p8774, p8775, p8776, p8777, p8778, p8779, p8780, p8781, p8782, p8783, p8784, p8785, p8786, p8787, p8788, p8789, p8790, p8791, p8792, p8793, p8794, p8795, p8796, p8797, p8798, p8799, p8800, p8801, p8802, p8803, p8804, p8805, p8806, p8807, p8808, p8809]

wave8_kernel_reduce trees := parts.map (fun p => WordAlloc.getClashTree p [])
wave8_kernel_reduce colPs := parts.map (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)))
wave8_kernel_reduce stackOk := colPs.all (everyStackVarHOL stackPred)
wave8_kernel_reduce forcedOk := parts.all (fun p => (WordAlloc.getForced riscvConfig p []).all (forcedPred (oracle154.getD .ln)))
wave8_kernel_reduce progs := parts.map (transform oracle154)
wave8_kernel_reduce maxV := maxListProg progs
wave8_kernel_reduce comp := compList riscvConfig false (22, 13, 12) progs (.nil, 136)

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154.Block02
