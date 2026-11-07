import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154Support

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154.Block16
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition Chunk05Stack151 Chunk05Word154

def p1310 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6005 5997 (Flapjack.WordRegImm.reg 6001)))

def p1311 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6013, 5617), (6009, 6005)]

def p1312 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6017 6009 (Flapjack.WordRegImm.reg 6013)))

def p1313 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6021 6017 (Flapjack.WordRegImm.imm 32#64)))

def p1314 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6025 6021 (Flapjack.WordRegImm.imm 32#64)))

def p1315 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6049, 5737), (6045, 5705), (6041, 5637), (6033, 5645), (6029, 6025)]

def p1316 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6053 6045 (Flapjack.WordRegImm.reg 6049)))

def p1317 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 6057 6041 (Flapjack.WordRegImm.reg 6053)))

def p1318 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6061, 6045)]

def p1319 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6065 6057 (Flapjack.WordRegImm.reg 6061)))

def p1320 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6069, 6049)]

def p1321 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6073 6069 (Flapjack.WordRegImm.imm 10#64)))

def p1322 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6077, 6069)]

def p1323 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6081 6077 (Flapjack.WordRegImm.imm 22#64)))

def p1324 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6085 6073 (Flapjack.WordRegImm.reg 6081)))

def p1325 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6089, 6077)]

def p1326 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6093 6089 (Flapjack.WordRegImm.imm 19#64)))

def p1327 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6097, 6089)]

def p1328 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6101 6097 (Flapjack.WordRegImm.imm 13#64)))

def p1329 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6105 6093 (Flapjack.WordRegImm.reg 6101)))

def p1330 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6109 6085 (Flapjack.WordRegImm.reg 6105)))

def p1331 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6113, 6097)]

def p1332 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6117 6113 (Flapjack.WordRegImm.imm 30#64)))

def p1333 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6121, 6113)]

def p1334 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6125 6121 (Flapjack.WordRegImm.imm 2#64)))

def p1335 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6129 6117 (Flapjack.WordRegImm.reg 6125)))

def p1336 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6133 6109 (Flapjack.WordRegImm.reg 6129)))

def p1337 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6137 6065 (Flapjack.WordRegImm.reg 6133)))

def p1338 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6141, 6009)]

def p1339 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6145 6137 (Flapjack.WordRegImm.reg 6141)))

def p1340 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6149 6145 (Flapjack.WordRegImm.imm 32#64)))

def p1341 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6153 6149 (Flapjack.WordRegImm.imm 32#64)))

def p1342 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6157, 5469)]

def p1343 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6161 6157 (Flapjack.WordRegImm.imm 10#64)))

def p1344 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6165, 6157)]

def p1345 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6169 6165 (Flapjack.WordRegImm.imm 13#64)))

def p1346 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6173, 6165)]

def p1347 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6177 6173 (Flapjack.WordRegImm.imm 19#64)))

def p1348 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6181 6169 (Flapjack.WordRegImm.reg 6177)))

def p1349 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6185 6161 (Flapjack.WordRegImm.reg 6181)))

def p1350 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6189, 6173)]

def p1351 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6193 6189 (Flapjack.WordRegImm.imm 15#64)))

def p1352 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6197, 6189)]

def p1353 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6201 6197 (Flapjack.WordRegImm.imm 17#64)))

def p1354 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6205 6193 (Flapjack.WordRegImm.reg 6201)))

def p1355 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6209 6185 (Flapjack.WordRegImm.reg 6205)))

def p1356 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6213, 4109)]

def p1357 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6217 6209 (Flapjack.WordRegImm.reg 6213)))

def p1358 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6221, 1949)]

def p1359 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6225 6221 (Flapjack.WordRegImm.imm 3#64)))

def p1360 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6229, 6221)]

def p1361 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6233 6229 (Flapjack.WordRegImm.imm 14#64)))

def p1362 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6237, 6229)]

def p1363 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6241 6237 (Flapjack.WordRegImm.imm 18#64)))

def p1364 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6245 6233 (Flapjack.WordRegImm.reg 6241)))

def p1365 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6249 6225 (Flapjack.WordRegImm.reg 6245)))

def p1366 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6253, 6237)]

def p1367 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6257 6253 (Flapjack.WordRegImm.imm 25#64)))

def p1368 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6261, 6253)]

def p1369 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6265 6261 (Flapjack.WordRegImm.imm 7#64)))

def p1370 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6269 6257 (Flapjack.WordRegImm.reg 6265)))

def p1371 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6273 6249 (Flapjack.WordRegImm.reg 6269)))

def p1372 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6277 6217 (Flapjack.WordRegImm.reg 6273)))

def p1373 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6281, 5845)]

def p1374 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6285 6277 (Flapjack.WordRegImm.reg 6281)))

def p1375 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6289 6285 (Flapjack.WordRegImm.imm 32#64)))

def p1376 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6293 6289 (Flapjack.WordRegImm.imm 32#64)))

def p1377 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6309, 5973), (6305, 5893), (6301, 6293)]

def p1378 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6313 6305 (Flapjack.WordRegImm.reg 6309)))

def p1379 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6317, 6029)]

def p1380 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 6321 6313 (Flapjack.WordRegImm.reg 6317)))

def p1381 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6325, 6305)]

def p1382 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6329 6321 (Flapjack.WordRegImm.reg 6325)))

def p1383 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6333 6301 (Flapjack.WordRegImm.reg 6329)))

def p1384 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6337, 6317)]

def p1385 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6341 6337 (Flapjack.WordRegImm.imm 7#64)))

def p1386 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6345, 6337)]

def p1387 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6349 6345 (Flapjack.WordRegImm.imm 25#64)))

def p1388 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6353 6341 (Flapjack.WordRegImm.reg 6349)))

def p1389 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6357, 6345)]

def p1390 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6361 6357 (Flapjack.WordRegImm.imm 21#64)))

def p1391 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6365, 6357)]

def p1392 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6369 6365 (Flapjack.WordRegImm.imm 11#64)))

def p1393 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6373 6361 (Flapjack.WordRegImm.reg 6369)))

def p1394 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6377 6353 (Flapjack.WordRegImm.reg 6373)))

def p1395 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6381, 6365)]

def p1396 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6385 6381 (Flapjack.WordRegImm.imm 26#64)))

def p1397 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6389, 6381)]

def p1398 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6393 6389 (Flapjack.WordRegImm.imm 6#64)))

def p1399 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6397 6385 (Flapjack.WordRegImm.reg 6393)))

def p1400 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6401 6377 (Flapjack.WordRegImm.reg 6397)))

def p1401 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6405 6333 (Flapjack.WordRegImm.reg 6401)))

def p1402 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6409, 5909)]

def p1403 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6413 6405 (Flapjack.WordRegImm.reg 6409)))

def p1404 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 6417 18446744073436809094#64)

def p1405 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6421 6413 (Flapjack.WordRegImm.reg 6417)))

def p1406 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6429, 6033), (6425, 6421)]

def p1407 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6433 6425 (Flapjack.WordRegImm.reg 6429)))

def p1408 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6437 6433 (Flapjack.WordRegImm.imm 32#64)))

def p1409 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6441 6437 (Flapjack.WordRegImm.imm 32#64)))

def p1410 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6465, 6153), (6461, 6121), (6457, 6053), (6449, 6061), (6445, 6441)]

def p1411 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6469 6461 (Flapjack.WordRegImm.reg 6465)))

def p1412 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 6473 6457 (Flapjack.WordRegImm.reg 6469)))

def p1413 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6477, 6461)]

def p1414 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6481 6473 (Flapjack.WordRegImm.reg 6477)))

def p1415 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6485, 6465)]

def p1416 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6489 6485 (Flapjack.WordRegImm.imm 10#64)))

def p1417 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6493, 6485)]

def p1418 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6497 6493 (Flapjack.WordRegImm.imm 22#64)))

def p1419 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6501 6489 (Flapjack.WordRegImm.reg 6497)))

def p1420 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6505, 6493)]

def p1421 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6509 6505 (Flapjack.WordRegImm.imm 19#64)))

def p1422 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6513, 6505)]

def p1423 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6517 6513 (Flapjack.WordRegImm.imm 13#64)))

def p1424 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6521 6509 (Flapjack.WordRegImm.reg 6517)))

def p1425 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6525 6501 (Flapjack.WordRegImm.reg 6521)))

def p1426 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6529, 6513)]

def p1427 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6533 6529 (Flapjack.WordRegImm.imm 30#64)))

def p1428 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6537, 6529)]

def p1429 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6541 6537 (Flapjack.WordRegImm.imm 2#64)))

def p1430 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6545 6533 (Flapjack.WordRegImm.reg 6541)))

def p1431 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6549 6525 (Flapjack.WordRegImm.reg 6545)))

def p1432 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6553 6481 (Flapjack.WordRegImm.reg 6549)))

def p1433 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6557, 6425)]

def p1434 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6561 6553 (Flapjack.WordRegImm.reg 6557)))

def p1435 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6565 6561 (Flapjack.WordRegImm.imm 32#64)))

def p1436 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6569 6565 (Flapjack.WordRegImm.imm 32#64)))

def p1437 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6573, 5885)]

def p1438 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6577 6573 (Flapjack.WordRegImm.imm 10#64)))

def p1439 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6581, 6573)]

def p1440 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6585 6581 (Flapjack.WordRegImm.imm 13#64)))

def p1441 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6589, 6581)]

def p1442 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6593 6589 (Flapjack.WordRegImm.imm 19#64)))

def p1443 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6597 6585 (Flapjack.WordRegImm.reg 6593)))

def p1444 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6601 6577 (Flapjack.WordRegImm.reg 6597)))

def p1445 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6605, 6589)]

def p1446 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6609 6605 (Flapjack.WordRegImm.imm 15#64)))

def p1447 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6613, 6605)]

def p1448 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6617 6613 (Flapjack.WordRegImm.imm 17#64)))

def p1449 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6621 6609 (Flapjack.WordRegImm.reg 6617)))

def p1450 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6625 6601 (Flapjack.WordRegImm.reg 6621)))

def p1451 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6629, 4381)]

def p1452 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6633 6625 (Flapjack.WordRegImm.reg 6629)))

def p1453 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6637, 2213)]

def p1454 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6641 6637 (Flapjack.WordRegImm.imm 3#64)))

def p1455 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6645, 6637)]

def p1456 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6649 6645 (Flapjack.WordRegImm.imm 14#64)))

def p1457 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6653, 6645)]

def p1458 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6657 6653 (Flapjack.WordRegImm.imm 18#64)))

def p1459 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6661 6649 (Flapjack.WordRegImm.reg 6657)))

def p1460 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6665 6641 (Flapjack.WordRegImm.reg 6661)))

def p1461 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6669, 6653)]

def p1462 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6673 6669 (Flapjack.WordRegImm.imm 25#64)))

def p1463 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6677, 6669)]

def p1464 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6681 6677 (Flapjack.WordRegImm.imm 7#64)))

def p1465 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6685 6673 (Flapjack.WordRegImm.reg 6681)))

def p1466 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6689 6665 (Flapjack.WordRegImm.reg 6685)))

def p1467 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6693 6633 (Flapjack.WordRegImm.reg 6689)))

def p1468 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6697, 6261)]

def p1469 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6701 6693 (Flapjack.WordRegImm.reg 6697)))

def p1470 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6705 6701 (Flapjack.WordRegImm.imm 32#64)))

def p1471 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6709 6705 (Flapjack.WordRegImm.imm 32#64)))

def p1472 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6725, 6389), (6721, 6309), (6717, 6709)]

def p1473 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6729 6721 (Flapjack.WordRegImm.reg 6725)))

def p1474 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6733, 6445)]

def p1475 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 6737 6729 (Flapjack.WordRegImm.reg 6733)))

def p1476 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6741, 6721)]

def p1477 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6745 6737 (Flapjack.WordRegImm.reg 6741)))

def p1478 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6749 6717 (Flapjack.WordRegImm.reg 6745)))

def p1479 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6753, 6733)]

def p1480 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6757 6753 (Flapjack.WordRegImm.imm 7#64)))

def p1481 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6761, 6753)]

def p1482 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6765 6761 (Flapjack.WordRegImm.imm 25#64)))

def p1483 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6769 6757 (Flapjack.WordRegImm.reg 6765)))

def p1484 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6773, 6761)]

def p1485 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6777 6773 (Flapjack.WordRegImm.imm 21#64)))

def p1486 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6781, 6773)]

def p1487 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6785 6781 (Flapjack.WordRegImm.imm 11#64)))

def p1488 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6789 6777 (Flapjack.WordRegImm.reg 6785)))

def p1489 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6793 6769 (Flapjack.WordRegImm.reg 6789)))

def p1490 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6797, 6781)]

def p1491 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6801 6797 (Flapjack.WordRegImm.imm 26#64)))

def p1492 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6805, 6797)]

def p1493 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6809 6805 (Flapjack.WordRegImm.imm 6#64)))

def p1494 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6813 6801 (Flapjack.WordRegImm.reg 6809)))

def p1495 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6817 6793 (Flapjack.WordRegImm.reg 6813)))

def p1496 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6821 6749 (Flapjack.WordRegImm.reg 6817)))

def p1497 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6825, 6325)]

def p1498 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6829 6821 (Flapjack.WordRegImm.reg 6825)))

def p1499 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 6833 264347078#64)

def p1500 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6837 6829 (Flapjack.WordRegImm.reg 6833)))

def p1501 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6845, 6449), (6841, 6837)]

def p1502 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6849 6841 (Flapjack.WordRegImm.reg 6845)))

def p1503 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6853 6849 (Flapjack.WordRegImm.imm 32#64)))

def p1504 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6857 6853 (Flapjack.WordRegImm.imm 32#64)))

def p1505 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6881, 6569), (6877, 6537), (6873, 6469), (6865, 6477), (6861, 6857)]

def p1506 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6885 6877 (Flapjack.WordRegImm.reg 6881)))

def p1507 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 6889 6873 (Flapjack.WordRegImm.reg 6885)))

def p1508 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6893, 6877)]

def p1509 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6897 6889 (Flapjack.WordRegImm.reg 6893)))

def p1510 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6901, 6881)]

def p1511 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6905 6901 (Flapjack.WordRegImm.imm 10#64)))

def p1512 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6909, 6901)]

def p1513 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6913 6909 (Flapjack.WordRegImm.imm 22#64)))

def p1514 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6917 6905 (Flapjack.WordRegImm.reg 6913)))

def p1515 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6921, 6909)]

def p1516 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6925 6921 (Flapjack.WordRegImm.imm 19#64)))

def p1517 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6929, 6921)]

def p1518 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6933 6929 (Flapjack.WordRegImm.imm 13#64)))

def p1519 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6937 6925 (Flapjack.WordRegImm.reg 6933)))

def p1520 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6941 6917 (Flapjack.WordRegImm.reg 6937)))

def p1521 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6945, 6929)]

def p1522 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6949 6945 (Flapjack.WordRegImm.imm 30#64)))

def p1523 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6953, 6945)]

def p1524 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6957 6953 (Flapjack.WordRegImm.imm 2#64)))

def p1525 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6961 6949 (Flapjack.WordRegImm.reg 6957)))

def p1526 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 6965 6941 (Flapjack.WordRegImm.reg 6961)))

def p1527 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6969 6897 (Flapjack.WordRegImm.reg 6965)))

def p1528 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6973, 6841)]

def p1529 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 6977 6969 (Flapjack.WordRegImm.reg 6973)))

def p1530 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 6981 6977 (Flapjack.WordRegImm.imm 32#64)))

def p1531 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6985 6981 (Flapjack.WordRegImm.imm 32#64)))

def p1532 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6989, 6301)]

def p1533 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 6993 6989 (Flapjack.WordRegImm.imm 10#64)))

def p1534 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(6997, 6989)]

def p1535 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7001 6997 (Flapjack.WordRegImm.imm 13#64)))

def p1536 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7005, 6997)]

def p1537 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7009 7005 (Flapjack.WordRegImm.imm 19#64)))

def p1538 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7013 7001 (Flapjack.WordRegImm.reg 7009)))

def p1539 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7017 6993 (Flapjack.WordRegImm.reg 7013)))

def p1540 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7021, 7005)]

def p1541 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7025 7021 (Flapjack.WordRegImm.imm 15#64)))

def p1542 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7029, 7021)]

def p1543 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7033 7029 (Flapjack.WordRegImm.imm 17#64)))

def p1544 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7037 7025 (Flapjack.WordRegImm.reg 7033)))

def p1545 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7041 7017 (Flapjack.WordRegImm.reg 7037)))

def p1546 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7045, 4653)]

def p1547 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7049 7041 (Flapjack.WordRegImm.reg 7045)))

def p1548 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7053, 2477)]

def p1549 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7057 7053 (Flapjack.WordRegImm.imm 3#64)))

def p1550 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7061, 7053)]

def p1551 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7065 7061 (Flapjack.WordRegImm.imm 14#64)))

def p1552 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7069, 7061)]

def p1553 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7073 7069 (Flapjack.WordRegImm.imm 18#64)))

def p1554 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7077 7065 (Flapjack.WordRegImm.reg 7073)))

def p1555 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7081 7057 (Flapjack.WordRegImm.reg 7077)))

def p1556 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7085, 7069)]

def p1557 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7089 7085 (Flapjack.WordRegImm.imm 25#64)))

def p1558 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7093, 7085)]

def p1559 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7097 7093 (Flapjack.WordRegImm.imm 7#64)))

def p1560 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7101 7089 (Flapjack.WordRegImm.reg 7097)))

def p1561 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7105 7081 (Flapjack.WordRegImm.reg 7101)))

def p1562 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7109 7049 (Flapjack.WordRegImm.reg 7105)))

def p1563 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7113, 6677)]

def p1564 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7117 7109 (Flapjack.WordRegImm.reg 7113)))

def p1565 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7121 7117 (Flapjack.WordRegImm.imm 32#64)))

def p1566 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7125 7121 (Flapjack.WordRegImm.imm 32#64)))

def p1567 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7141, 6805), (7137, 6725), (7133, 7125)]

def p1568 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7145 7137 (Flapjack.WordRegImm.reg 7141)))

def p1569 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7149, 6861)]

def p1570 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 7153 7145 (Flapjack.WordRegImm.reg 7149)))

def p1571 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7157, 7137)]

def p1572 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7161 7153 (Flapjack.WordRegImm.reg 7157)))

def p1573 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7165 7133 (Flapjack.WordRegImm.reg 7161)))

def p1574 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7169, 7149)]

def p1575 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7173 7169 (Flapjack.WordRegImm.imm 7#64)))

def p1576 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7177, 7169)]

def p1577 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7181 7177 (Flapjack.WordRegImm.imm 25#64)))

def p1578 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7185 7173 (Flapjack.WordRegImm.reg 7181)))

def p1579 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7189, 7177)]

def p1580 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7193 7189 (Flapjack.WordRegImm.imm 21#64)))

def p1581 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7197, 7189)]

def p1582 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7201 7197 (Flapjack.WordRegImm.imm 11#64)))

def p1583 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7205 7193 (Flapjack.WordRegImm.reg 7201)))

def p1584 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7209 7185 (Flapjack.WordRegImm.reg 7205)))

def p1585 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7213, 7197)]

def p1586 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7217 7213 (Flapjack.WordRegImm.imm 26#64)))

def p1587 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7221, 7213)]

def p1588 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7225 7221 (Flapjack.WordRegImm.imm 6#64)))

def p1589 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7229 7217 (Flapjack.WordRegImm.reg 7225)))

def p1590 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7233 7209 (Flapjack.WordRegImm.reg 7229)))

def p1591 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7237 7165 (Flapjack.WordRegImm.reg 7233)))

def p1592 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7241, 6741)]

def p1593 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7245 7237 (Flapjack.WordRegImm.reg 7241)))

def p1594 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 7249 604807628#64)

def p1595 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7253 7245 (Flapjack.WordRegImm.reg 7249)))

def p1596 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7261, 6865), (7257, 7253)]

def p1597 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7265 7257 (Flapjack.WordRegImm.reg 7261)))

def p1598 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7269 7265 (Flapjack.WordRegImm.imm 32#64)))

def p1599 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7273 7269 (Flapjack.WordRegImm.imm 32#64)))

def p1600 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7297, 6985), (7293, 6953), (7289, 6885), (7281, 6893), (7277, 7273)]

def p1601 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7301 7293 (Flapjack.WordRegImm.reg 7297)))

def p1602 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 7305 7289 (Flapjack.WordRegImm.reg 7301)))

def p1603 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7309, 7293)]

def p1604 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7313 7305 (Flapjack.WordRegImm.reg 7309)))

def p1605 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7317, 7297)]

def p1606 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7321 7317 (Flapjack.WordRegImm.imm 10#64)))

def p1607 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7325, 7317)]

def p1608 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7329 7325 (Flapjack.WordRegImm.imm 22#64)))

def p1609 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7333 7321 (Flapjack.WordRegImm.reg 7329)))

def p1610 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7337, 7325)]

def p1611 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7341 7337 (Flapjack.WordRegImm.imm 19#64)))

def p1612 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7345, 7337)]

def p1613 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7349 7345 (Flapjack.WordRegImm.imm 13#64)))

def p1614 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7353 7341 (Flapjack.WordRegImm.reg 7349)))

def p1615 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7357 7333 (Flapjack.WordRegImm.reg 7353)))

def p1616 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7361, 7345)]

def p1617 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7365 7361 (Flapjack.WordRegImm.imm 30#64)))

def p1618 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7369, 7361)]

def p1619 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7373 7369 (Flapjack.WordRegImm.imm 2#64)))

def p1620 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7377 7365 (Flapjack.WordRegImm.reg 7373)))

def p1621 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7381 7357 (Flapjack.WordRegImm.reg 7377)))

def p1622 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7385 7313 (Flapjack.WordRegImm.reg 7381)))

def p1623 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7389, 7257)]

def p1624 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7393 7385 (Flapjack.WordRegImm.reg 7389)))

def p1625 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7397 7393 (Flapjack.WordRegImm.imm 32#64)))

def p1626 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7401 7397 (Flapjack.WordRegImm.imm 32#64)))

def p1627 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7405, 6717)]

def p1628 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7409 7405 (Flapjack.WordRegImm.imm 10#64)))

def p1629 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7413, 7405)]

def p1630 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7417 7413 (Flapjack.WordRegImm.imm 13#64)))

def p1631 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7421, 7413)]

def p1632 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7425 7421 (Flapjack.WordRegImm.imm 19#64)))

def p1633 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7429 7417 (Flapjack.WordRegImm.reg 7425)))

def p1634 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7433 7409 (Flapjack.WordRegImm.reg 7429)))

def p1635 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7437, 7421)]

def p1636 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7441 7437 (Flapjack.WordRegImm.imm 15#64)))

def p1637 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7445, 7437)]

def p1638 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7449 7445 (Flapjack.WordRegImm.imm 17#64)))

def p1639 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7453 7441 (Flapjack.WordRegImm.reg 7449)))

def p1640 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7457 7433 (Flapjack.WordRegImm.reg 7453)))

def p1641 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7461, 4925)]

def p1642 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7465 7457 (Flapjack.WordRegImm.reg 7461)))

def p1643 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7469, 2749)]

def p1644 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7473 7469 (Flapjack.WordRegImm.imm 3#64)))

def p1645 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7477, 7469)]

def p1646 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7481 7477 (Flapjack.WordRegImm.imm 14#64)))

def p1647 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7485, 7477)]

def p1648 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7489 7485 (Flapjack.WordRegImm.imm 18#64)))

def p1649 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7493 7481 (Flapjack.WordRegImm.reg 7489)))

def p1650 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7497 7473 (Flapjack.WordRegImm.reg 7493)))

def p1651 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7501, 7485)]

def p1652 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7505 7501 (Flapjack.WordRegImm.imm 25#64)))

def p1653 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7509, 7501)]

def p1654 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7513 7509 (Flapjack.WordRegImm.imm 7#64)))

def p1655 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7517 7505 (Flapjack.WordRegImm.reg 7513)))

def p1656 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7521 7497 (Flapjack.WordRegImm.reg 7517)))

def p1657 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7525 7465 (Flapjack.WordRegImm.reg 7521)))

def p1658 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7529, 7093)]

def p1659 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7533 7525 (Flapjack.WordRegImm.reg 7529)))

def p1660 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7537 7533 (Flapjack.WordRegImm.imm 32#64)))

def p1661 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7541 7537 (Flapjack.WordRegImm.imm 32#64)))

def p1662 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7557, 7221), (7553, 7141), (7549, 7541)]

def p1663 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7561 7553 (Flapjack.WordRegImm.reg 7557)))

def p1664 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7565, 7277)]

def p1665 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 7569 7561 (Flapjack.WordRegImm.reg 7565)))

def p1666 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7573, 7553)]

def p1667 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7577 7569 (Flapjack.WordRegImm.reg 7573)))

def p1668 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7581 7549 (Flapjack.WordRegImm.reg 7577)))

def p1669 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7585, 7565)]

def p1670 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7589 7585 (Flapjack.WordRegImm.imm 7#64)))

def p1671 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7593, 7585)]

def p1672 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7597 7593 (Flapjack.WordRegImm.imm 25#64)))

def p1673 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7601 7589 (Flapjack.WordRegImm.reg 7597)))

def p1674 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7605, 7593)]

def p1675 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7609 7605 (Flapjack.WordRegImm.imm 21#64)))

def p1676 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7613, 7605)]

def p1677 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7617 7613 (Flapjack.WordRegImm.imm 11#64)))

def p1678 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7621 7609 (Flapjack.WordRegImm.reg 7617)))

def p1679 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7625 7601 (Flapjack.WordRegImm.reg 7621)))

def p1680 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7629, 7613)]

def p1681 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7633 7629 (Flapjack.WordRegImm.imm 26#64)))

def p1682 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7637, 7629)]

def p1683 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7641 7637 (Flapjack.WordRegImm.imm 6#64)))

def p1684 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7645 7633 (Flapjack.WordRegImm.reg 7641)))

def p1685 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7649 7625 (Flapjack.WordRegImm.reg 7645)))

def p1686 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7653 7581 (Flapjack.WordRegImm.reg 7649)))

def p1687 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7657, 7157)]

def p1688 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7661 7653 (Flapjack.WordRegImm.reg 7657)))

def p1689 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 7665 770255983#64)

def p1690 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7669 7661 (Flapjack.WordRegImm.reg 7665)))

def p1691 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7677, 7281), (7673, 7669)]

def p1692 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7681 7673 (Flapjack.WordRegImm.reg 7677)))

def p1693 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7685 7681 (Flapjack.WordRegImm.imm 32#64)))

def p1694 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7689 7685 (Flapjack.WordRegImm.imm 32#64)))

def p1695 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7713, 7401), (7709, 7369), (7705, 7301), (7697, 7309), (7693, 7689)]

def p1696 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7717 7709 (Flapjack.WordRegImm.reg 7713)))

def p1697 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 7721 7705 (Flapjack.WordRegImm.reg 7717)))

def p1698 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7725, 7709)]

def p1699 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7729 7721 (Flapjack.WordRegImm.reg 7725)))

def p1700 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7733, 7713)]

def p1701 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7737 7733 (Flapjack.WordRegImm.imm 10#64)))

def p1702 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7741, 7733)]

def p1703 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7745 7741 (Flapjack.WordRegImm.imm 22#64)))

def p1704 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7749 7737 (Flapjack.WordRegImm.reg 7745)))

def p1705 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7753, 7741)]

def p1706 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7757 7753 (Flapjack.WordRegImm.imm 19#64)))

def p1707 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7761, 7753)]

def p1708 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7765 7761 (Flapjack.WordRegImm.imm 13#64)))

def p1709 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7769 7757 (Flapjack.WordRegImm.reg 7765)))

def p1710 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7773 7749 (Flapjack.WordRegImm.reg 7769)))

def p1711 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7777, 7761)]

def p1712 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7781 7777 (Flapjack.WordRegImm.imm 30#64)))

def p1713 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7785, 7777)]

def p1714 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7789 7785 (Flapjack.WordRegImm.imm 2#64)))

def p1715 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7793 7781 (Flapjack.WordRegImm.reg 7789)))

def p1716 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7797 7773 (Flapjack.WordRegImm.reg 7793)))

def p1717 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7801 7729 (Flapjack.WordRegImm.reg 7797)))

def p1718 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7805, 7673)]

def p1719 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7809 7801 (Flapjack.WordRegImm.reg 7805)))

def p1720 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7813 7809 (Flapjack.WordRegImm.imm 32#64)))

def p1721 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7817 7813 (Flapjack.WordRegImm.imm 32#64)))

def p1722 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7821, 7133)]

def p1723 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7825 7821 (Flapjack.WordRegImm.imm 10#64)))

def p1724 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7829, 7821)]

def p1725 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7833 7829 (Flapjack.WordRegImm.imm 13#64)))

def p1726 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7837, 7829)]

def p1727 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7841 7837 (Flapjack.WordRegImm.imm 19#64)))

def p1728 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7845 7833 (Flapjack.WordRegImm.reg 7841)))

def p1729 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7849 7825 (Flapjack.WordRegImm.reg 7845)))

def p1730 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7853, 7837)]

def p1731 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7857 7853 (Flapjack.WordRegImm.imm 15#64)))

def p1732 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7861, 7853)]

def p1733 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7865 7861 (Flapjack.WordRegImm.imm 17#64)))

def p1734 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7869 7857 (Flapjack.WordRegImm.reg 7865)))

def p1735 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7873 7849 (Flapjack.WordRegImm.reg 7869)))

def p1736 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7877, 5781)]

def p1737 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7881 7873 (Flapjack.WordRegImm.reg 7877)))

def p1738 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7885, 3021)]

def p1739 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7889 7885 (Flapjack.WordRegImm.imm 3#64)))

def p1740 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7893, 7885)]

def p1741 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7897 7893 (Flapjack.WordRegImm.imm 14#64)))

def p1742 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7901, 7893)]

def p1743 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7905 7901 (Flapjack.WordRegImm.imm 18#64)))

def p1744 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7909 7897 (Flapjack.WordRegImm.reg 7905)))

def p1745 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7913 7889 (Flapjack.WordRegImm.reg 7909)))

def p1746 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7917, 7901)]

def p1747 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7921 7917 (Flapjack.WordRegImm.imm 25#64)))

def p1748 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7925, 7917)]

def p1749 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7929 7925 (Flapjack.WordRegImm.imm 7#64)))

def p1750 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 7933 7921 (Flapjack.WordRegImm.reg 7929)))

def p1751 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7937 7913 (Flapjack.WordRegImm.reg 7933)))

def p1752 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7941 7881 (Flapjack.WordRegImm.reg 7937)))

def p1753 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7945, 7509)]

def p1754 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7949 7941 (Flapjack.WordRegImm.reg 7945)))

def p1755 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 7953 7949 (Flapjack.WordRegImm.imm 32#64)))

def p1756 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 7957 7953 (Flapjack.WordRegImm.imm 32#64)))

def p1757 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7973, 7637), (7969, 7557), (7965, 7957)]

def p1758 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7977 7969 (Flapjack.WordRegImm.reg 7973)))

def p1759 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7981, 7693)]

def p1760 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 7985 7977 (Flapjack.WordRegImm.reg 7981)))

def p1761 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(7989, 7969)]

def p1762 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 7993 7985 (Flapjack.WordRegImm.reg 7989)))

def p1763 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 7997 7965 (Flapjack.WordRegImm.reg 7993)))

def p1764 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8001, 7981)]

def p1765 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 8005 8001 (Flapjack.WordRegImm.imm 7#64)))

def p1766 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8009, 8001)]

def p1767 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 8013 8009 (Flapjack.WordRegImm.imm 25#64)))

def p1768 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 8017 8005 (Flapjack.WordRegImm.reg 8013)))

def p1769 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8021, 8009)]

def p1770 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 8025 8021 (Flapjack.WordRegImm.imm 21#64)))

def p1771 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8029, 8021)]

def p1772 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 8033 8029 (Flapjack.WordRegImm.imm 11#64)))

def p1773 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 8037 8025 (Flapjack.WordRegImm.reg 8033)))

def p1774 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 8041 8017 (Flapjack.WordRegImm.reg 8037)))

def p1775 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8045, 8029)]

def p1776 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 8049 8045 (Flapjack.WordRegImm.imm 26#64)))

def p1777 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8053, 8045)]

def p1778 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 8057 8053 (Flapjack.WordRegImm.imm 6#64)))

def p1779 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 8061 8049 (Flapjack.WordRegImm.reg 8057)))

def p1780 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 8065 8041 (Flapjack.WordRegImm.reg 8061)))

def p1781 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 8069 7997 (Flapjack.WordRegImm.reg 8065)))

def p1782 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8073, 7573)]

def p1783 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 8077 8069 (Flapjack.WordRegImm.reg 8073)))

def p1784 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 8081 1249150122#64)

def p1785 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 8085 8077 (Flapjack.WordRegImm.reg 8081)))

def p1786 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8093, 7697), (8089, 8085)]

def p1787 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 8097 8089 (Flapjack.WordRegImm.reg 8093)))

def p1788 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 8101 8097 (Flapjack.WordRegImm.imm 32#64)))

def p1789 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 8105 8101 (Flapjack.WordRegImm.imm 32#64)))

def p1790 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8129, 7817), (8125, 7785), (8121, 7717), (8113, 7725), (8109, 8105)]

def p1791 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 8133 8125 (Flapjack.WordRegImm.reg 8129)))

def p1792 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 8137 8121 (Flapjack.WordRegImm.reg 8133)))

def p1793 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8141, 8125)]

def p1794 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 8145 8137 (Flapjack.WordRegImm.reg 8141)))

def p1795 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8149, 8129)]

def p1796 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 8153 8149 (Flapjack.WordRegImm.imm 10#64)))

def p1797 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8157, 8149)]

def p1798 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 8161 8157 (Flapjack.WordRegImm.imm 22#64)))

def p1799 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 8165 8153 (Flapjack.WordRegImm.reg 8161)))

def p1800 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8169, 8157)]

def p1801 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 8173 8169 (Flapjack.WordRegImm.imm 19#64)))

def p1802 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8177, 8169)]

def p1803 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 8181 8177 (Flapjack.WordRegImm.imm 13#64)))

def p1804 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 8185 8173 (Flapjack.WordRegImm.reg 8181)))

def p1805 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 8189 8165 (Flapjack.WordRegImm.reg 8185)))

def p1806 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8193, 8177)]

def p1807 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 8197 8193 (Flapjack.WordRegImm.imm 30#64)))

def p1808 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(8201, 8193)]

def p1809 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 8205 8201 (Flapjack.WordRegImm.imm 2#64)))

def parts : List (WordLangProgHOL (BitVec 64)) := [p1310, p1311, p1312, p1313, p1314, p1315, p1316, p1317, p1318, p1319, p1320, p1321, p1322, p1323, p1324, p1325, p1326, p1327, p1328, p1329, p1330, p1331, p1332, p1333, p1334, p1335, p1336, p1337, p1338, p1339, p1340, p1341, p1342, p1343, p1344, p1345, p1346, p1347, p1348, p1349, p1350, p1351, p1352, p1353, p1354, p1355, p1356, p1357, p1358, p1359, p1360, p1361, p1362, p1363, p1364, p1365, p1366, p1367, p1368, p1369, p1370, p1371, p1372, p1373, p1374, p1375, p1376, p1377, p1378, p1379, p1380, p1381, p1382, p1383, p1384, p1385, p1386, p1387, p1388, p1389, p1390, p1391, p1392, p1393, p1394, p1395, p1396, p1397, p1398, p1399, p1400, p1401, p1402, p1403, p1404, p1405, p1406, p1407, p1408, p1409, p1410, p1411, p1412, p1413, p1414, p1415, p1416, p1417, p1418, p1419, p1420, p1421, p1422, p1423, p1424, p1425, p1426, p1427, p1428, p1429, p1430, p1431, p1432, p1433, p1434, p1435, p1436, p1437, p1438, p1439, p1440, p1441, p1442, p1443, p1444, p1445, p1446, p1447, p1448, p1449, p1450, p1451, p1452, p1453, p1454, p1455, p1456, p1457, p1458, p1459, p1460, p1461, p1462, p1463, p1464, p1465, p1466, p1467, p1468, p1469, p1470, p1471, p1472, p1473, p1474, p1475, p1476, p1477, p1478, p1479, p1480, p1481, p1482, p1483, p1484, p1485, p1486, p1487, p1488, p1489, p1490, p1491, p1492, p1493, p1494, p1495, p1496, p1497, p1498, p1499, p1500, p1501, p1502, p1503, p1504, p1505, p1506, p1507, p1508, p1509, p1510, p1511, p1512, p1513, p1514, p1515, p1516, p1517, p1518, p1519, p1520, p1521, p1522, p1523, p1524, p1525, p1526, p1527, p1528, p1529, p1530, p1531, p1532, p1533, p1534, p1535, p1536, p1537, p1538, p1539, p1540, p1541, p1542, p1543, p1544, p1545, p1546, p1547, p1548, p1549, p1550, p1551, p1552, p1553, p1554, p1555, p1556, p1557, p1558, p1559, p1560, p1561, p1562, p1563, p1564, p1565, p1566, p1567, p1568, p1569, p1570, p1571, p1572, p1573, p1574, p1575, p1576, p1577, p1578, p1579, p1580, p1581, p1582, p1583, p1584, p1585, p1586, p1587, p1588, p1589, p1590, p1591, p1592, p1593, p1594, p1595, p1596, p1597, p1598, p1599, p1600, p1601, p1602, p1603, p1604, p1605, p1606, p1607, p1608, p1609, p1610, p1611, p1612, p1613, p1614, p1615, p1616, p1617, p1618, p1619, p1620, p1621, p1622, p1623, p1624, p1625, p1626, p1627, p1628, p1629, p1630, p1631, p1632, p1633, p1634, p1635, p1636, p1637, p1638, p1639, p1640, p1641, p1642, p1643, p1644, p1645, p1646, p1647, p1648, p1649, p1650, p1651, p1652, p1653, p1654, p1655, p1656, p1657, p1658, p1659, p1660, p1661, p1662, p1663, p1664, p1665, p1666, p1667, p1668, p1669, p1670, p1671, p1672, p1673, p1674, p1675, p1676, p1677, p1678, p1679, p1680, p1681, p1682, p1683, p1684, p1685, p1686, p1687, p1688, p1689, p1690, p1691, p1692, p1693, p1694, p1695, p1696, p1697, p1698, p1699, p1700, p1701, p1702, p1703, p1704, p1705, p1706, p1707, p1708, p1709, p1710, p1711, p1712, p1713, p1714, p1715, p1716, p1717, p1718, p1719, p1720, p1721, p1722, p1723, p1724, p1725, p1726, p1727, p1728, p1729, p1730, p1731, p1732, p1733, p1734, p1735, p1736, p1737, p1738, p1739, p1740, p1741, p1742, p1743, p1744, p1745, p1746, p1747, p1748, p1749, p1750, p1751, p1752, p1753, p1754, p1755, p1756, p1757, p1758, p1759, p1760, p1761, p1762, p1763, p1764, p1765, p1766, p1767, p1768, p1769, p1770, p1771, p1772, p1773, p1774, p1775, p1776, p1777, p1778, p1779, p1780, p1781, p1782, p1783, p1784, p1785, p1786, p1787, p1788, p1789, p1790, p1791, p1792, p1793, p1794, p1795, p1796, p1797, p1798, p1799, p1800, p1801, p1802, p1803, p1804, p1805, p1806, p1807, p1808, p1809]

wave8_kernel_reduce trees := parts.map (fun p => WordAlloc.getClashTree p [])
wave8_kernel_reduce colPs := parts.map (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)))
wave8_kernel_reduce stackOk := colPs.all (everyStackVarHOL stackPred)
wave8_kernel_reduce forcedOk := parts.all (fun p => (WordAlloc.getForced riscvConfig p []).all (forcedPred (oracle154.getD .ln)))
wave8_kernel_reduce progs := parts.map (transform oracle154)
wave8_kernel_reduce maxV := maxListProg progs
wave8_kernel_reduce comp := compList riscvConfig false (22, 13, 12) progs (.nil, 136)

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154.Block16
