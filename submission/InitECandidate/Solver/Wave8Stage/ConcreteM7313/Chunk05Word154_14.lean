import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154Support

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154.Block14
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition Chunk05Stack151 Chunk05Word154

def p2310 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10389, 10381)]

def p2311 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10393 10389 (Flapjack.WordRegImm.imm 14#64)))

def p2312 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10397, 10389)]

def p2313 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10401 10397 (Flapjack.WordRegImm.imm 18#64)))

def p2314 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10405 10393 (Flapjack.WordRegImm.reg 10401)))

def p2315 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10409 10385 (Flapjack.WordRegImm.reg 10405)))

def p2316 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10413, 10397)]

def p2317 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10417 10413 (Flapjack.WordRegImm.imm 25#64)))

def p2318 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10421, 10413)]

def p2319 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10425 10421 (Flapjack.WordRegImm.imm 7#64)))

def p2320 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10429 10417 (Flapjack.WordRegImm.reg 10425)))

def p2321 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10433 10409 (Flapjack.WordRegImm.reg 10429)))

def p2322 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10437 10377 (Flapjack.WordRegImm.reg 10433)))

def p2323 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10441, 10005)]

def p2324 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10445 10437 (Flapjack.WordRegImm.reg 10441)))

def p2325 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10449 10445 (Flapjack.WordRegImm.imm 32#64)))

def p2326 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10453 10449 (Flapjack.WordRegImm.imm 32#64)))

def p2327 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10469, 10133), (10465, 10053), (10461, 10453)]

def p2328 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10473 10465 (Flapjack.WordRegImm.reg 10469)))

def p2329 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10477, 10189)]

def p2330 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 10481 10473 (Flapjack.WordRegImm.reg 10477)))

def p2331 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10485, 10465)]

def p2332 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10489 10481 (Flapjack.WordRegImm.reg 10485)))

def p2333 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10493 10461 (Flapjack.WordRegImm.reg 10489)))

def p2334 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10497, 10477)]

def p2335 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10501 10497 (Flapjack.WordRegImm.imm 7#64)))

def p2336 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10505, 10497)]

def p2337 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10509 10505 (Flapjack.WordRegImm.imm 25#64)))

def p2338 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10513 10501 (Flapjack.WordRegImm.reg 10509)))

def p2339 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10517, 10505)]

def p2340 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10521 10517 (Flapjack.WordRegImm.imm 21#64)))

def p2341 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10525, 10517)]

def p2342 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10529 10525 (Flapjack.WordRegImm.imm 11#64)))

def p2343 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10533 10521 (Flapjack.WordRegImm.reg 10529)))

def p2344 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10537 10513 (Flapjack.WordRegImm.reg 10533)))

def p2345 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10541, 10525)]

def p2346 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10545 10541 (Flapjack.WordRegImm.imm 26#64)))

def p2347 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10549, 10541)]

def p2348 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10553 10549 (Flapjack.WordRegImm.imm 6#64)))

def p2349 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10557 10545 (Flapjack.WordRegImm.reg 10553)))

def p2350 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10561 10537 (Flapjack.WordRegImm.reg 10557)))

def p2351 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10565 10493 (Flapjack.WordRegImm.reg 10561)))

def p2352 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10569, 10069)]

def p2353 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10573 10565 (Flapjack.WordRegImm.reg 10569)))

def p2354 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 10577 18446744072624897991#64)

def p2355 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10581 10573 (Flapjack.WordRegImm.reg 10577)))

def p2356 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10589, 10193), (10585, 10581)]

def p2357 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10593 10585 (Flapjack.WordRegImm.reg 10589)))

def p2358 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10597 10593 (Flapjack.WordRegImm.imm 32#64)))

def p2359 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10601 10597 (Flapjack.WordRegImm.imm 32#64)))

def p2360 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10625, 10313), (10621, 10281), (10617, 10213), (10609, 10221), (10605, 10601)]

def p2361 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10629 10621 (Flapjack.WordRegImm.reg 10625)))

def p2362 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 10633 10617 (Flapjack.WordRegImm.reg 10629)))

def p2363 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10637, 10621)]

def p2364 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10641 10633 (Flapjack.WordRegImm.reg 10637)))

def p2365 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10645, 10625)]

def p2366 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10649 10645 (Flapjack.WordRegImm.imm 10#64)))

def p2367 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10653, 10645)]

def p2368 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10657 10653 (Flapjack.WordRegImm.imm 22#64)))

def p2369 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10661 10649 (Flapjack.WordRegImm.reg 10657)))

def p2370 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10665, 10653)]

def p2371 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10669 10665 (Flapjack.WordRegImm.imm 19#64)))

def p2372 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10673, 10665)]

def p2373 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10677 10673 (Flapjack.WordRegImm.imm 13#64)))

def p2374 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10681 10669 (Flapjack.WordRegImm.reg 10677)))

def p2375 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10685 10661 (Flapjack.WordRegImm.reg 10681)))

def p2376 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10689, 10673)]

def p2377 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10693 10689 (Flapjack.WordRegImm.imm 30#64)))

def p2378 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10697, 10689)]

def p2379 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10701 10697 (Flapjack.WordRegImm.imm 2#64)))

def p2380 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10705 10693 (Flapjack.WordRegImm.reg 10701)))

def p2381 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10709 10685 (Flapjack.WordRegImm.reg 10705)))

def p2382 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10713 10641 (Flapjack.WordRegImm.reg 10709)))

def p2383 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10717, 10585)]

def p2384 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10721 10713 (Flapjack.WordRegImm.reg 10717)))

def p2385 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10725 10721 (Flapjack.WordRegImm.imm 32#64)))

def p2386 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10729 10725 (Flapjack.WordRegImm.imm 32#64)))

def p2387 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10733, 10045)]

def p2388 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10737 10733 (Flapjack.WordRegImm.imm 10#64)))

def p2389 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10741, 10733)]

def p2390 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10745 10741 (Flapjack.WordRegImm.imm 13#64)))

def p2391 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10749, 10741)]

def p2392 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10753 10749 (Flapjack.WordRegImm.imm 19#64)))

def p2393 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10757 10745 (Flapjack.WordRegImm.reg 10753)))

def p2394 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10761 10737 (Flapjack.WordRegImm.reg 10757)))

def p2395 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10765, 10749)]

def p2396 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10769 10765 (Flapjack.WordRegImm.imm 15#64)))

def p2397 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10773, 10765)]

def p2398 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10777 10773 (Flapjack.WordRegImm.imm 17#64)))

def p2399 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10781 10769 (Flapjack.WordRegImm.reg 10777)))

def p2400 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10785 10761 (Flapjack.WordRegImm.reg 10781)))

def p2401 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10789, 8693)]

def p2402 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10793 10785 (Flapjack.WordRegImm.reg 10789)))

def p2403 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10797, 7461)]

def p2404 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10801 10797 (Flapjack.WordRegImm.imm 3#64)))

def p2405 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10805, 10797)]

def p2406 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10809 10805 (Flapjack.WordRegImm.imm 14#64)))

def p2407 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10813, 10805)]

def p2408 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10817 10813 (Flapjack.WordRegImm.imm 18#64)))

def p2409 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10821 10809 (Flapjack.WordRegImm.reg 10817)))

def p2410 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10825 10801 (Flapjack.WordRegImm.reg 10821)))

def p2411 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10829, 10813)]

def p2412 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10833 10829 (Flapjack.WordRegImm.imm 25#64)))

def p2413 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10837, 10829)]

def p2414 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10841 10837 (Flapjack.WordRegImm.imm 7#64)))

def p2415 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10845 10833 (Flapjack.WordRegImm.reg 10841)))

def p2416 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10849 10825 (Flapjack.WordRegImm.reg 10845)))

def p2417 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10853 10793 (Flapjack.WordRegImm.reg 10849)))

def p2418 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10857, 10421)]

def p2419 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10861 10853 (Flapjack.WordRegImm.reg 10857)))

def p2420 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10865 10861 (Flapjack.WordRegImm.imm 32#64)))

def p2421 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10869 10865 (Flapjack.WordRegImm.imm 32#64)))

def p2422 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10885, 10549), (10881, 10469), (10877, 10869)]

def p2423 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10889 10881 (Flapjack.WordRegImm.reg 10885)))

def p2424 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10893, 10605)]

def p2425 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 10897 10889 (Flapjack.WordRegImm.reg 10893)))

def p2426 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10901, 10881)]

def p2427 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10905 10897 (Flapjack.WordRegImm.reg 10901)))

def p2428 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10909 10877 (Flapjack.WordRegImm.reg 10905)))

def p2429 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10913, 10893)]

def p2430 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10917 10913 (Flapjack.WordRegImm.imm 7#64)))

def p2431 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10921, 10913)]

def p2432 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10925 10921 (Flapjack.WordRegImm.imm 25#64)))

def p2433 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10929 10917 (Flapjack.WordRegImm.reg 10925)))

def p2434 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10933, 10921)]

def p2435 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10937 10933 (Flapjack.WordRegImm.imm 21#64)))

def p2436 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10941, 10933)]

def p2437 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10945 10941 (Flapjack.WordRegImm.imm 11#64)))

def p2438 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10949 10937 (Flapjack.WordRegImm.reg 10945)))

def p2439 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10953 10929 (Flapjack.WordRegImm.reg 10949)))

def p2440 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10957, 10941)]

def p2441 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 10961 10957 (Flapjack.WordRegImm.imm 26#64)))

def p2442 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10965, 10957)]

def p2443 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 10969 10965 (Flapjack.WordRegImm.imm 6#64)))

def p2444 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 10973 10961 (Flapjack.WordRegImm.reg 10969)))

def p2445 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 10977 10953 (Flapjack.WordRegImm.reg 10973)))

def p2446 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10981 10909 (Flapjack.WordRegImm.reg 10977)))

def p2447 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(10985, 10485)]

def p2448 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10989 10981 (Flapjack.WordRegImm.reg 10985)))

def p2449 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 10993 18446744072751156211#64)

def p2450 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 10997 10989 (Flapjack.WordRegImm.reg 10993)))

def p2451 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11005, 10609), (11001, 10997)]

def p2452 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11009 11001 (Flapjack.WordRegImm.reg 11005)))

def p2453 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11013 11009 (Flapjack.WordRegImm.imm 32#64)))

def p2454 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11017 11013 (Flapjack.WordRegImm.imm 32#64)))

def p2455 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11041, 10729), (11037, 10697), (11033, 10629), (11025, 10637), (11021, 11017)]

def p2456 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11045 11037 (Flapjack.WordRegImm.reg 11041)))

def p2457 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 11049 11033 (Flapjack.WordRegImm.reg 11045)))

def p2458 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11053, 11037)]

def p2459 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11057 11049 (Flapjack.WordRegImm.reg 11053)))

def p2460 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11061, 11041)]

def p2461 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11065 11061 (Flapjack.WordRegImm.imm 10#64)))

def p2462 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11069, 11061)]

def p2463 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11073 11069 (Flapjack.WordRegImm.imm 22#64)))

def p2464 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11077 11065 (Flapjack.WordRegImm.reg 11073)))

def p2465 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11081, 11069)]

def p2466 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11085 11081 (Flapjack.WordRegImm.imm 19#64)))

def p2467 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11089, 11081)]

def p2468 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11093 11089 (Flapjack.WordRegImm.imm 13#64)))

def p2469 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11097 11085 (Flapjack.WordRegImm.reg 11093)))

def p2470 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11101 11077 (Flapjack.WordRegImm.reg 11097)))

def p2471 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11105, 11089)]

def p2472 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11109 11105 (Flapjack.WordRegImm.imm 30#64)))

def p2473 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11113, 11105)]

def p2474 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11117 11113 (Flapjack.WordRegImm.imm 2#64)))

def p2475 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11121 11109 (Flapjack.WordRegImm.reg 11117)))

def p2476 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11125 11101 (Flapjack.WordRegImm.reg 11121)))

def p2477 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11129 11057 (Flapjack.WordRegImm.reg 11125)))

def p2478 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11133, 11001)]

def p2479 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11137 11129 (Flapjack.WordRegImm.reg 11133)))

def p2480 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11141 11137 (Flapjack.WordRegImm.imm 32#64)))

def p2481 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11145 11141 (Flapjack.WordRegImm.imm 32#64)))

def p2482 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11149, 10461)]

def p2483 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11153 11149 (Flapjack.WordRegImm.imm 10#64)))

def p2484 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11157, 11149)]

def p2485 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11161 11157 (Flapjack.WordRegImm.imm 13#64)))

def p2486 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11165, 11157)]

def p2487 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11169 11165 (Flapjack.WordRegImm.imm 19#64)))

def p2488 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11173 11161 (Flapjack.WordRegImm.reg 11169)))

def p2489 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11177 11153 (Flapjack.WordRegImm.reg 11173)))

def p2490 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11181, 11165)]

def p2491 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11185 11181 (Flapjack.WordRegImm.imm 15#64)))

def p2492 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11189, 11181)]

def p2493 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11193 11189 (Flapjack.WordRegImm.imm 17#64)))

def p2494 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11197 11185 (Flapjack.WordRegImm.reg 11193)))

def p2495 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11201 11177 (Flapjack.WordRegImm.reg 11197)))

def p2496 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11205, 9109)]

def p2497 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11209 11201 (Flapjack.WordRegImm.reg 11205)))

def p2498 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11213, 7877)]

def p2499 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11217 11213 (Flapjack.WordRegImm.imm 3#64)))

def p2500 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11221, 11213)]

def p2501 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11225 11221 (Flapjack.WordRegImm.imm 14#64)))

def p2502 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11229, 11221)]

def p2503 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11233 11229 (Flapjack.WordRegImm.imm 18#64)))

def p2504 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11237 11225 (Flapjack.WordRegImm.reg 11233)))

def p2505 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11241 11217 (Flapjack.WordRegImm.reg 11237)))

def p2506 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11245, 11229)]

def p2507 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11249 11245 (Flapjack.WordRegImm.imm 25#64)))

def p2508 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11253, 11245)]

def p2509 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11257 11253 (Flapjack.WordRegImm.imm 7#64)))

def p2510 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11261 11249 (Flapjack.WordRegImm.reg 11257)))

def p2511 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11265 11241 (Flapjack.WordRegImm.reg 11261)))

def p2512 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11269 11209 (Flapjack.WordRegImm.reg 11265)))

def p2513 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11273, 10837)]

def p2514 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11277 11269 (Flapjack.WordRegImm.reg 11273)))

def p2515 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11281 11277 (Flapjack.WordRegImm.imm 32#64)))

def p2516 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11285 11281 (Flapjack.WordRegImm.imm 32#64)))

def p2517 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11301, 10965), (11297, 10885), (11293, 11285)]

def p2518 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11305 11297 (Flapjack.WordRegImm.reg 11301)))

def p2519 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11309, 11021)]

def p2520 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 11313 11305 (Flapjack.WordRegImm.reg 11309)))

def p2521 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11317, 11297)]

def p2522 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11321 11313 (Flapjack.WordRegImm.reg 11317)))

def p2523 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11325 11293 (Flapjack.WordRegImm.reg 11321)))

def p2524 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11329, 11309)]

def p2525 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11333 11329 (Flapjack.WordRegImm.imm 7#64)))

def p2526 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11337, 11329)]

def p2527 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11341 11337 (Flapjack.WordRegImm.imm 25#64)))

def p2528 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11345 11333 (Flapjack.WordRegImm.reg 11341)))

def p2529 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11349, 11337)]

def p2530 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11353 11349 (Flapjack.WordRegImm.imm 21#64)))

def p2531 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11357, 11349)]

def p2532 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11361 11357 (Flapjack.WordRegImm.imm 11#64)))

def p2533 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11365 11353 (Flapjack.WordRegImm.reg 11361)))

def p2534 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11369 11345 (Flapjack.WordRegImm.reg 11365)))

def p2535 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11373, 11357)]

def p2536 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11377 11373 (Flapjack.WordRegImm.imm 26#64)))

def p2537 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11381, 11373)]

def p2538 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11385 11381 (Flapjack.WordRegImm.imm 6#64)))

def p2539 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11389 11377 (Flapjack.WordRegImm.reg 11385)))

def p2540 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11393 11369 (Flapjack.WordRegImm.reg 11389)))

def p2541 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11397 11325 (Flapjack.WordRegImm.reg 11393)))

def p2542 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11401, 10901)]

def p2543 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11405 11397 (Flapjack.WordRegImm.reg 11401)))

def p2544 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 11409 18446744072999113031#64)

def p2545 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11413 11405 (Flapjack.WordRegImm.reg 11409)))

def p2546 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11421, 11025), (11417, 11413)]

def p2547 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11425 11417 (Flapjack.WordRegImm.reg 11421)))

def p2548 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11429 11425 (Flapjack.WordRegImm.imm 32#64)))

def p2549 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11433 11429 (Flapjack.WordRegImm.imm 32#64)))

def p2550 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11457, 11145), (11453, 11113), (11449, 11045), (11441, 11053), (11437, 11433)]

def p2551 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11461 11453 (Flapjack.WordRegImm.reg 11457)))

def p2552 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 11465 11449 (Flapjack.WordRegImm.reg 11461)))

def p2553 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11469, 11453)]

def p2554 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11473 11465 (Flapjack.WordRegImm.reg 11469)))

def p2555 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11477, 11457)]

def p2556 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11481 11477 (Flapjack.WordRegImm.imm 10#64)))

def p2557 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11485, 11477)]

def p2558 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11489 11485 (Flapjack.WordRegImm.imm 22#64)))

def p2559 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11493 11481 (Flapjack.WordRegImm.reg 11489)))

def p2560 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11497, 11485)]

def p2561 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11501 11497 (Flapjack.WordRegImm.imm 19#64)))

def p2562 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11505, 11497)]

def p2563 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11509 11505 (Flapjack.WordRegImm.imm 13#64)))

def p2564 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11513 11501 (Flapjack.WordRegImm.reg 11509)))

def p2565 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11517 11493 (Flapjack.WordRegImm.reg 11513)))

def p2566 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11521, 11505)]

def p2567 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11525 11521 (Flapjack.WordRegImm.imm 30#64)))

def p2568 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11529, 11521)]

def p2569 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11533 11529 (Flapjack.WordRegImm.imm 2#64)))

def p2570 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11537 11525 (Flapjack.WordRegImm.reg 11533)))

def p2571 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11541 11517 (Flapjack.WordRegImm.reg 11537)))

def p2572 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11545 11473 (Flapjack.WordRegImm.reg 11541)))

def p2573 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11549, 11417)]

def p2574 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11553 11545 (Flapjack.WordRegImm.reg 11549)))

def p2575 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11557 11553 (Flapjack.WordRegImm.imm 32#64)))

def p2576 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11561 11557 (Flapjack.WordRegImm.imm 32#64)))

def p2577 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11565, 10877)]

def p2578 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11569 11565 (Flapjack.WordRegImm.imm 10#64)))

def p2579 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11573, 11565)]

def p2580 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11577 11573 (Flapjack.WordRegImm.imm 13#64)))

def p2581 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11581, 11573)]

def p2582 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11585 11581 (Flapjack.WordRegImm.imm 19#64)))

def p2583 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11589 11577 (Flapjack.WordRegImm.reg 11585)))

def p2584 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11593 11569 (Flapjack.WordRegImm.reg 11589)))

def p2585 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11597, 11581)]

def p2586 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11601 11597 (Flapjack.WordRegImm.imm 15#64)))

def p2587 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11605, 11597)]

def p2588 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11609 11605 (Flapjack.WordRegImm.imm 17#64)))

def p2589 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11613 11601 (Flapjack.WordRegImm.reg 11609)))

def p2590 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11617 11593 (Flapjack.WordRegImm.reg 11613)))

def p2591 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11621, 9525)]

def p2592 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11625 11617 (Flapjack.WordRegImm.reg 11621)))

def p2593 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11629, 8293)]

def p2594 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11633 11629 (Flapjack.WordRegImm.imm 3#64)))

def p2595 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11637, 11629)]

def p2596 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11641 11637 (Flapjack.WordRegImm.imm 14#64)))

def p2597 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11645, 11637)]

def p2598 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11649 11645 (Flapjack.WordRegImm.imm 18#64)))

def p2599 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11653 11641 (Flapjack.WordRegImm.reg 11649)))

def p2600 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11657 11633 (Flapjack.WordRegImm.reg 11653)))

def p2601 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11661, 11645)]

def p2602 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11665 11661 (Flapjack.WordRegImm.imm 25#64)))

def p2603 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11669, 11661)]

def p2604 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11673 11669 (Flapjack.WordRegImm.imm 7#64)))

def p2605 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11677 11665 (Flapjack.WordRegImm.reg 11673)))

def p2606 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11681 11657 (Flapjack.WordRegImm.reg 11677)))

def p2607 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11685 11625 (Flapjack.WordRegImm.reg 11681)))

def p2608 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11689, 11253)]

def p2609 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11693 11685 (Flapjack.WordRegImm.reg 11689)))

def p2610 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11697 11693 (Flapjack.WordRegImm.imm 32#64)))

def p2611 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11701 11697 (Flapjack.WordRegImm.imm 32#64)))

def p2612 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11717, 11381), (11713, 11301), (11709, 11701)]

def p2613 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11721 11713 (Flapjack.WordRegImm.reg 11717)))

def p2614 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11725, 11437)]

def p2615 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 11729 11721 (Flapjack.WordRegImm.reg 11725)))

def p2616 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11733, 11713)]

def p2617 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11737 11729 (Flapjack.WordRegImm.reg 11733)))

def p2618 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11741 11709 (Flapjack.WordRegImm.reg 11737)))

def p2619 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11745, 11725)]

def p2620 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11749 11745 (Flapjack.WordRegImm.imm 7#64)))

def p2621 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11753, 11745)]

def p2622 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11757 11753 (Flapjack.WordRegImm.imm 25#64)))

def p2623 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11761 11749 (Flapjack.WordRegImm.reg 11757)))

def p2624 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11765, 11753)]

def p2625 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11769 11765 (Flapjack.WordRegImm.imm 21#64)))

def p2626 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11773, 11765)]

def p2627 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11777 11773 (Flapjack.WordRegImm.imm 11#64)))

def p2628 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11781 11769 (Flapjack.WordRegImm.reg 11777)))

def p2629 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11785 11761 (Flapjack.WordRegImm.reg 11781)))

def p2630 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11789, 11773)]

def p2631 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11793 11789 (Flapjack.WordRegImm.imm 26#64)))

def p2632 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11797, 11789)]

def p2633 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11801 11797 (Flapjack.WordRegImm.imm 6#64)))

def p2634 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11805 11793 (Flapjack.WordRegImm.reg 11801)))

def p2635 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11809 11785 (Flapjack.WordRegImm.reg 11805)))

def p2636 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11813 11741 (Flapjack.WordRegImm.reg 11809)))

def p2637 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11817, 11317)]

def p2638 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11821 11813 (Flapjack.WordRegImm.reg 11817)))

def p2639 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 11825 113926993#64)

def p2640 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11829 11821 (Flapjack.WordRegImm.reg 11825)))

def p2641 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11837, 11441), (11833, 11829)]

def p2642 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11841 11833 (Flapjack.WordRegImm.reg 11837)))

def p2643 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11845 11841 (Flapjack.WordRegImm.imm 32#64)))

def p2644 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11849 11845 (Flapjack.WordRegImm.imm 32#64)))

def p2645 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11873, 11561), (11869, 11529), (11865, 11461), (11857, 11469), (11853, 11849)]

def p2646 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11877 11869 (Flapjack.WordRegImm.reg 11873)))

def p2647 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 11881 11865 (Flapjack.WordRegImm.reg 11877)))

def p2648 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11885, 11869)]

def p2649 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11889 11881 (Flapjack.WordRegImm.reg 11885)))

def p2650 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11893, 11873)]

def p2651 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11897 11893 (Flapjack.WordRegImm.imm 10#64)))

def p2652 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11901, 11893)]

def p2653 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11905 11901 (Flapjack.WordRegImm.imm 22#64)))

def p2654 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11909 11897 (Flapjack.WordRegImm.reg 11905)))

def p2655 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11913, 11901)]

def p2656 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11917 11913 (Flapjack.WordRegImm.imm 19#64)))

def p2657 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11921, 11913)]

def p2658 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11925 11921 (Flapjack.WordRegImm.imm 13#64)))

def p2659 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11929 11917 (Flapjack.WordRegImm.reg 11925)))

def p2660 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11933 11909 (Flapjack.WordRegImm.reg 11929)))

def p2661 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11937, 11921)]

def p2662 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11941 11937 (Flapjack.WordRegImm.imm 30#64)))

def p2663 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11945, 11937)]

def p2664 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11949 11945 (Flapjack.WordRegImm.imm 2#64)))

def p2665 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 11953 11941 (Flapjack.WordRegImm.reg 11949)))

def p2666 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 11957 11933 (Flapjack.WordRegImm.reg 11953)))

def p2667 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11961 11889 (Flapjack.WordRegImm.reg 11957)))

def p2668 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11965, 11833)]

def p2669 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 11969 11961 (Flapjack.WordRegImm.reg 11965)))

def p2670 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11973 11969 (Flapjack.WordRegImm.imm 32#64)))

def p2671 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11977 11973 (Flapjack.WordRegImm.imm 32#64)))

def p2672 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11981, 11293)]

def p2673 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 11985 11981 (Flapjack.WordRegImm.imm 10#64)))

def p2674 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11989, 11981)]

def p2675 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 11993 11989 (Flapjack.WordRegImm.imm 13#64)))

def p2676 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(11997, 11989)]

def p2677 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12001 11997 (Flapjack.WordRegImm.imm 19#64)))

def p2678 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12005 11993 (Flapjack.WordRegImm.reg 12001)))

def p2679 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12009 11985 (Flapjack.WordRegImm.reg 12005)))

def p2680 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12013, 11997)]

def p2681 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12017 12013 (Flapjack.WordRegImm.imm 15#64)))

def p2682 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12021, 12013)]

def p2683 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12025 12021 (Flapjack.WordRegImm.imm 17#64)))

def p2684 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12029 12017 (Flapjack.WordRegImm.reg 12025)))

def p2685 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12033 12009 (Flapjack.WordRegImm.reg 12029)))

def p2686 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12037, 9941)]

def p2687 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12041 12033 (Flapjack.WordRegImm.reg 12037)))

def p2688 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12045, 8709)]

def p2689 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12049 12045 (Flapjack.WordRegImm.imm 3#64)))

def p2690 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12053, 12045)]

def p2691 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12057 12053 (Flapjack.WordRegImm.imm 14#64)))

def p2692 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12061, 12053)]

def p2693 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12065 12061 (Flapjack.WordRegImm.imm 18#64)))

def p2694 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12069 12057 (Flapjack.WordRegImm.reg 12065)))

def p2695 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12073 12049 (Flapjack.WordRegImm.reg 12069)))

def p2696 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12077, 12061)]

def p2697 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12081 12077 (Flapjack.WordRegImm.imm 25#64)))

def p2698 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12085, 12077)]

def p2699 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12089 12085 (Flapjack.WordRegImm.imm 7#64)))

def p2700 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12093 12081 (Flapjack.WordRegImm.reg 12089)))

def p2701 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12097 12073 (Flapjack.WordRegImm.reg 12093)))

def p2702 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12101 12041 (Flapjack.WordRegImm.reg 12097)))

def p2703 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12105, 11669)]

def p2704 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12109 12101 (Flapjack.WordRegImm.reg 12105)))

def p2705 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12113 12109 (Flapjack.WordRegImm.imm 32#64)))

def p2706 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12117 12113 (Flapjack.WordRegImm.imm 32#64)))

def p2707 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12133, 11797), (12129, 11717), (12125, 12117)]

def p2708 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12137 12129 (Flapjack.WordRegImm.reg 12133)))

def p2709 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12141, 11853)]

def p2710 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 12145 12137 (Flapjack.WordRegImm.reg 12141)))

def p2711 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12149, 12129)]

def p2712 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12153 12145 (Flapjack.WordRegImm.reg 12149)))

def p2713 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12157 12125 (Flapjack.WordRegImm.reg 12153)))

def p2714 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12161, 12141)]

def p2715 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12165 12161 (Flapjack.WordRegImm.imm 7#64)))

def p2716 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12169, 12161)]

def p2717 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12173 12169 (Flapjack.WordRegImm.imm 25#64)))

def p2718 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12177 12165 (Flapjack.WordRegImm.reg 12173)))

def p2719 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12181, 12169)]

def p2720 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12185 12181 (Flapjack.WordRegImm.imm 21#64)))

def p2721 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12189, 12181)]

def p2722 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12193 12189 (Flapjack.WordRegImm.imm 11#64)))

def p2723 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12197 12185 (Flapjack.WordRegImm.reg 12193)))

def p2724 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12201 12177 (Flapjack.WordRegImm.reg 12197)))

def p2725 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12205, 12189)]

def p2726 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12209 12205 (Flapjack.WordRegImm.imm 26#64)))

def p2727 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12213, 12205)]

def p2728 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12217 12213 (Flapjack.WordRegImm.imm 6#64)))

def p2729 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12221 12209 (Flapjack.WordRegImm.reg 12217)))

def p2730 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12225 12201 (Flapjack.WordRegImm.reg 12221)))

def p2731 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12229 12157 (Flapjack.WordRegImm.reg 12225)))

def p2732 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12233, 11733)]

def p2733 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12237 12229 (Flapjack.WordRegImm.reg 12233)))

def p2734 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 12241 338241895#64)

def p2735 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12245 12237 (Flapjack.WordRegImm.reg 12241)))

def p2736 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12253, 11857), (12249, 12245)]

def p2737 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12257 12249 (Flapjack.WordRegImm.reg 12253)))

def p2738 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12261 12257 (Flapjack.WordRegImm.imm 32#64)))

def p2739 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12265 12261 (Flapjack.WordRegImm.imm 32#64)))

def p2740 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12289, 11977), (12285, 11945), (12281, 11877), (12273, 11885), (12269, 12265)]

def p2741 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12293 12285 (Flapjack.WordRegImm.reg 12289)))

def p2742 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 12297 12281 (Flapjack.WordRegImm.reg 12293)))

def p2743 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12301, 12285)]

def p2744 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12305 12297 (Flapjack.WordRegImm.reg 12301)))

def p2745 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12309, 12289)]

def p2746 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12313 12309 (Flapjack.WordRegImm.imm 10#64)))

def p2747 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12317, 12309)]

def p2748 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12321 12317 (Flapjack.WordRegImm.imm 22#64)))

def p2749 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12325 12313 (Flapjack.WordRegImm.reg 12321)))

def p2750 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12329, 12317)]

def p2751 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12333 12329 (Flapjack.WordRegImm.imm 19#64)))

def p2752 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12337, 12329)]

def p2753 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12341 12337 (Flapjack.WordRegImm.imm 13#64)))

def p2754 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12345 12333 (Flapjack.WordRegImm.reg 12341)))

def p2755 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12349 12325 (Flapjack.WordRegImm.reg 12345)))

def p2756 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12353, 12337)]

def p2757 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12357 12353 (Flapjack.WordRegImm.imm 30#64)))

def p2758 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12361, 12353)]

def p2759 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12365 12361 (Flapjack.WordRegImm.imm 2#64)))

def p2760 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12369 12357 (Flapjack.WordRegImm.reg 12365)))

def p2761 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12373 12349 (Flapjack.WordRegImm.reg 12369)))

def p2762 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12377 12305 (Flapjack.WordRegImm.reg 12373)))

def p2763 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12381, 12249)]

def p2764 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12385 12377 (Flapjack.WordRegImm.reg 12381)))

def p2765 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12389 12385 (Flapjack.WordRegImm.imm 32#64)))

def p2766 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12393 12389 (Flapjack.WordRegImm.imm 32#64)))

def p2767 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12397, 11709)]

def p2768 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12401 12397 (Flapjack.WordRegImm.imm 10#64)))

def p2769 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12405, 12397)]

def p2770 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12409 12405 (Flapjack.WordRegImm.imm 13#64)))

def p2771 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12413, 12405)]

def p2772 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12417 12413 (Flapjack.WordRegImm.imm 19#64)))

def p2773 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12421 12409 (Flapjack.WordRegImm.reg 12417)))

def p2774 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12425 12401 (Flapjack.WordRegImm.reg 12421)))

def p2775 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12429, 12413)]

def p2776 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12433 12429 (Flapjack.WordRegImm.imm 15#64)))

def p2777 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12437, 12429)]

def p2778 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12441 12437 (Flapjack.WordRegImm.imm 17#64)))

def p2779 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12445 12433 (Flapjack.WordRegImm.reg 12441)))

def p2780 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12449 12425 (Flapjack.WordRegImm.reg 12445)))

def p2781 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12453, 10357)]

def p2782 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12457 12449 (Flapjack.WordRegImm.reg 12453)))

def p2783 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12461, 9125)]

def p2784 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12465 12461 (Flapjack.WordRegImm.imm 3#64)))

def p2785 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12469, 12461)]

def p2786 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12473 12469 (Flapjack.WordRegImm.imm 14#64)))

def p2787 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12477, 12469)]

def p2788 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12481 12477 (Flapjack.WordRegImm.imm 18#64)))

def p2789 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12485 12473 (Flapjack.WordRegImm.reg 12481)))

def p2790 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12489 12465 (Flapjack.WordRegImm.reg 12485)))

def p2791 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12493, 12477)]

def p2792 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12497 12493 (Flapjack.WordRegImm.imm 25#64)))

def p2793 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12501, 12493)]

def p2794 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12505 12501 (Flapjack.WordRegImm.imm 7#64)))

def p2795 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12509 12497 (Flapjack.WordRegImm.reg 12505)))

def p2796 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12513 12489 (Flapjack.WordRegImm.reg 12509)))

def p2797 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12517 12457 (Flapjack.WordRegImm.reg 12513)))

def p2798 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12521, 12085)]

def p2799 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12525 12517 (Flapjack.WordRegImm.reg 12521)))

def p2800 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 12529 12525 (Flapjack.WordRegImm.imm 32#64)))

def p2801 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 12533 12529 (Flapjack.WordRegImm.imm 32#64)))

def p2802 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12549, 12213), (12545, 12133), (12541, 12533)]

def p2803 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12553 12545 (Flapjack.WordRegImm.reg 12549)))

def p2804 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12557, 12269)]

def p2805 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.and 12561 12553 (Flapjack.WordRegImm.reg 12557)))

def p2806 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12565, 12545)]

def p2807 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.xor 12569 12561 (Flapjack.WordRegImm.reg 12565)))

def p2808 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 12573 12541 (Flapjack.WordRegImm.reg 12569)))

def p2809 : WordLangProgHOL (BitVec 64) :=
  Flapjack.WordLangProgHOL.move 0 [(12577, 12557)]

def parts : List (WordLangProgHOL (BitVec 64)) := [p2310, p2311, p2312, p2313, p2314, p2315, p2316, p2317, p2318, p2319, p2320, p2321, p2322, p2323, p2324, p2325, p2326, p2327, p2328, p2329, p2330, p2331, p2332, p2333, p2334, p2335, p2336, p2337, p2338, p2339, p2340, p2341, p2342, p2343, p2344, p2345, p2346, p2347, p2348, p2349, p2350, p2351, p2352, p2353, p2354, p2355, p2356, p2357, p2358, p2359, p2360, p2361, p2362, p2363, p2364, p2365, p2366, p2367, p2368, p2369, p2370, p2371, p2372, p2373, p2374, p2375, p2376, p2377, p2378, p2379, p2380, p2381, p2382, p2383, p2384, p2385, p2386, p2387, p2388, p2389, p2390, p2391, p2392, p2393, p2394, p2395, p2396, p2397, p2398, p2399, p2400, p2401, p2402, p2403, p2404, p2405, p2406, p2407, p2408, p2409, p2410, p2411, p2412, p2413, p2414, p2415, p2416, p2417, p2418, p2419, p2420, p2421, p2422, p2423, p2424, p2425, p2426, p2427, p2428, p2429, p2430, p2431, p2432, p2433, p2434, p2435, p2436, p2437, p2438, p2439, p2440, p2441, p2442, p2443, p2444, p2445, p2446, p2447, p2448, p2449, p2450, p2451, p2452, p2453, p2454, p2455, p2456, p2457, p2458, p2459, p2460, p2461, p2462, p2463, p2464, p2465, p2466, p2467, p2468, p2469, p2470, p2471, p2472, p2473, p2474, p2475, p2476, p2477, p2478, p2479, p2480, p2481, p2482, p2483, p2484, p2485, p2486, p2487, p2488, p2489, p2490, p2491, p2492, p2493, p2494, p2495, p2496, p2497, p2498, p2499, p2500, p2501, p2502, p2503, p2504, p2505, p2506, p2507, p2508, p2509, p2510, p2511, p2512, p2513, p2514, p2515, p2516, p2517, p2518, p2519, p2520, p2521, p2522, p2523, p2524, p2525, p2526, p2527, p2528, p2529, p2530, p2531, p2532, p2533, p2534, p2535, p2536, p2537, p2538, p2539, p2540, p2541, p2542, p2543, p2544, p2545, p2546, p2547, p2548, p2549, p2550, p2551, p2552, p2553, p2554, p2555, p2556, p2557, p2558, p2559, p2560, p2561, p2562, p2563, p2564, p2565, p2566, p2567, p2568, p2569, p2570, p2571, p2572, p2573, p2574, p2575, p2576, p2577, p2578, p2579, p2580, p2581, p2582, p2583, p2584, p2585, p2586, p2587, p2588, p2589, p2590, p2591, p2592, p2593, p2594, p2595, p2596, p2597, p2598, p2599, p2600, p2601, p2602, p2603, p2604, p2605, p2606, p2607, p2608, p2609, p2610, p2611, p2612, p2613, p2614, p2615, p2616, p2617, p2618, p2619, p2620, p2621, p2622, p2623, p2624, p2625, p2626, p2627, p2628, p2629, p2630, p2631, p2632, p2633, p2634, p2635, p2636, p2637, p2638, p2639, p2640, p2641, p2642, p2643, p2644, p2645, p2646, p2647, p2648, p2649, p2650, p2651, p2652, p2653, p2654, p2655, p2656, p2657, p2658, p2659, p2660, p2661, p2662, p2663, p2664, p2665, p2666, p2667, p2668, p2669, p2670, p2671, p2672, p2673, p2674, p2675, p2676, p2677, p2678, p2679, p2680, p2681, p2682, p2683, p2684, p2685, p2686, p2687, p2688, p2689, p2690, p2691, p2692, p2693, p2694, p2695, p2696, p2697, p2698, p2699, p2700, p2701, p2702, p2703, p2704, p2705, p2706, p2707, p2708, p2709, p2710, p2711, p2712, p2713, p2714, p2715, p2716, p2717, p2718, p2719, p2720, p2721, p2722, p2723, p2724, p2725, p2726, p2727, p2728, p2729, p2730, p2731, p2732, p2733, p2734, p2735, p2736, p2737, p2738, p2739, p2740, p2741, p2742, p2743, p2744, p2745, p2746, p2747, p2748, p2749, p2750, p2751, p2752, p2753, p2754, p2755, p2756, p2757, p2758, p2759, p2760, p2761, p2762, p2763, p2764, p2765, p2766, p2767, p2768, p2769, p2770, p2771, p2772, p2773, p2774, p2775, p2776, p2777, p2778, p2779, p2780, p2781, p2782, p2783, p2784, p2785, p2786, p2787, p2788, p2789, p2790, p2791, p2792, p2793, p2794, p2795, p2796, p2797, p2798, p2799, p2800, p2801, p2802, p2803, p2804, p2805, p2806, p2807, p2808, p2809]

wave8_kernel_reduce trees := parts.map (fun p => WordAlloc.getClashTree p [])
wave8_kernel_reduce colPs := parts.map (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)))
wave8_kernel_reduce stackOk := colPs.all (everyStackVarHOL stackPred)
wave8_kernel_reduce forcedOk := parts.all (fun p => (WordAlloc.getForced riscvConfig p []).all (forcedPred (oracle154.getD .ln)))
wave8_kernel_reduce progs := parts.map (transform oracle154)
wave8_kernel_reduce maxV := maxListProg progs
wave8_kernel_reduce comp := compList riscvConfig false (22, 13, 12) progs (.nil, 136)

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154.Block14
