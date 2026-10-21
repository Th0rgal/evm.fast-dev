import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass864_5
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word864_6_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(61, 0), (65, 2), (69, 4)]

def word864_6_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(73, 65)]

def word864_6_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 77 (Flapjack.WordLangAddr.addr 73 0#64))

def word864_6_3 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1 word864_6_2

def word864_6_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(81, 77)]

def word864_6_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 85 (Flapjack.WordLangAddr.addr 81 40#64))

def word864_6_6 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_4 word864_6_5

def word864_6_7 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_3 word864_6_6

def word864_6_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 93 88#64)

def word864_6_9 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_7 word864_6_8

def word864_6_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(99, 61), (103, 69), (107, 85), (111, 73), (115, 81)]

def word864_6_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 93)]

def word864_6_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(121, 99), (125, 103), (129, 107), (133, 111), (137, 115)]

def word864_6_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(141, 2)]

def word864_6_14 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_12 word864_6_13

def word864_6_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(149, 141)]

def word864_6_16 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_14 word864_6_15

def word864_6_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(145, 2)]

def word864_6_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 145)]

def word864_6_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def word864_6_20 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_18 word864_6_19

def word864_6_21 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_17 word864_6_20

def word864_6_22 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_12 word864_6_21

def word864_6_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 149 0#64)

def word864_6_24 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_22 word864_6_23

def word864_6_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
            (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word864_6_16, 864, 2)) (some 68) ([2]) (some (2, word864_6_24, 864, 3))

def word864_6_26 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_11 word864_6_25

def word864_6_27 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_10 word864_6_26

def word864_6_28 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_9 word864_6_27

def word864_6_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def word864_6_30 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_28 word864_6_29

def word864_6_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 157 Flapjack.WordStore.heapLength

def word864_6_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 161 157 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_33 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_31 word864_6_32

def word864_6_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 165 161

def word864_6_35 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_33 word864_6_34

def word864_6_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 169 165 (Flapjack.WordRegImm.imm 18446744073709551200#64)))

def word864_6_37 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_35 word864_6_36

def word864_6_38 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_30 word864_6_37

def word864_6_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(173, 149)]

def word864_6_40 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_38 word864_6_39

def word864_6_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(177, 173)]

def word864_6_42 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_40 word864_6_41

def word864_6_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(181, 169)]

def word864_6_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 177 (Flapjack.WordLangAddr.addr 181 0#64))

def word864_6_45 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_43 word864_6_44

def word864_6_46 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_42 word864_6_45

def word864_6_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(185, 157)]

def word864_6_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(189, 161)]

def word864_6_49 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_47 word864_6_48

def word864_6_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(193, 165)]

def word864_6_51 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_49 word864_6_50

def word864_6_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 197 (Flapjack.WordLangAddr.addr 193 18446744073709551200#64))

def word864_6_53 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_51 word864_6_52

def word864_6_54 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_46 word864_6_53

def word864_6_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 205 88#64)

def word864_6_56 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_54 word864_6_55

def word864_6_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(211, 121), (215, 125), (219, 129), (223, 133), (227, 137)]

def word864_6_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 197), (4, 205)]

def word864_6_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(233, 211), (237, 215), (241, 219), (245, 223), (249, 227)]

def word864_6_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(257, 2)]

def word864_6_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 257)]

def word864_6_62 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_61 word864_6_19

def word864_6_63 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_60 word864_6_62

def word864_6_64 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_59 word864_6_63

def word864_6_65 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
            (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_59, 864, 4)) (some 78) ([2, 4]) (some (2, word864_6_64, 864, 5))

def word864_6_66 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_58 word864_6_65

def word864_6_67 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_57 word864_6_66

def word864_6_68 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_56 word864_6_67

def word864_6_69 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_68 word864_6_29

def word864_6_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(269, 241)]

def word864_6_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 273 269 (Flapjack.WordRegImm.imm 4#64)))

def word864_6_72 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_70 word864_6_71

def word864_6_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 277 273 (Flapjack.WordRegImm.imm 16#64)))

def word864_6_74 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_72 word864_6_73

def word864_6_75 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_69 word864_6_74

def word864_6_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(283, 233), (287, 237), (291, 269), (295, 245), (299, 249)]

def word864_6_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 277)]

def word864_6_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(305, 283), (309, 287), (313, 291), (317, 295), (321, 299)]

def word864_6_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(325, 2)]

def word864_6_80 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_78 word864_6_79

def word864_6_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(333, 325)]

def word864_6_82 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_80 word864_6_81

def word864_6_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(329, 2)]

def word864_6_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 329)]

def word864_6_85 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_84 word864_6_19

def word864_6_86 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_83 word864_6_85

def word864_6_87 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_78 word864_6_86

def word864_6_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 333 0#64)

def word864_6_89 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_87 word864_6_88

def word864_6_90 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_82, 864, 6)) (some 68) ([2]) (some (2, word864_6_89, 864, 7))

def word864_6_91 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_77 word864_6_90

def word864_6_92 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_76 word864_6_91

def word864_6_93 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_75 word864_6_92

def word864_6_94 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_93 word864_6_29

def word864_6_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 341 Flapjack.WordStore.heapLength

def word864_6_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 345 341 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_97 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_95 word864_6_96

def word864_6_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 349 345

def word864_6_99 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_97 word864_6_98

def word864_6_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 353 (Flapjack.WordLangAddr.addr 349 18446744073709551200#64))

def word864_6_101 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_99 word864_6_100

def word864_6_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 357 353 (Flapjack.WordRegImm.imm 24#64)))

def word864_6_103 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_101 word864_6_102

def word864_6_104 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_94 word864_6_103

def word864_6_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(361, 333)]

def word864_6_106 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_104 word864_6_105

def word864_6_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(365, 361)]

def word864_6_108 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_106 word864_6_107

def word864_6_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(369, 357)]

def word864_6_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 365 (Flapjack.WordLangAddr.addr 369 0#64))

def word864_6_111 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_109 word864_6_110

def word864_6_112 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_108 word864_6_111

def word864_6_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(373, 313)]

def word864_6_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 377 373 (Flapjack.WordRegImm.imm 4#64)))

def word864_6_115 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_113 word864_6_114

def word864_6_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 381 377 (Flapjack.WordRegImm.imm 16#64)))

def word864_6_117 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_115 word864_6_116

def word864_6_118 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_112 word864_6_117

def word864_6_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(387, 305), (391, 309), (395, 365), (399, 373), (403, 317), (407, 321)]

def word864_6_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 381)]

def word864_6_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(413, 387), (417, 391), (421, 395), (425, 399), (429, 403), (433, 407)]

def word864_6_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(437, 2)]

def word864_6_123 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_121 word864_6_122

def word864_6_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(449, 437)]

def word864_6_125 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_123 word864_6_124

def word864_6_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(441, 2)]

def word864_6_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 441)]

def word864_6_128 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_127 word864_6_19

def word864_6_129 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_126 word864_6_128

def word864_6_130 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_121 word864_6_129

def word864_6_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 449 0#64)

def word864_6_132 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_130 word864_6_131

def word864_6_133 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word864_6_125, 864, 8)) (some 68) ([2]) (some (2, word864_6_132, 864, 9))

def word864_6_134 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_120 word864_6_133

def word864_6_135 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_119 word864_6_134

def word864_6_136 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_118 word864_6_135

def word864_6_137 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_136 word864_6_29

def word864_6_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 453 Flapjack.WordStore.heapLength

def word864_6_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 457 453 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_140 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_138 word864_6_139

def word864_6_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 461 457

def word864_6_142 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_140 word864_6_141

def word864_6_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 465 (Flapjack.WordLangAddr.addr 461 18446744073709551200#64))

def word864_6_144 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_142 word864_6_143

def word864_6_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 469 465 (Flapjack.WordRegImm.imm 32#64)))

def word864_6_146 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_144 word864_6_145

def word864_6_147 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_137 word864_6_146

def word864_6_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(473, 449)]

def word864_6_149 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_147 word864_6_148

def word864_6_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(477, 473)]

def word864_6_151 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_149 word864_6_150

def word864_6_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(481, 469)]

def word864_6_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 477 (Flapjack.WordLangAddr.addr 481 0#64))

def word864_6_154 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_152 word864_6_153

def word864_6_155 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_151 word864_6_154

def word864_6_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 493 16#64)

def word864_6_157 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_155 word864_6_156

def word864_6_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 497 8#64)

def word864_6_159 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_157 word864_6_158

def word864_6_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(503, 413), (507, 477), (511, 417), (515, 421), (519, 425), (523, 429), (527, 433)]

def word864_6_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 497), (4, 493)]

def word864_6_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(533, 503), (537, 507), (541, 511), (545, 515), (549, 519), (553, 523), (557, 527)]

def word864_6_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(561, 2)]

def word864_6_164 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_162 word864_6_163

def word864_6_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(569, 561)]

def word864_6_166 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_164 word864_6_165

def word864_6_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(565, 2)]

def word864_6_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 565)]

def word864_6_169 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_168 word864_6_19

def word864_6_170 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_167 word864_6_169

def word864_6_171 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_162 word864_6_170

def word864_6_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 569 0#64)

def word864_6_173 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_171 word864_6_172

def word864_6_174 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))))),
  Flapjack.Spt.ln)), word864_6_166, 864, 10)) (some 431) ([2, 4]) (some (2, word864_6_173, 864, 11))

def word864_6_175 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_161 word864_6_174

def word864_6_176 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_160 word864_6_175

def word864_6_177 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_159 word864_6_176

def word864_6_178 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_177 word864_6_29

def word864_6_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 577 Flapjack.WordStore.heapLength

def word864_6_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 581 577 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_181 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_179 word864_6_180

def word864_6_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 585 581

def word864_6_183 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_181 word864_6_182

def word864_6_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 589 (Flapjack.WordLangAddr.addr 585 18446744073709551200#64))

def word864_6_185 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_183 word864_6_184

def word864_6_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 593 589 (Flapjack.WordRegImm.imm 40#64)))

def word864_6_187 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_185 word864_6_186

def word864_6_188 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_178 word864_6_187

def word864_6_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(597, 569)]

def word864_6_190 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_188 word864_6_189

def word864_6_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(601, 597)]

def word864_6_192 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_190 word864_6_191

def word864_6_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(605, 593)]

def word864_6_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 601 (Flapjack.WordLangAddr.addr 605 0#64))

def word864_6_195 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_193 word864_6_194

def word864_6_196 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_192 word864_6_195

def word864_6_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 613 128#64)

def word864_6_198 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_196 word864_6_197

def word864_6_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(619, 533), (623, 537), (627, 541), (631, 545), (635, 549), (639, 553), (643, 601), (647, 557)]

def word864_6_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 613)]

def word864_6_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(653, 619), (657, 623), (661, 627), (665, 631), (669, 635), (673, 639), (677, 643), (681, 647)]

def word864_6_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(685, 2)]

def word864_6_203 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_201 word864_6_202

def word864_6_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(693, 685)]

def word864_6_205 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_203 word864_6_204

def word864_6_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(689, 2)]

def word864_6_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 689)]

def word864_6_208 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_207 word864_6_19

def word864_6_209 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_206 word864_6_208

def word864_6_210 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_201 word864_6_209

def word864_6_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 693 0#64)

def word864_6_212 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_210 word864_6_211

def word864_6_213 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))))),
  Flapjack.Spt.ln)), word864_6_205, 864, 12)) (some 68) ([2]) (some (2, word864_6_212, 864, 13))

def word864_6_214 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_200 word864_6_213

def word864_6_215 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_199 word864_6_214

def word864_6_216 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_198 word864_6_215

def word864_6_217 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_216 word864_6_29

def word864_6_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 701 Flapjack.WordStore.heapLength

def word864_6_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 705 701 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_220 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_218 word864_6_219

def word864_6_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 709 705

def word864_6_222 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_220 word864_6_221

def word864_6_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 713 (Flapjack.WordLangAddr.addr 709 18446744073709551200#64))

def word864_6_224 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_222 word864_6_223

def word864_6_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 717 713 (Flapjack.WordRegImm.imm 56#64)))

def word864_6_226 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_224 word864_6_225

def word864_6_227 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_217 word864_6_226

def word864_6_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(721, 693)]

def word864_6_229 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_227 word864_6_228

def word864_6_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(725, 721)]

def word864_6_231 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_229 word864_6_230

def word864_6_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(729, 717)]

def word864_6_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 725 (Flapjack.WordLangAddr.addr 729 0#64))

def word864_6_234 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_232 word864_6_233

def word864_6_235 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_231 word864_6_234

def word864_6_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 741 16#64)

def word864_6_237 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_235 word864_6_236

def word864_6_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 745 8#64)

def word864_6_239 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_237 word864_6_238

def word864_6_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(751, 653), (755, 725), (759, 657), (763, 661), (767, 665), (771, 669), (775, 673), (779, 677), (783, 681)]

def word864_6_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 745), (4, 741)]

def word864_6_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(789, 751), (793, 755), (797, 759), (801, 763), (805, 767), (809, 771), (813, 775), (817, 779), (821, 783)]

def word864_6_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(825, 2)]

def word864_6_244 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_242 word864_6_243

def word864_6_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(837, 825)]

def word864_6_246 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_244 word864_6_245

def word864_6_247 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(829, 2)]

def word864_6_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 829)]

def word864_6_249 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_248 word864_6_19

def word864_6_250 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_247 word864_6_249

def word864_6_251 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_242 word864_6_250

def word864_6_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 837 0#64)

def word864_6_253 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_251 word864_6_252

def word864_6_254 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))))),
  Flapjack.Spt.ln)), word864_6_246, 864, 14)) (some 431) ([2, 4]) (some (2, word864_6_253, 864, 15))

def word864_6_255 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_241 word864_6_254

def word864_6_256 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_240 word864_6_255

def word864_6_257 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_239 word864_6_256

def word864_6_258 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_257 word864_6_29

def word864_6_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 841 Flapjack.WordStore.heapLength

def word864_6_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 845 841 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_261 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_259 word864_6_260

def word864_6_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 849 845

def word864_6_263 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_261 word864_6_262

def word864_6_264 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 853 (Flapjack.WordLangAddr.addr 849 18446744073709551200#64))

def word864_6_265 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_263 word864_6_264

def word864_6_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 857 853 (Flapjack.WordRegImm.imm 72#64)))

def word864_6_267 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_265 word864_6_266

def word864_6_268 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_258 word864_6_267

def word864_6_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(861, 837)]

def word864_6_270 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_268 word864_6_269

def word864_6_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(865, 861)]

def word864_6_272 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_270 word864_6_271

def word864_6_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(869, 857)]

def word864_6_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 865 (Flapjack.WordLangAddr.addr 869 0#64))

def word864_6_275 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_273 word864_6_274

def word864_6_276 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_272 word864_6_275

def word864_6_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(873, 841)]

def word864_6_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(877, 845)]

def word864_6_279 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_277 word864_6_278

def word864_6_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(881, 849)]

def word864_6_281 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_279 word864_6_280

def word864_6_282 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 885 (Flapjack.WordLangAddr.addr 881 18446744073709551200#64))

def word864_6_283 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_281 word864_6_282

def word864_6_284 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 889 885 (Flapjack.WordRegImm.imm 80#64)))

def word864_6_285 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_283 word864_6_284

def word864_6_286 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_276 word864_6_285

def word864_6_287 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(893, 809)]

def word864_6_288 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_286 word864_6_287

def word864_6_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(897, 893)]

def word864_6_290 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_288 word864_6_289

def word864_6_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(901, 889)]

def word864_6_292 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 897 (Flapjack.WordLangAddr.addr 901 0#64))

def word864_6_293 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_291 word864_6_292

def word864_6_294 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_290 word864_6_293

def word864_6_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(907, 789), (911, 865), (915, 793), (919, 797), (923, 801), (927, 805), (931, 897), (935, 813), (939, 817),
    (943, 821)]

def word864_6_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(949, 907), (953, 911), (957, 915), (961, 919), (965, 923), (969, 927), (973, 931), (977, 935), (981, 939),
    (985, 943)]

def word864_6_297 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(993, 2)]

def word864_6_298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 993)]

def word864_6_299 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_298 word864_6_19

def word864_6_300 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_297 word864_6_299

def word864_6_301 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_296 word864_6_300

def word864_6_302 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_296, 864, 16)) (some 434) ([]) (some (2, word864_6_301, 864, 17))

def word864_6_303 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_295 word864_6_302

def word864_6_304 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_294 word864_6_303

def word864_6_305 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_304 word864_6_29

def word864_6_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 1005 Flapjack.WordStore.heapLength

def word864_6_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 1009 1005 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_308 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_306 word864_6_307

def word864_6_309 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 1013 1009

def word864_6_310 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_308 word864_6_309

def word864_6_311 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 1017 (Flapjack.WordLangAddr.addr 1013 18446744073709551152#64))

def word864_6_312 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_310 word864_6_311

def word864_6_313 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_305 word864_6_312

def word864_6_314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1021, 977)]

def word864_6_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 1025 (Flapjack.WordLangAddr.addr 1021 24#64))

def word864_6_316 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_314 word864_6_315

def word864_6_317 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_313 word864_6_316

def word864_6_318 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 1033 32#64)

def word864_6_319 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_317 word864_6_318

def word864_6_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1039, 949), (1043, 953), (1047, 957), (1051, 961), (1055, 965), (1059, 969), (1063, 973), (1067, 1021), (1071, 981),
    (1075, 985)]

def word864_6_321 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 1017), (4, 1025), (6, 1033)]

def word864_6_322 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1081, 1039), (1085, 1043), (1089, 1047), (1093, 1051), (1097, 1055), (1101, 1059), (1105, 1063), (1109, 1067),
    (1113, 1071), (1117, 1075)]

def word864_6_323 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1125, 2)]

def word864_6_324 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 1125)]

def word864_6_325 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_324 word864_6_19

def word864_6_326 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_323 word864_6_325

def word864_6_327 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_322 word864_6_326

def word864_6_328 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_322, 864, 18)) (some 856) ([2, 4, 6]) (some (2, word864_6_327, 864, 19))

def word864_6_329 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_321 word864_6_328

def word864_6_330 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_320 word864_6_329

def word864_6_331 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_319 word864_6_330

def word864_6_332 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_331 word864_6_29

def word864_6_333 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 1137 Flapjack.WordStore.heapLength

def word864_6_334 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 1141 1137 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_335 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_333 word864_6_334

def word864_6_336 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 1145 1141

def word864_6_337 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_335 word864_6_336

def word864_6_338 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 1149 (Flapjack.WordLangAddr.addr 1145 18446744073709551184#64))

def word864_6_339 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_337 word864_6_338

def word864_6_340 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_332 word864_6_339

def word864_6_341 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 1153 0#64)

def word864_6_342 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_340 word864_6_341

def word864_6_343 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1157, 1137)]

def word864_6_344 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1161, 1141)]

def word864_6_345 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_343 word864_6_344

def word864_6_346 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1165, 1145)]

def word864_6_347 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_345 word864_6_346

def word864_6_348 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 1169 (Flapjack.WordLangAddr.addr 1165 18446744073709551168#64))

def word864_6_349 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_347 word864_6_348

def word864_6_350 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_342 word864_6_349

def word864_6_351 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1181, 1157)]

def word864_6_352 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1185, 1161)]

def word864_6_353 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_351 word864_6_352

def word864_6_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1189, 1165)]

def word864_6_355 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_353 word864_6_354

def word864_6_356 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1193, 1169)]

def word864_6_357 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_355 word864_6_356

def word864_6_358 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 1197 1193 (Flapjack.WordRegImm.imm 18446744073709551615#64)))

def word864_6_359 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_357 word864_6_358

def word864_6_360 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 1201 1197 (Flapjack.WordRegImm.imm 5#64)))

def word864_6_361 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_359 word864_6_360

def word864_6_362 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1205, 1181)]

def word864_6_363 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1209, 1185)]

def word864_6_364 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_362 word864_6_363

def word864_6_365 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1213, 1189)]

def word864_6_366 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_364 word864_6_365

def word864_6_367 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 1217 (Flapjack.WordLangAddr.addr 1213 18446744073709551176#64))

def word864_6_368 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_366 word864_6_367

def word864_6_369 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 1221 1201 (Flapjack.WordRegImm.reg 1217)))

def word864_6_370 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_368 word864_6_369

def word864_6_371 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_361 word864_6_370

def word864_6_372 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_371

def word864_6_373 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1237, 1221)]

def word864_6_374 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_372 word864_6_373

def word864_6_375 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1237, 1149)]

def word864_6_376 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_375

def word864_6_377 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 1153 (Flapjack.WordRegImm.reg 1169) word864_6_374 word864_6_376

def word864_6_378 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_350 word864_6_377

def word864_6_379 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_378 word864_6_29

def word864_6_380 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1253, 1137)]

def word864_6_381 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1257, 1141)]

def word864_6_382 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_380 word864_6_381

def word864_6_383 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1261, 1145)]

def word864_6_384 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_382 word864_6_383

def word864_6_385 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 1265 (Flapjack.WordLangAddr.addr 1261 18446744073709551144#64))

def word864_6_386 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_384 word864_6_385

def word864_6_387 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_379 word864_6_386

def word864_6_388 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1269, 1237)]

def word864_6_389 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_387 word864_6_388

def word864_6_390 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 1277 32#64)

def word864_6_391 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_389 word864_6_390

def word864_6_392 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1283, 1081), (1287, 1085), (1291, 1089), (1295, 1093), (1299, 1097), (1303, 1101), (1307, 1269), (1311, 1105),
    (1315, 1109), (1319, 1113), (1323, 1117)]

def word864_6_393 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 1265), (4, 1269), (6, 1277)]

def word864_6_394 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1329, 1283), (1333, 1287), (1337, 1291), (1341, 1295), (1345, 1299), (1349, 1303), (1353, 1307), (1357, 1311),
    (1361, 1315), (1365, 1319), (1369, 1323)]

def word864_6_395 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1377, 2)]

def word864_6_396 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 1377)]

def word864_6_397 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_396 word864_6_19

def word864_6_398 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_395 word864_6_397

def word864_6_399 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_394 word864_6_398

def word864_6_400 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_394, 864, 20)) (some 856) ([2, 4, 6]) (some (2, word864_6_399, 864, 21))

def word864_6_401 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_393 word864_6_400

def word864_6_402 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_392 word864_6_401

def word864_6_403 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_391 word864_6_402

def word864_6_404 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_403 word864_6_29

def word864_6_405 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1391, 1329), (1395, 1333), (1399, 1337), (1403, 1341), (1407, 1345), (1411, 1349), (1415, 1353), (1419, 1357),
    (1423, 1361), (1427, 1365), (1431, 1369)]

def word864_6_406 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1437, 1391), (1441, 1395), (1445, 1399), (1449, 1403), (1453, 1407), (1457, 1411), (1461, 1415), (1465, 1419),
    (1469, 1423), (1473, 1427), (1477, 1431)]

def word864_6_407 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1485, 2)]

def word864_6_408 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 1485)]

def word864_6_409 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_408 word864_6_19

def word864_6_410 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_407 word864_6_409

def word864_6_411 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_406 word864_6_410

def word864_6_412 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))))),
  Flapjack.Spt.ln)), word864_6_406, 864, 22)) (some 383) ([]) (some (2, word864_6_411, 864, 23))

def word864_6_413 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_405 word864_6_412

def word864_6_414 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_404 word864_6_413

def word864_6_415 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_414 word864_6_29

def word864_6_416 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 1501 1#64)

def word864_6_417 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_415 word864_6_416

def word864_6_418 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1507, 1437), (1511, 1441), (1515, 1445), (1519, 1449), (1523, 1453), (1527, 1457), (1531, 1461), (1535, 1465),
    (1539, 1469), (1543, 1473), (1547, 1477)]

def word864_6_419 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 1501)]

def word864_6_420 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1553, 1507), (1557, 1511), (1561, 1515), (1565, 1519), (1569, 1523), (1573, 1527), (1577, 1531), (1581, 1535),
    (1585, 1539), (1589, 1543), (1593, 1547)]

def word864_6_421 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1601, 2)]

def word864_6_422 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 1601)]

def word864_6_423 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_422 word864_6_19

def word864_6_424 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_421 word864_6_423

def word864_6_425 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_420 word864_6_424

def word864_6_426 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))))))),
  Flapjack.Spt.ln)), word864_6_420, 864, 24)) (some 430) ([2]) (some (2, word864_6_425, 864, 25))

def word864_6_427 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_419 word864_6_426

def word864_6_428 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_418 word864_6_427

def word864_6_429 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_417 word864_6_428

def word864_6_430 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_429 word864_6_29

def word864_6_431 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1613, 1593)]

def word864_6_432 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 1617 (Flapjack.WordLangAddr.addr 1613 32#64))

def word864_6_433 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_431 word864_6_432

def word864_6_434 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_430 word864_6_433

def word864_6_435 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 1621 0#64)

def word864_6_436 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_434 word864_6_435

def word864_6_437 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_436 word864_6_29

def word864_6_438 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1625, 1553), (1629, 1557), (1633, 1621), (1637, 1561), (1641, 1565), (1645, 1569), (1649, 1573), (1653, 1577),
    (1657, 1581), (1661, 1585), (1665, 1589), (1669, 1613), (1673, 1617)]

def word864_6_439 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1677, 1633)]

def word864_6_440 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1681, 1657)]

def word864_6_441 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_439 word864_6_440

def word864_6_442 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1693, 1677)]

def word864_6_443 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 1697 1693 (Flapjack.WordRegImm.imm 4#64)))

def word864_6_444 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_442 word864_6_443

def word864_6_445 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1701, 1673)]

def word864_6_446 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 1705 1697 (Flapjack.WordRegImm.reg 1701)))

def word864_6_447 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_445 word864_6_446

def word864_6_448 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_444 word864_6_447

def word864_6_449 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 1709 (Flapjack.WordLangAddr.addr 1705 0#64))

def word864_6_450 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_448 word864_6_449

def word864_6_451 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_450

def word864_6_452 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1713, 1693)]

def word864_6_453 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1717, 1697)]

def word864_6_454 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_452 word864_6_453

def word864_6_455 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1721, 1701)]

def word864_6_456 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1725, 1705)]

def word864_6_457 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_455 word864_6_456

def word864_6_458 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_454 word864_6_457

def word864_6_459 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 1729 (Flapjack.WordLangAddr.addr 1725 8#64))

def word864_6_460 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_458 word864_6_459

def word864_6_461 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_451 word864_6_460

def word864_6_462 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1735, 1625), (1739, 1629), (1743, 1713), (1747, 1637), (1751, 1641), (1755, 1645), (1759, 1649), (1763, 1653),
    (1767, 1681), (1771, 1661), (1775, 1665), (1779, 1669), (1783, 1721)]

def word864_6_463 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 1709), (4, 1729)]

def word864_6_464 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1789, 1735), (1793, 1739), (1797, 1743), (1801, 1747), (1805, 1751), (1809, 1755), (1813, 1759), (1817, 1763),
    (1821, 1767), (1825, 1771), (1829, 1775), (1833, 1779), (1837, 1783)]

def word864_6_465 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1841, 2)]

def word864_6_466 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_464 word864_6_465

def word864_6_467 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1853, 1841)]

def word864_6_468 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_466 word864_6_467

def word864_6_469 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1845, 2)]

def word864_6_470 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 1845)]

def word864_6_471 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_470 word864_6_19

def word864_6_472 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_469 word864_6_471

def word864_6_473 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_464 word864_6_472

def word864_6_474 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 1853 0#64)

def word864_6_475 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_473 word864_6_474

def word864_6_476 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_468, 864, 26)) (some 342) ([2, 4]) (some (2, word864_6_475, 864, 27))

def word864_6_477 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_463 word864_6_476

def word864_6_478 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_462 word864_6_477

def word864_6_479 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_461 word864_6_478

def word864_6_480 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_479 word864_6_29

def word864_6_481 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1857, 1853)]

def word864_6_482 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_480 word864_6_481

def word864_6_483 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1861, 1797)]

def word864_6_484 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_482 word864_6_483

def word864_6_485 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1867, 1789), (1871, 1793), (1875, 1861), (1879, 1801), (1883, 1805), (1887, 1809), (1891, 1813), (1895, 1817),
    (1899, 1821), (1903, 1825), (1907, 1829), (1911, 1833), (1915, 1837)]

def word864_6_486 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 1857), (4, 1861)]

def word864_6_487 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(1921, 1867), (1925, 1871), (1929, 1875), (1933, 1879), (1937, 1883), (1941, 1887), (1945, 1891), (1949, 1895),
    (1953, 1899), (1957, 1903), (1961, 1907), (1965, 1911), (1969, 1915)]

def word864_6_488 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1977, 2)]

def word864_6_489 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 1977)]

def word864_6_490 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_489 word864_6_19

def word864_6_491 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_488 word864_6_490

def word864_6_492 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_487 word864_6_491

def word864_6_493 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_487, 864, 28)) (some 859) ([2, 4]) (some (2, word864_6_492, 864, 29))

def word864_6_494 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_486 word864_6_493

def word864_6_495 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_485 word864_6_494

def word864_6_496 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_484 word864_6_495

def word864_6_497 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_496 word864_6_29

def word864_6_498 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1989, 1929)]

def word864_6_499 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 1993 1989 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_500 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_498 word864_6_499

def word864_6_501 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_497 word864_6_500

def word864_6_502 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1997, 1993)]

def word864_6_503 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_501 word864_6_502

def word864_6_504 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(1625, 1921), (1629, 1925), (1633, 1997), (1637, 1933), (1641, 1937), (1645, 1941), (1649, 1945), (1653, 1949),
    (1657, 1953), (1661, 1957), (1665, 1961), (1669, 1965), (1673, 1969)]

def word864_6_505 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def word864_6_506 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_504 word864_6_505

def word864_6_507 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_503 word864_6_506

def word864_6_508 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2065, 1625), (2061, 1629), (2057, 1633), (2053, 1637), (2049, 1641), (2045, 1645), (2041, 1649), (2037, 1653),
    (2033, 1657), (2025, 1661), (2021, 1665), (2017, 1669), (2009, 1673)]

def word864_6_509 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_507 word864_6_508

def word864_6_510 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1657, 1681)]

def word864_6_511 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def word864_6_512 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_510 word864_6_511

def word864_6_513 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_512

def word864_6_514 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2065, 1625), (2061, 1629), (2057, 1677), (2053, 1637), (2049, 1641), (2045, 1645), (2041, 1649), (2037, 1653),
    (2033, 1657), (2025, 1661), (2021, 1665), (2017, 1669), (2009, 1673)]

def word864_6_515 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_513 word864_6_514

def word864_6_516 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 1677 (Flapjack.WordRegImm.reg 1681) word864_6_509 word864_6_515

def word864_6_517 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_441 word864_6_516

def word864_6_518 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_517 word864_6_29

def word864_6_519 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(1625, 2065), (1629, 2061), (1633, 2057), (1637, 2053), (1641, 2049), (1645, 2045), (1649, 2041), (1653, 2037),
    (1657, 2033), (1661, 2025), (1665, 2021), (1669, 2017), (1673, 2009)]

def word864_6_520 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_518 word864_6_519

def word864_6_521 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln)))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))))))
    Flapjack.Spt.ln)) word864_6_520 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln)))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          Flapjack.Spt.ln)))
    Flapjack.Spt.ln))

def word864_6_522 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_438 word864_6_521

def word864_6_523 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_437 word864_6_522

def word864_6_524 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_523 word864_6_29

def word864_6_525 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 2077 Flapjack.WordStore.heapLength

def word864_6_526 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 2081 2077 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_527 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_525 word864_6_526

def word864_6_528 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 2085 2081

def word864_6_529 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_527 word864_6_528

def word864_6_530 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 2089 2085 (Flapjack.WordRegImm.imm 18446744073709551392#64)))

def word864_6_531 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_529 word864_6_530

def word864_6_532 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_524 word864_6_531

def word864_6_533 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2093, 1657)]

def word864_6_534 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.binop Flapjack.BinOp.add 2097 2093 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_535 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_533 word864_6_534

def word864_6_536 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_532 word864_6_535

def word864_6_537 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2101, 2097)]

def word864_6_538 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_536 word864_6_537

def word864_6_539 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2105, 2089)]

def word864_6_540 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store 2101 (Flapjack.WordLangAddr.addr 2105 0#64))

def word864_6_541 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_539 word864_6_540

def word864_6_542 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_538 word864_6_541

def word864_6_543 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2109, 1669)]

def word864_6_544 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_542 word864_6_543

def word864_6_545 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2115, 1625), (2119, 1641), (2123, 1645), (2127, 1649), (2131, 2093), (2135, 2109)]

def word864_6_546 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2109)]

def word864_6_547 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2141, 2115), (2145, 2119), (2149, 2123), (2153, 2127), (2157, 2131), (2161, 2135)]

def word864_6_548 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2169, 2)]

def word864_6_549 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2169)]

def word864_6_550 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_549 word864_6_19

def word864_6_551 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_548 word864_6_550

def word864_6_552 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_547 word864_6_551

def word864_6_553 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word864_6_547, 864, 30)) (some 861) ([2]) (some (2, word864_6_552, 864, 31))

def word864_6_554 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_546 word864_6_553

def word864_6_555 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_545 word864_6_554

def word864_6_556 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_544 word864_6_555

def word864_6_557 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_556 word864_6_29

def word864_6_558 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2183, 2141), (2187, 2145), (2191, 2149), (2195, 2153), (2199, 2157), (2203, 2161)]

def word864_6_559 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2209, 2183), (2213, 2187), (2217, 2191), (2221, 2195), (2225, 2199), (2229, 2203)]

def word864_6_560 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2237, 2)]

def word864_6_561 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2237)]

def word864_6_562 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_561 word864_6_19

def word864_6_563 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_560 word864_6_562

def word864_6_564 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_559 word864_6_563

def word864_6_565 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word864_6_559, 864, 32)) (some 863) ([]) (some (2, word864_6_564, 864, 33))

def word864_6_566 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_558 word864_6_565

def word864_6_567 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_557 word864_6_566

def word864_6_568 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_567 word864_6_29

def word864_6_569 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2251, 2209), (2255, 2213), (2259, 2217), (2263, 2221), (2267, 2225), (2271, 2229)]

def word864_6_570 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2277, 2251), (2281, 2255), (2285, 2259), (2289, 2263), (2293, 2267), (2297, 2271)]

def word864_6_571 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2301, 2), (2305, 4)]

def word864_6_572 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_570 word864_6_571

def word864_6_573 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2317, 2305)]

def word864_6_574 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2321, 2301)]

def word864_6_575 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_573 word864_6_574

def word864_6_576 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_572 word864_6_575

def word864_6_577 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2309, 2)]

def word864_6_578 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2309)]

def word864_6_579 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_578 word864_6_19

def word864_6_580 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_577 word864_6_579

def word864_6_581 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_570 word864_6_580

def word864_6_582 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2317 0#64)

def word864_6_583 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2321 0#64)

def word864_6_584 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_582 word864_6_583

def word864_6_585 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_581 word864_6_584

def word864_6_586 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_576, 864, 34)) (some 456) ([]) (some (2, word864_6_585, 864, 35))

def word864_6_587 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_569 word864_6_586

def word864_6_588 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_568 word864_6_587

def word864_6_589 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_588 word864_6_29

def word864_6_590 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 2325 Flapjack.WordStore.heapLength

def word864_6_591 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 2329 2325 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_592 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_590 word864_6_591

def word864_6_593 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 2333 2329

def word864_6_594 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_592 word864_6_593

def word864_6_595 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 2337 (Flapjack.WordLangAddr.addr 2333 18446744073709551208#64))

def word864_6_596 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_594 word864_6_595

def word864_6_597 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 2341 (Flapjack.WordLangAddr.addr 2337 8#64))

def word864_6_598 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_596 word864_6_597

def word864_6_599 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_589 word864_6_598

def word864_6_600 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2347, 2277), (2351, 2321), (2355, 2281), (2359, 2285), (2363, 2289), (2367, 2293), (2371, 2317), (2375, 2297)]

def word864_6_601 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2341)]

def word864_6_602 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2381, 2347), (2385, 2351), (2389, 2355), (2393, 2359), (2397, 2363), (2401, 2367), (2405, 2371), (2409, 2375)]

def word864_6_603 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2417, 2)]

def word864_6_604 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2417)]

def word864_6_605 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_604 word864_6_19

def word864_6_606 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_603 word864_6_605

def word864_6_607 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_602 word864_6_606

def word864_6_608 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)))))),
  Flapjack.Spt.ln)), word864_6_602, 864, 36)) (some 457) ([2]) (some (2, word864_6_607, 864, 37))

def word864_6_609 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_601 word864_6_608

def word864_6_610 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_600 word864_6_609

def word864_6_611 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_599 word864_6_610

def word864_6_612 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_611 word864_6_29

def word864_6_613 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2433 32#64)

def word864_6_614 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_612 word864_6_613

def word864_6_615 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2439, 2381), (2443, 2385), (2447, 2389), (2451, 2393), (2455, 2397), (2459, 2401), (2463, 2405), (2467, 2409)]

def word864_6_616 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2433)]

def word864_6_617 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2473, 2439), (2477, 2443), (2481, 2447), (2485, 2451), (2489, 2455), (2493, 2459), (2497, 2463), (2501, 2467)]

def word864_6_618 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2505, 2)]

def word864_6_619 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_617 word864_6_618

def word864_6_620 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2513, 2505)]

def word864_6_621 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_619 word864_6_620

def word864_6_622 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2509, 2)]

def word864_6_623 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2509)]

def word864_6_624 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_623 word864_6_19

def word864_6_625 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_622 word864_6_624

def word864_6_626 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_617 word864_6_625

def word864_6_627 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2513 0#64)

def word864_6_628 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_626 word864_6_627

def word864_6_629 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_621, 864, 38)) (some 68) ([2]) (some (2, word864_6_628, 864, 39))

def word864_6_630 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_616 word864_6_629

def word864_6_631 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_615 word864_6_630

def word864_6_632 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_614 word864_6_631

def word864_6_633 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_632 word864_6_29

def word864_6_634 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2521, 2513)]

def word864_6_635 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_633 word864_6_634

def word864_6_636 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2527, 2473), (2531, 2477), (2535, 2481), (2539, 2485), (2543, 2489), (2547, 2493), (2551, 2497), (2555, 2501),
    (2559, 2521)]

def word864_6_637 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2521)]

def word864_6_638 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2565, 2527), (2569, 2531), (2573, 2535), (2577, 2539), (2581, 2543), (2585, 2547), (2589, 2551), (2593, 2555),
    (2597, 2559)]

def word864_6_639 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2605, 2)]

def word864_6_640 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2605)]

def word864_6_641 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_640 word864_6_19

def word864_6_642 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_639 word864_6_641

def word864_6_643 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_638 word864_6_642

def word864_6_644 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
                      Flapjack.Spt.ln))))))))),
  Flapjack.Spt.ln)), word864_6_638, 864, 40)) (some 846) ([2]) (some (2, word864_6_643, 864, 41))

def word864_6_645 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_637 word864_6_644

def word864_6_646 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_636 word864_6_645

def word864_6_647 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_635 word864_6_646

def word864_6_648 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_647 word864_6_29

def word864_6_649 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2621 32#64)

def word864_6_650 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_648 word864_6_649

def word864_6_651 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2627, 2565), (2631, 2569), (2635, 2573), (2639, 2577), (2643, 2581), (2647, 2585), (2651, 2589), (2655, 2593),
    (2659, 2597)]

def word864_6_652 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2621)]

def word864_6_653 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2665, 2627), (2669, 2631), (2673, 2635), (2677, 2639), (2681, 2643), (2685, 2647), (2689, 2651), (2693, 2655),
    (2697, 2659)]

def word864_6_654 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2701, 2)]

def word864_6_655 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_653 word864_6_654

def word864_6_656 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2713, 2701)]

def word864_6_657 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_655 word864_6_656

def word864_6_658 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2705, 2)]

def word864_6_659 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2705)]

def word864_6_660 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_659 word864_6_19

def word864_6_661 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_658 word864_6_660

def word864_6_662 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_653 word864_6_661

def word864_6_663 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2713 0#64)

def word864_6_664 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_662 word864_6_663

def word864_6_665 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_657, 864, 42)) (some 68) ([2]) (some (2, word864_6_664, 864, 43))

def word864_6_666 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_652 word864_6_665

def word864_6_667 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_651 word864_6_666

def word864_6_668 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_650 word864_6_667

def word864_6_669 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_668 word864_6_29

def word864_6_670 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2717, 2681)]

def word864_6_671 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_669 word864_6_670

def word864_6_672 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2721, 2685)]

def word864_6_673 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_671 word864_6_672

def word864_6_674 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2725, 2713)]

def word864_6_675 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_673 word864_6_674

def word864_6_676 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2731, 2665), (2735, 2669), (2739, 2673), (2743, 2677), (2747, 2721), (2751, 2689), (2755, 2693), (2759, 2725),
    (2763, 2697)]

def word864_6_677 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2717), (4, 2721), (6, 2725)]

def word864_6_678 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2769, 2731), (2773, 2735), (2777, 2739), (2781, 2743), (2785, 2747), (2789, 2751), (2793, 2755), (2797, 2759),
    (2801, 2763)]

def word864_6_679 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2809, 2)]

def word864_6_680 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2809)]

def word864_6_681 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_680 word864_6_19

def word864_6_682 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_679 word864_6_681

def word864_6_683 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_678 word864_6_682

def word864_6_684 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))))),
  Flapjack.Spt.ln)), word864_6_678, 864, 44)) (some 328) ([2, 4, 6]) (some (2, word864_6_683, 864, 45))

def word864_6_685 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_677 word864_6_684

def word864_6_686 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_676 word864_6_685

def word864_6_687 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_675 word864_6_686

def word864_6_688 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_687 word864_6_29

def word864_6_689 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2825 32#64)

def word864_6_690 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_688 word864_6_689

def word864_6_691 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2831, 2769), (2835, 2773), (2839, 2777), (2843, 2781), (2847, 2785), (2851, 2789), (2855, 2793), (2859, 2797),
    (2863, 2801)]

def word864_6_692 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2825)]

def word864_6_693 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2869, 2831), (2873, 2835), (2877, 2839), (2881, 2843), (2885, 2847), (2889, 2851), (2893, 2855), (2897, 2859),
    (2901, 2863)]

def word864_6_694 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2905, 2)]

def word864_6_695 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_693 word864_6_694

def word864_6_696 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2913, 2905)]

def word864_6_697 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_695 word864_6_696

def word864_6_698 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2909, 2)]

def word864_6_699 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2909)]

def word864_6_700 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_699 word864_6_19

def word864_6_701 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_698 word864_6_700

def word864_6_702 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_693 word864_6_701

def word864_6_703 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2913 0#64)

def word864_6_704 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_702 word864_6_703

def word864_6_705 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_697, 864, 46)) (some 68) ([2]) (some (2, word864_6_704, 864, 47))

def word864_6_706 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_692 word864_6_705

def word864_6_707 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_691 word864_6_706

def word864_6_708 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_690 word864_6_707

def word864_6_709 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_708 word864_6_29

def word864_6_710 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2921, 2877)]

def word864_6_711 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_709 word864_6_710

def word864_6_712 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2925, 2885)]

def word864_6_713 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_711 word864_6_712

def word864_6_714 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2929, 2913)]

def word864_6_715 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_713 word864_6_714

def word864_6_716 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2935, 2869), (2939, 2873), (2943, 2881), (2947, 2889), (2951, 2893), (2955, 2897), (2959, 2901), (2963, 2929)]

def word864_6_717 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2921), (4, 2925), (6, 2929)]

def word864_6_718 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(2969, 2935), (2973, 2939), (2977, 2943), (2981, 2947), (2985, 2951), (2989, 2955), (2993, 2959), (2997, 2963)]

def word864_6_719 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3005, 2)]

def word864_6_720 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3005)]

def word864_6_721 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_720 word864_6_19

def word864_6_722 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_719 word864_6_721

def word864_6_723 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_718 word864_6_722

def word864_6_724 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))))),
  Flapjack.Spt.ln)), word864_6_718, 864, 48)) (some 328) ([2, 4, 6]) (some (2, word864_6_723, 864, 49))

def word864_6_725 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_717 word864_6_724

def word864_6_726 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_716 word864_6_725

def word864_6_727 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_715 word864_6_726

def word864_6_728 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_727 word864_6_29

def word864_6_729 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 3021 256#64)

def word864_6_730 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_728 word864_6_729

def word864_6_731 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3027, 2969), (3031, 2973), (3035, 2977), (3039, 2981), (3043, 2985), (3047, 2989), (3051, 2993), (3055, 2997)]

def word864_6_732 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3021)]

def word864_6_733 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3061, 3027), (3065, 3031), (3069, 3035), (3073, 3039), (3077, 3043), (3081, 3047), (3085, 3051), (3089, 3055)]

def word864_6_734 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3093, 2)]

def word864_6_735 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_733 word864_6_734

def word864_6_736 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3101, 3093)]

def word864_6_737 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_735 word864_6_736

def word864_6_738 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3097, 2)]

def word864_6_739 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3097)]

def word864_6_740 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_739 word864_6_19

def word864_6_741 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_738 word864_6_740

def word864_6_742 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_733 word864_6_741

def word864_6_743 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 3101 0#64)

def word864_6_744 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_742 word864_6_743

def word864_6_745 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_737, 864, 50)) (some 68) ([2]) (some (2, word864_6_744, 864, 51))

def word864_6_746 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_732 word864_6_745

def word864_6_747 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_731 word864_6_746

def word864_6_748 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_730 word864_6_747

def word864_6_749 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_748 word864_6_29

def word864_6_750 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 3109 Flapjack.WordStore.heapLength

def word864_6_751 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 3113 3109 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_752 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_750 word864_6_751

def word864_6_753 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 3117 3113

def word864_6_754 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_752 word864_6_753

def word864_6_755 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 3121 (Flapjack.WordLangAddr.addr 3117 18446744073709551200#64))

def word864_6_756 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_754 word864_6_755

def word864_6_757 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 3125 (Flapjack.WordLangAddr.addr 3121 40#64))

def word864_6_758 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_756 word864_6_757

def word864_6_759 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_749 word864_6_758

def word864_6_760 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3129, 3101)]

def word864_6_761 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_759 word864_6_760

def word864_6_762 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3135, 3061), (3139, 3065), (3143, 3069), (3147, 3073), (3151, 3129), (3155, 3077), (3159, 3081), (3163, 3085),
    (3167, 3089)]

def word864_6_763 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3125), (4, 3129)]

def word864_6_764 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3173, 3135), (3177, 3139), (3181, 3143), (3185, 3147), (3189, 3151), (3193, 3155), (3197, 3159), (3201, 3163),
    (3205, 3167)]

def word864_6_765 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3213, 2)]

def word864_6_766 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3213)]

def word864_6_767 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_766 word864_6_19

def word864_6_768 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_765 word864_6_767

def word864_6_769 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_764 word864_6_768

def word864_6_770 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
                Flapjack.Spt.ln)))))),
  Flapjack.Spt.ln)), word864_6_764, 864, 52)) (some 835) ([2, 4]) (some (2, word864_6_769, 864, 53))

def word864_6_771 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_763 word864_6_770

def word864_6_772 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_762 word864_6_771

def word864_6_773 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_761 word864_6_772

def word864_6_774 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_773 word864_6_29

def word864_6_775 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 3229 32#64)

def word864_6_776 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_774 word864_6_775

def word864_6_777 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3235, 3173), (3239, 3177), (3243, 3181), (3247, 3185), (3251, 3189), (3255, 3193), (3259, 3197), (3263, 3201),
    (3267, 3205)]

def word864_6_778 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3229)]

def word864_6_779 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3273, 3235), (3277, 3239), (3281, 3243), (3285, 3247), (3289, 3251), (3293, 3255), (3297, 3259), (3301, 3263),
    (3305, 3267)]

def word864_6_780 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3309, 2)]

def word864_6_781 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_779 word864_6_780

def word864_6_782 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3321, 3309)]

def word864_6_783 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_781 word864_6_782

def word864_6_784 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3313, 2)]

def word864_6_785 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3313)]

def word864_6_786 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_785 word864_6_19

def word864_6_787 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_784 word864_6_786

def word864_6_788 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_779 word864_6_787

def word864_6_789 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 3321 0#64)

def word864_6_790 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_788 word864_6_789

def word864_6_791 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))))),
  Flapjack.Spt.ln)), word864_6_783, 864, 54)) (some 68) ([2]) (some (2, word864_6_790, 864, 55))

def word864_6_792 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_778 word864_6_791

def word864_6_793 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_777 word864_6_792

def word864_6_794 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_776 word864_6_793

def word864_6_795 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_794 word864_6_29

def word864_6_796 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 3325 Flapjack.WordStore.heapLength

def word864_6_797 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 3329 3325 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_798 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_796 word864_6_797

def word864_6_799 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 3333 3329

def word864_6_800 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_798 word864_6_799

def word864_6_801 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 3337 (Flapjack.WordLangAddr.addr 3333 18446744073709551088#64))

def word864_6_802 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_800 word864_6_801

def word864_6_803 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_795 word864_6_802

def word864_6_804 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3341, 3293)]

def word864_6_805 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 3345 (Flapjack.WordLangAddr.addr 3341 56#64))

def word864_6_806 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_804 word864_6_805

def word864_6_807 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_803 word864_6_806

def word864_6_808 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3349, 3321)]

def word864_6_809 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_807 word864_6_808

def word864_6_810 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3355, 3273), (3359, 3277), (3363, 3281), (3367, 3349), (3371, 3285), (3375, 3289), (3379, 3297), (3383, 3301),
    (3387, 3305)]

def word864_6_811 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3337), (4, 3345), (6, 3349)]

def word864_6_812 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3393, 3355), (3397, 3359), (3401, 3363), (3405, 3367), (3409, 3371), (3413, 3375), (3417, 3379), (3421, 3383),
    (3425, 3387)]

def word864_6_813 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3433, 2)]

def word864_6_814 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3433)]

def word864_6_815 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_814 word864_6_19

def word864_6_816 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_813 word864_6_815

def word864_6_817 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_812 word864_6_816

def word864_6_818 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_812, 864, 56)) (some 328) ([2, 4, 6]) (some (2, word864_6_817, 864, 57))

def word864_6_819 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_811 word864_6_818

def word864_6_820 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_810 word864_6_819

def word864_6_821 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_809 word864_6_820

def word864_6_822 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_821 word864_6_29

def word864_6_823 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 3449 32#64)

def word864_6_824 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_822 word864_6_823

def word864_6_825 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3455, 3393), (3459, 3397), (3463, 3401), (3467, 3405), (3471, 3409), (3475, 3413), (3479, 3417), (3483, 3421),
    (3487, 3425)]

def word864_6_826 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3449)]

def word864_6_827 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3493, 3455), (3497, 3459), (3501, 3463), (3505, 3467), (3509, 3471), (3513, 3475), (3517, 3479), (3521, 3483),
    (3525, 3487)]

def word864_6_828 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3529, 2)]

def word864_6_829 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_827 word864_6_828

def word864_6_830 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3537, 3529)]

def word864_6_831 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_829 word864_6_830

def word864_6_832 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3533, 2)]

def word864_6_833 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3533)]

def word864_6_834 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_833 word864_6_19

def word864_6_835 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_832 word864_6_834

def word864_6_836 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_827 word864_6_835

def word864_6_837 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 3537 0#64)

def word864_6_838 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_836 word864_6_837

def word864_6_839 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))))),
  Flapjack.Spt.ln)), word864_6_831, 864, 58)) (some 68) ([2]) (some (2, word864_6_838, 864, 59))

def word864_6_840 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_826 word864_6_839

def word864_6_841 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_825 word864_6_840

def word864_6_842 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_824 word864_6_841

def word864_6_843 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_842 word864_6_29

def word864_6_844 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 3545 Flapjack.WordStore.heapLength

def word864_6_845 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 3549 3545 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_846 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_844 word864_6_845

def word864_6_847 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 3553 3549

def word864_6_848 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_846 word864_6_847

def word864_6_849 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 3557 (Flapjack.WordLangAddr.addr 3553 18446744073709551200#64))

def word864_6_850 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_848 word864_6_849

def word864_6_851 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 3561 (Flapjack.WordLangAddr.addr 3557 56#64))

def word864_6_852 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_850 word864_6_851

def word864_6_853 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_843 word864_6_852

def word864_6_854 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3565, 3545)]

def word864_6_855 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3569, 3549)]

def word864_6_856 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_854 word864_6_855

def word864_6_857 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3573, 3553)]

def word864_6_858 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_856 word864_6_857

def word864_6_859 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3577, 3557)]

def word864_6_860 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_858 word864_6_859

def word864_6_861 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 3581 (Flapjack.WordLangAddr.addr 3577 64#64))

def word864_6_862 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_860 word864_6_861

def word864_6_863 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_853 word864_6_862

def word864_6_864 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3585, 3537)]

def word864_6_865 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_863 word864_6_864

def word864_6_866 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3591, 3493), (3595, 3497), (3599, 3501), (3603, 3505), (3607, 3509), (3611, 3513), (3615, 3517), (3619, 3521),
    (3623, 3585), (3627, 3525)]

def word864_6_867 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3561), (4, 3581), (6, 3585)]

def word864_6_868 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3633, 3591), (3637, 3595), (3641, 3599), (3645, 3603), (3649, 3607), (3653, 3611), (3657, 3615), (3661, 3619),
    (3665, 3623), (3669, 3627)]

def word864_6_869 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3677, 2)]

def word864_6_870 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3677)]

def word864_6_871 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_870 word864_6_19

def word864_6_872 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_869 word864_6_871

def word864_6_873 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_868 word864_6_872

def word864_6_874 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
                      Flapjack.Spt.ln))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
                      Flapjack.Spt.ln))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_868, 864, 60)) (some 843) ([2, 4, 6]) (some (2, word864_6_873, 864, 61))

def word864_6_875 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_867 word864_6_874

def word864_6_876 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_866 word864_6_875

def word864_6_877 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_865 word864_6_876

def word864_6_878 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_877 word864_6_29

def word864_6_879 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 3693 32#64)

def word864_6_880 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_878 word864_6_879

def word864_6_881 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3699, 3633), (3703, 3637), (3707, 3641), (3711, 3645), (3715, 3649), (3719, 3653), (3723, 3657), (3727, 3661),
    (3731, 3665), (3735, 3669)]

def word864_6_882 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3693)]

def word864_6_883 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3741, 3699), (3745, 3703), (3749, 3707), (3753, 3711), (3757, 3715), (3761, 3719), (3765, 3723), (3769, 3727),
    (3773, 3731), (3777, 3735)]

def word864_6_884 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3781, 2)]

def word864_6_885 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_883 word864_6_884

def word864_6_886 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3789, 3781)]

def word864_6_887 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_885 word864_6_886

def word864_6_888 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3785, 2)]

def word864_6_889 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3785)]

def word864_6_890 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_889 word864_6_19

def word864_6_891 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_888 word864_6_890

def word864_6_892 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_883 word864_6_891

def word864_6_893 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 3789 0#64)

def word864_6_894 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_892 word864_6_893

def word864_6_895 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))))))),
  Flapjack.Spt.ln)), word864_6_887, 864, 62)) (some 68) ([2]) (some (2, word864_6_894, 864, 63))

def word864_6_896 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_882 word864_6_895

def word864_6_897 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_881 word864_6_896

def word864_6_898 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_880 word864_6_897

def word864_6_899 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_898 word864_6_29

def word864_6_900 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3797, 3745)]

def word864_6_901 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_899 word864_6_900

def word864_6_902 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3801, 3757)]

def word864_6_903 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_901 word864_6_902

def word864_6_904 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3805, 3789)]

def word864_6_905 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_903 word864_6_904

def word864_6_906 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3811, 3741), (3815, 3749), (3819, 3753), (3823, 3761), (3827, 3765), (3831, 3805), (3835, 3769), (3839, 3773),
    (3843, 3777)]

def word864_6_907 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3797), (4, 3801), (6, 3805)]

def word864_6_908 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3849, 3811), (3853, 3815), (3857, 3819), (3861, 3823), (3865, 3827), (3869, 3831), (3873, 3835), (3877, 3839),
    (3881, 3843)]

def word864_6_909 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3889, 2)]

def word864_6_910 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3889)]

def word864_6_911 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_910 word864_6_19

def word864_6_912 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_909 word864_6_911

def word864_6_913 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_908 word864_6_912

def word864_6_914 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))))))),
  Flapjack.Spt.ln)), word864_6_908, 864, 64)) (some 158) ([2, 4, 6]) (some (2, word864_6_913, 864, 65))

def word864_6_915 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_907 word864_6_914

def word864_6_916 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_906 word864_6_915

def word864_6_917 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_905 word864_6_916

def word864_6_918 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_917 word864_6_29

def word864_6_919 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 3901 Flapjack.WordStore.heapLength

def word864_6_920 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 3905 3901 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_921 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_919 word864_6_920

def word864_6_922 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 3909 3905

def word864_6_923 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_921 word864_6_922

def word864_6_924 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 3913 (Flapjack.WordLangAddr.addr 3909 18446744073709551200#64))

def word864_6_925 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_923 word864_6_924

def word864_6_926 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 3917 (Flapjack.WordLangAddr.addr 3913 0#64))

def word864_6_927 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_925 word864_6_926

def word864_6_928 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_918 word864_6_927

def word864_6_929 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3921, 3901)]

def word864_6_930 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3925, 3905)]

def word864_6_931 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_929 word864_6_930

def word864_6_932 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3929, 3909)]

def word864_6_933 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_931 word864_6_932

def word864_6_934 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3933, 3913)]

def word864_6_935 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_933 word864_6_934

def word864_6_936 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 3937 (Flapjack.WordLangAddr.addr 3933 8#64))

def word864_6_937 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_935 word864_6_936

def word864_6_938 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_928 word864_6_937

def word864_6_939 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3943, 3849), (3947, 3853), (3951, 3857), (3955, 3861), (3959, 3865), (3963, 3869), (3967, 3873), (3971, 3877),
    (3975, 3881)]

def word864_6_940 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 3917), (4, 3937)]

def word864_6_941 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(3981, 3943), (3985, 3947), (3989, 3951), (3993, 3955), (3997, 3959), (4001, 3963), (4005, 3967), (4009, 3971),
    (4013, 3975)]

def word864_6_942 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4017, 2)]

def word864_6_943 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_941 word864_6_942

def word864_6_944 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4025, 4017)]

def word864_6_945 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_943 word864_6_944

def word864_6_946 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4021, 2)]

def word864_6_947 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4021)]

def word864_6_948 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_947 word864_6_19

def word864_6_949 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_946 word864_6_948

def word864_6_950 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_941 word864_6_949

def word864_6_951 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4025 0#64)

def word864_6_952 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_950 word864_6_951

def word864_6_953 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))))),
  Flapjack.Spt.ln)), word864_6_945, 864, 66)) (some 93) ([2, 4]) (some (2, word864_6_952, 864, 67))

def word864_6_954 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_940 word864_6_953

def word864_6_955 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_939 word864_6_954

def word864_6_956 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_938 word864_6_955

def word864_6_957 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_956 word864_6_29

def word864_6_958 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4033, 4025)]

def word864_6_959 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_957 word864_6_958

def word864_6_960 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4037, 3985)]

def word864_6_961 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4041 (Flapjack.WordLangAddr.addr 4037 112#64))

def word864_6_962 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_960 word864_6_961

def word864_6_963 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_959 word864_6_962

def word864_6_964 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4053 110#64)

def word864_6_965 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_964

def word864_6_966 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4057, 4053)]

def word864_6_967 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4057)

def word864_6_968 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_966 word864_6_967

def word864_6_969 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_965 word864_6_968

def word864_6_970 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4061 4#64)

def word864_6_971 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_969 word864_6_970

def word864_6_972 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4061)]

def word864_6_973 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_972 word864_6_19

def word864_6_974 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_971 word864_6_973

def word864_6_975 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def word864_6_976 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4033 (Flapjack.WordRegImm.reg 4041) word864_6_974 word864_6_975

def word864_6_977 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_976 word864_6_29

def word864_6_978 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_963 word864_6_977

def word864_6_979 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_978 word864_6_29

def word864_6_980 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4089, 3997)]

def word864_6_981 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_979 word864_6_980

def word864_6_982 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4093, 4037)]

def word864_6_983 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4097 (Flapjack.WordLangAddr.addr 4093 40#64))

def word864_6_984 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_982 word864_6_983

def word864_6_985 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_981 word864_6_984

def word864_6_986 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4105 32#64)

def word864_6_987 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_985 word864_6_986

def word864_6_988 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(4111, 3981), (4115, 4093), (4119, 3989), (4123, 3993), (4127, 4001), (4131, 4005), (4135, 4009), (4139, 4013)]

def word864_6_989 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4089), (4, 4097), (6, 4105)]

def word864_6_990 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(4145, 4111), (4149, 4115), (4153, 4119), (4157, 4123), (4161, 4127), (4165, 4131), (4169, 4135), (4173, 4139)]

def word864_6_991 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4177, 2)]

def word864_6_992 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_990 word864_6_991

def word864_6_993 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4189, 4177)]

def word864_6_994 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_992 word864_6_993

def word864_6_995 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4181, 2)]

def word864_6_996 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4181)]

def word864_6_997 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_996 word864_6_19

def word864_6_998 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_995 word864_6_997

def word864_6_999 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_990 word864_6_998

def word864_6_1000 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4189 0#64)

def word864_6_1001 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_999 word864_6_1000

def word864_6_1002 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word864_6_994, 864, 68)) (some 79) ([2, 4, 6]) (some (2, word864_6_1001, 864, 69))

def word864_6_1003 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_989 word864_6_1002

def word864_6_1004 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_988 word864_6_1003

def word864_6_1005 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_987 word864_6_1004

def word864_6_1006 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1005 word864_6_29

def word864_6_1007 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4193, 4189)]

def word864_6_1008 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1006 word864_6_1007

def word864_6_1009 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4197 0#64)

def word864_6_1010 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1008 word864_6_1009

def word864_6_1011 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4209 111#64)

def word864_6_1012 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_1011

def word864_6_1013 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4213, 4209)]

def word864_6_1014 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4213)

def word864_6_1015 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1013 word864_6_1014

def word864_6_1016 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1012 word864_6_1015

def word864_6_1017 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4217 4#64)

def word864_6_1018 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1016 word864_6_1017

def word864_6_1019 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4217)]

def word864_6_1020 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1019 word864_6_19

def word864_6_1021 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1018 word864_6_1020

def word864_6_1022 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4193 (Flapjack.WordRegImm.reg 4197) word864_6_1021 word864_6_975

def word864_6_1023 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1022 word864_6_29

def word864_6_1024 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1010 word864_6_1023

def word864_6_1025 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1024 word864_6_29

def word864_6_1026 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4245, 4165)]

def word864_6_1027 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1025 word864_6_1026

def word864_6_1028 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4249, 4149)]

def word864_6_1029 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4253 (Flapjack.WordLangAddr.addr 4249 32#64))

def word864_6_1030 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1028 word864_6_1029

def word864_6_1031 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1027 word864_6_1030

def word864_6_1032 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4261 32#64)

def word864_6_1033 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1031 word864_6_1032

def word864_6_1034 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(4267, 4145), (4271, 4249), (4275, 4153), (4279, 4157), (4283, 4161), (4287, 4169), (4291, 4173)]

def word864_6_1035 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4245), (4, 4253), (6, 4261)]

def word864_6_1036 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(4297, 4267), (4301, 4271), (4305, 4275), (4309, 4279), (4313, 4283), (4317, 4287), (4321, 4291)]

def word864_6_1037 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4325, 2)]

def word864_6_1038 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1036 word864_6_1037

def word864_6_1039 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4337, 4325)]

def word864_6_1040 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1038 word864_6_1039

def word864_6_1041 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4329, 2)]

def word864_6_1042 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4329)]

def word864_6_1043 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1042 word864_6_19

def word864_6_1044 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1041 word864_6_1043

def word864_6_1045 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1036 word864_6_1044

def word864_6_1046 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4337 0#64)

def word864_6_1047 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1045 word864_6_1046

def word864_6_1048 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))))),
  Flapjack.Spt.ln)), word864_6_1040, 864, 70)) (some 79) ([2, 4, 6]) (some (2, word864_6_1047, 864, 71))

def word864_6_1049 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1035 word864_6_1048

def word864_6_1050 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1034 word864_6_1049

def word864_6_1051 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1033 word864_6_1050

def word864_6_1052 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1051 word864_6_29

def word864_6_1053 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4341, 4337)]

def word864_6_1054 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1052 word864_6_1053

def word864_6_1055 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4345 0#64)

def word864_6_1056 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1054 word864_6_1055

def word864_6_1057 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4357 112#64)

def word864_6_1058 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_1057

def word864_6_1059 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4361, 4357)]

def word864_6_1060 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4361)

def word864_6_1061 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1059 word864_6_1060

def word864_6_1062 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1058 word864_6_1061

def word864_6_1063 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4365 4#64)

def word864_6_1064 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1062 word864_6_1063

def word864_6_1065 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4365)]

def word864_6_1066 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1065 word864_6_19

def word864_6_1067 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1064 word864_6_1066

def word864_6_1068 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4341 (Flapjack.WordRegImm.reg 4345) word864_6_1067 word864_6_975

def word864_6_1069 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1068 word864_6_29

def word864_6_1070 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1056 word864_6_1069

def word864_6_1071 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1070 word864_6_29

def word864_6_1072 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4393, 4321)]

def word864_6_1073 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1071 word864_6_1072

def word864_6_1074 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4397, 4301)]

def word864_6_1075 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4401 (Flapjack.WordLangAddr.addr 4397 48#64))

def word864_6_1076 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1074 word864_6_1075

def word864_6_1077 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1073 word864_6_1076

def word864_6_1078 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4409 32#64)

def word864_6_1079 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1077 word864_6_1078

def word864_6_1080 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4415, 4297), (4419, 4397), (4423, 4305), (4427, 4309), (4431, 4313), (4435, 4317)]

def word864_6_1081 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4393), (4, 4401), (6, 4409)]

def word864_6_1082 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4441, 4415), (4445, 4419), (4449, 4423), (4453, 4427), (4457, 4431), (4461, 4435)]

def word864_6_1083 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4465, 2)]

def word864_6_1084 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1082 word864_6_1083

def word864_6_1085 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4477, 4465)]

def word864_6_1086 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1084 word864_6_1085

def word864_6_1087 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4469, 2)]

def word864_6_1088 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4469)]

def word864_6_1089 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1088 word864_6_19

def word864_6_1090 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1087 word864_6_1089

def word864_6_1091 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1082 word864_6_1090

def word864_6_1092 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4477 0#64)

def word864_6_1093 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1091 word864_6_1092

def word864_6_1094 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)))))),
  Flapjack.Spt.ln)), word864_6_1086, 864, 72)) (some 79) ([2, 4, 6]) (some (2, word864_6_1093, 864, 73))

def word864_6_1095 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1081 word864_6_1094

def word864_6_1096 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1080 word864_6_1095

def word864_6_1097 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1079 word864_6_1096

def word864_6_1098 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1097 word864_6_29

def word864_6_1099 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4481, 4477)]

def word864_6_1100 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1098 word864_6_1099

def word864_6_1101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4485 0#64)

def word864_6_1102 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1100 word864_6_1101

def word864_6_1103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4497 113#64)

def word864_6_1104 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_1103

def word864_6_1105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4501, 4497)]

def word864_6_1106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4501)

def word864_6_1107 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1105 word864_6_1106

def word864_6_1108 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1104 word864_6_1107

def word864_6_1109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4505 4#64)

def word864_6_1110 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1108 word864_6_1109

def word864_6_1111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4505)]

def word864_6_1112 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1111 word864_6_19

def word864_6_1113 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1110 word864_6_1112

def word864_6_1114 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4481 (Flapjack.WordRegImm.reg 4485) word864_6_1113 word864_6_975

def word864_6_1115 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1114 word864_6_29

def word864_6_1116 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1102 word864_6_1115

def word864_6_1117 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1116 word864_6_29

def word864_6_1118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4533, 4453)]

def word864_6_1119 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1117 word864_6_1118

def word864_6_1120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4537, 4445)]

def word864_6_1121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4541 (Flapjack.WordLangAddr.addr 4537 56#64))

def word864_6_1122 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1120 word864_6_1121

def word864_6_1123 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1119 word864_6_1122

def word864_6_1124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4549 256#64)

def word864_6_1125 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1123 word864_6_1124

def word864_6_1126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4555, 4441), (4559, 4537), (4563, 4449), (4567, 4457), (4571, 4461)]

def word864_6_1127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4533), (4, 4541), (6, 4549)]

def word864_6_1128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4577, 4555), (4581, 4559), (4585, 4563), (4589, 4567), (4593, 4571)]

def word864_6_1129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4597, 2)]

def word864_6_1130 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1128 word864_6_1129

def word864_6_1131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4609, 4597)]

def word864_6_1132 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1130 word864_6_1131

def word864_6_1133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4601, 2)]

def word864_6_1134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4601)]

def word864_6_1135 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1134 word864_6_19

def word864_6_1136 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1133 word864_6_1135

def word864_6_1137 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1128 word864_6_1136

def word864_6_1138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4609 0#64)

def word864_6_1139 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1137 word864_6_1138

def word864_6_1140 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word864_6_1132, 864, 74)) (some 79) ([2, 4, 6]) (some (2, word864_6_1139, 864, 75))

def word864_6_1141 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1127 word864_6_1140

def word864_6_1142 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1126 word864_6_1141

def word864_6_1143 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1125 word864_6_1142

def word864_6_1144 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1143 word864_6_29

def word864_6_1145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4613, 4609)]

def word864_6_1146 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1144 word864_6_1145

def word864_6_1147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4617 0#64)

def word864_6_1148 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1146 word864_6_1147

def word864_6_1149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4629 114#64)

def word864_6_1150 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_1149

def word864_6_1151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4633, 4629)]

def word864_6_1152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4633)

def word864_6_1153 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1151 word864_6_1152

def word864_6_1154 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1150 word864_6_1153

def word864_6_1155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4637 4#64)

def word864_6_1156 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1154 word864_6_1155

def word864_6_1157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4637)]

def word864_6_1158 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1157 word864_6_19

def word864_6_1159 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1156 word864_6_1158

def word864_6_1160 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4613 (Flapjack.WordRegImm.reg 4617) word864_6_1159 word864_6_975

def word864_6_1161 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1160 word864_6_29

def word864_6_1162 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1148 word864_6_1161

def word864_6_1163 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1162 word864_6_29

def word864_6_1164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4665, 4585)]

def word864_6_1165 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1163 word864_6_1164

def word864_6_1166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4669, 4581)]

def word864_6_1167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4673 (Flapjack.WordLangAddr.addr 4669 192#64))

def word864_6_1168 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1166 word864_6_1167

def word864_6_1169 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1165 word864_6_1168

def word864_6_1170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4681 32#64)

def word864_6_1171 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1169 word864_6_1170

def word864_6_1172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4687, 4577), (4691, 4669), (4695, 4589), (4699, 4593)]

def word864_6_1173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4665), (4, 4673), (6, 4681)]

def word864_6_1174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4705, 4687), (4709, 4691), (4713, 4695), (4717, 4699)]

def word864_6_1175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4721, 2)]

def word864_6_1176 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1174 word864_6_1175

def word864_6_1177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4733, 4721)]

def word864_6_1178 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1176 word864_6_1177

def word864_6_1179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4725, 2)]

def word864_6_1180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4725)]

def word864_6_1181 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1180 word864_6_19

def word864_6_1182 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1179 word864_6_1181

def word864_6_1183 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1174 word864_6_1182

def word864_6_1184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4733 0#64)

def word864_6_1185 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1183 word864_6_1184

def word864_6_1186 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                      Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                      Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                      Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                      Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word864_6_1178, 864, 76)) (some 79) ([2, 4, 6]) (some (2, word864_6_1185, 864, 77))

def word864_6_1187 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1173 word864_6_1186

def word864_6_1188 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1172 word864_6_1187

def word864_6_1189 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1171 word864_6_1188

def word864_6_1190 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1189 word864_6_29

def word864_6_1191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4737, 4733)]

def word864_6_1192 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1190 word864_6_1191

def word864_6_1193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4741 0#64)

def word864_6_1194 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1192 word864_6_1193

def word864_6_1195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4753 115#64)

def word864_6_1196 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_1195

def word864_6_1197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4757, 4753)]

def word864_6_1198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4757)

def word864_6_1199 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1197 word864_6_1198

def word864_6_1200 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1196 word864_6_1199

def word864_6_1201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4761 4#64)

def word864_6_1202 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1200 word864_6_1201

def word864_6_1203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4761)]

def word864_6_1204 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1203 word864_6_19

def word864_6_1205 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1202 word864_6_1204

def word864_6_1206 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4737 (Flapjack.WordRegImm.reg 4741) word864_6_1205 word864_6_975

def word864_6_1207 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1206 word864_6_29

def word864_6_1208 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1194 word864_6_1207

def word864_6_1209 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1208 word864_6_29

def word864_6_1210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.get 4789 Flapjack.WordStore.heapLength

def word864_6_1211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith
    (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 4793 4789 (Flapjack.WordRegImm.imm 1#64)))

def word864_6_1212 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1210 word864_6_1211

def word864_6_1213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.opCurrHeap Flapjack.BinOp.add 4797 4793

def word864_6_1214 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1212 word864_6_1213

def word864_6_1215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4801 (Flapjack.WordLangAddr.addr 4797 18446744073709551200#64))

def word864_6_1216 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1214 word864_6_1215

def word864_6_1217 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4805 (Flapjack.WordLangAddr.addr 4801 48#64))

def word864_6_1218 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1216 word864_6_1217

def word864_6_1219 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1209 word864_6_1218

def word864_6_1220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4809, 4709)]

def word864_6_1221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4813 (Flapjack.WordLangAddr.addr 4809 200#64))

def word864_6_1222 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1220 word864_6_1221

def word864_6_1223 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1219 word864_6_1222

def word864_6_1224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4825 116#64)

def word864_6_1225 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_1224

def word864_6_1226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4829, 4825)]

def word864_6_1227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4829)

def word864_6_1228 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1226 word864_6_1227

def word864_6_1229 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1225 word864_6_1228

def word864_6_1230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4833 4#64)

def word864_6_1231 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1229 word864_6_1230

def word864_6_1232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4833)]

def word864_6_1233 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1232 word864_6_19

def word864_6_1234 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1231 word864_6_1233

def word864_6_1235 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4805 (Flapjack.WordRegImm.reg 4813) word864_6_1234 word864_6_975

def word864_6_1236 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1235 word864_6_29

def word864_6_1237 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1223 word864_6_1236

def word864_6_1238 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1237 word864_6_29

def word864_6_1239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4861, 4717)]

def word864_6_1240 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1238 word864_6_1239

def word864_6_1241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4865, 4809)]

def word864_6_1242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4869 (Flapjack.WordLangAddr.addr 4865 224#64))

def word864_6_1243 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1241 word864_6_1242

def word864_6_1244 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1240 word864_6_1243

def word864_6_1245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4877 32#64)

def word864_6_1246 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1244 word864_6_1245

def word864_6_1247 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4883, 4705), (4887, 4865), (4891, 4713)]

def word864_6_1248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4861), (4, 4869), (6, 4877)]

def word864_6_1249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4897, 4883), (4901, 4887), (4905, 4891)]

def word864_6_1250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4909, 2)]

def word864_6_1251 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1249 word864_6_1250

def word864_6_1252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4921, 4909)]

def word864_6_1253 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1251 word864_6_1252

def word864_6_1254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4913, 2)]

def word864_6_1255 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4913)]

def word864_6_1256 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1255 word864_6_19

def word864_6_1257 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1254 word864_6_1256

def word864_6_1258 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1249 word864_6_1257

def word864_6_1259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4921 0#64)

def word864_6_1260 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1258 word864_6_1259

def word864_6_1261 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                      Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                      Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                      Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))
            Flapjack.Spt.ln)
          Flapjack.Spt.ln))),
  Flapjack.Spt.ln)), word864_6_1253, 864, 78)) (some 79) ([2, 4, 6]) (some (2, word864_6_1260, 864, 79))

def word864_6_1262 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1248 word864_6_1261

def word864_6_1263 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1247 word864_6_1262

def word864_6_1264 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1246 word864_6_1263

def word864_6_1265 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1264 word864_6_29

def word864_6_1266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4925, 4921)]

def word864_6_1267 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1265 word864_6_1266

def word864_6_1268 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4929 0#64)

def word864_6_1269 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1267 word864_6_1268

def word864_6_1270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4941 117#64)

def word864_6_1271 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_1270

def word864_6_1272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4945, 4941)]

def word864_6_1273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4945)

def word864_6_1274 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1272 word864_6_1273

def word864_6_1275 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1271 word864_6_1274

def word864_6_1276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4949 4#64)

def word864_6_1277 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1275 word864_6_1276

def word864_6_1278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4949)]

def word864_6_1279 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1278 word864_6_19

def word864_6_1280 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1277 word864_6_1279

def word864_6_1281 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4925 (Flapjack.WordRegImm.reg 4929) word864_6_1280 word864_6_975

def word864_6_1282 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1281 word864_6_29

def word864_6_1283 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1269 word864_6_1282

def word864_6_1284 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1283 word864_6_29

def word864_6_1285 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4977, 4905)]

def word864_6_1286 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1284 word864_6_1285

def word864_6_1287 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4981, 4901)]

def word864_6_1288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4985 (Flapjack.WordLangAddr.addr 4981 232#64))

def word864_6_1289 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1287 word864_6_1288

def word864_6_1290 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1286 word864_6_1289

def word864_6_1291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4993 32#64)

def word864_6_1292 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1290 word864_6_1291

def word864_6_1293 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4999, 4897)]

def word864_6_1294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 4977), (4, 4985), (6, 4993)]

def word864_6_1295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(5005, 4999)]

def word864_6_1296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(5009, 2)]

def word864_6_1297 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1295 word864_6_1296

def word864_6_1298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(5021, 5009)]

def word864_6_1299 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1297 word864_6_1298

def word864_6_1300 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(5013, 2)]

def word864_6_1301 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 5013)]

def word864_6_1302 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1301 word864_6_19

def word864_6_1303 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1300 word864_6_1302

def word864_6_1304 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1295 word864_6_1303

def word864_6_1305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 5021 0#64)

def word864_6_1306 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1304 word864_6_1305

def word864_6_1307 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                      Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          Flapjack.Spt.ln))),
  Flapjack.Spt.ln)), word864_6_1299, 864, 80)) (some 79) ([2, 4, 6]) (some (2, word864_6_1306, 864, 81))

def word864_6_1308 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1294 word864_6_1307

def word864_6_1309 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1293 word864_6_1308

def word864_6_1310 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1292 word864_6_1309

def word864_6_1311 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1310 word864_6_29

def word864_6_1312 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(5025, 5021)]

def word864_6_1313 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1311 word864_6_1312

def word864_6_1314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 5029 0#64)

def word864_6_1315 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1313 word864_6_1314

def word864_6_1316 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 5041 118#64)

def word864_6_1317 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_29 word864_6_1316

def word864_6_1318 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(5045, 5041)]

def word864_6_1319 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 5045)

def word864_6_1320 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1318 word864_6_1319

def word864_6_1321 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1317 word864_6_1320

def word864_6_1322 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 5049 4#64)

def word864_6_1323 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1321 word864_6_1322

def word864_6_1324 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 5049)]

def word864_6_1325 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1324 word864_6_19

def word864_6_1326 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1323 word864_6_1325

def word864_6_1327 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 5025 (Flapjack.WordRegImm.reg 5029) word864_6_1326 word864_6_975

def word864_6_1328 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1327 word864_6_29

def word864_6_1329 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1315 word864_6_1328

def word864_6_1330 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1329 word864_6_29

def word864_6_1331 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 5077 0#64)

def word864_6_1332 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1330 word864_6_1331

def word864_6_1333 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 5077)]

def word864_6_1334 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 5005 [2]

def word864_6_1335 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1333 word864_6_1334

def word864_6_1336 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_1332 word864_6_1335

def word864_6_1337 : WordLangProgHOL (BitVec 64) :=
.seq word864_6_0 word864_6_1336

def pass864_6 : WordLangProgHOL (BitVec 64) :=
word864_6_1337
theorem pass864_6_eq : WordInst.threeToTwoRegProg riscvConfig.twoRegArith (pass864_5) = pass864_6 := by
  kernel_rfl
#print axioms pass864_6_eq
end InitECandidate.Proofs.WordStages
