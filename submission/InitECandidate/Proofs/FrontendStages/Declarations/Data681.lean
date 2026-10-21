import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify665
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body681_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.const 1152#64]

def body681_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "nQ", Flapjack.Exp.var Flapjack.VarKind.local "Q",
    Flapjack.Exp.const 1152#64]

def body681_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_neg"
  [Flapjack.Exp.const 12#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nQ", Flapjack.Exp.const 384#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.const 384#64]]

def body681_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "fnum"]

def body681_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "fden"]

def body681_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body681_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_linefunc"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "R",
    Flapjack.Exp.var Flapjack.VarKind.local "P"]

def body681_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnum", Flapjack.Exp.var Flapjack.VarKind.local "fnum"]

def body681_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnum", Flapjack.Exp.var Flapjack.VarKind.local "fnum",
    Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body681_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fden", Flapjack.Exp.var Flapjack.VarKind.local "fden"]

def body681_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fden", Flapjack.Exp.var Flapjack.VarKind.local "fden",
    Flapjack.Exp.var Flapjack.VarKind.local "d"]

def body681_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_double"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "R"]

def body681_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_linefunc"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "Q",
    Flapjack.Exp.var Flapjack.VarKind.local "P"]

def body681_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_add"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "R",
    Flapjack.Exp.var Flapjack.VarKind.local "Q"]

def body681_14 : Prog (BitVec 64) :=
.seq body681_10 body681_13

def body681_15 : Prog (BitVec 64) :=
.seq body681_8 body681_14

def body681_16 : Prog (BitVec 64) :=
.seq body681_12 body681_15

def body681_17 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body681_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.const 11637723931993326632#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "i"),
      Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 1#64)) body681_16 body681_17

def body681_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_linefunc"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "nQ",
    Flapjack.Exp.var Flapjack.VarKind.local "P"]

def body681_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_add"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "R",
    Flapjack.Exp.var Flapjack.VarKind.local "nQ"]

def body681_21 : Prog (BitVec 64) :=
.seq body681_10 body681_20

def body681_22 : Prog (BitVec 64) :=
.seq body681_8 body681_21

def body681_23 : Prog (BitVec 64) :=
.seq body681_19 body681_22

def body681_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.const 290499802545784960#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "i"),
      Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 1#64)) body681_23 body681_17

def body681_25 : Prog (BitVec 64) :=
.seq body681_18 body681_24

def body681_26 : Prog (BitVec 64) :=
.seq body681_11 body681_25

def body681_27 : Prog (BitVec 64) :=
.seq body681_10 body681_26

def body681_28 : Prog (BitVec 64) :=
.seq body681_9 body681_27

def body681_29 : Prog (BitVec 64) :=
.seq body681_8 body681_28

def body681_30 : Prog (BitVec 64) :=
.seq body681_7 body681_29

def body681_31 : Prog (BitVec 64) :=
.seq body681_6 body681_30

def body681_32 : Prog (BitVec 64) :=
.seq body681_5 body681_31

def body681_33 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body681_32

def body681_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "Q1", Flapjack.Exp.var Flapjack.VarKind.local "Q"]

def body681_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "Q1", Flapjack.Exp.const 384#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.const 384#64]]

def body681_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "Q1",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 384#64]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "Q",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 384#64]]]

def body681_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "nQ2", Flapjack.Exp.var Flapjack.VarKind.local "Q1"]

def body681_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nQ2", Flapjack.Exp.const 384#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "Q1", Flapjack.Exp.const 384#64]]

def body681_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_neg"
  [Flapjack.Exp.const 12#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nQ2", Flapjack.Exp.const 384#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nQ2", Flapjack.Exp.const 384#64]]

def body681_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "nQ2",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 384#64]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "Q1",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 384#64]]]

def body681_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_linefunc"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "Q1",
    Flapjack.Exp.var Flapjack.VarKind.local "P"]

def body681_42 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_add"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "R",
    Flapjack.Exp.var Flapjack.VarKind.local "Q1"]

def body681_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_linefunc"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "nQ2",
    Flapjack.Exp.var Flapjack.VarKind.local "P"]

def body681_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body681_45 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body681_46 : Prog (BitVec 64) :=
.seq body681_44 body681_45

def body681_47 : Prog (BitVec 64) :=
.seq body681_10 body681_46

def body681_48 : Prog (BitVec 64) :=
.seq body681_8 body681_47

def body681_49 : Prog (BitVec 64) :=
.seq body681_43 body681_48

def body681_50 : Prog (BitVec 64) :=
.seq body681_42 body681_49

def body681_51 : Prog (BitVec 64) :=
.seq body681_10 body681_50

def body681_52 : Prog (BitVec 64) :=
.seq body681_8 body681_51

def body681_53 : Prog (BitVec 64) :=
.seq body681_41 body681_52

def body681_54 : Prog (BitVec 64) :=
.seq body681_40 body681_53

def body681_55 : Prog (BitVec 64) :=
.seq body681_39 body681_54

def body681_56 : Prog (BitVec 64) :=
.seq body681_38 body681_55

def body681_57 : Prog (BitVec 64) :=
.seq body681_37 body681_56

def body681_58 : Prog (BitVec 64) :=
.seq body681_36 body681_57

def body681_59 : Prog (BitVec 64) :=
.seq body681_35 body681_58

def body681_60 : Prog (BitVec 64) :=
.seq body681_34 body681_59

def body681_61 : Prog (BitVec 64) :=
.seq body681_33 body681_60

def body681_62 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 64#64) body681_61

def body681_63 : Prog (BitVec 64) :=
.seq body681_4 body681_62

def body681_64 : Prog (BitVec 64) :=
.seq body681_3 body681_63

def body681_65 : Prog (BitVec 64) :=
.seq body681_2 body681_64

def body681_66 : Prog (BitVec 64) :=
.seq body681_1 body681_65

def body681_67 : Prog (BitVec 64) :=
.seq body681_0 body681_66

def body681_68 : Prog (BitVec 64) :=
.decCall ("d") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body681_67

def body681_69 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body681_68

def body681_70 : Prog (BitVec 64) :=
.decCall ("nQ2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body681_69

def body681_71 : Prog (BitVec 64) :=
.decCall ("Q1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body681_70

def body681_72 : Prog (BitVec 64) :=
.decCall ("nQ") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body681_71

def body681_73 : Prog (BitVec 64) :=
.decCall ("R") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body681_72

def body681_74 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body681_73

def body681_75 : Prog (BitVec 64) :=
.seq body681_0 body681_1

def body681_76 : Prog (BitVec 64) :=
.seq body681_75 body681_2

def body681_77 : Prog (BitVec 64) :=
.seq body681_76 body681_3

def body681_78 : Prog (BitVec 64) :=
.seq body681_77 body681_4

def body681_79 : Prog (BitVec 64) :=
.seq body681_5 body681_6

def body681_80 : Prog (BitVec 64) :=
.seq body681_79 body681_7

def body681_81 : Prog (BitVec 64) :=
.seq body681_80 body681_8

def body681_82 : Prog (BitVec 64) :=
.seq body681_81 body681_9

def body681_83 : Prog (BitVec 64) :=
.seq body681_82 body681_10

def body681_84 : Prog (BitVec 64) :=
.seq body681_83 body681_11

def body681_85 : Prog (BitVec 64) :=
.seq body681_12 body681_8

def body681_86 : Prog (BitVec 64) :=
.seq body681_85 body681_10

def body681_87 : Prog (BitVec 64) :=
.seq body681_86 body681_13

def body681_88 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.const 11637723931993326632#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "i"),
      Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 1#64)) body681_87 body681_17

def body681_89 : Prog (BitVec 64) :=
.seq body681_84 body681_88

def body681_90 : Prog (BitVec 64) :=
.seq body681_19 body681_8

def body681_91 : Prog (BitVec 64) :=
.seq body681_90 body681_10

def body681_92 : Prog (BitVec 64) :=
.seq body681_91 body681_20

def body681_93 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.const 290499802545784960#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "i"),
      Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 1#64)) body681_92 body681_17

def body681_94 : Prog (BitVec 64) :=
.seq body681_89 body681_93

def body681_95 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body681_94

def body681_96 : Prog (BitVec 64) :=
.seq body681_95 body681_34

def body681_97 : Prog (BitVec 64) :=
.seq body681_96 body681_35

def body681_98 : Prog (BitVec 64) :=
.seq body681_97 body681_36

def body681_99 : Prog (BitVec 64) :=
.seq body681_98 body681_37

def body681_100 : Prog (BitVec 64) :=
.seq body681_99 body681_38

def body681_101 : Prog (BitVec 64) :=
.seq body681_100 body681_39

def body681_102 : Prog (BitVec 64) :=
.seq body681_101 body681_40

def body681_103 : Prog (BitVec 64) :=
.seq body681_102 body681_41

def body681_104 : Prog (BitVec 64) :=
.seq body681_103 body681_8

def body681_105 : Prog (BitVec 64) :=
.seq body681_104 body681_10

def body681_106 : Prog (BitVec 64) :=
.seq body681_105 body681_42

def body681_107 : Prog (BitVec 64) :=
.seq body681_106 body681_43

def body681_108 : Prog (BitVec 64) :=
.seq body681_107 body681_8

def body681_109 : Prog (BitVec 64) :=
.seq body681_108 body681_10

def body681_110 : Prog (BitVec 64) :=
.seq body681_109 body681_44

def body681_111 : Prog (BitVec 64) :=
.seq body681_110 body681_45

def body681_112 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 64#64) body681_111

def body681_113 : Prog (BitVec 64) :=
.seq body681_78 body681_112

def body681_114 : Prog (BitVec 64) :=
.decCall ("d") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body681_113

def body681_115 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body681_114

def body681_116 : Prog (BitVec 64) :=
.decCall ("nQ2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body681_115

def body681_117 : Prog (BitVec 64) :=
.decCall ("Q1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body681_116

def body681_118 : Prog (BitVec 64) :=
.decCall ("nQ") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body681_117

def body681_119 : Prog (BitVec 64) :=
.decCall ("R") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body681_118

def body681_120 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body681_119

def originalData681 : Decl (BitVec 64) :=
.function { name := "bn254_miller_raw", inline := false, exported := false, params := [("fnum", Flapjack.Shape.one), ("fden", Flapjack.Shape.one), ("Q", Flapjack.Shape.one), ("P", Flapjack.Shape.one)], body := body681_74, returnShape := (Flapjack.Shape.one) }
def simplifiedData681 : Decl (BitVec 64) :=
.function { name := "bn254_miller_raw", inline := false, exported := false, params := [("fnum", Flapjack.Shape.one), ("fden", Flapjack.Shape.one), ("Q", Flapjack.Shape.one), ("P", Flapjack.Shape.one)], body := body681_120, returnShape := (Flapjack.Shape.one) }
def original681 := Pancake.PanLang.declToHOL originalData681
def simplified681 := Pancake.PanLang.declToHOL simplifiedData681
end InitECandidate.Proofs.FrontendStages.Declarations
