import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify672
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body688_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn254_init" []

def body688_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "anum"]

def body688_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "aden"]

def body688_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body688_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 2#64)

def body688_5 : Prog (BitVec 64) :=
.seq body688_3 body688_4

def body688_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body688_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "e1") (Flapjack.Exp.const 0#64)) body688_5 body688_6

def body688_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "e2") (Flapjack.Exp.const 0#64)) body688_5 body688_6

def body688_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_mul"
  [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "g1",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 4891460686036598785#64, Flapjack.Exp.const 2896914383306846353#64,
        Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]

def body688_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i1") (Flapjack.Exp.const 0#64)) body688_5 body688_6

def body688_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_mul"
  [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "g2",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 4891460686036598785#64, Flapjack.Exp.const 2896914383306846353#64,
        Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]

def body688_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i2") (Flapjack.Exp.const 0#64)) body688_5 body688_6

def body688_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_twist"
  [Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.var Flapjack.VarKind.local "g2"]

def body688_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_cast"
  [Flapjack.Exp.var Flapjack.VarKind.local "P", Flapjack.Exp.var Flapjack.VarKind.local "g1"]

def body688_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn254_miller_raw"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnum", Flapjack.Exp.var Flapjack.VarKind.local "fden",
    Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.var Flapjack.VarKind.local "P"]

def body688_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "anum", Flapjack.Exp.var Flapjack.VarKind.local "anum",
    Flapjack.Exp.var Flapjack.VarKind.local "fnum"]

def body688_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "aden", Flapjack.Exp.var Flapjack.VarKind.local "aden",
    Flapjack.Exp.var Flapjack.VarKind.local "fden"]

def body688_18 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "nontrivial" (Flapjack.Exp.const 1#64)

def body688_19 : Prog (BitVec 64) :=
.seq body688_17 body688_18

def body688_20 : Prog (BitVec 64) :=
.seq body688_16 body688_19

def body688_21 : Prog (BitVec 64) :=
.seq body688_15 body688_20

def body688_22 : Prog (BitVec 64) :=
.seq body688_14 body688_21

def body688_23 : Prog (BitVec 64) :=
.seq body688_13 body688_22

def body688_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.var Flapjack.VarKind.local "pinf", Flapjack.Exp.var Flapjack.VarKind.local "qinf"])
  (Flapjack.Exp.const 0#64)) body688_23 body688_6

def body688_25 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body688_26 : Prog (BitVec 64) :=
.seq body688_24 body688_25

def body688_27 : Prog (BitVec 64) :=
.decCall ("qinf") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "g2"]) body688_26

def body688_28 : Prog (BitVec 64) :=
.decCall ("pinf") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "g1"]) body688_27

def body688_29 : Prog (BitVec 64) :=
.seq body688_12 body688_28

def body688_30 : Prog (BitVec 64) :=
.decCall ("i2") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "t2"]) body688_29

def body688_31 : Prog (BitVec 64) :=
.seq body688_11 body688_30

def body688_32 : Prog (BitVec 64) :=
.seq body688_10 body688_31

def body688_33 : Prog (BitVec 64) :=
.decCall ("i1") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "t1"]) body688_32

def body688_34 : Prog (BitVec 64) :=
.seq body688_9 body688_33

def body688_35 : Prog (BitVec 64) :=
.seq body688_8 body688_34

def body688_36 : Prog (BitVec 64) :=
.decCall ("e2") (Flapjack.Shape.one) ("bn254_parse_g2") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "chunk", Flapjack.Exp.const 64#64],
  Flapjack.Exp.var Flapjack.VarKind.local "g2"]) body688_35

def body688_37 : Prog (BitVec 64) :=
.seq body688_7 body688_36

def body688_38 : Prog (BitVec 64) :=
.decCall ("e1") (Flapjack.Shape.one) ("bn254_parse_g1") ([Flapjack.Exp.var Flapjack.VarKind.local "chunk", Flapjack.Exp.var Flapjack.VarKind.local "g1"]) body688_37

def body688_39 : Prog (BitVec 64) :=
.dec ("chunk") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "pairs",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 192#64]]) body688_38

def body688_40 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n_pairs")) body688_39

def body688_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_inv"
  [Flapjack.Exp.var Flapjack.VarKind.local "aden", Flapjack.Exp.var Flapjack.VarKind.local "aden"]

def body688_42 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "anum", Flapjack.Exp.var Flapjack.VarKind.local "anum",
    Flapjack.Exp.var Flapjack.VarKind.local "aden"]

def body688_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_pow_words"
  [Flapjack.Exp.var Flapjack.VarKind.local "res", Flapjack.Exp.var Flapjack.VarKind.local "anum",
    Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 44#64]

def body688_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnum", Flapjack.Exp.const 384#64]

def body688_45 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "fnum")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def body688_46 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "memeq"
  [Flapjack.Exp.var Flapjack.VarKind.local "res", Flapjack.Exp.var Flapjack.VarKind.local "fnum",
    Flapjack.Exp.const 384#64]

def body688_47 : Prog (BitVec 64) :=
.seq body688_45 body688_46

def body688_48 : Prog (BitVec 64) :=
.seq body688_44 body688_47

def body688_49 : Prog (BitVec 64) :=
.seq body688_43 body688_48

def body688_50 : Prog (BitVec 64) :=
.seq body688_42 body688_49

def body688_51 : Prog (BitVec 64) :=
.seq body688_41 body688_50

def body688_52 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nontrivial") (Flapjack.Exp.const 1#64)) body688_51 body688_6

def body688_53 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "ok")

def body688_54 : Prog (BitVec 64) :=
.seq body688_3 body688_53

def body688_55 : Prog (BitVec 64) :=
.seq body688_52 body688_54

def body688_56 : Prog (BitVec 64) :=
.dec ("ok") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body688_55

def body688_57 : Prog (BitVec 64) :=
.seq body688_40 body688_56

def body688_58 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body688_57

def body688_59 : Prog (BitVec 64) :=
.dec ("nontrivial") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body688_58

def body688_60 : Prog (BitVec 64) :=
.seq body688_2 body688_59

def body688_61 : Prog (BitVec 64) :=
.seq body688_1 body688_60

def body688_62 : Prog (BitVec 64) :=
.decCall ("res") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body688_61

def body688_63 : Prog (BitVec 64) :=
.decCall ("aden") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body688_62

def body688_64 : Prog (BitVec 64) :=
.decCall ("anum") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body688_63

def body688_65 : Prog (BitVec 64) :=
.decCall ("fden") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body688_64

def body688_66 : Prog (BitVec 64) :=
.decCall ("fnum") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body688_65

def body688_67 : Prog (BitVec 64) :=
.decCall ("P") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body688_66

def body688_68 : Prog (BitVec 64) :=
.decCall ("Q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body688_67

def body688_69 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 192#64]) body688_68

def body688_70 : Prog (BitVec 64) :=
.decCall ("t1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body688_69

def body688_71 : Prog (BitVec 64) :=
.decCall ("g2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 192#64]) body688_70

def body688_72 : Prog (BitVec 64) :=
.decCall ("g1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body688_71

def body688_73 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body688_72

def body688_74 : Prog (BitVec 64) :=
.seq body688_0 body688_73

def body688_75 : Prog (BitVec 64) :=
.seq body688_1 body688_2

def body688_76 : Prog (BitVec 64) :=
.seq body688_8 body688_9

def body688_77 : Prog (BitVec 64) :=
.seq body688_10 body688_11

def body688_78 : Prog (BitVec 64) :=
.seq body688_13 body688_14

def body688_79 : Prog (BitVec 64) :=
.seq body688_78 body688_15

def body688_80 : Prog (BitVec 64) :=
.seq body688_79 body688_16

def body688_81 : Prog (BitVec 64) :=
.seq body688_80 body688_17

def body688_82 : Prog (BitVec 64) :=
.seq body688_81 body688_18

def body688_83 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.var Flapjack.VarKind.local "pinf", Flapjack.Exp.var Flapjack.VarKind.local "qinf"])
  (Flapjack.Exp.const 0#64)) body688_82 body688_6

def body688_84 : Prog (BitVec 64) :=
.seq body688_83 body688_25

def body688_85 : Prog (BitVec 64) :=
.decCall ("qinf") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "g2"]) body688_84

def body688_86 : Prog (BitVec 64) :=
.decCall ("pinf") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "g1"]) body688_85

def body688_87 : Prog (BitVec 64) :=
.seq body688_12 body688_86

def body688_88 : Prog (BitVec 64) :=
.decCall ("i2") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "t2"]) body688_87

def body688_89 : Prog (BitVec 64) :=
.seq body688_77 body688_88

def body688_90 : Prog (BitVec 64) :=
.decCall ("i1") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "t1"]) body688_89

def body688_91 : Prog (BitVec 64) :=
.seq body688_76 body688_90

def body688_92 : Prog (BitVec 64) :=
.decCall ("e2") (Flapjack.Shape.one) ("bn254_parse_g2") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "chunk", Flapjack.Exp.const 64#64],
  Flapjack.Exp.var Flapjack.VarKind.local "g2"]) body688_91

def body688_93 : Prog (BitVec 64) :=
.seq body688_7 body688_92

def body688_94 : Prog (BitVec 64) :=
.decCall ("e1") (Flapjack.Shape.one) ("bn254_parse_g1") ([Flapjack.Exp.var Flapjack.VarKind.local "chunk", Flapjack.Exp.var Flapjack.VarKind.local "g1"]) body688_93

def body688_95 : Prog (BitVec 64) :=
.dec ("chunk") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "pairs",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 192#64]]) body688_94

def body688_96 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n_pairs")) body688_95

def body688_97 : Prog (BitVec 64) :=
.seq body688_41 body688_42

def body688_98 : Prog (BitVec 64) :=
.seq body688_97 body688_43

def body688_99 : Prog (BitVec 64) :=
.seq body688_98 body688_44

def body688_100 : Prog (BitVec 64) :=
.seq body688_99 body688_45

def body688_101 : Prog (BitVec 64) :=
.seq body688_100 body688_46

def body688_102 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nontrivial") (Flapjack.Exp.const 1#64)) body688_101 body688_6

def body688_103 : Prog (BitVec 64) :=
.seq body688_102 body688_3

def body688_104 : Prog (BitVec 64) :=
.seq body688_103 body688_53

def body688_105 : Prog (BitVec 64) :=
.dec ("ok") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body688_104

def body688_106 : Prog (BitVec 64) :=
.seq body688_96 body688_105

def body688_107 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body688_106

def body688_108 : Prog (BitVec 64) :=
.dec ("nontrivial") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body688_107

def body688_109 : Prog (BitVec 64) :=
.seq body688_75 body688_108

def body688_110 : Prog (BitVec 64) :=
.decCall ("res") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body688_109

def body688_111 : Prog (BitVec 64) :=
.decCall ("aden") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body688_110

def body688_112 : Prog (BitVec 64) :=
.decCall ("anum") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body688_111

def body688_113 : Prog (BitVec 64) :=
.decCall ("fden") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body688_112

def body688_114 : Prog (BitVec 64) :=
.decCall ("fnum") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body688_113

def body688_115 : Prog (BitVec 64) :=
.decCall ("P") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body688_114

def body688_116 : Prog (BitVec 64) :=
.decCall ("Q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body688_115

def body688_117 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 192#64]) body688_116

def body688_118 : Prog (BitVec 64) :=
.decCall ("t1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body688_117

def body688_119 : Prog (BitVec 64) :=
.decCall ("g2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 192#64]) body688_118

def body688_120 : Prog (BitVec 64) :=
.decCall ("g1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body688_119

def body688_121 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body688_120

def body688_122 : Prog (BitVec 64) :=
.seq body688_0 body688_121

def originalData688 : Decl (BitVec 64) :=
.function { name := "bn254_pairing_check", inline := false, exported := false, params := [("pairs", Flapjack.Shape.one), ("n_pairs", Flapjack.Shape.one)], body := body688_74, returnShape := (Flapjack.Shape.one) }
def simplifiedData688 : Decl (BitVec 64) :=
.function { name := "bn254_pairing_check", inline := false, exported := false, params := [("pairs", Flapjack.Shape.one), ("n_pairs", Flapjack.Shape.one)], body := body688_122, returnShape := (Flapjack.Shape.one) }
def original688 := Pancake.PanLang.declToHOL originalData688
def simplified688 := Pancake.PanLang.declToHOL simplifiedData688
end InitECandidate.Proofs.FrontendStages.Declarations
