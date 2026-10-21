import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify663
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body679_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.const 416#64]

def body679_1 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r0")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 5544790254283102953#64, Flapjack.Exp.const 13698472384431417117#64,
      Flapjack.Exp.const 4628036095437277618#64, Flapjack.Exp.const 2762764518496934255#64])

def body679_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 10102850021236865696#64, Flapjack.Exp.const 15026249742141879542#64,
      Flapjack.Exp.const 2169086236411634456#64, Flapjack.Exp.const 2710440286313254821#64])

def body679_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.const 384#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def body679_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "r1", Flapjack.Exp.const 416#64]

def body679_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r1", Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 384#64]

def body679_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "s0", Flapjack.Exp.const 416#64]

def body679_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "s1", Flapjack.Exp.const 416#64]

def body679_8 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "s1")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def body679_9 : Prog (BitVec 64) :=
Flapjack.Prog.break

def body679_10 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body679_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLess (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "d1")) body679_9 body679_10

def body679_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 416#64]

def body679_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "d0", Flapjack.Exp.var Flapjack.VarKind.local "d1"],
          Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "cf")

def body679_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq_poly_submul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.var Flapjack.VarKind.local "r1",
    Flapjack.Exp.var Flapjack.VarKind.local "cf",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "d0", Flapjack.Exp.var Flapjack.VarKind.local "d1"],
    Flapjack.Exp.var Flapjack.VarKind.local "d1"]

def body679_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "d0"), none)) "fq_poly_deg"
  [Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.const 13#64]

def body679_16 : Prog (BitVec 64) :=
.seq body679_14 body679_15

def body679_17 : Prog (BitVec 64) :=
.seq body679_13 body679_16

def body679_18 : Prog (BitVec 64) :=
.decCall ("cf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.var Flapjack.VarKind.local "linv"]) body679_17

def body679_19 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "r0",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "d0", Flapjack.Exp.const 32#64]])) body679_18

def body679_20 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notLess (Flapjack.Exp.var Flapjack.VarKind.local "d0")
  (Flapjack.Exp.var Flapjack.VarKind.local "d1")) body679_19

def body679_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.var Flapjack.VarKind.local "s0",
    Flapjack.Exp.const 416#64]

def body679_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq_poly_submul"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.var Flapjack.VarKind.local "s1",
    Flapjack.Exp.var Flapjack.VarKind.local "qj", Flapjack.Exp.var Flapjack.VarKind.local "j",
    Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "j"]]

def body679_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "qz") (Flapjack.Exp.const 0#64)) body679_22 body679_10

def body679_24 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def body679_25 : Prog (BitVec 64) :=
.seq body679_23 body679_24

def body679_26 : Prog (BitVec 64) :=
.decCall ("qz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "qj"]) body679_25

def body679_27 : Prog (BitVec 64) :=
.dec ("qj") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 32#64]])) body679_26

def body679_28 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 13#64)) body679_27

def body679_29 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r0" (Flapjack.Exp.var Flapjack.VarKind.local "r1")

def body679_30 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r1" (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body679_31 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t" (Flapjack.Exp.var Flapjack.VarKind.local "s0")

def body679_32 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "s0" (Flapjack.Exp.var Flapjack.VarKind.local "s1")

def body679_33 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "s1" (Flapjack.Exp.var Flapjack.VarKind.local "tmp")

def body679_34 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "tmp" (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body679_35 : Prog (BitVec 64) :=
.seq body679_33 body679_34

def body679_36 : Prog (BitVec 64) :=
.seq body679_32 body679_35

def body679_37 : Prog (BitVec 64) :=
.seq body679_31 body679_36

def body679_38 : Prog (BitVec 64) :=
.seq body679_30 body679_37

def body679_39 : Prog (BitVec 64) :=
.seq body679_29 body679_38

def body679_40 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "r0") body679_39

def body679_41 : Prog (BitVec 64) :=
.seq body679_28 body679_40

def body679_42 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body679_41

def body679_43 : Prog (BitVec 64) :=
.seq body679_21 body679_42

def body679_44 : Prog (BitVec 64) :=
.seq body679_20 body679_43

def body679_45 : Prog (BitVec 64) :=
.decCall ("linv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_inv") ([Flapjack.Exp.var Flapjack.VarKind.local "lead"]) body679_44

def body679_46 : Prog (BitVec 64) :=
.dec ("lead") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "r1",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "d1", Flapjack.Exp.const 32#64]])) body679_45

def body679_47 : Prog (BitVec 64) :=
.seq body679_12 body679_46

def body679_48 : Prog (BitVec 64) :=
.decCall ("d0") (Flapjack.Shape.one) ("fq_poly_deg") ([Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.const 13#64]) body679_47

def body679_49 : Prog (BitVec 64) :=
.seq body679_11 body679_48

def body679_50 : Prog (BitVec 64) :=
.decCall ("d1") (Flapjack.Shape.one) ("fq_poly_deg") ([Flapjack.Exp.var Flapjack.VarKind.local "r1", Flapjack.Exp.const 13#64]) body679_49

def body679_51 : Prog (BitVec 64) :=
.while (Flapjack.Exp.const 1#64) body679_50

def body679_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 384#64]

def body679_53 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body679_54 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body679_55 : Prog (BitVec 64) :=
.seq body679_53 body679_54

def body679_56 : Prog (BitVec 64) :=
.seq body679_52 body679_55

def body679_57 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "dz") (Flapjack.Exp.const 0#64)) body679_56 body679_10

def body679_58 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "d",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "ri")

def body679_59 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body679_60 : Prog (BitVec 64) :=
.seq body679_58 body679_59

def body679_61 : Prog (BitVec 64) :=
.decCall ("ri") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.var Flapjack.VarKind.local "cinv"]) body679_60

def body679_62 : Prog (BitVec 64) :=
.dec ("si") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "s1",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]])) body679_61

def body679_63 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 12#64)) body679_62

def body679_64 : Prog (BitVec 64) :=
.seq body679_63 body679_55

def body679_65 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body679_64

def body679_66 : Prog (BitVec 64) :=
.decCall ("cinv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_inv") ([Flapjack.Exp.var Flapjack.VarKind.local "c"]) body679_65

def body679_67 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "r1")) body679_66

def body679_68 : Prog (BitVec 64) :=
.seq body679_57 body679_67

def body679_69 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("fq_poly_deg") ([Flapjack.Exp.var Flapjack.VarKind.local "r1", Flapjack.Exp.const 13#64]) body679_68

def body679_70 : Prog (BitVec 64) :=
.seq body679_51 body679_69

def body679_71 : Prog (BitVec 64) :=
.seq body679_8 body679_70

def body679_72 : Prog (BitVec 64) :=
.seq body679_7 body679_71

def body679_73 : Prog (BitVec 64) :=
.seq body679_6 body679_72

def body679_74 : Prog (BitVec 64) :=
.seq body679_5 body679_73

def body679_75 : Prog (BitVec 64) :=
.seq body679_4 body679_74

def body679_76 : Prog (BitVec 64) :=
.seq body679_3 body679_75

def body679_77 : Prog (BitVec 64) :=
.seq body679_2 body679_76

def body679_78 : Prog (BitVec 64) :=
.seq body679_1 body679_77

def body679_79 : Prog (BitVec 64) :=
.seq body679_0 body679_78

def body679_80 : Prog (BitVec 64) :=
.decCall ("tmp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_79

def body679_81 : Prog (BitVec 64) :=
.decCall ("q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_80

def body679_82 : Prog (BitVec 64) :=
.decCall ("s1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_81

def body679_83 : Prog (BitVec 64) :=
.decCall ("s0") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_82

def body679_84 : Prog (BitVec 64) :=
.decCall ("r1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_83

def body679_85 : Prog (BitVec 64) :=
.decCall ("r0") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_84

def body679_86 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body679_85

def body679_87 : Prog (BitVec 64) :=
.seq body679_0 body679_1

def body679_88 : Prog (BitVec 64) :=
.seq body679_87 body679_2

def body679_89 : Prog (BitVec 64) :=
.seq body679_88 body679_3

def body679_90 : Prog (BitVec 64) :=
.seq body679_89 body679_4

def body679_91 : Prog (BitVec 64) :=
.seq body679_90 body679_5

def body679_92 : Prog (BitVec 64) :=
.seq body679_91 body679_6

def body679_93 : Prog (BitVec 64) :=
.seq body679_92 body679_7

def body679_94 : Prog (BitVec 64) :=
.seq body679_93 body679_8

def body679_95 : Prog (BitVec 64) :=
.seq body679_13 body679_14

def body679_96 : Prog (BitVec 64) :=
.seq body679_95 body679_15

def body679_97 : Prog (BitVec 64) :=
.decCall ("cf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.var Flapjack.VarKind.local "linv"]) body679_96

def body679_98 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "r0",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "d0", Flapjack.Exp.const 32#64]])) body679_97

def body679_99 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notLess (Flapjack.Exp.var Flapjack.VarKind.local "d0")
  (Flapjack.Exp.var Flapjack.VarKind.local "d1")) body679_98

def body679_100 : Prog (BitVec 64) :=
.seq body679_99 body679_21

def body679_101 : Prog (BitVec 64) :=
.seq body679_29 body679_30

def body679_102 : Prog (BitVec 64) :=
.seq body679_101 body679_31

def body679_103 : Prog (BitVec 64) :=
.seq body679_102 body679_32

def body679_104 : Prog (BitVec 64) :=
.seq body679_103 body679_33

def body679_105 : Prog (BitVec 64) :=
.seq body679_104 body679_34

def body679_106 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "r0") body679_105

def body679_107 : Prog (BitVec 64) :=
.seq body679_28 body679_106

def body679_108 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body679_107

def body679_109 : Prog (BitVec 64) :=
.seq body679_100 body679_108

def body679_110 : Prog (BitVec 64) :=
.decCall ("linv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_inv") ([Flapjack.Exp.var Flapjack.VarKind.local "lead"]) body679_109

def body679_111 : Prog (BitVec 64) :=
.dec ("lead") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "r1",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "d1", Flapjack.Exp.const 32#64]])) body679_110

def body679_112 : Prog (BitVec 64) :=
.seq body679_12 body679_111

def body679_113 : Prog (BitVec 64) :=
.decCall ("d0") (Flapjack.Shape.one) ("fq_poly_deg") ([Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.const 13#64]) body679_112

def body679_114 : Prog (BitVec 64) :=
.seq body679_11 body679_113

def body679_115 : Prog (BitVec 64) :=
.decCall ("d1") (Flapjack.Shape.one) ("fq_poly_deg") ([Flapjack.Exp.var Flapjack.VarKind.local "r1", Flapjack.Exp.const 13#64]) body679_114

def body679_116 : Prog (BitVec 64) :=
.while (Flapjack.Exp.const 1#64) body679_115

def body679_117 : Prog (BitVec 64) :=
.seq body679_94 body679_116

def body679_118 : Prog (BitVec 64) :=
.seq body679_52 body679_53

def body679_119 : Prog (BitVec 64) :=
.seq body679_118 body679_54

def body679_120 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "dz") (Flapjack.Exp.const 0#64)) body679_119 body679_10

def body679_121 : Prog (BitVec 64) :=
.seq body679_63 body679_53

def body679_122 : Prog (BitVec 64) :=
.seq body679_121 body679_54

def body679_123 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body679_122

def body679_124 : Prog (BitVec 64) :=
.decCall ("cinv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_inv") ([Flapjack.Exp.var Flapjack.VarKind.local "c"]) body679_123

def body679_125 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "r1")) body679_124

def body679_126 : Prog (BitVec 64) :=
.seq body679_120 body679_125

def body679_127 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("fq_poly_deg") ([Flapjack.Exp.var Flapjack.VarKind.local "r1", Flapjack.Exp.const 13#64]) body679_126

def body679_128 : Prog (BitVec 64) :=
.seq body679_117 body679_127

def body679_129 : Prog (BitVec 64) :=
.decCall ("tmp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_128

def body679_130 : Prog (BitVec 64) :=
.decCall ("q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_129

def body679_131 : Prog (BitVec 64) :=
.decCall ("s1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_130

def body679_132 : Prog (BitVec 64) :=
.decCall ("s0") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_131

def body679_133 : Prog (BitVec 64) :=
.decCall ("r1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_132

def body679_134 : Prog (BitVec 64) :=
.decCall ("r0") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) body679_133

def body679_135 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body679_134

def originalData679 : Decl (BitVec 64) :=
.function { name := "fq12_inv", inline := false, exported := false, params := [("d", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body679_86, returnShape := (Flapjack.Shape.one) }
def simplifiedData679 : Decl (BitVec 64) :=
.function { name := "fq12_inv", inline := false, exported := false, params := [("d", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body679_135, returnShape := (Flapjack.Shape.one) }
def original679 := Pancake.PanLang.declToHOL originalData679
def simplified679 := Pancake.PanLang.declToHOL simplifiedData679
end InitECandidate.Proofs.FrontendStages.Declarations
