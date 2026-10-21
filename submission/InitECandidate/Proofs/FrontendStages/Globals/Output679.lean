import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data679
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate663
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody679_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.const 416#64]

def globalBody679_1 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r0")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 5544790254283102953#64, Flapjack.Exp.const 13698472384431417117#64,
      Flapjack.Exp.const 4628036095437277618#64, Flapjack.Exp.const 2762764518496934255#64])

def globalBody679_2 : Prog (BitVec 64) :=
.seq globalBody679_0 globalBody679_1

def globalBody679_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 10102850021236865696#64, Flapjack.Exp.const 15026249742141879542#64,
      Flapjack.Exp.const 2169086236411634456#64, Flapjack.Exp.const 2710440286313254821#64])

def globalBody679_4 : Prog (BitVec 64) :=
.seq globalBody679_2 globalBody679_3

def globalBody679_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.const 384#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def globalBody679_6 : Prog (BitVec 64) :=
.seq globalBody679_4 globalBody679_5

def globalBody679_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "r1", Flapjack.Exp.const 416#64]

def globalBody679_8 : Prog (BitVec 64) :=
.seq globalBody679_6 globalBody679_7

def globalBody679_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r1", Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 384#64]

def globalBody679_10 : Prog (BitVec 64) :=
.seq globalBody679_8 globalBody679_9

def globalBody679_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "s0", Flapjack.Exp.const 416#64]

def globalBody679_12 : Prog (BitVec 64) :=
.seq globalBody679_10 globalBody679_11

def globalBody679_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "s1", Flapjack.Exp.const 416#64]

def globalBody679_14 : Prog (BitVec 64) :=
.seq globalBody679_12 globalBody679_13

def globalBody679_15 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "s1")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def globalBody679_16 : Prog (BitVec 64) :=
.seq globalBody679_14 globalBody679_15

def globalBody679_17 : Prog (BitVec 64) :=
Flapjack.Prog.break

def globalBody679_18 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody679_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLess (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "d1")) globalBody679_17 globalBody679_18

def globalBody679_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 416#64]

def globalBody679_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "d0", Flapjack.Exp.var Flapjack.VarKind.local "d1"],
          Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "cf")

def globalBody679_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq_poly_submul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.var Flapjack.VarKind.local "r1",
    Flapjack.Exp.var Flapjack.VarKind.local "cf",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "d0", Flapjack.Exp.var Flapjack.VarKind.local "d1"],
    Flapjack.Exp.var Flapjack.VarKind.local "d1"]

def globalBody679_23 : Prog (BitVec 64) :=
.seq globalBody679_21 globalBody679_22

def globalBody679_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "d0"), none)) "fq_poly_deg"
  [Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.const 13#64]

def globalBody679_25 : Prog (BitVec 64) :=
.seq globalBody679_23 globalBody679_24

def globalBody679_26 : Prog (BitVec 64) :=
.decCall ("cf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.var Flapjack.VarKind.local "linv"]) globalBody679_25

def globalBody679_27 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "r0",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "d0", Flapjack.Exp.const 32#64]])) globalBody679_26

def globalBody679_28 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notLess (Flapjack.Exp.var Flapjack.VarKind.local "d0")
  (Flapjack.Exp.var Flapjack.VarKind.local "d1")) globalBody679_27

def globalBody679_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.var Flapjack.VarKind.local "s0",
    Flapjack.Exp.const 416#64]

def globalBody679_30 : Prog (BitVec 64) :=
.seq globalBody679_28 globalBody679_29

def globalBody679_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq_poly_submul"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.var Flapjack.VarKind.local "s1",
    Flapjack.Exp.var Flapjack.VarKind.local "qj", Flapjack.Exp.var Flapjack.VarKind.local "j",
    Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "j"]]

def globalBody679_32 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "qz") (Flapjack.Exp.const 0#64)) globalBody679_31 globalBody679_18

def globalBody679_33 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def globalBody679_34 : Prog (BitVec 64) :=
.seq globalBody679_32 globalBody679_33

def globalBody679_35 : Prog (BitVec 64) :=
.decCall ("qz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "qj"]) globalBody679_34

def globalBody679_36 : Prog (BitVec 64) :=
.dec ("qj") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 32#64]])) globalBody679_35

def globalBody679_37 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 13#64)) globalBody679_36

def globalBody679_38 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r0" (Flapjack.Exp.var Flapjack.VarKind.local "r1")

def globalBody679_39 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r1" (Flapjack.Exp.var Flapjack.VarKind.local "t")

def globalBody679_40 : Prog (BitVec 64) :=
.seq globalBody679_38 globalBody679_39

def globalBody679_41 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t" (Flapjack.Exp.var Flapjack.VarKind.local "s0")

def globalBody679_42 : Prog (BitVec 64) :=
.seq globalBody679_40 globalBody679_41

def globalBody679_43 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "s0" (Flapjack.Exp.var Flapjack.VarKind.local "s1")

def globalBody679_44 : Prog (BitVec 64) :=
.seq globalBody679_42 globalBody679_43

def globalBody679_45 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "s1" (Flapjack.Exp.var Flapjack.VarKind.local "tmp")

def globalBody679_46 : Prog (BitVec 64) :=
.seq globalBody679_44 globalBody679_45

def globalBody679_47 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "tmp" (Flapjack.Exp.var Flapjack.VarKind.local "t")

def globalBody679_48 : Prog (BitVec 64) :=
.seq globalBody679_46 globalBody679_47

def globalBody679_49 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "r0") globalBody679_48

def globalBody679_50 : Prog (BitVec 64) :=
.seq globalBody679_37 globalBody679_49

def globalBody679_51 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody679_50

def globalBody679_52 : Prog (BitVec 64) :=
.seq globalBody679_30 globalBody679_51

def globalBody679_53 : Prog (BitVec 64) :=
.decCall ("linv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_inv") ([Flapjack.Exp.var Flapjack.VarKind.local "lead"]) globalBody679_52

def globalBody679_54 : Prog (BitVec 64) :=
.dec ("lead") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "r1",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "d1", Flapjack.Exp.const 32#64]])) globalBody679_53

def globalBody679_55 : Prog (BitVec 64) :=
.seq globalBody679_20 globalBody679_54

def globalBody679_56 : Prog (BitVec 64) :=
.decCall ("d0") (Flapjack.Shape.one) ("fq_poly_deg") ([Flapjack.Exp.var Flapjack.VarKind.local "r0", Flapjack.Exp.const 13#64]) globalBody679_55

def globalBody679_57 : Prog (BitVec 64) :=
.seq globalBody679_19 globalBody679_56

def globalBody679_58 : Prog (BitVec 64) :=
.decCall ("d1") (Flapjack.Shape.one) ("fq_poly_deg") ([Flapjack.Exp.var Flapjack.VarKind.local "r1", Flapjack.Exp.const 13#64]) globalBody679_57

def globalBody679_59 : Prog (BitVec 64) :=
.while (Flapjack.Exp.const 1#64) globalBody679_58

def globalBody679_60 : Prog (BitVec 64) :=
.seq globalBody679_16 globalBody679_59

def globalBody679_61 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 384#64]

def globalBody679_62 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody679_63 : Prog (BitVec 64) :=
.seq globalBody679_61 globalBody679_62

def globalBody679_64 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody679_65 : Prog (BitVec 64) :=
.seq globalBody679_63 globalBody679_64

def globalBody679_66 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "dz") (Flapjack.Exp.const 0#64)) globalBody679_65 globalBody679_18

def globalBody679_67 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "d",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "ri")

def globalBody679_68 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody679_69 : Prog (BitVec 64) :=
.seq globalBody679_67 globalBody679_68

def globalBody679_70 : Prog (BitVec 64) :=
.decCall ("ri") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.var Flapjack.VarKind.local "cinv"]) globalBody679_69

def globalBody679_71 : Prog (BitVec 64) :=
.dec ("si") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "s1",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]])) globalBody679_70

def globalBody679_72 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 12#64)) globalBody679_71

def globalBody679_73 : Prog (BitVec 64) :=
.seq globalBody679_72 globalBody679_62

def globalBody679_74 : Prog (BitVec 64) :=
.seq globalBody679_73 globalBody679_64

def globalBody679_75 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody679_74

def globalBody679_76 : Prog (BitVec 64) :=
.decCall ("cinv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_inv") ([Flapjack.Exp.var Flapjack.VarKind.local "c"]) globalBody679_75

def globalBody679_77 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "r1")) globalBody679_76

def globalBody679_78 : Prog (BitVec 64) :=
.seq globalBody679_66 globalBody679_77

def globalBody679_79 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("fq_poly_deg") ([Flapjack.Exp.var Flapjack.VarKind.local "r1", Flapjack.Exp.const 13#64]) globalBody679_78

def globalBody679_80 : Prog (BitVec 64) :=
.seq globalBody679_60 globalBody679_79

def globalBody679_81 : Prog (BitVec 64) :=
.decCall ("tmp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) globalBody679_80

def globalBody679_82 : Prog (BitVec 64) :=
.decCall ("q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) globalBody679_81

def globalBody679_83 : Prog (BitVec 64) :=
.decCall ("s1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) globalBody679_82

def globalBody679_84 : Prog (BitVec 64) :=
.decCall ("s0") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) globalBody679_83

def globalBody679_85 : Prog (BitVec 64) :=
.decCall ("r1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) globalBody679_84

def globalBody679_86 : Prog (BitVec 64) :=
.decCall ("r0") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 416#64]) globalBody679_85

def globalBody679_87 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody679_86

def globalData679 : Decl (BitVec 64) :=
.function { name := "fq12_inv", inline := false, exported := false, params := [("d", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := globalBody679_87, returnShape := (Flapjack.Shape.one) }
def globalOutput679 := Pancake.PanLang.declToHOL globalData679
end InitECandidate.Proofs.FrontendStages.Declarations
