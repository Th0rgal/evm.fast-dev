import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify411
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body427_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body427_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body427_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 2#64)) body427_0 body427_1

def body427_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "mid" (Flapjack.Exp.var Flapjack.VarKind.local "n")

def body427_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "n")
  (Flapjack.Exp.var Flapjack.VarKind.local "mid")) body427_3 body427_1

def body427_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "right" (Flapjack.Exp.var Flapjack.VarKind.local "n")

def body427_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "n")
  (Flapjack.Exp.var Flapjack.VarKind.local "right")) body427_5 body427_1

def body427_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dst",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def body427_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body427_9 : Prog (BitVec 64) :=
.seq body427_7 body427_8

def body427_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dst",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def body427_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def body427_12 : Prog (BitVec 64) :=
.seq body427_10 body427_11

def body427_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "gt") (Flapjack.Exp.const 0#64)) body427_9 body427_12

def body427_14 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64])

def body427_15 : Prog (BitVec 64) :=
.seq body427_13 body427_14

def body427_16 : Prog (BitVec 64) :=
.decCall ("gt") (Flapjack.Shape.one) ("bal_sort_gt") ([Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "b",
  Flapjack.Exp.var Flapjack.VarKind.local "kind"]) body427_15

def body427_17 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "src",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body427_16

def body427_18 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "src",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body427_17

def body427_19 : Prog (BitVec 64) :=
.while (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
        (Flapjack.Exp.var Flapjack.VarKind.local "mid")),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
        (Flapjack.Exp.var Flapjack.VarKind.local "right"))]) body427_18

def body427_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dst",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "src",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def body427_21 : Prog (BitVec 64) :=
.seq body427_8 body427_14

def body427_22 : Prog (BitVec 64) :=
.seq body427_20 body427_21

def body427_23 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "mid")) body427_22

def body427_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dst",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "src",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def body427_25 : Prog (BitVec 64) :=
.seq body427_11 body427_14

def body427_26 : Prog (BitVec 64) :=
.seq body427_24 body427_25

def body427_27 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "right")) body427_26

def body427_28 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "left" (Flapjack.Exp.var Flapjack.VarKind.local "right")

def body427_29 : Prog (BitVec 64) :=
.seq body427_27 body427_28

def body427_30 : Prog (BitVec 64) :=
.seq body427_23 body427_29

def body427_31 : Prog (BitVec 64) :=
.seq body427_19 body427_30

def body427_32 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "left") body427_31

def body427_33 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "mid") body427_32

def body427_34 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "left") body427_33

def body427_35 : Prog (BitVec 64) :=
.seq body427_6 body427_34

def body427_36 : Prog (BitVec 64) :=
.dec ("right") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "mid", Flapjack.Exp.var Flapjack.VarKind.local "width"]) body427_35

def body427_37 : Prog (BitVec 64) :=
.seq body427_4 body427_36

def body427_38 : Prog (BitVec 64) :=
.dec ("mid") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "left", Flapjack.Exp.var Flapjack.VarKind.local "width"]) body427_37

def body427_39 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "left")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body427_38

def body427_40 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "src" (Flapjack.Exp.var Flapjack.VarKind.local "dst")

def body427_41 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "dst" (Flapjack.Exp.var Flapjack.VarKind.local "swap")

def body427_42 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "width"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "width", Flapjack.Exp.const 2#64])

def body427_43 : Prog (BitVec 64) :=
.seq body427_41 body427_42

def body427_44 : Prog (BitVec 64) :=
.seq body427_40 body427_43

def body427_45 : Prog (BitVec 64) :=
.dec ("swap") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "src") body427_44

def body427_46 : Prog (BitVec 64) :=
.seq body427_39 body427_45

def body427_47 : Prog (BitVec 64) :=
.dec ("left") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body427_46

def body427_48 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "width")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body427_47

def body427_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "src",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]

def body427_50 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "src")
  (Flapjack.Exp.var Flapjack.VarKind.local "p")) body427_49 body427_1

def body427_51 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body427_52 : Prog (BitVec 64) :=
.seq body427_51 body427_0

def body427_53 : Prog (BitVec 64) :=
.seq body427_50 body427_52

def body427_54 : Prog (BitVec 64) :=
.seq body427_48 body427_53

def body427_55 : Prog (BitVec 64) :=
.dec ("width") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body427_54

def body427_56 : Prog (BitVec 64) :=
.dec ("dst") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "aux") body427_55

def body427_57 : Prog (BitVec 64) :=
.dec ("src") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p") body427_56

def body427_58 : Prog (BitVec 64) :=
.decCall ("aux") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body427_57

def body427_59 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body427_58

def body427_60 : Prog (BitVec 64) :=
.seq body427_2 body427_59

def body427_61 : Prog (BitVec 64) :=
.seq body427_20 body427_8

def body427_62 : Prog (BitVec 64) :=
.seq body427_61 body427_14

def body427_63 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "mid")) body427_62

def body427_64 : Prog (BitVec 64) :=
.seq body427_19 body427_63

def body427_65 : Prog (BitVec 64) :=
.seq body427_24 body427_11

def body427_66 : Prog (BitVec 64) :=
.seq body427_65 body427_14

def body427_67 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "right")) body427_66

def body427_68 : Prog (BitVec 64) :=
.seq body427_64 body427_67

def body427_69 : Prog (BitVec 64) :=
.seq body427_68 body427_28

def body427_70 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "left") body427_69

def body427_71 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "mid") body427_70

def body427_72 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "left") body427_71

def body427_73 : Prog (BitVec 64) :=
.seq body427_6 body427_72

def body427_74 : Prog (BitVec 64) :=
.dec ("right") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "mid", Flapjack.Exp.var Flapjack.VarKind.local "width"]) body427_73

def body427_75 : Prog (BitVec 64) :=
.seq body427_4 body427_74

def body427_76 : Prog (BitVec 64) :=
.dec ("mid") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "left", Flapjack.Exp.var Flapjack.VarKind.local "width"]) body427_75

def body427_77 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "left")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body427_76

def body427_78 : Prog (BitVec 64) :=
.seq body427_40 body427_41

def body427_79 : Prog (BitVec 64) :=
.seq body427_78 body427_42

def body427_80 : Prog (BitVec 64) :=
.dec ("swap") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "src") body427_79

def body427_81 : Prog (BitVec 64) :=
.seq body427_77 body427_80

def body427_82 : Prog (BitVec 64) :=
.dec ("left") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body427_81

def body427_83 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "width")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body427_82

def body427_84 : Prog (BitVec 64) :=
.seq body427_83 body427_50

def body427_85 : Prog (BitVec 64) :=
.seq body427_84 body427_51

def body427_86 : Prog (BitVec 64) :=
.seq body427_85 body427_0

def body427_87 : Prog (BitVec 64) :=
.dec ("width") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body427_86

def body427_88 : Prog (BitVec 64) :=
.dec ("dst") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "aux") body427_87

def body427_89 : Prog (BitVec 64) :=
.dec ("src") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p") body427_88

def body427_90 : Prog (BitVec 64) :=
.decCall ("aux") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body427_89

def body427_91 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body427_90

def body427_92 : Prog (BitVec 64) :=
.seq body427_2 body427_91

def originalData427 : Decl (BitVec 64) :=
.function { name := "sort_elems", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("esz", Flapjack.Shape.one), ("kind", Flapjack.Shape.one),
  ("tmp", Flapjack.Shape.one)], body := body427_60, returnShape := (Flapjack.Shape.one) }
def simplifiedData427 : Decl (BitVec 64) :=
.function { name := "sort_elems", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("esz", Flapjack.Shape.one), ("kind", Flapjack.Shape.one),
  ("tmp", Flapjack.Shape.one)], body := body427_92, returnShape := (Flapjack.Shape.one) }
def original427 := Pancake.PanLang.declToHOL originalData427
def simplified427 := Pancake.PanLang.declToHOL simplifiedData427
end InitECandidate.Proofs.FrontendStages.Declarations
