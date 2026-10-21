import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify265
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body281_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 0#64)

def body281_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "node")

def body281_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 0#64)

def body281_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "_node_rlp_begin"
  [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.var Flapjack.VarKind.local "node"]

def body281_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 1#64)

def body281_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "child"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 48#64]))

def body281_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "found"), none)) "_node_needs_rlp"
  [Flapjack.Exp.var Flapjack.VarKind.local "child"]

def body281_7 : Prog (BitVec 64) :=
.seq body281_5 body281_6

def body281_8 : Prog (BitVec 64) :=
.seq body281_4 body281_7

def body281_9 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body281_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.const 0#64)) body281_8 body281_9

def body281_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "child"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 32#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]]))

def body281_12 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body281_13 : Prog (BitVec 64) :=
.seq body281_12 body281_6

def body281_14 : Prog (BitVec 64) :=
.seq body281_11 body281_13

def body281_15 : Prog (BitVec 64) :=
.while (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 16#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "found") (Flapjack.Exp.const 0#64))]) body281_14

def body281_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "i")

def body281_17 : Prog (BitVec 64) :=
.seq body281_15 body281_16

def body281_18 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64])) body281_17

def body281_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 3#64)) body281_18 body281_9

def body281_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 2#64)) body281_10 body281_19

def body281_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cf", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "top")

def body281_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cf", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "child")

def body281_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cf", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 0#64)

def body281_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "_node_rlp_begin"
  [Flapjack.Exp.var Flapjack.VarKind.local "cf", Flapjack.Exp.var Flapjack.VarKind.local "child"]

def body281_25 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "top" (Flapjack.Exp.var Flapjack.VarKind.local "cf")

def body281_26 : Prog (BitVec 64) :=
.seq body281_24 body281_25

def body281_27 : Prog (BitVec 64) :=
.seq body281_23 body281_26

def body281_28 : Prog (BitVec 64) :=
.seq body281_22 body281_27

def body281_29 : Prog (BitVec 64) :=
.seq body281_21 body281_28

def body281_30 : Prog (BitVec 64) :=
.decCall ("cf") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 48#64]) body281_29

def body281_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "_node_rlp_finish"
  [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.var Flapjack.VarKind.local "nd"]

def body281_32 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "top"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 0#64]))

def body281_33 : Prog (BitVec 64) :=
.seq body281_31 body281_32

def body281_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "found") (Flapjack.Exp.const 0#64)) body281_30 body281_33

def body281_35 : Prog (BitVec 64) :=
.seq body281_20 body281_34

def body281_36 : Prog (BitVec 64) :=
.dec ("found") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body281_35

def body281_37 : Prog (BitVec 64) :=
.dec ("child") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body281_36

def body281_38 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 0#64])) body281_37

def body281_39 : Prog (BitVec 64) :=
.dec ("nd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 8#64])) body281_38

def body281_40 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 0#64)) body281_39

def body281_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "scratch_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body281_42 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body281_43 : Prog (BitVec 64) :=
.seq body281_41 body281_42

def body281_44 : Prog (BitVec 64) :=
.seq body281_40 body281_43

def body281_45 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "fr") body281_44

def body281_46 : Prog (BitVec 64) :=
.seq body281_3 body281_45

def body281_47 : Prog (BitVec 64) :=
.seq body281_2 body281_46

def body281_48 : Prog (BitVec 64) :=
.seq body281_1 body281_47

def body281_49 : Prog (BitVec 64) :=
.seq body281_0 body281_48

def body281_50 : Prog (BitVec 64) :=
.decCall ("fr") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 48#64]) body281_49

def body281_51 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("scratch_mark") ([]) body281_50

def body281_52 : Prog (BitVec 64) :=
.seq body281_0 body281_1

def body281_53 : Prog (BitVec 64) :=
.seq body281_52 body281_2

def body281_54 : Prog (BitVec 64) :=
.seq body281_53 body281_3

def body281_55 : Prog (BitVec 64) :=
.seq body281_4 body281_5

def body281_56 : Prog (BitVec 64) :=
.seq body281_55 body281_6

def body281_57 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.const 0#64)) body281_56 body281_9

def body281_58 : Prog (BitVec 64) :=
.seq body281_11 body281_12

def body281_59 : Prog (BitVec 64) :=
.seq body281_58 body281_6

def body281_60 : Prog (BitVec 64) :=
.while (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 16#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "found") (Flapjack.Exp.const 0#64))]) body281_59

def body281_61 : Prog (BitVec 64) :=
.seq body281_60 body281_16

def body281_62 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64])) body281_61

def body281_63 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 3#64)) body281_62 body281_9

def body281_64 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 2#64)) body281_57 body281_63

def body281_65 : Prog (BitVec 64) :=
.seq body281_21 body281_22

def body281_66 : Prog (BitVec 64) :=
.seq body281_65 body281_23

def body281_67 : Prog (BitVec 64) :=
.seq body281_66 body281_24

def body281_68 : Prog (BitVec 64) :=
.seq body281_67 body281_25

def body281_69 : Prog (BitVec 64) :=
.decCall ("cf") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 48#64]) body281_68

def body281_70 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "found") (Flapjack.Exp.const 0#64)) body281_69 body281_33

def body281_71 : Prog (BitVec 64) :=
.seq body281_64 body281_70

def body281_72 : Prog (BitVec 64) :=
.dec ("found") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body281_71

def body281_73 : Prog (BitVec 64) :=
.dec ("child") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body281_72

def body281_74 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 0#64])) body281_73

def body281_75 : Prog (BitVec 64) :=
.dec ("nd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 8#64])) body281_74

def body281_76 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 0#64)) body281_75

def body281_77 : Prog (BitVec 64) :=
.seq body281_76 body281_41

def body281_78 : Prog (BitVec 64) :=
.seq body281_77 body281_42

def body281_79 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "fr") body281_78

def body281_80 : Prog (BitVec 64) :=
.seq body281_54 body281_79

def body281_81 : Prog (BitVec 64) :=
.decCall ("fr") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 48#64]) body281_80

def body281_82 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("scratch_mark") ([]) body281_81

def originalData281 : Decl (BitVec 64) :=
.function { name := "_node_rlp_fill", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := body281_51, returnShape := (Flapjack.Shape.one) }
def simplifiedData281 : Decl (BitVec 64) :=
.function { name := "_node_rlp_fill", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := body281_82, returnShape := (Flapjack.Shape.one) }
def original281 := Pancake.PanLang.declToHOL originalData281
def simplified281 := Pancake.PanLang.declToHOL simplifiedData281
end InitECandidate.Proofs.FrontendStages.Declarations
