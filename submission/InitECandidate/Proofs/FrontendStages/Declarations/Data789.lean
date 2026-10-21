import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify773
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body789_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "v7", Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body789_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "v7", Flapjack.Exp.var Flapjack.VarKind.local "v7",
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body789_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body789_3 : Prog (BitVec 64) :=
.seq body789_1 body789_2

def body789_4 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 6#64)) body789_3

def body789_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp1", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "v7"]

def body789_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp2", Flapjack.Exp.var Flapjack.VarKind.local "v7",
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body789_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp2", Flapjack.Exp.var Flapjack.VarKind.local "temp1",
    Flapjack.Exp.var Flapjack.VarKind.local "temp2"]

def body789_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_pow"
  [Flapjack.Exp.var Flapjack.VarKind.local "gamma", Flapjack.Exp.var Flapjack.VarKind.local "temp2",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1528#64],
    Flapjack.Exp.const 12#64]

def body789_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "gamma", Flapjack.Exp.var Flapjack.VarKind.local "gamma",
    Flapjack.Exp.var Flapjack.VarKind.local "temp1"]

def body789_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "gamma"]

def body789_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def body789_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "cand",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 5216#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 96#64]],
    Flapjack.Exp.var Flapjack.VarKind.local "gamma"]

def body789_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "chk", Flapjack.Exp.var Flapjack.VarKind.local "cand"]

def body789_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "chk", Flapjack.Exp.var Flapjack.VarKind.local "chk",
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body789_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "chk", Flapjack.Exp.var Flapjack.VarKind.local "chk",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body789_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "valid" (Flapjack.Exp.const 1#64)

def body789_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "cand"]

def body789_18 : Prog (BitVec 64) :=
.seq body789_16 body789_17

def body789_19 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body789_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "valid") (Flapjack.Exp.const 0#64))]) body789_18 body789_19

def body789_21 : Prog (BitVec 64) :=
.seq body789_20 body789_2

def body789_22 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "chk"]) body789_21

def body789_23 : Prog (BitVec 64) :=
.seq body789_15 body789_22

def body789_24 : Prog (BitVec 64) :=
.seq body789_14 body789_23

def body789_25 : Prog (BitVec 64) :=
.seq body789_13 body789_24

def body789_26 : Prog (BitVec 64) :=
.seq body789_12 body789_25

def body789_27 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 4#64)) body789_26

def body789_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body789_29 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "valid")

def body789_30 : Prog (BitVec 64) :=
.seq body789_28 body789_29

def body789_31 : Prog (BitVec 64) :=
.seq body789_27 body789_30

def body789_32 : Prog (BitVec 64) :=
.seq body789_11 body789_31

def body789_33 : Prog (BitVec 64) :=
.seq body789_10 body789_32

def body789_34 : Prog (BitVec 64) :=
.dec ("valid") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body789_33

def body789_35 : Prog (BitVec 64) :=
.seq body789_9 body789_34

def body789_36 : Prog (BitVec 64) :=
.seq body789_8 body789_35

def body789_37 : Prog (BitVec 64) :=
.seq body789_7 body789_36

def body789_38 : Prog (BitVec 64) :=
.seq body789_6 body789_37

def body789_39 : Prog (BitVec 64) :=
.seq body789_5 body789_38

def body789_40 : Prog (BitVec 64) :=
.seq body789_4 body789_39

def body789_41 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body789_40

def body789_42 : Prog (BitVec 64) :=
.seq body789_0 body789_41

def body789_43 : Prog (BitVec 64) :=
.dec ("chk") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) body789_42

def body789_44 : Prog (BitVec 64) :=
.dec ("cand") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) body789_43

def body789_45 : Prog (BitVec 64) :=
.dec ("gamma") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body789_44

def body789_46 : Prog (BitVec 64) :=
.dec ("temp2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) body789_45

def body789_47 : Prog (BitVec 64) :=
.dec ("temp1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) body789_46

def body789_48 : Prog (BitVec 64) :=
.dec ("v7") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body789_47

def body789_49 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 6#64]]) body789_48

def body789_50 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body789_49

def body789_51 : Prog (BitVec 64) :=
.seq body789_4 body789_5

def body789_52 : Prog (BitVec 64) :=
.seq body789_51 body789_6

def body789_53 : Prog (BitVec 64) :=
.seq body789_52 body789_7

def body789_54 : Prog (BitVec 64) :=
.seq body789_53 body789_8

def body789_55 : Prog (BitVec 64) :=
.seq body789_54 body789_9

def body789_56 : Prog (BitVec 64) :=
.seq body789_10 body789_11

def body789_57 : Prog (BitVec 64) :=
.seq body789_12 body789_13

def body789_58 : Prog (BitVec 64) :=
.seq body789_57 body789_14

def body789_59 : Prog (BitVec 64) :=
.seq body789_58 body789_15

def body789_60 : Prog (BitVec 64) :=
.seq body789_59 body789_22

def body789_61 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 4#64)) body789_60

def body789_62 : Prog (BitVec 64) :=
.seq body789_56 body789_61

def body789_63 : Prog (BitVec 64) :=
.seq body789_62 body789_28

def body789_64 : Prog (BitVec 64) :=
.seq body789_63 body789_29

def body789_65 : Prog (BitVec 64) :=
.dec ("valid") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body789_64

def body789_66 : Prog (BitVec 64) :=
.seq body789_55 body789_65

def body789_67 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body789_66

def body789_68 : Prog (BitVec 64) :=
.seq body789_0 body789_67

def body789_69 : Prog (BitVec 64) :=
.dec ("chk") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) body789_68

def body789_70 : Prog (BitVec 64) :=
.dec ("cand") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) body789_69

def body789_71 : Prog (BitVec 64) :=
.dec ("gamma") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body789_70

def body789_72 : Prog (BitVec 64) :=
.dec ("temp2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) body789_71

def body789_73 : Prog (BitVec 64) :=
.dec ("temp1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) body789_72

def body789_74 : Prog (BitVec 64) :=
.dec ("v7") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body789_73

def body789_75 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 6#64]]) body789_74

def body789_76 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body789_75

def originalData789 : Decl (BitVec 64) :=
.function { name := "swu_sqrt_division_fp2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("u", Flapjack.Shape.one), ("v", Flapjack.Shape.one)], body := body789_50, returnShape := (Flapjack.Shape.one) }
def simplifiedData789 : Decl (BitVec 64) :=
.function { name := "swu_sqrt_division_fp2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("u", Flapjack.Shape.one), ("v", Flapjack.Shape.one)], body := body789_76, returnShape := (Flapjack.Shape.one) }
def original789 := Pancake.PanLang.declToHOL originalData789
def simplified789 := Pancake.PanLang.declToHOL simplifiedData789
end InitECandidate.Proofs.FrontendStages.Declarations
