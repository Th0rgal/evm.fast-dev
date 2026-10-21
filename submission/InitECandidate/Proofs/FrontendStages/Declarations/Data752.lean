import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify736
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body752_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "base", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body752_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body752_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body752_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc",
    Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body752_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body752_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "started") (Flapjack.Exp.const 1#64)) body752_3 body752_4

def body752_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc",
    Flapjack.Exp.var Flapjack.VarKind.local "base"]

def body752_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "started" (Flapjack.Exp.const 1#64)

def body752_8 : Prog (BitVec 64) :=
.seq body752_6 body752_7

def body752_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "x")
        (Flapjack.Exp.var Flapjack.VarKind.local "i"),
      Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 1#64)) body752_8 body752_4

def body752_10 : Prog (BitVec 64) :=
.seq body752_5 body752_9

def body752_11 : Prog (BitVec 64) :=
.seq body752_2 body752_10

def body752_12 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body752_11

def body752_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body752_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body752_15 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body752_16 : Prog (BitVec 64) :=
.seq body752_14 body752_15

def body752_17 : Prog (BitVec 64) :=
.seq body752_13 body752_16

def body752_18 : Prog (BitVec 64) :=
.seq body752_12 body752_17

def body752_19 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 64#64) body752_18

def body752_20 : Prog (BitVec 64) :=
.dec ("started") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body752_19

def body752_21 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1376#64])) body752_20

def body752_22 : Prog (BitVec 64) :=
.seq body752_1 body752_21

def body752_23 : Prog (BitVec 64) :=
.seq body752_0 body752_22

def body752_24 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) body752_23

def body752_25 : Prog (BitVec 64) :=
.decCall ("base") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) body752_24

def body752_26 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body752_25

def body752_27 : Prog (BitVec 64) :=
.seq body752_0 body752_1

def body752_28 : Prog (BitVec 64) :=
.seq body752_2 body752_5

def body752_29 : Prog (BitVec 64) :=
.seq body752_28 body752_9

def body752_30 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body752_29

def body752_31 : Prog (BitVec 64) :=
.seq body752_30 body752_13

def body752_32 : Prog (BitVec 64) :=
.seq body752_31 body752_14

def body752_33 : Prog (BitVec 64) :=
.seq body752_32 body752_15

def body752_34 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 64#64) body752_33

def body752_35 : Prog (BitVec 64) :=
.dec ("started") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body752_34

def body752_36 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1376#64])) body752_35

def body752_37 : Prog (BitVec 64) :=
.seq body752_27 body752_36

def body752_38 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) body752_37

def body752_39 : Prog (BitVec 64) :=
.decCall ("base") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) body752_38

def body752_40 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body752_39

def originalData752 : Decl (BitVec 64) :=
.function { name := "fp12_pow_absx", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body752_26, returnShape := (Flapjack.Shape.one) }
def simplifiedData752 : Decl (BitVec 64) :=
.function { name := "fp12_pow_absx", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body752_40, returnShape := (Flapjack.Shape.one) }
def original752 := Pancake.PanLang.declToHOL originalData752
def simplified752 := Pancake.PanLang.declToHOL simplifiedData752
end InitECandidate.Proofs.FrontendStages.Declarations
