import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify775
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body791_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "v",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "kp",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 1#64],
            Flapjack.Exp.const 96#64]]]

def body791_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v",
    Flapjack.Exp.var Flapjack.VarKind.local "x"]

def body791_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "zp",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 96#64]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "kp",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.op Flapjack.BinOp.sub
              [Flapjack.Exp.op Flapjack.BinOp.sub
                  [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 2#64],
                Flapjack.Exp.var Flapjack.VarKind.local "j"],
            Flapjack.Exp.const 96#64]]]

def body791_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body791_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def body791_5 : Prog (BitVec 64) :=
.seq body791_3 body791_4

def body791_6 : Prog (BitVec 64) :=
.seq body791_2 body791_5

def body791_7 : Prog (BitVec 64) :=
.seq body791_1 body791_6

def body791_8 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 1#64])) body791_7

def body791_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body791_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body791_11 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body791_12 : Prog (BitVec 64) :=
.seq body791_10 body791_11

def body791_13 : Prog (BitVec 64) :=
.seq body791_9 body791_12

def body791_14 : Prog (BitVec 64) :=
.seq body791_8 body791_13

def body791_15 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body791_14

def body791_16 : Prog (BitVec 64) :=
.seq body791_0 body791_15

def body791_17 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body791_16

def body791_18 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body791_17

def body791_19 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body791_18

def body791_20 : Prog (BitVec 64) :=
.seq body791_1 body791_2

def body791_21 : Prog (BitVec 64) :=
.seq body791_20 body791_3

def body791_22 : Prog (BitVec 64) :=
.seq body791_21 body791_4

def body791_23 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 1#64])) body791_22

def body791_24 : Prog (BitVec 64) :=
.seq body791_23 body791_9

def body791_25 : Prog (BitVec 64) :=
.seq body791_24 body791_10

def body791_26 : Prog (BitVec 64) :=
.seq body791_25 body791_11

def body791_27 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body791_26

def body791_28 : Prog (BitVec 64) :=
.seq body791_0 body791_27

def body791_29 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body791_28

def body791_30 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body791_29

def body791_31 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body791_30

def originalData791 : Decl (BitVec 64) :=
.function { name := "iso_horner_fp2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("kp", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("x", Flapjack.Shape.one),
  ("zp", Flapjack.Shape.one)], body := body791_19, returnShape := (Flapjack.Shape.one) }
def simplifiedData791 : Decl (BitVec 64) :=
.function { name := "iso_horner_fp2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("kp", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("x", Flapjack.Shape.one),
  ("zp", Flapjack.Shape.one)], body := body791_31, returnShape := (Flapjack.Shape.one) }
def original791 := Pancake.PanLang.declToHOL originalData791
def simplified791 := Pancake.PanLang.declToHOL simplifiedData791
end InitECandidate.Proofs.FrontendStages.Declarations
