import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify821
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body837_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sha256"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "arr",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "arr",
          Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
          Flapjack.Exp.const 8#64]),
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "cat",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]]

def body837_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body837_2 : Prog (BitVec 64) :=
.seq body837_0 body837_1

def body837_3 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body837_2

def body837_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sha256"
  [Flapjack.Exp.var Flapjack.VarKind.local "cat",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 32#64],
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body837_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body837_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body837_7 : Prog (BitVec 64) :=
.seq body837_5 body837_6

def body837_8 : Prog (BitVec 64) :=
.seq body837_4 body837_7

def body837_9 : Prog (BitVec 64) :=
.seq body837_3 body837_8

def body837_10 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body837_9

def body837_11 : Prog (BitVec 64) :=
.decCall ("cat") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 32#64],
      Flapjack.Exp.const 8#64]]) body837_10

def body837_12 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body837_11

def body837_13 : Prog (BitVec 64) :=
.seq body837_3 body837_4

def body837_14 : Prog (BitVec 64) :=
.seq body837_13 body837_5

def body837_15 : Prog (BitVec 64) :=
.seq body837_14 body837_6

def body837_16 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body837_15

def body837_17 : Prog (BitVec 64) :=
.decCall ("cat") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 32#64],
      Flapjack.Exp.const 8#64]]) body837_16

def body837_18 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body837_17

def originalData837 : Decl (BitVec 64) :=
.function { name := "compute_requests_hash", inline := false, exported := false, params := [("arr", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body837_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData837 : Decl (BitVec 64) :=
.function { name := "compute_requests_hash", inline := false, exported := false, params := [("arr", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body837_18, returnShape := (Flapjack.Shape.one) }
def original837 := Pancake.PanLang.declToHOL originalData837
def simplified837 := Pancake.PanLang.declToHOL simplifiedData837
end InitECandidate.Proofs.FrontendStages.Declarations
