import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify726
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body742_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul_xi"
  [Flapjack.Exp.var Flapjack.VarKind.local "t",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 192#64]]

def body742_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 96#64]]

def body742_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body742_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "t"]

def body742_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body742_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body742_6 : Prog (BitVec 64) :=
.seq body742_4 body742_5

def body742_7 : Prog (BitVec 64) :=
.seq body742_3 body742_6

def body742_8 : Prog (BitVec 64) :=
.seq body742_2 body742_7

def body742_9 : Prog (BitVec 64) :=
.seq body742_1 body742_8

def body742_10 : Prog (BitVec 64) :=
.seq body742_0 body742_9

def body742_11 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body742_10

def body742_12 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body742_11

def body742_13 : Prog (BitVec 64) :=
.seq body742_0 body742_1

def body742_14 : Prog (BitVec 64) :=
.seq body742_13 body742_2

def body742_15 : Prog (BitVec 64) :=
.seq body742_14 body742_3

def body742_16 : Prog (BitVec 64) :=
.seq body742_15 body742_4

def body742_17 : Prog (BitVec 64) :=
.seq body742_16 body742_5

def body742_18 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body742_17

def body742_19 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body742_18

def originalData742 : Decl (BitVec 64) :=
.function { name := "fp6_mul_v", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body742_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData742 : Decl (BitVec 64) :=
.function { name := "fp6_mul_v", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body742_19, returnShape := (Flapjack.Shape.one) }
def original742 := Pancake.PanLang.declToHOL originalData742
def simplified742 := Pancake.PanLang.declToHOL simplifiedData742
end InitECandidate.Proofs.FrontendStages.Declarations
