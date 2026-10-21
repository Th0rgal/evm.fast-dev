import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify762
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body778_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1344#64],
    Flapjack.Exp.const 4#64]

def body778_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body778_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "inf")

def body778_3 : Prog (BitVec 64) :=
.seq body778_1 body778_2

def body778_4 : Prog (BitVec 64) :=
.decCall ("inf") (Flapjack.Shape.one) ("g2_is_inf") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) body778_3

def body778_5 : Prog (BitVec 64) :=
.seq body778_0 body778_4

def body778_6 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body778_5

def body778_7 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body778_6

def originalData778 : Decl (BitVec 64) :=
.function { name := "g2_subgroup_check", inline := false, exported := false, params := [("p", Flapjack.Shape.one)], body := body778_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData778 : Decl (BitVec 64) :=
.function { name := "g2_subgroup_check", inline := false, exported := false, params := [("p", Flapjack.Shape.one)], body := body778_7, returnShape := (Flapjack.Shape.one) }
def original778 := Pancake.PanLang.declToHOL originalData778
def simplified778 := Pancake.PanLang.declToHOL simplifiedData778
end InitECandidate.Proofs.FrontendStages.Declarations
