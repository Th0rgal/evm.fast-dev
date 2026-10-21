import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify730
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body746_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "one"]

def body746_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body746_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "e")

def body746_3 : Prog (BitVec 64) :=
.seq body746_1 body746_2

def body746_4 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "one", Flapjack.Exp.const 576#64]) body746_3

def body746_5 : Prog (BitVec 64) :=
.seq body746_0 body746_4

def body746_6 : Prog (BitVec 64) :=
.decCall ("one") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) body746_5

def body746_7 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body746_6

def originalData746 : Decl (BitVec 64) :=
.function { name := "fp12_is_one", inline := false, exported := false, params := [("a", Flapjack.Shape.one)], body := body746_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData746 : Decl (BitVec 64) :=
.function { name := "fp12_is_one", inline := false, exported := false, params := [("a", Flapjack.Shape.one)], body := body746_7, returnShape := (Flapjack.Shape.one) }
def original746 := Pancake.PanLang.declToHOL originalData746
def simplified746 := Pancake.PanLang.declToHOL simplifiedData746
end InitECandidate.Proofs.FrontendStages.Declarations
