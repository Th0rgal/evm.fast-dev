import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify239
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body255_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 176#64]

def body255_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 3#64)

def body255_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "nd")

def body255_3 : Prog (BitVec 64) :=
.seq body255_1 body255_2

def body255_4 : Prog (BitVec 64) :=
.seq body255_0 body255_3

def body255_5 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 176#64]) body255_4

def body255_6 : Prog (BitVec 64) :=
.seq body255_0 body255_1

def body255_7 : Prog (BitVec 64) :=
.seq body255_6 body255_2

def body255_8 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 176#64]) body255_7

def originalData255 : Decl (BitVec 64) :=
.function { name := "node_new_branch", inline := false, exported := false, params := [], body := body255_5, returnShape := (Flapjack.Shape.one) }
def simplifiedData255 : Decl (BitVec 64) :=
.function { name := "node_new_branch", inline := false, exported := false, params := [], body := body255_8, returnShape := (Flapjack.Shape.one) }
def original255 := Pancake.PanLang.declToHOL originalData255
def simplified255 := Pancake.PanLang.declToHOL simplifiedData255
end InitECandidate.Proofs.FrontendStages.Declarations
