import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify446
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body462_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 176#64]

def body462_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "m")

def body462_2 : Prog (BitVec 64) :=
.seq body462_0 body462_1

def body462_3 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 176#64]) body462_2

def originalData462 : Decl (BitVec 64) :=
.function { name := "msg_new", inline := false, exported := false, params := [], body := body462_3, returnShape := (Flapjack.Shape.one) }
def simplifiedData462 : Decl (BitVec 64) :=
.function { name := "msg_new", inline := false, exported := false, params := [], body := body462_3, returnShape := (Flapjack.Shape.one) }
def original462 := Pancake.PanLang.declToHOL originalData462
def simplified462 := Pancake.PanLang.declToHOL simplifiedData462
end InitECandidate.Proofs.FrontendStages.Declarations
