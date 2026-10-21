import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify447
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body463_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 176#64]

def body463_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "m")

def body463_2 : Prog (BitVec 64) :=
.seq body463_0 body463_1

def body463_3 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 176#64]) body463_2

def originalData463 : Decl (BitVec 64) :=
.function { name := "msg_new_scratch", inline := false, exported := false, params := [], body := body463_3, returnShape := (Flapjack.Shape.one) }
def simplifiedData463 : Decl (BitVec 64) :=
.function { name := "msg_new_scratch", inline := false, exported := false, params := [], body := body463_3, returnShape := (Flapjack.Shape.one) }
def original463 := Pancake.PanLang.declToHOL originalData463
def simplified463 := Pancake.PanLang.declToHOL simplifiedData463
end InitECandidate.Proofs.FrontendStages.Declarations
