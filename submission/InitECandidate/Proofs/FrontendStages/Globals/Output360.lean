import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data360
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate337
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody360_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 56#64]

def globalBody360_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "b")

def globalBody360_2 : Prog (BitVec 64) :=
.seq globalBody360_0 globalBody360_1

def globalBody360_3 : Prog (BitVec 64) :=
.decCall ("b") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 56#64]) globalBody360_2

def globalData360 : Decl (BitVec 64) :=
.function { name := "acct_copy", inline := false, exported := false, params := [("a", Flapjack.Shape.one)], body := globalBody360_3, returnShape := (Flapjack.Shape.one) }
def globalOutput360 := Pancake.PanLang.declToHOL globalData360
end InitECandidate.Proofs.FrontendStages.Declarations
