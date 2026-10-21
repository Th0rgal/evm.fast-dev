import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data387
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate371
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody387_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "destroy_storage" [Flapjack.Exp.var Flapjack.VarKind.local "addr"]

def globalBody387_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_account"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 1#64]

def globalBody387_2 : Prog (BitVec 64) :=
.seq globalBody387_0 globalBody387_1

def globalBody387_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody387_4 : Prog (BitVec 64) :=
.seq globalBody387_2 globalBody387_3

def globalData387 : Decl (BitVec 64) :=
.function { name := "destroy_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := globalBody387_4, returnShape := (Flapjack.Shape.one) }
def globalOutput387 := Pancake.PanLang.declToHOL globalData387
end InitECandidate.Proofs.FrontendStages.Declarations
