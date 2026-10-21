import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data471
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate455
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody471_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "addr"]

def globalBody471_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody471_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "c") (Flapjack.Exp.const 3000#64)) globalBody471_0 globalBody471_1

def globalBody471_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody471_4 : Prog (BitVec 64) :=
.seq globalBody471_2 globalBody471_3

def globalData471 : Decl (BitVec 64) :=
.function { name := "warm_after_charge", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("c", Flapjack.Shape.one)], body := globalBody471_4, returnShape := (Flapjack.Shape.one) }
def globalOutput471 := Pancake.PanLang.declToHOL globalData471
end InitECandidate.Proofs.FrontendStages.Declarations
