import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data470
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate454
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody470_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 100#64)

def globalBody470_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody470_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w") (Flapjack.Exp.const 0#64)) globalBody470_0 globalBody470_1

def globalBody470_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 3000#64)

def globalBody470_4 : Prog (BitVec 64) :=
.seq globalBody470_2 globalBody470_3

def globalBody470_5 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody470_4

def globalData470 : Decl (BitVec 64) :=
.function { name := "access_gas_cost", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := globalBody470_5, returnShape := (Flapjack.Shape.one) }
def globalOutput470 := Pancake.PanLang.declToHOL globalData470
end InitECandidate.Proofs.FrontendStages.Declarations
