import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data504
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate488
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody504_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 1#64]

def globalBody504_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody504_2 : Prog (BitVec 64) :=
.seq globalBody504_0 globalBody504_1

def globalBody504_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody504_4 : Prog (BitVec 64) :=
.seq globalBody504_2 globalBody504_3

def globalData504 : Decl (BitVec 64) :=
.function { name := "op_jumpdest", inline := false, exported := false, params := [], body := globalBody504_4, returnShape := (Flapjack.Shape.one) }
def globalOutput504 := Pancake.PanLang.declToHOL globalData504
end InitECandidate.Proofs.FrontendStages.Declarations
