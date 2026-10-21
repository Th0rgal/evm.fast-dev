import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify488
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body504_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 1#64]

def body504_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body504_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body504_3 : Prog (BitVec 64) :=
.seq body504_1 body504_2

def body504_4 : Prog (BitVec 64) :=
.seq body504_0 body504_3

def body504_5 : Prog (BitVec 64) :=
.seq body504_0 body504_1

def body504_6 : Prog (BitVec 64) :=
.seq body504_5 body504_2

def originalData504 : Decl (BitVec 64) :=
.function { name := "op_jumpdest", inline := false, exported := false, params := [], body := body504_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData504 : Decl (BitVec 64) :=
.function { name := "op_jumpdest", inline := false, exported := false, params := [], body := body504_6, returnShape := (Flapjack.Shape.one) }
def original504 := Pancake.PanLang.declToHOL originalData504
def simplified504 := Pancake.PanLang.declToHOL simplifiedData504
end InitECandidate.Proofs.FrontendStages.Declarations
