import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data737
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate721
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody737_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def globalBody737_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]]

def globalBody737_2 : Prog (BitVec 64) :=
.seq globalBody737_0 globalBody737_1

def globalBody737_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64]]

def globalBody737_4 : Prog (BitVec 64) :=
.seq globalBody737_2 globalBody737_3

def globalBody737_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody737_6 : Prog (BitVec 64) :=
.seq globalBody737_4 globalBody737_5

def globalData737 : Decl (BitVec 64) :=
.function { name := "fp6_set_one", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := globalBody737_6, returnShape := (Flapjack.Shape.one) }
def globalOutput737 := Pancake.PanLang.declToHOL globalData737
end InitECandidate.Proofs.FrontendStages.Declarations
