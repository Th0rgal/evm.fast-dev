import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data452
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate431
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody452_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.rStruct
      [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
        Flapjack.Exp.const 0#64]]

def globalBody452_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody452_2 : Prog (BitVec 64) :=
.seq globalBody452_0 globalBody452_1

def globalData452 : Decl (BitVec 64) :=
.function { name := "stack_push_word", inline := false, exported := false, params := [("w", Flapjack.Shape.one)], body := globalBody452_2, returnShape := (Flapjack.Shape.one) }
def globalOutput452 := Pancake.PanLang.declToHOL globalData452
end InitECandidate.Proofs.FrontendStages.Declarations
