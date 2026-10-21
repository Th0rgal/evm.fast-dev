import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data767
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate751
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody767_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def globalBody767_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]]

def globalBody767_2 : Prog (BitVec 64) :=
.seq globalBody767_0 globalBody767_1

def globalBody767_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64]]

def globalBody767_4 : Prog (BitVec 64) :=
.seq globalBody767_2 globalBody767_3

def globalBody767_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody767_6 : Prog (BitVec 64) :=
.seq globalBody767_4 globalBody767_5

def globalData767 : Decl (BitVec 64) :=
.function { name := "g2_set_inf", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := globalBody767_6, returnShape := (Flapjack.Shape.one) }
def globalOutput767 := Pancake.PanLang.declToHOL globalData767
end InitECandidate.Proofs.FrontendStages.Declarations
