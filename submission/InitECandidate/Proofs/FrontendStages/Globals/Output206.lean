import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data206
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate190
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody206_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "merkleize"
  [Flapjack.Exp.var Flapjack.VarKind.local "roots", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "lim", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody206_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mix_in_length"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody206_2 : Prog (BitVec 64) :=
.seq globalBody206_0 globalBody206_1

def globalBody206_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody206_4 : Prog (BitVec 64) :=
.seq globalBody206_2 globalBody206_3

def globalData206 : Decl (BitVec 64) :=
.function { name := "htr_list_roots", inline := false, exported := false, params := [("roots", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("lim", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody206_4, returnShape := (Flapjack.Shape.one) }
def globalOutput206 := Pancake.PanLang.declToHOL globalData206
end InitECandidate.Proofs.FrontendStages.Declarations
