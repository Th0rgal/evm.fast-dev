import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data255
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate232
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody255_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 176#64]

def globalBody255_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 3#64)

def globalBody255_2 : Prog (BitVec 64) :=
.seq globalBody255_0 globalBody255_1

def globalBody255_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "nd")

def globalBody255_4 : Prog (BitVec 64) :=
.seq globalBody255_2 globalBody255_3

def globalBody255_5 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 176#64]) globalBody255_4

def globalData255 : Decl (BitVec 64) :=
.function { name := "node_new_branch", inline := false, exported := false, params := [], body := globalBody255_5, returnShape := (Flapjack.Shape.one) }
def globalOutput255 := Pancake.PanLang.declToHOL globalData255
end InitECandidate.Proofs.FrontendStages.Declarations
