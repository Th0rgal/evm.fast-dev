import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data462
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate446
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody462_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 176#64]

def globalBody462_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "m")

def globalBody462_2 : Prog (BitVec 64) :=
.seq globalBody462_0 globalBody462_1

def globalBody462_3 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 176#64]) globalBody462_2

def globalData462 : Decl (BitVec 64) :=
.function { name := "msg_new", inline := false, exported := false, params := [], body := globalBody462_3, returnShape := (Flapjack.Shape.one) }
def globalOutput462 := Pancake.PanLang.declToHOL globalData462
end InitECandidate.Proofs.FrontendStages.Declarations
