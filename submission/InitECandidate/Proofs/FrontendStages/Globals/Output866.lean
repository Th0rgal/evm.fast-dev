import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data866
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate833
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody866_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 200#64]

def globalBody866_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "te")

def globalBody866_2 : Prog (BitVec 64) :=
.seq globalBody866_0 globalBody866_1

def globalBody866_3 : Prog (BitVec 64) :=
.decCall ("te") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 200#64]) globalBody866_2

def globalData866 : Decl (BitVec 64) :=
.function { name := "te_new", inline := false, exported := false, params := [], body := globalBody866_3, returnShape := (Flapjack.Shape.one) }
def globalOutput866 := Pancake.PanLang.declToHOL globalData866
end InitECandidate.Proofs.FrontendStages.Declarations
