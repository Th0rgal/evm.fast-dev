import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data265
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate249
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody265_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "root_node")

def globalBody265_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "secured")

def globalBody265_2 : Prog (BitVec 64) :=
.seq globalBody265_0 globalBody265_1

def globalBody265_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "m")

def globalBody265_4 : Prog (BitVec 64) :=
.seq globalBody265_2 globalBody265_3

def globalBody265_5 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 16#64]) globalBody265_4

def globalData265 : Decl (BitVec 64) :=
.function { name := "mpt_new", inline := false, exported := false, params := [("root_node", Flapjack.Shape.one), ("secured", Flapjack.Shape.one)], body := globalBody265_5, returnShape := (Flapjack.Shape.one) }
def globalOutput265 := Pancake.PanLang.declToHOL globalData265
end InitECandidate.Proofs.FrontendStages.Declarations
