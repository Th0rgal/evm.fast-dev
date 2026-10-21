import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify249
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body265_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "root_node")

def body265_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "secured")

def body265_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "m")

def body265_3 : Prog (BitVec 64) :=
.seq body265_1 body265_2

def body265_4 : Prog (BitVec 64) :=
.seq body265_0 body265_3

def body265_5 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 16#64]) body265_4

def body265_6 : Prog (BitVec 64) :=
.seq body265_0 body265_1

def body265_7 : Prog (BitVec 64) :=
.seq body265_6 body265_2

def body265_8 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 16#64]) body265_7

def originalData265 : Decl (BitVec 64) :=
.function { name := "mpt_new", inline := false, exported := false, params := [("root_node", Flapjack.Shape.one), ("secured", Flapjack.Shape.one)], body := body265_5, returnShape := (Flapjack.Shape.one) }
def simplifiedData265 : Decl (BitVec 64) :=
.function { name := "mpt_new", inline := false, exported := false, params := [("root_node", Flapjack.Shape.one), ("secured", Flapjack.Shape.one)], body := body265_8, returnShape := (Flapjack.Shape.one) }
def original265 := Pancake.PanLang.declToHOL originalData265
def simplified265 := Pancake.PanLang.declToHOL simplifiedData265
end InitECandidate.Proofs.FrontendStages.Declarations
