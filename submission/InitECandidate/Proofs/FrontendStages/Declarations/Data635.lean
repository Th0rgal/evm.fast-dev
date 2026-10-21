import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify619
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body635_0 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pt") (Flapjack.Exp.var Flapjack.VarKind.local "x")

def body635_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y")

def body635_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 1#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body635_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body635_4 : Prog (BitVec 64) :=
.seq body635_2 body635_3

def body635_5 : Prog (BitVec 64) :=
.seq body635_1 body635_4

def body635_6 : Prog (BitVec 64) :=
.seq body635_0 body635_5

def body635_7 : Prog (BitVec 64) :=
.seq body635_0 body635_1

def body635_8 : Prog (BitVec 64) :=
.seq body635_7 body635_2

def body635_9 : Prog (BitVec 64) :=
.seq body635_8 body635_3

def originalData635 : Decl (BitVec 64) :=
.function { name := "p256_set_affine", inline := false, exported := false, params := [("pt", Flapjack.Shape.one),
  ("x", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("y", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body635_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData635 : Decl (BitVec 64) :=
.function { name := "p256_set_affine", inline := false, exported := false, params := [("pt", Flapjack.Shape.one),
  ("x", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("y", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body635_9, returnShape := (Flapjack.Shape.one) }
def original635 := Pancake.PanLang.declToHOL originalData635
def simplified635 := Pancake.PanLang.declToHOL simplifiedData635
end InitECandidate.Proofs.FrontendStages.Declarations
