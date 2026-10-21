import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify659
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body675_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 1152#64]

def body675_1 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "out")
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.var Flapjack.VarKind.local "g1"))

def body675_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 384#64])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "g1", Flapjack.Exp.const 32#64]))

def body675_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 384#64]])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "g1", Flapjack.Exp.const 64#64]))

def body675_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body675_5 : Prog (BitVec 64) :=
.seq body675_3 body675_4

def body675_6 : Prog (BitVec 64) :=
.seq body675_2 body675_5

def body675_7 : Prog (BitVec 64) :=
.seq body675_1 body675_6

def body675_8 : Prog (BitVec 64) :=
.seq body675_0 body675_7

def body675_9 : Prog (BitVec 64) :=
.seq body675_0 body675_1

def body675_10 : Prog (BitVec 64) :=
.seq body675_9 body675_2

def body675_11 : Prog (BitVec 64) :=
.seq body675_10 body675_3

def body675_12 : Prog (BitVec 64) :=
.seq body675_11 body675_4

def originalData675 : Decl (BitVec 64) :=
.function { name := "fq12_cast", inline := false, exported := false, params := [("out", Flapjack.Shape.one), ("g1", Flapjack.Shape.one)], body := body675_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData675 : Decl (BitVec 64) :=
.function { name := "fq12_cast", inline := false, exported := false, params := [("out", Flapjack.Shape.one), ("g1", Flapjack.Shape.one)], body := body675_12, returnShape := (Flapjack.Shape.one) }
def original675 := Pancake.PanLang.declToHOL originalData675
def simplified675 := Pancake.PanLang.declToHOL simplifiedData675
end InitECandidate.Proofs.FrontendStages.Declarations
