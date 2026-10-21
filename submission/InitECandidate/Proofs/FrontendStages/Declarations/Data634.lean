import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify618
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body634_0 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pt")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 1#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body634_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 1#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body634_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body634_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body634_4 : Prog (BitVec 64) :=
.seq body634_2 body634_3

def body634_5 : Prog (BitVec 64) :=
.seq body634_1 body634_4

def body634_6 : Prog (BitVec 64) :=
.seq body634_0 body634_5

def body634_7 : Prog (BitVec 64) :=
.seq body634_0 body634_1

def body634_8 : Prog (BitVec 64) :=
.seq body634_7 body634_2

def body634_9 : Prog (BitVec 64) :=
.seq body634_8 body634_3

def originalData634 : Decl (BitVec 64) :=
.function { name := "p256_set_infinity", inline := false, exported := false, params := [("pt", Flapjack.Shape.one)], body := body634_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData634 : Decl (BitVec 64) :=
.function { name := "p256_set_infinity", inline := false, exported := false, params := [("pt", Flapjack.Shape.one)], body := body634_9, returnShape := (Flapjack.Shape.one) }
def original634 := Pancake.PanLang.declToHOL originalData634
def simplified634 := Pancake.PanLang.declToHOL simplifiedData634
end InitECandidate.Proofs.FrontendStages.Declarations
