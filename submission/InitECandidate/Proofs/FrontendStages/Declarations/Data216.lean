import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify200
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body216_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "root",
    Flapjack.Exp.const 32#64]

def body216_1 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "succ")

def body216_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_le64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 33#64],
    Flapjack.Exp.var Flapjack.VarKind.local "chain_id"]

def body216_3 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 41#64])
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "schema_id", Flapjack.Exp.const 255#64])

def body216_4 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 42#64])
  (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "schema_id")
    (Flapjack.Exp.const 8#64))

def body216_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 43#64)

def body216_6 : Prog (BitVec 64) :=
.seq body216_4 body216_5

def body216_7 : Prog (BitVec 64) :=
.seq body216_3 body216_6

def body216_8 : Prog (BitVec 64) :=
.seq body216_2 body216_7

def body216_9 : Prog (BitVec 64) :=
.seq body216_1 body216_8

def body216_10 : Prog (BitVec 64) :=
.seq body216_0 body216_9

def body216_11 : Prog (BitVec 64) :=
.seq body216_0 body216_1

def body216_12 : Prog (BitVec 64) :=
.seq body216_11 body216_2

def body216_13 : Prog (BitVec 64) :=
.seq body216_12 body216_3

def body216_14 : Prog (BitVec 64) :=
.seq body216_13 body216_4

def body216_15 : Prog (BitVec 64) :=
.seq body216_14 body216_5

def originalData216 : Decl (BitVec 64) :=
.function { name := "serialize_result", inline := false, exported := false, params := [("out", Flapjack.Shape.one), ("root", Flapjack.Shape.one), ("succ", Flapjack.Shape.one),
  ("chain_id", Flapjack.Shape.one), ("schema_id", Flapjack.Shape.one)], body := body216_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData216 : Decl (BitVec 64) :=
.function { name := "serialize_result", inline := false, exported := false, params := [("out", Flapjack.Shape.one), ("root", Flapjack.Shape.one), ("succ", Flapjack.Shape.one),
  ("chain_id", Flapjack.Shape.one), ("schema_id", Flapjack.Shape.one)], body := body216_15, returnShape := (Flapjack.Shape.one) }
def original216 := Pancake.PanLang.declToHOL originalData216
def simplified216 := Pancake.PanLang.declToHOL simplifiedData216
end InitECandidate.Proofs.FrontendStages.Declarations
