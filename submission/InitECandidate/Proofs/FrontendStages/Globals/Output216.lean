import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data216
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate200
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody216_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "root",
    Flapjack.Exp.const 32#64]

def globalBody216_1 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "succ")

def globalBody216_2 : Prog (BitVec 64) :=
.seq globalBody216_0 globalBody216_1

def globalBody216_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_le64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 33#64],
    Flapjack.Exp.var Flapjack.VarKind.local "chain_id"]

def globalBody216_4 : Prog (BitVec 64) :=
.seq globalBody216_2 globalBody216_3

def globalBody216_5 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 41#64])
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "schema_id", Flapjack.Exp.const 255#64])

def globalBody216_6 : Prog (BitVec 64) :=
.seq globalBody216_4 globalBody216_5

def globalBody216_7 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 42#64])
  (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "schema_id")
    (Flapjack.Exp.const 8#64))

def globalBody216_8 : Prog (BitVec 64) :=
.seq globalBody216_6 globalBody216_7

def globalBody216_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 43#64)

def globalBody216_10 : Prog (BitVec 64) :=
.seq globalBody216_8 globalBody216_9

def globalData216 : Decl (BitVec 64) :=
.function { name := "serialize_result", inline := false, exported := false, params := [("out", Flapjack.Shape.one), ("root", Flapjack.Shape.one), ("succ", Flapjack.Shape.one),
  ("chain_id", Flapjack.Shape.one), ("schema_id", Flapjack.Shape.one)], body := globalBody216_10, returnShape := (Flapjack.Shape.one) }
def globalOutput216 := Pancake.PanLang.declToHOL globalData216
end InitECandidate.Proofs.FrontendStages.Declarations
