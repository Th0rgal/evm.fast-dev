import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify560
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body576_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "refill_frame_state_gas" []

def body576_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_halt" [Flapjack.Exp.var Flapjack.VarKind.local "err"]

def body576_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "evm_empty")

def body576_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 0#64)

def body576_4 : Prog (BitVec 64) :=
.seq body576_2 body576_3

def body576_5 : Prog (BitVec 64) :=
.seq body576_1 body576_4

def body576_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "err")

def body576_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "err") (Flapjack.Exp.const 1#64)) body576_5 body576_6

def body576_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 1#64)

def body576_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body576_10 : Prog (BitVec 64) :=
.seq body576_8 body576_9

def body576_11 : Prog (BitVec 64) :=
.seq body576_7 body576_10

def body576_12 : Prog (BitVec 64) :=
.seq body576_0 body576_11

def body576_13 : Prog (BitVec 64) :=
.seq body576_1 body576_2

def body576_14 : Prog (BitVec 64) :=
.seq body576_13 body576_3

def body576_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "err") (Flapjack.Exp.const 1#64)) body576_14 body576_6

def body576_16 : Prog (BitVec 64) :=
.seq body576_0 body576_15

def body576_17 : Prog (BitVec 64) :=
.seq body576_16 body576_8

def body576_18 : Prog (BitVec 64) :=
.seq body576_17 body576_9

def originalData576 : Decl (BitVec 64) :=
.function { name := "frame_exception", inline := false, exported := false, params := [("err", Flapjack.Shape.one)], body := body576_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData576 : Decl (BitVec 64) :=
.function { name := "frame_exception", inline := false, exported := false, params := [("err", Flapjack.Shape.one)], body := body576_18, returnShape := (Flapjack.Shape.one) }
def original576 := Pancake.PanLang.declToHOL originalData576
def simplified576 := Pancake.PanLang.declToHOL simplifiedData576
end InitECandidate.Proofs.FrontendStages.Declarations
