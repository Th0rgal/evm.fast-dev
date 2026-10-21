import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify852
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body868_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_fresh_tx" []

def body868_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 70#64)

def body868_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body868_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code"))
  (Flapjack.Exp.const 0#64)) body868_1 body868_2

def body868_4 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 71#64)

def body868_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64]))
  (Flapjack.Exp.const 0#64)) body868_4 body868_2

def body868_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body868_7 : Prog (BitVec 64) :=
.seq body868_5 body868_6

def body868_8 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("process_unchecked_system_transaction") ([Flapjack.Exp.var Flapjack.VarKind.local "target", Flapjack.Exp.var Flapjack.VarKind.local "empty",
  Flapjack.Exp.const 0#64]) body868_7

def body868_9 : Prog (BitVec 64) :=
.decCall ("empty") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body868_8

def body868_10 : Prog (BitVec 64) :=
.seq body868_3 body868_9

def body868_11 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "target"]) body868_10

def body868_12 : Prog (BitVec 64) :=
.seq body868_0 body868_11

def originalData868 : Decl (BitVec 64) :=
.function { name := "process_checked_system_transaction", inline := false, exported := false, params := [("target", Flapjack.Shape.one)], body := body868_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData868 : Decl (BitVec 64) :=
.function { name := "process_checked_system_transaction", inline := false, exported := false, params := [("target", Flapjack.Shape.one)], body := body868_12, returnShape := (Flapjack.Shape.one) }
def original868 := Pancake.PanLang.declToHOL originalData868
def simplified868 := Pancake.PanLang.declToHOL simplifiedData868
end InitECandidate.Proofs.FrontendStages.Declarations
