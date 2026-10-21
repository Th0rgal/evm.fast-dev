import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data868
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate835
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody868_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_fresh_tx" []

def globalBody868_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 70#64)

def globalBody868_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody868_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code"))
  (Flapjack.Exp.const 0#64)) globalBody868_1 globalBody868_2

def globalBody868_4 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 71#64)

def globalBody868_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64]))
  (Flapjack.Exp.const 0#64)) globalBody868_4 globalBody868_2

def globalBody868_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "out")

def globalBody868_7 : Prog (BitVec 64) :=
.seq globalBody868_5 globalBody868_6

def globalBody868_8 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("process_unchecked_system_transaction") ([Flapjack.Exp.var Flapjack.VarKind.local "target", Flapjack.Exp.var Flapjack.VarKind.local "empty",
  Flapjack.Exp.const 0#64]) globalBody868_7

def globalBody868_9 : Prog (BitVec 64) :=
.decCall ("empty") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) globalBody868_8

def globalBody868_10 : Prog (BitVec 64) :=
.seq globalBody868_3 globalBody868_9

def globalBody868_11 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "target"]) globalBody868_10

def globalBody868_12 : Prog (BitVec 64) :=
.seq globalBody868_0 globalBody868_11

def globalData868 : Decl (BitVec 64) :=
.function { name := "process_checked_system_transaction", inline := false, exported := false, params := [("target", Flapjack.Shape.one)], body := globalBody868_12, returnShape := (Flapjack.Shape.one) }
def globalOutput868 := Pancake.PanLang.declToHOL globalData868
end InitECandidate.Proofs.FrontendStages.Declarations
