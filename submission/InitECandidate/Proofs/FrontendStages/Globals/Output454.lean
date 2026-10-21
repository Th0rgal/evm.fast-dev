import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data454
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate438
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody454_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 18446744073709551615#64)

def globalBody454_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody454_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sq"))
  (Flapjack.Exp.const 0#64)) globalBody454_0 globalBody454_1

def globalBody454_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def globalBody454_4 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.const 3#64],
  Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sq"))
    (Flapjack.Exp.const 9#64)]) globalBody454_3

def globalBody454_5 : Prog (BitVec 64) :=
.seq globalBody454_2 globalBody454_4

def globalBody454_6 : Prog (BitVec 64) :=
.decCall ("sq") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("mul64x64") ([Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "w"]) globalBody454_5

def globalBody454_7 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "size"]) globalBody454_6

def globalData454 : Decl (BitVec 64) :=
.function { name := "memory_gas_cost", inline := false, exported := false, params := [("size", Flapjack.Shape.one)], body := globalBody454_7, returnShape := (Flapjack.Shape.one) }
def globalOutput454 := Pancake.PanLang.declToHOL globalData454
end InitECandidate.Proofs.FrontendStages.Declarations
