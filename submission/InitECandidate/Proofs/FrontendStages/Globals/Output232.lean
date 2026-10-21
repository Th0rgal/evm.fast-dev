import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data232
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate214
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody232_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody232_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody232_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "gas_limit")
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit", Flapjack.Exp.var Flapjack.VarKind.local "max_delta"])) globalBody232_0 globalBody232_1

def globalBody232_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit")
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "gas_limit", Flapjack.Exp.var Flapjack.VarKind.local "max_delta"])) globalBody232_0 globalBody232_1

def globalBody232_4 : Prog (BitVec 64) :=
.seq globalBody232_2 globalBody232_3

def globalBody232_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "gas_limit") (Flapjack.Exp.const 5000#64)) globalBody232_0 globalBody232_1

def globalBody232_6 : Prog (BitVec 64) :=
.seq globalBody232_4 globalBody232_5

def globalBody232_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody232_8 : Prog (BitVec 64) :=
.seq globalBody232_6 globalBody232_7

def globalBody232_9 : Prog (BitVec 64) :=
.decCall ("max_delta") (Flapjack.Shape.one) ("udiv") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit", Flapjack.Exp.const 1024#64]) globalBody232_8

def globalData232 : Decl (BitVec 64) :=
.function { name := "check_gas_limit", inline := false, exported := false, params := [("gas_limit", Flapjack.Shape.one), ("parent_gas_limit", Flapjack.Shape.one)], body := globalBody232_9, returnShape := (Flapjack.Shape.one) }
def globalOutput232 := Pancake.PanLang.declToHOL globalData232
end InitECandidate.Proofs.FrontendStages.Declarations
