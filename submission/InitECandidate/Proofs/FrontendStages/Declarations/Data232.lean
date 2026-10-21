import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify216
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body232_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body232_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body232_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "gas_limit")
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit", Flapjack.Exp.var Flapjack.VarKind.local "max_delta"])) body232_0 body232_1

def body232_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit")
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "gas_limit", Flapjack.Exp.var Flapjack.VarKind.local "max_delta"])) body232_0 body232_1

def body232_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "gas_limit") (Flapjack.Exp.const 5000#64)) body232_0 body232_1

def body232_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body232_6 : Prog (BitVec 64) :=
.seq body232_4 body232_5

def body232_7 : Prog (BitVec 64) :=
.seq body232_3 body232_6

def body232_8 : Prog (BitVec 64) :=
.seq body232_2 body232_7

def body232_9 : Prog (BitVec 64) :=
.decCall ("max_delta") (Flapjack.Shape.one) ("udiv") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit", Flapjack.Exp.const 1024#64]) body232_8

def body232_10 : Prog (BitVec 64) :=
.seq body232_2 body232_3

def body232_11 : Prog (BitVec 64) :=
.seq body232_10 body232_4

def body232_12 : Prog (BitVec 64) :=
.seq body232_11 body232_5

def body232_13 : Prog (BitVec 64) :=
.decCall ("max_delta") (Flapjack.Shape.one) ("udiv") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit", Flapjack.Exp.const 1024#64]) body232_12

def originalData232 : Decl (BitVec 64) :=
.function { name := "check_gas_limit", inline := false, exported := false, params := [("gas_limit", Flapjack.Shape.one), ("parent_gas_limit", Flapjack.Shape.one)], body := body232_9, returnShape := (Flapjack.Shape.one) }
def simplifiedData232 : Decl (BitVec 64) :=
.function { name := "check_gas_limit", inline := false, exported := false, params := [("gas_limit", Flapjack.Shape.one), ("parent_gas_limit", Flapjack.Shape.one)], body := body232_13, returnShape := (Flapjack.Shape.one) }
def original232 := Pancake.PanLang.declToHOL originalData232
def simplified232 := Pancake.PanLang.declToHOL simplifiedData232
end InitECandidate.Proofs.FrontendStages.Declarations
