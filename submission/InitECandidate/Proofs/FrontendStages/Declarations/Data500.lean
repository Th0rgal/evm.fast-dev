import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify484
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body500_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 8#64]

def body500_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 6#64)

def body500_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body500_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body500_1 body500_2

def body500_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dest"))

def body500_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body500_6 : Prog (BitVec 64) :=
.seq body500_4 body500_5

def body500_7 : Prog (BitVec 64) :=
.seq body500_3 body500_6

def body500_8 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("is_valid_jumpdest") ([Flapjack.Exp.var Flapjack.VarKind.local "dest"]) body500_7

def body500_9 : Prog (BitVec 64) :=
.seq body500_0 body500_8

def body500_10 : Prog (BitVec 64) :=
.decCall ("dest") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body500_9

def body500_11 : Prog (BitVec 64) :=
.seq body500_3 body500_4

def body500_12 : Prog (BitVec 64) :=
.seq body500_11 body500_5

def body500_13 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("is_valid_jumpdest") ([Flapjack.Exp.var Flapjack.VarKind.local "dest"]) body500_12

def body500_14 : Prog (BitVec 64) :=
.seq body500_0 body500_13

def body500_15 : Prog (BitVec 64) :=
.decCall ("dest") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body500_14

def originalData500 : Decl (BitVec 64) :=
.function { name := "op_jump", inline := false, exported := false, params := [], body := body500_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData500 : Decl (BitVec 64) :=
.function { name := "op_jump", inline := false, exported := false, params := [], body := body500_15, returnShape := (Flapjack.Shape.one) }
def original500 := Pancake.PanLang.declToHOL originalData500
def simplified500 := Pancake.PanLang.declToHOL simplifiedData500
end InitECandidate.Proofs.FrontendStages.Declarations
