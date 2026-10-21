import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify512
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body528_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body528_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push" [Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body528_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body528_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body528_4 : Prog (BitVec 64) :=
.seq body528_2 body528_3

def body528_5 : Prog (BitVec 64) :=
.seq body528_1 body528_4

def body528_6 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("address_to_u256") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
        Flapjack.Exp.const 32#64])]) body528_5

def body528_7 : Prog (BitVec 64) :=
.seq body528_0 body528_6

def body528_8 : Prog (BitVec 64) :=
.seq body528_1 body528_2

def body528_9 : Prog (BitVec 64) :=
.seq body528_8 body528_3

def body528_10 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("address_to_u256") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
        Flapjack.Exp.const 32#64])]) body528_9

def body528_11 : Prog (BitVec 64) :=
.seq body528_0 body528_10

def originalData528 : Decl (BitVec 64) :=
.function { name := "op_address", inline := false, exported := false, params := [], body := body528_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData528 : Decl (BitVec 64) :=
.function { name := "op_address", inline := false, exported := false, params := [], body := body528_11, returnShape := (Flapjack.Shape.one) }
def original528 := Pancake.PanLang.declToHOL originalData528
def simplified528 := Pancake.PanLang.declToHOL simplifiedData528
end InitECandidate.Proofs.FrontendStages.Declarations
