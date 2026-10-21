import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify518
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body534_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body534_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
          Flapjack.Exp.const 96#64])]

def body534_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body534_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body534_4 : Prog (BitVec 64) :=
.seq body534_2 body534_3

def body534_5 : Prog (BitVec 64) :=
.seq body534_1 body534_4

def body534_6 : Prog (BitVec 64) :=
.seq body534_0 body534_5

def body534_7 : Prog (BitVec 64) :=
.seq body534_0 body534_1

def body534_8 : Prog (BitVec 64) :=
.seq body534_7 body534_2

def body534_9 : Prog (BitVec 64) :=
.seq body534_8 body534_3

def originalData534 : Decl (BitVec 64) :=
.function { name := "op_calldatasize", inline := false, exported := false, params := [], body := body534_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData534 : Decl (BitVec 64) :=
.function { name := "op_calldatasize", inline := false, exported := false, params := [], body := body534_9, returnShape := (Flapjack.Shape.one) }
def original534 := Pancake.PanLang.declToHOL originalData534
def simplified534 := Pancake.PanLang.declToHOL simplifiedData534
end InitECandidate.Proofs.FrontendStages.Declarations
