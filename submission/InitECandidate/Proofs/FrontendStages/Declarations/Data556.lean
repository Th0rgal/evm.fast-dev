import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify540
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body556_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body556_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 0#64])]

def body556_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body556_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body556_4 : Prog (BitVec 64) :=
.seq body556_2 body556_3

def body556_5 : Prog (BitVec 64) :=
.seq body556_1 body556_4

def body556_6 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body556_5

def body556_7 : Prog (BitVec 64) :=
.seq body556_0 body556_6

def body556_8 : Prog (BitVec 64) :=
.seq body556_1 body556_2

def body556_9 : Prog (BitVec 64) :=
.seq body556_8 body556_3

def body556_10 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body556_9

def body556_11 : Prog (BitVec 64) :=
.seq body556_0 body556_10

def originalData556 : Decl (BitVec 64) :=
.function { name := "op_chainid", inline := false, exported := false, params := [], body := body556_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData556 : Decl (BitVec 64) :=
.function { name := "op_chainid", inline := false, exported := false, params := [], body := body556_11, returnShape := (Flapjack.Shape.one) }
def original556 := Pancake.PanLang.declToHOL originalData556
def simplified556 := Pancake.PanLang.declToHOL simplifiedData556
end InitECandidate.Proofs.FrontendStages.Declarations
