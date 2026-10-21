import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify537
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body553_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body553_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 80#64])]

def body553_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body553_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body553_4 : Prog (BitVec 64) :=
.seq body553_2 body553_3

def body553_5 : Prog (BitVec 64) :=
.seq body553_1 body553_4

def body553_6 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body553_5

def body553_7 : Prog (BitVec 64) :=
.seq body553_0 body553_6

def body553_8 : Prog (BitVec 64) :=
.seq body553_1 body553_2

def body553_9 : Prog (BitVec 64) :=
.seq body553_8 body553_3

def body553_10 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body553_9

def body553_11 : Prog (BitVec 64) :=
.seq body553_0 body553_10

def originalData553 : Decl (BitVec 64) :=
.function { name := "op_timestamp", inline := false, exported := false, params := [], body := body553_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData553 : Decl (BitVec 64) :=
.function { name := "op_timestamp", inline := false, exported := false, params := [], body := body553_11, returnShape := (Flapjack.Shape.one) }
def original553 := Pancake.PanLang.declToHOL originalData553
def simplified553 := Pancake.PanLang.declToHOL simplifiedData553
end InitECandidate.Proofs.FrontendStages.Declarations
