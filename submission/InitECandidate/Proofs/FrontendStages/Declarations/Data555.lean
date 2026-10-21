import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify539
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body555_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body555_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 8#64])]

def body555_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body555_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body555_4 : Prog (BitVec 64) :=
.seq body555_2 body555_3

def body555_5 : Prog (BitVec 64) :=
.seq body555_1 body555_4

def body555_6 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body555_5

def body555_7 : Prog (BitVec 64) :=
.seq body555_0 body555_6

def body555_8 : Prog (BitVec 64) :=
.seq body555_1 body555_2

def body555_9 : Prog (BitVec 64) :=
.seq body555_8 body555_3

def body555_10 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body555_9

def body555_11 : Prog (BitVec 64) :=
.seq body555_0 body555_10

def originalData555 : Decl (BitVec 64) :=
.function { name := "op_gaslimit", inline := false, exported := false, params := [], body := body555_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData555 : Decl (BitVec 64) :=
.function { name := "op_gaslimit", inline := false, exported := false, params := [], body := body555_11, returnShape := (Flapjack.Shape.one) }
def original555 := Pancake.PanLang.declToHOL originalData555
def simplified555 := Pancake.PanLang.declToHOL simplifiedData555
end InitECandidate.Proofs.FrontendStages.Declarations
