import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify532
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body548_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body548_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 48#64])]

def body548_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body548_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body548_4 : Prog (BitVec 64) :=
.seq body548_2 body548_3

def body548_5 : Prog (BitVec 64) :=
.seq body548_1 body548_4

def body548_6 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body548_5

def body548_7 : Prog (BitVec 64) :=
.seq body548_0 body548_6

def body548_8 : Prog (BitVec 64) :=
.seq body548_1 body548_2

def body548_9 : Prog (BitVec 64) :=
.seq body548_8 body548_3

def body548_10 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body548_9

def body548_11 : Prog (BitVec 64) :=
.seq body548_0 body548_10

def originalData548 : Decl (BitVec 64) :=
.function { name := "op_basefee", inline := false, exported := false, params := [], body := body548_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData548 : Decl (BitVec 64) :=
.function { name := "op_basefee", inline := false, exported := false, params := [], body := body548_11, returnShape := (Flapjack.Shape.one) }
def original548 := Pancake.PanLang.declToHOL originalData548
def simplified548 := Pancake.PanLang.declToHOL simplifiedData548
end InitECandidate.Proofs.FrontendStages.Declarations
