import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data553
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate537
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody553_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def globalBody553_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 80#64])]

def globalBody553_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody553_3 : Prog (BitVec 64) :=
.seq globalBody553_1 globalBody553_2

def globalBody553_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody553_5 : Prog (BitVec 64) :=
.seq globalBody553_3 globalBody553_4

def globalBody553_6 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) globalBody553_5

def globalBody553_7 : Prog (BitVec 64) :=
.seq globalBody553_0 globalBody553_6

def globalData553 : Decl (BitVec 64) :=
.function { name := "op_timestamp", inline := false, exported := false, params := [], body := globalBody553_7, returnShape := (Flapjack.Shape.one) }
def globalOutput553 := Pancake.PanLang.declToHOL globalData553
end InitECandidate.Proofs.FrontendStages.Declarations
