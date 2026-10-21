import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data555
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate539
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody555_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def globalBody555_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 8#64])]

def globalBody555_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody555_3 : Prog (BitVec 64) :=
.seq globalBody555_1 globalBody555_2

def globalBody555_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody555_5 : Prog (BitVec 64) :=
.seq globalBody555_3 globalBody555_4

def globalBody555_6 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) globalBody555_5

def globalBody555_7 : Prog (BitVec 64) :=
.seq globalBody555_0 globalBody555_6

def globalData555 : Decl (BitVec 64) :=
.function { name := "op_gaslimit", inline := false, exported := false, params := [], body := globalBody555_7, returnShape := (Flapjack.Shape.one) }
def globalOutput555 := Pancake.PanLang.declToHOL globalData555
end InitECandidate.Proofs.FrontendStages.Declarations
