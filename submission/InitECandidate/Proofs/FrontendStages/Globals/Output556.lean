import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data556
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate540
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody556_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def globalBody556_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 0#64])]

def globalBody556_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody556_3 : Prog (BitVec 64) :=
.seq globalBody556_1 globalBody556_2

def globalBody556_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody556_5 : Prog (BitVec 64) :=
.seq globalBody556_3 globalBody556_4

def globalBody556_6 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) globalBody556_5

def globalBody556_7 : Prog (BitVec 64) :=
.seq globalBody556_0 globalBody556_6

def globalData556 : Decl (BitVec 64) :=
.function { name := "op_chainid", inline := false, exported := false, params := [], body := globalBody556_7, returnShape := (Flapjack.Shape.one) }
def globalOutput556 := Pancake.PanLang.declToHOL globalData556
end InitECandidate.Proofs.FrontendStages.Declarations
