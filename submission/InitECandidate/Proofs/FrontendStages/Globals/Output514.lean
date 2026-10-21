import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data514
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate498
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody514_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3#64]

def globalBody514_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 2#64)

def globalBody514_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody514_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "item")
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
        Flapjack.Exp.const 16#64]))) globalBody514_1 globalBody514_2

def globalBody514_4 : Prog (BitVec 64) :=
.seq globalBody514_0 globalBody514_3

def globalBody514_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_swap_positions"
  [Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "item"]

def globalBody514_6 : Prog (BitVec 64) :=
.seq globalBody514_4 globalBody514_5

def globalBody514_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody514_8 : Prog (BitVec 64) :=
.seq globalBody514_6 globalBody514_7

def globalBody514_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody514_10 : Prog (BitVec 64) :=
.seq globalBody514_8 globalBody514_9

def globalData514 : Decl (BitVec 64) :=
.function { name := "op_swap", inline := false, exported := false, params := [("item", Flapjack.Shape.one)], body := globalBody514_10, returnShape := (Flapjack.Shape.one) }
def globalOutput514 := Pancake.PanLang.declToHOL globalData514
end InitECandidate.Proofs.FrontendStages.Declarations
