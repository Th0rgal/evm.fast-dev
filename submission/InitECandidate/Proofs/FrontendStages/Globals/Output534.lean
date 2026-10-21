import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data534
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate518
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody534_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def globalBody534_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.load Flapjack.Shape.one
                  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
                Flapjack.Exp.const 112#64]),
          Flapjack.Exp.const 96#64])]

def globalBody534_2 : Prog (BitVec 64) :=
.seq globalBody534_0 globalBody534_1

def globalBody534_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody534_4 : Prog (BitVec 64) :=
.seq globalBody534_2 globalBody534_3

def globalBody534_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody534_6 : Prog (BitVec 64) :=
.seq globalBody534_4 globalBody534_5

def globalData534 : Decl (BitVec 64) :=
.function { name := "op_calldatasize", inline := false, exported := false, params := [], body := globalBody534_6, returnShape := (Flapjack.Shape.one) }
def globalOutput534 := Pancake.PanLang.declToHOL globalData534
end InitECandidate.Proofs.FrontendStages.Declarations
