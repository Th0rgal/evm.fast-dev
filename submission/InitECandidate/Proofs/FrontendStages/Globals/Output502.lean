import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data502
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate486
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody502_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def globalBody502_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
          Flapjack.Exp.const 0#64])]

def globalBody502_2 : Prog (BitVec 64) :=
.seq globalBody502_0 globalBody502_1

def globalBody502_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody502_4 : Prog (BitVec 64) :=
.seq globalBody502_2 globalBody502_3

def globalBody502_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody502_6 : Prog (BitVec 64) :=
.seq globalBody502_4 globalBody502_5

def globalData502 : Decl (BitVec 64) :=
.function { name := "op_pc", inline := false, exported := false, params := [], body := globalBody502_6, returnShape := (Flapjack.Shape.one) }
def globalOutput502 := Pancake.PanLang.declToHOL globalData502
end InitECandidate.Proofs.FrontendStages.Declarations
