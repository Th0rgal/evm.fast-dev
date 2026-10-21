import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data532
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate516
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody532_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def globalBody532_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.load Flapjack.Shape.one
                  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
                Flapjack.Exp.const 112#64]),
          Flapjack.Exp.const 56#64])]

def globalBody532_2 : Prog (BitVec 64) :=
.seq globalBody532_0 globalBody532_1

def globalBody532_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody532_4 : Prog (BitVec 64) :=
.seq globalBody532_2 globalBody532_3

def globalBody532_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody532_6 : Prog (BitVec 64) :=
.seq globalBody532_4 globalBody532_5

def globalData532 : Decl (BitVec 64) :=
.function { name := "op_callvalue", inline := false, exported := false, params := [], body := globalBody532_6, returnShape := (Flapjack.Shape.one) }
def globalOutput532 := Pancake.PanLang.declToHOL globalData532
end InitECandidate.Proofs.FrontendStages.Declarations
