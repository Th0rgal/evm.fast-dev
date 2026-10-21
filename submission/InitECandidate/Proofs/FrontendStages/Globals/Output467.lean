import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data467
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate451
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody467_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 8#64)

def globalBody467_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody467_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.load Flapjack.Shape.one
                (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
              Flapjack.Exp.const 112#64]),
        Flapjack.Exp.const 144#64]))
  (Flapjack.Exp.const 0#64)) globalBody467_0 globalBody467_1

def globalBody467_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody467_4 : Prog (BitVec 64) :=
.seq globalBody467_2 globalBody467_3

def globalData467 : Decl (BitVec 64) :=
.function { name := "require_not_static", inline := false, exported := false, params := [], body := globalBody467_4, returnShape := (Flapjack.Shape.one) }
def globalOutput467 := Pancake.PanLang.declToHOL globalData467
end InitECandidate.Proofs.FrontendStages.Declarations
