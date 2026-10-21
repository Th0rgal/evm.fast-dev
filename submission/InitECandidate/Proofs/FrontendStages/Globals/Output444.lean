import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data444
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate423
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody444_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def globalBody444_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody444_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
        Flapjack.Exp.const 64#64]))
  (Flapjack.Exp.var Flapjack.VarKind.local "amount")) globalBody444_0 globalBody444_1

def globalBody444_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody444_4 : Prog (BitVec 64) :=
.seq globalBody444_2 globalBody444_3

def globalData444 : Decl (BitVec 64) :=
.function { name := "check_gas", inline := false, exported := false, params := [("amount", Flapjack.Shape.one)], body := globalBody444_4, returnShape := (Flapjack.Shape.one) }
def globalOutput444 := Pancake.PanLang.declToHOL globalData444
end InitECandidate.Proofs.FrontendStages.Declarations
