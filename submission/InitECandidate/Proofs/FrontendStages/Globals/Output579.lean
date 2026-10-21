import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data579
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate563
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody579_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_restore"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
          Flapjack.Exp.const 24#64])]

def globalBody579_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody579_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
        Flapjack.Exp.const 160#64]))
  (Flapjack.Exp.const 0#64)) globalBody579_0 globalBody579_1

def globalBody579_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody579_4 : Prog (BitVec 64) :=
.seq globalBody579_2 globalBody579_3

def globalData579 : Decl (BitVec 64) :=
.function { name := "frame_epilogue", inline := false, exported := false, params := [], body := globalBody579_4, returnShape := (Flapjack.Shape.one) }
def globalOutput579 := Pancake.PanLang.declToHOL globalData579
end InitECandidate.Proofs.FrontendStages.Declarations
