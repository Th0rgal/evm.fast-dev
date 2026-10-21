import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data809
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate792
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody809_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 519#64)

def globalBody809_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody809_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 128#64) (Flapjack.Exp.var Flapjack.VarKind.local "k")) globalBody809_0 globalBody809_1

def globalBody809_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 400#64]),
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64],
            Flapjack.Exp.const 8#64]]))

def globalBody809_4 : Prog (BitVec 64) :=
.seq globalBody809_2 globalBody809_3

def globalData809 : Decl (BitVec 64) :=
.function { name := "bls_g1_msm_discount", inline := false, exported := false, params := [("k", Flapjack.Shape.one)], body := globalBody809_4, returnShape := (Flapjack.Shape.one) }
def globalOutput809 := Pancake.PanLang.declToHOL globalData809
end InitECandidate.Proofs.FrontendStages.Declarations
