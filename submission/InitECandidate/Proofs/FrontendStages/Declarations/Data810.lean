import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify794
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body810_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 524#64)

def body810_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body810_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 128#64) (Flapjack.Exp.var Flapjack.VarKind.local "k")) body810_0 body810_1

def body810_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.op Flapjack.BinOp.sub
              [Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.const 128#64, Flapjack.Exp.var Flapjack.VarKind.local "k"],
                Flapjack.Exp.const 1#64],
            Flapjack.Exp.const 8#64]]))

def body810_4 : Prog (BitVec 64) :=
.seq body810_2 body810_3

def originalData810 : Decl (BitVec 64) :=
.function { name := "bls_g2_msm_discount", inline := false, exported := false, params := [("k", Flapjack.Shape.one)], body := body810_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData810 : Decl (BitVec 64) :=
.function { name := "bls_g2_msm_discount", inline := false, exported := false, params := [("k", Flapjack.Shape.one)], body := body810_4, returnShape := (Flapjack.Shape.one) }
def original810 := Pancake.PanLang.declToHOL originalData810
def simplified810 := Pancake.PanLang.declToHOL simplifiedData810
end InitECandidate.Proofs.FrontendStages.Declarations
