import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data422
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate406
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody422_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody422_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody422_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "m"))
  (Flapjack.Exp.const 0#64)) globalBody422_0 globalBody422_1

def globalBody422_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bal_list_remove_idx"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m"),
          Flapjack.Exp.var Flapjack.VarKind.local "which"]),
    Flapjack.Exp.var Flapjack.VarKind.local "esz", Flapjack.Exp.var Flapjack.VarKind.local "idx"]

def globalBody422_4 : Prog (BitVec 64) :=
.seq globalBody422_2 globalBody422_3

def globalBody422_5 : Prog (BitVec 64) :=
.seq globalBody422_4 globalBody422_0

def globalBody422_6 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 216#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody422_5

def globalData422 : Decl (BitVec 64) :=
.function { name := "bal_remove_change", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("which", Flapjack.Shape.one), ("esz", Flapjack.Shape.one), ("idx", Flapjack.Shape.one)], body := globalBody422_6, returnShape := (Flapjack.Shape.one) }
def globalOutput422 := Pancake.PanLang.declToHOL globalData422
end InitECandidate.Proofs.FrontendStages.Declarations
