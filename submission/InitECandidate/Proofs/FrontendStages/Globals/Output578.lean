import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data578
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate558
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody578_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (some (Flapjack.VarKind.local, "done"),
      some
        ("EvmErr", "err",
          Flapjack.Prog.call (some (none, none)) "frame_exception" [Flapjack.Exp.var Flapjack.VarKind.local "err"])))
  "frame_prologue" []

def globalBody578_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
      Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 1#64)

def globalBody578_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody578_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "done") (Flapjack.Exp.const 0#64)) globalBody578_1 globalBody578_2

def globalBody578_4 : Prog (BitVec 64) :=
.seq globalBody578_0 globalBody578_3

def globalBody578_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody578_6 : Prog (BitVec 64) :=
.seq globalBody578_4 globalBody578_5

def globalBody578_7 : Prog (BitVec 64) :=
.dec ("done") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody578_6

def globalBody578_8 : Prog (BitVec 64) :=
.dec ("err") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody578_7

def globalData578 : Decl (BitVec 64) :=
.function { name := "frame_start", inline := false, exported := false, params := [], body := globalBody578_8, returnShape := (Flapjack.Shape.one) }
def globalOutput578 := Pancake.PanLang.declToHOL globalData578
end InitECandidate.Proofs.FrontendStages.Declarations
