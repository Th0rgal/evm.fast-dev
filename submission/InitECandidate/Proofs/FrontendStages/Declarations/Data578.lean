import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify562
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body578_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (some (Flapjack.VarKind.local, "done"),
      some
        ("EvmErr", "err",
          Flapjack.Prog.call (some (none, none)) "frame_exception" [Flapjack.Exp.var Flapjack.VarKind.local "err"])))
  "frame_prologue" []

def body578_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 1#64)

def body578_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body578_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "done") (Flapjack.Exp.const 0#64)) body578_1 body578_2

def body578_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body578_5 : Prog (BitVec 64) :=
.seq body578_3 body578_4

def body578_6 : Prog (BitVec 64) :=
.seq body578_0 body578_5

def body578_7 : Prog (BitVec 64) :=
.dec ("done") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body578_6

def body578_8 : Prog (BitVec 64) :=
.dec ("err") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body578_7

def body578_9 : Prog (BitVec 64) :=
.seq body578_0 body578_3

def body578_10 : Prog (BitVec 64) :=
.seq body578_9 body578_4

def body578_11 : Prog (BitVec 64) :=
.dec ("done") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body578_10

def body578_12 : Prog (BitVec 64) :=
.dec ("err") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body578_11

def originalData578 : Decl (BitVec 64) :=
.function { name := "frame_start", inline := false, exported := false, params := [], body := body578_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData578 : Decl (BitVec 64) :=
.function { name := "frame_start", inline := false, exported := false, params := [], body := body578_12, returnShape := (Flapjack.Shape.one) }
def original578 := Pancake.PanLang.declToHOL originalData578
def simplified578 := Pancake.PanLang.declToHOL simplifiedData578
end InitECandidate.Proofs.FrontendStages.Declarations
