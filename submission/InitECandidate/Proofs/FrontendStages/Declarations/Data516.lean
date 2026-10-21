import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify500
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body516_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.const 145#64],
      Flapjack.Exp.const 255#64])

def body516_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body516_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 90#64) (Flapjack.Exp.var Flapjack.VarKind.local "x"),
      Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "x") (Flapjack.Exp.const 128#64)])) body516_0 body516_1

def body516_3 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 10#64)

def body516_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body516_5 : Prog (BitVec 64) :=
.seq body516_3 body516_4

def body516_6 : Prog (BitVec 64) :=
.seq body516_2 body516_5

def body516_7 : Prog (BitVec 64) :=
.seq body516_2 body516_3

def body516_8 : Prog (BitVec 64) :=
.seq body516_7 body516_4

def originalData516 : Decl (BitVec 64) :=
.function { name := "decode_single", inline := false, exported := false, params := [("x", Flapjack.Shape.one)], body := body516_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData516 : Decl (BitVec 64) :=
.function { name := "decode_single", inline := false, exported := false, params := [("x", Flapjack.Shape.one)], body := body516_8, returnShape := (Flapjack.Shape.one) }
def original516 := Pancake.PanLang.declToHOL originalData516
def simplified516 := Pancake.PanLang.declToHOL simplifiedData516
end InitECandidate.Proofs.FrontendStages.Declarations
