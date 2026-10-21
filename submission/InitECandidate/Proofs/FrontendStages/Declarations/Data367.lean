import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify351
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body367_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body367_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body367_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body367_0 body367_1

def body367_3 : Prog (BitVec 64) :=
Flapjack.Prog.raise "StateErr" (Flapjack.Exp.const 2#64)

def body367_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r"))
  (Flapjack.Exp.const 0#64)) body367_3 body367_1

def body367_5 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "r")])

def body367_6 : Prog (BitVec 64) :=
.seq body367_4 body367_5

def body367_7 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("nodedb_lookup") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 16#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "code_hash"]) body367_6

def body367_8 : Prog (BitVec 64) :=
.seq body367_2 body367_7

def body367_9 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "code_hash", Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash",
  Flapjack.Exp.const 32#64]) body367_8

def originalData367 : Decl (BitVec 64) :=
.function { name := "ws_get_code", inline := false, exported := false, params := [("code_hash", Flapjack.Shape.one)], body := body367_9, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData367 : Decl (BitVec 64) :=
.function { name := "ws_get_code", inline := false, exported := false, params := [("code_hash", Flapjack.Shape.one)], body := body367_9, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original367 := Pancake.PanLang.declToHOL originalData367
def simplified367 := Pancake.PanLang.declToHOL simplifiedData367
end InitECandidate.Proofs.FrontendStages.Declarations
