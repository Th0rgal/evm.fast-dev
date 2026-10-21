import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify406
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body422_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body422_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body422_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "m"))
  (Flapjack.Exp.const 0#64)) body422_0 body422_1

def body422_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bal_list_remove_idx"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m"),
          Flapjack.Exp.var Flapjack.VarKind.local "which"]),
    Flapjack.Exp.var Flapjack.VarKind.local "esz", Flapjack.Exp.var Flapjack.VarKind.local "idx"]

def body422_4 : Prog (BitVec 64) :=
.seq body422_3 body422_0

def body422_5 : Prog (BitVec 64) :=
.seq body422_2 body422_4

def body422_6 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.global "bal_accounts", Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body422_5

def body422_7 : Prog (BitVec 64) :=
.seq body422_2 body422_3

def body422_8 : Prog (BitVec 64) :=
.seq body422_7 body422_0

def body422_9 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.global "bal_accounts", Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body422_8

def originalData422 : Decl (BitVec 64) :=
.function { name := "bal_remove_change", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("which", Flapjack.Shape.one), ("esz", Flapjack.Shape.one), ("idx", Flapjack.Shape.one)], body := body422_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData422 : Decl (BitVec 64) :=
.function { name := "bal_remove_change", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("which", Flapjack.Shape.one), ("esz", Flapjack.Shape.one), ("idx", Flapjack.Shape.one)], body := body422_9, returnShape := (Flapjack.Shape.one) }
def original422 := Pancake.PanLang.declToHOL originalData422
def simplified422 := Pancake.PanLang.declToHOL simplifiedData422
end InitECandidate.Proofs.FrontendStages.Declarations
