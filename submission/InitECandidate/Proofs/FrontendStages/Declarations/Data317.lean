import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify301
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body317_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "dst") (Flapjack.Exp.const 128#64)

def body317_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body317_2 : Prog (BitVec 64) :=
.seq body317_0 body317_1

def body317_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body317_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "to") (Flapjack.Exp.const 0#64)) body317_2 body317_3

def body317_5 : Prog (BitVec 64) :=
Flapjack.Prog.call none "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "to",
    Flapjack.Exp.const 20#64]

def body317_6 : Prog (BitVec 64) :=
.seq body317_4 body317_5

def originalData317 : Decl (BitVec 64) :=
.function { name := "tx_put_to", inline := false, exported := false, params := [("dst", Flapjack.Shape.one), ("to", Flapjack.Shape.one)], body := body317_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData317 : Decl (BitVec 64) :=
.function { name := "tx_put_to", inline := false, exported := false, params := [("dst", Flapjack.Shape.one), ("to", Flapjack.Shape.one)], body := body317_6, returnShape := (Flapjack.Shape.one) }
def original317 := Pancake.PanLang.declToHOL originalData317
def simplified317 := Pancake.PanLang.declToHOL simplifiedData317
end InitECandidate.Proofs.FrontendStages.Declarations
