import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify300
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body316_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body316_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body316_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) body316_0 body316_1

def body316_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
  (Flapjack.Exp.const 128#64)) body316_0 body316_1

def body316_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 1#64)) body316_3 body316_1

def body316_5 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "n"])

def body316_6 : Prog (BitVec 64) :=
.seq body316_4 body316_5

def body316_7 : Prog (BitVec 64) :=
.seq body316_2 body316_6

def body316_8 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("u256_byte_length") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) body316_7

def body316_9 : Prog (BitVec 64) :=
.seq body316_2 body316_4

def body316_10 : Prog (BitVec 64) :=
.seq body316_9 body316_5

def body316_11 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("u256_byte_length") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) body316_10

def originalData316 : Decl (BitVec 64) :=
.function { name := "tx_u256_encoded_len", inline := false, exported := false, params := [("v", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body316_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData316 : Decl (BitVec 64) :=
.function { name := "tx_u256_encoded_len", inline := false, exported := false, params := [("v", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body316_11, returnShape := (Flapjack.Shape.one) }
def original316 := Pancake.PanLang.declToHOL originalData316
def simplified316 := Pancake.PanLang.declToHOL simplifiedData316
end InitECandidate.Proofs.FrontendStages.Declarations
