import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify322
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body338_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pubkey65", Flapjack.Exp.const 1#64],
    Flapjack.Exp.const 64#64, Flapjack.Exp.var Flapjack.VarKind.local "h"]

def body338_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out20",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 12#64],
    Flapjack.Exp.const 20#64]

def body338_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body338_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body338_4 : Prog (BitVec 64) :=
.seq body338_2 body338_3

def body338_5 : Prog (BitVec 64) :=
.seq body338_1 body338_4

def body338_6 : Prog (BitVec 64) :=
.seq body338_0 body338_5

def body338_7 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body338_6

def body338_8 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body338_7

def body338_9 : Prog (BitVec 64) :=
.seq body338_0 body338_1

def body338_10 : Prog (BitVec 64) :=
.seq body338_9 body338_2

def body338_11 : Prog (BitVec 64) :=
.seq body338_10 body338_3

def body338_12 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body338_11

def body338_13 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body338_12

def originalData338 : Decl (BitVec 64) :=
.function { name := "sender_address_from_public_key", inline := false, exported := false, params := [("pubkey65", Flapjack.Shape.one), ("out20", Flapjack.Shape.one)], body := body338_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData338 : Decl (BitVec 64) :=
.function { name := "sender_address_from_public_key", inline := false, exported := false, params := [("pubkey65", Flapjack.Shape.one), ("out20", Flapjack.Shape.one)], body := body338_13, returnShape := (Flapjack.Shape.one) }
def original338 := Pancake.PanLang.declToHOL originalData338
def simplified338 := Pancake.PanLang.declToHOL simplifiedData338
end InitECandidate.Proofs.FrontendStages.Declarations
