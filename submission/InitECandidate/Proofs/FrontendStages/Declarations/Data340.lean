import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify324
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body340_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "pk") (Flapjack.Exp.const 4#64)

def body340_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "recover_transaction_public_key"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "chain_id",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pk", Flapjack.Exp.const 1#64]]

def body340_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sender_address_from_public_key"
  [Flapjack.Exp.var Flapjack.VarKind.local "pk", Flapjack.Exp.var Flapjack.VarKind.local "out20"]

def body340_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body340_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body340_5 : Prog (BitVec 64) :=
.seq body340_3 body340_4

def body340_6 : Prog (BitVec 64) :=
.seq body340_2 body340_5

def body340_7 : Prog (BitVec 64) :=
.seq body340_1 body340_6

def body340_8 : Prog (BitVec 64) :=
.seq body340_0 body340_7

def body340_9 : Prog (BitVec 64) :=
.decCall ("pk") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 72#64]) body340_8

def body340_10 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body340_9

def body340_11 : Prog (BitVec 64) :=
.seq body340_0 body340_1

def body340_12 : Prog (BitVec 64) :=
.seq body340_11 body340_2

def body340_13 : Prog (BitVec 64) :=
.seq body340_12 body340_3

def body340_14 : Prog (BitVec 64) :=
.seq body340_13 body340_4

def body340_15 : Prog (BitVec 64) :=
.decCall ("pk") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 72#64]) body340_14

def body340_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body340_15

def originalData340 : Decl (BitVec 64) :=
.function { name := "recover_sender_with_chain_id", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one), ("out20", Flapjack.Shape.one)], body := body340_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData340 : Decl (BitVec 64) :=
.function { name := "recover_sender_with_chain_id", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one), ("out20", Flapjack.Shape.one)], body := body340_16, returnShape := (Flapjack.Shape.one) }
def original340 := Pancake.PanLang.declToHOL originalData340
def simplified340 := Pancake.PanLang.declToHOL simplifiedData340
end InitECandidate.Proofs.FrontendStages.Declarations
