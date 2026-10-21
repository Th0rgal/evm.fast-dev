import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify323
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body339_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "pk") (Flapjack.Exp.const 4#64)

def body339_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "recover_transaction_public_key"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "cid"),
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pk", Flapjack.Exp.const 1#64]]

def body339_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sender_address_from_public_key"
  [Flapjack.Exp.var Flapjack.VarKind.local "pk", Flapjack.Exp.var Flapjack.VarKind.local "out20"]

def body339_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body339_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body339_5 : Prog (BitVec 64) :=
.seq body339_3 body339_4

def body339_6 : Prog (BitVec 64) :=
.seq body339_2 body339_5

def body339_7 : Prog (BitVec 64) :=
.seq body339_1 body339_6

def body339_8 : Prog (BitVec 64) :=
.seq body339_0 body339_7

def body339_9 : Prog (BitVec 64) :=
.decCall ("pk") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 72#64]) body339_8

def body339_10 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body339_9

def body339_11 : Prog (BitVec 64) :=
.decCall ("cid") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_chain_id") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body339_10

def body339_12 : Prog (BitVec 64) :=
.seq body339_0 body339_1

def body339_13 : Prog (BitVec 64) :=
.seq body339_12 body339_2

def body339_14 : Prog (BitVec 64) :=
.seq body339_13 body339_3

def body339_15 : Prog (BitVec 64) :=
.seq body339_14 body339_4

def body339_16 : Prog (BitVec 64) :=
.decCall ("pk") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 72#64]) body339_15

def body339_17 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body339_16

def body339_18 : Prog (BitVec 64) :=
.decCall ("cid") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_chain_id") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body339_17

def originalData339 : Decl (BitVec 64) :=
.function { name := "recover_sender", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("out20", Flapjack.Shape.one)], body := body339_11, returnShape := (Flapjack.Shape.one) }
def simplifiedData339 : Decl (BitVec 64) :=
.function { name := "recover_sender", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("out20", Flapjack.Shape.one)], body := body339_18, returnShape := (Flapjack.Shape.one) }
def original339 := Pancake.PanLang.declToHOL originalData339
def simplified339 := Pancake.PanLang.declToHOL simplifiedData339
end InitECandidate.Proofs.FrontendStages.Declarations
