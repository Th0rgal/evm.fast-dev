import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify576
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body592_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "evm_empty")

def body592_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.const 0#64)

def body592_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 216#64])
  (Flapjack.Exp.const 0#64)

def body592_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body592_4 : Prog (BitVec 64) :=
.seq body592_2 body592_3

def body592_5 : Prog (BitVec 64) :=
.seq body592_1 body592_4

def body592_6 : Prog (BitVec 64) :=
.seq body592_0 body592_5

def body592_7 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body592_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) body592_6 body592_7

def body592_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "dst"), none)) "alloc"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]

def body592_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "dst")

def body592_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 216#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n")

def body592_12 : Prog (BitVec 64) :=
.seq body592_10 body592_11

def body592_13 : Prog (BitVec 64) :=
.seq body592_9 body592_12

def body592_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "cap")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body592_13 body592_7

def body592_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body592_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n")

def body592_17 : Prog (BitVec 64) :=
.seq body592_16 body592_3

def body592_18 : Prog (BitVec 64) :=
.seq body592_15 body592_17

def body592_19 : Prog (BitVec 64) :=
.seq body592_14 body592_18

def body592_20 : Prog (BitVec 64) :=
.dec ("dst") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 144#64])) body592_19

def body592_21 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 216#64])) body592_20

def body592_22 : Prog (BitVec 64) :=
.seq body592_8 body592_21

def body592_23 : Prog (BitVec 64) :=
.seq body592_0 body592_1

def body592_24 : Prog (BitVec 64) :=
.seq body592_23 body592_2

def body592_25 : Prog (BitVec 64) :=
.seq body592_24 body592_3

def body592_26 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) body592_25 body592_7

def body592_27 : Prog (BitVec 64) :=
.seq body592_9 body592_10

def body592_28 : Prog (BitVec 64) :=
.seq body592_27 body592_11

def body592_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "cap")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body592_28 body592_7

def body592_30 : Prog (BitVec 64) :=
.seq body592_29 body592_15

def body592_31 : Prog (BitVec 64) :=
.seq body592_30 body592_16

def body592_32 : Prog (BitVec 64) :=
.seq body592_31 body592_3

def body592_33 : Prog (BitVec 64) :=
.dec ("dst") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 144#64])) body592_32

def body592_34 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 216#64])) body592_33

def body592_35 : Prog (BitVec 64) :=
.seq body592_26 body592_34

def originalData592 : Decl (BitVec 64) :=
.function { name := "set_retdata", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body592_22, returnShape := (Flapjack.Shape.one) }
def simplifiedData592 : Decl (BitVec 64) :=
.function { name := "set_retdata", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body592_35, returnShape := (Flapjack.Shape.one) }
def original592 := Pancake.PanLang.declToHOL originalData592
def simplified592 := Pancake.PanLang.declToHOL simplifiedData592
end InitECandidate.Proofs.FrontendStages.Declarations
