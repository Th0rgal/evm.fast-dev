import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify376
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body392_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "StateErr" (Flapjack.Exp.const 4#64)

def body392_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body392_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt") (Flapjack.Exp.const 0#64)) body392_0 body392_1

def body392_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "s"), none)) "acct_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "s"]

def body392_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nb")

def body392_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "modify_state_commit"
  [Flapjack.Exp.var Flapjack.VarKind.local "sender", Flapjack.Exp.var Flapjack.VarKind.local "s"]

def body392_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "acct_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def body392_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "nb"), none)) "u256_add"
  [Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "amount"]

def body392_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nb")

def body392_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "modify_state_commit"
  [Flapjack.Exp.var Flapjack.VarKind.local "recipient", Flapjack.Exp.var Flapjack.VarKind.local "r"]

def body392_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body392_11 : Prog (BitVec 64) :=
.seq body392_9 body392_10

def body392_12 : Prog (BitVec 64) :=
.seq body392_8 body392_11

def body392_13 : Prog (BitVec 64) :=
.seq body392_7 body392_12

def body392_14 : Prog (BitVec 64) :=
.seq body392_6 body392_13

def body392_15 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "recipient"]) body392_14

def body392_16 : Prog (BitVec 64) :=
.seq body392_5 body392_15

def body392_17 : Prog (BitVec 64) :=
.seq body392_4 body392_16

def body392_18 : Prog (BitVec 64) :=
.decCall ("nb") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "amount"]) body392_17

def body392_19 : Prog (BitVec 64) :=
.seq body392_3 body392_18

def body392_20 : Prog (BitVec 64) :=
.seq body392_2 body392_19

def body392_21 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "amount"]) body392_20

def body392_22 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body392_21

def body392_23 : Prog (BitVec 64) :=
.seq body392_2 body392_3

def body392_24 : Prog (BitVec 64) :=
.seq body392_4 body392_5

def body392_25 : Prog (BitVec 64) :=
.seq body392_6 body392_7

def body392_26 : Prog (BitVec 64) :=
.seq body392_25 body392_8

def body392_27 : Prog (BitVec 64) :=
.seq body392_26 body392_9

def body392_28 : Prog (BitVec 64) :=
.seq body392_27 body392_10

def body392_29 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "recipient"]) body392_28

def body392_30 : Prog (BitVec 64) :=
.seq body392_24 body392_29

def body392_31 : Prog (BitVec 64) :=
.decCall ("nb") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "amount"]) body392_30

def body392_32 : Prog (BitVec 64) :=
.seq body392_23 body392_31

def body392_33 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "amount"]) body392_32

def body392_34 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body392_33

def originalData392 : Decl (BitVec 64) :=
.function { name := "move_ether", inline := false, exported := false, params := [("sender", Flapjack.Shape.one), ("recipient", Flapjack.Shape.one),
  ("amount", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body392_22, returnShape := (Flapjack.Shape.one) }
def simplifiedData392 : Decl (BitVec 64) :=
.function { name := "move_ether", inline := false, exported := false, params := [("sender", Flapjack.Shape.one), ("recipient", Flapjack.Shape.one),
  ("amount", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body392_34, returnShape := (Flapjack.Shape.one) }
def original392 := Pancake.PanLang.declToHOL originalData392
def simplified392 := Pancake.PanLang.declToHOL simplifiedData392
end InitECandidate.Proofs.FrontendStages.Declarations
