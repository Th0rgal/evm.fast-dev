import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data392
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate376
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody392_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "StateErr" (Flapjack.Exp.const 4#64)

def globalBody392_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody392_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt") (Flapjack.Exp.const 0#64)) globalBody392_0 globalBody392_1

def globalBody392_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "s"), none)) "acct_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "s"]

def globalBody392_4 : Prog (BitVec 64) :=
.seq globalBody392_2 globalBody392_3

def globalBody392_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nb")

def globalBody392_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "modify_state_commit"
  [Flapjack.Exp.var Flapjack.VarKind.local "sender", Flapjack.Exp.var Flapjack.VarKind.local "s"]

def globalBody392_7 : Prog (BitVec 64) :=
.seq globalBody392_5 globalBody392_6

def globalBody392_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "acct_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def globalBody392_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "nb"), none)) "u256_add"
  [Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "amount"]

def globalBody392_10 : Prog (BitVec 64) :=
.seq globalBody392_8 globalBody392_9

def globalBody392_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nb")

def globalBody392_12 : Prog (BitVec 64) :=
.seq globalBody392_10 globalBody392_11

def globalBody392_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "modify_state_commit"
  [Flapjack.Exp.var Flapjack.VarKind.local "recipient", Flapjack.Exp.var Flapjack.VarKind.local "r"]

def globalBody392_14 : Prog (BitVec 64) :=
.seq globalBody392_12 globalBody392_13

def globalBody392_15 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody392_16 : Prog (BitVec 64) :=
.seq globalBody392_14 globalBody392_15

def globalBody392_17 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "recipient"]) globalBody392_16

def globalBody392_18 : Prog (BitVec 64) :=
.seq globalBody392_7 globalBody392_17

def globalBody392_19 : Prog (BitVec 64) :=
.decCall ("nb") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "amount"]) globalBody392_18

def globalBody392_20 : Prog (BitVec 64) :=
.seq globalBody392_4 globalBody392_19

def globalBody392_21 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "amount"]) globalBody392_20

def globalBody392_22 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "sender"]) globalBody392_21

def globalData392 : Decl (BitVec 64) :=
.function { name := "move_ether", inline := false, exported := false, params := [("sender", Flapjack.Shape.one), ("recipient", Flapjack.Shape.one),
  ("amount", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := globalBody392_22, returnShape := (Flapjack.Shape.one) }
def globalOutput392 := Pancake.PanLang.declToHOL globalData392
end InitECandidate.Proofs.FrontendStages.Declarations
