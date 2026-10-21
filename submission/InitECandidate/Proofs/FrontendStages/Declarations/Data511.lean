import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify495
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body511_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body511_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3#64]

def body511_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nbytes") (Flapjack.Exp.const 0#64)) body511_0 body511_1

def body511_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 56#64]),
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 0#64]),
        Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "nbytes", Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def body511_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body511_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push" [Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body511_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "nbytes"]]

def body511_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body511_8 : Prog (BitVec 64) :=
.seq body511_6 body511_7

def body511_9 : Prog (BitVec 64) :=
.seq body511_5 body511_8

def body511_10 : Prog (BitVec 64) :=
.seq body511_4 body511_9

def body511_11 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.var Flapjack.VarKind.local "nbytes"]) body511_10

def body511_12 : Prog (BitVec 64) :=
.seq body511_3 body511_11

def body511_13 : Prog (BitVec 64) :=
.decCall ("tmp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body511_12

def body511_14 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body511_13

def body511_15 : Prog (BitVec 64) :=
.seq body511_2 body511_14

def body511_16 : Prog (BitVec 64) :=
.seq body511_4 body511_5

def body511_17 : Prog (BitVec 64) :=
.seq body511_16 body511_6

def body511_18 : Prog (BitVec 64) :=
.seq body511_17 body511_7

def body511_19 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.var Flapjack.VarKind.local "nbytes"]) body511_18

def body511_20 : Prog (BitVec 64) :=
.seq body511_3 body511_19

def body511_21 : Prog (BitVec 64) :=
.decCall ("tmp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body511_20

def body511_22 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body511_21

def body511_23 : Prog (BitVec 64) :=
.seq body511_2 body511_22

def originalData511 : Decl (BitVec 64) :=
.function { name := "op_push", inline := false, exported := false, params := [("nbytes", Flapjack.Shape.one)], body := body511_15, returnShape := (Flapjack.Shape.one) }
def simplifiedData511 : Decl (BitVec 64) :=
.function { name := "op_push", inline := false, exported := false, params := [("nbytes", Flapjack.Shape.one)], body := body511_23, returnShape := (Flapjack.Shape.one) }
def original511 := Pancake.PanLang.declToHOL originalData511
def simplified511 := Pancake.PanLang.declToHOL simplifiedData511
end InitECandidate.Proofs.FrontendStages.Declarations
