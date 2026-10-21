import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify435
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body451_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 3#64)

def body451_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body451_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "cap") (Flapjack.Exp.const 1024#64)) body451_0 body451_1

def body451_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "ncap" (Flapjack.Exp.const 1024#64)

def body451_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1024#64) (Flapjack.Exp.var Flapjack.VarKind.local "ncap")) body451_3 body451_1

def body451_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "ns",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 32#64]]

def body451_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ns")

def body451_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 232#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ncap")

def body451_8 : Prog (BitVec 64) :=
.seq body451_6 body451_7

def body451_9 : Prog (BitVec 64) :=
.seq body451_5 body451_8

def body451_10 : Prog (BitVec 64) :=
.decCall ("ns") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "ncap", Flapjack.Exp.const 32#64]]) body451_9

def body451_11 : Prog (BitVec 64) :=
.seq body451_4 body451_10

def body451_12 : Prog (BitVec 64) :=
.dec ("ncap") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "cap", Flapjack.Exp.const 2#64]) body451_11

def body451_13 : Prog (BitVec 64) :=
.seq body451_2 body451_12

def body451_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "sp")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) body451_13 body451_1

def body451_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "sp") (Flapjack.Exp.const 1024#64)) body451_0 body451_1

def body451_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 8#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body451_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 1#64])

def body451_18 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body451_19 : Prog (BitVec 64) :=
.seq body451_17 body451_18

def body451_20 : Prog (BitVec 64) :=
.seq body451_16 body451_19

def body451_21 : Prog (BitVec 64) :=
.seq body451_15 body451_20

def body451_22 : Prog (BitVec 64) :=
.seq body451_14 body451_21

def body451_23 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 232#64])) body451_22

def body451_24 : Prog (BitVec 64) :=
.dec ("sp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])) body451_23

def body451_25 : Prog (BitVec 64) :=
.seq body451_5 body451_6

def body451_26 : Prog (BitVec 64) :=
.seq body451_25 body451_7

def body451_27 : Prog (BitVec 64) :=
.decCall ("ns") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "ncap", Flapjack.Exp.const 32#64]]) body451_26

def body451_28 : Prog (BitVec 64) :=
.seq body451_4 body451_27

def body451_29 : Prog (BitVec 64) :=
.dec ("ncap") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "cap", Flapjack.Exp.const 2#64]) body451_28

def body451_30 : Prog (BitVec 64) :=
.seq body451_2 body451_29

def body451_31 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "sp")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) body451_30 body451_1

def body451_32 : Prog (BitVec 64) :=
.seq body451_31 body451_15

def body451_33 : Prog (BitVec 64) :=
.seq body451_32 body451_16

def body451_34 : Prog (BitVec 64) :=
.seq body451_33 body451_17

def body451_35 : Prog (BitVec 64) :=
.seq body451_34 body451_18

def body451_36 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 232#64])) body451_35

def body451_37 : Prog (BitVec 64) :=
.dec ("sp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])) body451_36

def originalData451 : Decl (BitVec 64) :=
.function { name := "stack_push", inline := false, exported := false, params := [("v", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body451_24, returnShape := (Flapjack.Shape.one) }
def simplifiedData451 : Decl (BitVec 64) :=
.function { name := "stack_push", inline := false, exported := false, params := [("v", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body451_37, returnShape := (Flapjack.Shape.one) }
def original451 := Pancake.PanLang.declToHOL originalData451
def simplified451 := Pancake.PanLang.declToHOL simplifiedData451
end InitECandidate.Proofs.FrontendStages.Declarations
