import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify795
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body811_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 10#64)

def body811_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body811_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 256#64)) body811_0 body811_1

def body811_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 375#64]

def body811_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "err") (Flapjack.Exp.const 0#64)) body811_0 body811_1

def body811_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body811_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 128#64)

def body811_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body811_8 : Prog (BitVec 64) :=
.seq body811_6 body811_7

def body811_9 : Prog (BitVec 64) :=
.seq body811_5 body811_8

def body811_10 : Prog (BitVec 64) :=
.seq body811_4 body811_9

def body811_11 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bls_g1_add_exec") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "out"]) body811_10

def body811_12 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) body811_11

def body811_13 : Prog (BitVec 64) :=
.seq body811_3 body811_12

def body811_14 : Prog (BitVec 64) :=
.seq body811_2 body811_13

def body811_15 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body811_14

def body811_16 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body811_15

def body811_17 : Prog (BitVec 64) :=
.seq body811_2 body811_3

def body811_18 : Prog (BitVec 64) :=
.seq body811_4 body811_5

def body811_19 : Prog (BitVec 64) :=
.seq body811_18 body811_6

def body811_20 : Prog (BitVec 64) :=
.seq body811_19 body811_7

def body811_21 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bls_g1_add_exec") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "out"]) body811_20

def body811_22 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) body811_21

def body811_23 : Prog (BitVec 64) :=
.seq body811_17 body811_22

def body811_24 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body811_23

def body811_25 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body811_24

def originalData811 : Decl (BitVec 64) :=
.function { name := "pre_bls_g1_add", inline := false, exported := false, params := [], body := body811_16, returnShape := (Flapjack.Shape.one) }
def simplifiedData811 : Decl (BitVec 64) :=
.function { name := "pre_bls_g1_add", inline := false, exported := false, params := [], body := body811_25, returnShape := (Flapjack.Shape.one) }
def original811 := Pancake.PanLang.declToHOL originalData811
def simplified811 := Pancake.PanLang.declToHOL simplifiedData811
end InitECandidate.Proofs.FrontendStages.Declarations
