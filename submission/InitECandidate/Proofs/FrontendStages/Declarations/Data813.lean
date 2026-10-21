import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify797
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body813_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 10#64)

def body813_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body813_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 512#64)) body813_0 body813_1

def body813_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 600#64]

def body813_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "err") (Flapjack.Exp.const 0#64)) body813_0 body813_1

def body813_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body813_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 256#64)

def body813_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body813_8 : Prog (BitVec 64) :=
.seq body813_6 body813_7

def body813_9 : Prog (BitVec 64) :=
.seq body813_5 body813_8

def body813_10 : Prog (BitVec 64) :=
.seq body813_4 body813_9

def body813_11 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bls_g2_add_exec") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "out"]) body813_10

def body813_12 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 256#64]) body813_11

def body813_13 : Prog (BitVec 64) :=
.seq body813_3 body813_12

def body813_14 : Prog (BitVec 64) :=
.seq body813_2 body813_13

def body813_15 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body813_14

def body813_16 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body813_15

def body813_17 : Prog (BitVec 64) :=
.seq body813_2 body813_3

def body813_18 : Prog (BitVec 64) :=
.seq body813_4 body813_5

def body813_19 : Prog (BitVec 64) :=
.seq body813_18 body813_6

def body813_20 : Prog (BitVec 64) :=
.seq body813_19 body813_7

def body813_21 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bls_g2_add_exec") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "out"]) body813_20

def body813_22 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 256#64]) body813_21

def body813_23 : Prog (BitVec 64) :=
.seq body813_17 body813_22

def body813_24 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body813_23

def body813_25 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body813_24

def originalData813 : Decl (BitVec 64) :=
.function { name := "pre_bls_g2_add", inline := false, exported := false, params := [], body := body813_16, returnShape := (Flapjack.Shape.one) }
def simplifiedData813 : Decl (BitVec 64) :=
.function { name := "pre_bls_g2_add", inline := false, exported := false, params := [], body := body813_25, returnShape := (Flapjack.Shape.one) }
def original813 := Pancake.PanLang.declToHOL originalData813
def simplified813 := Pancake.PanLang.declToHOL simplifiedData813
end InitECandidate.Proofs.FrontendStages.Declarations
