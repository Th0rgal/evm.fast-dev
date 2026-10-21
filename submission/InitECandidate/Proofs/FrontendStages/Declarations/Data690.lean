import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify674
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body690_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 6000#64]

def body690_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64]),
    Flapjack.Exp.const 0#64, Flapjack.Exp.const 96#64, Flapjack.Exp.var Flapjack.VarKind.local "buf"]

def body690_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body690_3 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def body690_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body690_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "err") (Flapjack.Exp.const 0#64)) body690_3 body690_4

def body690_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body690_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 64#64)

def body690_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body690_9 : Prog (BitVec 64) :=
.seq body690_7 body690_8

def body690_10 : Prog (BitVec 64) :=
.seq body690_6 body690_9

def body690_11 : Prog (BitVec 64) :=
.seq body690_5 body690_10

def body690_12 : Prog (BitVec 64) :=
.seq body690_2 body690_11

def body690_13 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bn254_g1_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.var Flapjack.VarKind.local "out"]) body690_12

def body690_14 : Prog (BitVec 64) :=
.seq body690_1 body690_13

def body690_15 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body690_14

def body690_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body690_15

def body690_17 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body690_16

def body690_18 : Prog (BitVec 64) :=
.seq body690_0 body690_17

def body690_19 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body690_18

def body690_20 : Prog (BitVec 64) :=
.seq body690_2 body690_5

def body690_21 : Prog (BitVec 64) :=
.seq body690_20 body690_6

def body690_22 : Prog (BitVec 64) :=
.seq body690_21 body690_7

def body690_23 : Prog (BitVec 64) :=
.seq body690_22 body690_8

def body690_24 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bn254_g1_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.var Flapjack.VarKind.local "out"]) body690_23

def body690_25 : Prog (BitVec 64) :=
.seq body690_1 body690_24

def body690_26 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body690_25

def body690_27 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body690_26

def body690_28 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body690_27

def body690_29 : Prog (BitVec 64) :=
.seq body690_0 body690_28

def body690_30 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body690_29

def originalData690 : Decl (BitVec 64) :=
.function { name := "pre_alt_bn128_mul", inline := false, exported := false, params := [], body := body690_19, returnShape := (Flapjack.Shape.one) }
def simplifiedData690 : Decl (BitVec 64) :=
.function { name := "pre_alt_bn128_mul", inline := false, exported := false, params := [], body := body690_30, returnShape := (Flapjack.Shape.one) }
def original690 := Pancake.PanLang.declToHOL originalData690
def simplified690 := Pancake.PanLang.declToHOL simplifiedData690
end InitECandidate.Proofs.FrontendStages.Declarations
