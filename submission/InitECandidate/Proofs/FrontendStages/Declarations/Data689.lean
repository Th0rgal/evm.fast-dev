import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify673
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body689_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 150#64]

def body689_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64]),
    Flapjack.Exp.const 0#64, Flapjack.Exp.const 128#64, Flapjack.Exp.var Flapjack.VarKind.local "buf"]

def body689_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body689_3 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def body689_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body689_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "err") (Flapjack.Exp.const 0#64)) body689_3 body689_4

def body689_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body689_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 64#64)

def body689_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body689_9 : Prog (BitVec 64) :=
.seq body689_7 body689_8

def body689_10 : Prog (BitVec 64) :=
.seq body689_6 body689_9

def body689_11 : Prog (BitVec 64) :=
.seq body689_5 body689_10

def body689_12 : Prog (BitVec 64) :=
.seq body689_2 body689_11

def body689_13 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bn254_g1_add") ([Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.var Flapjack.VarKind.local "out"]) body689_12

def body689_14 : Prog (BitVec 64) :=
.seq body689_1 body689_13

def body689_15 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) body689_14

def body689_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body689_15

def body689_17 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body689_16

def body689_18 : Prog (BitVec 64) :=
.seq body689_0 body689_17

def body689_19 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body689_18

def body689_20 : Prog (BitVec 64) :=
.seq body689_2 body689_5

def body689_21 : Prog (BitVec 64) :=
.seq body689_20 body689_6

def body689_22 : Prog (BitVec 64) :=
.seq body689_21 body689_7

def body689_23 : Prog (BitVec 64) :=
.seq body689_22 body689_8

def body689_24 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bn254_g1_add") ([Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.var Flapjack.VarKind.local "out"]) body689_23

def body689_25 : Prog (BitVec 64) :=
.seq body689_1 body689_24

def body689_26 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) body689_25

def body689_27 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body689_26

def body689_28 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body689_27

def body689_29 : Prog (BitVec 64) :=
.seq body689_0 body689_28

def body689_30 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body689_29

def originalData689 : Decl (BitVec 64) :=
.function { name := "pre_alt_bn128_add", inline := false, exported := false, params := [], body := body689_19, returnShape := (Flapjack.Shape.one) }
def simplifiedData689 : Decl (BitVec 64) :=
.function { name := "pre_alt_bn128_add", inline := false, exported := false, params := [], body := body689_30, returnShape := (Flapjack.Shape.one) }
def original689 := Pancake.PanLang.declToHOL originalData689
def simplified689 := Pancake.PanLang.declToHOL simplifiedData689
end InitECandidate.Proofs.FrontendStages.Declarations
