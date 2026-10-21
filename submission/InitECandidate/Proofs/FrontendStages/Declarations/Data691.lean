import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify675
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body691_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.const 34000#64, Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr")],
        Flapjack.Exp.const 45000#64]]

def body691_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def body691_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body691_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "qr"))
  (Flapjack.Exp.const 0#64)) body691_1 body691_2

def body691_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "res") (Flapjack.Exp.const 2#64)) body691_1 body691_2

def body691_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64]

def body691_6 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 31#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "res")

def body691_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body691_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 32#64)

def body691_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body691_10 : Prog (BitVec 64) :=
.seq body691_8 body691_9

def body691_11 : Prog (BitVec 64) :=
.seq body691_7 body691_10

def body691_12 : Prog (BitVec 64) :=
.seq body691_6 body691_11

def body691_13 : Prog (BitVec 64) :=
.seq body691_5 body691_12

def body691_14 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body691_13

def body691_15 : Prog (BitVec 64) :=
.seq body691_4 body691_14

def body691_16 : Prog (BitVec 64) :=
.decCall ("res") (Flapjack.Shape.one) ("bn254_pairing_check") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr")]) body691_15

def body691_17 : Prog (BitVec 64) :=
.seq body691_3 body691_16

def body691_18 : Prog (BitVec 64) :=
.seq body691_0 body691_17

def body691_19 : Prog (BitVec 64) :=
.decCall ("qr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 192#64]) body691_18

def body691_20 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body691_19

def body691_21 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body691_20

def body691_22 : Prog (BitVec 64) :=
.seq body691_0 body691_3

def body691_23 : Prog (BitVec 64) :=
.seq body691_5 body691_6

def body691_24 : Prog (BitVec 64) :=
.seq body691_23 body691_7

def body691_25 : Prog (BitVec 64) :=
.seq body691_24 body691_8

def body691_26 : Prog (BitVec 64) :=
.seq body691_25 body691_9

def body691_27 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body691_26

def body691_28 : Prog (BitVec 64) :=
.seq body691_4 body691_27

def body691_29 : Prog (BitVec 64) :=
.decCall ("res") (Flapjack.Shape.one) ("bn254_pairing_check") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr")]) body691_28

def body691_30 : Prog (BitVec 64) :=
.seq body691_22 body691_29

def body691_31 : Prog (BitVec 64) :=
.decCall ("qr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 192#64]) body691_30

def body691_32 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body691_31

def body691_33 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body691_32

def originalData691 : Decl (BitVec 64) :=
.function { name := "pre_alt_bn128_pairing_check", inline := false, exported := false, params := [], body := body691_21, returnShape := (Flapjack.Shape.one) }
def simplifiedData691 : Decl (BitVec 64) :=
.function { name := "pre_alt_bn128_pairing_check", inline := false, exported := false, params := [], body := body691_33, returnShape := (Flapjack.Shape.one) }
def original691 := Pancake.PanLang.declToHOL originalData691
def simplified691 := Pancake.PanLang.declToHOL simplifiedData691
end InitECandidate.Proofs.FrontendStages.Declarations
