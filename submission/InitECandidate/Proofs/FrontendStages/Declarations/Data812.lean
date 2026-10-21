import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify796
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body812_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 10#64)

def body812_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body812_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) body812_0 body812_1

def body812_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "qr"))
  (Flapjack.Exp.const 0#64)) body812_0 body812_1

def body812_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "gasq")]

def body812_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "err") (Flapjack.Exp.const 0#64)) body812_0 body812_1

def body812_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body812_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 128#64)

def body812_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body812_9 : Prog (BitVec 64) :=
.seq body812_7 body812_8

def body812_10 : Prog (BitVec 64) :=
.seq body812_6 body812_9

def body812_11 : Prog (BitVec 64) :=
.seq body812_5 body812_10

def body812_12 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bls_g1_msm_exec") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "out"]) body812_11

def body812_13 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) body812_12

def body812_14 : Prog (BitVec 64) :=
.seq body812_4 body812_13

def body812_15 : Prog (BitVec 64) :=
.decCall ("gasq") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 12000#64],
      Flapjack.Exp.var Flapjack.VarKind.local "discount"],
  Flapjack.Exp.const 1000#64]) body812_14

def body812_16 : Prog (BitVec 64) :=
.decCall ("discount") (Flapjack.Shape.one) ("bls_g1_msm_discount") ([Flapjack.Exp.var Flapjack.VarKind.local "k"]) body812_15

def body812_17 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr")) body812_16

def body812_18 : Prog (BitVec 64) :=
.seq body812_3 body812_17

def body812_19 : Prog (BitVec 64) :=
.decCall ("qr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 160#64]) body812_18

def body812_20 : Prog (BitVec 64) :=
.seq body812_2 body812_19

def body812_21 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body812_20

def body812_22 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body812_21

def body812_23 : Prog (BitVec 64) :=
.seq body812_5 body812_6

def body812_24 : Prog (BitVec 64) :=
.seq body812_23 body812_7

def body812_25 : Prog (BitVec 64) :=
.seq body812_24 body812_8

def body812_26 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bls_g1_msm_exec") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "out"]) body812_25

def body812_27 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) body812_26

def body812_28 : Prog (BitVec 64) :=
.seq body812_4 body812_27

def body812_29 : Prog (BitVec 64) :=
.decCall ("gasq") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 12000#64],
      Flapjack.Exp.var Flapjack.VarKind.local "discount"],
  Flapjack.Exp.const 1000#64]) body812_28

def body812_30 : Prog (BitVec 64) :=
.decCall ("discount") (Flapjack.Shape.one) ("bls_g1_msm_discount") ([Flapjack.Exp.var Flapjack.VarKind.local "k"]) body812_29

def body812_31 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr")) body812_30

def body812_32 : Prog (BitVec 64) :=
.seq body812_3 body812_31

def body812_33 : Prog (BitVec 64) :=
.decCall ("qr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 160#64]) body812_32

def body812_34 : Prog (BitVec 64) :=
.seq body812_2 body812_33

def body812_35 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body812_34

def body812_36 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body812_35

def originalData812 : Decl (BitVec 64) :=
.function { name := "pre_bls_g1_msm", inline := false, exported := false, params := [], body := body812_22, returnShape := (Flapjack.Shape.one) }
def simplifiedData812 : Decl (BitVec 64) :=
.function { name := "pre_bls_g1_msm", inline := false, exported := false, params := [], body := body812_36, returnShape := (Flapjack.Shape.one) }
def original812 := Pancake.PanLang.declToHOL originalData812
def simplified812 := Pancake.PanLang.declToHOL simplifiedData812
end InitECandidate.Proofs.FrontendStages.Declarations
