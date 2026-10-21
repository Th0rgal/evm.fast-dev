import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify799
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body815_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 10#64)

def body815_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body815_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) body815_0 body815_1

def body815_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "qr"))
  (Flapjack.Exp.const 0#64)) body815_0 body815_1

def body815_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 32600#64, Flapjack.Exp.var Flapjack.VarKind.local "k"],
        Flapjack.Exp.const 37700#64]]

def body815_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "err") (Flapjack.Exp.const 0#64)) body815_0 body815_1

def body815_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body815_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 32#64)

def body815_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body815_9 : Prog (BitVec 64) :=
.seq body815_7 body815_8

def body815_10 : Prog (BitVec 64) :=
.seq body815_6 body815_9

def body815_11 : Prog (BitVec 64) :=
.seq body815_5 body815_10

def body815_12 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bls_pairing_exec") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "out"]) body815_11

def body815_13 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body815_12

def body815_14 : Prog (BitVec 64) :=
.seq body815_4 body815_13

def body815_15 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr")) body815_14

def body815_16 : Prog (BitVec 64) :=
.seq body815_3 body815_15

def body815_17 : Prog (BitVec 64) :=
.decCall ("qr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 384#64]) body815_16

def body815_18 : Prog (BitVec 64) :=
.seq body815_2 body815_17

def body815_19 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body815_18

def body815_20 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body815_19

def body815_21 : Prog (BitVec 64) :=
.seq body815_5 body815_6

def body815_22 : Prog (BitVec 64) :=
.seq body815_21 body815_7

def body815_23 : Prog (BitVec 64) :=
.seq body815_22 body815_8

def body815_24 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bls_pairing_exec") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "out"]) body815_23

def body815_25 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body815_24

def body815_26 : Prog (BitVec 64) :=
.seq body815_4 body815_25

def body815_27 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr")) body815_26

def body815_28 : Prog (BitVec 64) :=
.seq body815_3 body815_27

def body815_29 : Prog (BitVec 64) :=
.decCall ("qr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 384#64]) body815_28

def body815_30 : Prog (BitVec 64) :=
.seq body815_2 body815_29

def body815_31 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body815_30

def body815_32 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body815_31

def originalData815 : Decl (BitVec 64) :=
.function { name := "pre_bls_pairing", inline := false, exported := false, params := [], body := body815_20, returnShape := (Flapjack.Shape.one) }
def simplifiedData815 : Decl (BitVec 64) :=
.function { name := "pre_bls_pairing", inline := false, exported := false, params := [], body := body815_32, returnShape := (Flapjack.Shape.one) }
def original815 := Pancake.PanLang.declToHOL originalData815
def simplified815 := Pancake.PanLang.declToHOL simplifiedData815
end InitECandidate.Proofs.FrontendStages.Declarations
