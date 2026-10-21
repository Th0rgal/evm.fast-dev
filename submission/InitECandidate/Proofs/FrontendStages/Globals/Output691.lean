import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data691
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate675
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody691_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.const 34000#64, Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr")],
        Flapjack.Exp.const 45000#64]]

def globalBody691_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def globalBody691_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody691_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "qr"))
  (Flapjack.Exp.const 0#64)) globalBody691_1 globalBody691_2

def globalBody691_4 : Prog (BitVec 64) :=
.seq globalBody691_0 globalBody691_3

def globalBody691_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "res") (Flapjack.Exp.const 2#64)) globalBody691_1 globalBody691_2

def globalBody691_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64]

def globalBody691_7 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 31#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "res")

def globalBody691_8 : Prog (BitVec 64) :=
.seq globalBody691_6 globalBody691_7

def globalBody691_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def globalBody691_10 : Prog (BitVec 64) :=
.seq globalBody691_8 globalBody691_9

def globalBody691_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 32#64)

def globalBody691_12 : Prog (BitVec 64) :=
.seq globalBody691_10 globalBody691_11

def globalBody691_13 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody691_14 : Prog (BitVec 64) :=
.seq globalBody691_12 globalBody691_13

def globalBody691_15 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody691_14

def globalBody691_16 : Prog (BitVec 64) :=
.seq globalBody691_5 globalBody691_15

def globalBody691_17 : Prog (BitVec 64) :=
.decCall ("res") (Flapjack.Shape.one) ("bn254_pairing_check") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr")]) globalBody691_16

def globalBody691_18 : Prog (BitVec 64) :=
.seq globalBody691_4 globalBody691_17

def globalBody691_19 : Prog (BitVec 64) :=
.decCall ("qr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 192#64]) globalBody691_18

def globalBody691_20 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) globalBody691_19

def globalBody691_21 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 112#64])) globalBody691_20

def globalData691 : Decl (BitVec 64) :=
.function { name := "pre_alt_bn128_pairing_check", inline := false, exported := false, params := [], body := globalBody691_21, returnShape := (Flapjack.Shape.one) }
def globalOutput691 := Pancake.PanLang.declToHOL globalData691
end InitECandidate.Proofs.FrontendStages.Declarations
