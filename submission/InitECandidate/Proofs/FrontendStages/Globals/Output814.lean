import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data814
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate797
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody814_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 10#64)

def globalBody814_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody814_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) globalBody814_0 globalBody814_1

def globalBody814_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "qr"))
  (Flapjack.Exp.const 0#64)) globalBody814_0 globalBody814_1

def globalBody814_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "gasq")]

def globalBody814_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "err") (Flapjack.Exp.const 0#64)) globalBody814_0 globalBody814_1

def globalBody814_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def globalBody814_7 : Prog (BitVec 64) :=
.seq globalBody814_5 globalBody814_6

def globalBody814_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 256#64)

def globalBody814_9 : Prog (BitVec 64) :=
.seq globalBody814_7 globalBody814_8

def globalBody814_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody814_11 : Prog (BitVec 64) :=
.seq globalBody814_9 globalBody814_10

def globalBody814_12 : Prog (BitVec 64) :=
.decCall ("err") (Flapjack.Shape.one) ("bls_g2_msm_exec") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "out"]) globalBody814_11

def globalBody814_13 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 256#64]) globalBody814_12

def globalBody814_14 : Prog (BitVec 64) :=
.seq globalBody814_4 globalBody814_13

def globalBody814_15 : Prog (BitVec 64) :=
.decCall ("gasq") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 22500#64],
      Flapjack.Exp.var Flapjack.VarKind.local "discount"],
  Flapjack.Exp.const 1000#64]) globalBody814_14

def globalBody814_16 : Prog (BitVec 64) :=
.decCall ("discount") (Flapjack.Shape.one) ("bls_g2_msm_discount") ([Flapjack.Exp.var Flapjack.VarKind.local "k"]) globalBody814_15

def globalBody814_17 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr")) globalBody814_16

def globalBody814_18 : Prog (BitVec 64) :=
.seq globalBody814_3 globalBody814_17

def globalBody814_19 : Prog (BitVec 64) :=
.decCall ("qr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 288#64]) globalBody814_18

def globalBody814_20 : Prog (BitVec 64) :=
.seq globalBody814_2 globalBody814_19

def globalBody814_21 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) globalBody814_20

def globalBody814_22 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 112#64])) globalBody814_21

def globalData814 : Decl (BitVec 64) :=
.function { name := "pre_bls_g2_msm", inline := false, exported := false, params := [], body := globalBody814_22, returnShape := (Flapjack.Shape.one) }
def globalOutput814 := Pancake.PanLang.declToHOL globalData814
end InitECandidate.Proofs.FrontendStages.Declarations
