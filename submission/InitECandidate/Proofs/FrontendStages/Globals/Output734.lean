import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data734
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate718
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody734_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody734_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody734_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "s0") (Flapjack.Exp.const 1#64)) globalBody734_0 globalBody734_1

def globalBody734_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody734_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z0") (Flapjack.Exp.const 0#64)) globalBody734_3 globalBody734_1

def globalBody734_5 : Prog (BitVec 64) :=
Flapjack.Prog.call none "bls_fp_sgn0" [Flapjack.Exp.var Flapjack.VarKind.local "a1"]

def globalBody734_6 : Prog (BitVec 64) :=
.dec ("a1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 48#64])) globalBody734_5

def globalBody734_7 : Prog (BitVec 64) :=
.seq globalBody734_4 globalBody734_6

def globalBody734_8 : Prog (BitVec 64) :=
.decCall ("z0") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "a0"]) globalBody734_7

def globalBody734_9 : Prog (BitVec 64) :=
.seq globalBody734_2 globalBody734_8

def globalBody734_10 : Prog (BitVec 64) :=
.decCall ("s0") (Flapjack.Shape.one) ("bls_fp_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "a0"]) globalBody734_9

def globalBody734_11 : Prog (BitVec 64) :=
.dec ("a0") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "a")) globalBody734_10

def globalData734 : Decl (BitVec 64) :=
.function { name := "fp2_sgn0", inline := false, exported := false, params := [("a", Flapjack.Shape.one)], body := globalBody734_11, returnShape := (Flapjack.Shape.one) }
def globalOutput734 := Pancake.PanLang.declToHOL globalData734
end InitECandidate.Proofs.FrontendStages.Declarations
