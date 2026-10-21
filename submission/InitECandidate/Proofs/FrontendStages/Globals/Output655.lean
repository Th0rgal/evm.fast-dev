import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data655
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate637
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody655_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "e"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 1#64])

def globalBody655_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "c0"), none)) "fq_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "c0", Flapjack.Exp.var Flapjack.VarKind.local "t82"]

def globalBody655_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "c0")

def globalBody655_3 : Prog (BitVec 64) :=
.seq globalBody655_1 globalBody655_2

def globalBody655_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "c6"), none)) "fq_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "c6", Flapjack.Exp.var Flapjack.VarKind.local "t18"]

def globalBody655_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 6#64],
          Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "c6")

def globalBody655_6 : Prog (BitVec 64) :=
.seq globalBody655_4 globalBody655_5

def globalBody655_7 : Prog (BitVec 64) :=
.dec ("c6") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 6#64],
          Flapjack.Exp.const 32#64]])) globalBody655_6

def globalBody655_8 : Prog (BitVec 64) :=
.seq globalBody655_3 globalBody655_7

def globalBody655_9 : Prog (BitVec 64) :=
.dec ("c0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 32#64]])) globalBody655_8

def globalBody655_10 : Prog (BitVec 64) :=
.decCall ("t18") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul_small") ([Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 18#64]) globalBody655_9

def globalBody655_11 : Prog (BitVec 64) :=
.decCall ("t82") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul_small") ([Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 82#64]) globalBody655_10

def globalBody655_12 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 12#64],
          Flapjack.Exp.const 32#64]])) globalBody655_11

def globalBody655_13 : Prog (BitVec 64) :=
.seq globalBody655_0 globalBody655_12

def globalBody655_14 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "e")) globalBody655_13

def globalBody655_15 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody655_16 : Prog (BitVec 64) :=
.seq globalBody655_14 globalBody655_15

def globalBody655_17 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 11#64) globalBody655_16

def globalData655 : Decl (BitVec 64) :=
.function { name := "fq12_reduce", inline := false, exported := false, params := [("t", Flapjack.Shape.one)], body := globalBody655_17, returnShape := (Flapjack.Shape.one) }
def globalOutput655 := Pancake.PanLang.declToHOL globalData655
end InitECandidate.Proofs.FrontendStages.Declarations
