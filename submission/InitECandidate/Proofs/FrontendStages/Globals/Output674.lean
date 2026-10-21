import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data674
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate658
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody674_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 1152#64]

def globalBody674_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "shift" (Flapjack.Exp.const 2#64)

def globalBody674_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody674_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 0#64)) globalBody674_1 globalBody674_2

def globalBody674_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "shift" (Flapjack.Exp.const 3#64)

def globalBody674_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 1#64)) globalBody674_4 globalBody674_2

def globalBody674_6 : Prog (BitVec 64) :=
.seq globalBody674_3 globalBody674_5

def globalBody674_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "base",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "shift", Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "e0")

def globalBody674_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "base",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "shift", Flapjack.Exp.const 6#64],
          Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "c1")

def globalBody674_9 : Prog (BitVec 64) :=
.seq globalBody674_7 globalBody674_8

def globalBody674_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def globalBody674_11 : Prog (BitVec 64) :=
.seq globalBody674_9 globalBody674_10

def globalBody674_12 : Prog (BitVec 64) :=
.dec ("base") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 384#64]]) globalBody674_11

def globalBody674_13 : Prog (BitVec 64) :=
.seq globalBody674_6 globalBody674_12

def globalBody674_14 : Prog (BitVec 64) :=
.dec ("shift") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody674_13

def globalBody674_15 : Prog (BitVec 64) :=
.decCall ("e0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "c0", Flapjack.Exp.var Flapjack.VarKind.local "n9"]) globalBody674_14

def globalBody674_16 : Prog (BitVec 64) :=
.decCall ("n9") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul_small") ([Flapjack.Exp.var Flapjack.VarKind.local "c1", Flapjack.Exp.const 9#64]) globalBody674_15

def globalBody674_17 : Prog (BitVec 64) :=
.dec ("c1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "g2",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 64#64],
      Flapjack.Exp.const 32#64])) globalBody674_16

def globalBody674_18 : Prog (BitVec 64) :=
.dec ("c0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "g2",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 64#64]])) globalBody674_17

def globalBody674_19 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 3#64)) globalBody674_18

def globalBody674_20 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody674_21 : Prog (BitVec 64) :=
.seq globalBody674_19 globalBody674_20

def globalBody674_22 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody674_21

def globalBody674_23 : Prog (BitVec 64) :=
.seq globalBody674_0 globalBody674_22

def globalData674 : Decl (BitVec 64) :=
.function { name := "fq12_twist", inline := false, exported := false, params := [("out", Flapjack.Shape.one), ("g2", Flapjack.Shape.one)], body := globalBody674_23, returnShape := (Flapjack.Shape.one) }
def globalOutput674 := Pancake.PanLang.declToHOL globalData674
end InitECandidate.Proofs.FrontendStages.Declarations
