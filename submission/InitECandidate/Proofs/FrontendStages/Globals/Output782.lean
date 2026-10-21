import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data782
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate766
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody782_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.var Flapjack.VarKind.local "q"]

def globalBody782_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 96#64]]

def globalBody782_2 : Prog (BitVec 64) :=
.seq globalBody782_0 globalBody782_1

def globalBody782_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 192#64]]

def globalBody782_4 : Prog (BitVec 64) :=
.seq globalBody782_2 globalBody782_3

def globalBody782_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "f"]

def globalBody782_6 : Prog (BitVec 64) :=
.seq globalBody782_4 globalBody782_5

def globalBody782_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody782_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "f", Flapjack.Exp.var Flapjack.VarKind.local "f",
    Flapjack.Exp.var Flapjack.VarKind.local "f"]

def globalBody782_9 : Prog (BitVec 64) :=
.seq globalBody782_7 globalBody782_8

def globalBody782_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_doubling_step"
  [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.var Flapjack.VarKind.local "co"]

def globalBody782_11 : Prog (BitVec 64) :=
.seq globalBody782_9 globalBody782_10

def globalBody782_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_ell"
  [Flapjack.Exp.var Flapjack.VarKind.local "f", Flapjack.Exp.var Flapjack.VarKind.local "co",
    Flapjack.Exp.var Flapjack.VarKind.local "px", Flapjack.Exp.var Flapjack.VarKind.local "py"]

def globalBody782_13 : Prog (BitVec 64) :=
.seq globalBody782_11 globalBody782_12

def globalBody782_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_addition_step"
  [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "co"]

def globalBody782_15 : Prog (BitVec 64) :=
.seq globalBody782_14 globalBody782_12

def globalBody782_16 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody782_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "x")
        (Flapjack.Exp.var Flapjack.VarKind.local "i"),
      Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 1#64)) globalBody782_15 globalBody782_16

def globalBody782_18 : Prog (BitVec 64) :=
.seq globalBody782_13 globalBody782_17

def globalBody782_19 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) globalBody782_18

def globalBody782_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_conj"
  [Flapjack.Exp.var Flapjack.VarKind.local "f", Flapjack.Exp.var Flapjack.VarKind.local "f"]

def globalBody782_21 : Prog (BitVec 64) :=
.seq globalBody782_19 globalBody782_20

def globalBody782_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody782_23 : Prog (BitVec 64) :=
.seq globalBody782_21 globalBody782_22

def globalBody782_24 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody782_25 : Prog (BitVec 64) :=
.seq globalBody782_23 globalBody782_24

def globalBody782_26 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 63#64) globalBody782_25

def globalBody782_27 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
      Flapjack.Exp.const 1376#64])) globalBody782_26

def globalBody782_28 : Prog (BitVec 64) :=
.seq globalBody782_6 globalBody782_27

def globalBody782_29 : Prog (BitVec 64) :=
.decCall ("co") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 3#64]]) globalBody782_28

def globalBody782_30 : Prog (BitVec 64) :=
.decCall ("rp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) globalBody782_29

def globalBody782_31 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody782_30

def globalData782 : Decl (BitVec 64) :=
.function { name := "pair_miller_loop", inline := false, exported := false, params := [("f", Flapjack.Shape.one),
  ("px",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("py",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("q", Flapjack.Shape.one)], body := globalBody782_31, returnShape := (Flapjack.Shape.one) }
def globalOutput782 := Pancake.PanLang.declToHOL globalData782
end InitECandidate.Proofs.FrontendStages.Declarations
