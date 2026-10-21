import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data791
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate775
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody791_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "v",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "kp",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 1#64],
            Flapjack.Exp.const 96#64]]]

def globalBody791_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v",
    Flapjack.Exp.var Flapjack.VarKind.local "x"]

def globalBody791_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "zp",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 96#64]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "kp",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.op Flapjack.BinOp.sub
              [Flapjack.Exp.op Flapjack.BinOp.sub
                  [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 2#64],
                Flapjack.Exp.var Flapjack.VarKind.local "j"],
            Flapjack.Exp.const 96#64]]]

def globalBody791_3 : Prog (BitVec 64) :=
.seq globalBody791_1 globalBody791_2

def globalBody791_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody791_5 : Prog (BitVec 64) :=
.seq globalBody791_3 globalBody791_4

def globalBody791_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def globalBody791_7 : Prog (BitVec 64) :=
.seq globalBody791_5 globalBody791_6

def globalBody791_8 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 1#64])) globalBody791_7

def globalBody791_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "v"]

def globalBody791_10 : Prog (BitVec 64) :=
.seq globalBody791_8 globalBody791_9

def globalBody791_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody791_12 : Prog (BitVec 64) :=
.seq globalBody791_10 globalBody791_11

def globalBody791_13 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody791_14 : Prog (BitVec 64) :=
.seq globalBody791_12 globalBody791_13

def globalBody791_15 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody791_14

def globalBody791_16 : Prog (BitVec 64) :=
.seq globalBody791_0 globalBody791_15

def globalBody791_17 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) globalBody791_16

def globalBody791_18 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) globalBody791_17

def globalBody791_19 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody791_18

def globalData791 : Decl (BitVec 64) :=
.function { name := "iso_horner_fp2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("kp", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("x", Flapjack.Shape.one),
  ("zp", Flapjack.Shape.one)], body := globalBody791_19, returnShape := (Flapjack.Shape.one) }
def globalOutput791 := Pancake.PanLang.declToHOL globalData791
end InitECandidate.Proofs.FrontendStages.Declarations
