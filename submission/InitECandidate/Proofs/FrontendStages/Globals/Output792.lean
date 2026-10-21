import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data792
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate776
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody792_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.var Flapjack.VarKind.local "z"]

def globalBody792_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "z"]

def globalBody792_2 : Prog (BitVec 64) :=
.seq globalBody792_0 globalBody792_1

def globalBody792_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "z"]

def globalBody792_4 : Prog (BitVec 64) :=
.seq globalBody792_2 globalBody792_3

def globalBody792_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "iso_horner_fp2"
  [Flapjack.Exp.var Flapjack.VarKind.local "m",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 5600#64],
    Flapjack.Exp.const 4#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]

def globalBody792_6 : Prog (BitVec 64) :=
.seq globalBody792_4 globalBody792_5

def globalBody792_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "iso_horner_fp2"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 5984#64],
    Flapjack.Exp.const 4#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]

def globalBody792_8 : Prog (BitVec 64) :=
.seq globalBody792_6 globalBody792_7

def globalBody792_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "iso_horner_fp2"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 6368#64],
    Flapjack.Exp.const 4#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]

def globalBody792_10 : Prog (BitVec 64) :=
.seq globalBody792_8 globalBody792_9

def globalBody792_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "iso_horner_fp2"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 6752#64],
    Flapjack.Exp.const 4#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]

def globalBody792_12 : Prog (BitVec 64) :=
.seq globalBody792_10 globalBody792_11

def globalBody792_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 192#64],
    Flapjack.Exp.var Flapjack.VarKind.local "y"]

def globalBody792_14 : Prog (BitVec 64) :=
.seq globalBody792_12 globalBody792_13

def globalBody792_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 288#64],
    Flapjack.Exp.var Flapjack.VarKind.local "z"]

def globalBody792_16 : Prog (BitVec 64) :=
.seq globalBody792_14 globalBody792_15

def globalBody792_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.var Flapjack.VarKind.local "m",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 288#64]]

def globalBody792_18 : Prog (BitVec 64) :=
.seq globalBody792_16 globalBody792_17

def globalBody792_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 192#64]]

def globalBody792_20 : Prog (BitVec 64) :=
.seq globalBody792_18 globalBody792_19

def globalBody792_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 288#64]]

def globalBody792_22 : Prog (BitVec 64) :=
.seq globalBody792_20 globalBody792_21

def globalBody792_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "zp"]

def globalBody792_24 : Prog (BitVec 64) :=
.seq globalBody792_22 globalBody792_23

def globalBody792_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody792_26 : Prog (BitVec 64) :=
.seq globalBody792_24 globalBody792_25

def globalBody792_27 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody792_28 : Prog (BitVec 64) :=
.seq globalBody792_26 globalBody792_27

def globalBody792_29 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 192#64]) globalBody792_28

def globalBody792_30 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 96#64]) globalBody792_29

def globalBody792_31 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p") globalBody792_30

def globalBody792_32 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 4#64]]) globalBody792_31

def globalBody792_33 : Prog (BitVec 64) :=
.decCall ("zp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 3#64]]) globalBody792_32

def globalBody792_34 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody792_33

def globalData792 : Decl (BitVec 64) :=
.function { name := "iso_map_g2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := globalBody792_34, returnShape := (Flapjack.Shape.one) }
def globalOutput792 := Pancake.PanLang.declToHOL globalData792
end InitECandidate.Proofs.FrontendStages.Declarations
