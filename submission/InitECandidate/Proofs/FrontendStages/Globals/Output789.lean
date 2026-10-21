import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data789
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate773
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody789_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "v7", Flapjack.Exp.var Flapjack.VarKind.local "v"]

def globalBody789_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "v7", Flapjack.Exp.var Flapjack.VarKind.local "v7",
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def globalBody789_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody789_3 : Prog (BitVec 64) :=
.seq globalBody789_1 globalBody789_2

def globalBody789_4 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 6#64)) globalBody789_3

def globalBody789_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp1", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "v7"]

def globalBody789_6 : Prog (BitVec 64) :=
.seq globalBody789_4 globalBody789_5

def globalBody789_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp2", Flapjack.Exp.var Flapjack.VarKind.local "v7",
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def globalBody789_8 : Prog (BitVec 64) :=
.seq globalBody789_6 globalBody789_7

def globalBody789_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp2", Flapjack.Exp.var Flapjack.VarKind.local "temp1",
    Flapjack.Exp.var Flapjack.VarKind.local "temp2"]

def globalBody789_10 : Prog (BitVec 64) :=
.seq globalBody789_8 globalBody789_9

def globalBody789_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_pow"
  [Flapjack.Exp.var Flapjack.VarKind.local "gamma", Flapjack.Exp.var Flapjack.VarKind.local "temp2",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 1528#64],
    Flapjack.Exp.const 12#64]

def globalBody789_12 : Prog (BitVec 64) :=
.seq globalBody789_10 globalBody789_11

def globalBody789_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "gamma", Flapjack.Exp.var Flapjack.VarKind.local "gamma",
    Flapjack.Exp.var Flapjack.VarKind.local "temp1"]

def globalBody789_14 : Prog (BitVec 64) :=
.seq globalBody789_12 globalBody789_13

def globalBody789_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "gamma"]

def globalBody789_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def globalBody789_17 : Prog (BitVec 64) :=
.seq globalBody789_15 globalBody789_16

def globalBody789_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "cand",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 5216#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 96#64]],
    Flapjack.Exp.var Flapjack.VarKind.local "gamma"]

def globalBody789_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "chk", Flapjack.Exp.var Flapjack.VarKind.local "cand"]

def globalBody789_20 : Prog (BitVec 64) :=
.seq globalBody789_18 globalBody789_19

def globalBody789_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "chk", Flapjack.Exp.var Flapjack.VarKind.local "chk",
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def globalBody789_22 : Prog (BitVec 64) :=
.seq globalBody789_20 globalBody789_21

def globalBody789_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "chk", Flapjack.Exp.var Flapjack.VarKind.local "chk",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def globalBody789_24 : Prog (BitVec 64) :=
.seq globalBody789_22 globalBody789_23

def globalBody789_25 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "valid" (Flapjack.Exp.const 1#64)

def globalBody789_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "cand"]

def globalBody789_27 : Prog (BitVec 64) :=
.seq globalBody789_25 globalBody789_26

def globalBody789_28 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody789_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "valid") (Flapjack.Exp.const 0#64))]) globalBody789_27 globalBody789_28

def globalBody789_30 : Prog (BitVec 64) :=
.seq globalBody789_29 globalBody789_2

def globalBody789_31 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "chk"]) globalBody789_30

def globalBody789_32 : Prog (BitVec 64) :=
.seq globalBody789_24 globalBody789_31

def globalBody789_33 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 4#64)) globalBody789_32

def globalBody789_34 : Prog (BitVec 64) :=
.seq globalBody789_17 globalBody789_33

def globalBody789_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody789_36 : Prog (BitVec 64) :=
.seq globalBody789_34 globalBody789_35

def globalBody789_37 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "valid")

def globalBody789_38 : Prog (BitVec 64) :=
.seq globalBody789_36 globalBody789_37

def globalBody789_39 : Prog (BitVec 64) :=
.dec ("valid") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody789_38

def globalBody789_40 : Prog (BitVec 64) :=
.seq globalBody789_14 globalBody789_39

def globalBody789_41 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody789_40

def globalBody789_42 : Prog (BitVec 64) :=
.seq globalBody789_0 globalBody789_41

def globalBody789_43 : Prog (BitVec 64) :=
.dec ("chk") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) globalBody789_42

def globalBody789_44 : Prog (BitVec 64) :=
.dec ("cand") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) globalBody789_43

def globalBody789_45 : Prog (BitVec 64) :=
.dec ("gamma") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) globalBody789_44

def globalBody789_46 : Prog (BitVec 64) :=
.dec ("temp2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) globalBody789_45

def globalBody789_47 : Prog (BitVec 64) :=
.dec ("temp1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) globalBody789_46

def globalBody789_48 : Prog (BitVec 64) :=
.dec ("v7") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") globalBody789_47

def globalBody789_49 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 6#64]]) globalBody789_48

def globalBody789_50 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody789_49

def globalData789 : Decl (BitVec 64) :=
.function { name := "swu_sqrt_division_fp2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("u", Flapjack.Shape.one), ("v", Flapjack.Shape.one)], body := globalBody789_50, returnShape := (Flapjack.Shape.one) }
def globalOutput789 := Pancake.PanLang.declToHOL globalData789
end InitECandidate.Proofs.FrontendStages.Declarations
