import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data427
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate411
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody427_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody427_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody427_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 2#64)) globalBody427_0 globalBody427_1

def globalBody427_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "mid" (Flapjack.Exp.var Flapjack.VarKind.local "n")

def globalBody427_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "n")
  (Flapjack.Exp.var Flapjack.VarKind.local "mid")) globalBody427_3 globalBody427_1

def globalBody427_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "right" (Flapjack.Exp.var Flapjack.VarKind.local "n")

def globalBody427_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "n")
  (Flapjack.Exp.var Flapjack.VarKind.local "right")) globalBody427_5 globalBody427_1

def globalBody427_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dst",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def globalBody427_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody427_9 : Prog (BitVec 64) :=
.seq globalBody427_7 globalBody427_8

def globalBody427_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dst",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def globalBody427_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def globalBody427_12 : Prog (BitVec 64) :=
.seq globalBody427_10 globalBody427_11

def globalBody427_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "gt") (Flapjack.Exp.const 0#64)) globalBody427_9 globalBody427_12

def globalBody427_14 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64])

def globalBody427_15 : Prog (BitVec 64) :=
.seq globalBody427_13 globalBody427_14

def globalBody427_16 : Prog (BitVec 64) :=
.decCall ("gt") (Flapjack.Shape.one) ("bal_sort_gt") ([Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "b",
  Flapjack.Exp.var Flapjack.VarKind.local "kind"]) globalBody427_15

def globalBody427_17 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "src",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) globalBody427_16

def globalBody427_18 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "src",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) globalBody427_17

def globalBody427_19 : Prog (BitVec 64) :=
.while (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
        (Flapjack.Exp.var Flapjack.VarKind.local "mid")),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
        (Flapjack.Exp.var Flapjack.VarKind.local "right"))]) globalBody427_18

def globalBody427_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dst",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "src",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def globalBody427_21 : Prog (BitVec 64) :=
.seq globalBody427_20 globalBody427_8

def globalBody427_22 : Prog (BitVec 64) :=
.seq globalBody427_21 globalBody427_14

def globalBody427_23 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "mid")) globalBody427_22

def globalBody427_24 : Prog (BitVec 64) :=
.seq globalBody427_19 globalBody427_23

def globalBody427_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dst",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "src",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def globalBody427_26 : Prog (BitVec 64) :=
.seq globalBody427_25 globalBody427_11

def globalBody427_27 : Prog (BitVec 64) :=
.seq globalBody427_26 globalBody427_14

def globalBody427_28 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "right")) globalBody427_27

def globalBody427_29 : Prog (BitVec 64) :=
.seq globalBody427_24 globalBody427_28

def globalBody427_30 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "left" (Flapjack.Exp.var Flapjack.VarKind.local "right")

def globalBody427_31 : Prog (BitVec 64) :=
.seq globalBody427_29 globalBody427_30

def globalBody427_32 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "left") globalBody427_31

def globalBody427_33 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "mid") globalBody427_32

def globalBody427_34 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "left") globalBody427_33

def globalBody427_35 : Prog (BitVec 64) :=
.seq globalBody427_6 globalBody427_34

def globalBody427_36 : Prog (BitVec 64) :=
.dec ("right") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "mid", Flapjack.Exp.var Flapjack.VarKind.local "width"]) globalBody427_35

def globalBody427_37 : Prog (BitVec 64) :=
.seq globalBody427_4 globalBody427_36

def globalBody427_38 : Prog (BitVec 64) :=
.dec ("mid") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "left", Flapjack.Exp.var Flapjack.VarKind.local "width"]) globalBody427_37

def globalBody427_39 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "left")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) globalBody427_38

def globalBody427_40 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "src" (Flapjack.Exp.var Flapjack.VarKind.local "dst")

def globalBody427_41 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "dst" (Flapjack.Exp.var Flapjack.VarKind.local "swap")

def globalBody427_42 : Prog (BitVec 64) :=
.seq globalBody427_40 globalBody427_41

def globalBody427_43 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "width"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "width", Flapjack.Exp.const 2#64])

def globalBody427_44 : Prog (BitVec 64) :=
.seq globalBody427_42 globalBody427_43

def globalBody427_45 : Prog (BitVec 64) :=
.dec ("swap") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "src") globalBody427_44

def globalBody427_46 : Prog (BitVec 64) :=
.seq globalBody427_39 globalBody427_45

def globalBody427_47 : Prog (BitVec 64) :=
.dec ("left") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody427_46

def globalBody427_48 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "width")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) globalBody427_47

def globalBody427_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "src",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]

def globalBody427_50 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "src")
  (Flapjack.Exp.var Flapjack.VarKind.local "p")) globalBody427_49 globalBody427_1

def globalBody427_51 : Prog (BitVec 64) :=
.seq globalBody427_48 globalBody427_50

def globalBody427_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody427_53 : Prog (BitVec 64) :=
.seq globalBody427_51 globalBody427_52

def globalBody427_54 : Prog (BitVec 64) :=
.seq globalBody427_53 globalBody427_0

def globalBody427_55 : Prog (BitVec 64) :=
.dec ("width") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) globalBody427_54

def globalBody427_56 : Prog (BitVec 64) :=
.dec ("dst") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "aux") globalBody427_55

def globalBody427_57 : Prog (BitVec 64) :=
.dec ("src") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p") globalBody427_56

def globalBody427_58 : Prog (BitVec 64) :=
.decCall ("aux") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) globalBody427_57

def globalBody427_59 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody427_58

def globalBody427_60 : Prog (BitVec 64) :=
.seq globalBody427_2 globalBody427_59

def globalData427 : Decl (BitVec 64) :=
.function { name := "sort_elems", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("esz", Flapjack.Shape.one), ("kind", Flapjack.Shape.one),
  ("tmp", Flapjack.Shape.one)], body := globalBody427_60, returnShape := (Flapjack.Shape.one) }
def globalOutput427 := Pancake.PanLang.declToHOL globalData427
end InitECandidate.Proofs.FrontendStages.Declarations
