import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data614
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate594
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody614_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 336#64]))
  (Flapjack.Exp.const 1732584193#64)

def globalBody614_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 336#64]),
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 4023233417#64)

def globalBody614_2 : Prog (BitVec 64) :=
.seq globalBody614_0 globalBody614_1

def globalBody614_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 336#64]),
      Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 2562383102#64)

def globalBody614_4 : Prog (BitVec 64) :=
.seq globalBody614_2 globalBody614_3

def globalBody614_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 336#64]),
      Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 271733878#64)

def globalBody614_6 : Prog (BitVec 64) :=
.seq globalBody614_4 globalBody614_5

def globalBody614_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 336#64]),
      Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 3285377520#64)

def globalBody614_8 : Prog (BitVec 64) :=
.seq globalBody614_6 globalBody614_7

def globalBody614_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ripemd160_block"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 336#64]),
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "i"]]

def globalBody614_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 64#64])

def globalBody614_11 : Prog (BitVec 64) :=
.seq globalBody614_9 globalBody614_10

def globalBody614_12 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "n")
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 64#64])) globalBody614_11

def globalBody614_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 344#64]),
    Flapjack.Exp.const 128#64]

def globalBody614_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 344#64]),
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "i"],
    Flapjack.Exp.var Flapjack.VarKind.local "rem"]

def globalBody614_15 : Prog (BitVec 64) :=
.seq globalBody614_13 globalBody614_14

def globalBody614_16 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 344#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "rem"])
  (Flapjack.Exp.const 128#64)

def globalBody614_17 : Prog (BitVec 64) :=
.seq globalBody614_15 globalBody614_16

def globalBody614_18 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "total" (Flapjack.Exp.const 128#64)

def globalBody614_19 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody614_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "rem") (Flapjack.Exp.const 56#64)) globalBody614_18 globalBody614_19

def globalBody614_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_le64"
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.load Flapjack.Shape.one
              (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 344#64]),
            Flapjack.Exp.var Flapjack.VarKind.local "total"],
        Flapjack.Exp.const 8#64],
    Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 3#64)]

def globalBody614_22 : Prog (BitVec 64) :=
.seq globalBody614_20 globalBody614_21

def globalBody614_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ripemd160_block"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 336#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 344#64])]

def globalBody614_24 : Prog (BitVec 64) :=
.seq globalBody614_22 globalBody614_23

def globalBody614_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ripemd160_block"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 336#64]),
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 344#64]),
        Flapjack.Exp.const 64#64]]

def globalBody614_26 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "total") (Flapjack.Exp.const 128#64)) globalBody614_25 globalBody614_19

def globalBody614_27 : Prog (BitVec 64) :=
.seq globalBody614_24 globalBody614_26

def globalBody614_28 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def globalBody614_29 : Prog (BitVec 64) :=
.seq globalBody614_27 globalBody614_28

def globalBody614_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_le32"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64]],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 336#64]),
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])]

def globalBody614_31 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody614_32 : Prog (BitVec 64) :=
.seq globalBody614_30 globalBody614_31

def globalBody614_33 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 5#64)) globalBody614_32

def globalBody614_34 : Prog (BitVec 64) :=
.seq globalBody614_29 globalBody614_33

def globalBody614_35 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody614_36 : Prog (BitVec 64) :=
.seq globalBody614_34 globalBody614_35

def globalBody614_37 : Prog (BitVec 64) :=
.dec ("total") (Flapjack.Shape.one) (Flapjack.Exp.const 64#64) globalBody614_36

def globalBody614_38 : Prog (BitVec 64) :=
.seq globalBody614_17 globalBody614_37

def globalBody614_39 : Prog (BitVec 64) :=
.dec ("rem") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "i"]) globalBody614_38

def globalBody614_40 : Prog (BitVec 64) :=
.seq globalBody614_12 globalBody614_39

def globalBody614_41 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody614_40

def globalBody614_42 : Prog (BitVec 64) :=
.seq globalBody614_8 globalBody614_41

def globalData614 : Decl (BitVec 64) :=
.function { name := "ripemd160", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody614_42, returnShape := (Flapjack.Shape.one) }
def globalOutput614 := Pancake.PanLang.declToHOL globalData614
end InitECandidate.Proofs.FrontendStages.Declarations
