import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify598
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body614_0 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.global "rmd_h") (Flapjack.Exp.const 1732584193#64)

def body614_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_h", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 4023233417#64)

def body614_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_h", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 2562383102#64)

def body614_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_h", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 271733878#64)

def body614_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_h", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 3285377520#64)

def body614_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ripemd160_block"
  [Flapjack.Exp.var Flapjack.VarKind.global "rmd_h",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "i"]]

def body614_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 64#64])

def body614_7 : Prog (BitVec 64) :=
.seq body614_5 body614_6

def body614_8 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "n")
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 64#64])) body614_7

def body614_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.global "rmd_pad", Flapjack.Exp.const 128#64]

def body614_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.global "rmd_pad",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "i"],
    Flapjack.Exp.var Flapjack.VarKind.local "rem"]

def body614_11 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "rmd_pad", Flapjack.Exp.var Flapjack.VarKind.local "rem"])
  (Flapjack.Exp.const 128#64)

def body614_12 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "total" (Flapjack.Exp.const 128#64)

def body614_13 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body614_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "rem") (Flapjack.Exp.const 56#64)) body614_12 body614_13

def body614_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_le64"
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.global "rmd_pad", Flapjack.Exp.var Flapjack.VarKind.local "total"],
        Flapjack.Exp.const 8#64],
    Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 3#64)]

def body614_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ripemd160_block"
  [Flapjack.Exp.var Flapjack.VarKind.global "rmd_h", Flapjack.Exp.var Flapjack.VarKind.global "rmd_pad"]

def body614_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ripemd160_block"
  [Flapjack.Exp.var Flapjack.VarKind.global "rmd_h",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_pad", Flapjack.Exp.const 64#64]]

def body614_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "total") (Flapjack.Exp.const 128#64)) body614_17 body614_13

def body614_19 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def body614_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_le32"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64]],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.global "rmd_h",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])]

def body614_21 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body614_22 : Prog (BitVec 64) :=
.seq body614_20 body614_21

def body614_23 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 5#64)) body614_22

def body614_24 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body614_25 : Prog (BitVec 64) :=
.seq body614_23 body614_24

def body614_26 : Prog (BitVec 64) :=
.seq body614_19 body614_25

def body614_27 : Prog (BitVec 64) :=
.seq body614_18 body614_26

def body614_28 : Prog (BitVec 64) :=
.seq body614_16 body614_27

def body614_29 : Prog (BitVec 64) :=
.seq body614_15 body614_28

def body614_30 : Prog (BitVec 64) :=
.seq body614_14 body614_29

def body614_31 : Prog (BitVec 64) :=
.dec ("total") (Flapjack.Shape.one) (Flapjack.Exp.const 64#64) body614_30

def body614_32 : Prog (BitVec 64) :=
.seq body614_11 body614_31

def body614_33 : Prog (BitVec 64) :=
.seq body614_10 body614_32

def body614_34 : Prog (BitVec 64) :=
.seq body614_9 body614_33

def body614_35 : Prog (BitVec 64) :=
.dec ("rem") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body614_34

def body614_36 : Prog (BitVec 64) :=
.seq body614_8 body614_35

def body614_37 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body614_36

def body614_38 : Prog (BitVec 64) :=
.seq body614_4 body614_37

def body614_39 : Prog (BitVec 64) :=
.seq body614_3 body614_38

def body614_40 : Prog (BitVec 64) :=
.seq body614_2 body614_39

def body614_41 : Prog (BitVec 64) :=
.seq body614_1 body614_40

def body614_42 : Prog (BitVec 64) :=
.seq body614_0 body614_41

def body614_43 : Prog (BitVec 64) :=
.seq body614_0 body614_1

def body614_44 : Prog (BitVec 64) :=
.seq body614_43 body614_2

def body614_45 : Prog (BitVec 64) :=
.seq body614_44 body614_3

def body614_46 : Prog (BitVec 64) :=
.seq body614_45 body614_4

def body614_47 : Prog (BitVec 64) :=
.seq body614_9 body614_10

def body614_48 : Prog (BitVec 64) :=
.seq body614_47 body614_11

def body614_49 : Prog (BitVec 64) :=
.seq body614_14 body614_15

def body614_50 : Prog (BitVec 64) :=
.seq body614_49 body614_16

def body614_51 : Prog (BitVec 64) :=
.seq body614_50 body614_18

def body614_52 : Prog (BitVec 64) :=
.seq body614_51 body614_19

def body614_53 : Prog (BitVec 64) :=
.seq body614_52 body614_23

def body614_54 : Prog (BitVec 64) :=
.seq body614_53 body614_24

def body614_55 : Prog (BitVec 64) :=
.dec ("total") (Flapjack.Shape.one) (Flapjack.Exp.const 64#64) body614_54

def body614_56 : Prog (BitVec 64) :=
.seq body614_48 body614_55

def body614_57 : Prog (BitVec 64) :=
.dec ("rem") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body614_56

def body614_58 : Prog (BitVec 64) :=
.seq body614_8 body614_57

def body614_59 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body614_58

def body614_60 : Prog (BitVec 64) :=
.seq body614_46 body614_59

def originalData614 : Decl (BitVec 64) :=
.function { name := "ripemd160", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body614_42, returnShape := (Flapjack.Shape.one) }
def simplifiedData614 : Decl (BitVec 64) :=
.function { name := "ripemd160", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body614_60, returnShape := (Flapjack.Shape.one) }
def original614 := Pancake.PanLang.declToHOL originalData614
def simplified614 := Pancake.PanLang.declToHOL simplifiedData614
end InitECandidate.Proofs.FrontendStages.Declarations
