import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify745
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body761_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "base", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body761_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_set_inf" [Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body761_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body761_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_double"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body761_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body761_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "started") (Flapjack.Exp.const 1#64)) body761_3 body761_4

def body761_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc",
    Flapjack.Exp.var Flapjack.VarKind.local "base"]

def body761_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "started" (Flapjack.Exp.const 1#64)

def body761_8 : Prog (BitVec 64) :=
.seq body761_6 body761_7

def body761_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "bit") (Flapjack.Exp.const 1#64)) body761_8 body761_4

def body761_10 : Prog (BitVec 64) :=
.dec ("bit") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.shift Flapjack.Shift.lsr
      (Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "kptr",
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "i")
                  (Flapjack.Exp.const 6#64),
                Flapjack.Exp.const 8#64]]))
      (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 63#64]),
    Flapjack.Exp.const 1#64]) body761_9

def body761_11 : Prog (BitVec 64) :=
.seq body761_5 body761_10

def body761_12 : Prog (BitVec 64) :=
.seq body761_2 body761_11

def body761_13 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body761_12

def body761_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body761_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body761_16 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body761_17 : Prog (BitVec 64) :=
.seq body761_15 body761_16

def body761_18 : Prog (BitVec 64) :=
.seq body761_14 body761_17

def body761_19 : Prog (BitVec 64) :=
.seq body761_13 body761_18

def body761_20 : Prog (BitVec 64) :=
.dec ("started") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body761_19

def body761_21 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 64#64]) body761_20

def body761_22 : Prog (BitVec 64) :=
.seq body761_1 body761_21

def body761_23 : Prog (BitVec 64) :=
.seq body761_0 body761_22

def body761_24 : Prog (BitVec 64) :=
.decCall ("base") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body761_23

def body761_25 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body761_24

def body761_26 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body761_25

def body761_27 : Prog (BitVec 64) :=
.seq body761_0 body761_1

def body761_28 : Prog (BitVec 64) :=
.seq body761_2 body761_5

def body761_29 : Prog (BitVec 64) :=
.seq body761_28 body761_10

def body761_30 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body761_29

def body761_31 : Prog (BitVec 64) :=
.seq body761_30 body761_14

def body761_32 : Prog (BitVec 64) :=
.seq body761_31 body761_15

def body761_33 : Prog (BitVec 64) :=
.seq body761_32 body761_16

def body761_34 : Prog (BitVec 64) :=
.dec ("started") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body761_33

def body761_35 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 64#64]) body761_34

def body761_36 : Prog (BitVec 64) :=
.seq body761_27 body761_35

def body761_37 : Prog (BitVec 64) :=
.decCall ("base") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body761_36

def body761_38 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body761_37

def body761_39 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body761_38

def originalData761 : Decl (BitVec 64) :=
.function { name := "g1_mul", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("kptr", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body761_26, returnShape := (Flapjack.Shape.one) }
def simplifiedData761 : Decl (BitVec 64) :=
.function { name := "g1_mul", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("kptr", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body761_39, returnShape := (Flapjack.Shape.one) }
def original761 := Pancake.PanLang.declToHOL originalData761
def simplified761 := Pancake.PanLang.declToHOL simplifiedData761
end InitECandidate.Proofs.FrontendStages.Declarations
