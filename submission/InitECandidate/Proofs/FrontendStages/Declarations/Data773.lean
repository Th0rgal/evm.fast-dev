import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify757
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body773_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_set_inf" [Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body773_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body773_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_double"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body773_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body773_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "started") (Flapjack.Exp.const 1#64)) body773_2 body773_3

def body773_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc",
    Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body773_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "started" (Flapjack.Exp.const 1#64)

def body773_7 : Prog (BitVec 64) :=
.seq body773_5 body773_6

def body773_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "bit") (Flapjack.Exp.const 1#64)) body773_7 body773_3

def body773_9 : Prog (BitVec 64) :=
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
    Flapjack.Exp.const 1#64]) body773_8

def body773_10 : Prog (BitVec 64) :=
.seq body773_4 body773_9

def body773_11 : Prog (BitVec 64) :=
.seq body773_1 body773_10

def body773_12 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body773_11

def body773_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body773_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body773_15 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body773_16 : Prog (BitVec 64) :=
.seq body773_14 body773_15

def body773_17 : Prog (BitVec 64) :=
.seq body773_13 body773_16

def body773_18 : Prog (BitVec 64) :=
.seq body773_12 body773_17

def body773_19 : Prog (BitVec 64) :=
.dec ("started") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body773_18

def body773_20 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 64#64]) body773_19

def body773_21 : Prog (BitVec 64) :=
.seq body773_0 body773_20

def body773_22 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body773_21

def body773_23 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body773_22

def body773_24 : Prog (BitVec 64) :=
.seq body773_1 body773_4

def body773_25 : Prog (BitVec 64) :=
.seq body773_24 body773_9

def body773_26 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body773_25

def body773_27 : Prog (BitVec 64) :=
.seq body773_26 body773_13

def body773_28 : Prog (BitVec 64) :=
.seq body773_27 body773_14

def body773_29 : Prog (BitVec 64) :=
.seq body773_28 body773_15

def body773_30 : Prog (BitVec 64) :=
.dec ("started") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body773_29

def body773_31 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 64#64]) body773_30

def body773_32 : Prog (BitVec 64) :=
.seq body773_0 body773_31

def body773_33 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body773_32

def body773_34 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body773_33

def originalData773 : Decl (BitVec 64) :=
.function { name := "g2_mul", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("kptr", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body773_23, returnShape := (Flapjack.Shape.one) }
def simplifiedData773 : Decl (BitVec 64) :=
.function { name := "g2_mul", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("kptr", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body773_34, returnShape := (Flapjack.Shape.one) }
def original773 := Pancake.PanLang.declToHOL originalData773
def simplified773 := Pancake.PanLang.declToHOL simplifiedData773
end InitECandidate.Proofs.FrontendStages.Declarations
