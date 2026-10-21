import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify573
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body589_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "incorporate_child_on_error" [Flapjack.Exp.var Flapjack.VarKind.local "child"]

def body589_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64]),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 192#64])])

def body589_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "rep"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64]))

def body589_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body589_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64]))
  (Flapjack.Exp.var Flapjack.VarKind.local "rep")) body589_2 body589_3

def body589_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "rep"])

def body589_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "rep"])

def body589_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "rep"])

def body589_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "log_append"
  [Flapjack.Exp.var Flapjack.VarKind.global "ev",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "p",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])]

def body589_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body589_10 : Prog (BitVec 64) :=
.seq body589_8 body589_9

def body589_11 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body589_10

def body589_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 96#64]),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 96#64])])

def body589_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_union_into"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 136#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 136#64])]

def body589_14 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body589_15 : Prog (BitVec 64) :=
.seq body589_13 body589_14

def body589_16 : Prog (BitVec 64) :=
.seq body589_12 body589_15

def body589_17 : Prog (BitVec 64) :=
.seq body589_11 body589_16

def body589_18 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body589_17

def body589_19 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cl", Flapjack.Exp.const 0#64])) body589_18

def body589_20 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cl", Flapjack.Exp.const 8#64])) body589_19

def body589_21 : Prog (BitVec 64) :=
.dec ("cl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 88#64])) body589_20

def body589_22 : Prog (BitVec 64) :=
.seq body589_7 body589_21

def body589_23 : Prog (BitVec 64) :=
.seq body589_6 body589_22

def body589_24 : Prog (BitVec 64) :=
.seq body589_5 body589_23

def body589_25 : Prog (BitVec 64) :=
.seq body589_4 body589_24

def body589_26 : Prog (BitVec 64) :=
.dec ("rep") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])) body589_25

def body589_27 : Prog (BitVec 64) :=
.seq body589_1 body589_26

def body589_28 : Prog (BitVec 64) :=
.seq body589_0 body589_27

def body589_29 : Prog (BitVec 64) :=
.seq body589_0 body589_1

def body589_30 : Prog (BitVec 64) :=
.seq body589_4 body589_5

def body589_31 : Prog (BitVec 64) :=
.seq body589_30 body589_6

def body589_32 : Prog (BitVec 64) :=
.seq body589_31 body589_7

def body589_33 : Prog (BitVec 64) :=
.seq body589_11 body589_12

def body589_34 : Prog (BitVec 64) :=
.seq body589_33 body589_13

def body589_35 : Prog (BitVec 64) :=
.seq body589_34 body589_14

def body589_36 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body589_35

def body589_37 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cl", Flapjack.Exp.const 0#64])) body589_36

def body589_38 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cl", Flapjack.Exp.const 8#64])) body589_37

def body589_39 : Prog (BitVec 64) :=
.dec ("cl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 88#64])) body589_38

def body589_40 : Prog (BitVec 64) :=
.seq body589_32 body589_39

def body589_41 : Prog (BitVec 64) :=
.dec ("rep") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])) body589_40

def body589_42 : Prog (BitVec 64) :=
.seq body589_29 body589_41

def originalData589 : Decl (BitVec 64) :=
.function { name := "incorporate_child_on_success", inline := false, exported := false, params := [("child", Flapjack.Shape.one)], body := body589_28, returnShape := (Flapjack.Shape.one) }
def simplifiedData589 : Decl (BitVec 64) :=
.function { name := "incorporate_child_on_success", inline := false, exported := false, params := [("child", Flapjack.Shape.one)], body := body589_42, returnShape := (Flapjack.Shape.one) }
def original589 := Pancake.PanLang.declToHOL originalData589
def simplified589 := Pancake.PanLang.declToHOL simplifiedData589
end InitECandidate.Proofs.FrontendStages.Declarations
