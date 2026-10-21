import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify606
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body622_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "byte"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr
        (Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "d",
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "k")
                    (Flapjack.Exp.const 2#64),
                  Flapjack.Exp.const 8#64]]))
        (Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 3#64],
            Flapjack.Exp.const 8#64]),
      Flapjack.Exp.const 255#64])

def body622_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body622_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 2#64))
  (Flapjack.Exp.var Flapjack.VarKind.local "nd")) body622_0 body622_1

def body622_3 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "i"])
  (Flapjack.Exp.var Flapjack.VarKind.local "byte")

def body622_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body622_5 : Prog (BitVec 64) :=
.seq body622_3 body622_4

def body622_6 : Prog (BitVec 64) :=
.seq body622_2 body622_5

def body622_7 : Prog (BitVec 64) :=
.dec ("byte") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body622_6

def body622_8 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "nbytes", Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "i"]) body622_7

def body622_9 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nbytes")) body622_8

def body622_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body622_11 : Prog (BitVec 64) :=
.seq body622_9 body622_10

def body622_12 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body622_11

def body622_13 : Prog (BitVec 64) :=
.seq body622_2 body622_3

def body622_14 : Prog (BitVec 64) :=
.seq body622_13 body622_4

def body622_15 : Prog (BitVec 64) :=
.dec ("byte") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body622_14

def body622_16 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "nbytes", Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "i"]) body622_15

def body622_17 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nbytes")) body622_16

def body622_18 : Prog (BitVec 64) :=
.seq body622_17 body622_10

def body622_19 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body622_18

def originalData622 : Decl (BitVec 64) :=
.function { name := "bn_to_be", inline := false, exported := false, params := [("d", Flapjack.Shape.one), ("nd", Flapjack.Shape.one), ("out", Flapjack.Shape.one), ("nbytes", Flapjack.Shape.one)], body := body622_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData622 : Decl (BitVec 64) :=
.function { name := "bn_to_be", inline := false, exported := false, params := [("d", Flapjack.Shape.one), ("nd", Flapjack.Shape.one), ("out", Flapjack.Shape.one), ("nbytes", Flapjack.Shape.one)], body := body622_19, returnShape := (Flapjack.Shape.one) }
def original622 := Pancake.PanLang.declToHOL originalData622
def simplified622 := Pancake.PanLang.declToHOL simplifiedData622
end InitECandidate.Proofs.FrontendStages.Declarations
