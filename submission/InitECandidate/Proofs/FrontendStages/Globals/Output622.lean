import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data622
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate599
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody622_0 : Prog (BitVec 64) :=
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

def globalBody622_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody622_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 2#64))
  (Flapjack.Exp.var Flapjack.VarKind.local "nd")) globalBody622_0 globalBody622_1

def globalBody622_3 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "i"])
  (Flapjack.Exp.var Flapjack.VarKind.local "byte")

def globalBody622_4 : Prog (BitVec 64) :=
.seq globalBody622_2 globalBody622_3

def globalBody622_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody622_6 : Prog (BitVec 64) :=
.seq globalBody622_4 globalBody622_5

def globalBody622_7 : Prog (BitVec 64) :=
.dec ("byte") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody622_6

def globalBody622_8 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "nbytes", Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "i"]) globalBody622_7

def globalBody622_9 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nbytes")) globalBody622_8

def globalBody622_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody622_11 : Prog (BitVec 64) :=
.seq globalBody622_9 globalBody622_10

def globalBody622_12 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody622_11

def globalData622 : Decl (BitVec 64) :=
.function { name := "bn_to_be", inline := false, exported := false, params := [("d", Flapjack.Shape.one), ("nd", Flapjack.Shape.one), ("out", Flapjack.Shape.one), ("nbytes", Flapjack.Shape.one)], body := globalBody622_12, returnShape := (Flapjack.Shape.one) }
def globalOutput622 := Pancake.PanLang.declToHOL globalData622
end InitECandidate.Proofs.FrontendStages.Declarations
