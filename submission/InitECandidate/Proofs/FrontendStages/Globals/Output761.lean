import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data761
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate745
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody761_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "base", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def globalBody761_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_set_inf" [Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def globalBody761_2 : Prog (BitVec 64) :=
.seq globalBody761_0 globalBody761_1

def globalBody761_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody761_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_double"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def globalBody761_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody761_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "started") (Flapjack.Exp.const 1#64)) globalBody761_4 globalBody761_5

def globalBody761_7 : Prog (BitVec 64) :=
.seq globalBody761_3 globalBody761_6

def globalBody761_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc",
    Flapjack.Exp.var Flapjack.VarKind.local "base"]

def globalBody761_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "started" (Flapjack.Exp.const 1#64)

def globalBody761_10 : Prog (BitVec 64) :=
.seq globalBody761_8 globalBody761_9

def globalBody761_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "bit") (Flapjack.Exp.const 1#64)) globalBody761_10 globalBody761_5

def globalBody761_12 : Prog (BitVec 64) :=
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
    Flapjack.Exp.const 1#64]) globalBody761_11

def globalBody761_13 : Prog (BitVec 64) :=
.seq globalBody761_7 globalBody761_12

def globalBody761_14 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) globalBody761_13

def globalBody761_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def globalBody761_16 : Prog (BitVec 64) :=
.seq globalBody761_14 globalBody761_15

def globalBody761_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody761_18 : Prog (BitVec 64) :=
.seq globalBody761_16 globalBody761_17

def globalBody761_19 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody761_20 : Prog (BitVec 64) :=
.seq globalBody761_18 globalBody761_19

def globalBody761_21 : Prog (BitVec 64) :=
.dec ("started") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody761_20

def globalBody761_22 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 64#64]) globalBody761_21

def globalBody761_23 : Prog (BitVec 64) :=
.seq globalBody761_2 globalBody761_22

def globalBody761_24 : Prog (BitVec 64) :=
.decCall ("base") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) globalBody761_23

def globalBody761_25 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) globalBody761_24

def globalBody761_26 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody761_25

def globalData761 : Decl (BitVec 64) :=
.function { name := "g1_mul", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("kptr", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := globalBody761_26, returnShape := (Flapjack.Shape.one) }
def globalOutput761 := Pancake.PanLang.declToHOL globalData761
end InitECandidate.Proofs.FrontendStages.Declarations
