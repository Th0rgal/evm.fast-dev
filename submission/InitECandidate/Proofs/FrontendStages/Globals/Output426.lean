import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data426
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate410
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody426_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody426_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody426_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "b"))
  (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "a"))) globalBody426_0 globalBody426_1

def globalBody426_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody426_4 : Prog (BitVec 64) :=
.seq globalBody426_2 globalBody426_3

def globalBody426_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "kind") (Flapjack.Exp.const 0#64)) globalBody426_4 globalBody426_1

def globalBody426_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "len" (Flapjack.Exp.const 32#64)

def globalBody426_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "kind") (Flapjack.Exp.const 2#64)) globalBody426_6 globalBody426_1

def globalBody426_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "cb")
  (Flapjack.Exp.var Flapjack.VarKind.local "ca")) globalBody426_0 globalBody426_1

def globalBody426_9 : Prog (BitVec 64) :=
.seq globalBody426_8 globalBody426_3

def globalBody426_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "ca")
  (Flapjack.Exp.var Flapjack.VarKind.local "cb")) globalBody426_9 globalBody426_1

def globalBody426_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64])

def globalBody426_12 : Prog (BitVec 64) :=
.seq globalBody426_10 globalBody426_11

def globalBody426_13 : Prog (BitVec 64) :=
.dec ("cb") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "k"])) globalBody426_12

def globalBody426_14 : Prog (BitVec 64) :=
.dec ("ca") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "k"])) globalBody426_13

def globalBody426_15 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "k")
  (Flapjack.Exp.var Flapjack.VarKind.local "len")) globalBody426_14

def globalBody426_16 : Prog (BitVec 64) :=
.seq globalBody426_15 globalBody426_3

def globalBody426_17 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody426_16

def globalBody426_18 : Prog (BitVec 64) :=
.seq globalBody426_7 globalBody426_17

def globalBody426_19 : Prog (BitVec 64) :=
.dec ("len") (Flapjack.Shape.one) (Flapjack.Exp.const 20#64) globalBody426_18

def globalBody426_20 : Prog (BitVec 64) :=
.seq globalBody426_5 globalBody426_19

def globalData426 : Decl (BitVec 64) :=
.function { name := "bal_sort_gt", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one), ("kind", Flapjack.Shape.one)], body := globalBody426_20, returnShape := (Flapjack.Shape.one) }
def globalOutput426 := Pancake.PanLang.declToHOL globalData426
end InitECandidate.Proofs.FrontendStages.Declarations
