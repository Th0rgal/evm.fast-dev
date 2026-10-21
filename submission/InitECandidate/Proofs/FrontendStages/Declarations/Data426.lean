import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify410
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body426_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body426_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body426_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "b"))
  (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "a"))) body426_0 body426_1

def body426_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body426_4 : Prog (BitVec 64) :=
.seq body426_2 body426_3

def body426_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "kind") (Flapjack.Exp.const 0#64)) body426_4 body426_1

def body426_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "len" (Flapjack.Exp.const 32#64)

def body426_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "kind") (Flapjack.Exp.const 2#64)) body426_6 body426_1

def body426_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "cb")
  (Flapjack.Exp.var Flapjack.VarKind.local "ca")) body426_0 body426_1

def body426_9 : Prog (BitVec 64) :=
.seq body426_8 body426_3

def body426_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "ca")
  (Flapjack.Exp.var Flapjack.VarKind.local "cb")) body426_9 body426_1

def body426_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64])

def body426_12 : Prog (BitVec 64) :=
.seq body426_10 body426_11

def body426_13 : Prog (BitVec 64) :=
.dec ("cb") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "k"])) body426_12

def body426_14 : Prog (BitVec 64) :=
.dec ("ca") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "k"])) body426_13

def body426_15 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "k")
  (Flapjack.Exp.var Flapjack.VarKind.local "len")) body426_14

def body426_16 : Prog (BitVec 64) :=
.seq body426_15 body426_3

def body426_17 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body426_16

def body426_18 : Prog (BitVec 64) :=
.seq body426_7 body426_17

def body426_19 : Prog (BitVec 64) :=
.dec ("len") (Flapjack.Shape.one) (Flapjack.Exp.const 20#64) body426_18

def body426_20 : Prog (BitVec 64) :=
.seq body426_5 body426_19

def originalData426 : Decl (BitVec 64) :=
.function { name := "bal_sort_gt", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one), ("kind", Flapjack.Shape.one)], body := body426_20, returnShape := (Flapjack.Shape.one) }
def simplifiedData426 : Decl (BitVec 64) :=
.function { name := "bal_sort_gt", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one), ("kind", Flapjack.Shape.one)], body := body426_20, returnShape := (Flapjack.Shape.one) }
def original426 := Pancake.PanLang.declToHOL originalData426
def simplified426 := Pancake.PanLang.declToHOL simplifiedData426
end InitECandidate.Proofs.FrontendStages.Declarations
