import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify394
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body410_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.var Flapjack.VarKind.local "esz"]])

def body410_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body410_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]))
  (Flapjack.Exp.var Flapjack.VarKind.local "idx")) body410_0 body410_1

def body410_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body410_4 : Prog (BitVec 64) :=
.seq body410_2 body410_3

def body410_5 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body410_4

def body410_6 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "e") (Flapjack.Exp.var Flapjack.VarKind.local "idx")

def body410_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "e")

def body410_8 : Prog (BitVec 64) :=
.seq body410_6 body410_7

def body410_9 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("lst_push") ([Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body410_8

def body410_10 : Prog (BitVec 64) :=
.seq body410_5 body410_9

def body410_11 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body410_10

def body410_12 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 0#64])) body410_11

def body410_13 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 8#64])) body410_12

def originalData410 : Decl (BitVec 64) :=
.function { name := "lst_upsert_idx", inline := false, exported := false, params := [("l", Flapjack.Shape.one), ("esz", Flapjack.Shape.one), ("idx", Flapjack.Shape.one)], body := body410_13, returnShape := (Flapjack.Shape.one) }
def simplifiedData410 : Decl (BitVec 64) :=
.function { name := "lst_upsert_idx", inline := false, exported := false, params := [("l", Flapjack.Shape.one), ("esz", Flapjack.Shape.one), ("idx", Flapjack.Shape.one)], body := body410_13, returnShape := (Flapjack.Shape.one) }
def original410 := Pancake.PanLang.declToHOL originalData410
def simplified410 := Pancake.PanLang.declToHOL simplifiedData410
end InitECandidate.Proofs.FrontendStages.Declarations
