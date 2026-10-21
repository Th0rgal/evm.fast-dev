import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify609
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body625_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "mm", Flapjack.Exp.const 8#64]]

def body625_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "r",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "mm", Flapjack.Exp.const 8#64]],
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "mm"],
        Flapjack.Exp.const 8#64]]

def body625_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body625_3 : Prog (BitVec 64) :=
.seq body625_1 body625_2

def body625_4 : Prog (BitVec 64) :=
.seq body625_0 body625_3

def body625_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body625_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "mm")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body625_4 body625_5

def body625_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_divmnu"
  [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "mm",
    Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "un", Flapjack.Exp.var Flapjack.VarKind.local "vn"]

def body625_8 : Prog (BitVec 64) :=
.seq body625_7 body625_2

def body625_9 : Prog (BitVec 64) :=
.seq body625_6 body625_8

def body625_10 : Prog (BitVec 64) :=
.decCall ("mm") (Flapjack.Shape.one) ("digits_len") ([Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "m"]) body625_9

def body625_11 : Prog (BitVec 64) :=
.seq body625_0 body625_1

def body625_12 : Prog (BitVec 64) :=
.seq body625_11 body625_2

def body625_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "mm")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body625_12 body625_5

def body625_14 : Prog (BitVec 64) :=
.seq body625_13 body625_7

def body625_15 : Prog (BitVec 64) :=
.seq body625_14 body625_2

def body625_16 : Prog (BitVec 64) :=
.decCall ("mm") (Flapjack.Shape.one) ("digits_len") ([Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "m"]) body625_15

def originalData625 : Decl (BitVec 64) :=
.function { name := "bn_mod", inline := false, exported := false, params := [("u", Flapjack.Shape.one), ("m", Flapjack.Shape.one), ("v", Flapjack.Shape.one), ("n", Flapjack.Shape.one),
  ("r", Flapjack.Shape.one), ("q", Flapjack.Shape.one), ("un", Flapjack.Shape.one), ("vn", Flapjack.Shape.one)], body := body625_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData625 : Decl (BitVec 64) :=
.function { name := "bn_mod", inline := false, exported := false, params := [("u", Flapjack.Shape.one), ("m", Flapjack.Shape.one), ("v", Flapjack.Shape.one), ("n", Flapjack.Shape.one),
  ("r", Flapjack.Shape.one), ("q", Flapjack.Shape.one), ("un", Flapjack.Shape.one), ("vn", Flapjack.Shape.one)], body := body625_16, returnShape := (Flapjack.Shape.one) }
def original625 := Pancake.PanLang.declToHOL originalData625
def simplified625 := Pancake.PanLang.declToHOL simplifiedData625
end InitECandidate.Proofs.FrontendStages.Declarations
