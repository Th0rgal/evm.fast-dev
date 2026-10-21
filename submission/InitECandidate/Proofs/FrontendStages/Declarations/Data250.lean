import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify234
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body250_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cap"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "cap", Flapjack.Exp.const 2#64])

def body250_1 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "cap")
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "n"],
      Flapjack.Exp.const 2#64])) body250_0

def body250_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "slice_arr",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "slice_arr",
          Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
          Flapjack.Exp.const 8#64]),
    Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch"]

def body250_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "slice_arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]]

def body250_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body250_5 : Prog (BitVec 64) :=
.seq body250_3 body250_4

def body250_6 : Prog (BitVec 64) :=
.seq body250_2 body250_5

def body250_7 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body250_6

def body250_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body250_9 : Prog (BitVec 64) :=
.seq body250_7 body250_8

def body250_10 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body250_9

def body250_11 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "cap"]) body250_10

def body250_12 : Prog (BitVec 64) :=
.seq body250_1 body250_11

def body250_13 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.const 4#64) body250_12

def body250_14 : Prog (BitVec 64) :=
.seq body250_2 body250_3

def body250_15 : Prog (BitVec 64) :=
.seq body250_14 body250_4

def body250_16 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body250_15

def body250_17 : Prog (BitVec 64) :=
.seq body250_16 body250_8

def body250_18 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body250_17

def body250_19 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "cap"]) body250_18

def body250_20 : Prog (BitVec 64) :=
.seq body250_1 body250_19

def body250_21 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.const 4#64) body250_20

def originalData250 : Decl (BitVec 64) :=
.function { name := "nodedb_build", inline := false, exported := false, params := [("slice_arr", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body250_13, returnShape := (Flapjack.Shape.one) }
def simplifiedData250 : Decl (BitVec 64) :=
.function { name := "nodedb_build", inline := false, exported := false, params := [("slice_arr", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body250_21, returnShape := (Flapjack.Shape.one) }
def original250 := Pancake.PanLang.declToHOL originalData250
def simplified250 := Pancake.PanLang.declToHOL simplifiedData250
end InitECandidate.Proofs.FrontendStages.Declarations
