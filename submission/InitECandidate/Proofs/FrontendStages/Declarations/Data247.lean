import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify231
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body247_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "dst")
  (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 16#64, Flapjack.Exp.var Flapjack.VarKind.local "flag"])

def body247_1 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "dst")
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.const 16#64,
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "flag", Flapjack.Exp.const 1#64]],
      Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "nibs")])

def body247_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 1#64)

def body247_3 : Prog (BitVec 64) :=
.seq body247_1 body247_2

def body247_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 0#64)) body247_0 body247_3

def body247_5 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "o"])
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "nibs", Flapjack.Exp.var Flapjack.VarKind.local "i"]))
        (Flapjack.Exp.const 4#64),
      Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "nibs", Flapjack.Exp.var Flapjack.VarKind.local "i",
            Flapjack.Exp.const 1#64])])

def body247_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 2#64])

def body247_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "o"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o", Flapjack.Exp.const 1#64])

def body247_8 : Prog (BitVec 64) :=
.seq body247_6 body247_7

def body247_9 : Prog (BitVec 64) :=
.seq body247_5 body247_8

def body247_10 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body247_9

def body247_11 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "o")

def body247_12 : Prog (BitVec 64) :=
.seq body247_10 body247_11

def body247_13 : Prog (BitVec 64) :=
.dec ("o") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body247_12

def body247_14 : Prog (BitVec 64) :=
.seq body247_4 body247_13

def body247_15 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body247_14

def body247_16 : Prog (BitVec 64) :=
.dec ("flag") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "is_leaf", Flapjack.Exp.const 2#64]) body247_15

def body247_17 : Prog (BitVec 64) :=
.seq body247_5 body247_6

def body247_18 : Prog (BitVec 64) :=
.seq body247_17 body247_7

def body247_19 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body247_18

def body247_20 : Prog (BitVec 64) :=
.seq body247_19 body247_11

def body247_21 : Prog (BitVec 64) :=
.dec ("o") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body247_20

def body247_22 : Prog (BitVec 64) :=
.seq body247_4 body247_21

def body247_23 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body247_22

def body247_24 : Prog (BitVec 64) :=
.dec ("flag") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "is_leaf", Flapjack.Exp.const 2#64]) body247_23

def originalData247 : Decl (BitVec 64) :=
.function { name := "nibble_list_to_compact", inline := false, exported := false, params := [("nibs", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("is_leaf", Flapjack.Shape.one), ("dst", Flapjack.Shape.one)], body := body247_16, returnShape := (Flapjack.Shape.one) }
def simplifiedData247 : Decl (BitVec 64) :=
.function { name := "nibble_list_to_compact", inline := false, exported := false, params := [("nibs", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("is_leaf", Flapjack.Shape.one), ("dst", Flapjack.Shape.one)], body := body247_24, returnShape := (Flapjack.Shape.one) }
def original247 := Pancake.PanLang.declToHOL originalData247
def simplified247 := Pancake.PanLang.declToHOL simplifiedData247
end InitECandidate.Proofs.FrontendStages.Declarations
