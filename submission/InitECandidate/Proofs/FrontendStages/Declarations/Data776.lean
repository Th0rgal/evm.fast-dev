import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify760
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body776_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body776_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body776_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body776_0 body776_1

def body776_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "bls_fp_decode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 48#64]]

def body776_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "bls_fp_decode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 128#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]]

def body776_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "bls_fp_decode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64, Flapjack.Exp.const 48#64]]

def body776_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64]]

def body776_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body776_8 : Prog (BitVec 64) :=
.seq body776_6 body776_7

def body776_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "xz") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "yz") (Flapjack.Exp.const 1#64))]) body776_8 body776_1

def body776_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64]]

def body776_11 : Prog (BitVec 64) :=
Flapjack.Prog.call none "g2_on_curve"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]]

def body776_12 : Prog (BitVec 64) :=
.seq body776_10 body776_11

def body776_13 : Prog (BitVec 64) :=
.seq body776_9 body776_12

def body776_14 : Prog (BitVec 64) :=
.decCall ("yz") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]]) body776_13

def body776_15 : Prog (BitVec 64) :=
.decCall ("xz") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "r"]) body776_14

def body776_16 : Prog (BitVec 64) :=
.seq body776_2 body776_15

def body776_17 : Prog (BitVec 64) :=
.seq body776_5 body776_16

def body776_18 : Prog (BitVec 64) :=
.seq body776_2 body776_17

def body776_19 : Prog (BitVec 64) :=
.seq body776_4 body776_18

def body776_20 : Prog (BitVec 64) :=
.seq body776_2 body776_19

def body776_21 : Prog (BitVec 64) :=
.seq body776_3 body776_20

def body776_22 : Prog (BitVec 64) :=
.seq body776_2 body776_21

def body776_23 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("bls_fp_decode64") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "r"]) body776_22

def body776_24 : Prog (BitVec 64) :=
.seq body776_2 body776_3

def body776_25 : Prog (BitVec 64) :=
.seq body776_24 body776_2

def body776_26 : Prog (BitVec 64) :=
.seq body776_25 body776_4

def body776_27 : Prog (BitVec 64) :=
.seq body776_26 body776_2

def body776_28 : Prog (BitVec 64) :=
.seq body776_27 body776_5

def body776_29 : Prog (BitVec 64) :=
.seq body776_28 body776_2

def body776_30 : Prog (BitVec 64) :=
.seq body776_9 body776_10

def body776_31 : Prog (BitVec 64) :=
.seq body776_30 body776_11

def body776_32 : Prog (BitVec 64) :=
.decCall ("yz") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]]) body776_31

def body776_33 : Prog (BitVec 64) :=
.decCall ("xz") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "r"]) body776_32

def body776_34 : Prog (BitVec 64) :=
.seq body776_29 body776_33

def body776_35 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("bls_fp_decode64") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "r"]) body776_34

def originalData776 : Decl (BitVec 64) :=
.function { name := "g2_decode", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("r", Flapjack.Shape.one)], body := body776_23, returnShape := (Flapjack.Shape.one) }
def simplifiedData776 : Decl (BitVec 64) :=
.function { name := "g2_decode", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("r", Flapjack.Shape.one)], body := body776_35, returnShape := (Flapjack.Shape.one) }
def original776 := Pancake.PanLang.declToHOL originalData776
def simplified776 := Pancake.PanLang.declToHOL simplifiedData776
end InitECandidate.Proofs.FrontendStages.Declarations
