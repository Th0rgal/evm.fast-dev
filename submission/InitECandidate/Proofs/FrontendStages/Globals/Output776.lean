import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data776
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate760
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody776_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody776_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody776_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) globalBody776_0 globalBody776_1

def globalBody776_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "bls_fp_decode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 48#64]]

def globalBody776_4 : Prog (BitVec 64) :=
.seq globalBody776_2 globalBody776_3

def globalBody776_5 : Prog (BitVec 64) :=
.seq globalBody776_4 globalBody776_2

def globalBody776_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "bls_fp_decode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 128#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]]

def globalBody776_7 : Prog (BitVec 64) :=
.seq globalBody776_5 globalBody776_6

def globalBody776_8 : Prog (BitVec 64) :=
.seq globalBody776_7 globalBody776_2

def globalBody776_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "bls_fp_decode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64, Flapjack.Exp.const 48#64]]

def globalBody776_10 : Prog (BitVec 64) :=
.seq globalBody776_8 globalBody776_9

def globalBody776_11 : Prog (BitVec 64) :=
.seq globalBody776_10 globalBody776_2

def globalBody776_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64]]

def globalBody776_13 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody776_14 : Prog (BitVec 64) :=
.seq globalBody776_12 globalBody776_13

def globalBody776_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "xz") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "yz") (Flapjack.Exp.const 1#64))]) globalBody776_14 globalBody776_1

def globalBody776_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64]]

def globalBody776_17 : Prog (BitVec 64) :=
.seq globalBody776_15 globalBody776_16

def globalBody776_18 : Prog (BitVec 64) :=
Flapjack.Prog.call none "g2_on_curve"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]]

def globalBody776_19 : Prog (BitVec 64) :=
.seq globalBody776_17 globalBody776_18

def globalBody776_20 : Prog (BitVec 64) :=
.decCall ("yz") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]]) globalBody776_19

def globalBody776_21 : Prog (BitVec 64) :=
.decCall ("xz") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "r"]) globalBody776_20

def globalBody776_22 : Prog (BitVec 64) :=
.seq globalBody776_11 globalBody776_21

def globalBody776_23 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("bls_fp_decode64") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "r"]) globalBody776_22

def globalData776 : Decl (BitVec 64) :=
.function { name := "g2_decode", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("r", Flapjack.Shape.one)], body := globalBody776_23, returnShape := (Flapjack.Shape.one) }
def globalOutput776 := Pancake.PanLang.declToHOL globalData776
end InitECandidate.Proofs.FrontendStages.Declarations
