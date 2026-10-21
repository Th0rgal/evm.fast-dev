import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data774
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate758
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody774_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64]

def globalBody774_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody774_2 : Prog (BitVec 64) :=
.seq globalBody774_0 globalBody774_1

def globalBody774_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody774_4 : Prog (BitVec 64) :=
.seq globalBody774_2 globalBody774_3

def globalBody774_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody774_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "inf") (Flapjack.Exp.const 1#64)) globalBody774_4 globalBody774_5

def globalBody774_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_inv"
  [Flapjack.Exp.var Flapjack.VarKind.local "zi",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 192#64]]

def globalBody774_8 : Prog (BitVec 64) :=
.seq globalBody774_6 globalBody774_7

def globalBody774_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.var Flapjack.VarKind.local "zi"]

def globalBody774_10 : Prog (BitVec 64) :=
.seq globalBody774_8 globalBody774_9

def globalBody774_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "zi"]

def globalBody774_12 : Prog (BitVec 64) :=
.seq globalBody774_10 globalBody774_11

def globalBody774_13 : Prog (BitVec 64) :=
.seq globalBody774_12 globalBody774_1

def globalBody774_14 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody774_15 : Prog (BitVec 64) :=
.seq globalBody774_13 globalBody774_14

def globalBody774_16 : Prog (BitVec 64) :=
.decCall ("inf") (Flapjack.Shape.one) ("g2_is_inf") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) globalBody774_15

def globalBody774_17 : Prog (BitVec 64) :=
.decCall ("zi") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) globalBody774_16

def globalBody774_18 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody774_17

def globalData774 : Decl (BitVec 64) :=
.function { name := "g2_normalize", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := globalBody774_18, returnShape := (Flapjack.Shape.one) }
def globalOutput774 := Pancake.PanLang.declToHOL globalData774
end InitECandidate.Proofs.FrontendStages.Declarations
