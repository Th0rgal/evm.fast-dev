import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data777
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate761
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody777_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_normalize"
  [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def globalBody777_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_fp_encode64"
  [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody777_2 : Prog (BitVec 64) :=
.seq globalBody777_0 globalBody777_1

def globalBody777_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_fp_encode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.const 48#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64]]

def globalBody777_4 : Prog (BitVec 64) :=
.seq globalBody777_2 globalBody777_3

def globalBody777_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_fp_encode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 128#64]]

def globalBody777_6 : Prog (BitVec 64) :=
.seq globalBody777_4 globalBody777_5

def globalBody777_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_fp_encode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.const 144#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 192#64]]

def globalBody777_8 : Prog (BitVec 64) :=
.seq globalBody777_6 globalBody777_7

def globalBody777_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody777_10 : Prog (BitVec 64) :=
.seq globalBody777_8 globalBody777_9

def globalBody777_11 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody777_12 : Prog (BitVec 64) :=
.seq globalBody777_10 globalBody777_11

def globalBody777_13 : Prog (BitVec 64) :=
.decCall ("aff") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 192#64]) globalBody777_12

def globalBody777_14 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody777_13

def globalData777 : Decl (BitVec 64) :=
.function { name := "g2_encode", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody777_14, returnShape := (Flapjack.Shape.one) }
def globalOutput777 := Pancake.PanLang.declToHOL globalData777
end InitECandidate.Proofs.FrontendStages.Declarations
