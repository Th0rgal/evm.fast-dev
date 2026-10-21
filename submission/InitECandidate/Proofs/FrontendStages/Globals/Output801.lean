import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data801
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate785
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody801_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "g2_decode"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 256#64],
    Flapjack.Exp.var Flapjack.VarKind.local "p2"]

def globalBody801_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody801_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 1#64)) globalBody801_0 globalBody801_1

def globalBody801_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody801_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody801_5 : Prog (BitVec 64) :=
.seq globalBody801_3 globalBody801_4

def globalBody801_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) globalBody801_5 globalBody801_1

def globalBody801_7 : Prog (BitVec 64) :=
.seq globalBody801_2 globalBody801_6

def globalBody801_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.var Flapjack.VarKind.local "p1",
    Flapjack.Exp.var Flapjack.VarKind.local "p2"]

def globalBody801_9 : Prog (BitVec 64) :=
.seq globalBody801_7 globalBody801_8

def globalBody801_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_encode"
  [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody801_11 : Prog (BitVec 64) :=
.seq globalBody801_9 globalBody801_10

def globalBody801_12 : Prog (BitVec 64) :=
.seq globalBody801_11 globalBody801_3

def globalBody801_13 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody801_14 : Prog (BitVec 64) :=
.seq globalBody801_12 globalBody801_13

def globalBody801_15 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g2_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "p1"]) globalBody801_14

def globalBody801_16 : Prog (BitVec 64) :=
.decCall ("p2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) globalBody801_15

def globalBody801_17 : Prog (BitVec 64) :=
.decCall ("p1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) globalBody801_16

def globalBody801_18 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody801_17

def globalData801 : Decl (BitVec 64) :=
.function { name := "bls_g2_add_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody801_18, returnShape := (Flapjack.Shape.one) }
def globalOutput801 := Pancake.PanLang.declToHOL globalData801
end InitECandidate.Proofs.FrontendStages.Declarations
