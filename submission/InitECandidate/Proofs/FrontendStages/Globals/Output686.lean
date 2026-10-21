import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data686
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate670
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody686_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody686_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody686_2 : Prog (BitVec 64) :=
.seq globalBody686_0 globalBody686_1

def globalBody686_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody686_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "e0") (Flapjack.Exp.const 0#64)) globalBody686_2 globalBody686_3

def globalBody686_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "e1") (Flapjack.Exp.const 0#64)) globalBody686_2 globalBody686_3

def globalBody686_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_add"
  [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "p0", Flapjack.Exp.var Flapjack.VarKind.local "p0",
    Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def globalBody686_7 : Prog (BitVec 64) :=
.seq globalBody686_5 globalBody686_6

def globalBody686_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn254_g1_to_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p0", Flapjack.Exp.var Flapjack.VarKind.local "out64"]

def globalBody686_9 : Prog (BitVec 64) :=
.seq globalBody686_7 globalBody686_8

def globalBody686_10 : Prog (BitVec 64) :=
.seq globalBody686_9 globalBody686_0

def globalBody686_11 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody686_12 : Prog (BitVec 64) :=
.seq globalBody686_10 globalBody686_11

def globalBody686_13 : Prog (BitVec 64) :=
.decCall ("e1") (Flapjack.Shape.one) ("bn254_parse_g1") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "in128", Flapjack.Exp.const 64#64],
  Flapjack.Exp.var Flapjack.VarKind.local "p1"]) globalBody686_12

def globalBody686_14 : Prog (BitVec 64) :=
.seq globalBody686_4 globalBody686_13

def globalBody686_15 : Prog (BitVec 64) :=
.decCall ("e0") (Flapjack.Shape.one) ("bn254_parse_g1") ([Flapjack.Exp.var Flapjack.VarKind.local "in128", Flapjack.Exp.var Flapjack.VarKind.local "p0"]) globalBody686_14

def globalBody686_16 : Prog (BitVec 64) :=
.decCall ("p1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) globalBody686_15

def globalBody686_17 : Prog (BitVec 64) :=
.decCall ("p0") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) globalBody686_16

def globalBody686_18 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody686_17

def globalData686 : Decl (BitVec 64) :=
.function { name := "bn254_g1_add", inline := false, exported := false, params := [("in128", Flapjack.Shape.one), ("out64", Flapjack.Shape.one)], body := globalBody686_18, returnShape := (Flapjack.Shape.one) }
def globalOutput686 := Pancake.PanLang.declToHOL globalData686
end InitECandidate.Proofs.FrontendStages.Declarations
