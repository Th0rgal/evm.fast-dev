import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data819
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate802
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody819_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody819_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody819_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) globalBody819_0 globalBody819_1

def globalBody819_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 18#64)

def globalBody819_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "lo") (Flapjack.Exp.const 0#64)) globalBody819_3 globalBody819_1

def globalBody819_5 : Prog (BitVec 64) :=
.seq globalBody819_4 globalBody819_0

def globalBody819_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "hi") (Flapjack.Exp.const 1#64)) globalBody819_5 globalBody819_1

def globalBody819_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "hi") (Flapjack.Exp.const 0#64)) globalBody819_0 globalBody819_1

def globalBody819_8 : Prog (BitVec 64) :=
.seq globalBody819_6 globalBody819_7

def globalBody819_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "lo")

def globalBody819_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "lo") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 17#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "lo"))]) globalBody819_9 globalBody819_1

def globalBody819_11 : Prog (BitVec 64) :=
.seq globalBody819_8 globalBody819_10

def globalBody819_12 : Prog (BitVec 64) :=
.seq globalBody819_11 globalBody819_0

def globalBody819_13 : Prog (BitVec 64) :=
.dec ("lo") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 19#64])) globalBody819_12

def globalBody819_14 : Prog (BitVec 64) :=
.dec ("hi") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 18#64])) globalBody819_13

def globalBody819_15 : Prog (BitVec 64) :=
.seq globalBody819_2 globalBody819_14

def globalBody819_16 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("is_zero_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 18#64]) globalBody819_15

def globalData819 : Decl (BitVec 64) :=
.function { name := "precompile_index", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := globalBody819_16, returnShape := (Flapjack.Shape.one) }
def globalOutput819 := Pancake.PanLang.declToHOL globalData819
end InitECandidate.Proofs.FrontendStages.Declarations
