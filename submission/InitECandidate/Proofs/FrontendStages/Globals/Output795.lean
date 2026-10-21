import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data795
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate779
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody795_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_set_inf" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def globalBody795_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody795_2 : Prog (BitVec 64) :=
.seq globalBody795_0 globalBody795_1

def globalBody795_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody795_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 1#64)) globalBody795_2 globalBody795_3

def globalBody795_5 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("is_zero_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "bs", Flapjack.Exp.const 1#64],
  Flapjack.Exp.const 47#64]) globalBody795_4

def globalBody795_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "bs"))
  (Flapjack.Exp.const 192#64)) globalBody795_5 globalBody795_3

def globalBody795_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody795_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) globalBody795_7 globalBody795_3

def globalBody795_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "inf") (Flapjack.Exp.const 1#64)) globalBody795_7 globalBody795_3

def globalBody795_10 : Prog (BitVec 64) :=
Flapjack.Prog.call none "g1_subgroup_check" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def globalBody795_11 : Prog (BitVec 64) :=
.seq globalBody795_9 globalBody795_10

def globalBody795_12 : Prog (BitVec 64) :=
.decCall ("inf") (Flapjack.Shape.one) ("g1_is_inf") ([Flapjack.Exp.var Flapjack.VarKind.local "r"]) globalBody795_11

def globalBody795_13 : Prog (BitVec 64) :=
.seq globalBody795_8 globalBody795_12

def globalBody795_14 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("kzg_decompress_g1") ([Flapjack.Exp.var Flapjack.VarKind.local "bs", Flapjack.Exp.var Flapjack.VarKind.local "r"]) globalBody795_13

def globalBody795_15 : Prog (BitVec 64) :=
.seq globalBody795_6 globalBody795_14

def globalData795 : Decl (BitVec 64) :=
.function { name := "kzg_load_g1", inline := false, exported := false, params := [("bs", Flapjack.Shape.one), ("r", Flapjack.Shape.one)], body := globalBody795_15, returnShape := (Flapjack.Shape.one) }
def globalOutput795 := Pancake.PanLang.declToHOL globalData795
end InitECandidate.Proofs.FrontendStages.Declarations
