import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data625
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate602
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody625_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "mm", Flapjack.Exp.const 8#64]]

def globalBody625_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "r",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "mm", Flapjack.Exp.const 8#64]],
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "mm"],
        Flapjack.Exp.const 8#64]]

def globalBody625_2 : Prog (BitVec 64) :=
.seq globalBody625_0 globalBody625_1

def globalBody625_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody625_4 : Prog (BitVec 64) :=
.seq globalBody625_2 globalBody625_3

def globalBody625_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody625_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "mm")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) globalBody625_4 globalBody625_5

def globalBody625_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_divmnu"
  [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "mm",
    Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "un", Flapjack.Exp.var Flapjack.VarKind.local "vn"]

def globalBody625_8 : Prog (BitVec 64) :=
.seq globalBody625_6 globalBody625_7

def globalBody625_9 : Prog (BitVec 64) :=
.seq globalBody625_8 globalBody625_3

def globalBody625_10 : Prog (BitVec 64) :=
.decCall ("mm") (Flapjack.Shape.one) ("digits_len") ([Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "m"]) globalBody625_9

def globalData625 : Decl (BitVec 64) :=
.function { name := "bn_mod", inline := false, exported := false, params := [("u", Flapjack.Shape.one), ("m", Flapjack.Shape.one), ("v", Flapjack.Shape.one), ("n", Flapjack.Shape.one),
  ("r", Flapjack.Shape.one), ("q", Flapjack.Shape.one), ("un", Flapjack.Shape.one), ("vn", Flapjack.Shape.one)], body := globalBody625_10, returnShape := (Flapjack.Shape.one) }
def globalOutput625 := Pancake.PanLang.declToHOL globalData625
end InitECandidate.Proofs.FrontendStages.Declarations
