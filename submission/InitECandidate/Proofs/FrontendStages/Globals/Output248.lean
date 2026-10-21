import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data248
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate225
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody248_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "i")

def globalBody248_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody248_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.loadByte
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "i"]))
  (Flapjack.Exp.loadByte
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "i"]))) globalBody248_0 globalBody248_1

def globalBody248_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody248_4 : Prog (BitVec 64) :=
.seq globalBody248_2 globalBody248_3

def globalBody248_5 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) globalBody248_4

def globalBody248_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "n")

def globalBody248_7 : Prog (BitVec 64) :=
.seq globalBody248_5 globalBody248_6

def globalBody248_8 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody248_7

def globalBody248_9 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.var Flapjack.VarKind.local "al", Flapjack.Exp.var Flapjack.VarKind.local "bl"]) globalBody248_8

def globalData248 : Decl (BitVec 64) :=
.function { name := "common_prefix_length", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("al", Flapjack.Shape.one), ("b", Flapjack.Shape.one), ("bl", Flapjack.Shape.one)], body := globalBody248_9, returnShape := (Flapjack.Shape.one) }
def globalOutput248 := Pancake.PanLang.declToHOL globalData248
end InitECandidate.Proofs.FrontendStages.Declarations
