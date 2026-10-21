import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data513
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate497
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody513_0 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pa") (Flapjack.Exp.var Flapjack.VarKind.local "b")

def globalBody513_1 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pb") (Flapjack.Exp.var Flapjack.VarKind.local "a")

def globalBody513_2 : Prog (BitVec 64) :=
.seq globalBody513_0 globalBody513_1

def globalBody513_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody513_4 : Prog (BitVec 64) :=
.seq globalBody513_2 globalBody513_3

def globalBody513_5 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pb")) globalBody513_4

def globalBody513_6 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pa")) globalBody513_5

def globalBody513_7 : Prog (BitVec 64) :=
.dec ("pb") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "stk",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 1#64],
            Flapjack.Exp.var Flapjack.VarKind.local "j"],
        Flapjack.Exp.const 32#64]]) globalBody513_6

def globalBody513_8 : Prog (BitVec 64) :=
.dec ("pa") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "stk",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 1#64],
            Flapjack.Exp.var Flapjack.VarKind.local "i"],
        Flapjack.Exp.const 32#64]]) globalBody513_7

def globalBody513_9 : Prog (BitVec 64) :=
.dec ("stk") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 8#64])) globalBody513_8

def globalBody513_10 : Prog (BitVec 64) :=
.dec ("sp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 16#64])) globalBody513_9

def globalData513 : Decl (BitVec 64) :=
.function { name := "stack_swap_positions", inline := false, exported := false, params := [("i", Flapjack.Shape.one), ("j", Flapjack.Shape.one)], body := globalBody513_10, returnShape := (Flapjack.Shape.one) }
def globalOutput513 := Pancake.PanLang.declToHOL globalData513
end InitECandidate.Proofs.FrontendStages.Declarations
