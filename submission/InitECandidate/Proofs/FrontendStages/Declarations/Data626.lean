import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify610
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body626_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.sub
                [Flapjack.Exp.op Flapjack.BinOp.sub
                    [Flapjack.Exp.var Flapjack.VarKind.local "nbytes", Flapjack.Exp.const 1#64],
                  Flapjack.Exp.var Flapjack.VarKind.local "i"],
              Flapjack.Exp.const 8#64],
          Flapjack.Exp.var Flapjack.VarKind.local "bl"],
      Flapjack.Exp.const 1#64])

def body626_1 : Prog (BitVec 64) :=
.decCall ("bl") (Flapjack.Shape.one) ("bit_length64") ([Flapjack.Exp.var Flapjack.VarKind.local "b"]) body626_0

def body626_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body626_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "b") (Flapjack.Exp.const 0#64)) body626_1 body626_2

def body626_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body626_5 : Prog (BitVec 64) :=
.seq body626_3 body626_4

def body626_6 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "i"])) body626_5

def body626_7 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nbytes")) body626_6

def body626_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 0#64, Flapjack.Exp.const 1#64])

def body626_9 : Prog (BitVec 64) :=
.seq body626_7 body626_8

def body626_10 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body626_9

def originalData626 : Decl (BitVec 64) :=
.function { name := "be_top_bit", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("nbytes", Flapjack.Shape.one)], body := body626_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData626 : Decl (BitVec 64) :=
.function { name := "be_top_bit", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("nbytes", Flapjack.Shape.one)], body := body626_10, returnShape := (Flapjack.Shape.one) }
def original626 := Pancake.PanLang.declToHOL originalData626
def simplified626 := Pancake.PanLang.declToHOL simplifiedData626
end InitECandidate.Proofs.FrontendStages.Declarations
