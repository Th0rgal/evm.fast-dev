import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify857
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body873_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "blob")
  (Flapjack.Exp.var Flapjack.VarKind.local "type_byte")

def body873_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "blob", Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body873_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 56#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 16#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "blob")

def body873_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 56#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 1#64])

def body873_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64])

def body873_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body873_6 : Prog (BitVec 64) :=
.seq body873_4 body873_5

def body873_7 : Prog (BitVec 64) :=
.seq body873_3 body873_6

def body873_8 : Prog (BitVec 64) :=
.seq body873_2 body873_7

def body873_9 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 64#64])) body873_8

def body873_10 : Prog (BitVec 64) :=
.seq body873_1 body873_9

def body873_11 : Prog (BitVec 64) :=
.seq body873_0 body873_10

def body873_12 : Prog (BitVec 64) :=
.decCall ("blob") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) body873_11

def body873_13 : Prog (BitVec 64) :=
.seq body873_0 body873_1

def body873_14 : Prog (BitVec 64) :=
.seq body873_2 body873_3

def body873_15 : Prog (BitVec 64) :=
.seq body873_14 body873_4

def body873_16 : Prog (BitVec 64) :=
.seq body873_15 body873_5

def body873_17 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 64#64])) body873_16

def body873_18 : Prog (BitVec 64) :=
.seq body873_13 body873_17

def body873_19 : Prog (BitVec 64) :=
.decCall ("blob") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) body873_18

def originalData873 : Decl (BitVec 64) :=
.function { name := "requests_append", inline := false, exported := false, params := [("type_byte", Flapjack.Shape.one), ("data", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body873_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData873 : Decl (BitVec 64) :=
.function { name := "requests_append", inline := false, exported := false, params := [("type_byte", Flapjack.Shape.one), ("data", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body873_19, returnShape := (Flapjack.Shape.one) }
def original873 := Pancake.PanLang.declToHOL originalData873
def simplified873 := Pancake.PanLang.declToHOL simplifiedData873
end InitECandidate.Proofs.FrontendStages.Declarations
