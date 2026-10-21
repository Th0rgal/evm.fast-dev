import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify559
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body575_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 104#64]

def body575_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "parent")

def body575_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "cur_cont")

def body575_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "kind")

def body575_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "msg")

def body575_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "ev" (Flapjack.Exp.var Flapjack.VarKind.local "child")

def body575_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "cur_cont" (Flapjack.Exp.var Flapjack.VarKind.local "rec")

def body575_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "child")

def body575_8 : Prog (BitVec 64) :=
.seq body575_6 body575_7

def body575_9 : Prog (BitVec 64) :=
.seq body575_5 body575_8

def body575_10 : Prog (BitVec 64) :=
.seq body575_4 body575_9

def body575_11 : Prog (BitVec 64) :=
.seq body575_3 body575_10

def body575_12 : Prog (BitVec 64) :=
.seq body575_2 body575_11

def body575_13 : Prog (BitVec 64) :=
.seq body575_1 body575_12

def body575_14 : Prog (BitVec 64) :=
.seq body575_0 body575_13

def body575_15 : Prog (BitVec 64) :=
.decCall ("rec") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 104#64]) body575_14

def body575_16 : Prog (BitVec 64) :=
.decCall ("child") (Flapjack.Shape.one) ("frame_new") ([Flapjack.Exp.var Flapjack.VarKind.local "msg"]) body575_15

def body575_17 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "ev") body575_16

def body575_18 : Prog (BitVec 64) :=
.seq body575_0 body575_1

def body575_19 : Prog (BitVec 64) :=
.seq body575_18 body575_2

def body575_20 : Prog (BitVec 64) :=
.seq body575_19 body575_3

def body575_21 : Prog (BitVec 64) :=
.seq body575_20 body575_4

def body575_22 : Prog (BitVec 64) :=
.seq body575_21 body575_5

def body575_23 : Prog (BitVec 64) :=
.seq body575_22 body575_6

def body575_24 : Prog (BitVec 64) :=
.seq body575_23 body575_7

def body575_25 : Prog (BitVec 64) :=
.decCall ("rec") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 104#64]) body575_24

def body575_26 : Prog (BitVec 64) :=
.decCall ("child") (Flapjack.Shape.one) ("frame_new") ([Flapjack.Exp.var Flapjack.VarKind.local "msg"]) body575_25

def body575_27 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "ev") body575_26

def originalData575 : Decl (BitVec 64) :=
.function { name := "frame_open", inline := false, exported := false, params := [("msg", Flapjack.Shape.one), ("kind", Flapjack.Shape.one)], body := body575_17, returnShape := (Flapjack.Shape.one) }
def simplifiedData575 : Decl (BitVec 64) :=
.function { name := "frame_open", inline := false, exported := false, params := [("msg", Flapjack.Shape.one), ("kind", Flapjack.Shape.one)], body := body575_27, returnShape := (Flapjack.Shape.one) }
def original575 := Pancake.PanLang.declToHOL originalData575
def simplified575 := Pancake.PanLang.declToHOL simplifiedData575
end InitECandidate.Proofs.FrontendStages.Declarations
