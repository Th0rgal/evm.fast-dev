import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify443
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body459_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "avail"
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "buf_len", Flapjack.Exp.var Flapjack.VarKind.local "start"])

def body459_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "avail" (Flapjack.Exp.var Flapjack.VarKind.local "size")

def body459_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body459_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "size")
  (Flapjack.Exp.var Flapjack.VarKind.local "avail")) body459_1 body459_2

def body459_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.var Flapjack.VarKind.local "start"],
    Flapjack.Exp.var Flapjack.VarKind.local "avail"]

def body459_5 : Prog (BitVec 64) :=
.seq body459_3 body459_4

def body459_6 : Prog (BitVec 64) :=
.seq body459_0 body459_5

def body459_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "start")
  (Flapjack.Exp.var Flapjack.VarKind.local "buf_len")) body459_6 body459_2

def body459_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "avail"],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "size", Flapjack.Exp.var Flapjack.VarKind.local "avail"]]

def body459_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body459_10 : Prog (BitVec 64) :=
.seq body459_8 body459_9

def body459_11 : Prog (BitVec 64) :=
.seq body459_7 body459_10

def body459_12 : Prog (BitVec 64) :=
.dec ("avail") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body459_11

def body459_13 : Prog (BitVec 64) :=
.seq body459_0 body459_3

def body459_14 : Prog (BitVec 64) :=
.seq body459_13 body459_4

def body459_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "start")
  (Flapjack.Exp.var Flapjack.VarKind.local "buf_len")) body459_14 body459_2

def body459_16 : Prog (BitVec 64) :=
.seq body459_15 body459_8

def body459_17 : Prog (BitVec 64) :=
.seq body459_16 body459_9

def body459_18 : Prog (BitVec 64) :=
.dec ("avail") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body459_17

def originalData459 : Decl (BitVec 64) :=
.function { name := "buffer_read", inline := false, exported := false, params := [("buf", Flapjack.Shape.one), ("buf_len", Flapjack.Shape.one), ("start", Flapjack.Shape.one),
  ("size", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body459_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData459 : Decl (BitVec 64) :=
.function { name := "buffer_read", inline := false, exported := false, params := [("buf", Flapjack.Shape.one), ("buf_len", Flapjack.Shape.one), ("start", Flapjack.Shape.one),
  ("size", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body459_18, returnShape := (Flapjack.Shape.one) }
def original459 := Pancake.PanLang.declToHOL originalData459
def simplified459 := Pancake.PanLang.declToHOL simplifiedData459
end InitECandidate.Proofs.FrontendStages.Declarations
