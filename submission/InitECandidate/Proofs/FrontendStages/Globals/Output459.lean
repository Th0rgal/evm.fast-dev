import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data459
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate443
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody459_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "avail"
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "buf_len", Flapjack.Exp.var Flapjack.VarKind.local "start"])

def globalBody459_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "avail" (Flapjack.Exp.var Flapjack.VarKind.local "size")

def globalBody459_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody459_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "size")
  (Flapjack.Exp.var Flapjack.VarKind.local "avail")) globalBody459_1 globalBody459_2

def globalBody459_4 : Prog (BitVec 64) :=
.seq globalBody459_0 globalBody459_3

def globalBody459_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.var Flapjack.VarKind.local "start"],
    Flapjack.Exp.var Flapjack.VarKind.local "avail"]

def globalBody459_6 : Prog (BitVec 64) :=
.seq globalBody459_4 globalBody459_5

def globalBody459_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "start")
  (Flapjack.Exp.var Flapjack.VarKind.local "buf_len")) globalBody459_6 globalBody459_2

def globalBody459_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "avail"],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "size", Flapjack.Exp.var Flapjack.VarKind.local "avail"]]

def globalBody459_9 : Prog (BitVec 64) :=
.seq globalBody459_7 globalBody459_8

def globalBody459_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody459_11 : Prog (BitVec 64) :=
.seq globalBody459_9 globalBody459_10

def globalBody459_12 : Prog (BitVec 64) :=
.dec ("avail") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody459_11

def globalData459 : Decl (BitVec 64) :=
.function { name := "buffer_read", inline := false, exported := false, params := [("buf", Flapjack.Shape.one), ("buf_len", Flapjack.Shape.one), ("start", Flapjack.Shape.one),
  ("size", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody459_12, returnShape := (Flapjack.Shape.one) }
def globalOutput459 := Pancake.PanLang.declToHOL globalData459
end InitECandidate.Proofs.FrontendStages.Declarations
