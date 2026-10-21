import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data379
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate363
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody379_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody379_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody379_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m"), Flapjack.Exp.const 24#64]))) globalBody379_0 globalBody379_1

def globalBody379_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "m"))
  (Flapjack.Exp.const 0#64)) globalBody379_2 globalBody379_1

def globalBody379_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "m"), none)) "htab_get"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 176#64]),
          Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "addr"]

def globalBody379_5 : Prog (BitVec 64) :=
.seq globalBody379_3 globalBody379_4

def globalBody379_6 : Prog (BitVec 64) :=
.seq globalBody379_5 globalBody379_3

def globalBody379_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "record_pre_state_read" [Flapjack.Exp.var Flapjack.VarKind.local "addr"]

def globalBody379_8 : Prog (BitVec 64) :=
.seq globalBody379_6 globalBody379_7

def globalBody379_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "r")

def globalBody379_10 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.one) ("ws_account_has_storage") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody379_9

def globalBody379_11 : Prog (BitVec 64) :=
.seq globalBody379_8 globalBody379_10

def globalBody379_12 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 184#64]),
        Flapjack.Exp.const 32#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody379_11

def globalData379 : Decl (BitVec 64) :=
.function { name := "account_has_storage", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := globalBody379_12, returnShape := (Flapjack.Shape.one) }
def globalOutput379 := Pancake.PanLang.declToHOL globalData379
end InitECandidate.Proofs.FrontendStages.Declarations
