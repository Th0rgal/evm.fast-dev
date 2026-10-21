import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data371
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate355
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody371_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 184#64]),
          Flapjack.Exp.const 8#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 1#64]

def globalBody371_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "w"))

def globalBody371_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody371_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "w"))
  (Flapjack.Exp.const 0#64)) globalBody371_1 globalBody371_2

def globalBody371_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def globalBody371_5 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_pre_state_account_optional") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody371_4

def globalBody371_6 : Prog (BitVec 64) :=
.seq globalBody371_3 globalBody371_5

def globalBody371_7 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 184#64]),
        Flapjack.Exp.const 16#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody371_6

def globalBody371_8 : Prog (BitVec 64) :=
.seq globalBody371_0 globalBody371_7

def globalData371 : Decl (BitVec 64) :=
.function { name := "get_account_optional", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := globalBody371_8, returnShape := (Flapjack.Shape.one) }
def globalOutput371 := Pancake.PanLang.declToHOL globalData371
end InitECandidate.Proofs.FrontendStages.Declarations
