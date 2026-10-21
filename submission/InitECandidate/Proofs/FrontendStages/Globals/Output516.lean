import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data516
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate500
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody516_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.const 145#64],
      Flapjack.Exp.const 255#64])

def globalBody516_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody516_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 90#64) (Flapjack.Exp.var Flapjack.VarKind.local "x"),
      Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "x") (Flapjack.Exp.const 128#64)])) globalBody516_0 globalBody516_1

def globalBody516_3 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 10#64)

def globalBody516_4 : Prog (BitVec 64) :=
.seq globalBody516_2 globalBody516_3

def globalBody516_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody516_6 : Prog (BitVec 64) :=
.seq globalBody516_4 globalBody516_5

def globalData516 : Decl (BitVec 64) :=
.function { name := "decode_single", inline := false, exported := false, params := [("x", Flapjack.Shape.one)], body := globalBody516_6, returnShape := (Flapjack.Shape.one) }
def globalOutput516 := Pancake.PanLang.declToHOL globalData516
end InitECandidate.Proofs.FrontendStages.Declarations
