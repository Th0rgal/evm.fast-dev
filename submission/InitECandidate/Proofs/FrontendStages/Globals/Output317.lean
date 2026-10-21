import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data317
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate301
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody317_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "dst") (Flapjack.Exp.const 128#64)

def globalBody317_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody317_2 : Prog (BitVec 64) :=
.seq globalBody317_0 globalBody317_1

def globalBody317_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody317_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "to") (Flapjack.Exp.const 0#64)) globalBody317_2 globalBody317_3

def globalBody317_5 : Prog (BitVec 64) :=
Flapjack.Prog.call none "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "to",
    Flapjack.Exp.const 20#64]

def globalBody317_6 : Prog (BitVec 64) :=
.seq globalBody317_4 globalBody317_5

def globalData317 : Decl (BitVec 64) :=
.function { name := "tx_put_to", inline := false, exported := false, params := [("dst", Flapjack.Shape.one), ("to", Flapjack.Shape.one)], body := globalBody317_6, returnShape := (Flapjack.Shape.one) }
def globalOutput317 := Pancake.PanLang.declToHOL globalData317
end InitECandidate.Proofs.FrontendStages.Declarations
