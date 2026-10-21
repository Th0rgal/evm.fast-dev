import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data283
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate267
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody283_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "fb" (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "p"))

def globalBody283_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody283_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "n")) globalBody283_0 globalBody283_1

def globalBody283_3 : Prog (BitVec 64) :=
Flapjack.Prog.call none "rlp_bytes_encoded_len"
  [Flapjack.Exp.var Flapjack.VarKind.local "fb", Flapjack.Exp.var Flapjack.VarKind.local "n"]

def globalBody283_4 : Prog (BitVec 64) :=
.seq globalBody283_2 globalBody283_3

def globalBody283_5 : Prog (BitVec 64) :=
.dec ("fb") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody283_4

def globalData283 : Decl (BitVec 64) :=
.function { name := "rlp_value_encoded_len", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := globalBody283_5, returnShape := (Flapjack.Shape.one) }
def globalOutput283 := Pancake.PanLang.declToHOL globalData283
end InitECandidate.Proofs.FrontendStages.Declarations
