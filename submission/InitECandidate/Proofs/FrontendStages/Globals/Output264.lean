import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data264
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate248
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody264_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "key_to_nibbles"
  [Flapjack.Exp.var Flapjack.VarKind.local "key_hash32", Flapjack.Exp.const 32#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 144#64])]

def globalBody264_1 : Prog (BitVec 64) :=
Flapjack.Prog.call none "trie_walk"
  [Flapjack.Exp.var Flapjack.VarKind.local "root",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 144#64]),
    Flapjack.Exp.const 64#64]

def globalBody264_2 : Prog (BitVec 64) :=
.seq globalBody264_0 globalBody264_1

def globalData264 : Decl (BitVec 64) :=
.function { name := "trie_lookup", inline := false, exported := false, params := [("root", Flapjack.Shape.one), ("key_hash32", Flapjack.Shape.one)], body := globalBody264_2, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput264 := Pancake.PanLang.declToHOL globalData264
end InitECandidate.Proofs.FrontendStages.Declarations
