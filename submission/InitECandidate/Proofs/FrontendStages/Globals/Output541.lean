import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data541
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate525
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody541_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.const 100#64]]

def globalBody541_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_after_charge"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "c"]

def globalBody541_2 : Prog (BitVec 64) :=
.seq globalBody541_0 globalBody541_1

def globalBody541_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code")]

def globalBody541_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody541_5 : Prog (BitVec 64) :=
.seq globalBody541_3 globalBody541_4

def globalBody541_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody541_7 : Prog (BitVec 64) :=
.seq globalBody541_5 globalBody541_6

def globalBody541_8 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody541_7

def globalBody541_9 : Prog (BitVec 64) :=
.seq globalBody541_2 globalBody541_8

def globalBody541_10 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.one) ("access_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody541_9

def globalBody541_11 : Prog (BitVec 64) :=
.decCall ("addr") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "av"]) globalBody541_10

def globalBody541_12 : Prog (BitVec 64) :=
.decCall ("av") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody541_11

def globalData541 : Decl (BitVec 64) :=
.function { name := "op_extcodesize", inline := false, exported := false, params := [], body := globalBody541_12, returnShape := (Flapjack.Shape.one) }
def globalOutput541 := Pancake.PanLang.declToHOL globalData541
end InitECandidate.Proofs.FrontendStages.Declarations
