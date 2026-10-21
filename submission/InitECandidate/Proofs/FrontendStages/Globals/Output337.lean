import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data337
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate321
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody337_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody337_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 46#64)

def globalBody337_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody337_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) globalBody337_1 globalBody337_2

def globalBody337_4 : Prog (BitVec 64) :=
.seq globalBody337_0 globalBody337_3

def globalBody337_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody337_6 : Prog (BitVec 64) :=
.seq globalBody337_4 globalBody337_5

def globalBody337_7 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("secp256k1_recover") ([Flapjack.Exp.var Flapjack.VarKind.local "h",
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 320#64]),
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 352#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "recid", Flapjack.Exp.var Flapjack.VarKind.local "out64"]) globalBody337_6

def globalBody337_8 : Prog (BitVec 64) :=
.decCall ("recid") (Flapjack.Shape.one) ("signature_recovery_parameters") ([Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "chain_id",
  Flapjack.Exp.var Flapjack.VarKind.local "h"]) globalBody337_7

def globalBody337_9 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody337_8

def globalBody337_10 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody337_9

def globalData337 : Decl (BitVec 64) :=
.function { name := "recover_transaction_public_key", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one), ("out64", Flapjack.Shape.one)], body := globalBody337_10, returnShape := (Flapjack.Shape.one) }
def globalOutput337 := Pancake.PanLang.declToHOL globalData337
end InitECandidate.Proofs.FrontendStages.Declarations
