import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data343
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate327
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody343_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 66#64)

def globalBody343_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody343_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 4294967295#64) (Flapjack.Exp.var Flapjack.VarKind.local "gas")) globalBody343_0 globalBody343_1

def globalBody343_3 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 60#64)

def globalBody343_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "gas")
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ic"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "ic")])) globalBody343_3 globalBody343_1

def globalBody343_5 : Prog (BitVec 64) :=
.seq globalBody343_2 globalBody343_4

def globalBody343_6 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 61#64)

def globalBody343_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "gas")
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "ic"))) globalBody343_6 globalBody343_1

def globalBody343_8 : Prog (BitVec 64) :=
.seq globalBody343_5 globalBody343_7

def globalBody343_9 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 62#64)

def globalBody343_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 131072#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 200#64]))) globalBody343_9 globalBody343_1

def globalBody343_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 152#64]))
  (Flapjack.Exp.const 0#64)) globalBody343_10 globalBody343_1

def globalBody343_12 : Prog (BitVec 64) :=
.seq globalBody343_8 globalBody343_11

def globalBody343_13 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 63#64)

def globalBody343_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 16777216#64)
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ic"))) globalBody343_13 globalBody343_1

def globalBody343_15 : Prog (BitVec 64) :=
.seq globalBody343_12 globalBody343_14

def globalBody343_16 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 64#64)

def globalBody343_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 16777216#64)
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "ic"))) globalBody343_16 globalBody343_1

def globalBody343_18 : Prog (BitVec 64) :=
.seq globalBody343_15 globalBody343_17

def globalBody343_19 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 65#64)

def globalBody343_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) globalBody343_19 globalBody343_1

def globalBody343_21 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "nonce"))
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 0#64, Flapjack.Exp.const 1#64])) globalBody343_19 globalBody343_1

def globalBody343_22 : Prog (BitVec 64) :=
.seq globalBody343_20 globalBody343_21

def globalBody343_23 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "ic")

def globalBody343_24 : Prog (BitVec 64) :=
.seq globalBody343_22 globalBody343_23

def globalBody343_25 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "nonce"]) globalBody343_24

def globalBody343_26 : Prog (BitVec 64) :=
.dec ("nonce") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 16#64])) globalBody343_25

def globalBody343_27 : Prog (BitVec 64) :=
.seq globalBody343_18 globalBody343_26

def globalBody343_28 : Prog (BitVec 64) :=
.dec ("gas") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 144#64])) globalBody343_27

def globalBody343_29 : Prog (BitVec 64) :=
.decCall ("ic") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_intrinsic_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "sender"]) globalBody343_28

def globalData343 : Decl (BitVec 64) :=
.function { name := "validate_transaction", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("sender", Flapjack.Shape.one)], body := globalBody343_29, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput343 := Pancake.PanLang.declToHOL globalData343
end InitECandidate.Proofs.FrontendStages.Declarations
