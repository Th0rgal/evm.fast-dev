import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify327
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body343_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 66#64)

def body343_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body343_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 4294967295#64) (Flapjack.Exp.var Flapjack.VarKind.local "gas")) body343_0 body343_1

def body343_3 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 60#64)

def body343_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "gas")
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ic"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "ic")])) body343_3 body343_1

def body343_5 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 61#64)

def body343_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "gas")
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "ic"))) body343_5 body343_1

def body343_7 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 62#64)

def body343_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 131072#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 200#64]))) body343_7 body343_1

def body343_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 152#64]))
  (Flapjack.Exp.const 0#64)) body343_8 body343_1

def body343_10 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 63#64)

def body343_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 16777216#64)
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ic"))) body343_10 body343_1

def body343_12 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 64#64)

def body343_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 16777216#64)
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "ic"))) body343_12 body343_1

def body343_14 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 65#64)

def body343_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) body343_14 body343_1

def body343_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "nonce"))
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 0#64, Flapjack.Exp.const 1#64])) body343_14 body343_1

def body343_17 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "ic")

def body343_18 : Prog (BitVec 64) :=
.seq body343_16 body343_17

def body343_19 : Prog (BitVec 64) :=
.seq body343_15 body343_18

def body343_20 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "nonce"]) body343_19

def body343_21 : Prog (BitVec 64) :=
.dec ("nonce") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 16#64])) body343_20

def body343_22 : Prog (BitVec 64) :=
.seq body343_13 body343_21

def body343_23 : Prog (BitVec 64) :=
.seq body343_11 body343_22

def body343_24 : Prog (BitVec 64) :=
.seq body343_9 body343_23

def body343_25 : Prog (BitVec 64) :=
.seq body343_6 body343_24

def body343_26 : Prog (BitVec 64) :=
.seq body343_4 body343_25

def body343_27 : Prog (BitVec 64) :=
.seq body343_2 body343_26

def body343_28 : Prog (BitVec 64) :=
.dec ("gas") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 144#64])) body343_27

def body343_29 : Prog (BitVec 64) :=
.decCall ("ic") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_intrinsic_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body343_28

def body343_30 : Prog (BitVec 64) :=
.seq body343_2 body343_4

def body343_31 : Prog (BitVec 64) :=
.seq body343_30 body343_6

def body343_32 : Prog (BitVec 64) :=
.seq body343_31 body343_9

def body343_33 : Prog (BitVec 64) :=
.seq body343_32 body343_11

def body343_34 : Prog (BitVec 64) :=
.seq body343_33 body343_13

def body343_35 : Prog (BitVec 64) :=
.seq body343_15 body343_16

def body343_36 : Prog (BitVec 64) :=
.seq body343_35 body343_17

def body343_37 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "nonce"]) body343_36

def body343_38 : Prog (BitVec 64) :=
.dec ("nonce") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 16#64])) body343_37

def body343_39 : Prog (BitVec 64) :=
.seq body343_34 body343_38

def body343_40 : Prog (BitVec 64) :=
.dec ("gas") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 144#64])) body343_39

def body343_41 : Prog (BitVec 64) :=
.decCall ("ic") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_intrinsic_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body343_40

def originalData343 : Decl (BitVec 64) :=
.function { name := "validate_transaction", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("sender", Flapjack.Shape.one)], body := body343_29, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData343 : Decl (BitVec 64) :=
.function { name := "validate_transaction", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("sender", Flapjack.Shape.one)], body := body343_41, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original343 := Pancake.PanLang.declToHOL originalData343
def simplified343 := Pancake.PanLang.declToHOL simplifiedData343
end InitECandidate.Proofs.FrontendStages.Declarations
