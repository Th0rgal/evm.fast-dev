import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify403
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body419_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_le64"
  [Flapjack.Exp.var Flapjack.VarKind.local "kb", Flapjack.Exp.var Flapjack.VarKind.global "bal_index"]

def body419_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "kb", Flapjack.Exp.const 8#64],
    Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 20#64]

def body419_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m"))

def body419_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body419_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "m"))
  (Flapjack.Exp.const 0#64)) body419_2 body419_3

def body419_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 80#64]

def body419_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 48#64],
    Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash", Flapjack.Exp.const 32#64]

def body419_7 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "rec") (Flapjack.Exp.const 1#64)

def body419_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 0#64]))

def body419_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 8#64]))

def body419_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 48#64],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.const 32#64]

def body419_11 : Prog (BitVec 64) :=
.seq body419_9 body419_10

def body419_12 : Prog (BitVec 64) :=
.seq body419_8 body419_11

def body419_13 : Prog (BitVec 64) :=
.seq body419_7 body419_12

def body419_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "pre") (Flapjack.Exp.const 1#64)) body419_13 body419_3

def body419_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.global "bal_idx_accts", Flapjack.Exp.var Flapjack.VarKind.local "kb",
    Flapjack.Exp.var Flapjack.VarKind.local "rec"]

def body419_16 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "rec")

def body419_17 : Prog (BitVec 64) :=
.seq body419_15 body419_16

def body419_18 : Prog (BitVec 64) :=
.seq body419_1 body419_17

def body419_19 : Prog (BitVec 64) :=
.seq body419_0 body419_18

def body419_20 : Prog (BitVec 64) :=
.seq body419_14 body419_19

def body419_21 : Prog (BitVec 64) :=
.seq body419_6 body419_20

def body419_22 : Prog (BitVec 64) :=
.seq body419_5 body419_21

def body419_23 : Prog (BitVec 64) :=
.decCall ("rec") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 80#64]) body419_22

def body419_24 : Prog (BitVec 64) :=
.decCall ("pre") (Flapjack.Shape.one) ("get_pre_tx_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body419_23

def body419_25 : Prog (BitVec 64) :=
.seq body419_4 body419_24

def body419_26 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.global "bal_idx_accts", Flapjack.Exp.var Flapjack.VarKind.local "kb"]) body419_25

def body419_27 : Prog (BitVec 64) :=
.seq body419_1 body419_26

def body419_28 : Prog (BitVec 64) :=
.seq body419_0 body419_27

def body419_29 : Prog (BitVec 64) :=
.dec ("kb") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "bal_key_buf") body419_28

def body419_30 : Prog (BitVec 64) :=
.seq body419_0 body419_1

def body419_31 : Prog (BitVec 64) :=
.seq body419_5 body419_6

def body419_32 : Prog (BitVec 64) :=
.seq body419_7 body419_8

def body419_33 : Prog (BitVec 64) :=
.seq body419_32 body419_9

def body419_34 : Prog (BitVec 64) :=
.seq body419_33 body419_10

def body419_35 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "pre") (Flapjack.Exp.const 1#64)) body419_34 body419_3

def body419_36 : Prog (BitVec 64) :=
.seq body419_31 body419_35

def body419_37 : Prog (BitVec 64) :=
.seq body419_36 body419_0

def body419_38 : Prog (BitVec 64) :=
.seq body419_37 body419_1

def body419_39 : Prog (BitVec 64) :=
.seq body419_38 body419_15

def body419_40 : Prog (BitVec 64) :=
.seq body419_39 body419_16

def body419_41 : Prog (BitVec 64) :=
.decCall ("rec") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 80#64]) body419_40

def body419_42 : Prog (BitVec 64) :=
.decCall ("pre") (Flapjack.Shape.one) ("get_pre_tx_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body419_41

def body419_43 : Prog (BitVec 64) :=
.seq body419_4 body419_42

def body419_44 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.global "bal_idx_accts", Flapjack.Exp.var Flapjack.VarKind.local "kb"]) body419_43

def body419_45 : Prog (BitVec 64) :=
.seq body419_30 body419_44

def body419_46 : Prog (BitVec 64) :=
.dec ("kb") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "bal_key_buf") body419_45

def originalData419 : Decl (BitVec 64) :=
.function { name := "idx_start_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body419_29, returnShape := (Flapjack.Shape.one) }
def simplifiedData419 : Decl (BitVec 64) :=
.function { name := "idx_start_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body419_46, returnShape := (Flapjack.Shape.one) }
def original419 := Pancake.PanLang.declToHOL originalData419
def simplified419 := Pancake.PanLang.declToHOL simplifiedData419
end InitECandidate.Proofs.FrontendStages.Declarations
