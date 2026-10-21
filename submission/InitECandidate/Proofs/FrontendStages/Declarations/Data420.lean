import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify404
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body420_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_le64"
  [Flapjack.Exp.var Flapjack.VarKind.local "kb", Flapjack.Exp.var Flapjack.VarKind.global "bal_index"]

def body420_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "kb", Flapjack.Exp.const 8#64],
    Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 20#64]

def body420_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "kb", Flapjack.Exp.const 28#64],
    Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.const 32#64]

def body420_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m")))

def body420_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body420_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "m"))
  (Flapjack.Exp.const 0#64)) body420_3 body420_4

def body420_6 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "rec") (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body420_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.global "bal_idx_stor", Flapjack.Exp.var Flapjack.VarKind.local "kb",
    Flapjack.Exp.var Flapjack.VarKind.local "rec"]

def body420_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body420_9 : Prog (BitVec 64) :=
.seq body420_7 body420_8

def body420_10 : Prog (BitVec 64) :=
.seq body420_2 body420_9

def body420_11 : Prog (BitVec 64) :=
.seq body420_1 body420_10

def body420_12 : Prog (BitVec 64) :=
.seq body420_0 body420_11

def body420_13 : Prog (BitVec 64) :=
.seq body420_6 body420_12

def body420_14 : Prog (BitVec 64) :=
.decCall ("rec") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body420_13

def body420_15 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("get_pre_tx_storage") ([Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body420_14

def body420_16 : Prog (BitVec 64) :=
.seq body420_5 body420_15

def body420_17 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.global "bal_idx_stor", Flapjack.Exp.var Flapjack.VarKind.local "kb"]) body420_16

def body420_18 : Prog (BitVec 64) :=
.seq body420_2 body420_17

def body420_19 : Prog (BitVec 64) :=
.seq body420_1 body420_18

def body420_20 : Prog (BitVec 64) :=
.seq body420_0 body420_19

def body420_21 : Prog (BitVec 64) :=
.dec ("kb") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "bal_key_buf") body420_20

def body420_22 : Prog (BitVec 64) :=
.seq body420_0 body420_1

def body420_23 : Prog (BitVec 64) :=
.seq body420_22 body420_2

def body420_24 : Prog (BitVec 64) :=
.seq body420_6 body420_0

def body420_25 : Prog (BitVec 64) :=
.seq body420_24 body420_1

def body420_26 : Prog (BitVec 64) :=
.seq body420_25 body420_2

def body420_27 : Prog (BitVec 64) :=
.seq body420_26 body420_7

def body420_28 : Prog (BitVec 64) :=
.seq body420_27 body420_8

def body420_29 : Prog (BitVec 64) :=
.decCall ("rec") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body420_28

def body420_30 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("get_pre_tx_storage") ([Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body420_29

def body420_31 : Prog (BitVec 64) :=
.seq body420_5 body420_30

def body420_32 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.global "bal_idx_stor", Flapjack.Exp.var Flapjack.VarKind.local "kb"]) body420_31

def body420_33 : Prog (BitVec 64) :=
.seq body420_23 body420_32

def body420_34 : Prog (BitVec 64) :=
.dec ("kb") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "bal_key_buf") body420_33

def originalData420 : Decl (BitVec 64) :=
.function { name := "idx_start_storage", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("key", Flapjack.Shape.one)], body := body420_21, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData420 : Decl (BitVec 64) :=
.function { name := "idx_start_storage", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("key", Flapjack.Shape.one)], body := body420_34, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original420 := Pancake.PanLang.declToHOL originalData420
def simplified420 := Pancake.PanLang.declToHOL simplifiedData420
end InitECandidate.Proofs.FrontendStages.Declarations
