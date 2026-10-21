import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify393
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body409_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m"))

def body409_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body409_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "m"))
  (Flapjack.Exp.const 0#64)) body409_0 body409_1

def body409_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body409_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 32#64, Flapjack.Exp.const 8#64]

def body409_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body409_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "l")

def body409_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "l"), none)) "lst_new"
  [Flapjack.Exp.const 16#64, Flapjack.Exp.const 4#64]

def body409_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "l")

def body409_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "l"), none)) "lst_new"
  [Flapjack.Exp.const 24#64, Flapjack.Exp.const 2#64]

def body409_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "l")

def body409_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.global "bal_accounts", Flapjack.Exp.var Flapjack.VarKind.local "addr",
    Flapjack.Exp.var Flapjack.VarKind.local "ad"]

def body409_12 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "ad")

def body409_13 : Prog (BitVec 64) :=
.seq body409_11 body409_12

def body409_14 : Prog (BitVec 64) :=
.seq body409_10 body409_13

def body409_15 : Prog (BitVec 64) :=
.seq body409_9 body409_14

def body409_16 : Prog (BitVec 64) :=
.seq body409_8 body409_15

def body409_17 : Prog (BitVec 64) :=
.seq body409_7 body409_16

def body409_18 : Prog (BitVec 64) :=
.seq body409_6 body409_17

def body409_19 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.one) ("lst_new") ([Flapjack.Exp.const 40#64, Flapjack.Exp.const 4#64]) body409_18

def body409_20 : Prog (BitVec 64) :=
.seq body409_5 body409_19

def body409_21 : Prog (BitVec 64) :=
.seq body409_4 body409_20

def body409_22 : Prog (BitVec 64) :=
.seq body409_3 body409_21

def body409_23 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 32#64, Flapjack.Exp.const 8#64]) body409_22

def body409_24 : Prog (BitVec 64) :=
.decCall ("ad") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 40#64]) body409_23

def body409_25 : Prog (BitVec 64) :=
.seq body409_2 body409_24

def body409_26 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.global "bal_accounts", Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body409_25

def body409_27 : Prog (BitVec 64) :=
.seq body409_3 body409_4

def body409_28 : Prog (BitVec 64) :=
.seq body409_27 body409_5

def body409_29 : Prog (BitVec 64) :=
.seq body409_6 body409_7

def body409_30 : Prog (BitVec 64) :=
.seq body409_29 body409_8

def body409_31 : Prog (BitVec 64) :=
.seq body409_30 body409_9

def body409_32 : Prog (BitVec 64) :=
.seq body409_31 body409_10

def body409_33 : Prog (BitVec 64) :=
.seq body409_32 body409_11

def body409_34 : Prog (BitVec 64) :=
.seq body409_33 body409_12

def body409_35 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.one) ("lst_new") ([Flapjack.Exp.const 40#64, Flapjack.Exp.const 4#64]) body409_34

def body409_36 : Prog (BitVec 64) :=
.seq body409_28 body409_35

def body409_37 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 32#64, Flapjack.Exp.const 8#64]) body409_36

def body409_38 : Prog (BitVec 64) :=
.decCall ("ad") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 40#64]) body409_37

def body409_39 : Prog (BitVec 64) :=
.seq body409_2 body409_38

def body409_40 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.global "bal_accounts", Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body409_39

def originalData409 : Decl (BitVec 64) :=
.function { name := "bal_ensure_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body409_26, returnShape := (Flapjack.Shape.one) }
def simplifiedData409 : Decl (BitVec 64) :=
.function { name := "bal_ensure_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body409_40, returnShape := (Flapjack.Shape.one) }
def original409 := Pancake.PanLang.declToHOL originalData409
def simplified409 := Pancake.PanLang.declToHOL simplifiedData409
end InitECandidate.Proofs.FrontendStages.Declarations
