import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify407
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body423_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body423_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body423_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "m"))
  (Flapjack.Exp.const 0#64)) body423_0 body423_1

def body423_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sl"))
  (Flapjack.Exp.const 0#64)) body423_0 body423_1

def body423_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bal_list_remove_idx"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sl"), Flapjack.Exp.const 40#64,
    Flapjack.Exp.var Flapjack.VarKind.local "idx"]

def body423_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_del"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "slot"]

def body423_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sl"), Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 0#64)) body423_5 body423_1

def body423_7 : Prog (BitVec 64) :=
.seq body423_6 body423_0

def body423_8 : Prog (BitVec 64) :=
.seq body423_4 body423_7

def body423_9 : Prog (BitVec 64) :=
.seq body423_3 body423_8

def body423_10 : Prog (BitVec 64) :=
.decCall ("sl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "slot"]) body423_9

def body423_11 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m"), Flapjack.Exp.const 0#64])) body423_10

def body423_12 : Prog (BitVec 64) :=
.seq body423_2 body423_11

def body423_13 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.global "bal_accounts", Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body423_12

def body423_14 : Prog (BitVec 64) :=
.seq body423_3 body423_4

def body423_15 : Prog (BitVec 64) :=
.seq body423_14 body423_6

def body423_16 : Prog (BitVec 64) :=
.seq body423_15 body423_0

def body423_17 : Prog (BitVec 64) :=
.decCall ("sl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "slot"]) body423_16

def body423_18 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m"), Flapjack.Exp.const 0#64])) body423_17

def body423_19 : Prog (BitVec 64) :=
.seq body423_2 body423_18

def body423_20 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.global "bal_accounts", Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body423_19

def originalData423 : Decl (BitVec 64) :=
.function { name := "remove_storage_write", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("slot", Flapjack.Shape.one), ("idx", Flapjack.Shape.one)], body := body423_13, returnShape := (Flapjack.Shape.one) }
def simplifiedData423 : Decl (BitVec 64) :=
.function { name := "remove_storage_write", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("slot", Flapjack.Shape.one), ("idx", Flapjack.Shape.one)], body := body423_20, returnShape := (Flapjack.Shape.one) }
def original423 := Pancake.PanLang.declToHOL originalData423
def simplified423 := Pancake.PanLang.declToHOL simplifiedData423
end InitECandidate.Proofs.FrontendStages.Declarations
