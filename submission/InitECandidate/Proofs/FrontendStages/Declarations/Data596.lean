import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify580
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body596_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "require_not_static" []

def body596_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "cost"]

def body596_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "extend_memory"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "x")]

def body596_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "compute_contract_address"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 0#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "ca"]

def body596_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body596_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body596_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "started") (Flapjack.Exp.const 0#64)) body596_4 body596_5

def body596_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body596_8 : Prog (BitVec 64) :=
.seq body596_6 body596_7

def body596_9 : Prog (BitVec 64) :=
.decCall ("started") (Flapjack.Shape.one) ("generic_create") ([Flapjack.Exp.var Flapjack.VarKind.local "endowment", Flapjack.Exp.var Flapjack.VarKind.local "ca",
  Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.var Flapjack.VarKind.local "n"]) body596_8

def body596_10 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "mstart"]) body596_9

def body596_11 : Prog (BitVec 64) :=
.seq body596_3 body596_10

def body596_12 : Prog (BitVec 64) :=
.decCall ("ca") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body596_11

def body596_13 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])]) body596_12

def body596_14 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body596_13

def body596_15 : Prog (BitVec 64) :=
.seq body596_2 body596_14

def body596_16 : Prog (BitVec 64) :=
.seq body596_1 body596_15

def body596_17 : Prog (BitVec 64) :=
.decCall ("cost") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.const 12000#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "w"]],
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) body596_16

def body596_18 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) body596_17

def body596_19 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost1") ([Flapjack.Exp.var Flapjack.VarKind.local "mstart", Flapjack.Exp.var Flapjack.VarKind.local "msize"]) body596_18

def body596_20 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "msize"]) body596_19

def body596_21 : Prog (BitVec 64) :=
.decCall ("msize") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body596_20

def body596_22 : Prog (BitVec 64) :=
.decCall ("mstart") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body596_21

def body596_23 : Prog (BitVec 64) :=
.decCall ("endowment") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body596_22

def body596_24 : Prog (BitVec 64) :=
.seq body596_0 body596_23

def body596_25 : Prog (BitVec 64) :=
.seq body596_1 body596_2

def body596_26 : Prog (BitVec 64) :=
.seq body596_25 body596_14

def body596_27 : Prog (BitVec 64) :=
.decCall ("cost") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.const 12000#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "w"]],
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) body596_26

def body596_28 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) body596_27

def body596_29 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost1") ([Flapjack.Exp.var Flapjack.VarKind.local "mstart", Flapjack.Exp.var Flapjack.VarKind.local "msize"]) body596_28

def body596_30 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "msize"]) body596_29

def body596_31 : Prog (BitVec 64) :=
.decCall ("msize") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body596_30

def body596_32 : Prog (BitVec 64) :=
.decCall ("mstart") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body596_31

def body596_33 : Prog (BitVec 64) :=
.decCall ("endowment") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body596_32

def body596_34 : Prog (BitVec 64) :=
.seq body596_0 body596_33

def originalData596 : Decl (BitVec 64) :=
.function { name := "op_create", inline := false, exported := false, params := [], body := body596_24, returnShape := (Flapjack.Shape.one) }
def simplifiedData596 : Decl (BitVec 64) :=
.function { name := "op_create", inline := false, exported := false, params := [], body := body596_34, returnShape := (Flapjack.Shape.one) }
def original596 := Pancake.PanLang.declToHOL originalData596
def simplified596 := Pancake.PanLang.declToHOL simplifiedData596
end InitECandidate.Proofs.FrontendStages.Declarations
