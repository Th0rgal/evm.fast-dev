import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify526
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body542_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "cost"]

def body542_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_after_charge"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body542_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "extend_memory"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "x")]

def body542_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
    Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 24#64]),
        Flapjack.Exp.var Flapjack.VarKind.local "ms"]]

def body542_4 : Prog (BitVec 64) :=
.decCall ("cs") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "cstart"]) body542_3

def body542_5 : Prog (BitVec 64) :=
.decCall ("ms") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "mstart"]) body542_4

def body542_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body542_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) body542_5 body542_6

def body542_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body542_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body542_10 : Prog (BitVec 64) :=
.seq body542_8 body542_9

def body542_11 : Prog (BitVec 64) :=
.seq body542_7 body542_10

def body542_12 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body542_11

def body542_13 : Prog (BitVec 64) :=
.seq body542_2 body542_12

def body542_14 : Prog (BitVec 64) :=
.seq body542_1 body542_13

def body542_15 : Prog (BitVec 64) :=
.seq body542_0 body542_14

def body542_16 : Prog (BitVec 64) :=
.decCall ("cost") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.const 100#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.var Flapjack.VarKind.local "w"]],
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) body542_15

def body542_17 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("access_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body542_16

def body542_18 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost1") ([Flapjack.Exp.var Flapjack.VarKind.local "mstart", Flapjack.Exp.var Flapjack.VarKind.local "size"]) body542_17

def body542_19 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) body542_18

def body542_20 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "size"]) body542_19

def body542_21 : Prog (BitVec 64) :=
.decCall ("size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body542_20

def body542_22 : Prog (BitVec 64) :=
.decCall ("cstart") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body542_21

def body542_23 : Prog (BitVec 64) :=
.decCall ("mstart") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body542_22

def body542_24 : Prog (BitVec 64) :=
.decCall ("addr") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "av"]) body542_23

def body542_25 : Prog (BitVec 64) :=
.decCall ("av") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body542_24

def body542_26 : Prog (BitVec 64) :=
.seq body542_0 body542_1

def body542_27 : Prog (BitVec 64) :=
.seq body542_26 body542_2

def body542_28 : Prog (BitVec 64) :=
.seq body542_7 body542_8

def body542_29 : Prog (BitVec 64) :=
.seq body542_28 body542_9

def body542_30 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body542_29

def body542_31 : Prog (BitVec 64) :=
.seq body542_27 body542_30

def body542_32 : Prog (BitVec 64) :=
.decCall ("cost") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.const 100#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.var Flapjack.VarKind.local "w"]],
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) body542_31

def body542_33 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("access_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body542_32

def body542_34 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost1") ([Flapjack.Exp.var Flapjack.VarKind.local "mstart", Flapjack.Exp.var Flapjack.VarKind.local "size"]) body542_33

def body542_35 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) body542_34

def body542_36 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "size"]) body542_35

def body542_37 : Prog (BitVec 64) :=
.decCall ("size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body542_36

def body542_38 : Prog (BitVec 64) :=
.decCall ("cstart") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body542_37

def body542_39 : Prog (BitVec 64) :=
.decCall ("mstart") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body542_38

def body542_40 : Prog (BitVec 64) :=
.decCall ("addr") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "av"]) body542_39

def body542_41 : Prog (BitVec 64) :=
.decCall ("av") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body542_40

def originalData542 : Decl (BitVec 64) :=
.function { name := "op_extcodecopy", inline := false, exported := false, params := [], body := body542_25, returnShape := (Flapjack.Shape.one) }
def simplifiedData542 : Decl (BitVec 64) :=
.function { name := "op_extcodecopy", inline := false, exported := false, params := [], body := body542_41, returnShape := (Flapjack.Shape.one) }
def original542 := Pancake.PanLang.declToHOL originalData542
def simplified542 := Pancake.PanLang.declToHOL simplifiedData542
end InitECandidate.Proofs.FrontendStages.Declarations
