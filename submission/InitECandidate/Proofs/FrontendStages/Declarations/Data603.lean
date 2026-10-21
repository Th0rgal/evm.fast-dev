import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify587
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body603_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "access_cost" (Flapjack.Exp.const 3000#64)

def body603_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body603_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) body603_0 body603_1

def body603_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "need"]

def body603_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "to"]

def body603_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) body603_4 body603_1

def body603_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "dl")]

def body603_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "code_address"]

def body603_8 : Prog (BitVec 64) :=
.seq body603_6 body603_7

def body603_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dl"))
  (Flapjack.Exp.const 0#64)) body603_8 body603_1

def body603_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "mcg")]

def body603_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 184#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 184#64]),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "mcg")])

def body603_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "extend_memory"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "x")]

def body603_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 0#64)

def body603_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body603_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "started") (Flapjack.Exp.const 0#64)) body603_14 body603_1

def body603_16 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body603_17 : Prog (BitVec 64) :=
.seq body603_15 body603_16

def body603_18 : Prog (BitVec 64) :=
.decCall ("started") (Flapjack.Shape.one) ("generic_call") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "mcg"),
  Flapjack.Exp.var Flapjack.VarKind.local "reservoir",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64],
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "to", Flapjack.Exp.var Flapjack.VarKind.local "code_address",
  Flapjack.Exp.const 1#64, Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "is",
  Flapjack.Exp.var Flapjack.VarKind.local "isz", Flapjack.Exp.var Flapjack.VarKind.local "os",
  Flapjack.Exp.var Flapjack.VarKind.local "osz", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dl"), Flapjack.Exp.const 0#64]) body603_17

def body603_19 : Prog (BitVec 64) :=
.decCall ("osz") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "out_size"]) body603_18

def body603_20 : Prog (BitVec 64) :=
.decCall ("os") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "out_start"]) body603_19

def body603_21 : Prog (BitVec 64) :=
.decCall ("isz") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "in_size"]) body603_20

def body603_22 : Prog (BitVec 64) :=
.decCall ("is") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "in_start"]) body603_21

def body603_23 : Prog (BitVec 64) :=
.seq body603_13 body603_22

def body603_24 : Prog (BitVec 64) :=
.dec ("reservoir") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])) body603_23

def body603_25 : Prog (BitVec 64) :=
.seq body603_12 body603_24

def body603_26 : Prog (BitVec 64) :=
.seq body603_11 body603_25

def body603_27 : Prog (BitVec 64) :=
.seq body603_10 body603_26

def body603_28 : Prog (BitVec 64) :=
.decCall ("mcg") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_message_call_gas") ([Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64],
  Flapjack.Exp.var Flapjack.VarKind.local "gw",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64]),
  Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body603_27

def body603_29 : Prog (BitVec 64) :=
.decCall ("gw") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "gasv"]) body603_28

def body603_30 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "code_address"]) body603_29

def body603_31 : Prog (BitVec 64) :=
.seq body603_9 body603_30

def body603_32 : Prog (BitVec 64) :=
.dec ("code_address") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "dl")) body603_31

def body603_33 : Prog (BitVec 64) :=
.decCall ("dl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_delegation_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "to"]) body603_32

def body603_34 : Prog (BitVec 64) :=
.seq body603_5 body603_33

def body603_35 : Prog (BitVec 64) :=
.seq body603_3 body603_34

def body603_36 : Prog (BitVec 64) :=
.decCall ("need") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "access_cost",
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) body603_35

def body603_37 : Prog (BitVec 64) :=
.seq body603_2 body603_36

def body603_38 : Prog (BitVec 64) :=
.dec ("access_cost") (Flapjack.Shape.one) (Flapjack.Exp.const 100#64) body603_37

def body603_39 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "to"]) body603_38

def body603_40 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost2") ([Flapjack.Exp.var Flapjack.VarKind.local "in_start", Flapjack.Exp.var Flapjack.VarKind.local "in_size",
  Flapjack.Exp.var Flapjack.VarKind.local "out_start", Flapjack.Exp.var Flapjack.VarKind.local "out_size"]) body603_39

def body603_41 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body603_40

def body603_42 : Prog (BitVec 64) :=
.decCall ("out_size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_41

def body603_43 : Prog (BitVec 64) :=
.decCall ("out_start") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_42

def body603_44 : Prog (BitVec 64) :=
.decCall ("in_size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_43

def body603_45 : Prog (BitVec 64) :=
.decCall ("in_start") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_44

def body603_46 : Prog (BitVec 64) :=
.decCall ("to") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "tov"]) body603_45

def body603_47 : Prog (BitVec 64) :=
.decCall ("tov") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_46

def body603_48 : Prog (BitVec 64) :=
.decCall ("gasv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_47

def body603_49 : Prog (BitVec 64) :=
.seq body603_3 body603_5

def body603_50 : Prog (BitVec 64) :=
.seq body603_10 body603_11

def body603_51 : Prog (BitVec 64) :=
.seq body603_50 body603_12

def body603_52 : Prog (BitVec 64) :=
.seq body603_51 body603_24

def body603_53 : Prog (BitVec 64) :=
.decCall ("mcg") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_message_call_gas") ([Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64],
  Flapjack.Exp.var Flapjack.VarKind.local "gw",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64]),
  Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body603_52

def body603_54 : Prog (BitVec 64) :=
.decCall ("gw") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "gasv"]) body603_53

def body603_55 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "code_address"]) body603_54

def body603_56 : Prog (BitVec 64) :=
.seq body603_9 body603_55

def body603_57 : Prog (BitVec 64) :=
.dec ("code_address") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "dl")) body603_56

def body603_58 : Prog (BitVec 64) :=
.decCall ("dl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_delegation_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "to"]) body603_57

def body603_59 : Prog (BitVec 64) :=
.seq body603_49 body603_58

def body603_60 : Prog (BitVec 64) :=
.decCall ("need") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "access_cost",
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) body603_59

def body603_61 : Prog (BitVec 64) :=
.seq body603_2 body603_60

def body603_62 : Prog (BitVec 64) :=
.dec ("access_cost") (Flapjack.Shape.one) (Flapjack.Exp.const 100#64) body603_61

def body603_63 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "to"]) body603_62

def body603_64 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost2") ([Flapjack.Exp.var Flapjack.VarKind.local "in_start", Flapjack.Exp.var Flapjack.VarKind.local "in_size",
  Flapjack.Exp.var Flapjack.VarKind.local "out_start", Flapjack.Exp.var Flapjack.VarKind.local "out_size"]) body603_63

def body603_65 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body603_64

def body603_66 : Prog (BitVec 64) :=
.decCall ("out_size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_65

def body603_67 : Prog (BitVec 64) :=
.decCall ("out_start") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_66

def body603_68 : Prog (BitVec 64) :=
.decCall ("in_size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_67

def body603_69 : Prog (BitVec 64) :=
.decCall ("in_start") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_68

def body603_70 : Prog (BitVec 64) :=
.decCall ("to") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "tov"]) body603_69

def body603_71 : Prog (BitVec 64) :=
.decCall ("tov") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_70

def body603_72 : Prog (BitVec 64) :=
.decCall ("gasv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body603_71

def originalData603 : Decl (BitVec 64) :=
.function { name := "op_staticcall", inline := false, exported := false, params := [], body := body603_48, returnShape := (Flapjack.Shape.one) }
def simplifiedData603 : Decl (BitVec 64) :=
.function { name := "op_staticcall", inline := false, exported := false, params := [], body := body603_72, returnShape := (Flapjack.Shape.one) }
def original603 := Pancake.PanLang.declToHOL originalData603
def simplified603 := Pancake.PanLang.declToHOL simplifiedData603
end InitECandidate.Proofs.FrontendStages.Declarations
