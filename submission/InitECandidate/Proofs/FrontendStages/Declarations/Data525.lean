import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify509
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body525_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "require_not_static" []

def body525_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "u256_to_be32"
  [Flapjack.Exp.var Flapjack.VarKind.local "kv", Flapjack.Exp.var Flapjack.VarKind.local "key"]

def body525_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "access_cost" (Flapjack.Exp.const 2100#64)

def body525_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body525_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) body525_2 body525_3

def body525_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "check_gas" [Flapjack.Exp.var Flapjack.VarKind.local "mx"]

def body525_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "access_cost"]

def body525_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_storage_key"
  [Flapjack.Exp.var Flapjack.VarKind.local "target", Flapjack.Exp.var Flapjack.VarKind.local "key"]

def body525_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) body525_7 body525_3

def body525_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "gas_cost"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "gas_cost", Flapjack.Exp.const 10000#64])

def body525_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "oc") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "cn") (Flapjack.Exp.const 0#64))]) body525_9 body525_3

def body525_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 96#64]),
      Flapjack.Exp.const 11616#64])

def body525_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "oz") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "cz") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "nz") (Flapjack.Exp.const 0#64))]) body525_11 body525_3

def body525_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 96#64]),
      Flapjack.Exp.const 11616#64])

def body525_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "oz") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "cz") (Flapjack.Exp.const 0#64))]) body525_13 body525_3

def body525_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 96#64]),
      Flapjack.Exp.const 10000#64])

def body525_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "on") (Flapjack.Exp.const 0#64)) body525_15 body525_3

def body525_17 : Prog (BitVec 64) :=
.seq body525_14 body525_16

def body525_18 : Prog (BitVec 64) :=
.seq body525_12 body525_17

def body525_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "cn") (Flapjack.Exp.const 0#64)) body525_18 body525_3

def body525_20 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "state_gas" (Flapjack.Exp.const 97920#64)

def body525_21 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "oc") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "cn") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "oz") (Flapjack.Exp.const 0#64))]) body525_20 body525_3

def body525_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "credit_state_gas_refund" [Flapjack.Exp.const 97920#64]

def body525_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "cn") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "on") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "oz") (Flapjack.Exp.const 0#64))]) body525_22 body525_3

def body525_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "gas_cost", Flapjack.Exp.var Flapjack.VarKind.local "access_cost"]]

def body525_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_state_gas" [Flapjack.Exp.var Flapjack.VarKind.local "state_gas"]

def body525_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_storage"
  [Flapjack.Exp.var Flapjack.VarKind.local "target", Flapjack.Exp.var Flapjack.VarKind.local "key",
    Flapjack.Exp.var Flapjack.VarKind.local "new_value"]

def body525_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body525_28 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body525_29 : Prog (BitVec 64) :=
.seq body525_27 body525_28

def body525_30 : Prog (BitVec 64) :=
.seq body525_26 body525_29

def body525_31 : Prog (BitVec 64) :=
.seq body525_25 body525_30

def body525_32 : Prog (BitVec 64) :=
.seq body525_24 body525_31

def body525_33 : Prog (BitVec 64) :=
.seq body525_23 body525_32

def body525_34 : Prog (BitVec 64) :=
.seq body525_21 body525_33

def body525_35 : Prog (BitVec 64) :=
.dec ("state_gas") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body525_34

def body525_36 : Prog (BitVec 64) :=
.seq body525_19 body525_35

def body525_37 : Prog (BitVec 64) :=
.seq body525_10 body525_36

def body525_38 : Prog (BitVec 64) :=
.dec ("gas_cost") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "access_cost") body525_37

def body525_39 : Prog (BitVec 64) :=
.decCall ("nz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "new_value"]) body525_38

def body525_40 : Prog (BitVec 64) :=
.decCall ("cz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "current"]) body525_39

def body525_41 : Prog (BitVec 64) :=
.decCall ("oz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "original"]) body525_40

def body525_42 : Prog (BitVec 64) :=
.decCall ("on") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "original", Flapjack.Exp.var Flapjack.VarKind.local "new_value"]) body525_41

def body525_43 : Prog (BitVec 64) :=
.decCall ("cn") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "current", Flapjack.Exp.var Flapjack.VarKind.local "new_value"]) body525_42

def body525_44 : Prog (BitVec 64) :=
.decCall ("oc") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "original", Flapjack.Exp.var Flapjack.VarKind.local "current"]) body525_43

def body525_45 : Prog (BitVec 64) :=
.decCall ("current") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("get_storage") ([Flapjack.Exp.var Flapjack.VarKind.local "target", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body525_44

def body525_46 : Prog (BitVec 64) :=
.decCall ("original") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("get_storage_original") ([Flapjack.Exp.var Flapjack.VarKind.local "target", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body525_45

def body525_47 : Prog (BitVec 64) :=
.seq body525_8 body525_46

def body525_48 : Prog (BitVec 64) :=
.seq body525_6 body525_47

def body525_49 : Prog (BitVec 64) :=
.seq body525_5 body525_48

def body525_50 : Prog (BitVec 64) :=
.decCall ("mx") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "access_cost",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.const 2300#64, Flapjack.Exp.const 1#64]]) body525_49

def body525_51 : Prog (BitVec 64) :=
.seq body525_4 body525_50

def body525_52 : Prog (BitVec 64) :=
.dec ("access_cost") (Flapjack.Shape.one) (Flapjack.Exp.const 100#64) body525_51

def body525_53 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_storage_key") ([Flapjack.Exp.var Flapjack.VarKind.local "target", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body525_52

def body525_54 : Prog (BitVec 64) :=
.dec ("target") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 32#64])) body525_53

def body525_55 : Prog (BitVec 64) :=
.seq body525_1 body525_54

def body525_56 : Prog (BitVec 64) :=
.dec ("key") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "evm_key_buf") body525_55

def body525_57 : Prog (BitVec 64) :=
.decCall ("new_value") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body525_56

def body525_58 : Prog (BitVec 64) :=
.decCall ("kv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body525_57

def body525_59 : Prog (BitVec 64) :=
.seq body525_0 body525_58

def body525_60 : Prog (BitVec 64) :=
.seq body525_5 body525_6

def body525_61 : Prog (BitVec 64) :=
.seq body525_60 body525_8

def body525_62 : Prog (BitVec 64) :=
.seq body525_12 body525_14

def body525_63 : Prog (BitVec 64) :=
.seq body525_62 body525_16

def body525_64 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "cn") (Flapjack.Exp.const 0#64)) body525_63 body525_3

def body525_65 : Prog (BitVec 64) :=
.seq body525_10 body525_64

def body525_66 : Prog (BitVec 64) :=
.seq body525_21 body525_23

def body525_67 : Prog (BitVec 64) :=
.seq body525_66 body525_24

def body525_68 : Prog (BitVec 64) :=
.seq body525_67 body525_25

def body525_69 : Prog (BitVec 64) :=
.seq body525_68 body525_26

def body525_70 : Prog (BitVec 64) :=
.seq body525_69 body525_27

def body525_71 : Prog (BitVec 64) :=
.seq body525_70 body525_28

def body525_72 : Prog (BitVec 64) :=
.dec ("state_gas") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body525_71

def body525_73 : Prog (BitVec 64) :=
.seq body525_65 body525_72

def body525_74 : Prog (BitVec 64) :=
.dec ("gas_cost") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "access_cost") body525_73

def body525_75 : Prog (BitVec 64) :=
.decCall ("nz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "new_value"]) body525_74

def body525_76 : Prog (BitVec 64) :=
.decCall ("cz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "current"]) body525_75

def body525_77 : Prog (BitVec 64) :=
.decCall ("oz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "original"]) body525_76

def body525_78 : Prog (BitVec 64) :=
.decCall ("on") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "original", Flapjack.Exp.var Flapjack.VarKind.local "new_value"]) body525_77

def body525_79 : Prog (BitVec 64) :=
.decCall ("cn") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "current", Flapjack.Exp.var Flapjack.VarKind.local "new_value"]) body525_78

def body525_80 : Prog (BitVec 64) :=
.decCall ("oc") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "original", Flapjack.Exp.var Flapjack.VarKind.local "current"]) body525_79

def body525_81 : Prog (BitVec 64) :=
.decCall ("current") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("get_storage") ([Flapjack.Exp.var Flapjack.VarKind.local "target", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body525_80

def body525_82 : Prog (BitVec 64) :=
.decCall ("original") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("get_storage_original") ([Flapjack.Exp.var Flapjack.VarKind.local "target", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body525_81

def body525_83 : Prog (BitVec 64) :=
.seq body525_61 body525_82

def body525_84 : Prog (BitVec 64) :=
.decCall ("mx") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "access_cost",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.const 2300#64, Flapjack.Exp.const 1#64]]) body525_83

def body525_85 : Prog (BitVec 64) :=
.seq body525_4 body525_84

def body525_86 : Prog (BitVec 64) :=
.dec ("access_cost") (Flapjack.Shape.one) (Flapjack.Exp.const 100#64) body525_85

def body525_87 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_storage_key") ([Flapjack.Exp.var Flapjack.VarKind.local "target", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body525_86

def body525_88 : Prog (BitVec 64) :=
.dec ("target") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 32#64])) body525_87

def body525_89 : Prog (BitVec 64) :=
.seq body525_1 body525_88

def body525_90 : Prog (BitVec 64) :=
.dec ("key") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "evm_key_buf") body525_89

def body525_91 : Prog (BitVec 64) :=
.decCall ("new_value") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body525_90

def body525_92 : Prog (BitVec 64) :=
.decCall ("kv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body525_91

def body525_93 : Prog (BitVec 64) :=
.seq body525_0 body525_92

def originalData525 : Decl (BitVec 64) :=
.function { name := "op_sstore", inline := false, exported := false, params := [], body := body525_59, returnShape := (Flapjack.Shape.one) }
def simplifiedData525 : Decl (BitVec 64) :=
.function { name := "op_sstore", inline := false, exported := false, params := [], body := body525_93, returnShape := (Flapjack.Shape.one) }
def original525 := Pancake.PanLang.declToHOL originalData525
def simplified525 := Pancake.PanLang.declToHOL simplifiedData525
end InitECandidate.Proofs.FrontendStages.Declarations
