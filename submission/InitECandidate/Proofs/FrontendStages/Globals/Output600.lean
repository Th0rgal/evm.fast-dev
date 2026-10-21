import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data600
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate584
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody600_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 8#64)

def globalBody600_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody600_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
        (Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 144#64]))
        (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vz") (Flapjack.Exp.const 0#64))]) globalBody600_0 globalBody600_1

def globalBody600_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "access_cost" (Flapjack.Exp.const 3000#64)

def globalBody600_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) globalBody600_3 globalBody600_1

def globalBody600_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "transfer_cost" (Flapjack.Exp.const 11300#64)

def globalBody600_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vz") (Flapjack.Exp.const 0#64)) globalBody600_5 globalBody600_1

def globalBody600_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "need"]

def globalBody600_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "to"]

def globalBody600_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) globalBody600_8 globalBody600_1

def globalBody600_10 : Prog (BitVec 64) :=
.seq globalBody600_7 globalBody600_9

def globalBody600_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "dl")]

def globalBody600_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "code_address"]

def globalBody600_13 : Prog (BitVec 64) :=
.seq globalBody600_11 globalBody600_12

def globalBody600_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dl"))
  (Flapjack.Exp.const 0#64)) globalBody600_13 globalBody600_1

def globalBody600_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "new_account_charged" (Flapjack.Exp.const 1#64)

def globalBody600_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_state_gas" [Flapjack.Exp.const 183600#64]

def globalBody600_17 : Prog (BitVec 64) :=
.seq globalBody600_15 globalBody600_16

def globalBody600_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "alive") (Flapjack.Exp.const 0#64)) globalBody600_17 globalBody600_1

def globalBody600_19 : Prog (BitVec 64) :=
.decCall ("alive") (Flapjack.Shape.one) ("is_account_alive") ([Flapjack.Exp.var Flapjack.VarKind.local "to"]) globalBody600_18

def globalBody600_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vz") (Flapjack.Exp.const 0#64)) globalBody600_19 globalBody600_1

def globalBody600_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "mcg")]

def globalBody600_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 184#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.load Flapjack.Shape.one
              (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
            Flapjack.Exp.const 184#64]),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "mcg")])

def globalBody600_23 : Prog (BitVec 64) :=
.seq globalBody600_21 globalBody600_22

def globalBody600_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "extend_memory"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "x")]

def globalBody600_25 : Prog (BitVec 64) :=
.seq globalBody600_23 globalBody600_24

def globalBody600_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 0#64)

def globalBody600_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.rStruct
      [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]

def globalBody600_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_retdata"
  [Flapjack.Exp.var Flapjack.VarKind.local "empty", Flapjack.Exp.const 0#64]

def globalBody600_29 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.load Flapjack.Shape.one
              (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
            Flapjack.Exp.const 64#64]),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "mcg")])

def globalBody600_30 : Prog (BitVec 64) :=
.seq globalBody600_28 globalBody600_29

def globalBody600_31 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 72#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.load Flapjack.Shape.one
              (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
            Flapjack.Exp.const 72#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "reservoir"])

def globalBody600_32 : Prog (BitVec 64) :=
.seq globalBody600_30 globalBody600_31

def globalBody600_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "credit_state_gas_refund" [Flapjack.Exp.const 183600#64]

def globalBody600_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "new_account_charged")
  (Flapjack.Exp.const 0#64)) globalBody600_33 globalBody600_1

def globalBody600_35 : Prog (BitVec 64) :=
.seq globalBody600_32 globalBody600_34

def globalBody600_36 : Prog (BitVec 64) :=
.dec ("empty") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 264#64])) globalBody600_35

def globalBody600_37 : Prog (BitVec 64) :=
.seq globalBody600_27 globalBody600_36

def globalBody600_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "started"), none)) "generic_call"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "mcg"),
    Flapjack.Exp.var Flapjack.VarKind.local "reservoir", Flapjack.Exp.var Flapjack.VarKind.local "value",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "to", Flapjack.Exp.var Flapjack.VarKind.local "code_address",
    Flapjack.Exp.const 1#64, Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "is",
    Flapjack.Exp.var Flapjack.VarKind.local "isz", Flapjack.Exp.var Flapjack.VarKind.local "os",
    Flapjack.Exp.var Flapjack.VarKind.local "osz",
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dl"),
    Flapjack.Exp.var Flapjack.VarKind.local "new_account_charged"]

def globalBody600_39 : Prog (BitVec 64) :=
.decCall ("osz") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "out_size"]) globalBody600_38

def globalBody600_40 : Prog (BitVec 64) :=
.decCall ("os") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "out_start"]) globalBody600_39

def globalBody600_41 : Prog (BitVec 64) :=
.decCall ("isz") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "in_size"]) globalBody600_40

def globalBody600_42 : Prog (BitVec 64) :=
.decCall ("is") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "in_start"]) globalBody600_41

def globalBody600_43 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "insufficient")
  (Flapjack.Exp.const 0#64)) globalBody600_37 globalBody600_42

def globalBody600_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody600_45 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "started") (Flapjack.Exp.const 0#64)) globalBody600_44 globalBody600_1

def globalBody600_46 : Prog (BitVec 64) :=
.seq globalBody600_43 globalBody600_45

def globalBody600_47 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody600_48 : Prog (BitVec 64) :=
.seq globalBody600_46 globalBody600_47

def globalBody600_49 : Prog (BitVec 64) :=
.dec ("started") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody600_48

def globalBody600_50 : Prog (BitVec 64) :=
.decCall ("insufficient") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "sender", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "value"]) globalBody600_49

def globalBody600_51 : Prog (BitVec 64) :=
.decCall ("sender") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])]) globalBody600_50

def globalBody600_52 : Prog (BitVec 64) :=
.seq globalBody600_26 globalBody600_51

def globalBody600_53 : Prog (BitVec 64) :=
.dec ("reservoir") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 72#64])) globalBody600_52

def globalBody600_54 : Prog (BitVec 64) :=
.seq globalBody600_25 globalBody600_53

def globalBody600_55 : Prog (BitVec 64) :=
.decCall ("mcg") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_message_call_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "value", Flapjack.Exp.var Flapjack.VarKind.local "gw",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
        Flapjack.Exp.const 64#64]),
  Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody600_54

def globalBody600_56 : Prog (BitVec 64) :=
.decCall ("gw") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "gasv"]) globalBody600_55

def globalBody600_57 : Prog (BitVec 64) :=
.seq globalBody600_20 globalBody600_56

def globalBody600_58 : Prog (BitVec 64) :=
.dec ("new_account_charged") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody600_57

def globalBody600_59 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "code_address"]) globalBody600_58

def globalBody600_60 : Prog (BitVec 64) :=
.seq globalBody600_14 globalBody600_59

def globalBody600_61 : Prog (BitVec 64) :=
.dec ("code_address") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "dl")) globalBody600_60

def globalBody600_62 : Prog (BitVec 64) :=
.decCall ("dl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_delegation_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "to"]) globalBody600_61

def globalBody600_63 : Prog (BitVec 64) :=
.seq globalBody600_10 globalBody600_62

def globalBody600_64 : Prog (BitVec 64) :=
.decCall ("need") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "access_cost", Flapjack.Exp.var Flapjack.VarKind.local "transfer_cost"],
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) globalBody600_63

def globalBody600_65 : Prog (BitVec 64) :=
.seq globalBody600_6 globalBody600_64

def globalBody600_66 : Prog (BitVec 64) :=
.dec ("transfer_cost") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody600_65

def globalBody600_67 : Prog (BitVec 64) :=
.seq globalBody600_4 globalBody600_66

def globalBody600_68 : Prog (BitVec 64) :=
.dec ("access_cost") (Flapjack.Shape.one) (Flapjack.Exp.const 100#64) globalBody600_67

def globalBody600_69 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "to"]) globalBody600_68

def globalBody600_70 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost2") ([Flapjack.Exp.var Flapjack.VarKind.local "in_start", Flapjack.Exp.var Flapjack.VarKind.local "in_size",
  Flapjack.Exp.var Flapjack.VarKind.local "out_start", Flapjack.Exp.var Flapjack.VarKind.local "out_size"]) globalBody600_69

def globalBody600_71 : Prog (BitVec 64) :=
.seq globalBody600_2 globalBody600_70

def globalBody600_72 : Prog (BitVec 64) :=
.decCall ("vz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "value"]) globalBody600_71

def globalBody600_73 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 112#64])) globalBody600_72

def globalBody600_74 : Prog (BitVec 64) :=
.decCall ("out_size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody600_73

def globalBody600_75 : Prog (BitVec 64) :=
.decCall ("out_start") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody600_74

def globalBody600_76 : Prog (BitVec 64) :=
.decCall ("in_size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody600_75

def globalBody600_77 : Prog (BitVec 64) :=
.decCall ("in_start") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody600_76

def globalBody600_78 : Prog (BitVec 64) :=
.decCall ("value") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody600_77

def globalBody600_79 : Prog (BitVec 64) :=
.decCall ("to") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "tov"]) globalBody600_78

def globalBody600_80 : Prog (BitVec 64) :=
.decCall ("tov") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody600_79

def globalBody600_81 : Prog (BitVec 64) :=
.decCall ("gasv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody600_80

def globalData600 : Decl (BitVec 64) :=
.function { name := "op_call", inline := false, exported := false, params := [], body := globalBody600_81, returnShape := (Flapjack.Shape.one) }
def globalOutput600 := Pancake.PanLang.declToHOL globalData600
end InitECandidate.Proofs.FrontendStages.Declarations
