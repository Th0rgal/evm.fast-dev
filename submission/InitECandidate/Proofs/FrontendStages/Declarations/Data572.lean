import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify556
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body572_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "written",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 0#64]),
    Flapjack.Exp.const 1#64]

def body572_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "written",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.const 1#64]

def body572_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body572_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vz") (Flapjack.Exp.const 0#64)) body572_1 body572_2

def body572_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cid_ok" (Flapjack.Exp.const 1#64)

def body572_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "cz") (Flapjack.Exp.const 0#64)) body572_4 body572_2

def body572_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "cfit")
        (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "cid"))
        (Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 0#64])))]) body572_4 body572_2

def body572_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "rec"]

def body572_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "authority" (Flapjack.Exp.var Flapjack.VarKind.local "rec")

def body572_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body572_8 body572_2

def body572_10 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("validate_authorization_checks") ([Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.var Flapjack.VarKind.local "rec"]) body572_9

def body572_11 : Prog (BitVec 64) :=
.seq body572_7 body572_10

def body572_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "rec") (Flapjack.Exp.const 0#64)) body572_11 body572_2

def body572_13 : Prog (BitVec 64) :=
.decCall ("rec") (Flapjack.Shape.one) ("recover_authority") ([Flapjack.Exp.var Flapjack.VarKind.local "auth"]) body572_12

def body572_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 40#64]))
  (Flapjack.Exp.const 18446744073709551615#64)) body572_13 body572_2

def body572_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "cid_ok") (Flapjack.Exp.const 0#64)) body572_14 body572_2

def body572_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_state_gas" [Flapjack.Exp.const 183600#64]

def body572_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ex") (Flapjack.Exp.const 0#64)) body572_16 body572_2

def body572_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 9000#64]

def body572_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "written", Flapjack.Exp.var Flapjack.VarKind.local "authority",
    Flapjack.Exp.const 1#64]

def body572_20 : Prog (BitVec 64) :=
.seq body572_18 body572_19

def body572_21 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "wr") (Flapjack.Exp.const 0#64)) body572_20 body572_2

def body572_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_code"
  [Flapjack.Exp.var Flapjack.VarKind.local "authority", Flapjack.Exp.var Flapjack.VarKind.global "null_address",
    Flapjack.Exp.const 0#64]

def body572_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_state_gas" [Flapjack.Exp.const 35190#64]

def body572_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "delegated_before")
        (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "sf") (Flapjack.Exp.const 0#64))]) body572_23 body572_2

def body572_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "set_for", Flapjack.Exp.var Flapjack.VarKind.local "authority",
    Flapjack.Exp.const 1#64]

def body572_26 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "code") (Flapjack.Exp.const 239#64)

def body572_27 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 1#64)

def body572_28 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.const 2#64])
  (Flapjack.Exp.const 0#64)

def body572_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.const 3#64],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.const 20#64]

def body572_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_code"
  [Flapjack.Exp.var Flapjack.VarKind.local "authority", Flapjack.Exp.var Flapjack.VarKind.local "code",
    Flapjack.Exp.const 23#64]

def body572_31 : Prog (BitVec 64) :=
.seq body572_29 body572_30

def body572_32 : Prog (BitVec 64) :=
.seq body572_28 body572_31

def body572_33 : Prog (BitVec 64) :=
.seq body572_27 body572_32

def body572_34 : Prog (BitVec 64) :=
.seq body572_26 body572_33

def body572_35 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body572_34

def body572_36 : Prog (BitVec 64) :=
.seq body572_25 body572_35

def body572_37 : Prog (BitVec 64) :=
.seq body572_24 body572_36

def body572_38 : Prog (BitVec 64) :=
.decCall ("sf") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.var Flapjack.VarKind.local "set_for", Flapjack.Exp.var Flapjack.VarKind.local "authority"]) body572_37

def body572_39 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "is_null") (Flapjack.Exp.const 0#64)) body572_22 body572_38

def body572_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "increment_nonce" [Flapjack.Exp.var Flapjack.VarKind.local "authority"]

def body572_41 : Prog (BitVec 64) :=
.seq body572_39 body572_40

def body572_42 : Prog (BitVec 64) :=
.decCall ("is_null") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.var Flapjack.VarKind.global "null_address", Flapjack.Exp.const 20#64]) body572_41

def body572_43 : Prog (BitVec 64) :=
.decCall ("delegated_before") (Flapjack.Shape.one) ("is_valid_delegation") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "pre_code"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "pre_code")]) body572_42

def body572_44 : Prog (BitVec 64) :=
.decCall ("pre_code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("get_code") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "authority"]) body572_43

def body572_45 : Prog (BitVec 64) :=
.decCall ("pre") (Flapjack.Shape.one) ("get_pre_state_account") ([Flapjack.Exp.var Flapjack.VarKind.local "authority"]) body572_44

def body572_46 : Prog (BitVec 64) :=
.seq body572_21 body572_45

def body572_47 : Prog (BitVec 64) :=
.decCall ("wr") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.var Flapjack.VarKind.local "written", Flapjack.Exp.var Flapjack.VarKind.local "authority"]) body572_46

def body572_48 : Prog (BitVec 64) :=
.seq body572_17 body572_47

def body572_49 : Prog (BitVec 64) :=
.decCall ("ex") (Flapjack.Shape.one) ("account_exists") ([Flapjack.Exp.var Flapjack.VarKind.local "authority"]) body572_48

def body572_50 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "authority") (Flapjack.Exp.const 0#64)) body572_49 body572_2

def body572_51 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body572_52 : Prog (BitVec 64) :=
.seq body572_50 body572_51

def body572_53 : Prog (BitVec 64) :=
.seq body572_15 body572_52

def body572_54 : Prog (BitVec 64) :=
.seq body572_6 body572_53

def body572_55 : Prog (BitVec 64) :=
.seq body572_5 body572_54

def body572_56 : Prog (BitVec 64) :=
.dec ("cid_ok") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body572_55

def body572_57 : Prog (BitVec 64) :=
.decCall ("cfit") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "cid"]) body572_56

def body572_58 : Prog (BitVec 64) :=
.decCall ("cz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "cid"]) body572_57

def body572_59 : Prog (BitVec 64) :=
.dec ("cid") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 0#64])) body572_58

def body572_60 : Prog (BitVec 64) :=
.dec ("authority") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body572_59

def body572_61 : Prog (BitVec 64) :=
.dec ("auth") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "auths",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 120#64]]) body572_60

def body572_62 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body572_61

def body572_63 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body572_64 : Prog (BitVec 64) :=
.seq body572_62 body572_63

def body572_65 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body572_64

def body572_66 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 152#64])) body572_65

def body572_67 : Prog (BitVec 64) :=
.dec ("auths") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 144#64])) body572_66

def body572_68 : Prog (BitVec 64) :=
.decCall ("set_for") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 8#64]) body572_67

def body572_69 : Prog (BitVec 64) :=
.seq body572_3 body572_68

def body572_70 : Prog (BitVec 64) :=
.decCall ("vz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 16#64])]) body572_69

def body572_71 : Prog (BitVec 64) :=
.seq body572_0 body572_70

def body572_72 : Prog (BitVec 64) :=
.decCall ("written") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 8#64]) body572_71

def body572_73 : Prog (BitVec 64) :=
.dec ("benv") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 0#64])) body572_72

def body572_74 : Prog (BitVec 64) :=
.dec ("te") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 8#64])) body572_73

def body572_75 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body572_74

def body572_76 : Prog (BitVec 64) :=
.seq body572_5 body572_6

def body572_77 : Prog (BitVec 64) :=
.seq body572_76 body572_15

def body572_78 : Prog (BitVec 64) :=
.seq body572_24 body572_25

def body572_79 : Prog (BitVec 64) :=
.seq body572_26 body572_27

def body572_80 : Prog (BitVec 64) :=
.seq body572_79 body572_28

def body572_81 : Prog (BitVec 64) :=
.seq body572_80 body572_29

def body572_82 : Prog (BitVec 64) :=
.seq body572_81 body572_30

def body572_83 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body572_82

def body572_84 : Prog (BitVec 64) :=
.seq body572_78 body572_83

def body572_85 : Prog (BitVec 64) :=
.decCall ("sf") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.var Flapjack.VarKind.local "set_for", Flapjack.Exp.var Flapjack.VarKind.local "authority"]) body572_84

def body572_86 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "is_null") (Flapjack.Exp.const 0#64)) body572_22 body572_85

def body572_87 : Prog (BitVec 64) :=
.seq body572_86 body572_40

def body572_88 : Prog (BitVec 64) :=
.decCall ("is_null") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.var Flapjack.VarKind.global "null_address", Flapjack.Exp.const 20#64]) body572_87

def body572_89 : Prog (BitVec 64) :=
.decCall ("delegated_before") (Flapjack.Shape.one) ("is_valid_delegation") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "pre_code"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "pre_code")]) body572_88

def body572_90 : Prog (BitVec 64) :=
.decCall ("pre_code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("get_code") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "authority"]) body572_89

def body572_91 : Prog (BitVec 64) :=
.decCall ("pre") (Flapjack.Shape.one) ("get_pre_state_account") ([Flapjack.Exp.var Flapjack.VarKind.local "authority"]) body572_90

def body572_92 : Prog (BitVec 64) :=
.seq body572_21 body572_91

def body572_93 : Prog (BitVec 64) :=
.decCall ("wr") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.var Flapjack.VarKind.local "written", Flapjack.Exp.var Flapjack.VarKind.local "authority"]) body572_92

def body572_94 : Prog (BitVec 64) :=
.seq body572_17 body572_93

def body572_95 : Prog (BitVec 64) :=
.decCall ("ex") (Flapjack.Shape.one) ("account_exists") ([Flapjack.Exp.var Flapjack.VarKind.local "authority"]) body572_94

def body572_96 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "authority") (Flapjack.Exp.const 0#64)) body572_95 body572_2

def body572_97 : Prog (BitVec 64) :=
.seq body572_77 body572_96

def body572_98 : Prog (BitVec 64) :=
.seq body572_97 body572_51

def body572_99 : Prog (BitVec 64) :=
.dec ("cid_ok") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body572_98

def body572_100 : Prog (BitVec 64) :=
.decCall ("cfit") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "cid"]) body572_99

def body572_101 : Prog (BitVec 64) :=
.decCall ("cz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "cid"]) body572_100

def body572_102 : Prog (BitVec 64) :=
.dec ("cid") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 0#64])) body572_101

def body572_103 : Prog (BitVec 64) :=
.dec ("authority") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body572_102

def body572_104 : Prog (BitVec 64) :=
.dec ("auth") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "auths",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 120#64]]) body572_103

def body572_105 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body572_104

def body572_106 : Prog (BitVec 64) :=
.seq body572_105 body572_63

def body572_107 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body572_106

def body572_108 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 152#64])) body572_107

def body572_109 : Prog (BitVec 64) :=
.dec ("auths") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 144#64])) body572_108

def body572_110 : Prog (BitVec 64) :=
.decCall ("set_for") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 8#64]) body572_109

def body572_111 : Prog (BitVec 64) :=
.seq body572_3 body572_110

def body572_112 : Prog (BitVec 64) :=
.decCall ("vz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 16#64])]) body572_111

def body572_113 : Prog (BitVec 64) :=
.seq body572_0 body572_112

def body572_114 : Prog (BitVec 64) :=
.decCall ("written") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 8#64]) body572_113

def body572_115 : Prog (BitVec 64) :=
.dec ("benv") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 0#64])) body572_114

def body572_116 : Prog (BitVec 64) :=
.dec ("te") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 8#64])) body572_115

def body572_117 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body572_116

def originalData572 : Decl (BitVec 64) :=
.function { name := "set_delegation", inline := false, exported := false, params := [], body := body572_75, returnShape := (Flapjack.Shape.one) }
def simplifiedData572 : Decl (BitVec 64) :=
.function { name := "set_delegation", inline := false, exported := false, params := [], body := body572_117, returnShape := (Flapjack.Shape.one) }
def original572 := Pancake.PanLang.declToHOL originalData572
def simplified572 := Pancake.PanLang.declToHOL simplifiedData572
end InitECandidate.Proofs.FrontendStages.Declarations
