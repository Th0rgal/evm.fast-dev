import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify551
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body567_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "require_not_static" []

def body567_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "gas_cost"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "gas_cost", Flapjack.Exp.const 3000#64])

def body567_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body567_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) body567_1 body567_2

def body567_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "gas_cost"]

def body567_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "beneficiary"]

def body567_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) body567_5 body567_2

def body567_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "state_gas" (Flapjack.Exp.const 183600#64)

def body567_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "aw" (Flapjack.Exp.const 9000#64)

def body567_9 : Prog (BitVec 64) :=
.seq body567_7 body567_8

def body567_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "alive") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "obz") (Flapjack.Exp.const 0#64))]) body567_9 body567_2

def body567_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "aw"]

def body567_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_state_gas" [Flapjack.Exp.var Flapjack.VarKind.local "state_gas"]

def body567_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "oa"), none)) "get_account"
  [Flapjack.Exp.var Flapjack.VarKind.local "originator"]

def body567_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "move_ether"
  [Flapjack.Exp.var Flapjack.VarKind.local "originator", Flapjack.Exp.var Flapjack.VarKind.local "beneficiary",
    Flapjack.Exp.var Flapjack.VarKind.local "bal"]

def body567_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "emit_transfer_log"
  [Flapjack.Exp.var Flapjack.VarKind.local "originator", Flapjack.Exp.var Flapjack.VarKind.local "beneficiary",
    Flapjack.Exp.var Flapjack.VarKind.local "bal"]

def body567_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "same") (Flapjack.Exp.const 0#64)) body567_15 body567_2

def body567_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 136#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "originator", Flapjack.Exp.const 1#64]

def body567_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "created") (Flapjack.Exp.const 0#64)) body567_17 body567_2

def body567_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.const 0#64)

def body567_20 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body567_21 : Prog (BitVec 64) :=
.seq body567_19 body567_20

def body567_22 : Prog (BitVec 64) :=
.seq body567_18 body567_21

def body567_23 : Prog (BitVec 64) :=
.decCall ("created") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 56#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "originator"]) body567_22

def body567_24 : Prog (BitVec 64) :=
.seq body567_16 body567_23

def body567_25 : Prog (BitVec 64) :=
.decCall ("same") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "beneficiary", Flapjack.Exp.var Flapjack.VarKind.local "originator",
  Flapjack.Exp.const 20#64]) body567_24

def body567_26 : Prog (BitVec 64) :=
.seq body567_14 body567_25

def body567_27 : Prog (BitVec 64) :=
.dec ("bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "oa", Flapjack.Exp.const 8#64])) body567_26

def body567_28 : Prog (BitVec 64) :=
.seq body567_13 body567_27

def body567_29 : Prog (BitVec 64) :=
.seq body567_12 body567_28

def body567_30 : Prog (BitVec 64) :=
.seq body567_11 body567_29

def body567_31 : Prog (BitVec 64) :=
.seq body567_10 body567_30

def body567_32 : Prog (BitVec 64) :=
.dec ("aw") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body567_31

def body567_33 : Prog (BitVec 64) :=
.dec ("state_gas") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body567_32

def body567_34 : Prog (BitVec 64) :=
.decCall ("obz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "oa", Flapjack.Exp.const 8#64])]) body567_33

def body567_35 : Prog (BitVec 64) :=
.decCall ("oa") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "originator"]) body567_34

def body567_36 : Prog (BitVec 64) :=
.decCall ("alive") (Flapjack.Shape.one) ("is_account_alive") ([Flapjack.Exp.var Flapjack.VarKind.local "beneficiary"]) body567_35

def body567_37 : Prog (BitVec 64) :=
.dec ("originator") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 32#64])) body567_36

def body567_38 : Prog (BitVec 64) :=
.seq body567_6 body567_37

def body567_39 : Prog (BitVec 64) :=
.seq body567_4 body567_38

def body567_40 : Prog (BitVec 64) :=
.seq body567_3 body567_39

def body567_41 : Prog (BitVec 64) :=
.dec ("gas_cost") (Flapjack.Shape.one) (Flapjack.Exp.const 5000#64) body567_40

def body567_42 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "beneficiary"]) body567_41

def body567_43 : Prog (BitVec 64) :=
.decCall ("beneficiary") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "bv"]) body567_42

def body567_44 : Prog (BitVec 64) :=
.decCall ("bv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body567_43

def body567_45 : Prog (BitVec 64) :=
.seq body567_0 body567_44

def body567_46 : Prog (BitVec 64) :=
.seq body567_3 body567_4

def body567_47 : Prog (BitVec 64) :=
.seq body567_46 body567_6

def body567_48 : Prog (BitVec 64) :=
.seq body567_10 body567_11

def body567_49 : Prog (BitVec 64) :=
.seq body567_48 body567_12

def body567_50 : Prog (BitVec 64) :=
.seq body567_49 body567_13

def body567_51 : Prog (BitVec 64) :=
.seq body567_18 body567_19

def body567_52 : Prog (BitVec 64) :=
.seq body567_51 body567_20

def body567_53 : Prog (BitVec 64) :=
.decCall ("created") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 56#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "originator"]) body567_52

def body567_54 : Prog (BitVec 64) :=
.seq body567_16 body567_53

def body567_55 : Prog (BitVec 64) :=
.decCall ("same") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "beneficiary", Flapjack.Exp.var Flapjack.VarKind.local "originator",
  Flapjack.Exp.const 20#64]) body567_54

def body567_56 : Prog (BitVec 64) :=
.seq body567_14 body567_55

def body567_57 : Prog (BitVec 64) :=
.dec ("bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "oa", Flapjack.Exp.const 8#64])) body567_56

def body567_58 : Prog (BitVec 64) :=
.seq body567_50 body567_57

def body567_59 : Prog (BitVec 64) :=
.dec ("aw") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body567_58

def body567_60 : Prog (BitVec 64) :=
.dec ("state_gas") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body567_59

def body567_61 : Prog (BitVec 64) :=
.decCall ("obz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "oa", Flapjack.Exp.const 8#64])]) body567_60

def body567_62 : Prog (BitVec 64) :=
.decCall ("oa") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "originator"]) body567_61

def body567_63 : Prog (BitVec 64) :=
.decCall ("alive") (Flapjack.Shape.one) ("is_account_alive") ([Flapjack.Exp.var Flapjack.VarKind.local "beneficiary"]) body567_62

def body567_64 : Prog (BitVec 64) :=
.dec ("originator") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 32#64])) body567_63

def body567_65 : Prog (BitVec 64) :=
.seq body567_47 body567_64

def body567_66 : Prog (BitVec 64) :=
.dec ("gas_cost") (Flapjack.Shape.one) (Flapjack.Exp.const 5000#64) body567_65

def body567_67 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "beneficiary"]) body567_66

def body567_68 : Prog (BitVec 64) :=
.decCall ("beneficiary") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "bv"]) body567_67

def body567_69 : Prog (BitVec 64) :=
.decCall ("bv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body567_68

def body567_70 : Prog (BitVec 64) :=
.seq body567_0 body567_69

def originalData567 : Decl (BitVec 64) :=
.function { name := "op_selfdestruct", inline := false, exported := false, params := [], body := body567_45, returnShape := (Flapjack.Shape.one) }
def simplifiedData567 : Decl (BitVec 64) :=
.function { name := "op_selfdestruct", inline := false, exported := false, params := [], body := body567_70, returnShape := (Flapjack.Shape.one) }
def original567 := Pancake.PanLang.declToHOL originalData567
def simplified567 := Pancake.PanLang.declToHOL simplifiedData567
end InitECandidate.Proofs.FrontendStages.Declarations
