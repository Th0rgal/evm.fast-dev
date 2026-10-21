import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data567
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate547
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody567_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "require_not_static" []

def globalBody567_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "gas_cost"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "gas_cost", Flapjack.Exp.const 3000#64])

def globalBody567_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody567_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) globalBody567_1 globalBody567_2

def globalBody567_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "gas_cost"]

def globalBody567_5 : Prog (BitVec 64) :=
.seq globalBody567_3 globalBody567_4

def globalBody567_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "beneficiary"]

def globalBody567_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) globalBody567_6 globalBody567_2

def globalBody567_8 : Prog (BitVec 64) :=
.seq globalBody567_5 globalBody567_7

def globalBody567_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "state_gas" (Flapjack.Exp.const 183600#64)

def globalBody567_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "aw" (Flapjack.Exp.const 9000#64)

def globalBody567_11 : Prog (BitVec 64) :=
.seq globalBody567_9 globalBody567_10

def globalBody567_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "alive") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "obz") (Flapjack.Exp.const 0#64))]) globalBody567_11 globalBody567_2

def globalBody567_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "aw"]

def globalBody567_14 : Prog (BitVec 64) :=
.seq globalBody567_12 globalBody567_13

def globalBody567_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_state_gas" [Flapjack.Exp.var Flapjack.VarKind.local "state_gas"]

def globalBody567_16 : Prog (BitVec 64) :=
.seq globalBody567_14 globalBody567_15

def globalBody567_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "oa"), none)) "get_account"
  [Flapjack.Exp.var Flapjack.VarKind.local "originator"]

def globalBody567_18 : Prog (BitVec 64) :=
.seq globalBody567_16 globalBody567_17

def globalBody567_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "move_ether"
  [Flapjack.Exp.var Flapjack.VarKind.local "originator", Flapjack.Exp.var Flapjack.VarKind.local "beneficiary",
    Flapjack.Exp.var Flapjack.VarKind.local "bal"]

def globalBody567_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "emit_transfer_log"
  [Flapjack.Exp.var Flapjack.VarKind.local "originator", Flapjack.Exp.var Flapjack.VarKind.local "beneficiary",
    Flapjack.Exp.var Flapjack.VarKind.local "bal"]

def globalBody567_21 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "same") (Flapjack.Exp.const 0#64)) globalBody567_20 globalBody567_2

def globalBody567_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
          Flapjack.Exp.const 136#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "originator", Flapjack.Exp.const 1#64]

def globalBody567_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "created") (Flapjack.Exp.const 0#64)) globalBody567_22 globalBody567_2

def globalBody567_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 104#64])
  (Flapjack.Exp.const 0#64)

def globalBody567_25 : Prog (BitVec 64) :=
.seq globalBody567_23 globalBody567_24

def globalBody567_26 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody567_27 : Prog (BitVec 64) :=
.seq globalBody567_25 globalBody567_26

def globalBody567_28 : Prog (BitVec 64) :=
.decCall ("created") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 184#64]),
        Flapjack.Exp.const 56#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "originator"]) globalBody567_27

def globalBody567_29 : Prog (BitVec 64) :=
.seq globalBody567_21 globalBody567_28

def globalBody567_30 : Prog (BitVec 64) :=
.decCall ("same") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "beneficiary", Flapjack.Exp.var Flapjack.VarKind.local "originator",
  Flapjack.Exp.const 20#64]) globalBody567_29

def globalBody567_31 : Prog (BitVec 64) :=
.seq globalBody567_19 globalBody567_30

def globalBody567_32 : Prog (BitVec 64) :=
.dec ("bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "oa", Flapjack.Exp.const 8#64])) globalBody567_31

def globalBody567_33 : Prog (BitVec 64) :=
.seq globalBody567_18 globalBody567_32

def globalBody567_34 : Prog (BitVec 64) :=
.dec ("aw") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody567_33

def globalBody567_35 : Prog (BitVec 64) :=
.dec ("state_gas") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody567_34

def globalBody567_36 : Prog (BitVec 64) :=
.decCall ("obz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "oa", Flapjack.Exp.const 8#64])]) globalBody567_35

def globalBody567_37 : Prog (BitVec 64) :=
.decCall ("oa") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "originator"]) globalBody567_36

def globalBody567_38 : Prog (BitVec 64) :=
.decCall ("alive") (Flapjack.Shape.one) ("is_account_alive") ([Flapjack.Exp.var Flapjack.VarKind.local "beneficiary"]) globalBody567_37

def globalBody567_39 : Prog (BitVec 64) :=
.dec ("originator") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.load Flapjack.Shape.one
              (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
            Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 32#64])) globalBody567_38

def globalBody567_40 : Prog (BitVec 64) :=
.seq globalBody567_8 globalBody567_39

def globalBody567_41 : Prog (BitVec 64) :=
.dec ("gas_cost") (Flapjack.Shape.one) (Flapjack.Exp.const 5000#64) globalBody567_40

def globalBody567_42 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "beneficiary"]) globalBody567_41

def globalBody567_43 : Prog (BitVec 64) :=
.decCall ("beneficiary") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "bv"]) globalBody567_42

def globalBody567_44 : Prog (BitVec 64) :=
.decCall ("bv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody567_43

def globalBody567_45 : Prog (BitVec 64) :=
.seq globalBody567_0 globalBody567_44

def globalData567 : Decl (BitVec 64) :=
.function { name := "op_selfdestruct", inline := false, exported := false, params := [], body := globalBody567_45, returnShape := (Flapjack.Shape.one) }
def globalOutput567 := Pancake.PanLang.declToHOL globalData567
end InitECandidate.Proofs.FrontendStages.Declarations
