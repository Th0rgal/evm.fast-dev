import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data595
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate579
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody595_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def globalBody595_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody595_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 131072#64) (Flapjack.Exp.var Flapjack.VarKind.local "msize")) globalBody595_0 globalBody595_1

def globalBody595_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_retdata"
  [Flapjack.Exp.var Flapjack.VarKind.local "empty", Flapjack.Exp.const 0#64]

def globalBody595_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.rStruct
      [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]

def globalBody595_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody595_6 : Prog (BitVec 64) :=
.seq globalBody595_4 globalBody595_5

def globalBody595_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "insufficient")
        (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal
        (Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "sender", Flapjack.Exp.const 0#64]))
        (Flapjack.Exp.const 18446744073709551615#64),
      Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1024#64)
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.load Flapjack.Shape.one
              (Flapjack.Exp.op Flapjack.BinOp.add
                [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 128#64]),
            Flapjack.Exp.const 1#64])])) globalBody595_6 globalBody595_1

def globalBody595_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "contract_address"]

def globalBody595_9 : Prog (BitVec 64) :=
.seq globalBody595_7 globalBody595_8

def globalBody595_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "new_account_charged" (Flapjack.Exp.const 1#64)

def globalBody595_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_state_gas" [Flapjack.Exp.const 183600#64]

def globalBody595_12 : Prog (BitVec 64) :=
.seq globalBody595_10 globalBody595_11

def globalBody595_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "alive") (Flapjack.Exp.const 0#64)) globalBody595_12 globalBody595_1

def globalBody595_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "gl", Flapjack.Exp.var Flapjack.VarKind.local "create_gas"])

def globalBody595_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "increment_nonce" [Flapjack.Exp.var Flapjack.VarKind.local "sender_address"]

def globalBody595_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 184#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.load Flapjack.Shape.one
              (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
            Flapjack.Exp.const 184#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "create_gas"])

def globalBody595_17 : Prog (BitVec 64) :=
.seq globalBody595_15 globalBody595_16

def globalBody595_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "credit_state_gas_refund" [Flapjack.Exp.const 183600#64]

def globalBody595_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "new_account_charged")
  (Flapjack.Exp.const 0#64)) globalBody595_18 globalBody595_1

def globalBody595_20 : Prog (BitVec 64) :=
.seq globalBody595_17 globalBody595_19

def globalBody595_21 : Prog (BitVec 64) :=
.seq globalBody595_20 globalBody595_4

def globalBody595_22 : Prog (BitVec 64) :=
.seq globalBody595_21 globalBody595_5

def globalBody595_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "deployable") (Flapjack.Exp.const 0#64)) globalBody595_22 globalBody595_1

def globalBody595_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 0#64)

def globalBody595_25 : Prog (BitVec 64) :=
.seq globalBody595_24 globalBody595_15

def globalBody595_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "start_child"
  [Flapjack.Exp.var Flapjack.VarKind.local "cm", Flapjack.Exp.const 2#64,
    Flapjack.Exp.var Flapjack.VarKind.local "child_mark", Flapjack.Exp.var Flapjack.VarKind.local "child_mem_mark",
    Flapjack.Exp.var Flapjack.VarKind.local "new_account_charged", Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
    Flapjack.Exp.var Flapjack.VarKind.local "contract_address"]

def globalBody595_27 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody595_28 : Prog (BitVec 64) :=
.seq globalBody595_26 globalBody595_27

def globalBody595_29 : Prog (BitVec 64) :=
.decCall ("cm") (Flapjack.Shape.one) ("child_message") ([Flapjack.Exp.var Flapjack.VarKind.local "sender_address", Flapjack.Exp.const 0#64,
  Flapjack.Exp.var Flapjack.VarKind.local "contract_address", Flapjack.Exp.var Flapjack.VarKind.local "create_gas",
  Flapjack.Exp.var Flapjack.VarKind.local "reservoir", Flapjack.Exp.var Flapjack.VarKind.local "endowment",
  Flapjack.Exp.var Flapjack.VarKind.local "empty", Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
  Flapjack.Exp.var Flapjack.VarKind.local "call_data", Flapjack.Exp.var Flapjack.VarKind.local "msize",
  Flapjack.Exp.const 1#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody595_28

def globalBody595_30 : Prog (BitVec 64) :=
.decCall ("child_mem_mark") (Flapjack.Shape.one) ("frame_mem_mark") ([]) globalBody595_29

def globalBody595_31 : Prog (BitVec 64) :=
.decCall ("child_mark") (Flapjack.Shape.one) ("scratch_mark") ([]) globalBody595_30

def globalBody595_32 : Prog (BitVec 64) :=
.seq globalBody595_25 globalBody595_31

def globalBody595_33 : Prog (BitVec 64) :=
.dec ("reservoir") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 72#64])) globalBody595_32

def globalBody595_34 : Prog (BitVec 64) :=
.seq globalBody595_23 globalBody595_33

def globalBody595_35 : Prog (BitVec 64) :=
.decCall ("deployable") (Flapjack.Shape.one) ("account_deployable") ([Flapjack.Exp.var Flapjack.VarKind.local "contract_address"]) globalBody595_34

def globalBody595_36 : Prog (BitVec 64) :=
.seq globalBody595_14 globalBody595_35

def globalBody595_37 : Prog (BitVec 64) :=
.dec ("create_gas") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "gl",
    Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "gl") (Flapjack.Exp.const 6#64)]) globalBody595_36

def globalBody595_38 : Prog (BitVec 64) :=
.dec ("gl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 64#64])) globalBody595_37

def globalBody595_39 : Prog (BitVec 64) :=
.seq globalBody595_13 globalBody595_38

def globalBody595_40 : Prog (BitVec 64) :=
.dec ("new_account_charged") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody595_39

def globalBody595_41 : Prog (BitVec 64) :=
.decCall ("alive") (Flapjack.Shape.one) ("is_account_alive") ([Flapjack.Exp.var Flapjack.VarKind.local "contract_address"]) globalBody595_40

def globalBody595_42 : Prog (BitVec 64) :=
.seq globalBody595_9 globalBody595_41

def globalBody595_43 : Prog (BitVec 64) :=
.decCall ("insufficient") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "sender", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "endowment"]) globalBody595_42

def globalBody595_44 : Prog (BitVec 64) :=
.decCall ("sender") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "sender_address"]) globalBody595_43

def globalBody595_45 : Prog (BitVec 64) :=
.dec ("sender_address") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])) globalBody595_44

def globalBody595_46 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 112#64])) globalBody595_45

def globalBody595_47 : Prog (BitVec 64) :=
.seq globalBody595_3 globalBody595_46

def globalBody595_48 : Prog (BitVec 64) :=
.dec ("empty") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 264#64])) globalBody595_47

def globalBody595_49 : Prog (BitVec 64) :=
.dec ("call_data") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
          Flapjack.Exp.const 24#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "mstart"]) globalBody595_48

def globalBody595_50 : Prog (BitVec 64) :=
.seq globalBody595_2 globalBody595_49

def globalData595 : Decl (BitVec 64) :=
.function { name := "generic_create", inline := false, exported := false, params := [("endowment", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("contract_address", Flapjack.Shape.one), ("mstart", Flapjack.Shape.one), ("msize", Flapjack.Shape.one)], body := globalBody595_50, returnShape := (Flapjack.Shape.one) }
def globalOutput595 := Pancake.PanLang.declToHOL globalData595
end InitECandidate.Proofs.FrontendStages.Declarations
