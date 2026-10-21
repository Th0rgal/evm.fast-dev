import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify854
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body870_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_fresh_tx" []

def body870_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "bal_index"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "index", Flapjack.Exp.const 1#64])

def body870_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 24#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "index", Flapjack.Exp.const 16#64]])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "enc"))

def body870_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 24#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "index", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "enc"))

def body870_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body870_5 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 100#64)

def body870_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "cid"))
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 0#64]))) body870_5 body870_4

def body870_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "cid"))
  (Flapjack.Exp.const 0#64)) body870_6 body870_4

def body870_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "recover_sender_with_chain_id"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 0#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "sender"]

def body870_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "blob_gas_fee"
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "bgf"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "bgf"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "bgf"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "bgf")])

def body870_10 : Prog (BitVec 64) :=
.decCall ("bgf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "tx_blob_gas_used", Flapjack.Exp.var Flapjack.VarKind.local "bgp"]) body870_9

def body870_11 : Prog (BitVec 64) :=
.decCall ("bgp") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_blob_gas_price") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 96#64])]) body870_10

def body870_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "tx_blob_gas_used")
  (Flapjack.Exp.const 0#64)) body870_11 body870_4

def body870_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "increment_nonce" [Flapjack.Exp.var Flapjack.VarKind.local "sender"]

def body870_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "bal"), none)) "u256_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "bal", Flapjack.Exp.var Flapjack.VarKind.local "effective_gas_fee"]

def body870_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "bal"), none)) "u256_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "bal", Flapjack.Exp.var Flapjack.VarKind.local "blob_gas_fee"]

def body870_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_account_balance"
  [Flapjack.Exp.var Flapjack.VarKind.local "sender", Flapjack.Exp.var Flapjack.VarKind.local "bal"]

def body870_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "sender")

def body870_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 152#64]))

def body870_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 160#64]))

def body870_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "price")

def body870_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "mgas")

def body870_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "reservoir")

def body870_23 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "nal"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 216#64]))

def body870_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "hal") (Flapjack.Exp.const 0#64)) body870_23 body870_4

def body870_25 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "al_addrs")
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 32#64]))

def body870_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "al_addrs",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64],
          Flapjack.Exp.const 8#64]])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.const 0#64]))

def body870_27 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "nkeys"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "nkeys",
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.const 16#64])])

def body870_28 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body870_29 : Prog (BitVec 64) :=
.seq body870_27 body870_28

def body870_30 : Prog (BitVec 64) :=
.seq body870_26 body870_29

def body870_31 : Prog (BitVec 64) :=
.dec ("acc") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 208#64]),
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 24#64]]) body870_30

def body870_32 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nal")) body870_31

def body870_33 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def body870_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "al_keys",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 52#64]],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acc2", Flapjack.Exp.const 0#64]),
    Flapjack.Exp.const 20#64]

def body870_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "al_keys",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 52#64],
        Flapjack.Exp.const 20#64],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "acc2", Flapjack.Exp.const 8#64]),
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 32#64]],
    Flapjack.Exp.const 32#64]

def body870_36 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64])

def body870_37 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def body870_38 : Prog (BitVec 64) :=
.seq body870_36 body870_37

def body870_39 : Prog (BitVec 64) :=
.seq body870_35 body870_38

def body870_40 : Prog (BitVec 64) :=
.seq body870_34 body870_39

def body870_41 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "ns")) body870_40

def body870_42 : Prog (BitVec 64) :=
.seq body870_41 body870_28

def body870_43 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body870_42

def body870_44 : Prog (BitVec 64) :=
.dec ("ns") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acc2", Flapjack.Exp.const 16#64])) body870_43

def body870_45 : Prog (BitVec 64) :=
.dec ("acc2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 208#64]),
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 24#64]]) body870_44

def body870_46 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nal")) body870_45

def body870_47 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "al_addrs")

def body870_48 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nal", Flapjack.Exp.const 1#64])

def body870_49 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "al_keys")

def body870_50 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nkeys")

def body870_51 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 256#64]))

def body870_52 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 264#64]))

def body870_53 : Prog (BitVec 64) :=
.seq body870_51 body870_52

def body870_54 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "isb") (Flapjack.Exp.const 0#64)) body870_53 body870_4

def body870_55 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 272#64]))

def body870_56 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 280#64]))

def body870_57 : Prog (BitVec 64) :=
.seq body870_55 body870_56

def body870_58 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "issc") (Flapjack.Exp.const 0#64)) body870_57 body870_4

def body870_59 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.const 1#64)

def body870_60 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "index")

def body870_61 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "enc"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "enc"),
    Flapjack.Exp.var Flapjack.VarKind.local "txh"]

def body870_62 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 176#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "txh")

def body870_63 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 184#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic"))

def body870_64 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic"))

def body870_65 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "be")

def body870_66 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "te")

def body870_67 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "sender")

def body870_68 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 152#64]))

def body870_69 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "mgas")

def body870_70 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "reservoir")

def body870_71 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 160#64]))

def body870_72 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "aa", Flapjack.Exp.var Flapjack.VarKind.local "sender",
    Flapjack.Exp.const 1#64]

def body870_73 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "aa",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "precompile_addrs",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 20#64]],
    Flapjack.Exp.const 1#64]

def body870_74 : Prog (BitVec 64) :=
.seq body870_73 body870_28

def body870_75 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 18#64)) body870_74

def body870_76 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "aa",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "al_addrs",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]]),
    Flapjack.Exp.const 1#64]

def body870_77 : Prog (BitVec 64) :=
.seq body870_76 body870_28

def body870_78 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nal", Flapjack.Exp.const 1#64])) body870_77

def body870_79 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "ak",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "al_keys",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 52#64]],
    Flapjack.Exp.const 1#64]

def body870_80 : Prog (BitVec 64) :=
.seq body870_79 body870_28

def body870_81 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nkeys")) body870_80

def body870_82 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "compute_contract_address"
  [Flapjack.Exp.var Flapjack.VarKind.local "sender",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "sa", Flapjack.Exp.const 0#64]),
        Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "ct"]

def body870_83 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ct")

def body870_84 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "empty")

def body870_85 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.const 0#64)

def body870_86 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 192#64]))

def body870_87 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 200#64]))

def body870_88 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.const 0#64)

def body870_89 : Prog (BitVec 64) :=
.seq body870_87 body870_88

def body870_90 : Prog (BitVec 64) :=
.seq body870_86 body870_89

def body870_91 : Prog (BitVec 64) :=
.seq body870_85 body870_90

def body870_92 : Prog (BitVec 64) :=
.seq body870_84 body870_91

def body870_93 : Prog (BitVec 64) :=
.seq body870_83 body870_92

def body870_94 : Prog (BitVec 64) :=
.seq body870_82 body870_93

def body870_95 : Prog (BitVec 64) :=
.decCall ("ct") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body870_94

def body870_96 : Prog (BitVec 64) :=
.decCall ("sa") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body870_95

def body870_97 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 152#64]))

def body870_98 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 192#64]))

def body870_99 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 200#64]))

def body870_100 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "empty")

def body870_101 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.const 0#64)

def body870_102 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 152#64]))

def body870_103 : Prog (BitVec 64) :=
.seq body870_101 body870_102

def body870_104 : Prog (BitVec 64) :=
.seq body870_100 body870_103

def body870_105 : Prog (BitVec 64) :=
.seq body870_99 body870_104

def body870_106 : Prog (BitVec 64) :=
.seq body870_98 body870_105

def body870_107 : Prog (BitVec 64) :=
.seq body870_97 body870_106

def body870_108 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 152#64]))
  (Flapjack.Exp.const 0#64)) body870_96 body870_107

def body870_109 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.const 1#64)

def body870_110 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "aa",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.const 1#64]

def body870_111 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "aa")

def body870_112 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ak")

def body870_113 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "create_ether"
  [Flapjack.Exp.var Flapjack.VarKind.local "sender",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "gra"),
        Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "gra"),
        Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "gra"),
        Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "gra")]]

def body870_114 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "create_ether"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.rStruct
      [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "tf"),
        Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "tf"),
        Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "tf"),
        Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "tf")]]

def body870_115 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "tx_state_gas_nat" (Flapjack.Exp.const 0#64)

def body870_116 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "tx_state_gas") (Flapjack.Exp.const 0#64)) body870_115 body870_4

def body870_117 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 0#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "tx_regular_gas"])

def body870_118 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 8#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "tx_state_gas_nat"])

def body870_119 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 48#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "tx_blob_gas_used"])

def body870_120 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 16#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "tx_gas_used"])

def body870_121 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "logs"), none)) "lst_new"
  [Flapjack.Exp.const 8#64, Flapjack.Exp.const 1#64]

def body870_122 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "logs") (Flapjack.Exp.const 0#64)) body870_121 body870_4

def body870_123 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "succeeded" (Flapjack.Exp.const 0#64)

def body870_124 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64]))
  (Flapjack.Exp.const 0#64)) body870_123 body870_4

def body870_125 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 32#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "index", Flapjack.Exp.const 16#64]])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rc"))

def body870_126 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 32#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "index", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rc"))

def body870_127 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "slot")
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "lp",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]]))

def body870_128 : Prog (BitVec 64) :=
.seq body870_127 body870_28

def body870_129 : Prog (BitVec 64) :=
.decCall ("slot") (Flapjack.Shape.one) ("lst_push") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 40#64]),
  Flapjack.Exp.const 8#64]) body870_128

def body870_130 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nl")) body870_129

def body870_131 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "stable_log_cap" (Flapjack.Exp.const 1#64)

def body870_132 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "stable_log_cap") (Flapjack.Exp.const 0#64)) body870_131 body870_4

def body870_133 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "stable_logs", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nl")

def body870_134 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "stable_lp",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "lp",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]]))

def body870_135 : Prog (BitVec 64) :=
.seq body870_134 body870_28

def body870_136 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nl")) body870_135

def body870_137 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "rl")
  (Flapjack.Exp.var Flapjack.VarKind.local "stable_logs")

def body870_138 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "clear_account_preserving_balance"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s")]

def body870_139 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s"))
  (Flapjack.Exp.const 0#64)) body870_138 body870_4

def body870_140 : Prog (BitVec 64) :=
.seq body870_139 body870_28

def body870_141 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "del", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body870_140

def body870_142 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "dcap")) body870_141

def body870_143 : Prog (BitVec 64) :=
.seq body870_33 body870_142

def body870_144 : Prog (BitVec 64) :=
.dec ("dcap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "del", Flapjack.Exp.const 24#64])) body870_143

def body870_145 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "del") (Flapjack.Exp.const 0#64)) body870_144 body870_4

def body870_146 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "incorporate_tx_into_block" []

def body870_147 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "scratch_release" [Flapjack.Exp.var Flapjack.VarKind.local "tx_frame_mark"]

def body870_148 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_mem_release"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 88#64])]

def body870_149 : Prog (BitVec 64) :=
.seq body870_147 body870_148

def body870_150 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "tx_frame_mark")
  (Flapjack.Exp.const 0#64)) body870_149 body870_4

def body870_151 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body870_152 : Prog (BitVec 64) :=
.seq body870_150 body870_151

def body870_153 : Prog (BitVec 64) :=
.dec ("tx_frame_mark") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 80#64])) body870_152

def body870_154 : Prog (BitVec 64) :=
.seq body870_146 body870_153

def body870_155 : Prog (BitVec 64) :=
.seq body870_145 body870_154

def body870_156 : Prog (BitVec 64) :=
.dec ("del") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 24#64])) body870_155

def body870_157 : Prog (BitVec 64) :=
.seq body870_137 body870_156

def body870_158 : Prog (BitVec 64) :=
.decCall ("rl") (Flapjack.Shape.one) ("lst_push") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 72#64]),
  Flapjack.Exp.const 8#64]) body870_157

def body870_159 : Prog (BitVec 64) :=
.seq body870_136 body870_158

def body870_160 : Prog (BitVec 64) :=
.seq body870_33 body870_159

def body870_161 : Prog (BitVec 64) :=
.dec ("stable_lp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "stable_logs", Flapjack.Exp.const 0#64])) body870_160

def body870_162 : Prog (BitVec 64) :=
.seq body870_133 body870_161

def body870_163 : Prog (BitVec 64) :=
.decCall ("stable_logs") (Flapjack.Shape.one) ("lst_new") ([Flapjack.Exp.const 8#64, Flapjack.Exp.var Flapjack.VarKind.local "stable_log_cap"]) body870_162

def body870_164 : Prog (BitVec 64) :=
.seq body870_132 body870_163

def body870_165 : Prog (BitVec 64) :=
.dec ("stable_log_cap") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "nl") body870_164

def body870_166 : Prog (BitVec 64) :=
.seq body870_130 body870_165

def body870_167 : Prog (BitVec 64) :=
.seq body870_33 body870_166

def body870_168 : Prog (BitVec 64) :=
.dec ("lp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.const 0#64])) body870_167

def body870_169 : Prog (BitVec 64) :=
.dec ("nl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.const 8#64])) body870_168

def body870_170 : Prog (BitVec 64) :=
.seq body870_126 body870_169

def body870_171 : Prog (BitVec 64) :=
.seq body870_125 body870_170

def body870_172 : Prog (BitVec 64) :=
.decCall ("rc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_receipt") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "succeeded",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 16#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "logs"]) body870_171

def body870_173 : Prog (BitVec 64) :=
.seq body870_124 body870_172

def body870_174 : Prog (BitVec 64) :=
.dec ("succeeded") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body870_173

def body870_175 : Prog (BitVec 64) :=
.seq body870_122 body870_174

def body870_176 : Prog (BitVec 64) :=
.dec ("logs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 16#64])) body870_175

def body870_177 : Prog (BitVec 64) :=
.seq body870_4 body870_176

def body870_178 : Prog (BitVec 64) :=
.seq body870_120 body870_177

def body870_179 : Prog (BitVec 64) :=
.seq body870_119 body870_178

def body870_180 : Prog (BitVec 64) :=
.seq body870_118 body870_179

def body870_181 : Prog (BitVec 64) :=
.seq body870_117 body870_180

def body870_182 : Prog (BitVec 64) :=
.decCall ("tx_regular_gas") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "used_before_refund",
      Flapjack.Exp.var Flapjack.VarKind.local "tx_state_gas_nat"],
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic")]) body870_181

def body870_183 : Prog (BitVec 64) :=
.seq body870_116 body870_182

def body870_184 : Prog (BitVec 64) :=
.dec ("tx_state_gas_nat") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "tx_state_gas") body870_183

def body870_185 : Prog (BitVec 64) :=
.dec ("tx_state_gas") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic"),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 72#64])]) body870_184

def body870_186 : Prog (BitVec 64) :=
.seq body870_114 body870_185

def body870_187 : Prog (BitVec 64) :=
.seq body870_113 body870_186

def body870_188 : Prog (BitVec 64) :=
.decCall ("tf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "tx_gas_used", Flapjack.Exp.var Flapjack.VarKind.local "priority_fee"]) body870_187

def body870_189 : Prog (BitVec 64) :=
.decCall ("priority_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "price",
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 48#64])]) body870_188

def body870_190 : Prog (BitVec 64) :=
.decCall ("gra") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "tx_gas_left", Flapjack.Exp.var Flapjack.VarKind.local "price"]) body870_189

def body870_191 : Prog (BitVec 64) :=
.dec ("tx_gas_left") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "tx_gas_used"]) body870_190

def body870_192 : Prog (BitVec 64) :=
.decCall ("tx_gas_used") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "used_after_refund",
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic")]) body870_191

def body870_193 : Prog (BitVec 64) :=
.dec ("used_after_refund") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "used_before_refund", Flapjack.Exp.var Flapjack.VarKind.local "refund"]) body870_192

def body870_194 : Prog (BitVec 64) :=
.decCall ("refund") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.var Flapjack.VarKind.local "ubr5",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 8#64])]) body870_193

def body870_195 : Prog (BitVec 64) :=
.decCall ("ubr5") (Flapjack.Shape.one) ("udiv_small5") ([Flapjack.Exp.var Flapjack.VarKind.local "used_before_refund"]) body870_194

def body870_196 : Prog (BitVec 64) :=
.dec ("used_before_refund") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "gas",
        Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 0#64])],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 56#64])]) body870_195

def body870_197 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("process_message_call") ([Flapjack.Exp.var Flapjack.VarKind.local "m"]) body870_196

def body870_198 : Prog (BitVec 64) :=
.seq body870_112 body870_197

def body870_199 : Prog (BitVec 64) :=
.seq body870_111 body870_198

def body870_200 : Prog (BitVec 64) :=
.seq body870_4 body870_199

def body870_201 : Prog (BitVec 64) :=
.seq body870_110 body870_200

def body870_202 : Prog (BitVec 64) :=
.seq body870_109 body870_201

def body870_203 : Prog (BitVec 64) :=
.seq body870_4 body870_202

def body870_204 : Prog (BitVec 64) :=
.seq body870_108 body870_203

def body870_205 : Prog (BitVec 64) :=
.decCall ("empty") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body870_204

def body870_206 : Prog (BitVec 64) :=
.seq body870_4 body870_205

def body870_207 : Prog (BitVec 64) :=
.seq body870_81 body870_206

def body870_208 : Prog (BitVec 64) :=
.seq body870_33 body870_207

def body870_209 : Prog (BitVec 64) :=
.decCall ("ak") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 52#64, Flapjack.Exp.const 16#64]) body870_208

def body870_210 : Prog (BitVec 64) :=
.seq body870_4 body870_209

def body870_211 : Prog (BitVec 64) :=
.seq body870_78 body870_210

def body870_212 : Prog (BitVec 64) :=
.seq body870_33 body870_211

def body870_213 : Prog (BitVec 64) :=
.seq body870_75 body870_212

def body870_214 : Prog (BitVec 64) :=
.seq body870_33 body870_213

def body870_215 : Prog (BitVec 64) :=
.seq body870_4 body870_214

def body870_216 : Prog (BitVec 64) :=
.seq body870_72 body870_215

def body870_217 : Prog (BitVec 64) :=
.seq body870_4 body870_216

def body870_218 : Prog (BitVec 64) :=
.decCall ("aa") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 64#64]) body870_217

def body870_219 : Prog (BitVec 64) :=
.seq body870_71 body870_218

def body870_220 : Prog (BitVec 64) :=
.seq body870_70 body870_219

def body870_221 : Prog (BitVec 64) :=
.seq body870_69 body870_220

def body870_222 : Prog (BitVec 64) :=
.seq body870_68 body870_221

def body870_223 : Prog (BitVec 64) :=
.seq body870_67 body870_222

def body870_224 : Prog (BitVec 64) :=
.seq body870_66 body870_223

def body870_225 : Prog (BitVec 64) :=
.seq body870_65 body870_224

def body870_226 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("msg_new") ([]) body870_225

def body870_227 : Prog (BitVec 64) :=
.seq body870_4 body870_226

def body870_228 : Prog (BitVec 64) :=
.seq body870_64 body870_227

def body870_229 : Prog (BitVec 64) :=
.seq body870_63 body870_228

def body870_230 : Prog (BitVec 64) :=
.seq body870_62 body870_229

def body870_231 : Prog (BitVec 64) :=
.seq body870_61 body870_230

def body870_232 : Prog (BitVec 64) :=
.decCall ("txh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body870_231

def body870_233 : Prog (BitVec 64) :=
.seq body870_60 body870_232

def body870_234 : Prog (BitVec 64) :=
.seq body870_59 body870_233

def body870_235 : Prog (BitVec 64) :=
.seq body870_58 body870_234

def body870_236 : Prog (BitVec 64) :=
.decCall ("issc") (Flapjack.Shape.one) ("tx_is_setcode") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_235

def body870_237 : Prog (BitVec 64) :=
.seq body870_54 body870_236

def body870_238 : Prog (BitVec 64) :=
.decCall ("isb") (Flapjack.Shape.one) ("tx_is_blob") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_237

def body870_239 : Prog (BitVec 64) :=
.seq body870_50 body870_238

def body870_240 : Prog (BitVec 64) :=
.seq body870_49 body870_239

def body870_241 : Prog (BitVec 64) :=
.seq body870_48 body870_240

def body870_242 : Prog (BitVec 64) :=
.seq body870_47 body870_241

def body870_243 : Prog (BitVec 64) :=
.seq body870_46 body870_242

def body870_244 : Prog (BitVec 64) :=
.seq body870_33 body870_243

def body870_245 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body870_244

def body870_246 : Prog (BitVec 64) :=
.decCall ("al_keys") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "nkeys", Flapjack.Exp.const 52#64],
      Flapjack.Exp.const 8#64]]) body870_245

def body870_247 : Prog (BitVec 64) :=
.seq body870_32 body870_246

def body870_248 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body870_247

def body870_249 : Prog (BitVec 64) :=
.dec ("nkeys") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body870_248

def body870_250 : Prog (BitVec 64) :=
.seq body870_25 body870_249

def body870_251 : Prog (BitVec 64) :=
.decCall ("al_addrs") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nal", Flapjack.Exp.const 1#64],
      Flapjack.Exp.const 8#64]]) body870_250

def body870_252 : Prog (BitVec 64) :=
.seq body870_24 body870_251

def body870_253 : Prog (BitVec 64) :=
.decCall ("hal") (Flapjack.Shape.one) ("tx_has_access_list") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_252

def body870_254 : Prog (BitVec 64) :=
.dec ("nal") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body870_253

def body870_255 : Prog (BitVec 64) :=
.seq body870_22 body870_254

def body870_256 : Prog (BitVec 64) :=
.seq body870_21 body870_255

def body870_257 : Prog (BitVec 64) :=
.seq body870_20 body870_256

def body870_258 : Prog (BitVec 64) :=
.seq body870_19 body870_257

def body870_259 : Prog (BitVec 64) :=
.seq body870_18 body870_258

def body870_260 : Prog (BitVec 64) :=
.seq body870_17 body870_259

def body870_261 : Prog (BitVec 64) :=
.decCall ("te") (Flapjack.Shape.one) ("te_new") ([]) body870_260

def body870_262 : Prog (BitVec 64) :=
.seq body870_4 body870_261

def body870_263 : Prog (BitVec 64) :=
.seq body870_16 body870_262

def body870_264 : Prog (BitVec 64) :=
.seq body870_15 body870_263

def body870_265 : Prog (BitVec 64) :=
.seq body870_14 body870_264

def body870_266 : Prog (BitVec 64) :=
.dec ("bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 8#64])) body870_265

def body870_267 : Prog (BitVec 64) :=
.seq body870_13 body870_266

def body870_268 : Prog (BitVec 64) :=
.dec ("reservoir") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "execution_gas", Flapjack.Exp.var Flapjack.VarKind.local "mgas"]) body870_267

def body870_269 : Prog (BitVec 64) :=
.decCall ("mgas") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.var Flapjack.VarKind.local "regular_budget", Flapjack.Exp.var Flapjack.VarKind.local "execution_gas"]) body870_268

def body870_270 : Prog (BitVec 64) :=
.dec ("regular_budget") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.const 16777216#64, Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic")]) body870_269

def body870_271 : Prog (BitVec 64) :=
.dec ("execution_gas") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "intrinsic_gas"]) body870_270

def body870_272 : Prog (BitVec 64) :=
.dec ("effective_gas_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "egf"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "egf"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "egf"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "egf")]) body870_271

def body870_273 : Prog (BitVec 64) :=
.decCall ("egf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "price"]) body870_272

def body870_274 : Prog (BitVec 64) :=
.dec ("gas") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 144#64])) body870_273

def body870_275 : Prog (BitVec 64) :=
.seq body870_12 body870_274

def body870_276 : Prog (BitVec 64) :=
.dec ("blob_gas_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body870_275

def body870_277 : Prog (BitVec 64) :=
.seq body870_4 body870_276

def body870_278 : Prog (BitVec 64) :=
.decCall ("acct") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body870_277

def body870_279 : Prog (BitVec 64) :=
.decCall ("tx_blob_gas_used") (Flapjack.Shape.one) ("calculate_total_blob_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_278

def body870_280 : Prog (BitVec 64) :=
.seq body870_4 body870_279

def body870_281 : Prog (BitVec 64) :=
.decCall ("price") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("check_transaction") ([Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body870_280

def body870_282 : Prog (BitVec 64) :=
.dec ("intrinsic_gas") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic")]) body870_281

def body870_283 : Prog (BitVec 64) :=
.seq body870_4 body870_282

def body870_284 : Prog (BitVec 64) :=
.decCall ("intrinsic") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("validate_transaction") ([Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body870_283

def body870_285 : Prog (BitVec 64) :=
.seq body870_4 body870_284

def body870_286 : Prog (BitVec 64) :=
.seq body870_8 body870_285

def body870_287 : Prog (BitVec 64) :=
.decCall ("sender") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body870_286

def body870_288 : Prog (BitVec 64) :=
.seq body870_7 body870_287

def body870_289 : Prog (BitVec 64) :=
.decCall ("cid") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_chain_id") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_288

def body870_290 : Prog (BitVec 64) :=
.seq body870_4 body870_289

def body870_291 : Prog (BitVec 64) :=
.seq body870_3 body870_290

def body870_292 : Prog (BitVec 64) :=
.seq body870_2 body870_291

def body870_293 : Prog (BitVec 64) :=
.decCall ("enc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_transaction") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_292

def body870_294 : Prog (BitVec 64) :=
.seq body870_1 body870_293

def body870_295 : Prog (BitVec 64) :=
.seq body870_0 body870_294

def body870_296 : Prog (BitVec 64) :=
.seq body870_0 body870_1

def body870_297 : Prog (BitVec 64) :=
.seq body870_2 body870_3

def body870_298 : Prog (BitVec 64) :=
.seq body870_14 body870_15

def body870_299 : Prog (BitVec 64) :=
.seq body870_298 body870_16

def body870_300 : Prog (BitVec 64) :=
.seq body870_17 body870_18

def body870_301 : Prog (BitVec 64) :=
.seq body870_300 body870_19

def body870_302 : Prog (BitVec 64) :=
.seq body870_301 body870_20

def body870_303 : Prog (BitVec 64) :=
.seq body870_302 body870_21

def body870_304 : Prog (BitVec 64) :=
.seq body870_303 body870_22

def body870_305 : Prog (BitVec 64) :=
.seq body870_26 body870_27

def body870_306 : Prog (BitVec 64) :=
.seq body870_305 body870_28

def body870_307 : Prog (BitVec 64) :=
.dec ("acc") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 208#64]),
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 24#64]]) body870_306

def body870_308 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nal")) body870_307

def body870_309 : Prog (BitVec 64) :=
.seq body870_34 body870_35

def body870_310 : Prog (BitVec 64) :=
.seq body870_309 body870_36

def body870_311 : Prog (BitVec 64) :=
.seq body870_310 body870_37

def body870_312 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "ns")) body870_311

def body870_313 : Prog (BitVec 64) :=
.seq body870_312 body870_28

def body870_314 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body870_313

def body870_315 : Prog (BitVec 64) :=
.dec ("ns") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acc2", Flapjack.Exp.const 16#64])) body870_314

def body870_316 : Prog (BitVec 64) :=
.dec ("acc2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 208#64]),
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 24#64]]) body870_315

def body870_317 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nal")) body870_316

def body870_318 : Prog (BitVec 64) :=
.seq body870_33 body870_317

def body870_319 : Prog (BitVec 64) :=
.seq body870_318 body870_47

def body870_320 : Prog (BitVec 64) :=
.seq body870_319 body870_48

def body870_321 : Prog (BitVec 64) :=
.seq body870_320 body870_49

def body870_322 : Prog (BitVec 64) :=
.seq body870_321 body870_50

def body870_323 : Prog (BitVec 64) :=
.seq body870_58 body870_59

def body870_324 : Prog (BitVec 64) :=
.seq body870_323 body870_60

def body870_325 : Prog (BitVec 64) :=
.seq body870_61 body870_62

def body870_326 : Prog (BitVec 64) :=
.seq body870_325 body870_63

def body870_327 : Prog (BitVec 64) :=
.seq body870_326 body870_64

def body870_328 : Prog (BitVec 64) :=
.seq body870_65 body870_66

def body870_329 : Prog (BitVec 64) :=
.seq body870_328 body870_67

def body870_330 : Prog (BitVec 64) :=
.seq body870_329 body870_68

def body870_331 : Prog (BitVec 64) :=
.seq body870_330 body870_69

def body870_332 : Prog (BitVec 64) :=
.seq body870_331 body870_70

def body870_333 : Prog (BitVec 64) :=
.seq body870_332 body870_71

def body870_334 : Prog (BitVec 64) :=
.seq body870_72 body870_33

def body870_335 : Prog (BitVec 64) :=
.seq body870_334 body870_75

def body870_336 : Prog (BitVec 64) :=
.seq body870_335 body870_33

def body870_337 : Prog (BitVec 64) :=
.seq body870_336 body870_78

def body870_338 : Prog (BitVec 64) :=
.seq body870_33 body870_81

def body870_339 : Prog (BitVec 64) :=
.seq body870_82 body870_83

def body870_340 : Prog (BitVec 64) :=
.seq body870_339 body870_84

def body870_341 : Prog (BitVec 64) :=
.seq body870_340 body870_85

def body870_342 : Prog (BitVec 64) :=
.seq body870_341 body870_86

def body870_343 : Prog (BitVec 64) :=
.seq body870_342 body870_87

def body870_344 : Prog (BitVec 64) :=
.seq body870_343 body870_88

def body870_345 : Prog (BitVec 64) :=
.decCall ("ct") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body870_344

def body870_346 : Prog (BitVec 64) :=
.decCall ("sa") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body870_345

def body870_347 : Prog (BitVec 64) :=
.seq body870_97 body870_98

def body870_348 : Prog (BitVec 64) :=
.seq body870_347 body870_99

def body870_349 : Prog (BitVec 64) :=
.seq body870_348 body870_100

def body870_350 : Prog (BitVec 64) :=
.seq body870_349 body870_101

def body870_351 : Prog (BitVec 64) :=
.seq body870_350 body870_102

def body870_352 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 152#64]))
  (Flapjack.Exp.const 0#64)) body870_346 body870_351

def body870_353 : Prog (BitVec 64) :=
.seq body870_352 body870_109

def body870_354 : Prog (BitVec 64) :=
.seq body870_353 body870_110

def body870_355 : Prog (BitVec 64) :=
.seq body870_354 body870_111

def body870_356 : Prog (BitVec 64) :=
.seq body870_355 body870_112

def body870_357 : Prog (BitVec 64) :=
.seq body870_113 body870_114

def body870_358 : Prog (BitVec 64) :=
.seq body870_117 body870_118

def body870_359 : Prog (BitVec 64) :=
.seq body870_358 body870_119

def body870_360 : Prog (BitVec 64) :=
.seq body870_359 body870_120

def body870_361 : Prog (BitVec 64) :=
.seq body870_125 body870_126

def body870_362 : Prog (BitVec 64) :=
.seq body870_33 body870_130

def body870_363 : Prog (BitVec 64) :=
.seq body870_33 body870_136

def body870_364 : Prog (BitVec 64) :=
.seq body870_145 body870_146

def body870_365 : Prog (BitVec 64) :=
.seq body870_364 body870_153

def body870_366 : Prog (BitVec 64) :=
.dec ("del") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 24#64])) body870_365

def body870_367 : Prog (BitVec 64) :=
.seq body870_137 body870_366

def body870_368 : Prog (BitVec 64) :=
.decCall ("rl") (Flapjack.Shape.one) ("lst_push") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 72#64]),
  Flapjack.Exp.const 8#64]) body870_367

def body870_369 : Prog (BitVec 64) :=
.seq body870_363 body870_368

def body870_370 : Prog (BitVec 64) :=
.dec ("stable_lp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "stable_logs", Flapjack.Exp.const 0#64])) body870_369

def body870_371 : Prog (BitVec 64) :=
.seq body870_133 body870_370

def body870_372 : Prog (BitVec 64) :=
.decCall ("stable_logs") (Flapjack.Shape.one) ("lst_new") ([Flapjack.Exp.const 8#64, Flapjack.Exp.var Flapjack.VarKind.local "stable_log_cap"]) body870_371

def body870_373 : Prog (BitVec 64) :=
.seq body870_132 body870_372

def body870_374 : Prog (BitVec 64) :=
.dec ("stable_log_cap") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "nl") body870_373

def body870_375 : Prog (BitVec 64) :=
.seq body870_362 body870_374

def body870_376 : Prog (BitVec 64) :=
.dec ("lp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.const 0#64])) body870_375

def body870_377 : Prog (BitVec 64) :=
.dec ("nl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.const 8#64])) body870_376

def body870_378 : Prog (BitVec 64) :=
.seq body870_361 body870_377

def body870_379 : Prog (BitVec 64) :=
.decCall ("rc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_receipt") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "succeeded",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 16#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "logs"]) body870_378

def body870_380 : Prog (BitVec 64) :=
.seq body870_124 body870_379

def body870_381 : Prog (BitVec 64) :=
.dec ("succeeded") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body870_380

def body870_382 : Prog (BitVec 64) :=
.seq body870_122 body870_381

def body870_383 : Prog (BitVec 64) :=
.dec ("logs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 16#64])) body870_382

def body870_384 : Prog (BitVec 64) :=
.seq body870_360 body870_383

def body870_385 : Prog (BitVec 64) :=
.decCall ("tx_regular_gas") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "used_before_refund",
      Flapjack.Exp.var Flapjack.VarKind.local "tx_state_gas_nat"],
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic")]) body870_384

def body870_386 : Prog (BitVec 64) :=
.seq body870_116 body870_385

def body870_387 : Prog (BitVec 64) :=
.dec ("tx_state_gas_nat") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "tx_state_gas") body870_386

def body870_388 : Prog (BitVec 64) :=
.dec ("tx_state_gas") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic"),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 72#64])]) body870_387

def body870_389 : Prog (BitVec 64) :=
.seq body870_357 body870_388

def body870_390 : Prog (BitVec 64) :=
.decCall ("tf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "tx_gas_used", Flapjack.Exp.var Flapjack.VarKind.local "priority_fee"]) body870_389

def body870_391 : Prog (BitVec 64) :=
.decCall ("priority_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "price",
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 48#64])]) body870_390

def body870_392 : Prog (BitVec 64) :=
.decCall ("gra") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "tx_gas_left", Flapjack.Exp.var Flapjack.VarKind.local "price"]) body870_391

def body870_393 : Prog (BitVec 64) :=
.dec ("tx_gas_left") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "tx_gas_used"]) body870_392

def body870_394 : Prog (BitVec 64) :=
.decCall ("tx_gas_used") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "used_after_refund",
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic")]) body870_393

def body870_395 : Prog (BitVec 64) :=
.dec ("used_after_refund") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "used_before_refund", Flapjack.Exp.var Flapjack.VarKind.local "refund"]) body870_394

def body870_396 : Prog (BitVec 64) :=
.decCall ("refund") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.var Flapjack.VarKind.local "ubr5",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 8#64])]) body870_395

def body870_397 : Prog (BitVec 64) :=
.decCall ("ubr5") (Flapjack.Shape.one) ("udiv_small5") ([Flapjack.Exp.var Flapjack.VarKind.local "used_before_refund"]) body870_396

def body870_398 : Prog (BitVec 64) :=
.dec ("used_before_refund") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "gas",
        Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 0#64])],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 56#64])]) body870_397

def body870_399 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("process_message_call") ([Flapjack.Exp.var Flapjack.VarKind.local "m"]) body870_398

def body870_400 : Prog (BitVec 64) :=
.seq body870_356 body870_399

def body870_401 : Prog (BitVec 64) :=
.decCall ("empty") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body870_400

def body870_402 : Prog (BitVec 64) :=
.seq body870_338 body870_401

def body870_403 : Prog (BitVec 64) :=
.decCall ("ak") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 52#64, Flapjack.Exp.const 16#64]) body870_402

def body870_404 : Prog (BitVec 64) :=
.seq body870_337 body870_403

def body870_405 : Prog (BitVec 64) :=
.decCall ("aa") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 64#64]) body870_404

def body870_406 : Prog (BitVec 64) :=
.seq body870_333 body870_405

def body870_407 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("msg_new") ([]) body870_406

def body870_408 : Prog (BitVec 64) :=
.seq body870_327 body870_407

def body870_409 : Prog (BitVec 64) :=
.decCall ("txh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body870_408

def body870_410 : Prog (BitVec 64) :=
.seq body870_324 body870_409

def body870_411 : Prog (BitVec 64) :=
.decCall ("issc") (Flapjack.Shape.one) ("tx_is_setcode") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_410

def body870_412 : Prog (BitVec 64) :=
.seq body870_54 body870_411

def body870_413 : Prog (BitVec 64) :=
.decCall ("isb") (Flapjack.Shape.one) ("tx_is_blob") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_412

def body870_414 : Prog (BitVec 64) :=
.seq body870_322 body870_413

def body870_415 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body870_414

def body870_416 : Prog (BitVec 64) :=
.decCall ("al_keys") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "nkeys", Flapjack.Exp.const 52#64],
      Flapjack.Exp.const 8#64]]) body870_415

def body870_417 : Prog (BitVec 64) :=
.seq body870_308 body870_416

def body870_418 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body870_417

def body870_419 : Prog (BitVec 64) :=
.dec ("nkeys") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body870_418

def body870_420 : Prog (BitVec 64) :=
.seq body870_25 body870_419

def body870_421 : Prog (BitVec 64) :=
.decCall ("al_addrs") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nal", Flapjack.Exp.const 1#64],
      Flapjack.Exp.const 8#64]]) body870_420

def body870_422 : Prog (BitVec 64) :=
.seq body870_24 body870_421

def body870_423 : Prog (BitVec 64) :=
.decCall ("hal") (Flapjack.Shape.one) ("tx_has_access_list") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_422

def body870_424 : Prog (BitVec 64) :=
.dec ("nal") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body870_423

def body870_425 : Prog (BitVec 64) :=
.seq body870_304 body870_424

def body870_426 : Prog (BitVec 64) :=
.decCall ("te") (Flapjack.Shape.one) ("te_new") ([]) body870_425

def body870_427 : Prog (BitVec 64) :=
.seq body870_299 body870_426

def body870_428 : Prog (BitVec 64) :=
.dec ("bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 8#64])) body870_427

def body870_429 : Prog (BitVec 64) :=
.seq body870_13 body870_428

def body870_430 : Prog (BitVec 64) :=
.dec ("reservoir") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "execution_gas", Flapjack.Exp.var Flapjack.VarKind.local "mgas"]) body870_429

def body870_431 : Prog (BitVec 64) :=
.decCall ("mgas") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.var Flapjack.VarKind.local "regular_budget", Flapjack.Exp.var Flapjack.VarKind.local "execution_gas"]) body870_430

def body870_432 : Prog (BitVec 64) :=
.dec ("regular_budget") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.const 16777216#64, Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic")]) body870_431

def body870_433 : Prog (BitVec 64) :=
.dec ("execution_gas") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "intrinsic_gas"]) body870_432

def body870_434 : Prog (BitVec 64) :=
.dec ("effective_gas_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "egf"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "egf"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "egf"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "egf")]) body870_433

def body870_435 : Prog (BitVec 64) :=
.decCall ("egf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "price"]) body870_434

def body870_436 : Prog (BitVec 64) :=
.dec ("gas") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 144#64])) body870_435

def body870_437 : Prog (BitVec 64) :=
.seq body870_12 body870_436

def body870_438 : Prog (BitVec 64) :=
.dec ("blob_gas_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body870_437

def body870_439 : Prog (BitVec 64) :=
.decCall ("acct") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body870_438

def body870_440 : Prog (BitVec 64) :=
.decCall ("tx_blob_gas_used") (Flapjack.Shape.one) ("calculate_total_blob_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_439

def body870_441 : Prog (BitVec 64) :=
.decCall ("price") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("check_transaction") ([Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body870_440

def body870_442 : Prog (BitVec 64) :=
.dec ("intrinsic_gas") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "intrinsic")]) body870_441

def body870_443 : Prog (BitVec 64) :=
.decCall ("intrinsic") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("validate_transaction") ([Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body870_442

def body870_444 : Prog (BitVec 64) :=
.seq body870_8 body870_443

def body870_445 : Prog (BitVec 64) :=
.decCall ("sender") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body870_444

def body870_446 : Prog (BitVec 64) :=
.seq body870_7 body870_445

def body870_447 : Prog (BitVec 64) :=
.decCall ("cid") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_chain_id") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_446

def body870_448 : Prog (BitVec 64) :=
.seq body870_297 body870_447

def body870_449 : Prog (BitVec 64) :=
.decCall ("enc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_transaction") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body870_448

def body870_450 : Prog (BitVec 64) :=
.seq body870_296 body870_449

def originalData870 : Decl (BitVec 64) :=
.function { name := "process_transaction", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("index", Flapjack.Shape.one)], body := body870_295, returnShape := (Flapjack.Shape.one) }
def simplifiedData870 : Decl (BitVec 64) :=
.function { name := "process_transaction", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("index", Flapjack.Shape.one)], body := body870_450, returnShape := (Flapjack.Shape.one) }
def original870 := Pancake.PanLang.declToHOL originalData870
def simplified870 := Pancake.PanLang.declToHOL simplifiedData870
end InitECandidate.Proofs.FrontendStages.Declarations
