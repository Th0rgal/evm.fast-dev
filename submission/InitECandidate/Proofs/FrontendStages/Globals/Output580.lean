import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data580
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate564
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody580_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("EvmErr", "err",
          Flapjack.Prog.seq
            (Flapjack.Prog.seq
              (Flapjack.Prog.seq
                (Flapjack.Prog.seq
                  (Flapjack.Prog.call (some (none, none)) "state_restore"
                    [Flapjack.Exp.var Flapjack.VarKind.local "csnap"])
                  (Flapjack.Prog.call (some (none, none)) "refill_frame_state_gas" []))
                (Flapjack.Prog.call (some (none, none)) "frame_halt" [Flapjack.Exp.var Flapjack.VarKind.local "err"]))
              (Flapjack.Prog.store
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
                    Flapjack.Exp.const 120#64])
                (Flapjack.Exp.load Flapjack.Shape.one
                  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 264#64]))))
            (Flapjack.Prog.store
              (Flapjack.Exp.op Flapjack.BinOp.add
                [Flapjack.Exp.load Flapjack.Shape.one
                    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
                  Flapjack.Exp.const 128#64])
              (Flapjack.Exp.const 0#64)))))
  "create_finish" [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.var Flapjack.VarKind.local "child"]

def globalBody580_1 : Prog (BitVec 64) :=
.dec ("err") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody580_0

def globalBody580_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_restore" [Flapjack.Exp.var Flapjack.VarKind.local "csnap"]

def globalBody580_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 160#64]))
  (Flapjack.Exp.const 0#64)) globalBody580_1 globalBody580_2

def globalBody580_4 : Prog (BitVec 64) :=
.dec ("csnap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 96#64])) globalBody580_3

def globalBody580_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody580_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "kind") (Flapjack.Exp.const 2#64)) globalBody580_4 globalBody580_5

def globalBody580_7 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "parent")

def globalBody580_8 : Prog (BitVec 64) :=
.seq globalBody580_6 globalBody580_7

def globalBody580_9 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 8#64]))

def globalBody580_10 : Prog (BitVec 64) :=
.seq globalBody580_8 globalBody580_9

def globalBody580_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rollback_child_access" [Flapjack.Exp.var Flapjack.VarKind.local "child"]

def globalBody580_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "incorporate_child_on_error" [Flapjack.Exp.var Flapjack.VarKind.local "child"]

def globalBody580_13 : Prog (BitVec 64) :=
.seq globalBody580_11 globalBody580_12

def globalBody580_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "credit_state_gas_refund" [Flapjack.Exp.const 183600#64]

def globalBody580_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "new_account_charged")
  (Flapjack.Exp.const 0#64)) globalBody580_14 globalBody580_5

def globalBody580_16 : Prog (BitVec 64) :=
.seq globalBody580_13 globalBody580_15

def globalBody580_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_retdata"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 120#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 128#64])]

def globalBody580_18 : Prog (BitVec 64) :=
.seq globalBody580_16 globalBody580_17

def globalBody580_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.rStruct
      [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]

def globalBody580_20 : Prog (BitVec 64) :=
.seq globalBody580_18 globalBody580_19

def globalBody580_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "incorporate_child_on_success" [Flapjack.Exp.var Flapjack.VarKind.local "child"]

def globalBody580_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_retdata"
  [Flapjack.Exp.var Flapjack.VarKind.local "empty", Flapjack.Exp.const 0#64]

def globalBody580_23 : Prog (BitVec 64) :=
.seq globalBody580_21 globalBody580_22

def globalBody580_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push" [Flapjack.Exp.var Flapjack.VarKind.local "av"]

def globalBody580_25 : Prog (BitVec 64) :=
.decCall ("av") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("address_to_u256") ([Flapjack.Exp.var Flapjack.VarKind.local "contract_address"]) globalBody580_24

def globalBody580_26 : Prog (BitVec 64) :=
.seq globalBody580_23 globalBody580_25

def globalBody580_27 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 160#64]))
  (Flapjack.Exp.const 0#64)) globalBody580_20 globalBody580_26

def globalBody580_28 : Prog (BitVec 64) :=
.dec ("empty") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 264#64])) globalBody580_27

def globalBody580_29 : Prog (BitVec 64) :=
.seq globalBody580_21 globalBody580_17

def globalBody580_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.rStruct
      [Flapjack.Exp.const 1#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]

def globalBody580_31 : Prog (BitVec 64) :=
.seq globalBody580_29 globalBody580_30

def globalBody580_32 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 160#64]))
  (Flapjack.Exp.const 0#64)) globalBody580_20 globalBody580_31

def globalBody580_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.load Flapjack.Shape.one
                (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
              Flapjack.Exp.const 24#64]),
        Flapjack.Exp.var Flapjack.VarKind.local "out_start"],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
          Flapjack.Exp.const 144#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "actual"]

def globalBody580_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "actual") (Flapjack.Exp.const 0#64)) globalBody580_33 globalBody580_5

def globalBody580_35 : Prog (BitVec 64) :=
.decCall ("actual") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.var Flapjack.VarKind.local "out_size",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 128#64])]) globalBody580_34

def globalBody580_36 : Prog (BitVec 64) :=
.seq globalBody580_32 globalBody580_35

def globalBody580_37 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "kind") (Flapjack.Exp.const 2#64)) globalBody580_28 globalBody580_36

def globalBody580_38 : Prog (BitVec 64) :=
.seq globalBody580_10 globalBody580_37

def globalBody580_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "scratch_release" [Flapjack.Exp.var Flapjack.VarKind.local "child_mark"]

def globalBody580_40 : Prog (BitVec 64) :=
.seq globalBody580_38 globalBody580_39

def globalBody580_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_mem_release" [Flapjack.Exp.var Flapjack.VarKind.local "child_mem_mark"]

def globalBody580_42 : Prog (BitVec 64) :=
.seq globalBody580_40 globalBody580_41

def globalBody580_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody580_44 : Prog (BitVec 64) :=
.seq globalBody580_42 globalBody580_43

def globalBody580_45 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody580_46 : Prog (BitVec 64) :=
.seq globalBody580_44 globalBody580_45

def globalBody580_47 : Prog (BitVec 64) :=
.dec ("contract_address") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 88#64])) globalBody580_46

def globalBody580_48 : Prog (BitVec 64) :=
.dec ("out_size") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 80#64])) globalBody580_47

def globalBody580_49 : Prog (BitVec 64) :=
.dec ("out_start") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 72#64])) globalBody580_48

def globalBody580_50 : Prog (BitVec 64) :=
.dec ("child_mem_mark") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 56#64])) globalBody580_49

def globalBody580_51 : Prog (BitVec 64) :=
.dec ("child_mark") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 48#64])) globalBody580_50

def globalBody580_52 : Prog (BitVec 64) :=
.dec ("new_account_charged") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 64#64])) globalBody580_51

def globalBody580_53 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 40#64])) globalBody580_52

def globalBody580_54 : Prog (BitVec 64) :=
.dec ("kind") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 16#64])) globalBody580_53

def globalBody580_55 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 0#64])) globalBody580_54

def globalBody580_56 : Prog (BitVec 64) :=
.dec ("child") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64])) globalBody580_55

def globalBody580_57 : Prog (BitVec 64) :=
.dec ("rec") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64])) globalBody580_56

def globalData580 : Decl (BitVec 64) :=
.function { name := "finish_child", inline := false, exported := false, params := [], body := globalBody580_57, returnShape := (Flapjack.Shape.one) }
def globalOutput580 := Pancake.PanLang.declToHOL globalData580
end InitECandidate.Proofs.FrontendStages.Declarations
