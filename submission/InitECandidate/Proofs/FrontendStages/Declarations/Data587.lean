import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify571
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body587_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "destroy_storage" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def body587_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mark_account_created" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def body587_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "increment_nonce" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def body587_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "ev" (Flapjack.Exp.var Flapjack.VarKind.local "child")

def body587_4 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("EvmErr", "err",
          Flapjack.Prog.seq
            (Flapjack.Prog.call (some (none, none)) "state_restore"
              [Flapjack.Exp.var Flapjack.VarKind.local "snapshot"])
            (Flapjack.Prog.seq (Flapjack.Prog.call (some (none, none)) "refill_frame_state_gas" [])
              (Flapjack.Prog.seq
                (Flapjack.Prog.call (some (none, none)) "frame_halt" [Flapjack.Exp.var Flapjack.VarKind.local "err"])
                (Flapjack.Prog.seq
                  (Flapjack.Prog.store
                    (Flapjack.Exp.op Flapjack.BinOp.add
                      [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
                    (Flapjack.Exp.var Flapjack.VarKind.global "evm_empty"))
                  (Flapjack.Prog.store
                    (Flapjack.Exp.op Flapjack.BinOp.add
                      [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
                    (Flapjack.Exp.const 0#64))))))))
  "create_finish" [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.var Flapjack.VarKind.local "child"]

def body587_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "ev" (Flapjack.Exp.var Flapjack.VarKind.local "parent")

def body587_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "child")

def body587_7 : Prog (BitVec 64) :=
.seq body587_5 body587_6

def body587_8 : Prog (BitVec 64) :=
.seq body587_4 body587_7

def body587_9 : Prog (BitVec 64) :=
.dec ("err") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body587_8

def body587_10 : Prog (BitVec 64) :=
.seq body587_3 body587_9

def body587_11 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "ev") body587_10

def body587_12 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body587_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 160#64]))
  (Flapjack.Exp.const 0#64)) body587_11 body587_12

def body587_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_restore" [Flapjack.Exp.var Flapjack.VarKind.local "snapshot"]

def body587_15 : Prog (BitVec 64) :=
.seq body587_14 body587_6

def body587_16 : Prog (BitVec 64) :=
.seq body587_13 body587_15

def body587_17 : Prog (BitVec 64) :=
.decCall ("child") (Flapjack.Shape.one) ("process_message") ([Flapjack.Exp.var Flapjack.VarKind.local "msg"]) body587_16

def body587_18 : Prog (BitVec 64) :=
.seq body587_2 body587_17

def body587_19 : Prog (BitVec 64) :=
.seq body587_1 body587_18

def body587_20 : Prog (BitVec 64) :=
.seq body587_0 body587_19

def body587_21 : Prog (BitVec 64) :=
.dec ("target") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])) body587_20

def body587_22 : Prog (BitVec 64) :=
.decCall ("snapshot") (Flapjack.Shape.one) ("state_snapshot") ([]) body587_21

def body587_23 : Prog (BitVec 64) :=
.seq body587_0 body587_1

def body587_24 : Prog (BitVec 64) :=
.seq body587_23 body587_2

def body587_25 : Prog (BitVec 64) :=
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
                    [Flapjack.Exp.var Flapjack.VarKind.local "snapshot"])
                  (Flapjack.Prog.call (some (none, none)) "refill_frame_state_gas" []))
                (Flapjack.Prog.call (some (none, none)) "frame_halt" [Flapjack.Exp.var Flapjack.VarKind.local "err"]))
              (Flapjack.Prog.store
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
                (Flapjack.Exp.var Flapjack.VarKind.global "evm_empty")))
            (Flapjack.Prog.store
              (Flapjack.Exp.op Flapjack.BinOp.add
                [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
              (Flapjack.Exp.const 0#64)))))
  "create_finish" [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.var Flapjack.VarKind.local "child"]

def body587_26 : Prog (BitVec 64) :=
.seq body587_25 body587_5

def body587_27 : Prog (BitVec 64) :=
.seq body587_26 body587_6

def body587_28 : Prog (BitVec 64) :=
.dec ("err") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body587_27

def body587_29 : Prog (BitVec 64) :=
.seq body587_3 body587_28

def body587_30 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "ev") body587_29

def body587_31 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 160#64]))
  (Flapjack.Exp.const 0#64)) body587_30 body587_12

def body587_32 : Prog (BitVec 64) :=
.seq body587_31 body587_14

def body587_33 : Prog (BitVec 64) :=
.seq body587_32 body587_6

def body587_34 : Prog (BitVec 64) :=
.decCall ("child") (Flapjack.Shape.one) ("process_message") ([Flapjack.Exp.var Flapjack.VarKind.local "msg"]) body587_33

def body587_35 : Prog (BitVec 64) :=
.seq body587_24 body587_34

def body587_36 : Prog (BitVec 64) :=
.dec ("target") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])) body587_35

def body587_37 : Prog (BitVec 64) :=
.decCall ("snapshot") (Flapjack.Shape.one) ("state_snapshot") ([]) body587_36

def originalData587 : Decl (BitVec 64) :=
.function { name := "process_create_message", inline := false, exported := false, params := [("msg", Flapjack.Shape.one)], body := body587_22, returnShape := (Flapjack.Shape.one) }
def simplifiedData587 : Decl (BitVec 64) :=
.function { name := "process_create_message", inline := false, exported := false, params := [("msg", Flapjack.Shape.one)], body := body587_37, returnShape := (Flapjack.Shape.one) }
def original587 := Pancake.PanLang.declToHOL originalData587
def simplified587 := Pancake.PanLang.declToHOL simplifiedData587
end InitECandidate.Proofs.FrontendStages.Declarations
