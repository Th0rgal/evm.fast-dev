import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data587
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate571
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody587_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "destroy_storage" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def globalBody587_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mark_account_created" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def globalBody587_2 : Prog (BitVec 64) :=
.seq globalBody587_0 globalBody587_1

def globalBody587_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "increment_nonce" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def globalBody587_4 : Prog (BitVec 64) :=
.seq globalBody587_2 globalBody587_3

def globalBody587_5 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "child")

def globalBody587_6 : Prog (BitVec 64) :=
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

def globalBody587_7 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "parent")

def globalBody587_8 : Prog (BitVec 64) :=
.seq globalBody587_6 globalBody587_7

def globalBody587_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "child")

def globalBody587_10 : Prog (BitVec 64) :=
.seq globalBody587_8 globalBody587_9

def globalBody587_11 : Prog (BitVec 64) :=
.dec ("err") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody587_10

def globalBody587_12 : Prog (BitVec 64) :=
.seq globalBody587_5 globalBody587_11

def globalBody587_13 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64])) globalBody587_12

def globalBody587_14 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody587_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 160#64]))
  (Flapjack.Exp.const 0#64)) globalBody587_13 globalBody587_14

def globalBody587_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_restore" [Flapjack.Exp.var Flapjack.VarKind.local "snapshot"]

def globalBody587_17 : Prog (BitVec 64) :=
.seq globalBody587_15 globalBody587_16

def globalBody587_18 : Prog (BitVec 64) :=
.seq globalBody587_17 globalBody587_9

def globalBody587_19 : Prog (BitVec 64) :=
.decCall ("child") (Flapjack.Shape.one) ("process_message") ([Flapjack.Exp.var Flapjack.VarKind.local "msg"]) globalBody587_18

def globalBody587_20 : Prog (BitVec 64) :=
.seq globalBody587_4 globalBody587_19

def globalBody587_21 : Prog (BitVec 64) :=
.dec ("target") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])) globalBody587_20

def globalBody587_22 : Prog (BitVec 64) :=
.decCall ("snapshot") (Flapjack.Shape.one) ("state_snapshot") ([]) globalBody587_21

def globalData587 : Decl (BitVec 64) :=
.function { name := "process_create_message", inline := false, exported := false, params := [("msg", Flapjack.Shape.one)], body := globalBody587_22, returnShape := (Flapjack.Shape.one) }
def globalOutput587 := Pancake.PanLang.declToHOL globalData587
end InitECandidate.Proofs.FrontendStages.Declarations
