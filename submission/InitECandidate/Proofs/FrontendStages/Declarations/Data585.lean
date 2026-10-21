import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify569
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body585_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 7#64)

def body585_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body585_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1024#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 128#64]))) body585_0 body585_1

def body585_3 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("EvmErr", "perr",
          Flapjack.Prog.seq
            (Flapjack.Prog.ite
              (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "perr")
                (Flapjack.Exp.const 1#64))
              (Flapjack.Prog.seq
                (Flapjack.Prog.call (some (none, none)) "scratch_release"
                  [Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 208#64])])
                (Flapjack.Prog.seq
                  (Flapjack.Prog.call (some (none, none)) "frame_mem_release"
                    [Flapjack.Exp.load Flapjack.Shape.one
                        (Flapjack.Exp.op Flapjack.BinOp.add
                          [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 224#64])])
                  (Flapjack.Prog.seq
                    (Flapjack.Prog.assign Flapjack.VarKind.global "ev"
                      (Flapjack.Exp.var Flapjack.VarKind.local "parent"))
                    (Flapjack.Prog.seq
                      (Flapjack.Prog.assign Flapjack.VarKind.global "cur_cont"
                        (Flapjack.Exp.var Flapjack.VarKind.local "parent_cont"))
                      (Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.var Flapjack.VarKind.local "perr"))))))
              Flapjack.Prog.skip)
            (Flapjack.Prog.seq
              (Flapjack.Prog.call (some (none, none)) "state_restore"
                [Flapjack.Exp.var Flapjack.VarKind.local "prep_snapshot"])
              (Flapjack.Prog.seq
                (Flapjack.Prog.store
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 48#64])
                  (Flapjack.Exp.var Flapjack.VarKind.local "prep_reservoir"))
                (Flapjack.Prog.seq
                  (Flapjack.Prog.store
                    (Flapjack.Exp.op Flapjack.BinOp.add
                      [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 200#64])
                    (Flapjack.Exp.const 0#64))
                  (Flapjack.Prog.seq (Flapjack.Prog.call (some (none, none)) "refill_frame_state_gas" [])
                    (Flapjack.Prog.seq
                      (Flapjack.Prog.call (some (none, none)) "frame_halt"
                        [Flapjack.Exp.var Flapjack.VarKind.local "perr"])
                      (Flapjack.Prog.seq
                        (Flapjack.Prog.assign Flapjack.VarKind.global "ev"
                          (Flapjack.Exp.var Flapjack.VarKind.local "parent"))
                        (Flapjack.Prog.seq
                          (Flapjack.Prog.assign Flapjack.VarKind.global "cur_cont"
                            (Flapjack.Exp.var Flapjack.VarKind.local "parent_cont"))
                          (Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "child"))))))))))))
  "depth0_prepare" []

def body585_4 : Prog (BitVec 64) :=
.dec ("perr") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body585_3

def body585_5 : Prog (BitVec 64) :=
.dec ("prep_reservoir") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 48#64])) body585_4

def body585_6 : Prog (BitVec 64) :=
.decCall ("prep_snapshot") (Flapjack.Shape.one) ("state_snapshot") ([]) body585_5

def body585_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 128#64]))
  (Flapjack.Exp.const 0#64)) body585_6 body585_1

def body585_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "snapshot")

def body585_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_start" []

def body585_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "run_frames" []

def body585_11 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "child")

def body585_12 : Prog (BitVec 64) :=
.seq body585_10 body585_11

def body585_13 : Prog (BitVec 64) :=
.seq body585_9 body585_12

def body585_14 : Prog (BitVec 64) :=
.seq body585_8 body585_13

def body585_15 : Prog (BitVec 64) :=
.decCall ("snapshot") (Flapjack.Shape.one) ("state_snapshot") ([]) body585_14

def body585_16 : Prog (BitVec 64) :=
.seq body585_1 body585_15

def body585_17 : Prog (BitVec 64) :=
.seq body585_7 body585_16

def body585_18 : Prog (BitVec 64) :=
.seq body585_1 body585_17

def body585_19 : Prog (BitVec 64) :=
.decCall ("child") (Flapjack.Shape.one) ("frame_open") ([Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 0#64]) body585_18

def body585_20 : Prog (BitVec 64) :=
.dec ("parent_cont") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "cur_cont") body585_19

def body585_21 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "ev") body585_20

def body585_22 : Prog (BitVec 64) :=
.seq body585_1 body585_21

def body585_23 : Prog (BitVec 64) :=
.seq body585_2 body585_22

def body585_24 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("EvmErr", "perr",
          Flapjack.Prog.seq
            (Flapjack.Prog.seq
              (Flapjack.Prog.seq
                (Flapjack.Prog.seq
                  (Flapjack.Prog.seq
                    (Flapjack.Prog.seq
                      (Flapjack.Prog.seq
                        (Flapjack.Prog.seq
                          (Flapjack.Prog.ite
                            (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "perr")
                              (Flapjack.Exp.const 1#64))
                            (Flapjack.Prog.seq
                              (Flapjack.Prog.seq
                                (Flapjack.Prog.seq
                                  (Flapjack.Prog.seq
                                    (Flapjack.Prog.call (some (none, none)) "scratch_release"
                                      [Flapjack.Exp.load Flapjack.Shape.one
                                          (Flapjack.Exp.op Flapjack.BinOp.add
                                            [Flapjack.Exp.var Flapjack.VarKind.local "child",
                                              Flapjack.Exp.const 208#64])])
                                    (Flapjack.Prog.call (some (none, none)) "frame_mem_release"
                                      [Flapjack.Exp.load Flapjack.Shape.one
                                          (Flapjack.Exp.op Flapjack.BinOp.add
                                            [Flapjack.Exp.var Flapjack.VarKind.local "child",
                                              Flapjack.Exp.const 224#64])]))
                                  (Flapjack.Prog.assign Flapjack.VarKind.global "ev"
                                    (Flapjack.Exp.var Flapjack.VarKind.local "parent")))
                                (Flapjack.Prog.assign Flapjack.VarKind.global "cur_cont"
                                  (Flapjack.Exp.var Flapjack.VarKind.local "parent_cont")))
                              (Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.var Flapjack.VarKind.local "perr")))
                            Flapjack.Prog.skip)
                          (Flapjack.Prog.call (some (none, none)) "state_restore"
                            [Flapjack.Exp.var Flapjack.VarKind.local "prep_snapshot"]))
                        (Flapjack.Prog.store
                          (Flapjack.Exp.op Flapjack.BinOp.add
                            [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 48#64])
                          (Flapjack.Exp.var Flapjack.VarKind.local "prep_reservoir")))
                      (Flapjack.Prog.store
                        (Flapjack.Exp.op Flapjack.BinOp.add
                          [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 200#64])
                        (Flapjack.Exp.const 0#64)))
                    (Flapjack.Prog.call (some (none, none)) "refill_frame_state_gas" []))
                  (Flapjack.Prog.call (some (none, none)) "frame_halt"
                    [Flapjack.Exp.var Flapjack.VarKind.local "perr"]))
                (Flapjack.Prog.assign Flapjack.VarKind.global "ev" (Flapjack.Exp.var Flapjack.VarKind.local "parent")))
              (Flapjack.Prog.assign Flapjack.VarKind.global "cur_cont"
                (Flapjack.Exp.var Flapjack.VarKind.local "parent_cont")))
            (Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "child")))))
  "depth0_prepare" []

def body585_25 : Prog (BitVec 64) :=
.dec ("perr") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body585_24

def body585_26 : Prog (BitVec 64) :=
.dec ("prep_reservoir") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 48#64])) body585_25

def body585_27 : Prog (BitVec 64) :=
.decCall ("prep_snapshot") (Flapjack.Shape.one) ("state_snapshot") ([]) body585_26

def body585_28 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 128#64]))
  (Flapjack.Exp.const 0#64)) body585_27 body585_1

def body585_29 : Prog (BitVec 64) :=
.seq body585_8 body585_9

def body585_30 : Prog (BitVec 64) :=
.seq body585_29 body585_10

def body585_31 : Prog (BitVec 64) :=
.seq body585_30 body585_11

def body585_32 : Prog (BitVec 64) :=
.decCall ("snapshot") (Flapjack.Shape.one) ("state_snapshot") ([]) body585_31

def body585_33 : Prog (BitVec 64) :=
.seq body585_28 body585_32

def body585_34 : Prog (BitVec 64) :=
.decCall ("child") (Flapjack.Shape.one) ("frame_open") ([Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 0#64]) body585_33

def body585_35 : Prog (BitVec 64) :=
.dec ("parent_cont") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "cur_cont") body585_34

def body585_36 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "ev") body585_35

def body585_37 : Prog (BitVec 64) :=
.seq body585_2 body585_36

def originalData585 : Decl (BitVec 64) :=
.function { name := "process_message", inline := false, exported := false, params := [("msg", Flapjack.Shape.one)], body := body585_23, returnShape := (Flapjack.Shape.one) }
def simplifiedData585 : Decl (BitVec 64) :=
.function { name := "process_message", inline := false, exported := false, params := [("msg", Flapjack.Shape.one)], body := body585_37, returnShape := (Flapjack.Shape.one) }
def original585 := Pancake.PanLang.declToHOL originalData585
def simplified585 := Pancake.PanLang.declToHOL simplifiedData585
end InitECandidate.Proofs.FrontendStages.Declarations
