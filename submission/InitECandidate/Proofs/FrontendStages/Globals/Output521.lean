import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data521
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate505
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody521_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 2#64)

def globalBody521_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody521_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
        Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.var Flapjack.VarKind.local "ntopics")) globalBody521_0 globalBody521_1

def globalBody521_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cost" (Flapjack.Exp.const 18446744073709551615#64)

def globalBody521_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "cost"), none)) "add_sat"
  [Flapjack.Exp.var Flapjack.VarKind.local "cost", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dc")]

def globalBody521_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "dc"))
  (Flapjack.Exp.const 0#64)) globalBody521_3 globalBody521_4

def globalBody521_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "cost"]

def globalBody521_7 : Prog (BitVec 64) :=
.seq globalBody521_5 globalBody521_6

def globalBody521_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "u256_to_be32"
  [Flapjack.Exp.var Flapjack.VarKind.local "t",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "topics",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]]

def globalBody521_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody521_10 : Prog (BitVec 64) :=
.seq globalBody521_8 globalBody521_9

def globalBody521_11 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody521_10

def globalBody521_12 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "ntopics")) globalBody521_11

def globalBody521_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "extend_memory"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "x")]

def globalBody521_14 : Prog (BitVec 64) :=
.seq globalBody521_12 globalBody521_13

def globalBody521_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "require_not_static" []

def globalBody521_16 : Prog (BitVec 64) :=
.seq globalBody521_14 globalBody521_15

def globalBody521_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "log_address",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.load Flapjack.Shape.one
                  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
                Flapjack.Exp.const 112#64]),
          Flapjack.Exp.const 32#64]),
    Flapjack.Exp.const 20#64]

def globalBody521_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "log_address")

def globalBody521_19 : Prog (BitVec 64) :=
.seq globalBody521_17 globalBody521_18

def globalBody521_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "topics")

def globalBody521_21 : Prog (BitVec 64) :=
.seq globalBody521_19 globalBody521_20

def globalBody521_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ntopics")

def globalBody521_23 : Prog (BitVec 64) :=
.seq globalBody521_21 globalBody521_22

def globalBody521_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "data",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.load Flapjack.Shape.one
                (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
              Flapjack.Exp.const 24#64]),
        Flapjack.Exp.var Flapjack.VarKind.local "s"],
    Flapjack.Exp.var Flapjack.VarKind.local "n"]

def globalBody521_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "data")

def globalBody521_26 : Prog (BitVec 64) :=
.seq globalBody521_24 globalBody521_25

def globalBody521_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n")

def globalBody521_28 : Prog (BitVec 64) :=
.seq globalBody521_26 globalBody521_27

def globalBody521_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "log_append"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "log"]

def globalBody521_30 : Prog (BitVec 64) :=
.seq globalBody521_28 globalBody521_29

def globalBody521_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody521_32 : Prog (BitVec 64) :=
.seq globalBody521_30 globalBody521_31

def globalBody521_33 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody521_34 : Prog (BitVec 64) :=
.seq globalBody521_32 globalBody521_33

def globalBody521_35 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "start"]) globalBody521_34

def globalBody521_36 : Prog (BitVec 64) :=
.decCall ("data") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) globalBody521_35

def globalBody521_37 : Prog (BitVec 64) :=
.seq globalBody521_23 globalBody521_36

def globalBody521_38 : Prog (BitVec 64) :=
.decCall ("log_address") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) globalBody521_37

def globalBody521_39 : Prog (BitVec 64) :=
.decCall ("log") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 40#64]) globalBody521_38

def globalBody521_40 : Prog (BitVec 64) :=
.seq globalBody521_16 globalBody521_39

def globalBody521_41 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody521_40

def globalBody521_42 : Prog (BitVec 64) :=
.decCall ("topics") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "ntopics", Flapjack.Exp.const 32#64],
      Flapjack.Exp.const 8#64]]) globalBody521_41

def globalBody521_43 : Prog (BitVec 64) :=
.seq globalBody521_7 globalBody521_42

def globalBody521_44 : Prog (BitVec 64) :=
.decCall ("cost") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.const 375#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.const 375#64, Flapjack.Exp.var Flapjack.VarKind.local "ntopics"]],
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) globalBody521_43

def globalBody521_45 : Prog (BitVec 64) :=
.decCall ("dc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("mul64x64") ([Flapjack.Exp.const 8#64, Flapjack.Exp.var Flapjack.VarKind.local "n"]) globalBody521_44

def globalBody521_46 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost1") ([Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.var Flapjack.VarKind.local "size"]) globalBody521_45

def globalBody521_47 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "size"]) globalBody521_46

def globalBody521_48 : Prog (BitVec 64) :=
.seq globalBody521_2 globalBody521_47

def globalBody521_49 : Prog (BitVec 64) :=
.decCall ("size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody521_48

def globalBody521_50 : Prog (BitVec 64) :=
.decCall ("start") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody521_49

def globalData521 : Decl (BitVec 64) :=
.function { name := "op_log", inline := false, exported := false, params := [("ntopics", Flapjack.Shape.one)], body := globalBody521_50, returnShape := (Flapjack.Shape.one) }
def globalOutput521 := Pancake.PanLang.declToHOL globalData521
end InitECandidate.Proofs.FrontendStages.Declarations
