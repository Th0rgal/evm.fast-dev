import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data603
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate587
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody603_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "access_cost" (Flapjack.Exp.const 3000#64)

def globalBody603_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody603_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) globalBody603_0 globalBody603_1

def globalBody603_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "need"]

def globalBody603_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "to"]

def globalBody603_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) globalBody603_4 globalBody603_1

def globalBody603_6 : Prog (BitVec 64) :=
.seq globalBody603_3 globalBody603_5

def globalBody603_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "dl")]

def globalBody603_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "code_address"]

def globalBody603_9 : Prog (BitVec 64) :=
.seq globalBody603_7 globalBody603_8

def globalBody603_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dl"))
  (Flapjack.Exp.const 0#64)) globalBody603_9 globalBody603_1

def globalBody603_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "mcg")]

def globalBody603_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 184#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.load Flapjack.Shape.one
              (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
            Flapjack.Exp.const 184#64]),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "mcg")])

def globalBody603_13 : Prog (BitVec 64) :=
.seq globalBody603_11 globalBody603_12

def globalBody603_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "extend_memory"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "x")]

def globalBody603_15 : Prog (BitVec 64) :=
.seq globalBody603_13 globalBody603_14

def globalBody603_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 0#64)

def globalBody603_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody603_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "started") (Flapjack.Exp.const 0#64)) globalBody603_17 globalBody603_1

def globalBody603_19 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody603_20 : Prog (BitVec 64) :=
.seq globalBody603_18 globalBody603_19

def globalBody603_21 : Prog (BitVec 64) :=
.decCall ("started") (Flapjack.Shape.one) ("generic_call") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "mcg"),
  Flapjack.Exp.var Flapjack.VarKind.local "reservoir",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64],
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "to", Flapjack.Exp.var Flapjack.VarKind.local "code_address",
  Flapjack.Exp.const 1#64, Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "is",
  Flapjack.Exp.var Flapjack.VarKind.local "isz", Flapjack.Exp.var Flapjack.VarKind.local "os",
  Flapjack.Exp.var Flapjack.VarKind.local "osz", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dl"), Flapjack.Exp.const 0#64]) globalBody603_20

def globalBody603_22 : Prog (BitVec 64) :=
.decCall ("osz") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "out_size"]) globalBody603_21

def globalBody603_23 : Prog (BitVec 64) :=
.decCall ("os") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "out_start"]) globalBody603_22

def globalBody603_24 : Prog (BitVec 64) :=
.decCall ("isz") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "in_size"]) globalBody603_23

def globalBody603_25 : Prog (BitVec 64) :=
.decCall ("is") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "in_start"]) globalBody603_24

def globalBody603_26 : Prog (BitVec 64) :=
.seq globalBody603_16 globalBody603_25

def globalBody603_27 : Prog (BitVec 64) :=
.dec ("reservoir") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 72#64])) globalBody603_26

def globalBody603_28 : Prog (BitVec 64) :=
.seq globalBody603_15 globalBody603_27

def globalBody603_29 : Prog (BitVec 64) :=
.decCall ("mcg") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_message_call_gas") ([Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64],
  Flapjack.Exp.var Flapjack.VarKind.local "gw",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
        Flapjack.Exp.const 64#64]),
  Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody603_28

def globalBody603_30 : Prog (BitVec 64) :=
.decCall ("gw") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "gasv"]) globalBody603_29

def globalBody603_31 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "code_address"]) globalBody603_30

def globalBody603_32 : Prog (BitVec 64) :=
.seq globalBody603_10 globalBody603_31

def globalBody603_33 : Prog (BitVec 64) :=
.dec ("code_address") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "dl")) globalBody603_32

def globalBody603_34 : Prog (BitVec 64) :=
.decCall ("dl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_delegation_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "to"]) globalBody603_33

def globalBody603_35 : Prog (BitVec 64) :=
.seq globalBody603_6 globalBody603_34

def globalBody603_36 : Prog (BitVec 64) :=
.decCall ("need") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "access_cost",
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) globalBody603_35

def globalBody603_37 : Prog (BitVec 64) :=
.seq globalBody603_2 globalBody603_36

def globalBody603_38 : Prog (BitVec 64) :=
.dec ("access_cost") (Flapjack.Shape.one) (Flapjack.Exp.const 100#64) globalBody603_37

def globalBody603_39 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "to"]) globalBody603_38

def globalBody603_40 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost2") ([Flapjack.Exp.var Flapjack.VarKind.local "in_start", Flapjack.Exp.var Flapjack.VarKind.local "in_size",
  Flapjack.Exp.var Flapjack.VarKind.local "out_start", Flapjack.Exp.var Flapjack.VarKind.local "out_size"]) globalBody603_39

def globalBody603_41 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 112#64])) globalBody603_40

def globalBody603_42 : Prog (BitVec 64) :=
.decCall ("out_size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody603_41

def globalBody603_43 : Prog (BitVec 64) :=
.decCall ("out_start") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody603_42

def globalBody603_44 : Prog (BitVec 64) :=
.decCall ("in_size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody603_43

def globalBody603_45 : Prog (BitVec 64) :=
.decCall ("in_start") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody603_44

def globalBody603_46 : Prog (BitVec 64) :=
.decCall ("to") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "tov"]) globalBody603_45

def globalBody603_47 : Prog (BitVec 64) :=
.decCall ("tov") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody603_46

def globalBody603_48 : Prog (BitVec 64) :=
.decCall ("gasv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody603_47

def globalData603 : Decl (BitVec 64) :=
.function { name := "op_staticcall", inline := false, exported := false, params := [], body := globalBody603_48, returnShape := (Flapjack.Shape.one) }
def globalOutput603 := Pancake.PanLang.declToHOL globalData603
end InitECandidate.Proofs.FrontendStages.Declarations
