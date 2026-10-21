import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data869
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate836
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody869_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 80#64)

def globalBody869_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody869_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "regular_avail")
  (Flapjack.Exp.var Flapjack.VarKind.local "capped")) globalBody869_0 globalBody869_1

def globalBody869_3 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 81#64)

def globalBody869_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "state_avail")
  (Flapjack.Exp.var Flapjack.VarKind.local "gas")) globalBody869_3 globalBody869_1

def globalBody869_5 : Prog (BitVec 64) :=
.seq globalBody869_2 globalBody869_4

def globalBody869_6 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 82#64)

def globalBody869_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "blob_avail")
  (Flapjack.Exp.var Flapjack.VarKind.local "tx_blob_gas")) globalBody869_6 globalBody869_1

def globalBody869_8 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 83#64)

def globalBody869_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt") (Flapjack.Exp.const 0#64)) globalBody869_8 globalBody869_1

def globalBody869_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "price" (Flapjack.Exp.var Flapjack.VarKind.local "gp")

def globalBody869_11 : Prog (BitVec 64) :=
.seq globalBody869_9 globalBody869_10

def globalBody869_12 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "max_fee_per_gas" (Flapjack.Exp.var Flapjack.VarKind.local "gp")

def globalBody869_13 : Prog (BitVec 64) :=
.seq globalBody869_11 globalBody869_12

def globalBody869_14 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "gp", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]) globalBody869_13

def globalBody869_15 : Prog (BitVec 64) :=
.dec ("gp") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 48#64])) globalBody869_14

def globalBody869_16 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 84#64)

def globalBody869_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt1") (Flapjack.Exp.const 0#64)) globalBody869_16 globalBody869_1

def globalBody869_18 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 85#64)

def globalBody869_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt2") (Flapjack.Exp.const 0#64)) globalBody869_18 globalBody869_1

def globalBody869_20 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "prio" (Flapjack.Exp.var Flapjack.VarKind.local "mp")

def globalBody869_21 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt3") (Flapjack.Exp.const 0#64)) globalBody869_20 globalBody869_1

def globalBody869_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "price"), none)) "u256_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "prio", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]

def globalBody869_23 : Prog (BitVec 64) :=
.seq globalBody869_21 globalBody869_22

def globalBody869_24 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "max_fee_per_gas" (Flapjack.Exp.var Flapjack.VarKind.local "mf")

def globalBody869_25 : Prog (BitVec 64) :=
.seq globalBody869_23 globalBody869_24

def globalBody869_26 : Prog (BitVec 64) :=
.dec ("prio") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.var Flapjack.VarKind.local "diff") globalBody869_25

def globalBody869_27 : Prog (BitVec 64) :=
.decCall ("lt3") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "mp", Flapjack.Exp.var Flapjack.VarKind.local "diff"]) globalBody869_26

def globalBody869_28 : Prog (BitVec 64) :=
.decCall ("diff") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "mf", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]) globalBody869_27

def globalBody869_29 : Prog (BitVec 64) :=
.seq globalBody869_19 globalBody869_28

def globalBody869_30 : Prog (BitVec 64) :=
.decCall ("lt2") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "mf", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]) globalBody869_29

def globalBody869_31 : Prog (BitVec 64) :=
.seq globalBody869_17 globalBody869_30

def globalBody869_32 : Prog (BitVec 64) :=
.decCall ("lt1") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "mf", Flapjack.Exp.var Flapjack.VarKind.local "mp"]) globalBody869_31

def globalBody869_33 : Prog (BitVec 64) :=
.dec ("mp") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 80#64])) globalBody869_32

def globalBody869_34 : Prog (BitVec 64) :=
.dec ("mf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 112#64])) globalBody869_33

def globalBody869_35 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ty") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ty") (Flapjack.Exp.const 1#64)])) globalBody869_15 globalBody869_34

def globalBody869_36 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 86#64)

def globalBody869_37 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nb") (Flapjack.Exp.const 0#64)) globalBody869_36 globalBody869_1

def globalBody869_38 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 87#64)

def globalBody869_39 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 6#64) (Flapjack.Exp.var Flapjack.VarKind.local "nb")) globalBody869_38 globalBody869_1

def globalBody869_40 : Prog (BitVec 64) :=
.seq globalBody869_37 globalBody869_39

def globalBody869_41 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 88#64)

def globalBody869_42 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.loadByte
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 256#64]),
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 32#64]]))
  (Flapjack.Exp.const 1#64)) globalBody869_41 globalBody869_1

def globalBody869_43 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def globalBody869_44 : Prog (BitVec 64) :=
.seq globalBody869_42 globalBody869_43

def globalBody869_45 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "nb")) globalBody869_44

def globalBody869_46 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 89#64)

def globalBody869_47 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt4") (Flapjack.Exp.const 0#64)) globalBody869_46 globalBody869_1

def globalBody869_48 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "ovf" (Flapjack.Exp.const 1#64)

def globalBody869_49 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "bf"))
  (Flapjack.Exp.const 0#64)) globalBody869_48 globalBody869_1

def globalBody869_50 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "sum"))
  (Flapjack.Exp.const 0#64)) globalBody869_48 globalBody869_1

def globalBody869_51 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "max_gas_fee"
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sum"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sum"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "sum"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "sum")])

def globalBody869_52 : Prog (BitVec 64) :=
.seq globalBody869_50 globalBody869_51

def globalBody869_53 : Prog (BitVec 64) :=
.decCall ("sum") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add_carry") ([Flapjack.Exp.var Flapjack.VarKind.local "max_gas_fee",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "bf"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "bf"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "bf"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "bf")]]) globalBody869_52

def globalBody869_54 : Prog (BitVec 64) :=
.seq globalBody869_49 globalBody869_53

def globalBody869_55 : Prog (BitVec 64) :=
.decCall ("bf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "tx_blob_gas", Flapjack.Exp.var Flapjack.VarKind.local "mfb"]) globalBody869_54

def globalBody869_56 : Prog (BitVec 64) :=
.seq globalBody869_47 globalBody869_55

def globalBody869_57 : Prog (BitVec 64) :=
.decCall ("lt4") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "mfb", Flapjack.Exp.var Flapjack.VarKind.local "bgp"]) globalBody869_56

def globalBody869_58 : Prog (BitVec 64) :=
.dec ("mfb") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 224#64])) globalBody869_57

def globalBody869_59 : Prog (BitVec 64) :=
.decCall ("bgp") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_blob_gas_price") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
        Flapjack.Exp.const 96#64])]) globalBody869_58

def globalBody869_60 : Prog (BitVec 64) :=
.seq globalBody869_45 globalBody869_59

def globalBody869_61 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody869_60

def globalBody869_62 : Prog (BitVec 64) :=
.seq globalBody869_40 globalBody869_61

def globalBody869_63 : Prog (BitVec 64) :=
.dec ("nb") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 264#64])) globalBody869_62

def globalBody869_64 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ty") (Flapjack.Exp.const 3#64)) globalBody869_63 globalBody869_1

def globalBody869_65 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 90#64)

def globalBody869_66 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 280#64]))
  (Flapjack.Exp.const 0#64)) globalBody869_65 globalBody869_1

def globalBody869_67 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ty") (Flapjack.Exp.const 4#64)) globalBody869_66 globalBody869_1

def globalBody869_68 : Prog (BitVec 64) :=
.seq globalBody869_64 globalBody869_67

def globalBody869_69 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 92#64)

def globalBody869_70 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) globalBody869_69 globalBody869_1

def globalBody869_71 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 91#64)

def globalBody869_72 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "tn"))
  (Flapjack.Exp.var Flapjack.VarKind.local "an")) globalBody869_71 globalBody869_1

def globalBody869_73 : Prog (BitVec 64) :=
.seq globalBody869_70 globalBody869_72

def globalBody869_74 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "an")
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "tn"))) globalBody869_69 globalBody869_1

def globalBody869_75 : Prog (BitVec 64) :=
.seq globalBody869_73 globalBody869_74

def globalBody869_76 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 93#64)

def globalBody869_77 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "ovf") (Flapjack.Exp.const 0#64)) globalBody869_76 globalBody869_1

def globalBody869_78 : Prog (BitVec 64) :=
.seq globalBody869_75 globalBody869_77

def globalBody869_79 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "need"))
  (Flapjack.Exp.const 0#64)) globalBody869_76 globalBody869_1

def globalBody869_80 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt5") (Flapjack.Exp.const 0#64)) globalBody869_76 globalBody869_1

def globalBody869_81 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 94#64)

def globalBody869_82 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vd") (Flapjack.Exp.const 0#64)) globalBody869_81 globalBody869_1

def globalBody869_83 : Prog (BitVec 64) :=
.decCall ("vd") (Flapjack.Shape.one) ("is_valid_delegation") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "scode"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "scode")]) globalBody869_82

def globalBody869_84 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "che") (Flapjack.Exp.const 0#64)) globalBody869_83 globalBody869_1

def globalBody869_85 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "price")

def globalBody869_86 : Prog (BitVec 64) :=
.seq globalBody869_84 globalBody869_85

def globalBody869_87 : Prog (BitVec 64) :=
.decCall ("che") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 136#64]),
  Flapjack.Exp.const 32#64]) globalBody869_86

def globalBody869_88 : Prog (BitVec 64) :=
.decCall ("scode") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("get_code") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "sender"]) globalBody869_87

def globalBody869_89 : Prog (BitVec 64) :=
.seq globalBody869_80 globalBody869_88

def globalBody869_90 : Prog (BitVec 64) :=
.decCall ("lt5") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "need"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "need"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "need"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "need")]]) globalBody869_89

def globalBody869_91 : Prog (BitVec 64) :=
.seq globalBody869_79 globalBody869_90

def globalBody869_92 : Prog (BitVec 64) :=
.decCall ("need") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add_carry") ([Flapjack.Exp.var Flapjack.VarKind.local "max_gas_fee",
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 160#64])]) globalBody869_91

def globalBody869_93 : Prog (BitVec 64) :=
.seq globalBody869_78 globalBody869_92

def globalBody869_94 : Prog (BitVec 64) :=
.dec ("an") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 0#64])) globalBody869_93

def globalBody869_95 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "tn"]) globalBody869_94

def globalBody869_96 : Prog (BitVec 64) :=
.dec ("tn") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 16#64])) globalBody869_95

def globalBody869_97 : Prog (BitVec 64) :=
.seq globalBody869_68 globalBody869_96

def globalBody869_98 : Prog (BitVec 64) :=
.dec ("max_gas_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "mgf"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "mgf"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "mgf"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "mgf")]) globalBody869_97

def globalBody869_99 : Prog (BitVec 64) :=
.dec ("ovf") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "mgf")) globalBody869_98

def globalBody869_100 : Prog (BitVec 64) :=
.decCall ("mgf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "max_fee_per_gas"]) globalBody869_99

def globalBody869_101 : Prog (BitVec 64) :=
.seq globalBody869_35 globalBody869_100

def globalBody869_102 : Prog (BitVec 64) :=
.dec ("ty") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64])) globalBody869_101

def globalBody869_103 : Prog (BitVec 64) :=
.dec ("max_fee_per_gas") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody869_102

def globalBody869_104 : Prog (BitVec 64) :=
.dec ("price") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody869_103

def globalBody869_105 : Prog (BitVec 64) :=
.dec ("base_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 48#64])) globalBody869_104

def globalBody869_106 : Prog (BitVec 64) :=
.decCall ("acct") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "sender"]) globalBody869_105

def globalBody869_107 : Prog (BitVec 64) :=
.seq globalBody869_7 globalBody869_106

def globalBody869_108 : Prog (BitVec 64) :=
.decCall ("tx_blob_gas") (Flapjack.Shape.one) ("calculate_total_blob_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) globalBody869_107

def globalBody869_109 : Prog (BitVec 64) :=
.seq globalBody869_5 globalBody869_108

def globalBody869_110 : Prog (BitVec 64) :=
.decCall ("capped") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.const 16777216#64, Flapjack.Exp.var Flapjack.VarKind.local "gas"]) globalBody869_109

def globalBody869_111 : Prog (BitVec 64) :=
.dec ("gas") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 144#64])) globalBody869_110

def globalBody869_112 : Prog (BitVec 64) :=
.dec ("blob_avail") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.const 2752512#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 416#64]),
          Flapjack.Exp.const 48#64])]) globalBody869_111

def globalBody869_113 : Prog (BitVec 64) :=
.dec ("state_avail") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "block_gas_limit",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 416#64]),
          Flapjack.Exp.const 8#64])]) globalBody869_112

def globalBody869_114 : Prog (BitVec 64) :=
.dec ("regular_avail") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "block_gas_limit",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 416#64]),
          Flapjack.Exp.const 0#64])]) globalBody869_113

def globalBody869_115 : Prog (BitVec 64) :=
.dec ("block_gas_limit") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 8#64])) globalBody869_114

def globalData869 : Decl (BitVec 64) :=
.function { name := "check_transaction", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("sender", Flapjack.Shape.one)], body := globalBody869_115, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput869 := Pancake.PanLang.declToHOL globalData869
end InitECandidate.Proofs.FrontendStages.Declarations
