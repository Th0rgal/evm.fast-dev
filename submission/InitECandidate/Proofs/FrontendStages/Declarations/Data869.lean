import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify853
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body869_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 80#64)

def body869_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body869_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "regular_avail")
  (Flapjack.Exp.var Flapjack.VarKind.local "capped")) body869_0 body869_1

def body869_3 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 81#64)

def body869_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "state_avail")
  (Flapjack.Exp.var Flapjack.VarKind.local "gas")) body869_3 body869_1

def body869_5 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 82#64)

def body869_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "blob_avail")
  (Flapjack.Exp.var Flapjack.VarKind.local "tx_blob_gas")) body869_5 body869_1

def body869_7 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 83#64)

def body869_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt") (Flapjack.Exp.const 0#64)) body869_7 body869_1

def body869_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "price" (Flapjack.Exp.var Flapjack.VarKind.local "gp")

def body869_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "max_fee_per_gas" (Flapjack.Exp.var Flapjack.VarKind.local "gp")

def body869_11 : Prog (BitVec 64) :=
.seq body869_9 body869_10

def body869_12 : Prog (BitVec 64) :=
.seq body869_8 body869_11

def body869_13 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "gp", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]) body869_12

def body869_14 : Prog (BitVec 64) :=
.dec ("gp") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 48#64])) body869_13

def body869_15 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 84#64)

def body869_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt1") (Flapjack.Exp.const 0#64)) body869_15 body869_1

def body869_17 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 85#64)

def body869_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt2") (Flapjack.Exp.const 0#64)) body869_17 body869_1

def body869_19 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "prio" (Flapjack.Exp.var Flapjack.VarKind.local "mp")

def body869_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt3") (Flapjack.Exp.const 0#64)) body869_19 body869_1

def body869_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "price"), none)) "u256_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "prio", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]

def body869_22 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "max_fee_per_gas" (Flapjack.Exp.var Flapjack.VarKind.local "mf")

def body869_23 : Prog (BitVec 64) :=
.seq body869_21 body869_22

def body869_24 : Prog (BitVec 64) :=
.seq body869_20 body869_23

def body869_25 : Prog (BitVec 64) :=
.dec ("prio") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.var Flapjack.VarKind.local "diff") body869_24

def body869_26 : Prog (BitVec 64) :=
.decCall ("lt3") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "mp", Flapjack.Exp.var Flapjack.VarKind.local "diff"]) body869_25

def body869_27 : Prog (BitVec 64) :=
.decCall ("diff") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "mf", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]) body869_26

def body869_28 : Prog (BitVec 64) :=
.seq body869_18 body869_27

def body869_29 : Prog (BitVec 64) :=
.decCall ("lt2") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "mf", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]) body869_28

def body869_30 : Prog (BitVec 64) :=
.seq body869_16 body869_29

def body869_31 : Prog (BitVec 64) :=
.decCall ("lt1") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "mf", Flapjack.Exp.var Flapjack.VarKind.local "mp"]) body869_30

def body869_32 : Prog (BitVec 64) :=
.dec ("mp") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 80#64])) body869_31

def body869_33 : Prog (BitVec 64) :=
.dec ("mf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 112#64])) body869_32

def body869_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ty") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ty") (Flapjack.Exp.const 1#64)])) body869_14 body869_33

def body869_35 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 86#64)

def body869_36 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nb") (Flapjack.Exp.const 0#64)) body869_35 body869_1

def body869_37 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 87#64)

def body869_38 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 6#64) (Flapjack.Exp.var Flapjack.VarKind.local "nb")) body869_37 body869_1

def body869_39 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 88#64)

def body869_40 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.loadByte
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 256#64]),
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 32#64]]))
  (Flapjack.Exp.const 1#64)) body869_39 body869_1

def body869_41 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def body869_42 : Prog (BitVec 64) :=
.seq body869_40 body869_41

def body869_43 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "nb")) body869_42

def body869_44 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 89#64)

def body869_45 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt4") (Flapjack.Exp.const 0#64)) body869_44 body869_1

def body869_46 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "ovf" (Flapjack.Exp.const 1#64)

def body869_47 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "bf"))
  (Flapjack.Exp.const 0#64)) body869_46 body869_1

def body869_48 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "sum"))
  (Flapjack.Exp.const 0#64)) body869_46 body869_1

def body869_49 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "max_gas_fee"
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sum"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sum"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "sum"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "sum")])

def body869_50 : Prog (BitVec 64) :=
.seq body869_48 body869_49

def body869_51 : Prog (BitVec 64) :=
.decCall ("sum") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add_carry") ([Flapjack.Exp.var Flapjack.VarKind.local "max_gas_fee",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "bf"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "bf"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "bf"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "bf")]]) body869_50

def body869_52 : Prog (BitVec 64) :=
.seq body869_47 body869_51

def body869_53 : Prog (BitVec 64) :=
.decCall ("bf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "tx_blob_gas", Flapjack.Exp.var Flapjack.VarKind.local "mfb"]) body869_52

def body869_54 : Prog (BitVec 64) :=
.seq body869_45 body869_53

def body869_55 : Prog (BitVec 64) :=
.decCall ("lt4") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "mfb", Flapjack.Exp.var Flapjack.VarKind.local "bgp"]) body869_54

def body869_56 : Prog (BitVec 64) :=
.dec ("mfb") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 224#64])) body869_55

def body869_57 : Prog (BitVec 64) :=
.decCall ("bgp") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_blob_gas_price") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 96#64])]) body869_56

def body869_58 : Prog (BitVec 64) :=
.seq body869_43 body869_57

def body869_59 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body869_58

def body869_60 : Prog (BitVec 64) :=
.seq body869_38 body869_59

def body869_61 : Prog (BitVec 64) :=
.seq body869_36 body869_60

def body869_62 : Prog (BitVec 64) :=
.dec ("nb") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 264#64])) body869_61

def body869_63 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ty") (Flapjack.Exp.const 3#64)) body869_62 body869_1

def body869_64 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 90#64)

def body869_65 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 280#64]))
  (Flapjack.Exp.const 0#64)) body869_64 body869_1

def body869_66 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ty") (Flapjack.Exp.const 4#64)) body869_65 body869_1

def body869_67 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 92#64)

def body869_68 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) body869_67 body869_1

def body869_69 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 91#64)

def body869_70 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "tn"))
  (Flapjack.Exp.var Flapjack.VarKind.local "an")) body869_69 body869_1

def body869_71 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "an")
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "tn"))) body869_67 body869_1

def body869_72 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 93#64)

def body869_73 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "ovf") (Flapjack.Exp.const 0#64)) body869_72 body869_1

def body869_74 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "need"))
  (Flapjack.Exp.const 0#64)) body869_72 body869_1

def body869_75 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "lt5") (Flapjack.Exp.const 0#64)) body869_72 body869_1

def body869_76 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 94#64)

def body869_77 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vd") (Flapjack.Exp.const 0#64)) body869_76 body869_1

def body869_78 : Prog (BitVec 64) :=
.decCall ("vd") (Flapjack.Shape.one) ("is_valid_delegation") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "scode"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "scode")]) body869_77

def body869_79 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "che") (Flapjack.Exp.const 0#64)) body869_78 body869_1

def body869_80 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "price")

def body869_81 : Prog (BitVec 64) :=
.seq body869_79 body869_80

def body869_82 : Prog (BitVec 64) :=
.decCall ("che") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash", Flapjack.Exp.const 32#64]) body869_81

def body869_83 : Prog (BitVec 64) :=
.decCall ("scode") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("get_code") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body869_82

def body869_84 : Prog (BitVec 64) :=
.seq body869_75 body869_83

def body869_85 : Prog (BitVec 64) :=
.decCall ("lt5") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "need"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "need"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "need"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "need")]]) body869_84

def body869_86 : Prog (BitVec 64) :=
.seq body869_74 body869_85

def body869_87 : Prog (BitVec 64) :=
.decCall ("need") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add_carry") ([Flapjack.Exp.var Flapjack.VarKind.local "max_gas_fee",
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 160#64])]) body869_86

def body869_88 : Prog (BitVec 64) :=
.seq body869_73 body869_87

def body869_89 : Prog (BitVec 64) :=
.seq body869_71 body869_88

def body869_90 : Prog (BitVec 64) :=
.seq body869_70 body869_89

def body869_91 : Prog (BitVec 64) :=
.seq body869_68 body869_90

def body869_92 : Prog (BitVec 64) :=
.dec ("an") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 0#64])) body869_91

def body869_93 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "tn"]) body869_92

def body869_94 : Prog (BitVec 64) :=
.dec ("tn") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 16#64])) body869_93

def body869_95 : Prog (BitVec 64) :=
.seq body869_66 body869_94

def body869_96 : Prog (BitVec 64) :=
.seq body869_63 body869_95

def body869_97 : Prog (BitVec 64) :=
.dec ("max_gas_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "mgf"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "mgf"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "mgf"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "mgf")]) body869_96

def body869_98 : Prog (BitVec 64) :=
.dec ("ovf") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "mgf")) body869_97

def body869_99 : Prog (BitVec 64) :=
.decCall ("mgf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "max_fee_per_gas"]) body869_98

def body869_100 : Prog (BitVec 64) :=
.seq body869_34 body869_99

def body869_101 : Prog (BitVec 64) :=
.dec ("ty") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64])) body869_100

def body869_102 : Prog (BitVec 64) :=
.dec ("max_fee_per_gas") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body869_101

def body869_103 : Prog (BitVec 64) :=
.dec ("price") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body869_102

def body869_104 : Prog (BitVec 64) :=
.dec ("base_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 48#64])) body869_103

def body869_105 : Prog (BitVec 64) :=
.decCall ("acct") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body869_104

def body869_106 : Prog (BitVec 64) :=
.seq body869_6 body869_105

def body869_107 : Prog (BitVec 64) :=
.decCall ("tx_blob_gas") (Flapjack.Shape.one) ("calculate_total_blob_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body869_106

def body869_108 : Prog (BitVec 64) :=
.seq body869_4 body869_107

def body869_109 : Prog (BitVec 64) :=
.seq body869_2 body869_108

def body869_110 : Prog (BitVec 64) :=
.decCall ("capped") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.const 16777216#64, Flapjack.Exp.var Flapjack.VarKind.local "gas"]) body869_109

def body869_111 : Prog (BitVec 64) :=
.dec ("gas") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 144#64])) body869_110

def body869_112 : Prog (BitVec 64) :=
.dec ("blob_avail") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.const 2752512#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 48#64])]) body869_111

def body869_113 : Prog (BitVec 64) :=
.dec ("state_avail") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "block_gas_limit",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 8#64])]) body869_112

def body869_114 : Prog (BitVec 64) :=
.dec ("regular_avail") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "block_gas_limit",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 0#64])]) body869_113

def body869_115 : Prog (BitVec 64) :=
.dec ("block_gas_limit") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 8#64])) body869_114

def body869_116 : Prog (BitVec 64) :=
.seq body869_2 body869_4

def body869_117 : Prog (BitVec 64) :=
.seq body869_8 body869_9

def body869_118 : Prog (BitVec 64) :=
.seq body869_117 body869_10

def body869_119 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "gp", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]) body869_118

def body869_120 : Prog (BitVec 64) :=
.dec ("gp") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 48#64])) body869_119

def body869_121 : Prog (BitVec 64) :=
.seq body869_20 body869_21

def body869_122 : Prog (BitVec 64) :=
.seq body869_121 body869_22

def body869_123 : Prog (BitVec 64) :=
.dec ("prio") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.var Flapjack.VarKind.local "diff") body869_122

def body869_124 : Prog (BitVec 64) :=
.decCall ("lt3") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "mp", Flapjack.Exp.var Flapjack.VarKind.local "diff"]) body869_123

def body869_125 : Prog (BitVec 64) :=
.decCall ("diff") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "mf", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]) body869_124

def body869_126 : Prog (BitVec 64) :=
.seq body869_18 body869_125

def body869_127 : Prog (BitVec 64) :=
.decCall ("lt2") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "mf", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]) body869_126

def body869_128 : Prog (BitVec 64) :=
.seq body869_16 body869_127

def body869_129 : Prog (BitVec 64) :=
.decCall ("lt1") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "mf", Flapjack.Exp.var Flapjack.VarKind.local "mp"]) body869_128

def body869_130 : Prog (BitVec 64) :=
.dec ("mp") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 80#64])) body869_129

def body869_131 : Prog (BitVec 64) :=
.dec ("mf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 112#64])) body869_130

def body869_132 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ty") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ty") (Flapjack.Exp.const 1#64)])) body869_120 body869_131

def body869_133 : Prog (BitVec 64) :=
.seq body869_36 body869_38

def body869_134 : Prog (BitVec 64) :=
.seq body869_133 body869_59

def body869_135 : Prog (BitVec 64) :=
.dec ("nb") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 264#64])) body869_134

def body869_136 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ty") (Flapjack.Exp.const 3#64)) body869_135 body869_1

def body869_137 : Prog (BitVec 64) :=
.seq body869_136 body869_66

def body869_138 : Prog (BitVec 64) :=
.seq body869_68 body869_70

def body869_139 : Prog (BitVec 64) :=
.seq body869_138 body869_71

def body869_140 : Prog (BitVec 64) :=
.seq body869_139 body869_73

def body869_141 : Prog (BitVec 64) :=
.seq body869_140 body869_87

def body869_142 : Prog (BitVec 64) :=
.dec ("an") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 0#64])) body869_141

def body869_143 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "tn"]) body869_142

def body869_144 : Prog (BitVec 64) :=
.dec ("tn") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 16#64])) body869_143

def body869_145 : Prog (BitVec 64) :=
.seq body869_137 body869_144

def body869_146 : Prog (BitVec 64) :=
.dec ("max_gas_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "mgf"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "mgf"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "mgf"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "mgf")]) body869_145

def body869_147 : Prog (BitVec 64) :=
.dec ("ovf") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "mgf")) body869_146

def body869_148 : Prog (BitVec 64) :=
.decCall ("mgf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fee_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "max_fee_per_gas"]) body869_147

def body869_149 : Prog (BitVec 64) :=
.seq body869_132 body869_148

def body869_150 : Prog (BitVec 64) :=
.dec ("ty") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64])) body869_149

def body869_151 : Prog (BitVec 64) :=
.dec ("max_fee_per_gas") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body869_150

def body869_152 : Prog (BitVec 64) :=
.dec ("price") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body869_151

def body869_153 : Prog (BitVec 64) :=
.dec ("base_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 48#64])) body869_152

def body869_154 : Prog (BitVec 64) :=
.decCall ("acct") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "sender"]) body869_153

def body869_155 : Prog (BitVec 64) :=
.seq body869_6 body869_154

def body869_156 : Prog (BitVec 64) :=
.decCall ("tx_blob_gas") (Flapjack.Shape.one) ("calculate_total_blob_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body869_155

def body869_157 : Prog (BitVec 64) :=
.seq body869_116 body869_156

def body869_158 : Prog (BitVec 64) :=
.decCall ("capped") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.const 16777216#64, Flapjack.Exp.var Flapjack.VarKind.local "gas"]) body869_157

def body869_159 : Prog (BitVec 64) :=
.dec ("gas") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 144#64])) body869_158

def body869_160 : Prog (BitVec 64) :=
.dec ("blob_avail") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.const 2752512#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 48#64])]) body869_159

def body869_161 : Prog (BitVec 64) :=
.dec ("state_avail") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "block_gas_limit",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 8#64])]) body869_160

def body869_162 : Prog (BitVec 64) :=
.dec ("regular_avail") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "block_gas_limit",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 0#64])]) body869_161

def body869_163 : Prog (BitVec 64) :=
.dec ("block_gas_limit") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 8#64])) body869_162

def originalData869 : Decl (BitVec 64) :=
.function { name := "check_transaction", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("sender", Flapjack.Shape.one)], body := body869_115, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData869 : Decl (BitVec 64) :=
.function { name := "check_transaction", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("sender", Flapjack.Shape.one)], body := body869_163, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original869 := Pancake.PanLang.declToHOL originalData869
def simplified869 := Pancake.PanLang.declToHOL simplifiedData869
end InitECandidate.Proofs.FrontendStages.Declarations
