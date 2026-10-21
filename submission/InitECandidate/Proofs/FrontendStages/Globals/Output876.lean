import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data876
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate859
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody876_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 3#64)

def globalBody876_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody876_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nh") (Flapjack.Exp.const 0#64)) globalBody876_0 globalBody876_1

def globalBody876_3 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 440#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "vh"))

def globalBody876_4 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 448#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nh")

def globalBody876_5 : Prog (BitVec 64) :=
.seq globalBody876_3 globalBody876_4

def globalBody876_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_init"
  [Flapjack.Exp.var Flapjack.VarKind.local "nodedb",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "codedb"]

def globalBody876_7 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 4#64)

def globalBody876_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "txs",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 0#64)) globalBody876_7 globalBody876_1

def globalBody876_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody876_10 : Prog (BitVec 64) :=
.seq globalBody876_8 globalBody876_9

def globalBody876_11 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "ntx")) globalBody876_10

def globalBody876_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "header_hash"
  [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.var Flapjack.VarKind.local "bh"]

def globalBody876_13 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 5#64)

def globalBody876_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody876_13 globalBody876_1

def globalBody876_15 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 6#64)

def globalBody876_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vvh") (Flapjack.Exp.const 0#64)) globalBody876_15 globalBody876_1

def globalBody876_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "validate_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.var Flapjack.VarKind.local "hdr"]

def globalBody876_18 : Prog (BitVec 64) :=
.seq globalBody876_16 globalBody876_17

def globalBody876_19 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "")

def globalBody876_20 : Prog (BitVec 64) :=
.decCall ("") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 120#64]) globalBody876_19

def globalBody876_21 : Prog (BitVec 64) :=
.seq globalBody876_18 globalBody876_20

def globalBody876_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
    Flapjack.Exp.const 120#64]

def globalBody876_23 : Prog (BitVec 64) :=
.seq globalBody876_21 globalBody876_22

def globalBody876_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 0#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 88#64]))

def globalBody876_25 : Prog (BitVec 64) :=
.seq globalBody876_23 globalBody876_24

def globalBody876_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 104#64]))

def globalBody876_27 : Prog (BitVec 64) :=
.seq globalBody876_25 globalBody876_26

def globalBody876_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 16#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 440#64]))

def globalBody876_29 : Prog (BitVec 64) :=
.seq globalBody876_27 globalBody876_28

def globalBody876_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 24#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 448#64]))

def globalBody876_31 : Prog (BitVec 64) :=
.seq globalBody876_29 globalBody876_30

def globalBody876_32 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 32#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 24#64]))

def globalBody876_33 : Prog (BitVec 64) :=
.seq globalBody876_31 globalBody876_32

def globalBody876_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 40#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 96#64]))

def globalBody876_35 : Prog (BitVec 64) :=
.seq globalBody876_33 globalBody876_34

def globalBody876_36 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 48#64])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 160#64]))

def globalBody876_37 : Prog (BitVec 64) :=
.seq globalBody876_35 globalBody876_36

def globalBody876_38 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 80#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 120#64]))

def globalBody876_39 : Prog (BitVec 64) :=
.seq globalBody876_37 globalBody876_38

def globalBody876_40 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 88#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 144#64]))

def globalBody876_41 : Prog (BitVec 64) :=
.seq globalBody876_39 globalBody876_40

def globalBody876_42 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 96#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 208#64]))

def globalBody876_43 : Prog (BitVec 64) :=
.seq globalBody876_41 globalBody876_42

def globalBody876_44 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 104#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 216#64]))

def globalBody876_45 : Prog (BitVec 64) :=
.seq globalBody876_43 globalBody876_44

def globalBody876_46 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
      Flapjack.Exp.const 112#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 240#64]))

def globalBody876_47 : Prog (BitVec 64) :=
.seq globalBody876_45 globalBody876_46

def globalBody876_48 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "execute_block"
  [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.var Flapjack.VarKind.local "hdr"]

def globalBody876_49 : Prog (BitVec 64) :=
.seq globalBody876_47 globalBody876_48

def globalBody876_50 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody876_51 : Prog (BitVec 64) :=
.seq globalBody876_49 globalBody876_50

def globalBody876_52 : Prog (BitVec 64) :=
.decCall ("vvh") (Flapjack.Shape.one) ("is_valid_versioned_hashes") ([Flapjack.Exp.var Flapjack.VarKind.local "si"]) globalBody876_51

def globalBody876_53 : Prog (BitVec 64) :=
.seq globalBody876_14 globalBody876_52

def globalBody876_54 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "bh",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 0#64]),
      Flapjack.Exp.const 472#64],
  Flapjack.Exp.const 32#64]) globalBody876_53

def globalBody876_55 : Prog (BitVec 64) :=
.seq globalBody876_12 globalBody876_54

def globalBody876_56 : Prog (BitVec 64) :=
.decCall ("bh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody876_55

def globalBody876_57 : Prog (BitVec 64) :=
.decCall ("hdr") (Flapjack.Shape.one) ("payload_header") ([Flapjack.Exp.var Flapjack.VarKind.local "si"]) globalBody876_56

def globalBody876_58 : Prog (BitVec 64) :=
.seq globalBody876_11 globalBody876_57

def globalBody876_59 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody876_58

def globalBody876_60 : Prog (BitVec 64) :=
.dec ("ntx") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 40#64])) globalBody876_59

def globalBody876_61 : Prog (BitVec 64) :=
.dec ("txs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 32#64])) globalBody876_60

def globalBody876_62 : Prog (BitVec 64) :=
.seq globalBody876_6 globalBody876_61

def globalBody876_63 : Prog (BitVec 64) :=
.decCall ("codedb") (Flapjack.Shape.one) ("nodedb_build") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 56#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 64#64])]) globalBody876_62

def globalBody876_64 : Prog (BitVec 64) :=
.decCall ("nodedb") (Flapjack.Shape.one) ("nodedb_build") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 40#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 48#64])]) globalBody876_63

def globalBody876_65 : Prog (BitVec 64) :=
.seq globalBody876_5 globalBody876_64

def globalBody876_66 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "vh"),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "nh", Flapjack.Exp.const 1#64],
          Flapjack.Exp.const 8#64]])) globalBody876_65

def globalBody876_67 : Prog (BitVec 64) :=
.seq globalBody876_2 globalBody876_66

def globalBody876_68 : Prog (BitVec 64) :=
.dec ("nh") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 80#64])) globalBody876_67

def globalBody876_69 : Prog (BitVec 64) :=
.decCall ("vh") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("validate_headers") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 72#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 80#64])]) globalBody876_68

def globalBody876_70 : Prog (BitVec 64) :=
.dec ("pl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 0#64])) globalBody876_69

def globalData876 : Decl (BitVec 64) :=
.function { name := "run_attempt", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := globalBody876_70, returnShape := (Flapjack.Shape.one) }
def globalOutput876 := Pancake.PanLang.declToHOL globalData876
end InitECandidate.Proofs.FrontendStages.Declarations
