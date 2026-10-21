import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data874
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate857
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody874_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.var Flapjack.VarKind.local "dep",
    Flapjack.Exp.var Flapjack.VarKind.local "dep_n"]

def globalBody874_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "dep" (Flapjack.Exp.var Flapjack.VarKind.local "nd")

def globalBody874_2 : Prog (BitVec 64) :=
.seq globalBody874_0 globalBody874_1

def globalBody874_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "dep_cap"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "dep_cap", Flapjack.Exp.const 2#64],
      Flapjack.Exp.const 1024#64])

def globalBody874_4 : Prog (BitVec 64) :=
.seq globalBody874_2 globalBody874_3

def globalBody874_5 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "dep_cap", Flapjack.Exp.const 2#64],
      Flapjack.Exp.const 1024#64]]) globalBody874_4

def globalBody874_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody874_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "dep_cap")
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dep_n", Flapjack.Exp.const 192#64])) globalBody874_5 globalBody874_6

def globalBody874_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "extract_deposit_data"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dep", Flapjack.Exp.var Flapjack.VarKind.local "dep_n"]]

def globalBody874_9 : Prog (BitVec 64) :=
.seq globalBody874_7 globalBody874_8

def globalBody874_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "dep_n"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dep_n", Flapjack.Exp.const 192#64])

def globalBody874_11 : Prog (BitVec 64) :=
.seq globalBody874_9 globalBody874_10

def globalBody874_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "sig") (Flapjack.Exp.const 0#64)) globalBody874_11 globalBody874_6

def globalBody874_13 : Prog (BitVec 64) :=
.decCall ("sig") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 520#64]),
  Flapjack.Exp.const 32#64]) globalBody874_12

def globalBody874_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 16#64]))) globalBody874_13 globalBody874_6

def globalBody874_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "isdep") (Flapjack.Exp.const 0#64)) globalBody874_14 globalBody874_6

def globalBody874_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def globalBody874_17 : Prog (BitVec 64) :=
.seq globalBody874_15 globalBody874_16

def globalBody874_18 : Prog (BitVec 64) :=
.decCall ("isdep") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 512#64]),
  Flapjack.Exp.const 20#64]) globalBody874_17

def globalBody874_19 : Prog (BitVec 64) :=
.dec ("log") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "lp",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 8#64]])) globalBody874_18

def globalBody874_20 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "nl")) globalBody874_19

def globalBody874_21 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody874_22 : Prog (BitVec 64) :=
.seq globalBody874_20 globalBody874_21

def globalBody874_23 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody874_22

def globalBody874_24 : Prog (BitVec 64) :=
.dec ("lp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.const 0#64])) globalBody874_23

def globalBody874_25 : Prog (BitVec 64) :=
.dec ("nl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.const 8#64])) globalBody874_24

def globalBody874_26 : Prog (BitVec 64) :=
.dec ("logs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "rp",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])) globalBody874_25

def globalBody874_27 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nr")) globalBody874_26

def globalBody874_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "requests_append"
  [Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "dep",
    Flapjack.Exp.var Flapjack.VarKind.local "dep_n"]

def globalBody874_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "dep_n")) globalBody874_28 globalBody874_6

def globalBody874_30 : Prog (BitVec 64) :=
.seq globalBody874_27 globalBody874_29

def globalBody874_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "requests_append"
  [Flapjack.Exp.const 1#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o1", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o1", Flapjack.Exp.const 48#64])]

def globalBody874_32 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o1", Flapjack.Exp.const 48#64]))) globalBody874_31 globalBody874_6

def globalBody874_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "requests_append"
  [Flapjack.Exp.const 2#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o2", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o2", Flapjack.Exp.const 48#64])]

def globalBody874_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o2", Flapjack.Exp.const 48#64]))) globalBody874_33 globalBody874_6

def globalBody874_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "requests_append"
  [Flapjack.Exp.const 3#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o3", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o3", Flapjack.Exp.const 48#64])]

def globalBody874_36 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o3", Flapjack.Exp.const 48#64]))) globalBody874_35 globalBody874_6

def globalBody874_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "requests_append"
  [Flapjack.Exp.const 4#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o4", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o4", Flapjack.Exp.const 48#64])]

def globalBody874_38 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o4", Flapjack.Exp.const 48#64]))) globalBody874_37 globalBody874_6

def globalBody874_39 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody874_40 : Prog (BitVec 64) :=
.seq globalBody874_38 globalBody874_39

def globalBody874_41 : Prog (BitVec 64) :=
.decCall ("o4") (Flapjack.Shape.one) ("process_checked_system_transaction") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 504#64])]) globalBody874_40

def globalBody874_42 : Prog (BitVec 64) :=
.seq globalBody874_36 globalBody874_41

def globalBody874_43 : Prog (BitVec 64) :=
.decCall ("o3") (Flapjack.Shape.one) ("process_checked_system_transaction") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 496#64])]) globalBody874_42

def globalBody874_44 : Prog (BitVec 64) :=
.seq globalBody874_34 globalBody874_43

def globalBody874_45 : Prog (BitVec 64) :=
.decCall ("o2") (Flapjack.Shape.one) ("process_checked_system_transaction") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 488#64])]) globalBody874_44

def globalBody874_46 : Prog (BitVec 64) :=
.seq globalBody874_32 globalBody874_45

def globalBody874_47 : Prog (BitVec 64) :=
.decCall ("o1") (Flapjack.Shape.one) ("process_checked_system_transaction") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 480#64])]) globalBody874_46

def globalBody874_48 : Prog (BitVec 64) :=
.seq globalBody874_30 globalBody874_47

def globalBody874_49 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody874_48

def globalBody874_50 : Prog (BitVec 64) :=
.dec ("dep_cap") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody874_49

def globalBody874_51 : Prog (BitVec 64) :=
.dec ("dep_n") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody874_50

def globalBody874_52 : Prog (BitVec 64) :=
.decCall ("dep") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) globalBody874_51

def globalBody874_53 : Prog (BitVec 64) :=
.dec ("rp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rls", Flapjack.Exp.const 0#64])) globalBody874_52

def globalBody874_54 : Prog (BitVec 64) :=
.dec ("nr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rls", Flapjack.Exp.const 8#64])) globalBody874_53

def globalBody874_55 : Prog (BitVec 64) :=
.dec ("rls") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 416#64]),
      Flapjack.Exp.const 72#64])) globalBody874_54

def globalData874 : Decl (BitVec 64) :=
.function { name := "process_general_purpose_requests", inline := false, exported := false, params := [], body := globalBody874_55, returnShape := (Flapjack.Shape.one) }
def globalOutput874 := Pancake.PanLang.declToHOL globalData874
end InitECandidate.Proofs.FrontendStages.Declarations
