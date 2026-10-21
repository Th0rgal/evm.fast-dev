import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify557
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body573_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_state_gas" [Flapjack.Exp.const 183600#64]

def body573_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body573_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "e") (Flapjack.Exp.const 0#64)) body573_0 body573_1

def body573_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body573_4 : Prog (BitVec 64) :=
.seq body573_2 body573_3

def body573_5 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("acct_is_empty") ([Flapjack.Exp.var Flapjack.VarKind.local "pre"]) body573_4

def body573_6 : Prog (BitVec 64) :=
.decCall ("pre") (Flapjack.Shape.one) ("get_pre_state_account") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])]) body573_5

def body573_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 24#64]))
  (Flapjack.Exp.const 0#64)) body573_6 body573_1

def body573_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "alive") (Flapjack.Exp.const 0#64)) body573_0 body573_1

def body573_9 : Prog (BitVec 64) :=
.decCall ("alive") (Flapjack.Shape.one) ("is_account_alive") ([Flapjack.Exp.var Flapjack.VarKind.local "recipient"]) body573_8

def body573_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vz") (Flapjack.Exp.const 0#64)) body573_9 body573_1

def body573_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "daddr", Flapjack.Exp.var Flapjack.VarKind.local "da",
    Flapjack.Exp.const 20#64]

def body573_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 100#64]

def body573_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3000#64]

def body573_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "daddr"]

def body573_15 : Prog (BitVec 64) :=
.seq body573_13 body573_14

def body573_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) body573_12 body573_15

def body573_17 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "code"
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dcode"))

def body573_18 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "code_n"
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "dcode"))

def body573_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.const 1#64)

def body573_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "daddr")

def body573_21 : Prog (BitVec 64) :=
.seq body573_19 body573_20

def body573_22 : Prog (BitVec 64) :=
.seq body573_18 body573_21

def body573_23 : Prog (BitVec 64) :=
.seq body573_17 body573_22

def body573_24 : Prog (BitVec 64) :=
.decCall ("dcode") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "daddr"]) body573_23

def body573_25 : Prog (BitVec 64) :=
.seq body573_16 body573_24

def body573_26 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "daddr"]) body573_25

def body573_27 : Prog (BitVec 64) :=
.seq body573_11 body573_26

def body573_28 : Prog (BitVec 64) :=
.decCall ("daddr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body573_27

def body573_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "da") (Flapjack.Exp.const 0#64)) body573_28 body573_1

def body573_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code")

def body573_31 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code_n")

def body573_32 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code")

def body573_33 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code_n")

def body573_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "jd")

def body573_35 : Prog (BitVec 64) :=
.seq body573_34 body573_3

def body573_36 : Prog (BitVec 64) :=
.decCall ("jd") (Flapjack.Shape.one) ("compute_jumpdests") ([Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.var Flapjack.VarKind.local "code_n"]) body573_35

def body573_37 : Prog (BitVec 64) :=
.seq body573_33 body573_36

def body573_38 : Prog (BitVec 64) :=
.seq body573_32 body573_37

def body573_39 : Prog (BitVec 64) :=
.seq body573_31 body573_38

def body573_40 : Prog (BitVec 64) :=
.seq body573_30 body573_39

def body573_41 : Prog (BitVec 64) :=
.seq body573_29 body573_40

def body573_42 : Prog (BitVec 64) :=
.decCall ("da") (Flapjack.Shape.one) ("get_delegated_code_address") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rcode"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rcode")]) body573_41

def body573_43 : Prog (BitVec 64) :=
.dec ("code_n") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rcode")) body573_42

def body573_44 : Prog (BitVec 64) :=
.dec ("code") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rcode")) body573_43

def body573_45 : Prog (BitVec 64) :=
.decCall ("rcode") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "recipient"]) body573_44

def body573_46 : Prog (BitVec 64) :=
.seq body573_10 body573_45

def body573_47 : Prog (BitVec 64) :=
.decCall ("vz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 56#64])]) body573_46

def body573_48 : Prog (BitVec 64) :=
.dec ("recipient") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])) body573_47

def body573_49 : Prog (BitVec 64) :=
.seq body573_7 body573_48

def body573_50 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body573_49

def body573_51 : Prog (BitVec 64) :=
.seq body573_17 body573_18

def body573_52 : Prog (BitVec 64) :=
.seq body573_51 body573_19

def body573_53 : Prog (BitVec 64) :=
.seq body573_52 body573_20

def body573_54 : Prog (BitVec 64) :=
.decCall ("dcode") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "daddr"]) body573_53

def body573_55 : Prog (BitVec 64) :=
.seq body573_16 body573_54

def body573_56 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "daddr"]) body573_55

def body573_57 : Prog (BitVec 64) :=
.seq body573_11 body573_56

def body573_58 : Prog (BitVec 64) :=
.decCall ("daddr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body573_57

def body573_59 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "da") (Flapjack.Exp.const 0#64)) body573_58 body573_1

def body573_60 : Prog (BitVec 64) :=
.seq body573_59 body573_30

def body573_61 : Prog (BitVec 64) :=
.seq body573_60 body573_31

def body573_62 : Prog (BitVec 64) :=
.seq body573_61 body573_32

def body573_63 : Prog (BitVec 64) :=
.seq body573_62 body573_33

def body573_64 : Prog (BitVec 64) :=
.seq body573_63 body573_36

def body573_65 : Prog (BitVec 64) :=
.decCall ("da") (Flapjack.Shape.one) ("get_delegated_code_address") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rcode"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rcode")]) body573_64

def body573_66 : Prog (BitVec 64) :=
.dec ("code_n") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rcode")) body573_65

def body573_67 : Prog (BitVec 64) :=
.dec ("code") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rcode")) body573_66

def body573_68 : Prog (BitVec 64) :=
.decCall ("rcode") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "recipient"]) body573_67

def body573_69 : Prog (BitVec 64) :=
.seq body573_10 body573_68

def body573_70 : Prog (BitVec 64) :=
.decCall ("vz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 56#64])]) body573_69

def body573_71 : Prog (BitVec 64) :=
.dec ("recipient") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])) body573_70

def body573_72 : Prog (BitVec 64) :=
.seq body573_7 body573_71

def body573_73 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body573_72

def originalData573 : Decl (BitVec 64) :=
.function { name := "prepare_dispatch", inline := false, exported := false, params := [], body := body573_50, returnShape := (Flapjack.Shape.one) }
def simplifiedData573 : Decl (BitVec 64) :=
.function { name := "prepare_dispatch", inline := false, exported := false, params := [], body := body573_73, returnShape := (Flapjack.Shape.one) }
def original573 := Pancake.PanLang.declToHOL originalData573
def simplified573 := Pancake.PanLang.declToHOL simplifiedData573
end InitECandidate.Proofs.FrontendStages.Declarations
