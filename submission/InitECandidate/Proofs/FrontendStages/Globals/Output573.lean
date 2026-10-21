import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data573
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate553
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody573_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_state_gas" [Flapjack.Exp.const 183600#64]

def globalBody573_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody573_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "e") (Flapjack.Exp.const 0#64)) globalBody573_0 globalBody573_1

def globalBody573_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody573_4 : Prog (BitVec 64) :=
.seq globalBody573_2 globalBody573_3

def globalBody573_5 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("acct_is_empty") ([Flapjack.Exp.var Flapjack.VarKind.local "pre"]) globalBody573_4

def globalBody573_6 : Prog (BitVec 64) :=
.decCall ("pre") (Flapjack.Shape.one) ("get_pre_state_account") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])]) globalBody573_5

def globalBody573_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 24#64]))
  (Flapjack.Exp.const 0#64)) globalBody573_6 globalBody573_1

def globalBody573_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "alive") (Flapjack.Exp.const 0#64)) globalBody573_0 globalBody573_1

def globalBody573_9 : Prog (BitVec 64) :=
.decCall ("alive") (Flapjack.Shape.one) ("is_account_alive") ([Flapjack.Exp.var Flapjack.VarKind.local "recipient"]) globalBody573_8

def globalBody573_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vz") (Flapjack.Exp.const 0#64)) globalBody573_9 globalBody573_1

def globalBody573_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "daddr", Flapjack.Exp.var Flapjack.VarKind.local "da",
    Flapjack.Exp.const 20#64]

def globalBody573_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 100#64]

def globalBody573_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3000#64]

def globalBody573_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_address" [Flapjack.Exp.var Flapjack.VarKind.local "daddr"]

def globalBody573_15 : Prog (BitVec 64) :=
.seq globalBody573_13 globalBody573_14

def globalBody573_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) globalBody573_12 globalBody573_15

def globalBody573_17 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "code"
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dcode"))

def globalBody573_18 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "code_n"
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "dcode"))

def globalBody573_19 : Prog (BitVec 64) :=
.seq globalBody573_17 globalBody573_18

def globalBody573_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.const 1#64)

def globalBody573_21 : Prog (BitVec 64) :=
.seq globalBody573_19 globalBody573_20

def globalBody573_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "daddr")

def globalBody573_23 : Prog (BitVec 64) :=
.seq globalBody573_21 globalBody573_22

def globalBody573_24 : Prog (BitVec 64) :=
.decCall ("dcode") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "daddr"]) globalBody573_23

def globalBody573_25 : Prog (BitVec 64) :=
.seq globalBody573_16 globalBody573_24

def globalBody573_26 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "daddr"]) globalBody573_25

def globalBody573_27 : Prog (BitVec 64) :=
.seq globalBody573_11 globalBody573_26

def globalBody573_28 : Prog (BitVec 64) :=
.decCall ("daddr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) globalBody573_27

def globalBody573_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "da") (Flapjack.Exp.const 0#64)) globalBody573_28 globalBody573_1

def globalBody573_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code")

def globalBody573_31 : Prog (BitVec 64) :=
.seq globalBody573_29 globalBody573_30

def globalBody573_32 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code_n")

def globalBody573_33 : Prog (BitVec 64) :=
.seq globalBody573_31 globalBody573_32

def globalBody573_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code")

def globalBody573_35 : Prog (BitVec 64) :=
.seq globalBody573_33 globalBody573_34

def globalBody573_36 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code_n")

def globalBody573_37 : Prog (BitVec 64) :=
.seq globalBody573_35 globalBody573_36

def globalBody573_38 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 80#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "jd")

def globalBody573_39 : Prog (BitVec 64) :=
.seq globalBody573_38 globalBody573_3

def globalBody573_40 : Prog (BitVec 64) :=
.decCall ("jd") (Flapjack.Shape.one) ("compute_jumpdests") ([Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.var Flapjack.VarKind.local "code_n"]) globalBody573_39

def globalBody573_41 : Prog (BitVec 64) :=
.seq globalBody573_37 globalBody573_40

def globalBody573_42 : Prog (BitVec 64) :=
.decCall ("da") (Flapjack.Shape.one) ("get_delegated_code_address") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rcode"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rcode")]) globalBody573_41

def globalBody573_43 : Prog (BitVec 64) :=
.dec ("code_n") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rcode")) globalBody573_42

def globalBody573_44 : Prog (BitVec 64) :=
.dec ("code") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rcode")) globalBody573_43

def globalBody573_45 : Prog (BitVec 64) :=
.decCall ("rcode") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "recipient"]) globalBody573_44

def globalBody573_46 : Prog (BitVec 64) :=
.seq globalBody573_10 globalBody573_45

def globalBody573_47 : Prog (BitVec 64) :=
.decCall ("vz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 56#64])]) globalBody573_46

def globalBody573_48 : Prog (BitVec 64) :=
.dec ("recipient") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])) globalBody573_47

def globalBody573_49 : Prog (BitVec 64) :=
.seq globalBody573_7 globalBody573_48

def globalBody573_50 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 112#64])) globalBody573_49

def globalData573 : Decl (BitVec 64) :=
.function { name := "prepare_dispatch", inline := false, exported := false, params := [], body := globalBody573_50, returnShape := (Flapjack.Shape.one) }
def globalOutput573 := Pancake.PanLang.declToHOL globalData573
end InitECandidate.Proofs.FrontendStages.Declarations
