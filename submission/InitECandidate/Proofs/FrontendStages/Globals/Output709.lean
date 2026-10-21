import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data709
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate693
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody709_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def globalBody709_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody709_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "az") (Flapjack.Exp.const 1#64)) globalBody709_0 globalBody709_1

def globalBody709_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "x1")

def globalBody709_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "u"))
  (Flapjack.Exp.const 1#64)) globalBody709_3 globalBody709_1

def globalBody709_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "u"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "u"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "u"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "u"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "u")])
  (Flapjack.Exp.const 0#64)) globalBody709_4 globalBody709_1

def globalBody709_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "x2")

def globalBody709_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
  (Flapjack.Exp.const 1#64)) globalBody709_6 globalBody709_1

def globalBody709_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "v"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "v"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "v"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "v"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "v")])
  (Flapjack.Exp.const 0#64)) globalBody709_7 globalBody709_1

def globalBody709_9 : Prog (BitVec 64) :=
.seq globalBody709_5 globalBody709_8

def globalBody709_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "u"), none)) "bls_fp_shr1"
  [Flapjack.Exp.var Flapjack.VarKind.local "u"]

def globalBody709_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x1"), none)) "bls_fp_half_can"
  [Flapjack.Exp.var Flapjack.VarKind.local "x1"]

def globalBody709_12 : Prog (BitVec 64) :=
.seq globalBody709_10 globalBody709_11

def globalBody709_13 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "u"), Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 0#64)) globalBody709_12

def globalBody709_14 : Prog (BitVec 64) :=
.seq globalBody709_9 globalBody709_13

def globalBody709_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "bls_fp_shr1"
  [Flapjack.Exp.var Flapjack.VarKind.local "v"]

def globalBody709_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x2"), none)) "bls_fp_half_can"
  [Flapjack.Exp.var Flapjack.VarKind.local "x2"]

def globalBody709_17 : Prog (BitVec 64) :=
.seq globalBody709_15 globalBody709_16

def globalBody709_18 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"), Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 0#64)) globalBody709_17

def globalBody709_19 : Prog (BitVec 64) :=
.seq globalBody709_14 globalBody709_18

def globalBody709_20 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "u"
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "d")])

def globalBody709_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x1"), none)) "bls_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "x2"]

def globalBody709_22 : Prog (BitVec 64) :=
.seq globalBody709_20 globalBody709_21

def globalBody709_23 : Prog (BitVec 64) :=
.decCall ("d") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one]) ("bls_fp_sub_raw") ([Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "v"]) globalBody709_22

def globalBody709_24 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "v"
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "e")])

def globalBody709_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x2"), none)) "bls_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "x2", Flapjack.Exp.var Flapjack.VarKind.local "x1"]

def globalBody709_26 : Prog (BitVec 64) :=
.seq globalBody709_24 globalBody709_25

def globalBody709_27 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one]) ("bls_fp_sub_raw") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "u"]) globalBody709_26

def globalBody709_28 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ult") (Flapjack.Exp.const 0#64)) globalBody709_23 globalBody709_27

def globalBody709_29 : Prog (BitVec 64) :=
.decCall ("ult") (Flapjack.Shape.one) ("bls_fp_lt_raw") ([Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "v"]) globalBody709_28

def globalBody709_30 : Prog (BitVec 64) :=
.seq globalBody709_19 globalBody709_29

def globalBody709_31 : Prog (BitVec 64) :=
.while (Flapjack.Exp.const 1#64) globalBody709_30

def globalBody709_32 : Prog (BitVec 64) :=
.seq globalBody709_31 globalBody709_0

def globalBody709_33 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody709_32

def globalBody709_34 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 1#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody709_33

def globalBody709_35 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 13402431016077863595#64, Flapjack.Exp.const 2210141511517208575#64,
    Flapjack.Exp.const 7435674573564081700#64, Flapjack.Exp.const 7239337960414712511#64,
    Flapjack.Exp.const 5412103778470702295#64, Flapjack.Exp.const 1873798617647539866#64]) globalBody709_34

def globalBody709_36 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.var Flapjack.VarKind.local "a") globalBody709_35

def globalBody709_37 : Prog (BitVec 64) :=
.seq globalBody709_2 globalBody709_36

def globalBody709_38 : Prog (BitVec 64) :=
.decCall ("az") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "a"]) globalBody709_37

def globalData709 : Decl (BitVec 64) :=
.function { name := "bls_fp_inv_raw", inline := false, exported := false, params := [("a",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := globalBody709_38, returnShape := (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) }
def globalOutput709 := Pancake.PanLang.declToHOL globalData709
end InitECandidate.Proofs.FrontendStages.Declarations
