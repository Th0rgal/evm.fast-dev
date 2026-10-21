import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data455
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate439
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody455_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def globalBody455_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody455_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) globalBody455_0 globalBody455_1

def globalBody455_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 0#64])

def globalBody455_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "endp")
  (Flapjack.Exp.const 18446744073709551615#64)) globalBody455_3 globalBody455_1

def globalBody455_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "before")
  (Flapjack.Exp.var Flapjack.VarKind.local "after")) globalBody455_0 globalBody455_1

def globalBody455_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ca")
  (Flapjack.Exp.const 18446744073709551615#64)) globalBody455_3 globalBody455_1

def globalBody455_7 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "ca", Flapjack.Exp.var Flapjack.VarKind.local "cb"],
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "after", Flapjack.Exp.var Flapjack.VarKind.local "before"]])

def globalBody455_8 : Prog (BitVec 64) :=
.seq globalBody455_6 globalBody455_7

def globalBody455_9 : Prog (BitVec 64) :=
.decCall ("cb") (Flapjack.Shape.one) ("memory_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "before"]) globalBody455_8

def globalBody455_10 : Prog (BitVec 64) :=
.decCall ("ca") (Flapjack.Shape.one) ("memory_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "after"]) globalBody455_9

def globalBody455_11 : Prog (BitVec 64) :=
.seq globalBody455_5 globalBody455_10

def globalBody455_12 : Prog (BitVec 64) :=
.decCall ("after") (Flapjack.Shape.one) ("ceil32") ([Flapjack.Exp.var Flapjack.VarKind.local "endp"]) globalBody455_11

def globalBody455_13 : Prog (BitVec 64) :=
.decCall ("before") (Flapjack.Shape.one) ("ceil32") ([Flapjack.Exp.var Flapjack.VarKind.local "cur"]) globalBody455_12

def globalBody455_14 : Prog (BitVec 64) :=
.dec ("cur") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 32#64])) globalBody455_13

def globalBody455_15 : Prog (BitVec 64) :=
.seq globalBody455_4 globalBody455_14

def globalBody455_16 : Prog (BitVec 64) :=
.decCall ("endp") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.var Flapjack.VarKind.local "n"]) globalBody455_15

def globalBody455_17 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "size"]) globalBody455_16

def globalBody455_18 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "start"]) globalBody455_17

def globalBody455_19 : Prog (BitVec 64) :=
.seq globalBody455_2 globalBody455_18

def globalBody455_20 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "size"]) globalBody455_19

def globalData455 : Decl (BitVec 64) :=
.function { name := "extend_memory_cost1", inline := false, exported := false, params := [("start", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("size", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := globalBody455_20, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput455 := Pancake.PanLang.declToHOL globalData455
end InitECandidate.Proofs.FrontendStages.Declarations
