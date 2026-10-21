import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify439
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body455_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body455_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body455_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) body455_0 body455_1

def body455_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 0#64])

def body455_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "endp")
  (Flapjack.Exp.const 18446744073709551615#64)) body455_3 body455_1

def body455_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "before")
  (Flapjack.Exp.var Flapjack.VarKind.local "after")) body455_0 body455_1

def body455_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ca")
  (Flapjack.Exp.const 18446744073709551615#64)) body455_3 body455_1

def body455_7 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "ca", Flapjack.Exp.var Flapjack.VarKind.local "cb"],
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "after", Flapjack.Exp.var Flapjack.VarKind.local "before"]])

def body455_8 : Prog (BitVec 64) :=
.seq body455_6 body455_7

def body455_9 : Prog (BitVec 64) :=
.decCall ("cb") (Flapjack.Shape.one) ("memory_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "before"]) body455_8

def body455_10 : Prog (BitVec 64) :=
.decCall ("ca") (Flapjack.Shape.one) ("memory_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "after"]) body455_9

def body455_11 : Prog (BitVec 64) :=
.seq body455_5 body455_10

def body455_12 : Prog (BitVec 64) :=
.decCall ("after") (Flapjack.Shape.one) ("ceil32") ([Flapjack.Exp.var Flapjack.VarKind.local "endp"]) body455_11

def body455_13 : Prog (BitVec 64) :=
.decCall ("before") (Flapjack.Shape.one) ("ceil32") ([Flapjack.Exp.var Flapjack.VarKind.local "cur"]) body455_12

def body455_14 : Prog (BitVec 64) :=
.dec ("cur") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 32#64])) body455_13

def body455_15 : Prog (BitVec 64) :=
.seq body455_4 body455_14

def body455_16 : Prog (BitVec 64) :=
.decCall ("endp") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.var Flapjack.VarKind.local "n"]) body455_15

def body455_17 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "size"]) body455_16

def body455_18 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "start"]) body455_17

def body455_19 : Prog (BitVec 64) :=
.seq body455_2 body455_18

def body455_20 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "size"]) body455_19

def originalData455 : Decl (BitVec 64) :=
.function { name := "extend_memory_cost1", inline := false, exported := false, params := [("start", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("size", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body455_20, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData455 : Decl (BitVec 64) :=
.function { name := "extend_memory_cost1", inline := false, exported := false, params := [("start", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("size", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body455_20, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original455 := Pancake.PanLang.declToHOL originalData455
def simplified455 := Pancake.PanLang.declToHOL simplifiedData455
end InitECandidate.Proofs.FrontendStages.Declarations
