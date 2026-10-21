import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify809
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body825_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cplx"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "words"],
      Flapjack.Exp.var Flapjack.VarKind.local "words"])

def body825_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body825_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 32#64) (Flapjack.Exp.var Flapjack.VarKind.local "maxlen")) body825_0 body825_1

def body825_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "hbits"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "hbits", Flapjack.Exp.const 1#64])

def body825_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "hbits")) body825_3 body825_1

def body825_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "count" (Flapjack.Exp.var Flapjack.VarKind.local "hbits")

def body825_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "count"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.const 16#64,
          Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "elen", Flapjack.Exp.const 32#64]],
      Flapjack.Exp.var Flapjack.VarKind.local "hbits"])

def body825_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 32#64) (Flapjack.Exp.var Flapjack.VarKind.local "elen")) body825_5 body825_6

def body825_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "count" (Flapjack.Exp.const 1#64)

def body825_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "count") (Flapjack.Exp.const 1#64)) body825_8 body825_1

def body825_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cost" (Flapjack.Exp.const 500#64)

def body825_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "cost") (Flapjack.Exp.const 500#64)) body825_10 body825_1

def body825_12 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "cost")

def body825_13 : Prog (BitVec 64) :=
.seq body825_11 body825_12

def body825_14 : Prog (BitVec 64) :=
.dec ("cost") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul
  [Flapjack.Exp.var Flapjack.VarKind.local "cplx", Flapjack.Exp.var Flapjack.VarKind.local "count"]) body825_13

def body825_15 : Prog (BitVec 64) :=
.seq body825_9 body825_14

def body825_16 : Prog (BitVec 64) :=
.seq body825_7 body825_15

def body825_17 : Prog (BitVec 64) :=
.dec ("count") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body825_16

def body825_18 : Prog (BitVec 64) :=
.seq body825_4 body825_17

def body825_19 : Prog (BitVec 64) :=
.decCall ("hbits") (Flapjack.Shape.one) ("u256_bit_length") ([Flapjack.Exp.var Flapjack.VarKind.local "head"]) body825_18

def body825_20 : Prog (BitVec 64) :=
.seq body825_2 body825_19

def body825_21 : Prog (BitVec 64) :=
.dec ("cplx") (Flapjack.Shape.one) (Flapjack.Exp.const 16#64) body825_20

def body825_22 : Prog (BitVec 64) :=
.dec ("words") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "maxlen", Flapjack.Exp.const 7#64])
  (Flapjack.Exp.const 3#64)) body825_21

def body825_23 : Prog (BitVec 64) :=
.decCall ("maxlen") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.var Flapjack.VarKind.local "mlen"]) body825_22

def body825_24 : Prog (BitVec 64) :=
.seq body825_7 body825_9

def body825_25 : Prog (BitVec 64) :=
.seq body825_24 body825_14

def body825_26 : Prog (BitVec 64) :=
.dec ("count") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body825_25

def body825_27 : Prog (BitVec 64) :=
.seq body825_4 body825_26

def body825_28 : Prog (BitVec 64) :=
.decCall ("hbits") (Flapjack.Shape.one) ("u256_bit_length") ([Flapjack.Exp.var Flapjack.VarKind.local "head"]) body825_27

def body825_29 : Prog (BitVec 64) :=
.seq body825_2 body825_28

def body825_30 : Prog (BitVec 64) :=
.dec ("cplx") (Flapjack.Shape.one) (Flapjack.Exp.const 16#64) body825_29

def body825_31 : Prog (BitVec 64) :=
.dec ("words") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "maxlen", Flapjack.Exp.const 7#64])
  (Flapjack.Exp.const 3#64)) body825_30

def body825_32 : Prog (BitVec 64) :=
.decCall ("maxlen") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.var Flapjack.VarKind.local "mlen"]) body825_31

def originalData825 : Decl (BitVec 64) :=
.function { name := "modexp_gas", inline := false, exported := false, params := [("blen", Flapjack.Shape.one), ("mlen", Flapjack.Shape.one), ("elen", Flapjack.Shape.one),
  ("head", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body825_23, returnShape := (Flapjack.Shape.one) }
def simplifiedData825 : Decl (BitVec 64) :=
.function { name := "modexp_gas", inline := false, exported := false, params := [("blen", Flapjack.Shape.one), ("mlen", Flapjack.Shape.one), ("elen", Flapjack.Shape.one),
  ("head", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body825_32, returnShape := (Flapjack.Shape.one) }
def original825 := Pancake.PanLang.declToHOL originalData825
def simplified825 := Pancake.PanLang.declToHOL simplifiedData825
end InitECandidate.Proofs.FrontendStages.Declarations
