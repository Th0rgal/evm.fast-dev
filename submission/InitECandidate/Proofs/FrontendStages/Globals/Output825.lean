import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data825
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate809
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody825_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cplx"
  (Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "words"],
      Flapjack.Exp.var Flapjack.VarKind.local "words"])

def globalBody825_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody825_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 32#64) (Flapjack.Exp.var Flapjack.VarKind.local "maxlen")) globalBody825_0 globalBody825_1

def globalBody825_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "hbits"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "hbits", Flapjack.Exp.const 1#64])

def globalBody825_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "hbits")) globalBody825_3 globalBody825_1

def globalBody825_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "count" (Flapjack.Exp.var Flapjack.VarKind.local "hbits")

def globalBody825_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "count"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.const 16#64,
          Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "elen", Flapjack.Exp.const 32#64]],
      Flapjack.Exp.var Flapjack.VarKind.local "hbits"])

def globalBody825_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 32#64) (Flapjack.Exp.var Flapjack.VarKind.local "elen")) globalBody825_5 globalBody825_6

def globalBody825_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "count" (Flapjack.Exp.const 1#64)

def globalBody825_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "count") (Flapjack.Exp.const 1#64)) globalBody825_8 globalBody825_1

def globalBody825_10 : Prog (BitVec 64) :=
.seq globalBody825_7 globalBody825_9

def globalBody825_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cost" (Flapjack.Exp.const 500#64)

def globalBody825_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "cost") (Flapjack.Exp.const 500#64)) globalBody825_11 globalBody825_1

def globalBody825_13 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "cost")

def globalBody825_14 : Prog (BitVec 64) :=
.seq globalBody825_12 globalBody825_13

def globalBody825_15 : Prog (BitVec 64) :=
.dec ("cost") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul
  [Flapjack.Exp.var Flapjack.VarKind.local "cplx", Flapjack.Exp.var Flapjack.VarKind.local "count"]) globalBody825_14

def globalBody825_16 : Prog (BitVec 64) :=
.seq globalBody825_10 globalBody825_15

def globalBody825_17 : Prog (BitVec 64) :=
.dec ("count") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody825_16

def globalBody825_18 : Prog (BitVec 64) :=
.seq globalBody825_4 globalBody825_17

def globalBody825_19 : Prog (BitVec 64) :=
.decCall ("hbits") (Flapjack.Shape.one) ("u256_bit_length") ([Flapjack.Exp.var Flapjack.VarKind.local "head"]) globalBody825_18

def globalBody825_20 : Prog (BitVec 64) :=
.seq globalBody825_2 globalBody825_19

def globalBody825_21 : Prog (BitVec 64) :=
.dec ("cplx") (Flapjack.Shape.one) (Flapjack.Exp.const 16#64) globalBody825_20

def globalBody825_22 : Prog (BitVec 64) :=
.dec ("words") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "maxlen", Flapjack.Exp.const 7#64])
  (Flapjack.Exp.const 3#64)) globalBody825_21

def globalBody825_23 : Prog (BitVec 64) :=
.decCall ("maxlen") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.var Flapjack.VarKind.local "mlen"]) globalBody825_22

def globalData825 : Decl (BitVec 64) :=
.function { name := "modexp_gas", inline := false, exported := false, params := [("blen", Flapjack.Shape.one), ("mlen", Flapjack.Shape.one), ("elen", Flapjack.Shape.one),
  ("head", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := globalBody825_23, returnShape := (Flapjack.Shape.one) }
def globalOutput825 := Pancake.PanLang.declToHOL globalData825
end InitECandidate.Proofs.FrontendStages.Declarations
