import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data198
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate178
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody198_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody198_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody198_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) globalBody198_0 globalBody198_1

def globalBody198_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 10#64]

def globalBody198_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "o")
        (Flapjack.Exp.var Flapjack.VarKind.local "fixed"),
      Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "len")
        (Flapjack.Exp.var Flapjack.VarKind.local "o")])) globalBody198_3 globalBody198_1

def globalBody198_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 11#64]

def globalBody198_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "o")
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "offs",
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]],
        Flapjack.Exp.const 8#64]))) globalBody198_5 globalBody198_1

def globalBody198_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) globalBody198_6 globalBody198_1

def globalBody198_8 : Prog (BitVec 64) :=
.seq globalBody198_4 globalBody198_7

def globalBody198_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody198_10 : Prog (BitVec 64) :=
.seq globalBody198_8 globalBody198_9

def globalBody198_11 : Prog (BitVec 64) :=
.dec ("o") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "offs",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])) globalBody198_10

def globalBody198_12 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) globalBody198_11

def globalBody198_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 12#64]

def globalBody198_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "offs"))
  (Flapjack.Exp.var Flapjack.VarKind.local "fixed")) globalBody198_13 globalBody198_1

def globalBody198_15 : Prog (BitVec 64) :=
.seq globalBody198_12 globalBody198_14

def globalBody198_16 : Prog (BitVec 64) :=
.seq globalBody198_15 globalBody198_0

def globalBody198_17 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody198_16

def globalBody198_18 : Prog (BitVec 64) :=
.seq globalBody198_2 globalBody198_17

def globalData198 : Decl (BitVec 64) :=
.function { name := "ssz_check_offsets", inline := false, exported := false, params := [("offs", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("fixed", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := globalBody198_18, returnShape := (Flapjack.Shape.one) }
def globalOutput198 := Pancake.PanLang.declToHOL globalData198
end InitECandidate.Proofs.FrontendStages.Declarations
