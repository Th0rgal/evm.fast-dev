import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data373
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate357
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody373_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def globalBody373_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody373_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody373_0 globalBody373_1

def globalBody373_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "w")),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "w"), Flapjack.Exp.const 8#64])])

def globalBody373_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "w"))
  (Flapjack.Exp.const 0#64)) globalBody373_3 globalBody373_1

def globalBody373_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "htab_get"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 176#64]),
          Flapjack.Exp.const 48#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "code_hash"]

def globalBody373_6 : Prog (BitVec 64) :=
.seq globalBody373_4 globalBody373_5

def globalBody373_7 : Prog (BitVec 64) :=
.seq globalBody373_6 globalBody373_4

def globalBody373_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 184#64]),
          Flapjack.Exp.const 40#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64]

def globalBody373_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "c")

def globalBody373_10 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ws_get_code") ([Flapjack.Exp.var Flapjack.VarKind.local "code_hash"]) globalBody373_9

def globalBody373_11 : Prog (BitVec 64) :=
.seq globalBody373_8 globalBody373_10

def globalBody373_12 : Prog (BitVec 64) :=
.decCall ("k") (Flapjack.Shape.one) ("sk_make") ([Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "code_hash"]) globalBody373_11

def globalBody373_13 : Prog (BitVec 64) :=
.seq globalBody373_7 globalBody373_12

def globalBody373_14 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 184#64]),
        Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "code_hash"]) globalBody373_13

def globalBody373_15 : Prog (BitVec 64) :=
.seq globalBody373_2 globalBody373_14

def globalBody373_16 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "code_hash",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 136#64]),
  Flapjack.Exp.const 32#64]) globalBody373_15

def globalData373 : Decl (BitVec 64) :=
.function { name := "get_code", inline := false, exported := false, params := [("code_hash", Flapjack.Shape.one), ("addr", Flapjack.Shape.one)], body := globalBody373_16, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput373 := Pancake.PanLang.declToHOL globalData373
end InitECandidate.Proofs.FrontendStages.Declarations
