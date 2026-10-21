import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data409
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate388
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody409_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m"))

def globalBody409_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody409_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "m"))
  (Flapjack.Exp.const 0#64)) globalBody409_0 globalBody409_1

def globalBody409_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def globalBody409_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 32#64, Flapjack.Exp.const 8#64]

def globalBody409_5 : Prog (BitVec 64) :=
.seq globalBody409_3 globalBody409_4

def globalBody409_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def globalBody409_7 : Prog (BitVec 64) :=
.seq globalBody409_5 globalBody409_6

def globalBody409_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "l")

def globalBody409_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "l"), none)) "lst_new"
  [Flapjack.Exp.const 16#64, Flapjack.Exp.const 4#64]

def globalBody409_10 : Prog (BitVec 64) :=
.seq globalBody409_8 globalBody409_9

def globalBody409_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "l")

def globalBody409_12 : Prog (BitVec 64) :=
.seq globalBody409_10 globalBody409_11

def globalBody409_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "l"), none)) "lst_new"
  [Flapjack.Exp.const 24#64, Flapjack.Exp.const 2#64]

def globalBody409_14 : Prog (BitVec 64) :=
.seq globalBody409_12 globalBody409_13

def globalBody409_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "l")

def globalBody409_16 : Prog (BitVec 64) :=
.seq globalBody409_14 globalBody409_15

def globalBody409_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 216#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "ad"]

def globalBody409_18 : Prog (BitVec 64) :=
.seq globalBody409_16 globalBody409_17

def globalBody409_19 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "ad")

def globalBody409_20 : Prog (BitVec 64) :=
.seq globalBody409_18 globalBody409_19

def globalBody409_21 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.one) ("lst_new") ([Flapjack.Exp.const 40#64, Flapjack.Exp.const 4#64]) globalBody409_20

def globalBody409_22 : Prog (BitVec 64) :=
.seq globalBody409_7 globalBody409_21

def globalBody409_23 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 32#64, Flapjack.Exp.const 8#64]) globalBody409_22

def globalBody409_24 : Prog (BitVec 64) :=
.decCall ("ad") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 40#64]) globalBody409_23

def globalBody409_25 : Prog (BitVec 64) :=
.seq globalBody409_2 globalBody409_24

def globalBody409_26 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 216#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody409_25

def globalData409 : Decl (BitVec 64) :=
.function { name := "bal_ensure_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := globalBody409_26, returnShape := (Flapjack.Shape.one) }
def globalOutput409 := Pancake.PanLang.declToHOL globalData409
end InitECandidate.Proofs.FrontendStages.Declarations
