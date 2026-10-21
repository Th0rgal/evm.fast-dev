import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data286
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate270
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody286_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "dst") (Flapjack.Exp.const 128#64)

def globalBody286_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody286_2 : Prog (BitVec 64) :=
.seq globalBody286_0 globalBody286_1

def globalBody286_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody286_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "child") (Flapjack.Exp.const 0#64)) globalBody286_2 globalBody286_3

def globalBody286_5 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "dst") (Flapjack.Exp.const 160#64)

def globalBody286_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 1#64],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.const 32#64]

def globalBody286_7 : Prog (BitVec 64) :=
.seq globalBody286_5 globalBody286_6

def globalBody286_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 33#64)

def globalBody286_9 : Prog (BitVec 64) :=
.seq globalBody286_7 globalBody286_8

def globalBody286_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) globalBody286_9 globalBody286_3

def globalBody286_11 : Prog (BitVec 64) :=
.seq globalBody286_4 globalBody286_10

def globalBody286_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 13#64]

def globalBody286_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 0#64)) globalBody286_12 globalBody286_3

def globalBody286_14 : Prog (BitVec 64) :=
.seq globalBody286_11 globalBody286_13

def globalBody286_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "rp",
    Flapjack.Exp.var Flapjack.VarKind.local "rl"]

def globalBody286_16 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "rl")

def globalBody286_17 : Prog (BitVec 64) :=
.seq globalBody286_15 globalBody286_16

def globalBody286_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "rl") (Flapjack.Exp.const 32#64)) globalBody286_17 globalBody286_3

def globalBody286_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 32#64]

def globalBody286_20 : Prog (BitVec 64) :=
.seq globalBody286_5 globalBody286_19

def globalBody286_21 : Prog (BitVec 64) :=
.seq globalBody286_20 globalBody286_8

def globalBody286_22 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("node_hash_cached") ([Flapjack.Exp.var Flapjack.VarKind.local "child"]) globalBody286_21

def globalBody286_23 : Prog (BitVec 64) :=
.seq globalBody286_18 globalBody286_22

def globalBody286_24 : Prog (BitVec 64) :=
.dec ("rl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 16#64])) globalBody286_23

def globalBody286_25 : Prog (BitVec 64) :=
.dec ("rp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 8#64])) globalBody286_24

def globalBody286_26 : Prog (BitVec 64) :=
.seq globalBody286_14 globalBody286_25

def globalData286 : Decl (BitVec 64) :=
.function { name := "node_write_ref", inline := false, exported := false, params := [("child", Flapjack.Shape.one), ("dst", Flapjack.Shape.one)], body := globalBody286_26, returnShape := (Flapjack.Shape.one) }
def globalOutput286 := Pancake.PanLang.declToHOL globalData286
end InitECandidate.Proofs.FrontendStages.Declarations
