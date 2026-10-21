import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data301
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate284
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody301_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "buf",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]],
    Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 32#64]

def globalBody301_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody301_2 : Prog (BitVec 64) :=
.seq globalBody301_0 globalBody301_1

def globalBody301_3 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("tx_fixed_bytes") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "lst"), Flapjack.Exp.var Flapjack.VarKind.local "i",
  Flapjack.Exp.const 32#64]) globalBody301_2

def globalBody301_4 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst"))) globalBody301_3

def globalBody301_5 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "buf",
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst")])

def globalBody301_6 : Prog (BitVec 64) :=
.seq globalBody301_4 globalBody301_5

def globalBody301_7 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody301_6

def globalBody301_8 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst"), Flapjack.Exp.const 32#64]]) globalBody301_7

def globalBody301_9 : Prog (BitVec 64) :=
.decCall ("lst") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "len"]) globalBody301_8

def globalData301 : Decl (BitVec 64) :=
.function { name := "decode_blob_hashes", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := globalBody301_9, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput301 := Pancake.PanLang.declToHOL globalData301
end InitECandidate.Proofs.FrontendStages.Declarations
