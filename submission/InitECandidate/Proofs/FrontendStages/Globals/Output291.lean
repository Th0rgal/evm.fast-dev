import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data291
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate275
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody291_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "off"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "off", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody291_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 152#64]),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "balance")]

def globalBody291_2 : Prog (BitVec 64) :=
.seq globalBody291_0 globalBody291_1

def globalBody291_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 152#64]),
        Flapjack.Exp.const 8#64],
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "balance")]

def globalBody291_4 : Prog (BitVec 64) :=
.seq globalBody291_2 globalBody291_3

def globalBody291_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 152#64]),
        Flapjack.Exp.const 16#64],
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "balance")]

def globalBody291_6 : Prog (BitVec 64) :=
.seq globalBody291_4 globalBody291_5

def globalBody291_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 152#64]),
        Flapjack.Exp.const 24#64],
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "balance")]

def globalBody291_8 : Prog (BitVec 64) :=
.seq globalBody291_6 globalBody291_7

def globalBody291_9 : Prog (BitVec 64) :=
Flapjack.Prog.break

def globalBody291_10 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody291_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.loadByte
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 152#64]),
        Flapjack.Exp.var Flapjack.VarKind.local "z"]))
  (Flapjack.Exp.const 0#64)) globalBody291_9 globalBody291_10

def globalBody291_12 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "z"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "z", Flapjack.Exp.const 1#64])

def globalBody291_13 : Prog (BitVec 64) :=
.seq globalBody291_11 globalBody291_12

def globalBody291_14 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 32#64)) globalBody291_13

def globalBody291_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "off"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "off", Flapjack.Exp.var Flapjack.VarKind.local "wb"])

def globalBody291_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "off"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "off", Flapjack.Exp.var Flapjack.VarKind.local "wsl"])

def globalBody291_17 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "off"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "off", Flapjack.Exp.var Flapjack.VarKind.local "wc"])

def globalBody291_18 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "out") (Flapjack.Exp.const 248#64)

def globalBody291_19 : Prog (BitVec 64) :=
.seq globalBody291_17 globalBody291_18

def globalBody291_20 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "off", Flapjack.Exp.const 2#64])

def globalBody291_21 : Prog (BitVec 64) :=
.seq globalBody291_19 globalBody291_20

def globalBody291_22 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "off")

def globalBody291_23 : Prog (BitVec 64) :=
.seq globalBody291_21 globalBody291_22

def globalBody291_24 : Prog (BitVec 64) :=
.decCall ("wc") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.var Flapjack.VarKind.local "code_hash", Flapjack.Exp.const 32#64]) globalBody291_23

def globalBody291_25 : Prog (BitVec 64) :=
.seq globalBody291_16 globalBody291_24

def globalBody291_26 : Prog (BitVec 64) :=
.decCall ("wsl") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.var Flapjack.VarKind.local "storage_root", Flapjack.Exp.const 32#64]) globalBody291_25

def globalBody291_27 : Prog (BitVec 64) :=
.seq globalBody291_15 globalBody291_26

def globalBody291_28 : Prog (BitVec 64) :=
.decCall ("wb") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 152#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "z"],
  Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "z"]]) globalBody291_27

def globalBody291_29 : Prog (BitVec 64) :=
.seq globalBody291_14 globalBody291_28

def globalBody291_30 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody291_29

def globalBody291_31 : Prog (BitVec 64) :=
.seq globalBody291_8 globalBody291_30

def globalBody291_32 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_word") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.var Flapjack.VarKind.local "nonce"]) globalBody291_31

def globalBody291_33 : Prog (BitVec 64) :=
.dec ("off") (Flapjack.Shape.one) (Flapjack.Exp.const 2#64) globalBody291_32

def globalData291 : Decl (BitVec 64) :=
.function { name := "encode_account", inline := false, exported := false, params := [("nonce", Flapjack.Shape.one),
  ("balance", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("storage_root", Flapjack.Shape.one), ("code_hash", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody291_33, returnShape := (Flapjack.Shape.one) }
def globalOutput291 := Pancake.PanLang.declToHOL globalData291
end InitECandidate.Proofs.FrontendStages.Declarations
