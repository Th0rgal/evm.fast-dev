import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify275
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body291_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "off"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "off", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body291_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch",
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "balance")]

def body291_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch", Flapjack.Exp.const 8#64],
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "balance")]

def body291_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch", Flapjack.Exp.const 16#64],
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "balance")]

def body291_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch", Flapjack.Exp.const 24#64],
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "balance")]

def body291_5 : Prog (BitVec 64) :=
Flapjack.Prog.break

def body291_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body291_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.loadByte
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch", Flapjack.Exp.var Flapjack.VarKind.local "z"]))
  (Flapjack.Exp.const 0#64)) body291_5 body291_6

def body291_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "z"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "z", Flapjack.Exp.const 1#64])

def body291_9 : Prog (BitVec 64) :=
.seq body291_7 body291_8

def body291_10 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 32#64)) body291_9

def body291_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "off"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "off", Flapjack.Exp.var Flapjack.VarKind.local "wb"])

def body291_12 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "off"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "off", Flapjack.Exp.var Flapjack.VarKind.local "wsl"])

def body291_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "off"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "off", Flapjack.Exp.var Flapjack.VarKind.local "wc"])

def body291_14 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "out") (Flapjack.Exp.const 248#64)

def body291_15 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "off", Flapjack.Exp.const 2#64])

def body291_16 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "off")

def body291_17 : Prog (BitVec 64) :=
.seq body291_15 body291_16

def body291_18 : Prog (BitVec 64) :=
.seq body291_14 body291_17

def body291_19 : Prog (BitVec 64) :=
.seq body291_13 body291_18

def body291_20 : Prog (BitVec 64) :=
.decCall ("wc") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.var Flapjack.VarKind.local "code_hash", Flapjack.Exp.const 32#64]) body291_19

def body291_21 : Prog (BitVec 64) :=
.seq body291_12 body291_20

def body291_22 : Prog (BitVec 64) :=
.decCall ("wsl") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.var Flapjack.VarKind.local "storage_root", Flapjack.Exp.const 32#64]) body291_21

def body291_23 : Prog (BitVec 64) :=
.seq body291_11 body291_22

def body291_24 : Prog (BitVec 64) :=
.decCall ("wb") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch", Flapjack.Exp.var Flapjack.VarKind.local "z"],
  Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "z"]]) body291_23

def body291_25 : Prog (BitVec 64) :=
.seq body291_10 body291_24

def body291_26 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body291_25

def body291_27 : Prog (BitVec 64) :=
.seq body291_4 body291_26

def body291_28 : Prog (BitVec 64) :=
.seq body291_3 body291_27

def body291_29 : Prog (BitVec 64) :=
.seq body291_2 body291_28

def body291_30 : Prog (BitVec 64) :=
.seq body291_1 body291_29

def body291_31 : Prog (BitVec 64) :=
.seq body291_0 body291_30

def body291_32 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_word") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.var Flapjack.VarKind.local "nonce"]) body291_31

def body291_33 : Prog (BitVec 64) :=
.dec ("off") (Flapjack.Shape.one) (Flapjack.Exp.const 2#64) body291_32

def body291_34 : Prog (BitVec 64) :=
.seq body291_0 body291_1

def body291_35 : Prog (BitVec 64) :=
.seq body291_34 body291_2

def body291_36 : Prog (BitVec 64) :=
.seq body291_35 body291_3

def body291_37 : Prog (BitVec 64) :=
.seq body291_36 body291_4

def body291_38 : Prog (BitVec 64) :=
.seq body291_13 body291_14

def body291_39 : Prog (BitVec 64) :=
.seq body291_38 body291_15

def body291_40 : Prog (BitVec 64) :=
.seq body291_39 body291_16

def body291_41 : Prog (BitVec 64) :=
.decCall ("wc") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.var Flapjack.VarKind.local "code_hash", Flapjack.Exp.const 32#64]) body291_40

def body291_42 : Prog (BitVec 64) :=
.seq body291_12 body291_41

def body291_43 : Prog (BitVec 64) :=
.decCall ("wsl") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.var Flapjack.VarKind.local "storage_root", Flapjack.Exp.const 32#64]) body291_42

def body291_44 : Prog (BitVec 64) :=
.seq body291_11 body291_43

def body291_45 : Prog (BitVec 64) :=
.decCall ("wb") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch", Flapjack.Exp.var Flapjack.VarKind.local "z"],
  Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "z"]]) body291_44

def body291_46 : Prog (BitVec 64) :=
.seq body291_10 body291_45

def body291_47 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body291_46

def body291_48 : Prog (BitVec 64) :=
.seq body291_37 body291_47

def body291_49 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_word") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "off"],
  Flapjack.Exp.var Flapjack.VarKind.local "nonce"]) body291_48

def body291_50 : Prog (BitVec 64) :=
.dec ("off") (Flapjack.Shape.one) (Flapjack.Exp.const 2#64) body291_49

def originalData291 : Decl (BitVec 64) :=
.function { name := "encode_account", inline := false, exported := false, params := [("nonce", Flapjack.Shape.one),
  ("balance", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("storage_root", Flapjack.Shape.one), ("code_hash", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body291_33, returnShape := (Flapjack.Shape.one) }
def simplifiedData291 : Decl (BitVec 64) :=
.function { name := "encode_account", inline := false, exported := false, params := [("nonce", Flapjack.Shape.one),
  ("balance", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("storage_root", Flapjack.Shape.one), ("code_hash", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body291_50, returnShape := (Flapjack.Shape.one) }
def original291 := Pancake.PanLang.declToHOL originalData291
def simplified291 := Pancake.PanLang.declToHOL simplifiedData291
end InitECandidate.Proofs.FrontendStages.Declarations
