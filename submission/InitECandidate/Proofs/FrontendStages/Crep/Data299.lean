import InitECandidate.Proofs.FrontendStages.Crep.Translate283
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody299_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "tx_encode_bound" [Flapjack.CrepExp.var 0]

def crepBody299_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.var 3]

def crepBody299_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64])]

def crepBody299_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 9)

def crepBody299_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody299_5 : CrepProg (BitVec 64) :=
.seq crepBody299_3 crepBody299_4

def crepBody299_6 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 8]) crepBody299_5

def crepBody299_7 : CrepProg (BitVec 64) :=
.seq crepBody299_2 crepBody299_6

def crepBody299_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody299_7 crepBody299_4

def crepBody299_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody299_10 : CrepProg (BitVec 64) :=
.seq crepBody299_8 crepBody299_9

def crepBody299_11 : CrepProg (BitVec 64) :=
.seq crepBody299_10 crepBody299_6

def crepBody299_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody299_13 : CrepProg (BitVec 64) :=
.seq crepBody299_12 crepBody299_6

def crepBody299_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody299_15 : CrepProg (BitVec 64) :=
.seq crepBody299_14 crepBody299_6

def crepBody299_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody299_17 : CrepProg (BitVec 64) :=
.seq crepBody299_15 crepBody299_16

def crepBody299_18 : CrepProg (BitVec 64) :=
.seq crepBody299_17 crepBody299_6

def crepBody299_19 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.const 1#64) (Flapjack.CrepExp.var 7)) crepBody299_13 crepBody299_18

def crepBody299_20 : CrepProg (BitVec 64) :=
.seq crepBody299_11 crepBody299_19

def crepBody299_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 144#64])]

def crepBody299_22 : CrepProg (BitVec 64) :=
.seq crepBody299_20 crepBody299_21

def crepBody299_23 : CrepProg (BitVec 64) :=
.seq crepBody299_22 crepBody299_6

def crepBody299_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_to"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 152#64])]

def crepBody299_25 : CrepProg (BitVec 64) :=
.seq crepBody299_23 crepBody299_24

def crepBody299_26 : CrepProg (BitVec 64) :=
.seq crepBody299_25 crepBody299_6

def crepBody299_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody299_28 : CrepProg (BitVec 64) :=
.seq crepBody299_26 crepBody299_27

def crepBody299_29 : CrepProg (BitVec 64) :=
.seq crepBody299_28 crepBody299_6

def crepBody299_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 200#64])]

def crepBody299_31 : CrepProg (BitVec 64) :=
.seq crepBody299_29 crepBody299_30

def crepBody299_32 : CrepProg (BitVec 64) :=
.seq crepBody299_31 crepBody299_6

def crepBody299_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_access_list"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 208#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 216#64])]

def crepBody299_34 : CrepProg (BitVec 64) :=
.seq crepBody299_33 crepBody299_6

def crepBody299_35 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody299_34 crepBody299_4

def crepBody299_36 : CrepProg (BitVec 64) :=
.seq crepBody299_32 crepBody299_35

def crepBody299_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 224#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 224#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 224#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 224#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody299_38 : CrepProg (BitVec 64) :=
.seq crepBody299_37 crepBody299_6

def crepBody299_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_blob_hashes"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 264#64])]

def crepBody299_40 : CrepProg (BitVec 64) :=
.seq crepBody299_38 crepBody299_39

def crepBody299_41 : CrepProg (BitVec 64) :=
.seq crepBody299_40 crepBody299_6

def crepBody299_42 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 3#64)) crepBody299_41 crepBody299_4

def crepBody299_43 : CrepProg (BitVec 64) :=
.seq crepBody299_36 crepBody299_42

def crepBody299_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_authorizations"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 272#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 280#64])]

def crepBody299_45 : CrepProg (BitVec 64) :=
.seq crepBody299_44 crepBody299_6

def crepBody299_46 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 4#64)) crepBody299_45 crepBody299_4

def crepBody299_47 : CrepProg (BitVec 64) :=
.seq crepBody299_43 crepBody299_46

def crepBody299_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody299_49 : CrepProg (BitVec 64) :=
.seq crepBody299_48 crepBody299_6

def crepBody299_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody299_51 : CrepProg (BitVec 64) :=
.seq crepBody299_49 crepBody299_50

def crepBody299_52 : CrepProg (BitVec 64) :=
.seq crepBody299_51 crepBody299_6

def crepBody299_53 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "tx_put_u256"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody299_54 : CrepProg (BitVec 64) :=
.seq crepBody299_52 crepBody299_53

def crepBody299_55 : CrepProg (BitVec 64) :=
.seq crepBody299_54 crepBody299_6

def crepBody299_56 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody299_55 crepBody299_4

def crepBody299_57 : CrepProg (BitVec 64) :=
.seq crepBody299_47 crepBody299_56

def crepBody299_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_encode_word" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 2]

def crepBody299_59 : CrepProg (BitVec 64) :=
.seq crepBody299_58 crepBody299_6

def crepBody299_60 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 128#64)

def crepBody299_61 : CrepProg (BitVec 64) :=
.seq crepBody299_59 crepBody299_60

def crepBody299_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.const 128#64)

def crepBody299_63 : CrepProg (BitVec 64) :=
.seq crepBody299_61 crepBody299_62

def crepBody299_64 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 2#64]) crepBody299_5

def crepBody299_65 : CrepProg (BitVec 64) :=
.seq crepBody299_63 crepBody299_64

def crepBody299_66 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 2#64)) crepBody299_65 crepBody299_4

def crepBody299_67 : CrepProg (BitVec 64) :=
.seq crepBody299_57 crepBody299_66

def crepBody299_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 9]

def crepBody299_69 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "rlp_encode_list_header" [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 9]

def crepBody299_70 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody299_69

def crepBody299_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 12)

def crepBody299_72 : CrepProg (BitVec 64) :=
.seq crepBody299_71 crepBody299_4

def crepBody299_73 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 1#64]) crepBody299_72

def crepBody299_74 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 7)

def crepBody299_75 : CrepProg (BitVec 64) :=
.seq crepBody299_73 crepBody299_74

def crepBody299_76 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody299_75 crepBody299_4

def crepBody299_77 : CrepProg (BitVec 64) :=
.seq crepBody299_70 crepBody299_76

def crepBody299_78 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 11]]

def crepBody299_79 : CrepProg (BitVec 64) :=
.seq crepBody299_77 crepBody299_78

def crepBody299_80 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 10]) crepBody299_79

def crepBody299_81 : CrepProg (BitVec 64) :=
.seq crepBody299_68 crepBody299_80

def crepBody299_82 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody299_81

def crepBody299_83 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]) crepBody299_82

def crepBody299_84 : CrepProg (BitVec 64) :=
.seq crepBody299_67 crepBody299_83

def crepBody299_85 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody299_84

def crepBody299_86 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody299_85

def crepBody299_87 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 5) crepBody299_86

def crepBody299_88 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 10#64]) crepBody299_87

def crepBody299_89 : CrepProg (BitVec 64) :=
.seq crepBody299_1 crepBody299_88

def crepBody299_90 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody299_89

def crepBody299_91 : CrepProg (BitVec 64) :=
.seq crepBody299_0 crepBody299_90

def crepBody299_92 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody299_91

def data299 : CrepProg (BitVec 64) := crepBody299_92
def output299 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [116#8, 120#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 103#8, 101#8, 110#8, 101#8, 114#8, 105#8, 99#8], [0, 1, 2], crepProgToHOL data299)
end InitECandidate.Proofs.FrontendStages.Crep
