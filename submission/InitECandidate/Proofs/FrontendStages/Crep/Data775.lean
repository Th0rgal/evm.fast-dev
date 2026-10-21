import InitECandidate.Proofs.FrontendStages.Crep.Translate759
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody775_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "logs_encoded_bound" [Flapjack.CrepExp.var 3]

def crepBody775_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 400#64]]

def crepBody775_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 1#64)

def crepBody775_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.const 1#64)

def crepBody775_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody775_5 : CrepProg (BitVec 64) :=
.seq crepBody775_3 crepBody775_4

def crepBody775_6 : CrepProg (BitVec 64) :=
.seq crepBody775_2 crepBody775_5

def crepBody775_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 128#64)

def crepBody775_8 : CrepProg (BitVec 64) :=
.seq crepBody775_7 crepBody775_5

def crepBody775_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody775_6 crepBody775_8

def crepBody775_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 9)

def crepBody775_11 : CrepProg (BitVec 64) :=
.seq crepBody775_10 crepBody775_4

def crepBody775_12 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]) crepBody775_11

def crepBody775_13 : CrepProg (BitVec 64) :=
.seq crepBody775_9 crepBody775_12

def crepBody775_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_encode_word" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 2]

def crepBody775_15 : CrepProg (BitVec 64) :=
.seq crepBody775_13 crepBody775_14

def crepBody775_16 : CrepProg (BitVec 64) :=
.seq crepBody775_15 crepBody775_12

def crepBody775_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 256#64]

def crepBody775_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "logs_bloom" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 9]

def crepBody775_19 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody775_18

def crepBody775_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 256#64]

def crepBody775_21 : CrepProg (BitVec 64) :=
.seq crepBody775_19 crepBody775_20

def crepBody775_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 10)

def crepBody775_23 : CrepProg (BitVec 64) :=
.seq crepBody775_22 crepBody775_4

def crepBody775_24 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]) crepBody775_23

def crepBody775_25 : CrepProg (BitVec 64) :=
.seq crepBody775_21 crepBody775_24

def crepBody775_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "encode_logs" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 3]

def crepBody775_27 : CrepProg (BitVec 64) :=
.seq crepBody775_25 crepBody775_26

def crepBody775_28 : CrepProg (BitVec 64) :=
.seq crepBody775_27 crepBody775_24

def crepBody775_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_finish_list" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody775_30 : CrepProg (BitVec 64) :=
.seq crepBody775_28 crepBody775_29

def crepBody775_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.var 0)

def crepBody775_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64]]

def crepBody775_33 : CrepProg (BitVec 64) :=
.seq crepBody775_31 crepBody775_32

def crepBody775_34 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 0#64)) crepBody775_33 crepBody775_4

def crepBody775_35 : CrepProg (BitVec 64) :=
.seq crepBody775_30 crepBody775_34

def crepBody775_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 8]

def crepBody775_37 : CrepProg (BitVec 64) :=
.seq crepBody775_35 crepBody775_36

def crepBody775_38 : CrepProg (BitVec 64) :=
.seq crepBody775_17 crepBody775_37

def crepBody775_39 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody775_38

def crepBody775_40 : CrepProg (BitVec 64) :=
.seq crepBody775_16 crepBody775_39

def crepBody775_41 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody775_40

def crepBody775_42 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 9#64]) crepBody775_41

def crepBody775_43 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody775_42

def crepBody775_44 : CrepProg (BitVec 64) :=
.seq crepBody775_1 crepBody775_43

def crepBody775_45 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody775_44

def crepBody775_46 : CrepProg (BitVec 64) :=
.seq crepBody775_0 crepBody775_45

def crepBody775_47 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody775_46

def data775 : CrepProg (BitVec 64) := crepBody775_47
def output775 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 114#8, 101#8, 99#8, 101#8, 105#8, 112#8, 116#8], [0, 1, 2, 3], crepProgToHOL data775)
end InitECandidate.Proofs.FrontendStages.Crep
