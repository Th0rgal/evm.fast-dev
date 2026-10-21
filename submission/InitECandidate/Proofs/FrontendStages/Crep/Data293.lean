import InitECandidate.Proofs.FrontendStages.Crep.Translate277
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody293_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "access_list_payload_len" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody293_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "rlp_encode_list_header" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]

def crepBody293_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 9]

def crepBody293_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "rlp_encode_list_header"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.const 21#64, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 9]]

def crepBody293_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 11)

def crepBody293_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody293_6 : CrepProg (BitVec 64) :=
.seq crepBody293_4 crepBody293_5

def crepBody293_7 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 4]) crepBody293_6

def crepBody293_8 : CrepProg (BitVec 64) :=
.seq crepBody293_3 crepBody293_7

def crepBody293_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 0#64]),
    Flapjack.CrepExp.const 20#64]

def crepBody293_10 : CrepProg (BitVec 64) :=
.seq crepBody293_8 crepBody293_9

def crepBody293_11 : CrepProg (BitVec 64) :=
.seq crepBody293_10 crepBody293_7

def crepBody293_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "rlp_encode_list_header" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 9]

def crepBody293_13 : CrepProg (BitVec 64) :=
.seq crepBody293_11 crepBody293_12

def crepBody293_14 : CrepProg (BitVec 64) :=
.seq crepBody293_13 crepBody293_7

def crepBody293_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 11,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 32#64]],
    Flapjack.CrepExp.const 32#64]

def crepBody293_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 13)

def crepBody293_17 : CrepProg (BitVec 64) :=
.seq crepBody293_16 crepBody293_5

def crepBody293_18 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 4]) crepBody293_17

def crepBody293_19 : CrepProg (BitVec 64) :=
.seq crepBody293_15 crepBody293_18

def crepBody293_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.var 13)

def crepBody293_21 : CrepProg (BitVec 64) :=
.seq crepBody293_20 crepBody293_5

def crepBody293_22 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 1#64]) crepBody293_21

def crepBody293_23 : CrepProg (BitVec 64) :=
.seq crepBody293_19 crepBody293_22

def crepBody293_24 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 8)) crepBody293_23

def crepBody293_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 13)

def crepBody293_26 : CrepProg (BitVec 64) :=
.seq crepBody293_25 crepBody293_5

def crepBody293_27 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64]) crepBody293_26

def crepBody293_28 : CrepProg (BitVec 64) :=
.seq crepBody293_24 crepBody293_27

def crepBody293_29 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody293_28

def crepBody293_30 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64])) crepBody293_29

def crepBody293_31 : CrepProg (BitVec 64) :=
.seq crepBody293_14 crepBody293_30

def crepBody293_32 : CrepProg (BitVec 64) :=
.seq crepBody293_2 crepBody293_31

def crepBody293_33 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody293_32

def crepBody293_34 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 33#64, Flapjack.CrepExp.var 8]) crepBody293_33

def crepBody293_35 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 16#64])) crepBody293_34

def crepBody293_36 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 24#64]]) crepBody293_35

def crepBody293_37 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 2)) crepBody293_36

def crepBody293_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 0]]

def crepBody293_39 : CrepProg (BitVec 64) :=
.seq crepBody293_37 crepBody293_38

def crepBody293_40 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody293_39

def crepBody293_41 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4]) crepBody293_40

def crepBody293_42 : CrepProg (BitVec 64) :=
.seq crepBody293_1 crepBody293_41

def crepBody293_43 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody293_42

def crepBody293_44 : CrepProg (BitVec 64) :=
.seq crepBody293_0 crepBody293_43

def crepBody293_45 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody293_44

def data293 : CrepProg (BitVec 64) := crepBody293_45
def output293 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [116#8, 120#8, 95#8, 112#8, 117#8, 116#8, 95#8, 97#8, 99#8, 99#8, 101#8, 115#8, 115#8, 95#8, 108#8, 105#8, 115#8,
    116#8], [0, 1, 2], crepProgToHOL data293)
end InitECandidate.Proofs.FrontendStages.Crep
