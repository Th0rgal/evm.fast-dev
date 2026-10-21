import InitECandidate.Proofs.FrontendStages.Crep.Translate530
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody546_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody546_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody546_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 20#64]

def crepBody546_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 7)

def crepBody546_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody546_5 : CrepProg (BitVec 64) :=
.seq crepBody546_3 crepBody546_4

def crepBody546_6 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]) crepBody546_5

def crepBody546_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "rlp_encode_word" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1]

def crepBody546_8 : CrepProg (BitVec 64) :=
.seq crepBody546_6 crepBody546_7

def crepBody546_9 : CrepProg (BitVec 64) :=
.seq crepBody546_8 crepBody546_6

def crepBody546_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 7]

def crepBody546_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "rlp_encode_list_header"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub
      [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 9#64],
        Flapjack.CrepExp.var 8],
    Flapjack.CrepExp.var 7]

def crepBody546_12 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody546_11

def crepBody546_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody546_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "keccak256"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub
      [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 9#64],
        Flapjack.CrepExp.var 8],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8], Flapjack.CrepExp.var 9]

def crepBody546_15 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody546_14

def crepBody546_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "memcpy"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 12#64],
    Flapjack.CrepExp.const 20#64]

def crepBody546_17 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody546_16

def crepBody546_18 : CrepProg (BitVec 64) :=
.seq crepBody546_15 crepBody546_17

def crepBody546_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody546_20 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody546_19

def crepBody546_21 : CrepProg (BitVec 64) :=
.seq crepBody546_18 crepBody546_20

def crepBody546_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody546_23 : CrepProg (BitVec 64) :=
.seq crepBody546_21 crepBody546_22

def crepBody546_24 : CrepProg (BitVec 64) :=
.seq crepBody546_13 crepBody546_23

def crepBody546_25 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody546_24

def crepBody546_26 : CrepProg (BitVec 64) :=
.seq crepBody546_12 crepBody546_25

def crepBody546_27 : CrepProg (BitVec 64) :=
.seq crepBody546_10 crepBody546_26

def crepBody546_28 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody546_27

def crepBody546_29 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 9#64]]) crepBody546_28

def crepBody546_30 : CrepProg (BitVec 64) :=
.seq crepBody546_9 crepBody546_29

def crepBody546_31 : CrepProg (BitVec 64) :=
.seq crepBody546_2 crepBody546_30

def crepBody546_32 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody546_31

def crepBody546_33 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 9#64]) crepBody546_32

def crepBody546_34 : CrepProg (BitVec 64) :=
.seq crepBody546_1 crepBody546_33

def crepBody546_35 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody546_34

def crepBody546_36 : CrepProg (BitVec 64) :=
.seq crepBody546_0 crepBody546_35

def crepBody546_37 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody546_36

def data546 : CrepProg (BitVec 64) := crepBody546_37
def output546 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 111#8, 109#8, 112#8, 117#8, 116#8, 101#8, 95#8, 99#8, 111#8, 110#8, 116#8, 114#8, 97#8, 99#8, 116#8, 95#8,
    97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8], [0, 1, 2], crepProgToHOL data546)
end InitECandidate.Proofs.FrontendStages.Crep
