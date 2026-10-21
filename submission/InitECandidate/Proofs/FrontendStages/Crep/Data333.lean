import InitECandidate.Proofs.FrontendStages.Crep.Translate317
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody333_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "ws_storage_root_of" [Flapjack.CrepExp.var 0]

def crepBody333_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "memeq"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 128#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody333_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody333_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody333_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody333_2 crepBody333_3

def crepBody333_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "ws_storage_trie" [Flapjack.CrepExp.var 2]

def crepBody333_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_mark" []

def crepBody333_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody333_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "keccak256"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 6]

def crepBody333_9 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody333_8

def crepBody333_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7, 8, 9], none)) "trie_lookup" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 6]

def crepBody333_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "heap_release" [Flapjack.CrepExp.var 5]

def crepBody333_12 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody333_11

def crepBody333_13 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody333_2 crepBody333_3

def crepBody333_14 : CrepProg (BitVec 64) :=
.seq crepBody333_12 crepBody333_13

def crepBody333_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11, 12, 13], none)) "rlp_decode_fully"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]

def crepBody333_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 1#64)) crepBody333_2 crepBody333_3

def crepBody333_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 14)

def crepBody333_18 : CrepProg (BitVec 64) :=
.seq crepBody333_17 crepBody333_3

def crepBody333_19 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 1#64) crepBody333_18

def crepBody333_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 7#64

def crepBody333_21 : CrepProg (BitVec 64) :=
.seq crepBody333_19 crepBody333_20

def crepBody333_22 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 32#64) (Flapjack.CrepExp.var 12)) crepBody333_21 crepBody333_3

def crepBody333_23 : CrepProg (BitVec 64) :=
.seq crepBody333_16 crepBody333_22

def crepBody333_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15, 16, 17], none)) "u256_from_be" [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody333_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody333_26 : CrepProg (BitVec 64) :=
.seq crepBody333_24 crepBody333_25

def crepBody333_27 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody333_26

def crepBody333_28 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody333_27

def crepBody333_29 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody333_28

def crepBody333_30 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody333_29

def crepBody333_31 : CrepProg (BitVec 64) :=
.seq crepBody333_23 crepBody333_30

def crepBody333_32 : CrepProg (BitVec 64) :=
.seq crepBody333_15 crepBody333_31

def crepBody333_33 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody333_32

def crepBody333_34 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody333_33

def crepBody333_35 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody333_34

def crepBody333_36 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody333_35

def crepBody333_37 : CrepProg (BitVec 64) :=
.seq crepBody333_14 crepBody333_36

def crepBody333_38 : CrepProg (BitVec 64) :=
.seq crepBody333_10 crepBody333_37

def crepBody333_39 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody333_38

def crepBody333_40 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody333_39

def crepBody333_41 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody333_40

def crepBody333_42 : CrepProg (BitVec 64) :=
.seq crepBody333_9 crepBody333_41

def crepBody333_43 : CrepProg (BitVec 64) :=
.seq crepBody333_7 crepBody333_42

def crepBody333_44 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody333_43

def crepBody333_45 : CrepProg (BitVec 64) :=
.seq crepBody333_6 crepBody333_44

def crepBody333_46 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody333_45

def crepBody333_47 : CrepProg (BitVec 64) :=
.seq crepBody333_5 crepBody333_46

def crepBody333_48 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody333_47

def crepBody333_49 : CrepProg (BitVec 64) :=
.seq crepBody333_4 crepBody333_48

def crepBody333_50 : CrepProg (BitVec 64) :=
.seq crepBody333_1 crepBody333_49

def crepBody333_51 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody333_50

def crepBody333_52 : CrepProg (BitVec 64) :=
.seq crepBody333_0 crepBody333_51

def crepBody333_53 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody333_52

def data333 : CrepProg (BitVec 64) := crepBody333_53
def output333 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [119#8, 115#8, 95#8, 103#8, 101#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8], [0, 1], crepProgToHOL data333)
end InitECandidate.Proofs.FrontendStages.Crep
