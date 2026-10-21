import InitECandidate.Proofs.FrontendStages.Crep.Translate506
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody522_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody522_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody522_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 1#64))]) crepBody522_0 crepBody522_1

def crepBody522_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody522_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "u256_lt"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.const 13822214165235122497#64, Flapjack.CrepExp.const 13451932020343611451#64,
    Flapjack.CrepExp.const 18446744073709551614#64, Flapjack.CrepExp.const 18446744073709551615#64]

def crepBody522_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 0#64)])) crepBody522_0 crepBody522_1

def crepBody522_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]

def crepBody522_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "u256_gt"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.const 16134479119472337056#64, Flapjack.CrepExp.const 6725966010171805725#64,
    Flapjack.CrepExp.const 18446744073709551615#64, Flapjack.CrepExp.const 9223372036854775807#64]

def crepBody522_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 0#64)])) crepBody522_0 crepBody522_1

def crepBody522_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "heap_mark" []

def crepBody522_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "alloc" [Flapjack.CrepExp.const 128#64]

def crepBody522_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "rlp_put_u256"
  [Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody522_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 16 (Flapjack.CrepExp.var 18)

def crepBody522_13 : CrepProg (BitVec 64) :=
.seq crepBody522_12 crepBody522_1

def crepBody522_14 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]) crepBody522_13

def crepBody522_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.const 20#64]

def crepBody522_16 : CrepProg (BitVec 64) :=
.seq crepBody522_14 crepBody522_15

def crepBody522_17 : CrepProg (BitVec 64) :=
.seq crepBody522_16 crepBody522_14

def crepBody522_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "rlp_encode_word"
  [Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64])]

def crepBody522_19 : CrepProg (BitVec 64) :=
.seq crepBody522_17 crepBody522_18

def crepBody522_20 : CrepProg (BitVec 64) :=
.seq crepBody522_19 crepBody522_14

def crepBody522_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 18]

def crepBody522_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "rlp_encode_list_header" [Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 18]

def crepBody522_23 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody522_22

def crepBody522_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 20, Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.const 5#64)

def crepBody522_25 : CrepProg (BitVec 64) :=
.seq crepBody522_23 crepBody522_24

def crepBody522_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody522_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "keccak256"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 20, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.var 21]

def crepBody522_28 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody522_27

def crepBody522_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody522_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "secp256k1_recover"
  [Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 22]

def crepBody522_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "heap_release" [Flapjack.CrepExp.var 14]

def crepBody522_32 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody522_31

def crepBody522_33 : CrepProg (BitVec 64) :=
.seq crepBody522_32 crepBody522_0

def crepBody522_34 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 23) (Flapjack.CrepExp.const 0#64)) crepBody522_33 crepBody522_1

def crepBody522_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "keccak256"
  [Flapjack.CrepExp.var 22, Flapjack.CrepExp.const 64#64, Flapjack.CrepExp.var 21]

def crepBody522_36 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody522_35

def crepBody522_37 : CrepProg (BitVec 64) :=
.seq crepBody522_34 crepBody522_36

def crepBody522_38 : CrepProg (BitVec 64) :=
.seq crepBody522_37 crepBody522_32

def crepBody522_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "alloc" [Flapjack.CrepExp.const 24#64]

def crepBody522_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([25], none)) "memcpy"
  [Flapjack.CrepExp.var 24,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 12#64],
    Flapjack.CrepExp.const 20#64]

def crepBody522_41 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody522_40

def crepBody522_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 24]

def crepBody522_43 : CrepProg (BitVec 64) :=
.seq crepBody522_41 crepBody522_42

def crepBody522_44 : CrepProg (BitVec 64) :=
.seq crepBody522_39 crepBody522_43

def crepBody522_45 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody522_44

def crepBody522_46 : CrepProg (BitVec 64) :=
.seq crepBody522_38 crepBody522_45

def crepBody522_47 : CrepProg (BitVec 64) :=
.seq crepBody522_30 crepBody522_46

def crepBody522_48 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody522_47

def crepBody522_49 : CrepProg (BitVec 64) :=
.seq crepBody522_29 crepBody522_48

def crepBody522_50 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody522_49

def crepBody522_51 : CrepProg (BitVec 64) :=
.seq crepBody522_28 crepBody522_50

def crepBody522_52 : CrepProg (BitVec 64) :=
.seq crepBody522_26 crepBody522_51

def crepBody522_53 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody522_52

def crepBody522_54 : CrepProg (BitVec 64) :=
.seq crepBody522_25 crepBody522_53

def crepBody522_55 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 10#64],
    Flapjack.CrepExp.var 19]) crepBody522_54

def crepBody522_56 : CrepProg (BitVec 64) :=
.seq crepBody522_21 crepBody522_55

def crepBody522_57 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody522_56

def crepBody522_58 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 10#64]]) crepBody522_57

def crepBody522_59 : CrepProg (BitVec 64) :=
.seq crepBody522_20 crepBody522_58

def crepBody522_60 : CrepProg (BitVec 64) :=
.seq crepBody522_11 crepBody522_59

def crepBody522_61 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody522_60

def crepBody522_62 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 10#64]) crepBody522_61

def crepBody522_63 : CrepProg (BitVec 64) :=
.seq crepBody522_10 crepBody522_62

def crepBody522_64 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody522_63

def crepBody522_65 : CrepProg (BitVec 64) :=
.seq crepBody522_9 crepBody522_64

def crepBody522_66 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody522_65

def crepBody522_67 : CrepProg (BitVec 64) :=
.seq crepBody522_8 crepBody522_66

def crepBody522_68 : CrepProg (BitVec 64) :=
.seq crepBody522_7 crepBody522_67

def crepBody522_69 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody522_68

def crepBody522_70 : CrepProg (BitVec 64) :=
.seq crepBody522_6 crepBody522_69

def crepBody522_71 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody522_70

def crepBody522_72 : CrepProg (BitVec 64) :=
.seq crepBody522_5 crepBody522_71

def crepBody522_73 : CrepProg (BitVec 64) :=
.seq crepBody522_4 crepBody522_72

def crepBody522_74 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody522_73

def crepBody522_75 : CrepProg (BitVec 64) :=
.seq crepBody522_3 crepBody522_74

def crepBody522_76 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody522_75

def crepBody522_77 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 88#64],
      Flapjack.CrepExp.const 24#64])) crepBody522_76

def crepBody522_78 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 88#64],
      Flapjack.CrepExp.const 16#64])) crepBody522_77

def crepBody522_79 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 88#64],
      Flapjack.CrepExp.const 8#64])) crepBody522_78

def crepBody522_80 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 88#64])) crepBody522_79

def crepBody522_81 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64],
      Flapjack.CrepExp.const 24#64])) crepBody522_80

def crepBody522_82 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64],
      Flapjack.CrepExp.const 16#64])) crepBody522_81

def crepBody522_83 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64],
      Flapjack.CrepExp.const 8#64])) crepBody522_82

def crepBody522_84 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64])) crepBody522_83

def crepBody522_85 : CrepProg (BitVec 64) :=
.seq crepBody522_2 crepBody522_84

def crepBody522_86 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64])) crepBody522_85

def data522 : CrepProg (BitVec 64) := crepBody522_86
def output522 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8, 95#8, 97#8, 117#8, 116#8, 104#8, 111#8, 114#8, 105#8, 116#8, 121#8], [0], crepProgToHOL data522)
end InitECandidate.Proofs.FrontendStages.Crep
