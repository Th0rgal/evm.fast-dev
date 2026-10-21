import InitECandidate.Proofs.FrontendStages.Crep.Translate258
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody274_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "rlp_list_to_slices" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody274_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64]]

def crepBody274_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7, 8, 9], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody274_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 10)

def crepBody274_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody274_5 : CrepProg (BitVec 64) :=
.seq crepBody274_3 crepBody274_4

def crepBody274_6 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 19#64) crepBody274_5

def crepBody274_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 6#64

def crepBody274_8 : CrepProg (BitVec 64) :=
.seq crepBody274_6 crepBody274_7

def crepBody274_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 1#64)) crepBody274_8 crepBody274_4

def crepBody274_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11], none)) "rlp_list_to_slices" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody274_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 12)

def crepBody274_12 : CrepProg (BitVec 64) :=
.seq crepBody274_11 crepBody274_4

def crepBody274_13 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 19#64) crepBody274_12

def crepBody274_14 : CrepProg (BitVec 64) :=
.seq crepBody274_13 crepBody274_7

def crepBody274_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 2#64)) crepBody274_14 crepBody274_4

def crepBody274_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "tx_fixed_bytes"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 20#64]

def crepBody274_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13, 14], none)) "tx_list_item" [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 1#64]

def crepBody274_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16], none)) "rlp_list_to_slices" [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody274_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 32#64]]

def crepBody274_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "tx_fixed_bytes"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 32#64]

def crepBody274_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 17,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 32#64]],
    Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 32#64]

def crepBody274_22 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody274_21

def crepBody274_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18 (Flapjack.CrepExp.var 20)

def crepBody274_24 : CrepProg (BitVec 64) :=
.seq crepBody274_23 crepBody274_4

def crepBody274_25 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 1#64]) crepBody274_24

def crepBody274_26 : CrepProg (BitVec 64) :=
.seq crepBody274_22 crepBody274_25

def crepBody274_27 : CrepProg (BitVec 64) :=
.seq crepBody274_20 crepBody274_26

def crepBody274_28 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody274_27

def crepBody274_29 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.var 16)) crepBody274_28

def crepBody274_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.var 21)

def crepBody274_31 : CrepProg (BitVec 64) :=
.seq crepBody274_30 crepBody274_4

def crepBody274_32 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 12) crepBody274_31

def crepBody274_33 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 0#64]) crepBody274_32

def crepBody274_34 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 17) crepBody274_31

def crepBody274_35 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 8#64]) crepBody274_34

def crepBody274_36 : CrepProg (BitVec 64) :=
.seq crepBody274_33 crepBody274_35

def crepBody274_37 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 16) crepBody274_31

def crepBody274_38 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 16#64]) crepBody274_37

def crepBody274_39 : CrepProg (BitVec 64) :=
.seq crepBody274_36 crepBody274_38

def crepBody274_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 20)

def crepBody274_41 : CrepProg (BitVec 64) :=
.seq crepBody274_40 crepBody274_4

def crepBody274_42 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody274_41

def crepBody274_43 : CrepProg (BitVec 64) :=
.seq crepBody274_39 crepBody274_42

def crepBody274_44 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 24#64]]) crepBody274_43

def crepBody274_45 : CrepProg (BitVec 64) :=
.seq crepBody274_29 crepBody274_44

def crepBody274_46 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody274_45

def crepBody274_47 : CrepProg (BitVec 64) :=
.seq crepBody274_19 crepBody274_46

def crepBody274_48 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody274_47

def crepBody274_49 : CrepProg (BitVec 64) :=
.seq crepBody274_18 crepBody274_48

def crepBody274_50 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody274_49

def crepBody274_51 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody274_50

def crepBody274_52 : CrepProg (BitVec 64) :=
.seq crepBody274_17 crepBody274_51

def crepBody274_53 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody274_52

def crepBody274_54 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody274_53

def crepBody274_55 : CrepProg (BitVec 64) :=
.seq crepBody274_16 crepBody274_54

def crepBody274_56 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody274_55

def crepBody274_57 : CrepProg (BitVec 64) :=
.seq crepBody274_15 crepBody274_56

def crepBody274_58 : CrepProg (BitVec 64) :=
.seq crepBody274_10 crepBody274_57

def crepBody274_59 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody274_58

def crepBody274_60 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody274_59

def crepBody274_61 : CrepProg (BitVec 64) :=
.seq crepBody274_9 crepBody274_60

def crepBody274_62 : CrepProg (BitVec 64) :=
.seq crepBody274_2 crepBody274_61

def crepBody274_63 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody274_62

def crepBody274_64 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody274_63

def crepBody274_65 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody274_64

def crepBody274_66 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody274_65

def crepBody274_67 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 3)) crepBody274_66

def crepBody274_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 3]

def crepBody274_69 : CrepProg (BitVec 64) :=
.seq crepBody274_67 crepBody274_68

def crepBody274_70 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody274_69

def crepBody274_71 : CrepProg (BitVec 64) :=
.seq crepBody274_1 crepBody274_70

def crepBody274_72 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody274_71

def crepBody274_73 : CrepProg (BitVec 64) :=
.seq crepBody274_0 crepBody274_72

def crepBody274_74 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody274_73

def crepBody274_75 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody274_74

def data274 : CrepProg (BitVec 64) := crepBody274_75
def output274 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 97#8, 99#8, 99#8, 101#8, 115#8, 115#8, 95#8, 108#8, 105#8, 115#8,
    116#8], [0, 1], crepProgToHOL data274)
end InitECandidate.Proofs.FrontendStages.Crep
