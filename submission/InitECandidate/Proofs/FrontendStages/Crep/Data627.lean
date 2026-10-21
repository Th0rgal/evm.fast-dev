import InitECandidate.Proofs.FrontendStages.Crep.Translate611
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody627_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3, 4, 5], none)) "u256_from_be" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]

def crepBody627_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7, 8, 9], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.const 32#64]

def crepBody627_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "u256_lt"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.const 4332616871279656263#64, Flapjack.CrepExp.const 10917124144477883021#64,
    Flapjack.CrepExp.const 13281191951274694749#64, Flapjack.CrepExp.const 3486998266802970665#64]

def crepBody627_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody627_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody627_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody627_3 crepBody627_4

def crepBody627_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "u256_lt"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.const 4332616871279656263#64, Flapjack.CrepExp.const 10917124144477883021#64,
    Flapjack.CrepExp.const 13281191951274694749#64, Flapjack.CrepExp.const 3486998266802970665#64]

def crepBody627_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 0#64)) crepBody627_3 crepBody627_4

def crepBody627_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody627_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]

def crepBody627_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "ecp_set_inf" [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 1]

def crepBody627_11 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody627_10

def crepBody627_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody627_13 : CrepProg (BitVec 64) :=
.seq crepBody627_11 crepBody627_12

def crepBody627_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13])
  (Flapjack.CrepExp.const 1#64)) crepBody627_13 crepBody627_4

def crepBody627_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3, 4, 5], none)) "fq_to_mont"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody627_16 : CrepProg (BitVec 64) :=
.seq crepBody627_14 crepBody627_15

def crepBody627_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7, 8, 9], none)) "fq_to_mont"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]

def crepBody627_18 : CrepProg (BitVec 64) :=
.seq crepBody627_16 crepBody627_17

def crepBody627_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15, 16, 17], none)) "fq_mul"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]

def crepBody627_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18, 19, 20, 21], none)) "fq_mul"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody627_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18, 19, 20, 21], none)) "fq_mul"
  [Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21,
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody627_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18, 19, 20, 21], none)) "fq_add"
  [Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21,
    Flapjack.CrepExp.const 8797723225643362519#64, Flapjack.CrepExp.const 2263834496217719225#64,
    Flapjack.CrepExp.const 3696305541684646532#64, Flapjack.CrepExp.const 3035258219084094862#64]

def crepBody627_23 : CrepProg (BitVec 64) :=
.seq crepBody627_21 crepBody627_22

def crepBody627_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "u256_eq"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17,
    Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21]

def crepBody627_25 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 22) (Flapjack.CrepExp.const 0#64)) crepBody627_3 crepBody627_4

def crepBody627_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 23) (Flapjack.CrepExp.var 24)

def crepBody627_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 23, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 25)

def crepBody627_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 23, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 26)

def crepBody627_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 23, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 27)

def crepBody627_30 : CrepProg (BitVec 64) :=
.seq crepBody627_29 crepBody627_4

def crepBody627_31 : CrepProg (BitVec 64) :=
.seq crepBody627_28 crepBody627_30

def crepBody627_32 : CrepProg (BitVec 64) :=
.seq crepBody627_27 crepBody627_31

def crepBody627_33 : CrepProg (BitVec 64) :=
.seq crepBody627_26 crepBody627_32

def crepBody627_34 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.var 5) crepBody627_33

def crepBody627_35 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.var 4) crepBody627_34

def crepBody627_36 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.var 3) crepBody627_35

def crepBody627_37 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 2) crepBody627_36

def crepBody627_38 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.var 1) crepBody627_37

def crepBody627_39 : CrepProg (BitVec 64) :=
.seq crepBody627_25 crepBody627_38

def crepBody627_40 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.var 9) crepBody627_33

def crepBody627_41 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.var 8) crepBody627_40

def crepBody627_42 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.var 7) crepBody627_41

def crepBody627_43 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 6) crepBody627_42

def crepBody627_44 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]) crepBody627_43

def crepBody627_45 : CrepProg (BitVec 64) :=
.seq crepBody627_39 crepBody627_44

def crepBody627_46 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 1011752739694698287#64) crepBody627_33

def crepBody627_47 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 7381016538464732716#64) crepBody627_46

def crepBody627_48 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 754611498739239741#64) crepBody627_47

def crepBody627_49 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 15230403791020821917#64) crepBody627_48

def crepBody627_50 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 64#64]) crepBody627_49

def crepBody627_51 : CrepProg (BitVec 64) :=
.seq crepBody627_45 crepBody627_50

def crepBody627_52 : CrepProg (BitVec 64) :=
.seq crepBody627_51 crepBody627_12

def crepBody627_53 : CrepProg (BitVec 64) :=
.seq crepBody627_24 crepBody627_52

def crepBody627_54 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody627_53

def crepBody627_55 : CrepProg (BitVec 64) :=
.seq crepBody627_23 crepBody627_54

def crepBody627_56 : CrepProg (BitVec 64) :=
.seq crepBody627_20 crepBody627_55

def crepBody627_57 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody627_56

def crepBody627_58 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody627_57

def crepBody627_59 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody627_58

def crepBody627_60 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody627_59

def crepBody627_61 : CrepProg (BitVec 64) :=
.seq crepBody627_19 crepBody627_60

def crepBody627_62 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody627_61

def crepBody627_63 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody627_62

def crepBody627_64 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody627_63

def crepBody627_65 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody627_64

def crepBody627_66 : CrepProg (BitVec 64) :=
.seq crepBody627_18 crepBody627_65

def crepBody627_67 : CrepProg (BitVec 64) :=
.seq crepBody627_9 crepBody627_66

def crepBody627_68 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody627_67

def crepBody627_69 : CrepProg (BitVec 64) :=
.seq crepBody627_8 crepBody627_68

def crepBody627_70 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody627_69

def crepBody627_71 : CrepProg (BitVec 64) :=
.seq crepBody627_7 crepBody627_70

def crepBody627_72 : CrepProg (BitVec 64) :=
.seq crepBody627_6 crepBody627_71

def crepBody627_73 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody627_72

def crepBody627_74 : CrepProg (BitVec 64) :=
.seq crepBody627_5 crepBody627_73

def crepBody627_75 : CrepProg (BitVec 64) :=
.seq crepBody627_2 crepBody627_74

def crepBody627_76 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody627_75

def crepBody627_77 : CrepProg (BitVec 64) :=
.seq crepBody627_1 crepBody627_76

def crepBody627_78 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody627_77

def crepBody627_79 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody627_78

def crepBody627_80 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody627_79

def crepBody627_81 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody627_80

def crepBody627_82 : CrepProg (BitVec 64) :=
.seq crepBody627_0 crepBody627_81

def crepBody627_83 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody627_82

def crepBody627_84 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody627_83

def crepBody627_85 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody627_84

def crepBody627_86 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody627_85

def data627 : CrepProg (BitVec 64) := crepBody627_86
def output627 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 110#8, 50#8, 53#8, 52#8, 95#8, 112#8, 97#8, 114#8, 115#8, 101#8, 95#8, 103#8, 49#8], [0, 1], crepProgToHOL data627)
end InitECandidate.Proofs.FrontendStages.Crep
