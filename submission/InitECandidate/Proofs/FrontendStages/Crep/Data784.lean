import InitECandidate.Proofs.FrontendStages.Crep.Translate768
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody784_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody784_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody784_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody784_3 : CrepProg (BitVec 64) :=
.seq crepBody784_1 crepBody784_2

def crepBody784_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.var 1) crepBody784_3

def crepBody784_5 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 432#64]) crepBody784_4

def crepBody784_6 : CrepProg (BitVec 64) :=
.seq crepBody784_0 crepBody784_5

def crepBody784_7 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody784_6

def crepBody784_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "memzero"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 432#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody784_9 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody784_8

def crepBody784_10 : CrepProg (BitVec 64) :=
.seq crepBody784_7 crepBody784_9

def crepBody784_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 18#64, Flapjack.CrepExp.const 20#64]]

def crepBody784_12 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 424#64]) crepBody784_4

def crepBody784_13 : CrepProg (BitVec 64) :=
.seq crepBody784_11 crepBody784_12

def crepBody784_14 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody784_13

def crepBody784_15 : CrepProg (BitVec 64) :=
.seq crepBody784_10 crepBody784_14

def crepBody784_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "memzero"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 424#64]),
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 18#64, Flapjack.CrepExp.const 20#64]]

def crepBody784_17 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody784_16

def crepBody784_18 : CrepProg (BitVec 64) :=
.seq crepBody784_15 crepBody784_17

def crepBody784_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 424#64]),
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 20#64],
      Flapjack.CrepExp.const 19#64])
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64])

def crepBody784_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 1 (Flapjack.CrepExp.var 2)

def crepBody784_21 : CrepProg (BitVec 64) :=
.seq crepBody784_20 crepBody784_2

def crepBody784_22 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64]) crepBody784_21

def crepBody784_23 : CrepProg (BitVec 64) :=
.seq crepBody784_19 crepBody784_22

def crepBody784_24 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 17#64)) crepBody784_23

def crepBody784_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 424#64]),
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 17#64, Flapjack.CrepExp.const 20#64],
      Flapjack.CrepExp.const 18#64])
  (Flapjack.CrepExp.const 1#64)

def crepBody784_26 : CrepProg (BitVec 64) :=
.seq crepBody784_24 crepBody784_25

def crepBody784_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 24#64]

def crepBody784_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody784_29 : CrepProg (BitVec 64) :=
.seq crepBody784_28 crepBody784_2

def crepBody784_30 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 2) crepBody784_29

def crepBody784_31 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 464#64]) crepBody784_30

def crepBody784_32 : CrepProg (BitVec 64) :=
.seq crepBody784_27 crepBody784_31

def crepBody784_33 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_32

def crepBody784_34 : CrepProg (BitVec 64) :=
.seq crepBody784_26 crepBody784_33

def crepBody784_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "addr_from_words"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 464#64]),
    Flapjack.CrepExp.const 998902#64, Flapjack.CrepExp.const 15506597749690834871#64,
    Flapjack.CrepExp.const 13311379508201171970#64]

def crepBody784_36 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_35

def crepBody784_37 : CrepProg (BitVec 64) :=
.seq crepBody784_34 crepBody784_36

def crepBody784_38 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 472#64]) crepBody784_30

def crepBody784_39 : CrepProg (BitVec 64) :=
.seq crepBody784_27 crepBody784_38

def crepBody784_40 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_39

def crepBody784_41 : CrepProg (BitVec 64) :=
.seq crepBody784_37 crepBody784_40

def crepBody784_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "addr_from_words"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 472#64]),
    Flapjack.CrepExp.const 63752#64, Flapjack.CrepExp.const 2878298490047003138#64,
    Flapjack.CrepExp.const 3700577164601600309#64]

def crepBody784_43 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_42

def crepBody784_44 : CrepProg (BitVec 64) :=
.seq crepBody784_41 crepBody784_43

def crepBody784_45 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 480#64]) crepBody784_30

def crepBody784_46 : CrepProg (BitVec 64) :=
.seq crepBody784_27 crepBody784_45

def crepBody784_47 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_46

def crepBody784_48 : CrepProg (BitVec 64) :=
.seq crepBody784_44 crepBody784_47

def crepBody784_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "addr_from_words"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 480#64]),
    Flapjack.CrepExp.const 2401#64, Flapjack.CrepExp.const 17242047345525313946#64,
    Flapjack.CrepExp.const 15579492241104728066#64]

def crepBody784_50 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_49

def crepBody784_51 : CrepProg (BitVec 64) :=
.seq crepBody784_48 crepBody784_50

def crepBody784_52 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 488#64]) crepBody784_30

def crepBody784_53 : CrepProg (BitVec 64) :=
.seq crepBody784_27 crepBody784_52

def crepBody784_54 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_53

def crepBody784_55 : CrepProg (BitVec 64) :=
.seq crepBody784_51 crepBody784_54

def crepBody784_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "addr_from_words"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 488#64]),
    Flapjack.CrepExp.const 48093#64, Flapjack.CrepExp.const 14397524800236640159#64,
    Flapjack.CrepExp.const 10016273463683084881#64]

def crepBody784_57 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_56

def crepBody784_58 : CrepProg (BitVec 64) :=
.seq crepBody784_55 crepBody784_57

def crepBody784_59 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 496#64]) crepBody784_30

def crepBody784_60 : CrepProg (BitVec 64) :=
.seq crepBody784_27 crepBody784_59

def crepBody784_61 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_60

def crepBody784_62 : CrepProg (BitVec 64) :=
.seq crepBody784_58 crepBody784_61

def crepBody784_63 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "addr_from_words"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 496#64]),
    Flapjack.CrepExp.const 49140#64, Flapjack.CrepExp.const 7603452151126424148#64,
    Flapjack.CrepExp.const 760111669195932290#64]

def crepBody784_64 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_63

def crepBody784_65 : CrepProg (BitVec 64) :=
.seq crepBody784_62 crepBody784_64

def crepBody784_66 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 504#64]) crepBody784_30

def crepBody784_67 : CrepProg (BitVec 64) :=
.seq crepBody784_27 crepBody784_66

def crepBody784_68 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_67

def crepBody784_69 : CrepProg (BitVec 64) :=
.seq crepBody784_65 crepBody784_68

def crepBody784_70 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "addr_from_words"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 504#64]),
    Flapjack.CrepExp.const 25814#64, Flapjack.CrepExp.const 8669529151676140297#64,
    Flapjack.CrepExp.const 4307224735379260034#64]

def crepBody784_71 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_70

def crepBody784_72 : CrepProg (BitVec 64) :=
.seq crepBody784_69 crepBody784_71

def crepBody784_73 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 512#64]) crepBody784_30

def crepBody784_74 : CrepProg (BitVec 64) :=
.seq crepBody784_27 crepBody784_73

def crepBody784_75 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_74

def crepBody784_76 : CrepProg (BitVec 64) :=
.seq crepBody784_72 crepBody784_75

def crepBody784_77 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "addr_from_words"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 512#64]),
    Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 2421447037043915651#64,
    Flapjack.CrepExp.const 11294470620239562234#64]

def crepBody784_78 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_77

def crepBody784_79 : CrepProg (BitVec 64) :=
.seq crepBody784_76 crepBody784_78

def crepBody784_80 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody784_81 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 520#64]) crepBody784_30

def crepBody784_82 : CrepProg (BitVec 64) :=
.seq crepBody784_80 crepBody784_81

def crepBody784_83 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_82

def crepBody784_84 : CrepProg (BitVec 64) :=
.seq crepBody784_79 crepBody784_83

def crepBody784_85 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 520#64]),
        Flapjack.CrepExp.const 0#64],
    Flapjack.CrepExp.const 7249595157780304706#64]

def crepBody784_86 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_85

def crepBody784_87 : CrepProg (BitVec 64) :=
.seq crepBody784_84 crepBody784_86

def crepBody784_88 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 520#64]),
        Flapjack.CrepExp.const 8#64],
    Flapjack.CrepExp.const 12676030261858484297#64]

def crepBody784_89 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_88

def crepBody784_90 : CrepProg (BitVec 64) :=
.seq crepBody784_87 crepBody784_89

def crepBody784_91 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 520#64]),
        Flapjack.CrepExp.const 16#64],
    Flapjack.CrepExp.const 16708898399860066458#64]

def crepBody784_92 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_91

def crepBody784_93 : CrepProg (BitVec 64) :=
.seq crepBody784_90 crepBody784_92

def crepBody784_94 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 520#64]),
        Flapjack.CrepExp.const 24#64],
    Flapjack.CrepExp.const 12074291595689605317#64]

def crepBody784_95 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody784_94

def crepBody784_96 : CrepProg (BitVec 64) :=
.seq crepBody784_93 crepBody784_95

def crepBody784_97 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody784_98 : CrepProg (BitVec 64) :=
.seq crepBody784_96 crepBody784_97

def crepBody784_99 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody784_98

def crepBody784_100 : CrepProg (BitVec 64) :=
.seq crepBody784_18 crepBody784_99

def data784 : CrepProg (BitVec 64) := crepBody784_100
def output784 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 111#8, 114#8, 107#8, 95#8, 105#8, 110#8, 105#8, 116#8], [], crepProgToHOL data784)
end InitECandidate.Proofs.FrontendStages.Crep
