import InitECandidate.Proofs.FrontendStages.Crep.Translate609
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody625_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_mark" []

def crepBody625_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 1152#64]

def crepBody625_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 1152#64]

def crepBody625_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc" [Flapjack.CrepExp.const 1152#64]

def crepBody625_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "alloc" [Flapjack.CrepExp.const 1152#64]

def crepBody625_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 384#64]

def crepBody625_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "alloc" [Flapjack.CrepExp.const 384#64]

def crepBody625_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "memcpy"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1152#64]

def crepBody625_8 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody625_7

def crepBody625_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "memcpy"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1152#64]

def crepBody625_10 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody625_9

def crepBody625_11 : CrepProg (BitVec 64) :=
.seq crepBody625_8 crepBody625_10

def crepBody625_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "fe_neg"
  [Flapjack.CrepExp.const 12#64,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 384#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 384#64]]

def crepBody625_13 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody625_12

def crepBody625_14 : CrepProg (BitVec 64) :=
.seq crepBody625_11 crepBody625_13

def crepBody625_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "fe_set_one" [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 0]

def crepBody625_16 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody625_15

def crepBody625_17 : CrepProg (BitVec 64) :=
.seq crepBody625_14 crepBody625_16

def crepBody625_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "fe_set_one" [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 1]

def crepBody625_19 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody625_18

def crepBody625_20 : CrepProg (BitVec 64) :=
.seq crepBody625_17 crepBody625_19

def crepBody625_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 12)

def crepBody625_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody625_23 : CrepProg (BitVec 64) :=
.seq crepBody625_21 crepBody625_22

def crepBody625_24 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 1#64]) crepBody625_23

def crepBody625_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "ecp_linefunc"
  [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 3]

def crepBody625_26 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_25

def crepBody625_27 : CrepProg (BitVec 64) :=
.seq crepBody625_24 crepBody625_26

def crepBody625_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fq12_sqr" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 0]

def crepBody625_29 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_28

def crepBody625_30 : CrepProg (BitVec 64) :=
.seq crepBody625_27 crepBody625_29

def crepBody625_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fq12_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 9]

def crepBody625_32 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_31

def crepBody625_33 : CrepProg (BitVec 64) :=
.seq crepBody625_30 crepBody625_32

def crepBody625_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fq12_sqr" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 1]

def crepBody625_35 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_34

def crepBody625_36 : CrepProg (BitVec 64) :=
.seq crepBody625_33 crepBody625_35

def crepBody625_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fq12_mul"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 10]

def crepBody625_38 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_37

def crepBody625_39 : CrepProg (BitVec 64) :=
.seq crepBody625_36 crepBody625_38

def crepBody625_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "ecp_double"
  [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5]

def crepBody625_41 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_40

def crepBody625_42 : CrepProg (BitVec 64) :=
.seq crepBody625_39 crepBody625_41

def crepBody625_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "ecp_linefunc"
  [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody625_44 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_43

def crepBody625_45 : CrepProg (BitVec 64) :=
.seq crepBody625_44 crepBody625_32

def crepBody625_46 : CrepProg (BitVec 64) :=
.seq crepBody625_45 crepBody625_38

def crepBody625_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "ecp_add"
  [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 2]

def crepBody625_48 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_47

def crepBody625_49 : CrepProg (BitVec 64) :=
.seq crepBody625_46 crepBody625_48

def crepBody625_50 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.and
    [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.const 11637723931993326632#64)
        (Flapjack.CrepExp.var 11),
      Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.const 1#64)) crepBody625_49 crepBody625_22

def crepBody625_51 : CrepProg (BitVec 64) :=
.seq crepBody625_42 crepBody625_50

def crepBody625_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "ecp_linefunc"
  [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 3]

def crepBody625_53 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_52

def crepBody625_54 : CrepProg (BitVec 64) :=
.seq crepBody625_53 crepBody625_32

def crepBody625_55 : CrepProg (BitVec 64) :=
.seq crepBody625_54 crepBody625_38

def crepBody625_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "ecp_add"
  [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody625_57 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_56

def crepBody625_58 : CrepProg (BitVec 64) :=
.seq crepBody625_55 crepBody625_57

def crepBody625_59 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.and
    [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.const 290499802545784960#64) (Flapjack.CrepExp.var 11),
      Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.const 1#64)) crepBody625_58 crepBody625_22

def crepBody625_60 : CrepProg (BitVec 64) :=
.seq crepBody625_51 crepBody625_59

def crepBody625_61 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 11)) crepBody625_60

def crepBody625_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fq12_frob" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 2]

def crepBody625_63 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_62

def crepBody625_64 : CrepProg (BitVec 64) :=
.seq crepBody625_61 crepBody625_63

def crepBody625_65 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fq12_frob"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 384#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 384#64]]

def crepBody625_66 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_65

def crepBody625_67 : CrepProg (BitVec 64) :=
.seq crepBody625_64 crepBody625_66

def crepBody625_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fq12_frob"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 7,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 384#64]],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 2,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 384#64]]]

def crepBody625_69 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_68

def crepBody625_70 : CrepProg (BitVec 64) :=
.seq crepBody625_67 crepBody625_69

def crepBody625_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fq12_frob" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 7]

def crepBody625_72 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_71

def crepBody625_73 : CrepProg (BitVec 64) :=
.seq crepBody625_70 crepBody625_72

def crepBody625_74 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fq12_frob"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 384#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 384#64]]

def crepBody625_75 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_74

def crepBody625_76 : CrepProg (BitVec 64) :=
.seq crepBody625_73 crepBody625_75

def crepBody625_77 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fe_neg"
  [Flapjack.CrepExp.const 12#64,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 384#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 384#64]]

def crepBody625_78 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_77

def crepBody625_79 : CrepProg (BitVec 64) :=
.seq crepBody625_76 crepBody625_78

def crepBody625_80 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fq12_frob"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 8,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 384#64]],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 7,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 384#64]]]

def crepBody625_81 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_80

def crepBody625_82 : CrepProg (BitVec 64) :=
.seq crepBody625_79 crepBody625_81

def crepBody625_83 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "ecp_linefunc"
  [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 3]

def crepBody625_84 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_83

def crepBody625_85 : CrepProg (BitVec 64) :=
.seq crepBody625_82 crepBody625_84

def crepBody625_86 : CrepProg (BitVec 64) :=
.seq crepBody625_85 crepBody625_32

def crepBody625_87 : CrepProg (BitVec 64) :=
.seq crepBody625_86 crepBody625_38

def crepBody625_88 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "ecp_add"
  [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 7]

def crepBody625_89 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_88

def crepBody625_90 : CrepProg (BitVec 64) :=
.seq crepBody625_87 crepBody625_89

def crepBody625_91 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "ecp_linefunc"
  [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 3]

def crepBody625_92 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_91

def crepBody625_93 : CrepProg (BitVec 64) :=
.seq crepBody625_90 crepBody625_92

def crepBody625_94 : CrepProg (BitVec 64) :=
.seq crepBody625_93 crepBody625_32

def crepBody625_95 : CrepProg (BitVec 64) :=
.seq crepBody625_94 crepBody625_38

def crepBody625_96 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "heap_release" [Flapjack.CrepExp.var 4]

def crepBody625_97 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody625_96

def crepBody625_98 : CrepProg (BitVec 64) :=
.seq crepBody625_95 crepBody625_97

def crepBody625_99 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody625_100 : CrepProg (BitVec 64) :=
.seq crepBody625_98 crepBody625_99

def crepBody625_101 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 64#64) crepBody625_100

def crepBody625_102 : CrepProg (BitVec 64) :=
.seq crepBody625_20 crepBody625_101

def crepBody625_103 : CrepProg (BitVec 64) :=
.seq crepBody625_6 crepBody625_102

def crepBody625_104 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody625_103

def crepBody625_105 : CrepProg (BitVec 64) :=
.seq crepBody625_5 crepBody625_104

def crepBody625_106 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody625_105

def crepBody625_107 : CrepProg (BitVec 64) :=
.seq crepBody625_4 crepBody625_106

def crepBody625_108 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody625_107

def crepBody625_109 : CrepProg (BitVec 64) :=
.seq crepBody625_3 crepBody625_108

def crepBody625_110 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody625_109

def crepBody625_111 : CrepProg (BitVec 64) :=
.seq crepBody625_2 crepBody625_110

def crepBody625_112 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody625_111

def crepBody625_113 : CrepProg (BitVec 64) :=
.seq crepBody625_1 crepBody625_112

def crepBody625_114 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody625_113

def crepBody625_115 : CrepProg (BitVec 64) :=
.seq crepBody625_0 crepBody625_114

def crepBody625_116 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody625_115

def data625 : CrepProg (BitVec 64) := crepBody625_116
def output625 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 110#8, 50#8, 53#8, 52#8, 95#8, 109#8, 105#8, 108#8, 108#8, 101#8, 114#8, 95#8, 114#8, 97#8, 119#8], [0, 1, 2, 3], crepProgToHOL data625)
end InitECandidate.Proofs.FrontendStages.Crep
