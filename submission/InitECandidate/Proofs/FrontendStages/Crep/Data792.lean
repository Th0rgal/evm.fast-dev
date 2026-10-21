import InitECandidate.Proofs.FrontendStages.Crep.Translate776
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody792_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "state_fresh_tx" []

def crepBody792_1 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody792_0

def crepBody792_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "ext_code_of" [Flapjack.CrepExp.var 0]

def crepBody792_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "te_new" []

def crepBody792_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody792_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody792_6 : CrepProg (BitVec 64) :=
.seq crepBody792_4 crepBody792_5

def crepBody792_7 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 304#64])) crepBody792_6

def crepBody792_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 0#64]) crepBody792_7

def crepBody792_9 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 0) crepBody792_6

def crepBody792_10 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]) crepBody792_9

def crepBody792_11 : CrepProg (BitVec 64) :=
.seq crepBody792_8 crepBody792_10

def crepBody792_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 8)

def crepBody792_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 9)

def crepBody792_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 10)

def crepBody792_15 : CrepProg (BitVec 64) :=
.seq crepBody792_14 crepBody792_5

def crepBody792_16 : CrepProg (BitVec 64) :=
.seq crepBody792_13 crepBody792_15

def crepBody792_17 : CrepProg (BitVec 64) :=
.seq crepBody792_12 crepBody792_16

def crepBody792_18 : CrepProg (BitVec 64) :=
.seq crepBody792_4 crepBody792_17

def crepBody792_19 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
          Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 24#64])) crepBody792_18

def crepBody792_20 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
          Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 16#64])) crepBody792_19

def crepBody792_21 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
          Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 8#64])) crepBody792_20

def crepBody792_22 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
      Flapjack.CrepExp.const 48#64])) crepBody792_21

def crepBody792_23 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 48#64]) crepBody792_22

def crepBody792_24 : CrepProg (BitVec 64) :=
.seq crepBody792_11 crepBody792_23

def crepBody792_25 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 30000000#64) crepBody792_6

def crepBody792_26 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 80#64]) crepBody792_25

def crepBody792_27 : CrepProg (BitVec 64) :=
.seq crepBody792_24 crepBody792_26

def crepBody792_28 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 97920#64, Flapjack.CrepExp.const 16#64]) crepBody792_6

def crepBody792_29 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 88#64]) crepBody792_28

def crepBody792_30 : CrepProg (BitVec 64) :=
.seq crepBody792_27 crepBody792_29

def crepBody792_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "msg_new" []

def crepBody792_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 8)

def crepBody792_33 : CrepProg (BitVec 64) :=
.seq crepBody792_32 crepBody792_5

def crepBody792_34 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64])) crepBody792_33

def crepBody792_35 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 0#64]) crepBody792_34

def crepBody792_36 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 5) crepBody792_33

def crepBody792_37 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64]) crepBody792_36

def crepBody792_38 : CrepProg (BitVec 64) :=
.seq crepBody792_35 crepBody792_37

def crepBody792_39 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 304#64])) crepBody792_33

def crepBody792_40 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64]) crepBody792_39

def crepBody792_41 : CrepProg (BitVec 64) :=
.seq crepBody792_38 crepBody792_40

def crepBody792_42 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 0) crepBody792_33

def crepBody792_43 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 24#64]) crepBody792_42

def crepBody792_44 : CrepProg (BitVec 64) :=
.seq crepBody792_41 crepBody792_43

def crepBody792_45 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 32#64]) crepBody792_42

def crepBody792_46 : CrepProg (BitVec 64) :=
.seq crepBody792_44 crepBody792_45

def crepBody792_47 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 30000000#64) crepBody792_33

def crepBody792_48 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 40#64]) crepBody792_47

def crepBody792_49 : CrepProg (BitVec 64) :=
.seq crepBody792_46 crepBody792_48

def crepBody792_50 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 97920#64, Flapjack.CrepExp.const 16#64]) crepBody792_33

def crepBody792_51 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 48#64]) crepBody792_50

def crepBody792_52 : CrepProg (BitVec 64) :=
.seq crepBody792_49 crepBody792_51

def crepBody792_53 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 1) crepBody792_33

def crepBody792_54 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 88#64]) crepBody792_53

def crepBody792_55 : CrepProg (BitVec 64) :=
.seq crepBody792_52 crepBody792_54

def crepBody792_56 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 2) crepBody792_33

def crepBody792_57 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 96#64]) crepBody792_56

def crepBody792_58 : CrepProg (BitVec 64) :=
.seq crepBody792_55 crepBody792_57

def crepBody792_59 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 104#64]) crepBody792_42

def crepBody792_60 : CrepProg (BitVec 64) :=
.seq crepBody792_58 crepBody792_59

def crepBody792_61 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 3) crepBody792_33

def crepBody792_62 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 112#64]) crepBody792_61

def crepBody792_63 : CrepProg (BitVec 64) :=
.seq crepBody792_60 crepBody792_62

def crepBody792_64 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 4) crepBody792_33

def crepBody792_65 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 120#64]) crepBody792_64

def crepBody792_66 : CrepProg (BitVec 64) :=
.seq crepBody792_63 crepBody792_65

def crepBody792_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "htab_new" [Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.const 8#64]

def crepBody792_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody792_69 : CrepProg (BitVec 64) :=
.seq crepBody792_68 crepBody792_5

def crepBody792_70 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 7) crepBody792_69

def crepBody792_71 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 152#64]) crepBody792_70

def crepBody792_72 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "htab_new" [Flapjack.CrepExp.const 52#64, Flapjack.CrepExp.const 8#64]

def crepBody792_73 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody792_74 : CrepProg (BitVec 64) :=
.seq crepBody792_73 crepBody792_5

def crepBody792_75 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 8) crepBody792_74

def crepBody792_76 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 160#64]) crepBody792_75

def crepBody792_77 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "process_message_call" [Flapjack.CrepExp.var 6]

def crepBody792_78 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "incorporate_tx_into_block" []

def crepBody792_79 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody792_78

def crepBody792_80 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 8#64]]

def crepBody792_81 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "memcpy"
  [Flapjack.CrepExp.var 12,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 40#64]),
    Flapjack.CrepExp.var 11]

def crepBody792_82 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody792_81

def crepBody792_83 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody792_84 : CrepProg (BitVec 64) :=
.seq crepBody792_83 crepBody792_5

def crepBody792_85 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 12) crepBody792_84

def crepBody792_86 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 40#64]) crepBody792_85

def crepBody792_87 : CrepProg (BitVec 64) :=
.seq crepBody792_82 crepBody792_86

def crepBody792_88 : CrepProg (BitVec 64) :=
.seq crepBody792_80 crepBody792_87

def crepBody792_89 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody792_88

def crepBody792_90 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 11)) crepBody792_89 crepBody792_5

def crepBody792_91 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "scratch_release" [Flapjack.CrepExp.var 10]

def crepBody792_92 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody792_91

def crepBody792_93 : CrepProg (BitVec 64) :=
.seq crepBody792_90 crepBody792_92

def crepBody792_94 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "frame_mem_release"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 88#64])]

def crepBody792_95 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody792_94

def crepBody792_96 : CrepProg (BitVec 64) :=
.seq crepBody792_93 crepBody792_95

def crepBody792_97 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 48#64])) crepBody792_96

def crepBody792_98 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody792_97 crepBody792_5

def crepBody792_99 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 9]

def crepBody792_100 : CrepProg (BitVec 64) :=
.seq crepBody792_98 crepBody792_99

def crepBody792_101 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 80#64])) crepBody792_100

def crepBody792_102 : CrepProg (BitVec 64) :=
.seq crepBody792_79 crepBody792_101

def crepBody792_103 : CrepProg (BitVec 64) :=
.seq crepBody792_77 crepBody792_102

def crepBody792_104 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody792_103

def crepBody792_105 : CrepProg (BitVec 64) :=
.seq crepBody792_76 crepBody792_104

def crepBody792_106 : CrepProg (BitVec 64) :=
.seq crepBody792_72 crepBody792_105

def crepBody792_107 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody792_106

def crepBody792_108 : CrepProg (BitVec 64) :=
.seq crepBody792_71 crepBody792_107

def crepBody792_109 : CrepProg (BitVec 64) :=
.seq crepBody792_67 crepBody792_108

def crepBody792_110 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody792_109

def crepBody792_111 : CrepProg (BitVec 64) :=
.seq crepBody792_66 crepBody792_110

def crepBody792_112 : CrepProg (BitVec 64) :=
.seq crepBody792_31 crepBody792_111

def crepBody792_113 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody792_112

def crepBody792_114 : CrepProg (BitVec 64) :=
.seq crepBody792_30 crepBody792_113

def crepBody792_115 : CrepProg (BitVec 64) :=
.seq crepBody792_3 crepBody792_114

def crepBody792_116 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody792_115

def crepBody792_117 : CrepProg (BitVec 64) :=
.seq crepBody792_2 crepBody792_116

def crepBody792_118 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody792_117

def crepBody792_119 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody792_118

def crepBody792_120 : CrepProg (BitVec 64) :=
.seq crepBody792_1 crepBody792_119

def data792 : CrepProg (BitVec 64) := crepBody792_120
def output792 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 117#8, 110#8, 99#8, 104#8, 101#8, 99#8, 107#8, 101#8, 100#8,
    95#8, 115#8, 121#8, 115#8, 116#8, 101#8, 109#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8,
    111#8, 110#8], [0, 1, 2], crepProgToHOL data792)
end InitECandidate.Proofs.FrontendStages.Crep
