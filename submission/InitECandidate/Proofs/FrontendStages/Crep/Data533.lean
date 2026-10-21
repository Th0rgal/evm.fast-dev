import InitECandidate.Proofs.FrontendStages.Crep.Translate517
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody533_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody533_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody533_2 : CrepProg (BitVec 64) :=
.seq crepBody533_0 crepBody533_1

def crepBody533_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "state_restore" [Flapjack.CrepExp.var 12]

def crepBody533_4 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody533_3

def crepBody533_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "refill_frame_state_gas" []

def crepBody533_6 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody533_5

def crepBody533_7 : CrepProg (BitVec 64) :=
.seq crepBody533_4 crepBody533_6

def crepBody533_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "frame_halt" [Flapjack.CrepExp.var 13]

def crepBody533_9 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody533_8

def crepBody533_10 : CrepProg (BitVec 64) :=
.seq crepBody533_7 crepBody533_9

def crepBody533_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 15)

def crepBody533_12 : CrepProg (BitVec 64) :=
.seq crepBody533_11 crepBody533_1

def crepBody533_13 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 264#64])) crepBody533_12

def crepBody533_14 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody533_13

def crepBody533_15 : CrepProg (BitVec 64) :=
.seq crepBody533_10 crepBody533_14

def crepBody533_16 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody533_12

def crepBody533_17 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody533_16

def crepBody533_18 : CrepProg (BitVec 64) :=
.seq crepBody533_15 crepBody533_17

def crepBody533_19 : CrepProg (BitVec 64) :=
.seq crepBody533_2 crepBody533_18

def crepBody533_20 : CrepProg (BitVec 64) :=
.call (some (([14]), some ((8#64), crepBody533_19))) ("create_finish") ([Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 2])

def crepBody533_21 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody533_20

def crepBody533_22 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody533_21

def crepBody533_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "state_restore" [Flapjack.CrepExp.var 12]

def crepBody533_24 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody533_23

def crepBody533_25 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 160#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody533_22 crepBody533_24

def crepBody533_26 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody533_25

def crepBody533_27 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 2#64)) crepBody533_26 crepBody533_1

def crepBody533_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 13)

def crepBody533_29 : CrepProg (BitVec 64) :=
.seq crepBody533_28 crepBody533_1

def crepBody533_30 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 3) crepBody533_29

def crepBody533_31 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]) crepBody533_30

def crepBody533_32 : CrepProg (BitVec 64) :=
.seq crepBody533_27 crepBody533_31

def crepBody533_33 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody533_29

def crepBody533_34 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]) crepBody533_33

def crepBody533_35 : CrepProg (BitVec 64) :=
.seq crepBody533_32 crepBody533_34

def crepBody533_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "rollback_child_access" [Flapjack.CrepExp.var 2]

def crepBody533_37 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody533_36

def crepBody533_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "incorporate_child_on_error" [Flapjack.CrepExp.var 2]

def crepBody533_39 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody533_38

def crepBody533_40 : CrepProg (BitVec 64) :=
.seq crepBody533_37 crepBody533_39

def crepBody533_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "credit_state_gas_refund" [Flapjack.CrepExp.const 183600#64]

def crepBody533_42 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody533_41

def crepBody533_43 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody533_42 crepBody533_1

def crepBody533_44 : CrepProg (BitVec 64) :=
.seq crepBody533_40 crepBody533_43

def crepBody533_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "set_retdata"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 120#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 128#64])]

def crepBody533_46 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody533_45

def crepBody533_47 : CrepProg (BitVec 64) :=
.seq crepBody533_44 crepBody533_46

def crepBody533_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "stack_push"
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody533_49 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody533_48

def crepBody533_50 : CrepProg (BitVec 64) :=
.seq crepBody533_47 crepBody533_49

def crepBody533_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "incorporate_child_on_success" [Flapjack.CrepExp.var 2]

def crepBody533_52 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody533_51

def crepBody533_53 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "set_retdata" [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 0#64]

def crepBody533_54 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody533_53

def crepBody533_55 : CrepProg (BitVec 64) :=
.seq crepBody533_52 crepBody533_54

def crepBody533_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13, 14, 15, 16], none)) "address_to_u256" [Flapjack.CrepExp.var 11]

def crepBody533_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "stack_push"
  [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16]

def crepBody533_58 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody533_57

def crepBody533_59 : CrepProg (BitVec 64) :=
.seq crepBody533_56 crepBody533_58

def crepBody533_60 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody533_59

def crepBody533_61 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody533_60

def crepBody533_62 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody533_61

def crepBody533_63 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody533_62

def crepBody533_64 : CrepProg (BitVec 64) :=
.seq crepBody533_55 crepBody533_63

def crepBody533_65 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 160#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody533_50 crepBody533_64

def crepBody533_66 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 264#64])) crepBody533_65

def crepBody533_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "rollback_child_access" [Flapjack.CrepExp.var 2]

def crepBody533_68 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody533_67

def crepBody533_69 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "incorporate_child_on_error" [Flapjack.CrepExp.var 2]

def crepBody533_70 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody533_69

def crepBody533_71 : CrepProg (BitVec 64) :=
.seq crepBody533_68 crepBody533_70

def crepBody533_72 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "credit_state_gas_refund" [Flapjack.CrepExp.const 183600#64]

def crepBody533_73 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody533_72

def crepBody533_74 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody533_73 crepBody533_1

def crepBody533_75 : CrepProg (BitVec 64) :=
.seq crepBody533_71 crepBody533_74

def crepBody533_76 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "set_retdata"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 120#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 128#64])]

def crepBody533_77 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody533_76

def crepBody533_78 : CrepProg (BitVec 64) :=
.seq crepBody533_75 crepBody533_77

def crepBody533_79 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "stack_push"
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody533_80 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody533_79

def crepBody533_81 : CrepProg (BitVec 64) :=
.seq crepBody533_78 crepBody533_80

def crepBody533_82 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "incorporate_child_on_success" [Flapjack.CrepExp.var 2]

def crepBody533_83 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody533_82

def crepBody533_84 : CrepProg (BitVec 64) :=
.seq crepBody533_83 crepBody533_77

def crepBody533_85 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "stack_push"
  [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody533_86 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody533_85

def crepBody533_87 : CrepProg (BitVec 64) :=
.seq crepBody533_84 crepBody533_86

def crepBody533_88 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 160#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody533_81 crepBody533_87

def crepBody533_89 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "min"
  [Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 128#64])]

def crepBody533_90 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 9],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 144#64]),
    Flapjack.CrepExp.var 12]

def crepBody533_91 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody533_90

def crepBody533_92 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.const 0#64)) crepBody533_91 crepBody533_1

def crepBody533_93 : CrepProg (BitVec 64) :=
.seq crepBody533_89 crepBody533_92

def crepBody533_94 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody533_93

def crepBody533_95 : CrepProg (BitVec 64) :=
.seq crepBody533_88 crepBody533_94

def crepBody533_96 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 2#64)) crepBody533_66 crepBody533_95

def crepBody533_97 : CrepProg (BitVec 64) :=
.seq crepBody533_35 crepBody533_96

def crepBody533_98 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "scratch_release" [Flapjack.CrepExp.var 7]

def crepBody533_99 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody533_98

def crepBody533_100 : CrepProg (BitVec 64) :=
.seq crepBody533_97 crepBody533_99

def crepBody533_101 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "frame_mem_release" [Flapjack.CrepExp.var 8]

def crepBody533_102 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody533_101

def crepBody533_103 : CrepProg (BitVec 64) :=
.seq crepBody533_100 crepBody533_102

def crepBody533_104 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody533_105 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody533_104

def crepBody533_106 : CrepProg (BitVec 64) :=
.seq crepBody533_103 crepBody533_105

def crepBody533_107 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody533_108 : CrepProg (BitVec 64) :=
.seq crepBody533_106 crepBody533_107

def crepBody533_109 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64])) crepBody533_108

def crepBody533_110 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 80#64])) crepBody533_109

def crepBody533_111 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 72#64])) crepBody533_110

def crepBody533_112 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64])) crepBody533_111

def crepBody533_113 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64])) crepBody533_112

def crepBody533_114 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 64#64])) crepBody533_113

def crepBody533_115 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64])) crepBody533_114

def crepBody533_116 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64])) crepBody533_115

def crepBody533_117 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64])) crepBody533_116

def crepBody533_118 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64])) crepBody533_117

def crepBody533_119 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64])) crepBody533_118

def data533 : CrepProg (BitVec 64) := crepBody533_119
def output533 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [102#8, 105#8, 110#8, 105#8, 115#8, 104#8, 95#8, 99#8, 104#8, 105#8, 108#8, 100#8], [], crepProgToHOL data533)
end InitECandidate.Proofs.FrontendStages.Crep
