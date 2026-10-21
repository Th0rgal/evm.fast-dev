import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify547
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body563_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "s") (Flapjack.Exp.const 84#64)

def body563_1 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 114#64)

def body563_2 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 2#64])
  (Flapjack.Exp.const 97#64)

def body563_3 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 3#64])
  (Flapjack.Exp.const 110#64)

def body563_4 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 4#64])
  (Flapjack.Exp.const 115#64)

def body563_5 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 5#64])
  (Flapjack.Exp.const 102#64)

def body563_6 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 6#64])
  (Flapjack.Exp.const 101#64)

def body563_7 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 7#64])
  (Flapjack.Exp.const 114#64)

def body563_8 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 40#64)

def body563_9 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 9#64])
  (Flapjack.Exp.const 97#64)

def body563_10 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 10#64])
  (Flapjack.Exp.const 100#64)

def body563_11 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 11#64])
  (Flapjack.Exp.const 100#64)

def body563_12 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 12#64])
  (Flapjack.Exp.const 114#64)

def body563_13 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 13#64])
  (Flapjack.Exp.const 101#64)

def body563_14 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 14#64])
  (Flapjack.Exp.const 115#64)

def body563_15 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 15#64])
  (Flapjack.Exp.const 115#64)

def body563_16 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 44#64)

def body563_17 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 17#64])
  (Flapjack.Exp.const 97#64)

def body563_18 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 18#64])
  (Flapjack.Exp.const 100#64)

def body563_19 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 19#64])
  (Flapjack.Exp.const 100#64)

def body563_20 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 20#64])
  (Flapjack.Exp.const 114#64)

def body563_21 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 21#64])
  (Flapjack.Exp.const 101#64)

def body563_22 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 22#64])
  (Flapjack.Exp.const 115#64)

def body563_23 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 23#64])
  (Flapjack.Exp.const 115#64)

def body563_24 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 44#64)

def body563_25 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 25#64])
  (Flapjack.Exp.const 117#64)

def body563_26 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 26#64])
  (Flapjack.Exp.const 105#64)

def body563_27 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 27#64])
  (Flapjack.Exp.const 110#64)

def body563_28 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 28#64])
  (Flapjack.Exp.const 116#64)

def body563_29 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 29#64])
  (Flapjack.Exp.const 50#64)

def body563_30 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 30#64])
  (Flapjack.Exp.const 53#64)

def body563_31 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 31#64])
  (Flapjack.Exp.const 54#64)

def body563_32 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 41#64)

def body563_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body563_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "transfer_topic"), none)) "alloc" [Flapjack.Exp.const 32#64]

def body563_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 33#64,
    Flapjack.Exp.var Flapjack.VarKind.global "transfer_topic"]

def body563_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "vm_system_address"), none)) "alloc" [Flapjack.Exp.const 24#64]

def body563_37 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "vm_system_address", Flapjack.Exp.var Flapjack.VarKind.local "i"])
  (Flapjack.Exp.const 255#64)

def body563_38 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body563_39 : Prog (BitVec 64) :=
.seq body563_37 body563_38

def body563_40 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 20#64)) body563_39

def body563_41 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "vm_system_address", Flapjack.Exp.const 19#64])
  (Flapjack.Exp.const 254#64)

def body563_42 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "null_address"), none)) "alloc" [Flapjack.Exp.const 24#64]

def body563_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.global "null_address", Flapjack.Exp.const 24#64]

def body563_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "evm_empty"), none)) "alloc" [Flapjack.Exp.const 8#64]

def body563_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.global "evm_empty", Flapjack.Exp.const 8#64]

def body563_46 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "evm_key_buf"), none)) "alloc" [Flapjack.Exp.const 32#64]

def body563_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "pre_hdr_buf"), none)) "alloc" [Flapjack.Exp.const 96#64]

def body563_48 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body563_49 : Prog (BitVec 64) :=
.seq body563_47 body563_48

def body563_50 : Prog (BitVec 64) :=
.seq body563_46 body563_49

def body563_51 : Prog (BitVec 64) :=
.seq body563_45 body563_50

def body563_52 : Prog (BitVec 64) :=
.seq body563_44 body563_51

def body563_53 : Prog (BitVec 64) :=
.seq body563_43 body563_52

def body563_54 : Prog (BitVec 64) :=
.seq body563_42 body563_53

def body563_55 : Prog (BitVec 64) :=
.seq body563_41 body563_54

def body563_56 : Prog (BitVec 64) :=
.seq body563_40 body563_55

def body563_57 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body563_56

def body563_58 : Prog (BitVec 64) :=
.seq body563_36 body563_57

def body563_59 : Prog (BitVec 64) :=
.seq body563_35 body563_58

def body563_60 : Prog (BitVec 64) :=
.seq body563_34 body563_59

def body563_61 : Prog (BitVec 64) :=
.seq body563_33 body563_60

def body563_62 : Prog (BitVec 64) :=
.seq body563_32 body563_61

def body563_63 : Prog (BitVec 64) :=
.seq body563_31 body563_62

def body563_64 : Prog (BitVec 64) :=
.seq body563_30 body563_63

def body563_65 : Prog (BitVec 64) :=
.seq body563_29 body563_64

def body563_66 : Prog (BitVec 64) :=
.seq body563_28 body563_65

def body563_67 : Prog (BitVec 64) :=
.seq body563_27 body563_66

def body563_68 : Prog (BitVec 64) :=
.seq body563_26 body563_67

def body563_69 : Prog (BitVec 64) :=
.seq body563_25 body563_68

def body563_70 : Prog (BitVec 64) :=
.seq body563_24 body563_69

def body563_71 : Prog (BitVec 64) :=
.seq body563_23 body563_70

def body563_72 : Prog (BitVec 64) :=
.seq body563_22 body563_71

def body563_73 : Prog (BitVec 64) :=
.seq body563_21 body563_72

def body563_74 : Prog (BitVec 64) :=
.seq body563_20 body563_73

def body563_75 : Prog (BitVec 64) :=
.seq body563_19 body563_74

def body563_76 : Prog (BitVec 64) :=
.seq body563_18 body563_75

def body563_77 : Prog (BitVec 64) :=
.seq body563_17 body563_76

def body563_78 : Prog (BitVec 64) :=
.seq body563_16 body563_77

def body563_79 : Prog (BitVec 64) :=
.seq body563_15 body563_78

def body563_80 : Prog (BitVec 64) :=
.seq body563_14 body563_79

def body563_81 : Prog (BitVec 64) :=
.seq body563_13 body563_80

def body563_82 : Prog (BitVec 64) :=
.seq body563_12 body563_81

def body563_83 : Prog (BitVec 64) :=
.seq body563_11 body563_82

def body563_84 : Prog (BitVec 64) :=
.seq body563_10 body563_83

def body563_85 : Prog (BitVec 64) :=
.seq body563_9 body563_84

def body563_86 : Prog (BitVec 64) :=
.seq body563_8 body563_85

def body563_87 : Prog (BitVec 64) :=
.seq body563_7 body563_86

def body563_88 : Prog (BitVec 64) :=
.seq body563_6 body563_87

def body563_89 : Prog (BitVec 64) :=
.seq body563_5 body563_88

def body563_90 : Prog (BitVec 64) :=
.seq body563_4 body563_89

def body563_91 : Prog (BitVec 64) :=
.seq body563_3 body563_90

def body563_92 : Prog (BitVec 64) :=
.seq body563_2 body563_91

def body563_93 : Prog (BitVec 64) :=
.seq body563_1 body563_92

def body563_94 : Prog (BitVec 64) :=
.seq body563_0 body563_93

def body563_95 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 40#64]) body563_94

def body563_96 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body563_95

def body563_97 : Prog (BitVec 64) :=
.seq body563_0 body563_1

def body563_98 : Prog (BitVec 64) :=
.seq body563_97 body563_2

def body563_99 : Prog (BitVec 64) :=
.seq body563_98 body563_3

def body563_100 : Prog (BitVec 64) :=
.seq body563_99 body563_4

def body563_101 : Prog (BitVec 64) :=
.seq body563_100 body563_5

def body563_102 : Prog (BitVec 64) :=
.seq body563_101 body563_6

def body563_103 : Prog (BitVec 64) :=
.seq body563_102 body563_7

def body563_104 : Prog (BitVec 64) :=
.seq body563_103 body563_8

def body563_105 : Prog (BitVec 64) :=
.seq body563_104 body563_9

def body563_106 : Prog (BitVec 64) :=
.seq body563_105 body563_10

def body563_107 : Prog (BitVec 64) :=
.seq body563_106 body563_11

def body563_108 : Prog (BitVec 64) :=
.seq body563_107 body563_12

def body563_109 : Prog (BitVec 64) :=
.seq body563_108 body563_13

def body563_110 : Prog (BitVec 64) :=
.seq body563_109 body563_14

def body563_111 : Prog (BitVec 64) :=
.seq body563_110 body563_15

def body563_112 : Prog (BitVec 64) :=
.seq body563_111 body563_16

def body563_113 : Prog (BitVec 64) :=
.seq body563_112 body563_17

def body563_114 : Prog (BitVec 64) :=
.seq body563_113 body563_18

def body563_115 : Prog (BitVec 64) :=
.seq body563_114 body563_19

def body563_116 : Prog (BitVec 64) :=
.seq body563_115 body563_20

def body563_117 : Prog (BitVec 64) :=
.seq body563_116 body563_21

def body563_118 : Prog (BitVec 64) :=
.seq body563_117 body563_22

def body563_119 : Prog (BitVec 64) :=
.seq body563_118 body563_23

def body563_120 : Prog (BitVec 64) :=
.seq body563_119 body563_24

def body563_121 : Prog (BitVec 64) :=
.seq body563_120 body563_25

def body563_122 : Prog (BitVec 64) :=
.seq body563_121 body563_26

def body563_123 : Prog (BitVec 64) :=
.seq body563_122 body563_27

def body563_124 : Prog (BitVec 64) :=
.seq body563_123 body563_28

def body563_125 : Prog (BitVec 64) :=
.seq body563_124 body563_29

def body563_126 : Prog (BitVec 64) :=
.seq body563_125 body563_30

def body563_127 : Prog (BitVec 64) :=
.seq body563_126 body563_31

def body563_128 : Prog (BitVec 64) :=
.seq body563_127 body563_32

def body563_129 : Prog (BitVec 64) :=
.seq body563_128 body563_33

def body563_130 : Prog (BitVec 64) :=
.seq body563_129 body563_34

def body563_131 : Prog (BitVec 64) :=
.seq body563_130 body563_35

def body563_132 : Prog (BitVec 64) :=
.seq body563_131 body563_36

def body563_133 : Prog (BitVec 64) :=
.seq body563_40 body563_41

def body563_134 : Prog (BitVec 64) :=
.seq body563_133 body563_42

def body563_135 : Prog (BitVec 64) :=
.seq body563_134 body563_43

def body563_136 : Prog (BitVec 64) :=
.seq body563_135 body563_44

def body563_137 : Prog (BitVec 64) :=
.seq body563_136 body563_45

def body563_138 : Prog (BitVec 64) :=
.seq body563_137 body563_46

def body563_139 : Prog (BitVec 64) :=
.seq body563_138 body563_47

def body563_140 : Prog (BitVec 64) :=
.seq body563_139 body563_48

def body563_141 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body563_140

def body563_142 : Prog (BitVec 64) :=
.seq body563_132 body563_141

def body563_143 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 40#64]) body563_142

def body563_144 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body563_143

def originalData563 : Decl (BitVec 64) :=
.function { name := "evm_init", inline := false, exported := false, params := [], body := body563_96, returnShape := (Flapjack.Shape.one) }
def simplifiedData563 : Decl (BitVec 64) :=
.function { name := "evm_init", inline := false, exported := false, params := [], body := body563_144, returnShape := (Flapjack.Shape.one) }
def original563 := Pancake.PanLang.declToHOL originalData563
def simplified563 := Pancake.PanLang.declToHOL simplifiedData563
end InitECandidate.Proofs.FrontendStages.Declarations
