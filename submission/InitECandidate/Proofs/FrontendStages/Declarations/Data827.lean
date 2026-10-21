import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify811
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body827_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_ecrecover" []

def body827_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body827_2 : Prog (BitVec 64) :=
.seq body827_0 body827_1

def body827_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body827_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 1#64)) body827_2 body827_3

def body827_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_sha256" []

def body827_6 : Prog (BitVec 64) :=
.seq body827_5 body827_1

def body827_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 2#64)) body827_6 body827_3

def body827_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_ripemd160" []

def body827_9 : Prog (BitVec 64) :=
.seq body827_8 body827_1

def body827_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 3#64)) body827_9 body827_3

def body827_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_identity" []

def body827_12 : Prog (BitVec 64) :=
.seq body827_11 body827_1

def body827_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 4#64)) body827_12 body827_3

def body827_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_alt_bn128_add" []

def body827_15 : Prog (BitVec 64) :=
.seq body827_14 body827_1

def body827_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 6#64)) body827_15 body827_3

def body827_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_alt_bn128_mul" []

def body827_18 : Prog (BitVec 64) :=
.seq body827_17 body827_1

def body827_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 7#64)) body827_18 body827_3

def body827_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_alt_bn128_pairing_check" []

def body827_21 : Prog (BitVec 64) :=
.seq body827_20 body827_1

def body827_22 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 8#64)) body827_21 body827_3

def body827_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_modexp" []

def body827_24 : Prog (BitVec 64) :=
.seq body827_23 body827_1

def body827_25 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 5#64)) body827_24 body827_3

def body827_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_blake2f" []

def body827_27 : Prog (BitVec 64) :=
.seq body827_26 body827_1

def body827_28 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 9#64)) body827_27 body827_3

def body827_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_kzg_point_evaluation" []

def body827_30 : Prog (BitVec 64) :=
.seq body827_29 body827_1

def body827_31 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 10#64)) body827_30 body827_3

def body827_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_g1_add" []

def body827_33 : Prog (BitVec 64) :=
.seq body827_32 body827_1

def body827_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 11#64)) body827_33 body827_3

def body827_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_g1_msm" []

def body827_36 : Prog (BitVec 64) :=
.seq body827_35 body827_1

def body827_37 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 12#64)) body827_36 body827_3

def body827_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_g2_add" []

def body827_39 : Prog (BitVec 64) :=
.seq body827_38 body827_1

def body827_40 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 13#64)) body827_39 body827_3

def body827_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_g2_msm" []

def body827_42 : Prog (BitVec 64) :=
.seq body827_41 body827_1

def body827_43 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 14#64)) body827_42 body827_3

def body827_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_pairing" []

def body827_45 : Prog (BitVec 64) :=
.seq body827_44 body827_1

def body827_46 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 15#64)) body827_45 body827_3

def body827_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_map_fp_to_g1" []

def body827_48 : Prog (BitVec 64) :=
.seq body827_47 body827_1

def body827_49 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 16#64)) body827_48 body827_3

def body827_50 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_map_fp2_to_g2" []

def body827_51 : Prog (BitVec 64) :=
.seq body827_50 body827_1

def body827_52 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 17#64)) body827_51 body827_3

def body827_53 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_p256verify" []

def body827_54 : Prog (BitVec 64) :=
.seq body827_53 body827_1

def body827_55 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 18#64)) body827_54 body827_3

def body827_56 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 99#64)

def body827_57 : Prog (BitVec 64) :=
.seq body827_56 body827_1

def body827_58 : Prog (BitVec 64) :=
.seq body827_55 body827_57

def body827_59 : Prog (BitVec 64) :=
.seq body827_52 body827_58

def body827_60 : Prog (BitVec 64) :=
.seq body827_49 body827_59

def body827_61 : Prog (BitVec 64) :=
.seq body827_46 body827_60

def body827_62 : Prog (BitVec 64) :=
.seq body827_43 body827_61

def body827_63 : Prog (BitVec 64) :=
.seq body827_40 body827_62

def body827_64 : Prog (BitVec 64) :=
.seq body827_37 body827_63

def body827_65 : Prog (BitVec 64) :=
.seq body827_34 body827_64

def body827_66 : Prog (BitVec 64) :=
.seq body827_31 body827_65

def body827_67 : Prog (BitVec 64) :=
.seq body827_28 body827_66

def body827_68 : Prog (BitVec 64) :=
.seq body827_25 body827_67

def body827_69 : Prog (BitVec 64) :=
.seq body827_22 body827_68

def body827_70 : Prog (BitVec 64) :=
.seq body827_19 body827_69

def body827_71 : Prog (BitVec 64) :=
.seq body827_16 body827_70

def body827_72 : Prog (BitVec 64) :=
.seq body827_13 body827_71

def body827_73 : Prog (BitVec 64) :=
.seq body827_10 body827_72

def body827_74 : Prog (BitVec 64) :=
.seq body827_7 body827_73

def body827_75 : Prog (BitVec 64) :=
.seq body827_4 body827_74

def body827_76 : Prog (BitVec 64) :=
.seq body827_4 body827_7

def body827_77 : Prog (BitVec 64) :=
.seq body827_76 body827_10

def body827_78 : Prog (BitVec 64) :=
.seq body827_77 body827_13

def body827_79 : Prog (BitVec 64) :=
.seq body827_78 body827_16

def body827_80 : Prog (BitVec 64) :=
.seq body827_79 body827_19

def body827_81 : Prog (BitVec 64) :=
.seq body827_80 body827_22

def body827_82 : Prog (BitVec 64) :=
.seq body827_81 body827_25

def body827_83 : Prog (BitVec 64) :=
.seq body827_82 body827_28

def body827_84 : Prog (BitVec 64) :=
.seq body827_83 body827_31

def body827_85 : Prog (BitVec 64) :=
.seq body827_84 body827_34

def body827_86 : Prog (BitVec 64) :=
.seq body827_85 body827_37

def body827_87 : Prog (BitVec 64) :=
.seq body827_86 body827_40

def body827_88 : Prog (BitVec 64) :=
.seq body827_87 body827_43

def body827_89 : Prog (BitVec 64) :=
.seq body827_88 body827_46

def body827_90 : Prog (BitVec 64) :=
.seq body827_89 body827_49

def body827_91 : Prog (BitVec 64) :=
.seq body827_90 body827_52

def body827_92 : Prog (BitVec 64) :=
.seq body827_91 body827_55

def body827_93 : Prog (BitVec 64) :=
.seq body827_92 body827_56

def body827_94 : Prog (BitVec 64) :=
.seq body827_93 body827_1

def originalData827 : Decl (BitVec 64) :=
.function { name := "run_precompile", inline := false, exported := false, params := [("idx", Flapjack.Shape.one)], body := body827_75, returnShape := (Flapjack.Shape.one) }
def simplifiedData827 : Decl (BitVec 64) :=
.function { name := "run_precompile", inline := false, exported := false, params := [("idx", Flapjack.Shape.one)], body := body827_94, returnShape := (Flapjack.Shape.one) }
def original827 := Pancake.PanLang.declToHOL originalData827
def simplified827 := Pancake.PanLang.declToHOL simplifiedData827
end InitECandidate.Proofs.FrontendStages.Declarations
