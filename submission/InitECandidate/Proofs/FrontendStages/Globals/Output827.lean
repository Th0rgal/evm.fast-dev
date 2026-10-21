import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data827
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate811
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody827_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_ecrecover" []

def globalBody827_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody827_2 : Prog (BitVec 64) :=
.seq globalBody827_0 globalBody827_1

def globalBody827_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody827_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 1#64)) globalBody827_2 globalBody827_3

def globalBody827_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_sha256" []

def globalBody827_6 : Prog (BitVec 64) :=
.seq globalBody827_5 globalBody827_1

def globalBody827_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 2#64)) globalBody827_6 globalBody827_3

def globalBody827_8 : Prog (BitVec 64) :=
.seq globalBody827_4 globalBody827_7

def globalBody827_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_ripemd160" []

def globalBody827_10 : Prog (BitVec 64) :=
.seq globalBody827_9 globalBody827_1

def globalBody827_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 3#64)) globalBody827_10 globalBody827_3

def globalBody827_12 : Prog (BitVec 64) :=
.seq globalBody827_8 globalBody827_11

def globalBody827_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_identity" []

def globalBody827_14 : Prog (BitVec 64) :=
.seq globalBody827_13 globalBody827_1

def globalBody827_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 4#64)) globalBody827_14 globalBody827_3

def globalBody827_16 : Prog (BitVec 64) :=
.seq globalBody827_12 globalBody827_15

def globalBody827_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_alt_bn128_add" []

def globalBody827_18 : Prog (BitVec 64) :=
.seq globalBody827_17 globalBody827_1

def globalBody827_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 6#64)) globalBody827_18 globalBody827_3

def globalBody827_20 : Prog (BitVec 64) :=
.seq globalBody827_16 globalBody827_19

def globalBody827_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_alt_bn128_mul" []

def globalBody827_22 : Prog (BitVec 64) :=
.seq globalBody827_21 globalBody827_1

def globalBody827_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 7#64)) globalBody827_22 globalBody827_3

def globalBody827_24 : Prog (BitVec 64) :=
.seq globalBody827_20 globalBody827_23

def globalBody827_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_alt_bn128_pairing_check" []

def globalBody827_26 : Prog (BitVec 64) :=
.seq globalBody827_25 globalBody827_1

def globalBody827_27 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 8#64)) globalBody827_26 globalBody827_3

def globalBody827_28 : Prog (BitVec 64) :=
.seq globalBody827_24 globalBody827_27

def globalBody827_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_modexp" []

def globalBody827_30 : Prog (BitVec 64) :=
.seq globalBody827_29 globalBody827_1

def globalBody827_31 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 5#64)) globalBody827_30 globalBody827_3

def globalBody827_32 : Prog (BitVec 64) :=
.seq globalBody827_28 globalBody827_31

def globalBody827_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_blake2f" []

def globalBody827_34 : Prog (BitVec 64) :=
.seq globalBody827_33 globalBody827_1

def globalBody827_35 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 9#64)) globalBody827_34 globalBody827_3

def globalBody827_36 : Prog (BitVec 64) :=
.seq globalBody827_32 globalBody827_35

def globalBody827_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_kzg_point_evaluation" []

def globalBody827_38 : Prog (BitVec 64) :=
.seq globalBody827_37 globalBody827_1

def globalBody827_39 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 10#64)) globalBody827_38 globalBody827_3

def globalBody827_40 : Prog (BitVec 64) :=
.seq globalBody827_36 globalBody827_39

def globalBody827_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_g1_add" []

def globalBody827_42 : Prog (BitVec 64) :=
.seq globalBody827_41 globalBody827_1

def globalBody827_43 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 11#64)) globalBody827_42 globalBody827_3

def globalBody827_44 : Prog (BitVec 64) :=
.seq globalBody827_40 globalBody827_43

def globalBody827_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_g1_msm" []

def globalBody827_46 : Prog (BitVec 64) :=
.seq globalBody827_45 globalBody827_1

def globalBody827_47 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 12#64)) globalBody827_46 globalBody827_3

def globalBody827_48 : Prog (BitVec 64) :=
.seq globalBody827_44 globalBody827_47

def globalBody827_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_g2_add" []

def globalBody827_50 : Prog (BitVec 64) :=
.seq globalBody827_49 globalBody827_1

def globalBody827_51 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 13#64)) globalBody827_50 globalBody827_3

def globalBody827_52 : Prog (BitVec 64) :=
.seq globalBody827_48 globalBody827_51

def globalBody827_53 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_g2_msm" []

def globalBody827_54 : Prog (BitVec 64) :=
.seq globalBody827_53 globalBody827_1

def globalBody827_55 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 14#64)) globalBody827_54 globalBody827_3

def globalBody827_56 : Prog (BitVec 64) :=
.seq globalBody827_52 globalBody827_55

def globalBody827_57 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_pairing" []

def globalBody827_58 : Prog (BitVec 64) :=
.seq globalBody827_57 globalBody827_1

def globalBody827_59 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 15#64)) globalBody827_58 globalBody827_3

def globalBody827_60 : Prog (BitVec 64) :=
.seq globalBody827_56 globalBody827_59

def globalBody827_61 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_map_fp_to_g1" []

def globalBody827_62 : Prog (BitVec 64) :=
.seq globalBody827_61 globalBody827_1

def globalBody827_63 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 16#64)) globalBody827_62 globalBody827_3

def globalBody827_64 : Prog (BitVec 64) :=
.seq globalBody827_60 globalBody827_63

def globalBody827_65 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_bls_map_fp2_to_g2" []

def globalBody827_66 : Prog (BitVec 64) :=
.seq globalBody827_65 globalBody827_1

def globalBody827_67 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 17#64)) globalBody827_66 globalBody827_3

def globalBody827_68 : Prog (BitVec 64) :=
.seq globalBody827_64 globalBody827_67

def globalBody827_69 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pre_p256verify" []

def globalBody827_70 : Prog (BitVec 64) :=
.seq globalBody827_69 globalBody827_1

def globalBody827_71 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 18#64)) globalBody827_70 globalBody827_3

def globalBody827_72 : Prog (BitVec 64) :=
.seq globalBody827_68 globalBody827_71

def globalBody827_73 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 99#64)

def globalBody827_74 : Prog (BitVec 64) :=
.seq globalBody827_72 globalBody827_73

def globalBody827_75 : Prog (BitVec 64) :=
.seq globalBody827_74 globalBody827_1

def globalData827 : Decl (BitVec 64) :=
.function { name := "run_precompile", inline := false, exported := false, params := [("idx", Flapjack.Shape.one)], body := globalBody827_75, returnShape := (Flapjack.Shape.one) }
def globalOutput827 := Pancake.PanLang.declToHOL globalData827
end InitECandidate.Proofs.FrontendStages.Declarations
