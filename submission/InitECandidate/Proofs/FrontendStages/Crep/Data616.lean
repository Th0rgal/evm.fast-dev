import InitECandidate.Proofs.FrontendStages.Crep.Translate600
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody616_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "heap_mark" []

def crepBody616_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.var 7]

def crepBody616_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "alloc" [Flapjack.CrepExp.var 7]

def crepBody616_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "ecp_set_inf" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 9]

def crepBody616_4 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody616_3

def crepBody616_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "memcpy"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 7]

def crepBody616_6 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody616_5

def crepBody616_7 : CrepProg (BitVec 64) :=
.seq crepBody616_4 crepBody616_6

def crepBody616_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "u256_bit_length"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody616_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "u256_bit"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.var 12]

def crepBody616_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "ecp_add"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10]

def crepBody616_11 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody616_10

def crepBody616_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody616_13 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 1#64)) crepBody616_11 crepBody616_12

def crepBody616_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.var 14)

def crepBody616_15 : CrepProg (BitVec 64) :=
.seq crepBody616_14 crepBody616_12

def crepBody616_16 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 1#64]) crepBody616_15

def crepBody616_17 : CrepProg (BitVec 64) :=
.seq crepBody616_13 crepBody616_16

def crepBody616_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "ecp_double"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 10]

def crepBody616_19 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody616_18

def crepBody616_20 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 11)) crepBody616_19 crepBody616_12

def crepBody616_21 : CrepProg (BitVec 64) :=
.seq crepBody616_17 crepBody616_20

def crepBody616_22 : CrepProg (BitVec 64) :=
.seq crepBody616_9 crepBody616_21

def crepBody616_23 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody616_22

def crepBody616_24 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 11)) crepBody616_23

def crepBody616_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "memcpy"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 7]

def crepBody616_26 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody616_25

def crepBody616_27 : CrepProg (BitVec 64) :=
.seq crepBody616_24 crepBody616_26

def crepBody616_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "heap_release" [Flapjack.CrepExp.var 8]

def crepBody616_29 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody616_28

def crepBody616_30 : CrepProg (BitVec 64) :=
.seq crepBody616_27 crepBody616_29

def crepBody616_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody616_32 : CrepProg (BitVec 64) :=
.seq crepBody616_30 crepBody616_31

def crepBody616_33 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody616_32

def crepBody616_34 : CrepProg (BitVec 64) :=
.seq crepBody616_8 crepBody616_33

def crepBody616_35 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody616_34

def crepBody616_36 : CrepProg (BitVec 64) :=
.seq crepBody616_7 crepBody616_35

def crepBody616_37 : CrepProg (BitVec 64) :=
.seq crepBody616_2 crepBody616_36

def crepBody616_38 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody616_37

def crepBody616_39 : CrepProg (BitVec 64) :=
.seq crepBody616_1 crepBody616_38

def crepBody616_40 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody616_39

def crepBody616_41 : CrepProg (BitVec 64) :=
.seq crepBody616_0 crepBody616_40

def crepBody616_42 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody616_41

def crepBody616_43 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
  [Flapjack.CrepExp.const 3#64,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]]) crepBody616_42

def data616 : CrepProg (BitVec 64) := crepBody616_43
def output616 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [101#8, 99#8, 112#8, 95#8, 109#8, 117#8, 108#8], [0, 1, 2, 3, 4, 5, 6], crepProgToHOL data616)
end InitECandidate.Proofs.FrontendStages.Crep
