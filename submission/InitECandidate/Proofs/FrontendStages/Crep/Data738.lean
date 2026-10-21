import InitECandidate.Proofs.FrontendStages.Crep.Translate722
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody738_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "is_zero_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.const 47#64]

def crepBody738_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "g1_set_inf" [Flapjack.CrepExp.var 1]

def crepBody738_2 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody738_1

def crepBody738_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody738_4 : CrepProg (BitVec 64) :=
.seq crepBody738_2 crepBody738_3

def crepBody738_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody738_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 1#64)) crepBody738_4 crepBody738_5

def crepBody738_7 : CrepProg (BitVec 64) :=
.seq crepBody738_0 crepBody738_6

def crepBody738_8 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody738_7

def crepBody738_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 0))
  (Flapjack.CrepExp.const 192#64)) crepBody738_8 crepBody738_5

def crepBody738_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "kzg_decompress_g1" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody738_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody738_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody738_11 crepBody738_5

def crepBody738_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "g1_is_inf" [Flapjack.CrepExp.var 1]

def crepBody738_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 1#64)) crepBody738_11 crepBody738_5

def crepBody738_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call none "g1_subgroup_check" [Flapjack.CrepExp.var 1]

def crepBody738_16 : CrepProg (BitVec 64) :=
.seq crepBody738_14 crepBody738_15

def crepBody738_17 : CrepProg (BitVec 64) :=
.seq crepBody738_13 crepBody738_16

def crepBody738_18 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody738_17

def crepBody738_19 : CrepProg (BitVec 64) :=
.seq crepBody738_12 crepBody738_18

def crepBody738_20 : CrepProg (BitVec 64) :=
.seq crepBody738_10 crepBody738_19

def crepBody738_21 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody738_20

def crepBody738_22 : CrepProg (BitVec 64) :=
.seq crepBody738_9 crepBody738_21

def data738 : CrepProg (BitVec 64) := crepBody738_22
def output738 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [107#8, 122#8, 103#8, 95#8, 108#8, 111#8, 97#8, 100#8, 95#8, 103#8, 49#8], [0, 1], crepProgToHOL data738)
end InitECandidate.Proofs.FrontendStages.Crep
