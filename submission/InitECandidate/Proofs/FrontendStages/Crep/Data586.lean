import InitECandidate.Proofs.FrontendStages.Crep.Translate570
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody586_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9, 10, 11], none)) "p256_fp_sqr"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody586_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12, 13, 14, 15], none)) "p256_fp_sqr"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody586_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12, 13, 14, 15], none)) "p256_fp_mul"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody586_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16, 17, 18, 19], none)) "p256_fp_add"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody586_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16, 17, 18, 19], none)) "p256_fp_add"
  [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19,
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody586_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12, 13, 14, 15], none)) "p256_fp_sub"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19]

def crepBody586_6 : CrepProg (BitVec 64) :=
.seq crepBody586_4 crepBody586_5

def crepBody586_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12, 13, 14, 15], none)) "p256_fp_add"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.const 4309448131093880907#64, Flapjack.CrepExp.const 7285987128567378166#64,
    Flapjack.CrepExp.const 12964664127075681980#64, Flapjack.CrepExp.const 6540974713487397863#64]

def crepBody586_8 : CrepProg (BitVec 64) :=
.seq crepBody586_6 crepBody586_7

def crepBody586_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call none "u256_eq"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15]

def crepBody586_10 : CrepProg (BitVec 64) :=
.seq crepBody586_8 crepBody586_9

def crepBody586_11 : CrepProg (BitVec 64) :=
.seq crepBody586_3 crepBody586_10

def crepBody586_12 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody586_11

def crepBody586_13 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody586_12

def crepBody586_14 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody586_13

def crepBody586_15 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody586_14

def crepBody586_16 : CrepProg (BitVec 64) :=
.seq crepBody586_2 crepBody586_15

def crepBody586_17 : CrepProg (BitVec 64) :=
.seq crepBody586_1 crepBody586_16

def crepBody586_18 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody586_17

def crepBody586_19 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody586_18

def crepBody586_20 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody586_19

def crepBody586_21 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody586_20

def crepBody586_22 : CrepProg (BitVec 64) :=
.seq crepBody586_0 crepBody586_21

def crepBody586_23 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody586_22

def crepBody586_24 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody586_23

def crepBody586_25 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody586_24

def crepBody586_26 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody586_25

def data586 : CrepProg (BitVec 64) := crepBody586_26
def output586 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 50#8, 53#8, 54#8, 95#8, 111#8, 110#8, 95#8, 99#8, 117#8, 114#8, 118#8, 101#8], [0, 1, 2, 3, 4, 5, 6, 7], crepProgToHOL data586)
end InitECandidate.Proofs.FrontendStages.Crep
