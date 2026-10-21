import InitECandidate.Proofs.FrontendStages.Crep.Translate760
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody776_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "rlp_word_encoded_len"
  [Flapjack.CrepExp.op Flapjack.BinOp.or
      [Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 0),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 1#64]))
          (Flapjack.CrepExp.const 8#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 2#64]))
          (Flapjack.CrepExp.const 16#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 3#64]))
          (Flapjack.CrepExp.const 24#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.op Flapjack.BinOp.or
            [Flapjack.CrepExp.loadByte
                (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 4#64]),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 1#64]))
                (Flapjack.CrepExp.const 8#64),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 2#64]))
                (Flapjack.CrepExp.const 16#64),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 3#64]))
                (Flapjack.CrepExp.const 24#64)])
          (Flapjack.CrepExp.const 32#64)]]

def crepBody776_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "rlp_word_encoded_len"
  [Flapjack.CrepExp.op Flapjack.BinOp.or
      [Flapjack.CrepExp.loadByte
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64]),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 1#64]))
          (Flapjack.CrepExp.const 8#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 2#64]))
          (Flapjack.CrepExp.const 16#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 3#64]))
          (Flapjack.CrepExp.const 24#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.op Flapjack.BinOp.or
            [Flapjack.CrepExp.loadByte
                (Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 4#64]),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 1#64]))
                (Flapjack.CrepExp.const 8#64),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 2#64]))
                (Flapjack.CrepExp.const 16#64),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 3#64]))
                (Flapjack.CrepExp.const 24#64)])
          (Flapjack.CrepExp.const 32#64)]]

def crepBody776_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_word_encoded_len"
  [Flapjack.CrepExp.op Flapjack.BinOp.or
      [Flapjack.CrepExp.loadByte
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 36#64]),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 1#64]))
          (Flapjack.CrepExp.const 8#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 2#64]))
          (Flapjack.CrepExp.const 16#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 3#64]))
          (Flapjack.CrepExp.const 24#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.op Flapjack.BinOp.or
            [Flapjack.CrepExp.loadByte
                (Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 4#64]),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 1#64]))
                (Flapjack.CrepExp.const 8#64),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 2#64]))
                (Flapjack.CrepExp.const 16#64),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 36#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 3#64]))
                (Flapjack.CrepExp.const 24#64)])
          (Flapjack.CrepExp.const 32#64)]]

def crepBody776_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 4]

def crepBody776_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]]

def crepBody776_5 : CrepProg (BitVec 64) :=
.seq crepBody776_3 crepBody776_4

def crepBody776_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody776_5

def crepBody776_7 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 21#64, Flapjack.CrepExp.var 3]) crepBody776_6

def crepBody776_8 : CrepProg (BitVec 64) :=
.seq crepBody776_2 crepBody776_7

def crepBody776_9 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody776_8

def crepBody776_10 : CrepProg (BitVec 64) :=
.seq crepBody776_1 crepBody776_9

def crepBody776_11 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody776_10

def crepBody776_12 : CrepProg (BitVec 64) :=
.seq crepBody776_0 crepBody776_11

def crepBody776_13 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody776_12

def data776 : CrepProg (BitVec 64) := crepBody776_13
def output776 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [119#8, 105#8, 116#8, 104#8, 100#8, 114#8, 97#8, 119#8, 97#8, 108#8, 95#8, 114#8, 108#8, 112#8, 95#8, 108#8, 101#8,
    110#8], [0], crepProgToHOL data776)
end InitECandidate.Proofs.FrontendStages.Crep
