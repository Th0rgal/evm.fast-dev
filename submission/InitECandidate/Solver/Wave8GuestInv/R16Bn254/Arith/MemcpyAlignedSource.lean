import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryWordEval
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memcpyAddress (name : String) (offset : Nat) : ExpHOL 64 :=
  .op .add ([polyDivVar name,polyDivVar "i"] ++ if offset = 0 then [] else [.const (BitVec.ofNat 64 offset)])
def memcpyWord (offset : Nat) : ProgHOL 64 :=
  .store (memcpyAddress "dst" offset) (.load .one (memcpyAddress "src" offset))
def memcpyIncrement : ProgHOL 64 :=
  .assign .local (ofString "i") (.op .add [polyDivVar "i",.const 32])
def memcpyAlignedBody : ProgHOL 64 :=
  .seq (memcpyWord 0) (.seq (memcpyWord 8) (.seq (memcpyWord 16) (.seq (memcpyWord 24) memcpyIncrement)))
def memcpyAlignedSourceBody : ProgHOL 64 :=
  match arithSourceBody Guest.Software.guestFn_memcpy with
  | .dec _ _ _ (.seq (.ite _ (.seq (.while _ body) _) _) _) => body
  | _ => .skip

theorem memcpyAligned_source_eq : memcpyAlignedSourceBody = memcpyAlignedBody := rfl

theorem memcpyAddress_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : String) (base index : BitVec 64) (offset : Nat)
    (hb : s.locals.lookup (ofString name) = some (.val (.word base)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word index))) :
    arithEval s (memcpyAddress name offset) = some (.val (.word (base + index + BitVec.ofNat 64 offset))) := by
  by_cases hz : offset = 0
  · subst offset
    simp [memcpyAddress,arithEval,polyDivVar,evalHOLExact,evalListHOLExact,hb,hi,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  · simp [memcpyAddress,hz,arithEval,polyDivVar,evalHOLExact,evalListHOLExact,hb,hi,
      wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc]

theorem memcpyWord_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src index word : BitVec 64) (offset : Nat)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (hd : s.memaddrs (dst + index + BitVec.ofNat 64 offset))
    (hs : s.memaddrs (src + index + BitVec.ofNat 64 offset))
    (hm : s.memory (src + index + BitVec.ofNat 64 offset) = .word word) :
    evaluateHOLFiniteState s (memcpyWord offset) =
      (none,{s with memory := writeMemoryWord s.memory (dst+index+BitVec.ofNat 64 offset) word}) := by
  apply eval_store_word
  · exact memcpyAddress_eval s "dst" dst index offset hdst hi
  · exact eval_load_word s _ _ word (memcpyAddress_eval s "src" src index offset hsrc hi) hs hm
  · exact hd

end InitECandidate.Solver.Wave8GuestInv.Arith
