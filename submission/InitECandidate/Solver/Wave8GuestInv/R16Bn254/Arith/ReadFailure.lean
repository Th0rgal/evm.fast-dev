import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryTouch

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

noncomputable abbrev arithEval {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :=
  @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e
noncomputable abbrev arithEvalList {F : Type} (s : PanSemStateFiniteExact 64 F) (es : List (ExpHOL 64)) :=
  @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es

theorem arith_evalList_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (es : List (ExpHOL 64))
    (hn : arithEval s e = none) (hm : e ∈ es) : arithEvalList s es = none := by
  induction es with
  | nil => simp at hm
  | cons first rest ih =>
    rcases List.mem_cons.mp hm with he | he
    · subst first
      simp [arithEvalList, evalListHOLExact, hn]
    · have ht := ih he
      simp only [arithEvalList, evalListHOLExact] at ht ⊢
      rw [ht]
      cases hh : arithEval s first <;> dsimp only [arithEval] at hh <;> rw [hh]

theorem arith_op_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (op : BinOp) (e : ExpHOL 64) (es : List (ExpHOL 64))
    (hn : arithEval s e = none) (hm : e ∈ es) : arithEval s (.op op es) = none := by
  have hl := arith_evalList_none s e es hn hm
  simp only [arithEval, evalHOLExact, hl]

theorem arith_shift_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (op : Shift) (e amount : ExpHOL 64) (hn : arithEval s e = none) :
    arithEval s (.shift op e amount) = none := by
  simp only [arithEval, evalHOLExact, hn]

theorem arith_loadByte_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (address : BitVec 64)
    (he : arithEval s e = some (.val (.word address)))
    (hn : ¬ s.memaddrs (panByteAlignHOL address)) : arithEval s (.loadByte e) = none := by
  cases hm : s.memory (panByteAlignHOL address) with
  | word w => simp [arithEval, evalHOLExact, he, panMemLoadByteHOL, hm, hn]

theorem arith_load_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (address : BitVec 64)
    (he : arithEval s e = some (.val (.word address)))
    (hn : ¬ s.memaddrs address) : arithEval s (.load .one e) = none := by
  simp [arithEval, evalHOLExact, isWfShapeExactHOL, he, memLoadHOLExact, hn]

/-- A failed prefix cannot become a normal function return. -/
def ReadFailure {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) : Prop :=
  (evaluateHOLFiniteState s p).1 = some .error ∨ (evaluateHOLFiniteState s p).1 = some .timeOut

theorem ReadFailure.seq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (first rest : ProgHOL 64) (h : ReadFailure s first) : ReadFailure s (.seq first rest) := by
  unfold ReadFailure at h ⊢
  rw [evaluateHOLFiniteState_seq_line780]
  cases hr : evaluateHOLFiniteState s first with
  | mk result post =>
    rw [hr] at h
    rcases h with h | h <;> simp only at h <;> subst result <;> simp

theorem ReadFailure.ite {F : Type} (s : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (yes no : ProgHOL 64)
    (hy : ReadFailure s yes) (hn : ReadFailure s no) : ReadFailure s (.ite condition yes no) := by
  unfold ReadFailure at *
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn
    · exact hy
  · simp

theorem ReadFailure.while {F : Type} (s : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (body : ProgHOL 64) (word : BitVec 64)
    (hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word word)))
    (hw : word ≠ 0) (hb : ReadFailure (decClockHOLFinite s) body) :
    ReadFailure s (.while condition body) := by
  unfold ReadFailure at hb ⊢
  rw [evaluateHOLFiniteState_while_fixClockRewrite, hc]
  simp only [if_pos hw]
  by_cases hz : s.clock = 0
  · simp [hz]
  · rw [if_neg hz]
    cases hr : evaluateHOLFiniteState (decClockHOLFinite s) body with
    | mk result post =>
      rw [hr] at hb
      rcases hb with h | h <;> simp only at h <;> subst result <;> simp

theorem ReadFailure.dec {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (e : ExpHOL 64) (body : ProgHOL 64) (v : ValueHOL 64)
    (he : arithEval s e = some v)
    (hb : ReadFailure (setVarHOLFinite name v s) body) :
    ReadFailure s (.dec name shape e body) := by
  unfold ReadFailure at hb ⊢
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  dsimp only [arithEval] at he
  rw [he]
  dsimp only
  split
  · exact hb
  · simp

theorem ReadFailure.dec_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (e : ExpHOL 64) (body : ProgHOL 64)
    (he : arithEval s e = none) : ReadFailure s (.dec name shape e body) := by
  unfold ReadFailure
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  dsimp only [arithEval] at he
  rw [he]
  simp

theorem ReadFailure.store_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (address value : ExpHOL 64) (hv : arithEval s value = none) :
    ReadFailure s (.store address value) := by
  unfold ReadFailure
  rw [evaluateHOLFiniteState_store]
  split
  · simp only [hv]; simp
  · simp

end InitECandidate.Solver.Wave8GuestInv.Arith
