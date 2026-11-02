import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpPhased
import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpWord

/-! RLP family, part 9: `_rlp_validate_items_body` (STACK loop) via the phased no-repeat rule.
Potential: `φ = if frame_mem_ptr ≤ scratch_ptr then scratch_ptr / 8 else 2^61` (see ISSUES.md §1);
key: `(pos, end, top)`; frame `R`: everything but `clock` and the locals `pos/end/top/go`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8Leaves.Rlp

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound

namespace Vib

@[simp] theorem ne_pos_end : ofString "pos" ≠ ofString "end" := by decide
@[simp] theorem ne_pos_top : ofString "pos" ≠ ofString "top" := by decide
@[simp] theorem ne_pos_go : ofString "pos" ≠ ofString "go" := by decide
@[simp] theorem ne_pos_h : ofString "pos" ≠ ofString "h" := by decide
@[simp] theorem ne_pos_payload : ofString "pos" ≠ ofString "payload" := by decide
@[simp] theorem ne_pos_after : ofString "pos" ≠ ofString "after" := by decide
@[simp] theorem ne_pos_rec : ofString "pos" ≠ ofString "rec" := by decide
@[simp] theorem ne_pos_p : ofString "pos" ≠ ofString "p" := by decide
@[simp] theorem ne_pos_len : ofString "pos" ≠ ofString "len" := by decide
@[simp] theorem ne_end_pos : ofString "end" ≠ ofString "pos" := by decide
@[simp] theorem ne_end_top : ofString "end" ≠ ofString "top" := by decide
@[simp] theorem ne_end_go : ofString "end" ≠ ofString "go" := by decide
@[simp] theorem ne_end_h : ofString "end" ≠ ofString "h" := by decide
@[simp] theorem ne_end_payload : ofString "end" ≠ ofString "payload" := by decide
@[simp] theorem ne_end_after : ofString "end" ≠ ofString "after" := by decide
@[simp] theorem ne_end_rec : ofString "end" ≠ ofString "rec" := by decide
@[simp] theorem ne_end_p : ofString "end" ≠ ofString "p" := by decide
@[simp] theorem ne_end_len : ofString "end" ≠ ofString "len" := by decide
@[simp] theorem ne_top_pos : ofString "top" ≠ ofString "pos" := by decide
@[simp] theorem ne_top_end : ofString "top" ≠ ofString "end" := by decide
@[simp] theorem ne_top_go : ofString "top" ≠ ofString "go" := by decide
@[simp] theorem ne_top_h : ofString "top" ≠ ofString "h" := by decide
@[simp] theorem ne_top_payload : ofString "top" ≠ ofString "payload" := by decide
@[simp] theorem ne_top_after : ofString "top" ≠ ofString "after" := by decide
@[simp] theorem ne_top_rec : ofString "top" ≠ ofString "rec" := by decide
@[simp] theorem ne_top_p : ofString "top" ≠ ofString "p" := by decide
@[simp] theorem ne_top_len : ofString "top" ≠ ofString "len" := by decide
@[simp] theorem ne_go_pos : ofString "go" ≠ ofString "pos" := by decide
@[simp] theorem ne_go_end : ofString "go" ≠ ofString "end" := by decide
@[simp] theorem ne_go_top : ofString "go" ≠ ofString "top" := by decide
@[simp] theorem ne_go_h : ofString "go" ≠ ofString "h" := by decide
@[simp] theorem ne_go_payload : ofString "go" ≠ ofString "payload" := by decide
@[simp] theorem ne_go_after : ofString "go" ≠ ofString "after" := by decide
@[simp] theorem ne_go_rec : ofString "go" ≠ ofString "rec" := by decide
@[simp] theorem ne_go_p : ofString "go" ≠ ofString "p" := by decide
@[simp] theorem ne_go_len : ofString "go" ≠ ofString "len" := by decide
@[simp] theorem ne_h_pos : ofString "h" ≠ ofString "pos" := by decide
@[simp] theorem ne_h_end : ofString "h" ≠ ofString "end" := by decide
@[simp] theorem ne_h_top : ofString "h" ≠ ofString "top" := by decide
@[simp] theorem ne_h_go : ofString "h" ≠ ofString "go" := by decide
@[simp] theorem ne_h_payload : ofString "h" ≠ ofString "payload" := by decide
@[simp] theorem ne_h_after : ofString "h" ≠ ofString "after" := by decide
@[simp] theorem ne_h_rec : ofString "h" ≠ ofString "rec" := by decide
@[simp] theorem ne_h_p : ofString "h" ≠ ofString "p" := by decide
@[simp] theorem ne_h_len : ofString "h" ≠ ofString "len" := by decide
@[simp] theorem ne_payload_pos : ofString "payload" ≠ ofString "pos" := by decide
@[simp] theorem ne_payload_end : ofString "payload" ≠ ofString "end" := by decide
@[simp] theorem ne_payload_top : ofString "payload" ≠ ofString "top" := by decide
@[simp] theorem ne_payload_go : ofString "payload" ≠ ofString "go" := by decide
@[simp] theorem ne_payload_h : ofString "payload" ≠ ofString "h" := by decide
@[simp] theorem ne_payload_after : ofString "payload" ≠ ofString "after" := by decide
@[simp] theorem ne_payload_rec : ofString "payload" ≠ ofString "rec" := by decide
@[simp] theorem ne_payload_p : ofString "payload" ≠ ofString "p" := by decide
@[simp] theorem ne_payload_len : ofString "payload" ≠ ofString "len" := by decide
@[simp] theorem ne_after_pos : ofString "after" ≠ ofString "pos" := by decide
@[simp] theorem ne_after_end : ofString "after" ≠ ofString "end" := by decide
@[simp] theorem ne_after_top : ofString "after" ≠ ofString "top" := by decide
@[simp] theorem ne_after_go : ofString "after" ≠ ofString "go" := by decide
@[simp] theorem ne_after_h : ofString "after" ≠ ofString "h" := by decide
@[simp] theorem ne_after_payload : ofString "after" ≠ ofString "payload" := by decide
@[simp] theorem ne_after_rec : ofString "after" ≠ ofString "rec" := by decide
@[simp] theorem ne_after_p : ofString "after" ≠ ofString "p" := by decide
@[simp] theorem ne_after_len : ofString "after" ≠ ofString "len" := by decide
@[simp] theorem ne_rec_pos : ofString "rec" ≠ ofString "pos" := by decide
@[simp] theorem ne_rec_end : ofString "rec" ≠ ofString "end" := by decide
@[simp] theorem ne_rec_top : ofString "rec" ≠ ofString "top" := by decide
@[simp] theorem ne_rec_go : ofString "rec" ≠ ofString "go" := by decide
@[simp] theorem ne_rec_h : ofString "rec" ≠ ofString "h" := by decide
@[simp] theorem ne_rec_payload : ofString "rec" ≠ ofString "payload" := by decide
@[simp] theorem ne_rec_after : ofString "rec" ≠ ofString "after" := by decide
@[simp] theorem ne_rec_p : ofString "rec" ≠ ofString "p" := by decide
@[simp] theorem ne_rec_len : ofString "rec" ≠ ofString "len" := by decide
@[simp] theorem ne_p_pos : ofString "p" ≠ ofString "pos" := by decide
@[simp] theorem ne_p_end : ofString "p" ≠ ofString "end" := by decide
@[simp] theorem ne_p_top : ofString "p" ≠ ofString "top" := by decide
@[simp] theorem ne_p_go : ofString "p" ≠ ofString "go" := by decide
@[simp] theorem ne_p_h : ofString "p" ≠ ofString "h" := by decide
@[simp] theorem ne_p_payload : ofString "p" ≠ ofString "payload" := by decide
@[simp] theorem ne_p_after : ofString "p" ≠ ofString "after" := by decide
@[simp] theorem ne_p_rec : ofString "p" ≠ ofString "rec" := by decide
@[simp] theorem ne_p_len : ofString "p" ≠ ofString "len" := by decide
@[simp] theorem ne_len_pos : ofString "len" ≠ ofString "pos" := by decide
@[simp] theorem ne_len_end : ofString "len" ≠ ofString "end" := by decide
@[simp] theorem ne_len_top : ofString "len" ≠ ofString "top" := by decide
@[simp] theorem ne_len_go : ofString "len" ≠ ofString "go" := by decide
@[simp] theorem ne_len_h : ofString "len" ≠ ofString "h" := by decide
@[simp] theorem ne_len_payload : ofString "len" ≠ ofString "payload" := by decide
@[simp] theorem ne_len_after : ofString "len" ≠ ofString "after" := by decide
@[simp] theorem ne_len_rec : ofString "len" ≠ ofString "rec" := by decide
@[simp] theorem ne_len_p : ofString "len" ≠ ofString "p" := by decide

def wl (w : BitVec 64) : Option (ValueHOL 64) := some (.val (.word w))

/-- Fields every evaluation preserves. -/
theorem evalMeta {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) :
    (evaluateHOLFiniteState s p).2.code = s.code ∧
    (evaluateHOLFiniteState s p).2.memaddrs = s.memaddrs ∧
    (evaluateHOLFiniteState s p).2.shMemaddrs = s.shMemaddrs ∧
    (evaluateHOLFiniteState s p).2.be = s.be ∧
    (evaluateHOLFiniteState s p).2.eshapes = s.eshapes ∧
    (evaluateHOLFiniteState s p).2.baseAddr = s.baseAddr ∧
    (evaluateHOLFiniteState s p).2.structs = s.structs := by
  have hm := evaluateHOLFiniteState_metadata s p
  have invariant := evaluateInvariantsHOLFinite p
    (PanPropsEvalStateFiniteExact.ofPanSemFinite s)
    (evaluateHOLFiniteState s p).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState s p).2) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact ⟨hm.1, hm.2.1, hm.2.2.2.1, hm.2.2.1, hm.2.2.2.2, invariant.2.2.2.2.1, invariant.2.2.2.2.2.1⟩

def pop : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
    (.assign .local (ofString "go") (.const 0))
    (.seq (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
      (.seq (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
        (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16])))))

def pushTail : ProgHOL 64 :=
  .seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
    (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
      (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
        (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
          (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
            (.assign .local (ofString "end") (.var .local (ofString "after")))))))

def push : ProgHOL 64 :=
  .decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24] pushTail

def cont : ProgHOL 64 :=
  .dec (ofString "payload") .one
    (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
    (.dec (ofString "after") .one
      (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))])
      (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
        push
        (.assign .local (ofString "pos") (.var .local (ofString "after")))))

def hdrShape : ShapeHOL :=
  .comb (InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural
    [Shape.one, Shape.one, Shape.one])

def item : ProgHOL 64 :=
  .decCall (ofString "h") hdrShape (ofString "rlp_item_header")
    [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]]
    cont

def body : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end"))) pop item

def cond : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "go")) (.const 0)

/-! ### `rlp_item_header` is read-only -/

def hdrGood (f : MlS) : Bool := f == ofString "rlp_fail" || f == ofString "rlp_read_length"

theorem hdrGood_ro : ∀ function, hdrGood function = true → ∀ values body callee rs,
    PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
      some (body, callee, rs) → roProg hdrGood body = true := by
  intro function hf values body callee rs hl
  simp only [hdrGood, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 105 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_fail) rfl) hl
    subst hb
    rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 106 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_read_length) rfl) hl
    subst hb
    rfl

theorem hdr_body_ro : ∀ values body callee rs,
    PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_item_header")
      values = some (body, callee, rs) → roProg hdrGood body = true := by
  intro values body callee rs hl
  have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
    (lookup_of_guestAst_getElem 109 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_rlp_item_header) rfl) hl
  subst hb
  rfl

/-! ### `scratch_alloc` -/

/-- A `returned` run of `scratch_alloc` with `scratch_ptr = p`, `frame_mem_ptr = f`, `n` passed
both trap tests and set `scratch_ptr := q = (p - n) & ~7`, leaving memory and `frame_mem_ptr`. -/
theorem evaluate_scratch_alloc_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p f n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf_lookup : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)
    let q := (p - n) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word q) ∧
      out.2.globals.lookup (ofString "scratch_ptr") = some (.val (.word q)) ∧
      out.2.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) ∧
      ¬ ((p - f).toNat < n.toNat) ∧ ¬ (q.toNat < f.toNat) ∧
      out.2.memory = state.memory := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_scratch_alloc =
      .dec (ofString "p") .one (.var .global (ofString "scratch_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const 7])
                .skip)
              (.seq
                (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "scratch_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only
  rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only
  rw [if_pos hsh_p]
  dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  have hf_g : pState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) := hf_lookup
  have hcode_p : pState.code = originalRuntimeCode := hcode
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (p - f).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc, hf_g,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (p - f).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 7])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 7]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState 7 hcode_p
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 7 w hcode_p
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some r1' =>
      intro retVal hret
      exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 7])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]
    dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p - n) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
        ↓reduceIte, List.foldr]
      simp [q]
      rw [show AndOp.and (18446744073709551608#64) (18446744073709551615#64) = (18446744073709551608#64)
        by decide]
      rfl
    dsimp only
    rw [hq_eval]
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only
    rw [if_pos hsh_q]
    dsimp only
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hcode_q : qState.code = originalRuntimeCode := hcode
    have hf_q : qState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) := hf_lookup
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr"))) =
        some (.val (.word (if q.toNat < f.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, hf_q, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
        decide_eq_true_eq]
    by_cases hcmp2 : q.toNat < f.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 7]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none qState 7 hcode_q
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 7 w hcode_q
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some r2' =>
        intro retVal hret
        exact False.elim (hno_ret retVal hret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "q")))) =
          (some (.returned (.val (.word q))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      intro retVal hret
      injection hret with hr
      injection hr with hr'
      refine ⟨hr'.symm, ?_, ?_, hcmp1, hcmp2, rfl⟩
      · simp only [emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          ↓reduceIte]
        rfl
      · simp only [emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "frame_mem_ptr" ≠ ofString "scratch_ptr" by decide, ↓reduceIte]
        exact hf_q

/-! ### Congruences used to fix the branch of `cont` -/

theorem dec_congr {F : Type} {name : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {b1 b2 : ProgHOL 64}
    (x : MlS) (X : Option (ValueHOL 64)) (hne : name ≠ x)
    (hb : ∀ s' : PanSemStateFiniteExact 64 F, s'.locals.lookup x = X →
      evaluateHOLFiniteState s' b1 = evaluateHOLFiniteState s' b2)
    (s : PanSemStateFiniteExact 64 F) (hs : s.locals.lookup x = X) :
    evaluateHOLFiniteState s (.dec name sh e b1) = evaluateHOLFiniteState s (.dec name sh e b2) := by
  rw [evaluateHOLFiniteState_dec_total, evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · split
    · rename_i v _ _
      have := hb (setVarHOLFinite name v s)
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs])
      rw [this]
    · rfl

theorem ite_word_congr {F : Type} {c : ExpHOL 64} {a b : ProgHOL 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hc : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w))) :
    evaluateHOLFiniteState s (.ite c a b) =
      if w = 0 then evaluateHOLFiniteState s b else evaluateHOLFiniteState s a := by
  rw [evaluateHOLFiniteState_ite, hc]

def asg : ProgHOL 64 := .assign .local (ofString "pos") (.var .local (ofString "after"))

def contWith (q : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "payload") .one
    (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
    (.dec (ofString "after") .one
      (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))]) q)

def hval (a b c : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word a), .val (.word b), .val (.word c)]

theorem cont_branch {F : Type} (u : PanSemStateFiniteExact 64 F) (a b c : BitVec 64)
    (hu : u.locals.lookup (ofString "h") = some (hval a b c)) :
    evaluateHOLFiniteState u cont =
      if c = 0 then evaluateHOLFiniteState u (contWith asg)
      else evaluateHOLFiniteState u (contWith push) := by
  have key : ∀ s' : PanSemStateFiniteExact 64 F, s'.locals.lookup (ofString "h") = some (hval a b c) →
      evaluateHOLFiniteState s' (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
        push (.assign .local (ofString "pos") (.var .local (ofString "after")))) = if c = 0 then evaluateHOLFiniteState s' asg else evaluateHOLFiniteState s' push := by
    intro s' hs'
    rw [ite_word_congr s' (if c = 0 then 0 else 1)]
    · by_cases hc : c = 0 <;> simp [hc, asg]
    · by_cases hc : c = 0 <;>
        simp [evalHOLExact, hs', hval, Compiler.Encoders.Asm.wordCmpHOL, hc]
  by_cases hc : c = 0
  · rw [if_pos hc]
    refine dec_congr (ofString "h") _ (by decide) ?_ u hu
    intro s1 hs1
    refine dec_congr (ofString "h") _ (by decide) ?_ s1 hs1
    intro s2 hs2
    rw [key s2 hs2, if_pos hc]
  · rw [if_neg hc]
    refine dec_congr (ofString "h") _ (by decide) ?_ u hu
    intro s1 hs1
    refine dec_congr (ofString "h") _ (by decide) ?_ s1 hs1
    intro s2 hs2
    rw [key s2 hs2, if_neg hc]

theorem hdr_value (v : ValueHOL 64) (h : shapeEqHOL (shapeOfHOLExact v) hdrShape = true) :
    ∃ a b c, v = hval a b c := by
  rcases v with ⟨⟨w⟩⟩ | fs | ⟨n, fs⟩
  · simp [shapeOfHOLExact, shapeEqHOL, hdrShape,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural] at h
  · rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, fs⟩⟩⟩⟩ <;>
      simp [shapeOfHOLExact, shapeEqHOL, hdrShape, shapeEqHOL.shapeEqListHOL,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural] at h
    obtain ⟨h0, h1, h2⟩ := h
    obtain ⟨a, rfl⟩ := shape_one_word f0 (by simpa [shapeEqHOL] using h0)
    obtain ⟨b, rfl⟩ := shape_one_word f1 (by simpa [shapeEqHOL] using h1)
    obtain ⟨c, rfl⟩ := shape_one_word f2 (by simpa [shapeEqHOL] using h2)
    exact ⟨a, b, c, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL, hdrShape,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural] at h

theorem sa_callee (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "scratch_alloc")
      [.val (.word 24)] = some (body, callee, rs)) :
    body = sourceFnBody Guest.Software.guestFn_scratch_alloc ∧
      callee.lookup (ofString "n") = some (.val (.word 24)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · simp at hl
  · rename_i b cl r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    simp [lookupCodeHOLExact, lookup_scratch_alloc, shapeEqHOL, shapeOfHOLExact] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp

/-! ### The push branch lowers the scratch potential -/

def sp : MlS := ofString "scratch_ptr"
def fmp : MlS := ofString "frame_mem_ptr"

theorem pushTail_keeps {F : Type} (watched : MlS) (t : PanSemStateFiniteExact 64 F)
    (hcode : t.code = originalRuntimeCode) :
    (evaluateHOLFiniteState t pushTail).2.globals.lookup watched = t.globals.lookup watched :=
  InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG watched (fun _ => false)
    (fun _ h => by simp at h) pushTail rfl t hcode


/-- A `returned` run of `scratch_alloc` forces both pointer globals to be words. -/
theorem scratch_alloc_words {F : Type} (state : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hret : (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)).1 =
      some (.returned retVal)) :
    (∃ p, state.globals.lookup sp = some (.val (.word p))) ∧
      (∃ f, state.globals.lookup fmp = some (.val (.word f))) := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_scratch_alloc =
      .dec (ofString "p") .one (.var .global (ofString "scratch_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const 7])
                .skip)
              (.seq
                (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  have hsp : ∃ p, state.globals.lookup sp = some (.val (.word p)) := by
    rcases hg : state.globals.lookup (ofString "scratch_ptr") with _ | ⟨⟨p⟩⟩ | fs | ⟨n, fs⟩
    · simp [evalHOLExact, hg] at hret
    · exact ⟨p, hg⟩
    · simp [evalHOLExact, hg, shapeEqHOL, shapeOfHOLExact] at hret
    · simp [evalHOLExact, hg, shapeEqHOL, shapeOfHOLExact] at hret
  obtain ⟨p, hp⟩ := hsp
  refine ⟨⟨p, hp⟩, ?_⟩
  have hpe : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "scratch_ptr")) = some (.val (.word p)) := hp
  rw [hpe] at hret
  simp only [shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hret
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  rcases hg : state.globals.lookup (ofString "frame_mem_ptr") with _ | ⟨⟨f⟩⟩ | fs | ⟨n, fs⟩
  · simp [evalHOLExact, evalListHOLExact, hg, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, fixClockHOLFinite] at hret
  · exact ⟨f, hg⟩
  · simp [evalHOLExact, evalListHOLExact, hg, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, fixClockHOLFinite, valueIsWord] at hret
  · simp [evalHOLExact, evalListHOLExact, hg, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, fixClockHOLFinite, valueIsWord] at hret

theorem push_run {F : Type} (u : PanSemStateFiniteExact 64 F) (hcode : u.code = originalRuntimeCode)
    (hflow : (evaluateHOLFiniteState u push).1 = none) :
    ∃ p f q : BitVec 64, u.globals.lookup sp = some (.val (.word p)) ∧
      u.globals.lookup fmp = some (.val (.word f)) ∧
      (evaluateHOLFiniteState u push).2.globals.lookup sp = some (.val (.word q)) ∧
      (evaluateHOLFiniteState u push).2.globals.lookup fmp = some (.val (.word f)) ∧
      f.toNat ≤ q.toNat ∧ (f.toNat ≤ p.toNat → q.toNat + 24 ≤ p.toNat) := by
  unfold push at hflow ⊢
  rw [evaluateHOLFiniteState_decCall_total] at hflow ⊢
  have hargs : evalListHOLFinite u (h := fun address => Classical.propDecidable (u.memaddrs address))
      [ExpHOL.const (24 : BitVec 64)] = some [.val (.word 24#64)] := by
    simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact]
  simp only [hargs] at hflow ⊢
  rcases hl : lookupCodeHOLFinite u.code.lookup (ofString "scratch_alloc") [.val (.word 24#64)] with
    _ | ⟨body, callee, rs⟩
  · simp [hl] at hflow
  simp only [hl] at hflow ⊢
  rw [hcode] at hl
  obtain ⟨rfl, hn⟩ := sa_callee body callee rs hl
  by_cases hz : u.clock = 0
  · simp [hz] at hflow
  simp only [hz, ↓reduceIte] at hflow ⊢
  rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite u callee)
      (sourceFnBody Guest.Software.guestFn_scratch_alloc) with ⟨r, st⟩
  simp only [hrun] at hflow ⊢
  cases r with
  | none => simp at hflow
  | some r =>
    cases r with
    | returned v =>
      obtain ⟨⟨p, hp⟩, ⟨f, hf⟩⟩ := scratch_alloc_words (callEntryStateHOLFinite u callee) v (by rw [hrun])
      have hsa := evaluate_scratch_alloc_body (callEntryStateHOLFinite u callee) p f 24 hcode hp hf hn
      dsimp only at hsa
      rw [hrun] at hsa
      obtain ⟨rfl, hq, hfq, hc1, hc2, _⟩ := hsa v rfl
      have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite u callee)
        (sourceFnBody Guest.Software.guestFn_scratch_alloc)).1
      rw [hrun] at hmeta
      change st.code = u.code at hmeta
      dsimp only at hflow ⊢
      split
      · refine ⟨p, f, (p - 24) &&& ((0 : BitVec 64) - 8), hp, hf, ?_, ?_, ?_, ?_⟩
        · rw [pushTail_keeps sp _ (by simp [setVarHOLFinite, fixClockHOLFinite, hmeta, hcode])]
          simpa [setVarHOLFinite, fixClockHOLFinite, sp] using hq
        · rw [pushTail_keeps fmp _ (by simp [setVarHOLFinite, fixClockHOLFinite, hmeta, hcode])]
          simpa [setVarHOLFinite, fixClockHOLFinite, fmp] using hfq
        · omega
        · intro hle
          have h24 : (24 : BitVec 64).toNat = 24 := rfl
          have hsub : (p - f).toNat = p.toNat - f.toNat := by
            rw [BitVec.toNat_sub]; have := p.isLt; have := f.isLt; omega
          rw [h24] at hc1
          have hp24 : (p - 24).toNat = p.toNat - 24 := by
            rw [BitVec.toNat_sub]; have := p.isLt; simp; omega
          have := and_neg8_toNat (p - 24)
          omega
      · rename_i hsh
        rw [if_neg hsh] at hflow
        simp at hflow
    | _ => simp at hflow

theorem contWith_flow {F : Type} (u : PanSemStateFiniteExact 64 F) (q : ProgHOL 64)
    (hflow : (evaluateHOLFiniteState u (contWith q)).1 = none) :
    ∃ u2 : PanSemStateFiniteExact 64 F, u2.globals = u.globals ∧ u2.code = u.code ∧
      (evaluateHOLFiniteState u2 q).1 = none ∧
      (evaluateHOLFiniteState u (contWith q)).2.globals = (evaluateHOLFiniteState u2 q).2.globals := by
  unfold contWith at hflow ⊢
  rw [evaluateHOLFiniteState_dec_total] at hflow ⊢
  dsimp only at hflow ⊢
  split at hflow
  · simp at hflow
  · rename_i v1 hv1
    try rw [hv1] at *
    try dsimp only at hflow ⊢
    split at hflow
    · rename_i hs1
      rw [if_pos hs1]
      try dsimp only at hflow ⊢
      rw [evaluateHOLFiniteState_dec_total] at hflow ⊢
      try dsimp only at hflow ⊢
      split at hflow
      · simp at hflow
      · rename_i v2 hv2
        try rw [hv2]
        try dsimp only at hflow ⊢
        split at hflow
        · rename_i hs2
          rw [if_pos hs2]
          exact ⟨setVarHOLFinite (ofString "after") v2 (setVarHOLFinite (ofString "payload") v1 u),
            rfl, rfl, by simpa using hflow, rfl⟩
        · simp at hflow
    · simp at hflow

theorem item_step {F : Type} (t : PanSemStateFiniteExact 64 F) (hcode : t.code = originalRuntimeCode)
    (hflow : (evaluateHOLFiniteState t item).1 = none) :
    Frame t (evaluateHOLFiniteState t item).2 ∨
    ∃ p f q : BitVec 64, t.globals.lookup sp = some (.val (.word p)) ∧
      t.globals.lookup fmp = some (.val (.word f)) ∧
      (evaluateHOLFiniteState t item).2.globals.lookup sp = some (.val (.word q)) ∧
      (evaluateHOLFiniteState t item).2.globals.lookup fmp = some (.val (.word f)) ∧
      f.toNat ≤ q.toNat ∧ (f.toNat ≤ p.toNat → q.toNat + 24 ≤ p.toNat) := by
  revert hflow
  unfold item
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · simp
  rename_i values _
  split
  · simp
  rename_i fb callee rs hl
  have hro := hdr_body_ro values fb callee rs (by rw [← hcode]; exact hl)
  split
  · simp
  rename_i hz
  intro hflow
  have hfr := evaluate_ro hdrGood hdrGood_ro fb hro (callEntryStateHOLFinite t callee) hcode
  have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) fb).1
  rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) fb with ⟨r, st⟩
  rw [hrun] at hfr hmeta
  change st.code = t.code at hmeta
  simp only [hrun] at hflow ⊢
  cases r with
  | none => simp at hflow
  | some r =>
    cases r with
    | returned v =>
      dsimp only at hflow ⊢
      split
      · rename_i hsh
        simp only [Bool.and_eq_true] at hsh
        obtain ⟨a, b, c, rfl⟩ := hdr_value v hsh.1
        rw [if_pos (by simpa using hsh)] at hflow
        dsimp only at hflow ⊢
        set u := setVarHOLFinite (ofString "h") (hval a b c)
          { (fixClockHOLFinite (callEntryStateHOLFinite t callee) (some (PanSemResultExact.returned (hval a b c)), st)).2 with
            locals := t.locals } with hu_def
        have hu : u.locals.lookup (ofString "h") = some (hval a b c) := by
          simp [hu_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hucode : u.code = originalRuntimeCode := by
          simp [hu_def, setVarHOLFinite, fixClockHOLFinite, hmeta, hcode]
        rw [cont_branch u a b c hu] at hflow ⊢
        by_cases hc : c = 0
        · rw [if_pos hc] at hflow ⊢
          left
          have hro2 := evaluate_ro (fun _ => false) (fun _ h => by simp at h) (contWith asg) rfl u hucode
          exact ⟨hro2.1.trans hfr.1, hro2.2.1.trans hfr.2.1, hro2.2.2.1.trans hfr.2.2.1,
            hro2.2.2.2.trans hfr.2.2.2⟩
        · rw [if_neg hc] at hflow ⊢
          right
          obtain ⟨u2, hg2, hc2, hf2, hgl⟩ := contWith_flow u push hflow
          obtain ⟨p, f, q, hp, hf, hq, hfq, h1, h2⟩ := push_run u2 (hc2.trans hucode) hf2
          have hug : u.globals = t.globals := by
            simp only [hu_def, setVarHOLFinite, fixClockHOLFinite]; exact hfr.2.1
          refine ⟨p, f, q, ?_, ?_, ?_, ?_, h1, h2⟩
          · rw [← hug, ← hg2]; exact hp
          · rw [← hug, ← hg2]; exact hf
          · show (evaluateHOLFiniteState u (contWith push)).2.globals.lookup sp = _
            rw [hgl]; exact hq
          · show (evaluateHOLFiniteState u (contWith push)).2.globals.lookup fmp = _
            rw [hgl]; exact hfq
      · rename_i hsh
        rw [if_neg hsh] at hflow
        simp at hflow
    | _ => simp at hflow

/-! ### Loop invariant, frame relation, potential and key -/

def keyLoc (k : MlS) : Prop :=
  k ≠ ofString "pos" ∧ k ≠ ofString "end" ∧ k ≠ ofString "top" ∧ k ≠ ofString "go"

def Words {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  WordLocal (ofString "pos") s ∧ WordLocal (ofString "end") s ∧ WordLocal (ofString "top") s

def Pinv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s => GuestInv s ∧ Words s

def Rel : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s t => Words s ∧ Words t ∧ t.memory = s.memory ∧ t.globals = s.globals ∧ t.ffi = s.ffi ∧
    t.topAddr = s.topAddr ∧ t.code = s.code ∧ t.memaddrs = s.memaddrs ∧
    t.shMemaddrs = s.shMemaddrs ∧ t.be = s.be ∧ t.eshapes = s.eshapes ∧ t.baseAddr = s.baseAddr ∧
    t.structs = s.structs ∧ (∀ k, keyLoc k → t.locals.lookup k = s.locals.lookup k) ∧
    (t.locals.lookup (ofString "go") = s.locals.lookup (ofString "go") ∨
      t.locals.lookup (ofString "go") = some (.val (.word 0)))

def phi : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat := fun s =>
  match s.globals.lookup sp, s.globals.lookup fmp with
  | some (.val (.word p)), some (.val (.word f)) => if f.toNat ≤ p.toNat then p.toNat / 8 else 2 ^ 61
  | _, _ => 2 ^ 61

theorem phi_le {F : Type} (s : PanSemStateFiniteExact 64 F) : phi s ≤ 2 ^ 61 := by
  unfold phi
  split
  · rename_i p f _ _
    split
    · have := p.isLt; omega
    · exact le_refl _
  · exact le_refl _

def kappa : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin (2 ^ 192) := fun s =>
  match s.locals.lookup (ofString "pos"), s.locals.lookup (ofString "end"),
      s.locals.lookup (ofString "top") with
  | some (.val (.word a)), some (.val (.word b)), some (.val (.word c)) =>
      ⟨a.toNat * 2 ^ 128 + b.toNat * 2 ^ 64 + c.toNat, by
        have := a.isLt; have := b.isLt; have := c.isLt; omega⟩
  | _, _, _ => ⟨0, by decide⟩

theorem Rel_trans {F : Type} (a b c : PanSemStateFiniteExact 64 F) (h1 : Rel a b) (h2 : Rel b c) :
    Rel a c := by
  obtain ⟨wa, _, m1, g1, f1, t1, c1, ma1, sh1, be1, es1, ba1, st1, k1, go1⟩ := h1
  obtain ⟨_, wc, m2, g2, f2, t2, c2, ma2, sh2, be2, es2, ba2, st2, k2, go2⟩ := h2
  refine ⟨wa, wc, m2.trans m1, g2.trans g1, f2.trans f1, t2.trans t1, c2.trans c1, ma2.trans ma1,
    sh2.trans sh1, be2.trans be1, es2.trans es1, ba2.trans ba1, st2.trans st1,
    fun k hk => (k2 k hk).trans (k1 k hk), ?_⟩
  rcases go2 with h | h
  · rw [h]; exact go1
  · exact Or.inr h

theorem go_of_active {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PanTerminatingNoRepeat.LoopActive cond s) :
    ∃ g : BitVec 64, s.locals.lookup (ofString "go") = some (.val (.word g)) ∧ g ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := h
  simp only [cond, evalHOLFinite_eq_toExact, evalHOLExact] at hw
  rcases hg : s.locals.lookup (ofString "go") with _ | ⟨⟨g⟩⟩ | fs | ⟨n, fs⟩ <;> simp [hg] at hw
  refine ⟨g, rfl, ?_⟩
  intro hg0
  subst hg0
  simp [Compiler.Encoders.Asm.wordCmpHOL] at hw
  exact hw0 hw.symm

theorem Rel_key {F : Type} (a b : PanSemStateFiniteExact 64 F) (hR : Rel a b)
    (ha : PanTerminatingNoRepeat.LoopActive cond a) (hb : PanTerminatingNoRepeat.LoopActive cond b)
    (hk : kappa a = kappa b) : b = { a with clock := b.clock } := by
  obtain ⟨⟨⟨pa, hpa⟩, ⟨ea, hea⟩, ⟨ta, hta⟩⟩, ⟨⟨pb, hpb⟩, ⟨eb, heb⟩, ⟨tb, htb⟩⟩, m1, g1, f1, t1, c1, ma1,
    sh1, be1, es1, ba1, st1, k1, go1⟩ := hR
  obtain ⟨ga, hga, hga0⟩ := go_of_active a ha
  obtain ⟨gb, hgb, hgb0⟩ := go_of_active b hb
  have hgo : b.locals.lookup (ofString "go") = a.locals.lookup (ofString "go") := by
    rcases go1 with h | h
    · exact h
    · rw [hgb] at h; simp at h; exact absurd h hgb0
  simp only [kappa, hpa, hea, hta, hpb, heb, htb, Fin.mk.injEq] at hk
  have hp := pa.isLt; have he := ea.isLt; have ht := ta.isLt
  have hp' := pb.isLt; have he' := eb.isLt; have ht' := tb.isLt
  have e1 : pa.toNat = pb.toNat := by omega
  have e2 : ea.toNat = eb.toNat := by omega
  have e3 : ta.toNat = tb.toNat := by omega
  have hloc : b.locals = a.locals := by
    apply Flapjack.HolFiniteMapExact.ext_lookup
    intro k
    by_cases kp : k = ofString "pos"
    · subst kp; rw [hpa, hpb, BitVec.eq_of_toNat_eq e1]
    by_cases ke : k = ofString "end"
    · subst ke; rw [hea, heb, BitVec.eq_of_toNat_eq e2]
    by_cases kt : k = ofString "top"
    · subst kt; rw [hta, htb, BitVec.eq_of_toNat_eq e3]
    by_cases kg : k = ofString "go"
    · subst kg; exact hgo
    exact k1 k ⟨kp, ke, kt, kg⟩
  cases a; cases b
  simp only at m1 g1 f1 t1 c1 ma1 sh1 be1 es1 ba1 st1 hloc ⊢
  subst m1 g1 f1 t1 c1 ma1 sh1 be1 es1 ba1 st1 hloc
  rfl

/-! ### One iteration -/

theorem body_avoids (k : MlS) (hk : keyLoc k) : avoidsLocal k body = true := by
  obtain ⟨h1, h2, h3, h4⟩ := hk
  simp [body, pop, item, cont, push, pushTail, avoidsLocal, beq_iff_eq, Ne.symm h1, Ne.symm h2,
    Ne.symm h3, Ne.symm h4]

theorem item_avoids_go : avoidsLocal (ofString "go") item = true := by
  simp [item, cont, push, pushTail, avoidsLocal, beq_iff_eq]

theorem pop_go {F : Type} (t : PanSemStateFiniteExact 64 F)
    (hflow : (evaluateHOLFiniteState t pop).1 = none) :
    (evaluateHOLFiniteState t pop).2.locals.lookup (ofString "go") = t.locals.lookup (ofString "go") ∨
      (evaluateHOLFiniteState t pop).2.locals.lookup (ofString "go") = some (.val (.word 0)) := by
  revert hflow
  unfold pop
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i w _
    split
    · intro hflow
      left
      exact evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal, beq_iff_eq]) t (Or.inl hflow)
    · rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · rename_i v hv
        split
        · intro _
          right
          simp [evalHOLExact] at hv
          subst hv
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp
  · simp

theorem cond1_eval {F : Type} (t : PanSemStateFiniteExact 64 F) (P E : BitVec 64)
    (hp : t.locals.lookup (ofString "pos") = some (.val (.word P)))
    (he : t.locals.lookup (ofString "end") = some (.val (.word E))) :
    @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x))
      (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end"))) =
      some (.val (.word (if P = E then 1 else 0))) := by
  by_cases h : P = E <;> simp [evalHOLExact, hp, he, Compiler.Encoders.Asm.wordCmpHOL, h]

theorem step {F : Type} (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (hP : Pinv s) (hclk : s.clock ≠ 0)
    (hflow : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) :
    Pinv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
      ((phi (evaluateHOLFiniteState (decClockHOLFinite s) body).2 = phi s ∧
          Rel s (evaluateHOLFiniteState (decClockHOLFinite s) body).2) ∨
        phi (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < phi s) := by
  set t := decClockHOLFinite s with ht
  have hnc := evaluate_noTopContinue body rfl t
  have hnone : (evaluateHOLFiniteState t body).1 = none := by
    rcases hflow with h | h
    · exact h
    · exact absurd h hnc
  have hPt : GuestInv t := guestInv_congr (s := s) rfl rfl rfl rfl hP.1
  obtain ⟨⟨P, hp⟩, ⟨E, he⟩, ⟨T, htop⟩⟩ := hP.2
  have hwt : Words t := ⟨⟨P, hp⟩, ⟨E, he⟩, ⟨T, htop⟩⟩
  have hwo : Words (evaluateHOLFiniteState t body).2 :=
    ⟨evaluate_wordLocal _ body rfl t hwt.1 (Or.inl hnone),
     evaluate_wordLocal _ body rfl t hwt.2.1 (Or.inl hnone),
     evaluate_wordLocal _ body rfl t hwt.2.2 (Or.inl hnone)⟩
  refine ⟨⟨guestInv_evaluate t body hPt, hwo⟩, ?_⟩
  have hmeta := evalMeta t body
  have hkeep : ∀ k, keyLoc k → (evaluateHOLFiniteState t body).2.locals.lookup k = s.locals.lookup k :=
    fun k hk => evaluate_avoidsLocal_flowing k body (body_avoids k hk) t (Or.inl hnone)
  have hbody : evaluateHOLFiniteState t body =
      if P = E then evaluateHOLFiniteState t pop else evaluateHOLFiniteState t item := by
    unfold body
    rw [ite_word_congr t _ (cond1_eval t P E hp he)]
    by_cases h : P = E <;> simp [h]
  -- frame case, shared by `pop` and the non-push `item` run
  have frameCase (hfr : Frame t (evaluateHOLFiniteState t body).2)
      (hgo : (evaluateHOLFiniteState t body).2.locals.lookup (ofString "go") =
          s.locals.lookup (ofString "go") ∨
        (evaluateHOLFiniteState t body).2.locals.lookup (ofString "go") = some (.val (.word 0))) :
      (phi (evaluateHOLFiniteState t body).2 = phi s ∧ Rel s (evaluateHOLFiniteState t body).2) ∨
        phi (evaluateHOLFiniteState t body).2 < phi s := by
    left
    have hg : (evaluateHOLFiniteState t body).2.globals = s.globals := hfr.2.1
    refine ⟨by unfold phi; rw [hg], ⟨⟨P, hp⟩, ⟨E, he⟩, ⟨T, htop⟩⟩, hwo, hfr.1, hg, hfr.2.2.1, hfr.2.2.2,
      hmeta.1, hmeta.2.1, hmeta.2.2.1, hmeta.2.2.2.1, hmeta.2.2.2.2.1, hmeta.2.2.2.2.2.1,
      hmeta.2.2.2.2.2.2, hkeep, hgo⟩
  by_cases hPE : P = E
  · rw [if_pos hPE] at hbody
    have hpop : (evaluateHOLFiniteState t pop).1 = none := by rw [← hbody]; exact hnone
    apply frameCase
    · rw [hbody]; exact evaluate_ro (fun _ => false) (fun _ h => by simp at h) pop rfl t hcode
    · rw [hbody]; exact pop_go t hpop
  · rw [if_neg hPE] at hbody
    have hitem : (evaluateHOLFiniteState t item).1 = none := by rw [← hbody]; exact hnone
    rcases item_step t hcode hitem with hfr | ⟨p, f, q, hpg, hfg, hq, hfq, h1, h2⟩
    · apply frameCase
      · rw [hbody]; exact hfr
      · left; rw [hbody]
        exact evaluate_avoidsLocal_flowing _ item item_avoids_go t (Or.inl hitem)
    · right
      rw [hbody]
      have hs1 : s.globals.lookup sp = some (.val (.word p)) := hpg
      have hs2 : s.globals.lookup fmp = some (.val (.word f)) := hfg
      unfold phi
      rw [hq, hfq, hs1, hs2]
      dsimp only
      rw [if_pos h1]
      have := q.isLt
      split
      · rename_i hle; have := h2 hle; omega
      · omega

/-! ### The loop bound -/

def bodyK : Nat := Nat.max 0 ((K.«rlp_item_header» + 1) + Nat.max (K.«scratch_alloc» + 1) 0)

theorem body_bound : TerminatingProgBoundedOn GuestInv body bodyK := by
  apply TerminatingProgBoundedOn.weaken'
  · unfold body pop item cont push pushTail
    fb_auto
  · unfold bodyK
    simp only [nat_max_eq]
    omega

theorem loop_bound : TerminatingProgBoundedOn Pinv (.while cond body)
    ((2 ^ 61 + 1) * 2 ^ 192 * (bodyK + 1)) := by
  have hloop : PhasedLoop Pinv (fun s => GuestInv s) Rel phi kappa cond body bodyK :=
    { body_bound := body_bound
      entry := fun s _ _ hP _ _ _ => guestInv_congr (s := s) rfl rfl rfl rfl hP.1
      step := fun s _ hcode hP _ _ hclk => by
        dsimp only
        intro _ hflow
        exact step s hcode hP hclk hflow
      trans := Rel_trans
      key := Rel_key }
  intro F s hc hP
  exact TerminatingProgBoundedOn.while_phased (Φ := 2 ^ 61) hloop (fun s _ => phi_le s) s hc hP

end Vib

/-! ### Guarded `dec` that records a word local, and `seq` with a weaker second guard -/

theorem dec_on' {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (name : MlS)
    (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hQ : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      shapeEqHOL .one (shapeOfHOLExact v) = true → Q (setVarHOLFinite name v s))
    (hbody : TerminatingProgBoundedOn Q body K) :
    TerminatingProgBoundedOn P (.dec name .one init body) K := by
  intro F state hcode hPs
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i val _ hsh
      have hb := hbody (setVarHOLFinite name val state) hcode (hQ state val hPs hsh) hnt
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem seq_on' {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64}
    {a b : Nat} (h1 : TerminatingProgBoundedOn P first a) (hp : PreservesOn P Q first)
    (h2 : TerminatingProgBoundedOn Q second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := hp state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid (by simp)) hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem setVar_word {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (v : ValueHOL 64)
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) : WordLocal name (setVarHOLFinite name v s) := by
  obtain ⟨w, rfl⟩ := shape_one_word v (by
    rcases v with ⟨⟨w⟩⟩ | fs | ⟨n, fs⟩ <;> simp_all [shapeEqHOL, shapeOfHOLExact])
  exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩

theorem setVar_keep {F : Type} (s : PanSemStateFiniteExact 64 F) (name x : MlS) (v : ValueHOL 64)
    (hne : name ≠ x) (h : WordLocal x s) : WordLocal x (setVarHOLFinite name v s) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hw]⟩

/-- `_rlp_validate_items_body` (AST line 4507): #0 STACK (phased no-repeat, see ISSUES.md §1). -/
theorem «fb__rlp_validate_items_body» : TerminatingFunBoundedOn GuestInv
    (ofString "_rlp_validate_items_body") K.«_rlp_validate_items_body» := by
  fb_unfold 110 Guest.Software.guestFn__rlp_validate_items_body
  refine TerminatingProgBoundedOn.weaken' (K := (2 ^ 61 + 1) * 2 ^ 192 * (Vib.bodyK + 1) + 0) ?_ ?_
  · refine dec_on' (Q := fun s => GuestInv s ∧ WordLocal (ofString "top") s) _ _
      (fun s v hP hv => ⟨guestInv_setVar _ _ _ hP, setVar_word s _ v hv⟩) ?_
    refine dec_on' (P := fun s => GuestInv s ∧ WordLocal (ofString "top") s)
      (Q := fun s => (GuestInv s ∧ WordLocal (ofString "top") s) ∧
        WordLocal (ofString "pos") s) _ _
      (fun s v hP hv => ⟨⟨guestInv_setVar _ _ _ hP.1, setVar_keep s _ _ v (by decide) hP.2⟩,
        setVar_word s _ v hv⟩) ?_
    refine dec_on' (P := fun s => (GuestInv s ∧ WordLocal (ofString "top") s) ∧
        WordLocal (ofString "pos") s) (Q := fun s => Vib.Pinv s) _ _
      (fun s v hP hv => ⟨guestInv_setVar _ _ _ hP.1.1,
        setVar_keep s _ _ v (by decide) hP.2, setVar_word s _ v hv,
        setVar_keep s _ _ v (by decide) hP.1.2⟩) ?_
    refine dec_on' (P := fun s => Vib.Pinv s) (Q := fun s => Vib.Pinv s) _ _
      (fun s v hP hv => ⟨guestInv_setVar _ _ _ hP.1,
        setVar_keep s _ _ v (by decide) hP.2.1, setVar_keep s _ _ v (by decide) hP.2.2.1,
        setVar_keep s _ _ v (by decide) hP.2.2.2⟩) ?_
    exact seq_on' Vib.loop_bound (fun s _ hP _ => guestInv_evaluate s _ hP.1) (straightOn _ rfl)
  · unfold K.«_rlp_validate_items_body» Vib.bodyK
    simp only [nat_max_eq]
    omega


end InitECandidate.Solver.Wave8Leaves.Rlp
