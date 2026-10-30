import InitECandidate.Solver.GuestTrapAlign
import InitECandidate.Solver.GuestBeaconKeep
import InitECandidate.Solver.B2Oracle

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.HeapPotential

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestExceptionShapes
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestFrameMemKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestBeaconKeep
open InitECandidate.Solver.B2Oracle

def cMax : BitVec 64 := 2952790016

theorem alloc_bounds_of_lt_heapEnd (p n : BitVec 64)
    (hp_lt : p.toNat < 33806089704) (hn_hi : n.toNat ≤ 1024)
    (hcmp2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ 2952790016 ∧ q &&& 7 = 0 := by
  intro q
  have hq_eq : q.toNat = (p + (n + 7)).toNat / 8 * 8 := and_neg8_toNat (p + (n + 7))
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  have hn7 : (n + 7).toNat = n.toNat + 7 := by
    rw [BitVec.toNat_add, h7]
    omega
  have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by
    rw [BitVec.toNat_add, hn7]
    omega
  have halign : q &&& 7 = 0 := by
    change ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)) &&& 7 = 0
    rw [BitVec.and_assoc]
    have : (((0 : BitVec 64) - 8) &&& 7) = 0 := by decide
    rw [this]
    simp
  have hcMax : cMax.toNat = 2952790016 := rfl
  have hq_le : q.toNat ≤ 2952790016 := by
    have hle : q.toNat ≤ cMax.toNat := Nat.le_of_not_lt hcmp2
    omega
  refine ⟨by omega, hq_le, halign⟩

theorem alloc_q_word_eq (p n : BitVec 64) :
    p + (n + (7#64 + 0#64)) &&& (0#64 - 8#64 &&& (~~~0#64)) =
      (p + (n + 7)) &&& ((0 : BitVec 64) - 8) := by
  have h1 : (7#64 + 0#64) = (7 : BitVec 64) := by decide
  have h2 : (0#64 - 8#64 &&& (~~~0#64)) = ((0 : BitVec 64) - 8) := by decide
  rw [h1, h2]

theorem evaluate_alloc_body_eq {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word p) ∧
      out.2.globals.lookup (ofString "heap_ptr") = some (.val (.word q)) ∧
      ¬ (cMax.toNat < q.toNat) ∧
      out.2.memory = state.memory := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
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
  have hcode_p : pState.code = originalRuntimeCode := hcode
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (cMax - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode_p
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 1 w hcode_p
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some r1' =>
      intro retVal hret
      exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]
    dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
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
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    have hcode_q : qState.code = originalRuntimeCode := hcode
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
        some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : cMax.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode_q
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 1 w hcode_q
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some r2' =>
        intro retVal hret
        exact False.elim (hno_ret retVal hret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      intro retVal hret
      injection hret with hr
      injection hr with hr'
      refine ⟨hr'.symm, ?_, hcmp2, rfl⟩
      simp only [emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ↓reduceIte]
      rfl

theorem scratch_alloc_bounds_preserved (ptr frame size : BitVec 64)
    (hlo : frame.toNat ≤ ptr.toNat) (hhi : ptr.toNat ≤ 2965299200)
    (hcmp1 : ¬ ((ptr - frame).toNat < size.toNat))
    (hcmp2 : ¬ (((ptr - size) &&& ((0 : BitVec 64) - 8)).toNat < frame.toNat)) :
    let q := (ptr - size) &&& ((0 : BitVec 64) - 8)
    frame.toNat ≤ q.toNat ∧ q.toNat ≤ 2965299200 := by
  intro q
  have hp : ptr.toNat < 2 ^ 64 := ptr.isLt
  have hf : frame.toNat < 2 ^ 64 := frame.isLt
  have hsub_pf : (ptr - frame).toNat = ptr.toNat - frame.toNat := by
    rw [BitVec.toNat_sub]
    omega
  have hsize_le : size.toNat ≤ ptr.toNat := by omega
  have hq_le : q.toNat ≤ ptr.toNat := sub_and_neg8_le_ptr ptr size hsize_le
  exact ⟨Nat.le_of_not_lt hcmp2, Nat.le_trans hq_le hhi⟩

def heapPotential (p : BitVec 64) : Nat := cMax.toNat - p.toNat

theorem alloc_heap_potential (p n : BitVec 64)
    (hp_lt : p.toNat < 33806089704) (hn_hi : n.toNat ≤ 1024) (hn_pos : 0 < n.toNat)
    (hcmp2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    heapPotential q < heapPotential p ∧ heapPotential q + n.toNat ≤ heapPotential p := by
  dsimp only
  have hb := alloc_bounds_of_lt_heapEnd p n hp_lt hn_hi hcmp2
  dsimp only at hb
  have hcMax : cMax.toNat = 2952790016 := rfl
  unfold heapPotential
  omega

theorem scratch_potential (ptr frame size : BitVec 64)
    (hlo : frame.toNat ≤ ptr.toNat) (hhi : ptr.toNat ≤ 2965299200) (hsize : 0 < size.toNat)
    (hcmp1 : ¬ ((ptr - frame).toNat < size.toNat))
    (hcmp2 : ¬ (((ptr - size) &&& ((0 : BitVec 64) - 8)).toNat < frame.toNat)) :
    let q := (ptr - size) &&& ((0 : BitVec 64) - 8)
    q.toNat - frame.toNat < ptr.toNat - frame.toNat := by
  intro q
  have hb := scratch_alloc_bounds_preserved ptr frame size hlo hhi hcmp1 hcmp2
  dsimp only at hb
  have hp : ptr.toNat < 2 ^ 64 := ptr.isLt
  have hf : frame.toNat < 2 ^ 64 := frame.isLt
  have hsub_pf : (ptr - frame).toNat = ptr.toNat - frame.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hsize_le : size.toNat ≤ ptr.toNat := by omega
  have hsub_ps : (ptr - size).toNat = ptr.toNat - size.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hq_eq : q.toNat = (ptr - size).toNat / 8 * 8 := and_neg8_toNat (ptr - size)
  omega

theorem covered_trap_excludes_oom {ev}
    (hcov : coveredOutcome (.ffiOutcome ev))
    (htrap : ev.name = .extCall (ofString "trap")) :
    ev.configuration.length ≠ 1 ∧ ev.configuration.length ≠ 6 ∧ ev.configuration.length ≠ 7 := by
  rcases hcov.2 with hne | hlen
  · exact absurd htrap hne
  · exact hlen

end InitECandidate.Solver.HeapPotential
