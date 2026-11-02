import InitECandidate.Solver.PanRunBounded
import InitECandidate.Solver.HeapPotential

/-! Low-footprint body and call helper lemmas for `rt_te_new` in micro-shard `m27`
(`wave8/contracts-m27`), importing only `PanRunBounded` and `HeapPotential`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M27

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanRunBounded

theorem lookup_alloc_te :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem lookup_memzero :
    originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memzero, .one) :=
  lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memzero) rfl

theorem lookup_te_new :
    originalRuntimeCode.lookup (ofString "te_new") =
      some ((sourceFunctionEntry Guest.Software.guestFn_te_new).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 869 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_te_new) rfl

theorem alloc_body_run {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word p) ∧ ¬ ((cMax - p).toNat < n.toNat) ∧ ¬ (cMax.toNat < q.toNat) ∧
      out.2 = { state with
        globals := (state.globals.update (ofString "heap_ptr", .val (.word q)))
        locals := out.2.locals } := by
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
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]
      simp
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
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]
        simp
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
      exact ⟨hr'.symm, hcmp1, hcmp2, rfl⟩

def updW_te (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun c => if c = a then .word w else m c

private theorem store_zero_step {F : Type} (st : PanSemStateFiniteExact 64 F)
    (addrExp : ExpHOL 64) (a : BitVec 64)
    (heval : @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x))
      addrExp = some (.val (.word a)))
    (hdom : st.memaddrs a) :
    evaluateHOLFiniteState st (.store addrExp (.const 0#64)) =
      (none, { st with memory := updW_te st.memory a 0#64 }) := by
  rw [evaluateHOLFiniteState_store, heval]
  have hev0 : @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x))
      (.const 0#64) = some (.val (.word 0#64)) := rfl
  rw [hev0]
  dsimp only
  have hst : @panMemStoresHOL 64 _ a (flattenHOL (.val (.word 0#64))) st.memaddrs
      (fun x => Classical.propDecidable (st.memaddrs x)) st.memory =
      some (updW_te st.memory a 0#64) := by
    simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]
    rfl
  rw [hst]

private theorem memzero_w32_step {F : Type} (st : PanSemStateFiniteExact 64 F)
    (dst iv : BitVec 64)
    (hdst : st.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn : st.locals.lookup (ofString "n") = some (.val (.word 200#64)))
    (hi : st.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hcond_true : (iv + 32#64).toNat ≤ 200)
    (hclk : st.clock ≠ 0)
    (hd0 : st.memaddrs (dst + iv))
    (hd8 : st.memaddrs (dst + iv + 8#64))
    (hd16 : st.memaddrs (dst + iv + 16#64))
    (hd24 : st.memaddrs (dst + iv + 24#64)) :
    let w32body : ProgHOL 64 :=
      .seq
        (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
        (.seq
          (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8#64]) (.const 0#64))
          (.seq
            (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16#64]) (.const 0#64))
            (.seq
              (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24#64]) (.const 0#64))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32#64])))))
    let w32 : ProgHOL 64 :=
      .while (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32#64])) w32body
    evaluateHOLFiniteState st w32 =
      evaluateHOLFiniteState
        (setVarHOLFinite (ofString "i") (.val (.word (iv + 32#64)))
          { (decClockHOLFinite st) with
            memory := updW_te (updW_te (updW_te (updW_te st.memory (dst + iv) 0#64)
              (dst + iv + 8#64) 0#64) (dst + iv + 16#64) 0#64) (dst + iv + 24#64) 0#64 })
        w32 := by
  intro w32body w32
  have hcond : evalHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32#64])) =
      some (.val (.word 1#64)) := by
    rw [evalHOLFinite_eq_toExact]
    simp only [evalHOLExact, evalListHOLExact, hn, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [BitVec.toNat_add] at hcond_true
    change (iv.toNat + 32) % 18446744073709551616 ≤ 200 at hcond_true
    simp [show ¬ (200 < (iv.toNat + 32) % 18446744073709551616) by omega]
  dsimp only [w32]
  rw [evaluateHOLFiniteState_while_total, hcond]
  have h10 : (1#64 : BitVec 64) ≠ 0 := by decide
  let st_end := setVarHOLFinite (ofString "i") (.val (.word (iv + 32#64)))
    { (decClockHOLFinite st) with
      memory := updW_te (updW_te (updW_te (updW_te st.memory (dst + iv) 0#64)
        (dst + iv + 8#64) 0#64) (dst + iv + 16#64) 0#64) (dst + iv + 24#64) 0#64 }
  have hbRun : evaluateHOLFiniteState (decClockHOLFinite st) w32body = (none, st_end) := by
    dsimp only [w32body]
    let d0 := decClockHOLFinite st
    have hs0 : evaluateHOLFiniteState d0
        (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64)) =
        (none, { d0 with memory := updW_te d0.memory (dst + iv) 0#64 }) := by
      apply store_zero_step
      · simp [d0, decClockHOLFinite, evalHOLExact, evalListHOLExact, hdst, hi,
          wordOpHOL, wordOp, valueIsWord, valueWord]
      · exact hd0
    let d1 := { d0 with memory := updW_te d0.memory (dst + iv) 0#64 }
    have hs1 : evaluateHOLFiniteState d1
        (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8#64]) (.const 0#64)) =
        (none, { d1 with memory := updW_te d1.memory (dst + iv + 8#64) 0#64 }) := by
      apply store_zero_step
      · simp [d1, d0, decClockHOLFinite, evalHOLExact, evalListHOLExact, hdst, hi,
          wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [← BitVec.add_assoc]
      · exact hd8
    let d2 := { d1 with memory := updW_te d1.memory (dst + iv + 8#64) 0#64 }
    have hs2 : evaluateHOLFiniteState d2
        (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16#64]) (.const 0#64)) =
        (none, { d2 with memory := updW_te d2.memory (dst + iv + 16#64) 0#64 }) := by
      apply store_zero_step
      · simp [d2, d1, d0, decClockHOLFinite, evalHOLExact, evalListHOLExact, hdst, hi,
          wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [← BitVec.add_assoc]
      · exact hd16
    let d3 := { d2 with memory := updW_te d2.memory (dst + iv + 16#64) 0#64 }
    have hs3 : evaluateHOLFiniteState d3
        (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24#64]) (.const 0#64)) =
        (none, { d3 with memory := updW_te d3.memory (dst + iv + 24#64) 0#64 }) := by
      apply store_zero_step
      · simp [d3, d2, d1, d0, decClockHOLFinite, evalHOLExact, evalListHOLExact, hdst, hi,
          wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [← BitVec.add_assoc]
      · exact hd24
    let d4 := { d3 with memory := updW_te d3.memory (dst + iv + 24#64) 0#64 }
    have ha4 : evaluateHOLFiniteState d4
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32#64])) =
        (none, st_end) := by
      rw [evaluateHOLFiniteState_assign]
      simp [d4, d3, d2, d1, d0, st_end, decClockHOLFinite, evalHOLExact, evalListHOLExact, hi,
        wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
        PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
        setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [evaluateHOLFiniteState_seq_line780, hs0]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780, hs1]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780, hs2]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780, hs3]
    dsimp only
    exact ha4
  have hfix : ((decClockHOLFinite st).fixClockHOLFinite
      ((none : Option (PanSemResultExact 64)), st_end)) = (none, st_end) := by
    simp [fixClockHOLFinite, st_end, setVarHOLFinite, decClockHOLFinite]
  simp only [hclk, if_false, hbRun, hfix]
  exact if_pos h10

private theorem memzero_w8_step {F : Type} (st : PanSemStateFiniteExact 64 F)
    (dst iv : BitVec 64)
    (hdst : st.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn : st.locals.lookup (ofString "n") = some (.val (.word 200#64)))
    (hi : st.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hcond_true : (iv + 8#64).toNat ≤ 200)
    (hclk : st.clock ≠ 0)
    (hd0 : st.memaddrs (dst + iv)) :
    let w8body : ProgHOL 64 :=
      .seq
        (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64]))
    let w8 : ProgHOL 64 :=
      .while (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8#64])) w8body
    evaluateHOLFiniteState st w8 =
      evaluateHOLFiniteState
        (setVarHOLFinite (ofString "i") (.val (.word (iv + 8#64)))
          { (decClockHOLFinite st) with memory := updW_te st.memory (dst + iv) 0#64 })
        w8 := by
  intro w8body w8
  have hcond : evalHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8#64])) =
      some (.val (.word 1#64)) := by
    rw [evalHOLFinite_eq_toExact]
    simp only [evalHOLExact, evalListHOLExact, hn, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [BitVec.toNat_add] at hcond_true
    change (iv.toNat + 8) % 18446744073709551616 ≤ 200 at hcond_true
    simp [show ¬ (200 < (iv.toNat + 8) % 18446744073709551616) by omega]
  dsimp only [w8]
  rw [evaluateHOLFiniteState_while_total, hcond]
  have h10 : (1#64 : BitVec 64) ≠ 0 := by decide
  let st_end := setVarHOLFinite (ofString "i") (.val (.word (iv + 8#64)))
    { (decClockHOLFinite st) with memory := updW_te st.memory (dst + iv) 0#64 }
  have hbRun : evaluateHOLFiniteState (decClockHOLFinite st) w8body = (none, st_end) := by
    dsimp only [w8body]
    let d0 := decClockHOLFinite st
    have hs0 : evaluateHOLFiniteState d0
        (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64)) =
        (none, { d0 with memory := updW_te d0.memory (dst + iv) 0#64 }) := by
      apply store_zero_step
      · simp [d0, decClockHOLFinite, evalHOLExact, evalListHOLExact, hdst, hi,
          wordOpHOL, wordOp, valueIsWord, valueWord]
      · exact hd0
    let d1 := { d0 with memory := updW_te d0.memory (dst + iv) 0#64 }
    have ha1 : evaluateHOLFiniteState d1
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64])) =
        (none, st_end) := by
      rw [evaluateHOLFiniteState_assign]
      simp [d1, d0, st_end, decClockHOLFinite, evalHOLExact, evalListHOLExact, hi,
        wordOpHOL, wordOp, valueIsWord, valueWord,
        lookupKvarHOLExact, PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
        setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [evaluateHOLFiniteState_seq_line780, hs0]
    dsimp only
    exact ha1
  have hfix : ((decClockHOLFinite st).fixClockHOLFinite
      ((none : Option (PanSemResultExact 64)), st_end)) = (none, st_end) := by
    simp [fixClockHOLFinite, st_end, setVarHOLFinite, decClockHOLFinite]
  simp only [hclk, if_false, hbRun, hfix]
  exact if_pos h10

private def NS_te {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C : Nat) : PanSemStateFiniteExact 64 F :=
  { s with locals := L, memory := M, clock := C }

private theorem memzero_w32_ns {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64) (C : Nat)
    (dst iv : BitVec 64) {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    (hdst : L.lookup (ofString "dst") = some (.val (.word dst)))
    (hn : L.lookup (ofString "n") = some (.val (.word 200#64)))
    (hi : L.lookup (ofString "i") = some (.val (.word iv)))
    (hcond_true : (iv + 32#64).toNat ≤ 200)
    (hnot_to : r ≠ some .timeOut)
    (hd0 : s.memaddrs (dst + iv))
    (hd8 : s.memaddrs (dst + iv + 8#64))
    (hd16 : s.memaddrs (dst + iv + 16#64))
    (hd24 : s.memaddrs (dst + iv + 24#64))
    (hrun : evaluateHOLFiniteState (NS_te s L M C)
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 32#64]))
        (.seq
          (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
          (.seq
            (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8#64]) (.const 0#64))
            (.seq
              (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16#64]) (.const 0#64))
              (.seq
                (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24#64]) (.const 0#64))
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32#64]))))))) =
      (r, post)) :
    evaluateHOLFiniteState
      (NS_te s (L.update (ofString "i", .val (.word (iv + 32#64))))
        (updW_te (updW_te (updW_te (updW_te M (dst + iv) 0#64) (dst + iv + 8#64) 0#64)
          (dst + iv + 16#64) 0#64) (dst + iv + 24#64) 0#64)
        (C - 1))
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 32#64]))
        (.seq
          (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
          (.seq
            (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8#64]) (.const 0#64))
            (.seq
              (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16#64]) (.const 0#64))
              (.seq
                (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24#64]) (.const 0#64))
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32#64]))))))) =
      (r, post) := by
  by_cases hc0 : C = 0
  · subst hc0
    let sZ := NS_te s L M 0
    have hcond : evalHOLFinite sZ (h := fun x => Classical.propDecidable (sZ.memaddrs x))
        (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 32#64])) =
        some (.val (.word 1#64)) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [sZ, NS_te, evalHOLExact, evalListHOLExact, hn, hi, wordOpHOL, wordOp, valueIsWord,
        valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
        BitVec.add_zero, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      rw [BitVec.toNat_add] at hcond_true
      change (iv.toNat + 32) % 18446744073709551616 ≤ 200 at hcond_true
      simp [show ¬ (200 < (iv.toNat + 32) % 18446744073709551616) by omega]
    change evaluateHOLFiniteState sZ _ = (r, post) at hrun
    rw [evaluateHOLFiniteState_while_total, hcond] at hrun
    dsimp only at hrun
    have h10 : (1#64 : BitVec 64) ≠ 0 := by decide
    rw [if_pos h10] at hrun
    simp [sZ, NS_te] at hrun
    exact absurd hrun.1.symm hnot_to
  · have hstep := memzero_w32_step (NS_te s L M C) dst iv hdst hn hi hcond_true hc0 hd0 hd8 hd16 hd24
    dsimp only at hstep
    rw [hstep] at hrun
    exact hrun

private theorem memzero_w8_ns {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64) (C : Nat)
    (dst iv : BitVec 64) {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    (hdst : L.lookup (ofString "dst") = some (.val (.word dst)))
    (hn : L.lookup (ofString "n") = some (.val (.word 200#64)))
    (hi : L.lookup (ofString "i") = some (.val (.word iv)))
    (hcond_true : (iv + 8#64).toNat ≤ 200)
    (hnot_to : r ≠ some .timeOut)
    (hd0 : s.memaddrs (dst + iv))
    (hrun : evaluateHOLFiniteState (NS_te s L M C)
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 8#64]))
        (.seq
          (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64])))) =
      (r, post)) :
    evaluateHOLFiniteState
      (NS_te s (L.update (ofString "i", .val (.word (iv + 8#64))))
        (updW_te M (dst + iv) 0#64) (C - 1))
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 8#64]))
        (.seq
          (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64])))) =
      (r, post) := by
  by_cases hc0 : C = 0
  · subst hc0
    let sZ := NS_te s L M 0
    have hcond : evalHOLFinite sZ (h := fun x => Classical.propDecidable (sZ.memaddrs x))
        (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 8#64])) =
        some (.val (.word 1#64)) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [sZ, NS_te, evalHOLExact, evalListHOLExact, hn, hi, wordOpHOL, wordOp, valueIsWord,
        valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
        BitVec.add_zero, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      rw [BitVec.toNat_add] at hcond_true
      change (iv.toNat + 8) % 18446744073709551616 ≤ 200 at hcond_true
      simp [show ¬ (200 < (iv.toNat + 8) % 18446744073709551616) by omega]
    change evaluateHOLFiniteState sZ _ = (r, post) at hrun
    rw [evaluateHOLFiniteState_while_total, hcond] at hrun
    dsimp only at hrun
    have h10 : (1#64 : BitVec 64) ≠ 0 := by decide
    rw [if_pos h10] at hrun
    simp [sZ, NS_te] at hrun
    exact absurd hrun.1.symm hnot_to
  · have hstep := memzero_w8_step (NS_te s L M C) dst iv hdst hn hi hcond_true hc0 hd0
    dsimp only at hstep
    rw [hstep] at hrun
    exact hrun

private theorem while_false_exit {F : Type} (st : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hcond : @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x))
      cond = some (.val (.word 0#64))) :
    evaluateHOLFiniteState st (.while cond body) = (none, st) := by
  have hcond' : evalHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x))
      cond = some (.val (.word 0#64)) := by
    rw [evalHOLFinite_eq_toExact]; exact hcond
  rw [evaluateHOLFiniteState_while_total, hcond']
  simp

def zeroBlock25 (m : BitVec 64 → HolWordLab 64) (p : BitVec 64) :
    BitVec 64 → HolWordLab 64 :=
  updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te
    (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te (updW_te m
      (p + 0#64) 0#64)
      (p + 0#64 + 8#64) 0#64)
      (p + 0#64 + 16#64) 0#64)
      (p + 0#64 + 24#64) 0#64)
      (p + 32#64) 0#64)
      (p + 32#64 + 8#64) 0#64)
      (p + 32#64 + 16#64) 0#64)
      (p + 32#64 + 24#64) 0#64)
      (p + 64#64) 0#64)
      (p + 64#64 + 8#64) 0#64)
      (p + 64#64 + 16#64) 0#64)
      (p + 64#64 + 24#64) 0#64)
      (p + 96#64) 0#64)
      (p + 96#64 + 8#64) 0#64)
      (p + 96#64 + 16#64) 0#64)
      (p + 96#64 + 24#64) 0#64)
      (p + 128#64) 0#64)
      (p + 128#64 + 8#64) 0#64)
      (p + 128#64 + 16#64) 0#64)
      (p + 128#64 + 24#64) 0#64)
      (p + 160#64) 0#64)
      (p + 160#64 + 8#64) 0#64)
      (p + 160#64 + 16#64) 0#64)
      (p + 160#64 + 24#64) 0#64)
      (p + 192#64) 0#64

theorem zeroBlock25_read (m : BitVec 64 → HolWordLab 64) (p : BitVec 64)
    (k : Nat) (hk : k < 25) :
    zeroBlock25 m p (p + BitVec.ofNat 64 (8 * k)) = .word 0#64 := by
  have hk_cases :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
      k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨
      k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 := by omega
  have hadd_norm : ∀ (a b : BitVec 64), (p + a) + b = p + (a + b) := fun a b => BitVec.add_assoc p a b
  have hcancel : ∀ (x y : BitVec 64), (p + x = p + y) ↔ (x = y) := by
    intro x y
    constructor
    · intro h
      have := congrArg (fun z => z - p) h
      simpa [BitVec.add_sub_cancel] using this
    · intro h; rw [h]
  unfold zeroBlock25 updW_te
  simp only [hadd_norm, hcancel]
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> simp

attribute [local irreducible] zeroBlock25 in
theorem memzero_200_body_run {F : Type}
    (st post : PanSemStateFiniteExact 64 F) (p : BitVec 64) (retVal : ValueHOL 64)
    (hdst : st.locals.lookup (ofString "dst") = some (.val (.word p)))
    (hn : st.locals.lookup (ofString "n") = some (.val (.word 200#64)))
    (hal : p.toNat % 8 = 0)
    (hdom : ∀ off : Nat, off < 200 → off % 8 = 0 → st.memaddrs (p + BitVec.ofNat 64 off))
    (hrun : evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_memzero) =
      (some (.returned retVal), post)) :
    post = { st with
      memory := zeroBlock25 st.memory p
      locals := post.locals
      clock := post.clock } := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memzero,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hrun
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) st
  have hand0 : p &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change p.toNat &&& (2 ^ 3 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact hal
  have hcond_al : @evalHOLExact 64 F _ s0.toExact (fun x => Classical.propDecidable (s0.memaddrs x))
      (.cmp .equal (.op .and [.var .local (ofString "dst"), .const 7#64]) (.const 0#64)) =
      some (.val (.word 1#64)) := by
    have hd0 : s0.locals.lookup (ofString "dst") = some (.val (.word p)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "dst" by decide, hdst]
    have h7top : wordOpHOL (width := 64) .and [p, 7#64] = some 0#64 := by
      simp only [wordOpHOL, wordOp, List.foldr]
      have h1 : AndOp.and 7#64 (~~~(0 : BitVec 64)) = 7#64 := by decide
      have h2 : AndOp.and p 7#64 = 0#64 := hand0
      rw [h1, h2]
    simp only [evalHOLExact, evalListHOLExact, hd0, valueIsWord, valueWord, List.all, List.map,
      Option.map, Bool.and_self, ↓reduceIte, h7top, Compiler.Encoders.Asm.wordCmpHOL]
    rfl
  let w32body : ProgHOL 64 :=
    .seq
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
      (.seq
        (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8#64]) (.const 0#64))
        (.seq
          (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16#64]) (.const 0#64))
          (.seq
            (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24#64]) (.const 0#64))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32#64])))))
  let w32 : ProgHOL 64 :=
    .while (.cmp .notLower (.var .local (ofString "n"))
      (.op .add [.var .local (ofString "i"), .const 32#64])) w32body
  let w8body : ProgHOL 64 :=
    .seq
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64]))
  let w8 : ProgHOL 64 :=
    .while (.cmp .notLower (.var .local (ofString "n"))
      (.op .add [.var .local (ofString "i"), .const 8#64])) w8body
  have hdom_iv : ∀ (iv off : Nat), iv + off < 200 → (iv + off) % 8 = 0 →
      st.memaddrs (p + BitVec.ofNat 64 iv + BitVec.ofNat 64 off) := by
    intro iv off hlt hmod
    have heq : p + BitVec.ofNat 64 iv + BitVec.ofNat 64 off = p + BitVec.ofNat 64 (iv + off) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add]
    rw [heq]
    exact hdom (iv + off) hlt hmod
  have hd_u : ∀ (v : ValueHOL 64) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      L.lookup (ofString "dst") = some (.val (.word p)) →
      (L.update (ofString "i", v)).lookup (ofString "dst") = some (.val (.word p)) := by
    intro v L hL
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "dst" by decide, hL]
  have hn_u : ∀ (v : ValueHOL 64) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      L.lookup (ofString "n") = some (.val (.word 200#64)) →
      (L.update (ofString "i", v)).lookup (ofString "n") = some (.val (.word 200#64)) := by
    intro v L hL
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "n" by decide, hL]
  have hi_u : ∀ (v : ValueHOL 64) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      (L.update (ofString "i", v)).lookup (ofString "i") = some v := by
    intro v L
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  let L0 := st.locals.update (ofString "i", .val (.word 0#64))
  have hs0_eq : s0 = NS_te st L0 st.memory st.clock := by cases st; rfl
  have hite_branch : evaluateHOLFiniteState s0
      (.ite (.cmp .equal (.op .and [.var .local (ofString "dst"), .const 7#64]) (.const 0#64))
        (.seq w32 w8) .skip) =
      evaluateHOLFiniteState (NS_te st L0 st.memory st.clock) (.seq w32 w8) := by
    rw [evaluateHOLFiniteState_ite, hcond_al, hs0_eq]
    simp
  let b8body : ProgHOL 64 :=
    .seq
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
      (.seq
        (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1#64]) (.const 0#64))
        (.seq
          (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2#64]) (.const 0#64))
          (.seq
            (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3#64]) (.const 0#64))
            (.seq
              (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4#64]) (.const 0#64))
              (.seq
                (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5#64]) (.const 0#64))
                (.seq
                  (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6#64]) (.const 0#64))
                  (.seq
                    (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7#64]) (.const 0#64))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64])))))))))
  let b8 : ProgHOL 64 :=
    .while (.cmp .notLower (.var .local (ofString "n"))
      (.op .add [.var .local (ofString "i"), .const 8#64])) b8body
  let b1 : ProgHOL 64 :=
    .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
      (.seq
        (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))
  let tailProg : ProgHOL 64 := .seq b8 (.seq b1 (.return (.const 0#64)))
  rcases hinner : evaluateHOLFiniteState s0
      (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "dst"), .const 7#64]) (.const 0#64))
          (.seq w32 w8) .skip) tailProg) with ⟨r_in, p_in⟩
  have hrun_in : r_in = some (.returned retVal) ∧
      post = { p_in with locals := post.locals } := by
    have hinner' : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word 0#64)) st)
        (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "dst"), .const 7#64]) (.const 0#64))
            (.seq w32 w8) .skip) tailProg) = (r_in, p_in) := hinner
    rw [hinner'] at hrun
    dsimp only at hrun
    obtain ⟨hr1, hp2⟩ := Prod.mk.inj hrun
    refine ⟨hr1, ?_⟩
    rw [← hp2]
  rcases hrun_in with ⟨rfl, hpost_p⟩
  rw [evaluateHOLFiniteState_seq_line780, hite_branch, evaluateHOLFiniteState_seq_line780] at hinner
  have hd_L0 : L0.lookup (ofString "dst") = some (.val (.word p)) := hd_u (.val (.word 0#64)) st.locals hdst
  have hn_L0 : L0.lookup (ofString "n") = some (.val (.word 200#64)) := hn_u (.val (.word 0#64)) st.locals hn
  rcases hw32_out : evaluateHOLFiniteState (NS_te st L0 st.memory st.clock) w32 with ⟨rw32, pw32⟩
  have hw32_not_to : rw32 ≠ some .timeOut := by
    rintro rfl
    rw [hw32_out] at hinner
    dsimp only at hinner
    cases hinner
  have hw1 := memzero_w32_ns st L0 st.memory st.clock p 0#64 hd_L0 hn_L0 (hi_u (.val (.word 0#64)) st.locals)
    (by decide) hw32_not_to
    (by simpa using hdom 0 (by omega) (by omega))
    (hdom_iv 0 8 (by omega) (by omega))
    (hdom_iv 0 16 (by omega) (by omega))
    (hdom_iv 0 24 (by omega) (by omega)) hw32_out
  have hadd1 : (0#64 + 32#64 : BitVec 64) = 32#64 := rfl
  rw [hadd1] at hw1
  let L1 := L0.update (ofString "i", .val (.word 32#64))
  let M1 := updW_te (updW_te (updW_te (updW_te st.memory (p + 0#64) 0#64)
    (p + 0#64 + 8#64) 0#64) (p + 0#64 + 16#64) 0#64) (p + 0#64 + 24#64) 0#64
  have hd_L1 : L1.lookup (ofString "dst") = some (.val (.word p)) := hd_u (.val (.word 32#64)) L0 hd_L0
  have hn_L1 : L1.lookup (ofString "n") = some (.val (.word 200#64)) := hn_u (.val (.word 32#64)) L0 hn_L0
  have hw2 := memzero_w32_ns st L1 M1 (st.clock - 1) p 32#64 hd_L1 hn_L1 (hi_u (.val (.word 32#64)) L0)
    (by decide) hw32_not_to
    (by simpa using hdom 32 (by omega) (by omega))
    (hdom_iv 32 8 (by omega) (by omega))
    (hdom_iv 32 16 (by omega) (by omega))
    (hdom_iv 32 24 (by omega) (by omega)) hw1
  have hadd2 : (32#64 + 32#64 : BitVec 64) = 64#64 := rfl
  rw [hadd2] at hw2
  let L2 := L1.update (ofString "i", .val (.word 64#64))
  let M2 := updW_te (updW_te (updW_te (updW_te M1 (p + 32#64) 0#64)
    (p + 32#64 + 8#64) 0#64) (p + 32#64 + 16#64) 0#64) (p + 32#64 + 24#64) 0#64
  have hd_L2 : L2.lookup (ofString "dst") = some (.val (.word p)) := hd_u (.val (.word 64#64)) L1 hd_L1
  have hn_L2 : L2.lookup (ofString "n") = some (.val (.word 200#64)) := hn_u (.val (.word 64#64)) L1 hn_L1
  have hw3 := memzero_w32_ns st L2 M2 (st.clock - 1 - 1) p 64#64 hd_L2 hn_L2 (hi_u (.val (.word 64#64)) L1)
    (by decide) hw32_not_to
    (by simpa using hdom 64 (by omega) (by omega))
    (hdom_iv 64 8 (by omega) (by omega))
    (hdom_iv 64 16 (by omega) (by omega))
    (hdom_iv 64 24 (by omega) (by omega)) hw2
  have hadd3 : (64#64 + 32#64 : BitVec 64) = 96#64 := rfl
  rw [hadd3] at hw3
  let L3 := L2.update (ofString "i", .val (.word 96#64))
  let M3 := updW_te (updW_te (updW_te (updW_te M2 (p + 64#64) 0#64)
    (p + 64#64 + 8#64) 0#64) (p + 64#64 + 16#64) 0#64) (p + 64#64 + 24#64) 0#64
  have hd_L3 : L3.lookup (ofString "dst") = some (.val (.word p)) := hd_u (.val (.word 96#64)) L2 hd_L2
  have hn_L3 : L3.lookup (ofString "n") = some (.val (.word 200#64)) := hn_u (.val (.word 96#64)) L2 hn_L2
  have hw4 := memzero_w32_ns st L3 M3 (st.clock - 1 - 1 - 1) p 96#64 hd_L3 hn_L3 (hi_u (.val (.word 96#64)) L2)
    (by decide) hw32_not_to
    (by simpa using hdom 96 (by omega) (by omega))
    (hdom_iv 96 8 (by omega) (by omega))
    (hdom_iv 96 16 (by omega) (by omega))
    (hdom_iv 96 24 (by omega) (by omega)) hw3
  have hadd4 : (96#64 + 32#64 : BitVec 64) = 128#64 := rfl
  rw [hadd4] at hw4
  let L4 := L3.update (ofString "i", .val (.word 128#64))
  let M4 := updW_te (updW_te (updW_te (updW_te M3 (p + 96#64) 0#64)
    (p + 96#64 + 8#64) 0#64) (p + 96#64 + 16#64) 0#64) (p + 96#64 + 24#64) 0#64
  have hd_L4 : L4.lookup (ofString "dst") = some (.val (.word p)) := hd_u (.val (.word 128#64)) L3 hd_L3
  have hn_L4 : L4.lookup (ofString "n") = some (.val (.word 200#64)) := hn_u (.val (.word 128#64)) L3 hn_L3
  have hw5 := memzero_w32_ns st L4 M4 (st.clock - 1 - 1 - 1 - 1) p 128#64 hd_L4 hn_L4 (hi_u (.val (.word 128#64)) L3)
    (by decide) hw32_not_to
    (by simpa using hdom 128 (by omega) (by omega))
    (hdom_iv 128 8 (by omega) (by omega))
    (hdom_iv 128 16 (by omega) (by omega))
    (hdom_iv 128 24 (by omega) (by omega)) hw4
  have hadd5 : (128#64 + 32#64 : BitVec 64) = 160#64 := rfl
  rw [hadd5] at hw5
  let L5 := L4.update (ofString "i", .val (.word 160#64))
  let M5 := updW_te (updW_te (updW_te (updW_te M4 (p + 128#64) 0#64)
    (p + 128#64 + 8#64) 0#64) (p + 128#64 + 16#64) 0#64) (p + 128#64 + 24#64) 0#64
  have hd_L5 : L5.lookup (ofString "dst") = some (.val (.word p)) := hd_u (.val (.word 160#64)) L4 hd_L4
  have hn_L5 : L5.lookup (ofString "n") = some (.val (.word 200#64)) := hn_u (.val (.word 160#64)) L4 hn_L4
  have hw6 := memzero_w32_ns st L5 M5 (st.clock - 1 - 1 - 1 - 1 - 1) p 160#64 hd_L5 hn_L5 (hi_u (.val (.word 160#64)) L4)
    (by decide) hw32_not_to
    (by simpa using hdom 160 (by omega) (by omega))
    (hdom_iv 160 8 (by omega) (by omega))
    (hdom_iv 160 16 (by omega) (by omega))
    (hdom_iv 160 24 (by omega) (by omega)) hw5
  have hadd6 : (160#64 + 32#64 : BitVec 64) = 192#64 := rfl
  rw [hadd6] at hw6
  let L6 := L5.update (ofString "i", .val (.word 192#64))
  let M6 := updW_te (updW_te (updW_te (updW_te M5 (p + 160#64) 0#64)
    (p + 160#64 + 8#64) 0#64) (p + 160#64 + 16#64) 0#64) (p + 160#64 + 24#64) 0#64
  let C6 := st.clock - 1 - 1 - 1 - 1 - 1 - 1
  have hd_L6 : L6.lookup (ofString "dst") = some (.val (.word p)) := hd_u (.val (.word 192#64)) L5 hd_L5
  have hn_L6 : L6.lookup (ofString "n") = some (.val (.word 200#64)) := hn_u (.val (.word 192#64)) L5 hn_L5
  have hw6_exit : evaluateHOLFiniteState (NS_te st L6 M6 C6) w32 = (none, NS_te st L6 M6 C6) := by
    apply while_false_exit
    have hi_L6 : L6.lookup (ofString "i") = some (.val (.word 192#64)) := hi_u (.val (.word 192#64)) L5
    simp only [NS_te, evalHOLExact, evalListHOLExact, hn_L6, hi_L6, wordOpHOL, wordOp,
      valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
      List.foldr, BitVec.add_zero, Compiler.Encoders.Asm.wordCmpHOL]
    rfl
  change evaluateHOLFiniteState (NS_te st L6 M6 C6) w32 = (rw32, pw32) at hw6
  rw [hw6_exit] at hw6
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw6
  rw [hw32_out] at hinner
  dsimp only at hinner
  rcases hw8_out : evaluateHOLFiniteState (NS_te st L6 M6 C6) w8 with ⟨rw8, pw8⟩
  have hw8_not_to : rw8 ≠ some .timeOut := by
    rintro rfl
    rw [hw8_out] at hinner
    dsimp only at hinner
    cases hinner
  have hw7 := memzero_w8_ns st L6 M6 C6 p 192#64 hd_L6 hn_L6 (hi_u (.val (.word 192#64)) L5)
    (by decide) hw8_not_to (by simpa using hdom 192 (by omega) (by omega)) hw8_out
  have hadd7 : (192#64 + 8#64 : BitVec 64) = 200#64 := rfl
  rw [hadd7] at hw7
  let L7 := L6.update (ofString "i", .val (.word 200#64))
  let C7 := C6 - 1
  have hn_L7 : L7.lookup (ofString "n") = some (.val (.word 200#64)) := hn_u (.val (.word 200#64)) L6 hn_L6
  have hi_L7 : L7.lookup (ofString "i") = some (.val (.word 200#64)) := hi_u (.val (.word 200#64)) L6
  have hw8_exit : evaluateHOLFiniteState (NS_te st L7 (zeroBlock25 st.memory p) C7) w8 =
      (none, NS_te st L7 (zeroBlock25 st.memory p) C7) := by
    apply while_false_exit
    simp only [NS_te, evalHOLExact, evalListHOLExact, hn_L7, hi_L7, wordOpHOL, wordOp,
      valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
      List.foldr, BitVec.add_zero, Compiler.Encoders.Asm.wordCmpHOL]
    rfl
  have hm7 : updW_te M6 (p + 192#64) 0#64 = zeroBlock25 st.memory p := by
    unfold zeroBlock25; rfl
  change evaluateHOLFiniteState (NS_te st L7 (updW_te M6 (p + 192#64) 0#64) C7) w8 = (rw8, pw8) at hw7
  rw [hm7, hw8_exit] at hw7
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw7
  rw [hw8_out] at hinner
  dsimp only at hinner
  let s_done := NS_te st L7 (zeroBlock25 st.memory p) C7
  have hb8_exit : evaluateHOLFiniteState s_done b8 = (none, s_done) := by
    apply while_false_exit
    simp only [s_done, NS_te, evalHOLExact, evalListHOLExact, hn_L7, hi_L7, wordOpHOL, wordOp,
      valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
      List.foldr, BitVec.add_zero, Compiler.Encoders.Asm.wordCmpHOL]
    rfl
  have hb1_exit : evaluateHOLFiniteState s_done b1 = (none, s_done) := by
    apply while_false_exit
    simp only [s_done, NS_te, evalHOLExact, hn_L7, hi_L7, Compiler.Encoders.Asm.wordCmpHOL]
    rfl
  have hret_end : evaluateHOLFiniteState s_done (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), s_done.emptyLocalsHOLFinite) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  dsimp only [tailProg] at hinner
  rw [evaluateHOLFiniteState_seq_line780, hb8_exit] at hinner
  dsimp only at hinner
  rw [evaluateHOLFiniteState_seq_line780, hb1_exit] at hinner
  dsimp only at hinner
  rw [hret_end] at hinner
  obtain ⟨_, hp_eq⟩ := Prod.mk.inj hinner
  rw [← hp_eq] at hpost_p
  rw [hpost_p]
  cases st; rfl

theorem decCall_one_word_returned {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {x fname : MlS}
    {arg : ExpHOL 64} {cont fbody : ProgHOL 64} {retVal : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(ofString "n", .one)], fbody, .one))
    (nv : BitVec 64)
    (harg : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] =
      some [.val (.word nv)])
    (hrun : evaluateHOLFiniteState s (.decCall x .one fname [arg] cont) =
      (some (.returned retVal), post)) :
    ∃ (rv : ValueHOL 64) (pa inner : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        fbody = (some (.returned rv), pa) ∧
      evaluateHOLFiniteState (setVarHOLFinite x rv { pa with locals := s.locals }) cont =
        (some (.returned retVal), inner) ∧
      post = { inner with locals := HolFiniteMapExact.resVarEq inner.locals (x, s.locals.lookup x) } := by
  rw [evaluateHOLFiniteState_decCall_total, harg] at hrun
  dsimp only at hrun
  have hlk := pan_one_word_lookup s.code.lookup fname (ofString "n") fbody nv
    (by rw [hcode]; exact hlook)
  rw [hlk] at hrun
  dsimp only at hrun
  split at hrun
  · simp at hrun
  · rw [fixClockHOLFinite_evaluateState] at hrun
    rcases haRun : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        fbody with ⟨ra, pa⟩
    have haRun' : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        fbody = (ra, pa) := haRun
    rw [haRun'] at hrun
    dsimp only at hrun
    cases ra with
    | none => simp at hrun
    | some ra' =>
      cases ra' with
      | returned rv =>
        dsimp only at hrun
        split at hrun
        · rcases hcont : evaluateHOLFiniteState
              (setVarHOLFinite x rv { pa with locals := s.locals }) cont with ⟨rc, inner⟩
          have hcont' : evaluateHOLFiniteState
              (setVarHOLFinite x rv { pa with locals := s.locals }) cont = (rc, inner) := hcont
          rw [hcont'] at hrun
          dsimp only at hrun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
          exact ⟨rv, pa, inner, rfl, hcont, rfl⟩
        · simp at hrun
      | _ => simp at hrun

theorem call_two_words_void {F : Type}
    {s pmz : PanSemStateFiniteExact 64 F} {fname p1 p2 : MlS}
    {args : List (ExpHOL 64)} {fbody : ProgHOL 64} {w1 w2 : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hdiff : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname =
      some ([(p1, .one), (p2, .one)], fbody, .one))
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [.val (.word w1), .val (.word w2)])
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) fname args) = (none, pmz)) :
    ∃ (rvmz : ValueHOL 64) (pmzb : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState
        (callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
        fbody = (some (.returned rvmz), pmzb) ∧
      pmz = { pmzb with locals := s.locals } := by
  rw [evaluateHOLFiniteState_call, hargs] at hcall
  dsimp only at hcall
  have hlk2 : lookupCodeHOLFinite s.code.lookup fname [.val (.word w1), .val (.word w2)] =
      some (fbody,
        (HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2)),
        .one) := by
    rw [hcode]
    have raw : lookupCodeHOLExact originalRuntimeCode.lookup fname
        [.val (.word w1), .val (.word w2)] =
        some (fbody,
          (fun key => if key = p2 then some (.val (.word w2))
            else if key = p1 then some (.val (.word w1)) else none), .one) := by
      simp [lookupCodeHOLExact, hlook, shapeOfHOLExact, shapeEqHOL, hdiff]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i missing; rw [raw] at missing; cases missing
    · rename_i fb fl fs found
      have equal := Option.some.inj (found.symm.trans raw)
      obtain ⟨heq1, rest⟩ := Prod.mk.inj equal
      obtain ⟨heq2, heq3⟩ := Prod.mk.inj rest
      subst heq1 heq2 heq3
      congr 1; congr 1; congr 1
      apply HolFiniteMapExact.ext
      funext key
      by_cases two : key = p2
      · subst two; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
      · have backTwo : p2 ≠ key := Ne.symm two
        by_cases one : key = p1
        · subst one
          simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty,
            hdiff, Ne.symm hdiff]
        · have backOne : p1 ≠ key := Ne.symm one
          simp [one, two, backOne, backTwo, HolFiniteMapExact.lookup_update, FUPDATE,
            HolFiniteMapExact.empty, FEMPTY]
  rw [hlk2] at hcall
  dsimp only at hcall
  split at hcall
  · simp at hcall
  · rcases hbody : evaluateHOLFiniteState
        (callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
        fbody with ⟨rb, pb⟩
    rw [hbody] at hcall
    cases rb with
    | none => simp at hcall
    | some rb' =>
      cases rb' with
      | returned rv =>
        dsimp only at hcall
        split at hcall
        · simp only [Prod.mk.injEq] at hcall
          exact ⟨rv, pb, hbody, hcall.2.symm⟩
        · simp at hcall
      | _ => simp at hcall

theorem call_void_noret_te {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) (rv : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 ≠ some (.returned rv) := by
  rw [evaluateHOLFiniteState_call]
  cases hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) args with
  | none => simp
  | some vs =>
    dsimp only
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vs with
    | none => simp
    | some inst =>
      obtain ⟨body, callee, retSh⟩ := inst
      dsimp only
      split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, _⟩
        cases res with
        | none => simp
        | some r =>
          cases r with
          | returned _ => dsimp only; split <;> simp
          | _ => simp

attribute [local irreducible] zeroBlock25 in
theorem te_new_body_run {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : BitVec 64) (retVal : ValueHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hhp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)))
    (hp_align : hp.toNat % 8 = 0)
    (hp_le_lim : hp.toNat ≤ 2952790016)
    (hdom_fn : ∀ (q : BitVec 64), q.toNat ≤ 2952790016 → q.toNat = hp.toNat + 200 →
      ∀ off : Nat, off < 200 → off % 8 = 0 → s.memaddrs (hp + BitVec.ofNat 64 off))
    (hrun : evaluateHOLFiniteState s
        (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1 =
      (some (.returned retVal), post)) :
    let q : BitVec 64 := (hp + (200#64 + 7#64)) &&& ((0 : BitVec 64) - 8)
    retVal = .val (.word hp) ∧
    q.toNat = hp.toNat + 200 ∧
    q.toNat ≤ 2952790016 ∧
    post.memory = zeroBlock25 s.memory hp ∧
    post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
    post.code = s.code ∧
    post.memaddrs = s.memaddrs ∧
    post.shMemaddrs = s.shMemaddrs ∧
    post.baseAddr = s.baseAddr := by
  intro q
  have hcMax : cMax.toNat = 2952790016 := rfl
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_te_new,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  have hargs1 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 200#64] = some [.val (.word 200#64)] := by
    rw [evalListHOLFinite_eq_toExact]; rfl
  obtain ⟨rva, pa, inner, haRun, hcont, hpost_inner⟩ :=
    decCall_one_word_returned hcode lookup_alloc_te 200#64 hargs1 hrun
  let allocEntry := callEntryStateHOLFinite s
    (HolFiniteMapExact.empty.update (ofString "n", .val (.word 200#64)))
  have hn_entry : allocEntry.locals.lookup (ofString "n") = some (.val (.word 200#64)) := by
    simp [allocEntry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨rfl, _, hcmp2, hpa_eq⟩ :=
    alloc_body_run allocEntry hp 200#64 hcode hhp hn_entry rva (by rw [haRun])
  rw [haRun] at hpa_eq
  dsimp only at hpa_eq
  have hq_nat : q.toNat = hp.toNat + 200 := by
    have hand := InitECandidate.Solver.GuestTrapAndLookup.and_neg8_toNat (hp + (200#64 + 7#64))
    dsimp only [q]
    rw [hand]
    have hadd_nat : (hp + (200#64 + 7#64)).toNat = hp.toNat + 207 := by
      rw [BitVec.toNat_add_of_lt (by change hp.toNat + 207 < 2 ^ 64; omega)]
      rfl
    rw [hadd_nat]
    omega
  have hcmp2' : ¬ (cMax.toNat < q.toNat) := hcmp2
  have hq_le : q.toNat ≤ 2952790016 := by
    rw [← hcMax]; omega
  let s1 := setVarHOLFinite (ofString "te") (.val (.word hp)) { pa with locals := s.locals }
  have hs1_code : s1.code = originalRuntimeCode := by
    have hpa_c : pa.code = s.code := by rw [hpa_eq]; rfl
    exact hpa_c.trans hcode
  have hs1_memaddrs : s1.memaddrs = s.memaddrs := by
    rw [show s1.memaddrs = pa.memaddrs from rfl, hpa_eq]; rfl
  have hs1_te : s1.locals.lookup (ofString "te") = some (.val (.word hp)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  change evaluateHOLFiniteState s1 _ = (some (.returned retVal), inner) at hcont
  rw [evaluateHOLFiniteState_seq_line780] at hcont
  rcases hmzCall : evaluateHOLFiniteState s1
      (.call (some (none, none)) (ofString "memzero")
        [.var .local (ofString "te"), .const 200#64]) with ⟨rmz, pmz⟩
  have hmz_noret := call_void_noret_te s1 (ofString "memzero")
    [.var .local (ofString "te"), .const 200#64] retVal
  rw [hmzCall] at hcont hmz_noret
  cases rmz with
  | some rmz' =>
    dsimp only at hcont hmz_noret
    exact absurd (congrArg Prod.fst hcont) hmz_noret
  | none =>
    dsimp only at hcont
    have hargs2 : evalListHOLFinite s1
        (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "te"), .const 200#64] =
        some [.val (.word hp), .val (.word 200#64)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, evalHOLExact, hs1_te]
    obtain ⟨rvmz, pmzb, hmzBody, hpmz_eq⟩ :=
      call_two_words_void hs1_code (by decide) lookup_memzero hargs2 hmzCall
    let mzEntry := callEntryStateHOLFinite s1
      ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word hp))).update
        (ofString "n", .val (.word 200#64)))
    have hmz_dst : mzEntry.locals.lookup (ofString "dst") = some (.val (.word hp)) := by
      simp [mzEntry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide]
    have hmz_n : mzEntry.locals.lookup (ofString "n") = some (.val (.word 200#64)) := by
      simp [mzEntry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hmz_dom : ∀ off : Nat, off < 200 → off % 8 = 0 →
        mzEntry.memaddrs (hp + BitVec.ofNat 64 off) := by
      intro off hoff hmod
      change s1.memaddrs _
      rw [hs1_memaddrs]
      exact hdom_fn q hq_le hq_nat off hoff hmod
    have hpmzb := memzero_200_body_run mzEntry pmzb hp rvmz hmz_dst hmz_n hp_align
      hmz_dom hmzBody
    have hpmz_te : pmz.locals.lookup (ofString "te") = some (.val (.word hp)) := by
      rw [hpmz_eq]; exact hs1_te
    have hret_te : evaluateHOLFiniteState pmz (.return (.var .local (ofString "te"))) =
        (some (.returned (.val (.word hp))), pmz.emptyLocalsHOLFinite) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, lookupKvarHOLExact, hpmz_te,
        shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hret_te] at hcont
    obtain ⟨hv_eq, hinner_eq⟩ := Prod.mk.inj hcont
    simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hv_eq
    have hpa_mem : pa.memory = s.memory := by rw [hpa_eq]; rfl
    have hpa_glob : pa.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
      rw [hpa_eq]; rfl
    have hpa_code : pa.code = s.code := by rw [hpa_eq]; rfl
    have hpa_memaddrs : pa.memaddrs = s.memaddrs := by rw [hpa_eq]; rfl
    have hpa_sh : pa.shMemaddrs = s.shMemaddrs := by rw [hpa_eq]; rfl
    have hpa_base : pa.baseAddr = s.baseAddr := by rw [hpa_eq]; rfl
    refine ⟨hv_eq.symm, hq_nat, hq_le, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpost_inner, ← hinner_eq]; dsimp only [emptyLocalsHOLFinite]
      rw [hpmz_eq, hpmzb]; dsimp only
      exact congrArg (fun m => zeroBlock25 m hp) hpa_mem
    · rw [hpost_inner, ← hinner_eq]; dsimp only [emptyLocalsHOLFinite]
      rw [hpmz_eq, hpmzb]; dsimp only
      exact hpa_glob
    · rw [hpost_inner, ← hinner_eq]; dsimp only [emptyLocalsHOLFinite]
      rw [hpmz_eq, hpmzb]; dsimp only
      exact hpa_code
    · rw [hpost_inner, ← hinner_eq]; dsimp only [emptyLocalsHOLFinite]
      rw [hpmz_eq, hpmzb]; dsimp only
      exact hpa_memaddrs
    · rw [hpost_inner, ← hinner_eq]; dsimp only [emptyLocalsHOLFinite]
      rw [hpmz_eq, hpmzb]; dsimp only
      exact hpa_sh
    · rw [hpost_inner, ← hinner_eq]; dsimp only [emptyLocalsHOLFinite]
      rw [hpmz_eq, hpmzb]; dsimp only
      exact hpa_base

end InitECandidate.Solver.Wave8Contracts.M27
