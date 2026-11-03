import InitECandidate.Solver.Wave8GuestInv.Primitives
import InitECandidate.Solver.GuestTrapAndLookup
import InitECandidate.Solver.GuestTrapAlign
import InitECandidate.Solver.HeapPotential

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.P02

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential

private theorem funBounded_node_new_leaf : FunBounded (ofString "node_new_leaf") 2 := by
  refine InitECandidate.Solver.GuestUniformClockBound.funBounded_of_guestAst 256 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_node_new_leaf 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_node_new_leaf,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall InitECandidate.Solver.GuestUniformClockBound.funBounded_alloc _ _ _
      (ProgBounded.straight _ rfl))
    (by decide)

theorem fb_node_new_leaf : TerminatingFunBoundedOn GuestInv (ofString "node_new_leaf") K.«node_new_leaf» := by
  apply TerminatingFunBoundedOn.of_unconditional
  apply TerminatingFunBounded.weaken
    (InitECandidate.Solver.PanTerminatingBounded.terminatingFunBounded_of_funBounded funBounded_node_new_leaf)
  unfold K.«node_new_leaf» K.«alloc» K.«trap_with»
  decide

theorem ro_scratch_mark : ReadOnlyFn (ofString "scratch_mark") := by
  refine ⟨_, _, _, InitECandidate.Solver.GuestTrapAndLookup.lookup_of_guestAst_getElem 14 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_mark) rfl, ?_⟩
  intro F s hcode hInv hlookup hnt hres
  dsimp only [extractFn, Guest.Software.guestFn_scratch_mark,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hres ⊢
  simp only [evaluateHOLFiniteState_return] at hres ⊢
  split
  · rename_i heq
    simp [Resumes, heq] at hres
  · rename_i value heq
    split
    · rw [hcode]
      rw [← hcode]
      cases s
      rfl
    · rename_i hsz
      simp [Resumes, heq, hsz] at hres
theorem globWord_of_pos {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String)
    (hpos : 0 < globN s name) :
    ∃ w : BitVec 64, s.globals.lookup (ofString name) = some (.val (.word w)) ∧
      w.toNat = globN s name := by
  unfold globN at hpos ⊢
  rcases hg : s.globals.lookup (ofString name) with _ | v
  · simp [hg] at hpos
  · rcases v with ⟨⟨w⟩⟩ | _ | _
    · exact ⟨w, rfl, by simp [hg]⟩
    · simp [hg] at hpos
    · simp [hg] at hpos

theorem arenaOK_globals {F : Type} (s : PanSemStateFiniteExact 64 F) (hA : ArenaOK s) :
    ∃ hp fp sp : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) ∧
      hp.toNat = globN s "heap_ptr" ∧
      s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)) ∧
      fp.toNat = globN s "frame_mem_ptr" ∧
      s.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) ∧
      sp.toNat = globN s "scratch_ptr" := by
  have hsb : 0 < sourceBase := by decide
  have hss : 0 < scratchStart := by decide
  obtain ⟨hp, hhp, hhp_eq⟩ := globWord_of_pos s "heap_ptr" (by have := hA.1; omega)
  obtain ⟨fp, hfp, hfp_eq⟩ := globWord_of_pos s "frame_mem_ptr" (by have := hA.2.2.1; omega)
  obtain ⟨sp, hsp, hsp_eq⟩ := globWord_of_pos s "scratch_ptr"
    (by have := hA.2.2.1; have := hA.2.2.2.1; omega)
  exact ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩

theorem not_resumes_error : ¬ Resumes (some .error) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

theorem evaluate_call_trap_with_not_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    ¬ Resumes (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 := by
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const codeVal] =
      some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlookup := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal (by rw [hcode]; exact lookup_trap_with)
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  split
  · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hbody] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | exception eid v =>
        dsimp only
        rintro (⟨_, h⟩ | ⟨e', v', h, hne⟩)
        · simp at h
        · injection h with h'
          cases h'
          exact hout.2.2 eid v hne rfl
      | «break» | «continue» | error | timeOut | finalFfi _ =>
        rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h



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
      exact ⟨hr'.symm, hcmp1, hcmp2, rfl⟩


theorem alloc_arith (p n : BitVec 64)
    (hp_hi : p.toNat ≤ heapLimit) (hp_al : p.toNat % 8 = 0)
    (hcmp1 : ¬ ((cMax - p).toNat < n.toNat))
    (hcmp2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    q.toNat = p.toNat + (n.toNat + 7) / 8 * 8 ∧
    q.toNat ≤ heapLimit ∧ q.toNat % 8 = 0 ∧ p.toNat ≤ q.toNat := by
  intro q
  have hcMax : cMax.toNat = 2952790016 := rfl
  have hlim : heapLimit = 2952790016 := by decide
  have hsub : (cMax - p).toNat = 2952790016 - p.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hn_le : n.toNat ≤ 2952790016 - p.toNat := by omega
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  have hn7 : (n + 7).toNat = n.toNat + 7 := by
    rw [BitVec.toNat_add, h7]; omega
  have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by
    rw [BitVec.toNat_add, hn7]; omega
  have hq_nat : q.toNat = (p + (n + 7)).toNat / 8 * 8 := and_neg8_toNat (p + (n + 7))
  rw [hsum] at hq_nat
  have hq_le : q.toNat ≤ cMax.toNat := Nat.le_of_not_lt hcmp2
  exact ⟨by omega, by omega, by omega, by omega⟩




/-! ## 4. Normal-return combinators (`Ret` and `NS`) -/

def Ret {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) → Φ v (evaluateHOLFiniteState s p).2

noncomputable abbrev ev {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e

theorem Ret.seq {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (ha : Ret s a Φ) (hb : ∀ t, evaluateHOLFiniteState s a = (none, t) → Ret t b Φ) :
    Ret s (.seq a b) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780] at hv ⊢
  rcases h : evaluateHOLFiniteState s a with ⟨r, t⟩
  simp only [h] at hv
  try simp only [h]
  cases r with
  | none => exact hb t h v hv
  | some r' =>
    have := ha v (by rw [h]; exact hv)
    rw [h] at this
    exact this

def updW (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun c => if c = a then .word w else m c

theorem stores_word {dom : BitVec 64 → Prop} (inst : DecidablePred dom)
    {m m' : BitVec 64 → HolWordLab 64}
    {a w : BitVec 64}
    (h : @panMemStoresHOL 64 _ a (flattenHOL (.val (.word w))) dom inst m = some m') :
    dom a ∧ m' = updW m a w := by
  unfold flattenHOL at h
  unfold panMemStoresHOL at h
  unfold panMemStoreHOL at h
  by_cases hd : dom a
  · simp only [hd, ↓reduceIte] at h
    simp only [panMemStoresHOL, Option.some.injEq] at h
    exact ⟨hd, h.symm⟩
  · simp [hd] at h

theorem Ret.seq_store {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hb : ∀ (a : BitVec 64) (val : ValueHOL 64) m, ev s d = some (.val (.word a)) →
      ev s e = some val →
      @panMemStoresHOL 64 _ a (flattenHOL val) s.memaddrs
        (fun x => Classical.propDecidable (s.memaddrs x)) s.memory = some m →
      Ret { s with memory := m } b Φ) :
    Ret s (.seq (.store d e) b) Φ := by
  refine Ret.seq ?_ ?_
  · intro v hv
    rw [evaluateHOLFiniteState_store] at hv
    revert hv
    split
    · split
      · split <;> simp
      · simp
    · simp
  · intro t ht
    rw [evaluateHOLFiniteState_store] at ht
    revert ht
    split
    · rename_i a hd
      split
      · rename_i val he
        split
        · rename_i m hm
          intro ht
          simp only [Prod.mk.injEq] at ht
          rw [← ht.2]
          exact hb a val m hd he hm
        · simp
      · simp
    · simp

theorem Ret.seq_storeW {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a w : BitVec 64) (hd : ev s d = some (.val (.word a))) (he : ev s e = some (.val (.word w)))
    (hb : s.memaddrs a → Ret { s with memory := updW s.memory a w } b Φ) :
    Ret s (.seq (.store d e) b) Φ := by
  apply Ret.seq_store
  intro a' val m hd' he' hm
  rw [hd] at hd'
  rw [he] at he'
  simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hd' he'
  subst hd' he'
  obtain ⟨hdom, rfl⟩ := stores_word _ hm
  exact hb hdom

theorem Ret.dec {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev s init = some val →
      Ret (setVarHOLFinite x val s) body
        (fun v t => Φ v { t with
          locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.dec x sh init body) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_dec_total] at hv ⊢
  dsimp only at hv ⊢
  revert hv
  split
  · simp
  · rename_i val hval
    split
    · intro hv
      exact h val hval v hv
    · simp

theorem Ret.ret {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev s e = some val → Φ val (emptyLocalsHOLFinite s)) :
    Ret s (.return e) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_return] at hv ⊢
  revert hv
  split
  · simp
  · rename_i val hval
    split
    · intro hv
      simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hv
      subst hv
      exact h _ hval
    · simp

theorem Ret.decCall1 {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname : MlS}
    {arg : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(ofString "n", .one)], fbody, .one))
    (nv : BitVec 64) (harg : ev s arg = some (.val (.word nv)))
    (hk : ∀ w post,
      evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        fbody = (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont
        (fun v t => Φ v { t with
          locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one fname [arg] cont) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] =
      some [.val (.word nv)] := by
    simp only [ev] at harg
    simp [evalListHOLFinite, evalListHOLExact, harg]
  have hl := pan_one_word_lookup s.code.lookup fname (ofString "n") fbody nv
    (by rw [hcode]; exact hlook)
  rw [hargs] at hv ⊢
  dsimp only at hv ⊢
  rw [hl] at hv ⊢
  dsimp only at hv ⊢
  revert hv
  split
  · simp
  · rw [fixClockHOLFinite_evaluateState]
    rcases hrun : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        fbody with ⟨r, post⟩
    dsimp only
    rcases r with _ | r
    · simp
    · cases r with
      | returned rv =>
        dsimp only
        split
        · rename_i hsh
          rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
          · intro hv
            exact hk w post hrun v hv
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · simp
      | _ => simp

theorem Ret.decCall_alloc {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS}
    {arg : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (nv : BitVec 64)
    (harg : ev s arg = some (.val (.word nv))) (p : BitVec 64)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hk : ¬ ((cMax - p).toNat < nv.toNat) →
      ¬ (cMax.toNat < ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)).toNat) →
      Ret (setVarHOLFinite x (.val (.word p)) { s with
          globals := (s.globals.update (ofString "heap_ptr",
            .val (.word ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)))))
          clock := s.clock - 1 }) cont
        (fun v t => Φ v { t with
          locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one (ofString "alloc") [arg] cont) Φ := by
  refine Ret.decCall1 hcode lookup_alloc nv harg ?_
  intro w post hrun
  have hn : (callEntryStateHOLFinite s
      (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))).locals.lookup (ofString "n") =
      some (.val (.word nv)) := by
    simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have := alloc_body_run (callEntryStateHOLFinite s
    (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))) p nv hcode hp hn
    (.val (.word w)) (by rw [hrun])
  rw [hrun] at this
  obtain ⟨hw, h1, h2, hpost⟩ := this
  simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at hw
  subst hw
  have hst : { post with locals := s.locals } = { s with
      globals := (s.globals.update (ofString "heap_ptr",
        .val (.word ((w + (nv + 7)) &&& ((0 : BitVec 64) - 8)))))
      clock := s.clock - 1 } := by
    dsimp only at hpost
    rw [hpost]; rfl
  rw [hst]
  exact hk h1 h2

def NS {F : Type} (s : PanSemStateFiniteExact 64 F) (L G : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C : Nat) : PanSemStateFiniteExact 64 F :=
  { s with locals := L, globals := G, memory := M, clock := C }

section NSlemmas
variable {F : Type} (s : PanSemStateFiniteExact 64 F) (L G : HolFiniteMapExact MlS (ValueHOL 64))
  (M : BitVec 64 → HolWordLab 64) (C : Nat)
@[simp] theorem NS_locals : (NS s L G M C).locals = L := rfl
@[simp] theorem NS_globals : (NS s L G M C).globals = G := rfl
@[simp] theorem NS_memory : (NS s L G M C).memory = M := rfl
@[simp] theorem NS_clock : (NS s L G M C).clock = C := rfl
@[simp] theorem NS_code : (NS s L G M C).code = s.code := rfl
@[simp] theorem NS_memaddrs : (NS s L G M C).memaddrs = s.memaddrs := rfl
@[simp] theorem NS_toExact_memaddrs : (NS s L G M C).toExact.memaddrs = s.memaddrs := rfl
end NSlemmas

theorem Ret.of_NS {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : Ret (NS s s.locals s.globals s.memory s.clock) p Φ) : Ret s p Φ := by
  cases s; exact h

theorem Ret.ns_storeW {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {d e : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a w : BitVec 64) (hd : ev (NS s L G M C) d = some (.val (.word a)))
    (he : ev (NS s L G M C) e = some (.val (.word w)))
    (hb : s.memaddrs a → Ret (NS s L G (updW M a w) C) b Φ) :
    Ret (NS s L G M C) (.seq (.store d e) b) Φ :=
  Ret.seq_storeW a w hd he hb

theorem Ret.ns_dec {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {x : MlS}
    {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev (NS s L G M C) init = some val →
      Ret (NS s (L.update (x, val)) G M C) body
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, L.lookup x) })) :
    Ret (NS s L G M C) (.dec x sh init body) Φ :=
  Ret.dec h

theorem Ret.ns_alloc {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {x : MlS}
    {arg : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (nv : BitVec 64)
    (harg : ev (NS s L G M C) arg = some (.val (.word nv))) (p : BitVec 64)
    (hp : G.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hk : ¬ ((cMax - p).toNat < nv.toNat) →
      ¬ (cMax.toNat < ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)).toNat) →
      Ret (NS s (L.update (x, .val (.word p)))
          (G.update (ofString "heap_ptr", .val (.word ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)))))
          M (C - 1)) cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, L.lookup x) })) :
    Ret (NS s L G M C) (.decCall x .one (ofString "alloc") [arg] cont) Φ :=
  Ret.decCall_alloc hcode nv harg p hp hk

theorem Ret.ns_ret {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {e : ExpHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev (NS s L G M C) e = some val →
      Φ val (NS s (emptyLocalsHOLFinite (NS s L G M C)).locals G M C)) :
    Ret (NS s L G M C) (.return e) Φ :=
  Ret.ret h

theorem ofNat_add_toNat_eq (p : BitVec 64) (k : Nat) :
    BitVec.ofNat 64 (p.toNat + k) = p + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem scratch_alloc_body_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p f : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf_lookup : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)
    Resumes out.1 →
      ∃ n : BitVec 64,
        state.locals.lookup (ofString "n") = some (.val (.word n)) ∧
        let q := (p - n) &&& ((0 : BitVec 64) - 8)
        out.1 = some (.returned (.val (.word q))) ∧
        ¬ ((p - f).toNat < n.toNat) ∧ ¬ (q.toNat < f.toNat) ∧
        out.2 = { state with
          globals := state.globals.update (ofString "scratch_ptr", .val (.word q))
          locals := out.2.locals } := by
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
  have hn_eq : pState.locals.lookup (ofString "n") = state.locals.lookup (ofString "n") := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "n" by decide]
  have hf_g : pState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) := hf_lookup
  have hcode_p : pState.code = originalRuntimeCode := hcode
  rcases hn : state.locals.lookup (ofString "n") with _ | vn
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    have hnone : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
          (.var .local (ofString "n"))) = none := by
      simp [evalHOLExact, evalListHOLExact, hp_loc, hn_eq, hn, hf_g]
    rw [hnone]
    intro hr; exact absurd hr not_resumes_error
  · rcases vn with ⟨⟨n⟩⟩ | _ | _
    · have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
        rw [hn_eq, hn]
      rw [evaluateHOLFiniteState_seq_line780]
      have hev1 : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n"))) =
          some (.val (.word (if (p - f).toNat < n.toNat then 1 else 0))) := by
        simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc, hf_g,
          Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
        simp [wordOpHOL, wordOp, valueIsWord, valueWord]
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
        have hno_res := evaluate_call_trap_with_not_resumes pState 7 hcode_p
        rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r1, s1⟩
        rw [htr] at hno_none hno_res
        cases r1 with
        | none => exact absurd rfl hno_none
        | some r1' => intro hr; exact absurd hr hno_res
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
            wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
          have h2 : AndOp.and ((0 : BitVec 64) - 8) (~~~0) = (0 : BitVec 64) - 8 := by decide
          simp only [h2]
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
        have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
            show ofString "q" ≠ ofString "p" by decide]
        have hcode_q : qState.code = originalRuntimeCode := hcode
        rw [evaluateHOLFiniteState_seq_line780]
        have hev2 : @evalHOLExact 64 F _ qState.toExact
            (fun a => Classical.propDecidable (qState.memaddrs a))
            (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr"))) =
            some (.val (.word (if q.toNat < f.toNat then 1 else 0))) := by
          have hf_q : qState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) := hf_lookup
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
          have hno_res := evaluate_call_trap_with_not_resumes qState 7 hcode_q
          rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r2, s2⟩
          rw [htr] at hno_none hno_res
          cases r2 with
          | none => exact absurd rfl hno_none
          | some r2' => intro hr; exact absurd hr hno_res
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
            simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
              shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
              evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
          rw [heval_end]
          intro _
          exact ⟨n, rfl, rfl, hcmp1, hcmp2, rfl⟩
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      have hnone : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n"))) = none := by
        simp [evalHOLExact, evalListHOLExact, hp_loc, hn_eq, hn, hf_g, valueIsWord]
      rw [hnone]
      intro hr; exact absurd hr not_resumes_error
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      have hnone : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n"))) = none := by
        simp [evalHOLExact, evalListHOLExact, hp_loc, hn_eq, hn, hf_g, valueIsWord]
      rw [hnone]
      intro hr; exact absurd hr not_resumes_error

theorem scratch_alloc_arith (sp fp n : BitVec 64)
    (hfp_le_sp : fp.toNat ≤ sp.toNat) (hsp_al : sp.toNat % 8 = 0)
    (hcmp1 : ¬ ((sp - fp).toNat < n.toNat))
    (hcmp2 : ¬ (((sp - n) &&& ((0 : BitVec 64) - 8)).toNat < fp.toNat)) :
    let q := (sp - n) &&& ((0 : BitVec 64) - 8)
    q.toNat % 8 = 0 ∧ fp.toNat ≤ q.toNat ∧ q.toNat ≤ sp.toNat ∧
    q.toNat + (n.toNat + 7) / 8 * 8 = sp.toNat := by
  intro q
  have hsp_lt := sp.isLt
  have hfp_lt := fp.isLt
  have hsub_pf : (sp - fp).toNat = sp.toNat - fp.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hn_le_gap : n.toNat ≤ sp.toNat - fp.toNat := by omega
  have hn_le_sp : n.toNat ≤ sp.toNat := by omega
  have hsub_pn : (sp - n).toNat = sp.toNat - n.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hq_nat : q.toNat = (sp.toNat - n.toNat) / 8 * 8 := by
    have h := and_neg8_toNat (sp - n)
    rw [hsub_pn] at h
    exact h
  have hq_ge_fp : fp.toNat ≤ q.toNat := Nat.le_of_not_lt hcmp2
  exact ⟨by omega, hq_ge_fp, by omega, by omega⟩


theorem addresses_iff (b : BitVec 64) (n : Nat) (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      ∃ i, i < n ∧ x = b + BitVec.ofNat 64 (8 * i) := by
  induction n generalizing b with
  | zero => simp [Flapjack.Compiler.Backend.StackRemove.addresses]
  | succ n ih =>
    simp only [Flapjack.Compiler.Backend.StackRemove.addresses,
      Flapjack.Compiler.Backend.StackRemove.bytesInWord]
    rw [ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨i + 1, by omega, ?_⟩
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega
    · rintro ⟨i, hi, rfl⟩
      rcases i with _ | i
      · left; simp
      · right
        refine ⟨i, by omega, ?_⟩
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega

theorem ordinaryDomain_eq : ordinaryDomain =
    Flapjack.Compiler.Backend.StackRemove.addresses (BitVec.ofNat 64 2701131776) 3888119741 := by
  have h1 : (BitVec.ofNat 64 sourceBase) = BitVec.ofNat 64 2701131776 := rfl
  have h2 : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 := by decide
  unfold ordinaryDomain
  rw [h1, h2]

theorem addresses_iff_nat (b : BitVec 64) (n : Nat) (hb : b.toNat + 8 * n ≤ 2 ^ 64)
    (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      b.toNat ≤ x.toNat ∧ x.toNat < b.toNat + 8 * n ∧ (x.toNat - b.toNat) % 8 = 0 := by
  rw [addresses_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : (b + BitVec.ofNat 64 (8 * i)).toNat = b.toNat + 8 * i := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [this]
    omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(x.toNat - b.toNat) / 8, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd ∧ x.toNat % 8 = 0 := by
  have hb : (BitVec.ofNat 64 2701131776).toNat = 2701131776 := rfl
  have hsb : sourceBase = 2701131776 := by decide
  have hhe : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  rw [ordinaryDomain_eq, addresses_iff_nat _ _ (by rw [hb]; norm_num), hb, hsb, hhe]
  omega

theorem ordinaryDomain_of_nat (a : Nat) (hlo : sourceBase ≤ a) (hhi : a < heapEnd)
    (hal : a % 8 = 0) : ordinaryDomain (BitVec.ofNat 64 a) := by
  have hlt : a < 2 ^ 64 := by
    have : heapEnd < 2 ^ 64 := by decide
    omega
  have hbv : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [ordinaryDomain_iff, hbv]
  exact ⟨hlo, hhi, hal⟩

theorem wordsOK_of_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (p len : Nat) (hp : p % 8 = 0) (hlen : len % 8 = 0)
    (hlo : sourceBase ≤ p) (hhi : p + len ≤ heapEnd) :
    WordsOK s (p, len) := by
  refine ⟨hp, hlen, ?_⟩
  intro k hk
  rcases hmem : s.memory (BitVec.ofNat 64 (p + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hmem⟩
  rw [hG.memaddrs]
  exact ordinaryDomain_of_nat (p + 8 * k) (by omega) (by omega) (by omega)


theorem node_new_ext_params {F : Type} (s : PanSemStateFiniteExact 64 F)
  (h : ∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_ext") values =
    some (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_node_new_ext).body, s.locals,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural
      (extractFn Guest.Software.guestFn_node_new_ext).returnShape)) :
  ∃ a b c : BitVec 64, s.locals.lookup (ofString "nib") = some (.val (.word a)) ∧
   s.locals.lookup (ofString "nlen") = some (.val (.word b)) ∧
   s.locals.lookup (ofString "child") = some (.val (.word c)) := by
  obtain ⟨vs, hv⟩ := h
  have hlook : originalRuntimeCode.lookup (ofString "node_new_ext") =
      some ([(ofString "nib", .one), (ofString "nlen", .one), (ofString "child", .one)],
        sourceFnBody Guest.Software.guestFn_node_new_ext, .one) :=
    lookup_of_guestAst_getElem 257 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_node_new_ext) rfl
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "node_new_ext") vs
    (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_node_new_ext).body) s.locals
    (InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural
      (extractFn Guest.Software.guestFn_node_new_ext).returnShape) hv
  simp [lookupCodeHOLExact, hlook] at hx
  rcases vs with _ | ⟨v1, vs⟩ <;> simp at hx
  rcases vs with _ | ⟨v2, vs⟩ <;> simp at hx
  rcases vs with _ | ⟨v3, vs⟩ <;> simp at hx
  rcases vs with _ | ⟨v4, vs⟩ <;> simp at hx
  have hshape1 := hx.1.2 (ofString "nib") .one v1 (Or.inl ⟨⟨rfl, rfl⟩, rfl⟩)
  have hshape2 := hx.1.2 (ofString "nlen") .one v2 (Or.inr (Or.inl ⟨⟨rfl, rfl⟩, rfl⟩))
  have hshape3 := hx.1.2 (ofString "child") .one v3 (Or.inr (Or.inr ⟨⟨rfl, rfl⟩, rfl⟩))
  have h12 := hx.1.1.1.1
  have h13 := hx.1.1.1.2
  have h23 := hx.1.1.2
  have hnib : s.locals.lookup (ofString "nib") = some v1 := by rw [← hx.2.2.1]; simp [h12, h13, h23]
  have hnlen : s.locals.lookup (ofString "nlen") = some v2 := by rw [← hx.2.2.1]; simp [h12, h13, h23]
  have hchild : s.locals.lookup (ofString "child") = some v3 := by rw [← hx.2.2.1]; simp [h12, h13, h23]
  rcases v1 with ⟨⟨a⟩⟩ | fs | ⟨nm, fs⟩ <;> simp [shapeEqHOL, shapeOfHOLExact] at hshape1
  · rcases v2 with ⟨⟨b⟩⟩ | fs | ⟨nm, fs⟩ <;> simp [shapeEqHOL, shapeOfHOLExact] at hshape2
    · rcases v3 with ⟨⟨c⟩⟩ | fs | ⟨nm, fs⟩ <;> simp [shapeEqHOL, shapeOfHOLExact] at hshape3
      · exact ⟨a,b,c,hnib,hnlen,hchild⟩

theorem lookup_node_new_ext :
    originalRuntimeCode.lookup (ofString "node_new_ext") =
      some ([(ofString "nib", .one), (ofString "nlen", .one), (ofString "child", .one)],
        sourceFnBody Guest.Software.guestFn_node_new_ext, .one) :=
  lookup_of_guestAst_getElem 257 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_ext) rfl

theorem Ret.seq_store_any {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hb : ∀ m : BitVec 64 → HolWordLab 64, Ret { s with memory := m } b Φ) :
    Ret s (.seq (.store d e) b) Φ :=
  Ret.seq_store (fun _ _ m _ _ _ => hb m)

theorem Ret.ns_store_any {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {d e : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hb : ∀ M' : BitVec 64 → HolWordLab 64, Ret (NS s L G M' C) b Φ) :
    Ret (NS s L G M C) (.seq (.store d e) b) Φ :=
  Ret.seq_store_any hb

/-- `node_new_ext` (AST line 10021): returns a fresh 56-byte heap node, separated from the decoder
scratch stack. -/
theorem rt_node_new_ext :
    Returns ArenaReady (fun s post p => FreshBlock s post p 56)
    (ofString "node_new_ext") := by
  refine ⟨_, _, _, lookup_node_new_ext, ?_⟩
  intro F s hcode hAR _hlookup _hnt v hret
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_ext =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 56]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0]) (.const 2))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8]) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16]) (.const 0))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24]) (.const 0))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const 32]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const 40]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const 48]) (.var .local (ofString "child")))
                      (.return (.var .local (ofString "nd")))))))))) := rfl
  have hrun : Ret s (sourceFnBody Guest.Software.guestFn_node_new_ext)
      (fun rv post => ∃ w : BitVec 64, rv = .val (.word w) ∧
        ArenaReady post ∧ AllocatorGrows s post ∧ FreshBlock s post w.toNat 56) := by
    rw [hbody]
    apply Ret.of_NS
    refine Ret.ns_alloc hcode 56 rfl hp hhp ?_
    intro hcmp1 hcmp2
    apply Ret.ns_store_any; intro M1
    apply Ret.ns_store_any; intro M2
    apply Ret.ns_store_any; intro M3
    apply Ret.ns_store_any; intro M4
    apply Ret.ns_store_any; intro M5
    apply Ret.ns_store_any; intro M6
    apply Ret.ns_store_any; intro M7
    apply Ret.ns_ret
    intro val hval
    have hval_eq : val = .val (.word hp) := by
      simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE] at hval
      exact hval.symm
    subst hval_eq
    set q : BitVec 64 := (hp + (56 + 7)) &&& ((0 : BitVec 64) - 8)
    set post : PanSemStateFiniteExact 64 F :=
      { (NS s (emptyLocalsHOLFinite (NS s (s.locals.update (ofString "nd", .val (.word hp)))
            (s.globals.update (ofString "heap_ptr", .val (.word q))) M7 (s.clock - 1))).locals
          (s.globals.update (ofString "heap_ptr", .val (.word q))) M7 (s.clock - 1)) with
        locals := HolFiniteMapExact.resVarEq
          (emptyLocalsHOLFinite (NS s (s.locals.update (ofString "nd", .val (.word hp)))
            (s.globals.update (ofString "heap_ptr", .val (.word q))) M7 (s.clock - 1))).locals
          (ofString "nd", s.locals.lookup (ofString "nd")) }
    refine ⟨hp, rfl, ?_⟩
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := alloc_arith hp 56 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = _ at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    change q.toNat % 8 = 0 at hq_al
    change hp.toNat ≤ q.toNat at hp_le_q
    have h56 : ((56 : BitVec 64).toNat + 7) / 8 * 8 = 56 := by decide
    rw [h56] at hq_eq
    have hpost_hp : globN post "heap_ptr" = q.toNat := by
      simp [post, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      simp [post, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
      simp [post, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hG_post : GuestInv post := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
    have hA_post : ArenaOK post := by
      unfold ArenaOK
      rw [hpost_hp, hpost_fp, hpost_sp]
      refine ⟨?_, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1,
        hA.2.2.2.2.2.2.2.1, globalsWord_update (ofString "heap_ptr") q rfl hA.2.2.2.2.2.2.2.2⟩
      have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
      omega
    have hAG : AllocatorGrows s post := by
      refine ⟨?_, by rw [hpost_sp]⟩
      rw [hpost_hp, ← hhp_eq]
      exact hp_le_q
    have hlim_le_he : heapLimit ≤ heapEnd := by decide
    have hWOK : WordsOK post (hp.toNat, (56 + 7) / 8 * 8) := by
      change WordsOK post (hp.toNat, 56)
      apply wordsOK_of_guestInv post hG_post hp.toNat 56 hhp_al (by decide)
      · rw [hhp_eq]; exact hA.1
      · omega
    refine ⟨⟨hG_post, hA_post⟩, hAG, hhp_al, ?_, hWOK⟩
    change Inside (hp.toNat, 56) (globN s "heap_ptr") (globN post "heap_ptr")
    rw [← hhp_eq, hpost_hp]
    exact ⟨le_rfl, le_of_eq hq_eq.symm⟩
  exact hrun v hret

theorem ww_scratch_alloc : WritesWithin (fun s => []) ["scratch_ptr"] (ofString "scratch_alloc") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_alloc) rfl, ?_⟩
  intro F s hcode hArena hlookup hnt hres
  obtain ⟨hG, hA⟩ := hArena
  have hA' := hA
  unfold ArenaOK at hA'
  obtain ⟨hbase, hlimit, hsstart, hframe, hsend, hpalign, hfpalign, hspalign, hgw⟩ := hA'
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_scratch_alloc =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_scratch_alloc).body := by rfl
  have hres' : Resumes (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_scratch_alloc)).1 := by
    rw [hbody]
    exact hres
  obtain ⟨n, hn, hret, hc1, hc2, hpost⟩ :=
    scratch_alloc_body_resumes s sp fp hcode hsp hfp hres'
  have hfp_sp : fp.toNat ≤ sp.toNat := by rw [hfp_eq, hsp_eq]; exact hA.2.2.2.1
  have hsp_al : sp.toNat % 8 = 0 := by rw [hsp_eq]; exact hA.2.2.2.2.2.2.2.1
  have hq := scratch_alloc_arith sp fp n hfp_sp hsp_al hc1 hc2
  let q := (sp - n) &&& ((0 : BitVec 64) - 8)
  have hq_eq : q = (sp - n) &&& ((0 : BitVec 64) - 8) := rfl
  have hsp_hp : (ofString "scratch_ptr" : MlS) ≠ ofString "heap_ptr" := by decide
  have hsp_fp : (ofString "scratch_ptr" : MlS) ≠ ofString "frame_mem_ptr" := by decide
  rw [hbody] at hpost
  rw [hpost]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩, ?_⟩
    have hgw_post : GlobalsWord { s with
        locals := (emptyLocalsHOLFinite s).locals
        globals := s.globals.update (ofString "scratch_ptr", .val (.word q)) } :=
      globalsWord_update (ofString "scratch_ptr") q rfl hgw
    unfold ArenaOK
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hgw_post⟩
    all_goals (
      dsimp [q] at hq
      simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, hhp, hfp, hsp, hsp_hp, hsp_fp] at hq ⊢
      try rw [← hhp_eq] at hbase hlimit hpalign
      try rw [← hfp_eq] at hsstart hframe hfpalign
      try rw [← hsp_eq] at hframe hsend hspalign
      omega)
  · simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, hhp, hsp_hp]
  · simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, hsp, hsp_hp]
    dsimp [q] at hq
    omega
  · intro a _ _
    rfl
  · intro k hk
    have hks : k ≠ ofString "scratch_ptr" := by simpa using hk
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hks, Ne.symm hks]

theorem alloc_body_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    Resumes out.1 →
      out.1 = some (.returned (.val (.word p))) ∧
      ¬ ((cMax - p).toNat < n.toNat) ∧ ¬ (cMax.toNat < q.toNat) ∧
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
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode_p
    have hno_res := evaluate_call_trap_with_not_resumes pState 1 hcode_p
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_res
    cases r1 with
    | none => exact absurd rfl hno_none
    | some r1' => intro hr; exact absurd hr hno_res
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
      have hno_res := evaluate_call_trap_with_not_resumes qState 1 hcode_q
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_res
      cases r2 with
      | none => exact absurd rfl hno_none
      | some r2' => intro hr; exact absurd hr hno_res
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
      intro _
      exact ⟨rfl, hcmp1, hcmp2, rfl⟩

theorem noExn_seq_store {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64}
    (hb : ∀ m : BitVec 64 → HolWordLab 64, ∀ eid ev,
      (evaluateHOLFiniteState { s with memory := m } b).1 ≠ some (.exception eid ev)) :
    ∀ eid ev, (evaluateHOLFiniteState s (.seq (.store d e) b)).1 ≠ some (.exception eid ev) := by
  intro eid ev
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
  split
  · split
    · split
      · exact hb _ eid ev
      · simp
    · simp
  · simp

theorem noExn_return {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64} :
    ∀ eid ev, (evaluateHOLFiniteState s (.return e)).1 ≠ some (.exception eid ev) := by
  intro eid ev
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

theorem ww_node_new_ext :
    WritesWithin (fun _s => []) ["heap_ptr"] (ofString "node_new_ext") := by
  refine ⟨_, _, _, lookup_node_new_ext, ?_⟩
  intro F s hcode hAR hlookup hnt hres
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_ext =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 56]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0]) (.const 2))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8]) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16]) (.const 0))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24]) (.const 0))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const 32]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const 40]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const 48]) (.var .local (ofString "child")))
                      (.return (.var .local (ofString "nd")))))))))) := rfl
  -- First show `node_new_ext` cannot resume via an exception, so `Resumes` implies `returned`!
  have hret_ex : ∃ v, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_ext)).1 =
      some (.returned v) := by
    rcases hres with ⟨v, hv⟩ | ⟨eid, ev_val, hexn, hne_trap⟩
    · exact ⟨v, hv⟩
    · exfalso
      rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hexn hnt
      have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const 56] =
          some [.val (.word 56)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
      have hl := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_alloc) 56 (by rw [hcode]; exact lookup_alloc)
      simp only [hargs, hl] at hexn hnt
      by_cases hclk0 : s.clock = 0
      · simp [hclk0] at hnt
      · simp only [hclk0, ↓reduceIte] at hexn hnt
        have hal := alloc_body_resumes (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 56))))
          hp 56 hcode hhp (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        rcases hrun : evaluateHOLFiniteState
            (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 56))))
            (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ar, apost⟩
        simp only [hrun] at hal hexn
        cases ar with
        | none => simp at hexn
        | some ar' =>
          cases ar' with
          | returned av =>
            obtain ⟨hav, _, _, _⟩ := hal (Or.inl ⟨av, rfl⟩)
            injection hav with hav'; injection hav' with hav''; subst hav''
            have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            simp only [hsh, ↓reduceIte] at hexn
            exact (noExn_seq_store fun _ => noExn_seq_store fun _ => noExn_seq_store fun _ =>
              noExn_seq_store fun _ => noExn_seq_store fun _ => noExn_seq_store fun _ =>
              noExn_seq_store fun _ => noExn_return) eid ev_val hexn
          | exception aeid aev =>
            dsimp only at hexn
            injection hexn with hexn'; injection hexn' with he1 he2; subst he1 he2
            have := hal (Or.inr ⟨aeid, aev, rfl, hne_trap⟩)
            cases this.1
          | _ => simp at hexn
  obtain ⟨rv, hrv⟩ := hret_ex
  -- Now evaluate the returned run with exact memory updates!
  obtain ⟨nibw, nlenw, childw, hnib, hnlen, hchild⟩ := node_new_ext_params s hlookup
  have hrun : Ret s (sourceFnBody Guest.Software.guestFn_node_new_ext)
      (fun _ post =>
        ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
        globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
        FrameOutside s post
          ([(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
          (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
        ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
          s.globals.lookup k = post.globals.lookup k) := by
    rw [hbody]
    apply Ret.of_NS
    refine Ret.ns_alloc hcode 56 rfl hp hhp ?_
    intro hcmp1 hcmp2
    have hnd0 : (s.locals.update (ofString "nd", .val (.word hp))).lookup (ofString "nd") =
        some (.val (.word hp)) := by
      simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hnib0 : (s.locals.update (ofString "nd", .val (.word hp))).lookup (ofString "nib") =
        some (.val (.word nibw)) := by
      simp [HolFiniteMapExact.lookup_update, FUPDATE, hnib, show ofString "nd" ≠ ofString "nib" by decide]
    have hnlen0 : (s.locals.update (ofString "nd", .val (.word hp))).lookup (ofString "nlen") =
        some (.val (.word nlenw)) := by
      simp [HolFiniteMapExact.lookup_update, FUPDATE, hnlen, show ofString "nd" ≠ ofString "nlen" by decide]
    have hchild0 : (s.locals.update (ofString "nd", .val (.word hp))).lookup (ofString "child") =
        some (.val (.word childw)) := by
      simp [HolFiniteMapExact.lookup_update, FUPDATE, hchild, show ofString "nd" ≠ ofString "child" by decide]
    have hev_add : ∀ {M0 C0} (off : BitVec 64),
        ev (NS s (s.locals.update (ofString "nd", .val (.word hp)))
          (s.globals.update (ofString "heap_ptr", .val (.word ((hp + (56 + 7)) &&& ((0 : BitVec 64) - 8)))))
          M0 C0) (.op .add [.var .local (ofString "nd"), .const off]) =
        some (.val (.word (hp + off))) := by
      intro M0 C0 off
      simp only [ev, evalHOLExact, evalListHOLExact, NS_locals, hnd0, wordOpHOL, wordOp,
        valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
        List.foldr]
      have hz : off + (0 : BitVec 64) = off := BitVec.add_zero off
      exact congrArg (fun x => some (ValueHOL.val (HolWordLab.word (hp + x)))) hz
    have hev_var : ∀ {M0 C0} (nm : MlS) (w : BitVec 64),
        (s.locals.update (ofString "nd", .val (.word hp))).lookup nm = some (.val (.word w)) →
        ev (NS s (s.locals.update (ofString "nd", .val (.word hp)))
          (s.globals.update (ofString "heap_ptr", .val (.word ((hp + (56 + 7)) &&& ((0 : BitVec 64) - 8)))))
          M0 C0) (.var .local nm) = some (.val (.word w)) := by
      intro M0 C0 nm w hlk
      simp only [ev, evalHOLExact, NS_locals, hlk]
    refine Ret.ns_storeW (hp + 0) 2 (hev_add 0) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 8) 0 (hev_add 8) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 16) 0 (hev_add 16) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 24) 0 (hev_add 24) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 32) nibw (hev_add 32) (hev_var _ _ hnib0) fun _ => ?_
    refine Ret.ns_storeW (hp + 40) nlenw (hev_add 40) (hev_var _ _ hnlen0) fun _ => ?_
    refine Ret.ns_storeW (hp + 48) childw (hev_add 48) (hev_var _ _ hchild0) fun _ => ?_
    apply Ret.ns_ret
    intro _ _
    set q : BitVec 64 := (hp + (56 + 7)) &&& ((0 : BitVec 64) - 8)
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := alloc_arith hp 56 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = _ at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    change q.toNat % 8 = 0 at hq_al
    change hp.toNat ≤ q.toNat at hp_le_q
    have h56 : ((56 : BitVec 64).toNat + 7) / 8 * 8 = 56 := by decide
    rw [h56] at hq_eq
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hoff_nat : ∀ (off : Nat), off ≤ 48 → (hp + BitVec.ofNat 64 off).toNat = hp.toNat + off := by
      intro off hoff
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
      rw [this]
      exact Nat.mod_eq_of_lt (by omega)
    set M7 := updW (updW (updW (updW (updW (updW (updW s.memory (hp + 0) 2) (hp + 8) 0) (hp + 16) 0) (hp + 24) 0) (hp + 32) nibw) (hp + 40) nlenw) (hp + 48) childw
    set post : PanSemStateFiniteExact 64 F :=
      { (NS s (emptyLocalsHOLFinite (NS s (s.locals.update (ofString "nd", .val (.word hp)))
            (s.globals.update (ofString "heap_ptr", .val (.word q))) M7 (s.clock - 1))).locals
          (s.globals.update (ofString "heap_ptr", .val (.word q))) M7 (s.clock - 1)) with
        locals := HolFiniteMapExact.resVarEq
          (emptyLocalsHOLFinite (NS s (s.locals.update (ofString "nd", .val (.word hp)))
            (s.globals.update (ofString "heap_ptr", .val (.word q))) M7 (s.clock - 1))).locals
          (ofString "nd", s.locals.lookup (ofString "nd")) }
    have hpost_hp : globN post "heap_ptr" = q.toNat := by
      simp [post, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      simp [post, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
      simp [post, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    change ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
      globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
      FrameOutside s post
        ([(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
        (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
      ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
        s.globals.lookup k = post.globals.lookup k
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩, ?_⟩
      unfold ArenaOK
      rw [hpost_hp, hpost_fp, hpost_sp]
      have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
      exact ⟨by omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1,
        hA.2.2.2.2.2.2.2.1, globalsWord_update (ofString "heap_ptr") q rfl hA.2.2.2.2.2.2.2.2⟩
    · rw [hpost_hp, ← hhp_eq]; exact hp_le_q
    · rw [hpost_sp]
    · intro a _ hfresh
      have hne_off : ∀ (off : Nat), off ≤ 48 → a ≠ hp + BitVec.ofNat 64 off := by
        intro off hoff heq
        subst heq
        apply hfresh
        unfold CellHits
        have hn := hoff_nat off hoff
        rw [hn, ← hhp_eq]
        dsimp only
        omega
      have n0 : a ≠ hp + (0 : BitVec 64) := hne_off 0 (by omega)
      have n8 : a ≠ hp + (8 : BitVec 64) := hne_off 8 (by omega)
      have n16 : a ≠ hp + (16 : BitVec 64) := hne_off 16 (by omega)
      have n24 : a ≠ hp + (24 : BitVec 64) := hne_off 24 (by omega)
      have n32 : a ≠ hp + (32 : BitVec 64) := hne_off 32 (by omega)
      have n40 : a ≠ hp + (40 : BitVec 64) := hne_off 40 (by omega)
      have n48 : a ≠ hp + (48 : BitVec 64) := hne_off 48 (by omega)
      change M7 a = s.memory a
      dsimp only [M7]
      simp only [updW, if_neg n48, if_neg n40, if_neg n32, if_neg n24, if_neg n16, if_neg n8, if_neg n0]
    · intro k hk
      have hkh : k ≠ ofString "heap_ptr" := by simpa using hk
      simp [post, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hkh]
  simpa using hrun rv hrv

/-! ## 5. `ww_rlp_item` (`WritesWithin (fun _ => []) ["scratch_ptr"] "rlp_item"`) -/

private def RlpFlowFrame {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady post ∧
  globN post "heap_ptr" = globN s "heap_ptr" ∧
  globN post "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
  globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
  FrameOutside s post
    ([(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
    (0, 0) ∧
  ∀ k : MlS, k ∉ (["scratch_ptr"] : List String).map ofString →
    s.globals.lookup k = post.globals.lookup k

private theorem rlpFlowFrame_refl {F : Type} {s : PanSemStateFiniteExact 64 F} (hA : ArenaReady s) :
    RlpFlowFrame s s :=
  ⟨hA, rfl, rfl, le_rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

private theorem rlpFlowFrame_with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : RlpFlowFrame s post) (L : HolFiniteMapExact MlS (ValueHOL 64)) (c : Nat) :
    RlpFlowFrame s { post with locals := L, clock := c } :=
  ⟨⟨⟨h.1.1.code, h.1.1.memaddrs, h.1.1.shMemaddrs, h.1.1.baseAddr⟩, h.1.2⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem rlpFlowFrame_trans {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    (h1 : RlpFlowFrame a b) (h2 : RlpFlowFrame b c) : RlpFlowFrame a c := by
  refine ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    Nat.le_trans h2.2.2.2.1 h1.2.2.2.1, ?_, ?_⟩
  · intro x hx h0
    have hxb : ∀ i ∈ [(globN b "frame_mem_ptr", globN b "scratch_ptr" - globN b "frame_mem_ptr")],
        ¬ CellHits x.toNat i := by
      intro i hi hch
      simp only [List.mem_singleton] at hi; subst hi
      apply hx (globN a "frame_mem_ptr", globN a "scratch_ptr" - globN a "frame_mem_ptr")
        (List.mem_singleton.2 rfl)
      unfold CellHits at hch ⊢
      have := h1.2.2.1
      have := h1.2.2.2.1
      omega
    exact (h2.2.2.2.2.1 x hxb h0).trans (h1.2.2.2.2.1 x hx h0)
  · intro k hk
    exact (h1.2.2.2.2.2 k hk).trans (h2.2.2.2.2.2 k hk)

private def FlowsOrResumes (r : Option (PanSemResultExact 64)) : Prop :=
  r = none ∨ r = some .break ∨ r = some .continue ∨ Resumes r

private def ReadOnlyProg (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → GuestInv s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowsOrResumes (evaluateHOLFiniteState s prog).1 →
    (evaluateHOLFiniteState s prog).2 =
      { s with
        locals := (evaluateHOLFiniteState s prog).2.locals
        clock := (evaluateHOLFiniteState s prog).2.clock }

private theorem state_eq_with_locals_clock {F : Type} {a b : PanSemStateFiniteExact 64 F}
    (h : a = { b with locals := a.locals, clock := a.clock })
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat) :
    { a with locals := locals, clock := clock } = { b with locals := locals, clock := clock } := by
  cases a; cases b
  dsimp only at h
  injection h with _ hg hst hc he hm hma hsh _ hbe hffi hba hta
  subst hg hst hc he hm hma hsh hbe hffi hba hta
  rfl

private theorem state_trans_locals_clock {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    (h1 : mid = { s with locals := mid.locals, clock := mid.clock })
    (h2 : post = { mid with locals := post.locals, clock := post.clock }) :
    post = { s with locals := post.locals, clock := post.clock } := by
  rw [h2]
  exact state_eq_with_locals_clock h1 post.locals post.clock

private theorem ReadOnlyProg.skip : ReadOnlyProg .skip := by
  intro _ s _ _ _ _
  simp only [evaluateHOLFiniteState_skip]

private theorem ReadOnlyProg.ret (e : ExpHOL 64) : ReadOnlyProg (.return e) := by
  intro _ s _ _ _ _
  simp only [evaluateHOLFiniteState_return]
  split
  · rfl
  · split <;> [simp [emptyLocalsHOLFinite]; rfl]

private theorem ReadOnlyProg.raise (eid : MlS) (e : ExpHOL 64) : ReadOnlyProg (.raise eid e) := by
  intro _ s _ _ _ _
  simp only [evaluateHOLFiniteState_raise]
  split
  · split <;> [simp [emptyLocalsHOLFinite]; rfl]
  · rfl

private theorem ReadOnlyProg.assign_local (name : MlS) (e : ExpHOL 64) :
    ReadOnlyProg (.assign .local name e) := by
  intro _ s _ _ _ _
  simp only [evaluateHOLFiniteState_assign]
  split
  · rfl
  · split
    · simp [setKvarHOLFinite, setVarHOLFinite]
    · rfl

private theorem ReadOnlyProg.dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64)
    {body : ProgHOL 64} (hbody : ReadOnlyProg body) :
    ReadOnlyProg (.dec name shape init body) := by
  intro F s hcode hG hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · rfl
  · rename_i v hv
    by_cases hsh : shapeEqHOL shape (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
      have hb := hbody (setVarHOLFinite name v s) hcode (guestInv_setVar name v s hG) hnt hfr
      have hset : setVarHOLFinite name v s =
          { s with locals := (setVarHOLFinite name v s).locals, clock := s.clock } := by
        cases s; rfl
      exact state_eq_with_locals_clock (state_trans_locals_clock hset hb) _ _
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte]

private theorem ReadOnlyProg.seq {first second : ProgHOL 64}
    (h1 : ReadOnlyProg first) (h2 : ReadOnlyProg second) :
    ReadOnlyProg (.seq first second) := by
  intro F s hcode hG hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s first).1
  have hGmid := guestInv_evaluate s first hG
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hGmid hnt hfr ⊢
  change mid.code = s.code at hmeta
  cases r1 with
  | none =>
    have hb1 := h1 s hcode hG (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hb1
    dsimp only at hb1 hnt hfr ⊢
    exact state_trans_locals_clock hb1 (h2 mid (hmeta.trans hcode) hGmid hnt hfr)
  | some r =>
    have hb1 := h1 s hcode hG (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hb1; exact hb1

private theorem ReadOnlyProg.ite (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (hyes : ReadOnlyProg yes) (hno : ReadOnlyProg no) :
    ReadOnlyProg (.ite cond yes no) := by
  intro F s hcode hG hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · split at hnt
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hno s hcode hG hnt hfr
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hyes s hcode hG hnt hfr
  · cases s; rfl

private theorem ReadOnlyProg.while_loop (cond : ExpHOL 64) {body : ProgHOL 64}
    (hbody : ReadOnlyProg body) :
    ReadOnlyProg (.while cond body) := by
  intro F s hcode hG hnt hfr
  generalize hk : s.clock = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    subst hk
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hfr ⊢
    revert hnt hfr
    split <;> intro hnt hfr
    · rename_i w hw
      by_cases hnz : w = 0
      · subst hnz; simp only [ne_eq, not_true_eq_false, ↓reduceIte]
      · rw [if_pos hnz] at hnt hfr ⊢
        by_cases hclk : s.clock = 0
        · rw [if_pos hclk] at hnt; simp at hnt
        · rw [if_neg hclk] at hnt hfr ⊢
          have hGd : GuestInv (decClockHOLFinite s) := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body).1
          have hGmid := guestInv_evaluate (decClockHOLFinite s) body hGd
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          simp only [hrun] at hmeta hGmid hrem hnt hfr ⊢
          change mid.code = s.code at hmeta
          change mid.clock ≤ s.clock - 1 at hrem
          have hlt : mid.clock < s.clock := by omega
          have hdecEq : decClockHOLFinite s =
              { s with locals := s.locals, clock := (decClockHOLFinite s).clock } := by
            cases s; rfl
          cases r1 with
          | none =>
            have hb1 := hbody (decClockHOLFinite s) hcode hGd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl rfl)
            rw [hrun] at hb1
            exact state_trans_locals_clock (state_trans_locals_clock hdecEq hb1)
              (ih mid.clock hlt mid (hmeta.trans hcode) hGmid hnt hfr rfl)
          | some res =>
            cases res with
            | «continue» =>
              have hb1 := hbody (decClockHOLFinite s) hcode hGd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hrun] at hb1
              exact state_trans_locals_clock (state_trans_locals_clock hdecEq hb1)
                (ih mid.clock hlt mid (hmeta.trans hcode) hGmid hnt hfr rfl)
            | «break» =>
              have hb1 := hbody (decClockHOLFinite s) hcode hGd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inl rfl))
              rw [hrun] at hb1; exact state_trans_locals_clock hdecEq hb1
            | timeOut => simp at hnt
            | returned v =>
              have hb1 := hbody (decClockHOLFinite s) hcode hGd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hrun] at hb1; exact state_trans_locals_clock hdecEq hb1
            | exception e v =>
              have hres : Resumes (some (.exception e v)) := by
                rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
              have hb1 := hbody (decClockHOLFinite s) hcode hGd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr hres)))
              rw [hrun] at hb1; exact state_trans_locals_clock hdecEq hb1
            | error =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
            | finalFfi _ =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
    · rfl

private theorem ReadOnlyProg.call0 {fname : MlS} (hf : ReadOnlyFn fname) (args : List (ExpHOL 64)) :
    ReadOnlyProg (.call (some (none, none)) fname args) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hcode hG hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rfl
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rfl
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return s fname params body' body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hret_eq
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
            · simp only [hsh, ↓reduceIte] at hfr ⊢
              have hro := hspec (callEntryStateHOLFinite s callee) hcode
                (guestInv_callEntry s callee hG) hex (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              rw [hrun] at hro
              dsimp only at hro
              exact state_eq_with_locals_clock (state_trans_locals_clock hentryEq hro) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            dsimp only at hfr ⊢
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hro := hspec (callEntryStateHOLFinite s callee) hcode
              (guestInv_callEntry s callee hG) hex (by rw [hrun]; simp) (by rw [hrun]; exact hres)
            rw [hrun] at hro
            dsimp only at hro
            exact state_eq_with_locals_clock (state_trans_locals_clock hentryEq hro) _ _
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem ReadOnlyProg.decCall {fname : MlS} (hf : ReadOnlyFn fname)
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : ReadOnlyProg cont) :
    ReadOnlyProg (.decCall name shape fname args cont) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hcode hG hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rfl
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rfl
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return s fname params body' body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hret_eq
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hro := hspec (callEntryStateHOLFinite s callee) hcode
                (guestInv_callEntry s callee hG) hex (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              rw [hrun] at hro; dsimp only at hro
              have hpost : post = { s with locals := post.locals, clock := post.clock } :=
                state_trans_locals_clock hentryEq hro
              let cstate := setVarHOLFinite name v { post with locals := s.locals }
              have hcstateEq : cstate = { s with locals := cstate.locals, clock := cstate.clock } := by
                have h2 : cstate = { post with locals := cstate.locals, clock := post.clock } := by
                  dsimp only [cstate]; cases post; rfl
                exact state_trans_locals_clock hpost h2
              have hGcstate : GuestInv cstate := by
                have hGpost := guestInv_evaluate (callEntryStateHOLFinite s callee) body' (guestInv_callEntry s callee hG)
                rw [hrun] at hGpost
                exact guestInv_setVar name v _ (guestInv_with_locals_clock post s.locals post.clock hGpost)
              have hbcont := hcont cstate hGcstate.code hGcstate hnt hfr
              exact state_eq_with_locals_clock (state_trans_locals_clock hcstateEq hbcont) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hro := hspec (callEntryStateHOLFinite s callee) hcode
              (guestInv_callEntry s callee hG) hex (by rw [hrun]; simp) (by rw [hrun]; exact hres)
            rw [hrun] at hro; dsimp only at hro
            exact state_eq_with_locals_clock (state_trans_locals_clock hentryEq hro) _ post.clock
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem readOnlyFn_of_guestAst
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64))
    (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hprog : ReadOnlyProg
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)) :
    ReadOnlyFn (ofString (extractFn d).name) := by
  refine ⟨(extractFn d).params.map InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural (extractFn d).returnShape,
    lookup_of_guestAst_getElem i hi (extractFn d) hd, ?_⟩
  intro F s hcode hG _hlookup hnt hres
  exact hprog s hcode hG hnt (Or.inr (Or.inr (Or.inr hres)))

private theorem ro_rlp_fail : ReadOnlyFn (ofString "rlp_fail") := by
  refine readOnlyFn_of_guestAst 105 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_fail rfl ?_
  dsimp only [Guest.Software.guestFn_rlp_fail, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.seq (ReadOnlyProg.raise _ _) (ReadOnlyProg.ret _)

private theorem ro_rlp_read_length : ReadOnlyFn (ofString "rlp_read_length") := by
  refine readOnlyFn_of_guestAst 106 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_read_length rfl ?_
  dsimp only [Guest.Software.guestFn_rlp_read_length, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.seq
    (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
    (ReadOnlyProg.dec _ _ _
      (ReadOnlyProg.dec _ _ _
        (ReadOnlyProg.seq
          (ReadOnlyProg.while_loop _
            (ReadOnlyProg.seq (ReadOnlyProg.assign_local _ _) (ReadOnlyProg.assign_local _ _)))
          (ReadOnlyProg.ret _))))

private def RlpFlowProg (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → ArenaReady s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowsOrResumes (evaluateHOLFiniteState s prog).1 →
    RlpFlowFrame s (evaluateHOLFiniteState s prog).2

private theorem RlpFlowProg.of_ro {prog : ProgHOL 64} (h : ReadOnlyProg prog) :
    RlpFlowProg prog := by
  intro F s hcode hAR hnt hfr
  have heq := h s hcode hAR.1 hnt hfr
  rw [heq]
  exact rlpFlowFrame_with_locals_clock (rlpFlowFrame_refl hAR) _ _

private theorem RlpFlowProg.seq {first second : ProgHOL 64}
    (h1 : RlpFlowProg first) (h2 : RlpFlowProg second) :
    RlpFlowProg (.seq first second) := by
  intro F s hcode hAR hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s first).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hfr ⊢
  change mid.code = s.code at hmeta
  cases r1 with
  | none =>
    have hb1 := h1 s hcode hAR (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hb1; dsimp only at hb1 hnt hfr ⊢
    exact rlpFlowFrame_trans hb1 (h2 mid (hmeta.trans hcode) hb1.1 hnt hfr)
  | some r =>
    have hb1 := h1 s hcode hAR (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hb1; exact hb1

private theorem RlpFlowProg.ite (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (hyes : RlpFlowProg yes) (hno : RlpFlowProg no) :
    RlpFlowProg (.ite cond yes no) := by
  intro F s hcode hAR hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · split at hnt
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hno s hcode hAR hnt hfr
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hyes s hcode hAR hnt hfr
  · exact rlpFlowFrame_refl hAR

private theorem RlpFlowProg.dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64)
    {body : ProgHOL 64} (hbody : RlpFlowProg body) :
    RlpFlowProg (.dec name shape init body) := by
  intro F s hcode hAR hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · exact rlpFlowFrame_refl hAR
  · rename_i v hv
    by_cases hsh : shapeEqHOL shape (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
      have hAR' : ArenaReady (setVarHOLFinite name v s) :=
        ⟨guestInv_setVar name v s hAR.1, hAR.2⟩
      have hb := hbody (setVarHOLFinite name v s) hcode hAR' hnt hfr
      have hpre : RlpFlowFrame s (setVarHOLFinite name v s) :=
        rlpFlowFrame_with_locals_clock (rlpFlowFrame_refl hAR) _ _
      exact rlpFlowFrame_with_locals_clock (rlpFlowFrame_trans hpre hb) _ _
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
      exact rlpFlowFrame_refl hAR

private theorem RlpFlowProg.while_loop (cond : ExpHOL 64) {body : ProgHOL 64}
    (hbody : RlpFlowProg body) :
    RlpFlowProg (.while cond body) := by
  intro F s hcode hAR hnt hfr
  generalize hk : s.clock = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    subst hk
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hfr ⊢
    revert hnt hfr
    split <;> intro hnt hfr
    · rename_i w hw
      by_cases hnz : w = 0
      · subst hnz; simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact rlpFlowFrame_refl hAR
      · rw [if_pos hnz] at hnt hfr ⊢
        by_cases hclk : s.clock = 0
        · rw [if_pos hclk] at hnt; simp at hnt
        · rw [if_neg hclk] at hnt hfr ⊢
          have hARd : ArenaReady (decClockHOLFinite s) :=
            ⟨⟨hAR.1.code, hAR.1.memaddrs, hAR.1.shMemaddrs, hAR.1.baseAddr⟩, hAR.2⟩
          have hdecF : RlpFlowFrame s (decClockHOLFinite s) :=
            rlpFlowFrame_with_locals_clock (rlpFlowFrame_refl hAR) _ _
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body).1
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          simp only [hrun] at hmeta hrem hnt hfr ⊢
          change mid.code = s.code at hmeta
          change mid.clock ≤ s.clock - 1 at hrem
          have hlt : mid.clock < s.clock := by omega
          cases r1 with
          | none =>
            have hb1 := hbody (decClockHOLFinite s) hcode hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl rfl)
            rw [hrun] at hb1; dsimp only at hb1
            exact rlpFlowFrame_trans (rlpFlowFrame_trans hdecF hb1)
              (ih mid.clock hlt mid (hmeta.trans hcode) hb1.1 hnt hfr rfl)
          | some res =>
            cases res with
            | «continue» =>
              have hb1 := hbody (decClockHOLFinite s) hcode hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hrun] at hb1; dsimp only at hb1
              exact rlpFlowFrame_trans (rlpFlowFrame_trans hdecF hb1)
                (ih mid.clock hlt mid (hmeta.trans hcode) hb1.1 hnt hfr rfl)
            | «break» =>
              have hb1 := hbody (decClockHOLFinite s) hcode hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inl rfl))
              rw [hrun] at hb1; exact rlpFlowFrame_trans hdecF hb1
            | timeOut => simp at hnt
            | returned v =>
              have hb1 := hbody (decClockHOLFinite s) hcode hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hrun] at hb1; exact rlpFlowFrame_trans hdecF hb1
            | exception e v =>
              have hres : Resumes (some (.exception e v)) := by
                rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
              have hb1 := hbody (decClockHOLFinite s) hcode hARd (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr hres)))
              rw [hrun] at hb1; exact rlpFlowFrame_trans hdecF hb1
            | error =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
            | finalFfi _ =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
    · exact rlpFlowFrame_refl hAR

private theorem RlpFlowProg.decCall_ro {fname : MlS} (hf : ReadOnlyFn fname)
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : RlpFlowProg cont) :
    RlpFlowProg (.decCall name shape fname args cont) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hcode hAR hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact rlpFlowFrame_refl hAR
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact rlpFlowFrame_refl hAR
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return s fname params body' body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hret_eq
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hro := hspec (callEntryStateHOLFinite s callee) hcode
                (guestInv_callEntry s callee hAR.1) hex (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              rw [hrun] at hro; dsimp only at hro
              have hpost : post = { s with locals := post.locals, clock := post.clock } :=
                state_trans_locals_clock hentryEq hro
              let cstate := setVarHOLFinite name v { post with locals := s.locals }
              have hcstateEq : cstate = { s with locals := cstate.locals, clock := cstate.clock } := by
                have h2 : cstate = { post with locals := cstate.locals, clock := post.clock } := by
                  dsimp only [cstate]; cases post; rfl
                exact state_trans_locals_clock hpost h2
              have hAR_cstate : ArenaReady cstate := by
                rw [hcstateEq]
                exact ⟨⟨hAR.1.code, hAR.1.memaddrs, hAR.1.shMemaddrs, hAR.1.baseAddr⟩, hAR.2⟩
              have hpre : RlpFlowFrame s cstate := by
                rw [hcstateEq]
                exact rlpFlowFrame_with_locals_clock (rlpFlowFrame_refl hAR) _ _
              have hbcont := hcont cstate hAR_cstate.1.code hAR_cstate hnt hfr
              exact rlpFlowFrame_with_locals_clock (rlpFlowFrame_trans hpre hbcont) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hro := hspec (callEntryStateHOLFinite s callee) hcode
              (guestInv_callEntry s callee hAR.1) hex (by rw [hrun]; simp) (by rw [hrun]; exact hres)
            rw [hrun] at hro; dsimp only at hro
            have hpost : post = { s with locals := post.locals, clock := post.clock } :=
              state_trans_locals_clock hentryEq hro
            have hfin : emptyLocalsHOLFinite post =
                { s with locals := (emptyLocalsHOLFinite post).locals, clock := post.clock } :=
              state_eq_with_locals_clock hpost _ _
            rw [hfin]
            exact rlpFlowFrame_with_locals_clock (rlpFlowFrame_refl hAR) _ _
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem RlpFlowProg.call0 {fname : MlS}
    (hf : FunSpec ArenaReady (fun s r post => Resumes r → RlpFlowFrame s post) fname)
    (args : List (ExpHOL 64)) :
    RlpFlowProg (.call (some (none, none)) fname args) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hcode hAR hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact rlpFlowFrame_refl hAR
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact rlpFlowFrame_refl hAR
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return s fname params body' body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hret_eq
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
        have hAR_ent : ArenaReady (callEntryStateHOLFinite s callee) :=
          ⟨guestInv_callEntry s callee hAR.1, hAR.2⟩
        have hpre : RlpFlowFrame s (callEntryStateHOLFinite s callee) :=
          rlpFlowFrame_with_locals_clock (rlpFlowFrame_refl hAR) _ _
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
            · simp only [hsh, ↓reduceIte] at hfr ⊢
              have hb := hspec (callEntryStateHOLFinite s callee) hcode hAR_ent hex
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              rw [hrun] at hb; dsimp only at hb
              exact rlpFlowFrame_with_locals_clock (rlpFlowFrame_trans hpre hb) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            dsimp only at hfr ⊢
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hb := hspec (callEntryStateHOLFinite s callee) hcode hAR_ent hex
              (by rw [hrun]; simp) (by rw [hrun]; exact hres)
            rw [hrun] at hb; dsimp only at hb
            exact rlpFlowFrame_with_locals_clock (rlpFlowFrame_trans hpre hb) _ _
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem RlpFlowProg.decCall {fname : MlS}
    (hf : FunSpec ArenaReady (fun s r post => Resumes r → RlpFlowFrame s post) fname)
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : RlpFlowProg cont) :
    RlpFlowProg (.decCall name shape fname args cont) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hcode hAR hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact rlpFlowFrame_refl hAR
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact rlpFlowFrame_refl hAR
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return s fname params body' body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hret_eq
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
        have hAR_ent : ArenaReady (callEntryStateHOLFinite s callee) :=
          ⟨guestInv_callEntry s callee hAR.1, hAR.2⟩
        have hpre : RlpFlowFrame s (callEntryStateHOLFinite s callee) :=
          rlpFlowFrame_with_locals_clock (rlpFlowFrame_refl hAR) _ _
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hb := hspec (callEntryStateHOLFinite s callee) hcode hAR_ent hex
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              rw [hrun] at hb; dsimp only at hb
              let cstate := setVarHOLFinite name v { post with locals := s.locals }
              have hpre_c : RlpFlowFrame s cstate :=
                rlpFlowFrame_with_locals_clock (rlpFlowFrame_trans hpre hb) _ _
              have hbcont := hcont cstate hpre_c.1.1.code hpre_c.1 hnt hfr
              exact rlpFlowFrame_with_locals_clock (rlpFlowFrame_trans hpre_c hbcont) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hb := hspec (callEntryStateHOLFinite s callee) hcode hAR_ent hex
              (by rw [hrun]; simp) (by rw [hrun]; exact hres)
            rw [hrun] at hb; dsimp only at hb
            exact rlpFlowFrame_with_locals_clock (rlpFlowFrame_trans hpre hb) _ _
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem ro_rlp_item_header : ReadOnlyFn (ofString "rlp_item_header") := by
  refine readOnlyFn_of_guestAst 109 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_item_header rfl ?_
  dsimp only [Guest.Software.guestFn_rlp_item_header, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.seq
    (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
    (ReadOnlyProg.dec _ _ _
      (ReadOnlyProg.seq
        (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
        (ReadOnlyProg.seq
          (ReadOnlyProg.ite _
            (ReadOnlyProg.dec _ _ _
              (ReadOnlyProg.seq
                (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                (ReadOnlyProg.seq
                  (ReadOnlyProg.ite _
                    (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                    ReadOnlyProg.skip)
                  (ReadOnlyProg.ret _))))
            ReadOnlyProg.skip)
          (ReadOnlyProg.seq
            (ReadOnlyProg.ite _
              (ReadOnlyProg.dec _ _ _
                (ReadOnlyProg.seq
                  (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                  (ReadOnlyProg.decCall ro_rlp_read_length _ _ _
                    (ReadOnlyProg.seq
                      (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                      (ReadOnlyProg.seq
                        (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                        (ReadOnlyProg.ret _))))))
              ReadOnlyProg.skip)
            (ReadOnlyProg.seq
              (ReadOnlyProg.ite _
                (ReadOnlyProg.dec _ _ _
                  (ReadOnlyProg.seq
                    (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                    (ReadOnlyProg.ret _)))
                ReadOnlyProg.skip)
              (ReadOnlyProg.dec _ _ _
                (ReadOnlyProg.seq
                  (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                  (ReadOnlyProg.decCall ro_rlp_read_length _ _ _
                    (ReadOnlyProg.seq
                      (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                      (ReadOnlyProg.seq
                        (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                        (ReadOnlyProg.ret _)))))))))))

private def WordLocals {F : Type} (names : List String) (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ n ∈ names, ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))

private theorem assign_word_preserves {F : Type} (names : List String)
    (nm : MlS) (e : ExpHOL 64) (s : PanSemStateFiniteExact 64 F)
    (hw : WordLocals names s) :
    WordLocals names (evaluateHOLFiniteState s (.assign .local nm e)).2 := by
  rw [evaluateHOLFiniteState_assign]
  split
  · exact hw
  · rename_i v hv
    by_cases hvld : isValidValueHOLFinite s .local nm v = true
    · simp only [hvld, ↓reduceIte, setKvarHOLFinite, setVarHOLFinite]
      intro n hn
      obtain ⟨w0, hw0⟩ := hw n hn
      by_cases heq : ofString n = nm
      · subst heq
        simp only [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact,
          shapeOfHOLExact] at hvld
        have hex : s.locals.lookup (ofString n) = some (.val (.word w0)) := hw0
        rw [hex] at hvld
        rcases v with ⟨⟨vw⟩⟩ | _ | _
        · exact ⟨vw, by simp [HolFiniteMapExact.lookup_update, FUPDATE]⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hvld
        · simp [shapeOfHOLExact, shapeEqHOL] at hvld
      · exact ⟨w0, by simp [HolFiniteMapExact.lookup_update, FUPDATE, heq, Ne.symm heq, hw0]⟩
    · simp only [hvld, Bool.false_eq_true, ↓reduceIte]
      exact hw

private theorem rff_vib_push {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hw : WordLocals ["top", "pos", "end", "go", "payload", "after"] s)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
        (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
          (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
            (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
              (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
                (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
                  (.assign .local (ofString "end") (.var .local (ofString "after")))))))))).1 ≠ some .timeOut)
    (hfr : FlowsOrResumes (evaluateHOLFiniteState s
      (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
        (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
          (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
            (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
              (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
                (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
                  (.assign .local (ofString "end") (.var .local (ofString "after")))))))))).1) :
    let out := evaluateHOLFiniteState s
      (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
        (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
          (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
            (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
              (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
                (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
                  (.assign .local (ofString "end") (.var .local (ofString "after")))))))))
    RlpFlowFrame s out.2 ∧ (out.1 = none → WordLocals ["top", "pos", "end", "go"] out.2) := by
  dsimp only
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA
  obtain ⟨w_top, htop⟩ := hw "top" (by simp)
  obtain ⟨w_pos, hpos⟩ := hw "pos" (by simp)
  obtain ⟨w_end, hend⟩ := hw "end" (by simp)
  obtain ⟨w_go, hgo⟩ := hw "go" (by simp)
  obtain ⟨w_pay, hpay⟩ := hw "payload" (by simp)
  obtain ⟨w_aft, haft⟩ := hw "after" (by simp)
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const 24] =
      some [.val (.word 24)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlook_sa : originalRuntimeCode.lookup (ofString "scratch_alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_scratch_alloc, .one) :=
    lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_scratch_alloc) rfl
  have hlook := pan_one_word_lookup s.code.lookup (ofString "scratch_alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_scratch_alloc) 24
    (by rw [hcode]; exact hlook_sa)
  simp only [hargs, hlook] at hnt hfr ⊢
  by_cases hz : s.clock = 0
  · simp [hz] at hnt
  · simp only [hz, ↓reduceIte] at hnt hfr ⊢
    let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 24)))
    have hsa := scratch_alloc_body_resumes entry sp fp hcode hsp hfp
    rcases hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_scratch_alloc) with ⟨ar, apost⟩
    have hrun_raw : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 24))))
        (sourceFnBody Guest.Software.guestFn_scratch_alloc) = (ar, apost) := hrun
    simp only [hrun] at hsa
    simp only [hrun_raw] at hnt hfr ⊢
    cases ar with
    | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
    | some ar' =>
      cases ar' with
      | timeOut => simp at hnt
      | «break» | «continue» | error | finalFfi _ =>
        rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
      | exception eid ev =>
        dsimp only at hfr ⊢
        have hres : Resumes (some (.exception eid ev)) := by
          rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
        obtain ⟨_, _, hret, _, _, _⟩ := hsa hres
        cases hret
      | returned av =>
        obtain ⟨n', hn', hret, hc1, hc2, hapost⟩ := hsa (Or.inl ⟨av, rfl⟩)
        have hn24 : n' = 24 := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at hn'
          exact hn'.symm
        subst hn24
        injection hret with hret'; injection hret' with hret''; subst hret''
        set q : BitVec 64 := (sp - 24) &&& ((0 : BitVec 64) - 8)
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word q) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word q) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hnt hfr ⊢
        have hfp_sp : fp.toNat ≤ sp.toNat := by rw [hfp_eq, hsp_eq]; exact hA.2.2.2.1
        have hsp_al : sp.toNat % 8 = 0 := by rw [hsp_eq]; exact hA.2.2.2.2.2.2.2.1
        obtain ⟨hq_al, hfp_q, hq_sp, hq_sum⟩ := scratch_alloc_arith sp fp 24 hfp_sp hsp_al hc1 hc2
        change q.toNat % 8 = 0 at hq_al
        change fp.toNat ≤ q.toNat at hfp_q
        change q.toNat ≤ sp.toNat at hq_sp
        change q.toNat + ((24 : BitVec 64).toNat + 7) / 8 * 8 = sp.toNat at hq_sum
        have h24 : ((24 : BitVec 64).toNat + 7) / 8 * 8 = 24 := by decide
        rw [h24] at hq_sum
        have hse_lt : scratchEnd < 2 ^ 64 := by decide
        have hsp_se : sp.toNat ≤ scratchEnd := by rw [hsp_eq]; exact hA.2.2.2.2.1
        have hq8_nat : (q + 8).toNat = q.toNat + 8 := BitVec.toNat_add_of_lt (by change q.toNat + 8 < 2 ^ 64; omega)
        have hq16_nat : (q + 16).toNat = q.toNat + 16 := BitVec.toNat_add_of_lt (by change q.toNat + 16 < 2 ^ 64; omega)
        let c0 := setVarHOLFinite (ofString "rec") (.val (.word q)) { apost with locals := s.locals }
        have hc0_eq : c0 = { s with
            locals := s.locals.update (ofString "rec", .val (.word q))
            globals := s.globals.update (ofString "scratch_ptr", .val (.word q))
            clock := apost.clock } := by
          dsimp only [c0, setVarHOLFinite]; rw [hapost]; rfl
        have hc0_dom_q : c0.memaddrs q := by
          rw [hc0_eq]; dsimp only; rw [hG.memaddrs]
          have hq_bv : BitVec.ofNat 64 q.toNat = q := by apply BitVec.eq_of_toNat_eq; simp
          rw [← hq_bv]
          have hss : sourceBase ≤ scratchStart := by decide
          have hse : scratchEnd ≤ heapEnd := by decide
          have := hA.2.2.1
          exact ordinaryDomain_of_nat q.toNat (by omega) (by omega) hq_al
        have hc0_dom_q8 : c0.memaddrs (q + 8) := by
          rw [hc0_eq]; dsimp only; rw [hG.memaddrs]
          have hq8_bv : BitVec.ofNat 64 (q + 8).toNat = q + 8 := by apply BitVec.eq_of_toNat_eq; simp
          rw [← hq8_bv, hq8_nat]
          have hss : sourceBase ≤ scratchStart := by decide
          have hse : scratchEnd ≤ heapEnd := by decide
          have := hA.2.2.1
          exact ordinaryDomain_of_nat (q.toNat + 8) (by omega) (by omega) (by omega)
        have hc0_dom_q16 : c0.memaddrs (q + 16) := by
          rw [hc0_eq]; dsimp only; rw [hG.memaddrs]
          have hq16_bv : BitVec.ofNat 64 (q + 16).toNat = q + 16 := by apply BitVec.eq_of_toNat_eq; simp
          rw [← hq16_bv, hq16_nat]
          have hss : sourceBase ≤ scratchStart := by decide
          have hse : scratchEnd ≤ heapEnd := by decide
          have := hA.2.2.1
          exact ordinaryDomain_of_nat (q.toNat + 16) (by omega) (by omega) (by omega)
        have hc0_rec : c0.locals.lookup (ofString "rec") = some (.val (.word q)) := by
          rw [hc0_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hc0_aft : c0.locals.lookup (ofString "after") = some (.val (.word w_aft)) := by
          rw [hc0_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, haft, show ofString "rec" ≠ ofString "after" by decide]
        have hc0_end : c0.locals.lookup (ofString "end") = some (.val (.word w_end)) := by
          rw [hc0_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hend, show ofString "rec" ≠ ofString "end" by decide]
        have hc0_top : c0.locals.lookup (ofString "top") = some (.val (.word w_top)) := by
          rw [hc0_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, htop, show ofString "rec" ≠ ofString "top" by decide]
        have hc0_pay : c0.locals.lookup (ofString "payload") = some (.val (.word w_pay)) := by
          rw [hc0_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hpay, show ofString "rec" ≠ ofString "payload" by decide]
        have hc0_pos : c0.locals.lookup (ofString "pos") = some (.val (.word w_pos)) := by
          rw [hc0_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hpos, show ofString "rec" ≠ ofString "pos" by decide]
        have hc0_go : c0.locals.lookup (ofString "go") = some (.val (.word w_go)) := by
          rw [hc0_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hgo, show ofString "rec" ≠ ofString "go" by decide]
        have hst1 : evaluateHOLFiniteState c0 (.store (.var .local (ofString "rec")) (.var .local (ofString "after"))) =
            (none, { c0 with memory := updW c0.memory q w_aft }) := by
          rw [evaluateHOLFiniteState_store]
          have hd : @evalHOLExact 64 F _ c0.toExact (fun a => Classical.propDecidable (c0.memaddrs a)) (.var .local (ofString "rec")) = some (.val (.word q)) := hc0_rec
          have hv : @evalHOLExact 64 F _ c0.toExact (fun a => Classical.propDecidable (c0.memaddrs a)) (.var .local (ofString "after")) = some (.val (.word w_aft)) := hc0_aft
          rw [hd, hv]
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hc0_dom_q, ↓reduceIte]
          rfl
        let c1 : PanSemStateFiniteExact 64 F := { c0 with memory := updW c0.memory q w_aft }
        have hst2 : evaluateHOLFiniteState c1 (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end"))) =
            (none, { c0 with memory := updW c1.memory (q + 8) w_end }) := by
          rw [evaluateHOLFiniteState_store]
          have hc1_rec : c1.locals.lookup (ofString "rec") = some (.val (.word q)) := hc0_rec
          have hd : @evalHOLExact 64 F _ c1.toExact (fun a => Classical.propDecidable (c1.memaddrs a)) (.op .add [.var .local (ofString "rec"), .const 8]) = some (.val (.word (q + 8))) := by
            simp only [evalHOLExact, evalListHOLExact, hc1_rec, wordOpHOL, wordOp, valueIsWord, valueWord,
              List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
            have hz : (8 : BitVec 64) + 0 = 8 := by decide
            exact congrArg (fun x => some (ValueHOL.val (HolWordLab.word (q + x)))) hz
          have hv : @evalHOLExact 64 F _ c1.toExact (fun a => Classical.propDecidable (c1.memaddrs a)) (.var .local (ofString "end")) = some (.val (.word w_end)) := hc0_end
          rw [hd, hv]
          simp only [c1, flattenHOL, panMemStoresHOL, panMemStoreHOL, hc0_dom_q8, ↓reduceIte]
          rfl
        let c2 : PanSemStateFiniteExact 64 F := { c0 with memory := updW c1.memory (q + 8) w_end }
        have hst3 : evaluateHOLFiniteState c2 (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top"))) =
            (none, { c0 with memory := updW c2.memory (q + 16) w_top }) := by
          rw [evaluateHOLFiniteState_store]
          have hc2_rec : c2.locals.lookup (ofString "rec") = some (.val (.word q)) := hc0_rec
          have hd : @evalHOLExact 64 F _ c2.toExact (fun a => Classical.propDecidable (c2.memaddrs a)) (.op .add [.var .local (ofString "rec"), .const 16]) = some (.val (.word (q + 16))) := by
            simp only [evalHOLExact, evalListHOLExact, hc2_rec, wordOpHOL, wordOp, valueIsWord, valueWord,
              List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
            have hz : (16 : BitVec 64) + 0 = 16 := by decide
            exact congrArg (fun x => some (ValueHOL.val (HolWordLab.word (q + x)))) hz
          have hv : @evalHOLExact 64 F _ c2.toExact (fun a => Classical.propDecidable (c2.memaddrs a)) (.var .local (ofString "top")) = some (.val (.word w_top)) := hc0_top
          rw [hd, hv]
          simp only [c2, flattenHOL, panMemStoresHOL, panMemStoreHOL, hc0_dom_q16, ↓reduceIte]
          rfl
        let c3 : PanSemStateFiniteExact 64 F := { c0 with memory := updW c2.memory (q + 16) w_top }
        have hasg : evaluateHOLFiniteState c3
            (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
              (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
                (.assign .local (ofString "end") (.var .local (ofString "after"))))) =
            (none, setVarHOLFinite (ofString "end") (.val (.word w_aft))
              (setVarHOLFinite (ofString "pos") (.val (.word w_pay))
                (setVarHOLFinite (ofString "top") (.val (.word q)) c3))) := by
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
          have h1 : @evalHOLExact 64 F _ c3.toExact (fun a => Classical.propDecidable (c3.memaddrs a)) (.var .local (ofString "rec")) = some (.val (.word q)) := hc0_rec
          have hv1 : isValidValueHOLFinite c3 .local (ofString "top") (.val (.word q)) = true := by
            simp [c3, isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact, hc0_top, shapeOfHOLExact, shapeEqHOL]
          rw [h1]; dsimp only [setKvarHOLFinite]; rw [if_pos hv1]; dsimp only
          set c4 := setVarHOLFinite (ofString "top") (.val (.word q)) c3
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
          have h2 : @evalHOLExact 64 F _ c4.toExact (fun a => Classical.propDecidable (c4.memaddrs a)) (.var .local (ofString "payload")) = some (.val (.word w_pay)) := by
            simp [c4, c3, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hc0_pay, show ofString "top" ≠ ofString "payload" by decide]
          have hv2 : isValidValueHOLFinite c4 .local (ofString "pos") (.val (.word w_pay)) = true := by
            simp [c4, c3, setVarHOLFinite, isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hc0_pos, show ofString "top" ≠ ofString "pos" by decide, shapeOfHOLExact, shapeEqHOL]
          rw [h2]; dsimp only [setKvarHOLFinite]; rw [if_pos hv2]; dsimp only
          set c5 := setVarHOLFinite (ofString "pos") (.val (.word w_pay)) c4
          rw [evaluateHOLFiniteState_assign]
          have h3 : @evalHOLExact 64 F _ c5.toExact (fun a => Classical.propDecidable (c5.memaddrs a)) (.var .local (ofString "after")) = some (.val (.word w_aft)) := by
            simp [c5, c4, c3, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hc0_aft,
              show ofString "pos" ≠ ofString "after" by decide, show ofString "top" ≠ ofString "after" by decide]
          have hv3 : isValidValueHOLFinite c5 .local (ofString "end") (.val (.word w_aft)) = true := by
            simp [c5, c4, c3, setVarHOLFinite, isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hc0_end,
              show ofString "pos" ≠ ofString "end" by decide, show ofString "top" ≠ ofString "end" by decide, shapeOfHOLExact, shapeEqHOL]
          rw [h3]; dsimp only [setKvarHOLFinite]; rw [if_pos hv3]
        have hcont_eval : evaluateHOLFiniteState c0
            (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
              (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
                (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
                  (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
                    (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
                      (.assign .local (ofString "end") (.var .local (ofString "after")))))))) =
            (none, setVarHOLFinite (ofString "end") (.val (.word w_aft))
              (setVarHOLFinite (ofString "pos") (.val (.word w_pay))
                (setVarHOLFinite (ofString "top") (.val (.word q)) c3))) := by
          rw [evaluateHOLFiniteState_seq_line780, hst1]; dsimp only
          rw [evaluateHOLFiniteState_seq_line780, hst2]; dsimp only
          rw [evaluateHOLFiniteState_seq_line780, hst3]; dsimp only
          exact hasg
        change (let res := evaluateHOLFiniteState c0 _
          RlpFlowFrame s { res.2 with locals := HolFiniteMapExact.resVarEq res.2.locals (ofString "rec", s.locals.lookup (ofString "rec")) } ∧
          (res.1 = none → WordLocals ["top", "pos", "end", "go"]
            { res.2 with locals := HolFiniteMapExact.resVarEq res.2.locals (ofString "rec", s.locals.lookup (ofString "rec")) }))
        rw [hcont_eval]
        dsimp only
        refine ⟨?_, fun _ => ?_⟩
        · have hsp_hp : (ofString "scratch_ptr" : MlS) ≠ ofString "heap_ptr" := by decide
          have hsp_fp : (ofString "scratch_ptr" : MlS) ≠ ofString "frame_mem_ptr" := by decide
          have hc0_g : c0.globals = s.globals.update (ofString "scratch_ptr", .val (.word q)) := by rw [hc0_eq]
          set outSt : PanSemStateFiniteExact 64 F :=
            { (setVarHOLFinite (ofString "end") (.val (.word w_aft))
                (setVarHOLFinite (ofString "pos") (.val (.word w_pay))
                  (setVarHOLFinite (ofString "top") (.val (.word q)) c3))) with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "end") (.val (.word w_aft))
                  (setVarHOLFinite (ofString "pos") (.val (.word w_pay))
                    (setVarHOLFinite (ofString "top") (.val (.word q)) c3))).locals
                (ofString "rec", s.locals.lookup (ofString "rec")) }
          have hout_g : outSt.globals = s.globals.update (ofString "scratch_ptr", .val (.word q)) := hc0_g
          have hout_hp : globN outSt "heap_ptr" = globN s "heap_ptr" := by
            unfold globN; rw [hout_g]
            simp [HolFiniteMapExact.lookup_update, FUPDATE, hsp_hp, Ne.symm hsp_hp]
          have hout_fp : globN outSt "frame_mem_ptr" = globN s "frame_mem_ptr" := by
            unfold globN; rw [hout_g]
            simp [HolFiniteMapExact.lookup_update, FUPDATE, hsp_fp, Ne.symm hsp_fp]
          have hout_sp : globN outSt "scratch_ptr" = q.toNat := by
            unfold globN; rw [hout_g]
            simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hG_out : GuestInv outSt := by
            have hc : outSt.code = s.code := by dsimp [outSt, c3, setVarHOLFinite]; rw [hc0_eq]
            have hm : outSt.memaddrs = s.memaddrs := by dsimp [outSt, c3, setVarHOLFinite]; rw [hc0_eq]
            have hs : outSt.shMemaddrs = s.shMemaddrs := by dsimp [outSt, c3, setVarHOLFinite]; rw [hc0_eq]
            have hb : outSt.baseAddr = s.baseAddr := by dsimp [outSt, c3, setVarHOLFinite]; rw [hc0_eq]
            exact ⟨hc.trans hG.code, hm.trans hG.memaddrs, hs.trans hG.shMemaddrs, hb.trans hG.baseAddr⟩
          change RlpFlowFrame s outSt
          refine ⟨⟨hG_out, ?_⟩, hout_hp, hout_fp, ?_, ?_, ?_⟩
          · unfold ArenaOK
            rw [hout_hp, hout_fp, hout_sp]
            exact ⟨hA.1, hA.2.1, hA.2.2.1, by rw [← hfp_eq]; exact hfp_q, by omega,
              hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hq_al,
              globalsWord_update (ofString "scratch_ptr") q hout_g hA.2.2.2.2.2.2.2.2⟩
          · rw [hout_sp, ← hsp_eq]; exact hq_sp
          · intro a ha _
            have hne_q : a ≠ q := by
              rintro rfl
              exact ha (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")
                (List.mem_singleton.2 rfl) ⟨by rw [← hfp_eq, ← hsp_eq]; omega, by rw [← hfp_eq, ← hsp_eq]; omega⟩
            have hne_q8 : a ≠ q + 8 := by
              rintro rfl
              exact ha (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")
                (List.mem_singleton.2 rfl) ⟨by rw [hq8_nat, ← hfp_eq, ← hsp_eq]; omega, by rw [hq8_nat, ← hfp_eq, ← hsp_eq]; omega⟩
            have hne_q16 : a ≠ q + 16 := by
              rintro rfl
              exact ha (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")
                (List.mem_singleton.2 rfl) ⟨by rw [hq16_nat, ← hfp_eq, ← hsp_eq]; omega, by rw [hq16_nat, ← hfp_eq, ← hsp_eq]; omega⟩
            have hc0_mem : c0.memory = s.memory := by rw [hc0_eq]
            change updW (updW (updW c0.memory q w_aft) (q + 8) w_end) (q + 16) w_top a = s.memory a
            simp only [updW, if_neg hne_q16, if_neg hne_q8, if_neg hne_q, hc0_mem]
          · intro k hk
            have hks : k ≠ ofString "scratch_ptr" := by simpa using hk
            rw [hout_g]
            simp [HolFiniteMapExact.lookup_update, FUPDATE, hks, Ne.symm hks]
        · intro n hn
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl | rfl | rfl
          · refine ⟨q, ?_⟩
            rw [resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "end" ≠ ofString "top" by decide, show ofString "pos" ≠ ofString "top" by decide]
          · refine ⟨w_pay, ?_⟩
            rw [resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "end" ≠ ofString "pos" by decide]
          · refine ⟨w_aft, ?_⟩
            rw [resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          · refine ⟨w_go, ?_⟩
            rw [resVarEq_lookup_ne _ _ _ _ (by decide)]
            have hc3_go : c3.locals.lookup (ofString "go") = some (.val (.word w_go)) := hc0_go
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hc3_go,
              show ofString "end" ≠ ofString "go" by decide,
              show ofString "pos" ≠ ofString "go" by decide,
              show ofString "top" ≠ ofString "go" by decide]

private theorem two_word_params {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p1 p2 : MlS) (body : ProgHOL 64) (ret : ShapeHOL)
    (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, ret))
    (h : ∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
      some (body, s.locals, ret)) :
    ∃ a b : BitVec 64,
      s.locals.lookup p1 = some (.val (.word a)) ∧
      s.locals.lookup p2 = some (.val (.word b)) := by
  obtain ⟨vs, hv⟩ := h
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup fname vs body s.locals ret hv
  simp [lookupCodeHOLExact, hlook, hne] at hx
  rcases vs with _ | ⟨v1, vs⟩ <;> simp at hx
  rcases vs with _ | ⟨v2, vs⟩ <;> simp at hx
  rcases vs with _ | ⟨v3, vs⟩ <;> simp at hx
  have hsh1 := hx.1 (p1) .one v1 (Or.inl ⟨⟨rfl, rfl⟩, rfl⟩)
  have hsh2 := hx.1 (p2) .one v2 (Or.inr ⟨⟨rfl, rfl⟩, rfl⟩)
  have hp1 : s.locals.lookup p1 = some v1 := by rw [← hx.2]; simp [hne]
  have hp2 : s.locals.lookup p2 = some v2 := by rw [← hx.2]; simp
  rcases v1 with ⟨⟨a⟩⟩ | _ | _ <;> simp [shapeEqHOL, shapeOfHOLExact] at hsh1
  rcases v2 with ⟨⟨b⟩⟩ | _ | _ <;> simp [shapeEqHOL, shapeOfHOLExact] at hsh2
  exact ⟨a, b, hp1, hp2⟩

private theorem rff_dec_word {F : Type} (s0 s : PanSemStateFiniteExact 64 F)
    (names : List String) (nm : String) (init : ExpHOL 64) (body : ProgHOL 64)
    (hAR : ArenaReady s) (hpre : RlpFlowFrame s0 s) (hw : WordLocals names s)
    (hnt : (evaluateHOLFiniteState s (.dec (ofString nm) .one init body)).1 ≠ some .timeOut)
    (hfr : FlowsOrResumes (evaluateHOLFiniteState s (.dec (ofString nm) .one init body)).1)
    (hk : ∀ (w : BitVec 64),
      let s' := setVarHOLFinite (ofString nm) (.val (.word w)) s
      ArenaReady s' → RlpFlowFrame s0 s' → WordLocals (names ++ [nm]) s' →
      (evaluateHOLFiniteState s' body).1 ≠ some .timeOut →
      FlowsOrResumes (evaluateHOLFiniteState s' body).1 →
      RlpFlowFrame s0 (evaluateHOLFiniteState s' body).2 ∧
      ((evaluateHOLFiniteState s' body).1 = none → WordLocals names
        { (evaluateHOLFiniteState s' body).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s' body).2.locals
            (ofString nm, s.locals.lookup (ofString nm)) })) :
    let out := evaluateHOLFiniteState s (.dec (ofString nm) .one init body)
    RlpFlowFrame s0 out.2 ∧ (out.1 = none → WordLocals names out.2) := by
  dsimp only
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | v
  · simp only [hev] at hfr ⊢
    exact ⟨hpre, fun h => by simp at h⟩
  · simp only [hev] at hnt hfr ⊢
    by_cases hsh : shapeEqHOL .one (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
      rcases v with ⟨⟨w⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh)
      let s' := setVarHOLFinite (ofString nm) (.val (.word w)) s
      have hAR' : ArenaReady s' := ⟨guestInv_setVar _ _ s hAR.1, hAR.2⟩
      have hpre' : RlpFlowFrame s0 s' := rlpFlowFrame_with_locals_clock hpre _ _
      have hw' : WordLocals (names ++ [nm]) s' := by
        intro n hn
        by_cases heq : ofString n = ofString nm
        · exact ⟨w, by simp [s', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, heq]⟩
        · have hn_in : n ∈ names := by
            rcases List.mem_append.1 hn with h | h
            · exact h
            · simp at h; subst h; exact absurd rfl heq
          obtain ⟨w0, hw0⟩ := hw n hn_in
          exact ⟨w0, by simp [s', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, heq, Ne.symm heq, hw0]⟩
      obtain ⟨hf_b, hw_b⟩ := hk w hAR' hpre' hw' hnt hfr
      exact ⟨rlpFlowFrame_with_locals_clock hf_b _ _, hw_b⟩
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr ⊢
      exact ⟨hpre, fun h => by simp at h⟩

private theorem rff_vib_item {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hw : WordLocals ["top", "pos", "end", "go"] s)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "h") (.comb [.one, .one, .one]) (ofString "rlp_item_header")
        [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]]
        (.dec (ofString "payload") .one
          (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
          (.dec (ofString "after") .one
            (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))])
            (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
              (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
                (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
                  (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
                    (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
                      (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
                        (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
                          (.assign .local (ofString "end") (.var .local (ofString "after")))))))))
              (.assign .local (ofString "pos") (.var .local (ofString "after")))))))).1 ≠ some .timeOut)
    (hfr : FlowsOrResumes (evaluateHOLFiniteState s
      (.decCall (ofString "h") (.comb [.one, .one, .one]) (ofString "rlp_item_header")
        [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]]
        (.dec (ofString "payload") .one
          (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
          (.dec (ofString "after") .one
            (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))])
            (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
              (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
                (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
                  (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
                    (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
                      (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
                        (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
                          (.assign .local (ofString "end") (.var .local (ofString "after")))))))))
              (.assign .local (ofString "pos") (.var .local (ofString "after")))))))).1) :
    let out := evaluateHOLFiniteState s
      (.decCall (ofString "h") (.comb [.one, .one, .one]) (ofString "rlp_item_header")
        [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]]
        (.dec (ofString "payload") .one
          (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
          (.dec (ofString "after") .one
            (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))])
            (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
              (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
                (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
                  (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
                    (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
                      (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
                        (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
                          (.assign .local (ofString "end") (.var .local (ofString "after")))))))))
              (.assign .local (ofString "pos") (.var .local (ofString "after")))))))
    RlpFlowFrame s out.2 ∧ (out.1 = none → WordLocals ["top", "pos", "end", "go"] out.2) := by
  dsimp only
  obtain ⟨params, body, ret, hlook, hspec⟩ := ro_rlp_item_header
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]] with _ | values
  · exact ⟨rlpFlowFrame_refl hAR, fun h => by simp at h⟩
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "rlp_item_header") values with _ | ⟨body', callee, ret'⟩
    · exact ⟨rlpFlowFrame_refl hAR, fun h => by simp at h⟩
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "rlp_item_header")
          params body body' ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hsame
        have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "rlp_item_header")
          params body' body' ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hret_eq
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_item_header") vs =
            some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
          ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | timeOut => simp at hnt
          | «break» | «continue» | error | finalFfi _ =>
            rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            have hro := hspec (callEntryStateHOLFinite s callee) hcode
              (guestInv_callEntry s callee hAR.1) hex (by rw [hrun]; simp) (by rw [hrun]; exact hres)
            rw [hrun] at hro; dsimp only at hro
            have hpost : post = { s with locals := post.locals, clock := post.clock } :=
              state_trans_locals_clock hentryEq hro
            have hfin : emptyLocalsHOLFinite post =
                { s with locals := (emptyLocalsHOLFinite post).locals, clock := post.clock } :=
              state_eq_with_locals_clock hpost _ _
            rw [hfin]
            exact ⟨rlpFlowFrame_with_locals_clock (rlpFlowFrame_refl hAR) _ _, fun h => by simp at h⟩
          | returned hv =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact hv) (.comb [.one, .one, .one]) &&
                shapeEqHOL (shapeOfHOLExact hv) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hro := hspec (callEntryStateHOLFinite s callee) hcode
                (guestInv_callEntry s callee hAR.1) hex (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨hv, rfl⟩)
              rw [hrun] at hro; dsimp only at hro
              have hpost : post = { s with locals := post.locals, clock := post.clock } :=
                state_trans_locals_clock hentryEq hro
              let s1 := setVarHOLFinite (ofString "h") hv { post with locals := s.locals }
              have hs1_eq : s1 = { s with locals := s.locals.update (ofString "h", hv), clock := post.clock } := by
                have h2 : s1 = { post with locals := s.locals.update (ofString "h", hv), clock := post.clock } := rfl
                exact state_trans_locals_clock hpost h2
              have hAR1 : ArenaReady s1 := by
                rw [hs1_eq]; exact ⟨⟨hAR.1.code, hAR.1.memaddrs, hAR.1.shMemaddrs, hAR.1.baseAddr⟩, hAR.2⟩
              have hpre1 : RlpFlowFrame s s1 := by
                rw [hs1_eq]; exact rlpFlowFrame_with_locals_clock (rlpFlowFrame_refl hAR) _ _
              have hw1 : WordLocals ["top", "pos", "end", "go"] s1 := by
                intro n hn
                obtain ⟨w0, hw0⟩ := hw n hn
                have hne : ofString "h" ≠ ofString n := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                  rcases hn with rfl | rfl | rfl | rfl <;> decide
                rw [hs1_eq]
                exact ⟨w0, by simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hw0]⟩
              obtain ⟨hf_c, hw_c⟩ := rff_dec_word s s1 ["top", "pos", "end", "go"] "payload"
                (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))]) _
                hAR1 hpre1 hw1 hnt hfr (fun wpay hAR2 hpre2 hw2 hnt2 hfr2 => by
                  obtain ⟨hf_c2, hw_c2⟩ := rff_dec_word s _ ["top", "pos", "end", "go", "payload"] "after"
                    (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))]) _
                    hAR2 hpre2 hw2 hnt2 hfr2 (fun waft hAR3 hpre3 hw3 hnt3 hfr3 => by
                      set s3 := setVarHOLFinite (ofString "after") (.val (.word waft))
                        (setVarHOLFinite (ofString "payload") (.val (.word wpay)) s1)
                      change (RlpFlowFrame s (evaluateHOLFiniteState s3 _).2 ∧ _)
                      rw [evaluateHOLFiniteState_ite] at hnt3 hfr3 ⊢
                      rcases hc_ite : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                          (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0)) with _ | vc_ite
                      · simp only [hc_ite] at hfr3 ⊢
                        exact ⟨hpre3, fun h => by simp at h⟩
                      · rcases vc_ite with ⟨⟨wc⟩⟩ | _ | _
                        · simp only [hc_ite] at hnt3 hfr3 ⊢
                          by_cases hwc0 : wc = 0
                          · simp only [hwc0, ↓reduceIte] at hnt3 hfr3 ⊢
                            have hw_asg := assign_word_preserves ["top", "pos", "end", "go", "payload"]
                              (ofString "pos") (.var .local (ofString "after")) s3
                              (fun n hn => hw3 n (by simp at hn ⊢; tauto))
                            have hro_asg := (ReadOnlyProg.assign_local (ofString "pos") (.var .local (ofString "after")))
                              s3 hAR3.1.code hAR3.1 hnt3 hfr3
                            refine ⟨?_, fun _ n hn => ?_⟩
                            · rw [hro_asg]; exact rlpFlowFrame_with_locals_clock hpre3 _ _
                            · obtain ⟨w, hwn⟩ := hw_asg n hn
                              have hne : ofString n ≠ ofString "after" := by
                                simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                                rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
                              exact ⟨w, by dsimp only; rw [resVarEq_lookup_ne _ _ _ _ hne]; exact hwn⟩
                          · simp only [hwc0, ↓reduceIte] at hnt3 hfr3 ⊢
                            obtain ⟨hfr_p, hw_p⟩ := rff_vib_push s3 hAR3.1.code hAR3 hw3 hnt3 hfr3
                            refine ⟨rlpFlowFrame_trans hpre3 hfr_p, fun hn n hmem => ?_⟩
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                            rcases hmem with rfl | rfl | rfl | rfl | rfl
                            · obtain ⟨w, h⟩ := hw_p hn "top" (by simp)
                              exact ⟨w, by dsimp only; rw [resVarEq_lookup_ne _ _ _ _ (by decide)]; exact h⟩
                            · obtain ⟨w, h⟩ := hw_p hn "pos" (by simp)
                              exact ⟨w, by dsimp only; rw [resVarEq_lookup_ne _ _ _ _ (by decide)]; exact h⟩
                            · obtain ⟨w, h⟩ := hw_p hn "end" (by simp)
                              exact ⟨w, by dsimp only; rw [resVarEq_lookup_ne _ _ _ _ (by decide)]; exact h⟩
                            · obtain ⟨w, h⟩ := hw_p hn "go" (by simp)
                              exact ⟨w, by dsimp only; rw [resVarEq_lookup_ne _ _ _ _ (by decide)]; exact h⟩
                            · have havoid := evaluate_avoidsLocal_flowing (ofString "payload")
                                (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
                                  (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
                                    (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
                                      (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
                                        (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
                                          (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
                                            (.assign .local (ofString "end") (.var .local (ofString "after")))))))))
                                rfl s3 (Or.inl hn)
                              obtain ⟨w, h⟩ := hw3 "payload" (by simp)
                              exact ⟨w, by dsimp only; rw [resVarEq_lookup_ne _ _ _ _ (by decide), havoid]; exact h⟩
                        · simp only [hc_ite] at hfr3 ⊢
                          exact ⟨hpre3, fun h => by simp at h⟩
                        · simp only [hc_ite] at hfr3 ⊢
                          exact ⟨hpre3, fun h => by simp at h⟩)
                  refine ⟨hf_c2, fun hn n hmem => ?_⟩
                  obtain ⟨w, h⟩ := hw_c2 hn n (List.mem_append_left _ hmem)
                  have hne : ofString n ≠ ofString "payload" := by
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                    rcases hmem with rfl | rfl | rfl | rfl <;> decide
                  exact ⟨w, by dsimp only; rw [resVarEq_lookup_ne _ _ _ _ hne]; exact h⟩)
              refine ⟨rlpFlowFrame_with_locals_clock hf_c _ _, fun hn n hmem => ?_⟩
              obtain ⟨w, h⟩ := hw_c hn n hmem
              have hne : ofString n ≠ ofString "h" := by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with rfl | rfl | rfl | rfl <;> decide
              exact ⟨w, by dsimp only; rw [resVarEq_lookup_ne _ _ _ _ hne]; exact h⟩
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem rff_vib_pop {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hw : WordLocals ["top", "pos", "end", "go"] s)
    (hnt : (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
        (.assign .local (ofString "go") (.const 0))
        (.seq (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
          (.seq (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
            (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16]))))))).1 ≠ some .timeOut)
    (hfr : FlowsOrResumes (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
        (.assign .local (ofString "go") (.const 0))
        (.seq (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
          (.seq (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
            (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16]))))))).1) :
    let out := evaluateHOLFiniteState s
      (.ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
        (.assign .local (ofString "go") (.const 0))
        (.seq (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
          (.seq (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
            (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16]))))))
    RlpFlowFrame s out.2 ∧ (out.1 = none → WordLocals ["top", "pos", "end", "go"] out.2) := by
  dsimp only
  have hro : ReadOnlyProg
      (.ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
        (.assign .local (ofString "go") (.const 0))
        (.seq (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
          (.seq (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
            (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16])))))) :=
    ReadOnlyProg.ite _
      (ReadOnlyProg.assign_local _ _)
      (ReadOnlyProg.seq (ReadOnlyProg.assign_local _ _)
        (ReadOnlyProg.seq (ReadOnlyProg.assign_local _ _) (ReadOnlyProg.assign_local _ _)))
  refine ⟨RlpFlowProg.of_ro hro s hcode hAR hnt hfr, fun _ => ?_⟩
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_seq_line780]
      rcases h1 : evaluateHOLFiniteState s (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0]))) with ⟨r1, m1⟩
      have hw1 : WordLocals ["top", "pos", "end", "go"] m1 := by
        have := assign_word_preserves ["top", "pos", "end", "go"] (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])) s hw
        rwa [h1] at this
      cases r1 with
      | some _ => exact hw1
      | none =>
        dsimp only
        rw [evaluateHOLFiniteState_seq_line780]
        rcases h2 : evaluateHOLFiniteState m1 (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8]))) with ⟨r2, m2⟩
        have hw2 : WordLocals ["top", "pos", "end", "go"] m2 := by
          have := assign_word_preserves ["top", "pos", "end", "go"] (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])) m1 hw1
          rwa [h2] at this
        cases r2 with
        | some _ => exact hw2
        | none =>
          dsimp only
          exact assign_word_preserves ["top", "pos", "end", "go"] (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16])) m2 hw2
    · exact assign_word_preserves ["top", "pos", "end", "go"] (ofString "go") (.const 0) s hw
  · exact hw

private theorem spec__rlp_validate_items_body :
    FunSpec ArenaReady (fun s r post => Resumes r → RlpFlowFrame s post)
      (ofString "_rlp_validate_items_body") := by
  have hlook : originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn__rlp_validate_items_body, .one) :=
    lookup_of_guestAst_getElem 110 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn__rlp_validate_items_body) rfl
  refine ⟨_, _, _, hlook, ?_⟩
  intro F s hcode hAR hlookup hnt hres
  have hfr : FlowsOrResumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).1 :=
    Or.inr (Or.inr (Or.inr hres))
  have hb : sourceFnBody Guest.Software.guestFn__rlp_validate_items_body =
      .dec (ofString "top") .one (.const 0)
        (.dec (ofString "pos") .one (.var .local (ofString "p"))
          (.dec (ofString "end") .one (.op .add [.var .local (ofString "p"), .var .local (ofString "len")])
            (.dec (ofString "go") .one (.const 1)
              (.seq
                (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0))
                  (.ite (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end")))
                    (.ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
                      (.assign .local (ofString "go") (.const 0))
                      (.seq (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
                        (.seq (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
                          (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16]))))))
                    (.decCall (ofString "h") (.comb [.one, .one, .one]) (ofString "rlp_item_header")
                      [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]]
                      (.dec (ofString "payload") .one
                        (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
                        (.dec (ofString "after") .one
                          (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))])
                          (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
                            (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
                              (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
                                (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
                                  (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
                                    (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
                                      (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
                                        (.assign .local (ofString "end") (.var .local (ofString "after")))))))))
                            (.assign .local (ofString "pos") (.var .local (ofString "after")))))))))
                (.return (.const 0)))))) := rfl
  rw [hb] at hnt hfr ⊢
  have hw0 : WordLocals [] s := fun _ h => by simp at h
  have hseq_not_none : ∀ {st : PanSemStateFiniteExact 64 F} {p : ProgHOL 64},
      (evaluateHOLFiniteState st (.seq p (.return (.const 0)))).1 ≠ none := by
    intro st p h
    rw [evaluateHOLFiniteState_seq_line780] at h
    rcases hr : evaluateHOLFiniteState st p with ⟨r, m⟩
    rw [hr] at h
    cases r with
    | none =>
      dsimp only at h
      rw [evaluateHOLFiniteState_return] at h
      simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at h
    | some _ => dsimp only at h; cases h
  have hdec_not_none : ∀ {st : PanSemStateFiniteExact 64 F} {nm : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {b : ProgHOL 64},
      (∀ v, (evaluateHOLFiniteState (setVarHOLFinite nm v st) b).1 ≠ none) →
      (evaluateHOLFiniteState st (.dec nm sh e b)).1 ≠ none := by
    intro st nm sh e b hb h
    rw [evaluateHOLFiniteState_dec_total] at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · exact hb _ (by simpa using h)
      · cases h
  refine (rff_dec_word s s [] "top" _ _ hAR (rlpFlowFrame_refl hAR) hw0 hnt hfr fun w_top hAR1 hpre1 hw1 hnt1 hfr1 => ?_).1
  refine ⟨(rff_dec_word s _ ["top"] "pos" _ _ hAR1 hpre1 hw1 hnt1 hfr1 fun w_pos hAR2 hpre2 hw2 hnt2 hfr2 => ?_).1,
    fun h => absurd h (hdec_not_none fun _ => hdec_not_none fun _ => hdec_not_none fun _ => hseq_not_none)⟩
  refine ⟨(rff_dec_word s _ ["top", "pos"] "end" _ _ hAR2 hpre2 hw2 hnt2 hfr2 fun w_end hAR3 hpre3 hw3 hnt3 hfr3 => ?_).1,
    fun h => absurd h (hdec_not_none fun _ => hdec_not_none fun _ => hseq_not_none)⟩
  refine ⟨(rff_dec_word s _ ["top", "pos", "end"] "go" _ _ hAR3 hpre3 hw3 hnt3 hfr3 fun w_go hAR4 hpre4 hw4 hnt4 hfr4 => ?_).1,
    fun h => absurd h (hdec_not_none fun _ => hseq_not_none)⟩
  set s4 := setVarHOLFinite (ofString "go") (.val (.word w_go))
    (setVarHOLFinite (ofString "end") (.val (.word w_end))
      (setVarHOLFinite (ofString "pos") (.val (.word w_pos))
        (setVarHOLFinite (ofString "top") (.val (.word w_top)) s)))
  refine ⟨?_, fun h => absurd h hseq_not_none⟩
  let wcond : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "go")) (.const 0)
  let wpop : ProgHOL 64 := .ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
    (.assign .local (ofString "go") (.const 0))
    (.seq (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
      (.seq (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
        (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16])))))
  let witem : ProgHOL 64 := .decCall (ofString "h") (.comb [.one, .one, .one]) (ofString "rlp_item_header")
    [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]]
    (.dec (ofString "payload") .one
      (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
      (.dec (ofString "after") .one
        (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))])
        (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
          (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
            (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
              (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
                (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
                  (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
                    (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
                      (.assign .local (ofString "end") (.var .local (ofString "after")))))))))
          (.assign .local (ofString "pos") (.var .local (ofString "after"))))))
  let wbody : ProgHOL 64 := .ite (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end"))) wpop witem
  have hbody_step : ∀ (t : PanSemStateFiniteExact 64 F),
      t.code = originalRuntimeCode → ArenaReady t → WordLocals ["top", "pos", "end", "go"] t →
      (evaluateHOLFiniteState t wbody).1 ≠ some .timeOut →
      FlowsOrResumes (evaluateHOLFiniteState t wbody).1 →
      RlpFlowFrame t (evaluateHOLFiniteState t wbody).2 ∧
      ((evaluateHOLFiniteState t wbody).1 = none → WordLocals ["top", "pos", "end", "go"] (evaluateHOLFiniteState t wbody).2) := by
    intro t ht_code ht_AR ht_w ht_nt ht_fr
    dsimp only [wbody] at ht_nt ht_fr ⊢
    rw [evaluateHOLFiniteState_ite] at ht_nt ht_fr ⊢
    rcases hc : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end"))) with _ | vc
    · simp only [hc] at ht_fr ⊢
      exact ⟨rlpFlowFrame_refl ht_AR, fun h => by simp at h⟩
    · rcases vc with ⟨⟨wc⟩⟩ | _ | _
      · simp only [hc] at ht_nt ht_fr ⊢
        by_cases hwc0 : wc = 0
        · simp only [hwc0, ↓reduceIte] at ht_nt ht_fr ⊢
          exact rff_vib_item t ht_code ht_AR ht_w ht_nt ht_fr
        · simp only [hwc0, ↓reduceIte] at ht_nt ht_fr ⊢
          exact rff_vib_pop t ht_code ht_AR ht_w ht_nt ht_fr
      · simp only [hc] at ht_fr ⊢; exact ⟨rlpFlowFrame_refl ht_AR, fun h => by simp at h⟩
      · simp only [hc] at ht_fr ⊢; exact ⟨rlpFlowFrame_refl ht_AR, fun h => by simp at h⟩
  have hwhile : ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F),
      t.clock = k → t.code = originalRuntimeCode → ArenaReady t → WordLocals ["top", "pos", "end", "go"] t →
      (evaluateHOLFiniteState t (.while wcond wbody)).1 ≠ some .timeOut →
      FlowsOrResumes (evaluateHOLFiniteState t (.while wcond wbody)).1 →
      RlpFlowFrame t (evaluateHOLFiniteState t (.while wcond wbody)).2 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro t hclk ht_code ht_AR ht_w ht_nt ht_fr
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at ht_nt ht_fr ⊢
      revert ht_nt ht_fr
      split <;> intro ht_nt ht_fr
      · rename_i cw hcw
        by_cases hnz : cw = 0
        · subst hnz; simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact rlpFlowFrame_refl ht_AR
        · rw [if_pos hnz] at ht_nt ht_fr ⊢
          by_cases hclk0 : t.clock = 0
          · rw [if_pos hclk0] at ht_nt; simp at ht_nt
          · rw [if_neg hclk0] at ht_nt ht_fr ⊢
            have ht_ARd : ArenaReady (decClockHOLFinite t) :=
              ⟨⟨ht_AR.1.code, ht_AR.1.memaddrs, ht_AR.1.shMemaddrs, ht_AR.1.baseAddr⟩, ht_AR.2⟩
            have hdecF : RlpFlowFrame t (decClockHOLFinite t) :=
              rlpFlowFrame_with_locals_clock (rlpFlowFrame_refl ht_AR) _ _
            have hnc := evaluate_noTopContinue wbody (by decide) (decClockHOLFinite t)
            have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite t) wbody
            rcases hrun_b : evaluateHOLFiniteState (decClockHOLFinite t) wbody with ⟨rb, mid⟩
            simp only [hrun_b] at hnc hrem ht_nt ht_fr ⊢
            have hlt : mid.clock < k := by change mid.clock ≤ t.clock - 1 at hrem; omega
            cases rb with
            | none =>
              obtain ⟨hf_b, hw_b⟩ := hbody_step (decClockHOLFinite t) ht_code ht_ARd ht_w
                (by rw [hrun_b]; simp) (by rw [hrun_b]; exact Or.inl rfl)
              rw [hrun_b] at hf_b hw_b
              exact rlpFlowFrame_trans (rlpFlowFrame_trans hdecF hf_b)
                (ih mid.clock hlt mid rfl hf_b.1.1.code hf_b.1 (hw_b rfl) ht_nt ht_fr)
            | some res_b =>
              cases res_b with
              | «continue» => exact absurd rfl hnc
              | «break» =>
                obtain ⟨hf_b, _⟩ := hbody_step (decClockHOLFinite t) ht_code ht_ARd ht_w
                  (by rw [hrun_b]; simp) (by rw [hrun_b]; exact Or.inr (Or.inl rfl))
                rw [hrun_b] at hf_b; exact rlpFlowFrame_trans hdecF hf_b
              | timeOut => simp at ht_nt
              | returned rv =>
                obtain ⟨hf_b, _⟩ := hbody_step (decClockHOLFinite t) ht_code ht_ARd ht_w
                  (by rw [hrun_b]; simp) (by rw [hrun_b]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩))))
                rw [hrun_b] at hf_b; exact rlpFlowFrame_trans hdecF hf_b
              | exception eid ev =>
                have hres_e : Resumes (some (.exception eid ev)) := by
                  rcases ht_fr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
                obtain ⟨hf_b, _⟩ := hbody_step (decClockHOLFinite t) ht_code ht_ARd ht_w
                  (by rw [hrun_b]; simp) (by rw [hrun_b]; exact Or.inr (Or.inr (Or.inr hres_e)))
                rw [hrun_b] at hf_b; exact rlpFlowFrame_trans hdecF hf_b
              | error | finalFfi _ =>
                rcases ht_fr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
      · exact rlpFlowFrame_refl ht_AR
  change RlpFlowFrame s (evaluateHOLFiniteState s4 (.seq (.while wcond wbody) (.return (.const 0)))).2
  change (evaluateHOLFiniteState s4 (.seq (.while wcond wbody) (.return (.const 0)))).1 ≠ some .timeOut at hnt4
  change FlowsOrResumes (evaluateHOLFiniteState s4 (.seq (.while wcond wbody) (.return (.const 0)))).1 at hfr4
  rw [evaluateHOLFiniteState_seq_line780] at hnt4 hfr4 ⊢
  rcases hwl : evaluateHOLFiniteState s4 (.while wcond wbody) with ⟨rwl, swl⟩
  simp only [hwl] at hnt4 hfr4 ⊢
  cases rwl with
  | none =>
    dsimp only at hnt4 hfr4 ⊢
    have hf_wl := hwhile s4.clock s4 rfl hAR4.1.code hAR4 hw4 (by rw [hwl]; simp) (by rw [hwl]; exact Or.inl rfl)
    rw [hwl] at hf_wl; dsimp only at hf_wl
    have hf_ret := RlpFlowProg.of_ro (ReadOnlyProg.ret (.const 0)) swl hf_wl.1.1.code hf_wl.1 hnt4 hfr4
    exact rlpFlowFrame_trans hpre4 (rlpFlowFrame_trans hf_wl hf_ret)
  | some r =>
    dsimp only at hnt4 hfr4 ⊢
    have hf_wl := hwhile s4.clock s4 rfl hAR4.1.code hAR4 hw4 (by rw [hwl]; exact hnt4) (by rw [hwl]; exact hfr4)
    rw [hwl] at hf_wl; dsimp only at hf_wl
    exact rlpFlowFrame_trans hpre4 hf_wl

private theorem scratch_release_call_exact {F : Type}
    (st : PanSemStateFiniteExact 64 F) (mExp : ExpHOL 64) (mw : BitVec 64)
    (hcode : st.code = originalRuntimeCode)
    (hm : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hsp_ex : ∃ spw : BitVec 64, st.globals.lookup (ofString "scratch_ptr") = some (.val (.word spw))) :
    st.clock = 0 ∨
    ∃ ck, evaluateHOLFiniteState st (.call (some (none, none)) (ofString "scratch_release") [mExp]) =
      (none, { st with
        globals := st.globals.update (ofString "scratch_ptr", .val (.word mw))
        clock := ck }) := by
  by_cases hz : st.clock = 0
  · exact Or.inl hz
  · right
    obtain ⟨spw, hsp⟩ := hsp_ex
    rw [evaluateHOLFiniteState_call]
    have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [mExp] =
        some [.val (.word mw)] := by
      simp [evalListHOLFinite, evalListHOLExact, hm]
    have hlook_sr : originalRuntimeCode.lookup (ofString "scratch_release") =
        some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_scratch_release, .one) :=
      lookup_of_guestAst_getElem 15 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_scratch_release) rfl
    have hl := pan_one_word_lookup st.code.lookup (ofString "scratch_release") (ofString "m")
      (sourceFnBody Guest.Software.guestFn_scratch_release) mw (by rw [hcode]; exact hlook_sr)
    rw [hargs]; dsimp only; rw [hl]; dsimp only; rw [if_neg hz]
    let entry := callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw)))
    have hb : sourceFnBody Guest.Software.guestFn_scratch_release =
        .seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := rfl
    have hev_b : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_scratch_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mw)) entry)) := by
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
      have hm_ent : entry.locals.lookup (ofString "m") = some (.val (.word mw)) := by
        simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsp_ent : entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word spw)) := hsp
      simp [evalHOLExact, hm_ent, isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact,
        hsp_ent, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
        evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
    have hev_b' : evaluateHOLFiniteState
        (callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw))))
        (sourceFnBody Guest.Software.guestFn_scratch_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mw)) entry)) := hev_b
    rw [hev_b']; dsimp only
    have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh]
    exact ⟨st.clock - 1, rfl⟩

private theorem spec_rlp_validate_items :
    FunSpec ArenaReady (fun s r post => Resumes r → RlpFlowFrame s post)
      (ofString "rlp_validate_items") := by
  have hlook : originalRuntimeCode.lookup (ofString "rlp_validate_items") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_validate_items, .one) :=
    lookup_of_guestAst_getElem 111 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_rlp_validate_items) rfl
  refine ⟨_, _, _, hlook, ?_⟩
  intro F s hcode hAR hlookup hnt hres
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA
  have hb : sourceFnBody Guest.Software.guestFn_rlp_validate_items =
      .decCall (ofString "mark") .one (ofString "scratch_mark") []
        (.dec (ofString "e") .one (.const 0)
          (.seq
            (.call (some (none, some (ofString "RlpErr", ofString "e",
                .seq
                  (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
                  (.raise (ofString "RlpErr") (.var .local (ofString "e"))))))
              (ofString "_rlp_validate_items_body") [.var .local (ofString "p"), .var .local (ofString "len")])
            (.seq
              (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
              (.return (.const 0))))) := rfl
  rw [hb] at hnt hres ⊢
  -- Step 1: `decCall "mark" .one "scratch_mark" []`
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have hargs_sm : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [] = some [] := rfl
  have hlook_sm : originalRuntimeCode.lookup (ofString "scratch_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_scratch_mark, .one) :=
    lookup_of_guestAst_getElem 14 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_scratch_mark) rfl
  have hl_sm : lookupCodeHOLFinite s.code.lookup (ofString "scratch_mark") [] =
      some (sourceFnBody Guest.Software.guestFn_scratch_mark, HolFiniteMapExact.empty, .one) := by
    rw [hcode]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "scratch_mark") [] =
        some (sourceFnBody Guest.Software.guestFn_scratch_mark, FEMPTY, .one) := by
      simp only [lookupCodeHOLExact, hlook_sm, List.length_nil, List.nodup_nil, List.zip_nil_left,
        List.all_nil, Bool.and_self, ↓reduceIte, List.foldl_nil]
      rfl
    split
    · rename_i hnone; rw [hraw] at hnone; cases hnone
    · rename_i b' l' r' hsome
      have heq := Option.some.inj (hsome.symm.trans hraw)
      obtain ⟨rfl, hrest⟩ := Prod.mk.inj heq
      obtain ⟨hl_eq, rfl⟩ := Prod.mk.inj hrest
      refine congrArg some (Prod.ext rfl (Prod.ext ?_ rfl))
      apply HolFiniteMapExact.ext; funext k
      simp [HolFiniteMapExact.empty, hl_eq]; rfl
  simp only [hargs_sm, hl_sm] at hnt hres ⊢
  by_cases hz0 : s.clock = 0
  · simp [hz0] at hnt
  · simp only [hz0, ↓reduceIte] at hnt hres ⊢
    have hsm_run : evaluateHOLFiniteState (callEntryStateHOLFinite s HolFiniteMapExact.empty)
        (sourceFnBody Guest.Software.guestFn_scratch_mark) =
        (some (.returned (.val (.word sp))), emptyLocalsHOLFinite (callEntryStateHOLFinite s HolFiniteMapExact.empty)) := by
      have hbsm : sourceFnBody Guest.Software.guestFn_scratch_mark = .return (.var .global (ofString "scratch_ptr")) := rfl
      rw [hbsm, evaluateHOLFiniteState_return]
      have hg_sp : (callEntryStateHOLFinite s HolFiniteMapExact.empty).globals.lookup (ofString "scratch_ptr") =
          some (.val (.word sp)) := hsp
      simp [evalHOLExact, hg_sp, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    simp only [hsm_run] at hnt hres ⊢
    have hsh_sp : (shapeEqHOL (shapeOfHOLExact (.val (.word sp) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word sp) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hsh_sp, ↓reduceIte] at hnt hres ⊢
    -- Step 2: `dec "e" .one (.const 0)`
    rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    have hev0 : ∀ {st : PanSemStateFiniteExact 64 F},
        @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) (.const 0) =
        some (.val (.word 0)) := rfl
    have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    simp only [hev0, hsh0, ↓reduceIte] at hnt hres ⊢
    set s1 := setVarHOLFinite (ofString "e") (.val (.word 0))
      (setVarHOLFinite (ofString "mark") (.val (.word sp))
        { (emptyLocalsHOLFinite (callEntryStateHOLFinite s HolFiniteMapExact.empty)) with locals := s.locals })
    have hs1_eq : s1 = { s with
        locals := (s.locals.update (ofString "mark", .val (.word sp))).update (ofString "e", .val (.word 0))
        clock := s.clock - 1 } := rfl
    have hs1_code : s1.code = originalRuntimeCode := hcode
    have hAR1 : ArenaReady s1 := ⟨⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩, hA⟩
    have hpre1 : RlpFlowFrame s s1 := rlpFlowFrame_with_locals_clock (rlpFlowFrame_refl ⟨hG, hA⟩) _ _
    have hs1_mark : s1.locals.lookup (ofString "mark") = some (.val (.word sp)) := by
      rw [hs1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "e" ≠ ofString "mark" by decide]
    -- Helper: restoring `scratch_ptr := sp` on any state `st` satisfying `RlpFlowFrame s st` yields `RlpFlowFrame s`!
    have restore_sp : ∀ {st : PanSemStateFiniteExact 64 F} (ck : Nat) (L : HolFiniteMapExact MlS (ValueHOL 64)),
        RlpFlowFrame s st →
        RlpFlowFrame s { st with
          locals := L
          globals := st.globals.update (ofString "scratch_ptr", .val (.word sp))
          clock := ck } := by
      intro st ck L hF
      have hsp_hp : (ofString "scratch_ptr" : MlS) ≠ ofString "heap_ptr" := by decide
      have hsp_fp : (ofString "scratch_ptr" : MlS) ≠ ofString "frame_mem_ptr" := by decide
      let outSt : PanSemStateFiniteExact 64 F := { st with
        locals := L
        globals := st.globals.update (ofString "scratch_ptr", .val (.word sp))
        clock := ck }
      have hout_hp : globN outSt "heap_ptr" = globN s "heap_ptr" := by
        have : globN outSt "heap_ptr" = globN st "heap_ptr" := by
          unfold globN; dsimp only [outSt]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hsp_hp, Ne.symm hsp_hp]
        exact this.trans hF.2.1
      have hout_fp : globN outSt "frame_mem_ptr" = globN s "frame_mem_ptr" := by
        have : globN outSt "frame_mem_ptr" = globN st "frame_mem_ptr" := by
          unfold globN; dsimp only [outSt]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hsp_fp, Ne.symm hsp_fp]
        exact this.trans hF.2.2.1
      have hout_sp : globN outSt "scratch_ptr" = globN s "scratch_ptr" := by
        unfold globN; dsimp only [outSt]
        simp [HolFiniteMapExact.lookup_update, FUPDATE, hsp]
      refine ⟨⟨⟨hF.1.1.code, hF.1.1.memaddrs, hF.1.1.shMemaddrs, hF.1.1.baseAddr⟩, ?_⟩,
        hout_hp, hout_fp, le_of_eq hout_sp, hF.2.2.2.2.1, ?_⟩
      · unfold ArenaOK
        rw [hout_hp, hout_fp, hout_sp]
        exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1,
          hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1,
          globalsWord_update (ofString "scratch_ptr") sp rfl hF.1.2.2.2.2.2.2.2.2.2⟩
      · intro k hk
        have hks : k ≠ ofString "scratch_ptr" := by simpa using hk
        have hlk : outSt.globals.lookup k = st.globals.lookup k := by
          dsimp only [outSt]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hks, Ne.symm hks]
        exact (hF.2.2.2.2.2 k hk).trans hlk.symm
    -- Step 3: `.seq (call with RlpErr handler to _rlp_validate_items_body) (seq (scratch_release mark) (return 0))`
    let hcall : ProgHOL 64 :=
      .call (some (none, some (ofString "RlpErr", ofString "e",
          .seq
            (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
            (.raise (ofString "RlpErr") (.var .local (ofString "e"))))))
        (ofString "_rlp_validate_items_body") [.var .local (ofString "p"), .var .local (ofString "len")]
    -- Analyze `evaluateHOLFiniteState s1 hcall`:
    have hhcall : ∀ {r_c : Option (PanSemResultExact 64)} {m_c : PanSemStateFiniteExact 64 F},
        evaluateHOLFiniteState s1 hcall = (r_c, m_c) →
        r_c ≠ some .timeOut →
        (r_c = none → RlpFlowFrame s m_c ∧ m_c.locals.lookup (ofString "mark") = some (.val (.word sp))) ∧
        (Resumes r_c → RlpFlowFrame s m_c) := by
      intro r_c m_c hrc hnt_c
      dsimp only [hcall] at hrc
      rw [evaluateHOLFiniteState_call] at hrc
      rcases hargs_b : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
          [.var .local (ofString "p"), .var .local (ofString "len")] with _ | vs_b
      · simp only [hargs_b] at hrc; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrc
        exact ⟨fun h => by simp at h, fun hr => absurd hr not_resumes_error⟩
      · simp only [hargs_b] at hrc
        rcases hl_b : lookupCodeHOLFinite s1.code.lookup (ofString "_rlp_validate_items_body") vs_b with _ | ⟨body_b, callee_b, ret_b⟩
        · simp only [hl_b] at hrc; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrc
          exact ⟨fun h => by simp at h, fun hr => absurd hr not_resumes_error⟩
        · simp only [hl_b] at hrc
          by_cases hz1 : s1.clock = 0
          · simp only [hz1, ↓reduceIte] at hrc; obtain ⟨rfl, _⟩ := Prod.mk.inj hrc; exact absurd rfl hnt_c
          · simp only [hz1, ↓reduceIte] at hrc
            obtain ⟨params_v, body_v, ret_v, hlook_v, hspec_v⟩ := spec__rlp_validate_items_body
            have hsame := lookupCodeHOLFinite_installed_body s1.code.lookup (ofString "_rlp_validate_items_body")
              params_v body_v body_b ret_v ret_b vs_b callee_b (by rw [hs1_code]; exact hlook_v) hl_b
            subst hsame
            have hret_eq := lookupCodeHOLFinite_installed_return s1 (ofString "_rlp_validate_items_body")
              params_v body_b body_b ret_v ret_b vs_b callee_b (by rw [hs1_code]; exact hlook_v) hl_b
            subst hret_eq
            have hex_v : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") vs =
                some (body_b, (callEntryStateHOLFinite s1 callee_b).locals, ret_b) :=
              ⟨vs_b, by simpa only [hs1_code, callEntryStateHOLFinite] using hl_b⟩
            have hAR_ent : ArenaReady (callEntryStateHOLFinite s1 callee_b) :=
              ⟨guestInv_callEntry s1 callee_b hAR1.1, hAR1.2⟩
            have hpre_ent : RlpFlowFrame s (callEntryStateHOLFinite s1 callee_b) :=
              rlpFlowFrame_with_locals_clock hpre1 _ _
            try rw [fixClockHOLFinite_evaluateState] at hrc
            rcases hrun_v : evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee_b) body_b with ⟨res_v, post_v⟩
            rw [hrun_v] at hrc
            cases res_v with
            | none =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrc
              exact ⟨fun h => by simp at h, fun hr => absurd hr not_resumes_error⟩
            | some rv_in =>
              cases rv_in with
              | timeOut =>
                obtain ⟨rfl, _⟩ := Prod.mk.inj hrc; exact absurd rfl hnt_c
              | «break» | «continue» | error | finalFfi _ =>
                dsimp only at hrc
                obtain ⟨rfl, _⟩ := Prod.mk.inj hrc
                exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
              | returned val_v =>
                dsimp only at hrc
                split at hrc
                · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrc
                  have hf_v := hspec_v (callEntryStateHOLFinite s1 callee_b) hs1_code hAR_ent hex_v
                    (by rw [hrun_v]; simp) (by rw [hrun_v]; exact Or.inl ⟨val_v, rfl⟩)
                  rw [hrun_v] at hf_v; dsimp only at hf_v
                  exact ⟨fun _ => ⟨rlpFlowFrame_with_locals_clock (rlpFlowFrame_trans hpre_ent hf_v) _ _, hs1_mark⟩,
                    fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
                · obtain ⟨rfl, _⟩ := Prod.mk.inj hrc
                  exact ⟨fun h => by simp at h, fun hr => absurd hr not_resumes_error⟩
              | exception eid_v ev_v =>
                dsimp only at hrc
                by_cases heid : eid_v = ofString "RlpErr"
                · subst heid
                  simp only [↓reduceIte] at hrc
                  split at hrc
                  · split at hrc
                    · have hf_v := hspec_v (callEntryStateHOLFinite s1 callee_b) hs1_code hAR_ent hex_v
                        (by rw [hrun_v]; simp)
                        (by rw [hrun_v]; exact Or.inr ⟨ofString "RlpErr", ev_v, rfl, by decide⟩)
                      rw [hrun_v] at hf_v; dsimp only at hf_v
                      have hf_pv : RlpFlowFrame s post_v := rlpFlowFrame_trans hpre_ent hf_v
                      let hst_in := setVarHOLFinite (ofString "e") ev_v { post_v with locals := s1.locals }
                      have hhst_mark : @evalHOLExact 64 F _ hst_in.toExact (fun a => Classical.propDecidable (hst_in.memaddrs a))
                          (.var .local (ofString "mark")) = some (.val (.word sp)) := by
                        simp [hst_in, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hs1_mark,
                          show ofString "e" ≠ ofString "mark" by decide]
                      have hhst_sp : ∃ spw : BitVec 64, hst_in.globals.lookup (ofString "scratch_ptr") = some (.val (.word spw)) := by
                        obtain ⟨_, _, hs_pv, hf_le_sp_pv, _, _, _, _⟩ := hf_pv.1.2
                        have hss : 0 < scratchStart := by decide
                        exact globWord_of_pos post_v "scratch_ptr" (by omega) |>.imp fun _ h => h.1
                      have hhst_code : hst_in.code = originalRuntimeCode := hf_pv.1.1.code
                      rcases scratch_release_call_exact hst_in (.var .local (ofString "mark")) sp hhst_code hhst_mark hhst_sp with hz_h | ⟨ck_h, hsr_h⟩
                      · change (evaluateHOLFiniteState hst_in
                            (.seq (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
                              (.raise (ofString "RlpErr") (.var .local (ofString "e"))))) = (r_c, m_c) at hrc
                        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hrc
                        have ha_h : evalListHOLFinite hst_in (h := fun a => Classical.propDecidable (hst_in.memaddrs a)) [.var .local (ofString "mark")] = some [.val (.word sp)] := by
                          simp [evalListHOLFinite, evalListHOLExact, hhst_mark]
                        have hlook_sr : originalRuntimeCode.lookup (ofString "scratch_release") =
                            some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_scratch_release, .one) :=
                          lookup_of_guestAst_getElem 15 (by rw [guestAst_len]; decide)
                            (extractFn Guest.Software.guestFn_scratch_release) rfl
                        have hl_h := pan_one_word_lookup hst_in.code.lookup (ofString "scratch_release") (ofString "m")
                          (sourceFnBody Guest.Software.guestFn_scratch_release) sp (by rw [hhst_code]; exact hlook_sr)
                        simp only [ha_h, hl_h, hz_h, ↓reduceIte] at hrc
                        obtain ⟨rfl, _⟩ := Prod.mk.inj hrc
                        exact absurd rfl hnt_c
                      · change (evaluateHOLFiniteState hst_in
                            (.seq (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
                              (.raise (ofString "RlpErr") (.var .local (ofString "e"))))) = (r_c, m_c) at hrc
                        rw [evaluateHOLFiniteState_seq_line780, hsr_h] at hrc
                        dsimp only at hrc
                        rw [evaluateHOLFiniteState_raise] at hrc
                        rcases hsh_e : hst_in.eshapes.lookup (ofString "RlpErr") with _ | sh_e
                        · simp only [hsh_e] at hrc
                          obtain ⟨rfl, _⟩ := Prod.mk.inj hrc
                          exact ⟨fun h => by simp at h, fun hr => absurd hr not_resumes_error⟩
                        · rcases hev_e : @evalHOLExact 64 F _
                              ({ hst_in with globals := hst_in.globals.update (ofString "scratch_ptr", .val (.word sp)), clock := ck_h }).toExact
                              (fun a => Classical.propDecidable (hst_in.memaddrs a)) (.var .local (ofString "e")) with _ | val_e
                          · simp only [hsh_e, hev_e] at hrc
                            obtain ⟨rfl, _⟩ := Prod.mk.inj hrc
                            exact ⟨fun h => by simp at h, fun hr => absurd hr not_resumes_error⟩
                          · simp only [hsh_e, hev_e] at hrc
                            by_cases hcond_e : shapeOfHOLExact val_e = sh_e ∧
                                sizeOfShapeWithContextHOL hst_in.structs (shapeOfHOLExact val_e) ≤ 32
                            · rw [if_pos hcond_e] at hrc
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrc
                              exact ⟨fun h => by simp at h,
                                fun _ => restore_sp ck_h _ (rlpFlowFrame_with_locals_clock hf_pv _ _)⟩
                            · rw [if_neg hcond_e] at hrc
                              obtain ⟨rfl, _⟩ := Prod.mk.inj hrc
                              exact ⟨fun h => by simp at h, fun hr => absurd hr not_resumes_error⟩
                    · obtain ⟨rfl, _⟩ := Prod.mk.inj hrc
                      exact ⟨fun h => by simp at h, fun hr => absurd hr not_resumes_error⟩
                  · obtain ⟨rfl, _⟩ := Prod.mk.inj hrc
                    exact ⟨fun h => by simp at h, fun hr => absurd hr not_resumes_error⟩
                · simp only [heid, ↓reduceIte] at hrc
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrc
                  refine ⟨fun h => by simp at h, fun hr => ?_⟩
                  have hne_trap : eid_v ≠ ofString "TrapErr" := by
                    rcases hr with ⟨_, h⟩ | ⟨_, _, h, hntrap⟩
                    · simp at h
                    · injection h with h'; injection h' with he _; subst he; exact hntrap
                  have hf_v := hspec_v (callEntryStateHOLFinite s1 callee_b) hs1_code hAR_ent hex_v
                    (by rw [hrun_v]; simp)
                    (by rw [hrun_v]; exact Or.inr ⟨eid_v, ev_v, rfl, hne_trap⟩)
                  rw [hrun_v] at hf_v; dsimp only at hf_v
                  exact rlpFlowFrame_with_locals_clock (rlpFlowFrame_trans hpre_ent hf_v) _ _
    -- Now combine `hcall` with `.seq (scratch_release mark) (return 0)`!
    have hseq_out : ∀ {r_all : Option (PanSemResultExact 64)} {m_all : PanSemStateFiniteExact 64 F},
        evaluateHOLFiniteState s1
          (.seq hcall (.seq (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")]) (.return (.const 0)))) =
          (r_all, m_all) →
        r_all ≠ some .timeOut →
        Resumes r_all →
        RlpFlowFrame s m_all := by
      intro r_all m_all hall hnt_all hres_all
      rw [evaluateHOLFiniteState_seq_line780] at hall
      rcases h1 : evaluateHOLFiniteState s1 hcall with ⟨r_c, m_c⟩
      rw [h1] at hall
      cases r_c with
      | some rc =>
        dsimp only at hall
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hall
        exact (hhcall h1 hnt_all).2 hres_all
      | none =>
        dsimp only at hall
        obtain ⟨hf_mc, hmark_mc⟩ := (hhcall h1 (by simp)).1 rfl
        have hm_ev : @evalHOLExact 64 F _ m_c.toExact (fun a => Classical.propDecidable (m_c.memaddrs a))
            (.var .local (ofString "mark")) = some (.val (.word sp)) := hmark_mc
        have hm_sp : ∃ spw : BitVec 64, m_c.globals.lookup (ofString "scratch_ptr") = some (.val (.word spw)) := by
          obtain ⟨_, _, hs_mc, hf_le_sp_mc, _, _, _, _⟩ := hf_mc.1.2
          have hss : 0 < scratchStart := by decide
          exact globWord_of_pos m_c "scratch_ptr" (by omega) |>.imp fun _ h => h.1
        rw [evaluateHOLFiniteState_seq_line780] at hall
        rcases scratch_release_call_exact m_c (.var .local (ofString "mark")) sp hf_mc.1.1.code hm_ev hm_sp with hz_m | ⟨ck_m, hsr_m⟩
        · rw [evaluateHOLFiniteState_call] at hall
          have ha_m : evalListHOLFinite m_c (h := fun a => Classical.propDecidable (m_c.memaddrs a)) [.var .local (ofString "mark")] = some [.val (.word sp)] := by
            simp [evalListHOLFinite, evalListHOLExact, hm_ev]
          have hlook_sr : originalRuntimeCode.lookup (ofString "scratch_release") =
              some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_scratch_release, .one) :=
            lookup_of_guestAst_getElem 15 (by rw [guestAst_len]; decide)
              (extractFn Guest.Software.guestFn_scratch_release) rfl
          have hl_m := pan_one_word_lookup m_c.code.lookup (ofString "scratch_release") (ofString "m")
            (sourceFnBody Guest.Software.guestFn_scratch_release) sp (by rw [hf_mc.1.1.code]; exact hlook_sr)
          simp only [ha_m, hl_m, hz_m, ↓reduceIte] at hall
          obtain ⟨rfl, _⟩ := Prod.mk.inj hall
          exact absurd rfl hnt_all
        · rw [hsr_m] at hall; dsimp only at hall
          rw [evaluateHOLFiniteState_return] at hall
          have hsz_z : sizeOfShapeWithContextHOL m_c.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
            simp [shapeOfHOLExact]
          simp only [hev0, hsz_z, ↓reduceIte] at hall
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hall
          exact restore_sp ck_m _ hf_mc
    let fullSeq : ProgHOL 64 :=
      .seq hcall (.seq (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")]) (.return (.const 0)))
    change (evaluateHOLFiniteState s1 fullSeq).1 ≠ some .timeOut at hnt
    change Resumes (evaluateHOLFiniteState s1 fullSeq).1 at hres
    change RlpFlowFrame s { (evaluateHOLFiniteState s1 fullSeq).2 with locals := _ }
    rcases hout_seq : evaluateHOLFiniteState s1 fullSeq with ⟨r_s, m_s⟩
    have hnt_s : r_s ≠ some .timeOut := by rw [hout_seq] at hnt; exact hnt
    have hres_s : Resumes r_s := by rw [hout_seq] at hres; exact hres
    exact rlpFlowFrame_with_locals_clock (hseq_out hout_seq hnt_s hres_s) _ _

private theorem spec_rlp_item_total :
    FunSpec ArenaReady (fun s r post => Resumes r → RlpFlowFrame s post)
      (ofString "rlp_item_total") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 112 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_total) rfl, ?_⟩
  intro F s hcode hAR _hlookup hnt hres
  dsimp only [Guest.Software.guestFn_rlp_item_total, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural] at hnt hres ⊢
  exact (RlpFlowProg.decCall_ro ro_rlp_item_header _ _ _
    (RlpFlowProg.seq
      (RlpFlowProg.ite _
        (RlpFlowProg.call0 spec_rlp_validate_items _)
        (RlpFlowProg.of_ro ReadOnlyProg.skip))
      (RlpFlowProg.of_ro (ReadOnlyProg.ret _)))) s hcode hAR hnt (Or.inr (Or.inr (Or.inr hres)))

private theorem spec_rlp_list_count :
    FunSpec ArenaReady (fun s r post => Resumes r → RlpFlowFrame s post)
      (ofString "rlp_list_count") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 113 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_count) rfl, ?_⟩
  intro F s hcode hAR _hlookup hnt hres
  dsimp only [Guest.Software.guestFn_rlp_list_count, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural] at hnt hres ⊢
  exact (RlpFlowProg.dec _ _ _
    (RlpFlowProg.dec _ _ _
      (RlpFlowProg.seq
        (RlpFlowProg.while_loop _
          (RlpFlowProg.decCall spec_rlp_item_total _ _ _
            (RlpFlowProg.of_ro
              (ReadOnlyProg.seq (ReadOnlyProg.assign_local _ _) (ReadOnlyProg.assign_local _ _)))))
        (RlpFlowProg.of_ro (ReadOnlyProg.ret _))))) s hcode hAR hnt (Or.inr (Or.inr (Or.inr hres)))

theorem ww_rlp_item : WritesWithin (fun _s => []) ["scratch_ptr"] (ofString "rlp_item") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 107 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item) rfl, ?_⟩
  intro F s hcode hAR _hlookup hnt hres
  have hf : RlpFlowProg
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_rlp_item).body) := by
    dsimp only [Guest.Software.guestFn_rlp_item, extractFn,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, Option.map]
    exact RlpFlowProg.seq
      (RlpFlowProg.of_ro (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip))
      (RlpFlowProg.dec _ _ _
        (RlpFlowProg.seq
          (RlpFlowProg.of_ro (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip))
          (RlpFlowProg.seq
            (RlpFlowProg.of_ro
              (ReadOnlyProg.ite _
                (ReadOnlyProg.dec _ _ _
                  (ReadOnlyProg.seq
                    (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                    (ReadOnlyProg.seq
                      (ReadOnlyProg.ite _
                        (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                        ReadOnlyProg.skip)
                      (ReadOnlyProg.ret _))))
                ReadOnlyProg.skip))
            (RlpFlowProg.seq
              (RlpFlowProg.of_ro
                (ReadOnlyProg.ite _
                  (ReadOnlyProg.dec _ _ _
                    (ReadOnlyProg.seq
                      (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                      (ReadOnlyProg.decCall ro_rlp_read_length _ _ _
                        (ReadOnlyProg.seq
                          (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                          (ReadOnlyProg.seq
                            (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip)
                            (ReadOnlyProg.ret _))))))
                  ReadOnlyProg.skip))
              (RlpFlowProg.seq
                (RlpFlowProg.ite _
                  (RlpFlowProg.dec _ _ _
                    (RlpFlowProg.seq
                      (RlpFlowProg.of_ro (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip))
                      (RlpFlowProg.seq
                        (RlpFlowProg.call0 spec_rlp_list_count _)
                        (RlpFlowProg.of_ro (ReadOnlyProg.ret _)))))
                  (RlpFlowProg.of_ro ReadOnlyProg.skip))
                (RlpFlowProg.dec _ _ _
                  (RlpFlowProg.seq
                    (RlpFlowProg.of_ro (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip))
                    (RlpFlowProg.decCall_ro ro_rlp_read_length _ _ _
                      (RlpFlowProg.seq
                        (RlpFlowProg.of_ro (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip))
                        (RlpFlowProg.seq
                          (RlpFlowProg.of_ro (ReadOnlyProg.ite _ (ReadOnlyProg.call0 ro_rlp_fail _) ReadOnlyProg.skip))
                          (RlpFlowProg.seq
                            (RlpFlowProg.call0 spec_rlp_list_count _)
                            (RlpFlowProg.of_ro (ReadOnlyProg.ret _)))))))))))))
  have hout := hf s hcode hAR hnt (Or.inr (Or.inr (Or.inr hres)))
  refine ⟨hout.1, le_of_eq hout.2.1.symm, hout.2.2.2.1, ?_, hout.2.2.2.2.2⟩
  intro a hkeep _
  exact hout.2.2.2.2.1 a hkeep (fun hch => by unfold CellHits at hch; omega)

theorem ww_rlp_list_count : WritesWithin (fun _s => []) ["scratch_ptr"] (ofString "rlp_list_count") := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := spec_rlp_list_count
  refine ⟨params, body, ret, hlook, ?_⟩
  intro F s hcode hAR hlookup hnt hres
  have hout := hspec s hcode hAR hlookup hnt hres
  refine ⟨hout.1, le_of_eq hout.2.1.symm, hout.2.2.2.1, ?_, hout.2.2.2.2.2⟩
  intro a hkeep _
  exact hout.2.2.2.2.1 a hkeep (fun hch => by unfold CellHits at hch; omega)

/-! ## 6. Byte-write & `memcpy` exact evaluation for MPT node constructors -/

theorem panGetByte_panSetByte_same (addr : BitVec 64) (b : UInt8) (cell : BitVec 64) (be : Bool) :
    panGetByteHOL addr (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be) be = b := by
  have hb8 : b.toNat < 256 := b.toNat_lt_size
  have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
  have h256_pow : (256 : Nat) ^ (if be then 8 - 1 - addr.toNat % 8 else addr.toNat % 8) =
      2 ^ byteBitIndex addr be := by
    rw [pow256_eq_two_pow_mul]
    cases be <;> simp [byteBitIndex]
  simp only [panGetByteHOL]
  have h1 : (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
      256 ^ (if be then 8 - 1 - addr.toNat % 8 else addr.toNat % 8) % 256 = b.toNat := by
    change (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
      256 ^ (if be then 8 - 1 - addr.toNat % 8 else addr.toNat % 8) % 256 = b.toNat
    rw [hset_nat, h256_pow]
    set K := byteBitIndex addr be
    have hpK : 0 < 2 ^ K := Nat.two_pow_pos K
    have hrem : cell.toNat % 2 ^ K < 2 ^ K := Nat.mod_lt _ hpK
    have hdK8 : 2 ^ (K + 8) = 256 * 2 ^ K := by
      rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_comm]
    have hsum : cell.toNat / 2 ^ (K + 8) * 2 ^ (K + 8) + b.toNat * 2 ^ K + cell.toNat % 2 ^ K =
        cell.toNat % 2 ^ K + (cell.toNat / 2 ^ (K + 8) * 256 + b.toNat) * 2 ^ K := by
      rw [hdK8, ← Nat.mul_assoc, ← Nat.add_mul]
      omega
    rw [hsum, Nat.add_mul_div_right _ _ hpK, Nat.div_eq_of_lt hrem, Nat.zero_add]
    omega
  change UInt8.ofNat ((panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
      256 ^ (if be then 8 - 1 - addr.toNat % 8 else addr.toNat % 8) % 256) = b
  rw [h1]
  exact UInt8.ofNat_toNat

theorem panMemStoreByte_other_byte {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {be : Bool}
    {addr : BitVec 64} {bw : BitVec 8} {mem' : BitVec 64 → HolWordLab 64}
    (hst : panMemStoreByteWord8HOL mem dom be addr bw = some mem')
    {addr' : BitVec 64} (hne : addr' ≠ addr) :
    (match mem' (panByteAlignHOL addr') with | .word v => (panGetByteHOL addr' v be).toNat) =
    (match mem (panByteAlignHOL addr') with | .word v => (panGetByteHOL addr' v be).toNat) := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hcell : mem (panByteAlignHOL addr) with
  | word cell =>
    rw [hcell] at hst
    split at hst
    · injection hst with hmem
      subst hmem
      by_cases hal : panByteAlignHOL addr' = panByteAlignHOL addr
      · simp only [hal, ↓reduceIte, hcell, panGetByteHOL]
        let b : UInt8 := UInt8.ofNat bw.toNat
        have hb8 : b.toNat < 256 := b.toNat_lt_size
        have hbw_eq : bw.toNat = b.toNat := by
          have := bw.isLt
          simp [b, UInt8.toNat_ofNat', Nat.mod_eq_of_lt this]
        rw [hbw_eq]
        have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
        have hpow_div_low : ∀ (x y z K J : Nat), y < 256 → z < 2 ^ K → J + 8 ≤ K →
            (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 = z / 2 ^ J % 256 := by
          intro x y z K J _ _ hJK
          have hpJ : 0 < 2 ^ J := Nat.two_pow_pos J
          have hdK : 2 ^ K = 2 ^ (K - J - 8) * (256 * 2 ^ J) := by
            have hk_eq : K = (K - J - 8) + 8 + J := by omega
            conv_lhs => rw [hk_eq]
            rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
          have hdK8 : 2 ^ (K + 8) = 2 ^ (K - J) * (256 * 2 ^ J) := by
            have hk_eq : K + 8 = (K - J) + 8 + J := by omega
            conv_lhs => rw [hk_eq]
            rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
          have h1 : x * 2 ^ (K + 8) + y * 2 ^ K + z =
              z + ((x * 2 ^ (K - J) + y * 2 ^ (K - J - 8)) * 256) * 2 ^ J := by
            rw [hdK, hdK8, ← Nat.mul_assoc x, ← Nat.mul_assoc y, ← Nat.add_mul, ← Nat.mul_assoc]
            omega
          rw [h1, Nat.add_mul_div_right _ _ hpJ]
          omega
        have hpow_div_high : ∀ (x y z K J : Nat), y < 256 → z < 2 ^ K → K + 8 ≤ J →
            (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 =
              (x * 2 ^ (K + 8)) / 2 ^ J % 256 := by
          intro x y z K J hy hz hKJ
          have hyz : y * 2 ^ K + z < 2 ^ (K + 8) := by
            have : y * 2 ^ K ≤ 255 * 2 ^ K := Nat.mul_le_mul_right _ (by omega)
            have h2 : 255 * 2 ^ K + 2 ^ K = 2 ^ (K + 8) := by
              rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]; omega
            omega
          have hdJ : 2 ^ J = 2 ^ (K + 8) * 2 ^ (J - (K + 8)) := by
            have hj_eq : J = (K + 8) + (J - (K + 8)) := by omega
            conv_lhs => rw [hj_eq]
            rw [Nat.pow_add]
          have hpK8 : 0 < 2 ^ (K + 8) := Nat.two_pow_pos _
          have hsum : x * 2 ^ (K + 8) + y * 2 ^ K + z = (y * 2 ^ K + z) + x * 2 ^ (K + 8) := by omega
          rw [hsum, hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
            Nat.add_mul_div_right _ _ hpK8, Nat.div_eq_of_lt hyz, Nat.zero_add,
            Nat.mul_div_cancel _ hpK8]
        have hcell_high : ∀ J : Nat, byteBitIndex addr be + 8 ≤ J →
            ((cell.toNat / 2 ^ (byteBitIndex addr be + 8)) * 2 ^ (byteBitIndex addr be + 8)) / 2 ^ J =
              cell.toNat / 2 ^ J := by
          intro J hKJ
          have hdJ : 2 ^ J = 2 ^ (byteBitIndex addr be + 8) * 2 ^ (J - (byteBitIndex addr be + 8)) := by
            have hj_eq : J = (byteBitIndex addr be + 8) + (J - (byteBitIndex addr be + 8)) := by omega
            conv_lhs => rw [hj_eq]
            rw [Nat.pow_add]
          have hpK8 : 0 < 2 ^ (byteBitIndex addr be + 8) := Nat.two_pow_pos _
          rw [hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpK8]
        have h256_pow : ∀ a : BitVec 64,
            (256 : Nat) ^ (if be then 8 - 1 - a.toNat % 8 else a.toNat % 8) = 2 ^ byteBitIndex a be := by
          intro a
          rw [pow256_eq_two_pow_mul]
          cases be <;> simp [byteBitIndex]
        have hmod_ne : addr'.toNat % 8 ≠ addr.toNat % 8 := by
          intro hmeq
          apply hne
          apply BitVec.eq_of_toNat_eq
          have ha1 := panByteAlign_toNat64 addr'
          have ha2 := panByteAlign_toNat64 addr
          rw [hal] at ha1
          omega
        have hidx_sep : byteBitIndex addr' be + 8 ≤ byteBitIndex addr be ∨
            byteBitIndex addr be + 8 ≤ byteBitIndex addr' be := by
          have hm1 : addr'.toNat % 8 < 8 := by omega
          have hm2 : addr.toNat % 8 < 8 := by omega
          cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
        have heq_mod : (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
            256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 =
          cell.toNat / 256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 := by
          rw [hset_nat, h256_pow addr']
          rcases hidx_sep with hlow | hhigh
          · rw [hpow_div_low _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hlow]
            have hc_eq : 2 ^ byteBitIndex addr be =
                (2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8)) * 256) *
                  2 ^ byteBitIndex addr' be := by
              have hk_eq : byteBitIndex addr be =
                  (byteBitIndex addr be - (byteBitIndex addr' be + 8)) + 8 + byteBitIndex addr' be := by omega
              conv_lhs => rw [hk_eq]
              rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]
            have hcell_eq : cell.toNat =
                cell.toNat % 2 ^ byteBitIndex addr be +
                (((cell.toNat / 2 ^ byteBitIndex addr be) *
                  2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
                  2 ^ byteBitIndex addr' be := by
              have hdm := (Nat.div_add_mod cell.toNat (2 ^ byteBitIndex addr be)).symm
              rw [Nat.mul_comm (2 ^ byteBitIndex addr be)] at hdm
              have hmul : (cell.toNat / 2 ^ byteBitIndex addr be) * 2 ^ byteBitIndex addr be =
                  (((cell.toNat / 2 ^ byteBitIndex addr be) *
                    2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
                    2 ^ byteBitIndex addr' be := by
                rw [hc_eq, ← Nat.mul_assoc, ← Nat.mul_assoc]
              rw [hmul] at hdm
              omega
            conv_rhs => rw [hcell_eq]
            rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
            omega
          · rw [hpow_div_high _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hhigh,
              hcell_high _ hhigh]
        simpa [UInt8.toNat_ofNat'] using heq_mod
      · simp only [hal, ↓reduceIte]
    · cases hst

theorem panMemStoreByte_same_byte {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {be : Bool}
    {addr : BitVec 64} {bw : BitVec 8} {mem' : BitVec 64 → HolWordLab 64}
    (hst : panMemStoreByteWord8HOL mem dom be addr bw = some mem') :
    (match mem' (panByteAlignHOL addr) with | .word v => (panGetByteHOL addr v be).toNat) = bw.toNat := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hcell : mem (panByteAlignHOL addr) with
  | word cell =>
    rw [hcell] at hst
    split at hst
    · injection hst with hmem
      subst hmem
      simp only [↓reduceIte]
      let b : UInt8 := UInt8.ofNat bw.toNat
      have hbw_eq : bw.toNat = b.toNat := by
        have := bw.isLt
        simp [b, UInt8.toNat_ofNat', Nat.mod_eq_of_lt this]
      rw [hbw_eq, panGetByte_panSetByte_same addr b cell be]
    · cases hst

theorem memB_word_eq {F : Type} (s : PanSemStateFiniteExact 64 F) (x w : BitVec 64)
    (hx8 : x.toNat % 8 = 0) (hx_lt : x.toNat + 8 ≤ 2 ^ 64)
    (hm : s.memory x = .word w) (j : Nat) (hj : j < 8) :
    memB s (x.toNat + j) = (panGetByteHOL (x + BitVec.ofNat 64 j) w s.be).toNat := by
  have haddr_bv : BitVec.ofNat 64 (x.toNat + j) = x + BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
    omega
  have hal : panByteAlignHOL (BitVec.ofNat 64 (x.toNat + j)) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold memB
  rw [hal, hm, haddr_bv]

structure MemCopyEffect {F : Type} (s0 s : PanSemStateFiniteExact 64 F) (dst src n : Nat) : Prop where
  code       : s.code = s0.code
  memaddrs   : s.memaddrs = s0.memaddrs
  shMemaddrs : s.shMemaddrs = s0.shMemaddrs
  baseAddr   : s.baseAddr = s0.baseAddr
  be         : s.be = s0.be
  globals    : s.globals = s0.globals
  cell_frame : FrameOutside s0 s [(dst, n)] (0, 0)
  byte_frame : ∀ a : Nat, a < 2 ^ 64 → ¬ InIvl a (dst, n) → memB s a = memB s0 a
  byte_copy  : ∀ k : Nat, k < n → memB s (dst + k) = memB s0 (src + k)

theorem MemCopyEffect.refl_zero {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst src : Nat) :
    MemCopyEffect s0 s0 dst src 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ hk => by omega⟩

theorem MemCopyEffect.with_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst src n : Nat} (h : MemCopyEffect s0 s dst src n)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (c : Nat) :
    MemCopyEffect s0 { s with locals := L, clock := c } dst src n :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals,
   h.cell_frame, h.byte_frame, h.byte_copy⟩

theorem store_word_copy_step {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 src0 : BitVec 64} {cur : Nat}
    (hG : GuestInv s) (hmce : MemCopyEffect s0 s dst0.toNat src0.toNat cur)
    (hdisj : Disj (dst0.toNat, cur + 8) (src0.toNat, cur + 8))
    (hsrc_lt : src0.toNat + cur + 8 ≤ 2 ^ 64)
    (addrExp srcAddrExp : ExpHOL 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word (dst0 + BitVec.ofNat 64 cur))))
    (hsrc_addr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcAddrExp =
      some (.val (.word (src0 + BitVec.ofNat 64 cur))))
    (hprev : cur > 0 → sourceBase ≤ dst0.toNat ∧ dst0.toNat + cur ≤ heapEnd)
    (hnone : (evaluateHOLFiniteState s (.store addrExp (.load .one srcAddrExp))).1 = none) :
    sourceBase ≤ dst0.toNat ∧ dst0.toNat + (cur + 8) ≤ heapEnd ∧
    MemCopyEffect s0 (evaluateHOLFiniteState s (.store addrExp (.load .one srcAddrExp))).2
      dst0.toNat src0.toNat (cur + 8) ∧
    (evaluateHOLFiniteState s (.store addrExp (.load .one srcAddrExp))).2.locals = s.locals := by
  have hhe_lt : heapEnd < 2 ^ 64 := by decide
  have hhe_al : heapEnd % 8 = 0 := by decide
  let _ : DecidablePred s.memaddrs := fun a => Classical.propDecidable (s.memaddrs a)
  rw [evaluateHOLFiniteState_store, haddr] at hnone ⊢
  dsimp only at hnone ⊢
  -- Evaluate `.load .one srcAddrExp`:
  have hload_eq : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one srcAddrExp) =
      if s.memaddrs (src0 + BitVec.ofNat 64 cur) then
        some (ValueHOL.val (s.memory (src0 + BitVec.ofNat 64 cur)))
      else none := by
    have hwf : isWfShapeExactHOL s.structs ShapeHOL.one = true := by simp [isWfShapeExactHOL]
    simp only [evalHOLExact, hsrc_addr, memLoadHOLExact.eq_1]
    split
    · cases s.memory (src0 + BitVec.ofNat 64 cur) with
      | word w => simp [hwf]
    · rfl
  rw [hload_eq] at hnone ⊢
  by_cases hdom_src : s.memaddrs (src0 + BitVec.ofNat 64 cur)
  · simp only [hdom_src, ↓reduceIte] at hnone ⊢
    cases hsrc_cell : s.memory (src0 + BitVec.ofNat 64 cur) with
    | word w_src =>
      simp only [hsrc_cell, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hnone ⊢
      by_cases hdom_dst : s.memaddrs (dst0 + BitVec.ofNat 64 cur)
      · simp only [hdom_dst, ↓reduceIte] at hnone ⊢
        have hd_ord : sourceBase ≤ (dst0 + BitVec.ofNat 64 cur).toNat ∧
            (dst0 + BitVec.ofNat 64 cur).toNat < heapEnd ∧
            (dst0 + BitVec.ofNat 64 cur).toNat % 8 = 0 := by
          have := hG.memaddrs ▸ hdom_dst; rwa [ordinaryDomain_iff] at this
        have hs_ord : sourceBase ≤ (src0 + BitVec.ofNat 64 cur).toNat ∧
            (src0 + BitVec.ofNat 64 cur).toNat < heapEnd ∧
            (src0 + BitVec.ofNat 64 cur).toNat % 8 = 0 := by
          have := hG.memaddrs ▸ hdom_src; rwa [ordinaryDomain_iff] at this
        have hdst_add : (dst0 + BitVec.ofNat 64 cur).toNat = dst0.toNat + cur := by
          by_cases hcz : cur = 0
          · subst hcz; simp
          · have hp := hprev (by omega)
            rw [BitVec.toNat_add, BitVec.toNat_ofNat]
            have hcm : cur % 2 ^ 64 = cur := Nat.mod_eq_of_lt (by omega)
            rw [hcm]; exact Nat.mod_eq_of_lt (by omega)
        have hsrc_add : (src0 + BitVec.ofNat 64 cur).toNat = src0.toNat + cur := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          have hcm : cur % 2 ^ 64 = cur := Nat.mod_eq_of_lt (by omega)
          rw [hcm]; exact Nat.mod_eq_of_lt (by omega)
        have hd_lo : sourceBase ≤ dst0.toNat := by
          by_cases hcz : cur = 0
          · subst hcz; simpa using hd_ord.1
          · exact (hprev (by omega)).1
        have hd_hi : dst0.toNat + (cur + 8) ≤ heapEnd := by omega
        -- Notice `s.memory (src0 + cur) = s0.memory (src0 + cur)` because `src0 + cur` does not hit `(dst0, cur)`!
        have hsrc_unch : s0.memory (src0 + BitVec.ofNat 64 cur) = .word w_src := by
          have hnot_hit : ¬ CellHits (src0 + BitVec.ofNat 64 cur).toNat (dst0.toNat, cur) := by
            unfold CellHits
            unfold Disj at hdisj
            rw [hsrc_add]
            omega
          have heq := hmce.cell_frame (src0 + BitVec.ofNat 64 cur)
            (fun i hi => by simp at hi; subst hi; exact hnot_hit)
            (fun h0 => by unfold CellHits at h0; omega)
          exact heq.symm.trans hsrc_cell
        refine ⟨hd_lo, hd_hi, ⟨hmce.code, hmce.memaddrs, hmce.shMemaddrs, hmce.baseAddr,
          hmce.be, hmce.globals, ?_, ?_, ?_⟩, trivial⟩
        · intro a hk hf
          dsimp only
          have hne : a ≠ dst0 + BitVec.ofNat 64 cur := by
            rintro rfl
            apply hk (dst0.toNat, cur + 8) (List.mem_singleton.2 rfl)
            unfold CellHits; rw [hdst_add]; omega
          rw [if_neg hne]
          exact hmce.cell_frame a
            (fun i hi hch => by
              simp at hi; subst hi
              exact hk (dst0.toNat, cur + 8) (List.mem_singleton.2 rfl)
                ⟨hch.1, by unfold CellHits at hch; omega⟩)
            hf
        · intro a ha_lt hnot_in
          have hal_ne : panByteAlignHOL (BitVec.ofNat 64 a) ≠ dst0 + BitVec.ofNat 64 cur := by
            intro heq
            have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 a)
            rw [heq, hdst_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at hc_nat
            apply hnot_in; unfold InIvl; omega
          unfold memB; dsimp only
          rw [if_neg hal_ne]
          exact hmce.byte_frame a ha_lt (fun hin => hnot_in ⟨hin.1, by unfold InIvl at hin; omega⟩)
        · intro k hk
          by_cases hk_old : k < cur
          · have hal_ne : panByteAlignHOL (BitVec.ofNat 64 (dst0.toNat + k)) ≠ dst0 + BitVec.ofNat 64 cur := by
              intro heq
              have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 (dst0.toNat + k))
              rw [heq, hdst_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc_nat
              omega
            have hm_eq : memB { s with memory := fun c => if c = dst0 + BitVec.ofNat 64 cur then .word w_src else s.memory c }
                (dst0.toNat + k) = memB s (dst0.toNat + k) := by
              unfold memB; dsimp only; rw [if_neg hal_ne]
            rw [hm_eq]
            exact hmce.byte_copy k hk_old
          · set j := k - cur
            have hj8 : j < 8 := by omega
            have hk_eq : dst0.toNat + k = (dst0 + BitVec.ofNat 64 cur).toNat + j := by omega
            have hsk_eq : src0.toNat + k = (src0 + BitVec.ofNat 64 cur).toNat + j := by omega
            let postS : PanSemStateFiniteExact 64 F :=
              { s with memory := fun c => if c = dst0 + BitVec.ofNat 64 cur then .word w_src else s.memory c }
            change memB postS (dst0.toNat + k) = memB s0 (src0.toNat + k)
            rw [hk_eq, hsk_eq]
            rw [memB_word_eq postS (dst0 + BitVec.ofNat 64 cur) w_src hd_ord.2.2 (by omega)
              (by dsimp [postS]; simp) j hj8]
            rw [memB_word_eq s0 (src0 + BitVec.ofNat 64 cur) w_src hs_ord.2.2 (by omega)
              hsrc_unch j hj8]
            have hbe : postS.be = s0.be := hmce.be
            rw [hbe]
            -- Wait: `panGetByteHOL (x + j) w_src be` depends ONLY on `(x + j).toNat % 8`!
            -- Since both `dst0 + cur` and `src0 + cur` are 8-byte aligned (`% 8 = 0`),
            -- `((dst0 + cur) + j).toNat % 8 = j = ((src0 + cur) + j).toNat % 8`!
            have hmod_d : ((dst0 + BitVec.ofNat 64 cur) + BitVec.ofNat 64 j).toNat % 8 = j := by
              have hadd_j : ((dst0 + BitVec.ofNat 64 cur) + BitVec.ofNat 64 j).toNat =
                  (dst0 + BitVec.ofNat 64 cur).toNat + j := by
                rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                have hjm : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
                rw [hjm]; exact Nat.mod_eq_of_lt (by omega)
              rw [hadd_j]; omega
            have hmod_s : ((src0 + BitVec.ofNat 64 cur) + BitVec.ofNat 64 j).toNat % 8 = j := by
              have hadd_j : ((src0 + BitVec.ofNat 64 cur) + BitVec.ofNat 64 j).toNat =
                  (src0 + BitVec.ofNat 64 cur).toNat + j := by
                rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                have hjm : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
                rw [hjm]; exact Nat.mod_eq_of_lt (by omega)
              rw [hadd_j]; omega
            simp only [panGetByteHOL, show 64 / 8 = 8 by decide, hmod_d, hmod_s]
      · simp [hdom_dst] at hnone
  · simp [hdom_src] at hnone

theorem storeByte_copy_step {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 src0 : BitVec 64} {cur : Nat}
    (hG : GuestInv s) (hmce : MemCopyEffect s0 s dst0.toNat src0.toNat cur)
    (hdisj : Disj (dst0.toNat, cur + 1) (src0.toNat, cur + 1))
    (hsrc_lt : src0.toNat + cur + 1 ≤ 2 ^ 64)
    (hdst_al : cur = 0 → dst0.toNat % 8 = 0 ∨ sourceBase ≤ dst0.toNat)
    (addrExp srcAddrExp : ExpHOL 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word (dst0 + BitVec.ofNat 64 cur))))
    (hsrc_addr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcAddrExp =
      some (.val (.word (src0 + BitVec.ofNat 64 cur))))
    (hprev : cur > 0 → sourceBase ≤ dst0.toNat ∧ dst0.toNat + cur ≤ heapEnd)
    (hnone : (evaluateHOLFiniteState s (.storeByte addrExp (.loadByte srcAddrExp))).1 = none) :
    sourceBase ≤ dst0.toNat ∧ dst0.toNat + (cur + 1) ≤ heapEnd ∧
    MemCopyEffect s0 (evaluateHOLFiniteState s (.storeByte addrExp (.loadByte srcAddrExp))).2
      dst0.toNat src0.toNat (cur + 1) ∧
    (evaluateHOLFiniteState s (.storeByte addrExp (.loadByte srcAddrExp))).2.locals = s.locals := by
  have hhe_lt : heapEnd < 2 ^ 64 := by decide
  have hhe_al : heapEnd % 8 = 0 := by decide
  let _ : DecidablePred s.memaddrs := fun a => Classical.propDecidable (s.memaddrs a)
  rw [evaluateHOLFiniteState_storeByte, haddr] at hnone ⊢
  dsimp only at hnone ⊢
  have hloadB : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.loadByte srcAddrExp) =
      match s.memory (panByteAlignHOL (src0 + BitVec.ofNat 64 cur)) with
      | .word v =>
        if s.memaddrs (panByteAlignHOL (src0 + BitVec.ofNat 64 cur)) then
          some (ValueHOL.val (.word (BitVec.ofNat 64 (panGetByteHOL (src0 + BitVec.ofNat 64 cur) v s.be).toNat)))
        else none := by
    simp only [evalHOLExact, hsrc_addr, panMemLoadByteHOL]
    cases hcell : s.memory (panByteAlignHOL (src0 + BitVec.ofNat 64 cur)) with
    | word v =>
      split
      · simp
      · rfl
  rw [hloadB] at hnone ⊢
  cases hsrc_cell : s.memory (panByteAlignHOL (src0 + BitVec.ofNat 64 cur)) with
  | word v_src =>
    simp only [hsrc_cell] at hnone ⊢
    by_cases hdom_s : s.memaddrs (panByteAlignHOL (src0 + BitVec.ofNat 64 cur))
    · simp only [hdom_s, ↓reduceIte] at hnone ⊢
      split at hnone
      · rename_i mem' hst
        simp only [hst] at ⊢
        have hdom_d : s.memaddrs (panByteAlignHOL (dst0 + BitVec.ofNat 64 cur)) := by
          by_contra hc
          unfold panMemStoreByteWord8HOL at hst
          cases s.memory (panByteAlignHOL (dst0 + BitVec.ofNat 64 cur)) with
          | word _ => simp [hc] at hst
        have hd_ord : sourceBase ≤ (panByteAlignHOL (dst0 + BitVec.ofNat 64 cur)).toNat ∧
            (panByteAlignHOL (dst0 + BitVec.ofNat 64 cur)).toNat < heapEnd ∧
            (panByteAlignHOL (dst0 + BitVec.ofNat 64 cur)).toNat % 8 = 0 := by
          have := hG.memaddrs ▸ hdom_d; rwa [ordinaryDomain_iff] at this
        have hal_d := panByteAlign_toNat64 (dst0 + BitVec.ofNat 64 cur)
        have hdst_add : (dst0 + BitVec.ofNat 64 cur).toNat = dst0.toNat + cur := by
          by_cases hcz : cur = 0
          · subst hcz; simp
          · have hp := hprev (by omega)
            rw [BitVec.toNat_add, BitVec.toNat_ofNat]
            have hcm : cur % 2 ^ 64 = cur := Nat.mod_eq_of_lt (by omega)
            rw [hcm]; exact Nat.mod_eq_of_lt (by omega)
        have hsrc_add : (src0 + BitVec.ofNat 64 cur).toNat = src0.toNat + cur := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          have hcm : cur % 2 ^ 64 = cur := Nat.mod_eq_of_lt (by omega)
          rw [hcm]; exact Nat.mod_eq_of_lt (by omega)
        have hd_lo : sourceBase ≤ dst0.toNat := by
          by_cases hcz : cur = 0
          · rcases hdst_al hcz with hal0 | hlo0
            · have hd0 : dst0 + BitVec.ofNat 64 cur = dst0 := by subst hcz; simp
              rw [hd0] at hal_d hd_ord
              omega
            · exact hlo0
          · exact (hprev (by omega)).1
        have hd_hi : dst0.toNat + (cur + 1) ≤ heapEnd := by omega
        have hmem_cell : ∀ a : BitVec 64, a ≠ panByteAlignHOL (dst0 + BitVec.ofNat 64 cur) → mem' a = s.memory a := by
          intro a hne
          have hm' := hst
          unfold panMemStoreByteWord8HOL at hm'
          cases s.memory (panByteAlignHOL (dst0 + BitVec.ofNat 64 cur)) with
          | word c =>
            dsimp only at hm'; rw [if_pos hdom_d] at hm'
            injection hm' with hmeq; subst hmeq; simp [hne]
        -- Notice the byte read at `src0 + cur` in `s` equals `memB s0 (src0.toNat + cur)`!
        have hsrc_bv : BitVec.ofNat 64 (src0.toNat + cur) = src0 + BitVec.ofNat 64 cur := by
          apply BitVec.eq_of_toNat_eq
          rw [hsrc_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hdst_bv : BitVec.ofNat 64 (dst0.toNat + cur) = dst0 + BitVec.ofNat 64 cur := by
          apply BitVec.eq_of_toNat_eq
          rw [hdst_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hsrc_byte_eq : (panGetByteHOL (src0 + BitVec.ofNat 64 cur) v_src s.be).toNat =
            memB s0 (src0.toNat + cur) := by
          have hnot_in : ¬ InIvl (src0.toNat + cur) (dst0.toNat, cur) := by
            unfold InIvl; unfold Disj at hdisj; omega
          rw [← hmce.byte_frame (src0.toNat + cur) (by omega) hnot_in]
          unfold memB
          rw [hsrc_bv, hsrc_cell]
        refine ⟨hd_lo, hd_hi, ⟨hmce.code, hmce.memaddrs, hmce.shMemaddrs, hmce.baseAddr,
          hmce.be, hmce.globals, ?_, ?_, ?_⟩, trivial⟩
        · intro a hk hf
          dsimp only
          by_cases hax : a = panByteAlignHOL (dst0 + BitVec.ofNat 64 cur)
          · exfalso; subst hax
            apply hk (dst0.toNat, cur + 1) (List.mem_singleton.2 rfl)
            unfold CellHits; rw [hal_d, hdst_add]; omega
          · change mem' a = s0.memory a
            rw [hmem_cell a hax]
            exact hmce.cell_frame a
              (fun i hi hch => by
                simp at hi; subst hi
                exact hk (dst0.toNat, cur + 1) (List.mem_singleton.2 rfl)
                  ⟨hch.1, by unfold CellHits at hch; omega⟩)
              hf
        · intro a ha_lt hnot_in
          have hba_ne : BitVec.ofNat 64 a ≠ dst0 + BitVec.ofNat 64 cur := by
            intro heq
            have : a = dst0.toNat + cur := by
              have := congrArg BitVec.toNat heq
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt, hdst_add] at this
              exact this
            subst this
            exact hnot_in ⟨by omega, by omega⟩
          have hob := @panMemStoreByte_other_byte s.memory s.memaddrs
            (fun addr => Classical.propDecidable (s.memaddrs addr)) s.be
            (dst0 + BitVec.ofNat 64 cur) _ mem' hst (BitVec.ofNat 64 a) hba_ne
          have heq_m : memB { s with memory := mem' } a = memB s a := hob
          exact heq_m.trans (hmce.byte_frame a ha_lt (fun hin => hnot_in ⟨hin.1, by unfold InIvl at hin; omega⟩))
        · intro k hk
          by_cases hk_old : k < cur
          · have hba_ne : BitVec.ofNat 64 (dst0.toNat + k) ≠ dst0 + BitVec.ofNat 64 cur := by
              intro heq
              have := congrArg BitVec.toNat heq
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hdst_add] at this
              omega
            have hob := @panMemStoreByte_other_byte s.memory s.memaddrs
              (fun addr => Classical.propDecidable (s.memaddrs addr)) s.be
              (dst0 + BitVec.ofNat 64 cur) _ mem' hst (BitVec.ofNat 64 (dst0.toNat + k)) hba_ne
            have heq_m : memB { s with memory := mem' } (dst0.toNat + k) = memB s (dst0.toNat + k) := hob
            exact heq_m.trans (hmce.byte_copy k hk_old)
          · have hk_eq : k = cur := by omega
            rw [hk_eq]
            have hsame := @panMemStoreByte_same_byte s.memory s.memaddrs
              (fun addr => Classical.propDecidable (s.memaddrs addr)) s.be
              (dst0 + BitVec.ofNat 64 cur) _ mem' hst
            have heq_m : memB { s with memory := mem' } (dst0.toNat + cur) =
                (BitVec.ofNat 8 (BitVec.ofNat 64 (panGetByteHOL (src0 + BitVec.ofNat 64 cur) v_src s.be).toNat).toNat).toNat := by
              unfold memB; dsimp only; rw [hdst_bv]; exact hsame
            rw [heq_m]
            have hlt256 : (panGetByteHOL (src0 + BitVec.ofNat 64 cur) v_src s.be).toNat < 256 := UInt8.toNat_lt _
            simp only [BitVec.toNat_ofNat]
            have m64 : (panGetByteHOL (src0 + BitVec.ofNat 64 cur) v_src s.be).toNat % 2 ^ 64 =
                (panGetByteHOL (src0 + BitVec.ofNat 64 cur) v_src s.be).toNat :=
              Nat.mod_eq_of_lt (by omega)
            rw [m64, Nat.mod_eq_of_lt hlt256, hsrc_byte_eq]
      · simp at hnone
    · simp [hdom_s] at hnone

theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
            sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem eval_dst_src_i_off {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64) (cur off : Nat)
    (hcur_lt : cur + off < 2 ^ 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base)))
    (hi_loc : s.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 cur)))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString nm), .var .local (ofString "i"), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (base + BitVec.ofNat 64 (cur + off)))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, hi_loc,
    wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  congr 3
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := by simp
  rw [hz]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem eval_dst_src_i_0 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64) (cur : Nat)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base)))
    (hi_loc : s.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 cur)))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString nm), .var .local (ofString "i")]) =
      some (.val (.word (base + BitVec.ofNat 64 cur))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, hi_loc,
    wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  simp

theorem mce_seq_step {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst src cur d : Nat} {p1 p2 : ProgHOL 64} {P : PanSemStateFiniteExact 64 F → Prop}
    (hnone : (evaluateHOLFiniteState s (.seq p1 p2)).1 = none)
    (h1 : (evaluateHOLFiniteState s p1).1 = none →
      sourceBase ≤ dst ∧ dst + (cur + d) ≤ heapEnd ∧
      MemCopyEffect s0 (evaluateHOLFiniteState s p1).2 dst src (cur + d) ∧
      (evaluateHOLFiniteState s p1).2.locals = s.locals)
    (h2 : ∀ m1, m1.locals = s.locals →
      sourceBase ≤ dst ∧ dst + (cur + d) ≤ heapEnd →
      GuestInv m1 → MemCopyEffect s0 m1 dst src (cur + d) →
      (evaluateHOLFiniteState m1 p2).1 = none →
      P (evaluateHOLFiniteState m1 p2).2)
    (hG : GuestInv s) :
    P (evaluateHOLFiniteState s (.seq p1 p2)).2 := by
  have hGmid := guestInv_evaluate s p1 hG
  rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, m1⟩
  simp only [hr1] at hGmid hnone h1 ⊢
  cases r1 with
  | some r1' => simp at hnone
  | none =>
    dsimp only at hnone h1 ⊢
    obtain ⟨hlo, hhi, hm1, hloc⟩ := h1 rfl
    exact h2 m1 hloc ⟨hlo, hhi⟩ hGmid hm1 hnone

theorem mce_assign_i {F : Type} {s0 m1 : PanSemStateFiniteExact 64 F}
    {L0 : HolFiniteMapExact MlS (ValueHOL 64)}
    {dst src n : BitVec 64} {cur stride : Nat}
    (hloc : m1.locals = L0)
    (hdst_loc : L0.lookup (ofString "dst") = some (.val (.word dst)))
    (hsrc_loc : L0.lookup (ofString "src") = some (.val (.word src)))
    (hn_loc : L0.lookup (ofString "n") = some (.val (.word n)))
    (hi_loc : L0.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 cur))))
    (hcur_lt : cur + stride < 2 ^ 64)
    (hd_bounds : sourceBase ≤ dst.toNat ∧ dst.toNat + (cur + stride) ≤ heapEnd)
    (hmce1 : MemCopyEffect s0 m1 dst.toNat src.toNat (cur + stride))
    (hnone : (evaluateHOLFiniteState m1
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 stride)]))).1 = none) :
    let post := (evaluateHOLFiniteState m1
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 stride)]))).2
    sourceBase ≤ dst.toNat ∧ dst.toNat + (cur + stride) ≤ heapEnd ∧
    MemCopyEffect s0 post dst.toNat src.toNat (cur + stride) ∧
    post.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
    post.locals.lookup (ofString "src") = some (.val (.word src)) ∧
    post.locals.lookup (ofString "n") = some (.val (.word n)) ∧
    post.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (cur + stride)))) := by
  dsimp only
  have hi_m1 : m1.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 cur))) := by
    rw [hloc]; exact hi_loc
  have hev : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
      (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 stride)]) =
      some (.val (.word (BitVec.ofNat 64 (cur + stride)))) := by
    simp only [evalHOLExact, evalListHOLExact, hi_m1,
      wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
    congr 3
    apply BitVec.eq_of_toNat_eq
    have hz : BitVec.ofNat 64 stride + (0 : BitVec 64) = BitVec.ofNat 64 stride := by simp
    rw [hz, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [evaluateHOLFiniteState_assign, hev] at hnone ⊢
  dsimp only at hnone ⊢
  have hval_ok : isValidValueHOLFinite m1 .local (ofString "i")
      (.val (.word (BitVec.ofNat 64 (cur + stride)))) = true := by
    simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hi_m1, shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hval_ok]
  dsimp only [setKvarHOLFinite, setVarHOLFinite]
  refine ⟨hd_bounds.1, hd_bounds.2, hmce1.with_locals_clock _ m1.clock, ?_, ?_, ?_, ?_⟩
  · simp [HolFiniteMapExact.lookup_update, FUPDATE, hloc, hdst_loc, show ofString "i" ≠ ofString "dst" by decide]
  · simp [HolFiniteMapExact.lookup_update, FUPDATE, hloc, hsrc_loc, show ofString "i" ≠ ofString "src" by decide]
  · simp [HolFiniteMapExact.lookup_update, FUPDATE, hloc, hn_loc, show ofString "i" ≠ ofString "n" by decide]
  · simp [HolFiniteMapExact.lookup_update, FUPDATE]

theorem mce_while_stride {F : Type} (s0 s : PanSemStateFiniteExact 64 F)
    (dst src n : BitVec 64) (cur stride : Nat)
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hstride_pos : 0 < stride)
    (hcond_eval : ∀ (st : PanSemStateFiniteExact 64 F) (c : Nat),
      c ≤ n.toNat → n.toNat + 32 < 2 ^ 64 →
      st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 c))) →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) cond =
        some (.val (.word (if c + stride ≤ n.toNat then 1 else 0))))
    (hbody_no_ctrl : ∀ (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState st body).1 = none ∨ (evaluateHOLFiniteState st body).1 = some .error)
    (hbody_step : ∀ (st : PanSemStateFiniteExact 64 F) (c : Nat),
      GuestInv st → MemCopyEffect s0 st dst.toNat src.toNat c →
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "src") = some (.val (.word src)) →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 c))) →
      c + stride ≤ n.toNat →
      (c > 0 → sourceBase ≤ dst.toNat ∧ dst.toNat + c ≤ heapEnd) →
      (evaluateHOLFiniteState st body).1 = none →
      let post := (evaluateHOLFiniteState st body).2
      sourceBase ≤ dst.toNat ∧ dst.toNat + (c + stride) ≤ heapEnd ∧
      MemCopyEffect s0 post dst.toNat src.toNat (c + stride) ∧
      post.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      post.locals.lookup (ofString "src") = some (.val (.word src)) ∧
      post.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (c + stride)))))
    (hG : GuestInv s) (hmce : MemCopyEffect s0 s dst.toNat src.toNat cur)
    (hdst_loc : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hsrc_loc : s.locals.lookup (ofString "src") = some (.val (.word src)))
    (hn_loc : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi_loc : s.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 cur))))
    (hcur_le : cur ≤ n.toNat) (hn_lt : n.toNat + 32 < 2 ^ 64)
    (hprev : cur > 0 → sourceBase ≤ dst.toNat ∧ dst.toNat + cur ≤ heapEnd)
    (hnone : (evaluateHOLFiniteState s (.while cond body)).1 = none) :
    let post := (evaluateHOLFiniteState s (.while cond body)).2
    ∃ cur' : Nat,
      cur ≤ cur' ∧ cur' ≤ n.toNat ∧ n.toNat < cur' + stride ∧
      (cur' > 0 → sourceBase ≤ dst.toNat ∧ dst.toNat + cur' ≤ heapEnd) ∧
      MemCopyEffect s0 post dst.toNat src.toNat cur' ∧
      post.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      post.locals.lookup (ofString "src") = some (.val (.word src)) ∧
      post.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 cur'))) := by
  dsimp only
  generalize hk : s.clock = k
  induction k using Nat.strongRecOn generalizing s cur with
  | ind k ih =>
    subst hk
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    have hce : s.evalHOLFinite (h := fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word (if cur + stride ≤ n.toNat then 1 else 0))) :=
      hcond_eval s cur hcur_le hn_lt hi_loc hn_loc
    rw [hce] at hnone ⊢
    dsimp only at hnone ⊢
    by_cases hle : cur + stride ≤ n.toNat
    · rw [if_pos hle] at hnone ⊢
      have hnz1 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos hnz1] at hnone ⊢
      by_cases hclk : s.clock = 0
      · rw [if_pos hclk] at hnone; simp at hnone
      · rw [if_neg hclk] at hnone ⊢
        have hGd : GuestInv (decClockHOLFinite s) := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
        have hmce_d : MemCopyEffect s0 (decClockHOLFinite s) dst.toNat src.toNat cur :=
          hmce.with_locals_clock s.locals (s.clock - 1)
        have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        have hnc := hbody_no_ctrl (decClockHOLFinite s)
        rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, mid⟩
        simp only [hbody] at hrem hnc hnone ⊢
        have hlt_clk : mid.clock < s.clock := by
          change mid.clock ≤ s.clock - 1 at hrem; omega
        rcases hnc with hr0 | hr0
        · rw [hr0] at hnone ⊢
          dsimp only at hnone ⊢
          have hst := hbody_step (decClockHOLFinite s) cur hGd hmce_d hdst_loc hsrc_loc hn_loc hi_loc hle hprev
            (by rw [hbody]; exact hr0)
          rw [hbody] at hst
          obtain ⟨hd_lo, hd_hi, hmce_mid, hdl, hsl, hnl, hil⟩ := hst
          have hG_mid : GuestInv mid := guestInv_evaluate (decClockHOLFinite s) body hGd |> fun h => by rw [hbody] at h; exact h
          obtain ⟨cur', hc1, hc2, hc3, hpr', hmce_end, hdl', hsl', hnl', hil'⟩ :=
            ih mid.clock hlt_clk mid (cur + stride) hG_mid hmce_mid hdl hsl hnl hil
              hle (fun _ => ⟨hd_lo, hd_hi⟩) hnone rfl
          exact ⟨cur', by omega, hc2, hc3, hpr', hmce_end, hdl', hsl', hnl', hil'⟩
        · rw [hr0] at hnone; simp at hnone
    · rw [if_neg hle] at ⊢
      simp only [ne_eq, not_true_eq_false, ↓reduceIte]
      exact ⟨cur, le_rfl, hcur_le, by omega, hprev, hmce, hdst_loc, hsrc_loc, hn_loc, hi_loc⟩

theorem no_ctrl_store {F : Type} (s : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.store d e)).1 = none ∨
    (evaluateHOLFiniteState s (.store d e)).1 = some .error := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

theorem no_ctrl_storeByte {F : Type} (s : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.storeByte d e)).1 = none ∨
    (evaluateHOLFiniteState s (.storeByte d e)).1 = some .error := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

theorem no_ctrl_assign {F : Type} (s : PanSemStateFiniteExact 64 F) (vk : VarKind) (nm : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.assign vk nm e)).1 = none ∨
    (evaluateHOLFiniteState s (.assign vk nm e)).1 = some .error := by
  rw [evaluateHOLFiniteState_assign]
  split
  · exact Or.inr rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem no_ctrl_seq {F : Type} {p1 p2 : ProgHOL 64}
    (h1 : ∀ st : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState st p1).1 = none ∨ (evaluateHOLFiniteState st p1).1 = some .error)
    (h2 : ∀ st : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState st p2).1 = none ∨ (evaluateHOLFiniteState st p2).1 = some .error)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.seq p1 p2)).1 = none ∨
    (evaluateHOLFiniteState s (.seq p1 p2)).1 = some .error := by
  rw [evaluateHOLFiniteState_seq_line780]
  have hc1 := h1 s
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, m1⟩
  rw [hr1] at hc1
  rcases hc1 with hr | hr
  · subst hr; exact h2 m1
  · subst hr; exact Or.inr rfl

theorem eval_cond_notLower {F : Type} (stride : Nat) (hstride : stride ≤ 32)
    (st : PanSemStateFiniteExact 64 F) (n : BitVec 64) (c : Nat)
    (hc : c ≤ n.toNat) (hn_lt : n.toNat + 32 < 2 ^ 64)
    (hi_loc : st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 c))))
    (hn_loc : st.locals.lookup (ofString "n") = some (.val (.word n))) :
    @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 stride)])) =
      some (.val (.word (if c + stride ≤ n.toNat then 1 else 0))) := by
  simp only [evalHOLExact, evalListHOLExact, hi_loc, hn_loc,
    wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
  have hz : BitVec.ofNat 64 stride + (0 : BitVec 64) = BitVec.ofNat 64 stride := by simp
  rw [hz]
  have hadd_nat : (BitVec.ofNat 64 c + BitVec.ofNat 64 stride).toNat = c + stride := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hadd_nat]
  by_cases hle : c + stride ≤ n.toNat
  · have hnlt : ¬ n.toNat < c + stride := by omega
    simp [hle, hnlt]
  · have hlt : n.toNat < c + stride := by omega
    simp [hle, hlt]

theorem eval_cond_lower1 {F : Type}
    (st : PanSemStateFiniteExact 64 F) (n : BitVec 64) (c : Nat)
    (hc : c ≤ n.toNat) (hn_lt : n.toNat + 32 < 2 ^ 64)
    (hi_loc : st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 c))))
    (hn_loc : st.locals.lookup (ofString "n") = some (.val (.word n))) :
    @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
      some (.val (.word (if c + 1 ≤ n.toNat then 1 else 0))) := by
  simp only [evalHOLExact, hi_loc, hn_loc,
    Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
  have hc_nat : (BitVec.ofNat 64 c).toNat = c := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [hc_nat]
  by_cases hle : c + 1 ≤ n.toNat
  · have hlt : c < n.toNat := by omega
    simp [hle, hlt]
  · have hnlt : ¬ c < n.toNat := by omega
    simp [hle, hnlt]

theorem not_returned_while {F : Type} {cond : ExpHOL 64} {body : ProgHOL 64}
    (hb : ∀ st : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState st body).1 = none ∨ (evaluateHOLFiniteState st body).1 = some .error)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.while cond body)).1 ≠ some (.returned v) := by
  generalize hk : s.clock = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    subst hk
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    split
    · split
      · split
        · simp
        · have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hc := hb (decClockHOLFinite s)
          rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, mid⟩
          simp only [hbody] at hrem hc ⊢
          have hlt : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at hrem; omega
          rcases hc with hr | hr
          · rw [hr]; exact ih mid.clock hlt mid rfl
          · rw [hr]; simp
      · simp
    · simp

theorem not_returned_seq {F : Type} {p1 p2 : ProgHOL 64}
    (h1 : ∀ (st : PanSemStateFiniteExact 64 F) v, (evaluateHOLFiniteState st p1).1 ≠ some (.returned v))
    (h2 : ∀ (st : PanSemStateFiniteExact 64 F) v, (evaluateHOLFiniteState st p2).1 ≠ some (.returned v))
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_seq_line780]
  have hc1 := h1 s v
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, m1⟩
  rw [hr1] at hc1
  cases r1 with
  | none => exact h2 m1 v
  | some r1' => dsimp only; exact hc1

theorem not_returned_ite {F : Type} {cond : ExpHOL 64} {p1 p2 : ProgHOL 64}
    (h1 : ∀ (st : PanSemStateFiniteExact 64 F) v, (evaluateHOLFiniteState st p1).1 ≠ some (.returned v))
    (h2 : ∀ (st : PanSemStateFiniteExact 64 F) v, (evaluateHOLFiniteState st p2).1 ≠ some (.returned v))
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.ite cond p1 p2)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact h2 s v
    · exact h1 s v
  · simp

theorem seq_returned_inv {F : Type} {s : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64}
    {v : ValueHOL 64} {post : PanSemStateFiniteExact 64 F}
    (hno1 : ∀ (st : PanSemStateFiniteExact 64 F) u, (evaluateHOLFiniteState st p1).1 ≠ some (.returned u))
    (hrun : evaluateHOLFiniteState s (.seq p1 p2) = (some (.returned v), post)) :
    (evaluateHOLFiniteState s p1).1 = none ∧
    evaluateHOLFiniteState (evaluateHOLFiniteState s p1).2 p2 = (some (.returned v), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  have hc1 := hno1 s v
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, m1⟩
  simp only [hr1] at hrun hc1 ⊢
  cases r1 with
  | none => exact ⟨rfl, hrun⟩
  | some r1' => dsimp only at hrun; injection hrun with hr _; exact absurd hr hc1

private def memcpy_w32_body : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
         (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
    (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 8])))
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 16])))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 24])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32])))))

private def memcpy_w8_body : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
         (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))

private def memcpy_b8_body : ProgHOL 64 :=
  .seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
         (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 1])))
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 2])))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 3])))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 4])))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5])
                    (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 5])))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6])
                      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 6])))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7])
                        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 7])))
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))))))))

private def memcpy_b1_body : ProgHOL 64 :=
  .seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
         (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))

private theorem no_ctrl_w32 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s memcpy_w32_body).1 = none ∨
    (evaluateHOLFiniteState s memcpy_w32_body).1 = some .error :=
  no_ctrl_seq (fun st => no_ctrl_store st _ _)
    (fun st => no_ctrl_seq (fun st => no_ctrl_store st _ _)
      (fun st => no_ctrl_seq (fun st => no_ctrl_store st _ _)
        (fun st => no_ctrl_seq (fun st => no_ctrl_store st _ _)
          (fun st => no_ctrl_assign st _ _ _) st) st) st) s

private theorem no_ctrl_w8 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s memcpy_w8_body).1 = none ∨
    (evaluateHOLFiniteState s memcpy_w8_body).1 = some .error :=
  no_ctrl_seq (fun st => no_ctrl_store st _ _) (fun st => no_ctrl_assign st _ _ _) s

private theorem no_ctrl_b8 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s memcpy_b8_body).1 = none ∨
    (evaluateHOLFiniteState s memcpy_b8_body).1 = some .error :=
  no_ctrl_seq (fun st => no_ctrl_storeByte st _ _)
    (fun st => no_ctrl_seq (fun st => no_ctrl_storeByte st _ _)
      (fun st => no_ctrl_seq (fun st => no_ctrl_storeByte st _ _)
        (fun st => no_ctrl_seq (fun st => no_ctrl_storeByte st _ _)
          (fun st => no_ctrl_seq (fun st => no_ctrl_storeByte st _ _)
            (fun st => no_ctrl_seq (fun st => no_ctrl_storeByte st _ _)
              (fun st => no_ctrl_seq (fun st => no_ctrl_storeByte st _ _)
                (fun st => no_ctrl_seq (fun st => no_ctrl_storeByte st _ _)
                  (fun st => no_ctrl_assign st _ _ _) st) st) st) st) st) st) st) s

private theorem no_ctrl_b1 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s memcpy_b1_body).1 = none ∨
    (evaluateHOLFiniteState s memcpy_b1_body).1 = some .error :=
  no_ctrl_seq (fun st => no_ctrl_storeByte st _ _) (fun st => no_ctrl_assign st _ _ _) s

private def McePost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst src n : BitVec 64)
    (endCur : Nat) (post : PanSemStateFiniteExact 64 F) : Prop :=
  sourceBase ≤ dst.toNat ∧ dst.toNat + endCur ≤ heapEnd ∧
  MemCopyEffect s0 post dst.toNat src.toNat endCur ∧
  post.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
  post.locals.lookup (ofString "src") = some (.val (.word src)) ∧
  post.locals.lookup (ofString "n") = some (.val (.word n)) ∧
  post.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 endCur)))

private theorem step_w32 {F : Type} (s0 st : PanSemStateFiniteExact 64 F)
    (dst src n : BitVec 64) (c : Nat)
    (hn_lt : n.toNat + 32 < 2 ^ 64)
    (hdisj : Disj (dst.toNat, n.toNat) (src.toNat, n.toNat))
    (hsrc_lt : src.toNat + n.toNat ≤ 2 ^ 64)
    (hG : GuestInv st) (hmce : MemCopyEffect s0 st dst.toNat src.toNat c)
    (hdst_loc : st.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hsrc_loc : st.locals.lookup (ofString "src") = some (.val (.word src)))
    (hn_loc : st.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi_loc : st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 c))))
    (hle : c + 32 ≤ n.toNat)
    (hprev : c > 0 → sourceBase ≤ dst.toNat ∧ dst.toNat + c ≤ heapEnd)
    (hnone : (evaluateHOLFiniteState st memcpy_w32_body).1 = none) :
    McePost s0 dst src n (c + 32) (evaluateHOLFiniteState st memcpy_w32_body).2 := by
  dsimp only [memcpy_w32_body] at hnone ⊢
  refine mce_seq_step (d := 8) (P := McePost s0 dst src n (c + 32)) hnone
    (fun hn0 => store_word_copy_step hG hmce (by unfold Disj at hdisj ⊢; omega) (by omega) _ _
      (eval_dst_src_i_0 st "dst" dst c hdst_loc hi_loc)
      (eval_dst_src_i_0 st "src" src c hsrc_loc hi_loc) hprev hn0) ?_ hG
  intro m1 hl1 hb1 hGm1 hmce1 hn1
  refine mce_seq_step (d := 8) (P := McePost s0 dst src n (c + 32)) hn1
    (fun hn0 => store_word_copy_step hGm1 hmce1 (by unfold Disj at hdisj ⊢; omega) (by omega) _ _
      (eval_dst_src_i_off m1 "dst" dst c 8 (by omega) (hl1 ▸ hdst_loc) (hl1 ▸ hi_loc))
      (eval_dst_src_i_off m1 "src" src c 8 (by omega) (hl1 ▸ hsrc_loc) (hl1 ▸ hi_loc))
      (fun _ => hb1) hn0) ?_ hGm1
  intro m2 hl2 hb2 hGm2 hmce2 hn2
  have hl2' : m2.locals = st.locals := hl2.trans hl1
  refine mce_seq_step (d := 8) (P := McePost s0 dst src n (c + 32)) hn2
    (fun hn0 => store_word_copy_step hGm2 hmce2 (by unfold Disj at hdisj ⊢; omega) (by omega) _ _
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m2 "dst" dst c 16 (by omega) (hl2' ▸ hdst_loc) (hl2' ▸ hi_loc))
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m2 "src" src c 16 (by omega) (hl2' ▸ hsrc_loc) (hl2' ▸ hi_loc))
      (fun _ => hb2) hn0) ?_ hGm2
  intro m3 hl3 hb3 hGm3 hmce3 hn3
  have hl3' : m3.locals = st.locals := hl3.trans hl2'
  refine mce_seq_step (d := 8) (P := McePost s0 dst src n (c + 32)) hn3
    (fun hn0 => store_word_copy_step hGm3 hmce3 (by unfold Disj at hdisj ⊢; omega) (by omega) _ _
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m3 "dst" dst c 24 (by omega) (hl3' ▸ hdst_loc) (hl3' ▸ hi_loc))
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m3 "src" src c 24 (by omega) (hl3' ▸ hsrc_loc) (hl3' ▸ hi_loc))
      (fun _ => hb3) hn0) ?_ hGm3
  intro m4 hl4 hb4 _ hmce4 hn4
  have h32 : c + 8 + 8 + 8 + 8 = c + 32 := by omega
  rw [h32] at hb4 hmce4
  exact mce_assign_i (hl4.trans hl3') hdst_loc hsrc_loc hn_loc hi_loc (by omega) hb4 hmce4 hn4

private theorem step_w8 {F : Type} (s0 st : PanSemStateFiniteExact 64 F)
    (dst src n : BitVec 64) (c : Nat)
    (hn_lt : n.toNat + 32 < 2 ^ 64)
    (hdisj : Disj (dst.toNat, n.toNat) (src.toNat, n.toNat))
    (hsrc_lt : src.toNat + n.toNat ≤ 2 ^ 64)
    (hG : GuestInv st) (hmce : MemCopyEffect s0 st dst.toNat src.toNat c)
    (hdst_loc : st.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hsrc_loc : st.locals.lookup (ofString "src") = some (.val (.word src)))
    (hn_loc : st.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi_loc : st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 c))))
    (hle : c + 8 ≤ n.toNat)
    (hprev : c > 0 → sourceBase ≤ dst.toNat ∧ dst.toNat + c ≤ heapEnd)
    (hnone : (evaluateHOLFiniteState st memcpy_w8_body).1 = none) :
    McePost s0 dst src n (c + 8) (evaluateHOLFiniteState st memcpy_w8_body).2 := by
  dsimp only [memcpy_w8_body] at hnone ⊢
  refine mce_seq_step (d := 8) (P := McePost s0 dst src n (c + 8)) hnone
    (fun hn0 => store_word_copy_step hG hmce (by unfold Disj at hdisj ⊢; omega) (by omega) _ _
      (eval_dst_src_i_0 st "dst" dst c hdst_loc hi_loc)
      (eval_dst_src_i_0 st "src" src c hsrc_loc hi_loc) hprev hn0) ?_ hG
  intro m1 hl1 hb1 _ hmce1 hn1
  exact mce_assign_i hl1 hdst_loc hsrc_loc hn_loc hi_loc (by omega) hb1 hmce1 hn1

private theorem step_b8 {F : Type} (s0 st : PanSemStateFiniteExact 64 F)
    (dst src n : BitVec 64) (c : Nat)
    (hdst_al : dst.toNat % 8 = 0 ∨ sourceBase ≤ dst.toNat)
    (hn_lt : n.toNat + 32 < 2 ^ 64)
    (hdisj : Disj (dst.toNat, n.toNat) (src.toNat, n.toNat))
    (hsrc_lt : src.toNat + n.toNat ≤ 2 ^ 64)
    (hG : GuestInv st) (hmce : MemCopyEffect s0 st dst.toNat src.toNat c)
    (hdst_loc : st.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hsrc_loc : st.locals.lookup (ofString "src") = some (.val (.word src)))
    (hn_loc : st.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi_loc : st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 c))))
    (hle : c + 8 ≤ n.toNat)
    (hprev : c > 0 → sourceBase ≤ dst.toNat ∧ dst.toNat + c ≤ heapEnd)
    (hnone : (evaluateHOLFiniteState st memcpy_b8_body).1 = none) :
    McePost s0 dst src n (c + 8) (evaluateHOLFiniteState st memcpy_b8_body).2 := by
  dsimp only [memcpy_b8_body] at hnone ⊢
  refine mce_seq_step (d := 1) (P := McePost s0 dst src n (c + 8)) hnone
    (fun hn0 => storeByte_copy_step hG hmce (by unfold Disj at hdisj ⊢; omega) (by omega)
      (fun _ => hdst_al) _ _
      (eval_dst_src_i_0 st "dst" dst c hdst_loc hi_loc)
      (eval_dst_src_i_0 st "src" src c hsrc_loc hi_loc) hprev hn0) ?_ hG
  intro m1 hl1 hb1 hGm1 hmce1 hn1
  refine mce_seq_step (d := 1) (P := McePost s0 dst src n (c + 8)) hn1
    (fun hn0 => storeByte_copy_step hGm1 hmce1 (by unfold Disj at hdisj ⊢; omega) (by omega)
      (fun h => by omega) _ _
      (eval_dst_src_i_off m1 "dst" dst c 1 (by omega) (hl1 ▸ hdst_loc) (hl1 ▸ hi_loc))
      (eval_dst_src_i_off m1 "src" src c 1 (by omega) (hl1 ▸ hsrc_loc) (hl1 ▸ hi_loc))
      (fun _ => hb1) hn0) ?_ hGm1
  intro m2 hl2 hb2 hGm2 hmce2 hn2
  have hl2' := hl2.trans hl1
  refine mce_seq_step (d := 1) (P := McePost s0 dst src n (c + 8)) hn2
    (fun hn0 => storeByte_copy_step hGm2 hmce2 (by unfold Disj at hdisj ⊢; omega) (by omega)
      (fun h => by omega) _ _
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m2 "dst" dst c 2 (by omega) (hl2' ▸ hdst_loc) (hl2' ▸ hi_loc))
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m2 "src" src c 2 (by omega) (hl2' ▸ hsrc_loc) (hl2' ▸ hi_loc))
      (fun _ => hb2) hn0) ?_ hGm2
  intro m3 hl3 hb3 hGm3 hmce3 hn3
  have hl3' := hl3.trans hl2'
  refine mce_seq_step (d := 1) (P := McePost s0 dst src n (c + 8)) hn3
    (fun hn0 => storeByte_copy_step hGm3 hmce3 (by unfold Disj at hdisj ⊢; omega) (by omega)
      (fun h => by omega) _ _
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m3 "dst" dst c 3 (by omega) (hl3' ▸ hdst_loc) (hl3' ▸ hi_loc))
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m3 "src" src c 3 (by omega) (hl3' ▸ hsrc_loc) (hl3' ▸ hi_loc))
      (fun _ => hb3) hn0) ?_ hGm3
  intro m4 hl4 hb4 hGm4 hmce4 hn4
  have hl4' := hl4.trans hl3'
  refine mce_seq_step (d := 1) (P := McePost s0 dst src n (c + 8)) hn4
    (fun hn0 => storeByte_copy_step hGm4 hmce4 (by unfold Disj at hdisj ⊢; omega) (by omega)
      (fun h => by omega) _ _
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m4 "dst" dst c 4 (by omega) (hl4' ▸ hdst_loc) (hl4' ▸ hi_loc))
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m4 "src" src c 4 (by omega) (hl4' ▸ hsrc_loc) (hl4' ▸ hi_loc))
      (fun _ => hb4) hn0) ?_ hGm4
  intro m5 hl5 hb5 hGm5 hmce5 hn5
  have hl5' := hl5.trans hl4'
  refine mce_seq_step (d := 1) (P := McePost s0 dst src n (c + 8)) hn5
    (fun hn0 => storeByte_copy_step hGm5 hmce5 (by unfold Disj at hdisj ⊢; omega) (by omega)
      (fun h => by omega) _ _
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m5 "dst" dst c 5 (by omega) (hl5' ▸ hdst_loc) (hl5' ▸ hi_loc))
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m5 "src" src c 5 (by omega) (hl5' ▸ hsrc_loc) (hl5' ▸ hi_loc))
      (fun _ => hb5) hn0) ?_ hGm5
  intro m6 hl6 hb6 hGm6 hmce6 hn6
  have hl6' := hl6.trans hl5'
  refine mce_seq_step (d := 1) (P := McePost s0 dst src n (c + 8)) hn6
    (fun hn0 => storeByte_copy_step hGm6 hmce6 (by unfold Disj at hdisj ⊢; omega) (by omega)
      (fun h => by omega) _ _
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m6 "dst" dst c 6 (by omega) (hl6' ▸ hdst_loc) (hl6' ▸ hi_loc))
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m6 "src" src c 6 (by omega) (hl6' ▸ hsrc_loc) (hl6' ▸ hi_loc))
      (fun _ => hb6) hn0) ?_ hGm6
  intro m7 hl7 hb7 hGm7 hmce7 hn7
  have hl7' := hl7.trans hl6'
  refine mce_seq_step (d := 1) (P := McePost s0 dst src n (c + 8)) hn7
    (fun hn0 => storeByte_copy_step hGm7 hmce7 (by unfold Disj at hdisj ⊢; omega) (by omega)
      (fun h => by omega) _ _
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m7 "dst" dst c 7 (by omega) (hl7' ▸ hdst_loc) (hl7' ▸ hi_loc))
      (by simpa [Nat.add_assoc] using eval_dst_src_i_off m7 "src" src c 7 (by omega) (hl7' ▸ hsrc_loc) (hl7' ▸ hi_loc))
      (fun _ => hb7) hn0) ?_ hGm7
  intro m8 hl8 hb8 _ hmce8 hn8
  have h8 : c + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = c + 8 := by omega
  rw [h8] at hb8 hmce8
  exact mce_assign_i (hl8.trans hl7') hdst_loc hsrc_loc hn_loc hi_loc (by omega) hb8 hmce8 hn8

private theorem step_b1 {F : Type} (s0 st : PanSemStateFiniteExact 64 F)
    (dst src n : BitVec 64) (c : Nat)
    (hdst_al : dst.toNat % 8 = 0 ∨ sourceBase ≤ dst.toNat)
    (hn_lt : n.toNat + 32 < 2 ^ 64)
    (hdisj : Disj (dst.toNat, n.toNat) (src.toNat, n.toNat))
    (hsrc_lt : src.toNat + n.toNat ≤ 2 ^ 64)
    (hG : GuestInv st) (hmce : MemCopyEffect s0 st dst.toNat src.toNat c)
    (hdst_loc : st.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hsrc_loc : st.locals.lookup (ofString "src") = some (.val (.word src)))
    (hn_loc : st.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi_loc : st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 c))))
    (hle : c + 1 ≤ n.toNat)
    (hprev : c > 0 → sourceBase ≤ dst.toNat ∧ dst.toNat + c ≤ heapEnd)
    (hnone : (evaluateHOLFiniteState st memcpy_b1_body).1 = none) :
    McePost s0 dst src n (c + 1) (evaluateHOLFiniteState st memcpy_b1_body).2 := by
  dsimp only [memcpy_b1_body] at hnone ⊢
  refine mce_seq_step (d := 1) (P := McePost s0 dst src n (c + 1)) hnone
    (fun hn0 => storeByte_copy_step hG hmce (by unfold Disj at hdisj ⊢; omega) (by omega)
      (fun _ => hdst_al) _ _
      (eval_dst_src_i_0 st "dst" dst c hdst_loc hi_loc)
      (eval_dst_src_i_0 st "src" src c hsrc_loc hi_loc) hprev hn0) ?_ hG
  intro m1 hl1 hb1 _ hmce1 hn1
  exact mce_assign_i hl1 hdst_loc hsrc_loc hn_loc hi_loc (by omega) hb1 hmce1 hn1

theorem memcpy_body_effect {F : Type} (state : PanSemStateFiniteExact 64 F)
    (dst src n : BitVec 64)
    (hG : GuestInv state)
    (hdst_al : dst.toNat % 8 = 0 ∨ sourceBase ≤ dst.toNat)
    (hdisj : Disj (dst.toNat, n.toNat) (src.toNat, n.toNat))
    (hsrc_lt : src.toNat + n.toNat ≤ 2 ^ 64)
    (hn_lt : n.toNat + 32 < 2 ^ 64)
    (hdst_loc : state.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hsrc_loc : state.locals.lookup (ofString "src") = some (.val (.word src)))
    (hn_loc : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_memcpy) =
      (some (.returned v), post)) :
    v = .val (.word 0) ∧
    (n.toNat > 0 → sourceBase ≤ dst.toNat ∧ dst.toNat + n.toNat ≤ heapEnd) ∧
    MemCopyEffect state post dst.toNat src.toNat n.toNat := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  dsimp only at hrun
  have hev0 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
  rw [hev0] at hrun
  dsimp only at hrun
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hrun
  set s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  let restProg : ProgHOL 64 :=
    .seq (.ite (.cmp .equal (.op .and [.op .or [.var .local (ofString "dst"), .var .local (ofString "src")], .const 7]) (.const 0))
          (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) memcpy_w32_body)
                (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) memcpy_w8_body))
          .skip)
      (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) memcpy_b8_body)
        (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) memcpy_b1_body)
          (.return (.const 0))))
  have hrun_rest : (evaluateHOLFiniteState s0 restProg).1 = some (.returned v) ∧
      { (evaluateHOLFiniteState s0 restProg).2 with
        locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s0 restProg).2.locals
          (ofString "i", state.locals.lookup (ofString "i")) } = post := by
    injection hrun with h1 h2
    exact ⟨h1, h2⟩
  rcases hr_all : evaluateHOLFiniteState s0 restProg with ⟨r_all, post_i⟩
  rw [hr_all] at hrun_rest
  obtain ⟨hr_eq, hpost_eq⟩ := hrun_rest
  dsimp only at hr_eq hpost_eq
  subst hr_eq hpost_eq
  dsimp only [restProg] at hr_all
  have hG0 : GuestInv s0 := guestInv_setVar _ _ state hG
  have hmce0 : MemCopyEffect state s0 dst.toNat src.toNat 0 :=
    (MemCopyEffect.refl_zero state dst.toNat src.toNat).with_locals_clock s0.locals state.clock
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 0))) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_dst : s0.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst_loc,
      show ofString "i" ≠ ofString "dst" by decide]
  have hs0_src : s0.locals.lookup (ofString "src") = some (.val (.word src)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsrc_loc,
      show ofString "i" ≠ ofString "src" by decide]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_loc,
      show ofString "i" ≠ ofString "n" by decide]
  have hno_ite : ∀ (st : PanSemStateFiniteExact 64 F) u,
      (evaluateHOLFiniteState st
        (.ite (.cmp .equal (.op .and [.op .or [.var .local (ofString "dst"), .var .local (ofString "src")], .const 7]) (.const 0))
          (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) memcpy_w32_body)
                (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) memcpy_w8_body))
          .skip)).1 ≠ some (.returned u) :=
    not_returned_ite
      (not_returned_seq (not_returned_while no_ctrl_w32) (not_returned_while no_ctrl_w8))
      (fun st u => by simp [evaluateHOLFiniteState_skip])
  obtain ⟨hn_ite, hrun1⟩ := seq_returned_inv hno_ite hr_all
  set s1 := (evaluateHOLFiniteState s0
    (.ite (.cmp .equal (.op .and [.op .or [.var .local (ofString "dst"), .var .local (ofString "src")], .const 7]) (.const 0))
      (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) memcpy_w32_body)
            (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) memcpy_w8_body))
      .skip)).2
  have hs1_inv : ∃ cur1 : Nat,
      cur1 ≤ n.toNat ∧
      (cur1 > 0 → sourceBase ≤ dst.toNat ∧ dst.toNat + cur1 ≤ heapEnd) ∧
      GuestInv s1 ∧ MemCopyEffect state s1 dst.toNat src.toNat cur1 ∧
      s1.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      s1.locals.lookup (ofString "src") = some (.val (.word src)) ∧
      s1.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      s1.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 cur1))) := by
    have hGs1 : GuestInv s1 := guestInv_evaluate s0 _ hG0
    dsimp only [s1] at hn_ite hGs1 ⊢
    rw [evaluateHOLFiniteState_ite] at hn_ite hGs1 ⊢
    revert hn_ite hGs1
    split
    · split
      · simp only [evaluateHOLFiniteState_skip]
        intro _ _
        exact ⟨0, by omega, fun h => by omega, hG0, hmce0, hs0_dst, hs0_src, hs0_n, hs0_i⟩
      · rw [evaluateHOLFiniteState_seq_line780]
        rcases hw1 : evaluateHOLFiniteState s0
          (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) memcpy_w32_body) with ⟨rw1, sw1⟩
        cases rw1 with
        | some rw1' => simp
        | none =>
          dsimp only
          intro hn_w2 hGs1
          have hGsw1 : GuestInv sw1 := guestInv_evaluate s0 _ hG0 |> fun h => by rw [hw1] at h; exact h
          obtain ⟨c1, _, hc1_le, _, hpr1, hmce1, hdl1, hsl1, hnl1, hil1⟩ :=
            mce_while_stride state s0 dst src n 0 32
              (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32]))
              memcpy_w32_body (by decide)
              (fun st c hc hlt hi hn => eval_cond_notLower 32 (by decide) st n c hc hlt hi hn)
              no_ctrl_w32
              (fun st c => step_w32 state st dst src n c hn_lt hdisj hsrc_lt)
              hG0 hmce0 hs0_dst hs0_src hs0_n hs0_i (by omega) hn_lt (fun h => by omega)
              (by rw [hw1])
          rw [hw1] at hmce1 hdl1 hsl1 hnl1 hil1
          dsimp only at hmce1 hdl1 hsl1 hnl1 hil1
          obtain ⟨c2, _, hc2_le, _, hpr2, hmce2, hdl2, hsl2, hnl2, hil2⟩ :=
            mce_while_stride state sw1 dst src n c1 8
              (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8]))
              memcpy_w8_body (by decide)
              (fun st c hc hlt hi hn => eval_cond_notLower 8 (by decide) st n c hc hlt hi hn)
              no_ctrl_w8
              (fun st c => step_w8 state st dst src n c hn_lt hdisj hsrc_lt)
              hGsw1 hmce1 hdl1 hsl1 hnl1 hil1 hc1_le hn_lt hpr1 hn_w2
          exact ⟨c2, hc2_le, hpr2, hGs1, hmce2, hdl2, hsl2, hnl2, hil2⟩
    · simp
  obtain ⟨cur1, hc1_le, hpr1, hGs1, hmce1, hdl1, hsl1, hnl1, hil1⟩ := hs1_inv
  obtain ⟨hn_b8, hrun2⟩ := seq_returned_inv (not_returned_while no_ctrl_b8) hrun1
  set s2 := (evaluateHOLFiniteState s1
    (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) memcpy_b8_body)).2
  have hGs2 : GuestInv s2 := guestInv_evaluate s1 _ hGs1
  obtain ⟨cur2, _, hc2_le, _, hpr2, hmce2, hdl2, hsl2, hnl2, hil2⟩ :=
    mce_while_stride state s1 dst src n cur1 8
      (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8]))
      memcpy_b8_body (by decide)
      (fun st c hc hlt hi hn => eval_cond_notLower 8 (by decide) st n c hc hlt hi hn)
      no_ctrl_b8
      (fun st c => step_b8 state st dst src n c hdst_al hn_lt hdisj hsrc_lt)
      hGs1 hmce1 hdl1 hsl1 hnl1 hil1 hc1_le hn_lt hpr1 hn_b8
  obtain ⟨hn_b1, hrun3⟩ := seq_returned_inv (not_returned_while no_ctrl_b1) hrun2
  set s3 := (evaluateHOLFiniteState s2
    (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) memcpy_b1_body)).2
  obtain ⟨cur3, _, hc3_le, hc3_gt, hpr3, hmce3, _, _, _, _⟩ :=
    mce_while_stride state s2 dst src n cur2 1
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
      memcpy_b1_body (by decide)
      (fun st c hc hlt hi hn => eval_cond_lower1 st n c hc hlt hi hn)
      no_ctrl_b1
      (fun st c => step_b1 state st dst src n c hdst_al hn_lt hdisj hsrc_lt)
      hGs2 hmce2 hdl2 hsl2 hnl2 hil2 hc2_le hn_lt hpr2 hn_b1
  have hcur3_eq : cur3 = n.toNat := by omega
  subst hcur3_eq
  rw [evaluateHOLFiniteState_return] at hrun3
  have hev_ret : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.const 0) = some (.val (.word 0)) := rfl
  rw [hev_ret] at hrun3
  dsimp only at hrun3
  have hle32 : sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
    simp [sizeOfShapeWithContextHOL, shapeOfHOLExact]
  rw [if_pos hle32] at hrun3
  injection hrun3 with hv_eq hpost_i_eq
  injection hv_eq with hv_eq'
  injection hv_eq' with hv_eq''
  subst hv_eq'' hpost_i_eq
  exact ⟨rfl, hpr3, (hmce3.with_locals_clock _ _).with_locals_clock _ _⟩

/-! ## 7. `NodeHeap` preservation & extension lemmas for MPT node constructors -/

theorem memB_eq_of_frameOutside {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh : Ivl} (hbe : post.be = s.be)
    (hfr : FrameOutside s post keep fresh) (a : Nat) (ha_lt : a < 2 ^ 64)
    (hk : ∀ i ∈ keep, ¬ CellHits (a / 8 * 8) i)
    (hf : ¬ CellHits (a / 8 * 8) fresh) :
    memB post a = memB s a := by
  have hal_nat : (panByteAlignHOL (BitVec.ofNat 64 a)).toNat = a / 8 * 8 := by
    rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hmem := hfr (panByteAlignHOL (BitVec.ofNat 64 a))
    (fun i hi => by rw [hal_nat]; exact hk i hi)
    (by rw [hal_nat]; exact hf)
  unfold memB
  rw [hmem, hbe]

theorem not_cellHits_align_of_disj {p len a : Nat} (hk : a < len)
    (i : Ivl) (halign : i.1 % 8 = 0 ∧ i.2 % 8 = 0)
    (hdisj : Disj (p, len) i) :
    ¬ CellHits ((p + a) / 8 * 8) i := by
  unfold CellHits
  unfold Disj at hdisj
  omega

theorem keyIn_mono_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} {p len : Nat}
    {keep : List Ivl} {fresh : Ivl}
    (hbe : post.be = s.be)
    (hfr : FrameOutside s post keep fresh)
    (hkey : KeyIn s Nd p len)
    (hgrows : AllocatorGrows s post)
    (hkeep_disj : len > 0 → ∀ i ∈ keep, i.1 % 8 = 0 ∧ i.2 % 8 = 0 ∧ Disj (p, len) i)
    (hfresh_disj : len > 0 → fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0 ∧ Disj (p, len) fresh)
    (hNd'_sub : ∀ n ∈ Nd',
      (n ∈ Nd ∧ nodeIvl post n = nodeIvl s n) ∨
      Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr"))
    (hA_s : ArenaOK s) :
    KeyIn post Nd' p len := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hse_lt : scratchEnd < 2 ^ 64 := by decide
  rcases hkey with rfl | ⟨hnib, halloc, hins, hdisj_Nd⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨?_, hgrows.allocated halloc, hins, ?_⟩
    · intro k hk
      have hpos : len > 0 := by omega
      have hpa_lt : p + k < 2 ^ 64 := by unfold Inside at hins; omega
      have heq := memB_eq_of_frameOutside hbe hfr (p + k) hpa_lt
        (fun i hi => by
          obtain ⟨h1, h2, hd⟩ := hkeep_disj hpos i hi
          exact not_cellHits_align_of_disj hk i ⟨h1, h2⟩ hd)
        (by
          obtain ⟨h1, h2, hd⟩ := hfresh_disj hpos
          exact not_cellHits_align_of_disj hk fresh ⟨h1, h2⟩ hd)
      rw [heq]
      exact hnib k hk
    · intro n hn
      rcases hNd'_sub n hn with ⟨hn_old, hivl_eq⟩ | hnew_in
      · rw [hivl_eq]; exact hdisj_Nd n hn_old
      · rcases halloc with hheap | hscr
        · unfold Disj Inside at *; omega
        · have h1 := hA_s.2.1
          have h2 := hA_s.2.2.1
          have h3 := hA_s.2.2.2.1
          have hsl : heapLimit ≤ scratchStart := by decide
          -- Wait: `hins : Inside (p, len) sourceBase heapLimit`, while `hscr : Inside (p, len) (globN s "scratch_ptr") scratchEnd`!
          -- If `len = 0`, `Disj` is `Or.inl rfl`; if `len > 0`, `hscr` contradicts `hins`!
          by_cases hlz : len = 0
          · exact Or.inl hlz
          · unfold Inside at hins hscr; omega

theorem wordsOK_of_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hma : post.memaddrs = s.memaddrs) (i : Ivl) (hw : WordsOK s i) :
    WordsOK post i := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨w, hdom, _⟩ := hw.2.2 k hk
  cases hm : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with
  | word w' => exact ⟨w', hma ▸ hdom, hm⟩

theorem wordsOK_ordinary_range {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hG : GuestInv s) (p sz : Nat)
    (hal1 : p % 8 = 0) (hal2 : sz % 8 = 0)
    (hlo : sourceBase ≤ p) (hhi : p + sz ≤ heapLimit) :
    WordsOK s (p, sz) := by
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhe_lt : heapEnd < 2 ^ 64 := by decide
  refine ⟨hal1, hal2, fun k hk => ?_⟩
  dsimp only
  cases hm : s.memory (BitVec.ofNat 64 (p + 8 * k)) with
  | word w =>
    refine ⟨w, ?_, hm⟩
    rw [hG.memaddrs, ordinaryDomain_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, by omega, by omega⟩

theorem memW_eq_of_frameOutside {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh : Ivl}
    (hfr : FrameOutside s post keep fresh) (a : Nat) (ha_lt : a < 2 ^ 64)
    (hk : ∀ i ∈ keep, ¬ CellHits a i) (hf : ¬ CellHits a fresh) :
    memW post a = memW s a := by
  have hnat : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hm := hfr (BitVec.ofNat 64 a)
    (fun i hi => by rw [hnat]; exact hk i hi)
    (by rw [hnat]; exact hf)
  unfold memW; rw [hm]

theorem not_cellHits_of_disj_word {a : Nat} {j : Ivl}
    (hd : Disj (a, 8) j) (hj_pos : 0 < j.2) : ¬ CellHits a j := by
  intro ⟨h1, h2⟩
  rcases hd with h | h | h | h
  · cases h
  · change j.2 = 0 at h; omega
  · change a + 8 ≤ j.1 at h; omega
  · change j.1 + j.2 ≤ a at h; omega

theorem nodeSize_mod8 (k : Nat) : nodeSize k % 8 = 0 := by
  unfold nodeSize
  split <;> [decide; (split <;> [decide; (split <;> decide)])]

theorem nodeSize_pos (k : Nat) : 32 ≤ nodeSize k ∧ nodeSize k ≤ 176 := by
  unfold nodeSize
  split <;> [decide; (split <;> [decide; (split <;> decide)])]

theorem nodeIvl_in_heap {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hNH : NodeHeap s Nd) {n : Nat} (hn : n ∈ Nd) (hA : ArenaOK s) :
    Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
  obtain ⟨_, halloc, hins_hl, _, _⟩ := hNH.1 n hn
  rcases halloc with hh | hs
  · exact hh
  · exfalso
    have hsz := (nodeSize_pos (memW s n)).1
    have hsl : heapLimit ≤ scratchStart := by decide
    have h1 := hA.2.1; have h2 := hA.2.2.1; have h3 := hA.2.2.2.1
    unfold nodeIvl Inside at hins_hl hs
    omega

theorem keyIn_in_heap {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {p len : Nat} (hk : KeyIn s Nd p len) (hlen_pos : len > 0) (hA : ArenaOK s) :
    Inside (p, len) sourceBase (globN s "heap_ptr") := by
  rcases hk with rfl | ⟨_, halloc, hins_hl, _⟩
  · omega
  · rcases halloc with hh | hs
    · exact hh
    · exfalso
      have hsl : heapLimit ≤ scratchStart := by decide
      have h1 := hA.2.1; have h2 := hA.2.2.1; have h3 := hA.2.2.2.1
      unfold Inside at hins_hl hs
      omega

theorem nodeHeap_mono_fresh {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hNH : NodeHeap s Nd)
    (hA_s : ArenaOK s) (hA_post : ArenaOK post)
    (hma : post.memaddrs = s.memaddrs) (hbe : post.be = s.be)
    (hfr : FrameOutside s post
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    (hhp_le : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr") :
    NodeHeap post Nd ∧ (∀ n ∈ Nd, memW post n = memW s n) ∧
    (∀ n ∈ Nd, nodeIvl post n = nodeIvl s n) := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hsl : heapLimit ≤ scratchStart := by decide
  have hgrows : AllocatorGrows s post := ⟨hhp_le, le_of_eq hsp_eq⟩
  -- Every word `[a, a+8) ⊆ [sourceBase, globN s "heap_ptr")` is unchanged!
  have hword_unch : ∀ a : Nat, sourceBase ≤ a → a + 8 ≤ globN s "heap_ptr" →
      memW post a = memW s a := by
    intro a hlo hhi
    have ha_lt : a < 2 ^ 64 := by have := hA_s.2.1; omega
    refine memW_eq_of_frameOutside hfr a ha_lt ?_ ?_
    · intro i hi
      simp only [List.mem_singleton] at hi; subst hi
      unfold CellHits
      have := hA_s.2.1; have := hA_s.2.2.1; omega
    · unfold CellHits; omega
  have hkind_eq : ∀ n ∈ Nd, memW post n = memW s n := by
    intro n hn
    have hin := nodeIvl_in_heap hNH hn hA_s
    have hsz := (nodeSize_pos (memW s n)).1
    unfold nodeIvl Inside at hin
    exact hword_unch n hin.1 (by omega)
  have hivl_eq : ∀ n ∈ Nd, nodeIvl post n = nodeIvl s n := by
    intro n hn
    simp only [nodeIvl, hkind_eq n hn]
  refine ⟨⟨?_, ?_⟩, hkind_eq, hivl_eq⟩
  · intro n hn
    obtain ⟨hk3, halloc, hins_hl, hwok, hext, hbr, hpath, hc16, hl56, hb168⟩ := hNH.1 n hn
    have hin_hp := nodeIvl_in_heap hNH hn hA_s
    have hsz := (nodeSize_pos (memW s n)).1
    have hfield : ∀ off : Nat, off + 8 ≤ nodeSize (memW s n) → memW post (n + off) = memW s (n + off) := by
      intro off hoff
      unfold nodeIvl Inside at hin_hp
      exact hword_unch (n + off) (by omega) (by omega)
    rw [hkind_eq n hn, hivl_eq n hn]
    refine ⟨hk3, hgrows.allocated halloc, hins_hl, wordsOK_of_frame hma _ hwok, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hk2
      have hsz2 : nodeSize (memW s n) = 56 := by simp [nodeSize, hk2]
      rw [hfield 48 (by omega)]; exact hext hk2
    · intro hk3' i hi16
      have hsz3 : nodeSize (memW s n) = 176 := by simp [nodeSize, hk3']
      have heq_off : n + 32 + 8 * i = n + (32 + 8 * i) := by omega
      rw [heq_off, hfield (32 + 8 * i) (by omega), ← heq_off]
      exact hbr hk3' i hi16
    · intro hk12
      have hsz12 : 56 ≤ nodeSize (memW s n) := by
        rcases hk12 with h1 | h2
        · simp [nodeSize, h1]
        · simp [nodeSize, h2]
      rw [hfield 32 (by omega), hfield 40 (by omega)]
      refine keyIn_mono_frame hbe hfr (hpath hk12) hgrows ?_ ?_
        (fun m hm => Or.inl ⟨hm, hivl_eq m hm⟩) hA_s
      · intro hpos i hi
        simp only [List.mem_singleton] at hi; subst hi
        have hk_hp := keyIn_in_heap (hpath hk12) hpos hA_s
        refine ⟨hA_s.2.2.2.2.2.2.1, ?_, ?_⟩
        · dsimp only; have := hA_s.2.2.2.2.2.2.1; have := hA_s.2.2.2.2.2.2.2.1; omega
        · unfold Disj Inside at *; have := hA_s.2.1; have := hA_s.2.2.1; omega
      · intro hpos
        have hk_hp := keyIn_in_heap (hpath hk12) hpos hA_s
        refine ⟨hA_s.2.2.2.2.2.1, ?_, ?_⟩
        · dsimp only
          have h1 := hA_s.2.2.2.2.2.1
          have h2 : heapLimit % 8 = 0 := by decide
          omega
        · unfold Disj Inside at *; omega
    · rw [hfield 16 (by omega)]; exact hc16
    · intro hk1
      have hsz1 : nodeSize (memW s n) = 64 := by simp [nodeSize, hk1]
      rw [hfield 56 (by omega)]; exact hl56 hk1
    · intro hk3'
      have hsz3 : nodeSize (memW s n) = 176 := by simp [nodeSize, hk3']
      rw [hfield 168 (by omega)]; exact hb168 hk3'
  · intro n hn m hm hne
    rw [hivl_eq n hn, hivl_eq m hm]
    exact hNH.2 n hn m hm hne

end InitECandidate.Solver.Wave8GuestInv.R10Shards.P02
