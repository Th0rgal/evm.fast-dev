import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.HeapPotential
import Guest.SoftwareAst

/-! Shared light-cone definitions and allocator/frame helpers for contract micro-shard `m29`
(`wave8/contracts-m29`, frozen spec rev9 `8a79d9f28`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.MemoryViews` plus
existing cone modules (`HeapPotential`, `Guest.SoftwareAst`).
Restates `FunSpec`, `Resumes`, `WritesWithin`, and `ZeroFills` verbatim from
`campaign/specs-proposed/GuestInv.lean` @ `8a79d9f28` so every proved theorem delta-reduces
definitionally (`rfl`) to its frozen spec statement in `Axioms.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M29

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Verbatim rev9 contract definitions (`GuestInv.lean` @ `8a79d9f28`) -/

def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

def WritesWithin (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => Resumes r →
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    FrameOutside s post
      (R s ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
    ∀ k : MlS, k ∉ gw.map ofString → s.globals.lookup k = post.globals.lookup k)
    fname

def ZeroFills (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) → ∀ a, locN s "dst" ≤ a →
    a + 8 ≤ locN s "dst" + locN s "n" → a % 8 = 0 → memW post a = 0) fname

/-! ## 2. Ordinary domain and arena globals helpers -/

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  unfold ordinaryDomain
  rw [StackRemove.mem_addresses]
  have hx := x.isLt
  have hconst : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 ∧
      sourceBase = 2701131776 ∧ heapEnd = 33806089704 ∧
      StackRemove.bytesInWord 64 = BitVec.ofNat 64 8 := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    decide
  rcases hconst with ⟨hn, hsb, hhe, hbw⟩
  rw [hn, hbw]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe]
    omega
  · rintro ⟨hal, hlo, hhi⟩
    refine ⟨(x.toNat - sourceBase) / 8, by simp only [hsb, hhe] at hlo hhi; omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe] at hlo hhi ⊢
    omega

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

/-! ## 3. `trap_with` never resumes -/

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

/-! ## 4. `scratch_alloc` body semantics on `Resumes` -/

theorem lookup_scratch_alloc :
    originalRuntimeCode.lookup (ofString "scratch_alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_scratch_alloc, .one) :=
  lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_alloc) rfl

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

end InitECandidate.Solver.Wave8Contracts.M29
